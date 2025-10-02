import { 
    window, 
    Uri, 
    TextDocumentContentProvider, 
    CancellationToken, 
    EventEmitter,
    Event
} from "vscode";
import {
  RequestType,
  TextDocumentIdentifier,
} from "vscode-languageclient";

import { DocumentStateRequest, DocumentStateResponse } from "../protocol/types";

import Client from '../client';

export class DocumentStateViewProvider implements TextDocumentContentProvider {

    readonly scheme = "vsrocq-document-state";
    readonly uri = Uri.parse(this.scheme + "://doc");

    private textDocument: TextDocumentIdentifier | null = null; 
    readonly eventEmitter = new EventEmitter<Uri>();

    constructor(
        private _client: Client
    ){ }

    fire() : void {
        if(this.uri !== null) {
            Client.writeToVsrocqChannel("[DocumentStateViewProvider] Firing event");
            Client.writeToVsrocqChannel("[DocumentStateViewProvider] Current doc uri: " + this.textDocument?.uri.toString());
            this.eventEmitter.fire(this.uri);
        } 
    }
    
    get onDidChange(): Event<Uri> {
        return this.eventEmitter.event;
    }

    setDocumentUri(uri: Uri) {
        this.textDocument = TextDocumentIdentifier.create(uri.toString());
    }

    async provideTextDocumentContent(uri: Uri, token: CancellationToken): Promise<string> {
    
        if(this.textDocument === null) {
            Client.writeToVsrocqChannel("[DocumentStateViewProvider] No document was set so no state can be returned !"); 
            return Promise.reject();
        }

        const params: DocumentStateRequest = {textDocument: this.textDocument}; 
        const req = new RequestType<DocumentStateRequest, DocumentStateResponse, void>("prover/documentState");
        Client.writeToVsrocqChannel("[DocumentStateViewProvider] Getting document state for uri: " + this.textDocument.uri.toString());
        return this._client.sendRequest(req, params).then(
            (result: DocumentStateResponse) => {
                return result.document;
            }
        );   
    }

}