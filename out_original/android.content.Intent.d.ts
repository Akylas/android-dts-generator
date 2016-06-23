/// <reference path="./_helpers.d.ts" />
/// <reference path="./android.content.ClipData.d.ts" />
/// <reference path="./android.content.ComponentName.d.ts" />
/// <reference path="./android.content.ContentResolver.d.ts" />
/// <reference path="./android.content.Context.d.ts" />
/// <reference path="./android.content.IntentSender.d.ts" />
/// <reference path="./android.content.pm.ActivityInfo.d.ts" />
/// <reference path="./android.content.pm.PackageManager.d.ts" />
/// <reference path="./android.content.res.Resources.d.ts" />
/// <reference path="./android.graphics.Rect.d.ts" />
/// <reference path="./android.net.Uri.d.ts" />
/// <reference path="./android.os.Bundle.d.ts" />
/// <reference path="./android.os.Parcel.d.ts" />
/// <reference path="./android.os.Parcelable.d.ts" />
/// <reference path="./android.util.AttributeSet.d.ts" />
/// <reference path="./java.io.Serializable.d.ts" />
/// <reference path="./java.lang.CharSequence.d.ts" />
/// <reference path="./java.lang.Class.d.ts" />
/// <reference path="./java.lang.ClassLoader.d.ts" />
/// <reference path="./java.lang.Object.d.ts" />
/// <reference path="./java.lang.String.d.ts" />
/// <reference path="./java.util.ArrayList.d.ts" />
/// <reference path="./java.util.Set.d.ts" />
/// <reference path="./org.xmlpull.v1.XmlPullParser.d.ts" />

declare module android {
	export module content {
		export class Intent {
			public constructor();
			public constructor(param0: android.content.Intent);
			public constructor(param0: string);
			public constructor(param0: string, param1: android.net.Uri);
			public constructor(param0: android.content.Context, param1: java.lang.Class);
			public constructor(param0: string, param1: android.net.Uri, param2: android.content.Context, param3: java.lang.Class);
			public static createChooser(param0: android.content.Intent, param1: string): android.content.Intent;
			public static createChooser(param0: android.content.Intent, param1: string, param2: android.content.IntentSender): android.content.Intent;
			public clone(): java.lang.Object;
			public cloneFilter(): android.content.Intent;
			public static makeMainActivity(param0: android.content.ComponentName): android.content.Intent;
			public static makeMainSelectorActivity(param0: string, param1: string): android.content.Intent;
			public static makeRestartActivityTask(param0: android.content.ComponentName): android.content.Intent;
			public static getIntent(param0: string): android.content.Intent;
			public static parseUri(param0: string, param1: number): android.content.Intent;
			public static getIntentOld(param0: string): android.content.Intent;
			public getAction(): string;
			public getData(): android.net.Uri;
			public getDataString(): string;
			public getScheme(): string;
			public getType(): string;
			public resolveType(param0: android.content.Context): string;
			public resolveType(param0: android.content.ContentResolver): string;
			public resolveTypeIfNeeded(param0: android.content.ContentResolver): string;
			public hasCategory(param0: string): boolean;
			public getCategories(): java.util.Set;
			public getSelector(): android.content.Intent;
			public getClipData(): android.content.ClipData;
			public setExtrasClassLoader(param0: java.lang.ClassLoader): void;
			public hasExtra(param0: string): boolean;
			public hasFileDescriptors(): boolean;
			public getBooleanExtra(param0: string, param1: boolean): boolean;
			public getByteExtra(param0: string, param1: number): number;
			public getShortExtra(param0: string, param1: number): number;
			public getCharExtra(param0: string, param1: string): string;
			public getIntExtra(param0: string, param1: number): number;
			public getLongExtra(param0: string, param1: number): number;
			public getFloatExtra(param0: string, param1: number): number;
			public getDoubleExtra(param0: string, param1: number): number;
			public getStringExtra(param0: string): string;
			public getCharSequenceExtra(param0: string): string;
			public getParcelableExtra(param0: string): android.os.Parcelable;
			public getParcelableArrayExtra(param0: string): native.Array<android.os.Parcelable>;
			public getParcelableArrayListExtra(param0: string): java.util.ArrayList;
			public getSerializableExtra(param0: string): java.io.Serializable;
			public getIntegerArrayListExtra(param0: string): java.util.ArrayList;
			public getStringArrayListExtra(param0: string): java.util.ArrayList;
			public getCharSequenceArrayListExtra(param0: string): java.util.ArrayList;
			public getBooleanArrayExtra(param0: string): native.Array<boolean>;
			public getByteArrayExtra(param0: string): native.Array<number>;
			public getShortArrayExtra(param0: string): native.Array<number>;
			public getCharArrayExtra(param0: string): native.Array<string>;
			public getIntArrayExtra(param0: string): native.Array<number>;
			public getLongArrayExtra(param0: string): native.Array<number>;
			public getFloatArrayExtra(param0: string): native.Array<number>;
			public getDoubleArrayExtra(param0: string): native.Array<number>;
			public getStringArrayExtra(param0: string): native.Array<string>;
			public getCharSequenceArrayExtra(param0: string): native.Array<java.lang.CharSequence>;
			public getBundleExtra(param0: string): android.os.Bundle;
			public getExtras(): android.os.Bundle;
			public getFlags(): number;
			public getPackage(): string;
			public getComponent(): android.content.ComponentName;
			public getSourceBounds(): android.graphics.Rect;
			public resolveActivity(param0: android.content.pm.PackageManager): android.content.ComponentName;
			public resolveActivityInfo(param0: android.content.pm.PackageManager, param1: number): android.content.pm.ActivityInfo;
			public setAction(param0: string): android.content.Intent;
			public setData(param0: android.net.Uri): android.content.Intent;
			public setDataAndNormalize(param0: android.net.Uri): android.content.Intent;
			public setType(param0: string): android.content.Intent;
			public setTypeAndNormalize(param0: string): android.content.Intent;
			public setDataAndType(param0: android.net.Uri, param1: string): android.content.Intent;
			public setDataAndTypeAndNormalize(param0: android.net.Uri, param1: string): android.content.Intent;
			public addCategory(param0: string): android.content.Intent;
			public removeCategory(param0: string): void;
			public setSelector(param0: android.content.Intent): void;
			public setClipData(param0: android.content.ClipData): void;
			public putExtra(param0: string, param1: boolean): android.content.Intent;
			public putExtra(param0: string, param1: number): android.content.Intent;
			public putExtra(param0: string, param1: string): android.content.Intent;
			public putExtra(param0: string, param1: number): android.content.Intent;
			public putExtra(param0: string, param1: number): android.content.Intent;
			public putExtra(param0: string, param1: number): android.content.Intent;
			public putExtra(param0: string, param1: number): android.content.Intent;
			public putExtra(param0: string, param1: number): android.content.Intent;
			public putExtra(param0: string, param1: string): android.content.Intent;
			public putExtra(param0: string, param1: string): android.content.Intent;
			public putExtra(param0: string, param1: android.os.Parcelable): android.content.Intent;
			public putExtra(param0: string, param1: native.Array<android.os.Parcelable>): android.content.Intent;
			public putParcelableArrayListExtra(param0: string, param1: java.util.ArrayList): android.content.Intent;
			public putIntegerArrayListExtra(param0: string, param1: java.util.ArrayList): android.content.Intent;
			public putStringArrayListExtra(param0: string, param1: java.util.ArrayList): android.content.Intent;
			public putCharSequenceArrayListExtra(param0: string, param1: java.util.ArrayList): android.content.Intent;
			public putExtra(param0: string, param1: java.io.Serializable): android.content.Intent;
			public putExtra(param0: string, param1: native.Array<boolean>): android.content.Intent;
			public putExtra(param0: string, param1: native.Array<number>): android.content.Intent;
			public putExtra(param0: string, param1: native.Array<number>): android.content.Intent;
			public putExtra(param0: string, param1: native.Array<string>): android.content.Intent;
			public putExtra(param0: string, param1: native.Array<number>): android.content.Intent;
			public putExtra(param0: string, param1: native.Array<number>): android.content.Intent;
			public putExtra(param0: string, param1: native.Array<number>): android.content.Intent;
			public putExtra(param0: string, param1: native.Array<number>): android.content.Intent;
			public putExtra(param0: string, param1: native.Array<string>): android.content.Intent;
			public putExtra(param0: string, param1: native.Array<java.lang.CharSequence>): android.content.Intent;
			public putExtra(param0: string, param1: android.os.Bundle): android.content.Intent;
			public putExtras(param0: android.content.Intent): android.content.Intent;
			public putExtras(param0: android.os.Bundle): android.content.Intent;
			public replaceExtras(param0: android.content.Intent): android.content.Intent;
			public replaceExtras(param0: android.os.Bundle): android.content.Intent;
			public removeExtra(param0: string): void;
			public setFlags(param0: number): android.content.Intent;
			public addFlags(param0: number): android.content.Intent;
			public setPackage(param0: string): android.content.Intent;
			public setComponent(param0: android.content.ComponentName): android.content.Intent;
			public setClassName(param0: android.content.Context, param1: string): android.content.Intent;
			public setClassName(param0: string, param1: string): android.content.Intent;
			public setClass(param0: android.content.Context, param1: java.lang.Class): android.content.Intent;
			public setSourceBounds(param0: android.graphics.Rect): void;
			public fillIn(param0: android.content.Intent, param1: number): number;
			public filterEquals(param0: android.content.Intent): boolean;
			public filterHashCode(): number;
			public toString(): string;
			public toURI(): string;
			public toUri(param0: number): string;
			public describeContents(): number;
			public writeToParcel(param0: android.os.Parcel, param1: number): void;
			public readFromParcel(param0: android.os.Parcel): void;
			public static parseIntent(param0: android.content.res.Resources, param1: org.xmlpull.v1.XmlPullParser, param2: android.util.AttributeSet): android.content.Intent;
			public static normalizeMimeType(param0: string): string;
			public static ACTION_AIRPLANE_MODE_CHANGED: string;
			public static ACTION_ALL_APPS: string;
			public static ACTION_ANSWER: string;
			public static ACTION_APPLICATION_RESTRICTIONS_CHANGED: string;
			public static ACTION_APP_ERROR: string;
			public static ACTION_ASSIST: string;
			public static ACTION_ATTACH_DATA: string;
			public static ACTION_BATTERY_CHANGED: string;
			public static ACTION_BATTERY_LOW: string;
			public static ACTION_BATTERY_OKAY: string;
			public static ACTION_BOOT_COMPLETED: string;
			public static ACTION_BUG_REPORT: string;
			public static ACTION_CALL: string;
			public static ACTION_CALL_BUTTON: string;
			public static ACTION_CAMERA_BUTTON: string;
			public static ACTION_CHOOSER: string;
			public static ACTION_CLOSE_SYSTEM_DIALOGS: string;
			public static ACTION_CONFIGURATION_CHANGED: string;
			public static ACTION_CREATE_DOCUMENT: string;
			public static ACTION_CREATE_SHORTCUT: string;
			public static ACTION_DATE_CHANGED: string;
			public static ACTION_DEFAULT: string;
			public static ACTION_DELETE: string;
			public static ACTION_DEVICE_STORAGE_LOW: string;
			public static ACTION_DEVICE_STORAGE_OK: string;
			public static ACTION_DIAL: string;
			public static ACTION_DOCK_EVENT: string;
			public static ACTION_DREAMING_STARTED: string;
			public static ACTION_DREAMING_STOPPED: string;
			public static ACTION_EDIT: string;
			public static ACTION_EXTERNAL_APPLICATIONS_AVAILABLE: string;
			public static ACTION_EXTERNAL_APPLICATIONS_UNAVAILABLE: string;
			public static ACTION_FACTORY_TEST: string;
			public static ACTION_GET_CONTENT: string;
			public static ACTION_GET_RESTRICTION_ENTRIES: string;
			public static ACTION_GTALK_SERVICE_CONNECTED: string;
			public static ACTION_GTALK_SERVICE_DISCONNECTED: string;
			public static ACTION_HEADSET_PLUG: string;
			public static ACTION_INPUT_METHOD_CHANGED: string;
			public static ACTION_INSERT: string;
			public static ACTION_INSERT_OR_EDIT: string;
			public static ACTION_INSTALL_PACKAGE: string;
			public static ACTION_LOCALE_CHANGED: string;
			public static ACTION_MAIN: string;
			public static ACTION_MANAGED_PROFILE_ADDED: string;
			public static ACTION_MANAGED_PROFILE_REMOVED: string;
			public static ACTION_MANAGE_NETWORK_USAGE: string;
			public static ACTION_MANAGE_PACKAGE_STORAGE: string;
			public static ACTION_MEDIA_BAD_REMOVAL: string;
			public static ACTION_MEDIA_BUTTON: string;
			public static ACTION_MEDIA_CHECKING: string;
			public static ACTION_MEDIA_EJECT: string;
			public static ACTION_MEDIA_MOUNTED: string;
			public static ACTION_MEDIA_NOFS: string;
			public static ACTION_MEDIA_REMOVED: string;
			public static ACTION_MEDIA_SCANNER_FINISHED: string;
			public static ACTION_MEDIA_SCANNER_SCAN_FILE: string;
			public static ACTION_MEDIA_SCANNER_STARTED: string;
			public static ACTION_MEDIA_SHARED: string;
			public static ACTION_MEDIA_UNMOUNTABLE: string;
			public static ACTION_MEDIA_UNMOUNTED: string;
			public static ACTION_MY_PACKAGE_REPLACED: string;
			public static ACTION_NEW_OUTGOING_CALL: string;
			public static ACTION_OPEN_DOCUMENT: string;
			public static ACTION_OPEN_DOCUMENT_TREE: string;
			public static ACTION_PACKAGE_ADDED: string;
			public static ACTION_PACKAGE_CHANGED: string;
			public static ACTION_PACKAGE_DATA_CLEARED: string;
			public static ACTION_PACKAGE_FIRST_LAUNCH: string;
			public static ACTION_PACKAGE_FULLY_REMOVED: string;
			public static ACTION_PACKAGE_INSTALL: string;
			public static ACTION_PACKAGE_NEEDS_VERIFICATION: string;
			public static ACTION_PACKAGE_REMOVED: string;
			public static ACTION_PACKAGE_REPLACED: string;
			public static ACTION_PACKAGE_RESTARTED: string;
			public static ACTION_PACKAGE_VERIFIED: string;
			public static ACTION_PASTE: string;
			public static ACTION_PICK: string;
			public static ACTION_PICK_ACTIVITY: string;
			public static ACTION_POWER_CONNECTED: string;
			public static ACTION_POWER_DISCONNECTED: string;
			public static ACTION_POWER_USAGE_SUMMARY: string;
			public static ACTION_PROCESS_TEXT: string;
			public static ACTION_PROVIDER_CHANGED: string;
			public static ACTION_QUICK_CLOCK: string;
			public static ACTION_REBOOT: string;
			public static ACTION_RUN: string;
			public static ACTION_SCREEN_OFF: string;
			public static ACTION_SCREEN_ON: string;
			public static ACTION_SEARCH: string;
			public static ACTION_SEARCH_LONG_PRESS: string;
			public static ACTION_SEND: string;
			public static ACTION_SENDTO: string;
			public static ACTION_SEND_MULTIPLE: string;
			public static ACTION_SET_WALLPAPER: string;
			public static ACTION_SHUTDOWN: string;
			public static ACTION_SYNC: string;
			public static ACTION_SYSTEM_TUTORIAL: string;
			public static ACTION_TIMEZONE_CHANGED: string;
			public static ACTION_TIME_CHANGED: string;
			public static ACTION_TIME_TICK: string;
			public static ACTION_UID_REMOVED: string;
			public static ACTION_UMS_CONNECTED: string;
			public static ACTION_UMS_DISCONNECTED: string;
			public static ACTION_UNINSTALL_PACKAGE: string;
			public static ACTION_USER_BACKGROUND: string;
			public static ACTION_USER_FOREGROUND: string;
			public static ACTION_USER_INITIALIZE: string;
			public static ACTION_USER_PRESENT: string;
			public static ACTION_VIEW: string;
			public static ACTION_VOICE_COMMAND: string;
			public static ACTION_WALLPAPER_CHANGED: string;
			public static ACTION_WEB_SEARCH: string;
			public static CATEGORY_ALTERNATIVE: string;
			public static CATEGORY_APP_BROWSER: string;
			public static CATEGORY_APP_CALCULATOR: string;
			public static CATEGORY_APP_CALENDAR: string;
			public static CATEGORY_APP_CONTACTS: string;
			public static CATEGORY_APP_EMAIL: string;
			public static CATEGORY_APP_GALLERY: string;
			public static CATEGORY_APP_MAPS: string;
			public static CATEGORY_APP_MARKET: string;
			public static CATEGORY_APP_MESSAGING: string;
			public static CATEGORY_APP_MUSIC: string;
			public static CATEGORY_BROWSABLE: string;
			public static CATEGORY_CAR_DOCK: string;
			public static CATEGORY_CAR_MODE: string;
			public static CATEGORY_DEFAULT: string;
			public static CATEGORY_DESK_DOCK: string;
			public static CATEGORY_DEVELOPMENT_PREFERENCE: string;
			public static CATEGORY_EMBED: string;
			public static CATEGORY_FRAMEWORK_INSTRUMENTATION_TEST: string;
			public static CATEGORY_HE_DESK_DOCK: string;
			public static CATEGORY_HOME: string;
			public static CATEGORY_INFO: string;
			public static CATEGORY_LAUNCHER: string;
			public static CATEGORY_LEANBACK_LAUNCHER: string;
			public static CATEGORY_LE_DESK_DOCK: string;
			public static CATEGORY_MONKEY: string;
			public static CATEGORY_OPENABLE: string;
			public static CATEGORY_PREFERENCE: string;
			public static CATEGORY_SAMPLE_CODE: string;
			public static CATEGORY_SELECTED_ALTERNATIVE: string;
			public static CATEGORY_TAB: string;
			public static CATEGORY_TEST: string;
			public static CATEGORY_UNIT_TEST: string;
			public static CATEGORY_VOICE: string;
			public static CREATOR: android.os.Parcelable.Creator;
			public static EXTRA_ALARM_COUNT: string;
			public static EXTRA_ALLOW_MULTIPLE: string;
			public static EXTRA_ALLOW_REPLACE: string;
			public static EXTRA_ALTERNATE_INTENTS: string;
			public static EXTRA_ASSIST_CONTEXT: string;
			public static EXTRA_ASSIST_INPUT_DEVICE_ID: string;
			public static EXTRA_ASSIST_INPUT_HINT_KEYBOARD: string;
			public static EXTRA_ASSIST_PACKAGE: string;
			public static EXTRA_ASSIST_UID: string;
			public static EXTRA_BCC: string;
			public static EXTRA_BUG_REPORT: string;
			public static EXTRA_CC: string;
			public static EXTRA_CHANGED_COMPONENT_NAME: string;
			public static EXTRA_CHANGED_COMPONENT_NAME_LIST: string;
			public static EXTRA_CHANGED_PACKAGE_LIST: string;
			public static EXTRA_CHANGED_UID_LIST: string;
			public static EXTRA_CHOOSER_REFINEMENT_INTENT_SENDER: string;
			public static EXTRA_CHOSEN_COMPONENT: string;
			public static EXTRA_CHOSEN_COMPONENT_INTENT_SENDER: string;
			public static EXTRA_DATA_REMOVED: string;
			public static EXTRA_DOCK_STATE: string;
			public static EXTRA_DOCK_STATE_CAR: number;
			public static EXTRA_DOCK_STATE_DESK: number;
			public static EXTRA_DOCK_STATE_HE_DESK: number;
			public static EXTRA_DOCK_STATE_LE_DESK: number;
			public static EXTRA_DOCK_STATE_UNDOCKED: number;
			public static EXTRA_DONT_KILL_APP: string;
			public static EXTRA_EMAIL: string;
			public static EXTRA_HTML_TEXT: string;
			public static EXTRA_INITIAL_INTENTS: string;
			public static EXTRA_INSTALLER_PACKAGE_NAME: string;
			public static EXTRA_INTENT: string;
			public static EXTRA_KEY_EVENT: string;
			public static EXTRA_LOCAL_ONLY: string;
			public static EXTRA_MIME_TYPES: string;
			public static EXTRA_NOT_UNKNOWN_SOURCE: string;
			public static EXTRA_ORIGINATING_URI: string;
			public static EXTRA_PHONE_NUMBER: string;
			public static EXTRA_PROCESS_TEXT: string;
			public static EXTRA_PROCESS_TEXT_READONLY: string;
			public static EXTRA_REFERRER: string;
			public static EXTRA_REFERRER_NAME: string;
			public static EXTRA_REMOTE_INTENT_TOKEN: string;
			public static EXTRA_REPLACEMENT_EXTRAS: string;
			public static EXTRA_REPLACING: string;
			public static EXTRA_RESTRICTIONS_BUNDLE: string;
			public static EXTRA_RESTRICTIONS_INTENT: string;
			public static EXTRA_RESTRICTIONS_LIST: string;
			public static EXTRA_RESULT_RECEIVER: string;
			public static EXTRA_RETURN_RESULT: string;
			public static EXTRA_SHORTCUT_ICON: string;
			public static EXTRA_SHORTCUT_ICON_RESOURCE: string;
			public static EXTRA_SHORTCUT_INTENT: string;
			public static EXTRA_SHORTCUT_NAME: string;
			public static EXTRA_SHUTDOWN_USERSPACE_ONLY: string;
			public static EXTRA_STREAM: string;
			public static EXTRA_SUBJECT: string;
			public static EXTRA_TEMPLATE: string;
			public static EXTRA_TEXT: string;
			public static EXTRA_TITLE: string;
			public static EXTRA_UID: string;
			public static EXTRA_USER: string;
			public static FILL_IN_ACTION: number;
			public static FILL_IN_CATEGORIES: number;
			public static FILL_IN_CLIP_DATA: number;
			public static FILL_IN_COMPONENT: number;
			public static FILL_IN_DATA: number;
			public static FILL_IN_PACKAGE: number;
			public static FILL_IN_SELECTOR: number;
			public static FILL_IN_SOURCE_BOUNDS: number;
			public static FLAG_ACTIVITY_BROUGHT_TO_FRONT: number;
			public static FLAG_ACTIVITY_CLEAR_TASK: number;
			public static FLAG_ACTIVITY_CLEAR_TOP: number;
			public static FLAG_ACTIVITY_CLEAR_WHEN_TASK_RESET: number;
			public static FLAG_ACTIVITY_EXCLUDE_FROM_RECENTS: number;
			public static FLAG_ACTIVITY_FORWARD_RESULT: number;
			public static FLAG_ACTIVITY_LAUNCHED_FROM_HISTORY: number;
			public static FLAG_ACTIVITY_MULTIPLE_TASK: number;
			public static FLAG_ACTIVITY_NEW_DOCUMENT: number;
			public static FLAG_ACTIVITY_NEW_TASK: number;
			public static FLAG_ACTIVITY_NO_ANIMATION: number;
			public static FLAG_ACTIVITY_NO_HISTORY: number;
			public static FLAG_ACTIVITY_NO_USER_ACTION: number;
			public static FLAG_ACTIVITY_PREVIOUS_IS_TOP: number;
			public static FLAG_ACTIVITY_REORDER_TO_FRONT: number;
			public static FLAG_ACTIVITY_RESET_TASK_IF_NEEDED: number;
			public static FLAG_ACTIVITY_RETAIN_IN_RECENTS: number;
			public static FLAG_ACTIVITY_SINGLE_TOP: number;
			public static FLAG_ACTIVITY_TASK_ON_HOME: number;
			public static FLAG_DEBUG_LOG_RESOLUTION: number;
			public static FLAG_EXCLUDE_STOPPED_PACKAGES: number;
			public static FLAG_FROM_BACKGROUND: number;
			public static FLAG_GRANT_PERSISTABLE_URI_PERMISSION: number;
			public static FLAG_GRANT_PREFIX_URI_PERMISSION: number;
			public static FLAG_GRANT_READ_URI_PERMISSION: number;
			public static FLAG_GRANT_WRITE_URI_PERMISSION: number;
			public static FLAG_INCLUDE_STOPPED_PACKAGES: number;
			public static FLAG_RECEIVER_FOREGROUND: number;
			public static FLAG_RECEIVER_NO_ABORT: number;
			public static FLAG_RECEIVER_REGISTERED_ONLY: number;
			public static FLAG_RECEIVER_REPLACE_PENDING: number;
			public static METADATA_DOCK_HOME: string;
			public static URI_ALLOW_UNSAFE: number;
			public static URI_ANDROID_APP_SCHEME: number;
			public static URI_INTENT_SCHEME: number;
		}
		export module Intent {
			export class FilterComparison {
				public constructor();
				public constructor(param0: android.content.Intent);
				public getIntent(): android.content.Intent;
				public equals(param0: java.lang.Object): boolean;
				public hashCode(): number;
			}
			export class ShortcutIconResource {
				public constructor();
				public static fromContext(param0: android.content.Context, param1: number): android.content.Intent.ShortcutIconResource;
				public describeContents(): number;
				public writeToParcel(param0: android.os.Parcel, param1: number): void;
				public toString(): string;
				public static CREATOR: android.os.Parcelable.Creator;
				public packageName: string;
				public resourceName: string;
			}
		}
	}
}