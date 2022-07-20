// tslint:disable
/**
 * Yugabyte Cloud
 * YugabyteDB as a Service
 *
 * The version of the OpenAPI document: v1
 * Contact: support@yugabyte.com
 *
 * NOTE: This class is auto generated by OpenAPI Generator (https://openapi-generator.tech).
 * https://openapi-generator.tech
 * Do not edit the class manually.
 */


// eslint-disable-next-line no-duplicate-imports
import type { PaymentMethodEnum } from './PaymentMethodEnum';


/**
 * Update payment method of a billing account
 * @export
 * @interface UpdatePaymentMethodSpec
 */
export interface UpdatePaymentMethodSpec  {
  /**
   * 
   * @type {PaymentMethodEnum}
   * @memberof UpdatePaymentMethodSpec
   */
  payment_method_type: PaymentMethodEnum;
}


