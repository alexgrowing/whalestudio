import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsLocalHomExtension

set_option autoImplicit false

namespace GlobalTheory.CharDepth

open IsLocalRing Formalism.L2.Pj

theorem exists_local_extension_of_integral {A B O C : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [IsLocalRing B] [CommRing O] [IsLocalRing O] [Field C] [IsAlgClosed C]
    [Algebra O C] (v : Valuation C NNReal) (hv : v.Integers O) (φ : A →+* B) (hφ : Function.Injective φ)
    (hint : φ.IsIntegral) (ι : A →+* O) [IsLocalHom ι]
    (hι : Function.Injective ((algebraMap O C).comp ι)) :
    ∃ ι' : B →+* O, IsLocalHom ι' ∧ ι'.comp φ = ι := by
  first
  | (rename_i h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13 h_14 h_21; revert A B O C h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13 h_14 v hv φ hφ hint ι h_21 hι; exact @_root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension)
  | exact @_root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension
  | exact _root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension
  | (apply _root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension ..)

theorem ValExt.exists_local_extension :
    ∀ (T T' : CDVR) (φ : T.V →+* T'.V), Function.Injective φ → φ.Finite → ∀ (p : ℕ) [Fact p.Prime]
      (X : ValExt T p), ∃ ι' : T'.V →+* X.O, IsLocalHom ι' ∧ ι'.comp φ = X.ι := by
  intro T T' φ hφ hfin p _ X
  haveI := X.ι_local
  refine exists_local_extension_of_integral X.v X.ints φ hφ hfin.to_isIntegral X.ι ?_
  have h : (algebraMap X.O X.C).comp X.ι = X.ιF.comp (algebraMap T.V T.Fr) := by
    ext x; exact (X.comp x).symm
  rw [h, RingHom.coe_comp]
  exact X.ιF.injective.comp (IsFractionRing.injective T.V T.Fr)

end GlobalTheory.CharDepth
