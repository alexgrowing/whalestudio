import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteGroupIdentificationFixedPlacesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGoodCharacterSetIdempotentCoeffCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperUnipotentGenericCharacterMemIntegralFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnFaceLevelsBaseLevelSymmetricLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiLevelPairCompatibleOfColumnLevelsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.Grp

theorem coeff_conj_of_central {G : Type} [Group G] (e : MonoidAlgebra ℂ G) (he : ∀ x, x * e = e * x) (k g : G) :
    e.coeff (k * g * k⁻¹) = e.coeff g := by
  have h := congrArg (fun a : MonoidAlgebra ℂ G => a.coeff (k * g)) (he (MonoidAlgebra.single k 1))
  simp only [MonoidAlgebra.mul_single_apply, MonoidAlgebra.single_mul_apply] at h
  simpa [mul_assoc] using h.symm

theorem idemOf_coeff_conj : ∀ (X : Stages) (px : PreX X.B.toPre) (eR : Gc X.B px ≃* G0g X.toD7.nd) (Xg : Finset (Gc X.B px → X.B.LL)), GoodSet X (px := px) eR Xg → X.toD7.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g X.toD7.nd)) → ∀ a b : Gc X.B px, (idemOf Xg).coeff (a * b * a⁻¹) = (idemOf Xg).coeff b := by
  intro X px eR Xg hgood hc a b
  apply X.B.embLL.injective
  rw [hgood.2, hgood.2, map_mul eR, map_mul eR, map_inv eR]
  exact coeff_conj_of_central _ (Subalgebra.mem_center_iff.1 hc) _ _

theorem grp_levels_exist : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → GrpAt X I → LevOf X I U L → ∃ (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (cG : G0 L.Pg X.toD7.R.r ≃* G0g X.toD7.nd) (Xg : Finset (Gc X.B px → X.B.LL)), IsPlacewiseIdentity X (px := px) eG ∧ GoodSet X (px := px) (eG.trans cG) Xg ∧ PsiPPTie X.toD7 (lev0 I) (chr0 I) (lev1 I) (chr1 I) (eG.trans cG) ∧ (∀ g, (idemOf Xg).coeff g ∈ X.B.Ks) ∧ (∀ p, ((chr0 I p : X.B.LLˣ) : X.B.LL) ∈ X.B.Ks) ∧ ∀ tr, IdemClass (D := X.toD7) (famR X I hX U Xg tr).A ∧ Seed.LevelsL (famR X I hX U Xg tr) L eG (face0 X I hX U Xg tr).lv2 ∧ ∃ (plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ L.Pg) (iso : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), ZMod (X.toD7.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : L.Pg) : Pl X.toD7.host.E) = X.toD7.naut.plGw kv.1 kv.2) ∧ (∀ kv, L.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* kP (plg kv).1) ((eG.trans cG) g kv) := by
  intro X px I hX U L hI hG hL
  obtain ⟨eG, cG, plg, iso, hid, hpl, hdiv, hbc⟩ := GlobalTheory.T.exists_finiteGroupIdentification_fixedPlaces X px I U L hI hG hL
  obtain ⟨Xg, hgood, hKs⟩ := GlobalTheory.T.exists_goodCharacterSet_idempotent_coeff_coefficientField X px (eG.trans cG)
  refine ⟨eG, cG, Xg, hid, hgood, GlobalTheory.T.psiLevelPairCompatible_of_columnLevels X px I U L eG cG plg iso hI hL hid hpl hbc, hKs, GlobalTheory.T.upperUnipotentGenericCharacter_mem_integralField X.B px I,
    fun tr => ⟨?_, GlobalTheory.T.columnFaceLevels_baseLevel_symmetricLevel X px I hX U Xg tr L eG hI hL hid, plg, iso, hpl, hdiv, hbc⟩⟩
  exact idemOf_coeff_conj X px (eG.trans cG) Xg hgood hG.cen

end GlobalTheory.Mem.R3.Grp

end
