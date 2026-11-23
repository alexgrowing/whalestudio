import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemLevelOfLocalDepth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCardCodeWordStagesFiniteGroupEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCentralIdempotentOfGoodSeriesIdempotent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumIrrCharOneMulIrrCharColumnOrthogonalityStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassFunctionActsByScalarOnIrrCharStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralIdempotentEqSumCharacterIdempotentsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharCompMemComplexIrrCharSetStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharRealiseOfPrimitiveRootCardStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharMemClosurePrimitiveRootCardStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.GoodSetExists

section Gen

variable {G : Type} [Group G] [Fintype G]

theorem one_ne_zero_of_mem (ψ : G → ℂ) (h : ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ) : ψ 1 ≠ 0 := by
  obtain ⟨n, ρ, hρ, rfl⟩ := h
  intro e
  rw [Representation.char_one, Nat.cast_eq_zero, Module.finrank_zero_iff] at e
  exact (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem coeff_conj_of_center {e : MonoidAlgebra ℂ G} (he : e ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G)) (x y : G) :
    e.coeff (y * x * y⁻¹) = e.coeff x := by
  have h := congrArg (fun a : MonoidAlgebra ℂ G => a.coeff (y * x))
    ((Subalgebra.mem_center_iff.1 he (MonoidAlgebra.single y 1)).symm)
  simp only [MonoidAlgebra.coeff_mul_single_apply, MonoidAlgebra.coeff_single_mul_apply, mul_one, one_mul,
    inv_mul_cancel_left] at h
  exact h

end Gen

section Record

variable (X : Stages) (px : PreX X.B.toPre)

theorem exists_goodSet_Ks (eR : Gc X.B px ≃* G0g X.toD7.nd) :
    ∃ Xg : Finset (Gc X.B px → X.B.LL), GoodSet X (px := px) eR Xg ∧ ∀ g, (idemOf Xg).coeff g ∈ X.B.Ks := by
  classical
  let σ := X.B.embLL
  let f := MonoidAlgebra.domCongr ℂ ℂ eR.symm
  let e : MonoidAlgebra ℂ (Gc X.B px) := f X.toD7.ntypes.e0
  have hcoeff : ∀ g, e.coeff g = X.toD7.ntypes.e0.coeff (eR g) := fun g => by
    simp [e, f, MonoidAlgebra.domCongr_apply]
  obtain ⟨hcen0, hid0⟩ := GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent X.toD7
  have hid : e * e = e := by simp only [e, ← map_mul, hid0]
  have hcen : e ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (Gc X.B px)) := by
    refine Subalgebra.mem_center_iff.2 fun b => ?_
    obtain ⟨c, rfl⟩ := f.surjective b
    simp only [e, ← map_mul, (Subalgebra.mem_center_iff.1 hcen0 c)]
  have hcard : Fintype.card (Gc X.B px) = X.B.restRowsFiniteGroupCard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr eR.toEquiv]
    have : ∀ k, NeZero (X.toD7.host.g k) := fun k => ⟨(X.toD7.host.g_prime k).ne_zero⟩
    rw [Nat.card_pi, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    change ∏ _y : X.toD7.nd.PlG k, Nat.card (GL (Fin X.toD7.R.r) (ZMod (X.toD7.host.g k))) = _
    rw [Finset.prod_const, Finset.card_univ, X.toD7.nd.card_PlG k]
    rfl
  obtain ⟨z, hzK, hz⟩ := X.B.roots_Ks X.B.restRowsFiniteGroupCard (by simp)
  have hzp : IsPrimitiveRoot z (Fintype.card (Gc X.B px)) := by
    rw [hcard, ← IsPrimitiveRoot.map_iff_of_injective σ.injective]
    rw [show σ z = _ from hz]
    exact Complex.isPrimitiveRoot_exp _ X.B.restRowsFiniteGroupCard_pos.ne'
  refine ⟨Formalism.L2.Col.XgE σ e, Model.goodSet_of_idem X eR _ Formalism.L2.Col.XgE_irr fun g => ?_, fun g => ?_⟩
  · let A := (Formalism.L2.Col.gxIrrSet_finite (G := Gc X.B px) (k := ℂ)).toFinset
    have hA : ∀ ψ, ψ ∈ A ↔ ψ ∈ Formalism.L2.Col.gxIrrSet (G := Gc X.B px) ℂ := fun ψ => Set.Finite.mem_toFinset _
    have hexp := GlobalTheory.T.centralIdempotent_eq_sum_character_idempotents A e (fun ψ hψ => one_ne_zero_of_mem ψ ((hA ψ).1 hψ)) (GlobalTheory.T.sum_irrChar_one_mul_irrChar_column_orthogonality A hA)
      (fun ψ hψ x => GlobalTheory.T.classFunction_acts_by_scalar_on_irrChar e (coeff_conj_of_center hcen) ψ ((hA ψ).1 hψ) x) hid
    have himg : (A.filter fun ψ => ∑ g, e.coeff g * ψ g = ψ 1) =
        (Formalism.L2.Col.XgE σ e).image (fun χ g => σ (χ g)) := by
      ext ψ
      simp only [Finset.mem_filter, Finset.mem_image, hA, Formalism.L2.Col.mem_XgE]
      constructor
      · rintro ⟨hψ, hs⟩
        obtain ⟨χ, hχ, hχψ⟩ := GlobalTheory.T.absIrrChar_realise_of_primitiveRoot_card σ z hzp ψ hψ
        refine ⟨χ, ⟨hχ, ?_⟩, funext hχψ⟩
        simp only [hχψ]
        exact hs
      · rintro ⟨χ, ⟨hχ, hs⟩, rfl⟩
        exact ⟨GlobalTheory.T.absIrrChar_comp_mem_complexIrrCharSet σ χ hχ, hs⟩
    have hinj : Set.InjOn (fun (χ : Gc X.B px → X.B.LL) g => σ (χ g)) (Formalism.L2.Col.XgE σ e : Set _) :=
      fun χ _ χ' _ h => funext fun g => σ.injective (congrFun h g)
    rw [← hcoeff g]
    conv_rhs => rw [hexp]
    rw [himg, coeff_idemOf, coeff_idemOf, Finset.sum_image hinj, map_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    simp [σ, map_div₀, map_mul, map_natCast]
  · rw [coeff_idemOf]
    have hcl : ∀ y ∈ Subring.closure ({z} : Set X.B.LL), y ∈ X.B.Ks := fun y hy => by
      have : Subring.closure ({z} : Set X.B.LL) ≤ X.B.Ks.toSubfield.toSubring := by
        rw [Subring.closure_le, Set.singleton_subset_iff]
        exact hzK
      exact this hy
    refine IntermediateField.sum_mem _ fun χ hχ => ?_
    have hχ' := Formalism.L2.Col.XgE_irr χ hχ
    exact IntermediateField.mul_mem _ (IntermediateField.div_mem _ (hcl _ (GlobalTheory.T.absIrrChar_mem_closure_primitiveRoot_card z hzp χ hχ' 1))
      (IntermediateField.natCast_mem _ _)) (hcl _ (GlobalTheory.T.absIrrChar_mem_closure_primitiveRoot_card z hzp χ hχ' _))

end Record

end GlobalTheory.Mem.R3.GoodSetExists

end
