import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreExtra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing blockWeight IsMultiHomog IsMultiProjPrime gradedPiece hilbFn intNum
  genFib)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

namespace GenFibNef

section Transport

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {F₁ F₂ : Type} [Field F₁] [Field F₂] (e : F₁ ≃+* F₂)

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem isMultiHomog_map_iff (f : MRing ι F₁) (b : K → ℕ) :
    IsMultiHomog (map (e : F₁ →+* F₂) f) b ↔ IsMultiHomog f b := by
  unfold IsMultiHomog IsWeightedHomogeneous
  simp only [coeff_map, ne_eq, RingHom.coe_coe, EmbeddingLike.map_eq_zero_iff]

noncomputable def quotEquiv (P : Ideal (MRing ι F₁)) :
    (MRing ι F₁ ⧸ P) ≃+* (MRing ι F₂ ⧸ P.map (map (e : F₁ →+* F₂))) :=
  Ideal.quotientEquiv P _ (mapEquiv (Σ k, ι k) e) (by
    congr 1)

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem quotEquiv_mk (P : Ideal (MRing ι F₁)) (f : MRing ι F₁) :
    quotEquiv e P (Ideal.Quotient.mk P f) = Ideal.Quotient.mk _ (map (e : F₁ →+* F₂) f) := rfl

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem quotEquiv_smul (P : Ideal (MRing ι F₁)) (r : F₁) (x : MRing ι F₁ ⧸ P) :
    quotEquiv e P (r • x) = e r • quotEquiv e P x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h₁ : r • Ideal.Quotient.mk P f = Ideal.Quotient.mk P (C r * f) := by
    rw [← Ideal.Quotient.mkₐ_eq_mk F₁, ← map_smul, smul_eq_C_mul]
  have h₂ : e r • Ideal.Quotient.mk (P.map (map (e : F₁ →+* F₂))) (map (e : F₁ →+* F₂) f) =
      Ideal.Quotient.mk (P.map (map (e : F₁ →+* F₂))) (C (e r) * map (e : F₁ →+* F₂) f) := by
    rw [← Ideal.Quotient.mkₐ_eq_mk F₂, ← map_smul, smul_eq_C_mul]
  rw [h₁, quotEquiv_mk, quotEquiv_mk, h₂, map_mul, map_C]
  rfl

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem quotEquiv_mem_gradedPiece (P : Ideal (MRing ι F₁)) (n : K → ℕ) (x : MRing ι F₁ ⧸ P)
    (hx : x ∈ gradedPiece P n) : quotEquiv e P x ∈ gradedPiece (P.map (map (e : F₁ →+* F₂))) n := by
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hx
  refine Submodule.mem_map.2 ⟨map (e : F₁ →+* F₂) f, ?_, rfl⟩
  rw [mem_weightedHomogeneousSubmodule] at hf ⊢
  exact (isMultiHomog_map_iff e f n).2 hf

theorem finrank_gradedPiece_map (P : Ideal (MRing ι F₁)) (n : K → ℕ) :
    Module.finrank F₂ (gradedPiece (P.map (map (e : F₁ →+* F₂))) n) =
      Module.finrank F₁ (gradedPiece P n) := by
  let j₀ : gradedPiece P n →+ gradedPiece (P.map (map (e : F₁ →+* F₂))) n :=
    { toFun := fun x => ⟨quotEquiv e P x.1, quotEquiv_mem_gradedPiece e P n x.1 x.2⟩
      map_zero' := Subtype.ext (map_zero (quotEquiv e P))
      map_add' := fun a b => Subtype.ext (map_add (quotEquiv e P) a.1 b.1) }
  have hinj : Function.Injective j₀ := fun a b h =>
    Subtype.ext ((quotEquiv e P).injective (congrArg Subtype.val h))
  have hsurj : Function.Surjective j₀ := by
    rintro ⟨z, hz⟩
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.1 hz
    have hg' : map (e.symm : F₂ →+* F₁) g ∈ weightedHomogeneousSubmodule F₁ (blockWeight ι) n := by
      rw [mem_weightedHomogeneousSubmodule] at hg ⊢
      have hgg : map (e : F₁ →+* F₂) (map (e.symm : F₂ →+* F₁) g) = g :=
        (mapEquiv (Σ k, ι k) e).apply_symm_apply g
      have h' : IsMultiHomog (map (e : F₁ →+* F₂) (map (e.symm : F₂ →+* F₁) g)) n := by
        rw [hgg]
        exact hg
      exact (isMultiHomog_map_iff e _ n).1 h'
    refine ⟨⟨Ideal.Quotient.mk P (map (e.symm : F₂ →+* F₁) g), Submodule.mem_map.2 ⟨_, hg', rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change quotEquiv e P (Ideal.Quotient.mk P (map (e.symm : F₂ →+* F₁) g)) = Ideal.Quotient.mk _ g
    rw [quotEquiv_mk]
    congr 1
    exact (mapEquiv (Σ k, ι k) e).apply_symm_apply g
  let j := AddEquiv.ofBijective j₀ ⟨hinj, hsurj⟩
  have hrank := rank_eq_of_equiv_equiv (e : F₁ → F₂) j e.bijective (fun r m => by
    apply Subtype.ext
    exact quotEquiv_smul e P r m)
  unfold Module.finrank
  rw [hrank]

theorem hilbFn_map (P : Ideal (MRing ι F₁)) :
    hilbFn (P.map (map (e : F₁ →+* F₂))) = hilbFn P := by
  funext m
  unfold hilbFn
  split_ifs
  · rw [finrank_gradedPiece_map]
  · rfl

theorem intNum_map (P : Ideal (MRing ι F₁)) {n : ℕ} (bs : Fin n → K → ℤ) :
    intNum F₂ (P.map (map (e : F₁ →+* F₂))) bs = intNum F₁ P bs := by
  unfold intNum
  rw [hilbFn_map]

end Transport

end GenFibNef

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
