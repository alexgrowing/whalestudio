import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDimLeOfFiniteAndOfSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfIsFiniteOfDimEqAbelianVarietyHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorisationThroughAbelianSubvarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInverseIsogenyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteOfSurjectiveOfDimEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleFreeFinrankTwoMulDimStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar.IsogTate

variable {K : Type} [Field K] (l : ℕ) [Fact l.Prime]

theorem vmap_comp' {A B C : AbVar K} (f : A ⟶ B) (g : B ⟶ C) :
    vmap l (f ≫ g) = vmap l g ∘ₗ vmap l f := by
  simp only [vmap, tmap_comp, LinearMap.baseChange_comp]

theorem vmap_nsmul_id (A : AbVar K) (n : ℕ) (x : Vl l A) :
    vmap l (n • 𝟙 A) x = (n : ℚ_[l]) • x := by
  have h1 : tmap l A A (n • 𝟙 A) = (n : ℤ_[l]) • LinearMap.id := by
    rw [map_nsmul, tmap_id, Nat.cast_smul_eq_nsmul]
  rw [vmap, h1, LinearMap.baseChange_smul, LinearMap.baseChange_id]
  rw [LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem tmap_injective_of_finite_ker {A B : AbVar K} (f : A ⟶ B) (hG : Finite (ptMap f).ker) :
    Function.Injective (tmap l A B f) := by
  have hp : l.Prime := Fact.out
  set N := Nat.card (ptMap f).ker with hN
  have hN0 : 0 < N := Nat.card_pos
  have hx : ∀ x ∈ (ptMap f).ker, x ^ N = 1 := fun x hx => by
    have := pow_card_eq_one' (G := (ptMap f).ker) (x := ⟨x, hx⟩)
    exact congrArg Subtype.val this
  refine (injective_iff_map_eq_zero _).2 fun t ht => Tate.ext fun n => ?_
  have hmem : ∀ m, t.lev m ∈ (ptMap f).ker := fun m => by
    rw [MonoidHom.mem_ker, ptMap_apply, ← lev_tmap l f t m, ht]
    rfl
  have h1 : t.lev (n + N) ^ l ^ (n + N) = 1 := t.lev_pow _
  have h2 : t.lev (n + N) ^ N = 1 := hx _ (hmem _)
  have h3 : t.lev (n + N) ^ Nat.gcd (l ^ (n + N)) N = 1 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow hp).1 (Nat.gcd_dvd_left (l ^ (n + N)) N)
  have h4 : l ^ j ≤ N := hj' ▸ Nat.le_of_dvd hN0 (Nat.gcd_dvd_right _ _)
  have h5 : j < N := lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt) h4
  have h6 : t.lev (n + N) ^ l ^ N = 1 := by
    obtain ⟨c, hc⟩ := pow_dvd_pow l h5.le
    rw [hc, pow_mul, ← hj', h3, one_pow]
  show t.lev n = 1
  rw [← t.lev_add_pow n N]
  exact h6

theorem isFinite_of_tmap_injective (hl : (l : K) ≠ 0) {A B : AbVar K} (f : A ⟶ B)
    (hf : Function.Injective (tmap l A B f)) : IsFinite f.hom.left := by
  obtain ⟨C, p, i, hp, hi, rfl⟩ := GlobalTheory.T.exists_factorisation_through_abelianSubvariety K A B f
  have hpi : Function.Injective (tmap l A C p) := by
    rw [tmap_comp, LinearMap.coe_comp] at hf
    exact hf.of_comp
  obtain ⟨hA1, hA2, hA3, -, -⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl A
  obtain ⟨hC1, hC2, hC3, -, -⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl C
  have h1 : 2 * A.dim ≤ 2 * C.dim := by
    rw [← hA3, ← hC3]
    exact LinearMap.finrank_le_finrank_of_injective hpi
  have h2 : C.dim ≤ A.dim := (GlobalTheory.T.abelianVariety_dim_le_of_finite_and_of_surjective K A C p).2 hp
  have h3 : A.dim = C.dim := le_antisymm (by omega) h2
  have hpf : IsFinite p.hom.left := GlobalTheory.T.isFinite_of_surjective_of_dim_eq' K A C p h3 hp
  haveI := hi
  rw [comp_hom, Over.comp_left]
  infer_instance

theorem tmap_injective_of_vmap_injective (hl : (l : K) ≠ 0) {A B : AbVar K} (f : A ⟶ B)
    (hv : Function.Injective (vmap l f)) : Function.Injective (tmap l A B f) := by
  obtain ⟨hA1, -, -, -, -⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl A
  obtain ⟨hB1, -, -, -, -⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl B
  have hinj : ∀ (X : AbVar K) [Module.Free ℤ_[l] (Tl l X)],
      Function.Injective (fun t : Tl l X => (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] t) := by
    intro X _
    have h := Module.Flat.rTensor_preserves_injective_linearMap (M := Tl l X)
      (Algebra.linearMap ℤ_[l] ℚ_[l]) (IsFractionRing.injective ℤ_[l] ℚ_[l])
    intro s t hst
    apply (TensorProduct.lid ℤ_[l] (Tl l X)).symm.injective
    apply h
    simpa using hst
  intro s t hst
  apply hinj A
  apply hv
  simp only [vmap, LinearMap.baseChange_tmul, hst]

theorem vmap_bijective_of_isIsogeny {A B : AbVar K} (f : A ⟶ B) (hf : IsIsogeny f) :
    Function.Bijective (vmap l f) := by
  obtain ⟨n, g, hn, -, hfg, hgf⟩ := GlobalTheory.T.exists_quasiInverse_isogeny' K A B f hf
  have hn' : (n : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hb : ∀ (X : AbVar K), Function.Bijective (vmap l (n • 𝟙 X)) := fun X => by
    constructor
    · intro x y h
      rw [vmap_nsmul_id, vmap_nsmul_id] at h
      exact smul_right_injective _ hn' h
    · intro y
      exact ⟨(n : ℚ_[l])⁻¹ • y, by rw [vmap_nsmul_id, smul_smul, mul_inv_cancel₀ hn', one_smul]⟩
  refine ⟨?_, ?_⟩
  · have h := (hb A).1
    rw [← hfg, vmap_comp', LinearMap.coe_comp] at h
    exact h.of_comp
  · have h := (hb B).2
    rw [← hgf, vmap_comp', LinearMap.coe_comp] at h
    exact h.of_comp

end GlobalTheory.AV.AbVar.IsogTate

namespace GlobalTheory.AV.AbVar

open IsogTate in

theorem isFinite_iff_tmap_injective_and_isIsogeny_iff_vmap_bijective : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime],
    (l : K) ≠ 0 → ∀ (A B : AbVar K) (f : A ⟶ B),
    (IsFinite f.hom.left ↔ Function.Injective (tmap l A B f)) ∧ (IsIsogeny f ↔ Function.Bijective (vmap l f)) := by
  intro K _ l _ hl A B f
  have h1 : IsFinite f.hom.left ↔ Function.Injective (tmap l A B f) :=
    ⟨fun h => tmap_injective_of_finite_ker l f ((GlobalTheory.T.isFinite_iff_finite_ker' K A B f).1 h), isFinite_of_tmap_injective l hl f⟩
  refine ⟨h1, fun h => vmap_bijective_of_isIsogeny l f h, fun h => ?_⟩
  have hfin := h1.2 (tmap_injective_of_vmap_injective l hl f h.1)
  obtain ⟨-, -, -, hA4, hA5⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl A
  obtain ⟨-, -, -, hB4, hB5⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl B
  have hd : 2 * A.dim = 2 * B.dim := by
    rw [← hA5, ← hB5]
    exact (LinearEquiv.ofBijective _ h).finrank_eq
  exact ⟨hfin, GlobalTheory.T.surjective_of_isFinite_of_dim_eq_abelianVarietyHom K A B f (by omega) hfin⟩

end GlobalTheory.AV.AbVar
