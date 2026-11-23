import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

theorem UpperTheory.Gal.productCup_of_system.fixZ_of :
    ValBasic → RYBasic → FixZ := by
  intro hV hR F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A h e he
  have hmem : ∀ b ∈ rB ℂ K (xv x) {0}, algebraMap K K' b ∈ rB ℂ K' (xv x) {0} :=
    fun b hb => ((hR F K K' d x j2 h.toY0).2.2.2.1 {0} b hb).1
  let ι : rB ℂ K (xv x) {0} →ₐ[ℂ] rB ℂ K' (xv x) {0} :=
    ((IsScalarTower.toAlgHom ℂ K K').comp (rB ℂ K (xv x) {0}).val).codRestrict _ fun b => hmem b b.2
  have hι : ∀ (b : K) (hb : b ∈ rB ℂ K (xv x) {0}), (e.1.comp ι) ⟨b, hb⟩ = e.1 ⟨_, hmem b hb⟩ :=
    fun _ _ => rfl
  refine ⟨⟨e.1.comp ι, fun j => ?_⟩, ?_⟩
  · rw [hι]
    refine Eq.trans ?_ (e.2 j)
    congr 2
    exact (IsScalarTower.algebraMap_apply F K K' _).symm
  rintro v c ⟨b, hb, hbv, hzb, hz⟩
  rw [hι] at hzb
  rw [hι, hι] at hz
  have h1b := hmem b hb
  have h1bv := hmem _ hbv
  constructor
  · have hm : algebraMap K K' b * algebraMap K K' v ∈ rB ℂ K' (xv x) {0} := by
      rw [← map_mul]; exact h1bv
    refine ⟨_, h1b, hm, hzb, ?_⟩
    rw [← hz]
    congr 2
    exact (map_mul _ _ _).symm
  · have fix := (h.fx e).1 he
    obtain ⟨-, ⟨ev, hev⟩, -, hinv⟩ := hV K' (rB ℂ K' (xv x) {0}) e.1
    have v1 := fix b hb h1b
    have v2 := fix _ hbv h1bv
    obtain ⟨m1, hm1⟩ := (hev _ _).1 v1
    obtain ⟨m2, hm2⟩ := (hev _ _).1 v2
    obtain ⟨hne, hi⟩ := hinv _ _ v1 hzb
    have hv : j2 v = (j2 b)⁻¹ * j2 (b * v) := by
      rw [map_mul, inv_mul_cancel_left₀ hne]
    have hl : j2 v ∈ loc (rB ℂ K' (xv x) {0}) e.1 := by
      rw [hv]; exact mul_mem hi m2
    refine (hev _ _).2 ⟨hl, ?_⟩
    have hmul : (⟨j2 b, m1⟩ : loc (rB ℂ K' (xv x) {0}) e.1) * ⟨j2 v, hl⟩ = ⟨j2 (b * v), m2⟩ :=
      Subtype.ext (map_mul j2 b v).symm
    have := congrArg ev hmul
    rw [map_mul, hm1, hm2, hz] at this
    exact mul_left_cancel₀ hzb this
