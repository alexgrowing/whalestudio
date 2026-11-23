import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMulTrInv
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.FewEq.Cochain

theorem triple_mem {B : Type*} [CommRing B] {𝔞 𝔟 : Ideal B} (h𝔟 : 𝔟 * 𝔟 ≤ 𝔞) (h𝔞 : 𝔞 ≤ 𝔟)
    {ua uc ud wc wd g₁ g₂ g₃ h₁ h₂ h₃ : B} (hc : uc * wc - 1 ∈ 𝔞) (hd : ud * wd - 1 ∈ 𝔞)
    (e₁ : ua - g₁ * uc ∈ 𝔟) (e₂ : uc - g₂ * ud ∈ 𝔟) (hg : g₁ * g₂ = g₃)
    (i₁ : g₁ * h₁ = 1) (i₂ : g₂ * h₂ = 1) (i₃ : g₃ * h₃ = 1) :
    (ua - g₁ * uc) * h₁ * wc + (uc - g₂ * ud) * h₂ * wd - (ua - g₃ * ud) * h₃ * wd ∈ 𝔞 := by
  have hh : h₃ = h₁ * h₂ := by
    subst hg
    linear_combination (-(h₃ * g₂ * h₂)) * i₁ - h₃ * i₂ + (h₁ * h₂) * i₃
  have hm : wc - h₂ * wd ∈ 𝔟 := by
    have : wc - h₂ * wd = (wd * h₂) * (uc * wc - 1) - (wc * wd * h₂) * (uc - g₂ * ud)
        - wc * (ud * wd - 1) := by
      linear_combination (-(wc * wd * ud)) * i₂
    rw [this]
    exact 𝔟.sub_mem (𝔟.sub_mem (𝔟.mul_mem_left _ (h𝔞 hc)) (𝔟.mul_mem_left _ e₂))
      (𝔟.mul_mem_left _ (h𝔞 hd))
  have : (ua - g₁ * uc) * h₁ * wc + (uc - g₂ * ud) * h₂ * wd - (ua - g₃ * ud) * h₃ * wd =
      h₁ * ((ua - g₁ * uc) * (wc - h₂ * wd)) := by
    subst hg hh
    linear_combination ((uc - g₂ * ud) * h₂ * wd) * (-i₁)
  rw [this]
  exact 𝔞.mul_mem_left _ (h𝔟 (Ideal.mul_mem_mul e₁ hm))

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem rs_cst (s : X ⟶ Sp R) {U W : X.Opens} (h : W ≤ U) (x : R) :
    rs X h (GlobalTheory.SmallExtLift.cst s U x) = GlobalTheory.SmallExtLift.cst s W x := by
  refine GlobalTheory.SmallExtLift.gr_ext fun y hy => ?_
  have e := GlobalTheory.SmallExtLift.gr_res (𝟙 X) y h hy (GlobalTheory.SmallExtLift.cst s U x)
  exact e.trans (by rw [GlobalTheory.SmallExtLift.gr_cst, GlobalTheory.SmallExtLift.gr_cst])

theorem rs_mem_ext (s : X ⟶ Sp R) (J : Ideal R) {U W : X.Opens} (h : W ≤ U) {x : Γ(X, U)}
    (hx : x ∈ ext s J U) : rs X h x ∈ ext s J W := by
  have e : (ext s J U).map (rs X h) = ext s J W := by
    rw [ext, ext, Ideal.map_map]
    congr 1
    exact RingHom.ext fun r => rs_cst s h r
  exact e ▸ Ideal.mem_map_of_mem _ hx

theorem ext_eq_span (s : X ⟶ Sp R) {I : Ideal R} {r : ℕ} {t : Fin r → R}
    (ht : Ideal.span (Set.range t) = I) (U : X.Opens) :
    ext s I U = Ideal.span (Set.range fun i => GlobalTheory.SmallExtLift.cst s U (t i)) := by
  rw [ext, ← ht, Ideal.map_span, ← Set.range_comp]
  rfl

theorem sum_cst_rs (s : X ⟶ Sp R) {r : ℕ} (t : Fin r → R) {U W : X.Opens} (h : W ≤ U)
    (f : Fin r → Γ(X, U)) :
    ∑ i, GlobalTheory.SmallExtLift.cst s W (t i) * rs X h (f i) =
      rs X h (∑ i, GlobalTheory.SmallExtLift.cst s U (t i) * f i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, rs_cst]

theorem exists_cochain : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (𝔪 I : Ideal R) (r : ℕ) (t : Fin r → R),
    Ideal.span (Set.range t) = I → I ≤ 𝔪 → ∀ (M : LB X), M.IsLB →
    ∀ (A : Type) (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)) (u w : ∀ a, Γ(X, V a)),
      (∀ a, u a * w a - 1 ∈ ext s (𝔪 * I) (V a)) →
      (∀ a c, rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c) ∈ ext s I (V a ⊓ V c)) →
      ∃ b : Fin r → ∀ a c, Γ(X, V a ⊓ V c),
        (∀ a c d, ∑ i, GlobalTheory.SmallExtLift.cst s _ (t i) * (rs X (le₁₂ V a c d) (b i a c) +
            rs X (le₂₃ V a c d) (b i c d) - rs X (le₁₃ V a c d) (b i a d)) ∈ ext s (𝔪 * I) (V a ⊓ V c ⊓ V d)) ∧
        ∀ a c, rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c) *
          (1 + ∑ i, GlobalTheory.SmallExtLift.cst s _ (t i) * b i a c) ∈ ext s (𝔪 * I) (V a ⊓ V c) := by
  intro R _ X s 𝔪 I r t ht hI M hM A V j hj u w huw he
  have key : ∀ a c, ∃ b0 : Fin r → Γ(X, V a ⊓ V c),
      ∑ i, b0 i * GlobalTheory.SmallExtLift.cst s _ (t i) =
        rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c) := by
    intro a c
    have := he a c
    rw [ext_eq_span s ht] at this
    exact (Ideal.mem_span_range_iff_exists_fun).1 this
  choose b0 hb0 using key
  have hT : ∀ a c, ∑ i, GlobalTheory.SmallExtLift.cst s _ (t i) *
      (b0 a c i * trInv M V j hj a c * rs X inf_le_right (w c)) =
      (rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c)) *
        trInv M V j hj a c * rs X inf_le_right (w c) := by
    intro a c
    rw [← hb0, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine ⟨fun i a c => b0 a c i * trInv M V j hj a c * rs X inf_le_right (w c), ?_, ?_⟩
  · intro a c d
    have h𝔟 : ∀ U : X.Opens, ext s I U * ext s I U ≤ ext s (𝔪 * I) U := fun U => by
      rw [ext, ← Ideal.map_mul]
      exact Ideal.map_mono (Ideal.mul_mono_left hI)
    have h𝔞 : ∀ U : X.Opens, ext s (𝔪 * I) U ≤ ext s I U := fun U =>
      Ideal.map_mono Ideal.mul_le_right
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_cst_rs, hT]
    have i₁ := congrArg (rs X (le₁₂ V a c d)) (tr_mul_trInv M V j hj a c)
    have i₂ := congrArg (rs X (le₂₃ V a c d)) (tr_mul_trInv M V j hj c d)
    have i₃ := congrArg (rs X (le₁₃ V a c d)) (tr_mul_trInv M V j hj a d)
    rw [map_mul, map_one] at i₁ i₂ i₃
    have hU : ∀ x {W : X.Opens} (h : W ≤ V x),
        rs X h (u x) * rs X h (w x) - 1 ∈ ext s (𝔪 * I) W := fun x W h => by
      simpa only [map_sub, map_mul, map_one] using rs_mem_ext s (𝔪 * I) h (huw x)
    have := triple_mem (h𝔟 (V a ⊓ V c ⊓ V d)) (h𝔞 _)
      (hU c (inf_le_left.trans inf_le_right)) (hU d inf_le_right)
      (by simpa only [map_sub, map_mul, GlobalTheory.AbLaw.rs_rs] using rs_mem_ext s I (le₁₂ V a c d) (he a c))
      (by simpa only [map_sub, map_mul, GlobalTheory.AbLaw.rs_rs] using rs_mem_ext s I (le₂₃ V a c d) (he c d))
      (tr_cocycle hM V j hj a c d) i₁ i₂ i₃
    simpa only [map_sub, map_mul, map_add, map_one, GlobalTheory.AbLaw.rs_rs] using this
  · intro a c
    simp only [hT]
    have hx := rs_mem_ext s (𝔪 * I) (inf_le_right : V a ⊓ V c ≤ V c) (huw c)
    rw [map_sub, map_mul, map_one] at hx
    have e : rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c) *
        (1 + (rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c)) *
          trInv M V j hj a c * rs X inf_le_right (w c)) =
        -(rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c)) *
          (rs X inf_le_right (u c) * rs X inf_le_right (w c) - 1) := by
      linear_combination (-(rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c)) *
        rs X inf_le_right (u c) * rs X inf_le_right (w c)) * tr_mul_trInv M V j hj a c
    rw [e]
    exact Ideal.mul_mem_left _ _ hx

end GlobalTheory.CompanionTheory.FewEq.Cochain
