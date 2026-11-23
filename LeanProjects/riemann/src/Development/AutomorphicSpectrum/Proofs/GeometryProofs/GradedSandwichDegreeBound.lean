import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt

theorem cls_frame : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (a : K → ℤ) (e₀ : Ω),
    LinearIndependent Ω b₀ → Sandwich M V b₀ m → (V.gr b₀ i).IsDegOn Set.univ y a e₀ →
    ∀ (p : Cpt ξ) (c : (k : K) → J k), InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p →
    ∃ (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li) (κ : Ω), (∀ n : ℕ, flagStep Ω b n = flagStep Ω b₀ n) ∧
      V.IsFrameAt b p ∧ (∀ j, (m : Ω) • b j ∈ M.lat p) ∧ (∀ j l, π j (b l) = if j = l then 1 else 0) ∧
      (∀ j, ∀ e ∈ M.lat p, (m : Ω) * π j e ∈ regAt ξ p) ∧ κ ≠ 0 ∧ κ ∈ regAt ξ p ∧ κ⁻¹ ∈ regAt ξ p ∧
      ∀ (e : Li) (t : Ω), e ∈ flagStep Ω b₀ (i + 1) → IsCls b₀ i e t → t / gen y a e₀ c = π i e * κ := by
  intro X Ω _ ξ K _ J y G _ Li _ _ M V r b₀ m i a e₀ _hb₀ hS hD p c hc
  obtain ⟨b, π, hf, hfr, hm, hπ, hr⟩ := hS p

  have hker : flagStep Ω b₀ i ≤ LinearMap.ker (π i) := by
    rw [← hf]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    have hne : i ≠ k := by
      rintro rfl
      simp at hk
    simp [hπ, hne]
  have hkill : ∀ (e : Li) (t : Ω), e - t • b₀ i ∈ flagStep Ω b₀ i → π i e = t * π i (b₀ i) := by
    intro e t h
    have h1 : π i (e - t • b₀ i) = 0 := hker h
    simpa [sub_eq_zero] using h1

  have hbi : b i ∈ flagStep Ω b₀ (i + 1) := by
    rw [← hf]
    exact Submodule.subset_span ⟨i, by simp, rfl⟩
  rw [Flag.step_succ] at hbi
  obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.1 hbi
  obtain ⟨u', rfl⟩ := Submodule.mem_span_singleton.1 hw
  have hone : u' * π i (b₀ i) = 1 := by
    have h1 : π i (b i) = 1 := by simp [hπ]
    have h2 : π i z = 0 := hker hz
    rw [← hzw] at h1
    simpa [h2] using h1
  have hu' : u' ≠ 0 := left_ne_zero_of_mul_eq_one hone
  have hw0 : π i (b₀ i) ≠ 0 := right_ne_zero_of_mul_eq_one hone
  have hcls : b i - u' • b₀ i ∈ flagStep Ω b₀ i := by
    have : b i - u' • b₀ i = z := by rw [← hzw]; abel
    rw [this]; exact hz

  have hreg : ∀ e ∈ V p, π i e ∈ regAt ξ p := by
    intro e he
    rw [hfr.2] at he
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [hπ]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    | zero => simp [zero_mem]
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul s x _ hx =>
      have : π i (s • x) = (s : Ω) * π i x := (π i).map_smul (s : Ω) x
      rw [this]
      exact mul_mem s.2 hx

  have hgen : (V.gr b₀ i) p = Submodule.span (regAt ξ p) {u'} := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
    · rintro s ⟨e, he, hs⟩
      have h1 := hkill e s hs
      refine Submodule.mem_span_singleton.2 ⟨⟨π i e, hreg e he⟩, ?_⟩
      show π i e * u' = s
      rw [h1, _root_.mul_assoc, mul_comm (π i (b₀ i)), hone, _root_.mul_one]
    · rintro _ rfl
      exact ⟨b i, by rw [hfr.2]; exact Submodule.subset_span ⟨i, rfl⟩, hcls⟩
  have hdeg : (V.gr b₀ i) p = Submodule.span (regAt ξ p) {gen y a e₀ c} := by
    have := hD.2 p (Set.mem_univ p) c hc
    rw [this]
    rfl
  have hspan : Submodule.span (regAt ξ p) {u'} = Submodule.span (regAt ξ p) {gen y a e₀ c} := by
    rw [← hgen, hdeg]
  have a1 : u' ∈ Submodule.span (regAt ξ p) {gen y a e₀ c} := by
    rw [← hspan]; exact Submodule.mem_span_singleton_self _
  have a2 : gen y a e₀ c ∈ Submodule.span (regAt ξ p) {u'} := by
    rw [hspan]; exact Submodule.mem_span_singleton_self _
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.1 a1
  obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.1 a2
  have hα' : (α : Ω) * gen y a e₀ c = u' := hα
  have hβ' : (β : Ω) * u' = gen y a e₀ c := hβ
  have hg0 : gen y a e₀ c ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hα'
    exact hu' hα'.symm
  have hκ : u' / gen y a e₀ c = α := by
    rw [← hα']; field_simp
  have hκi : (u' / gen y a e₀ c)⁻¹ = β := by
    rw [inv_div, ← hβ']; field_simp
  refine ⟨b, π, u' / gen y a e₀ c, hf, hfr, hm, hπ, hr, div_ne_zero hu' hg0, ?_, ?_, ?_⟩
  · rw [hκ]; exact α.2
  · rw [hκi]; exact β.2
  · intro e t _ hcl
    have h1 := hkill e t hcl
    have h2 : t = π i e * u' := by
      rw [h1, _root_.mul_assoc, mul_comm (π i (b₀ i)), hone, _root_.mul_one]
    rw [h2, mul_div_assoc]

end GlobalTheory.CompanionTheory.Ar.RootHt
