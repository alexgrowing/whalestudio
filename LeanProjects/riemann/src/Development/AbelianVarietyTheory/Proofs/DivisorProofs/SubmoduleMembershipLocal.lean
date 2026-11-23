import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiMapMemLocalSpan
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent GlobalTheory.LatGlue
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG)

set_option autoImplicit false

namespace GlobalTheory.LatGlue

theorem exists_pow_smul_mem_of_mem_span_away {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (r : A)
    [IsLocalization.Away r B] {h : ℕ} (T : Submodule A (Fin h → A)) (v : Fin h → A)
    (hv : piMap (algebraMap A B) (Fin h) v ∈
      Submodule.span B (piMap (algebraMap A B) (Fin h) '' (T : Set (Fin h → A)))) :
    ∃ n : ℕ, r ^ n • v ∈ T := by
  have key : ∀ w ∈ Submodule.span B (piMap (algebraMap A B) (Fin h) '' (T : Set (Fin h → A))),
      ∃ (n : ℕ) (t : Fin h → A), t ∈ T ∧
        algebraMap A B (r ^ n) • w = piMap (algebraMap A B) (Fin h) t := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      exact ⟨0, t, ht, by simp⟩
    | zero => exact ⟨0, 0, T.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, t, ht, e⟩ := hx
      obtain ⟨m, s, hs, e'⟩ := hy
      refine ⟨n + m, r ^ m • t + r ^ n • s, add_mem (T.smul_mem _ ht) (T.smul_mem _ hs), ?_⟩
      rw [map_add, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, ← e, ← e', smul_smul, smul_smul, smul_add,
        ← map_mul, ← map_mul, pow_add, mul_comm (r ^ m)]
    | smul b x _ hx =>
      obtain ⟨n, t, ht, e⟩ := hx
      obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, hb⟩ := IsLocalization.surj (Submonoid.powers r) b
      simp only at hb
      refine ⟨n + m, a • t, T.smul_mem _ ht, ?_⟩
      rw [LinearMap.map_smulₛₗ, ← e, ← hb, smul_smul, smul_smul, pow_add, map_mul]
      congr 1
      ring
  obtain ⟨n, t, ht, e⟩ := key _ hv
  have hc : ∀ l : Fin h, ∃ m : ℕ, r ^ m * (r ^ n * v l) = r ^ m * t l := by
    intro l
    have el : algebraMap A B (r ^ n * v l) = algebraMap A B (t l) := by
      have := congrFun e l
      simpa using this
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers r) B).1 el
    exact ⟨m, hm⟩
  choose m hm using hc
  refine ⟨∑ l, m l + n, ?_⟩
  have : r ^ (∑ l, m l + n) • v = r ^ (∑ l, m l) • t := by
    funext l
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le
      (Finset.single_le_sum (f := m) (fun i _ => Nat.zero_le (m i)) (Finset.mem_univ l))
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hk, pow_add, pow_add]
    linear_combination r ^ k * hm l
  rw [this]
  exact T.smul_mem _ ht

theorem mem_of_locally_mem_span_res :
    ∀ (Y : Scheme.{0}) (h : ℕ) (W : Y.Opens), IsAffineOpen W → ∀ (T : Submodule Γ(Y, W) (Fin h → Γ(Y, W))) (v : Fin h → Γ(Y, W)), (∀ y ∈ W, ∃ (W' : Y.Opens) (hle : W' ≤ W), y ∈ W' ∧ piMap (resG Y hle) (Fin h) v ∈ Submodule.span Γ(Y, W') (piMap (resG Y hle) (Fin h) '' (T : Set (Fin h → Γ(Y, W))))) → v ∈ T := by
  intro Y h W hW T v H
  have H' : ∀ y ∈ W, ∃ r : Γ(Y, W), y ∈ Y.basicOpen r ∧ ∃ n : ℕ, r ^ n • v ∈ T := by
    intro y hy
    obtain ⟨W', hle, hy', hm⟩ := H y hy
    obtain ⟨r, hr, hyr⟩ := hW.exists_basicOpen_le (V := W') ⟨y, hy'⟩ hy
    refine ⟨r, hyr, ?_⟩
    haveI := hW.isLocalization_basicOpen r
    have halg : algebraMap Γ(Y, W) Γ(Y, Y.basicOpen r) = resG Y (Y.basicOpen_le r) := rfl
    apply exists_pow_smul_mem_of_mem_span_away (B := Γ(Y, Y.basicOpen r)) r T v
    rw [halg]
    have comp : ∀ u : Fin h → Γ(Y, W), piMap (resG Y hr) (Fin h) (piMap (resG Y hle) (Fin h) u) =
        piMap (resG Y (Y.basicOpen_le r)) (Fin h) u := fun u => funext fun l => by
      simp only [piMap_apply]
      exact GlobalTheory.LB.resG_resG hle hr (u l)
    have gen : ∀ w ∈ Submodule.span Γ(Y, W') (piMap (resG Y hle) (Fin h) '' (T : Set (Fin h → Γ(Y, W)))),
        piMap (resG Y hr) (Fin h) w ∈ Submodule.span Γ(Y, Y.basicOpen r)
          (piMap (resG Y (Y.basicOpen_le r)) (Fin h) '' (T : Set (Fin h → Γ(Y, W)))) := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨t, ht, rfl⟩ := hx
        exact Submodule.subset_span ⟨t, ht, (comp t).symm⟩
      | zero => simp
      | add x y _ _ hx hy => simpa using add_mem hx hy
      | smul a x _ hx =>
        rw [LinearMap.map_smulₛₗ]
        exact Submodule.smul_mem _ _ hx
    rw [← comp]
    exact gen _ hm
  let s : Set Γ(Y, W) := {r | ∃ n : ℕ, r ^ n • v ∈ T}
  have hs : Ideal.span s = ⊤ := by
    rw [← hW.self_le_iSup_basicOpen_iff]
    intro y hy
    obtain ⟨r, hyr, hr⟩ := H' y hy
    simp only [TopologicalSpace.Opens.mem_iSup, SetLike.mem_coe]
    exact ⟨⟨r, hr⟩, hyr⟩
  exact Submodule.mem_of_span_eq_top_of_smul_pow_mem T s hs v fun r => r.2

end GlobalTheory.LatGlue
