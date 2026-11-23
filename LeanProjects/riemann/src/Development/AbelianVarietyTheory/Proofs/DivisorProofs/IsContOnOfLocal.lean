import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

namespace GlobalTheory.WeilCont

variable (F : Type) [Field F] [NumberField F] {κ : Type}

def adeleJoin (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) : κ → AdeleRing (𝓞 F) F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i)

theorem pureA_adeleJoin (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilM.pureA F f g (adeleJoin F x y) = f x * g y := by
  simp [GlobalTheory.WeilM.pureA, adeleJoin]

theorem exists_slice [Fintype κ] {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ)
    (y : κ → FiniteAdeleRing (𝓞 F) F) :
    ∃ s : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∀ x, s x = Φ (adeleJoin F x y) := by
  unfold GlobalTheory.WeilM.schA at hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, -, rfl⟩ := h
    exact ⟨g y • f, fun x => by rw [smul_apply, pureA_adeleJoin, smul_eq_mul, mul_comm]⟩
  | zero => exact ⟨0, fun x => by simp⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨s1, hs1⟩ := h1
    obtain ⟨s2, hs2⟩ := h2
    exact ⟨s1 + s2, fun x => by rw [add_apply, hs1, hs2]; rfl⟩
  | smul c Φ _ h =>
    obtain ⟨s, hs⟩ := h
    exact ⟨c • s, fun x => by rw [smul_apply, hs]; rfl⟩

theorem isContOn_of_local [Fintype κ] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] {G : Type} [Group G] [TopologicalSpace G]
    {om : G →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ)}
    (hfin : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ p0 : G, ∃ N ∈ nhds p0, ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
      (y : Fin m → κ → FiniteAdeleRing (𝓞 F) F),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (y j) = if i = j then 1 else 0) ∧
      ∀ p ∈ N, ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, om p Φ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i))
    (hsl : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ y : κ → FiniteAdeleRing (𝓞 F) F,
      ∃ s : G → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, Continuous s ∧ ∀ p x, s p x = om p Φ (adeleJoin F x y)) :
    GlobalTheory.WeilM.IsContOn (GlobalTheory.WeilM.adeleClass F) om := by
  intro l hl φ hφ
  change φ ∈ GlobalTheory.WeilM.schA F κ at hφ
  change ∀ g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F),
    ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, l (GlobalTheory.WeilM.pureA F f g) = T f at hl
  rw [continuous_iff_continuousAt]
  intro p0
  obtain ⟨N, hN, m, g, y, hgSB, hgy, hrep⟩ := hfin φ hφ p0
  choose T hT using fun i => hl (g i) (hgSB i)
  choose s hs hsx using fun j => hsl φ hφ (y j)
  have hcont : Continuous fun p => ∑ i, T i (s i p) :=
    continuous_finsetSum _ (fun i _ => (T i).continuous.comp (hs i))
  refine hcont.continuousAt.congr ?_
  filter_upwards [hN] with p hp
  obtain ⟨f, hf⟩ := hrep p hp
  have hfs : ∀ j, f j = s j p := by
    intro j
    ext x
    rw [hsx, hf, Finset.sum_apply, Finset.sum_eq_single j]
    · rw [pureA_adeleJoin, hgy j j, if_pos rfl, mul_one]
    · intro i _ hij
      rw [pureA_adeleJoin, hgy i j, if_neg hij, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [hf, map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [hT, hfs])

end GlobalTheory.WeilCont

end
