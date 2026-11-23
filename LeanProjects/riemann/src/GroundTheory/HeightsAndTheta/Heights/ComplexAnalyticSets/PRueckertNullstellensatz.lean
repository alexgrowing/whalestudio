import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRueckertNullstellensatz
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticGermsNoetherian
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeGermNullstellensatz
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

namespace RueckertNullstellensatz

variable {σ : Type} [Fintype σ] {w : σ → ℂ}

theorem exists_of_mem_holGermIdeal {k : ℕ} (p : Fin k → (σ → ℂ) → ℂ) {φ : holGerms w}
    (hφ : φ ∈ holGermIdeal w p) :
    ∃ h : Fin k → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (h i) w) ∧
      (φ : Germ (𝓝 w) ℂ) = ((fun z => ∑ i, h i z * p i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) := by
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨i, hi⟩ := hφ
    refine ⟨fun j _ => if j = i then 1 else 0, fun j => analyticAt_const, ?_⟩
    rw [hi]
    congr 1
    funext z
    simp
  | zero =>
    refine ⟨fun _ _ => 0, fun _ => analyticAt_const, ?_⟩
    rw [show (fun z => ∑ i, (fun (_ : Fin k) (_ : σ → ℂ) => (0 : ℂ)) i z * p i z) = (0 : (σ → ℂ) → ℂ) by
      funext z; simp]
    rfl
  | add x y _ _ hx hy =>
    obtain ⟨h₁, hh₁, e₁⟩ := hx
    obtain ⟨h₂, hh₂, e₂⟩ := hy
    refine ⟨fun i z => h₁ i z + h₂ i z, fun i => (hh₁ i).add (hh₂ i), ?_⟩
    show (x : Germ (𝓝 w) ℂ) + y = _
    rw [e₁, e₂, ← Germ.coe_add]
    congr 1
    funext z
    simp [add_mul, Finset.sum_add_distrib]
  | smul a x _ hx =>
    obtain ⟨h, hh, e⟩ := hx
    obtain ⟨fa, hfa, efa⟩ : ∃ f : (σ → ℂ) → ℂ, AnalyticAt ℂ f w ∧ (f : Germ (𝓝 w) ℂ) = a := a.2
    refine ⟨fun i z => fa z * h i z, fun i => hfa.mul (hh i), ?_⟩
    show (a : Germ (𝓝 w) ℂ) * x = _
    rw [e, ← efa, ← Germ.coe_mul]
    congr 1
    funext z
    simp [Finset.mul_sum, mul_assoc]

theorem mem_holGermIdeal_of_eq {k : ℕ} {p : Fin k → (σ → ℂ) → ℂ} (hp : ∀ i, AnalyticAt ℂ (p i) w)
    {h : Fin k → (σ → ℂ) → ℂ} (hh : ∀ i, AnalyticAt ℂ (h i) w) (φ : holGerms w)
    (hφ : (φ : Germ (𝓝 w) ℂ) = ((fun z => ∑ i, h i z * p i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)) :
    φ ∈ holGermIdeal w p := by
  have hsum : φ = ∑ i, (⟨(h i : Germ (𝓝 w) ℂ), h i, hh i, rfl⟩ : holGerms w) *
      ⟨(p i : Germ (𝓝 w) ℂ), p i, hp i, rfl⟩ := by
    apply Subtype.ext
    rw [hφ, show (fun z => ∑ i, h i z * p i z : (σ → ℂ) → ℂ) = ∑ i, h i * p i by
      funext z; simp [Finset.sum_apply]]
    rw [show ((∑ i, h i * p i : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = Germ.coeRingHom (𝓝 w) (∑ i, h i * p i) from rfl,
      map_sum, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    rfl
  rw [hsum]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem proof (hNoeth : AnalyticGermsNoetherian.Statement) (hPrime : PrimeGermNullstellensatz.Statement) :
    RueckertNullstellensatz.Statement := by
  intro σ _ w k f g hf hg hvan
  let G : holGerms w := ⟨(g : Germ (𝓝 w) ℂ), g, hg, rfl⟩
  have : IsNoetherianRing (holGerms w) := hNoeth σ w

  have hrad : G ∈ (holGermIdeal w f).radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hfP, hP⟩
    obtain ⟨r, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian P)
    choose p hp hps using fun j => (show ∃ q : (σ → ℂ) → ℂ, AnalyticAt ℂ q w ∧ (q : Germ (𝓝 w) ℂ) = s j from (s j).2)
    have hPeq : holGermIdeal w p = P := by
      rw [← hs, holGermIdeal]
      congr 1
      ext φ
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨j, Subtype.ext (hj.trans (hps j)).symm⟩
      · rintro ⟨j, rfl⟩
        exact ⟨j, (hps j).symm⟩
    have hfmem : ∀ i, (⟨(f i : Germ (𝓝 w) ℂ), f i, hf i, rfl⟩ : holGerms w) ∈ holGermIdeal w p := fun i =>
      hPeq ▸ hfP (Ideal.subset_span ⟨i, rfl⟩)
    choose c _ hc using fun i => exists_of_mem_holGermIdeal p (hfmem i)
    have hfev : ∀ᶠ z in 𝓝 w, ∀ i, f i z = ∑ j, c i j z * p j z :=
      eventually_all.2 fun i => Germ.coe_eq.1 (hc i)
    have hvanp : ∀ᶠ z in 𝓝 w, (∀ j, p j z = 0) → g z = 0 := by
      filter_upwards [hvan, hfev] with z hz hfz hpz
      exact hz fun i => by rw [hfz i]; simp [hpz]
    obtain ⟨h, hh, hgh⟩ := hPrime σ w r p g hp hg (hPeq ▸ hP) hvanp
    exact hPeq ▸ mem_holGermIdeal_of_eq hp hh G (Germ.coe_eq.2 hgh)

  obtain ⟨m, hm⟩ := hrad
  have hm' : G ^ (m + 1) ∈ holGermIdeal w f := by
    rw [pow_succ']
    exact Ideal.mul_mem_left _ G hm
  obtain ⟨h, hh, hgh⟩ := exists_of_mem_holGermIdeal f hm'
  refine ⟨m + 1, h, Nat.succ_pos m, hh, ?_⟩
  have hG : ((G ^ (m + 1) : holGerms w) : Germ (𝓝 w) ℂ) = ((g ^ (m + 1) : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) := by
    rw [Germ.coe_pow]
    rfl
  rw [hG] at hgh
  filter_upwards [Germ.coe_eq.1 hgh] with z hz
  simpa using hz

end RueckertNullstellensatz

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
