import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree

theorem eq_smul_of_stable_graph : ∀ (D : D7) (X : HSp D) (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi), IsIrred X Pi rf rl → Module.rank ℂ Pi ≤ Cardinal.aleph0 → ∀ S : Submodule ℂ (Pi × Pi), (∀ g ∈ GfC X, ∀ x ∈ S, (rf g x.1, rf g x.2) ∈ S) → (∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ S, (rl τ Y x.1, rl τ Y x.2) ∈ S) → (∀ x : Pi, ((x, 0) : Pi × Pi) ∈ S → x = 0) → (∀ y : Pi, ((0, y) : Pi × Pi) ∈ S → y = 0) → (∀ x : Pi, ∃ y : Pi, ((x, y) : Pi × Pi) ∈ S) → ∃ c : ℂ, c ≠ 0 ∧ ∀ x y : Pi, ((x, y) : Pi × Pi) ∈ S → y = c • x := by
  intro D X Pi rf rl hirr hrank S hf hl h1 h2 hon
  classical
  haveI : Nontrivial Pi := hirr.1
  choose t ht using hon
  have huniq : ∀ x y, ((x, y) : Pi × Pi) ∈ S → t x = y := by
    intro x y hxy
    have h0 : (((0 : Pi), t x - y) : Pi × Pi) ∈ S := by
      have := S.sub_mem (ht x) hxy
      simpa using this
    exact sub_eq_zero.1 (h2 _ h0)
  let T : Module.End ℂ Pi :=
    { toFun := t
      map_add' := fun a b => huniq _ _ (by simpa using S.add_mem (ht a) (ht b))
      map_smul' := fun r a => by
        simp only [RingHom.id_apply]
        exact huniq _ _ (by simpa using S.smul_mem r (ht a)) }
  have hTf : ∀ g ∈ GfC X, ∀ x, T (rf g x) = rf g (T x) := fun g hg x => huniq _ _ (hf g hg _ (ht x))
  have hTl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x, T (rl τ Y x) = rl τ Y (T x) := fun τ Y hY x => huniq _ _ (hl τ Y hY _ (ht x))
  obtain ⟨c, hc⟩ := GlobalTheory.LocGL.exists_not_isUnit_sub hrank T
  set A := T - algebraMap ℂ (Module.End ℂ Pi) c with hA
  have hAx : ∀ x, A x = T x - c • x := fun x => by simp [hA]
  have hAf : ∀ g ∈ GfC X, ∀ x, A (rf g x) = rf g (A x) := by
    intro g hg x; rw [hAx, hAx, hTf g hg, map_sub, map_smul]
  have hAl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x, A (rl τ Y x) = rl τ Y (A x) := by
    intro τ Y hY x; rw [hAx, hAx, hTl τ Y hY, map_sub, map_smul]
  have hA0 : A = 0 := by
    rcases hirr.2 (LinearMap.ker A)
        (fun g hg x hx => by rw [LinearMap.mem_ker] at hx ⊢; rw [hAf g hg, hx, map_zero])
        (fun τ Y hY x hx => by rw [LinearMap.mem_ker] at hx ⊢; rw [hAl τ Y hY, hx, map_zero]) with hk | hk
    · rcases hirr.2 (LinearMap.range A)
          (fun g hg x hx => by obtain ⟨z, rfl⟩ := hx; exact ⟨rf g z, hAf g hg z⟩)
          (fun τ Y hY x hx => by obtain ⟨z, rfl⟩ := hx; exact ⟨rl τ Y z, hAl τ Y hY z⟩) with hr | hr
      · exact LinearMap.range_eq_bot.1 hr
      · exact absurd ((Module.End.isUnit_iff _).2 ⟨LinearMap.ker_eq_bot.1 hk, LinearMap.range_eq_top.1 hr⟩) hc
    · exact LinearMap.ker_eq_top.1 hk
  have hTc : ∀ x, t x = c • x := fun x => by
    have := congrArg (fun f : Module.End ℂ Pi => f x) hA0
    simp only [hAx, LinearMap.zero_apply] at this
    exact sub_eq_zero.1 this
  refine ⟨c, ?_, fun x y hxy => by rw [← huniq x y hxy, hTc]⟩
  rintro rfl
  obtain ⟨x, hx⟩ := exists_ne (0 : Pi)
  exact hx (h1 x (by simpa [hTc] using ht x))

end GlobalTheory.SquareAgree
