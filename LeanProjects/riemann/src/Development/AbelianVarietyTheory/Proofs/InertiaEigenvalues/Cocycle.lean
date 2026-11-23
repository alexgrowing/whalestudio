import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisOfSubmodule

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.ConnCoc

section General

variable {G Qp LL O : Type} [Group G] [TopologicalSpace G] [Field Qp] [Field LL]
  [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]

theorem cocycle (Y Yt : LocLat G Qp LL O) (ι : LatHom Y.L Yt.L) (hι : Function.Injective ι.f)
    (yt : Yt.V) (f : G → ↥Y.L.T) (hf : ∀ g, ι.f (f g : Y.V) = Yt.ρ g yt - yt) (g h : G) :
    f (g * h) = f g + actT Y.L g (f h) := by
  apply Subtype.ext
  apply hι
  have e : ((f g + actT Y.L g (f h) : ↥Y.L.T) : Y.V) = (f g : Y.V) + Y.ρ g (f h : Y.V) := rfl
  rw [e, map_add, ι.equiv, hf, hf, hf, map_sub, map_mul, Module.End.mul_apply]
  abel

theorem continuous (Y Yt : LocLat G Qp LL O) (ι : LatHom Y.L Yt.L) (hι : Function.Injective ι.f)
    (yt : Yt.V) (f : G → ↥Y.L.T) (hf : ∀ g, ι.f (f g : Y.V) = Yt.ρ g yt - yt) :
    Continuous fun g => (f g : Y.V) := by
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective ι.f (LinearMap.ker_eq_bot.2 hι)
  have : ContinuousSMul LL Y.V := IsModuleTopology.toContinuousSMul LL Y.V
  have hc : Continuous r := IsModuleTopology.continuous_of_linearMap r
  have e : (fun g => (f g : Y.V)) = fun g => r (Yt.ρ g yt) + (- r yt) := by
    funext g
    rw [← sub_eq_add_neg, ← map_sub, ← hf]
    exact (LinearMap.congr_fun hr _).symm
  rw [e]
  exact (hc.comp (Yt.cont yt)).add continuous_const

end General

theorem locConst {l : ℕ} [Fact l.Prime] {G V : Type} [TopologicalSpace G] [AddCommGroup V]
    [Module ℚ_[l] V] [TopologicalSpace V] (T : Set V) {m : ℕ} (w : Module.Basis (Fin m) ℚ_[l] V)
    (hw : ∀ x : V, x ∈ T ↔ ∀ i, ‖w.repr x i‖ ≤ 1) (hc : Continuous w.equivFun)
    (F : G → V) (hF : Continuous F) (n : ℕ) (g : G) :
    ∀ᶠ h in nhds g, ∃ y ∈ T, F h - F g = (l ^ n : ℕ) • y := by
  have hl : ((l : ℚ_[l]) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have key : ∀ i, ∀ᶠ h in nhds g,
      ‖((l : ℚ_[l]) ^ n)⁻¹ * (w.equivFun (F h) i - w.equivFun (F g) i)‖ < 1 := by
    intro i
    have c : Continuous fun h =>
        ‖((l : ℚ_[l]) ^ n)⁻¹ * (w.equivFun (F h) i - w.equivFun (F g) i)‖ :=
      (continuous_const.mul (((continuous_apply i).comp (hc.comp hF)).sub continuous_const)).norm
    apply c.continuousAt.eventually_lt continuousAt_const
    simp
  filter_upwards [Filter.eventually_all.2 key] with h hh
  refine ⟨((l : ℚ_[l]) ^ n)⁻¹ • (F h - F g), (hw _).2 fun i => ?_, ?_⟩
  · have := (hh i).le
    simpa [Module.Basis.equivFun_apply] using this
  · rw [← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, Nat.cast_pow, mul_inv_cancel₀ hl, one_smul]

theorem conn : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (LL : FinExt l) (Y Yt : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom Y.L Yt.L), Function.Injective ι.f → ∀ (yt : Yt.V) (f : G → ↥Y.L.T), (∀ g, ι.f (f g : Y.V) = Yt.ρ g yt - yt) → (∀ g h, f (g * h) = f g + actT Y.L g (f h)) ∧ ∀ (n : ℕ) (g : G), ∀ᶠ h in nhds g, ∃ y : ↥Y.L.T, f h - f g = (l ^ n : ℕ) • y := by
  intro l _ G _ _ LL Y Yt ι hι yt f hf
  refine ⟨cocycle Y Yt ι hι yt f hf, fun n g => ?_⟩
  obtain ⟨m, w, hw, hc, -⟩ := GlobalTheory.Cyc.LatBasis.exists_basis l G LL Y
  have := locConst (Y.L.T : Set Y.V) w hw hc _ (continuous Y Yt ι hι yt f hf) n g
  filter_upwards [this] with h hh
  obtain ⟨y, hy, e⟩ := hh
  exact ⟨⟨y, hy⟩, Subtype.ext e⟩

end GlobalTheory.ConnCoc
