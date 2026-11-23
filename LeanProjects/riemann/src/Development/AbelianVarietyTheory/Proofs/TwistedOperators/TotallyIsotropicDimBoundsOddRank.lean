import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoDim

theorem finrank_perp_add {E : Type} [Field E] [NumberField E] [StarRing E] (V : HSpace E)
    (W : Submodule E V.V) :
    Module.finrank E (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W) + Module.finrank E W = V.rank := by
  classical
  set a := Module.finrank E W
  let b := Module.finBasis E W
  let ψ : V.V →ₗ[E] (Fin a → E) := LinearMap.pi fun i => V.hT (b i : V.V)
  have hker : LinearMap.ker ψ = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W := by
    ext y
    simp only [LinearMap.mem_ker, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp, Submodule.mem_iInf]
    constructor
    · intro h w hw
      have e := congrArg (fun v : Fin a → E => v) h
      have hw' : (⟨w, hw⟩ : W) = ∑ i, (b.repr ⟨w, hw⟩ i) • b i := (b.sum_repr _).symm
      have : w = ∑ i, (b.repr ⟨w, hw⟩ i) • (b i : V.V) := by
        have := congrArg Subtype.val hw'
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this
      rw [this, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply]
      have := congrFun h i
      simp only [ψ, LinearMap.pi_apply, Pi.zero_apply] at this
      rw [this, smul_zero]
    · intro h
      funext i
      simpa [ψ] using h (b i) (b i).2
  have hsurj : LinearMap.range ψ = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
    let c : Fin a → E := fun i => f (Pi.single i 1)
    have hfc : ∀ v : Fin a → E, f v = ∑ i, v i * c i := by
      intro v
      rw [LinearMap.pi_apply_eq_sum_univ f v]
      simp only [smul_eq_mul, c]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      funext j
      simp [Pi.single_apply, eq_comm]
    have hy : ∀ y, V.hT (∑ i, (star (c i)) • (b i : V.V)) y = 0 := by
      intro y
      have h1 : f (ψ y) = 0 := by
        have : f (ψ y) ∈ (LinearMap.range ψ).map f := ⟨ψ y, ⟨y, rfl⟩, rfl⟩
        rw [hf] at this
        exact (Submodule.mem_bot E).1 this
      rw [hfc] at h1
      rw [map_sum, LinearMap.sum_apply]
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
      simp [ψ, mul_comm]
    have hx := V.nondeg.1 _ hy
    have hli : LinearIndependent E (fun i => (b i : V.V)) :=
      b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    have hc : ∀ i, star (c i) = 0 := by
      have := (Fintype.linearIndependent_iff.1 hli) (fun i => star (c i)) hx
      exact this
    apply hf0
    apply LinearMap.ext
    intro v
    rw [hfc]
    simp [fun i => star_eq_zero.1 (hc i)]
  have hrn := LinearMap.finrank_range_add_finrank_ker ψ
  rw [hsurj, hker, finrank_top, Module.finrank_fin_fun, V.rank_eq] at hrn
  omega

end GlobalTheory.IsoDim

theorem GlobalTheory.IsoDim.isotropic_dim_bounds : ∀ (D : D7) (V : HSp D), Odd V.rank → ∀ W : Submodule D.host.E V.V, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W →
    0 < Module.finrank D.host.E W ∧ 2 * Module.finrank D.host.E W + 1 ≤ V.rank := by
  intro D V hodd W hW
  have h := GlobalTheory.IsoDim.finrank_perp_add V W
  have hle : Module.finrank D.host.E W ≤ Module.finrank D.host.E (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W) :=
    Submodule.finrank_mono hW.2
  have hpos : 0 < Module.finrank D.host.E W :=
    Nat.pos_of_ne_zero fun h0 => hW.1 (Submodule.finrank_eq_zero.1 h0)
  obtain ⟨k, hk⟩ := hodd
  refine ⟨hpos, ?_⟩
  omega
