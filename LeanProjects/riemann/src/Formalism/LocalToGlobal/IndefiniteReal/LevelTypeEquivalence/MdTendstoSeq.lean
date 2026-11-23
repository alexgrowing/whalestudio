import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.TransportedFrame
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IpTheta

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}

theorem md_fun_succ (φ : WO S T → (Fin k → ℝ) → ℂ) (n : ℕ) (v : Fin (n + 1) → (Fin k → ℝ)) (h : ℝ) (a : Fin k → ℝ) :
    (fun y => md (φ y) (n + 1) v h a) = ((h : ℂ)⁻¹) • ((fun y => md (φ y) n (Fin.tail v) h (a + h • v 0)) +
      (-1 : ℂ) • (fun y => md (φ y) n (Fin.tail v) h a)) := by
  funext y
  simp only [md, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

theorem md_theta {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) {M : (Fin k → ℝ) →+ WO S T} (hM : IsRealFrame M) :
    ∀ (n : ℕ) (v : Fin n → (Fin k → ℝ)) (h : ℝ) (a : Fin k → ℝ),
      IsThetaFunO ψ S T (fun y => md (Gf ψ M f y) n v h a)
  | 0, v, h, a => by
    have : (fun y => md (Gf ψ M f y) 0 v h a) = heisO ψ S T (M a) f := rfl
    rw [this]
    exact thetaO_heis hψ hf (M a) ((wo_real_iff (M a)).mp (hM.2.1 a))
  | n + 1, v, h, a => by
    rw [md_fun_succ]
    exact thetaO_smul _ (thetaO_add (md_theta hψ hf hM n _ h _) (thetaO_smul _ (md_theta hψ hf hM n _ h _)))

theorem om_md {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hω : IsWeilDatumO ψ S T χS χT om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (L : (Fin k → ℝ) →+ WO S T) (hL : IsRealFrame L) (g : GA D S)
    (h : GA D T) :
    ∀ (n : ℕ) (v : Fin n → (Fin k → ℝ)) (r : ℝ) (a : Fin k → ℝ),
      om (g, h) (fun y => md (Gf ψ ((actOAdd g⁻¹ h⁻¹).comp L) f y) n v r a) =
        fun x => md (Gf ψ L (om (g, h) f) x) n v r a
  | 0, v, r, a => by
    show om (g, h) (heisO ψ S T (actO S T g⁻¹ h⁻¹ (L a)) f) = heisO ψ S T (L a) (om (g, h) f)
    rw [hω.om_heis g h _ f hf, actO_inv]
  | n + 1, v, r, a => by
    rw [md_fun_succ, md_fun_succ (fun x => Gf ψ L (om (g, h) f) x), map_smul, map_add, map_smul,
      om_md hω hf L hL g h n, om_md hω hf L hL g h n]

theorem md_tendsto_seq {φ : (Fin k → ℝ) → ℂ} (hφ : ContDiff ℝ ∞ φ) {n : ℕ} (v : Fin n → (Fin k → ℝ)) :
    Tendsto (fun j : ℕ => md φ n v (1 / ((j : ℝ) + 1)) 0) atTop (𝓝 (iteratedFDeriv ℝ n φ 0 v)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := md_tendsto n φ hφ v 0 (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨N, fun j hj => ?_⟩
  rw [dist_eq_norm]
  have hpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  have hlt : 1 / ((j : ℝ) + 1) < δ := by
    refine lt_of_le_of_lt ?_ hN
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.succ_le_succ hj
  exact lt_of_le_of_lt (hδε _ hpos hlt 0 (by simpa using hδ)) (by linarith)

end Formalism.IndefR.Eqv

end
