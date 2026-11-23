import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

noncomputable section

theorem mt_mul_splitStab {D : D7} (V : HSp D) (g h : GA D V) : Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul]

theorem mt_one_splitStab {D : D7} (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [map_one, Units.val_one]

theorem idem_unit_splitStab {R : Type} [CommRing R] {e d d' : R} (he : e * e = e) (h : d' * d = 1) :
    (e * d + (1 - e)) * (e * d' + (1 - e)) = 1 := by
  linear_combination (e * e) * h + (2 - d - d') * he

theorem exists_isDetAt_splitStab {D : D7} {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) : ∃ y, IsDetAt e V g y :=
  ⟨Units.mkOfMulEqOne _ _ (idem_unit_splitStab he (det_conj_mul V g)), Units.val_mkOfMulEqOne _⟩

open scoped ComplexOrder in
theorem isCartanInv_one_splitStab (k : ℕ) : IsCartanInv (1 : Matrix (Fin k) (Fin k) ℂ) 1 := by
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one]
  exact Matrix.PosDef.one

theorem heisO_zero_splitStab {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (f : WO V W → ℂ) : heisO ψ V W 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem om_vacuum_split_stab : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSelfDualC V ΛV → IsSelfDualC W ΛW → ∀ (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), (∀ τ, IsCartanInv (gramAt D W τ) (s τ)) → ∀ f, IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f → ∀ (e : AE D) (k : GA D W), IsSplitIdem D e → SuppAt e W k → (∀ u, u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) ↔ actO V W 1 k u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True)) → om (1, k) f = mu k • f := by
  intro D ψ θ V W χV χW om hP mu hmu ΛV ΛW hV hW s hs f hf e k he hk hst
  obtain ⟨y, hy⟩ := exists_isDetAt_splitStab he.1 W k
  have h1 : ∀ τ, IsCartanInv (gramAt D V τ) ((fun _ => 1 : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) τ) := by
    intro τ
    have : gramAt D V τ = 1 := by
      unfold gramAt
      rw [hP.std]
      simp
    rw [this]
    exact isCartanInv_one_splitStab _
  have hs1 : SuppAt e V 1 := by
    intro i j
    rw [mt_one_splitStab, sub_self, Matrix.zero_apply, mul_zero]
  have hx : IsDetAt e V 1 1 := by
    unfold IsDetAt
    rw [mt_one_splitStab, Matrix.det_one, Units.val_one]
    ring
  have hact : ∀ u, actO V W 1 k (actO V W 1 k⁻¹ u) = u := by
    intro u
    unfold actO
    rw [inv_one, mt_one_splitStab, Matrix.mul_one, Matrix.mul_one, ← Matrix.mul_assoc, ← mt_mul_splitStab,
      mul_inv_cancel, mt_one_splitStab, Matrix.one_mul]
  have key := GlobalTheory.SplitScalar.om_vacuum_eq_splitFac_smul_sum D ψ θ V W χV χW om hP.weil hP.inf hP.sigV hP.sigW
    (fun _ => 1) s h1 hs ΛV ΛV ΛW ΛW hV hV hW hW e he 1 k hs1 hk 1 y hx hy
    (fun u => ⟨fun hu => ⟨actO V W 1 k⁻¹ u, (hst _).2 (by rw [hact]; exact hu), (hact u).symm⟩,
      fun ⟨u₀, hu₀, h⟩ => h ▸ (hst u₀).1 hu₀⟩)
    {0} {0}
    (fun u hu => by
      rw [Finset.mem_singleton.1 hu]
      exact ⟨zero_mem _, fun i j => mul_zero _⟩)
    (fun u hu _ => ⟨0, ⟨Finset.mem_singleton_self _, by rwa [sub_zero]⟩, fun v hv => Finset.mem_singleton.1 hv.1⟩)
    (fun u hu => by
      rw [Finset.mem_singleton.1 hu]
      exact ⟨zero_mem _, fun i j => mul_zero _⟩)
    (fun u hu _ => ⟨0, ⟨Finset.mem_singleton_self _, by rwa [sub_zero]⟩, fun v hv => Finset.mem_singleton.1 hv.1⟩)
    f hf
  have hr : IsDetRoot W k y := isDetAt_root he W k hk y hy
  rw [key, hmu.2 k y hr]
  simp [heisO_zero_splitStab, splitFacO]

end

end GlobalTheory.AdTh
