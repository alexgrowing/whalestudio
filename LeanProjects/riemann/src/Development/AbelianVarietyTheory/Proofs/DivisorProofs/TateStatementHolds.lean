import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointLevelPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateModuleOfEvaluationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateLatticeSpansStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingUnitScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDataTateSpanStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem tateSt : TateSt := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ n _ hstar hA yb yy P π ψ hP β σ J _ N a T S hL
  obtain ⟨ev, ζ, hζp, hζpow, hadd, hlin, honto, htow, hweil, hlev⟩ :=
    GlobalTheory.T.p_adic_point_level_power E H Dw l' Xo' c' W Y p n hA yb yy P π ψ hP
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hev1 : ∀ b, ev 1 b = 1 := fun b => by
    have := (honto 1 one_pos (ev 1 b)).2 ⟨b, rfl⟩
    simpa using this
  obtain ⟨f, hflev, hflin⟩ := GlobalTheory.T.exists_tate_module_of_evaluations E H Dw p P ev hadd hlin htow hev1
  have hspan := GlobalTheory.T.tate_lattice_spans E H Dw p P f (fun x hx => by
    obtain ⟨b, hb⟩ := (honto p hp x).1 hx
    exact ⟨b, by rw [hflev, pow_one, hb]⟩)
  obtain ⟨u, hu, hpair⟩ := GlobalTheory.T.weil_pairing_unit_scalar E H Dw p P f ζ hζp hζpow (fun k b b' => by
    rw [hflev, hflev]; exact hweil _ (pow_pos hp k) b b')
  have hmem : ∀ (c : 𝓞_ℂ_[p]) (t : P.T), ((c : ℂ_[p]) ⊗ₜ[ℤ_[p]] t : P.V) ∈ P.latT := fun c t =>
    ⟨c ⊗ₜ t, by rw [Point.inclT_tmul]; rfl⟩
  have hsum : ∀ (X : Fin N → 𝓞_ℂ_[p]), (∑ m, ((X m : ℂ_[p]) ⊗ₜ[ℤ_[p]] f (a m)) : P.V) ∈ P.latT := fun X =>
    Submodule.sum_mem _ fun m _ => hmem _ _
  let Φ : (c'.V W) ⊗[ℤ] Dw.La →ₗ[ℤ] P.V := TensorProduct.lift (LinearMap.mk₂ ℤ
    (fun (v : c'.V W) (b : Dw.La) => ((β v : ℂ_[p]) ⊗ₜ[ℤ_[p]] f b : P.V))
    (fun v v' b => by simp [TensorProduct.add_tmul])
    (fun z v b => by simp [TensorProduct.smul_tmul'])
    (fun v b b' => by simp [TensorProduct.tmul_add])
    (fun z v b => by simp [TensorProduct.tmul_smul]))
  have hΦ : ∀ v b, Φ (v ⊗ₜ b) = (β v : ℂ_[p]) ⊗ₜ[ℤ_[p]] f b := fun v b => rfl
  refine ⟨fun m => f (a m), algebraMap ℤ_[p] ℂ_[p] u, fun m => by rw [hflev]; exact hlev _, ?_⟩
  refine ⟨fun i => ⟨hsum _, ?_⟩, fun i => hsum _, ?_, fun i j => ?_, ?_⟩
  · refine EigenSplit.mem_eigenSub.2 fun o => ?_
    have e1 := congrArg Φ (hL.1 i o)
    simp only [map_sum, hΦ] at e1
    have e2 : ∀ (c : ℂ_[p]) (t : P.T), P.actV o (c ⊗ₜ[ℤ_[p]] t) = c ⊗ₜ[ℤ_[p]] P.actT o t := fun c t => rfl
    simp only [map_sum, e2, ← hflin]
    rw [e1, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [TensorProduct.smul_tmul', map_mul]
    rfl
  · change ‖algebraMap ℚ_[p] ℂ_[p] (u : ℚ_[p])‖ = 1
    rw [norm_algebraMap']
    exact PadicInt.isUnit_iff.1 hu
  · have hc : ∀ x : 𝓞_ℂ_[p], algebraMap 𝓞_ℂ_[p] ℂ_[p] x = (x : ℂ_[p]) := fun x => rfl
    have e := congrArg (fun x : c'.V W => algebraMap 𝓞_ℂ_[p] ℂ_[p] (β x)) (hL.2.1 i j)
    simp only [map_sum, map_mul, map_intCast] at e
    simp only [hc] at e
    simp only [map_sum, LinearMap.sum_apply, Point.pairV_tmul, hpair]
    simp only [Algebra.smul_def, map_mul, map_intCast]
    have e4 : ∀ m m', algebraMap ℤ_[p] ℂ_[p] u * ((Dw.EF (a m) (a m') : ℤ) : ℂ_[p]) * (((β (S i m) : 𝓞_ℂ_[p]) : ℂ_[p]) * ((β (T j m') : 𝓞_ℂ_[p]) : ℂ_[p])) =
        algebraMap ℤ_[p] ℂ_[p] u * (((β (S i m) : 𝓞_ℂ_[p]) : ℂ_[p]) * ((β (T j m') : 𝓞_ℂ_[p]) : ℂ_[p]) * ((Dw.EF (a m) (a m') : ℤ) : ℂ_[p])) :=
      fun m m' => by ring
    rw [Finset.sum_comm]
    simp only [e4, ← Finset.mul_sum, e]
    by_cases h : i = j <;> simp [h]
  · exact GlobalTheory.T.lattice_data_tate_span E H Dw p P (c'.V W) β (embV c' W σ) J N a T S f hL hflin hspan

end GlobalTheory.FlatModel
