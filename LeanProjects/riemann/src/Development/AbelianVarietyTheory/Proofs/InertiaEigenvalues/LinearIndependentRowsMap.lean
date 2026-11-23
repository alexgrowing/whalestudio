import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodScalarOfIsAdelicScalar

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

theorem linearIndependent_rows_map {K L : Type*} [Field K] [Field L] (e : K →+* L) {n m : ℕ}
    (a : Fin n → Fin m → K) (ha : LinearIndependent K a) :
    LinearIndependent L fun c k => e (a c k) := by
  classical
  obtain ⟨g, hg⟩ := (Fintype.linearCombination K a).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 ha.fintypeLinearCombination_injective)
  have hj : ∀ c j, g (a c) j = if c = j then 1 else 0 := fun c j => by
    have := congrFun (LinearMap.congr_fun hg (Pi.single c 1)) j
    simpa [Pi.single_apply, eq_comm] using this
  have hg' : ∀ (x : Fin m → K) j, g x j = ∑ k, x k * g (fun j' => if k = j' then 1 else 0) j := fun x j => by
    conv_lhs => rw [pi_eq_sum_univ x]
    rw [map_sum, Finset.sum_apply]
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.linearIndependent_iff]
  intro μ hμ j
  have h0 : ∀ k, ∑ c, μ c * e (a c k) = 0 := fun k => by
    have := congrFun hμ k
    simpa [Finset.sum_apply] using this
  calc μ j = ∑ c, μ c * e (g (a c) j) := by simp [hj]
    _ = ∑ c, ∑ k, μ c * e (a c k * g (fun j' => if k = j' then 1 else 0) j) :=
        Finset.sum_congr rfl fun c _ => by rw [hg' (a c) j, map_sum, Finset.mul_sum]
    _ = ∑ k, e (g (fun j' => if k = j' then 1 else 0) j) * ∑ c, μ c * e (a c k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [map_mul]
        ring
    _ = 0 := by simp [h0]

theorem realRd_faithful : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ), ν ≠ 0 → Rl.toRealDat.LUnif → Rl.toRealDat.models_HW → FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _) → (S.A ((j : ℕ) + 1)).IsKsForm → Faithful (realRd YS v₀ hρ i j b ν) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG S YS v₀ ρ hρ i j b ν hν hU hW hv hK
  classical
  let L : (Rl.HW j (sg0 D A3.A)).H →ₗ[ℂ] (GA D (Wc D j) → ℂ) :=
    { toFun := fun x => (Rl.HW j (sg0 D A3.A)).e x (v₀ j _)
      map_add' := fun x y => by rw [map_add]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hL : LinearMap.ker L = ⊥ :=
    LinearMap.ker_eq_bot.2 fun x y h => GlobalTheory.LiftScalarCompare.eval_inj hW hv h
  obtain ⟨m, bb, -, hKs, hspan, hLL, -⟩ := hK
  let bK : Module.Basis (Fin m) S.Ks ↥(S.A ((j : ℕ) + 1)).WK :=
    (Module.Basis.span hKs).map (LinearEquiv.ofEq _ _ hspan)
  have hbK : ∀ k, ((bK k : ↥(S.A ((j : ℕ) + 1)).WK) : S.WL ((j : ℕ) + 1)) = bb k := fun k => by
    simp [bK, Module.Basis.span_apply]
  let φ : Fin m → (GA D (Wc D j) → ℂ) := fun k => evW YS v₀ j (bb k)
  have hφ : LinearIndependent ℂ φ := by
    have h1 : LinearIndependent D.what₂.LL fun k => (YS.fi j).e (bb k) :=
      hLL.map' (YS.fi j).e.toLinearMap (YS.fi j).e.ker
    exact ((hU j (sg0 D A3.A)).1 m _ h1).map' L hL
  let B : Module.Basis (Fin m) (NX.KB S i b) (NX.Fm S i ((j : ℕ) + 1) b) :=
    Algebra.TensorProduct.basis (NX.KB S i b) bK
  intro n v hvi
  let w : Fin n → NX.Fm S i ((j : ℕ) + 1) b := fun c => YS.eF i _ b (Nat.le_add_left _ _) j.2 (v c)
  have hw0 : LinearIndependent (FractionRing (D.ntw.O i)) w :=
    hvi.map' (YS.eF i _ b (Nat.le_add_left _ _) j.2).toLinearMap (YS.eF i _ b (Nat.le_add_left _ _) j.2).ker
  have hw1 : LinearIndependent (NX.KB S i b) w := hw0
  have hw : LinearIndependent (NX.KB S i b) fun c => B.equivFun (w c) :=
    hw1.map' B.equivFun.toLinearMap B.equivFun.ker
  have hr := linearIndependent_rows_map (ρ.e i b) (fun c => B.equivFun (w c)) hw
  let Ψ : (Fin m → ℂ) →ₗ[ℂ] (GA D (Wc D j) → ℂ) := ν⁻¹ • Fintype.linearCombination ℂ φ
  have hΨ : LinearMap.ker Ψ = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun z hz => ?_
    have h0 : Fintype.linearCombination ℂ φ z = 0 := by
      have := hz
      simp only [Ψ, LinearMap.smul_apply, smul_eq_zero, inv_eq_zero, hν, false_or] at this
      exact this
    exact hφ.fintypeLinearCombination_injective (h0.trans (map_zero _).symm)
  suffices key : (fun c => realRd YS v₀ hρ i j b ν (v c)) = Ψ ∘ fun c k => ρ.e i b (B.equivFun (w c) k) by
    rw [key]; exact hr.map' Ψ hΨ
  funext c
  change ν⁻¹ • evK YS v₀ hρ i j b (w c) = ν⁻¹ • Fintype.linearCombination ℂ φ _
  congr 1
  rw [Fintype.linearCombination_apply]
  conv_lhs => rw [← B.sum_equivFun (w c)]
  refine (map_sum (evK YS v₀ hρ i j b) _ _).trans ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show B k = ((1 : NX.KB S i b) ⊗ₜ[S.Ks] bK k : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) from
    Algebra.TensorProduct.basis_apply _ _]
  change evK YS v₀ hρ i j b ((B.equivFun (w c) k • (1 : NX.KB S i b)) ⊗ₜ[S.Ks] (bK k : NX.FmK S ((j : ℕ) + 1))) = _
  rw [smul_eq_mul, mul_one]
  refine (evK_tmul YS v₀ hρ i j b _ _).trans ?_
  exact congrArg _ (congrArg (evW YS v₀ j) (hbK k))

end GlobalTheory.SeriesTie
