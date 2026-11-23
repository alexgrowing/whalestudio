import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRootOfExp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKsFormOfAlgebraicFormsIso

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

theorem conj_sum_zero (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type)
    (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (j : Fin D.R.m)
    (hU : Rl.toRealDat.LUnif) (hW : Rl.toRealDat.models_HW) (hv : FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _))
    (hK : (S.A ((j : ℕ) + 1)).IsKsForm) (τ : ℂ ≃+* ℂ) (hτ : ∀ y, τ (Formalism.L2.Host.embLL0 D y) = Formalism.L2.Host.embLL0 D y)
    (n : ℕ) (c : Fin n → ℂ) (g : Fin n → NX.FmK S ((j : ℕ) + 1))
    (h0 : ∑ k, c k • evW YS v₀ j (g k).val = 0) : ∑ k, τ (c k) • evW YS v₀ j (g k).val = 0 := by
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
  let σ : S.Ks → ℂ := fun r => D.what₂.embLL (algebraMap S.Ks D.what₂.LL r)
  have hσ : ∀ r, τ (σ r) = σ r := fun r => by
    have := hτ (S.kKs r)
    simp only [σ, ← S.kKs_spec]
    exact this
  have hg : ∀ k, evW YS v₀ j (g k).val = ∑ a, σ (bK.repr (g k) a) • φ a := fun k => by
    conv_lhs => rw [← bK.sum_repr (g k)]
    rw [Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Submodule.coe_smul, ← algebraMap_smul D.what₂.LL, evW_smul, hbK]
  have hexp : ∀ d : Fin n → ℂ, ∑ k, d k • evW YS v₀ j (g k).val =
      ∑ a, (∑ k, d k * σ (bK.repr (g k) a)) • φ a := fun d => by
    simp only [hg, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hz : ∀ a, ∑ k, c k * σ (bK.repr (g k) a) = 0 := fun a =>
    Fintype.linearIndependent_iff.1 hφ _ ((hexp c).symm.trans h0) a
  rw [hexp]
  refine Finset.sum_eq_zero fun a _ => ?_
  have : ∑ k, τ (c k) * σ (bK.repr (g k) a) = τ (∑ k, c k * σ (bK.repr (g k) a)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_mul, hσ]
  rw [this, hz a, map_zero, zero_smul]

def ExpZero : Prop := AtTw fun Fm x _ i p _ j => ∀ τ : ℂ ≃+* ℂ,
  (∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y) →
  ∀ (n : ℕ) (c : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
    ∑ k, c k • evW p.nexp p.v₀ j (g k).val = 0 → ∑ k, τ (c k) • evW p.nexp p.v₀ j (g k).val = 0

theorem expZero : ExpZero := by
  unfold ExpZero AtTw AtPts
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    ⟨0, fun x hx _ i p hr hm w _ j τ hτ n c g h0 => ?_⟩⟩⟩
  obtain ⟨Z⟩ := hm.2.2.series
  have hU : p.R.toRealDat.LUnif := hr.prim.unif
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  exact conj_sum_zero _ _ _ _ _ _ _ _ _ _ p.nexp p.v₀ j hU hW (Z.vec j) hK τ hτ n c g h0

def ExpOne : Prop := AtTw fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  RatBase (rdAt p w j hρ ν) →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ τ : ℂ ≃+* ℂ, (∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y) →
      ∃ c : ℂ, (∃ m : ℕ, m ≠ 0 ∧ c ^ m = 1) ∧
        ∃ (n : ℕ) (b : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
          ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = ∑ k, b k • evW p.nexp p.v₀ j (g k).val ∧
          ∑ k, τ (b k) • evW p.nexp p.v₀ j (g k).val =
            c • (ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P)

end GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp

end GlobalTheory.BigOn.Exp
