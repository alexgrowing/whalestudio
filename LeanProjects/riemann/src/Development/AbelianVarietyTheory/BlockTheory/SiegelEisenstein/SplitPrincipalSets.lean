import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitPrincipalSets

open scoped ComplexConjugate Matrix ComplexOrder Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff)
open GlobalTheory.Core.Rk.IP (WRep up wcoef rcoef)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev FinPlE (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E)

open Classical in

def below (Z : Finset (FinPlE D)) : Finset (FinPl D) := Z.image fun w => w.under (𝓞 D.host.F)

def IsSplitSet (Z : Finset (FinPlE D)) : Prop :=
  (∀ w ∈ Z, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F))) ∧
    ∀ w ∈ Z, ∀ w' ∈ Z, w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) → w = w'

def prinLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (GLoc σ J v) where
  carrier := {k | k ∈ stabLoc σ J L v ∧ ∀ y ∈ latLoc F L v,
    (GlobalTheory.AdelicU.matHom _ σ J k).1 *ᵥ y - y ∈ latLoc F (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) • L) v}
  one_mem' := ⟨one_mem _, fun y _ => by
    rw [map_one, Units.val_one, Matrix.one_mulVec, sub_self]; exact zero_mem _⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun y hy => by
    have h := add_mem (ha.2 _ ((mem_stabLoc.1 hb.1 y).1 hy)) (hb.2 y hy)
    rwa [sub_add_sub_cancel, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul] at h⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun y hy => by
    have h := neg_mem (ha.2 _ ((mem_stabLoc.1 (inv_mem ha.1) y).1 hy))
    rwa [neg_sub, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.one_mulVec] at h⟩

variable (A : HSp D) (L : Lat A)

def prin (Z : Finset (FinPlE D)) : Subgroup (GA D A) :=
  levelFin D.sp.cm.sig A.gram L ⊓ ⨅ v ∈ below Z, (prinLoc D.sp.cm.sig A.gram L v).comap (proj D.sp.cm.sig A.gram v)

def IsSmallFam (S : Finset (FinPl D)) (r : ℕ) (c : LFun.Fam D.host.E) : Prop :=
  ∀ w : FinPlE D, w.under (𝓞 D.host.F) ∉ S → (c w).card = r ∧
    ∀ β ∈ c w, ‖(β : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((r : ℝ) - 1) / 2)

def LiftNonvanishing (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A W : HSp D) (r t : ℕ), IsInfFam θ →
    A.rank = r + t → W.rank = r → 1 ≤ r → r + 5 ≤ t → (∀ τ : D.host.E →+* ℂ, (A.gram.map τ).PosDef) →
  ∀ (χA χW : (AE D)ˣ →* Circle) (om : WRep A W), IsWeilDatumO ψ A W χA χW om →
  ∀ (LA : Lat A) (LW : Lat W), IsSelfDualC A LA → IsSelfDualC W LW →
  ∀ Z : Finset (FinPlE D), IsSplitSet Z →
    (∀ v : FinPl D, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) →
    LFun.UnrOff χW (below Z : Set (FinPl D)) →
  ∀ u : GA D A → ℂ, IsAutFunDef A u → (∀ k ∈ prin A LA Z, ∀ g, u (g * k) = u g) →
  ∀ c : LFun.Fam D.host.E, IsSmallFam (below Z) r c →
    LFun.IsParamFun D.sp.cm.sig A.gram LA (below Z : Set (FinPl D)) u (c + LFun.segFam (LFun.val χW) t) →
  ∀ (m : Measure (GA D A)) (mInf : Measure (GinfC A)), m.IsHaarMeasure → mInf.IsHaarMeasure →
  ∀ (ν : Measure (WO A W)) (𝓕 : Set (WO A W)), IsCovolOne (ratL W A) ν 𝓕 →
  ∀ sW : RealMat W, (∀ τ, IsCartanInv (gramAt D W τ) (sW τ)) →
  ∀ Φ : WO A W → ℂ, IsFockVec ψ θ A W (fun _ => 1) sW Φ → IsSphOff ψ A W LA LW (below Z) Φ →
    (∀ k ∈ prin A LA Z, om (k, 1) Φ = Φ) →
    ∫ b : GinfC A, wcoef om ν 𝓕 Φ Φ b * rcoef m u u b ∂mInf ≠ 0 →
    ∃ f, IsThetaFunO ψ A W f ∧ ∃ h, up om m f u h ≠ 0

example : prin A L ∅ = levelFin D.sp.cm.sig A.gram L := by simp [prin, below]

example (τ : D.what₂.Tau) (h : ∀ τ : D.host.E →+* ℂ, (A.gram.map τ).PosDef) : IsCartanInv (gramAt D A τ) 1 :=
  ⟨one_mul _, by simp, by rw [mul_one]; exact h _⟩

example (S : Finset (FinPl D)) (r t : ℕ) (c : LFun.Fam D.host.E) (h : IsSmallFam S r c) (χ : (AE D)ˣ →* Circle)
    (w : FinPlE D) (hw : w.under (𝓞 D.host.F) ∉ S) : ((c + LFun.segFam (LFun.val χ) t) w).card = r + t := by
  simp [LFun.segFam, LFun.seg, (h w hw).1]

end GlobalTheory.IndefiniteRowSideFullHecke.SplitPrincipalSets

end
