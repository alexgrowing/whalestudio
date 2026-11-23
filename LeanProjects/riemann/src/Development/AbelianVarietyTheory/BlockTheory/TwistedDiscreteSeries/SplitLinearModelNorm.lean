import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def absV (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (y : (Fv F v)ˣ) : ℝ :=
  ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (WithZero.log (Valued.v (y : Fv F v)))

theorem absV_pos (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (y : (Fv F v)ˣ) :
    0 < absV F v y := by
  unfold absV
  refine zpow_pos ?_ _
  have : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero this

def normV (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : (AE D)ˣ →* (Fv D.host.F v)ˣ :=
  Units.map (((evalV D.host.F v).comp (sndA D.host.F)).toRingHom.toMonoidHom.comp
    (Algebra.norm (AF D.host.F) (S := AE D)))

def normFin (D : D7) : (AE D)ˣ →* (Af D.host.F)ˣ :=
  Units.map ((sndA D.host.F).toRingHom.toMonoidHom.comp (Algebra.norm (AF D.host.F) (S := AE D)))

def absFin (D : D7) (x : (AE D)ˣ) : ℝ := ∏ᶠ v, absV D.host.F v (normV D v x)

theorem absFin_finite (D : D7) (x : (AE D)ˣ) :
    (Function.mulSupport fun v => absV D.host.F v (normV D v x)).Finite := by
  have h1 := ((normFin D x : Af D.host.F)).2
  have h2 := (((normFin D x)⁻¹ : (Af D.host.F)ˣ) : Af D.host.F).2
  have h := h1.and h2
  rw [Filter.eventually_cofinite] at h
  refine h.subset fun v hv => ?_
  intro hh
  apply hv
  have e1 : ((normV D v x : (Fv D.host.F v)ˣ) : Fv D.host.F v) = (normFin D x : Af D.host.F).1 v := rfl
  have e2 : (((normV D v x)⁻¹ : (Fv D.host.F v)ˣ) : Fv D.host.F v) =
      (((normFin D x)⁻¹ : (Af D.host.F)ˣ) : Af D.host.F).1 v := rfl
  have a1 : Valued.v ((normV D v x : (Fv D.host.F v)ˣ) : Fv D.host.F v) ≤ 1 := by rw [e1]; exact hh.1
  have a2 : Valued.v (((normV D v x)⁻¹ : (Fv D.host.F v)ˣ) : Fv D.host.F v) ≤ 1 := by rw [e2]; exact hh.2
  have hne : Valued.v ((normV D v x : (Fv D.host.F v)ˣ) : Fv D.host.F v) ≠ 0 := by
    simp
  rw [Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hne)] at a2
  have : Valued.v ((normV D v x : (Fv D.host.F v)ˣ) : Fv D.host.F v) = 1 := le_antisymm a1 a2
  simp [absV, this]

theorem absFin_pos (D : D7) (x : (AE D)ˣ) : 0 < absFin D x :=
  finprod_induction (fun r : ℝ => 0 < r) one_pos (fun _ _ => mul_pos) fun v => absV_pos _ v _

example (D : D7) : absFin D 1 = 1 := by simp [absFin, absV]

variable {D : D7}

def subst (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) : WO S T :=
  HMul.hMul (HMul.hMul (mt T h⁻¹) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g)

example (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) : subst S T g h x = actO S T g⁻¹ h⁻¹ x := by
  simp [subst, actO]

def modFac (S T : HSp D) (x y : (AE D)ˣ) : ℝ :=
  absFin D x ^ ((T.rank : ℝ) / 2) * absFin D y ^ (-(S.rank : ℝ) / 2)

theorem modFac_pos (S T : HSp D) (x y : (AE D)ˣ) : 0 < modFac S T x y :=
  mul_pos (Real.rpow_pos_of_pos (absFin_pos D x) _) (Real.rpow_pos_of_pos (absFin_pos D y) _)

def SplitLinearModel (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ (f₀ : WO S T → ℂ), IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀ →
    ∀ (c : ℂ), c ≠ 0 → ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
      IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) c f₀ Tm →
    ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h →
    ∀ x y : (AE D)ˣ, IsDetAt e S g x → IsDetAt e T h y →
    ∀ Φ : WO S T → ℂ, IsSBHalf e (latO S T ΛS ΛT fun _ => True) Φ →
      om (g, h) (Tm Φ) =
        Tm fun t => (splitFacO χS χT x y : ℂ) * (modFac S T x y : ℂ) * Φ (subst S T g h t)

def SplitLinearModelConj (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ (f₀ : WO S T → ℂ), IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀ →
    ∀ (c : ℂ), c ≠ 0 → ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
      IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T ΛS ΛT fun _ => True) c f₀ Tm →
    ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h →
    ∀ x y : (AE D)ˣ, IsDetAt e S g x → IsDetAt e T h y →
    ∀ Φ : WO S T → ℂ, IsSBHalf (cA D e) (latO S T ΛS ΛT fun _ => True) Φ →
      om (g, h) (Tm Φ) =
        Tm fun t => (splitFacO χS χT x y : ℂ) * ((modFac S T x y)⁻¹ : ℝ) * Φ (subst S T g h t)

end GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm

end
