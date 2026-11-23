import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GeometricConstantEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IpMSelfEqZero

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.GeoActCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.L2.Pj
  Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.GeometricConstantEquiv (Cusp IsLift IsGeo ReadTwist KeepsIntegral IsIntegralForm ConstEquiv IsKappa GeoActAt)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Model

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem levChi_flag (i : Fin D.R.m) (k : GA D (Wc D i)) : levChi _ (R.βW i) (flagL (R.datWp i R.triv)) k = 1 := by
  simp [levChi, Formalism.L2.DIV.levFn, flagL, withP, LevCh.datWp, datY, LevelP.full]
  first
    | exact subgroupCharExtension_one_apply _ _
    | (unfold Formalism.L2.DIV.ext1; exact dite_eq_right_iff.2 fun _ => rfl)

private theorem wall_apply_mul_eq_levChi_mul_of_mem_levS {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} {T : MMap (R.MW i σ)} (hT : T ∈ R.Wall i σ)
    (v : (R.MW i σ).Vec) {k : GA D (Wc D i)} (hk : k ∈ levS _ (R.βW i) (R.datWp i R.triv)) (g : GA D (Wc D i)) :
    T v (g * k) = levChi _ (R.βW i) (R.datWp i R.triv) k * T v g := by
  unfold RealDat.Wall Formalism.IndefR.Mult.Mult at hT
  induction hT using Submodule.span_induction with
  | mem x hx =>
    have hx' : IsMultMap R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i R.triv))
        (levChi _ (R.βW i) (R.datWp i R.triv)) x := hx
    exact hx'.lev v k hk g
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [MultilinearMap.add_apply, Pi.add_apply, hx, hy]
    ring
  | smul a x _ hx =>
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx]
    ring

theorem hasType_e (he : R.models_HW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (y : (R.HW i σ).H) (v : (R.MW i σ).Vec) :
    HasType (Wc D i) (R.βW i) (flag1L (R.datWp i R.triv)) ((R.HW i σ).e y v) := by
  have hm : (R.HW i σ).e y ∈ R.Wall i σ := by
    rw [← (he i σ).2.1]
    exact LinearMap.mem_range_self _ y
  intro k hk h
  exact wall_apply_mul_eq_levChi_mul_of_mem_levS R hm v hk h

theorem actW_apply (he : R.models_HW) {i : Fin D.R.m} (σ : D.what₂.LL →+* ℂ) {g : G} {k : GA D (Wc D i)}
    (hk : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) (y : (R.HW i σ).H) (v : (R.MW i σ).Vec)
    (x : GA D (Wc D i)) : actW R i σ g ((R.HW i σ).e y) v x = (R.HW i σ).e y v (x * k) := by
  have hs := level_action_spec (hasType_e R he i σ y v) ⟨k, hk⟩ k hk x
  rw [levChi_flag R i k, inv_one, one_mul] at hs
  exact hs

end Model

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

theorem cast_mul {V W : HSp D} (h : V = W) (x y : GA D V) :
    cast (congrArg (GA D) h) (x * y) = cast (congrArg (GA D) h) x * cast (congrArg (GA D) h) y := by
  subst h
  rfl

def ReadModel (i : Fin D.R.m) (ρ : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i)) : Prop :=
  ∀ σ g f, (R.HW i σ).e (jTop T R κ v₀ i σ (ρ g f)) =
    σ ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) • actW R i σ g ((R.HW i σ).e (jTop T R κ v₀ i σ f))

structure Ties : Prop where
  laws : LawsJ T
  model : R.models_HW
  act : R.models_gW
  chi : R.grp_chiW
  vec : ∀ i σ, IsChosenExtremalVector R i σ (v₀ i σ)

variable {T R κ v₀}

end GlobalTheory.GeoActCompare
