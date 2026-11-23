import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftIntertwinesLevelLiftsLowestKTypeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActionPreservesPrincipalFlagMultiplic

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaShiftSmooth

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levChi_flag_eq_one (R : RealDat D A Ks) (i : Fin D.R.m) (κ : GA D (Wc D i)) :
    levChi (Wc D i) (R.βW i) (flagL (R.datWp i R.triv)) κ = 1 := by
  have h2 : ext1 (flagL (R.datWp i R.triv)).P.H (flagL (R.datWp i R.triv)).P.chi
      (rTup (R.βW i) (flagL (R.datWp i R.triv)) (finE (Wc D i) κ)) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi levFn
  rw [h2]
  have hs : (flagL (R.datWp i R.triv)).s = 0 := rfl
  have hQ : (flagL (R.datWp i R.triv)).Q = ∅ := rfl
  rw [hs, hQ]
  simp

theorem exists_translate (R : RealDat D A Ks) (hθ : IsInfFam R.θ) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (g0 : G0 R.Pg D.R.r) (κ' : GA D (Wc D i)) (hκ' : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')
    (X : MMap (R.MW i σ)) (hX : X ∈ R.Wall i σ) :
    ∃ U ∈ R.Wall i σ, ∀ v x, U v x = X v (x * κ') := by
  refine ⟨postOn (R.MW i σ) (actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0) X,
    GlobalTheory.FlagAction.finiteGroupAction_preserves_principalFlagMultiplicity R.θ (R.MW i σ) hθ (R.βW i) (R.datWp i R.triv) g0 X hX _ fun _ => rfl, fun v x => ?_⟩
  have hT : HasType (Wc D i) (R.βW i) (R.datWp i R.triv) (X v) := fun k hk h =>
    (GlobalTheory.mult_value_left_cont_level R.θ (R.MW i σ) _ _ X hX v).2.2 k hk h
  have h1 := level_action_spec (V := Wc D i) (β := R.βW i) (L := R.datWp i R.triv) hT ⟨κ', hκ'⟩ κ' hκ' x
  rw [levChi_flag_eq_one, inv_one, one_mul] at h1
  exact h1

theorem translate_of_lowT (R : RealDat D A Ks) (hθ : IsInfFam R.θ) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (g0 : G0 R.Pg D.R.r) (κ' : GA D (Wc D i)) (hκ' : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')
    (X X' : MMap (R.MW i σ)) (hX : X ∈ R.Wall i σ) (hX' : X' ∈ R.Wall i σ)
    (h : ∀ (v : ∀ ρ, lowT (R.MW i σ) ρ) (x : GA D (Wc D i)), X' (fun ρ => v ρ) x = X (fun ρ => v ρ) (x * κ'))
    (v : (R.MW i σ).Vec) (x : GA D (Wc D i)) : X' v x = X v (x * κ') := by
  obtain ⟨U, hU, hUv⟩ := exists_translate R hθ i σ g0 κ' hκ' X hX
  have h0 : X' - U = 0 := GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ (R.MW i σ) R.θ hθ
    (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ (X' - U) (Submodule.sub_mem _ hX' hU) fun w => by
      funext z
      exact sub_eq_zero.2 ((h w z).trans (hUv _ z).symm)
  rw [sub_eq_zero.1 h0]
  exact hUv v x

theorem thF_shift_all : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' → ∀ y y' : (R.HV i t).H, (∀ h, R.extV i t y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ)) → ∀ (v : (R.MW i (sg0 D A)).Vec) (x : GA D (Wc D i)), R.thF i t y' v x = R.thF i t y v (x * κ') := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hM hP i t g0 κ κ' hκ hκ' y y' hy
  exact translate_of_lowT R hM.inf i (sg0 D A) g0 κ' hκ' (R.thF i t y) (R.thF i t y') (hP.thF_mem i t y)
    (hP.thF_mem i t y') (GlobalTheory.T.thetaLift_intertwines_levelLifts_lowestKType R hL hM hP i t g0 κ κ' hκ hκ' y y' hy)

end GlobalTheory.ThetaShiftSmooth

end
