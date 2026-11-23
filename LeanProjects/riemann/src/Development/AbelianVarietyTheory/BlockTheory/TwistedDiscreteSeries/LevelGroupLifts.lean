import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelGroupLifts

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def idealLatHat (V : HSp D) (I : Ideal (𝓞 D.host.E)) :
    AddSubgroup (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {w | ∃ b ∈ I, ∃ z ∈ latGHat V 1, w = halfVec V b z}

def IsLift (V : HSp D) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (Dw : Datum H) (l : Level H)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (g : LaMod Dw l ≃ₗ[𝓞 D.host.E] LaMod Dw l) (k : GA D V) : Prop :=
  k ∈ GfC V ∧ gLat V k = (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) ∧
    ∀ a b : Dw.La, (Submodule.Quotient.mk b : LaMod Dw l) = g (Submodule.Quotient.mk a) →
      (finHom V k).1.mulVec (finVec V (ι a)) - finVec V (ι b) ∈ idealLatHat V l.Mb

abbrev LevGrp (T : CoreJ D) (j : ℕ) : Type :=
  LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l

def iotaAt (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (hr : (T.V j σ).rank = D.R.r) :
    (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (T.V j σ).rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j

def IsGeoRep (T : CoreJ D) (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (ρ : LevGrp T j →* (T.cuspA j a n →ₗ[T.Q.c.F] T.cuspA j a n)) : Prop :=
  ∀ g f, ((ρ g f : T.cuspA j a n) : T.R j) =
    actLev (Xo := T.Q.Xo j) T.Q.c (GlobalTheory.FormTies.levFull (T.Q.Dw j) T.Q.l) g (f : T.R j)

def IsChiDet (T : CoreJ D) (j : ℕ) {V : HSp D} (ℓ : LevGrp T j → GA D V) (chi : LevGrp T j →* T.Q.c.Fˣ) : Prop :=
  ∀ g x, FinUnit x → IsDetRoot V (ℓ g) x →
    T.σ₀ ((chi g : T.Q.c.Fˣ) : T.Q.c.F) * ((T.chiW j T.σ₀ x : Circle) : ℂ) = 1

def UnitConstEquivariant : Prop :=
  ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n →
    ∀ (ρ : LevGrp T j →* (T.cuspA j a n →ₗ[T.Q.c.F] T.cuspA j a n)), IsGeoRep T j a n ρ →
    ∀ (chi : LevGrp T j →* T.Q.c.Fˣ) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ →
    ∀ (hr : (T.V j σ).rank = D.R.r) (ℓ : LevGrp T j → GA D (T.V j σ)),
      (∀ g, IsLift (T.V j σ) (T.Q.Dw j) T.Q.l (iotaAt T j σ hr) g (ℓ g)) → IsChiDet T j ℓ chi →
      ∃ c' : (T.U j σ).Comp → ℂ, CUnit c' ∧
        EquivariantFiniteGroup (T.V j σ) σ ((rdU (T.U j σ)).comp (T.cuspA j a n).subtype) (T.dict j σ)
          (muPin (T.V j σ) (T.dict j σ) (T.mu j σ) c') ρ chi ℓ

example (V : HSp D) : (1 : GA D V) ∈ GfC V ∧
    gLat V 1 = (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) := by
  refine ⟨one_mem _, ?_⟩
  simp [gLat]

end GlobalTheory.IndefiniteRowSideFullHecke.LevelGroupLifts
