import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal
open GlobalTheory.LocLanglands GlobalTheory.Published GlobalTheory.Pst GlobalTheory.TripleGal UpperTheory.V.W UpperTheory.V

namespace UpperTheory.Lit.CharWD

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {A : ValuationSubring Ω} {w : Plc F} (P : LocPrime l) (ι : Qbar l ≃+* ℂ) (h : IsPlaceOver A w)
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
  (hj : GlobalTheory.Pst.Induces Bw)

def WDis (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (ξ : Weil h →* (Qbar l)ˣ) : Prop :=
  IsPstAt P Bw (rk1 κ) ∧ ∃ hs, wdAt P ι Bw h hj (rk1 κ) = WD.lpOfChar h ((Units.map ι.toRingHom.toMonoidHom).comp ξ) hs

end

def ChBasic : Prop :=
  ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    {A : ValuationSubring Ω} {w : Plc F} (ι : Qbar l ≃+* ℂ) (h : IsPlaceOver A w)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
    (hj : GlobalTheory.Pst.Induces Bw),
    (∀ κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ, Continuous κ → IsPstAt (Loc.PP l) Bw (rk1 κ) →
      ∃! ξ, WDis (Loc.PP l) ι h Bw hj κ ξ) ∧
    (∀ (κ κ' : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (ξ ξ' : Weil h →* (Qbar l)ˣ), Continuous κ → Continuous κ' →
      WDis (Loc.PP l) ι h Bw hj κ ξ → WDis (Loc.PP l) ι h Bw hj κ' ξ' → IsPstAt (Loc.PP l) Bw (rk1 (κ * κ')) →
      WDis (Loc.PP l) ι h Bw hj (κ * κ') (ξ * ξ')) ∧
    ∀ ξ : Weil h →* (Qbar l)ˣ, WDis (Loc.PP l) ι h Bw hj ((cycBar F Ω l).comp (Dec (F := F) A).subtype) ξ →
      ∀ σ, (ξ σ : Qbar l) = ((normV w : ℕ) : Qbar l) ^ deg σ

def ChRes : Prop :=
  ∀ {F F' Ω : Type} [Field F] [NumberField F] [Field F'] [NumberField F'] [Field Ω] [Algebra F F'] [Algebra F Ω] [Algebra F' Ω]
    [IsScalarTower F F' Ω] [IsAlgClosure F Ω] [IsAlgClosure F' Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F}
    {w' : Plc F'} (ι : Qbar l ≃+* ℂ) (h : IsPlaceOver A w) (h' : IsPlaceOver A w')
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
    (hj : GlobalTheory.Pst.Induces Bw), ∃ (O' : Type) (_ : CommRing O') (_ : Algebra ℤ_[l] O') (_ : TopologicalSpace O')
    (Bw' : LocBridge l F' Ω (Dec (F := F') A) O') (hj' : GlobalTheory.Pst.Induces Bw'),
    ∀ (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (κ' : ↥(Dec (F := F') A) →* (Qbar l)ˣ), Continuous κ →
      (∀ (g : ↥(Dec (F := F) A)) (g' : ↥(Dec (F := F') A)), (∀ z, (g : G F Ω) z = (g' : G F' Ω) z) → κ g = κ' g') →
      ∀ ξ : Weil h →* (Qbar l)ˣ, WDis (Loc.PP l) ι h Bw hj κ ξ → ∃ ξ' : Weil h' →* (Qbar l)ˣ,
        WDis (Loc.PP l) ι h' Bw' hj' κ' ξ' ∧
        ∀ (σ : Weil h) (σ' : Weil h'), (∀ z, (σ : G F Ω) z = (σ' : G F' Ω) z) → ξ σ = ξ' σ'

def ChCoef : Prop :=
  ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    {A : ValuationSubring Ω} {w : Plc F} (ι : Qbar l ≃+* ℂ) (h : IsPlaceOver A w)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
    (hj : GlobalTheory.Pst.Induces Bw) (s : GQ l) (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (ξ : Weil h →* (Qbar l)ˣ), Continuous κ →
    WDis (Loc.PP l) ι h Bw hj κ ξ →
    WDis (Loc.PP l) ι h Bw hj ((Units.map (s : Qbar l →* Qbar l)).comp κ) ((Units.map (s : Qbar l →* Qbar l)).comp ξ)

def ChIndep : Prop :=
  ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    {A : ValuationSubring Ω} {w : Plc F} (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (ι : Qbar l ≃+* ℂ) (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ)
      (ξ : Weil h →* (Qbar l)ˣ), Continuous κ → WDis (Loc.PP l) ι h Bw hj κ ξ → WDis P ι h Bw hj κ ξ

def ArtNorm : Prop :=
  ∀ {F F' Ω : Type} [Field F] [NumberField F] [Field F'] [NumberField F'] [Field Ω] [Algebra F F'] [Algebra F Ω] [Algebra F' Ω]
    [IsScalarTower F F' Ω] [IsAlgClosure F Ω] [IsAlgClosure F' Ω] (l : ℕ) [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F}
    {w' : Plc F'} (h : IsPlaceOver A w) (h' : IsPlaceOver A w'), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal →
    ∃ (res : Emb l w' → Emb l w) (N : (w'.adicCompletion F')ˣ →* (w.adicCompletion F)ˣ),
      (∀ τ' (x : F), (res τ').1 (algebraMap F _ x) = τ'.1 (algebraMap F' _ (algebraMap F F' x))) ∧
      (∀ (τ : Emb l w) (y : (w'.adicCompletion F')ˣ),
        τ.1 (N y : w.adicCompletion F) = ∏ᶠ (τ' : Emb l w') (_ : res τ' = τ), τ'.1 (y : w'.adicCompletion F')) ∧
      ∀ (a : Weil h →* (w.adicCompletion F)ˣ) (a' : Weil h' →* (w'.adicCompletion F')ˣ), IsLocalArtin h a → IsLocalArtin h' a' →
        ∀ (σ : Weil h) (σ' : Weil h'), (∀ z, (σ : G F Ω) z = (σ' : G F' Ω) z) → a σ = N (a' σ')

def ExField : Prop :=
  ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {A : ValuationSubring Ω} {w : Plc F}
    (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ σ : Weil h, deg σ = -1 →
    ∀ V ∈ nhds (1 : (w.adicCompletion F)ˣ),
    ∃ (F' : IntermediateField F Ω) (_ : NumberField F') (_ : IsAlgClosure F' Ω) (w' : Plc F') (h' : IsPlaceOver A w'),
      (∃ σ' : Weil h', ∀ z, (σ : G F Ω) z = (σ' : G F' Ω) z) ∧
      ∀ (s : Weil h) (s' : Weil h'), deg s' = 0 → (∀ z, (s : G F Ω) z = (s' : G F' Ω) z) → a s ∈ V

def EmbOrbit : Prop :=
  ∀ {F : Type} [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (w : Plc F) (c : Emb l w → Qbar l),
    (∀ (s : GQ l) (τ τ' : Emb l w), (∀ x, τ'.1 x = s (τ.1 x)) → c τ' = s (c τ)) →
    Nonempty (Emb l w) → ∃ u : w.adicCompletion F, ∀ τ, c τ = τ.1 u

def LocWD : Prop :=
  ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    {A : ValuationSubring Ω} {w : Plc F} (ι : Qbar l ≃+* ℂ) (h : IsPlaceOver A w)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
    (hj : GlobalTheory.Pst.Induces Bw) (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a →
    ∀ (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ), Continuous κ → ∀ wt : Emb l w → ℤ, IsLocAlg h κ wt →
      ∃ ξ, WDis (Loc.PP l) ι h Bw hj κ ξ ∧ ∀ σ, (ξ σ : Qbar l) =
        (κ (Subgroup.inclusion (Weil_le_Dec h) σ) : Qbar l) * ∏ᶠ τ : Emb l w, τ.1 (a σ : w.adicCompletion F) ^ wt τ

end UpperTheory.Lit.CharWD
