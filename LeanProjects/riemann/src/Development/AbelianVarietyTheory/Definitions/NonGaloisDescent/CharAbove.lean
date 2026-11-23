import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TameGeneratorProjectors
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

noncomputable section

namespace GlobalTheory.TripleGal

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.Pst
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf)

def rk1 {Γ K : Type} [Group Γ] [CommRing K] (χ : Γ →* Kˣ) : Γ →* GL (Fin 1) K :=
  (Units.map (Matrix.scalar (Fin 1) : K →+* Matrix (Fin 1) (Fin 1) K).toMonoidHom).comp χ

def Temp (D : D7) : Prop :=
  ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π → ∀ w, D.naut.tempered (D.naut.locG π w)

open Classical in

def GalAbove (D : D7) : Prop :=
  ∀ (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar l)), IsGaloisRepOf D π l ι r →
    ∀ w ∈ placesOver D.host.E l, ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw →
      IsdRAt (D.loc l) Bw (r.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) ∧
      (D.naut.unr (D.naut.locG π w) → IsCrysAt (D.loc l) Bw (r.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)) ∧
      (D.naut.mono0 (D.naut.locG π w) → IsPotCrysAt (D.loc l) Bw (r.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)) ∧
      ∀ (τ : D.host.E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        ∃ J : Multiset ℤ, IsJumpsAt (D.loc l) Bw (r.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ J ∧
          J.map (fun n : ℤ => (n : ℂ)) =
            (D.naut.infG π (ι.toRingHom.comp τ)).map fun z => ((D.R.r : ℂ) - 1) / 2 - z

def CharAbove : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Qbar l ≃+* ℂ)
    (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ) (μ : G E Ω →* (Qbar l)ˣ),
    IsAlgPos χ n → Continuous μ → IsLAdicOf art ι χ n μ →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
      IsdRAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) ∧ IsPotCrysAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) ∧
      (χ.UnrAt w → IsCrysAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype)) ∧
      ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) τ {-n (ι.toRingHom.comp τ)}

def MonoG (D : D7) : Prop :=
  ∀ (σ : D.what₂.FT) (π : D.naut.CG D.R.r), D.nd.goodRow σ → D.naut.csd π → D.naut.ralg π →
    (∀ k v, D.nd.lab k σ v = D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG π (D.naut.plGw k v))) →
    ∀ k, ∀ w ∈ placesOver D.host.E (D.host.g k), D.naut.mono0 (D.naut.locG π w)

structure Mid (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i) : Prop where
  unr : UnrRho i s
  hodge : HodgeL bkP i s
  pure : ∃ ι, Pure i s ι
  jumps : ∃ ι J, JumpsAre bkP i s ι J ∧ GoodJ D J
  dual : FrobDual i s
  hk : HkFrob i s

def LocTrue (D : D7) (i : D.ntw.Tw) : Prop :=
  ∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI)

end GlobalTheory.TripleGal

end
