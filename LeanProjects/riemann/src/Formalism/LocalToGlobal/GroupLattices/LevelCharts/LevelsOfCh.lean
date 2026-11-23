import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FiniteCompG
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.CompletionIntegersIff
import Formalism.SharpRestriction.GrowthBounds.DataGChain

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
  {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

structure FrS (I : LocId L p nV W Qq) {N : ℕ} (Lb : Submodule (𝓞 E) (Fin N → E)) where
  fr : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → GL (Fin N) (w.adicCompletion F)
  fr_lat : ∀ w h (t : Fin N → w.adicCompletion F),
    (∃ x ∈ Formalism.L2.Herm.locL w Lb, ∀ a, (I.spl w h (x a)).1 = t a) ↔
      ∀ a, (((fr w h)⁻¹ : GL (Fin N) (w.adicCompletion F)) :
        Matrix (Fin N) (Fin N) (w.adicCompletion F)).mulVec t a ∈ w.adicCompletionIntegers F

def FrS.frQ {I : LocId L p nV W Qq} {N : ℕ} {Lb : Submodule (𝓞 E) (Fin N → E)} (B : FrS I Lb) (v : Fin nV) :
    GL (Fin N) Qq := bc (I.eQ v).symm.toRingHom (B.fr (I.pl v).1 (I.pl v).2)

def LocId.frS (I : LocId L p nV W Qq) : FrS I L.Lb := ⟨I.fr, I.fr_lat⟩

structure StepAt (I : LocId L p nV W Qq) (O : Type) [CommRing O] (N : ℕ) where
  J : Matrix (Fin N) (Fin N) E
  Lb : Submodule (𝓞 E) (Fin N → E)
  Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F))
  fr : FrS I Lb
  ψ : awayG sp.cm.sig J Uloc p →* Oˣ

  eps : UJ (sp.cm.sig : E →+* E) J →* Oˣ
  fin : Finite (compG sp.cm.sig J Uloc p)

namespace StepAt

variable {I : LocId L p nV W Qq} {O : Type} [CommRing O] {N : ℕ} (St : StepAt I O N)

abbrev Up : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := awayG sp.cm.sig St.J St.Uloc p

abbrev comp : Type := compG sp.cm.sig St.J St.Uloc p

abbrev rep (i : St.comp) : UPts sp.cm.sig St.J (FiniteAdeleRing (𝓞 F) F) := repG sp.cm.sig St.J St.Uloc p i

end StepAt

variable {n' : ℕ} {O Kf : Type} [IsDomain W] [IsDiscreteValuationRing W]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}

abbrev levStep (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ) {m' : ℕ} (lam' : Fin nV → Fin n' → Fin (m' + 1) → ℤ)
    (dom' : ∀ v, IsDominant (lam' v)) {N : ℕ} (hk : m' + 1 = N) {I : LocId L p nV W Qq} (St : StepAt I O N) (i : St.comp) :
    Level (placesConst hS nV m' r lam' dom') :=
  { levC sp.cm.sig St.J St.Up hS nV r lam' dom' hk I.iw St.fr.frQ St.ψ
      (St.rep i : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) with
    χ := St.ψ.comp (gamToUp sp.cm.sig St.J St.Up (St.rep i : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) *
      St.eps.comp (gamC sp.cm.sig St.J St.Up (St.rep i : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))).subtype }

abbrev levelsOf (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ)
    (y : compL L p → UPts sp.cm.sig sp.gram0 (Formalism.L2.Herm.Af F)) [Finite (compL L p)] (e : ℕ)
    (Fl : Fills (gatOfLevel L hS nV r lam0 dom hk I ψ y e)) (M : ℕ) (Nj : ℕ → ℕ)
    (hN : ∀ i, i < M → m + (i + 1) * (Fl.t + 1) + 1 = Nj i) (St : ∀ i, i < M → StepAt I O (Nj i)) : Levels Fl where
  compS := fun i => (h : i < M) ×' (St i h).comp
  finS := fun i => by
    haveI : ∀ h : i < M, Finite (St i h).comp := fun h => (St i h).fin
    exact Fintype.ofFinite _
  levS := fun i c => levStep hS r (fun v s => liftWt Fl.t m (lam0 v s) (fun a => Fl.w v a s) (i + 1)) (Fl.domJ (i + 1))
    (hN i c.1) (St i c.1) c.2

abbrev levelsOfCh (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ)
    (y : compL L p → UPts sp.cm.sig sp.gram0 (Formalism.L2.Herm.Af F)) [Finite (compL L p)] (e : ℕ)
    (Fl : Fills (gatOfLevel L hS nV r lam0 dom hk I ψ y e)) (M : ℕ) (Nj : ℕ → ℕ)
    (hN : ∀ i, i < M → m + (i + 1) * (Fl.t + 1) + 1 = Nj i) (Ch : ∀ i, i < M → Type) [∀ i h, Finite (Ch i h)]
    (St : ∀ i (h : i < M), Ch i h → StepAt I O (Nj i)) : Levels Fl where
  compS := fun i => (h : i < M) ×' Σ b : Ch i h, (St i h b).comp
  finS := fun i => by
    haveI : ∀ (h : i < M) (b : Ch i h), Finite (St i h b).comp := fun h b => (St i h b).fin
    exact Fintype.ofFinite _
  levS := fun i c => levStep hS r (fun v s => liftWt Fl.t m (lam0 v s) (fun a => Fl.w v a s) (i + 1)) (Fl.domJ (i + 1))
    (hN i c.1) (St i c.1 c.2.1) c.2.2

end Formalism.L2.G
