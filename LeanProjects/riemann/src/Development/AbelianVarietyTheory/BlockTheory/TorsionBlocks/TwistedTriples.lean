import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

variable (D : D7)

abbrev Trip (a : D.nd.Loc) : Type := D.ntw.Sig (D.ntw.twOf a)

def rhoTrip (a : D.nd.Loc) (s : Trip D a) : GE D.nd →* GL (Fin D.R.r) (D.nd.O a) :=
  mapRep (D.ntw.twist₂ a) (D.ntw.rhoS (D.ntw.twOf a) s)

def chiTrip (a : D.nd.Loc) (s : Trip D a) : GE D.nd →* (D.nd.O a)ˣ :=
  (Units.map (D.ntw.twist₂ a).toMonoidHom).comp
    (D.ntw.chi1 (D.ntw.twOf a) (D.ntw.jS (D.ntw.twOf a) s) (D.ntw.side (D.ntw.twOf a) s))

def tTrip (a : D.nd.Loc) (s : Trip D a) : GE D.nd →* Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a) :=
  twistM ((Units.coeHom _).comp (rhoTrip D a s)) (chiTrip D a s)⁻¹

def badS (a : D.nd.Loc) : Set (HeightOneSpectrum (𝓞 D.host.E)) :=
  {v | ((∃ k, v ∈ placesOver D.host.E (D.host.g k)) ∨ v ∈ D.ntw.pD (D.ntw.twOf a)) ∧
    v ∉ placesOver D.host.E (D.nd.l a)}

def selT (a : D.nd.Loc) (s : Trip D a) (ψ : GE D.nd →* (D.nd.O a)ˣ) :
    Submodule (D.nd.O a) (H1 (WKG (twistM (tTrip D a s) ψ⁻¹))) :=
  Br.selG D.nd.plOm (D.nd.l a) (D.loc (D.nd.l a)) (D.nbr a) (badS D a ∪ ↑(D.nd.Q a))
    (twistM (tTrip D a s) ψ⁻¹)

def sTFin (a : D.nd.Loc) (s : Trip D a) (ψ : GE D.nd →* (D.nd.O a)ˣ) : Prop :=
  Module.length (D.nd.O a) ↥(selT D a s ψ) < ⊤

def sT_vp (a : D.nd.Loc) (s : Trip D a) (ψ : GE D.nd →* (D.nd.O a)ˣ) : ℚ :=
  lenUnit (O := D.nd.O a) (D.nd.l a) ↥(selT D a s ψ)

def psiAt (a : D.nd.Loc) (s : Trip D a) : GE D.nd →* (D.nd.O a)ˣ :=
  if D.ntw.side (D.ntw.twOf a) s = D.ntw.twSide a then D.ntw.psiL a else (D.ntw.psiL a)⁻¹

def IsGoodRow (a : D.nd.Loc) (σ : D.what₂.FT) : Prop :=
  D.what₂.isot (D.nd.j a) σ ≠ ⊥ ∧ D.nd.goodRow σ

def IsRhoOfRow (a : D.nd.Loc) (σ : D.what₂.FT) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O a)) : Prop :=
  IsSSRep (mapRep (algebraMap (D.nd.O a) (Kf D.nd a)) ρ) ∧
  ∀ᶠ w in Filter.cofinite, IsSplitPl D.host w →
    ∀ (B : ValuationSubring D.nd.Om) (g : GE D.nd), IsPlaceOver (F := D.host.E) B w →
      IsFrob (F := D.host.E) B (normV w) g →
      ((ρ g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)).charpoly.map
          (iotaO D.nd D.naut a) =
        galPol D.naut (D.naut.lpTw (D.naut.lpChar (D.naut.locW a σ w) (D.naut.locG D.naut.etaTinv w))
          ((1 - (D.R.nV : ℝ)) / 2))

def IsTripleOf (a : D.nd.Loc) (σ : D.what₂.FT) (s : Trip D a) : Prop :=
  D.ntw.jS (D.ntw.twOf a) s = D.nd.j a ∧ D.ntw.side (D.ntw.twOf a) s = D.ntw.twSide a ∧
    IsRhoOfRow D a σ (rhoTrip D a s)

def TripAll : Prop :=
  ∀ (a : D.nd.Loc) (σ : D.what₂.FT), IsGoodRow D a σ → ∃ s : Trip D a, IsTripleOf D a σ s

def IsRowOf (a : D.nd.Loc) (π : D.nd.X a) (σ : D.what₂.FT) : Prop :=
  IsGoodRow D a σ ∧ ∃ Sg : List (Part D.naut.CG),
    HasParamW D.nd D.naut a σ Sg ∧ HasParamX D.nd D.naut a π Sg

def Attached (a : D.nd.Loc) (π : D.nd.X a) (s : Trip D a) : Prop :=
  ∃ σ, IsRowOf D a π σ ∧ IsTripleOf D a σ s

def IsRhoOfPt (a : D.nd.Loc) (π : D.nd.X a) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O a)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a))) ∧
  ∃ r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O a), IsHeckeGalois D.nd a π r ∧
    ∃ e : (Fin D.R.nV → KK D.nd a) ≃ₗ[KK D.nd a] ((Fin D.R.r → KK D.nd a) × (Fin D.R.t → KK D.nd a)),
      ∀ g u, e ((((r g : GL (Fin D.R.nV) (D.nd.O a)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O a)).map
          (toK D.nd a)).mulVec u) =
        ((((ρ g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)).map
            (toK D.nd a)).mulVec (e u).1,
          fun c : Fin D.R.t =>
            toK D.nd a ((D.nd.chi a ((c : ℕ) + 1) g : (D.nd.O a)ˣ) : D.nd.O a) * (e u).2 c)

def ind2 (l : ℕ) : ℚ := if l = 2 then 1 else 0

def epsL (l : ℕ) : ℚ := ((l : ℚ) ^ 2)⁻¹

def TwistSmallAt (a : D.nd.Loc) : Prop :=
  ∃ ε : Trip D a → ℝ, (∀ s, 0 ≤ ε s) ∧ ∑ s, ε s ≤ (epsL (D.nd.l a) : ℝ) ∧
    ∀ s, sTFin D a s (psiAt D a s) ∧ (sT_vp D a s (psiAt D a s) : ℝ) ≤ (ind2 (D.nd.l a) : ℝ) + ε s

def selEq_at : Prop :=
  ∀ (a : D.nd.Loc) (π : D.nd.X a), π ∈ D.nd.Zgood a →
    (∃ s, Attached D a π s) ∧
    ∀ (s : Trip D a), Attached D a π s →
      ∀ ρ : D.nd.X a → (GE D.nd →* GL (Fin D.R.r) (D.nd.O a)), IsRhoOfPt D a π (ρ π) →
        (Br.sFin D.loc D.nbr a ρ π ↔ sTFin D a s (D.ntw.psiL a)) ∧
        Br.sPi D.loc D.nbr a ρ π = sT_vp D a s (D.ntw.psiL a)

def selBound_at : Prop :=
  ∀ (a : D.nd.Loc), TwistSmallAt D a → ∀ (π : D.nd.X a), π ∈ D.nd.Zgood a →
    ∀ ρ : D.nd.X a → (GE D.nd →* GL (Fin D.R.r) (D.nd.O a)), IsRhoOfPt D a π (ρ π) →
      Br.sFin D.loc D.nbr a ρ π ∧
      Br.sPi D.loc D.nbr a ρ π ≤ ind2 (D.nd.l a) + epsL (D.nd.l a) ∧
      (D.nd.l a ≠ 2 → Br.sPi D.loc D.nbr a ρ π + epsL (D.nd.l a) ≤ 2 * epsL (D.nd.l a)) ∧
      (D.nd.l a = 2 → Br.sPi D.loc D.nbr a ρ π + epsL (D.nd.l a) ≤ 3 / 2)

def dGood (j : ℕ) (w : D.what₂.places.Pl) : ℕ :=
  ∑ a ∈ D.nd.locs j w, ∑ π ∈ D.nd.Zgood a, D.nd.mult a π

def selSum_at : Prop :=
  ∀ (j : ℕ) (w : D.what₂.places.Pl), (∀ a ∈ D.nd.locs j w, TwistSmallAt D a) →
    ∀ ρ : ∀ a : D.nd.Loc, D.nd.X a → (GE D.nd →* GL (Fin D.R.r) (D.nd.O a)),
      (∀ a ∈ D.nd.locs j w, ∀ π ∈ D.nd.Zgood a, IsRhoOfPt D a π (ρ a π)) →
      (∀ a ∈ D.nd.locs j w, ∀ π ∈ D.nd.Zgood a, Br.sFin D.loc D.nbr a (ρ a) π) ∧
      ∑ a ∈ D.nd.locs j w, ∑ π ∈ D.nd.Zgood a, (D.nd.mult a π : ℚ) * Br.sPi D.loc D.nbr a (ρ a) π ≤
        (dGood D j w : ℚ) * (ind2 (D.what₂.places.resChar w) + epsL (D.what₂.places.resChar w))

def tie_at : Prop := TripAll D → selEq_at D ∧ selBound_at D ∧ selSum_at D

def GoodPtHasRow : Prop :=
  ∀ (a : D.nd.Loc) (π : D.nd.X a), π ∈ D.nd.Zgood a → ∃ σ, IsRowOf D a π σ

def GoodPtResIrr : Prop :=
  ∀ (a : D.nd.Loc) (π : D.nd.X a), π ∈ D.nd.Zgood a →
    ∀ ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O a), IsRhoOfPt D a π ρ → AbsIrrSub (redRep D.nd a ρ) ⊤

def tie_step : Prop := GoodPtHasRow D → GoodPtResIrr D → tie_at D

def tieF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, tie_at (Fm.D x i)

def tieClosed (𝒞 : FamClass) : Prop := Closed 𝒞 (fun Fm _ => tieF Fm)

theorem badS_eq (a : D.nd.Loc) : badS D a = ↑(D.nd.S a) := by
  ext v
  have h := D.ntw.pD_eq (D.ntw.twOf a)
  rw [D.ntw.twOf_l a] at h
  have h' : v ∈ D.ntw.pD (D.ntw.twOf a) ↔
      v ∈ placesOver D.host.E (if D.nd.l a = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← h]; rfl
  simp only [badS, Set.mem_setOf_eq, Finset.mem_coe, D.nd.S_def, h', Fin.exists_fin_two, or_assoc]

example : ind2 2 + epsL 2 + epsL 2 = 3 / 2 := by norm_num [ind2, epsL]

end GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples

end
