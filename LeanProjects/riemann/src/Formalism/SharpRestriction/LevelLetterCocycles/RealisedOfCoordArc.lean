import Formalism.SharpRestriction.LevelLetterCocycles.FinalLevelsOf

noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    [Fintype (K →ₐ[Qp] LL)]

def CoordSteps (hR : Ring9 W) (e : W.DD W.one) : Prop :=
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
    ∃ (C₁ : Coord W (baseIdOf hR) T₁) (C₂ : Coord W (baseIdOf hR) T₂) (C₀ : Coord W (baseIdOf hR) W.one)
      (_h : CoordHom C₁ C₂ F) (e₀ : C₀.V), ∀ i, C₀.t i e₀ = (letE i : LetA O n) • e

def ArcSteps (Lb : LevB W) (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) : Prop :=
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L),
    GoodCoeffs (K := K) (Qp := Qp) (LL := LL) (O := O) (V := T₁.V) →
    CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
    ∀ (C₁ : Coord W (baseIdOf hR) T₁) (C₂ : Coord W (baseIdOf hR) T₂) (hC : CoordHom C₁ C₂ F),
    ∀ (j Gp S η h : ℕ) (ty : ZMod n → LT) (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ)
      (hCu : CutsOK n j ty cuts arcLen),
      KindJumps PD T₁ W.emb Gp S η ty →
      (∀ τ : K →ₐ[Qp] LL, JumpsInV PD T₁.ρ τ (Set.Icc (-(h : ℤ)) h)) →
      gPar Gp S η ≤ h → SizesOK (gPar Gp S η) S h ty → ThickLe2 ty cuts arcLen →
      ∀ c ∈ (cutsOf hCu).cuts,
        ∃ (κ₁ κ₂ : PowerSeries O) (r₁ r₂ : ℕ) (e₁ : Fin r₁ → C₁.V) (e₂ : Fin r₂ → C₂.V)
          (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))
          (Hy₁ : LvHyp Lb hR uZ ιZ C₁ c ((cutsOf hCu).ell c)
            (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p (E.HArc (gPar Gp S η) Gp S η (kdOf ty) (bbOf ty) c)
              ((cutsOf hCu).ell c)) κ₁ (lamOf C₁ c ((cutsOf hCu).ell c) e₁))
          (Hy₂ : LvHyp Lb hR uZ ιZ C₂ c ((cutsOf hCu).ell c)
            (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p (E.HArc (gPar Gp S η) Gp S η (kdOf ty) (bbOf ty) c)
              ((cutsOf hCu).ell c)) κ₂ (lamOf C₂ c ((cutsOf hCu).ell c) e₂))
          (Mh : MapHyp hR uZ ιZ F c),
          (∀ ϖ : O, Irreducible ϖ →
            LevSteps Hy₁ ϖ j (E.parM (baseIdOf hR).Bs.ℓ h (gPar Gp S η)) (gPar Gp S η) Gp S η
                (E.kindAt (kdOf ty) c) (E.sizeAt (bbOf ty) c) e₁ ∧
            LevSteps Hy₂ ϖ j (E.parM (baseIdOf hR).Bs.ℓ h (gPar Gp S η)) (gPar Gp S η) Gp S η
                (E.kindAt (kdOf ty) c) (E.sizeAt (bbOf ty) c) e₂) ∧
          MapSteps hC Hy₁ Hy₂ Mh j (E.parM (baseIdOf hR).Bs.ℓ h (gPar Gp S η)) (gPar Gp S η) η
            (E.kindAt (kdOf ty) c) (E.sizeAt (bbOf ty) c) e₁ e₂ P

end Formalism.MainNotions.N.Ln03
