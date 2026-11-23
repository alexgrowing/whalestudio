import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi

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
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

structure LevSteps {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ}
    {Λ κ : PowerSeries O} {r : ℕ} {lam : Fin r → Dc W T c}
    (Hy : LvHyp Lb hR uZ ιZ C c ell Λ κ lam) (ϖ : O) (j M g G₀ Sz η : ℕ) (kind : ℕ → Kind)
    (b : ℕ → ℕ) (e : Fin r → C.V) : Prop where

  k1b : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).K1b

  k1c : ∀ s < ell, ((lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).lev s).FiniteOrderFixed (baseIdOf hR).Bs.ℓ s

  k1d : ∀ s < ell, ((lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).lev s).PhiGammaCommute

  unitsAt : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).UnitsAt

  compl : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).Compl ϖ

  filt : ∀ s < ell, IsFilt (FilD W T c s)

  jumps : ∀ s < ell, Formalism.ExponentWindows.G.Jumps (kind s) G₀ Sz η (b s) (FilD W T c s)

  mem : (lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).Mem

  locReg : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).LocReg

  pa1b : (lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).LocalizesConst M e

  equiv : (lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).Equiv

  span : Submodule.span (PowerSeries O) (Set.range e) = (latOf C).N (c - (ell : ZMod n))

  ind : LinearIndependent (PowerSeries O) e

  locLIs : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).LocLIs lam

  lamInd : LinearIndependent LL lam

  lamSpan : Submodule.span LL (Set.range lam) = ⊤

theorem finalLevels_of {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ}
    {H : ℕ → ℕ} {κ : PowerSeries O} {r : ℕ} {lam : Fin r → Dc W T c}
    (Hy : LvHyp Lb hR uZ ιZ C c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ lam) (ϖ : O)
    (j M g G₀ Sz η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ) (e : Fin r → C.V)
    (hs : LevSteps Hy ϖ j M g G₀ Sz η kind b e) :
    E.FinalLevels (latOf C) c ell H (lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η)
      (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η) ϖ (W.χΓ W.gam) j M g G₀ Sz η kind b e lam
      (UL lam kind b η) where
  kind_eq := fun _ _ => rfl
  b_eq := fun _ _ => rfl
  η_eq := rfl
  k1b := hs.k1b
  hasU := fun _ _ => rfl
  k1c := hs.k1c
  k1d := hs.k1d
  unitsAt := hs.unitsAt
  compl := hs.compl
  filt := hs.filt
  jumps := hs.jumps
  mem := hs.mem
  locReg := hs.locReg
  pa1b := hs.pa1b
  equiv := hs.equiv
  span := hs.span
  ind := hs.ind
  flDef := fun _ _ _ => Iff.rfl
  locLIs := hs.locLIs
  lamInd := hs.lamInd
  lamSpan := hs.lamSpan
  uIs := fun _ _ _ => Iff.rfl

section ThetaShiftProofs

variable {T₁ T₂ : LocLat G Qp LL O} {C₁ : Coord W (baseIdOf hR) T₁} {C₂ : Coord W (baseIdOf hR) T₂}
  {F : LatHom T₁.L T₂.L} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ} {κ₁ κ₂ : PowerSeries O} {r₁ r₂ : ℕ}
  {lam₁ : Fin r₁ → Dc W T₁ c} {lam₂ : Fin r₂ → Dc W T₂ c}

structure MapSteps (hC : CoordHom C₁ C₂ F)
    (Hy₁ : LvHyp Lb hR uZ ιZ C₁ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₁ lam₁)
    (Hy₂ : LvHyp Lb hR uZ ιZ C₂ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₂ lam₂)
    (Mh : MapHyp hR uZ ιZ F c) (j M g η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ)
    (e₁ : Fin r₁ → C₁.V) (e₂ : Fin r₂ → C₂.V) (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)) : Prop where

  locComm : ∀ s < ell, ∀ (w : C₁.V)
    (hw : w ∈ (latOf C₁).W c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell))
    (hw' : (latHomOf hC).f w ∈ (latOf C₂).W c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell)),
    prEOf Mh (hΔ₁ := Hy₁.delta) (hΔ₂ := Hy₂.delta) ell
        ((lvData Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).loc s ⟨w, hw⟩) =
      (lvData Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).loc s ⟨(latHomOf hC).f w, hw'⟩

  loclComm : ∀ s < ell, ∀ y : Fin r₁ → PowerSeries O,
    prEOf Mh (hΔ₁ := Hy₁.delta) (hΔ₂ := Hy₂.delta) ell
        ((lvData Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).locL s y) =
      (lvData Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).locL s (E.extL P y)

  mapFl : ∀ s < ell, ∀ e ∈ (lvData Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).Fl s,
    prEOf Mh (hΔ₁ := Hy₁.delta) (hΔ₂ := Hy₂.delta) ell e ∈
      (lvData Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).Fl s

  cMap : ∀ s < ell, kind s = Kind.up → Formalism.ExponentWindows.E.CMap (UL lam₁ kind b η s) (UL lam₂ kind b η s) P

  prLIs : ∀ k, (latHomOf hC).f (e₁ k) -
      ∑ l, PowerSeries.C (LinearMap.toMatrix' P l k) • e₂ l ∈
    E.sm (PowerSeries.X : PowerSeries O) ((latOf C₂).N (c - (ell : ZMod n)))

def levelMapOf (hC : CoordHom C₁ C₂ F)
    (Hy₁ : LvHyp Lb hR uZ ιZ C₁ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₁ lam₁)
    (Hy₂ : LvHyp Lb hR uZ ιZ C₂ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₂ lam₂)
    (Mh : MapHyp hR uZ ιZ F c) (j M g η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ)
    (e₁ : Fin r₁ → C₁.V) (e₂ : Fin r₂ → C₂.V) (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))
    (ms : MapSteps hC Hy₁ Hy₂ Mh j M g η kind b e₁ e₂ P) :
    E.LevelMap (latHomOf hC) (lvData Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η)
      (lvData Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η) where
  prE := prEOf Mh ell
  prL := P
  loc_comm := ms.locComm
  locL_comm := ms.loclComm

theorem arc_of_steps (hC : CoordHom C₁ C₂ F)
    (Hy₁ : LvHyp Lb hR uZ ιZ C₁ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₁ lam₁)
    (Hy₂ : LvHyp Lb hR uZ ιZ C₂ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₂ lam₂)
    (Mh : MapHyp hR uZ ιZ F c) (ϖ : O) (j M g G₀ Sz η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ)
    (e₁ : Fin r₁ → C₁.V) (e₂ : Fin r₂ → C₂.V) (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))
    (ls₁ : LevSteps Hy₁ ϖ j M g G₀ Sz η kind b e₁) (ls₂ : LevSteps Hy₂ ϖ j M g G₀ Sz η kind b e₂)
    (ms : MapSteps hC Hy₁ Hy₂ Mh j M g η kind b e₁ e₂ P) :
    E.FinalArc (latHomOf hC) c ell H LL (KsW W) (DeltaT PD.p) ϖ (W.χΓ W.gam) j M g G₀ Sz η kind b :=
  ⟨{ r₁ := r₁
     r₂ := r₂
     S₁ := lvData Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η
     S₂ := lvData Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η
     m := levelMapOf hC Hy₁ Hy₂ Mh j M g η kind b e₁ e₂ P ms
     D₁ := Dc W T₁ c
     D₂ := Dc W T₂ c
     R₁ := lvModel Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η
     R₂ := lvModel Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η
     e₁ := e₁
     e₂ := e₂
     lam₁ := lam₁
     lam₂ := lam₂
     U₁ := UL lam₁ kind b η
     U₂ := UL lam₂ kind b η },
   { lev₁ := finalLevels_of Hy₁ ϖ j M g G₀ Sz η kind b e₁ ls₁
     lev₂ := finalLevels_of Hy₂ ϖ j M g G₀ Sz η kind b e₂ ls₂
     mapFl := ms.mapFl
     cMap := ms.cMap
     prLIs := ms.prLIs }⟩

end ThetaShiftProofs

end Formalism.MainNotions.N.Ln03
