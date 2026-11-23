import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup

noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.Strict

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.TruncatedSeriesCountingBounds

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

section Funct

variable {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'} (f : V →ₗ[LL] V')

theorem ιV_crisMap (z : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V') (crisMap B f z) = crisMap BdR f (ιV PD (LL := LL) (V := V) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [crisMap, ιV]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem crisMap_mulVB (c : K₀) (z : V ⊗[Qp] B) :
    crisMap B f (mulVB (LL := LL) (V := V) (B := B) c z) = mulVB (LL := LL) (V := V') (B := B) c (crisMap B f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [crisMap, mulVB]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mem_DcrisL_iff (τ₀ : K₀ →ₐ[Qp] LL) (z : V ⊗[Qp] B) :
    z ∈ DcrisL PD ρ τ₀ ↔ z ∈ Dcris PD ρ ∧ ∀ c : K₀, mulVB (LL := LL) (V := V) (B := B) c z = τ₀ c • z := by
  simp [DcrisL, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

end Funct

section SES

variable {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def StrictOne (W : LocWach PD LL O v n) : Prop :=
  ∀ (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L), IsSESLat (Qp := Qp) ι π →
    IsCrys PD T₂.ρ → IsCrys PD Y.ρ → ∀ u : ℤ,
      (FilCris PD Y.ρ u).comap (crisMap B ι.f) ⊓ Dcris PD T₂.ρ = FilCris PD T₂.ρ u

end SES

section P4Y

variable {PD} {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

end P4Y

section Rec

theorem p4YL (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (hL : Formalism.MainNotions.UnusedSlot80.LevCoeff D HW F) :
    Formalism.MainNotions.ArcLiftingSetup.AtCaseA fun l _ K LL hG => Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration ((HW l).W K 1 LL hG) := by
  intro l _ K LL hG hCA h5
  exact hL l K LL hCA h5

end Rec

end Formalism.MainNotions.UnusedSlot80.Strict

end
