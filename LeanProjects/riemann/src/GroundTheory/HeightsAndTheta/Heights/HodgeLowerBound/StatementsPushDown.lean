import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlag
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFStep
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFHoriz
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def PushDown.Statement : Prop :=
  ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
    (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D) (H : HodgeData D) (B : AdaptedBasis H),
    (∀ (G : GenFibre Pl.xV (Pl.flagPrime B))
        (J : IFamily G.Φ (fibreIdx Pl.ιY (Sum.inl : K → K ⊕ (Ψ × Fin (D.N - 1)))))
        (L : Fin (D.n + 1) → HermLine ι) (L' : Fin (D.n + 1) → HermLine Pl.ιY)
        (N : Fin D.flagDim0 → HermLine Pl.ιY),
        IsFieldIntersection J → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm Sum.inl Pl.xV (L j) (L' j)) →
        (∀ j, IsSmoothHerm (N j)) →
        II _ Pl.ιY (Pl.flagPrime B) (D.n + 1 + D.flagDim0) (Fin.append L' N) =
          (J (fibreIdeal Sum.inl G) D.flagDim0 (fun j => fibreDeg Sum.inl (N j).a) : ℝ) *
            II K ι (mCoordIdeal D.y) (D.n + 1) L) ∧
    (∀ (d r : ℕ) (L : Fin d → HermLine ι) (L' : Fin d → HermLine Pl.ιY) (N : Fin r → HermLine Pl.ιY),
        d + r = D.n + 1 + D.flagDim0 → D.n + 1 < d → (∀ j, IsSmoothHerm (L j)) →
        (∀ j, IsPullHerm Sum.inl Pl.xV (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) →
        II _ Pl.ιY (Pl.flagPrime B) (d + r) (Fin.append L' N) = 0)

section Bot

variable {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}

abbrev botAlgBase (v : (Σ k, ι k) → (Σ k', ι' k')) : Algebra (MRing ι) (FractionRing (MRing ι')) :=
  ((algebraMap (MRing ι') (FractionRing (MRing ι'))).comp (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom).toAlgebra

theorem botAlgBase_injective {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : Function.Injective v) :
    Function.Injective (@algebraMap (MRing ι) (FractionRing (MRing ι')) _ _ (botAlgBase v)) :=
  (IsFractionRing.injective (MRing ι') (FractionRing (MRing ι'))).comp (rename_injective _ hv)

abbrev botAlg (v : (Σ k, ι k) → (Σ k', ι' k')) (hv : Function.Injective v) :
    Algebra (FractionRing (MRing ι)) (FractionRing (MRing ι')) :=
  letI := botAlgBase v
  haveI : FaithfulSMul (MRing ι) (FractionRing (MRing ι')) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (botAlgBase_injective hv)
  FractionRing.liftAlgebra _ _

theorem botAlg_algebraMap {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : Function.Injective v) (f : MRing ι) :
    @algebraMap _ _ _ _ (botAlg v hv) (algebraMap (MRing ι) (FractionRing (MRing ι)) f) =
      algebraMap (MRing ι') (FractionRing (MRing ι')) (rename v f) := by
  let := botAlgBase v
  have : FaithfulSMul (MRing ι) (FractionRing (MRing ι')) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (botAlgBase_injective hv)
  exact IsFractionRing.lift_algebraMap (botAlgBase_injective hv) f

def genFibreBot (v : (Σ k, ι k) → (Σ k', ι' k')) (hv : Function.Injective v) :
    GenFibre v (⊥ : Ideal (MRing ι')) where
  Φ := FractionRing (MRing ι)
  Φ' := FractionRing (MRing ι')
  alg := botAlg v hv
  x p := algebraMap (MRing ι) (FractionRing (MRing ι)) (X p)
  x' q := algebraMap (MRing ι') (FractionRing (MRing ι')) (X q)
  ker_x := by
    rw [show imageZ v (⊥ : Ideal (MRing ι')) = ⊥ from Ideal.comap_bot_of_injective _ (rename_injective _ hv)]
    ext f
    rw [RingHom.mem_ker, Ideal.mem_bot]
    convert map_eq_zero_iff (algebraMap (MRing ι) (FractionRing (MRing ι)))
      (IsFractionRing.injective _ _) using 2
    exact Inter.aeval_algebraMap_X_eq f
  gen c := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι) c
    refine ⟨a, b, ?_, ?_⟩
    · convert IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (K := FractionRing (MRing ι)) hb using 2
      exact Inter.aeval_algebraMap_X_eq b
    · exact (congrArg₂ (· / ·) (Inter.aeval_algebraMap_X_eq a) (Inter.aeval_algebraMap_X_eq b)).symm
  genericFibre_ker_target := by
    ext f
    rw [RingHom.mem_ker, Ideal.mem_bot]
    convert map_eq_zero_iff (algebraMap (MRing ι') (FractionRing (MRing ι')))
      (IsFractionRing.injective _ _) using 2
    exact Inter.aeval_algebraMap_X_eq f
  compat p := by
    rw [botAlg_algebraMap, rename_X]

end Bot

def Line.projLineFlagGenericFibre :
    GenFibre (Line.linePl Line.zeroSystem fun _ _ => le_rfl).xV
      ((Line.linePl Line.zeroSystem fun _ _ => le_rfl).flagPrime (Line.lineAdapted Line.zeroSystem fun _ _ => le_rfl)) :=
  Inter.PFHoriz.genFibreOf
    (genFibreBot (Line.linePl Line.zeroSystem fun _ _ => le_rfl).xV
      (Line.linePl Line.zeroSystem fun _ _ => le_rfl).isBlockMap_xV.2.1) _
    (by
      have h1 := (Line.linePl Line.zeroSystem fun _ _ => le_rfl).imageZ_xV_PY
      have h2 : (Line.linePl Line.zeroSystem fun _ _ => le_rfl).PY = ⊥ := Line.PY_line _ _
      rw [h2] at h1
      rw [PlueckerData.imageZ_forget_flagPrime, h1])

end GroundTheory.Heights₂.Heights.LowerBoundFree
