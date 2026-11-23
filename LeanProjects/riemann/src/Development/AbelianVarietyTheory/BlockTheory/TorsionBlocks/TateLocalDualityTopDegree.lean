import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.WeaklyAdmissibleFiltrations.StatementTor
import Formalism.GaloisCohomology.LocalTateDualityK

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TateLocalDualityDegreeTwo

open Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {l : ℕ} [Fact l.Prime]

def intSub (LL : FinExt l) : Submodule ↥(OL LL) ↥LL.1 :=
  LinearMap.range (Algebra.linearMap ↥(OL LL) ↥LL.1)

def FracModInt (LL : FinExt l) : Type := ↥LL.1 ⧸ intSub LL

instance (LL : FinExt l) : AddCommGroup (FracModInt LL) :=
  inferInstanceAs (AddCommGroup (↥LL.1 ⧸ intSub LL))
instance (LL : FinExt l) : Module ↥(OL LL) (FracModInt LL) :=
  Submodule.Quotient.module (intSub LL)
instance (LL : FinExt l) : TopologicalSpace (FracModInt LL) := ⊥
instance (LL : FinExt l) : DiscreteTopology (FracModInt LL) := ⟨rfl⟩
instance (LL : FinExt l) : IsTopologicalAddGroup (FracModInt LL) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology
instance (LL : FinExt l) : ContinuousConstSMul ↥(OL LL) (FracModInt LL) where
  continuous_const_smul _ := continuous_of_discreteTopology

def FracModInt.mk (LL : FinExt l) : ↥LL.1 →ₗ[↥(OL LL)] FracModInt LL := (intSub LL).mkQ

theorem norm_chi_le_one (P : LocPrime l) (K : FinExt l) (g : ↥(GK K)) :
    ‖(((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
  obtain ⟨a, ha, -⟩ := P.χQ_cyc (g : GQ l) 0 1 (by simp)
  rw [P.PD_χ]
  have h1 : ‖((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])‖ ≤ 1 := by simpa using ha
  have h2 : ‖(a : ℚ_[l])‖ ≤ 1 := by simpa using Padic.norm_int_le_one (p := l) (a : ℤ)
  have h3 := IsUltrametricDist.norm_add_le_max
    (((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])) (a : ℚ_[l])
  rw [sub_add_cancel] at h3
  exact h3.trans (max_le h1 h2)

def chiInt (P : LocPrime l) (K : FinExt l) : ↥(GK K) →* ℤ_[l] where
  toFun g := ⟨(((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]), norm_chi_le_one P K g⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by
    change (((P.PD K).χ (g * h) : ℚ_[l]ˣ) : ℚ_[l]) =
      (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) * (((P.PD K).χ h : ℚ_[l]ˣ) : ℚ_[l])
    rw [map_mul, Units.val_mul])

def chiO (P : LocPrime l) (K LL : FinExt l) : ↥(GK K) →* (↥(OL LL))ˣ :=
  ((algebraMap ℤ_[l] ↥(OL LL)).toMonoidHom.comp (chiInt P K)).toHomUnits

def fracModIntTwist (P : LocPrime l) (K LL : FinExt l) :
    Representation ↥(OL LL) ↥(GK K) (FracModInt LL) :=
  Formalism.GaloisCohomology.scalRep (FracModInt LL) (chiO P K LL)

theorem fracModIntTwist_mk (P : LocPrime l) (K LL : FinExt l) (g : ↥(GK K)) (x : ↥LL.1) :
    fracModIntTwist P K LL g (FracModInt.mk LL x) =
      FracModInt.mk LL (algebraMap ℚ_[l] ↥LL.1 (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) * x) := by
  rw [fracModIntTwist, Formalism.GaloisCohomology.scalRep_apply, ← map_smul]
  congr 1

def H2IsoCoefficients {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    (rho : Representation R G M) : Prop :=
  Nonempty (ReciprocityTheory.Gal.H2 rho ≃ₗ[R] M)

def TateLocalDualityDegreeTwoAt (P : LocPrime l) (K LL : FinExt l) : Prop :=
  H2IsoCoefficients (fracModIntTwist P K LL)

def TateLocalDualityDegreeTwoAll (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), TateLocalDualityDegreeTwoAt (D.loc l) K LL

def TateLocalDualityDegreeTwoGood (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL →
    TateLocalDualityDegreeTwoAt (D.loc l) K LL

theorem TateLocalDualityDegreeTwoAll.tateDualityTop_of_all {D : D7} (h : TateLocalDualityDegreeTwoAll D) : TateLocalDualityDegreeTwoGood D :=
  fun l _ K _ LL _ => h l K LL

end GlobalTheory.IndefiniteRowSideFullHecke.TateLocalDualityDegreeTwo
