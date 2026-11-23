import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ZMemPerp

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def UnimodOneGenus : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K),
    Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm → h.Nondegenerate →
    ∀ L M : Submodule (𝓞 K) V, Submodule.IsLattice K L → Submodule.IsLattice K M →
      Formalism.HermitianLatticesTheory.IsUnimodular h L → Formalism.HermitianLatticesTheory.IsUnimodular h M → Formalism.HermitianLatticesTheory.SameGenus h L M

section Constr

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

def aaI (a : Fin D.R.rS) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ)))

def PartnerOK (f : Fin D.R.rS → (VS D).V) : Prop :=
  (∀ a b, (VS D).hT (F0.e a) (f b) = if a = b then 1 else 0) ∧ (∀ a b, (VS D).hT (f a) (f b) = 0) ∧
    ∀ a, (VS D).hT (f a) F0.z = 0

def vPr (f : Fin D.R.rS → (VS D).V) (v : (VS D).V) : (VS D).V :=
  v - ∑ a, (VS D).hT (F0.e a) v • f a

theorem vPr_add (f : Fin D.R.rS → (VS D).V) (v w : (VS D).V) :
    vPr D F0 f (v + w) = vPr D F0 f v + vPr D F0 f w := by
  simp only [vPr, map_add, add_smul, Finset.sum_add_distrib]
  abel

theorem vPr_smul (f : Fin D.R.rS → (VS D).V) (c : D.host.E) (v : (VS D).V) :
    vPr D F0 f (c • v) = c • vPr D F0 f v := by
  simp only [vPr, map_smul, smul_eq_mul, mul_smul, smul_sub, Finset.smul_sum]

theorem vPr_zero (f : Fin D.R.rS → (VS D).V) : vPr D F0 f 0 = 0 := by
  simp [vPr]

theorem fi_add {I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E} {x y : D.host.E}
    (hx : x ∈ I) (hy : y ∈ I) : x + y ∈ I := by
  have h := Submodule.add_mem (I : Submodule (𝓞 D.host.E) D.host.E)
    (FractionalIdeal.mem_coe.mpr hx) (FractionalIdeal.mem_coe.mpr hy)
  exact FractionalIdeal.mem_coe.mp h

theorem fi_zero (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : (0 : D.host.E) ∈ I := by
  exact FractionalIdeal.mem_coe.mp (Submodule.zero_mem (I : Submodule (𝓞 D.host.E) D.host.E))

theorem fi_mul {I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E} (o : 𝓞 D.host.E) {x : D.host.E}
    (hx : x ∈ I) : (o : D.host.E) * x ∈ I := by
  have h := Submodule.smul_mem (I : Submodule (𝓞 D.host.E) D.host.E) o (FractionalIdeal.mem_coe.mpr hx)
  rw [Algebra.smul_def] at h
  exact FractionalIdeal.mem_coe.mp h

theorem star_int (o : 𝓞 D.host.E) : ∃ o' : 𝓞 D.host.E, (o' : D.host.E) = star (o : D.host.E) := by
  exact ⟨NumberField.RingOfIntegers.mapRingHom (starRingEnd D.host.E) o, rfl⟩

def lamC (f : Fin D.R.rS → (VS D).V) (M : Submodule (𝓞 D.host.E) (WbQ D F0)) :
    Submodule (𝓞 D.host.E) (VS D).V where
  carrier := {v | (∀ a, star ((VS D).hT (F0.e a) v) ∈ (aaI D a)⁻¹) ∧
    (∃ w : perpS (VS D) F0.X, (w : (VS D).V) = vPr D F0 f v ∧ (Submodule.Quotient.mk w : WbQ D F0) ∈ M) ∧
    ∀ a, (VS D).hT (f a) (vPr D F0 f v) ∈ aaI D a}
  add_mem' := by
    rintro v v' ⟨h1, ⟨w, hw, hwM⟩, h3⟩ ⟨h1', ⟨w', hw', hwM'⟩, h3'⟩
    refine ⟨fun a => ?_, ⟨w + w', ?_, ?_⟩, fun a => ?_⟩
    · rw [map_add, star_add]; exact fi_add D (h1 a) (h1' a)
    · rw [Submodule.coe_add, hw, hw', vPr_add]
    · rw [Submodule.Quotient.mk_add]; exact M.add_mem hwM hwM'
    · rw [vPr_add, map_add]; exact fi_add D (h3 a) (h3' a)
  zero_mem' := by
    refine ⟨fun a => ?_, ⟨0, ?_, ?_⟩, fun a => ?_⟩
    · simp only [map_zero, star_zero]; exact fi_zero D _
    · simp [vPr_zero]
    · simp
    · simp only [vPr_zero, map_zero]; exact fi_zero D _
  smul_mem' := by
    rintro o v ⟨h1, ⟨w, hw, hwM⟩, h3⟩
    have hs : o • v = (o : D.host.E) • v := (algebraMap_smul D.host.E o v).symm
    refine ⟨fun a => ?_, ⟨o • w, ?_, ?_⟩, fun a => ?_⟩
    · obtain ⟨o', ho'⟩ := star_int D o
      rw [hs, map_smul, smul_eq_mul, star_mul, ← ho', mul_comm]
      exact fi_mul D o' (h1 a)
    · rw [hs, vPr_smul, ← hw]
      show o • (w : (VS D).V) = _
      exact (algebraMap_smul D.host.E o (w : (VS D).V)).symm
    · rw [Submodule.Quotient.mk_smul]; exact M.smul_mem o hwM
    · rw [hs, vPr_smul, map_smul, smul_eq_mul]; exact fi_mul D o (h3 a)

end Constr

def PartnerEx : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)), ∃ f, PartnerOK D F0 f

def LamLattice : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (f : Fin D.R.rS → (VS D).V)
    (M : Submodule (𝓞 D.host.E) (WbQ D F0)), PartnerOK D F0 f → IsGlueLat (hWb D F0) (zbar D F0) M →
      Submodule.IsLattice D.host.E (lamC D F0 f M)

def LamUnimod : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (f : Fin D.R.rS → (VS D).V)
    (M : Submodule (𝓞 D.host.E) (WbQ D F0)), PartnerOK D F0 f → IsGlueLat (hWb D F0) (zbar D F0) M →
      Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (lamC D F0 f M)

def LamFlag : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (f : Fin D.R.rS → (VS D).V)
    (M : Submodule (𝓞 D.host.E) (WbQ D F0)), PartnerOK D F0 f → IsGlueLat (hWb D F0) (zbar D F0) M →
      F0.z ∈ lamC D F0 f M ∧ XLam (lamC D F0 f M) (lf D F0) = XS D F0 ∧
      (∀ c : D.host.E, c • F0.z ∈ Lsub (lamC D F0 f M) (lf D F0) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) ∧
      Mof D F0 (lamC D F0 f M) = M

def LocGenXS : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)), ∃ c : Fin D.R.rS → D.host.E, (∀ a, c a ≠ 0) ∧
      (((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∀ a, c a = 1) ∧
      (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XS D F0) =
        Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range fun a => c a • F0.e a)))

theorem rowSurj_of (hJ : UnimodOneGenus) (hP : PartnerEx) (hL : LamLattice) (hU : LamUnimod)
    (hF : LamFlag) (hG : LocGenXS) : RowSurj := by
  intro D u F0 M hM
  obtain ⟨f, hf⟩ := hP D u F0
  obtain ⟨hz, hX, hprim, hMof⟩ := hF D u F0 f M hf hM
  have hLat := hL D u F0 f M hf hM
  have hUn := hU D u F0 f M hf hM
  refine ⟨lamC D F0 f M, ?_, hMof⟩
  refine ⟨?_, ⟨hLat, hUn, ⟨hz, rfl⟩, ?_, hprim⟩, hX⟩
  ·
    exact ⟨hLat, hJ D.host.E (VS D).V (VS D).hT D.sp.cm.cmUnram (VS D).herm (VS D).nondeg
      (VS D).L0 (lamC D F0 f M) (VS D).standardTuple_isLattice hLat (VS D).baseLattice_isUnimodular hUn⟩
  · intro P
    rw [hX]
    exact hG D u F0 P

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
