import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtSide
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isProper_str (R : Type) [CommRing R] (N : ℕ) : IsProper (PSpace.str R N) := by
  have hb : Function.Bijective (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)) := by
    constructor
    · intro a b h
      exact MvPolynomial.C_injective (Fin (N + 1)) R (congrArg Subtype.val h)
    · rintro ⟨x, hx⟩
      exact ⟨MvPolynomial.coeff 0 x, Subtype.ext
        (MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 ((MvPolynomial.totalDegree_zero_iff_isHomogeneous _).2 hx)).symm⟩
  have : IsIso (spMap (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0))) := by
    have : IsIso (CommRingCat.ofHom (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0))) :=
      (ConcreteCategory.isIso_iff_bijective _).2 hb
    infer_instance
  have : IsScalarTower R ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) (MvPolynomial (Fin (N + 1)) R) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) (MvPolynomial (Fin (N + 1)) R) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R _ _
  unfold PSpace.str
  infer_instance

theorem isProper_of_proj {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) : IsProper f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_str R N
  infer_instance

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem sm_proper {M : Model l K} (h : M.Sm) : IsProper M.p := isProper_of_proj h.1.1

theorem sm_proper_q {M : Model l K} (h : M.Sm) : IsProper M.q :=
  have := sm_proper h
  inferInstance

theorem sm_smooth_q {M : Model l K} (h : M.Sm) : Smooth M.q :=
  have := h.2
  inferInstance

def cupR (M : Model l K) (i j : ℕ) : HdR M.q i →ₗ[K] HdR M.q j →ₗ[K] HdR M.q (i + j) := (k_cup M.q i j).1.choose

theorem cupR_eq (M : Model l K) (i j : ℕ) (x : HdR M.q i) (y : HdR M.q j) : cupR M i j x y = cupK M.q rfl x y :=
  (k_cup M.q i j).1.choose_spec x y

theorem cupR_fil (M : Model l K) (i j r s : ℕ) : ∀ x ∈ FilR M.q i r, ∀ y ∈ FilR M.q j s, cupR M i j x y ∈ FilR M.q (i + j) (r + s) :=
  fun x hx y hy => cupR_eq M i j x y ▸ (k_cup M.q i j).2 r s x hx y hy

theorem m_fin (M : Model l K) (h : M.Sm) (j : ℕ) : FiniteDimensional K (HdR M.q j) ∧ ∀ x ∈ FilR M.q j (j + 1), x = 0 :=
  have := sm_proper_q h
  have := sm_smooth_q h
  k_fin M.q j

theorem m_top (M : Model l K) (h : M.Sm) (d : ℕ) (hd : M.Conn d) (j : ℕ) : ∀ x ∈ FilR M.q j (d + 1), x = 0 :=
  have := sm_proper_q h
  have := hd.2
  k_top M.q d j

end CrystallineSemistableComparison.Pb
