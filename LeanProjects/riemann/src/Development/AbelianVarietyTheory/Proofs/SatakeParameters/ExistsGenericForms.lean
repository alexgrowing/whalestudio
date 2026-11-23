import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RingKrullDimLeOfQuasiFinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCotangentBasis
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraMapBasicOpen
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioLinear

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD

set_option autoImplicit false

noncomputable section

open TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj.Generic

variable {N : ℕ}

def lin (c : Fin (N + 1) → ℂ) : MvPolynomial (Fin (N + 1)) ℂ := ∑ l, c l • MvPolynomial.X l

theorem lin_mem (c : Fin (N + 1) → ℂ) : lin c ∈ ProjSpace.grading ℂ N 1 := by
  unfold lin
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (ProjSpace.X_mem ℂ N l)

def linMap : (Fin (N + 1) → ℂ) →ₗ[ℂ] MvPolynomial (Fin (N + 1)) ℂ where
  toFun := lin
  map_add' a b := by simp [lin, add_smul, Finset.sum_add_distrib]
  map_smul' a b := by simp [lin, smul_smul, Finset.smul_sum]

theorem exists_X_notMem (z : PSpace ℂ N) :
    ∃ l, (MvPolynomial.X l : MvPolynomial (Fin (N + 1)) ℂ) ∉ z.asHomogeneousIdeal.toIdeal := by
  by_contra h
  push_neg at h
  have hle : Ideal.span (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) ℂ)) ≤
      z.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    exact h l
  apply ProjectiveSpectrum.not_irrelevant_le z
  intro x hx
  exact hle (ProjSpace.irrelevant_le_span_X ℂ N hx)

def van (z : PSpace ℂ N) : Submodule ℂ (Fin (N + 1) → ℂ) :=
  (z.asHomogeneousIdeal.toIdeal.restrictScalars ℂ).comap linMap

theorem exists_finite_gen {Y : Scheme.{0}} [NoetherianSpace Y] (Z : Set Y) (hZ : IsClosed Z) :
    ∃ T : Set Y, T.Finite ∧ T ⊆ Z ∧ ∀ x ∈ Z, ∃ t ∈ T, t ⤳ x := by
  obtain ⟨S, hSf, hSc, hSi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  haveI : Finite S := hSf.to_subtype
  refine ⟨Set.range fun s : S => (hSi s.1 s.2).genericPoint, Set.finite_range _, ?_, ?_⟩
  · rintro _ ⟨⟨s, hs⟩, rfl⟩
    exact Set.mem_sUnion_of_mem ((hSi s hs).isGenericPoint_genericPoint (hSc s hs)).mem hs
  · rintro x ⟨s, hs, hx⟩
    exact ⟨_, ⟨⟨s, hs⟩, rfl⟩, ((hSi s hs).isGenericPoint_genericPoint (hSc s hs)).specializes hx⟩

theorem coheight_step {Y : Scheme.{0}} {t x : Y} (h : t ⤳ x) (W : Set Y) (hW : IsOpen W) (ht : t ∈ W)
    (hx : x ∉ W) : Order.coheight t + 1 ≤ Order.coheight x := by
  apply Order.coheight_add_one_le
  exact lt_iff_le_not_ge.2 ⟨h, fun h' => hx (Specializes.mem_open h' hW ht)⟩

section Cot

variable {X : Scheme.{0}} {p : X ⟶ Sp ℂ} (ι : X ⟶ PSpace ℂ N) (g₀ : MvPolynomial (Fin (N + 1)) ℂ)
  (hg₀ : g₀ ∈ ProjSpace.grading ℂ N 1) {y : CxPts p (RingHom.id ℂ)}
  (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι g₀))

def ev₀ : Sec p (fOpen ι g₀) →+* ℂ := CxPts.evHom hy

def sqQ : Submodule ℂ (Sec p (fOpen ι g₀)) := ((RingHom.ker (ev₀ ι g₀ hy)) ^ 2).restrictScalars ℂ

def rr (l : Fin (N + 1)) : Sec p (fOpen ι g₀) := fRatio ι (MvPolynomial.X l) g₀ (ProjSpace.X_mem ℂ N l) hg₀

def fr (c : Fin (N + 1) → ℂ) : Sec p (fOpen ι g₀) := fRatio ι (lin c) g₀ (lin_mem c) hg₀

def vv (l : Fin (N + 1)) : Sec p (fOpen ι g₀) :=
  rr ι g₀ hg₀ l - algebraMap ℂ (Sec p (fOpen ι g₀)) (ev₀ ι g₀ hy (rr ι g₀ hg₀ l))

def Lm : (Fin (N + 1) → ℂ) →ₗ[ℂ] Sec p (fOpen ι g₀) ⧸ sqQ ι g₀ hy :=
  (sqQ ι g₀ hy).mkQ ∘ₗ Fintype.linearCombination ℂ (vv ι g₀ hg₀ hy)

theorem ev₀_algebraMap (z : ℂ) : ev₀ ι g₀ hy (algebraMap ℂ (Sec p (fOpen ι g₀)) z) = z := by
  first
  | exact (CxPts.ev_eq hy _).symm.trans (CxPts.ev_algX hy z)
  | exact CxPts.ev_algX hy z

theorem ev₀_smul (z : ℂ) (a : Sec p (fOpen ι g₀)) : ev₀ ι g₀ hy (z • a) = z * ev₀ ι g₀ hy a := by
  rw [Algebra.smul_def, map_mul, ev₀_algebraMap]

theorem ev₀_vv (l : Fin (N + 1)) : ev₀ ι g₀ hy (vv ι g₀ hg₀ hy l) = 0 := by
  unfold vv
  rw [map_sub, ev₀_algebraMap, sub_self]

theorem ev₀_sum (c : Fin (N + 1) → ℂ) : ev₀ ι g₀ hy (∑ l, c l • vv ι g₀ hg₀ hy l) = 0 := by
  rw [map_sum]
  exact Finset.sum_eq_zero fun l _ => by rw [ev₀_smul, ev₀_vv, mul_zero]

theorem mkQ_eq_mkQ (a b : Sec p (fOpen ι g₀)) :
    (sqQ ι g₀ hy).mkQ a = (sqQ ι g₀ hy).mkQ b ↔ a - b ∈ RingHom.ker (ev₀ ι g₀ hy) ^ 2 := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact Iff.rfl

theorem Lm_apply' (c : Fin (N + 1) → ℂ) :
    Lm ι g₀ hg₀ hy c = (sqQ ι g₀ hy).mkQ (∑ l, c l • vv ι g₀ hg₀ hy l) := by
  simp only [Lm, LinearMap.coe_comp, Function.comp_apply, Fintype.linearCombination_apply]

theorem Lm_apply (hp : ι ≫ PSpace.str ℂ N = p) (c : Fin (N + 1) → ℂ) :
    Lm ι g₀ hg₀ hy c = (sqQ ι g₀ hy).mkQ
      (fr ι g₀ hg₀ c - algebraMap ℂ (Sec p (fOpen ι g₀)) (ev₀ ι g₀ hy (fr ι g₀ hg₀ c))) := by
  rw [Lm_apply']
  have hfr : fr ι g₀ hg₀ c = ∑ l, c l • rr ι g₀ hg₀ l :=
    fRatio_linear X p N ι hp g₀ hg₀ c (lin_mem c)
  rw [hfr]
  congr 1
  simp only [vv, smul_sub, Finset.sum_sub_distrib, map_sum, ev₀_smul, map_mul, Algebra.smul_def,
    ev₀_algebraMap, mul_sub]

end Cot

section Range

variable {X : Scheme.{0}} {p : X ⟶ Sp ℂ} (ι : X ⟶ PSpace ℂ N) (g₀ : MvPolynomial (Fin (N + 1)) ℂ)
  (hg₀ : g₀ ∈ ProjSpace.grading ℂ N 1) {y : CxPts p (RingHom.id ℂ)}
  (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι g₀))

end Range

end GlobalTheory.EtProj.Generic
