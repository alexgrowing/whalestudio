import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMulPowEqIncl
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaLoc

theorem baseChange_loc {B A P P' Q Q' : Type} [CommRing B] [CommRing A] [CommRing P] [CommRing P'] [CommRing Q]
    [CommRing Q'] [Algebra B A] [Algebra B P] [Algebra B P'] [Algebra B Q] [Algebra B Q'] [Algebra A Q] [Algebra A Q']
    [IsScalarTower B A Q] [IsScalarTower B A Q']
    (i : P →+* P') (r : Q →+* Q') (t₁ : P →+* Q) (t : P' →+* Q') (c : P)
    (hi : ∀ b, i (algebraMap B P b) = algebraMap B P' b)
    (hr : ∀ a, r (algebraMap A Q a) = algebraMap A Q' a)
    (ht₁ : ∀ b, t₁ (algebraMap B P b) = algebraMap B Q b)
    (ht : ∀ b, t (algebraMap B P' b) = algebraMap B Q' b)
    (hcomm : ∀ x, t (i x) = r (t₁ x))
    (hP : letI := i.toAlgebra; IsLocalization.Away c P')
    (hQ : letI := r.toAlgebra; IsLocalization.Away (t₁ c) Q')
    (f₁ : P →ₗ[B] Q) (hf₁ : ∀ x, f₁ x = t₁ x) (f : P' →ₗ[B] Q') (hf : ∀ x, f x = t x)
    (h : IsBaseChange A f₁) : IsBaseChange A f := by
  letI a1 : Algebra P P' := i.toAlgebra
  letI a2 : Algebra Q Q' := r.toAlgebra
  letI a3 : Algebra P Q := t₁.toAlgebra
  letI a4 : Algebra P' Q' := t.toAlgebra
  letI a5 : Algebra P Q' := (t.comp i).toAlgebra
  haveI : IsScalarTower B P P' := .of_algebraMap_eq fun b => (hi b).symm
  haveI : IsScalarTower B P Q := .of_algebraMap_eq fun b => (ht₁ b).symm
  haveI : IsScalarTower B P' Q' := .of_algebraMap_eq fun b => (ht b).symm
  haveI : IsScalarTower B P Q' := .of_algebraMap_eq fun b => by
    change _ = t (i _)
    rw [hi, ht]
  haveI : IsScalarTower P P' Q' := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower P Q Q' := .of_algebraMap_eq fun x => hcomm x
  haveI : IsScalarTower A Q Q' := .of_algebraMap_eq fun a => (hr a).symm
  haveI : IsScalarTower B Q Q' := .of_algebraMap_eq fun b => by
    rw [IsScalarTower.algebraMap_apply B A Q, IsScalarTower.algebraMap_apply B A Q']
    exact (hr _).symm
  have e1 : f₁ = (IsScalarTower.toAlgHom B P Q).toLinearMap := LinearMap.ext hf₁
  have p1 : Algebra.IsPushout B A P Q := ⟨by rw [← e1]; exact h⟩
  haveI p2 : Algebra.IsPushout B P A Q := p1.symm
  haveI : IsLocalization.Away c P' := hP
  have hQ' : IsLocalization (Algebra.algebraMapSubmonoid Q (Submonoid.powers c)) Q' := by
    have e : Algebra.algebraMapSubmonoid Q (Submonoid.powers c) = Submonoid.powers (t₁ c) := by
      simp only [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
      rfl
    rw [e]
    exact hQ
  have p3 : Algebra.IsPushout P Q P' Q' := (Algebra.isLocalization_iff_isPushout (Submonoid.powers c) P').1 hQ'
  have p4 : Algebra.IsPushout P P' Q Q' := p3.symm
  have p5 : Algebra.IsPushout B P' A Q' := (Algebra.IsPushout.comp_iff B P A Q).2 p4
  have e2 : f = (IsScalarTower.toAlgHom B P' Q').toLinearMap := LinearMap.ext hf
  rw [e2]
  exact p5.symm.out

variable {K : Type} [Field K] {n d : ℕ}

theorem mon_congr {M : AddSubmonoid (Gam n d)} {g g' : Gam n d} (e : g = g') (hg : g ∈ M) (hg' : g' ∈ M) :
    mon K g hg = mon K g' hg' := by
  subst e
  rfl

theorem mon_sum {ι : Type} {M : AddSubmonoid (Gam n d)} (s : Finset ι) (g : ι → Gam n d) (hg : ∀ j, g j ∈ M) :
    mon K (∑ j ∈ s, g j) (sum_mem fun j _ => hg j) = ∏ j ∈ s, mon K (g j) (hg j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact mon_congr (K := K) Finset.sum_empty _ M.zero_mem
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ← ih, mon_mul]
    exact mon_congr (Finset.sum_insert ha) _ _

def cE (S : Finset (Fin d)) (k : Fin d) : Gam n d := ∑ j ∈ S, ratE k j

theorem cE_mem (S : Finset (Fin d)) (k : Fin d) : cE S k ∈ (cone {k} : AddSubmonoid (Gam n d)) :=
  sum_mem fun j _ => ratE_mem (Finset.mem_singleton_self k) j

theorem neg_cE_mem {S : Finset (Fin d)} (k : Fin d) : -cE S k ∈ (cone S : AddSubmonoid (Gam n d)) := by
  have e : -cE S k = ∑ j ∈ S, (ratE j k : Gam n d) := by
    simp [cE, ratE, ← Finset.sum_neg_distrib]
  rw [e]
  exact sum_mem fun j hj => ratE_mem hj k

theorem one_le_cE {S : Finset (Fin d)} {k j : Fin d} (hj : j ∈ S) (hne : j ≠ k) :
    1 ≤ (cE S k : Gam n d) (Sum.inr j) := by
  have : (cE S k : Gam n d) (Sum.inr j) = 1 := by
    simp [cE, ratE, oneE, Finset.sum_apply, Pi.single_apply, hj, hne]
  exact this.ge

theorem exists_add_nsmul_mem {S : Finset (Fin d)} (k : Fin d) (g : Gam n d) (hg : g ∈ (cone S : AddSubmonoid (Gam n d))) :
    ∃ N : ℕ, g + N • cE S k ∈ (cone {k} : AddSubmonoid (Gam n d)) := by
  have hc := cE_mem (n := n) S k
  have hN := (cone {k} : AddSubmonoid (Gam n d)).nsmul_mem hc
  refine ⟨∑ j, (g (Sum.inr j)).natAbs, fun l => ?_, fun j hj => ?_, ?_⟩
  · exact add_nonneg (hg.1 l) ((hN _).1 l)
  · have hne : j ≠ k := fun h => hj (h ▸ Finset.mem_singleton_self k)
    by_cases hjS : j ∈ S
    · have h1 := one_le_cE (n := n) hjS hne
      have h2 : (g (Sum.inr j)).natAbs ≤ ∑ j, (g (Sum.inr j)).natAbs :=
        Finset.single_le_sum (f := fun j => (g (Sum.inr j)).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      show 0 ≤ g (Sum.inr j) + (∑ j, (g (Sum.inr j)).natAbs) • (cE S k : Gam n d) (Sum.inr j)
      rw [nsmul_eq_mul]
      have h3 : -g (Sum.inr j) ≤ ((g (Sum.inr j)).natAbs : ℤ) := by
        rw [Int.natCast_natAbs]; exact neg_le_abs _
      have h4 : ((g (Sum.inr j)).natAbs : ℤ) ≤ ((∑ j, (g (Sum.inr j)).natAbs : ℕ) : ℤ) := by exact_mod_cast h2
      have h5 : (0 : ℤ) ≤ ((∑ j, (g (Sum.inr j)).natAbs : ℕ) : ℤ) := Int.natCast_nonneg _
      nlinarith
    · exact add_nonneg (hg.2.1 j hjS) ((hN _).2.1 j hj)
  · rw [tdeg_add]
    exact add_nonneg hg.2.2 (hN _).2.2

end GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaLoc

namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaLoc

theorem theta_loc : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) (S : Finset (Fin d)) (k : Fin d) (hk : k ∈ S) (θ₁ : R0 K n d {k} →ₐ[K] C.R {k}) (hθ₁ : ∀ b, θ₁ (poly n K {k} b) = toR C {k} (phi C b)), (∀ j, θ₁ (mon K (ratE k j) (ratE_mem (Finset.mem_singleton_self k) j)) = C.u {k} k (Finset.mem_singleton_self k) j) → IsBaseChange (Aa C) (thetaLin C θ₁ hθ₁) → ∃ (θ : R0 K n d S →ₐ[K] C.R S) (hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b)), IsBaseChange (Aa C) (thetaLin C θ hθ) := by
  intro K _ n d A _ _ C S k hk θ₁ hθ₁ hu hbc
  have hsk : ({k} : Finset (Fin d)) ⊆ S := Finset.singleton_subset_iff.2 hk
  have hle : (cone {k} : AddSubmonoid (Gam n d)) ≤ cone S := cone_mono hsk
  have hc := cE_mem (n := n) S k
  have hP := Away.isLocalization_away (K := K) hle (cE S k) hc (neg_cE_mem k)
    (fun g hg => exists_add_nsmul_mem k g hg)
  have hθc : θ₁ (mon K (cE S k) hc) = ∏ j ∈ S, C.u {k} k (Finset.mem_singleton_self k) j := by
    have e : mon K (cE S k) hc = ∏ j ∈ S, mon K (ratE k j) (ratE_mem (Finset.mem_singleton_self k) j) :=
      mon_sum S _ _
    rw [e, map_prod]
    exact Finset.prod_congr rfl fun j _ => hu j
  letI aP : Algebra (R0 K n d {k}) (R0 K n d S) := (incl (K := K) hle).toRingHom.toAlgebra
  letI aQ : Algebra (C.R {k}) (C.R S) := (C.res hsk).toRingHom.toAlgebra
  haveI hP' : IsLocalization.Away (mon K (cE S k) hc) (R0 K n d S) := hP
  have hQ : IsLocalization.Away (θ₁ (mon K (cE S k) hc)) (C.R S) := by
    rw [hθc]
    exact C.loc S k hk
  have hunit : IsUnit (((C.res hsk).toRingHom.comp θ₁.toRingHom) (mon K (cE S k) hc)) :=
    IsLocalization.Away.algebraMap_isUnit (S := C.R S) (θ₁ (mon K (cE S k) hc))
  let T : R0 K n d S →+* C.R S := IsLocalization.Away.lift (mon K (cE S k) hc) hunit
  have hT : ∀ x, T (incl hle x) = C.res hsk (θ₁ x) := fun x =>
    IsLocalization.Away.lift_eq (mon K (cE S k) hc) hunit x
  let θ : R0 K n d S →ₐ[K] C.R S :=
    { T with
      commutes' := fun r => by
        have e : algebraMap K (R0 K n d S) r = incl hle (algebraMap K (R0 K n d {k}) r) :=
          ((incl (K := K) hle).commutes r).symm
        change T _ = _
        rw [e, hT, θ₁.commutes, (C.res hsk).commutes] }
  have hθT : ∀ x, θ x = T x := fun _ => rfl
  have hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b) := fun b => by
    rw [hθT, ← incl_poly hsk, hT, hθ₁, res_toR]
  refine ⟨θ, hθ, ?_⟩
  exact baseChange_loc (A := Aa C) (Q := Rb C {k}) (Q' := Rb C S)
    (incl (K := K) hle).toRingHom (C.res hsk).toRingHom θ₁.toRingHom T (mon K (cE S k) hc)
    (fun b => incl_poly hsk b) (fun a => res_toR C hsk a) hθ₁ hθ hT hP hQ
    (thetaLin C θ₁ hθ₁) (fun _ => rfl) (thetaLin C θ hθ) (fun _ => rfl) hbc

end GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaLoc
