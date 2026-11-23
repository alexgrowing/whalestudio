import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraEtaleOfSeparableCharpolyMulLeft
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralClosureFgFiniteEtaleDvr

noncomputable section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial

namespace GlobalTheory.UnitLemma.Desc.PosCount

section Idem

variable {ι : Type} [Fintype ι] {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

theorem sum_smul_mul_idem {e : ι → A} (he : CompleteOrthogonalIdempotents e) (c : ι → R) (i : ι) (x : A) :
    (∑ j, c j • e j) * (e i * x) = c i • (e i * x) := by
  classical
  rw [Finset.sum_mul, Finset.sum_eq_single i]
  · rw [smul_mul_assoc, ← mul_assoc, (he.idem i).eq]
  · intro j _ hj
    rw [smul_mul_assoc, ← mul_assoc, he.ortho hj, zero_mul, smul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem sum_smul_mul {e : ι → A} (he : CompleteOrthogonalIdempotents e) (c : ι → R) (x : A) :
    (∑ j, c j • e j) * x = ∑ i, c i • (e i * x) := by
  calc (∑ j, c j • e j) * x = (∑ j, c j • e j) * (∑ i, e i * x) := by
        rw [← Finset.sum_mul, he.complete, one_mul]
    _ = ∑ i, (∑ j, c j • e j) * (e i * x) := Finset.mul_sum _ _ _
    _ = _ := Finset.sum_congr rfl fun i _ => sum_smul_mul_idem he c i x

theorem sum_smul_mul_cancel {e : ι → A} (he : CompleteOrthogonalIdempotents e) (c c' : ι → R)
    (h : ∀ i, c' i * c i = 1) (x : A) : (∑ j, c' j • e j) * ((∑ j, c j • e j) * x) = x := by
  rw [sum_smul_mul he c x, Finset.mul_sum]
  calc ∑ i, (∑ j, c' j • e j) * (c i • (e i * x)) = ∑ i, e i * x :=
        Finset.sum_congr rfl fun i _ => by
          rw [mul_smul_comm, sum_smul_mul_idem he, smul_smul, mul_comm, h, one_smul]
    _ = x := by rw [← Finset.sum_mul, he.complete, one_mul]

end Idem

variable (K : UQ) (B : InvAlg K)

def Sandwich (a : K.O) (N : ℕ) : Set (Submodule K.O B.A) :=
  {M | (∀ r : B.A, IsIntegral K.O r → a ^ N • r ∈ M) ∧ ∀ m ∈ M, IsIntegral K.O m}

theorem finite_quotient_span_pow {a : K.O} (ha : a ≠ 0) (N : ℕ) :
    Finite (K.O ⧸ Ideal.span {a ^ N}) := by
  rw [IsLocalRing.finite_quotient_iff]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  refine ⟨k * N, ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton, mul_pow,
    ← Units.val_pow_eq_pow_val, Units.mul_left_dvd, ← pow_mul]

theorem sandwich_finite (hR : (Subalgebra.toSubmodule (integralClosure K.O B.A)).FG) {a : K.O} (ha : a ≠ 0)
    (N : ℕ) : (Sandwich K B a N).Finite := by
  set R := Subalgebra.toSubmodule (integralClosure K.O B.A) with hRdef
  haveI : Module.Finite K.O R := Module.Finite.iff_fg.mpr hR
  set I : Ideal K.O := Ideal.span {a ^ N}
  haveI := finite_quotient_span_pow K ha N
  set P : Submodule K.O R := I • (⊤ : Submodule K.O R)
  haveI : Module.Finite (K.O ⧸ I) (R ⧸ P) := Module.Finite.of_restrictScalars_finite K.O _ _
  haveI : Finite (R ⧸ P) := Module.finite_of_finite (K.O ⧸ I)
  haveI : Finite (Submodule K.O (R ⧸ P)) :=
    Finite.of_injective (fun Q : Submodule K.O (R ⧸ P) => (Q : Set (R ⧸ P))) SetLike.coe_injective
  let Φ : Submodule K.O B.A → Submodule K.O (R ⧸ P) := fun M => (M.comap R.subtype).map P.mkQ
  have key : ∀ M ∈ Sandwich K B a N, M = ((Φ M).comap P.mkQ).map R.subtype := by
    intro M hM
    have hP : P ≤ M.comap R.subtype := by
      refine Submodule.smul_le.2 fun r hr n _ => ?_
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul, mul_smul]
      exact M.smul_mem b (hM.1 _ n.2)
    rw [Submodule.comap_map_mkQ, sup_eq_right.2 hP, Submodule.map_comap_subtype,
      inf_eq_right.2 fun m hm => hM.2 m hm]
  have hinj : Set.InjOn Φ (Sandwich K B a N) := by
    intro M₁ h₁ M₂ h₂ h
    rw [key M₁ h₁, key M₂ h₂, h]
  exact Set.Finite.of_finite_image (Set.toFinite _) hinj

theorem card_pos_le : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι) (a : K.O),
    B.P.Separable → K.Small a → IsFrame B e π S → ∀ N : ℕ, ∃ C : ℕ, ∀ p : ι → ℤ,
    {M : Submodule K.O B.A | Pos B a e N M p}.Finite ∧ {M : Submodule K.O B.A | Pos B a e N M p}.ncard ≤ C := by
  intro K B ι _ e π S a hP ha hF N
  have he : CompleteOrthogonalIdempotents e := hF.1.1
  haveI : Algebra.Etale K.E B.A := GlobalTheory.etale_of_separable_charpoly_mulLeft K.E B.A B.g hP
  have hR := GlobalTheory.IntegralClosureFG.integralClosure_fg K.O K.E B.A
  have hfin := sandwich_finite K B hR ha.1 N
  refine ⟨(Sandwich K B a N).ncard, fun p => ?_⟩
  have hal : al K a ≠ 0 := by
    simpa using (IsFractionRing.injective K.O K.E).ne ha.1
  set t : B.A := ∑ j, (al K a ^ (-p j)) • e j with ht
  set t' : B.A := ∑ j, (al K a ^ (p j)) • e j with ht'
  have hcancel : ∀ x : B.A, t' * (t * x) = x := fun x =>
    sum_smul_mul_cancel he (fun j => al K a ^ (-p j)) (fun j => al K a ^ (p j))
      (fun i => by rw [← zpow_add₀ hal, add_neg_cancel, zpow_zero]) x
  have hmaps : ∀ M ∈ {M : Submodule K.O B.A | Pos B a e N M p}, mulLat K.O t M ∈ Sandwich K B a N := by
    intro M hM
    refine ⟨fun r hr => ?_, fun m hm => ?_⟩
    · refine Submodule.mem_map.2 ⟨∑ i, (al K a ^ (p i + N)) • (e i * r),
        Submodule.sum_mem _ fun i _ => (hM i).1 r hr, ?_⟩
      rw [LinearMap.mulLeft_apply, Finset.mul_sum]
      calc ∑ i, t * (al K a ^ (p i + N) • (e i * r)) = ∑ i, (al K a ^ N) • (e i * r) :=
            Finset.sum_congr rfl fun i _ => by
              rw [mul_smul_comm, ht, sum_smul_mul_idem he, smul_smul, ← zpow_add₀ hal,
                show p i + N + -p i = (N : ℤ) by ring, zpow_natCast]
        _ = a ^ N • r := by
            rw [← Finset.smul_sum, ← Finset.sum_mul, he.complete, one_mul, ← map_pow, algebraMap_smul]
    · obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hm
      rw [LinearMap.mulLeft_apply, ht, sum_smul_mul he]
      exact IsIntegral.sum _ fun i _ => (hM i).2 y hy
  have hinj : Set.InjOn (mulLat K.O t) {M : Submodule K.O B.A | Pos B a e N M p} := by
    intro M₁ _ M₂ _ h
    have hid : (LinearMap.mulLeft K.O t').comp (LinearMap.mulLeft K.O t) = LinearMap.id :=
      LinearMap.ext fun x => hcancel x
    have h' := congrArg (Submodule.map (LinearMap.mulLeft K.O t')) h
    simp only [mulLat, ← Submodule.map_comp, hid, Submodule.map_id] at h'
    exact h'
  exact ⟨Set.Finite.of_finite_image (hfin.subset (Set.image_subset_iff.2 hmaps)) hinj,
    Set.ncard_le_ncard_of_injOn _ hmaps hinj hfin⟩

end GlobalTheory.UnitLemma.Desc.PosCount
