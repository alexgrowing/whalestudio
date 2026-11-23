import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsTildeVanish
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeVanishLoc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Compare

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem coe_d_sub (F : SubSystem S x E) {i : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥(F.sub I)) i)
    (J : Cech.Idx (support x) (i + 1)) :
    ((Cech.d (fun I : Chart x => ↥(F.sub I)) F.res i t J : F.sub J.1) : E) =
      ∑ j : J.1.1, Cech.sgn J.1.1 j • (t (Cech.face J j) : E) := by
  rw [Cech.d_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Submodule.coe_smul_of_tower]
  rfl

variable (M : FinGradedSub (S := S) (x := x) E) (c : ℤ)

def liftTilde (I : StdCell N) (hI : I.1 ⊆ support x) (y : M.tilde c ⟨I.1, I.2.1, hI⟩) :
    LocMod S N M.coneSubE I.1 :=
  Classical.choose (exists_locConeE_eq M c I hI y.2)

theorem liftTilde_mem (I : StdCell N) (hI : I.1 ⊆ support x) (y : M.tilde c ⟨I.1, I.2.1, hI⟩) :
    liftTilde M c I hI y ∈ degLoc M.coneGradedE c I :=
  (Classical.choose_spec (exists_locConeE_eq M c I hI y.2)).1

theorem locConeE_liftTilde (I : StdCell N) (hI : I.1 ⊆ support x) (y : M.tilde c ⟨I.1, I.2.1, hI⟩) :
    locConeE M I.1 hI (liftTilde M c I hI y) = singleE S x E c y :=
  (Classical.choose_spec (exists_locConeE_eq M c I hI y.2)).2

def liftCochain {i : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) i) :
    Cech.Cochain (locSys S N M.coneSubE) i := fun J =>
  if hJ : J.1.1 ⊆ support x then liftTilde M c J.1 hJ (t ⟨⟨J.1.1, J.1.2.1, hJ⟩, J.2⟩) else 0

theorem liftCochain_of {i : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) i)
    (J : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) (hJ : J.1.1 ⊆ support x) :
    liftCochain M c t J = liftTilde M c J.1 hJ (t ⟨⟨J.1.1, J.1.2.1, hJ⟩, J.2⟩) :=
  dif_pos hJ

theorem liftCochain_mem {i : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) i) :
    liftCochain M c t ∈ Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) i := by
  intro J _
  by_cases hJ : J.1.1 ⊆ support x
  · rw [liftCochain_of M c t J hJ]
    exact liftTilde_mem M c _ hJ _
  · change (if hJ : J.1.1 ⊆ support x then _ else 0) ∈ _
    rw [dif_neg hJ]
    exact zero_mem _

theorem locConeE_d {i : ℕ} (z : Cech.Cochain (locSys S N M.coneSubE) i)
    (K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) (i + 1)) (hK : K.1.1 ⊆ support x) :
    locConeE M K.1.1 hK (Cech.d (locSys S N M.coneSubE) locResS i z K) =
      ∑ j : K.1.1, Cech.sgn K.1.1 j • locConeE M (Cech.face K j).1.1
        ((Cech.face_subset K j).trans hK) (z (Cech.face K j)) := by
  rw [Cech.d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  congr 1
  exact locConeE_locRes M (Cech.face_subset K j) hK _

theorem d_liftCochain {i : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) (i + 1))
    (ht : Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res (i + 1) t = 0) :
    Cech.d (locSys S N M.coneSubE) locResS (i + 1) (liftCochain M c t) = 0 := by
  funext K
  change _ = 0
  by_cases hK : K.1.1 ⊆ support x
  · apply locConeE_injective M K.1.1 hK
    rw [locConeE_d M (liftCochain M c t) K hK, map_zero]
    have h0 := coe_d_sub (M.tildeSys c) t ⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩
    rw [ht] at h0
    calc ∑ j : K.1.1, Cech.sgn K.1.1 j • locConeE M (Cech.face K j).1.1
          ((Cech.face_subset K j).trans hK) (liftCochain M c t (Cech.face K j))
        = ∑ j : K.1.1, Cech.sgn K.1.1 j • singleE S x E c
            (t (Cech.face (⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩ : Cech.Idx (support x) (i + 1 + 1)) j) : E) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [liftCochain_of M c t _ ((Cech.face_subset K j).trans hK)]
          congr 1
          exact locConeE_liftTilde M c _ _ _
      _ = singleE S x E c (∑ j : K.1.1, Cech.sgn K.1.1 j •
            (t (Cech.face (⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩ : Cech.Idx (support x) (i + 1 + 1)) j) : E)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_zsmul]
      _ = 0 := by
          rw [← h0]
          exact map_zero _
  · haveI := locModE_subsingleton (S := S) M (Finset.not_subset.mp hK).choose_spec.1
      (by simpa [mem_support] using (Finset.not_subset.mp hK).choose_spec.2)
    exact Subsingleton.elim _ _

theorem tildeSys_H_subsingleton (k : ℕ) (h : Subsingleton (cohom M.coneGradedE (k + 1) c)) :
    Subsingleton ((M.tildeSys c).H (k + 1)) := by
  unfold cohom Cech.Hdeg at h
  rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff'] at h
  unfold SubSystem.H Cech.H
  refine Submodule.Quotient.subsingleton_iff.mpr (Submodule.eq_top_iff'.mpr ?_)
  rintro ⟨t, ht⟩
  rw [Submodule.mem_comap]
  change t ∈ LinearMap.range (Cech.d _ (M.tildeSys c).res k)
  have hz : liftCochain M c t ∈
      Cech.cocyDeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) locResS (k + 1) :=
    ⟨d_liftCochain M c t (LinearMap.mem_ker.mp ht), liftCochain_mem M c t⟩
  have hb := h ⟨_, hz⟩
  rw [Submodule.mem_comap] at hb
  change liftCochain M c t ∈ (Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) k).map
    (Cech.d (locSys S N M.coneSubE) locResS k) at hb
  obtain ⟨y, hy, hyz⟩ := hb
  have hu : ∀ I : Cech.Idx (support x) k, coeffE S x E c (locConeE M I.1.1 I.1.2.2
      (y ⟨⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩, I.2⟩)) ∈ (M.tildeSys c).sub I.1 := fun I => by
    obtain ⟨v, hv, hyv⟩ := locConeE_degLoc M c _ I.1.2.2
      (hy ⟨⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩, I.2⟩ (Set.mem_univ _))
    rw [hyv, coeffE_singleE_same]
    exact hv
  refine ⟨fun I => ⟨_, hu I⟩, ?_⟩
  funext J
  apply Subtype.ext
  rw [coe_d_sub]
  have e1 := locConeE_liftTilde M c ⟨J.1.1, J.1.2.1, Finset.subset_univ _⟩ J.1.2.2 (t J)
  have e2 := congrFun hyz ⟨⟨J.1.1, J.1.2.1, Finset.subset_univ _⟩, J.2⟩
  rw [liftCochain_of M c t _ J.1.2.2] at e2
  rw [← coeffE_singleE_same (S := S) (x := x) c (t J : E), ← e1, ← e2]
  refine Eq.trans ?_ (congrArg (coeffE S x E c)
    (locConeE_d M y ⟨⟨J.1.1, J.1.2.1, Finset.subset_univ _⟩, J.2⟩ J.1.2.2)).symm
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  rfl

end Compare

theorem TildeVanish.proof (h : SerreVanish.Statement.{u, v}) : TildeVanish.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ M
  obtain ⟨c₀, hc₀⟩ := h S N M.coneSubE M.coneGradedE M.coneSubE_finite
  refine ⟨c₀, fun i hi c hc => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  exact tildeSys_H_subsingleton M c k (hc₀ (k + 1) hi c hc)

end

end GroundTheory.Heights₂.Heights.Kleiman
