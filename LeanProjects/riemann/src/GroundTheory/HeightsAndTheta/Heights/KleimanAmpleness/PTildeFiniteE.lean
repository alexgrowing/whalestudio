import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TildeFiniteESt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeVanish
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section ReadOnCharts

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  (M : FinGradedSub (S := S) (x := x) E) (c : ℤ)

def chartVal {n : ℕ} (y : Cech.Cochain (locSys S N M.coneSubE) n) (I : Cech.Idx (support x) n) : E :=
  coeffE S x E c (locConeE M I.1.1 I.1.2.2 (y ⟨⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩, I.2⟩))

theorem chartVal_zero {n : ℕ} (I : Cech.Idx (support x) n) :
    chartVal M c (0 : Cech.Cochain (locSys S N M.coneSubE) n) I = 0 := by
  unfold chartVal
  rw [Pi.zero_apply, map_zero, map_zero]

theorem chartVal_add {n : ℕ} (y y' : Cech.Cochain (locSys S N M.coneSubE) n) (I : Cech.Idx (support x) n) :
    chartVal M c (y + y') I = chartVal M c y I + chartVal M c y' I := by
  unfold chartVal
  rw [Pi.add_apply, map_add, map_add]

theorem chartVal_smul {n : ℕ} (a : S) (y : Cech.Cochain (locSys S N M.coneSubE) n)
    (I : Cech.Idx (support x) n) : chartVal M c (a • y) I = a • chartVal M c y I := by
  unfold chartVal
  rw [Pi.smul_apply, LinearMap.map_smul_of_tower, map_smul]

theorem chartVal_mem {n : ℕ} {y : Cech.Cochain (locSys S N M.coneSubE) n}
    (hy : y ∈ Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) n) (I : Cech.Idx (support x) n) :
    chartVal M c y I ∈ (M.tildeSys c).sub I.1 := by
  obtain ⟨v, hv, hyv⟩ := locConeE_degLoc M c _ I.1.2.2
    (hy ⟨⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩, I.2⟩ (Set.mem_univ _))
  unfold chartVal
  rw [hyv, coeffE_singleE_same]
  exact hv

theorem chartVal_d {n : ℕ} (y : Cech.Cochain (locSys S N M.coneSubE) n) (J : Cech.Idx (support x) (n + 1)) :
    chartVal M c (Cech.d (locSys S N M.coneSubE) locResS n y) J =
      ∑ j : J.1.1, Cech.sgn J.1.1 j • chartVal M c y (Cech.face J j) := by
  refine (congrArg (coeffE S x E c)
    (locConeE_d M y ⟨⟨J.1.1, J.1.2.1, Finset.subset_univ _⟩, J.2⟩ J.1.2.2)).trans ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  rfl

def toTildeC {n : ℕ} (y : Cech.Cochain (locSys S N M.coneSubE) n)
    (hy : y ∈ Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) n) :
    Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) n :=
  fun I => ⟨chartVal M c y I, chartVal_mem M c hy I⟩

theorem coe_d_toTildeC {n : ℕ} (y : Cech.Cochain (locSys S N M.coneSubE) n)
    (hy : y ∈ Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) n) (J : Cech.Idx (support x) (n + 1)) :
    ((Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res n (toTildeC M c y hy) J : _) : E) =
      chartVal M c (Cech.d (locSys S N M.coneSubE) locResS n y) J := by
  rw [coe_d_sub, chartVal_d]
  rfl

def toTildeCocy (n : ℕ) :
    Cech.cocyDeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) locResS n →ₗ[S]
      LinearMap.ker (Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res n) where
  toFun y := ⟨toTildeC M c y.1 y.2.2, LinearMap.mem_ker.mpr (funext fun J => Subtype.ext (by
    rw [coe_d_toTildeC, LinearMap.mem_ker.mp y.2.1, chartVal_zero]
    rfl))⟩
  map_add' y y' := Subtype.ext (funext fun I => Subtype.ext (chartVal_add M c y.1 y'.1 I))
  map_smul' a y := Subtype.ext (funext fun I => Subtype.ext (chartVal_smul M c a y.1 I))

def toTildeH (n : ℕ) : cohom M.coneGradedE n c →ₗ[S] (M.tildeSys c).H n :=
  Submodule.liftQ _ ((Submodule.mkQ _).comp (toTildeCocy M c n)) (by
    intro y hy
    rw [Submodule.mem_comap] at hy
    refine LinearMap.mem_ker.mpr ((Submodule.Quotient.mk_eq_zero _).mpr ?_)
    cases n with
    | zero =>
      change (y : Cech.Cochain (locSys S N M.coneSubE) 0) ∈ (⊥ : Submodule S _) at hy
      rw [Submodule.mem_bot] at hy
      change toTildeC M c y.1 y.2.2 ∈ (⊥ : Submodule S _)
      rw [Submodule.mem_bot]
      funext I
      apply Subtype.ext
      change chartVal M c (y : Cech.Cochain (locSys S N M.coneSubE) 0) I = 0
      rw [hy, chartVal_zero]
    | succ k =>
      change (y : Cech.Cochain (locSys S N M.coneSubE) (k + 1)) ∈
        (Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) k).map
          (Cech.d (locSys S N M.coneSubE) locResS k) at hy
      obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hy
      change toTildeC M c y.1 y.2.2 ∈
        LinearMap.range (Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res k)
      refine ⟨toTildeC M c z hz, funext fun J => Subtype.ext ?_⟩
      rw [coe_d_toTildeC]
      change _ = chartVal M c (y : Cech.Cochain (locSys S N M.coneSubE) (k + 1)) J
      rw [← hzy])

theorem d_liftCochain_any {n : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) n)
    (ht : Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res n t = 0) :
    Cech.d (locSys S N M.coneSubE) locResS n (liftCochain M c t) = 0 := by
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
            (t (Cech.face (⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩ : Cech.Idx (support x) (n + 1)) j) : E) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [liftCochain_of M c t _ ((Cech.face_subset K j).trans hK)]
          congr 1
          exact locConeE_liftTilde M c _ _ _
      _ = singleE S x E c (∑ j : K.1.1, Cech.sgn K.1.1 j •
            (t (Cech.face (⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩ : Cech.Idx (support x) (n + 1)) j) : E)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_zsmul]
      _ = 0 := by
          rw [← h0]
          exact map_zero _
  · have := locModE_subsingleton (S := S) M (Finset.not_subset.mp hK).choose_spec.1
      (by simpa [mem_support] using (Finset.not_subset.mp hK).choose_spec.2)
    exact Subsingleton.elim _ _

theorem chartVal_liftCochain {n : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) n)
    (I : Cech.Idx (support x) n) : chartVal M c (liftCochain M c t) I = (t I : E) := by
  have e1 := liftCochain_of M c t ⟨⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩, I.2⟩ I.1.2.2
  have e2 := locConeE_liftTilde M c ⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩ I.1.2.2 (t I)
  unfold chartVal
  rw [e1]
  exact (congrArg (coeffE S x E c) e2).trans (coeffE_singleE_same _ _)

theorem toTildeH_surjective (n : ℕ) : Function.Surjective (toTildeH M c n) := by
  intro q
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine ⟨Submodule.Quotient.mk ⟨liftCochain M c t.1,
    d_liftCochain_any M c t.1 (LinearMap.mem_ker.mp t.2), liftCochain_mem M c t.1⟩, ?_⟩
  change Submodule.Quotient.mk (toTildeCocy M c n _) = Submodule.Quotient.mk t
  congr 1
  exact Subtype.ext (funext fun I => Subtype.ext (chartVal_liftCochain M c t.1 I))

end ReadOnCharts

theorem TildeFiniteE.proof (h : SerreFinite.Statement.{u, v}) : TildeFiniteE.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ M i c
  have : Module.Finite S (cohom M.coneGradedE i c) :=
    h S N M.coneSubE M.coneGradedE M.coneSubE_finite i c
  exact Module.Finite.of_surjective (toTildeH M c i) (toTildeH_surjective M c i)

end

end GroundTheory.Heights₂.Heights.Kleiman
