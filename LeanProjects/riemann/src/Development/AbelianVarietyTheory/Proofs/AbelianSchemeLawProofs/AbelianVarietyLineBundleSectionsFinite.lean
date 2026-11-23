import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.AbLaw

def finSecPullId {X : Scheme.{0}} {M : LB X} (s : LB.Sec M) : LB.Sec (M.pull (𝟙 X)) where
  f := fun j => rs X (LB.wchart_le M (K := PUnit) (fun _ => 𝟙 X) j PUnit.unit) (s.f (j PUnit.unit))
  compat := fun i j => by
    have h := congrArg (rs X (inf_le_inf (LB.wchart_le M (K := PUnit) (fun _ => 𝟙 X) i PUnit.unit)
      (LB.wchart_le M (K := PUnit) (fun _ => 𝟙 X) j PUnit.unit) :
        (M.pull (𝟙 X)).U i ⊓ (M.pull (𝟙 X)).U j ≤ M.U (i PUnit.unit) ⊓ M.U (j PUnit.unit)))
      (s.compat (i PUnit.unit) (j PUnit.unit))
    rw [map_mul] at h
    erw [rs_rs, rs_rs] at h
    erw [rs_rs, rs_rs, h]
    congr 1
    unfold LB.pull LB.LinComb
    dsimp only
    rw [Fintype.prod_unique, zpow_one]
    rfl

theorem finSec_eq_zero_of_cover {X : Scheme.{0}} {I : Type} (V : I → X.Opens) (hV : ⨆ i, V i = ⊤)
    {U : X.Opens} (x : Γ(X, U)) (hx : ∀ i, rs X (inf_le_left : U ⊓ V i ≤ U) x = 0) : x = 0 := by
  refine X.sheaf.eq_of_locally_eq' (fun i => U ⊓ V i) U (fun i => homOfLE inf_le_left) ?_ x 0 ?_
  · rw [← inf_iSup_eq, hV, inf_top_eq]
  · intro i
    exact (hx i).trans (map_zero (rs X (inf_le_left : U ⊓ V i ≤ U))).symm

theorem Perf.exists_relation {X : Scheme.{0}} {K : Type} [Field K] {f : X ⟶ Spec (CommRingCat.of K)}
    {M : LB X} (Q : Perf f M) (s : Fin (Q.a + 1) → LB.Sec M) :
    ∃ c : Fin (Q.a + 1) → K, c ≠ 0 ∧ ∀ i, ∑ k, cst f (M.U i) (c k) * (s k).f i = 0 := by
  have hpb : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id K))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.id_horiz f
  obtain ⟨E, hE⟩ := Q.sec K (RingHom.id K) X (𝟙 X) f hpb
  let v : Fin (Q.a + 1) → Fin Q.a → K := fun k => (E.symm (finSecPullId (s k))).1
  have hv : ∀ k j, rs X (Q.le j) ((s k).f (Q.ch j)) = ∑ l, cst f (Q.W j) (v k l) * Q.u l j := by
    intro k j
    have h := hE (E.symm (finSecPullId (s k))) j
    rw [Equiv.apply_symm_apply] at h
    refine Eq.trans ?_ h
    exact (rs_rs _ _ _).symm
  have hdep : ¬ LinearIndependent K v := by
    intro h
    have := h.fintype_card_le_finrank
    simp at this
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨c, hc, k₀, hk₀⟩ := hdep
  have hc' : ∀ l, ∑ k, c k * v k l = 0 := fun l => by
    have := congrFun hc l
    simpa [Finset.sum_apply] using this
  have hW : ∀ j, ∑ k, cst f (Q.W j) (c k) * rs X (Q.le j) ((s k).f (Q.ch j)) = 0 := by
    intro j
    simp only [hv, Finset.mul_sum, ← _root_.mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, ← map_sum, hc', map_zero, zero_mul, Finset.sum_const_zero]
  refine ⟨c, fun h => hk₀ (congrFun h k₀), fun i => ?_⟩
  refine finSec_eq_zero_of_cover Q.W Q.cover _ fun j => ?_
  have h₁ : ∀ k, rs X (inf_le_left : M.U i ⊓ Q.W j ≤ M.U i) ((s k).f i) =
      rs X (inf_le_inf le_rfl (Q.le j) : M.U i ⊓ Q.W j ≤ M.U i ⊓ M.U (Q.ch j)) (M.g i (Q.ch j)).val *
        rs X (inf_le_right : M.U i ⊓ Q.W j ≤ Q.W j) (rs X (Q.le j) ((s k).f (Q.ch j))) := by
    intro k
    have h := congrArg (rs X (inf_le_inf le_rfl (Q.le j) : M.U i ⊓ Q.W j ≤ M.U i ⊓ M.U (Q.ch j)))
      ((s k).compat i (Q.ch j))
    rw [map_mul] at h
    simp only [rs_rs] at h ⊢
    exact h
  have h₂ := congrArg (rs X (inf_le_right : M.U i ⊓ Q.W j ≤ Q.W j)) (hW j)
  simp only [map_sum, map_mul, rs_cst, map_zero] at h₂
  simp only [map_sum, map_mul, rs_cst, h₁]
  simp only [mul_left_comm (cst f _ _), ← Finset.mul_sum, h₂, mul_zero]

theorem sections_finite_of_perf
    (hperf : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)),
      Smooth f → IsProjBy f → ∀ M : LB X, M.IsLB → Nonempty (Perf f M))
    (hva : ∀ (S : Scheme.{0}) (P : PolAV S) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S)
      (X : Scheme.{0}) (π : X ⟶ P.A.left) (f : X ⟶ Spec (CommRingCat.of R)),
      IsPullback π f P.A.hom t → ∃ N : ℕ, 1 ≤ N ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (P.L.pull π) N)),
        (pw (P.L.pull π) N).IsLB ∧ VeryAmpleBy f (pw (P.L.pull π) N) s)
    (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (M : LB P.A.left)
    (hM : M.IsLB) :
    ∃ n : ℕ, ∀ s : Fin n → LB.Sec M, ∃ c : Fin n → Γ(Spec (CommRingCat.of K), ⊤), c ≠ 0 ∧
      ∀ i, ∑ k, (P.A.hom.appLE ⊤ (M.U i) le_top).hom (c k) * (s k).f i = 0 := by
  obtain ⟨N, -, m, σ, hLB, hσ⟩ := hva _ P K (𝟙 _) P.A.left (𝟙 _) P.A.hom (IsPullback.id_horiz _)
  have hsm : Smooth P.A.hom := by
    haveI := P.smoothDim
    exact SmoothOfRelativeDimension.smooth P.g _
  obtain ⟨Q⟩ := hperf K P.A.left P.A.hom hsm ⟨_, hLB, m, σ, hσ⟩ M hM
  refine ⟨Q.a + 1, fun s => ?_⟩
  obtain ⟨c, hc, h⟩ := Q.exists_relation s
  refine ⟨fun k => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c k), fun h0 => hc ?_, h⟩
  funext k
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1
  exact hinj ((congrFun h0 k).trans (map_zero _).symm)

end GlobalTheory.AbLaw
