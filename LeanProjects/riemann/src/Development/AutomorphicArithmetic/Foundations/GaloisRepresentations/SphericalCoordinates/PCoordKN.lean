import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPosDenominatorOfIsCompactFiniteAdele

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2

section SlopeTestRemainingChoices

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

private theorem smul_mem_laHat {c : AfP p} (hc : IsIntAf c) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) :
    c • v ∈ LaHat D := by
  classical
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  apply KNLevel.mem_laHat_of_repr b
  intro i
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, KNLevel.isIntAf_iff]
  exact mul_mem ((KNLevel.isIntAf_iff _).mp hc)
    ((KNLevel.isIntAf_iff _).mp (KNLevel.repr_isIntAf b v hv i))

private theorem inAf_mem_laHat (a : D.La) : inAf D a ∈ LaHat D := by
  unfold inAf LaHat
  exact AddSubgroup.subset_closure ⟨1, a, (KNLevel.isIntAf_iff 1).mpr (one_mem _), rfl⟩

private theorem exists_den_act (g : G.GAf) :
    ∃ m : ℕ, 0 < m ∧ ∀ z ∈ LaHat D, m • L.actG g z ∈ LaHat D := by
  classical
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  let B := KNLevel.bA b
  obtain ⟨m, hm, hden⟩ := AfPCpctDen.exists_den p
    (Set.range fun ki : Module.Free.ChooseBasisIndex ℤ D.La × Module.Free.ChooseBasisIndex ℤ D.La =>
      B.repr (L.actG g (B ki.1)) ki.2) (Set.finite_range _).isCompact
  refine ⟨m, hm, fun z hz => ?_⟩
  have hy : ∀ k, m • L.actG g (B k) ∈ LaHat D := by
    intro k
    apply KNLevel.mem_laHat_of_repr b
    intro i
    rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul, KNLevel.isIntAf_iff]
    exact hden _ ⟨(k, i), rfl⟩
  rw [← B.sum_repr z, map_sum, Finset.smul_sum]
  refine sum_mem fun k _ => ?_
  rw [LinearMap.map_smul, smul_comm m]
  exact smul_mem_laHat (KNLevel.repr_isIntAf b z hz k) (hy k)

private theorem rd_move (x : (AfP p ⊗[ℚ] G.C)ˣ) (h₁ h₂ : G.GAf) (w : VQ D) :
    rd L x h₂ w = L.actG (h₂⁻¹ * h₁) (rd L x h₁ w) := by
  simp only [rd]
  rw [← Module.End.mul_apply (L.actG (h₂⁻¹ * h₁)), ← map_mul, mul_inv_cancel_right]

private theorem stable (hd : RdDense) (x : (AfP p ⊗[ℚ] G.C)ˣ) (h₁ h₂ : G.GAf) (P : VQ D → Prop)
    (A₁ : ∀ w, P w ↔ rd L x h₁ w ∈ LaHat D) (A₂ : ∀ w, P w ↔ rd L x h₂ w ∈ LaHat D)
    (z : AfP p ⊗[ℚ] VQ D) (hz : z ∈ LaHat D) : L.actG (h₂⁻¹ * h₁) z ∈ LaHat D := by
  obtain ⟨m, hm, hden⟩ := exists_den_act L (h₂⁻¹ * h₁)
  obtain ⟨w, e, he, rfl⟩ := hd p D G L x h₁ m hm z
  have h1 : rd L x h₁ w ∈ LaHat D := by
    have := sub_mem hz (nsmul_mem he m)
    rwa [add_sub_cancel_right] at this
  have h2 : rd L x h₂ w ∈ LaHat D := (A₂ w).mp ((A₁ w).mpr h1)
  rw [map_add, map_nsmul, ← rd_move L x h₁ h₂ w]
  exact add_mem h2 (hden e he)

private theorem congOne_of_gen {N : ℕ} {g : G.GAf}
    (gen : ∀ a : D.La, ∃ u ∈ LaHat D, L.actG g (inAf D a) = inAf D a + N • u) : L.CongOne N g := by
  unfold Link.CongOne
  intro v hv
  unfold LaHat at hv
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, y, hc, rfl⟩ := hz
    obtain ⟨u, hu, hgu⟩ := gen y
    have hcy : c ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] y) = c • inAf D y := by
      rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    refine ⟨c • u, smul_mem_laHat hc hu, ?_⟩
    rw [hcy, LinearMap.map_smul, hgu, smul_add, smul_comm c N u]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨w₁, hw₁, e₁⟩ := hy
    obtain ⟨w₂, hw₂, e₂⟩ := hz
    exact ⟨w₁ + w₂, add_mem hw₁ hw₂, by rw [map_add, e₁, e₂, smul_add]; abel⟩
  | neg y _ hy =>
    obtain ⟨w, hw, e⟩ := hy
    exact ⟨-w, neg_mem hw, by rw [map_neg, e, neg_add, smul_neg]⟩

end SlopeTestRemainingChoices

theorem coordKN_of : RdDense → CoordKN := by
  intro hd p _ D G L x N hN hcop D' t j h₁ h₂ hc1
  have memOf : ∀ {g : G.GAf}, L.CongOne N g → ∀ v ∈ LaHat D, L.actG g v ∈ LaHat D := by
    intro g hC v hv
    obtain ⟨w, hw, e⟩ := hC v hv
    rw [e]
    exact add_mem hv (nsmul_mem hw N)
  have cong : ∀ k₁ k₂ : G.GAf, IsCoordA L x N D' t j k₁ → IsCoordA L x N D' t j k₂ →
      L.CongOne N (k₂⁻¹ * k₁) := by
    intro k₁ k₂ hk₁ hk₂
    have hst : ∀ z ∈ LaHat D, L.actG (k₂⁻¹ * k₁) z ∈ LaHat D :=
      stable L hd x k₁ k₂ (fun w => ∃ r u, p ^ r • w = j u) hk₁.1 hk₂.1
    apply congOne_of_gen L
    intro a
    obtain ⟨w₁, hw₁, e₁⟩ := hk₁.2 a
    obtain ⟨w₂, hw₂, e₂⟩ := hk₂.2 a
    refine ⟨w₂ - L.actG (k₂⁻¹ * k₁) w₁, sub_mem hw₂ (hst w₁ hw₁), ?_⟩
    have e₃ := rd_move L x k₁ k₂ (j (t a))
    rw [e₂, e₁, map_add, map_nsmul] at e₃
    rw [smul_sub, ← add_sub_assoc, e₃]
    abel
  constructor
  · intro hc2
    exact ⟨cong h₁ h₂ hc1 hc2, by rw [mul_inv_rev, inv_inv]; exact cong h₂ h₁ hc2 hc1⟩
  · intro hg
    obtain ⟨hC, hCi⟩ := hg
    have hinv : (h₂⁻¹ * h₁)⁻¹ = h₁⁻¹ * h₂ := by rw [mul_inv_rev, inv_inv]
    refine ⟨fun w => ?_, fun a => ?_⟩
    · rw [hc1.1 w]
      constructor
      · intro hw
        rw [rd_move L x h₁ h₂ w]
        exact memOf hC _ hw
      · intro hw
        rw [rd_move L x h₂ h₁ w, ← hinv]
        exact memOf hCi _ hw
    · obtain ⟨w₁, hw₁, e₁⟩ := hc1.2 a
      obtain ⟨w₃, hw₃, e₃⟩ := hC _ (inAf_mem_laHat a)
      refine ⟨w₃ + L.actG (h₂⁻¹ * h₁) w₁, add_mem hw₃ (memOf hC _ hw₁), ?_⟩
      rw [rd_move L x h₁ h₂, e₁, map_add, map_nsmul, e₃, smul_add, add_assoc]

end UpperTheory.Gal.W2
