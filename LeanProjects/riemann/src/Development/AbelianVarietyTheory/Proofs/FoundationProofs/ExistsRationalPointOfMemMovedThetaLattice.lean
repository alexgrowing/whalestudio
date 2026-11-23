import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.NormSum.MovedTheta

open Matrix GlobalTheory.NormSum.AdLattice

variable {D : D7} {N N' : ℕ}

def mv (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (z : Matrix (Fin N') (Fin N) D.host.E) :
    Matrix (Fin N') (Fin N) (AE D) :=
  ((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
    (g : Matrix (Fin N) (Fin N) (AE D))

theorem mv_zero (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) : mv g g' 0 = 0 := by
  unfold mv
  rw [Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul]

theorem mv_add (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (z w : Matrix (Fin N') (Fin N) D.host.E) :
    mv g g' (z + w) = mv g g' z + mv g g' w := by
  unfold mv
  rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]

theorem mv_smul (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (e : D.host.E)
    (z : Matrix (Fin N') (Fin N) D.host.E) : mv g g' (e • z) = inc D e • mv g g' z := by
  unfold mv
  have : (e • z).map (inc D) = inc D e • z.map (inc D) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem inc_int (o : 𝓞 D.host.E) : inc D (o : D.host.E) ∈ OhE D :=
  (incl_mem_iff (F := ℚ) (o : D.host.E)).2 ⟨o, rfl⟩

theorem mulVec_mem_of_span {R m n : Type} [CommRing R] [Fintype n] {S : Subring R} (M : Matrix m n R) (i : m)
    {T : Set (n → R)} (hT : ∀ u ∈ T, (M *ᵥ u) i ∈ S) {u : n → R} (hu : u ∈ Submodule.span S T) :
    (M *ᵥ u) i ∈ S := by
  induction hu using Submodule.span_induction with
  | mem u hu => exact hT u hu
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [mulVec_add]; exact add_mem hu hv
  | smul s u _ hu =>
    have e : s • u = (s : R) • u := rfl
    rw [e, mulVec_smul]
    exact mul_mem s.2 hu

theorem mv_int_of_maps {g : GL (Fin N) (AE D)} {g' : GL (Fin N') (AE D)}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h : Moves D g L) (h' : Moves D g' L') {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : ∀ x ∈ L, A.mulVec x ∈ L') (i : Fin N') (j : Fin N) : mv g g' A i j ∈ OhE D := by
  have hL : L = lat g := by
    ext x
    exact (h x).trans (mem_lat g x).symm
  have h1 := (lat_span g ((g : Matrix (Fin N) (Fin N) (AE D)) *ᵥ Pi.single j 1)).2 (by
    intro k
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _)
  have h3 := mulVec_mem_of_span
    (((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * A.map (inc D)) i (by
      rintro _ ⟨x, hx, rfl⟩
      have h2 := (h' _).1 (hA x (hL ▸ hx)) i
      have e : (fun j => inc D ((A *ᵥ x) j)) = A.map (inc D) *ᵥ (fun j => inc D (x j)) := by
        ext k; rw [RingHom.map_mulVec]; rfl
      rw [e, mulVec_mulVec] at h2
      exact h2) h1
  rw [mulVec_mulVec, mulVec_single_one] at h3
  exact h3

theorem mv_int_of_hom {g : GL (Fin N) (AE D)} {g' : GL (Fin N') (AE D)}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h : Moves D g L) (h' : Moves D g' L') {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ homL D L L') (i : Fin N') (j : Fin N) : mv g g' A i j ∈ OhE D := by
  induction hA using Submodule.span_induction with
  | mem A hA => exact mv_int_of_maps h h' hA i j
  | zero => rw [mv_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [mv_add]; exact add_mem hu hv
  | smul o u _ hu =>
    have e : o • u = (o : D.host.E) • u := rfl
    rw [e, mv_smul]
    exact mul_mem (inc_int o) hu

theorem mul_mem_IhE {cc : Ideal (𝓞 D.host.K)} {s y : AE D} (hs : s ∈ OhE D) (hy : y ∈ IhE D cc) :
    s * y ∈ IhE D cc := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, a, ha, t, ht, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨c, hc, a, ha, s * t, mul_mem hs ht, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
  | neg u _ hu => rw [mul_neg]; exact neg_mem hu

theorem mv_mem_IhE {cc : Ideal (𝓞 D.host.K)} {g : GL (Fin N) (AE D)} {g' : GL (Fin N') (AE D)}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h : Moves D g L) (h' : Moves D g' L') {c : 𝓞 D.host.K} (hc : c ∈ cc)
    {B : Matrix (Fin N') (Fin N) D.host.E} (hB : B ∈ YYl D L L') (i : Fin N') (j : Fin N) :
    mv g g' (((c : D.host.K) : D.host.E) • B) i j ∈ IhE D cc := by
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    rw [smul_smul, mv_smul]
    exact AddSubgroup.subset_closure ⟨c, hc, a, ha, _, mv_int_of_hom h h' hA i j, rfl⟩
  | zero => rw [smul_zero, mv_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [smul_add, mv_add]; exact add_mem hu hv
  | smul o u _ hu =>
    have e : o • u = (o : D.host.E) • u := rfl
    rw [e, smul_comm, mv_smul]
    exact mul_mem_IhE (inc_int o) hu

theorem pt_zero (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    pt D (tor0 D cc δ) δ (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
  funext τ i j
  simp [pt, embV, tor0]

theorem pt_add (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (z w : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z + w) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ w := by
  funext τ i j
  simp [pt, embV, tor0, mul_add]

theorem pt_neg (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (-z) = -pt D (tor0 D cc δ) δ z := by
  funext τ i j
  simp [pt, embV, tor0]

theorem mv_neg (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (z : Matrix (Fin N') (Fin N) D.host.E) :
    mv g g' (-z) = -mv g g' z := by
  rw [← neg_one_smul D.host.E z, mv_smul, map_neg, map_one, neg_one_smul]

end GlobalTheory.NormSum.MovedTheta

open GlobalTheory.NormSum.MovedTheta in

theorem GlobalTheory.NormSum.exists_pt_of_mem_La_moved : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' : ℕ) (g : GA D N) (g' : GA D N') (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → ∀ x ∈ La D (tor0 D cc δ) L₁ L₁', ∃ z : Matrix (Fin N') (Fin N) D.host.E, x = pt D (tor0 D cc δ) δ z ∧ ∀ i j, ((((g' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) * ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) i j ∈ IhE D cc := by
  intro D hG cc δ _ N N' g g' L L' h h' x hx
  let P : VC D N N' → Prop := fun x => ∃ z : Matrix (Fin N') (Fin N) D.host.E, x = pt D (tor0 D cc δ) δ z ∧
    ∀ i j, mv (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) z i j ∈ IhE D cc
  have h0 : P 0 := ⟨0, (pt_zero cc δ).symm, fun i j => by rw [mv_zero]; exact zero_mem _⟩
  have hadd : ∀ u v, P u → P v → P (u + v) := by
    rintro _ _ ⟨z, rfl, hz⟩ ⟨w, rfl, hw⟩
    exact ⟨z + w, (pt_add cc δ z w).symm, fun i j => by rw [mv_add]; exact add_mem (hz i j) (hw i j)⟩
  have hneg : ∀ u, P u → P (-u) := by
    rintro _ ⟨z, rfl, hz⟩
    exact ⟨-z, (pt_neg cc δ z).symm, fun i j => by rw [mv_neg]; exact neg_mem (hz i j)⟩
  show P x
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    change w ∈ lamOf D cc δ at hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨c, hc, rfl⟩ := hw
      refine ⟨((c : D.host.K) : D.host.E) • A, ?_, mv_mem_IhE h h' hc hA⟩
      funext τ i j
      have e := hG.1 τ (c : D.host.K)
      simp only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
      rw [e, mul_assoc]
    | zero => rw [zero_smul]; exact h0
    | add u v _ _ hu hv => rw [add_smul]; exact hadd _ _ hu hv
    | neg u _ hu => rw [neg_smul]; exact hneg _ hu
  | zero => exact h0
  | add u v _ _ hu hv => exact hadd _ _ hu hv
  | neg u _ hu => exact hneg _ hu
