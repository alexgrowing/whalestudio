import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAdelicVectorDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousUnitaryRootExchangeMapStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootExch.ExStruct

open GlobalTheory.BesselCompare (mt_mul mt_one hA_add hA_smul hA_smul_right hA_vec cA_inc)

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem hA_half {ε : AE D} {y : Fin B.rank → AE D} (hy : ε • y = y) (x) : hA B x y = cA D ε * hA B x y := by
  rw [← hA_smul_right, hy]

theorem eps_hA {ε : AE D} (h0 : ε * cA D ε = 0) {y : Fin B.rank → AE D} (hy : ε • y = y) (x) :
    ε * hA B x y = 0 := by
  rw [hA_half hy, ← mul_assoc, h0, zero_mul]

theorem hA_smul_zero {ε : AE D} (h0 : ε * cA D ε = 0) {y y' : Fin B.rank → AE D} (hy : ε • y = y)
    (hy' : ε • y' = y') (x) : hA B x y' • y = 0 := by
  rw [← hy, smul_smul, mul_comm, eps_hA h0 hy', zero_smul]

theorem hA_halves {ε : AE D} (h0 : ε * cA D ε = 0) {y y' : Fin B.rank → AE D} (hy : ε • y = y)
    (hy' : ε • y' = y') : hA B y y' = 0 := by
  rw [← hy, hA_smul, eps_hA h0 hy']

theorem isK_mul {ε : AE D} (h0 : ε * cA D ε = 0) {v y y' : Fin B.rank → AE D} (hy : ε • y = y)
    (hy' : ε • y' = y') (hv' : hA B y' v = 0) (hv : hA B v y = 0) {k k' : GA D B} (hk : IsK B v y k)
    (hk' : IsK B v y' k') : IsK B v (y + y') (k * k') := by
  intro x
  rw [mulVec_mul, hk', hk]
  simp only [hA_add, hA_sub, hA_smul, hA_add_right, hv, hv', hA_halves h0 hy' hy, mul_zero, add_zero, sub_zero,
    add_smul, smul_add, mul_comm (hA B x y'), mul_smul, hA_smul_zero h0 hy hy', smul_zero, zero_smul]
  abel

theorem isK_eps {ε : AE D} (h0 : ε * cA D ε = 0) {v y : Fin B.rank → AE D} (hy : ε • y = y) {k : GA D B}
    (hk : IsK B v y k) (x) : ε • ((mt B k).mulVec x - x) = -(hA B x v • y) := by
  rw [hk, add_sub_assoc, add_sub_cancel_left, smul_sub, smul_smul, eps_hA h0 hy, zero_smul, zero_sub, smul_comm, hy]

theorem isK_supp {ε : AE D} (h1 : ε * ε = ε) (h0 : ε * cA D ε = 0) {v y : Fin B.rank → AE D} (hy : ε • y = y)
    {k : GA D B} (hk : IsK B v y k) : SuppAt ε B k := by
  rw [suppAt_iff_vec]
  intro x
  have hc : cA D ε • y = 0 := by rw [← hy, smul_smul, mul_comm, h0, zero_smul]
  rw [add_smul, isK_eps h0 hy hk, hk, add_sub_assoc, add_sub_cancel_left, smul_sub, smul_smul, ← hA_half hy,
    smul_comm, hc, smul_zero]
  abel

theorem eq_one_of_half {ε : AE D} {u : GA D B} (hu : SuppAt ε B u) (h : ∀ x, ε • ((mt B u).mulVec x - x) = 0) :
    u = 1 := by
  refine mt_ext fun x => ?_
  rw [mt_one, Matrix.one_mulVec, ← sub_eq_zero, ← suppAt_iff_vec.1 hu x, add_smul, h, zero_add]
  refine hA_nondeg fun y => ?_
  have e : (mt B u).mulVec (ε • y) = ε • y := by
    have := h y
    rwa [smul_sub, sub_eq_zero, ← Matrix.mulVec_smul] at this
  rw [hA_smul, ← hA_smul_right, hA_sub]
  conv_lhs => rw [← e]
  rw [hA_mt, e, sub_self]

theorem iA_eq (t : Fin A.rank → AE D) : iA ι t = ∑ l, t l • vecA B (ι (A.frame l)) := by
  rw [iA, GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.eMat_mulVec]

theorem dual_iA (d : BesselDatum A B ι) (i) (t) : hA B (vecA B (dual d i)) (iA ι t) = 0 :=
  hA_vec_iA (dual_perp d i) t

theorem iA_dual (d : BesselDatum A B ι) (i) (t) : hA B (iA ι t) (vecA B (dual d i)) = 0 := by
  rw [← hA_herm, dual_iA, map_zero]

theorem vec_dual (d : BesselDatum A B ι) (i) (x : A.V) : hA B (vecA B (ι x)) (vecA B (dual d i)) = 0 := by
  rw [← hA_herm, hA_vec, dual_perp, map_zero, map_zero]

theorem mem_exSet (d : BesselDatum A B ι) {ε : AE D} (h1 : ε * ε = ε) (h0 : ε * cA D ε = 0) (i) {t} (ht : ε • t = t)
    {k : GA D B} (hk : IsK B (vecA B (dual d i)) (iA ι t) k) :
    SuppAt ε B k ∧
    (∀ x : A.V, ε • (actV B k (ι x) - vecA B (ι x)) = 0) ∧
    (∀ l, ε • (actV B k (d.f l) - vecA B (d.f l)) = 0) ∧
    (∀ l, l ≠ i → ε • (actV B k (d.aux l) - vecA B (d.aux l)) = 0) ∧
      ε • (actV B k (d.aux i) - vecA B (d.aux i)) = -iA ι t := by
  have hy : ε • iA ι t = iA ι t := by rw [← iA_smul, ht]
  obtain ⟨p1, p2, -⟩ := GlobalTheory.T.besselDatum_adelicVector_decomposition D A B ι d
  unfold actV
  refine ⟨isK_supp h1 h0 hy hk, fun x => ?_, fun l => ?_, fun l hl => ?_, ?_⟩
  · rw [isK_eps h0 hy hk, vec_dual, zero_smul, neg_zero]
  · rw [isK_eps h0 hy hk, hA_vec, p2, map_zero, zero_smul, neg_zero]
  · rw [isK_eps h0 hy hk, hA_vec, p1, if_neg hl, map_zero, zero_smul, neg_zero]
  · rw [isK_eps h0 hy hk, hA_vec, p1, if_pos rfl, map_one, one_smul]

theorem exists_k (d : BesselDatum A B ι) {ε : AE D} (h0 : ε * cA D ε = 0) (i) {t} (ht : ε • t = t) :
    ∃ k : GA D B, IsK B (vecA B (dual d i)) (iA ι t) k := by
  obtain ⟨K, -, hK⟩ := GlobalTheory.T.exists_continuous_unitaryRootExchangeMap D B ε h0 (vecA B (dual d i))
  exact ⟨_, hK ⟨iA ι t, by rw [← iA_smul, ht], dual_iA d i t⟩⟩

theorem isK_one (v : Fin B.rank → AE D) : IsK B v 0 1 := fun x => by
  rw [mt_one, Matrix.one_mulVec, hA_zero_right, zero_smul, smul_zero, add_zero, sub_zero]

theorem isK_unique {v y : Fin B.rank → AE D} {k k' : GA D B} (h : IsK B v y k) (h' : IsK B v y k') : k = k' :=
  mt_ext fun x => (h x).trans (h' x).symm

def kGrp (d : BesselDatum A B ι) {ε : AE D} (h0 : ε * cA D ε = 0) (i : Fin (d.ρ + 1)) : Subgroup (GA D B) where
  carrier := {g | ∃ t, ε • t = t ∧ IsK B (vecA B (dual d i)) (iA ι t) g}
  one_mem' := ⟨0, smul_zero _, by rw [iA, Matrix.mulVec_zero]; exact isK_one _⟩
  mul_mem' := by
    rintro g g' ⟨t, ht, hg⟩ ⟨t', ht', hg'⟩
    refine ⟨t + t', by rw [smul_add, ht, ht'], ?_⟩
    rw [iA_add]
    exact isK_mul h0 (by rw [← iA_smul, ht]) (by rw [← iA_smul, ht']) (iA_dual d i _) (dual_iA d i _) hg hg'
  inv_mem' := by
    rintro g ⟨t, ht, hg⟩
    have ht' : ε • (-t) = -t := by rw [smul_neg, ht]
    obtain ⟨k, hk⟩ := exists_k d h0 i ht'
    have := isK_mul h0 (by rw [← iA_smul, ht]) (by rw [← iA_smul, ht']) (iA_dual d i _) (dual_iA d i _) hg hk
    rw [iA_neg, add_neg_cancel] at this
    rw [inv_eq_of_mul_eq_one_right (isK_unique this (isK_one _))]
    exact ⟨-t, ht', hk⟩

theorem mulVec_comb (L : Matrix (Fin B.rank) (Fin B.rank) (AE D)) {a : ℕ} (u : Fin a → Fin B.rank → AE D)
    (hu : ∀ i, L.mulVec (u i) = 0) (r : Fin a → AE D) : L.mulVec (∑ i, r i • u i) = 0 := by
  refine Finset.sum_induction _ (fun x => L.mulVec x = 0) (fun x y hx hy => ?_) (Matrix.mulVec_zero _) fun i _ => ?_
  · rw [Matrix.mulVec_add, hx, hy, add_zero]
  · rw [Matrix.mulVec_smul, hu, smul_zero]

theorem mulVec_zero_of (d : BesselDatum A B ι) (L : Matrix (Fin B.rank) (Fin B.rank) (AE D))
    (a1 : ∀ x, L.mulVec (vecA B (ι x)) = 0) (a2 : ∀ l, L.mulVec (vecA B (d.f l)) = 0)
    (a3 : ∀ l, L.mulVec (vecA B (d.aux l)) = 0) (x) : L.mulVec x = 0 := by
  obtain ⟨t, e⟩ := (GlobalTheory.T.besselDatum_adelicVector_decomposition D A B ι d).2.2 x
  rw [e, iA_eq, Matrix.mulVec_add, Matrix.mulVec_add, mulVec_comb L _ (fun l => a1 (A.frame l)),
    mulVec_comb L _ a3, mulVec_comb L _ a2, add_zero, add_zero]

theorem eq_of_half {ε : AE D} {g k : GA D B} (g1 : SuppAt ε B g) (k1 : SuppAt ε B k)
    (h : ∀ x, ε • ((mt B g).mulVec x - x) = ε • ((mt B k).mulVec x - x)) : k = g := by
  refine inv_mul_eq_one.1 (eq_one_of_half (suppAt_mul (suppAt_inv k1) g1) fun x => ?_)
  have e : ε • (mt B g).mulVec x = ε • (mt B k).mulVec x := by
    have := h x
    rwa [smul_sub, smul_sub, sub_left_inj] at this
  have := congrArg (mt B k⁻¹).mulVec e
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, mulVec_inv_cancel, ← mulVec_mul] at this
  rw [smul_sub, this, sub_self]

set_option maxHeartbeats 800000 in
theorem exSet_sub (d : BesselDatum A B ι) {ε : AE D} (h1 : ε * ε = ε) (h0 : ε * cA D ε = 0) (i) {g : GA D B}
    (hg : g ∈ d.ExSet ε i) : g ∈ kGrp d h0 i := by
  obtain ⟨g1, g2, g3, g4, y, g5⟩ := hg
  have ht : ε • (-(ε • y)) = -(ε • y) := by rw [smul_neg, smul_smul, h1]
  obtain ⟨k, hk⟩ := exists_k d h0 i ht
  obtain ⟨k1, k2, k3, k4, k5⟩ := mem_exSet d h1 h0 i ht hk
  obtain ⟨L, hL⟩ : ∃ L : Matrix (Fin B.rank) (Fin B.rank) (AE D),
      ∀ x, L.mulVec x = ε • ((mt B g).mulVec x - x) - ε • ((mt B k).mulVec x - x) :=
    ⟨ε • (mt B g - mt B k), fun x => by
      rw [← smul_sub, sub_sub_sub_cancel_right, ← Matrix.sub_mulVec, ← Matrix.smul_mulVec]⟩
  have a1 : ∀ x, L.mulVec (vecA B (ι x)) = 0 := fun x => by
    rw [hL]; exact sub_eq_zero.2 ((g2 x).trans (k2 x).symm)
  have a2 : ∀ l, L.mulVec (vecA B (d.f l)) = 0 := fun l => by
    rw [hL]; exact sub_eq_zero.2 ((g3 l).trans (k3 l).symm)
  have a3 : ∀ l, L.mulVec (vecA B (d.aux l)) = 0 := fun l => by
    rw [hL]
    by_cases hl : l = i
    · subst hl
      refine sub_eq_zero.2 (g5.trans (Eq.symm (k5.trans ?_)))
      rw [iA_neg, neg_neg, iA_smul]; rfl
    · exact sub_eq_zero.2 ((g4 l hl).trans (k4 l hl).symm)
  have a4 : ∀ x, L.mulVec x = 0 := mulVec_zero_of d L a1 a2 a3
  rw [← eq_of_half g1 k1 fun x => sub_eq_zero.1 ((hL x).symm.trans (a4 x))]
  exact ⟨_, ht, hk⟩

theorem mem_Ex_iff : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ε : AE D), IsSplitIdem D ε → ∀ (i : Fin (d.ρ + 1)) (g : GA D B), g ∈ d.Ex ε i ↔ ∃ t, ε • t = t ∧ IsK B (vecA B (dual d i)) (iA ι t) g := by
  intro D A B ι d ε he i g
  have h1 : ε * ε = ε := he.1
  have h0 : ε * cA D ε = 0 := he.2.1
  refine ⟨fun hg => (Subgroup.closure_le (kGrp d h0 i)).2 (fun _ h => exSet_sub d h1 h0 i h) hg, ?_⟩
  rintro ⟨t, ht, hk⟩
  obtain ⟨k1, k2, k3, k4, k5⟩ := mem_exSet d h1 h0 i ht hk
  refine Subgroup.subset_closure ⟨k1, k2, k3, k4, -t, k5.trans ?_⟩
  show _ = ε • iA ι (-t)
  rw [← iA_smul, smul_neg, ht, iA_neg]

end GlobalTheory.RootExch.ExStruct

end
