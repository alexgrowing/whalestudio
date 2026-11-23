import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.KStableHighestWeightVector
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.StripDataTensorColumnFamilies

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

lemma qr_prim {n : ℕ} [NeZero n] {M : GLMod n} {mu : Fin n → ℤ} {β : M.ι → GLCoord ℤ n}
    (hS : SBasis) (hmu : Dominant mu) (hβ : IsSMu M mu β)
    (ph : Matrix M.ι (TIdx mu) ℤ) (hph : ∀ I, ∑ i, ph i I • β i = brk mu I) (I0 : TIdx mu) (hI0 : StdT I0) (d : ℤ)
    (hd : ∀ i, d ∣ ph i I0) : d ∣ 1 := by
  classical
  have : Fintype {I : TIdx mu // StdT I} := Fintype.ofFinite _
  choose q hq using hd
  have hy : ∑ i, q i • β i ∈ Submodule.span ℤ (Set.range fun I : {I : TIdx mu // StdT I} => brk mu I.1) := by
    rw [(hS n mu hmu).2, ← hβ.2.1]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy
  have hcan : brk mu I0 = d • ∑ i, q i • β i := by
    rw [← hph]
    simp only [zsmul_eq_mul, Finset.mul_sum, hq, Int.cast_mul, mul_assoc]
  let c0 : {I : TIdx mu // StdT I} := ⟨I0, hI0⟩
  have h0 : ∑ I : {I : TIdx mu // StdT I}, ((if I = c0 then 1 else 0) - d * r I) • brk mu I.1 = 0 := by
    have h2 : ∀ I : {I : TIdx mu // StdT I}, ((if I = c0 then 1 else 0) - d * r I) • brk mu I.1 =
        (if I = c0 then brk mu I.1 else 0) - (d : GLCoord ℤ n) * (r I • brk mu I.1) := by
      intro I
      split_ifs <;> simp [zsmul_eq_mul, sub_mul, mul_assoc]
    simp only [h2, Finset.sum_sub_distrib, ← Finset.mul_sum, hr, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [sub_eq_zero, ← zsmul_eq_mul]
    exact hcan
  have h1 := Fintype.linearIndependent_iff.1 (hS n mu hmu).1 _ h0 c0
  simp only [if_true] at h1
  exact ⟨r c0, by linarith⟩

lemma qr_equiv {m : ℕ} [NeZero m] {M : GLMod (m + 1)} {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ}
    (hl : Dominant lam) (hn : Dominant nu) (hi : Interl lam nu)
    (ph : Matrix M.ι (TIdx lam) ℤ)
    (hE : (M.A * ph.map (Int.castRingHom (GLCoord ℤ (m + 1))) : Matrix _ _ _) =
      (ph.map (Int.castRingHom (GLCoord ℤ (m + 1))) * TMat lam : Matrix _ _ _))
    {R : Type} [CommRing R] {h : GL (Fin (m + 1)) R} {g1 : GL (Fin m) R} {t : Rˣ} (hb : IsBlock h g1 t)
    (i : M.ι) (I' : TIdx nu) :
    ∑ k, evGL h (M.A i k) * ((ph k (qr_j hi I') : ℤ) : R) =
      ((t ^ (∑ a, lam a - ∑ a, nu a) : Rˣ) : R) *
        ∑ K' : TIdx nu, ((ph i (qr_j hi K') : ℤ) : R) * evGL g1 (TMat nu K' I') := by
  have h1 := congrArg (evGL h) (congrFun (congrFun hE i) (qr_j hi I'))
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, eq_intCast, map_intCast] at h1
  rw [h1, Finset.mul_sum]
  symm
  apply Finset.sum_of_injOn (qr_j hi) (qr_j_inj hi).injOn (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  · intro K _ hK
    rw [qr_TMat_zero hb hn hi K I' (fun K' hK' => hK ⟨K', Finset.mem_coe.2 (Finset.mem_univ _), hK'⟩), mul_zero]
  · intro K' _
    rw [qr_TMat_j hb hl hn hi]
    ring

theorem closure_third_part_of (hA : LemmaA) (hS : SBasis) (hC : CntBranch) : ClosureBranching := by
  classical
  intro m _ M lam β hl hβ
  let Sg : Finset (Fin m → ℤ) :=
    (Fintype.piFinset fun a : Fin m => Finset.Icc (lam a.succ) (lam a.castSucc)).filter fun nu =>
      Dominant nu ∧ Interl lam nu
  have hSg : ∀ nu : Fin m → ℤ, nu ∈ Sg ↔ Dominant nu ∧ Interl lam nu := by
    intro nu
    simp only [Sg, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc, and_iff_right_iff_imp]
    rintro ⟨_, hi⟩ a
    exact ⟨(hi a).2, (hi a).1⟩
  have hex : ∀ I : TIdx lam, ∃ c : M.ι → ℤ, ∑ i, c i • β i = brk lam I := fun I =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).1 (by rw [hβ.2.1]; exact Submodule.subset_span ⟨I, rfl⟩)
  choose c hc using hex
  let ph : Matrix M.ι (TIdx lam) ℤ := fun i I => c I i
  have hph : ∀ I, ∑ i, ph i I • β i = brk lam I := hc
  have hE := qc_equiv hA hS hl hβ ph hph
  refine ⟨Sg, fun nu i I' => ph i (qr_j ((hSg nu.1).1 nu.2).2 I'), hSg, ?_, ?_, ?_⟩
  · intro nu R _ h g1 t hb
    ext i I'
    exact qr_equiv hl ((hSg nu.1).1 nu.2).1 ((hSg nu.1).1 nu.2).2 ph hE hb i I'
  · intro nu
    have hpr := qr_prim hS hl hβ ph hph _ (qr_j_can_std (lam := lam) ((hSg nu.1).1 nu.2).2)
    constructor
    · intro p hp h0
      have h1 := hpr (p : ℤ) fun i => (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (congrFun h0 i)
      have h2 : p ∣ 1 := by exact_mod_cast h1
      exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
    · intro h0
      have h1 := hpr 0 fun i => by
        have := congrFun h0 i
        simp only [Pi.zero_apply, Int.cast_eq_zero] at this
        rw [this]
      simp at h1
  · rw [qc_card_eq hS hl hβ, hC m lam hl Sg hSg, Finset.sum_coe_sort Sg (fun nu => dMu nu)]

end Formalism.InvariantFactorPaths.ColumnFamilies
