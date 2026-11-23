import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepBS

noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.IndefR.DatumF GlobalTheory.FinLatF GlobalTheory.FinWeil

namespace PositivityTheory.ThKW.LatB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {nS nT : ℕ} {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)}

theorem fin_smul_self (u : XFF F E nS nT) :
    algebraMap (AF F) (AEF F E) (pairA F 0 1) • (u : WOF F E nS nT) = u := by
  have h0 : pairA F 1 0 • (u : WOF F E nS nT) = 0 := GlobalTheory.HeisThetaF.smul_eq_zero_of_map_infPartF (XFF.fin u)
  have h := PositivityTheory.ThKW.LatA.dec (u : WOF F E nS nT)
  rw [h0, zero_add] at h
  rw [algebraMap_smul]
  exact h.symm

theorem int_smul_mem {a : AEF F E} (ha : finPartF F E a ∈ hatO (F := F) E) {u : XFF F E nS nT}
    (hu : u ∈ (latF F E nS nT Λ).toAddSubgroup) : a • u ∈ (latF F E nS nT Λ).toAddSubgroup := by
  show ((a • u : XFF F E nS nT) : WOF F E nS nT) ∈ latOF F E nS nT Λ
  rw [XFF.coe_asmul, ← fin_smul_self u, smul_smul, mul_comm, fin_mul_eq]
  exact liftF_smul_mem ha hu

theorem int_smul_mem_map {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
    (p : GAF σ JS × GAF σ JT) {a : AEF F E} (ha : finPartF F E a ∈ hatO (F := F) E) {u : XFF F E nS nT}
    (hu : u ∈ ((latF F E nS nT Λ).map (rhoFF σ JS JT p)).toAddSubgroup) :
    a • u ∈ ((latF F E nS nT Λ).map (rhoFF σ JS JT p)).toAddSubgroup := by
  obtain ⟨y, hy, rfl⟩ := hu
  refine ⟨a • y, int_smul_mem ha hy, XFF.ext ?_⟩
  rw [coe_rhoFF, XFF.coe_asmul, XFF.coe_asmul, coe_rhoFF, actOF_smul]

theorem mul_e_zero {a e : AEF F E} (ha : finPartF F E a = 0)
    (hf : algebraMap (AF F) (AEF F E) (pairA F 0 1) * e = e) : a * e = 0 := by
  rw [← hf, ← mul_assoc, mul_comm a, fin_mul_eq, ha, map_zero, zero_mul]

theorem finPart_cAF_zero {a : AEF F E} (ha : finPartF F E a = 0) : finPartF F E (cAF σ a) = 0 := by
  have hr : infPartF F E (algebraMap (AF F) (AEF F E) (pairA F 1 0)) = 1 := rfl
  have hf : finPartF F E (algebraMap (AF F) (AEF F E) (pairA F 1 0)) = 0 := TensorProduct.zero_tmul _ _
  have e : a = algebraMap (AF F) (AEF F E) (pairA F 1 0) * a := by
    rw [← sub_eq_zero]
    refine GlobalTheory.SplitDetCharF.adele_tensor_ext _ ?_ ?_
    · rw [map_sub, map_mul, hr, one_mul, sub_self]
    · rw [map_sub, map_mul, hf, ha, zero_mul, sub_self]
  rw [e, map_mul, GlobalTheory.HeisThetaF.cAF_algebraMap, map_mul, hf, zero_mul]

theorem approx {k : ℕ} (hk : 0 < k) {z : Af F ⊗[F] E} (hz : z ∈ hatO (F := F) E) :
    ∃ (r : 𝓞 E) (s : AEF F E), finPartF F E s ∈ hatO (F := F) E ∧ finPartF F E (cAF σ s) ∈ hatO (F := F) E ∧
      z = finPartF F E (incAF F E (r : E) + k • s) := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, _, ⟨t, rfl⟩, rfl⟩ := hw
    obtain ⟨x, β, hβ, hx⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F k hk).2 α hα
    refine ⟨algebraMap (𝓞 F) (𝓞 E) x * t, pairA F 0 β ⊗ₜ[F] (t : E),
      AddSubgroup.subset_closure ⟨β, hβ, _, ⟨t, rfl⟩, rfl⟩,
      AddSubgroup.subset_closure ⟨β, hβ, _, ⟨sgOF σ t, rfl⟩, rfl⟩, ?_⟩
    rw [hx, map_add, map_nsmul]
    exact GlobalTheory.SplitIndex.tmul_split β (x : F) k (t : E)
  | zero => exact ⟨0, 0, by rw [map_zero]; exact zero_mem _,
      by rw [map_zero, map_zero]; exact zero_mem _, by simp⟩
  | add x x' _ _ h h' =>
    obtain ⟨r, s, h1, h2, rfl⟩ := h
    obtain ⟨r', s', h1', h2', rfl⟩ := h'
    refine ⟨r + r', s + s', by rw [map_add]; exact add_mem h1 h1',
      by rw [map_add, map_add]; exact add_mem h2 h2', ?_⟩
    rw [← map_add]
    congr 1
    push_cast
    rw [map_add, smul_add]
    abel
  | neg x _ h =>
    obtain ⟨r, s, h1, h2, rfl⟩ := h
    refine ⟨-r, -s, by rw [map_neg]; exact neg_mem h1,
      by rw [map_neg, map_neg]; exact neg_mem h2, ?_⟩
    rw [← map_neg]
    congr 1
    push_cast
    rw [map_neg, smul_neg, neg_add]

theorem split_mem (h : IsCMExt F E σ) {e : AEF F E} (hee : e * e = e)
    (hf : algebraMap (AF F) (AEF F E) (pairA F 0 1) * e = e) (hec : e * cAF σ e = 0) {q : ℕ} (hq : q.Prime)
    (hin : InertQF σ q) {x : XFF F E nS nT} (hx : q • x ∈ (latF F E nS nT Λ).toAddSubgroup) :
    e • x ∈ (latF F E nS nT Λ).toAddSubgroup := by
  have heI : finPartF F E e ∈ hatO (F := F) E :=
    GlobalTheory.AdIdem.mem_hat_of_idempotent F E _ (by rw [← map_mul, hee])
  obtain ⟨r, s, hs, hs', hz⟩ := approx (σ := σ) hq.pos heI
  have h0 : finPartF F E (e - (incAF F E (r : E) + q • s)) = 0 := by rw [map_sub, ← hz, sub_self]
  have h0' := finPart_cAF_zero (σ := σ) h0
  rw [map_sub, map_add, map_nsmul, GlobalTheory.HeisLineF.cAF_incAF, ← coe_sgOF] at h0'
  refine GlobalTheory.SplitIndex.core_split ((incAF F E).comp (algebraMap (𝓞 E) E)) _
    (fun a => finPartF F E a ∈ hatO (F := F) E) (fun a ha u hu => int_smul_mem ha hu)
    (fun r => AddSubgroup.subset_closure ⟨1, fun v => GlobalTheory.AdLat.adele_one_integral F v, _, ⟨r, rfl⟩, rfl⟩)
    q x hx e (cAF σ e) s (cAF σ s) heI hs hs' hee hec r (sgOF σ r) (mul_e_zero h0 hf) (mul_e_zero h0' hf) ?_
  intro P hP hqP hr
  have := hin P hP hqP _ hr
  rwa [show sgOF σ (sgOF σ r) = r from RingOfIntegers.ext (sg_sg h _)] at this

theorem mtF_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (a b : GAF σ J) : mtF σ J (a * b) = mtF σ J a * mtF σ J b := by
  simp only [mtF, map_mul, Units.val_mul]

theorem mtF_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mtF σ J 1 = 1 := by
  simp only [mtF, map_one, Units.val_one]

theorem supp_smul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {e : AEF F E} {g : GAF σ J} (hg : SuppAtF σ e J g) :
    (1 - (e + cAF σ e)) • mtF σ J g = (1 - (e + cAF σ e)) • (1 : Matrix (Fin n) (Fin n) (AEF F E)) := by
  ext i j
  have := hg i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
  linear_combination -this

theorem supp_smul_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {e : AEF F E} {g : GAF σ J} (hg : SuppAtF σ e J g) :
    (1 - (e + cAF σ e)) • mtF σ J g⁻¹ = (1 - (e + cAF σ e)) • (1 : Matrix (Fin n) (Fin n) (AEF F E)) := by
  calc (1 - (e + cAF σ e)) • mtF σ J g⁻¹ = ((1 - (e + cAF σ e)) • (1 : Matrix (Fin n) (Fin n) (AEF F E))) * mtF σ J g⁻¹ := by
        rw [Matrix.smul_mul, Matrix.one_mul]
    _ = ((1 - (e + cAF σ e)) • mtF σ J g) * mtF σ J g⁻¹ := by rw [supp_smul hg]
    _ = _ := by rw [Matrix.smul_mul, ← mtF_mul, mul_inv_cancel, mtF_one]

theorem act_supp {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {e : AEF F E}
    {g : GAF σ JS} {k : GAF σ JT} (hg : SuppAtF σ e JS g) (hk : SuppAtF σ e JT k) (y : WOF F E nS nT) :
    (1 - (e + cAF σ e)) • actOF σ JS JT g k y = (1 - (e + cAF σ e)) • y := by
  unfold actOF
  calc (1 - (e + cAF σ e)) • (mtF σ JT k * y * mtF σ JS g⁻¹)
      = ((1 - (e + cAF σ e)) • mtF σ JT k) * y * mtF σ JS g⁻¹ := by rw [Matrix.smul_mul, Matrix.smul_mul]
    _ = ((1 - (e + cAF σ e)) • (1 : Matrix (Fin nT) (Fin nT) (AEF F E))) * y * mtF σ JS g⁻¹ := by rw [supp_smul hk]
    _ = y * ((1 - (e + cAF σ e)) • mtF σ JS g⁻¹) := by
        rw [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul]
    _ = y * ((1 - (e + cAF σ e)) • (1 : Matrix (Fin nS) (Fin nS) (AEF F E))) := by rw [supp_smul_inv hg]
    _ = _ := by rw [Matrix.mul_smul, Matrix.mul_one]

theorem idx_main (h : IsCMExt F E σ) {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
    (hfin : ∀ p, idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) ≠ 0) :
    ∀ e, IsSplitIdemF σ e → ∀ g k, SuppAtF σ e JS g → SuppAtF σ e JT k → ∀ q : ℕ, q.Prime → InertQF σ q →
    ¬ q ∣ idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, k))) := by
  intro e he g k hg hk q hq hin
  obtain ⟨hf, hfc, hcc⟩ := split_parts he
  have hc2 : cAF σ (cAF σ e) = e := GlobalTheory.HeisLineF.cAF_cAF σ (sg_sg h) e
  have hec : e * cAF σ e = 0 := he.2.1
  have heI : finPartF F E e ∈ hatO (F := F) E :=
    GlobalTheory.AdIdem.mem_hat_of_idempotent F E _ (by rw [← map_mul, he.1])
  have hcI : finPartF F E (cAF σ e) ∈ hatO (F := F) E :=
    GlobalTheory.AdIdem.mem_hat_of_idempotent F E _ (by rw [← map_mul, hcc])
  have hcI' : finPartF F E (1 - (e + cAF σ e)) ∈ hatO (F := F) E := by
    rw [map_sub, map_add, map_one]
    exact sub_mem (GlobalTheory.AdLat.one_tmul_mem_adelicCompletionOfElementSet F ⟨1, map_one _⟩) (add_mem heI hcI)
  refine GlobalTheory.SplitIndex.not_dvd_of_saturated _ _ (hfin (g, k)) hq fun x hx hqx => ?_
  refine GlobalTheory.SplitIndex.mem_of_parts _ e (cAF σ e) x (split_mem h he.1 hf hec hq hin hqx)
    (split_mem h hcc hfc (by rw [hc2, mul_comm, hec]) hq hin hqx) ?_
  obtain ⟨y, hy, rfl⟩ := hx
  have e1 : (1 - (e + cAF σ e)) • rhoFF σ JS JT (g, k) y = (1 - (e + cAF σ e)) • y :=
    XFF.ext (by rw [XFF.coe_asmul, XFF.coe_asmul, coe_rhoFF]; exact act_supp hg hk _)
  rw [e1]
  exact int_smul_mem hcI' hy

end PositivityTheory.ThKW.LatB

end
