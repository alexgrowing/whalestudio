import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppRedW
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRho

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppFrameW

attribute [local instance] Ideal.Quotient.field

open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf Formalism.L2.SG.Pf.unitaryCongruence
  Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.AllRowsRho

variable {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {p : ℕ} {m : ℕ}

theorem hhat_sum_right (u : Fin I.n → I.E ⊗[I.F] Af I.F) {ι : Type*} (s : Finset ι) (a : ι → I.E ⊗[I.F] Af I.F)
    (v : ι → Fin I.n → I.E ⊗[I.F] Af I.F) :
    hhat I u (∑ j ∈ s, a j • v j) = ∑ j ∈ s, a j * hhat I u (v j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DictLat.hhat_zero_right]
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, DictLat.hhat_add_right, DictLat.hhat_smul_right, ih]

theorem iv_sum_int (b : Fin m → Fin I.n → I.E) (c : Fin m → ℤ) :
    iv I (∑ j, ((c j : ℤ) : I.E) • b j) = ∑ j, ((c j : ℤ) : I.E ⊗[I.F] Af I.F) • iv I (b j) := by
  funext k
  simp [iv, Finset.sum_apply, map_sum]

def GramW (w : HeightOneSpectrum (𝓞 I.E)) {r : ℕ} (fr frd : Fin r → Fin I.n → I.E ⊗[I.F] Af I.F) : Prop :=
  ∀ i j, hhat I (frd i) (fr j) - (if i = j then 1 else 0) ∈ Wq I w

theorem exists_lifts (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {r : ℕ}
    {fr : Fin r → Fin I.n → I.E ⊗[I.F] Af I.F} (hfr : ∀ j, fr j ∈ I.Lf) :
    ∃ c : Fin r → Fin I.n → I.E, ∀ j, c j ∈ I.L ∧ fr j - iv I (c j) ∈ Lq I w := by
  choose c hcL hc using fun j => dense I w hp hcard (hfr j)
  exact ⟨c, fun j => ⟨hcL j, hc j⟩⟩

theorem gram_lift {r : ℕ} {fr frd : Fin r → Fin I.n → I.E ⊗[I.F] Af I.F} (hfrd : ∀ i, frd i ∈ I.Lf)
    (hg : GramW w fr frd) {c : Fin r → Fin I.n → I.E} (hc : ∀ j, fr j - iv I (c j) ∈ Lq I w) :
    GramW w (fun j => iv I (c j)) frd := fun i j => by
  have := sub_mem (hg i j) (hhat_Lq_right (hfrd i) (hc j))
  convert this using 1
  rw [hhat_sub_right]
  ring

theorem isRedBasis_of_gram (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) (hm : m = I.n)
    {frd : Fin m → Fin I.n → I.E ⊗[I.F] Af I.F} (hfrd : ∀ i, frd i ∈ I.Lf) {c : Fin m → Fin I.n → I.E}
    (hcL : ∀ j, c j ∈ I.L) (hg : GramW w (fun j => iv I (c j)) frd) : IsRedBasis0 I w c := by
  subst hm
  refine ⟨hcL, ?_⟩
  let b' : Fin I.n → I.L := fun j => ⟨c j, hcL j⟩
  let f := Submodule.mkQ (w.asIdeal • (⊤ : Submodule (𝓞 I.E) I.L))
  have hli : LinearIndependent (𝓞 I.E ⧸ w.asIdeal) (f ∘ b') := by
    rw [Fintype.linearIndependent_iff]
    intro g hg0 i
    have hn : 0 < I.n := Fin.pos i
    choose α hα using fun j => Ideal.Quotient.mk_surjective (g j)
    have h0 : (∑ j, α j • b' j : I.L) ∈ w.asIdeal • (⊤ : Submodule (𝓞 I.E) I.L) := by
      rw [← Submodule.Quotient.mk_eq_zero, mk_sum' I w, ← hg0]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hα j]
      exact (Module.Quotient.mk_smul_mk _ _ _ _).symm
    rw [← mem_iff] at h0
    have h1 : iv I (∑ j, ((α j : 𝓞 I.E) : I.E) • c j) ∈ Lq I w := by
      refine iv_mem_w I w ?_
      convert h0 using 1
      simp [b']
    have hiv : iv I (∑ j, ((α j : 𝓞 I.E) : I.E) • c j) = ∑ j, iE I (α j) • iv I (c j) := by
      funext k
      simp only [iv, iE, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
    have h2 := hhat_Lq_right (hfrd i) h1
    rw [hiv, hhat_sum_right] at h2
    have h3 : ∑ j, iE I (α j) * (hhat I (frd i) (iv I (c j)) - (if i = j then 1 else 0)) ∈ Wq I w :=
      sum_mem fun j _ => Wq_mul (hg i j) (iE_int I (α j))
    have h4 := sub_mem h2 h3
    have e : ∑ j, iE I (α j) * hhat I (frd i) (iv I (c j)) -
        ∑ j, iE I (α j) * (hhat I (frd i) (iv I (c j)) - (if i = j then 1 else 0)) = iE I (α i) := by
      rw [← Finset.sum_sub_distrib]
      simp only [mul_sub, sub_sub_cancel, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq]
      simp
    rw [e] at h4
    have h5 : α i ∈ w.asIdeal := int_of_Wq hp hcard hn h4
    rw [← hα i]
    exact Ideal.Quotient.eq_zero_iff_mem.2 h5
  intro y hy
  by_cases hn : I.n = 0
  · refine ⟨fun _ => 0, ?_⟩
    have : y = 0 := by
      funext k
      exact absurd k.2 (by omega)
    rw [this]
    simp
  have : Nonempty (Fin I.n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  have hcE : Fintype.card (Fin I.n) = Module.finrank (𝓞 I.E ⧸ w.asIdeal) (RedQ I w) := by
    rw [Fintype.card_fin, finrank_eq I w]
  have hspan := hli.span_eq_top_of_card_eq_finrank hcE
  have hmem : f ⟨y, hy⟩ ∈ Submodule.span (𝓞 I.E ⧸ w.asIdeal) (Set.range (f ∘ b')) := by
    rw [hspan]; trivial
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hmem
  choose k hk using fun j => int_surj I w hp hcard (a j)
  refine ⟨k, ?_⟩
  have h1 : ((⟨y, hy⟩ : I.L) - ∑ j, k j • b' j) ∈ (w.asIdeal • (⊤ : Submodule (𝓞 I.E) I.L)) := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero, mk_sum' I w]
    change f ⟨y, hy⟩ = _
    rw [← ha]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hk j, Submodule.Quotient.mk_smul, Int.cast_smul_eq_zsmul]
    rfl
  rw [← mem_iff] at h1
  convert h1 using 1
  simp [b', Int.cast_smul_eq_zsmul]

def RepV (w : HeightOneSpectrum (𝓞 I.E)) (p : ℕ) {r : ℕ} (u : Fin r → Fin I.n → I.E ⊗[I.F] Af I.F)
    (v : Fin I.n → I.E ⊗[I.F] Af I.F) (a : Fin r → ZMod p) : Prop :=
  v - ∑ j, (((a j).val : ℕ) : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w

theorem coef [NeZero p] {r : ℕ} {frd u : Fin r → Fin I.n → I.E ⊗[I.F] Af I.F} (hfrd : ∀ i, frd i ∈ I.Lf)
    (hu : ∀ j, u j ∈ I.Lf) (hg : GramW w u frd) {v : Fin I.n → I.E ⊗[I.F] Af I.F} {a : Fin r → ZMod p}
    (hv : RepV w p u v a) (i : Fin r) : CongW (w := w) p (hhat I (frd i) v) (a i) := by
  have h1 : hhat I (frd i) v - hhat I (frd i) (∑ j, (((a j).val : ℕ) : I.E ⊗[I.F] Af I.F) • u j) ∈ Wq I w := by
    rw [← hhat_sub_right]; exact hhat_Lq_right (hfrd i) hv
  refine congW_of_sub ?_ h1
  rw [hhat_sum_right]
  have h2 : CongW (w := w) p (∑ j, (((a j).val : ℕ) : I.E ⊗[I.F] Af I.F) * hhat I (frd i) (u j))
      (∑ j, a j * (if i = j then 1 else 0)) := by
    refine congW_sum _ fun j _ => ?_
    refine congW_mul (dual_hat_integral I _ (hfrd i) _ (hu j)) ?_ ?_
    · have := congW_natCast (I := I) (w := w) (p := p) (a j).val
      rwa [ZMod.natCast_zmod_val] at this
    · refine congW_of_sub (t := ((if i = j then 1 else 0 : ℤ) : I.E ⊗[I.F] Af I.F)) ?_ ?_
      · have := congW_intCast (I := I) (w := w) (p := p) (if i = j then 1 else 0)
        convert this using 2
        split_ifs <;> simp
      · convert hg i j using 2
        split_ifs <;> simp
  simpa [mul_ite, Finset.sum_ite_eq] using h2

theorem natSmul_Lq' (k : ℕ) {z : Fin I.n → I.E ⊗[I.F] Af I.F} (hz : z ∈ Lq I w) :
    (k : I.E ⊗[I.F] Af I.F) • z ∈ Lq I w := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hz k

theorem rep_unique (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) (hm : m = I.n)
    {b : Fin m → Fin I.n → I.E} (hb : IsRedBasis0 I w b) {v : Fin I.n → I.E ⊗[I.F] Af I.F}
    {a a' : Fin m → ZMod p} (h : RepV w p (fun j => iv I (b j)) v a) (h' : RepV w p (fun j => iv I (b j)) v a') :
    a = a' := by
  subst hm
  have : NeZero p := ⟨hp.ne_zero⟩
  have h1 : iv I (∑ j, ((((a' j).val : ℤ) - (a j).val : ℤ) : I.E) • b j) ∈ Lq I w := by
    rw [iv_sum_int]
    have := sub_mem h h'
    convert this using 1
    simp only [Int.cast_sub, Int.cast_natCast, sub_smul, Finset.sum_sub_distrib]
    abel
  have h2 := redBasis_indep I w hp hcard hb _ (inter I w h1)
  funext j
  have h3 := h2 j
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub] at h3
  simpa using h3

theorem rep_exists (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {b : Fin m → Fin I.n → I.E}
    (hb : IsRedBasis0 I w b) {v : Fin I.n → I.E ⊗[I.F] Af I.F} (hv : v ∈ I.Lf) :
    ∃ a, RepV w p (fun j => iv I (b j)) v a := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨c, hc⟩ := coords I w hp hcard hb hv
  refine ⟨fun j => (c j : ZMod p), ?_⟩
  have h2 : ∑ j, (c j : I.E ⊗[I.F] Af I.F) • iv I (b j) -
      ∑ j, ((((c j : ℤ) : ZMod p).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lq I w := by
    rw [← Finset.sum_sub_distrib]
    refine sum_mem fun j _ => ?_
    have := neg_mem (val_sub I w hp hcard (hb.1 j) (c j))
    rwa [neg_sub] at this
  have := add_mem hc h2
  show v - _ ∈ _
  convert this using 1
  abel

theorem rep_comp (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {r : ℕ}
    {b : Fin m → Fin I.n → I.E} (hb : ∀ k, b k ∈ I.L) {u : Fin r → Fin I.n → I.E ⊗[I.F] Af I.F}
    {v : Fin I.n → I.E ⊗[I.F] Af I.F} {A : Fin r → ZMod p} (hA : RepV w p u v A)
    {P : Matrix (Fin m) (Fin r) (ZMod p)} (hP : ∀ j, RepV w p (fun k => iv I (b k)) (u j) (fun k => P k j)) :
    RepV w p (fun k => iv I (b k)) v (P *ᵥ A) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have s2 : ∑ j, (((A j).val : ℕ) : I.E ⊗[I.F] Af I.F) • u j -
      ∑ j, (((A j).val : ℕ) : I.E ⊗[I.F] Af I.F) •
        ∑ k, (((P k j).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b k) ∈ Lq I w := by
    rw [← Finset.sum_sub_distrib]
    refine sum_mem fun j _ => ?_
    rw [← smul_sub]
    exact natSmul_Lq' _ (hP j)
  have e3 : ∑ j, (((A j).val : ℕ) : I.E ⊗[I.F] Af I.F) •
        ∑ k, (((P k j).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b k) =
      ∑ k, (((∑ j, (P k j).val * (A j).val : ℕ) : ℤ) : I.E ⊗[I.F] Af I.F) • iv I (b k) := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Int.cast_natCast, Nat.cast_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.cast_mul, mul_comm]
  have s3 : ∑ k, (((∑ j, (P k j).val * (A j).val : ℕ) : ℤ) : I.E ⊗[I.F] Af I.F) • iv I (b k) -
      ∑ k, ((((P *ᵥ A) k).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b k) ∈ Lq I w := by
    rw [← Finset.sum_sub_distrib]
    refine sum_mem fun k _ => ?_
    have hc : (((∑ j, (P k j).val * (A j).val : ℕ) : ℤ) : ZMod p) = (P *ᵥ A) k := by
      rw [Int.cast_natCast, Nat.cast_sum, Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have := val_sub I w hp hcard (hb k) ((∑ j, (P k j).val * (A j).val : ℕ) : ℤ)
    rw [hc] at this
    have := neg_mem this
    rwa [neg_sub] at this
  rw [e3] at s2
  have := add_mem (add_mem hA s2) s3
  show v - _ ∈ _
  convert this using 1
  abel

theorem rep_mulVec {x : I.Gf} (hx : x ∈ I.Kset) {r : ℕ} {u : Fin r → Fin I.n → I.E ⊗[I.F] Af I.F}
    {v : Fin I.n → I.E ⊗[I.F] Af I.F} {a : Fin r → ZMod p} (h : RepV w p u v a) :
    RepV w p (fun j => I.fmat x *ᵥ u j) (I.fmat x *ᵥ v) a := by
  unfold RepV at h ⊢
  have := stab_w I w hx h
  rw [Matrix.mulVec_sub, Matrix.mulVec_sum] at this
  simpa only [Matrix.mulVec_smul] using this

theorem rep_self [NeZero p] (hp : p.Prime) {r : ℕ} (u : Fin r → Fin I.n → I.E ⊗[I.F] Af I.F) (j : Fin r) :
    RepV w p u (u j) (fun i => (1 : Matrix (Fin r) (Fin r) (ZMod p)) i j) := by
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have e : ∑ i, ((((1 : Matrix (Fin r) (Fin r) (ZMod p)) i j).val : ℕ) : I.E ⊗[I.F] Af I.F) • u i = u j := by
    rw [Finset.sum_eq_single j]
    · simp only [Matrix.one_apply_eq, ZMod.val_one, Nat.cast_one, one_smul]
    · intro i _ hi; simp [Matrix.one_apply_ne hi]
    · simp
  show u j - _ ∈ _
  rw [e, sub_self]
  exact zero_mem _

theorem redMatB_rep {b : Fin m → Fin I.n → I.E} {x : I.Gf} {M : Matrix (Fin m) (Fin m) (ZMod p)}
    (h : RedMatB I w p b x M) (i : Fin m) :
    RepV w p (fun j => iv I (b j)) (I.fmat x *ᵥ iv I (b i)) (fun j => M j i) := h i

theorem conj_basis (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) (hm : m = I.n)
    {b c : Fin m → Fin I.n → I.E} (hb : IsRedBasis0 I w b) (hc : IsRedBasis0 I w c) :
    ∃ P Q : Matrix (Fin m) (Fin m) (ZMod p), P * Q = 1 ∧ Q * P = 1 ∧
      ∀ x ∈ I.Kset, ∀ M N : Matrix (Fin m) (Fin m) (ZMod p), RedMatB I w p b x M → RedMatB I w p c x N →
        M * P = P * N := by
  have : NeZero p := ⟨hp.ne_zero⟩
  choose Pc hPc using fun j => rep_exists hp hcard hb (DictLat.iv_mem I (hc.1 j))
  choose Qc hQc using fun j => rep_exists hp hcard hc (DictLat.iv_mem I (hb.1 j))
  let P : Matrix (Fin m) (Fin m) (ZMod p) := Matrix.of fun k j => Pc j k
  let Q : Matrix (Fin m) (Fin m) (ZMod p) := Matrix.of fun k j => Qc j k
  have hP : ∀ j, RepV w p (fun k => iv I (b k)) (iv I (c j)) (fun k => P k j) := hPc
  have hQ : ∀ j, RepV w p (fun k => iv I (c k)) (iv I (b j)) (fun k => Q k j) := hQc
  have hPQ : P * Q = 1 := by
    ext i j
    have h1 := rep_comp hp hcard hb.1 (hQ j) hP
    have h2 := rep_self (w := w) hp (fun k => iv I (b k)) j
    have := rep_unique hp hcard hm hb h1 h2
    have := congrFun this i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  refine ⟨P, Q, hPQ, (Matrix.mul_eq_one_comm_of_card_eq (Fin m) (Fin m) _ rfl).mp hPQ, ?_⟩
  intro x hx M N hM hN
  ext i j
  have h1 := rep_comp hp hcard hb.1 (redMatB_rep hN j) hP
  have h2 := rep_comp hp hcard hb.1 (rep_mulVec hx (hP j)) (fun k => redMatB_rep hM k)
  have := rep_unique hp hcard hm hb h2 h1
  have := congrFun this i
  simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this

theorem entry [NeZero p] {fr frd : Fin m → Fin I.n → I.E ⊗[I.F] Af I.F} (hfrd : ∀ i, frd i ∈ I.Lf)
    {c : Fin m → Fin I.n → I.E} (hcL : ∀ j, c j ∈ I.L) (hc : ∀ j, fr j - iv I (c j) ∈ Lq I w)
    (hg : GramW w (fun j => iv I (c j)) frd) {x : I.Gf} (hx : x ∈ I.Kset) {N : Matrix (Fin m) (Fin m) (ZMod p)}
    (hN : RedMatB I w p c x N) (i j : Fin m) :
    CongW (w := w) p (hhat I (frd i) (I.fmat x *ᵥ fr j)) (N i j) := by
  have h1 := coef hfrd (fun k => DictLat.iv_mem I (hcL k)) hg (redMatB_rep hN j) i
  refine congW_of_sub h1 ?_
  rw [← hhat_sub_right, ← Matrix.mulVec_sub]
  exact hhat_Lq_right (hfrd i) (stab_w I w hx (hc j))

end Formalism.L2.SG.Pf.KppFrameW
