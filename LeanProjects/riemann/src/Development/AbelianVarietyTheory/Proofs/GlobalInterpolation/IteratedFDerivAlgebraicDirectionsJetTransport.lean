import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

noncomputable section

namespace GlobalTheory.JetTransport

section Formal

variable {σ : Type} [Fintype σ] [DecidableEq σ] {p : ℕ} [Fact p.Prime]

def factP (n : σ →₀ ℕ) : ℂ_[p] := ∏ i, ((n i).factorial : ℂ_[p])

theorem multiIndexFactorial_zero : (factP (0 : σ →₀ ℕ) : ℂ_[p]) = 1 := by simp [factP]

theorem multiIndexFactorial_add_single (n : σ →₀ ℕ) (k : σ) :
    (factP (n + Finsupp.single k 1) : ℂ_[p]) = factP n * ((n k : ℂ_[p]) + 1) := by
  unfold factP
  have h : ∀ i, (((n + Finsupp.single k 1 : σ →₀ ℕ) i).factorial : ℂ_[p]) =
      ((n i).factorial : ℂ_[p]) * (if i = k then (n k : ℂ_[p]) + 1 else 1) := by
    intro i
    by_cases hi : i = k
    · subst hi
      rw [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ, if_pos rfl]
      push_cast; ring
    · rw [Finsupp.add_apply, if_neg hi]
      simp [Finsupp.single_apply, Ne.symm hi]
  rw [Finset.prod_congr rfl fun i _ => h i, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k]
  simp

theorem coeff_pd (k : σ) (F : MvPowerSeries σ ℂ_[p]) (n : σ →₀ ℕ) :
    MvPowerSeries.coeff n (pd k F) = ((n k : ℂ_[p]) + 1) * MvPowerSeries.coeff (n + Finsupp.single k 1) F := rfl

def cntL (l : List σ) : σ →₀ ℕ := (l.map fun k => Finsupp.single k 1).sum

theorem coeff_foldr_pd (F : MvPowerSeries σ ℂ_[p]) : ∀ (l : List σ) (n : σ →₀ ℕ),
    factP n * MvPowerSeries.coeff n (l.foldr (fun k G => pd k G) F) =
      factP (n + cntL l) * MvPowerSeries.coeff (n + cntL l) F
  | [], n => by simp [cntL]
  | k :: l, n => by
    have hc : cntL (k :: l) = Finsupp.single k 1 + cntL l := by simp [cntL]
    rw [List.foldr_cons, coeff_pd, ← mul_assoc, ← multiIndexFactorial_add_single, coeff_foldr_pd F l, hc, add_assoc]

theorem pd_sum_smul {ι : Type} (s : Finset ι) (a : ι → ℂ_[p]) (P : ι → MvPowerSeries σ ℂ_[p]) (k : σ) :
    pd k (∑ i ∈ s, a i • P i) = ∑ i ∈ s, a i • pd k (P i) := by
  ext n
  simp only [coeff_pd, map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem foldr_expand {β : Type} (c : β → σ → ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]) : ∀ (m : ℕ) (y : Fin m → β),
    (List.ofFn y).foldr (fun b G => ∑ k, algebraMap ℂ_[p] (MvPowerSeries σ ℂ_[p]) (c b k) * pd k G) F =
      ∑ f : Fin m → σ, (∏ j, c (y j) (f j)) • (List.ofFn f).foldr (fun k G => pd k G) F
  | 0, y => by simp
  | m + 1, y => by
    rw [List.ofFn_succ, List.foldr_cons, foldr_expand c F m]
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => σ)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Algebra.smul_def, pd_sum_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    have e : (Fin.consEquiv (fun _ : Fin (m + 1) => σ)) (k, f) = Fin.cons k f := rfl
    rw [e, List.ofFn_cons, List.foldr_cons, Fin.prod_univ_succ, smul_smul]
    simp only [Fin.cons_zero, Fin.cons_succ]

theorem cntL_ofFn {m : ℕ} (f : Fin m → σ) : cntL (List.ofFn f) = ∑ j, Finsupp.single (f j) 1 := by
  simp [cntL, List.map_ofFn, List.sum_ofFn]

end Formal

section Cplx

variable {σ : Type} [Fintype σ]

def cnt {k : ℕ} (f : Fin k → σ) (i : σ) : ℕ := (Finset.univ.filter fun j => f j = i).card

theorem perm_of_cnt {k : ℕ} (f l : Fin k → σ) (h : ∀ i, cnt f i = cnt l i) :
    ∃ e : Equiv.Perm (Fin k), f = l ∘ e := by
  have e : ∀ c, {a // f a = c} ≃ {b // l b = c} := fun c =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype]; exact h c)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext a
  exact (Equiv.ofFiberEquiv_map e a).symm

theorem cnt_toList (α : σ →₀ ℕ) (i : σ) :
    cnt (fun j : Fin (Multiset.card α.toMultiset) => α.toMultiset.toList.get ⟨j, by simpa using j.2⟩) i = α i := by
  set l := fun j : Fin (Multiset.card α.toMultiset) => α.toMultiset.toList.get ⟨j, by simpa using j.2⟩
  have hmap : Multiset.map l Finset.univ.val = α.toMultiset := by
    rw [Fin.univ_val_map]
    have : List.ofFn l = α.toMultiset.toList := by
      refine List.ext_get (by simp) ?_
      intro n h1 h2
      simp [l]
    rw [this, Multiset.coe_toList]
  have h := congrArg (Multiset.count i) hmap
  rw [Multiset.count_map, Finsupp.count_toMultiset] at h
  rw [← h]
  unfold cnt
  rw [Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr fun j _ => eq_comm

def cntF {m : ℕ} (f : Fin m → σ) : σ →₀ ℕ := ∑ j, Finsupp.single (f j) 1

theorem cntF_apply {m : ℕ} (f : Fin m → σ) (i : σ) : cntF f i = cnt f i := by
  rw [cntF, cnt, Finsupp.finset_sum_apply, Finset.card_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : f j = i
  · rw [h, if_pos rfl, Finsupp.single_eq_same]
  · rw [if_neg h, Finsupp.single_apply, if_neg h]

theorem card_cntF {m : ℕ} (f : Fin m → σ) : Multiset.card (cntF f).toMultiset = m := by
  rw [cntF, map_sum, Multiset.card_sum]
  simp

end Cplx

section Main

variable {D : D7} {N N' : ℕ}

theorem vec_eq (v : VC D N N') :
    v = ∑ k : D.what₂.Tau × Fin N' × Fin N, v k.1 k.2.1 k.2.2 • coordV D k := by
  funext τ i j
  simp only [Finset.sum_apply, Pi.smul_apply, coordV, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (τ, i, j)]
  · simp
  · rintro ⟨a, b, c⟩ _ hb
    rw [if_neg]
    rintro ⟨rfl, rfl, rfl⟩
    exact hb rfl
  · simp

theorem mlin_expand {m : ℕ} (A : ContinuousMultilinearMap ℂ (fun _ : Fin m => VC D N N') ℂ) (v : Fin m → VC D N N') :
    A v = ∑ f : Fin m → D.what₂.Tau × Fin N' × Fin N,
      (∏ j, v j (f j).1 (f j).2.1 (f j).2.2) * A (fun j => coordV D (f j)) := by
  have hv : v = fun j => ∑ k : D.what₂.Tau × Fin N' × Fin N, v j k.1 k.2.1 k.2.2 • coordV D k :=
    funext fun j => vec_eq (v j)
  conv_lhs => rw [hv]
  rw [A.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [A.map_smul_univ, smul_eq_mul]

theorem iFD_coord (G : VC D N N' → ℂ) (hG : ContDiff ℂ ⊤ G) {m : ℕ} (f : Fin m → D.what₂.Tau × Fin N' × Fin N) :
    iteratedFDeriv ℂ m G 0 (fun j => coordV D (f j)) =
      (∏ i, ((cntF f i).factorial : ℂ)) * taylor D G (cntF f) := by
  have key : ∀ (k : ℕ) (hk : k = m) (l : Fin k → D.what₂.Tau × Fin N' × Fin N), (∀ i, cnt l i = cntF f i) →
      iteratedFDeriv ℂ k G 0 (fun j => coordV D (l j)) = iteratedFDeriv ℂ m G 0 (fun j => coordV D (f j)) := by
    rintro k rfl l hl
    obtain ⟨e, he⟩ := perm_of_cnt f l (fun i => by rw [hl, cntF_apply])
    rw [he]
    exact (hG.contDiffAt.iteratedFDeriv_comp_perm (fun j => coordV D (l j)) e).symm
  have e1 : iteratedFDeriv ℂ (Multiset.card (cntF f).toMultiset) G 0
      (fun i => coordV D ((cntF f).toMultiset.toList.get ⟨i, by simpa using i.2⟩)) =
      iteratedFDeriv ℂ m G 0 (fun j => coordV D (f j)) :=
    key _ (card_cntF f) _ (cnt_toList (cntF f))
  have h0 : ((cntF f).prod fun _ n => (n.factorial : ℂ)) = ∏ i, ((cntF f i).factorial : ℂ) :=
    Finsupp.prod_fintype _ _ (by simp)
  have hne : (∏ i, ((cntF f i).factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  unfold taylor
  rw [e1, h0, mul_div_cancel₀ _ hne]

theorem embT_mem (τ : D.what₂.Tau) (x : D.host.E) : embT D τ x ∈ Qbar :=
  mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D τ).toRatAlgHom)

theorem lam_mk {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (a : ℂ) (h : a ∈ Qbar) :
    lam ⟨a, h⟩ = lamC lam a := by
  unfold lamC; rw [dif_pos h]

end Main

end GlobalTheory.JetTransport

namespace GlobalTheory.JetTransport

theorem jet_pSer : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ) (G : VC D N N' → ℂ), ContDiff ℂ ⊤ G → CoefIn D G Qbar → ∀ (m : ℕ) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E), iteratedFDeriv ℂ m G 0 (fun j => embV D (tor0 D cc δ) (y j)) ∈ Qbar ∧ jet D lam y (pSer D lam G) = lamC lam (iteratedFDeriv ℂ m G 0 fun j => embV D (tor0 D cc δ) (y j)) := by
  intro D cc δ p _ lam N N' G hG hco m y
  have hC : iteratedFDeriv ℂ m G 0 (fun j => embV D (tor0 D cc δ) (y j)) =
      ∑ f : Fin m → D.what₂.Tau × Fin N' × Fin N, (∏ j, embT D (f j).1 (y j (f j).2.1 (f j).2.2)) *
        ((∏ i, ((cntF f i).factorial : ℂ)) * taylor D G (cntF f)) := by
    rw [mlin_expand]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [iFD_coord G hG f]
    rfl
  have hP : jet D lam y (pSer D lam G) =
      ∑ f : Fin m → D.what₂.Tau × Fin N' × Fin N, (∏ j, lamC lam (embT D (f j).1 (y j (f j).2.1 (f j).2.2))) *
        ((∏ i, ((cntF f i).factorial : ℂ_[p])) * lamC lam (taylor D G (cntF f))) := by
    unfold jet
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    have hx := foldr_expand (fun (b : Matrix (Fin N') (Fin N) D.host.E) (k : D.what₂.Tau × Fin N' × Fin N) =>
      lamC lam (embT D k.1 (b k.2.1 k.2.2))) (pSer D lam G) m y
    erw [hx, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [map_smul, smul_eq_mul]
    congr 1
    have h := coeff_foldr_pd (pSer D lam G) (List.ofFn f) 0
    rw [zero_add, cntL_ofFn, multiIndexFactorial_zero, one_mul] at h
    rw [h]
    rfl
  set z : Qbar := ∑ f : Fin m → D.what₂.Tau × Fin N' × Fin N,
    (∏ j, (⟨embT D (f j).1 (y j (f j).2.1 (f j).2.2), embT_mem _ _⟩ : Qbar)) *
      ((∏ i, ((cntF f i).factorial : Qbar)) * ⟨taylor D G (cntF f), hco _⟩) with hzdef
  have hz : (z : ℂ) = iteratedFDeriv ℂ m G 0 (fun j => embV D (tor0 D cc δ) (y j)) := by
    rw [hC, hzdef, IntermediateField.coe_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [IntermediateField.coe_mul, IntermediateField.coe_mul, IntermediateField.coe_prod, IntermediateField.coe_prod]
    simp
  have hl : lam z = jet D lam y (pSer D lam G) := by
    rw [hP, hzdef, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [map_mul, map_prod, map_natCast, lam_mk]
  refine ⟨hz ▸ z.2, ?_⟩
  rw [← hz, ← hl]
  exact lam_mk lam _ z.2

end GlobalTheory.JetTransport
