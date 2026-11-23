import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormDetLe

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen.Loc

section CoefLeLemmas

variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {σ : Type}

theorem coefLe_sum {α : Type} (s : Finset α) (f : α → MvPolynomial σ ℂ) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ a ∈ s, CoefLe ι R (f a)) : CoefLe ι R (∑ a ∈ s, f a) := by
  intro m
  rw [MvPolynomial.coeff_sum, map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR (fun a ha => h a ha m)

theorem coefLe_mul {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S) {p q : MvPolynomial σ ℂ}
    (hp : CoefLe ι R p) (hq : CoefLe ι S q) : CoefLe ι (R * S) (p * q) := by
  classical
  intro m
  rw [MvPolynomial.coeff_mul, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hR hS) ?_
  intro x _
  rw [map_mul, norm_mul]
  exact mul_le_mul (hp _) (hq _) (norm_nonneg _) hR

theorem coefLe_one : CoefLe ι 1 (1 : MvPolynomial σ ℂ) := by
  classical
  intro m
  rw [MvPolynomial.coeff_one]
  split_ifs <;> simp

theorem coefLe_pow {R : ℝ} (hR : 0 ≤ R) {p : MvPolynomial σ ℂ} (hp : CoefLe ι R p) (k : ℕ) :
    CoefLe ι (R ^ k) (p ^ k) := by
  induction k with
  | zero => simpa using coefLe_one ι
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact coefLe_mul ι (pow_nonneg hR _) hR ih hp

theorem coefLe_prod {α : Type} (s : Finset α) (f : α → MvPolynomial σ ℂ) (r : α → ℝ)
    (hr : ∀ a, 0 ≤ r a) (h : ∀ a ∈ s, CoefLe ι (r a) (f a)) :
    CoefLe ι (∏ a ∈ s, r a) (∏ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using coefLe_one ι
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact coefLe_mul ι (hr a) (Finset.prod_nonneg fun b _ => hr b) (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem coefLe_C_mul_X {c : ℂ} {R : ℝ} (hR : 1 ≤ R) (hc : ‖ι.symm c‖ ≤ R) (v : σ) :
    CoefLe ι R (MvPolynomial.C c * MvPolynomial.X v) := by
  classical
  intro m
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X']
  split_ifs
  · simpa using hc
  · simpa using zero_le_one.trans hR

end CoefLeLemmas

theorem norm_det_le {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (R : ℝ)
    (hR : 1 ≤ R) (h : ∀ i j, ‖ι.symm (M i j)‖ ≤ R) : ‖ι.symm M.det‖ ≤ R ^ n :=
  _root_.UpperTheory.Reformulated.B.Qh58.norm_det_le ι M R hR h

def sz {a : ℕ} (lam : DomWeight a) : ℕ := ∑ k, (lam.w k).natAbs

theorem sz_dual {a : ℕ} (lam : DomWeight a) : sz lam.dual = sz lam := by
  unfold sz
  simp only [DomWeight.dual, Int.natAbs_neg]
  exact Equiv.sum_comp Fin.revPerm (fun k => (lam.w k).natAbs)

theorem one_le {a : ℕ} (lam : DomWeight a) :
    ∑ i, lam.natW i + a * lam.detShift.natAbs ≤ a * (2 * sz lam) := by
  cases a with
  | zero => simp
  | succ n =>
    have hd : lam.detShift = lam.w (Fin.last n) := by
      simp [DomWeight.detShift, Fin.last]
    have hl : lam.natW (Fin.last n) = 0 := by
      simp [DomWeight.natW, hd]
    have hi : ∀ i : Fin n, lam.natW i.castSucc ≤ (lam.w i.castSucc).natAbs + (lam.w (Fin.last n)).natAbs := by
      intro i
      simp only [DomWeight.natW, hd]
      omega
    have h1 : ∑ i : Fin n, lam.natW i.castSucc ≤
        (∑ i : Fin n, (lam.w i.castSucc).natAbs) + n * (lam.w (Fin.last n)).natAbs := by
      calc ∑ i : Fin n, lam.natW i.castSucc
          ≤ ∑ i : Fin n, ((lam.w i.castSucc).natAbs + (lam.w (Fin.last n)).natAbs) :=
            Finset.sum_le_sum fun i _ => hi i
        _ = _ := by simp [Finset.sum_add_distrib]
    rw [Fin.sum_univ_castSucc, hl, hd]
    unfold sz
    rw [Fin.sum_univ_castSucc]
    generalize (∑ i : Fin n, (lam.w i.castSucc).natAbs) = t at h1 ⊢
    generalize (lam.w (Fin.last n)).natAbs = e at h1 ⊢
    generalize (∑ i : Fin n, lam.natW i.castSucc) = u at h1 ⊢
    nlinarith [Nat.zero_le (n * t), Nat.zero_le (n * e)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

noncomputable def emb : InfinitePlace E ⊕ InfinitePlace E → (E →+* ℂ)
  | .inl v => v.embedding
  | .inr v => ComplexEmbedding.conjugate v.embedding

theorem mk_emb_inl (v : InfinitePlace E) : InfinitePlace.mk (emb (.inl v)) = v :=
  InfinitePlace.mk_embedding v

theorem mk_emb_inr (v : InfinitePlace E) : InfinitePlace.mk (emb (.inr v)) = v := by
  simp only [emb]
  rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

theorem emb_injective : Function.Injective (emb (E := E)) := by
  rintro (v | v) (w | w) h
  · have := congrArg InfinitePlace.mk h
    rw [mk_emb_inl, mk_emb_inl] at this
    rw [this]
  · exfalso
    have := congrArg InfinitePlace.mk h
    rw [mk_emb_inl, mk_emb_inr] at this
    subst this
    exact conjugate_ne v.embedding h.symm
  · exfalso
    have := congrArg InfinitePlace.mk h
    rw [mk_emb_inr, mk_emb_inl] at this
    subst this
    exact conjugate_ne v.embedding h
  · have := congrArg InfinitePlace.mk h
    rw [mk_emb_inr, mk_emb_inr] at this
    rw [this]

def wI {T : Type} [DecidableEq T] (I : Finset T) (n : ℕ) : T × Fin n × Fin n → ℕ := fun v => if v.1 ∈ I then 1 else 0

theorem homog_of_mem {T : Type} [Fintype T] [DecidableEq T] (I : Finset T) (n : ℕ) (lam : T → DomWeight n)
    (x : MvPolynomial (T × Fin n × Fin n) ℂ) (hx : x ∈ Formalism.L2.DIV.VV ℂ lam) :
    MvPolynomial.IsWeightedHomogeneous (wI I n) x (∑ τ, if τ ∈ I then ∑ i, (lam τ).natW i else 0) := by
  unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hx
  rw [← MvPolynomial.mem_weightedHomogeneousSubmodule]
  refine (Submodule.span_le.2 ?_) hx
  rintro _ ⟨F, hF, rfl⟩
  refine (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).2 ?_
  refine MvPolynomial.IsWeightedHomogeneous.prod _ _ _ fun τ _ => ?_
  intro d hd
  obtain ⟨m, rfl, hm⟩ := MvPolynomial.coeff_rename_ne_zero _ _ _ hd
  have hw : Finsupp.weight (Formalism.GradedWeylDivisibility.colW n n) m = (lam τ).natW :=
    (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp (hF τ).1 hm
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_mul])]
  by_cases hτ : τ ∈ I
  · rw [if_pos hτ, ← hw, Finsupp.weight_apply]
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, Formalism.GradedWeylDivisibility.colW, smul_eq_mul, wI, if_pos hτ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [Pi.single_apply]
  · simp [wI, hτ, Finsupp.sum]

theorem block_le {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {T : Type} [DecidableEq T] (I : Finset T) {n : ℕ}
    (A : T → Matrix (Fin n) (Fin n) ℂ) (R : ℝ) (hR : 1 ≤ R) (hA : ∀ τ i j, ‖ι.symm (A τ i j)‖ ≤ if τ ∈ I then R else 1)
    (D : ℕ) (x : MvPolynomial (T × Fin n × Fin n) ℂ) (hx : MvPolynomial.IsWeightedHomogeneous (wI I n) x D)
    (h1 : CoefLe ι 1 x) : CoefLe ι (R ^ D) (Formalism.GradedWeylDivisibility.blockAct ℂ A x) := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  set y : T × Fin n × Fin n → MvPolynomial (T × Fin n × Fin n) ℂ :=
    fun v => ∑ b : Fin n, MvPolynomial.C (A v.1 v.2.1 b) * MvPolynomial.X (v.1, (b, v.2.2)) with hydef
  have hr : ∀ τ, (if τ ∈ I then R else 1) = R ^ (if τ ∈ I then 1 else 0) := fun τ => by split_ifs <;> simp
  have hy : ∀ v, CoefLe ι (R ^ wI I n v) (y v) := fun v =>
    coefLe_sum ι _ _ (pow_nonneg hR0 _) fun b _ => coefLe_C_mul_X ι (one_le_pow₀ hR) ((hA _ _ _).trans_eq (hr _)) _
  have e : Formalism.GradedWeylDivisibility.blockAct ℂ A x =
      ∑ m ∈ x.support, MvPolynomial.C (MvPolynomial.coeff m x) * (m.prod fun v e => y v ^ e) := by
    conv_lhs => rw [x.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Formalism.GradedWeylDivisibility.blockAct, MvPolynomial.aeval_monomial]
    rfl
  rw [e]
  refine coefLe_sum ι _ _ (pow_nonneg hR0 _) fun m hm k => ?_
  rw [MvPolynomial.coeff_C_mul, map_mul, norm_mul]
  have hdeg : Finsupp.weight (wI I n) m = D := hx (MvPolynomial.mem_support_iff.1 hm)
  have h := coefLe_prod ι m.support (fun v => y v ^ m v) (fun v => (R ^ wI I n v) ^ m v)
    (fun _ => by positivity) (fun v _ => coefLe_pow ι (pow_nonneg hR0 _) (hy v) (m v))
  have e2 : ∏ v ∈ m.support, (R ^ wI I n v) ^ m v = R ^ D := by
    rw [← hdeg, Finsupp.weight_apply, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun v _ => by rw [← pow_mul, smul_eq_mul, mul_comm]
  rw [e2] at h
  exact (mul_le_mul (h1 m) (h k) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem det_le {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {T : Type} [Fintype T] [DecidableEq T] (I : Finset T) {n : ℕ}
    (lam : T → DomWeight n) (A : T → GL (Fin n) ℂ) (R : ℝ) (hR : 1 ≤ R)
    (h : ∀ τ i j, (‖ι.symm (((A τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j)‖ ≤ if τ ∈ I then R else 1) ∧
      ‖ι.symm ((((A τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j)‖ ≤ if τ ∈ I then R else 1) :
    ‖ι.symm (Formalism.L2.DIV.detTwK lam A)‖ ≤ R ^ (∑ τ, if τ ∈ I then n * (lam τ).detShift.natAbs else 0) := by
  rw [Formalism.L2.DIV.detTw_eq, map_prod, norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun τ _ => ?_
  have hR' : 1 ≤ if τ ∈ I then R else 1 := by split_ifs; exacts [hR, le_rfl]
  have h1 := norm_det_le ι ((A τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) _ hR' fun i j => (h τ i j).1
  have h2 := norm_det_le ι (((A τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) _ hR' fun i j => (h τ i j).2
  have hinv : (((A τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det =
      (((A τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have e : R ^ (if τ ∈ I then n * (lam τ).detShift.natAbs else 0) =
      ((if τ ∈ I then R else 1) ^ n) ^ (lam τ).detShift.natAbs := by
    split_ifs <;> simp [pow_mul]
  rw [e]
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg (lam τ).detShift
  · rw [hk, zpow_natCast, map_pow, norm_pow, Int.natAbs_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 k
  · rw [hk, zpow_neg, zpow_natCast, ← inv_pow, ← hinv, map_pow, norm_pow, Int.natAbs_neg, Int.natAbs_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) h2 k

theorem rho_le {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (W : Wt E a) [DecidableEq (InfinitePlace E)]
    (I : Finset (InfinitePlace E)) (A : InfinitePlace E → GL (Fin a) ℂ) (R : ℝ) (hR : 1 ≤ R)
    (hA : ∀ τ i j, (‖ι.symm (((A τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j)‖ ≤ if τ ∈ I then R else 1) ∧
      ‖ι.symm ((((A τ)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j)‖ ≤ if τ ∈ I then R else 1)
    (x : W.Sp) (hx : CoefLe ι 1 x.1) :
    CoefLe ι (R ^ (a * ∑ v ∈ I, 2 * sz (W v))) (Formalism.L2.DIV.rhoK (K := ℂ) W A x).1 := by
  intro m
  have hb := block_le ι I (fun τ => Matrix.transpose ((A τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)) R hR
    (fun τ i j => by simpa [Matrix.transpose_apply] using (hA τ j i).1) _ x.1 (homog_of_mem I a W x.1 x.2) hx m
  have hd := det_le ι I W A R hR hA
  have hcoe : (Formalism.L2.DIV.rhoK (K := ℂ) W A x).1 =
      Formalism.L2.DIV.detTwK W A • Formalism.L2.DIV.trAct A x.1 := rfl
  rw [hcoe, MvPolynomial.coeff_smul, smul_eq_mul, map_mul, norm_mul]
  have hR0 : (0 : ℝ) ≤ R := by linarith
  refine (mul_le_mul hd hb (norm_nonneg _) (pow_nonneg hR0 _)).trans ?_
  rw [← pow_add]
  refine pow_le_pow_right₀ hR ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_ite_mem_eq I]
  refine Finset.sum_le_sum fun v _ => ?_
  split_ifs
  · rw [add_comm]; exact one_le (W v)
  · simp

end UpperTheory.Gal.Gen.Loc
