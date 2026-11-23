import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.NormDegUniv
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.SubstSPtrue

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.G.WittFrameLocaliserOrders
open Formalism.L2.G.Model (Lin)

section Zero

variable {R : Type} [CommRing R] {n' k : ℕ}

theorem normal_degree_zero_one (r : ℕ) : (1 : MvPolynomial (TV n' k) R) ∈ NDsub R n' k r 0 := by
  rw [NDsub, MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  have hm0 : m = 0 := by
    by_contra hne
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff, MvPolynomial.coeff_one, if_neg (Ne.symm hne)] at hm
    exact hm rfl
  subst hm0
  simp [normDeg]

private lemma normDeg_add' {r : ℕ} (a b : TV n' k →₀ ℕ) : normDeg r (a + b) = normDeg r a + normDeg r b := by
  classical
  unfold normDeg
  exact Finsupp.sum_add_index' (h := fun v c => if IsNormal r v then c else 0) (fun v => by simp)
    (fun v c₁ c₂ => by split_ifs <;> simp)

theorem normal_degree_zero_mul {r : ℕ} {P Q : MvPolynomial (TV n' k) R} (hP : P ∈ NDsub R n' k r 0) (hQ : Q ∈ NDsub R n' k r 0) :
    P * Q ∈ NDsub R n' k r 0 := by
  rw [NDsub, MvPolynomial.mem_restrictSupport_iff] at hP hQ ⊢
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hm)
  have h1 := hP ha
  have h2 := hQ hb
  simp only [Set.mem_setOf_eq, nonpos_iff_eq_zero] at h1 h2 ⊢
  simp [normDeg_add', h1, h2]

theorem normal_degree_zero_pow {r : ℕ} {P : MvPolynomial (TV n' k) R} (hP : P ∈ NDsub R n' k r 0) (n : ℕ) :
    P ^ n ∈ NDsub R n' k r 0 := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact normal_degree_zero_one r
  | succ n ih =>
    rw [pow_succ]
    exact normal_degree_zero_mul ih hP

theorem normal_degree_zero_prod {r : ℕ} {α : Type} (s : Finset α) (f : α → MvPolynomial (TV n' k) R)
    (h : ∀ i ∈ s, f i ∈ NDsub R n' k r 0) : ∏ i ∈ s, f i ∈ NDsub R n' k r 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact normal_degree_zero_one r
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact normal_degree_zero_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem normal_degree_zero_X_abnormal {r : ℕ} (v : TV n' k) (hv : ¬ IsNormal r v) : (X v : MvPolynomial (TV n' k) R) ∈ NDsub R n' k r 0 := by
  rw [NDsub, MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  have hm' : m ∈ ({Finsupp.single v 1} : Finset (TV n' k →₀ ℕ)) :=
    MvPolynomial.support_monomial_subset (R := R) hm
  rw [Finset.mem_singleton] at hm'
  subst hm'
  show normDeg r (Finsupp.single v 1) ≤ 0
  unfold normDeg
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, if_neg hv]

theorem normal_degree_zero_det_pmat {r : ℕ} (hrk : r ≤ k) (A : Fin r → Fin n') (P : Fin r → ℕ) (hA : ∀ l, Even (A l).val) :
    (pmat R hrk A P).det ∈ NDsub R n' k r 0 := by
  rw [Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  refine normal_degree_zero_prod _ _ fun i _ => ?_
  refine normal_degree_zero_pow ?_ _
  refine normal_degree_zero_X_abnormal _ ?_
  intro hN
  unfold IsNormal at hN
  rw [if_pos (hA _)] at hN
  simp only [Fin.coe_castLE] at hN
  omega

theorem fixed_symbol_normal_degree_zero (p : ℕ) [NeZero n'] {r : ℕ} (F : Frames n' r) {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (hn : Even n')
    (hr : 1 ≤ r) (hrk : r ≤ k) (c' Q : ℕ) : SPR R p F hrk c' Q ∈ NDsub R n' k r 0 := by
  have h1 : ∀ j : ℤ, (pmat R hrk (fun l => posOf n' (F.fr j l.val))
      (fun l => p ^ (zF F j - F.fr j l.val).toNat)).det ∈ NDsub R n' k r 0 := fun j =>
    normal_degree_zero_det_pmat hrk _ _ fun l => (posOf_even hn _).2 (hV.2.2.2.2.1 j l.val l.isLt).2
  have h2 : ∀ s : ℤ, (pmat R hrk (fun l => posOf n' (Arow F s l.val))
      (fun l => p ^ (s - Arow F s l.val).toNat)).det ∈ NDsub R n' k r 0 := fun s =>
    normal_degree_zero_det_pmat hrk _ _ fun l => (posOf_even hn _).2 (window_holds_even_tops n' r F L₁ N₁ hV hn hr s l.val l.isLt).1
  unfold SPR
  exact normal_degree_zero_mul (normal_degree_zero_mul (normal_degree_zero_pow (normal_degree_zero_prod _ _ fun j _ => normal_degree_zero_pow (h1 _) _) _)
    (normal_degree_zero_prod _ _ fun j _ => normal_degree_zero_pow (h1 _) _)) (normal_degree_zero_prod _ _ fun s _ => normal_degree_zero_pow (h2 _) _)

theorem nd_map {R' : Type} [CommRing R'] (f : R →+* R') {r T : ℕ} {P : MvPolynomial (TV n' k) R}
    (hP : P ∈ NDsub R n' k r T) : map f P ∈ NDsub R' n' k r T := by
  rw [NDsub, MvPolynomial.mem_restrictSupport_iff] at hP ⊢
  exact fun m hm => hP (MvPolynomial.support_map_subset f P hm)

theorem nd_rename {r K : ℕ} (hk : k = r + K) {T : ℕ} {P : MvPolynomial (Fin n' × Fin (r + K)) R}
    (hP : ∀ mm ∈ P.support, vsDeg mm ≤ T) : rename (castVK (n' := n') hk) P ∈ NDsub R n' k r T := by
  classical
  rw [NDsub, MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  have hinj : Function.Injective (castVK (n' := n') hk) := by
    intro x y hxy
    simp only [castVK, Prod.mk.injEq] at hxy
    exact Prod.ext hxy.1 (Fin.cast_injective _ hxy.2)
  rw [Finset.mem_coe, MvPolynomial.support_rename_of_injective hinj, Finset.mem_image] at hm
  obtain ⟨mm, hmm, rfl⟩ := hm
  have key : normDeg r (Finsupp.mapDomain (castVK hk) mm) = vsDeg mm := by
    unfold normDeg vsDeg
    rw [show (∑ v ∈ (Finsupp.mapDomain (castVK hk) mm).support,
        if IsNormal r v then (Finsupp.mapDomain (castVK hk) mm) v else 0) =
        (Finsupp.mapDomain (castVK hk) mm).sum (fun v c => if IsNormal r v then c else 0) from rfl]
    rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by split_ifs <;> simp),
      Finsupp.sum_fintype _ _ (fun _ => by simp), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Fin.sum_univ_add]
    by_cases ht : Even t.val
    · rw [if_pos ht]
      simp [IsNormal, castVK, ht]
    · rw [if_neg ht]
      simp [IsNormal, castVK, ht]
  rw [Set.mem_setOf_eq, key]
  exact hP mm hmm

end Zero

section Sub

variable (p n' : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF p n') O] (w : O) (r : ℕ) {k : ℕ}
  (g : Matrix (Fin k) (Fin k) (WF p n'))

def Nsub (s : Fin n') : Matrix (Fin k) (Fin k) (KK O) := fun a b =>
  if Even s.val then (if r ≤ b.val then algebraMap O (KK O) w else 1) * (sigMat p n' O g (s.val : ℤ))⁻¹ b a
  else (if b.val < r then algebraMap O (KK O) w else 1) * sigMat p n' O g (s.val : ℤ) a b

def NsubInv (s : Fin n') : Matrix (Fin k) (Fin k) (KK O) := fun b c =>
  if Even s.val then (if r ≤ b.val then (algebraMap O (KK O) w)⁻¹ else 1) * sigMat p n' O g (s.val : ℤ) c b
  else (if b.val < r then (algebraMap O (KK O) w)⁻¹ else 1) * (sigMat p n' O g (s.val : ℤ))⁻¹ b c

theorem subst_eq_Lin (f : MvPolynomial (TV n' k) (KK O)) :
    subst p n' O w n' r g f = Lin (Nsub p n' O w r g) f := by
  have key : subst p n' O w n' r g = Lin (Nsub p n' O w r g) := by
    apply MvPolynomial.algHom_ext
    intro v
    unfold subst liftSubst Lin
    rw [aeval_X, aeval_X]
    by_cases hs : Even v.1.val
    · simp only [LLT, hs, decide_true, if_true, Nsub]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs
      · rw [C_mul]; ring
      · rw [one_mul]; ring
    · simp only [LLT, hs, decide_false, Bool.false_eq_true, if_false, Nsub]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs
      · rw [C_mul]; ring
      · rw [one_mul]; ring
  rw [key]

variable {g}

theorem Nsub_mul (hw : algebraMap O (KK O) w ≠ 0) (hg : IsGLW g) (s : Fin n') :
    Nsub p n' O w r g s * NsubInv p n' O w r g s = 1 := by
  ext a c
  simp only [Matrix.mul_apply, Nsub, NsubInv, Matrix.one_apply]
  set σ := sigMat p n' O g (s.val : ℤ) with hσdef
  have hσ : IsUnit σ.det := by
    let φ : WF p n' →+* KK O := (algebraMap O (KK O)).comp ((algebraMap (WF p n') O).comp (sigPow p n' (s.val : ℤ)))
    have h1 : σ = φ.mapMatrix g := by
      ext i j
      rfl
    rw [h1, ← RingHom.map_det]
    exact hg.map φ
  by_cases hs : Even s.val
  · simp only [if_pos hs]
    have h2 : ∀ b : Fin k, (if r ≤ b.val then algebraMap O (KK O) w else 1) * σ⁻¹ b a *
        ((if r ≤ b.val then (algebraMap O (KK O) w)⁻¹ else 1) * σ c b) = σ c b * σ⁻¹ b a := by
      intro b
      split_ifs
      · field_simp
      · ring
    simp_rw [h2]
    rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv _ hσ, Matrix.one_apply]
    simp [eq_comm]
  · simp only [if_neg hs]
    have h2 : ∀ b : Fin k, (if b.val < r then algebraMap O (KK O) w else 1) * σ a b *
        ((if b.val < r then (algebraMap O (KK O) w)⁻¹ else 1) * σ⁻¹ b c) = σ a b * σ⁻¹ b c := by
      intro b
      split_ifs
      · field_simp
      · ring
    simp_rw [h2]
    rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv _ hσ, Matrix.one_apply]

end Sub

end Formalism.MainNotions.TestSideCounting
