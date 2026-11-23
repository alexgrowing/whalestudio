import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.SquareNormIntegralNonneg
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HookBound

noncomputable section

open MvPolynomial Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum

namespace Formalism.IndefR.Fock.DeltaPf

open Formalism.REAL

theorem fockF_eq_sum_of_subset {σ : Type*} {f g : MvPolynomial σ ℂ} {s : Finset (σ →₀ ℕ)} (h : f.support ⊆ s) :
    fockF f g = ∑ m ∈ s, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold fockF
  refine Finset.sum_subset h ?_
  intro m _ hm
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  simp [hm]

theorem fockF_one {σ : Type*} : fockF (1 : MvPolynomial σ ℂ) 1 = 1 := by
  classical
  rw [fockF_eq_sum_of_subset (s := {0})]
  · simp
  · intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
    rw [Finset.mem_singleton]
    by_contra h0
    exact hm (if_neg (Ne.symm h0))

theorem fockF_neg {σ : Type*} (f : MvPolynomial σ ℂ) : fockF (-f) (-f) = fockF f f := by
  unfold fockF
  simp [MvPolynomial.support_neg, MvPolynomial.coeff_neg]

theorem fockF_rename {σ τ : Type*} {i : σ → τ} (hi : Function.Injective i) (f g : MvPolynomial σ ℂ) :
    fockF (rename i f) (rename i g) = fockF f g := by
  classical
  unfold fockF
  rw [MvPolynomial.support_rename_of_injective hi, Finset.sum_image (by
    intro a _ b _ hab
    exact Finsupp.mapDomain_injective hi hab)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.coeff_rename_mapDomain i hi, MvPolynomial.coeff_rename_mapDomain i hi,
    Finsupp.mapDomain_support_of_injective hi, Finset.prod_image (by
      intro a _ b _ hab
      exact hi hab)]
  simp only [Finsupp.mapDomain_apply hi]

theorem fockF_map_rat {σ : Type*} (f : MvPolynomial σ ℚ) :
    fockF (map (algebraMap ℚ ℂ) f) (map (algebraMap ℚ ℂ) f) = ((Formalism.GradedWeylDivisibility.fockQ f f : ℝ) : ℂ) := by
  unfold fockF Formalism.GradedWeylDivisibility.fockQ
  have hs : ∀ q : ℚ, star (q : ℂ) = q := fun q => by
    rw [← Complex.ofReal_ratCast, ← starRingEnd_apply, Complex.conj_ofReal]
  rw [MvPolynomial.support_map_of_injective _ (algebraMap ℚ ℂ).injective]
  push_cast
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.coeff_map, eq_ratCast, hs]

theorem split_unique {σ : Type*} {A B : Set σ} (hAB : Disjoint A B) {x y a b : σ →₀ ℕ}
    (hx : (↑x.support : Set σ) ⊆ A) (hy : (↑y.support : Set σ) ⊆ B) (ha : (↑a.support : Set σ) ⊆ A)
    (hb : (↑b.support : Set σ) ⊆ B) (h : x + y = a + b) : x = a ∧ y = b := by
  have key : ∀ k, x k = a k ∧ y k = b k := by
    intro k
    have hk := DFunLike.congr_fun h k
    simp only [Finsupp.add_apply] at hk
    by_cases hA : k ∈ A
    · have hB : k ∉ B := fun hB => Set.disjoint_left.mp hAB hA hB
      have hy0 : y k = 0 := by
        by_contra hne
        exact hB (hy (Finset.mem_coe.2 (Finsupp.mem_support_iff.mpr hne)))
      have hb0 : b k = 0 := by
        by_contra hne
        exact hB (hb (Finset.mem_coe.2 (Finsupp.mem_support_iff.mpr hne)))
      omega
    · have hx0 : x k = 0 := by
        by_contra hne
        exact hA (hx (Finset.mem_coe.2 (Finsupp.mem_support_iff.mpr hne)))
      have ha0 : a k = 0 := by
        by_contra hne
        exact hA (ha (Finset.mem_coe.2 (Finsupp.mem_support_iff.mpr hne)))
      omega
  exact ⟨Finsupp.ext fun k => (key k).1, Finsupp.ext fun k => (key k).2⟩

theorem fockF_mul_of_disjoint {σ : Type*} {A B : Set σ} (hAB : Disjoint A B) {P Q : MvPolynomial σ ℂ}
    (hP : P ∈ supported ℂ A) (hQ : Q ∈ supported ℂ B) :
    fockF (P * Q) (P * Q) = fockF P P * fockF Q Q := by
  classical
  have hPs : ∀ x ∈ P.support, (↑x.support : Set σ) ⊆ A := fun x hx k hk =>
    (MvPolynomial.mem_supported.1 hP) (Finset.mem_coe.2 ((MvPolynomial.mem_vars k).2 ⟨x, hx, Finset.mem_coe.1 hk⟩))
  have hQs : ∀ y ∈ Q.support, (↑y.support : Set σ) ⊆ B := fun y hy k hk =>
    (MvPolynomial.mem_supported.1 hQ) (Finset.mem_coe.2 ((MvPolynomial.mem_vars k).2 ⟨y, hy, Finset.mem_coe.1 hk⟩))
  have hcoeff : ∀ x ∈ P.support, ∀ y ∈ Q.support, (P * Q).coeff (x + y) = P.coeff x * Q.coeff y := by
    intro x hx y hy
    rw [MvPolynomial.coeff_mul]
    refine Finset.sum_eq_single (x, y) ?_ ?_
    · rintro ⟨u, v⟩ huv hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at huv
      by_cases hu : u ∈ P.support
      · by_cases hv : v ∈ Q.support
        · exact absurd (Prod.ext_iff.2 (split_unique hAB (hPs u hu) (hQs v hv) (hPs x hx) (hQs y hy) huv)) hne
        · rw [MvPolynomial.mem_support_iff, not_not] at hv
          rw [hv, mul_zero]
      · rw [MvPolynomial.mem_support_iff, not_not] at hu
        rw [hu, zero_mul]
    · intro hn
      exact (hn (by simp)).elim
  have hw : ∀ x ∈ P.support, ∀ y ∈ Q.support,
      (∏ k ∈ (x + y).support, ((x + y) k).factorial) =
        (∏ k ∈ x.support, (x k).factorial) * ∏ k ∈ y.support, (y k).factorial := by
    intro x hx y hy
    have hd : Disjoint x.support y.support := by
      rw [Finset.disjoint_left]
      intro k hkx hky
      exact Set.disjoint_left.1 hAB (hPs x hx (Finset.mem_coe.2 hkx)) (hQs y hy (Finset.mem_coe.2 hky))
    rw [Finsupp.support_add_eq hd, Finset.prod_union hd]
    congr 1
    · refine Finset.prod_congr rfl fun k hk => ?_
      have h0 : y k = 0 := by simpa using Finset.disjoint_left.1 hd hk
      simp [h0]
    · refine Finset.prod_congr rfl fun k hk => ?_
      have h0 : x k = 0 := by simpa using Finset.disjoint_right.1 hd hk
      simp [h0]
  have hinj : ∀ p ∈ P.support ×ˢ Q.support, ∀ q ∈ P.support ×ˢ Q.support, p.1 + p.2 = q.1 + q.2 → p = q := by
    intro p hp q hq h
    rw [Finset.mem_product] at hp hq
    obtain ⟨h1, h2⟩ := split_unique hAB (hPs _ hp.1) (hQs _ hp.2) (hPs _ hq.1) (hQs _ hq.2) h
    exact Prod.ext h1 h2
  have hsub : (P * Q).support ⊆ (P.support ×ˢ Q.support).image (fun p : (σ →₀ ℕ) × (σ →₀ ℕ) => p.1 + p.2) := by
    intro m hm
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul P Q hm)
    exact Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨hx, hy⟩, rfl⟩
  rw [fockF_eq_sum_of_subset hsub, Finset.sum_image (by
    intro p hp q hq h
    exact hinj p hp q hq h), Finset.sum_product]
  unfold fockF
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  simp only [hcoeff x hx y hy, hw x hx y hy, star_mul', Nat.cast_mul]
  ring

theorem fockF_prod {ι σ : Type*} (s : Finset ι) (A : ι → Set σ) (hA : Pairwise fun i j => Disjoint (A i) (A j))
    (P : ι → MvPolynomial σ ℂ) (hP : ∀ i, P i ∈ supported ℂ (A i)) :
    fockF (∏ i ∈ s, P i) (∏ i ∈ s, P i) = ∏ i ∈ s, fockF (P i) (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fockF_one]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    rw [fockF_mul_of_disjoint (A := A i) (B := ⋃ j ∈ s, A j) ?_ (hP i) ?_, ih]
    · exact Set.disjoint_iUnion₂_right.2 fun j hj => hA (fun hij => hi (by rw [hij]; exact hj))
    · exact prod_mem fun j hj => MvPolynomial.supported_mono (fun x hx => Set.mem_iUnion₂.2 ⟨j, hj, hx⟩) (hP j)

theorem rename_mem_supported {σ τ : Type*} (i : σ → τ) (f : MvPolynomial σ ℂ) :
    rename i f ∈ supported ℂ (Set.range i) := by
  classical
  rw [MvPolynomial.mem_supported]
  intro v hv
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename i f (Finset.mem_coe.1 hv))
  exact ⟨w, rfl⟩

def PmEq {R : Type*} [Ring R] (f g : R) : Prop := f = g ∨ f = -g

theorem PmEq.mul {R : Type*} [Ring R] {f g f' g' : R} (h : PmEq f g) (h' : PmEq f' g') : PmEq (f * f') (g * g') := by
  unfold PmEq at *
  rcases h with rfl | rfl <;> rcases h' with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (mul_neg _ _)
  · exact Or.inr (neg_mul _ _)
  · exact Or.inl (neg_mul_neg _ _)

theorem PmEq.pow {R : Type*} [Ring R] {f g : R} (h : PmEq f g) (k : ℕ) : PmEq (f ^ k) (g ^ k) := by
  induction k with
  | zero => exact Or.inl (by rw [pow_zero, pow_zero])
  | succ k ih => simpa only [pow_succ] using ih.mul h

theorem PmEq.prod {ι R : Type*} [CommRing R] (s : Finset ι) (f g : ι → R) (h : ∀ i ∈ s, PmEq (f i) (g i)) :
    PmEq (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Or.inl (by simp)
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem pmEq_sign {R : Type*} [CommRing R] (u : ℤˣ) (x : R) : PmEq (((u : ℤ) : R) * x) x := by
  unfold PmEq
  rcases Int.units_eq_one_or u with rfl | rfl
  · left
    simp
  · right
    simp

theorem fockF_pm {σ : Type*} {f g : MvPolynomial σ ℂ} (h : PmEq f g) : fockF f f = fockF g g := by
  unfold PmEq at h
  rcases h with rfl | rfl
  · rfl
  · exact fockF_neg g

theorem PmEq.mem {σ : Type*} {S : Set σ} {f g : MvPolynomial σ ℂ} (h : PmEq f g) (hg : g ∈ supported ℂ S) :
    f ∈ supported ℂ S := by
  unfold PmEq at h
  rcases h with rfl | rfl
  · exact hg
  · exact neg_mem hg

theorem hw_low (N : ℕ) (ν : Fin N → ℕ) (h : Antitone ν) :
    (∏ l, ((ν l).factorial : ℝ)) ≤ (Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl ν) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl ν) : ℝ) := by
  have h1 := PI.HookLower.one_le_cNu ν h
  unfold PI.cNu at h1
  have hpos : (0 : ℝ) < ∏ l, ((ν l).factorial : ℝ) :=
    Finset.prod_pos fun l _ => by exact_mod_cast Nat.factorial_pos _
  rwa [one_le_div hpos] at h1

section Spec

variable {D : D7} {m n : ℕ}

def iotaP (τ : D.what₂.Tau) {P : ℕ} (hm : P ≤ m) (hn : P ≤ n) (v : Fin P × Fin P) : FVar D m n :=
  (τ, Fin.castLE hm v.2, Fin.castLE hn v.1)

def embedding₂ (τ : D.what₂.Tau) (P : ℕ) {Q : ℕ} (hm : P + Q ≤ m) (hn : Q ≤ n) (v : Fin Q × Fin Q) : FVar D m n :=
  (τ, ⟨P + v.2, by have := v.2.isLt; omega⟩, ⟨n - 1 - v.1, by have := v.1.isLt; omega⟩)

theorem cornerInclusion_injective (τ : D.what₂.Tau) {P : ℕ} (hm : P ≤ m) (hn : P ≤ n) : Function.Injective (iotaP τ hm hn) := by
  intro v w h
  have h1 := congrArg (fun z : FVar D m n => (z.2.2 : ℕ)) h
  have h2 := congrArg (fun z : FVar D m n => (z.2.1 : ℕ)) h
  simp only [iotaP, Fin.coe_castLE] at h1 h2
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)

theorem iotaM_inj (τ : D.what₂.Tau) (P : ℕ) {Q : ℕ} (hm : P + Q ≤ m) (hn : Q ≤ n) :
    Function.Injective (embedding₂ (D := D) τ P hm hn) := by
  intro v w h
  have h1 := congrArg (fun z : FVar D m n => (z.2.2 : ℕ)) h
  have h2 := congrArg (fun z : FVar D m n => (z.2.1 : ℕ)) h
  simp only [embedding₂] at h1 h2
  have := v.1.isLt
  have := w.1.isLt
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

def psiP (τ : D.what₂.Tau) {P : ℕ} (hm : P ≤ m) (hn : P ≤ n) :
    MvPolynomial (Fin P × Fin P) ℚ →+* MvPolynomial (FVar D m n) ℂ :=
  (rename (iotaP τ hm hn)).toRingHom.comp (map (algebraMap ℚ ℂ))

def psiM (τ : D.what₂.Tau) (P : ℕ) {Q : ℕ} (hm : P + Q ≤ m) (hn : Q ≤ n) :
    MvPolynomial (Fin Q × Fin Q) ℚ →+* MvPolynomial (FVar D m n) ℂ :=
  (rename (embedding₂ τ P hm hn)).toRingHom.comp (map (algebraMap ℚ ℂ))

theorem minorPlus_eq (τ : D.what₂.Tau) {P : ℕ} (hm : P ≤ m) (hn : P ≤ n) (k : ℕ) (hk : k ≤ P) (hk' : k ≤ P) :
    psiP τ hm hn (Formalism.GradedWeylDivisibility.lpMinor ℚ k hk hk') = minorPlus τ k := by
  unfold minorPlus Formalism.GradedWeylDivisibility.lpMinor
  rw [RingHom.map_det]
  refine congrArg Matrix.det (Matrix.ext fun α β => ?_)
  have hα := α.isLt
  have hβ := β.isLt
  simp [psiP, iotaP, varF, RingHom.mapMatrix_apply]
  split_ifs with h
  · rfl
  · exact absurd ⟨by omega, by omega⟩ h

theorem minorMinus_eq (τ : D.what₂.Tau) (P : ℕ) {Q : ℕ} (hm : P + Q ≤ m) (hn : Q ≤ n) (k : ℕ) (hk : k ≤ Q)
    (hk' : k ≤ Q) :
    minorMinus τ P k =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin k)) : ℤ) : MvPolynomial (FVar D m n) ℂ) *
        psiM τ P hm hn (Formalism.GradedWeylDivisibility.lpMinor ℚ k hk hk') := by
  unfold minorMinus Formalism.GradedWeylDivisibility.lpMinor
  rw [RingHom.map_det, ← Matrix.det_permute]
  refine congrArg Matrix.det (Matrix.ext fun α β => ?_)
  have hα := α.isLt
  have hβ := β.isLt
  simp [psiM, embedding₂, varF, RingHom.mapMatrix_apply, Fin.revPerm_apply]
  split_ifs with h
  · first
      | rfl
      | (congr 1
         refine Prod.ext rfl (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) <;> (try simp [Fin.val_rev]) <;> omega)
      | (simp [Fin.val_rev]; omega)
  · exact absurd ⟨by omega, by omega⟩ h

theorem plusPart_eq (τ : D.what₂.Tau) {P : ℕ} (hm : P ≤ m) (hn : P ≤ n) (a : ℕ → ℕ) :
    (∏ i ∈ Finset.range P, minorPlus (D := D) (m := m) (n := n) τ (i + 1) ^ (a i - if i + 1 < P then a (i + 1) else 0)) =
      psiP τ hm hn (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun s : Fin P => a s)) := by
  rw [Finset.prod_range]
  unfold Formalism.GradedWeylDivisibility.hw
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  have hs := s.isLt
  rw [map_pow, minorPlus_eq τ hm hn (s.val + 1) (by omega) (by omega)]
  congr 1
  all_goals simp [Formalism.GradedWeylDivisibility.nuNext]

theorem minusPart_pm (τ : D.what₂.Tau) (P : ℕ) {Q : ℕ} (hm : P + Q ≤ m) (hn : Q ≤ n) (a : ℕ → ℕ) :
    PmEq (∏ i ∈ Finset.range Q,
        minorMinus (D := D) (m := m) (n := n) τ P (i + 1) ^ (a i - if i + 1 < Q then a (i + 1) else 0))
      (psiM τ P hm hn (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun s : Fin Q => a s))) := by
  rw [Finset.prod_range]
  unfold Formalism.GradedWeylDivisibility.hw
  rw [map_prod]
  refine PmEq.prod _ _ _ fun s _ => ?_
  have hs := s.isLt
  rw [map_pow, minorMinus_eq τ P hm hn (s.val + 1) (by omega) (by omega)]
  have he : (a ↑s - if ↑s + 1 < Q then a (↑s + 1) else 0) =
      a ↑s - Formalism.GradedWeylDivisibility.nuNext (fun s : Fin Q => a ↑s) s := by
    simp [Formalism.GradedWeylDivisibility.nuNext]
  rw [he]
  exact (pmEq_sign _ _).pow _

end Spec

section Asm

variable {D : D7} {m n : ℕ}

theorem fockF_psiP (τ : D.what₂.Tau) {P : ℕ} (hm : P ≤ m) (hn : P ≤ n) (x : MvPolynomial (Fin P × Fin P) ℚ) :
    fockF (psiP τ hm hn x) (psiP τ hm hn x) = ((Formalism.GradedWeylDivisibility.fockQ x x : ℝ) : ℂ) := by
  show fockF (rename (iotaP τ hm hn) (map (algebraMap ℚ ℂ) x)) (rename (iotaP τ hm hn) (map (algebraMap ℚ ℂ) x)) = _
  rw [fockF_rename (cornerInclusion_injective τ hm hn), fockF_map_rat]

theorem fockF_psiM (τ : D.what₂.Tau) (P : ℕ) {Q : ℕ} (hm : P + Q ≤ m) (hn : Q ≤ n)
    (x : MvPolynomial (Fin Q × Fin Q) ℚ) :
    fockF (psiM τ P hm hn x) (psiM τ P hm hn x) = ((Formalism.GradedWeylDivisibility.fockQ x x : ℝ) : ℂ) := by
  show fockF (rename (embedding₂ τ P hm hn) (map (algebraMap ℚ ℂ) x)) (rename (embedding₂ τ P hm hn) (map (algebraMap ℚ ℂ) x)) = _
  rw [fockF_rename (iotaM_inj τ P hm hn), fockF_map_rat]

theorem psiP_mem_supported (τ : D.what₂.Tau) {P : ℕ} (hm : P ≤ m) (hn : P ≤ n) (x : MvPolynomial (Fin P × Fin P) ℚ) :
    psiP τ hm hn x ∈ supported ℂ {v : FVar D m n | v.1 = τ ∧ (v.2.1 : ℕ) < P} := by
  show rename (iotaP τ hm hn) (map (algebraMap ℚ ℂ) x) ∈ _
  refine MvPolynomial.supported_mono ?_ (rename_mem_supported (iotaP τ hm hn) _)
  rintro _ ⟨v, rfl⟩
  simp [iotaP]

theorem psiM_mem (τ : D.what₂.Tau) (P : ℕ) {Q : ℕ} (hm : P + Q ≤ m) (hn : Q ≤ n)
    (x : MvPolynomial (Fin Q × Fin Q) ℚ) :
    psiM τ P hm hn x ∈ supported ℂ {v : FVar D m n | v.1 = τ ∧ P ≤ (v.2.1 : ℕ)} := by
  show rename (embedding₂ τ P hm hn) (map (algebraMap ℚ ℂ) x) ∈ _
  refine MvPolynomial.supported_mono ?_ (rename_mem_supported (embedding₂ τ P hm hn) _)
  rintro _ ⟨v, rfl⟩
  simp [embedding₂]

theorem deltaAt_fock (τ : D.what₂.Tau) (P Q : ℕ) (hm : P + Q ≤ m) (hPn : P ≤ n) (hQn : Q ≤ n) (ap am : ℕ → ℕ) :
    fockF (deltaAt (D := D) (m := m) (n := n) τ P ap Q am) (deltaAt τ P ap Q am) =
        ((Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl fun s : Fin P => ap s) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl fun s : Fin P => ap s) :
            ℝ) : ℂ) *
          ((Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl fun s : Fin Q => am s)
            (Formalism.GradedWeylDivisibility.hw ℚ le_rfl fun s : Fin Q => am s) : ℝ) : ℂ) ∧
      deltaAt (D := D) (m := m) (n := n) τ P ap Q am ∈ supported ℂ {v : FVar D m n | v.1 = τ} := by
  unfold deltaAt
  have h1 : P ≤ m := le_trans (Nat.le_add_right P Q) hm
  have hP := plusPart_eq (D := D) τ h1 hPn ap
  have hM := minusPart_pm (D := D) τ P hm hQn am
  have hAB : Disjoint {v : FVar D m n | v.1 = τ ∧ (v.2.1 : ℕ) < P} {v : FVar D m n | v.1 = τ ∧ P ≤ (v.2.1 : ℕ)} := by
    rw [Set.disjoint_left]
    rintro v ⟨-, hv1⟩ ⟨-, hv2⟩
    omega
  have hPmem := psiP_mem_supported (D := D) τ h1 hPn (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun s : Fin P => ap s))
  rw [← hP] at hPmem
  have hMmem := hM.mem (psiM_mem (D := D) τ P hm hQn (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun s : Fin Q => am s)))
  refine ⟨?_, ?_⟩
  · rw [fockF_mul_of_disjoint hAB hPmem hMmem, fockF_pm hM, hP, fockF_psiP, fockF_psiM]
  · exact mul_mem (MvPolynomial.supported_mono (fun v hv => hv.1) hPmem)
      (MvPolynomial.supported_mono (fun v hv => hv.1) hMmem)

theorem fockDeltaLow_core (m n : ℕ) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ)
    (h1 : ∀ τ, p τ + q τ ≤ m) (h2 : ∀ τ, p τ ≤ n ∧ q τ ≤ n) (h3 : ∀ τ, Antitone (ap τ) ∧ Antitone (am τ)) :
    (∏ τ, ((∏ i ∈ Finset.range (p τ), ((ap τ i).factorial : ℝ)) *
        ∏ i ∈ Finset.range (q τ), ((am τ i).factorial : ℝ))) ≤
      (fockF (delta (D := D) (m := m) (n := n) p q ap am) (delta p q ap am)).re := by
  have hA : Pairwise fun τ τ' : D.what₂.Tau => Disjoint {v : FVar D m n | v.1 = τ} {v : FVar D m n | v.1 = τ'} := by
    intro τ τ' hne
    rw [Set.disjoint_left]
    rintro v hv hv'
    exact hne (hv.symm.trans hv')
  have hD := fun τ => deltaAt_fock (D := D) (m := m) (n := n) τ (p τ) (q τ) (h1 τ) (h2 τ).1 (h2 τ).2 (ap τ) (am τ)
  unfold delta
  rw [fockF_prod Finset.univ (fun τ => {v : FVar D m n | v.1 = τ}) hA _ (fun τ => (hD τ).2),
    Finset.prod_congr rfl fun τ _ => (hD τ).1]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_prod, Complex.ofReal_re]
  refine Finset.prod_le_prod (fun τ _ => by positivity) (fun τ _ => ?_)
  have hp := hw_low (p τ) (fun s : Fin (p τ) => ap τ s) (fun a b hab => (h3 τ).1 hab)
  have hq := hw_low (q τ) (fun s : Fin (q τ) => am τ s) (fun a b hab => (h3 τ).2 hab)
  rw [Finset.prod_range (fun i => ((ap τ i).factorial : ℝ)), Finset.prod_range (fun i => ((am τ i).factorial : ℝ))]
  exact mul_le_mul hp hq (by positivity) (le_trans (by positivity) hp)

end Asm

theorem fockDeltaLow (D : D7) : Formalism.IndefR.Fock.Delta.FockDeltaLow D := by
  unfold Formalism.IndefR.Fock.Delta.FockDeltaLow
  intro m n p q ap am h1 h2 h3 _ _
  unfold Formalism.IndefR.Fock.Delta.factProd
  exact fockDeltaLow_core m n p q ap am h1 h2 h3

end Formalism.IndefR.Fock.DeltaPf

end
