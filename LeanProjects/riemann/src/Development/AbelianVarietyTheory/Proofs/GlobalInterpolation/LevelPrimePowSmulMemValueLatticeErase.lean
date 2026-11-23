import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLTwist

noncomputable section

namespace GlobalTheory.LvT.KerLat

open MvPolynomial Formalism.GradedWeylDivisibility

def rowZ (r n : ℕ) : Fin r × Fin n → (Fin r → ℤ) := fun v => Pi.single v.1 1

def Shift {R : Type} [CommRing R] {r n : ℕ} (P : Polynomial (MvPolynomial (Fin r × Fin n) R))
    (μ δ : Fin r → ℤ) : Prop :=
  ∀ k : ℕ, IsWeightedHomogeneous (rowZ r n) (P.coeff k) (μ + k • δ)

theorem shift_mul {R : Type} [CommRing R] {r n : ℕ}
    {P Q : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ μ' δ : Fin r → ℤ}
    (hP : Shift P μ δ) (hQ : Shift Q μ' δ) : Shift (P * Q) (μ + μ') δ := by
  intro k
  rw [Polynomial.coeff_mul]
  refine IsWeightedHomogeneous.sum _ _ _ fun x hx => ?_
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have e : μ + μ' + k • δ = (μ + x.1 • δ) + (μ' + x.2 • δ) := by
    rw [← hx', add_smul]; abel
  rw [e]
  exact (hP x.1).mul (hQ x.2)

theorem shift_one {R : Type} [CommRing R] {r n : ℕ} (δ : Fin r → ℤ) :
    Shift (1 : Polynomial (MvPolynomial (Fin r × Fin n) R)) 0 δ := by
  intro k
  rw [Polynomial.coeff_one]
  split_ifs with h
  · have hk : k = 0 := by omega
    subst hk
    simpa using isWeightedHomogeneous_one R (rowZ r n)
  · exact isWeightedHomogeneous_zero R _ _

theorem shift_pow {R : Type} [CommRing R] {r n : ℕ}
    {P : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ δ : Fin r → ℤ}
    (hP : Shift P μ δ) (e : ℕ) : Shift (P ^ e) (e • μ) δ := by
  induction e with
  | zero => rw [pow_zero, zero_smul]; exact shift_one δ
  | succ e ih => rw [pow_succ, succ_nsmul]; exact shift_mul ih hP

theorem shift_prod {R : Type} [CommRing R] {r n : ℕ} {ι : Type} (s : Finset ι)
    (P : ι → Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ : ι → Fin r → ℤ) (δ : Fin r → ℤ)
    (h : ∀ i ∈ s, Shift (P i) (μ i) δ) : Shift (∏ i ∈ s, P i) (∑ i ∈ s, μ i) δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (shift_one (R := R) (r := r) (n := n) δ)
  | insert i s his IH =>
    rw [Finset.prod_insert his, Finset.sum_insert his]
    exact shift_mul (h i (Finset.mem_insert_self _ _))
      (IH fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem shift_algebraMap {R : Type} [CommRing R] {r n : ℕ} (c : R) (δ : Fin r → ℤ) :
    Shift (algebraMap R (Polynomial (MvPolynomial (Fin r × Fin n) R)) c) 0 δ := by
  intro k
  rw [Polynomial.algebraMap_apply, Polynomial.coeff_C]
  split_ifs with h
  · subst h
    rw [MvPolynomial.algebraMap_eq]
    simpa using isWeightedHomogeneous_C (rowZ r n) c
  · exact isWeightedHomogeneous_zero R _ _

theorem shift_gen {R : Type} [CommRing R] {r n : ℕ} (a b : Fin r) (v : Fin r × Fin n) :
    Shift (Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) :
        Polynomial (MvPolynomial (Fin r × Fin n) R)) (rowZ r n v) (Pi.single a 1 - Pi.single b 1) := by
  intro k
  have hX : IsWeightedHomogeneous (rowZ r n) (X v : MvPolynomial (Fin r × Fin n) R)
      (rowZ r n v) := isWeightedHomogeneous_X R _ v
  have hXa : IsWeightedHomogeneous (rowZ r n) (X (a, v.2) : MvPolynomial (Fin r × Fin n) R)
      (rowZ r n (a, v.2)) := isWeightedHomogeneous_X R _ (a, v.2)
  rw [Polynomial.coeff_add]
  refine IsWeightedHomogeneous.add ?_ ?_
  · rw [Polynomial.coeff_C]
    split_ifs with h
    · subst h; simpa using hX
    · exact isWeightedHomogeneous_zero R _ _
  · split_ifs with hb
    · rw [mul_comm, Polynomial.coeff_C_mul_X]
      split_ifs with h
      · subst h
        have e : rowZ r n v + (1 : ℕ) • (Pi.single a 1 - Pi.single b 1 : Fin r → ℤ) = rowZ r n (a, v.2) := by
          simp [rowZ, hb]
        rw [e]; exact hXa
      · exact isWeightedHomogeneous_zero R _ _
    · rw [Polynomial.coeff_zero]
      exact isWeightedHomogeneous_zero R _ _

theorem shift_rowGen_monomial (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r)
    (d : Fin r × Fin n →₀ ℕ) (c : R) :
    Shift (rowGen R a b (monomial d c)) (Finsupp.weight (rowZ r n) d) (Pi.single a 1 - Pi.single b 1) := by
  unfold rowGen
  rw [aeval_monomial, Finsupp.weight_apply, ← zero_add (Finsupp.sum d _)]
  refine shift_mul (shift_algebraMap c _) ?_
  unfold Finsupp.prod Finsupp.sum
  exact shift_prod _ _ _ _ fun v _ => shift_pow (shift_gen a b v) _

theorem rowDiv_shift (R : Type) [CommRing R] {r n : ℕ} (H : Fin r → ℤ) (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (rowZ r n) f H) :
    IsWeightedHomogeneous (rowZ r n) (rowDiv R a b k f) (H + k • (Pi.single a 1 - Pi.single b 1)) := by
  unfold rowDiv
  conv => enter [2, 1, 2]; rw [f.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have := shift_rowGen_monomial R a b d (coeff d f) k
  rwa [hf (mem_support_iff.mp hd)] at this

theorem weight_rowZ {r n : ℕ} (d : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowZ r n) d a = ((Finsupp.weight (rowW r n) d a : ℕ) : ℤ) := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Pi.add_apply, Nat.cast_add, hf, hg]
  | single v c =>
    simp [Finsupp.weight_apply, rowZ, rowW, Pi.single_apply, Finsupp.sum_single_index]

theorem weight_rowW {r n : ℕ} (d : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r n) d a = rowDeg d a := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp [rowDeg]
  | add f g hf hg => simp only [map_add, Pi.add_apply, hf, hg, rowDeg, Finsupp.add_apply, Finset.sum_add_distrib]
  | single v c =>
    obtain ⟨b, s⟩ := v
    by_cases h : a = b
    · subst h
      simp [Finsupp.weight_apply, rowDeg, rowW, Finsupp.sum_single_index, Finsupp.single_apply]
    · simp [Finsupp.weight_apply, rowDeg, rowW, Finsupp.sum_single_index, Finsupp.single_apply, h, Ne.symm h]

theorem word_homog (R : Type) [CommRing R] {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν)
    (w : List (Fin n × Fin n × ℕ)) :
    ∃ H, IsWeightedHomogeneous (rowZ n n) (applyWord R w (hw R le_rfl ν)) H := by
  induction w with
  | nil =>
    refine ⟨fun a => (rowNu (r := n) ν a : ℤ), fun d hd => ?_⟩
    have := hwRowWeight R n n le_rfl ν hν hd
    funext a
    rw [weight_rowZ, this]
  | cons x w ih =>
    obtain ⟨H, hH⟩ := ih
    exact ⟨_, rowDiv_shift R H _ _ _ _ hH⟩

theorem word_weight {n : ℕ} (hn : 0 < n) (ν : Fin n → ℕ) (hν : Antitone ν)
    (w : List (Fin n × Fin n × ℕ)) :
    ∃ μ : Fin n → ℕ, μ ⟨0, hn⟩ ≤ ν ⟨0, hn⟩ ∧
      IsWeightedHomogeneous (rowW n n) (applyWord ℂ w (hw ℂ le_rfl ν)) μ := by
  by_cases h0 : applyWord ℂ w (hw ℂ le_rfl ν) = 0
  · exact ⟨0, Nat.zero_le _, by rw [h0]; exact isWeightedHomogeneous_zero _ _ _⟩
  obtain ⟨m, hm⟩ := ne_zero_iff.mp h0
  obtain ⟨H, hH⟩ := word_homog ℂ ν hν w
  refine ⟨Finsupp.weight (rowW n n) m, ?_, fun d hd => ?_⟩
  · have e : applyWord ℂ w (hw ℂ le_rfl ν) = map (Int.castRingHom ℂ) (applyWord ℤ w (hw ℤ le_rfl ν)) := by
      rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]
    have hm' : m ∈ (applyWord ℤ w (hw ℤ le_rfl ν)).support := by
      rw [mem_support_iff]
      intro h
      apply hm
      rw [e, coeff_map, h, map_zero]
    have hd := (dualWeylDominanceZ n n ν le_rfl hν _
      (weylLeDual ℤ n n le_rfl ν hν (Submodule.subset_span ⟨w, rfl⟩)) m hm').1 1
    have hs : (Finset.univ.filter fun a : Fin n => a.val < 1) = {⟨0, hn⟩} := by
      ext a; simp [Fin.ext_iff]
    rw [hs, Finset.sum_singleton, Finset.sum_singleton] at hd
    rw [weight_rowW]
    simpa [rowNu, hn] using hd
  · funext a
    have := congrFun ((hH hd).trans (hH hm).symm) a
    rw [weight_rowZ, weight_rowZ] at this
    exact_mod_cast this

open Formalism.BasicNotions

def roundL (R : Type) [CommRing R] (n : ℕ) (lam : DomWeight n) (g : GL (Fin n) R) :
    MvPolynomial (Fin n × Fin n) R →ₗ[R] MvPolynomial (Fin n × Fin n) R :=
  detPow R n g (-lam.detShift) • (Formalism.UG.dwAct R n n g).toLinearMap

theorem roundL_coe (R : Type) [CommRing R] (n : ℕ) (lam : DomWeight n) (g : GL (Fin n) R) :
    (fun f => roundL R n lam g f) = roundAct R n lam g := rfl

def dq (K : Type) [CommRing K] {n : ℕ} (hn : 0 < n) (t : Kˣ) : GL (Fin n) K :=
  diagGL K n (Function.update 1 ⟨0, hn⟩ t)

theorem roundAct_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} (lam : DomWeight n)
    (k : GL (Fin n) R) (g : MvPolynomial (Fin n × Fin n) R) :
    roundAct S n lam (Matrix.GeneralLinearGroup.map φ k) (map φ g) = map φ (roundAct R n lam k g) := by
  have hd : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map φ k) =
      Units.map φ.toMonoidHom (Matrix.GeneralLinearGroup.det k) := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, Matrix.GeneralLinearGroup.val_det_apply]
    exact (φ.map_det (k : Matrix (Fin n) (Fin n) R)).symm
  unfold roundAct Formalism.UG.dwAct
  rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C, ldtwist_map_rowAct, ← map_inv, detPow, detPow, hd,
    ← map_zpow, Units.coe_map]
  rfl

theorem roundAct_mem (R : Type) [CommRing R] {n : ℕ} (lam : DomWeight n)
    (k : GL (Fin n) R) (g : MvPolynomial (Fin n × Fin n) R) (hg : g ∈ delSq R n lam) :
    roundAct R n lam k g ∈ delSq R n lam :=
  Submodule.smul_mem _ _ (Formalism.UG.Final.WeylGLStable R n n le_rfl _ _ g hg)

theorem diag_step {R : Type} [CommRing R] (φ : R →+* ℂ) {n : ℕ} (hn : 0 < n) (lam : DomWeight n) (T : ℕ)
    (t : ℂˣ) (ht : (t : ℂ) = T) (g : MvPolynomial (Fin n × Fin n) R) (hg : g ∈ delSq R n lam) :
    ∃ g' ∈ delSq R n lam,
      ((T : ℂ) ^ lam.w ⟨0, hn⟩) • roundAct ℂ n lam (dq ℂ hn t) (map φ g) = map φ g' := by
  induction hg using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    obtain ⟨μ, hμ, hh⟩ := word_weight hn lam.natW (factNatW n lam).1 w
    refine ⟨((T : R) ^ (lam.natW ⟨0, hn⟩ - μ ⟨0, hn⟩)) • applyWord R w (hw R le_rfl lam.natW),
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, rfl⟩), ?_⟩
    have hdet : Matrix.GeneralLinearGroup.det (dq ℂ hn t) = t := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply]
      show (Matrix.diagonal fun a => (((Function.update (1 : Fin n → ℂˣ) ⟨0, hn⟩ t a : ℂˣ)) : ℂ)).det = _
      rw [Matrix.det_diagonal, Finset.prod_eq_single ⟨0, hn⟩]
      · simp
      · intro b _ hb; simp [Function.update_of_ne hb]
      · simp
    have hinv : (((dq ℂ hn t)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
        Matrix.diagonal fun a => (((Function.update (1 : Fin n → ℂˣ) ⟨0, hn⟩ t a : ℂˣ)⁻¹ : ℂˣ) : ℂ) := rfl
    have hT : (T : ℂ) ≠ 0 := ht ▸ t.ne_zero
    simp only
    rw [smul_eq_C_mul (a := (T : R) ^ _), map_mul, map_C, ← smul_eq_C_mul, ← lclosedeq_applyWord_map, lclosedeq_hw_map]
    unfold roundAct Formalism.UG.dwAct
    rw [hinv, rowActDiagWeight ℂ n n _ μ _ hh, smul_smul, smul_smul, detPow, hdet,
      Finset.prod_eq_single ⟨0, hn⟩]
    · congr 1
      have h2 := (factNatW n lam).2.1 ⟨0, hn⟩
      simp only [Function.update_self, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, ht, map_pow, map_natCast]
      rw [inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hT, ← zpow_add₀ hT, ← zpow_natCast]
      congr 1
      rw [Nat.cast_sub hμ]
      omega
    · intro b _ hb; simp [Function.update_of_ne hb]
    · simp
  | zero =>
    refine ⟨0, zero_mem _, ?_⟩
    rw [← roundL_coe]; simp
  | add y z _ _ hy hz =>
    obtain ⟨y', hy', ey⟩ := hy
    obtain ⟨z', hz', ez⟩ := hz
    refine ⟨y' + z', add_mem hy' hz', ?_⟩
    rw [map_add, map_add, ← ey, ← ez, ← roundL_coe]
    simp
  | smul a y _ hy =>
    obtain ⟨y', hy', ey⟩ := hy
    refine ⟨a • y', Submodule.smul_mem _ _ hy', ?_⟩
    rw [smul_eq_C_mul (a := a), smul_eq_C_mul (a := a), map_mul, map_mul, map_C, ← smul_eq_C_mul, ← smul_eq_C_mul, ← ey,
      ← roundL_coe]
    simp only [map_smul]
    rw [smul_comm]

section Lattice

variable {q : ℕ} {F : Type} [Field F] {Lc : LocF q F} {n : ℕ}

theorem mem_std (x : Fin n → Lc.K) : x ∈ Lc.std n ↔ ∀ a, x a ∈ Lc.O := by
  simp only [LocF.std, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  refine forall_congr' fun a => ⟨?_, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]; exact y.2

theorem mulVec_std (A : Matrix (Fin n) (Fin n) Lc.K) (hA : ∀ a b, A a b ∈ Lc.O) (x : Fin n → Lc.K)
    (hx : x ∈ Lc.std n) : A.mulVec x ∈ Lc.std n := by
  rw [mem_std] at hx ⊢
  intro a
  rw [Matrix.mulVec, dotProduct]
  exact sum_mem fun b _ => mul_mem (hA a b) (hx b)

theorem single_std (b : Fin n) : (Pi.single b 1 : Fin n → Lc.K) ∈ Lc.std n := by
  rw [mem_std]
  intro a
  rw [Pi.single_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

def unip {K : Type} [CommRing K] (N : Matrix (Fin n) (Fin n) K) (hN : N * N = 0) : GL (Fin n) K where
  val := 1 + N
  inv := 1 - N
  val_inv := by rw [add_mul, mul_sub, mul_sub, hN]; simp
  inv_val := by rw [sub_mul, mul_add, mul_add, hN]; simp

theorem frame_unip {Λ : Submodule Lc.O (Fin n → Lc.K)} {h : GL (Fin n) Lc.K} (hh : Lc.IsFrame n h Λ)
    (N : Matrix (Fin n) (Fin n) Lc.K) (hN : N * N = 0) (hO : ∀ a b, N a b ∈ Lc.O) :
    Lc.IsFrame n (h * unip N hN) Λ := by
  intro x
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, hh]
  show (1 + N).mulVec x ∈ _ ↔ _
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  refine ⟨fun hx => ?_, fun hx => add_mem hx (mulVec_std N hO x hx)⟩
  have h2 := sub_mem hx (mulVec_std N hO _ hx)
  rwa [Matrix.mulVec_add, Matrix.mulVec_mulVec, hN, Matrix.zero_mulVec, add_zero, add_sub_cancel_right] at h2

theorem f_zero (p : LocF.PP Lc n) : p.1.f 0 = 0 := by
  have := p.2.add 0 (zero_mem _) 0 (zero_mem _)
  rw [add_zero] at this
  exact left_eq_add.mp this

theorem f_expand (p : LocF.PP Lc n) {h : GL (Fin n) Lc.K} (hh : Lc.IsFrame n h p.1.L) (x : Fin n → Lc.O) :
    p.1.f ((h : Matrix (Fin n) (Fin n) Lc.K).mulVec fun a => (x a : Lc.K)) =
      ∑ a, Lc.res (x a) * p.1.f ((h : Matrix (Fin n) (Fin n) Lc.K).mulVec (Pi.single a 1)) := by
  have e : (h : Matrix (Fin n) (Fin n) Lc.K).mulVec (fun a => (x a : Lc.K)) =
      ∑ a, x a • (h : Matrix (Fin n) (Fin n) Lc.K).mulVec (Pi.single a 1) := by
    funext b
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply, Subring.smul_def, mul_comm]
  rw [e]
  have hm : ∀ a, (h : Matrix (Fin n) (Fin n) Lc.K).mulVec (Pi.single a 1) ∈ p.1.L :=
    fun a => (hh _).2 (single_std a)
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simpa using f_zero p
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      p.2.add _ (Submodule.smul_mem _ _ (hm a)) _ (sum_mem fun b _ => Submodule.smul_mem _ _ (hm b)),
      p.2.smul _ _ (hm a), ih]

theorem exists_frame_ne (hn : 0 < n) (p : LocF.PP Lc n) : ∃ h : GL (Fin n) Lc.K, Lc.IsFrame n h p.1.L ∧
    p.1.f ((h : Matrix (Fin n) (Fin n) Lc.K).mulVec (Pi.single ⟨0, hn⟩ 1)) ≠ 0 := by
  obtain ⟨h, hh⟩ := p.2.lat
  by_cases h0 : p.1.f ((h : Matrix (Fin n) (Fin n) Lc.K).mulVec (Pi.single ⟨0, hn⟩ 1)) = 0
  swap
  · exact ⟨h, hh, h0⟩
  have hex : ∃ a, p.1.f ((h : Matrix (Fin n) (Fin n) Lc.K).mulVec (Pi.single a 1)) ≠ 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨x, hx⟩ := p.2.ne
    have hxL : x ∈ p.1.L := by_contra fun h' => hx (p.2.off x h')
    have e : (h : Matrix (Fin n) (Fin n) Lc.K).mulVec (((h⁻¹ : GL (Fin n) Lc.K) : Matrix _ _ _).mulVec x) = x := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have hs := (mem_std _).1 ((hh _).1 (e.symm ▸ hxL))
    have := f_expand p hh fun a => ⟨_, hs a⟩
    apply hx
    rw [← e]
    refine this.trans (Finset.sum_eq_zero fun a _ => by rw [hc a, mul_zero])
  obtain ⟨a, ha⟩ := hex
  have hne : a ≠ ⟨0, hn⟩ := fun e => ha (e ▸ h0)
  have hN : (Matrix.single a (⟨0, hn⟩ : Fin n) (1 : Lc.K)) * Matrix.single a (⟨0, hn⟩ : Fin n) (1 : Lc.K) = 0 :=
    Matrix.single_mul_single_of_ne _ _ _ _ hne.symm _
  refine ⟨h * unip _ hN, frame_unip hh _ hN fun c d => ?_, ?_⟩
  · rw [Matrix.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    have e0 : ((unip _ hN : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) =
      1 + Matrix.single a (⟨0, hn⟩ : Fin n) (1 : Lc.K) := rfl
    rw [e0]
    have e : (Matrix.single a (⟨0, hn⟩ : Fin n) (1 : Lc.K)).mulVec (Pi.single ⟨0, hn⟩ 1) = Pi.single a 1 := by
      funext c
      simp [Matrix.single_apply, Pi.single_apply, eq_comm]
    rw [Matrix.add_mulVec, Matrix.one_mulVec, e, Matrix.mulVec_add,
      p.2.add _ ((hh _).2 (single_std _)) _ ((hh _).2 (single_std _)), h0, zero_add]
    exact ha

theorem exists_frame_adapted (hn : 0 < n) (p : LocF.PP Lc n) : ∃ (h : GL (Fin n) Lc.K) (c : F), c ≠ 0 ∧
    Lc.IsFrame n h p.1.L ∧ ∀ x : Fin n → Lc.O,
      p.1.f ((h : Matrix (Fin n) (Fin n) Lc.K).mulVec fun a => (x a : Lc.K)) = Lc.res (x ⟨0, hn⟩) * c := by
  obtain ⟨h, hh, h0⟩ := exists_frame_ne hn p
  set c : Fin n → F := fun a => p.1.f ((h : Matrix (Fin n) (Fin n) Lc.K).mulVec (Pi.single a 1)) with hc
  choose b hb using fun a => Lc.res_surj (-c a / c ⟨0, hn⟩)
  let N₀ : Matrix (Fin n) (Fin n) Lc.O := Matrix.of fun a d => if a = ⟨0, hn⟩ ∧ d ≠ ⟨0, hn⟩ then b d else 0
  let N : Matrix (Fin n) (Fin n) Lc.K := N₀.map Lc.O.subtype
  have hN : N * N = 0 := by
    ext a d
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun e _ => ?_
    by_cases he : e = ⟨0, hn⟩ <;> simp [N, N₀, he]
  refine ⟨h * unip N hN, c ⟨0, hn⟩, h0, frame_unip hh N hN fun a d => (N₀ a d).2, fun x => ?_⟩
  rw [Units.val_mul, ← Matrix.mulVec_mulVec]
  have e : ((unip N hN : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K).mulVec (fun a => (x a : Lc.K)) =
      fun a => ((x a + N₀.mulVec x a : Lc.O) : Lc.K) := by
    show (1 + N).mulVec _ = _
    rw [Matrix.add_mulVec, Matrix.one_mulVec]
    funext a
    simp [N, Matrix.mulVec, dotProduct]
  rw [e, f_expand p hh]
  show ∑ a, Lc.res (x a + N₀.mulVec x a) * c a = _
  simp only [map_add, add_mul, Finset.sum_add_distrib]
  have h0' : c ⟨0, hn⟩ ≠ 0 := h0
  have e2 : ∑ a, Lc.res (N₀.mulVec x a) * c a = ∑ d ∈ Finset.univ.erase ⟨0, hn⟩, -(Lc.res (x d) * c d) := by
    rw [Finset.sum_eq_single ⟨0, hn⟩]
    · rw [Matrix.mulVec, dotProduct, map_sum, Finset.sum_mul, ← Finset.sum_erase (a := ⟨0, hn⟩) _ (by simp [N₀])]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd' := Finset.ne_of_mem_erase hd
      simp only [N₀, Matrix.of_apply, true_and, ne_eq, hd', not_false_eq_true, if_true, map_mul, hb]
      field_simp
    · intro a _ ha
      simp [N₀, Matrix.mulVec, dotProduct, ha]
    · simp
  rw [e2, ← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, hn⟩ : Fin n)), Finset.sum_neg_distrib]
  ring

theorem frame_ker_decomp (hn : 0 < n) (p : LocF.PP Lc n) (h : GL (Fin n) Lc.K)
    (hh : ∀ x, (h : Matrix (Fin n) (Fin n) Lc.K).mulVec x ∈ p.ker ↔ x ∈ Lc.std n) :
    ∃ (h₁ : GL (Fin n) Lc.K) (k : GL (Fin n) Lc.O), Lc.IsFrame n h₁ p.1.L ∧
      h = h₁ * (dq Lc.K hn (Units.mk0 _ Lc.q_ne) * Matrix.GeneralLinearGroup.map Lc.O.subtype k) := by
  obtain ⟨h₁, c, hc, hf, hx⟩ := exists_frame_adapted hn p
  set d := dq Lc.K hn (Units.mk0 _ Lc.q_ne) with hd
  have hdx : ∀ (x : Fin n → Lc.K) a, (d : Matrix (Fin n) (Fin n) Lc.K).mulVec x a =
      if a = ⟨0, hn⟩ then (q : Lc.K) * x a else x a := by
    intro x a
    show (Matrix.diagonal _).mulVec x a = _
    rw [Matrix.mulVec_diagonal]
    split_ifs with ha
    · subst ha; simp
    · simp [Function.update_of_ne ha]
  have h2 : ∀ x, ((h₁ * d : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K).mulVec x ∈ p.ker ↔ x ∈ Lc.std n := by
    intro x
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    constructor
    · rintro ⟨h3, h4⟩
      have hs := (mem_std _).1 ((hf _).1 h3)
      have h5 := (hx fun a => ⟨_, hs a⟩).symm.trans h4
      obtain ⟨y, hy⟩ := (Lc.res_ker _).1 ((mul_eq_zero.1 h5).resolve_right hc)
      rw [mem_std]
      intro a
      by_cases ha : a = ⟨0, hn⟩
      · subst ha
        simp only [hdx, if_true] at hy
        rw [mul_left_cancel₀ Lc.q_ne hy]
        exact y.2
      · have := hs a
        rwa [hdx, if_neg ha] at this
    · intro h3
      rw [mem_std] at h3
      have hs : ∀ a, (d : Matrix (Fin n) (Fin n) Lc.K).mulVec x a ∈ Lc.O := by
        intro a
        rw [hdx]
        split_ifs
        · exact mul_mem (natCast_mem _ _) (h3 a)
        · exact h3 a
      refine ⟨(hf _).2 ((mem_std _).2 hs), (hx fun a => ⟨_, hs a⟩).trans ?_⟩
      rw [(Lc.res_ker _).2 ⟨⟨_, h3 ⟨0, hn⟩⟩, by simp [hdx]⟩, zero_mul]
  have key : ∀ g g' : GL (Fin n) Lc.K,
      (∀ x, (g : Matrix (Fin n) (Fin n) Lc.K).mulVec x ∈ p.ker ↔ x ∈ Lc.std n) →
      (∀ x, (g' : Matrix (Fin n) (Fin n) Lc.K).mulVec x ∈ p.ker ↔ x ∈ Lc.std n) →
      ∀ a b, ((g⁻¹ * g' : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) a b ∈ Lc.O := by
    intro g g' hg hg' a b
    have h3 := (hg' _).2 (single_std b)
    have h4 : ((g⁻¹ * g' : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K).mulVec (Pi.single b 1) ∈ Lc.std n := by
      rw [← hg, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_left]
      exact h3
    have := (mem_std _).1 h4 a
    simpa using this
  have k1 := key _ _ h2 hh
  have k2 := key _ _ hh h2
  have inj : Function.Injective fun A : Matrix (Fin n) (Fin n) Lc.O => A.map Lc.O.subtype :=
    Matrix.map_injective Subtype.val_injective
  let A : Matrix (Fin n) (Fin n) Lc.O := Matrix.of fun a b => ⟨_, k1 a b⟩
  let B : Matrix (Fin n) (Fin n) Lc.O := Matrix.of fun a b => ⟨_, k2 a b⟩
  have eA : A.map Lc.O.subtype = (((h₁ * d)⁻¹ * h : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) := rfl
  have eB : B.map Lc.O.subtype = ((h⁻¹ * (h₁ * d) : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) := rfl
  refine ⟨h₁, ⟨A, B, inj ?_, inj ?_⟩, hf, ?_⟩
  · simp only
    rw [Matrix.map_mul, eA, eB, ← Units.val_mul, Matrix.map_one _ (map_zero _) (map_one _), mul_assoc,
      mul_inv_cancel_left, inv_mul_cancel, Units.val_one]
  · simp only
    rw [Matrix.map_mul, eA, eB, ← Units.val_mul, Matrix.map_one _ (map_zero _) (map_one _), mul_assoc,
      mul_inv_cancel_left, inv_mul_cancel, Units.val_one]
  · rw [← mul_assoc, ← inv_mul_eq_iff_eq_mul]
    apply Units.ext
    exact eA.symm

end Lattice

open Formalism.MainNotions.product_first_zeroth_parts (Ow ten blk IntSpan tenM tenM_apply blk_ten wSh delSq_wSh)

theorem ten_update_mem (D : D7) (w : D.what₂.places.Pl) {n : ℕ} (lam : D.what₂.Tau → DomWeight n)
    {R : Type} [CommRing R] (φ : R →+* ℂ) (hφ : ∀ a, ∃ s ∈ Ow D w, φ a = D.what₂.embLL s)
    [DecidableEq D.what₂.Tau] (f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ) (hf : ∀ τ, f τ ∈ delSq ℤ n (lam τ))
    (τ₀ : D.what₂.Tau) (g : MvPolynomial (Fin n × Fin n) R) (hg : g ∈ delSq R n (lam τ₀)) :
    ∀ r ∈ Ow D w, D.what₂.embLL r •
      ten (Function.update (fun τ => map (Int.castRingHom ℂ) (f τ)) τ₀ (map φ g)) ∈ IntSpan D w lam := by
  induction hg using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    intro r hr
    refine AddSubgroup.subset_closure ⟨r, Function.update f τ₀ (applyWord ℤ v (hw ℤ le_rfl (lam τ₀).natW)), hr, ?_, ?_⟩
    · intro τ
      by_cases h : τ = τ₀
      · subst h
        rw [Function.update_self]
        exact Submodule.subset_span ⟨v, rfl⟩
      · rw [Function.update_of_ne h]; exact hf τ
    · congr 2
      funext τ
      by_cases h : τ = τ₀
      · subst h
        simp only [Function.update_self]
        rw [← lclosedeq_applyWord_map, lclosedeq_hw_map, ← lclosedeq_applyWord_map, lclosedeq_hw_map]
      · simp only [Function.update_of_ne h]
  | zero =>
    intro r _
    rw [map_zero, ← tenM_apply, MultilinearMap.map_update_zero, smul_zero]
    exact zero_mem _
  | add y z _ _ hy hz =>
    intro r hr
    rw [map_add, ← tenM_apply, MultilinearMap.map_update_add, smul_add, tenM_apply, tenM_apply]
    exact add_mem (hy r hr) (hz r hr)
  | smul a y _ hy =>
    intro r hr
    obtain ⟨s, hs, e⟩ := hφ a
    rw [smul_eq_C_mul (a := a), map_mul, map_C, ← smul_eq_C_mul, ← tenM_apply, MultilinearMap.map_update_smul,
      smul_smul, e, ← map_mul, tenM_apply]
    exact hy _ (mul_mem hr hs)

theorem map_int_mem (R : Type) [CommRing R] {n : ℕ} (lam : DomWeight n)
    {f : MvPolynomial (Fin n × Fin n) ℤ} (hf : f ∈ delSq ℤ n lam) : map (Int.castRingHom R) f ∈ delSq R n lam := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    refine Submodule.subset_span ⟨v, ?_⟩
    simp only
    rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hy

end GlobalTheory.LvT.KerLat

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT MvPolynomial KerLat
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw tenM tenM_apply blk_ten delSq_wSh)

theorem pow_smul_mem_valB_erase : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (Co : M.Coord), Co.Ok → ∀ w, OverT X w → X.fm.seenP w = true → ∀ (V : Finset X.A.vT) (v : X.A.vT), v ∈ V → ∀ p, ∀ y ∈ Co.valB w V p, ((X.A.T : ℂ) ^ (PtModel.lamT X i (X.fm.tauOf w v)).w ⟨0, D.R.N_pos i⟩) • y ∈ Co.valB w (V.erase v) p := by
  intro D u X i M Co _ w hw hs V v hv p y hy
  obtain ⟨h, hh, z, hz, hy⟩ := hy
  have hhv := hh v
  rw [if_neg (fun h' => h'.2 hv)] at hhv
  obtain ⟨h₁, k, hf, hdec⟩ := frame_ker_decomp (D.R.N_pos i) (p.2 v) (h v) hhv
  let ψ : (M.Lc v).K →+* ℂ := D.what₂.embLL.comp (Co.j w v)
  let φ : (M.Lc v).O →+* ℂ := ψ.comp (M.Lc v).O.subtype
  have hφ : ∀ a, ∃ s ∈ Ow D w, φ a = D.what₂.embLL s :=
    fun a => ⟨Co.j w v a, (Co.j_int w hw v a).2 a.2, rfl⟩
  have hT : (X.A.T : ℂ) ≠ 0 := by
    have := (M.Lc v).q_ne
    intro h0
    apply this
    exact (congrArg Nat.cast (Nat.cast_eq_zero.1 h0)).trans Nat.cast_zero
  have hmv0 : ∀ g : ∀ v, GL (Fin (D.R.N i)) (M.Lc v).K,
      Co.mv w g (X.fm.tauOf w v) = Matrix.GeneralLinearGroup.map ψ (g v) := by
    intro g
    have : ∀ v', v' = v → Matrix.GeneralLinearGroup.map (D.what₂.embLL.comp (Co.j w v')) (g v') =
        Matrix.GeneralLinearGroup.map ψ (g v) := by
      rintro _ rfl; rfl
    simp only [PtModel.Coord.mv, hs, if_true]
    exact this _ (Equiv.symm_apply_apply _ _)
  have hmv1 : ∀ τ, τ ≠ X.fm.tauOf w v → Co.mv w (Function.update h v h₁) τ = Co.mv w h τ := by
    intro τ hτ
    have hne : (X.fm.tauOf w).symm τ ≠ v := fun e => hτ (by rw [← e, Equiv.apply_symm_apply])
    simp only [PtModel.Coord.mv, Function.update_of_ne hne]
  have hdq : Matrix.GeneralLinearGroup.map ψ (dq (M.Lc v).K (D.R.N_pos i) (Units.mk0 _ (M.Lc v).q_ne)) =
      dq ℂ (D.R.N_pos i) (Units.mk0 _ hT) := by
    apply Units.ext
    show (Matrix.diagonal _).map ψ = Matrix.diagonal _
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1
    funext a
    by_cases ha : a = ⟨0, D.R.N_pos i⟩
    · subst ha; simp
    · simp [Function.update_of_ne ha]
  have hmov : ∀ (g : ∀ v, GL (Fin (D.R.N i)) (M.Lc v).K) f, Co.mov w g (ten f) =
      ten fun τ => roundAct ℂ _ (PtModel.lamT X i τ) (Co.mv w g τ) (f τ) := fun g f =>
    blk_ten (fun τ => roundL ℂ _ (PtModel.lamT X i τ) (Co.mv w g τ)) f
  have key : ∀ z ∈ IntSpan D w (X.fm.lam i), ∃ z' ∈ IntSpan D w (X.fm.lam i),
      ((X.A.T : ℂ) ^ (PtModel.lamT X i (X.fm.tauOf w v)).w ⟨0, D.R.N_pos i⟩) • Co.mov w h z =
        Co.mov w (Function.update h v h₁) z' := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨r, f, hr, hfm, rfl⟩ := hz
      have e0 : delSq (M.Lc v).O _ (PtModel.lamT X i (X.fm.tauOf w v)) =
          delSq (M.Lc v).O _ (X.fm.lam i (X.fm.tauOf w v)) := delSq_wSh _ _ _
      have m1 := map_int_mem (M.Lc v).O _ (hfm (X.fm.tauOf w v))
      rw [← e0] at m1
      obtain ⟨g', hg', eg⟩ := diag_step φ (D.R.N_pos i) _ X.A.T (Units.mk0 _ hT) rfl _ (roundAct_mem _ _ k _ m1)
      rw [e0] at hg'
      refine ⟨_, ten_update_mem D w (X.fm.lam i) φ hφ f hfm _ g' hg' r hr, ?_⟩
      rw [map_smul, map_smul, smul_comm, hmov, hmov]
      congr 1
      rw [← tenM_apply, ← tenM_apply, ← Function.update_eq_self (X.fm.tauOf w v)
        (fun τ => roundAct ℂ _ (PtModel.lamT X i τ) (Co.mv w h τ) (map (Int.castRingHom ℂ) (f τ))),
        ← MultilinearMap.map_update_smul]
      congr 1
      funext τ
      by_cases hτ : τ = X.fm.tauOf w v
      · subst hτ
        simp only [Function.update_self]
        rw [hmv0, hmv0, Function.update_self, ← eg, ← roundAct_map, map_map,
          RingHom.ext_int (φ.comp _) (Int.castRingHom ℂ), hdec, map_mul, map_mul, hdq,
          (factSqActMul ℂ _ _ _ _ _).2, (factSqActMul ℂ _ _ _ _ _).2,
          ← roundL_coe ℂ _ _ (Matrix.GeneralLinearGroup.map ψ h₁)]
        simp only [map_smul]
        rfl
      · simp only [Function.update_of_ne hτ, hmv1 τ hτ]
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha', ea⟩ := ha
      obtain ⟨b', hb', eb⟩ := hb
      exact ⟨a' + b', add_mem ha' hb', by rw [map_add, map_add, smul_add, ea, eb]⟩
    | neg a _ ha =>
      obtain ⟨a', ha', ea⟩ := ha
      exact ⟨-a', neg_mem ha', by rw [map_neg, map_neg, smul_neg, ea]⟩
  obtain ⟨z', hz', ez⟩ := key z hz
  refine ⟨Function.update h v h₁, fun v' => ?_, z', hz', by rw [map_smul, hy, ez]⟩
  by_cases hv' : v' = v
  · subst hv'
    rw [Function.update_self, if_pos ⟨hs, Finset.notMem_erase _ _⟩]
    exact hf
  · rw [Function.update_of_ne hv']
    have := hh v'
    simpa only [Finset.mem_erase, ne_eq, hv', not_false_eq_true, true_and] using this

end GlobalTheory.LvT
