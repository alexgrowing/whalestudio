import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCN

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

theorem pos_trace {m n : ℕ} {m' n' : Type} [Fintype m'] [Fintype n'] (P : Matrix m' (Fin m) ℂ) (P' : Matrix (Fin m) m' ℂ)
    (hP : P' * P = 1) (Q : Matrix (Fin n) n' ℂ) (Q' : Matrix n' (Fin n) ℂ) (hQ : Q * Q' = 1) (X : Matrix (Fin m) (Fin n) ℂ) :
    0 ≤ (Xᴴ * (Pᴴ * P) * X * (Q * Qᴴ)).trace.re ∧ ((Xᴴ * (Pᴴ * P) * X * (Q * Qᴴ)).trace.re = 0 → X = 0) := by
  have e : (Xᴴ * (Pᴴ * P) * X * (Q * Qᴴ)).trace = ((P * X * Q)ᴴ * (P * X * Q)).trace := by
    rw [← Matrix.mul_assoc _ Q, Matrix.trace_mul_comm]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have e2 : ∀ Y : Matrix m' n' ℂ, (Yᴴ * Y).trace.re = ∑ j, ∑ i, Complex.normSq (Y i j) := fun Y => by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  rw [e, e2]
  refine ⟨Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _, fun h => ?_⟩
  have h0 : P * X * Q = 0 := by
    ext i j
    have a := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _).1 h j
      (Finset.mem_univ j)
    exact Complex.normSq_eq_zero.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _).1 a i (Finset.mem_univ i))
  calc X = (P' * P) * X * (Q * Q') := by rw [hP, hQ, Matrix.one_mul, Matrix.mul_one]
    _ = P' * (P * X * Q) * Q' := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h0, Matrix.mul_zero, Matrix.zero_mul]

theorem cartan {n p q : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : IsUnit H.det) (e : Fin n ≃ Fin p ⊕ Fin q)
    (A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) (hA : Aᴴ * Formalism.UG.Jpq p q * A = H) :
    ∃ (s : Matrix (Fin n) (Fin n) ℂ) (A' : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ), A' * A = 1 ∧ H * s = Aᴴ * A ∧
      sᴴ * H * s = H ∧ s * s = 1 ∧ ∀ (b : Mat p q) k, IsKC b → b * A = A * k → s * k = k * s := by
  have J2 : Formalism.UG.Jpq p q * Formalism.UG.Jpq p q = 1 := Formalism.MainNotions.DIV.Inh.Jm_sq p q
  have Jh : (Formalism.UG.Jpq p q)ᴴ = Formalism.UG.Jpq p q := by simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]
  have a1 : H⁻¹ * (Aᴴ * Formalism.UG.Jpq p q) * A = 1 := by rw [Matrix.mul_assoc, hA, Matrix.nonsing_inv_mul _ hH]
  have a2 := (Matrix.mul_eq_one_comm_of_equiv e).1 a1
  generalize H⁻¹ * (Aᴴ * Formalism.UG.Jpq p q) = A' at a1 a2
  have b : A * (A' * Formalism.UG.Jpq p q * A) = Formalism.UG.Jpq p q * A := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, a2, Matrix.one_mul]
  have canc : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, A * X = A * Y → X = Y := fun X Y h => by
    rw [← Matrix.one_mul X, ← Matrix.one_mul Y, ← a1, Matrix.mul_assoc, Matrix.mul_assoc, h]
  refine ⟨A' * Formalism.UG.Jpq p q * A, A', a1, ?_, ?_, canc _ _ ?_, fun c k hc h => canc _ _ ?_⟩
  · rw [← hA, Matrix.mul_assoc, b, Matrix.mul_assoc, ← Matrix.mul_assoc (Formalism.UG.Jpq p q), J2, Matrix.one_mul]
  · generalize A' * Formalism.UG.Jpq p q * A = s at b
    calc sᴴ * H * s = (A * s)ᴴ * Formalism.UG.Jpq p q * (A * s) := by
          rw [← hA]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Aᴴ * (Formalism.UG.Jpq p q * Formalism.UG.Jpq p q) * Formalism.UG.Jpq p q * A := by
          rw [b, Matrix.conjTranspose_mul, Jh]; simp only [Matrix.mul_assoc]
      _ = H := by rw [J2, Matrix.mul_one, hA]
  · rw [← Matrix.mul_assoc, b, Matrix.mul_assoc, b, ← Matrix.mul_assoc, J2, Matrix.one_mul, Matrix.mul_one]
  · have hc' : Formalism.UG.Jpq p q * c = c * Formalism.UG.Jpq p q := by
      ext x y
      rcases x with x | x <;> rcases y with y | y
      · simp [Formalism.UG.Jpq, Matrix.mul_apply, Matrix.one_apply]
      · simp [Formalism.UG.Jpq, Matrix.mul_apply, Matrix.one_apply, hc (Sum.inl x) (Sum.inr y) (fun h => h)]
      · simp [Formalism.UG.Jpq, Matrix.mul_apply, Matrix.one_apply, hc (Sum.inr x) (Sum.inl y) (fun h => h)]
      · simp [Formalism.UG.Jpq, Matrix.mul_apply, Matrix.one_apply]
    generalize A' * Formalism.UG.Jpq p q * A = s at b
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, b, ← h, Matrix.mul_assoc, Matrix.mul_assoc, b, ← h, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hc']

theorem cont_act {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {m n : ℕ} (c : R)
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) :
    Continuous fun x : Matrix (Fin m) (Fin n) R => c • (A * x * B) :=
  ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).const_smul c

theorem quadruple_sum_map_zero {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m n : ℕ} (a : Fin m → Fin n → Fin m → Fin n → R)
    (y : Matrix (Fin m) (Fin n) R) (h : ∀ k l, f (y k l) = 0) : f (∑ i, ∑ j, ∑ k, ∑ l, a i j k l * y k l) = 0 := by
  simp only [map_sum, map_mul, h, mul_zero, Finset.sum_const_zero]

theorem alg_trace_gen {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (h : ∀ e, algebraMap F E (Algebra.trace F E e) = e + σ e) (z : R ⊗[F] E) :
    algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) z) = z + sigR R σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, add_add_add_comm]
  | tmul a e =>
    have h4 : (a ⊗ₜ[F] e : R ⊗[F] E) = a • inclR R e := by
      show _ = a • ((1 : R) ⊗ₜ[F] e)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h5 : sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := rfl
    rw [h5, ← TensorProduct.tmul_add, ← h, h4, map_smul, trace_gen, smul_eq_mul, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, Algebra.algebraMap_eq_smul_one (A := E), ← TensorProduct.smul_tmul,
      Algebra.smul_def, mul_comm]

end Gen

variable {D : D7}

theorem real_pt (V : HSp D) (z : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hz : ∀ τ, (z τ)ᴴ * gramAt D V τ * z τ = gramAt D V τ) :
    ∃ h ∈ GinfC V, ∀ τ, (mt V h).map (cmpAt D τ) = z τ := by
  classical
  have key : ∀ S : Finset D.what₂.Tau, ∃ h ∈ GinfC V, ∀ τ, (mt V h).map (cmpAt D τ) = if τ ∈ S then z τ else 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, one_mem _, fun τ => (infMat_one (th0 D τ) V).trans (if_neg (Finset.notMem_empty τ)).symm⟩
    | insert σ S hσ ih =>
      obtain ⟨h, a, b⟩ := ih
      have s := atTau_spec (atTauU D) (hz σ)
      refine ⟨atTau (th0 D) V σ (z σ) * h, mul_mem s.1 a, fun τ => ?_⟩
      rw [← infMat_eq, infMat_mul, infMat_eq V τ h, b]
      by_cases e : τ = σ
      · subst e
        rw [s.2.1, if_neg hσ, if_pos (Finset.mem_insert_self _ _), Matrix.mul_one]
      · rw [s.2.2 τ e, Matrix.one_mul]
        simp [e]
  obtain ⟨h, a, b⟩ := key Finset.univ
  exact ⟨h, a, fun τ => (b τ).trans (if_pos (Finset.mem_univ τ))⟩

theorem inf_ext {V : HSp D} {g h : GA D V} (hg : g ∈ GinfC V) (hh : h ∈ GinfC V)
    (e : ∀ τ, (mt V g).map (cmpAt D τ) = (mt V h).map (cmpAt D τ)) : g = h := by
  have a : finHom V g = 1 := hg
  have b : finHom V h = 1 := hh
  exact Subtype.ext (Units.ext (mat_ext (M := mt V g) (N := mt V h) e
    ((congrArg Units.val a).trans (congrArg Units.val b).symm)))

theorem cartan_pt (V : HSp D) (hV : V.SigOK) : ∃ s ∈ GinfC V, s * s = 1 ∧
    (∀ k, IsKinf (th0 D) V (cptC V) k → s * k = k * s) ∧
    ∀ τ, gramAt D V τ * (mt V s).map (cmpAt D τ) = (cptC V τ)ᴴ * cptC V τ ∧
      ∃ A' : Matrix (Fin V.rank) (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) ℂ, A' * cptC V τ = 1 := by
  choose z A' h1 h2 h3 h4 h5 using fun τ =>
    cartan (gramAt D V τ) (gramAt_unit V τ) (hV (tauE D τ)).choose (cptC V τ) (cptC_gram V hV τ)
  obtain ⟨s, a, b⟩ := real_pt V z h3
  refine ⟨s, a, inf_ext (mul_mem a a) (one_mem _) fun τ => ?_, fun k hk => inf_ext (mul_mem a hk.1) (mul_mem hk.1 a) fun τ => ?_,
    fun τ => ⟨by rw [b, h2], A' τ, h1 τ⟩⟩
  · rw [mt_mul, Matrix.map_mul, b, h4]
    exact (infMat_one (th0 D τ) V).symm
  · obtain ⟨c, hc, e⟩ := hk.2 τ
    rw [mt_mul, mt_mul, Matrix.map_mul, Matrix.map_mul, b]
    exact h5 τ c _ hc e

variable {V W : HSp D}

theorem actHom_mul (g g' : GA D V) (h h' : GA D W) (x : WA V W) :
    actHom V W g h (actHom V W g' h' x) = actHom V W (g * g') (h * h') x := by
  unfold actHom cM
  split_ifs <;> simp only [mt_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem actHom_one (x : WA V W) : actHom V W 1 1 x = x := by
  have a : mt V 1 = 1 := rfl
  have b : mt W 1 = 1 := rfl
  unfold actHom cM
  rw [a, b, Matrix.map_one _ (cA D).map_zero (cA D).map_one, Matrix.map_one _ (cA D).map_zero (cA D).map_one,
    Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, ite_self]

theorem actHom_smul (g : GA D V) (h : GA D W) (c : AE D) (x : WA V W) : actHom V W g h (c • x) = c • actHom V W g h x := by
  unfold actHom
  split_ifs <;> rw [Matrix.mul_smul, Matrix.smul_mul]

theorem actHom_add (g : GA D V) (h : GA D W) (x y : WA V W) :
    actHom V W g h (x + y) = actHom V W g h x + actHom V W g h y := by
  unfold actHom
  split_ifs <;> rw [Matrix.mul_add, Matrix.add_mul]

theorem hHom_smul (c c' : AE D) (x y : WA V W) : hHom V W (c • x) (c' • y) = cA D c * c' * hHom V W x y := by
  unfold hHom
  split_ifs <;>
  · simp only [Finset.mul_sum, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => ?_
    ring

theorem hHom_real {x y : WA V W} (hy : IsRealW V W y) : finPart D (hHom V W x y) = 0 := by
  have e : ∀ k l, finPart D (y k l) = 0 := fun k l => congrFun (congrFun hy k) l
  unfold hHom
  split_ifs <;> exact quadruple_sum_map_zero (finPart D) _ y e

theorem alg_trace (z : AE D) : algebraMap (AF D.host.F) (AE D) (Algebra.trace (AF D.host.F) (AE D) z) = z + cA D z := by
  refine alg_trace_gen D.sp.cm.sig (fun e => ?_) z
  obtain ⟨t, ht⟩ := (D.sp.cm.fixed (e + star e)).1 (by rw [star_add, star_star, add_comm])
  have h1 : Algebra.trace D.host.F D.host.E (star e) = Algebra.trace D.host.F D.host.E e :=
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective D.sp.cm.sig star_involutive.bijective) e
  have h2 := congrArg (Algebra.trace D.host.F D.host.E) ht
  rw [Algebra.trace_algebraMap, D.sp.cm.deg2, LinearMap.map_add, h1, two_smul, ← two_mul, ← two_mul] at h2
  rw [← mul_left_cancel₀ two_ne_zero h2]
  exact ht

theorem realPlace_imaginaryGenerator_re_eq_zero (τ : D.what₂.Tau) : (tauE D τ D.host.xi0).re = 0 := by
  unfold Host.xi0
  rw [map_div₀, map_neg, map_one, map_mul, map_natCast, tauE_sqrtMinusD]
  simp [Complex.div_re]

theorem cmp_hHom (τ : D.what₂.Tau) (x y : WA V W) : cmpAt D τ (hHom V W x y) =
    if V.rank ≤ W.rank then ((x.map (cmpAt D τ))ᴴ * (gramAt D V τ)ᵀ * y.map (cmpAt D τ) * (gramAt D W τ)ᵀ).trace
    else ((x.map (cmpAt D τ))ᴴ * gramAt D V τ * y.map (cmpAt D τ) * gramAt D W τ).trace := by
  unfold hHom
  split_ifs
  · simp only [map_sum, RingHom.map_mul, cmpAt_cA, cmpAt_incA]
    exact sum_eq_trace (starRingEnd ℂ) (gramAt D V τ) (gramAt D W τ) (x.map (cmpAt D τ)) (y.map (cmpAt D τ))
  · simp only [map_sum, RingHom.map_mul, cmpAt_cA, cmpAt_incA]
    exact sum_eq_trace (starRingEnd ℂ) (gramAt D V τ)ᵀ (gramAt D W τ)ᵀ (x.map (cmpAt D τ)) (y.map (cmpAt D τ))

theorem cmp_cM (τ : D.what₂.Tau) {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) :
    (cM M).map (cmpAt D τ) = ((M.map (cmpAt D τ))ᴴ)ᵀ := by
  ext i j
  exact cmpAt_cA τ _

variable (D) in

def iE : AE D := mkAE (fun _ => Complex.I) 0

theorem iE_cmp (τ : D.what₂.Tau) : cmpAt D τ (iE D) = Complex.I := cmpAt_mkAE _ _ τ

theorem iE_fin : finPart D (iE D) = 0 := finPart_mkAE _ _

def fockJ (s : GA D V) (t : GA D W) : WA V W →+ WA V W :=
  AddMonoidHom.mk' (fun x => iE D • actHom V W s t x) fun x y => by rw [actHom_add, smul_add]

theorem fockJ_apply (s : GA D V) (t : GA D W) (x : WA V W) : fockJ s t x = iE D • actHom V W s t x := rfl

theorem fock_pos {s : GA D V} {t : GA D W} (τ : D.what₂.Tau)
    (s4 : gramAt D V τ * (mt V s).map (cmpAt D τ) = (cptC V τ)ᴴ * cptC V τ ∧
      ∃ A' : Matrix (Fin V.rank) (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) ℂ, A' * cptC V τ = 1)
    (t4 : gramAt D W τ * (mt W t).map (cmpAt D τ) = (cptC W τ)ᴴ * cptC W τ ∧
      ∃ A' : Matrix (Fin W.rank) (Fin (W.sig (tauE D τ)).1 ⊕ Fin (W.sig (tauE D τ)).2) ℂ, A' * cptC W τ = 1) (x : WA V W) :
    0 ≤ (cmpAt D τ (hHom V W x (actHom V W s t x))).re ∧
      ((cmpAt D τ (hHom V W x (actHom V W s t x))).re = 0 → x.map (cmpAt D τ) = 0) := by
  obtain ⟨a, A', a'⟩ := s4
  obtain ⟨b, B', b'⟩ := t4
  have hv := gramAt_herm V τ
  have hw := gramAt_herm W τ
  rw [cmp_hHom]
  unfold actHom
  split_ifs
  · have := pos_trace ((cptC V τ)ᴴ)ᵀ (A'ᴴ)ᵀ (by
      rw [← Matrix.transpose_mul, ← Matrix.conjTranspose_mul, a']; simp) (cptC W τ)ᵀ B'ᵀ
      (by rw [← Matrix.transpose_mul, b', Matrix.transpose_one]) (x.map (cmpAt D τ))
    have e1 : (((cptC V τ)ᴴ)ᵀ)ᴴ * ((cptC V τ)ᴴ)ᵀ = (gramAt D V τ)ᵀ * (((mt V s).map (cmpAt D τ))ᴴ)ᵀ := by
      have c := congrArg (fun M => (Mᴴ)ᵀ) a
      simp only [Matrix.conjTranspose_mul, Matrix.transpose_mul, hv, Matrix.conjTranspose_conjTranspose] at c
      rw [c]
      congr 1
      ext i j
      simp
    have e2 : (cptC W τ)ᵀ * ((cptC W τ)ᵀ)ᴴ = ((mt W t).map (cmpAt D τ))ᵀ * (gramAt D W τ)ᵀ := by
      rw [← Matrix.transpose_mul, b, Matrix.transpose_mul]
      rfl
    rw [e1, e2] at this
    rw [Matrix.map_mul, Matrix.map_mul, cmp_cM, Matrix.transpose_map]
    simpa only [Matrix.mul_assoc] using this
  · have := pos_trace (cptC V τ) A' a' (cptC W τ)ᴴ B'ᴴ
      (by rw [← Matrix.conjTranspose_mul, b', Matrix.conjTranspose_one]) (x.map (cmpAt D τ))
    have e2 : (cptC W τ)ᴴ * ((cptC W τ)ᴴ)ᴴ = ((mt W t).map (cmpAt D τ))ᴴ * gramAt D W τ := by
      have c := congrArg Matrix.conjTranspose b
      rw [Matrix.conjTranspose_mul, hw, Matrix.conjTranspose_mul] at c
      exact c.symm
    rw [← a, e2] at this
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, cmp_cM, Matrix.transpose_transpose]
    simpa only [Matrix.mul_assoc] using this

theorem fock_val (s : GA D V) (t : GA D W) (τ : D.what₂.Tau) (x : WA V W) : valTau (th0 D) τ (sympl V W (fockJ s t x) x) =
    -(2 * (tauE D τ D.host.xi0).im * (cmpAt D τ (hHom V W x (actHom V W s t x))).re) := by
  have e := hHom_smul 1 (iE D) x (actHom V W s t x)
  rw [one_smul, RingHom.map_one, one_mul] at e
  show (cmpAt D τ (algebraMap (AF D.host.F) (AE D) (sympl V W (fockJ s t x) x))).re = _
  unfold sympl
  rw [alg_trace, RingHom.map_add, cmpAt_cA, fockJ_apply, e, RingHom.map_mul, RingHom.map_mul, cmpAt_incA, iE_cmp]
  simp only [Complex.add_re, Complex.conj_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, realPlace_imaginaryGenerator_re_eq_zero]
  ring

theorem fock_cont (s : GA D V) (t : GA D W) : Continuous (fockJ s t) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
  show Continuous fun x => iE D • actHom V W s t x
  unfold actHom
  by_cases h : V.rank ≤ W.rank
  · simp only [if_pos h]
    exact cont_act (iE D) (cM (mt V s)) (mt W t).transpose
  · simp only [if_neg h]
    exact cont_act (iE D) (mt V s) (cM (mt W t)).transpose

theorem fock_sq {s : GA D V} {t : GA D W} (s2 : s * s = 1) (t2 : t * t = 1) {x : WA V W} (hx : IsRealW V W x) :
    fockJ s t (fockJ s t x) = -x := by
  rw [fockJ_apply, fockJ_apply, actHom_smul, actHom_mul, s2, t2, actHom_one, smul_smul]
  refine Matrix.ext fun i j => ?_
  have e : finPart D (x i j) = 0 := congrFun (congrFun hx i) j
  show iE D * iE D * x i j = -x i j
  refine ae_ext' (fun τ => ?_) ?_
  · rw [RingHom.map_mul, RingHom.map_mul, iE_cmp, Complex.I_mul_I, RingHom.map_neg, neg_one_mul]
  · rw [RingHom.map_mul, RingHom.map_neg, e, mul_zero, neg_zero]

theorem fock_symp (s : GA D V) (t : GA D W) {x : WA V W} (hx : IsRealW V W x) (y : WA V W) :
    sympl V W (fockJ s t x) (fockJ s t y) = sympl V W x y := by
  have e : cA D (iE D) * iE D * hHom V W y x = hHom V W y x := by
    refine ae_ext' (fun τ => ?_) ?_
    · rw [RingHom.map_mul, RingHom.map_mul, cmpAt_cA, iE_cmp, Complex.conj_I, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
    · rw [RingHom.map_mul, hHom_real hx, mul_zero]
  unfold sympl
  rw [fockJ_apply, fockJ_apply, hHom_smul, hHom_actHom, e]

theorem fockCxEx (D : D7) : FockCxEx D := by
  intro V W _ hV hW
  obtain ⟨s, s1, s2, s3, s4⟩ := cartan_pt V hV
  obtain ⟨t, t1, t2, t3, t4⟩ := cartan_pt W hW
  refine ⟨fockJ s t, fock_cont s t, fun x _ => ?_, fun x hx => fock_sq s2 t2 hx, fun x y hx _ => fock_symp s t hx y,
    fun k k' hk hk' x _ => ?_, -1, Or.inr rfl, fun x hx => ⟨fun τ => ?_, fun h => ?_⟩⟩
  · refine Matrix.ext fun i j => ?_
    show finPart D (iE D * actHom V W s t x i j) = 0
    rw [RingHom.map_mul, iE_fin, zero_mul]
  · rw [fockJ_apply, fockJ_apply, actHom_smul, actHom_mul, actHom_mul, s3 k hk, t3 k' hk']
  · rw [fock_val, neg_one_mul, neg_neg]
    exact mul_nonneg (mul_nonneg zero_le_two (xi_zero_im_pos D τ).le) (fock_pos τ (s4 τ) (t4 τ) x).1
  · refine mat_ext (fun τ => ?_) (hx.trans (Matrix.map_zero _ (RingHom.map_zero _)).symm)
    have e := h τ
    rw [fock_val, neg_eq_zero, mul_eq_zero] at e
    rw [(fock_pos τ (s4 τ) (t4 τ) x).2 (e.resolve_left (mul_pos two_pos (xi_zero_im_pos D τ)).ne'),
      Matrix.map_zero _ (RingHom.map_zero _)]

end Formalism.L2.Fam.ThC

end
