import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasicLift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorRepresentations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAlgebraFacts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftCapelliOperators
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftOfFunctions
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFpmDecay
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.SumFourCommVersion
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.JdPolyOKPolynomialOperators
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorSumPolynomialOperator

namespace GlobalTheory.CapelliLead

open Matrix Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.TL

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A] {R : Type} [CommRing R] [Algebra ℂ R]

def Der (μ : R →ₐ[ℂ] A) (a : A) (x x' : R) : Prop := a * μ x - μ x * a = μ x'

theorem Der.mul {μ : R →ₐ[ℂ] A} {a : A} {x x' y y' : R} (h : Der μ a x x') (h' : Der μ a y y') :
    Der μ a (x * y) (x' * y + x * y') := by
  unfold Der at *
  rw [map_add, map_mul, map_mul, map_mul, ← h, ← h']
  noncomm_ring

theorem der_intCast (μ : R →ₐ[ℂ] A) (a : A) (n : ℤ) : Der μ a n 0 := by
  unfold Der
  rw [map_intCast, map_zero, (Int.cast_commute n a).eq, sub_self]

theorem der_sum {μ : R →ₐ[ℂ] A} {a : A} {ι : Type} (s : Finset ι) {x x' : ι → R}
    (h : ∀ i ∈ s, Der μ a (x i) (x' i)) : Der μ a (∑ i ∈ s, x i) (∑ i ∈ s, x' i) := by
  unfold Der at *
  rw [map_sum, map_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl h

theorem der_prod_zero {μ : R →ₐ[ℂ] A} {a : A} {ι : Type} (s : Finset ι) {x : ι → R}
    (h : ∀ i ∈ s, Der μ a (x i) 0) : Der μ a (∏ i ∈ s, x i) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using der_intCast μ a 1
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    simpa using (h i (by simp)).mul (ih fun j hj => h j (by simp [hj]))

theorem der_det_zero {μ : R →ₐ[ℂ] A} {a : A} {p : ℕ} (M : Matrix (Fin p) (Fin p) R)
    (h : ∀ i j, Der μ a (M i j) 0) : Der μ a M.det 0 := by
  rw [Matrix.det_apply']
  simpa using der_sum Finset.univ fun (σ : Equiv.Perm (Fin p)) _ =>
    (der_intCast μ a (Equiv.Perm.sign σ : ℤ)).mul (der_prod_zero Finset.univ fun i _ => h (σ i) i)

theorem der_det_col {μ : R →ₐ[ℂ] A} {a : A} {p : ℕ} (M : Matrix (Fin p) (Fin p) R) (c : Fin p) (v : Fin p → R)
    (h : ∀ i j, Der μ a (M i j) (if j = c then v i else 0)) : Der μ a M.det (cramer M v c) := by
  rw [cramer_apply, Matrix.det_apply', Matrix.det_apply']
  refine der_sum Finset.univ fun σ _ => ?_
  have h1 : Der μ a (∏ i ∈ Finset.univ.erase c, M (σ i) i) 0 :=
    der_prod_zero _ fun i hi => by simpa [Finset.ne_of_mem_erase hi] using h (σ i) i
  have h2 := (der_intCast μ a (Equiv.Perm.sign σ : ℤ)).mul ((h (σ c) c).mul h1)
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c), ← Finset.mul_prod_erase _ _ (Finset.mem_univ c)]
  have e : ∏ i ∈ Finset.univ.erase c, M.updateCol c v (σ i) i = ∏ i ∈ Finset.univ.erase c, M (σ i) i :=
    Finset.prod_congr rfl fun i hi => by rw [updateCol_ne (Finset.ne_of_mem_erase hi)]
  rw [e, updateCol_self]
  simpa using h2

theorem conj_pow {φ φi x η : A} (h1 : φi * φ = 1) (hx : x * φ - φ * x = η) (hη : η * φ = φ * η) (s : ℕ) :
    φi ^ s * x * φ ^ s = x + (s : ℂ) • (φi * η) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have e : φi ^ (s + 1) * x * φ ^ (s + 1) = φi * (φi ^ s * x * φ ^ s) * φ := by
      rw [pow_succ', pow_succ]; simp only [mul_assoc]
    have e1 : φi * x * φ = x + φi * η := by
      rw [← hx, mul_sub, ← mul_assoc φi φ, h1, one_mul, mul_assoc]; abel
    have e2 : φi * (φi * η) * φ = φi * η := by
      rw [mul_assoc, mul_assoc, hη, ← mul_assoc φi φ, h1, one_mul]
    rw [e, ih, mul_add, add_mul, e1, mul_smul_comm, smul_mul_assoc, e2]
    push_cast
    rw [add_smul, one_smul]; abel

theorem conj_prod {a b : A} (h1 : a * b = 1) (h2 : b * a = 1) (l : List A) :
    a * l.prod * b = (l.map fun x => a * x * b).prod := by
  induction l with
  | nil => simpa using h1
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ← ih]
    calc a * (x * l.prod) * b = a * x * (b * a) * l.prod * b := by rw [h2]; simp only [mul_assoc, one_mul, mul_one]
      _ = _ := by simp only [mul_assoc]

theorem pt_ofFn : ∀ (p : ℕ) (x h : Fin p → A),
    PT p (fun s => (List.ofFn fun k => x k + s • h k).prod) (List.ofFn h).prod
  | 0, x, h => by simpa using PT.const (1 : A)
  | p + 1, x, h => by
    have ih := pt_ofFn p (fun k => x k.succ) (fun k => h k.succ)
    refine ((ih.mulL (x 0)).up.add (ih.mulL (h 0)).mulS).congr (fun s => ?_) ?_
    · simp only [List.ofFn_succ, List.prod_cons, add_mul, smul_mul_assoc]
    · simp only [List.ofFn_succ, List.prod_cons, zero_add]

theorem pt_zero : ∀ d : ℕ, PT d (fun _ => (0 : A)) 0
  | 0 => PT.const 0
  | d + 1 => (pt_zero d).up

theorem pt_sum {ι : Type} (s : Finset ι) {d : ℕ} {f : ι → ℂ → A} {c : ι → A} (h : ∀ i ∈ s, PT d (f i) (c i)) :
    PT d (fun z => ∑ i ∈ s, f i z) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pt_zero d
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (by simp)).add (ih fun j hj => h j (by simp [hj]))

def blk {p t : ℕ} (π : Equiv.Perm (Fin p)) (ρ : Equiv.Perm (Fin t)) : Equiv.Perm (Fin (p + t)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr π ρ)

theorem blk_left {p t : ℕ} (π : Equiv.Perm (Fin p)) (ρ : Equiv.Perm (Fin t)) (i : Fin p) :
    blk π ρ (Fin.castAdd t i) = Fin.castAdd t (π i) := by simp [blk]

theorem blk_right {p t : ℕ} (π : Equiv.Perm (Fin p)) (ρ : Equiv.Perm (Fin t)) (i : Fin t) :
    blk π ρ (Fin.natAdd p i) = Fin.natAdd p (ρ i) := by simp [blk]

theorem blk_sign {p t : ℕ} (π : Equiv.Perm (Fin p)) (ρ : Equiv.Perm (Fin t)) :
    Equiv.Perm.sign (blk π ρ) = Equiv.Perm.sign π * Equiv.Perm.sign ρ := by simp [blk]

theorem alt_average {p t : ℕ} (H : (Fin p → Fin (p + t)) → A) (W : (Fin t → Fin (p + t)) → A) :
    ((p.factorial * t.factorial : ℕ) : ℂ) • ∑ σ : Equiv.Perm (Fin (p + t)), ((Equiv.Perm.sign σ : ℤ) : A) *
        (H (fun i => σ (Fin.castAdd t i)) * W fun i => σ (Fin.natAdd p i)) =
      ∑ σ : Equiv.Perm (Fin (p + t)), ((Equiv.Perm.sign σ : ℤ) : A) *
        ((∑ π : Equiv.Perm (Fin p), ((Equiv.Perm.sign π : ℤ) : A) * H fun i => σ (Fin.castAdd t (π i))) *
          ∑ ρ : Equiv.Perm (Fin t), ((Equiv.Perm.sign ρ : ℤ) : A) * W fun i => σ (Fin.natAdd p (ρ i))) := by
  have key : ∀ (π : Equiv.Perm (Fin p)) (ρ : Equiv.Perm (Fin t)),
      ∑ σ : Equiv.Perm (Fin (p + t)), ((Equiv.Perm.sign σ : ℤ) : A) *
        (H (fun i => σ (Fin.castAdd t i)) * W fun i => σ (Fin.natAdd p i)) =
      ∑ σ : Equiv.Perm (Fin (p + t)), ((Equiv.Perm.sign σ : ℤ) : A) *
        ((((Equiv.Perm.sign π : ℤ) : A) * H fun i => σ (Fin.castAdd t (π i))) *
          (((Equiv.Perm.sign ρ : ℤ) : A) * W fun i => σ (Fin.natAdd p (ρ i)))) := by
    intro π ρ
    rw [← Equiv.sum_comp (Equiv.mulRight (blk π ρ))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Equiv.coe_mulRight, Equiv.Perm.coe_mul, Function.comp, blk_left, blk_right, Equiv.Perm.sign_mul, blk_sign,
      Units.val_mul, Int.cast_mul, ← zsmul_eq_mul, smul_mul_assoc, mul_smul_comm, mul_smul]
    simp only [smul_smul]
    congr 1
    ring
  simp only [Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => arg 2; ext π; rw [Finset.sum_comm]
  simp only [← key, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, smul_smul]
  rw [Nat.cast_smul_eq_nsmul]

theorem lead_std {p t : ℕ} (μ : R →ₐ[ℂ] A) (E : Fin (p + t) → Fin (p + t) → A) (hE : GlRel E)
    (Y : Fin p → Fin (p + t) → R)
    (hY : ∀ i a b c, E a b * μ (Y i c) - μ (Y i c) * E a b = if a = c then -μ (Y i b) else 0)
    (f fi : R) (hf : f = (Matrix.of fun i j : Fin p => Y i (Fin.castAdd t j)).det) (hfi : μ fi * μ f = 1) (u : ℂ) :
    ∃ (F : ℂ → A) (c : A), PT p F c ∧ (∀ s : ℕ, F s = μ fi ^ s * qdet E u * μ f ^ s) ∧
      μ f * c ∈ Submodule.span ℂ {x | ∃ (e : Fin p → Fin (p + t)) (a b : Fin t → Fin (p + t)),
        x = μ (Matrix.of fun i j : Fin p => Y i (e j)).det * qminor E a b u} := by
  set M : Matrix (Fin p) (Fin p) R := Matrix.of fun i j : Fin p => Y i (Fin.castAdd t j) with hM
  have hfi' : μ f * μ fi = 1 := by rw [← map_mul, mul_comm, map_mul, hfi]
  let η : Fin p → Fin (p + t) → R := fun a b => cramer M (fun i => -Y i b) a
  have d1 : ∀ a b, Der μ (E (Fin.castAdd t a) b) f (η a b) := fun a b => by
    rw [hf]
    refine der_det_col M a _ fun i j => ?_
    unfold Der
    rw [hM, Matrix.of_apply, hY]
    by_cases h : j = a
    · simp [h]
    · simp [h, Ne.symm h]
  have d2 : ∀ a b, Der μ (E (Fin.natAdd p a) b) f 0 := fun a b => by
    rw [hf]
    refine der_det_zero M fun i j => ?_
    unfold Der
    rw [hM, Matrix.of_apply, hY, if_neg, map_zero]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have tm : ∀ (w : ℂ) a b x', Der μ (E a b) f x' → ∀ s : ℕ,
      μ fi ^ s * Tm E w a b * μ f ^ s = Tm E w a b + (s : ℂ) • μ (fi * x') := by
    intro w a b x' h s
    rw [map_mul]
    refine conj_pow hfi ?_ (by rw [← map_mul, mul_comm, map_mul]) s
    unfold Der at h
    rw [← h, Tm]
    split_ifs
    · rw [add_mul, mul_add, Algebra.commutes]; abel
    · simp
  let w : Fin (p + t) → ℂ := fun k => u - ((p + t : ℕ) : ℂ) + 1 + ((k : ℕ) : ℂ)
  let W : (Fin t → Fin (p + t)) → A := fun b =>
    (List.ofFn fun k : Fin t => Tm E (w (Fin.natAdd p k)) (Fin.natAdd p k) (b k)).prod
  let H : (Fin p → Fin (p + t)) → A := fun e => (List.ofFn fun k : Fin p => μ (fi * η k (e k))).prod
  refine ⟨fun s => ∑ σ : Equiv.Perm (Fin (p + t)), ((Equiv.Perm.sign σ : ℤ) : A) *
      ((List.ofFn fun k : Fin p => Tm E (w (Fin.castAdd t k)) (Fin.castAdd t k) (σ (Fin.castAdd t k)) +
        s • μ (fi * η k (σ (Fin.castAdd t k)))).prod * W fun i => σ (Fin.natAdd p i)),
    ∑ σ : Equiv.Perm (Fin (p + t)), ((Equiv.Perm.sign σ : ℤ) : A) *
        (H (fun i => σ (Fin.castAdd t i)) * W fun i => σ (Fin.natAdd p i)),
    pt_sum _ fun σ _ => ((pt_ofFn p _ _).mulR _).mulL _, fun s => ?_, ?_⟩
  · have hs1 : μ fi ^ s * μ f ^ s = 1 := by rw [← (show Commute (μ fi) (μ f) from hfi.trans hfi'.symm).mul_pow, hfi, one_pow]
    have hs2 : μ f ^ s * μ fi ^ s = 1 := by rw [← (show Commute (μ f) (μ fi) from hfi'.trans hfi.symm).mul_pow, hfi', one_pow]
    rw [qdet, Formalism.FourierDecayAlt.P.line_form_of_minor A _ _ E hE, qminorRow, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← zsmul_eq_mul, ← zsmul_eq_mul, mul_smul_comm, smul_mul_assoc, conj_prod hs1 hs2, List.map_ofFn, List.ofFn_add,
      List.prod_append]
    congr 2
    · congr 1
      refine List.ofFn_inj.2 (funext fun k => ?_)
      exact (tm _ _ _ _ (d1 k _) s).symm
    · refine congrArg List.prod (List.ofFn_inj.2 (funext fun k => ?_))
      have := tm (w (Fin.natAdd p k)) _ (σ (Fin.natAdd p k)) _ (d2 k _) s
      rw [mul_zero, map_zero, smul_zero, add_zero] at this
      exact this.symm
  · have hne : ((p.factorial * t.factorial : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.mul_pos p.factorial_pos t.factorial_pos).ne'
    rw [← Submodule.smul_mem_iff _ hne, ← mul_smul_comm, alt_average, Finset.mul_sum]
    refine Submodule.sum_mem _ fun σ _ => ?_
    have e1 : (∑ ρ : Equiv.Perm (Fin t), ((Equiv.Perm.sign ρ : ℤ) : A) * W fun i => σ (Fin.natAdd p (ρ i))) =
        qminor E (Fin.natAdd p) (fun i => σ (Fin.natAdd p i)) u := by
      rw [Formalism.FourierDecayAlt.P.line_form_of_minor A _ _ E hE, qminorRow]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      congr 1
      refine congrArg List.prod (List.ofFn_inj.2 (funext fun k => ?_))
      congr 1
      simp only [w, Fin.val_natAdd]
      push_cast; ring
    have e2 : (∑ π : Equiv.Perm (Fin p), ((Equiv.Perm.sign π : ℤ) : A) * H fun i => σ (Fin.castAdd t (π i))) =
        μ (Matrix.of fun a j : Fin p => fi * η a (σ (Fin.castAdd t j))).det := by
      rw [← Matrix.det_transpose, Matrix.det_apply', map_sum]
      refine Finset.sum_congr rfl fun π _ => ?_
      rw [map_mul, map_intCast, ← List.prod_ofFn, map_list_prod, List.map_ofFn]
      rfl
    have e3 : M * (Matrix.of fun a j : Fin p => fi * η a (σ (Fin.castAdd t j))) =
        (-(fi * f)) • Matrix.of fun i j : Fin p => Y i (σ (Fin.castAdd t j)) := by
      ext i j
      have := congrFun (mulVec_cramer M fun i => -Y i (σ (Fin.castAdd t j))) i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, ← hf] at this
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, η]
      calc ∑ x, M i x * (fi * cramer M (fun i => -Y i (σ (Fin.castAdd t j))) x)
          = fi * ∑ x, M i x * cramer M (fun i => -Y i (σ (Fin.castAdd t j))) x := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
        _ = _ := by rw [this]; ring
    have e4 : μ f * μ (Matrix.of fun a j : Fin p => fi * η a (σ (Fin.castAdd t j))).det =
        ((-1 : ℂ) ^ p) • μ (Matrix.of fun i j : Fin p => Y i (σ (Fin.castAdd t j))).det := by
      have := congrArg (fun N => μ (Matrix.det N)) e3
      simp only [Matrix.det_mul, Matrix.det_smul, Fintype.card_fin, map_mul, map_pow, map_neg, hfi, ← hf] at this
      rw [this, Algebra.smul_def, map_pow, map_neg, map_one]
    rw [e1, e2, ← zsmul_eq_mul, mul_smul_comm, ← mul_assoc, e4, smul_mul_assoc]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, _, rfl⟩))

theorem exists_completion {p : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (β : Fin p → V)
    (hβ : LinearIndependent ℂ β) : ∀ t : ℕ, p + t ≤ Module.finrank ℂ V →
      ∃ γ : Fin (p + t) → V, LinearIndependent ℂ γ ∧ ∀ j, γ (Fin.castAdd t j) = β j
  | 0, _ => ⟨β, hβ, fun _ => rfl⟩
  | t + 1, h => by
    obtain ⟨γ, hγ, e⟩ := exists_completion β hβ t (by omega)
    obtain ⟨x, hx⟩ := exists_linearIndependent_snoc_of_lt_finrank hγ (by omega)
    refine ⟨Fin.snoc (α := fun _ => V) γ x, hx, fun j => ?_⟩
    rw [← e j]
    exact Fin.snoc_castSucc (α := fun _ => V) x γ (Fin.castAdd t j)

theorem lead_conj_qdet {n p t : ℕ} (hn : n = p + t) (μ : R →ₐ[ℂ] A) (E : Fin n → Fin n → A) (hE : GlRel E)
    (Y : Fin p → Fin n → R)
    (hY : ∀ i a b c, E a b * μ (Y i c) - μ (Y i c) * E a b = if a = c then -μ (Y i b) else 0)
    (β : Fin p → Fin n → ℂ) (hβ : LinearIndependent ℂ β)
    (f fi : R) (hf : f = (Matrix.of fun i j : Fin p => ∑ c, β j c • Y i c).det) (hfi : μ fi * μ f = 1) (u : ℂ) :
    ∃ (F : ℂ → A) (c : A), PT p F c ∧ (∀ s : ℕ, F s = μ fi ^ s * qdet E u * μ f ^ s) ∧
      μ f * c ∈ Submodule.span ℂ {x | ∃ (γ : Fin p → Fin n → ℂ) (a b : Fin t → Fin n),
        x = μ (Matrix.of fun i j : Fin p => ∑ c, γ j c • Y i c).det * qminor E a b u} := by
  subst hn
  obtain ⟨γ, hγ, e⟩ := exists_completion β hβ t (by simp)
  let Q : Matrix (Fin (p + t)) (Fin (p + t)) ℂ := Matrix.of γ
  have hQ : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hγ)
  have h1 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQ
  have h2 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQ
  obtain ⟨F, c, hF, hs, hc⟩ := lead_std μ (Econj E Q⁻¹ Q) (Formalism.QuantumDeterminants.gl_relation_adjoint_holds A _ E _ _ hE h1)
    (fun i a => ∑ c, Q a c • Y i c) (fun i a b c => by
      have := PI.QnHermHaar.leibVec E (fun c => μ (Y i c)) Q⁻¹ Q h1 (hY i) a b c
      simpa only [PI.QnHermHaar.vecC, map_sum, map_smul] using this) f fi
    (by rw [hf]; simp only [Q, Matrix.of_apply, e]) hfi u
  refine ⟨F, c, hF, fun s => ?_, ?_⟩
  · rw [hs, (Formalism.FourierDecayAlt.P.contractions_covariant A _ E _ _ hE h1 h2 u 0 0 0 0).1]
  · refine Submodule.span_le.2 ?_ hc
    rintro x ⟨e', a, b, rfl⟩
    rw [covariant_linear A _ _ E _ _ h1]
    simp only [Finset.mul_sum, mul_smul_comm]
    exact Submodule.sum_mem _ fun a' _ => Submodule.sum_mem _ fun b' _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨fun j => Q (e' j), a', b', rfl⟩)

end

end GlobalTheory.CapelliLead

namespace GlobalTheory.HatNF.LiftR

open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.TL Formalism.FourierDecayAlt.P.RuleGD
open scoped ContDiff

noncomputable section

section radial

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

theorem nf_zetab {P : M.Par} (d : Q.NFData P A) (hS : IsStarLevel d.L) (hR : d.Rel) (Y : ℂ) :
    d.QQ Y 0 0 * d.L.ζb = d.L.ζb * d.QQ Y 0 0 + d.QQ Y 1 0 ∧ d.QQ Y 0 1 * d.L.ζb = d.L.ζb * d.QQ Y 0 1 + d.QQ Y 1 1 ∧
      Commute (d.QQ Y 1 0) d.L.ζb ∧ Commute (d.QQ Y 1 1) d.L.ζb := by
  have hk : ∀ f, Commute (d.κ f) d.L.ζb := fun f => hR.2.1 f _ (Or.inl (m_ζb d.L))
  have hs : ∀ l, Commute (d.SS l) d.L.ζb := fun l => hR.2.2.1 l _ (Or.inl (Or.inl (m_ζb d.L)))
  have hs' : ∀ l, Commute (star (d.SS l)) d.L.ζb := fun l => by
    have := congrArg star (hR.2.2.1 l _ (Or.inl (Or.inl (m_ζ d.L)))).eq
    rw [star_mul, star_mul, hS.1] at this
    exact this.symm
  have hf : ∀ x ∈ d.L.fns, Commute x d.L.ζb := fun x hx => d.L.fns_comm x hx _ (m_ζb d.L)
  have hG := hf _ (show d.L.GG ∈ d.L.fns by simp [LevelData.fns])
  have hGi := hf _ (m_GGi d.L)
  have hl : Commute (d.L.l0 Y) d.L.ζb :=
    Commute.sub_left (Commute.neg_left d.L.nab_ζb)
      (Commute.mul_left (Algebra.commutes _ _) ((Commute.refl _).mul_left hGi))
  have hm : d.L.m0 Y * d.L.ζb = d.L.ζb * d.L.m0 Y + 1 := by
    have : Commute (algebraMap ℂ A (Y - 1/2) * (d.L.ζ * d.L.GGi)) d.L.ζb :=
      Commute.mul_left (Algebra.commutes _ _) ((hf _ (m_ζ d.L)).mul_left hGi)
    rw [LevelData.m0, sub_mul, this.eq, neg_mul, d.L.nabs_ζb]
    noncomm_ring
  have hx : Commute (d.x Y) d.L.ζb := hk _
  have h21 : Commute (d.weightedSumBis Y) d.L.ζb := Commute.sum_left _ _ _ fun l _ => (hs l).mul_left (hk _)
  have h12 : Commute (d.S12 Y) d.L.ζb := Commute.sum_left _ _ _ fun l _ => (hk _).mul_left (hs' l)
  have h4 : Commute (d.S4 Y) d.L.ζb := Commute.sum_left _ _ _ fun l _ => Commute.sum_left _ _ _ fun j _ =>
    ((hs' l).mul_left (hs j)).mul_left (hk _)
  have step : ∀ a b : A, Commute a d.L.ζb → Commute b d.L.ζb →
      a * d.L.m0 Y * b * d.L.ζb = d.L.ζb * (a * d.L.m0 Y * b) + a * b := fun a b ha hb => by
    rw [mul_assoc _ b, hb.eq, ← mul_assoc, mul_assoc a, hm, mul_add, add_mul, ← mul_assoc a, ha.eq, mul_one]
    simp only [mul_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (d.L.GGi * (d.κ fun ρ => M.wC P ρ Y) + d.L.GG * d.x Y * d.L.m0 Y * d.L.l0 Y +
      d.L.GG * d.L.m0 Y * d.L.GGi * d.weightedSumBis Y + d.S12 Y * d.L.l0 Y + d.L.GGi * d.S4 Y) * d.L.ζb =
      d.L.ζb * (d.L.GGi * (d.κ fun ρ => M.wC P ρ Y) + d.L.GG * d.x Y * d.L.m0 Y * d.L.l0 Y +
      d.L.GG * d.L.m0 Y * d.L.GGi * d.weightedSumBis Y + d.S12 Y * d.L.l0 Y + d.L.GGi * d.S4 Y) +
      (d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y)
    have e := step d.L.GG (d.L.GGi * d.weightedSumBis Y) hG (hGi.mul_left h21)
    rw [← mul_assoc d.L.GG d.L.GGi, d.L.GG_GGi, one_mul, ← mul_assoc] at e
    simp only [add_mul, mul_add]
    rw [(hGi.mul_left (hk _)).eq, step _ _ (hG.mul_left hx) hl, e, (h12.mul_left hl).eq, (hGi.mul_left h4).eq]
    abel
  · show (d.L.GG * d.x Y * d.L.m0 Y + d.S12 Y) * d.L.ζb = d.L.ζb * (d.L.GG * d.x Y * d.L.m0 Y + d.S12 Y) + d.L.GG * d.x Y
    have e := step (d.L.GG * d.x Y) 1 (hG.mul_left hx) (Commute.one_left _)
    simp only [mul_one] at e
    rw [add_mul, mul_add, e, h12.eq]
    abel
  · exact ((hG.mul_left hx).mul_left hl).add_left h21
  · exact hG.mul_left hx

theorem b_top {r : ℕ} (L : LevelData A r) (st : Start A) (h : AHyp L st) (Y : ℂ)
    (c00 : st.QQ Y 0 0 * L.ζb = L.ζb * st.QQ Y 0 0 + st.QQ Y 1 0)
    (a01 : st.QQ Y 0 1 * L.ζb = L.ζb * st.QQ Y 0 1 + st.QQ Y 1 1)
    (b10 : Commute (st.QQ Y 1 0) L.ζb) (b11 : Commute (st.QQ Y 1 1) L.ζb) :
    bP L st Y = (-1 : ℂ) ^ r • ∑ s : Fin (r + 2), ((F7.lagCo (fun j : Fin (r + 2) => ((j : ℕ) : ℝ)) s : ℝ) : ℂ) •
      (L.Dbi ^ (s : ℕ) * cst L st Y * L.Db ^ (s : ℕ)) := by
  have e2 := eff_Drb L
  have e4 := eff_Zb L
  have cc : ∀ s : ℕ, L.Dbi ^ s * cst L st Y * L.Db ^ s =
      L.Avr (Y - s) * (nP L st Y 0 + (s : ℂ) • bP L st Y) + L.Bvr (Y - s) * nP L st Y 1 := by
    intro s
    have hχ : ∀ x, cZb L (cDrb L x) = L.Dbi * x * L.Db := fun x => by
      simp only [cZb, cDrb, cj_apply, LevelData.Dbi, LevelData.Db, mul_assoc]
    have q00 : cZb L (st.QQ Y 0 0) = st.QQ Y 0 0 + L.ζbi * st.QQ Y 1 0 := cj_add _ _ _ _ c00
    have q01 : cZb L (st.QQ Y 0 1) = st.QQ Y 0 1 + L.ζbi * st.QQ Y 1 1 := cj_add _ _ _ _ a01
    have q10 : cZb L (st.QQ Y 1 0) = st.QQ Y 1 0 := cj_fix _ _ _ _ b10.eq
    have q11 : cZb L (st.QQ Y 1 1) = st.QQ Y 1 1 := cj_fix _ _ _ _ b11.eq
    have n1 : cZb L (cDrb L (nP L st Y 1)) = nP L st Y 1 := by
      simp only [nP, map_add, map_mul, (qq_Dr h Y _ _).2, (e2.P Y).1, (e2.P Y).2, (e4.P Y).1, (e4.P Y).2, add_zero, q10, q11]
    have n0 : cZb L (cDrb L (nP L st Y 0)) = nP L st Y 0 + bP L st Y := by
      simp only [bP, nP, map_add, map_mul, (qq_Dr h Y _ _).2, (e2.P Y).1, (e2.P Y).2, (e4.P Y).1, (e4.P Y).2, add_zero,
        q00, q01]
      noncomm_ring
    have nb : cZb L (cDrb L (bP L st Y)) = bP L st Y := by
      rw [bP, map_mul, map_mul, n1, e2.f _ (m_ζbi L), e4.f _ (m_ζbi L)]
    induction s with
    | zero => simp [cst]
    | succ s ih =>
      have : L.Dbi ^ (s + 1) * cst L st Y * L.Db ^ (s + 1) = L.Dbi * (L.Dbi ^ s * cst L st Y * L.Db ^ s) * L.Db := by
        rw [pow_succ', pow_succ]; simp only [mul_assoc]
      rw [this, ih, ← hχ]
      simp only [map_add, map_mul, e2.smul, e4.smul, n0, n1, nb, (e2.M _).1, (e2.M _).2, (e4.M _).1, (e4.M _).2, sub_zero]
      push_cast
      rw [sub_sub, add_smul, one_smul]
      noncomm_ring
  obtain ⟨m0, m1⟩ := ptM L Y
  have := (((m0.mulR (nP L st Y 0)).up.add (m0.mulR (bP L st Y)).mulS).add (m1.mulR (nP L st Y 1)).up).lag
  simp only [cc _, mul_add, mul_smul_comm]
  rw [← this, zero_add, add_zero, ← Algebra.smul_def, smul_smul, ← mul_pow]
  simp

end radial

section group

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OperatorRepresentations

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)}

theorem smooth_of_contDiff {i : Fin (r + 1)} {c : Mx k r → E} (hc : ContDiff ℝ ∞ c) : SmoothLev k r i D c :=
  fun _ _ => ⟨Set.univ, c, isOpen_univ, Set.mem_univ _, hc.contDiffOn, fun _ _ _ => rfl⟩

theorem smooth_inv {i : Fin (r + 1)} {c : Mx k r → ℂ} (hc : SmoothLev k r i D c)
    (h0 : ∀ g ∈ Glev k r i ∩ D, c g ≠ 0) : SmoothLev k r i D (fun g => (c g)⁻¹) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hc g₀ hg₀
  refine ⟨U ∩ F ⁻¹' {0}ᶜ, fun x => (F x)⁻¹, hF.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton,
    ⟨hgU, ?_⟩, (hF.mono Set.inter_subset_left).inv fun x hx => hx.2, fun x hx hxG => by
      show (c x)⁻¹ = (F x)⁻¹
      rw [he x hx.1 hxG]⟩
  show F g₀ ≠ 0
  rw [← he g₀ hgU hg₀.1]
  exact h0 g₀ hg₀

variable (k r D) in

def smAlg : Subalgebra ℂ (Mx k r → ℂ) where
  carrier := {c | SmoothLev k r 0 D c}
  mul_mem' := fun ha hb => smooth_coef ha hb
  add_mem' := fun ha hb => Qx2.smooth_add ha hb
  algebraMap_mem' := fun _ => smooth_of_contDiff contDiff_const

theorem rep_mul (hD : IsOpen D) (c : smAlg k r D) : Rep (opV k r 0 D (mulF (E := E) c.1)) (mulF c.1) :=
  rep_opV hD (good_mulF c.2)

variable (E) in

def mulHom (hD : IsOpen D) : smAlg k r D →ₐ[ℂ] Module.End ℂ (SV k r 0 D E) where
  toFun := fun c => opV k r 0 D (mulF c.1)
  map_one' := (rep_mul hD 1).ext rep_one fun φ g _ => one_smul _ _
  map_mul' := fun a b => (rep_mul hD (a * b)).ext ((rep_mul hD a).mul (rep_mul hD b)) fun φ g _ => mul_smul _ _ _
  map_zero' := (rep_mul hD 0).ext rep_zero fun φ g _ => zero_smul _ _
  map_add' := fun a b => (rep_mul hD (a + b)).ext ((rep_mul hD a).add (rep_mul hD b)) fun φ g _ => add_smul _ _ _
  commutes' := fun c => (rep_mul hD (algebraMap ℂ _ c)).ext (rep_algebraMap c) fun φ g _ => rfl

theorem rep_mulHom (hD : IsOpen D) (c : smAlg k r D) : Rep (mulHom E hD c) (mulF c.1) := rep_mul hD c

theorem invL_apply (v : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) (g : Mx k r) :
    invL k r v p g = ((Hpk k r * gᴴ * Hpk k r) *ᵥ v) p := rfl

theorem inv_leibniz (v : Fin (2 * r + k + 1) → ℂ) {i : Fin (r + 1)} (a b c : Fin (mdim k r i)) (f : Mx k r → E)
    (hf : SmoothLev k r i D f) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    EH k r (posL k r i a) (posL k r i b) (fun x => invL k r v (posL k r i c) x • f x) g =
      invL k r v (posL k r i c) g • EH k r (posL k r i a) (posL k r i b) f g -
        (if a = c then invL k r v (posL k r i b) g • f g else 0) := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  obtain ⟨hX1, hX2⟩ := QnYLeibnizW.hpart_mem (k := k) (r := r) (i := i) a b
  set Z : Mx k r := Matrix.single (posL k r i a) (posL k r i b) 1 with hZdef
  set X1 := hpart1 (Hpk k r) Z with hX1def
  set X2 := hpart2 (Hpk k r) Z with hX2def
  have hf1 := QnYLeibnizW.hasDerivAt_f f F U g X1 hU hgU hg.1 hF hfF hX1
  have hf2 := QnYLeibnizW.hasDerivAt_f f F U g X2 hU hgU hg.1 hF hfF hX2
  have hd : ∀ X : Mx k r, HasDerivAt (fun t : ℝ => invL k r v (posL k r i c) (g * NormedSpace.exp ((t : ℂ) • X)))
      (invL k r v (posL k r i c) (g * X)) 0 := fun X =>
    (invL k r v (posL k r i c)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_mul_exp_smul_zero g X)
  have hv : ∀ X : Mx k r, Xᴴ * Hpk k r + Hpk k r * X = 0 →
      invL k r v (posL k r i c) (g * X) = -(X *ᵥ ((Hpk k r * gᴴ * Hpk k r) *ᵥ v)) (posL k r i c) := by
    intro X hX
    have e : Hpk k r * Xᴴ = -(X * Hpk k r) := by
      have h2 := GBasic.Hpk_sq k r
      calc Hpk k r * Xᴴ = Hpk k r * (Xᴴ * Hpk k r) * Hpk k r := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
        _ = -(X * Hpk k r) := by
            rw [eq_neg_of_add_eq_zero_left hX, Matrix.mul_neg, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.neg_mul]
    rw [invL_apply, Matrix.conjTranspose_mul, ← Matrix.mul_assoc, e, Matrix.mulVec_mulVec]
    simp only [Matrix.neg_mul, Matrix.neg_mulVec, Matrix.mul_assoc, Pi.neg_apply]
  have hsum : invL k r v (posL k r i c) (g * X1) + Complex.I * invL k r v (posL k r i c) (g * X2) =
      -(if a = c then invL k r v (posL k r i b) g else 0) := by
    have h1 : X1 *ᵥ ((Hpk k r * gᴴ * Hpk k r) *ᵥ v) + Complex.I • (X2 *ᵥ ((Hpk k r * gᴴ * Hpk k r) *ᵥ v)) =
        Z *ᵥ ((Hpk k r * gᴴ * Hpk k r) *ᵥ v) := by
      rw [← Matrix.smul_mulVec, ← Matrix.add_mulVec, hX1def, hX2def, QnYLeibnizW.hpart_sum]
    have h2 := congrFun h1 (posL k r i c)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h2
    have hz : (Z *ᵥ ((Hpk k r * gᴴ * Hpk k r) *ᵥ v)) (posL k r i c) =
        if a = c then invL k r v (posL k r i b) g else 0 := by
      rw [hZdef, Matrix.single_mulVec, Function.update_apply]
      by_cases hac : a = c
      · subst hac; simp [invL_apply]
      · rw [if_neg (fun h => hac ((QnYLeibnizW.posL_inj c a).1 h).symm), if_neg hac]; rfl
    rw [hv X1 hX1.1, hv X2 hX2.1, ← hz, ← h2]
    ring
  show RdV X1 (fun x => invL k r v (posL k r i c) x • f x) g +
      Complex.I • RdV X2 (fun x => invL k r v (posL k r i c) x • f x) g =
    invL k r v (posL k r i c) g • (RdV X1 f g + Complex.I • RdV X2 f g) - _
  rw [QnYLeibnizW.rdV_smul_of X1 g _ f _ _ (hd X1) hf1, QnYLeibnizW.rdV_smul_of X2 g _ f _ _ (hd X2) hf2,
    QnYLeibnizW.rdV_of_hasDerivAt X1 g f _ hf1, QnYLeibnizW.rdV_of_hasDerivAt X2 g f _ hf2]
  have e : (if a = c then invL k r v (posL k r i b) g • f g else 0) =
      (if a = c then invL k r v (posL k r i b) g else 0) • f g := by split_ifs <;> simp
  rw [e, sub_eq_add_neg, ← neg_smul, ← hsum]
  module

theorem invL_pd (v : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) :
    U.IsPolyDeg 1 (fun g : Mx k r => invL k r v p g) := by
  simp only [invL_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine PartialDerivativeAlgebra.pd_sum _ fun j _ => PartialDerivativeAlgebra.pd_mono (by norm_num : 1 + 0 ≤ 1) (PartialDerivativeAlgebra.pd_mul ?_ (PartialDerivativeAlgebra.pd_const _ 0))
  refine PartialDerivativeAlgebra.pd_sum _ fun l _ => PartialDerivativeAlgebra.pd_mono (by norm_num : 1 + 0 ≤ 1) (PartialDerivativeAlgebra.pd_mul ?_ (PartialDerivativeAlgebra.pd_const _ 0))
  exact PartialDerivativeAlgebra.pd_sum _ fun m _ => PartialDerivativeAlgebra.pd_mono (by norm_num : 0 + 1 ≤ 1)
    (PartialDerivativeAlgebra.pd_mul (PartialDerivativeAlgebra.pd_const _ 0) (PartialDerivativeAlgebra.pd_star_entry _ _))

def posEquiv (k r : ℕ) : Fin (mdim k r 0) ≃ Fin (2 * r + k + 1) := finCongr (by simp [mdim])

theorem posEquiv_apply (c : Fin (mdim k r 0)) : posEquiv k r c = posL k r 0 c := by
  ext; simp [posEquiv, posL]

theorem flag_cov_indep (z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') (hT' : 0 < Tz k r z') :
    LinearIndependent ℂ fun (j : Fin (r + 1)) (c : Fin (mdim k r 0)) =>
      (star (fvec k r z' j) ᵥ* Hpk k r) (posL k r 0 c) := by
  rw [Fintype.linearIndependent_iff]
  intro w hw
  have h1 : (∑ j, w j • star (fvec k r z' j)) ᵥ* Hpk k r = 0 := by
    funext p
    obtain ⟨c, rfl⟩ := (posEquiv k r).surjective p
    have := congrFun hw c
    rw [posEquiv_apply, Matrix.sum_vecMul]
    simpa only [Finset.sum_apply, Pi.smul_apply, Matrix.smul_vecMul, Pi.zero_apply] using this
  have h2 : ∑ j, w j • star (fvec k r z' j) = 0 := by
    have := congrArg (· ᵥ* Hpk k r) h1
    simpa only [Matrix.vecMul_vecMul, GBasic.Hpk_sq, Matrix.vecMul_one, Matrix.zero_vecMul] using this
  rw [Fin.sum_univ_castSucc] at h2
  have hl : fvec k r z' (Fin.last r) = z' := by simp [fvec]
  have hc : ∀ a : Fin r, fvec k r z' a.castSucc = bvec (eI k r a) := fun a => by simp [fvec]
  simp only [hl, hc] at h2
  have h3 : ∀ a : Fin r, w a.castSucc = 0 := fun a => by
    have := congrFun h2 (eI k r a)
    have hi : ∀ b : Fin r, eI k r a = eI k r b ↔ a = b := fun b => by simp [eI, Fin.ext_iff]
    simpa [bvec, Finset.sum_apply, Pi.single_apply, hi, hz' (eI k r a) (Or.inl a.isLt)] using this
  intro j
  refine Fin.lastCases ?_ h3 j
  simp only [h3, zero_smul, Finset.sum_const_zero, zero_add, smul_eq_zero, star_eq_zero] at h2
  refine h2.resolve_right fun h => ?_
  simp [h, Tz, herm] at hT'

theorem star_zhat (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) (i j : Fin (r + 1)) :
    star (Zhat k r z z' g i j) = ∑ c : Fin (mdim k r 0),
      (star (fvec k r z' j) ᵥ* Hpk k r) (posL k r 0 c) * invL k r (fvec k r z i) (posL k r 0 c) g := by
  have e := (posEquiv k r).sum_comp fun p => (star (fvec k r z' j) ᵥ* Hpk k r) p * invL k r (fvec k r z i) p g
  simp only [posEquiv_apply] at e
  rw [e]
  show star (star (fvec k r z i) ⬝ᵥ (Hpk k r *ᵥ (g *ᵥ fvec k r z' j))) =
    (star (fvec k r z' j) ᵥ* Hpk k r) ⬝ᵥ ((Hpk k r * gᴴ * Hpk k r) *ᵥ fvec k r z i)
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    GBasic.Hpk_sq, Matrix.one_mul, ← Matrix.star_dotProduct, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.conjTranspose_mul, GBasic.Hpk_herm]

def dBar (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) : ℂ := star (Dmin k r z z' g (Fin.last (r + 1)))

theorem dBar_ne {z z' : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') {g : Mx k r}
    (hg : 0 < Gf k r z z' g) : dBar k r z z' g ≠ 0 := by
  intro h
  have h0 : Dmin k r z z' g (Fin.last (r + 1)) = 0 := star_eq_zero.1 h
  unfold Gf at hg
  rw [h0, map_zero] at hg
  nlinarith [mul_nonneg (mul_pos hT hT').le (Complex.normSq_nonneg (Dmin k r z z' g ⟨r, by omega⟩))]

def evAt (g : Mx k r) : smAlg k r D →+* ℂ := (Pi.evalRingHom (fun _ : Mx k r => ℂ) g).comp (smAlg k r D).val.toRingHom

theorem evAt_apply (g : Mx k r) (c : smAlg k r D) : evAt g c = c.1 g := rfl

variable (D) in

def yF (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (c : Fin (mdim k r 0)) : smAlg k r D :=
  ⟨invL k r (fvec k r z i) (posL k r 0 c), smooth_of_contDiff (invL k r (fvec k r z i) (posL k r 0 c)).contDiff⟩

theorem det_yF (z : Fin (2 * r + k + 1) → ℂ) (γ : Fin (r + 1) → Fin (mdim k r 0) → ℂ) (g : Mx k r) :
    ((Matrix.of fun i j : Fin (r + 1) => ∑ c, γ j c • yF D z i c).det).1 g =
      (Matrix.of fun i j : Fin (r + 1) => ∑ c, γ j c * invL k r (fvec k r z i) (posL k r 0 c) g).det := by
  rw [← evAt_apply, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum]
  rfl

variable (E) in

theorem group_identity (z z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (Y : ℂ) : ∃ (m : ℕ) (co : Fin m → Mx k r → ℂ) (a b : Fin m → Fin (r + k) → Fin (2 * r + k + 1)),
      (∀ i, U.IsPolyDeg (r + 1) (co i)) ∧ ∀ F : Mx k r → E, B.CkOn ⊤ (B.GV k r) F → ∀ g ∈ B.GV k r, 0 < Gf k r z z' g →
        ∑ s : Fin (r + 2), ((F7.lagCo (fun j : Fin (r + 2) => ((j : ℕ) : ℝ)) s : ℝ) : ℂ) •
            dBar k r z z' g ^ (r + 1 - (s : ℕ)) • CV k r Y (fun x => dBar k r z z' x ^ (s : ℕ) • F x) g =
          dBar k r z z' g ^ r • ∑ i, co i g • qminorOp (EabH (Hpk k r)) (a i) (b i) (uC k r 0 Y) F g := by
  set D : Set (Mx k r) := {g | 0 < Gf k r z z' g} with hDdef
  have hD : IsOpen D := isOpen_lt continuous_const (BetaSesquilinearity.Gf_cont _ _)
  let β : Fin (r + 1) → Fin (mdim k r 0) → ℂ := fun j c => (star (fvec k r z' j) ᵥ* Hpk k r) (posL k r 0 c)
  let f : smAlg k r D := (Matrix.of fun i j : Fin (r + 1) => ∑ c, β j c • yF D z i c).det
  have hf : ∀ g, f.1 g = dBar k r z z' g := fun g => by
    rw [det_yF, dBar, Dmin, ← Matrix.det_conjTranspose, ← Matrix.det_transpose]
    congr 1
    ext i j
    simp only [Matrix.transpose_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, Matrix.of_apply, star_zhat]
    rfl
  have hne : ∀ g ∈ Glev k r 0 ∩ D, f.1 g ≠ 0 := fun g hg => by rw [hf]; exact dBar_ne hT hT' hg.2
  let fi : smAlg k r D := ⟨fun g => (f.1 g)⁻¹, smooth_inv f.2 hne⟩
  have hfi : mulHom E hD fi * mulHom E hD f = 1 :=
    ((rep_mulHom hD fi).mul (rep_mulHom hD f)).ext rep_one fun φ g hg => by
      show (f.1 g)⁻¹ • f.1 g • φ.1 g = φ.1 g
      rw [smul_smul, inv_mul_cancel₀ (hne g hg), one_smul]
  obtain ⟨Fs, c, hP, hFs, hc⟩ := GlobalTheory.CapelliLead.lead_conj_qdet (p := r + 1) (t := r + k) (by simp [mdim]; omega)
    (mulHom E hD) (EV k r 0 D E) (relation_representation E k r z 0 D hD).1 (yF D z) (fun i a b c => by
      refine (((rep_EV hD a b).mul (rep_mulHom hD (yF D z i c))).sub
        ((rep_mulHom hD (yF D z i c)).mul (rep_EV hD a b))).ext
        ((rep_mulHom hD (yF D z i b)).neg.ite (a = c)) fun φ g hg => ?_
      have h := inv_leibniz (fvec k r z i) a b c φ.1 φ.2.1 g hg
      show EH k r (posL k r 0 a) (posL k r 0 b) (fun x => invL k r (fvec k r z i) (posL k r 0 c) x • φ.1 x) g -
        invL k r (fvec k r z i) (posL k r 0 c) g • EH k r (posL k r 0 a) (posL k r 0 b) φ.1 g =
          if a = c then -(invL k r (fvec k r z i) (posL k r 0 b) g • φ.1 g) else 0
      rw [h]
      split_ifs <;> simp) β (flag_cov_indep z' hz' hT') f fi rfl hfi (uC k r 0 Y)
  obtain ⟨m, w, x, hx⟩ := Submodule.mem_span_set'.1 hc
  choose γ a b hxe using fun i => (x i).2
  refine ⟨m, fun i g => w i * (Matrix.of fun i' j : Fin (r + 1) =>
      ∑ c, γ i j c * invL k r (fvec k r z i') (posL k r 0 c) g).det, fun i => posL k r 0 ∘ a i, fun i => posL k r 0 ∘ b i,
    fun i => ?_, fun F hF g hg hG => ?_⟩
  · refine PartialDerivativeAlgebra.pd_mono (by omega : 0 + (r + 1) ≤ r + 1) (PartialDerivativeAlgebra.pd_mul (PartialDerivativeAlgebra.pd_const _ 0) (PartialDerivativeAlgebra.pd_det _ fun i' j => ?_))
    simp only [Matrix.of_apply]
    exact PartialDerivativeAlgebra.pd_sum _ fun c _ => PartialDerivativeAlgebra.pd_mono (by norm_num : 0 + 1 ≤ 1) (PartialDerivativeAlgebra.pd_mul (PartialDerivativeAlgebra.pd_const _ 0) (invL_pd _ _))
  · have hgm : g ∈ Glev k r 0 ∩ D := ⟨⟨hg, fun a ha => absurd ha (by simp)⟩, hG⟩
    have hFs' : SmoothLev k r 0 D F := fun g₀ hg₀ => by
      obtain ⟨U, F', h1, h2, h3, h4⟩ := hF g₀ hg₀.1.1
      exact ⟨U, F', h1, h2, h3, fun x hx hxG => h4 x hx hxG.1⟩
    rw [hP.lag] at hx
    simp only [hFs, hxe, ← map_pow] at hx
    have r1 := (rep_sum Finset.univ _ _ fun (i : Fin m) _ => ((rep_mulHom (E := E) hD
      (Matrix.of fun i' j : Fin (r + 1) => ∑ c, γ i j c • yF D z i' c).det).mul
        (rep_qminor hD (a i) (b i) (uC k r 0 Y))).smul (w i)).mkV hD hFs' hgm
    have r2 := ((rep_mulHom (E := E) hD f).mul (rep_sum Finset.univ _ _ fun (s : Fin (r + 1 + 1)) _ =>
      (((rep_mulHom (E := E) hD (fi ^ (s : ℕ))).mul (rep_qminor hD id id (uC k r 0 Y))).mul
        (rep_mulHom hD (f ^ (s : ℕ)))).smul
          ((F7.lagCo (fun j : Fin (r + 1 + 1) => ((j : ℕ) : ℝ)) s : ℝ) : ℂ))).mkV hD hFs' hgm
    have e := r1.symm.trans ((congrArg (fun T : Module.End ℂ (SV k r 0 D E) => (T (mkV hD F hFs')).1 g) hx).trans r2)
    simp only [mulF, det_yF, smul_smul] at e
    simp only []
    rw [e, smul_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have e1 : mulF (E := E) (f ^ (s : ℕ)).1 F = fun x => dBar k r z z' x ^ (s : ℕ) • F x := by
      funext x
      rw [← hf]; rfl
    have e2 : (fi ^ (s : ℕ)).1 g = (dBar k r z z' g)⁻¹ ^ (s : ℕ) := by rw [← hf]; rfl
    have h0 := dBar_ne hT hT' hG
    rw [e1, e2, hf, smul_smul, smul_smul]
    congr 1
    rw [pow_sub₀ _ h0 (by have := s.isLt; omega), inv_pow, pow_succ]
    ring

end group

section lift

open Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TLB MeasureTheory

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
  {Bs : B.RealPlaceData P.k P.r Wp Wq} {ε : ℝ}

variable (Bs ε) in

def RadOp (a : RA P Bs) (T : (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ F, JC.NiceCoef Bs ε F → JC.NiceCoef Bs ε (T F) ∧ ∀ Φ, Top.IsRadOf P Bs Φ F → Top.IsRadOf P Bs (a.1 Φ) (T F)

theorem RadOp.mul {a b : RA P Bs} {T S} (h : RadOp Bs ε a T) (h' : RadOp Bs ε b S) :
    RadOp Bs ε (a * b) (fun F => T (S F)) :=
  fun F hF => ⟨(h _ (h' F hF).1).1, fun Φ hΦ => (h _ (h' F hF).1).2 _ ((h' F hF).2 Φ hΦ)⟩

theorem RadOp.add {a b : RA P Bs} {T S} (h : RadOp Bs ε a T) (h' : RadOp Bs ε b S) :
    RadOp Bs ε (a + b) (fun F g => T F g + S F g) := by
  refine fun F hF => ⟨JCx2.mn_nice_add (h F hF).1 (h' F hF).1, fun Φ hΦ x hx => ?_⟩
  show (a.1 Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 + (b.1 Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = _
  rw [(h F hF).2 Φ hΦ x hx, (h' F hF).2 Φ hΦ x hx]
  simp only [Q.resG]
  rw [JCx2.bc_JF_add (h F hF).1 (h' F hF).1 (wCell_om Bs hx), smul_add]

theorem RadOp.smul {a : RA P Bs} {T} (h : RadOp Bs ε a T) (c : ℂ) : RadOp Bs ε (c • a) (fun F g => c • T F g) := by
  refine fun F hF => ⟨JCx2.mn_nice_smul c (h F hF).1, fun Φ hΦ x hx => ?_⟩
  show c • (a.1 Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = _
  rw [(h F hF).2 Φ hΦ x hx]
  simp only [Q.resG]
  rw [JCx2.bc_JF_smul, smul_comm]

theorem radOp_zero : RadOp Bs ε 0 (fun _ _ => 0) := by
  refine fun F _ => ⟨JCx2.mn_nice_zero, fun Φ _ x _ => ?_⟩
  simp only [Q.resG]
  rw [JCx2.bc_JF_zero, smul_zero]
  rfl

theorem radOp_sum {ι : Type} (s : Finset ι) {a : ι → RA P Bs}
    {T : ι → (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (h : ∀ i ∈ s, RadOp Bs ε (a i) (T i)) :
    RadOp Bs ε (∑ i ∈ s, a i) (fun F g => ∑ i ∈ s, T i F g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using radOp_zero
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (by simp)).add (ih fun j hj => h j (by simp [hj]))

theorem jf_dBar_pow (n : ℕ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r) :
    B.JF Bs (fun x => dBar P.k P.r Bs.z Bs.z' x ^ n • F x) g = dBar P.k P.r Bs.z Bs.z' g ^ n • B.JF Bs F g := by
  unfold B.JF besselJ
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [B7.ae_inSS Bs] with p hp
  have h1 := BigCellZetaMinors.dmin_sgs Bs hp g (Fin.last _)
  unfold B.sgs at h1
  simp only [dBar]
  rw [h1, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]

theorem mulAt_db_pow (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (L : LevelData (RA P Bs) P.r)
    (hL : Q.IsActualLevel X L) (n : ℕ) {x : (Fin P.r → ℂ) × Mx P.k P.r} (hx : x ∈ DomR P.k P.r Bs.z Bs.z') :
    MulAt x (L.Db ^ n).1 (dBar P.k P.r Bs.z Bs.z' (wCell P.k P.r (Fin.last P.r) x.1 * x.2) ^ n) := by
  have h1 : MulAt x L.Db.1 (dBar P.k P.r Bs.z Bs.z' (wCell P.k P.r (Fin.last P.r) x.1 * x.2)) := by
    have hzb : MulAt x L.ζb.1 (star (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2)) := by
      rw [hL.2.2.2.2.2.2.2.2.1]; exact act_fn X x hx 2
    rw [dBar, (big_cell_values P.k P.r Wp Wq Bs x hx).2.2.1, star_mul', star_prod]
    exact mulAt_mul (mulAt_ofFn L.cb _ fun l => act_cb X L hL x l) hzb
  induction n with
  | zero => simpa only [pow_zero, pr_one_fst] using mulAt_one x
  | succ n ih => rw [pow_succ, pow_succ]; exact mulAt_mul ih h1

theorem radOp_db_pow (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (L : LevelData (RA P Bs) P.r)
    (hL : Q.IsActualLevel X L) (n : ℕ) :
    RadOp Bs ε (L.Db ^ n) (fun F g => dBar P.k P.r Bs.z Bs.z' g ^ n • F g) := by
  have hp : U.IsPolyDeg (n * (P.r + 1)) (fun g => dBar P.k P.r Bs.z Bs.z' g ^ n) := by
    simpa [dBar] using PartialDerivativeAlgebra.pd_prod (Finset.range n) fun _ _ => dmin_star_pd P.k P.r Bs.z Bs.z' (Fin.last _)
  have hg := CutBP.pd_good_of_poly (Wp := Wp) (Wq := Wq) hp
  refine fun F hF => ⟨⟨hg.1 F hF.1, fun A m => ?_, fun g hg hne => hF.2.2 g hg fun h0 => hne (by simp [h0])⟩,
    fun Φ hΦ x hx => ?_⟩
  · obtain ⟨K, -, hK⟩ := hg.2 A m
    obtain ⟨b, hb⟩ := hF.2.1 (A + (n * (P.r + 1) : ℕ)) m
    exact ⟨_, hK F b hb⟩
  · rw [mulAt_db_pow X L hL n hx, hΦ x hx]
    simp only [Q.resG]
    rw [jf_dBar_pow, smul_comm]

theorem radOp_cap (hε : 0 < ε) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r))
    (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (hD : P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0)
    (Y : ℂ) : RadOp Bs ε (P5.QQi L st 0 Y 0 0) (fun F g => M.sgn P l0 • Q.CV P.k P.r Y F g) := by
  refine fun F hN => ⟨(JCx2.bcGood_tL (Bs := Bs) (ε := ε) (M.sgn P l0) Y 0 0).1 F hN, fun Φ hΦ y hy => ?_⟩
  have hz := Bs.z_mem
  have hz' := Bs.z'_mem
  have hL := hD.2.2.1
  have hJ := bessel_function_finite_class P.k P.r Wp Wq Bs F ε hε hN
  have hh := wCell_om Bs hy
  have h1 := JCx2.rma_QQi X L hL st _ hD.2.2.2.1 Y 0 0 Φ hy
  have h2 := (JCx2.rma_sandw X L hL Y P.r le_rfl _ _ (JCx2.rma_base X Y) (JCx2.rma_QL_loc Y)).2 0 0
    (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) (resG P.k P.r (Fin.last P.r) (B.JF Bs F)) (fun y' hy' => hΦ y' hy') y hy
  have h3 := chain_recursion_all_levels Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' (Fin.last P.r) _ Y 0 0 hz hz'
    (JCx2.rma_isDom_omPlus hz hz') _ hJ y.1 hy.1 y.2 hy.2.1 hh.2
  rw [Fin.val_last] at h3
  have h4 : B.JF Bs (fun g => M.sgn P l0 • Q.CV P.k P.r Y F g) (wCell P.k P.r (Fin.last P.r) y.1 * y.2) =
      M.sgn P l0 • Q.tL P.k P.r Bs.z Bs.z' 0 Y 0 0 (B.JF Bs F) (wCell P.k P.r (Fin.last P.r) y.1 * y.2) :=
    (JCx2.bcGood_tL (Bs := Bs) (ε := ε) (M.sgn P l0) Y 0 0).2.1 F hN _ hh
  refine Eq.trans h1 ?_
  rw [h2, ← h3]
  simp only [Q.resG]
  rw [h4, smul_comm]

theorem db_pow_rh (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r))
    (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs))
    (hD : P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0) (hN : IsNF X d) (y : ℝ) :
    L.Db ^ P.r * rh d y = (M.sgn P l0 * (-1) ^ P.r) • ∑ s : Fin (P.r + 2),
      ((F7.lagCo (fun j : Fin (P.r + 2) => ((j : ℕ) : ℝ)) s : ℝ) : ℂ) •
        (L.Db ^ (P.r + 1 - (s : ℕ)) * P5.QQi L st 0 y 0 0 * L.Db ^ (s : ℕ)) := by
  obtain ⟨hA, hC, -⟩ := actual_algebra_facts Wp Wq P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 hD
  have hL := hD.2.2.1
  have hL' := hN.1
  have hq : ∀ a b, st.QQ y a b = M.sgn P l0 • d.QQ y a b := fun a b => by rw [hD.2.2.2.1, hN.2.2.2]; rfl
  have ep : L.p = d.L.p := funext fun l => (hL.1 l).trans (hL'.1 l).symm
  have ec : L.c = d.L.c := funext fun l => (hL.2.2.1 l).trans (hL'.2.2.1 l).symm
  have eci : L.ci = d.L.ci := funext fun l => (hL.2.2.2.1 l).trans (hL'.2.2.2.1 l).symm
  have ecb : L.cb = d.L.cb := funext fun l => (hL.2.2.2.2.1 l).trans (hL'.2.2.2.2.1 l).symm
  have ez : L.ζb = d.L.ζb := hL.2.2.2.2.2.2.2.2.1.trans hL'.2.2.2.2.2.2.2.2.1.symm
  have eT : L.Tprod y = d.L.Tprod y := by
    unfold LevelData.Tprod LevelData.Tl
    rw [ep, ec, eci]
  obtain ⟨z00, z01, z10, z11⟩ := nf_zetab d hN.2.1 hN.2.2.1 y
  have hb := b_top L st hA y (by rw [hq, hq, ez, smul_mul_assoc, z00, smul_add, mul_smul_comm])
    (by rw [hq, hq, ez, smul_mul_assoc, z01, smul_add, mul_smul_comm])
    (by rw [hq, ez]; exact z10.smul_left _) (by rw [hq, ez]; exact z11.smul_left _)
  have hs : M.sgn P l0 * M.sgn P l0 = 1 := by rw [M.sgn, ← mul_pow]; simp
  have h1 : L.Db * bP L st y = M.sgn P l0 • rh d y := by
    rw [LevelData.Db, bP, mul_assoc, ← mul_assoc L.ζb, L.ζb_ζbi, one_mul, nP, hq, hq, rh, smul_mul_assoc, smul_mul_assoc,
      ← smul_add, mul_smul_comm]
    unfold LevelData.Drb LevelData.Ar LevelData.Br
    rw [ecb, eT]
  have h2 : rh d y = M.sgn P l0 • (L.Db * bP L st y) := by rw [h1, smul_smul, hs, one_smul]
  have hi : L.Db * L.Dbi = 1 := by
    rw [LevelData.Db, LevelData.Dbi, mul_assoc, ← mul_assoc L.ζb, L.ζb_ζbi, one_mul, Drb_Drbi]
  have hi' : L.Dbi * L.Db = 1 := by
    rw [LevelData.Db, LevelData.Dbi, mul_assoc, ← mul_assoc L.Drbi, Drbi_Drb, one_mul, L.ζbi_ζb]
  rw [h2, hb, hC _ (Complex.conj_ofReal y), mul_smul_comm, mul_smul_comm, mul_smul_comm, smul_smul, ← mul_assoc,
    ← pow_succ, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  have e : L.Db ^ (P.r + 1) * L.Dbi ^ (s : ℕ) = L.Db ^ (P.r + 1 - (s : ℕ)) := by
    conv_lhs => rw [show P.r + 1 = (P.r + 1 - (s : ℕ)) + s by have := s.isLt; omega, pow_add]
    rw [mul_assoc, ← (show Commute L.Db L.Dbi from hi.trans hi'.symm).mul_pow, hi, one_pow, mul_one]
  rw [mul_smul_comm, ← e]
  simp only [mul_assoc]

end lift

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TLB MeasureTheory in

theorem polyLift_rh : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ y : ℝ, PolyLift P Bs (2 * P.r + P.k + 1) (8 * (P.r + 1) * (2 * P.r + P.k + 1)) (rh d y) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN y
  obtain ⟨m, co, a, b, hco, hid⟩ := group_identity (Wq →L[ℂ] Wp) Bs.z Bs.z' Bs.z'_mem Bs.T_pos Bs.T'_pos (y : ℂ)
  obtain ⟨Θ, hΘ, hΘa⟩ := GlobalTheory.HatNF.MinorPoly.minor_polyOp Wp Wq P.k P.r (P.r + P.k) (8 * (P.r + 1) * (2 * P.r + P.k + 1)) (Fin m) a b
    (Q.uC P.k P.r 0 y) (fun i g => (-1) ^ P.r * co i g) fun i =>
      PartialDerivativeAlgebra.pd_mono (by nlinarith) (PartialDerivativeAlgebra.pd_mul (PartialDerivativeAlgebra.pd_const _ 0) (hco i))
  refine ⟨Θ, fun T hT => ⟨(hΘ T hT).1.trans (by omega), (hΘ T hT).2⟩, fun F hF Φ hΦ x hx => ?_⟩
  obtain ⟨ε, hε, hn⟩ := nice_of_cpt hF
  have hL := hD.2.2.1
  have hs : M.sgn P l0 * M.sgn P l0 = 1 := by rw [M.sgn, ← mul_pow]; simp
  have R := (radOp_sum (ε := ε) Finset.univ fun (s : Fin (P.r + 2)) _ =>
    (((radOp_db_pow X L hL (P.r + 1 - (s : ℕ))).mul (radOp_cap hε X μ L st l0 hD y)).mul
      (radOp_db_pow X L hL s)).smul ((F7.lagCo (fun j : Fin (P.r + 2) => ((j : ℕ) : ℝ)) s : ℝ) : ℂ)).smul
        (M.sgn P l0 * (-1) ^ P.r)
  rw [← db_pow_rh X μ L st l0 d hD hN y] at R
  obtain ⟨R1, R2⟩ := R F hn
  have h1 := R2 Φ hΦ x hx
  have h2 := mulAt_db_pow X L hL P.r hx ((rh d y).1 Φ)
  have key : ∀ g ∈ B.GV P.k P.r, (M.sgn P l0 * (-1) ^ P.r) • ∑ s : Fin (P.r + 2),
      ((F7.lagCo (fun j : Fin (P.r + 2) => ((j : ℕ) : ℝ)) s : ℝ) : ℂ) • dBar P.k P.r Bs.z Bs.z' g ^ (P.r + 1 - (s : ℕ)) •
        M.sgn P l0 • Q.CV P.k P.r y (fun g => dBar P.k P.r Bs.z Bs.z' g ^ (s : ℕ) • F g) g =
      (1 : ℂ) • dBar P.k P.r Bs.z Bs.z' g ^ P.r • B.opApply Θ F g := by
    intro g hg
    by_cases hG : 0 < Gf P.k P.r Bs.z Bs.z' g
    · have e := hid F hF.1 g hg hG
      rw [hΘa F g hg Set.univ isOpen_univ (Set.mem_univ _) (by rw [Set.inter_univ]; exact hF.1), one_smul]
      simp only [smul_comm _ (M.sgn P l0), mul_smul ((-1 : ℂ) ^ P.r), ← Finset.smul_sum]
      rw [e, smul_smul, ← mul_assoc, hs, one_mul, smul_comm]
    · rw [op_zero_off hF ((polyOp_ok _ _ _ _ _ _ _ hΘ).1 _) g hg fun h => hG h.2.1, smul_zero, smul_zero]
      by_contra hne
      exact hG (hε.trans_le (R1.2.2 g hg hne))
  have h3 := Qx8.JF_congr Bs key (wCell_gv Bs hx)
  have h0 := dBar_ne Bs.T_pos Bs.T'_pos (wCell_om Bs hx).2.2
  have h4 := h2.symm.trans h1
  simp only [Q.resG] at h4 ⊢
  rw [h3, one_smul, jf_dBar_pow, smul_comm] at h4
  exact smul_right_injective _ (pow_ne_zero _ h0) h4

end

end GlobalTheory.HatNF.LiftR
