import Mathlib
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSelfDualForm
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.HermCoord

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory Topology
open scoped TensorProduct

theorem exists_basis {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) :
    ∃ (b : Module.Basis (Fin 2) F E) (D : F), D ≠ 0 ∧ b 0 = 1 ∧ σ (b 1) = - b 1 ∧
      b 1 * b 1 = algebraMap F E D := by
  obtain ⟨-, hc, hf, hτ⟩ := h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinv : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hτ, hτ]; simp)
  have hne : ∃ x, σ x ≠ x := by
    by_contra hall
    push Not at hall
    have hr : NumberField.ComplexEmbedding.IsReal τ := by
      rw [NumberField.ComplexEmbedding.isReal_iff]
      ext x
      have := hτ τ x
      rw [hall x] at this
      simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this.symm
    exact (InfinitePlace.isComplex_mk_iff.1 (hc.isComplex (InfinitePlace.mk τ))) hr
  obtain ⟨x, hx⟩ := hne
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = x - σ x := ⟨_, rfl⟩
  have hδ0 : δ ≠ 0 := by
    rw [hδ]
    exact sub_ne_zero.2 (Ne.symm hx)
  have hσδ : σ δ = -δ := by
    rw [hδ, map_sub, hinv, neg_sub]
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hsm : ∀ (s : F) (x : E), σ (s • x) = s • σ x := fun s x => by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgHom.commutes]
  have key : ∀ s t : F, s • (1 : E) + t • δ = s • (1 : E) - t • δ → t = 0 := by
    intro s t hst
    have h3 : (2 * t) • δ = 0 := by
      have : t • δ = -(t • δ) := by
        have := add_left_cancel (a := s • (1 : E)) (b := t • δ) (c := -(t • δ))
          (by rw [hst, sub_eq_add_neg])
        exact this
      rw [mul_smul, two_smul]
      nth_rw 2 [this]
      simp
    rcases smul_eq_zero.1 h3 with h4 | h4
    · exact (mul_eq_zero.1 h4).resolve_left h2
    · exact absurd h4 hδ0
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h' := congrArg σ hst
    simp only [map_add, hsm, map_one, hσδ, map_zero, smul_neg] at h'
    have ht : t = 0 := key s t (by rw [hst, sub_eq_add_neg, h'])
    subst ht
    simpa using hst
  let b : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hf])
  have hb : ⇑b = ![(1 : E), δ] := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  have hb0 : b 0 = 1 := by simp [hb]
  have hb1 : b 1 = δ := by simp [hb]
  have hs := b.sum_repr (δ * δ)
  rw [Fin.sum_univ_two, hb0, hb1] at hs
  have hσ2 : σ (δ * δ) = δ * δ := by rw [map_mul, hσδ]; ring
  have hq : b.repr (δ * δ) 1 = 0 := by
    refine key (b.repr (δ * δ) 0) _ ?_
    have h' := congrArg σ hs
    simp only [map_add, hsm, map_one, hσδ, hσ2, smul_neg] at h'
    rw [hs, sub_eq_add_neg, h']
  rw [hq, zero_smul, add_zero] at hs
  refine ⟨b, b.repr (δ * δ) 0, ?_, hb0, by rw [hb1, hσδ], ?_⟩
  · intro h0
    rw [h0, zero_smul] at hs
    exact mul_self_ne_zero.2 hδ0 hs.symm
  · rw [hb1, Algebra.algebraMap_eq_smul_one, hs]

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (b : Module.Basis (Fin 2) F E)

def mk (a c : R) : R ⊗[F] E := a ⊗ₜ[F] b 0 + c ⊗ₜ[F] b 1

def rc (y : R ⊗[F] E) (k : Fin 2) : R := (Algebra.TensorProduct.basis R b).repr y k

theorem tmul_eq (a : R) (i : Fin 2) :
    a ⊗ₜ[F] b i = a • Algebra.TensorProduct.basis R b i := by
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem rc_mk (a c : R) : rc R b (mk R b a c) = ![a, c] := by
  have h : mk R b a c = a • Algebra.TensorProduct.basis R b 0 +
      c • Algebra.TensorProduct.basis R b 1 := by
    rw [mk, tmul_eq, tmul_eq]
  funext k
  rw [rc, h]
  simp only [map_add, map_smul, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply]
  fin_cases k <;> simp

theorem mk_rc (y : R ⊗[F] E) : mk R b (rc R b y 0) (rc R b y 1) = y := by
  have := (Algebra.TensorProduct.basis R b).sum_repr y
  rw [Fin.sum_univ_two] at this
  rw [mk, tmul_eq, tmul_eq]
  exact this

theorem rc_add (y z : R ⊗[F] E) (k : Fin 2) : rc R b (y + z) k = rc R b y k + rc R b z k := by
  simp [rc, map_add]

variable {R b}
variable {σ : E →ₐ[F] E} {D : F}

theorem mk_mul (hb0 : b 0 = 1) (hD : b 1 * b 1 = algebraMap F E D) (a c a' c' : R) :
    mk R b a c * mk R b a' c' = mk R b (a * a' + algebraMap F R D * (c * c')) (a * c' + c * a') := by
  simp only [mk, mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, hb0, mul_one, one_mul, hD,
    TensorProduct.add_tmul]
  have : (c * c') ⊗ₜ[F] (algebraMap F E D) = (algebraMap F R D * (c * c')) ⊗ₜ[F] (1 : E) := by
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Algebra.smul_def]
  rw [this]
  abel

theorem sig_mk (hb0 : b 0 = 1) (hσ : σ (b 1) = - b 1) (a c : R) :
    sigR R σ (mk R b a c) = mk R b a (-c) := by
  simp [mk, sigR, hb0, hσ, TensorProduct.tmul_neg, TensorProduct.neg_tmul]

theorem rc_sig (hb0 : b 0 = 1) (hσ : σ (b 1) = - b 1) (y : R ⊗[F] E) :
    rc R b (sigR R σ y) = ![rc R b y 0, - rc R b y 1] := by
  conv_lhs => rw [← mk_rc R b y]
  rw [sig_mk hb0 hσ, rc_mk]

theorem trace_eq (hb0 : b 0 = 1) (hD : b 1 * b 1 = algebraMap F E D) (y : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) y = 2 * rc R b y 0 := by
  have e0 : Algebra.TensorProduct.basis R b 0 = mk R b 1 0 := by
    simp [mk, Algebra.TensorProduct.basis_apply]
  have e1 : Algebra.TensorProduct.basis R b 1 = mk R b 0 1 := by
    simp [mk, Algebra.TensorProduct.basis_apply]
  rw [Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R b), Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, e0, e1]
  conv_lhs => rw [← mk_rc R b y]
  rw [mk_mul hb0 hD, mk_mul hb0 hD]
  change rc R b _ 0 + rc R b _ 1 = _
  rw [rc_mk, rc_mk]
  simp
  ring

end Coord

section Herm

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (b : Module.Basis (Fin 2) F E) {n : ℕ}

def toX (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (p : Fin n × Fin n) : R :=
  if p.1 ≤ p.2 then rc R b (S p.1 p.2) 0 else rc R b (S p.1 p.2) 1

def ofX (X : Fin n × Fin n → R) : Matrix (Fin n) (Fin n) (R ⊗[F] E) := fun i j =>
  mk R b (if i ≤ j then X (i, j) else X (j, i))
    (if i < j then - X (j, i) else if j < i then X (i, j) else 0)

def wt {F : Type} [Field F] (D : F) (p : Fin n × Fin n) : F :=
  if p.1 = p.2 then 1 else if p.1 < p.2 then 2 else -2 * D

variable {R b} {σ : E →ₐ[F] E} {D : F}

theorem ofX_mem (hb0 : b 0 = 1) (hσ : σ (b 1) = - b 1) (X : Fin n × Fin n → R) :
    ofX R b X ∈ HermR R σ n := by
  intro i j
  change sigR R σ (ofX R b X j i) = ofX R b X i j
  simp only [ofX]
  rw [sig_mk hb0 hσ]
  rcases lt_trichotomy i j with h | h | h
  · simp [h, h.le, not_lt.2 h.le, not_le.2 h]
  · subst h; simp
  · simp [h, h.le, not_lt.2 h.le, not_le.2 h]

theorem toX_ofX (X : Fin n × Fin n → R) : toX R b (ofX R b X) = X := by
  funext ⟨i, j⟩
  simp only [toX, ofX, rc_mk]
  by_cases h : i ≤ j
  · simp [h]
  · simp [h, not_le.1 h, not_lt.2 (not_le.1 h).le]

theorem toX_add (S T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    toX R b (S + T) = toX R b S + toX R b T := by
  funext p
  simp only [toX, Matrix.add_apply, rc_add, Pi.add_apply]
  split_ifs <;> rfl

theorem herm_rc (hb0 : b 0 = 1) (hσ : σ (b 1) = - b 1) {S : Matrix (Fin n) (Fin n) (R ⊗[F] E)}
    (hS : S ∈ HermR R σ n) (i j : Fin n) :
    rc R b (S i j) 0 = rc R b (S j i) 0 ∧ rc R b (S i j) 1 = - rc R b (S j i) 1 := by
  have h : sigR R σ (S j i) = S i j := hS i j
  have h' := rc_sig hb0 hσ (S j i)
  rw [h] at h'
  exact ⟨by simpa using congrFun h' 0, by simpa using congrFun h' 1⟩

theorem herm_diag (h2 : (2 : F) ≠ 0) (hb0 : b 0 = 1) (hσ : σ (b 1) = - b 1)
    {S : Matrix (Fin n) (Fin n) (R ⊗[F] E)} (hS : S ∈ HermR R σ n) (i : Fin n) :
    rc R b (S i i) 1 = 0 := by
  have h := (herm_rc hb0 hσ hS i i).2
  have h3 : (2 : F) • rc R b (S i i) 1 = 0 := by
    rw [two_smul]
    nth_rw 1 [h]
    simp
  have h4 := congrArg (fun x => (2 : F)⁻¹ • x) h3
  simpa [smul_smul, inv_mul_cancel₀ h2] using h4

theorem ofX_toX (h2 : (2 : F) ≠ 0) (hb0 : b 0 = 1) (hσ : σ (b 1) = - b 1)
    {S : Matrix (Fin n) (Fin n) (R ⊗[F] E)} (hS : S ∈ HermR R σ n) : ofX R b (toX R b S) = S := by
  funext i j
  conv_rhs => rw [← mk_rc R b (S i j)]
  simp only [ofX, toX]
  rcases lt_trichotomy i j with h | h | h
  · simp [h, h.le, not_lt.2 h.le, not_le.2 h, (herm_rc hb0 hσ hS i j).2]
  · subst h
    simp [herm_diag h2 hb0 hσ hS i]
  · simp [h, h.le, not_lt.2 h.le, not_le.2 h, (herm_rc hb0 hσ hS i j).1]

theorem rc_mul (hb0 : b 0 = 1) (hD : b 1 * b 1 = algebraMap F E D) (y z : R ⊗[F] E) :
    rc R b (y * z) 0 = rc R b y 0 * rc R b z 0 + algebraMap F R D * (rc R b y 1 * rc R b z 1) := by
  conv_lhs => rw [← mk_rc R b y, ← mk_rc R b z, mk_mul hb0 hD, rc_mk]
  simp

omit [Algebra F R] in
theorem sum_tri (P Q : Fin n → Fin n → R) (hP : ∀ i j, P i j = P j i) (hQ : ∀ i j, Q i j = Q j i)
    (hd : ∀ i, Q i i = 0) :
    ∑ i, ∑ j, (P i j + Q i j) =
      ∑ i, ∑ j, (if i = j then P i j else if i < j then 2 * P i j else 2 * Q i j) := by
  have sw : ∀ A : Fin n → Fin n → R, (∀ i j, A i j = A j i) →
      ∑ i, ∑ j, (if j < i then A i j else 0) = ∑ i, ∑ j, (if i < j then A i j else 0) := by
    intro A hA
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hA]
  have L : ∑ i, ∑ j, (P i j + Q i j) = ∑ i, ∑ j, (if i = j then P i j else 0) +
      ∑ i, ∑ j, (if i < j then P i j else 0) + ∑ i, ∑ j, (if j < i then P i j else 0) +
      ∑ i, ∑ j, (if i < j then Q i j else 0) + ∑ i, ∑ j, (if j < i then Q i j else 0) := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · subst h
      simp [hd]
    · simp [h, h.ne', not_lt.2 h.le]
  have M : ∑ i, ∑ j, (if i = j then P i j else if i < j then 2 * P i j else 2 * Q i j) =
      ∑ i, ∑ j, (if i = j then P i j else 0) + 2 * ∑ i, ∑ j, (if i < j then P i j else 0) +
      2 * ∑ i, ∑ j, (if j < i then Q i j else 0) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · subst h
      simp
    · simp [h, h.ne', not_lt.2 h.le]
  rw [L, M, sw P hP, ← sw Q hQ]
  ring

theorem pair_eq (h2 : (2 : F) ≠ 0) (hb0 : b 0 = 1) (hσ : σ (b 1) = - b 1)
    (hD : b 1 * b 1 = algebraMap F E D) (S T : HermR R σ n) :
    pairHerm R σ n S T =
      ∑ p : Fin n × Fin n, toX R b S.1 p * (algebraMap F R (wt D p) * toX R b T.1 p) := by
  have hh : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F R) 2, ← map_mul, one_div, inv_mul_cancel₀ h2, map_one]
  have hS := S.2
  have hT := T.2
  have A : pairHerm R σ n S T = ∑ i, ∑ j, (rc R b (S.1 i j) 0 * rc R b (T.1 i j) 0 +
      (-algebraMap F R D * rc R b (S.1 i j) 1 * rc R b (T.1 i j) 1)) := by
    unfold pairHerm
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [trace_eq hb0 hD, ← mul_assoc, hh, one_mul, rc_mul hb0 hD, (herm_rc hb0 hσ hT j i).1,
      (herm_rc hb0 hσ hT j i).2]
    ring
  rw [A, sum_tri _ _ (fun i j => by rw [(herm_rc hb0 hσ hS i j).1, (herm_rc hb0 hσ hT i j).1])
    (fun i j => by rw [(herm_rc hb0 hσ hS i j).2, (herm_rc hb0 hσ hT i j).2]; ring)
    (fun i => by rw [herm_diag h2 hb0 hσ hS i]; ring), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [toX, wt]
  rcases lt_trichotomy i j with h | h | h
  · simp [h, h.ne, h.le, map_ofNat]
    ring
  · subst h
    simp
  · simp [h.ne', not_lt.2 h.le, not_le.2 h, map_ofNat]
    ring

end Herm

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] (b : Module.Basis (Fin 2) F E)

theorem continuous_rc (k : Fin 2) : Continuous fun y : R ⊗[F] E => rc R b y k :=
  (continuous_apply k).comp (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).continuous

theorem continuous_mk {Y : Type} [TopologicalSpace Y] {f g : Y → R} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => mk R b (f x) (g x) := by
  have h : (fun x => mk R b (f x) (g x)) =
      fun x => (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).symm ![f x, g x] := by
    funext x
    apply (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).injective
    rw [Homeomorph.apply_symm_apply]
    exact rc_mk R b _ _
  rw [h]
  refine (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).symm.continuous.comp (continuous_pi fun k => ?_)
  fin_cases k
  · exact hf
  · exact hg

variable {R b} {σ : E →ₐ[F] E}

def hermEquiv (h2 : (2 : F) ≠ 0) (hb0 : b 0 = 1) (hσ : σ (b 1) = - b 1) (n : ℕ) :
    HermR R σ n ≃ₜ+ (Fin n × Fin n → R) where
  toFun S := toX R b S.1
  invFun X := ⟨ofX R b X, ofX_mem hb0 hσ X⟩
  left_inv S := Subtype.ext (ofX_toX h2 hb0 hσ S.2)
  right_inv X := toX_ofX X
  map_add' S T := toX_add S.1 T.1
  continuous_toFun := continuous_pi fun p => by
    have hc : ∀ k, Continuous fun S : HermR R σ n => rc R b (S.1 p.1 p.2) k := fun k =>
      (continuous_rc R b k).comp (continuous_subtype_val.matrix_elem _ _)
    by_cases h : p.1 ≤ p.2
    · simpa only [toX, h, if_true] using hc 0
    · simpa only [toX, h, if_false] using hc 1
  continuous_invFun := Continuous.subtype_mk (continuous_matrix fun i j => by
    refine continuous_mk R b ?_ ?_
    · split_ifs <;> exact continuous_apply _
    · split_ifs
      · exact (continuous_apply _).neg
      · exact continuous_apply _
      · exact continuous_const) _

end Top

end GlobalTheory.CompanionTheory.SW.HermCoord

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SW.HermCoord

theorem exists_sdHerm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ n : ℕ, ∃ ν : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n ν := by
  intro F E _ _ _ _ _ σ hCM ψ hψ n
  obtain ⟨b, D, hD0, hb0, hσ, hD⟩ := exists_basis σ hCM
  obtain ⟨h1, -, -, -, -, -, -, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := h1
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hw : ∀ p : Fin n × Fin n, wt D p ≠ 0 := by
    intro p
    simp only [wt]
    split_ifs
    · exact one_ne_zero
    · exact h2
    · exact mul_ne_zero (neg_ne_zero.2 h2) hD0
  have hsym : (Matrix.diagonal (wt D : Fin n × Fin n → F)).IsSymm := Matrix.isSymm_diagonal _
  have hdet : (Matrix.diagonal (wt D : Fin n × Fin n → F)).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun p _ => hw p
  obtain ⟨μ, hμ⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.SdExist.exists_selfDual_form ψ hψ _ hsym hdet
    (hermEquiv (R := AF F) (σ := σ) h2 hb0 hσ n)
  refine ⟨μ, ?_⟩
  unfold SdHerm
  have hf : (fun S T : HermR (AF F) σ n => ψ (pairHerm (AF F) σ n S T)) = fun X Y =>
      ψ (dotProduct (hermEquiv (R := AF F) (σ := σ) h2 hb0 hσ n X) (Matrix.mulVec
        ((Matrix.diagonal (wt D : Fin n × Fin n → F)).map (algebraMap F (AF F)))
        (hermEquiv (R := AF F) (σ := σ) h2 hb0 hσ n Y))) := by
    funext S T
    rw [pair_eq h2 hb0 hσ hD S T, Matrix.diagonal_map (map_zero _)]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.mulVec_diagonal]
    rfl
  rw [hf]
  exact hμ

end GlobalTheory.CompanionTheory.SW.HermCoord
