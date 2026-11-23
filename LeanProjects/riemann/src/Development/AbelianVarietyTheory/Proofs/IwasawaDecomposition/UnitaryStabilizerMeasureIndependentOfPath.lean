import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableSetOrbitExistsMeasurableSection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdHermitianFibreMeasureInvariantOrbitFiniteNonzStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueStdHermitianFibreProductOfRankGeThreStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicTwoStepMeasureOrthogonalBasesPlaneCompareStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueUnitaryTwoStepPairMeasureStatement

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal Matrix

noncomputable section

namespace GlobalTheory.GaugeSquare

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}

theorem consCol_mulVec {M : ℕ} (x : Fin 1 → Fin (M + 1) → E) (B : Matrix (Fin (M + 1)) (Fin M) E)
    (c : E) (w : Fin M → E) :
    (consCol x B) *ᵥ (Fin.cons (α := fun _ => E) c w) = c • x 0 + B *ᵥ w := by
  funext i
  simp [consCol, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]

theorem decomp {M : ℕ} {x : Fin 1 → Fin (M + 1) → E} {B : Matrix (Fin (M + 1)) (Fin M) E}
    (h : (consCol x B).det ≠ 0) (v : Fin (M + 1) → E) : ∃ (c : E) (w : Fin M → E),
    v = c • x 0 + B *ᵥ w := by
  have hu : IsUnit (consCol x B).det := isUnit_iff_ne_zero.2 h
  refine ⟨((consCol x B)⁻¹ *ᵥ v) 0, Fin.tail ((consCol x B)⁻¹ *ᵥ v), ?_⟩
  rw [← consCol_mulVec, Fin.cons_self_tail, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mulVec]

theorem indep {M : ℕ} {x : Fin 1 → Fin (M + 1) → E} {B : Matrix (Fin (M + 1)) (Fin M) E}
    (h : (consCol x B).det ≠ 0) {c : E} {w : Fin M → E} (h0 : c • x 0 + B *ᵥ w = 0) :
    c = 0 ∧ w = 0 := by
  rw [← consCol_mulVec] at h0
  have := Matrix.eq_zero_of_mulVec_eq_zero h h0
  exact ⟨congrFun this 0, funext fun i => congrFun this i.succ⟩

theorem leftInv {M : ℕ} {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {x : Fin 1 → Fin (M + 1) → E}
    {a : F} {B : Matrix (Fin (M + 1)) (Fin M) E} {J' : Matrix (Fin M) (Fin M) E}
    (h : StepData σ J x a B J') : ∃ L : Matrix (Fin M) (Fin (M + 1)) E, L * B = 1 := by
  obtain ⟨-, -, -, -, h5, -, h6⟩ := h
  refine ⟨J'⁻¹ * (Formalism.UG.cT (σ : E →+* E) B * J), ?_⟩
  rw [Matrix.mul_assoc, ← h5, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h6)]

def rowP (σ : E →ₐ[F] E) {M N : ℕ} (J : Matrix (Fin M) (Fin M) E) (D : Matrix (Fin M) (Fin N) E)
    (v : Fin M → E) : Fin N → E := (fun i => σ (v i)) ᵥ* (J * D)

theorem rowP_apply {M N : ℕ} (J : Matrix (Fin M) (Fin M) E) (D : Matrix (Fin M) (Fin N) E)
    (v : Fin M → E) (j : Fin N) : rowP σ J D v j = hE σ J v (fun i => D i j) := by
  simp [rowP, hE, Formalism.UG.hform, Matrix.vecMul, dotProduct, Matrix.mul_apply, Finset.mul_sum, mul_assoc]

theorem rowP_mul {M N K : ℕ} (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin M) (Fin N) E)
    (C : Matrix (Fin N) (Fin K) E) (v : Fin M → E) : rowP σ J (B * C) v = rowP σ J B v ᵥ* C := by
  simp [rowP, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem rowP_mulVec {M N K : ℕ} (J : Matrix (Fin M) (Fin M) E) (D : Matrix (Fin M) (Fin N) E)
    (B : Matrix (Fin M) (Fin K) E) (w : Fin K → E) :
    rowP σ J D (B *ᵥ w) = (fun i => σ (w i)) ᵥ* (Formalism.UG.cT (σ : E →+* E) B * J * D) := by
  have : (fun i => σ ((B *ᵥ w) i)) = (fun i => σ (w i)) ᵥ* Formalism.UG.cT (σ : E →+* E) B := by
    funext i
    simp [Formalism.UG.cT, Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
  rw [rowP, this, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem rowPairing_add {M N : ℕ} (J : Matrix (Fin M) (Fin M) E) (D : Matrix (Fin M) (Fin N) E)
    (v w : Fin M → E) : rowP σ J D (v + w) = rowP σ J D v + rowP σ J D w := by
  rw [rowP, rowP, rowP, ← Matrix.add_vecMul]
  congr 1
  funext i
  simp

theorem rowPairing_smul {M N : ℕ} (J : Matrix (Fin M) (Fin M) E) (D : Matrix (Fin M) (Fin N) E)
    (c : E) (v : Fin M → E) : rowP σ J D (c • v) = σ c • rowP σ J D v := by
  rw [rowP, rowP, ← Matrix.smul_vecMul]
  congr 1
  funext i
  simp

section Two

variable {M : ℕ} {J : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) E} {x : Fin 1 → Fin (M + 1 + 1) → E}
  {a : F} {B : Matrix (Fin (M + 1 + 1)) (Fin (M + 1)) E} {J₁ : Matrix (Fin (M + 1)) (Fin (M + 1)) E}
  {y : Fin 1 → Fin (M + 1) → E} {b : F} {C : Matrix (Fin (M + 1)) (Fin M) E}
  {J₀ : Matrix (Fin M) (Fin M) E}

theorem perp_fst (h : StepData σ J x a B J₁) : rowP σ J (B * C) (x 0) = 0 := by
  have : rowP σ J B (x 0) = 0 := funext fun j => by rw [rowP_apply]; exact h.2.2.2.1 j
  rw [rowP_mul, this, Matrix.zero_vecMul]

theorem perp_snd (h : StepData σ J x a B J₁) (h' : StepData σ J₁ y b C J₀) :
    rowP σ J (B * C) (B *ᵥ y 0) = 0 := by
  have : rowP σ J₁ C (y 0) = 0 := funext fun j => by rw [rowP_apply]; exact h'.2.2.2.1 j
  rw [rowP_mulVec, ← Matrix.mul_assoc, ← h.2.2.2.2.1]
  exact this

theorem span_perp (h : StepData σ J x a B J₁) (h' : StepData σ J₁ y b C J₀)
    (hd : (consCol x B).det ≠ 0) (hd' : (consCol y C).det ≠ 0) {v : Fin (M + 1 + 1) → E}
    (hv : rowP σ J (B * C) v = 0) : ∃ c c' : E, v = c • x 0 + c' • B *ᵥ y 0 := by
  obtain ⟨c, w, rfl⟩ := decomp hd v
  obtain ⟨c', u, rfl⟩ := decomp hd' w
  refine ⟨c, c', ?_⟩
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec] at hv ⊢
  rw [rowPairing_add, rowPairing_add, rowPairing_smul, rowPairing_smul, perp_fst h, perp_snd h h', rowP_mulVec] at hv
  have e : Formalism.UG.cT (σ : E →+* E) (B * C) * J * (B * C) = J₀ := by
    rw [h'.2.2.2.2.1, h.2.2.2.2.1, Formalism.UG.cT_mul]
    simp only [Matrix.mul_assoc]
  rw [e] at hv
  simp only [smul_zero, zero_add] at hv
  have h0 := Matrix.eq_zero_of_vecMul_eq_zero h'.2.2.2.2.2.2 hv
  have hu : u = 0 := funext fun i => by simpa using congrFun h0 i
  simp [hu]

theorem indep_two (h' : StepData σ J₁ y b C J₀) (hd : (consCol x B).det ≠ 0) {c c' : E}
    (h0 : c • x 0 + c' • B *ᵥ y 0 = 0) : c = 0 ∧ c' = 0 := by
  rw [← Matrix.mulVec_smul] at h0
  obtain ⟨h1, h2⟩ := indep hd h0
  refine ⟨h1, ?_⟩
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact h3
  · exfalso
    have h4 := h'.2.2.1
    rw [h3] at h4
    simp only [hE, Formalism.UG.hform, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h4
    exact h'.2.1 ((map_eq_zero _).1 h4.symm)

end Two

theorem lrAct_lrAct {S : Type} [CommRing S] {n M : ℕ} (γ γ' : Matrix (Fin n) (Fin n) S)
    (X : Fin n → Fin M → S) : lrAct 1 γ' (lrAct 1 γ X) = lrAct 1 (γ * γ') X := by
  funext a i
  simp only [lrAct, Matrix.one_mulVec, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem lrAct_one {S : Type} [CommRing S] {n M : ℕ} (X : Fin n → Fin M → S) : lrAct 1 1 X = X := by
  funext a i
  simp [lrAct, Matrix.one_apply]

theorem lrAct_two {M : ℕ} (γ : Matrix (Fin 2) (Fin 2) E) (u v : Fin M → E) (a : Fin 2) :
    lrAct 1 γ ![u, v] a = γ 0 a • u + γ 1 a • v := by
  funext i
  simp [lrAct, Fin.sum_univ_two, mul_comm]

theorem exists_gamma {M : ℕ} {J : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) E}
    {x₁ x₂ : Fin 1 → Fin (M + 1 + 1) → E} {a₁ a₂ : F}
    {B₁ B₂ : Matrix (Fin (M + 1 + 1)) (Fin (M + 1)) E}
    {J₁ J₂ : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {y₁ y₂ : Fin 1 → Fin (M + 1) → E} {b₁ b₂ : F}
    {C₁ C₂ : Matrix (Fin (M + 1)) (Fin M) E} {J₀ : Matrix (Fin M) (Fin M) E}
    (h₁ : StepData σ J x₁ a₁ B₁ J₁) (h₁' : StepData σ J₁ y₁ b₁ C₁ J₀)
    (h₂ : StepData σ J x₂ a₂ B₂ J₂) (h₂' : StepData σ J₂ y₂ b₂ C₂ J₀) (hBC : B₁ * C₁ = B₂ * C₂)
    (d₁ : (consCol x₁ B₁).det ≠ 0) (d₁' : (consCol y₁ C₁).det ≠ 0)
    (d₂ : (consCol x₂ B₂).det ≠ 0) :
    ∃ γ : GL (Fin 2) E, ![x₂ 0, B₂.mulVec (y₂ 0)] =
      lrAct 1 (γ : Matrix (Fin 2) (Fin 2) E) ![x₁ 0, B₁.mulVec (y₁ 0)] := by
  obtain ⟨p, q, hp⟩ := span_perp h₁ h₁' d₁ d₁' (v := x₂ 0) (by rw [hBC]; exact perp_fst h₂)
  obtain ⟨r, t, hr⟩ := span_perp h₁ h₁' d₁ d₁' (v := B₂ *ᵥ y₂ 0) (by rw [hBC]; exact perp_snd h₂ h₂')
  have hdet : (!![p, r; q, t] : Matrix (Fin 2) (Fin 2) E).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have e0 : p * v 0 + r * v 1 = 0 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hv 0
    have e1 : q * v 0 + t * v 1 = 0 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hv 1
    have : v 0 • x₂ 0 + v 1 • B₂ *ᵥ y₂ 0 = 0 := by
      rw [hp, hr]
      have : v 0 • (p • x₁ 0 + q • B₁ *ᵥ y₁ 0) + v 1 • (r • x₁ 0 + t • B₁ *ᵥ y₁ 0) =
          (p * v 0 + r * v 1) • x₁ 0 + (q * v 0 + t * v 1) • B₁ *ᵥ y₁ 0 := by module
      rw [this, e0, e1]; simp
    obtain ⟨f0, f1⟩ := indep_two h₂' d₂ this
    apply hv0
    funext i
    fin_cases i
    · exact f0
    · exact f1
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, ?_⟩
  funext a
  rw [lrAct_two]
  fin_cases a
  · simpa using hp
  · simpa using hr

end Alg

section Grp

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
  (R : Type) [CommRing R] [Algebra F R]

abbrev mt {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (g : HA R σ J) : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
  ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E))

theorem smul_apply' {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (g : HA R σ J)
    (X : Fin n → Fin M → R ⊗[F] E) (a : Fin n) : (g • X) a = mt R g *ᵥ X a := rfl

theorem mt_mul {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (g h : HA R σ J) :
    mt R (g * h) = mt R g * mt R h := rfl

theorem mt_inj {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {g h : HA R σ J} (e : mt R g = mt R h) :
    g = h := Subtype.ext (Units.ext e)

theorem smul_lrAct {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (g : HA R σ J)
    (γ : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E) :
    g • lrAct 1 γ X = lrAct 1 γ (g • X) := by
  funext a i
  simp only [smul_apply', lrAct, Matrix.one_mulVec]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem ratTup_lrAct {M n : ℕ} (γ : Matrix (Fin n) (Fin n) E) (X : Fin n → Fin M → E) :
    ratTup (F := F) R (lrAct 1 γ X) = lrAct 1 (γ.map (inclR (F := F) R)) (ratTup (F := F) R X) := by
  funext a i
  simp [ratTup, lrAct]

theorem ratTup_zero {M N : ℕ} (x : Fin 1 → Fin M → E) (B : Matrix (Fin M) (Fin N) E)
    (y : Fin 1 → Fin N → E) :
    ratTup (F := F) R ![x 0, B *ᵥ y 0] 0 = ratTup (F := F) R x 0 := rfl

theorem ratTup_one {M N : ℕ} (x : Fin 1 → Fin M → E) (B : Matrix (Fin M) (Fin N) E)
    (y : Fin 1 → Fin N → E) :
    ratTup (F := F) R ![x 0, B *ᵥ y 0] 1 = B.map (inclR (F := F) R) *ᵥ ratTup (F := F) R y 0 := by
  funext i
  simp [ratTup, Matrix.mulVec, dotProduct]

theorem mem_stab {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (x : Fin 1 → Fin M → E) (g : HA R σ J) :
    g ∈ Hstab R σ J x ↔ mt R g *ᵥ ratTup (F := F) R x 0 = ratTup (F := F) R x 0 := by
  constructor
  · intro h
    exact congrFun (MulAction.mem_stabilizer_iff.1 h) 0
  · intro h
    refine MulAction.mem_stabilizer_iff.2 (funext fun a => ?_)
    rw [Subsingleton.elim a 0]
    exact h

theorem cancel_mat {M N K : ℕ} {B : Matrix (Fin M) (Fin N) E} {L : Matrix (Fin N) (Fin M) E}
    (hL : L * B = 1) {P Q : Matrix (Fin N) (Fin K) (R ⊗[F] E)}
    (h : B.map (inclR (F := F) R) * P = B.map (inclR (F := F) R) * Q) : P = Q := by
  have e : L.map (inclR (F := F) R) * B.map (inclR (F := F) R) = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← Matrix.one_mul P, ← Matrix.one_mul Q, ← e, Matrix.mul_assoc, h, Matrix.mul_assoc]

theorem cancel_vec {M N : ℕ} {B : Matrix (Fin M) (Fin N) E} {L : Matrix (Fin N) (Fin M) E}
    (hL : L * B = 1) {P Q : Fin N → R ⊗[F] E}
    (h : B.map (inclR (F := F) R) *ᵥ P = B.map (inclR (F := F) R) *ᵥ Q) : P = Q := by
  have e : L.map (inclR (F := F) R) * B.map (inclR (F := F) R) = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← Matrix.one_mulVec P, ← Matrix.one_mulVec Q, ← e, ← Matrix.mulVec_mulVec, h,
    Matrix.mulVec_mulVec]

variable {M : ℕ} {J : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) E} {x : Fin 1 → Fin (M + 1 + 1) → E}
  {B : Matrix (Fin (M + 1 + 1)) (Fin (M + 1)) E} {J₁ : Matrix (Fin (M + 1)) (Fin (M + 1)) E}
  {y : Fin 1 → Fin (M + 1) → E} {C : Matrix (Fin (M + 1)) (Fin M) E}
  {J₀ : Matrix (Fin M) (Fin M) E}

def emb (e : Hstab R σ J x ≃* HA R σ J₁) (e' : Hstab R σ J₁ y ≃* HA R σ J₀) :
    HA R σ J₀ →* HA R σ J :=
  (Hstab R σ J x).subtype.comp (e.symm.toMonoidHom.comp
    ((Hstab R σ J₁ y).subtype.comp e'.symm.toMonoidHom))

variable {R} {e : Hstab R σ J x ≃* HA R σ J₁} {e' : Hstab R σ J₁ y ≃* HA R σ J₀}

theorem emb_apply (h : HA R σ J₀) :
    emb R e e' h = (e.symm (e'.symm h : HA R σ J₁) : HA R σ J) := rfl

theorem symm_rel (he : ∀ g : Hstab R σ J x, FrameRelR R σ J J₁ B (g : HA R σ J) (e g))
    (g : HA R σ J₁) :
    mt R (e.symm g : HA R σ J) * B.map (inclR (F := F) R) = B.map (inclR (F := F) R) * mt R g := by
  have := he (e.symm g)
  rw [e.apply_symm_apply] at this
  exact this

theorem emb_rel (he : ∀ g : Hstab R σ J x, FrameRelR R σ J J₁ B (g : HA R σ J) (e g))
    (he' : ∀ g : Hstab R σ J₁ y, FrameRelR R σ J₁ J₀ C (g : HA R σ J₁) (e' g)) (h : HA R σ J₀) :
    mt R (emb R e e' h) * (B * C).map (inclR (F := F) R) = (B * C).map (inclR (F := F) R) * mt R h := by
  have h2 := he' (e'.symm h)
  rw [e'.apply_symm_apply] at h2
  rw [emb_apply, Matrix.map_mul, ← Matrix.mul_assoc, symm_rel he, Matrix.mul_assoc, Matrix.mul_assoc]
  exact congrArg _ h2

theorem pair_eq (he : ∀ g : Hstab R σ J x, FrameRelR R σ J J₁ B (g : HA R σ J) (e g))
    (g : HA R σ J) (g' : HA R σ J₁) :
    pairOf R σ J B (g • ratTup (F := F) R x) g (g' • ratTup (F := F) R y) =
      (g * (e.symm g' : HA R σ J)) • ratTup (F := F) R ![x 0, B *ᵥ y 0] := by
  funext a
  fin_cases a
  · show mt R g *ᵥ ratTup (F := F) R x 0 = mt R (g * _) *ᵥ ratTup (F := F) R x 0
    rw [mt_mul, ← Matrix.mulVec_mulVec, (mem_stab R x _).1 (e.symm g').2]
  · show mt R g *ᵥ (B.map (inclR (F := F) R) *ᵥ (mt R g' *ᵥ ratTup (F := F) R y 0)) =
      mt R (g * _) *ᵥ ratTup (F := F) R ![x 0, B *ᵥ y 0] 1
    rw [ratTup_one, mt_mul]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [symm_rel he]

theorem emb_fix (he : ∀ g : Hstab R σ J x, FrameRelR R σ J J₁ B (g : HA R σ J) (e g))
    (h : HA R σ J₀) :
    emb R e e' h • ratTup (F := F) R ![x 0, B *ᵥ y 0] = ratTup (F := F) R ![x 0, B *ᵥ y 0] := by
  funext a
  fin_cases a
  · exact (mem_stab R x _).1 (e.symm (e'.symm h : HA R σ J₁)).2
  · show mt R (emb R e e' h) *ᵥ ratTup (F := F) R ![x 0, B *ᵥ y 0] 1 =
      ratTup (F := F) R ![x 0, B *ᵥ y 0] 1
    rw [ratTup_one, Matrix.mulVec_mulVec, emb_apply, symm_rel he, ← Matrix.mulVec_mulVec,
      (mem_stab R y _).1 (e'.symm h).2]

theorem emb_surj {L : Matrix (Fin (M + 1)) (Fin (M + 1 + 1)) E} (hL : L * B = 1)
    (he : ∀ g : Hstab R σ J x, FrameRelR R σ J J₁ B (g : HA R σ J) (e g)) (g : HA R σ J)
    (hg : g • ratTup (F := F) R ![x 0, B *ᵥ y 0] = ratTup (F := F) R ![x 0, B *ᵥ y 0]) :
    ∃ h, emb R e e' h = g := by
  have h0 : g ∈ Hstab R σ J x := (mem_stab R x _).2 (congrFun hg 0)
  have h1 : e ⟨g, h0⟩ ∈ Hstab R σ J₁ y := by
    refine (mem_stab R y _).2 (cancel_vec R hL ?_)
    have h2 : mt R g *ᵥ ratTup (F := F) R ![x 0, B *ᵥ y 0] 1 =
      ratTup (F := F) R ![x 0, B *ᵥ y 0] 1 := congrFun hg 1
    have h3 : mt R g * B.map (inclR (F := F) R) = B.map (inclR (F := F) R) * mt R (e ⟨g, h0⟩) := he ⟨g, h0⟩
    rw [ratTup_one, Matrix.mulVec_mulVec, h3, ← Matrix.mulVec_mulVec] at h2
    exact h2
  refine ⟨e' ⟨_, h1⟩, ?_⟩
  rw [emb_apply, e'.symm_apply_apply, e.symm_apply_apply]

end Grp

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem exists_sec (R : Type) [CommRing R] [Algebra F R] {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x : Fin 1 → Fin M → E) : ∃ s, IsSec R σ J x s := by
  classical
  refine ⟨fun y => if h : ∃ g : HA R σ J, g • ratTup (F := F) R x = y then h.choose else 1, ?_⟩
  intro y hy
  simp only [dif_pos hy]
  exact hy.choose_spec

theorem meas_avg [FiniteDimensional F E] {M N : ℕ} {J : Matrix (Fin N) (Fin N) E}
    {J₀ : Matrix (Fin M) (Fin M) E} (μ₀ : Measure (HA (AF F) σ J₀)) [μ₀.IsHaarMeasure]
    {ι : HA (AF F) σ J₀ → HA (AF F) σ J} (hι : Continuous ι) {f : HA (AF F) σ J → ℝ≥0∞}
    (hf : Measurable f) {t : (Fin 2 → Fin N → AF F ⊗[F] E) → HA (AF F) σ J} (ht : Measurable t) :
    Measurable fun X => ∫⁻ h, f (t X * ι h) ∂μ₀ := by
  refine Measurable.lintegral_prod_right' (f := fun p : _ × _ => f (t p.1 * ι p.2)) ?_
  exact hf.comp ((ht.comp measurable_fst).mul (hι.measurable.comp measurable_snd))

theorem unfold_two [FiniteDimensional F E] {d : ℕ} {bb : Module.Basis (Fin d) F E} {s : StdMeas bb}
    {M : ℕ} {J : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) E} {x : Fin 1 → Fin (M + 1 + 1) → E}
    {a : F} {B : Matrix (Fin (M + 1 + 1)) (Fin (M + 1)) E} {J₁ : Matrix (Fin (M + 1)) (Fin (M + 1)) E}
    {y : Fin 1 → Fin (M + 1) → E} {b : F} {C : Matrix (Fin (M + 1)) (Fin M) E}
    {J₀ : Matrix (Fin M) (Fin M) E} (h₁ : StepData σ J x a B J₁)
    {e : Hstab (AF F) σ J x ≃* HA (AF F) σ J₁} {e' : Hstab (AF F) σ J₁ y ≃* HA (AF F) σ J₀}
    (he : ∀ g : Hstab (AF F) σ J x, FrameRelR (AF F) σ J J₁ B (g : HA (AF F) σ J) (e g))
    (he' : ∀ g : Hstab (AF F) σ J₁ y, FrameRelR (AF F) σ J₁ J₀ C (g : HA (AF F) σ J₁) (e' g))
    (ce : Continuous e.symm) (ce' : Continuous e'.symm)
    {μ₀ : Measure (HA (AF F) σ J₀)} [μ₀.IsHaarMeasure] {μ₁ : Measure (HA (AF F) σ J₁)}
    {τ : Measure (HA (AF F) σ J)}
    (r' : StepRel s σ J₁ y b C J₀ μ₁ μ₀) (r : StepRel s σ J x a B J₁ τ μ₁)
    {ν : Measure (Fin 1 → Fin (M + 1 + 1) → AF F ⊗[F] E)}
    {ν' : Measure (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)}
    (hν : IsStdX s σ J a ν) (hν' : IsStdX s σ J₁ b ν')
    (oν : OnOrbit (AF F) σ J x ν) (oν' : OnOrbit (AF F) σ J₁ y ν')
    {N : Measure (Fin 2 → Fin (M + 1 + 1) → AF F ⊗[F] E)} (hN : TwoStep (AF F) σ J x B ν ν' N)
    {f : HA (AF F) σ J → ℝ≥0∞} (hf : Measurable f)
    {t : (Fin 2 → Fin (M + 1 + 1) → AF F ⊗[F] E) → HA (AF F) σ J} (ht : Measurable t)
    (hs : ∀ Y, (∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) ![x 0, B *ᵥ y 0] = Y) →
      t Y • ratTup (F := F) (AF F) ![x 0, B *ᵥ y 0] = Y) :
    ∫⁻ g, f g ∂τ = ∫⁻ X, ∫⁻ h, f (t X * emb (AF F) e e' h) ∂μ₀ ∂N := by
  obtain ⟨L, hL⟩ := leftInv h₁
  obtain ⟨u, hu⟩ := exists_sec (σ := σ) (AF F) J x
  obtain ⟨u', hu'⟩ := exists_sec (σ := σ) (AF F) J₁ y
  have c1 : Continuous fun g : HA (AF F) σ J₁ => (e.symm g : HA (AF F) σ J) :=
    continuous_subtype_val.comp ce
  have c2 : Continuous fun g : HA (AF F) σ J₀ => (e'.symm g : HA (AF F) σ J₁) :=
    continuous_subtype_val.comp ce'
  have cι : Continuous (emb (AF F) e e') := c1.comp c2
  rw [hN _ (meas_avg μ₀ cι hf ht) u hu, r ν hν e he f hf u hu]
  refine lintegral_congr_ae ?_
  have a1 : ∀ᵐ z ∂ν, ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = z := ae_iff.2 oν
  have a2 : ∀ᵐ z ∂ν', ∃ g : HA (AF F) σ J₁, g • ratTup (F := F) (AF F) y = z := ae_iff.2 oν'
  filter_upwards [a1] with z hz
  have m1 : Measurable fun h' : Hstab (AF F) σ J x => f (u z * (h' : HA (AF F) σ J)) :=
    hf.comp (measurable_subtype_coe.const_mul _)
  have m2 : Measurable fun g : HA (AF F) σ J₁ => f (u z * (e.symm g : HA (AF F) σ J)) :=
    hf.comp (c1.measurable.const_mul _)
  rw [lintegral_map m1 ce.measurable, r' ν' hν' e' he' _ m2 u' hu']
  refine lintegral_congr_ae ?_
  filter_upwards [a2] with z' hz'
  have m3 : Measurable fun h' : Hstab (AF F) σ J₁ y =>
      f (u z * (e.symm (u' z' * (h' : HA (AF F) σ J₁)) : HA (AF F) σ J)) :=
    m2.comp (measurable_subtype_coe.const_mul _)
  rw [lintegral_map m3 ce'.measurable]
  have hp : pairOf (AF F) σ J B z (u z) z' =
      (u z * (e.symm (u' z') : HA (AF F) σ J)) • ratTup (F := F) (AF F) ![x 0, B *ᵥ y 0] := by
    rw [← pair_eq he, hu z hz, hu' z' hz']
  set g := u z * (e.symm (u' z') : HA (AF F) σ J) with hg
  have h3 := hs _ ⟨g, hp.symm⟩
  obtain ⟨h₀, hh₀⟩ := emb_surj (e' := e') hL he (g⁻¹ * t (pairOf (AF F) σ J B z (u z) z'))
    (by rw [mul_smul, h3, hp, inv_smul_smul])
  have h4 : t (pairOf (AF F) σ J B z (u z) z') = g * emb (AF F) e e' h₀ := by
    rw [hh₀, mul_inv_cancel_left]
  rw [h4, ← lintegral_mul_left_eq_self _ h₀]
  refine lintegral_congr fun h => ?_
  simp only [hg, emb_apply, map_mul, Subgroup.coe_mul, mul_assoc]

theorem square : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) E) (x₁ x₂ : Fin 1 → Fin (M + 1 + 1) → E) (a₁ a₂ : F) (B₁ B₂ : Matrix (Fin (M + 1 + 1)) (Fin (M + 1)) E) (J₁ J₂ : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (y₁ y₂ : Fin 1 → Fin (M + 1) → E) (b₁ b₂ : F) (C₁ C₂ : Matrix (Fin (M + 1)) (Fin M) E) (J₀ : Matrix (Fin M) (Fin M) E) (μ₀ : Measure (HA (AF F) σ J₀)) (μ₁ : Measure (HA (AF F) σ J₁)) (μ₂ : Measure (HA (AF F) σ J₂)) (τ₁ τ₂ : Measure (HA (AF F) σ J)), 2 ≤ M → StepData σ J x₁ a₁ B₁ J₁ → StepData σ J₁ y₁ b₁ C₁ J₀ → StepData σ J x₂ a₂ B₂ J₂ → StepData σ J₂ y₂ b₂ C₂ J₀ → B₁ * C₁ = B₂ * C₂ → μ₀.IsHaarMeasure → StepRel s σ J₁ y₁ b₁ C₁ J₀ μ₁ μ₀ → StepRel s σ J x₁ a₁ B₁ J₁ τ₁ μ₁ → StepRel s σ J₂ y₂ b₂ C₂ J₀ μ₂ μ₀ → StepRel s σ J x₂ a₂ B₂ J₂ τ₂ μ₂ → τ₁ = τ₂ := by
  intro F E _ _ _ _ _ σ hσ d b s M J x₁ x₂ a₁ a₂ B₁ B₂ J₁ J₂ y₁ y₂ b₁ b₂ C₁ C₂ J₀ μ₀ μ₁ μ₂ τ₁ τ₂ hM
    h₁ h₁' h₂ h₂' hBC hμ r₁' r₁ r₂' r₂
  obtain ⟨d₁, ⟨e₁, he₁, -⟩, c₁⟩ := GlobalTheory.FrameStep.frameStep F E σ hσ (AF F) _ J x₁ a₁ B₁ J₁ h₁
  obtain ⟨d₁', ⟨e₁', he₁', -⟩, c₁'⟩ := GlobalTheory.FrameStep.frameStep F E σ hσ (AF F) _ J₁ y₁ b₁ C₁ J₀ h₁'
  obtain ⟨d₂, ⟨e₂, he₂, -⟩, c₂⟩ := GlobalTheory.FrameStep.frameStep F E σ hσ (AF F) _ J x₂ a₂ B₂ J₂ h₂
  obtain ⟨d₂', ⟨e₂', he₂', -⟩, c₂'⟩ := GlobalTheory.FrameStep.frameStep F E σ hσ (AF F) _ J₂ y₂ b₂ C₂ J₀ h₂'
  obtain ⟨ν₁, n₁, -⟩ := GlobalTheory.T.existsUnique_stdHermitianFibreProduct_of_rank_ge_three F E σ hσ d b s _ J a₁ (by omega) h₁.1 h₁.2.1
  obtain ⟨ν₁', n₁', -⟩ := GlobalTheory.T.existsUnique_stdHermitianFibreProduct_of_rank_ge_three F E σ hσ d b s _ J₁ b₁ (by omega) h₁'.1 h₁'.2.1
  obtain ⟨ν₂, n₂, -⟩ := GlobalTheory.T.existsUnique_stdHermitianFibreProduct_of_rank_ge_three F E σ hσ d b s _ J a₂ (by omega) h₂.1 h₂.2.1
  obtain ⟨ν₂', n₂', -⟩ := GlobalTheory.T.existsUnique_stdHermitianFibreProduct_of_rank_ge_three F E σ hσ d b s _ J₂ b₂ (by omega) h₂'.1 h₂'.2.1
  obtain ⟨-, -, o₁, f₁, -⟩ := GlobalTheory.T.stdHermitianFibreMeasure_invariant_orbit_finite_nonzero F E σ hσ d b s _ J x₁ a₁ ν₁ h₁.1 h₁.2.1 h₁.2.2.1 n₁
  obtain ⟨-, i₁', o₁', f₁', -⟩ :=
    GlobalTheory.T.stdHermitianFibreMeasure_invariant_orbit_finite_nonzero F E σ hσ d b s _ J₁ y₁ b₁ ν₁' h₁'.1 h₁'.2.1 h₁'.2.2.1 n₁'
  obtain ⟨-, -, o₂, f₂, -⟩ := GlobalTheory.T.stdHermitianFibreMeasure_invariant_orbit_finite_nonzero F E σ hσ d b s _ J x₂ a₂ ν₂ h₂.1 h₂.2.1 h₂.2.2.1 n₂
  obtain ⟨-, i₂', o₂', f₂', -⟩ :=
    GlobalTheory.T.stdHermitianFibreMeasure_invariant_orbit_finite_nonzero F E σ hσ d b s _ J₂ y₂ b₂ ν₂' h₂'.1 h₂'.2.1 h₂'.2.2.1 n₂'
  obtain ⟨N₁, t₁, -⟩ := GlobalTheory.T.existsUnique_unitaryTwoStepPairMeasure F E σ hσ (AF F) _ J x₁ a₁ B₁ J₁ ν₁ ν₁' h₁ o₁ f₁ f₁' i₁'
  obtain ⟨N₂, t₂, -⟩ := GlobalTheory.T.existsUnique_unitaryTwoStepPairMeasure F E σ hσ (AF F) _ J x₂ a₂ B₂ J₂ ν₂ ν₂' h₂ o₂ f₂ f₂' i₂'
  obtain ⟨γ, hγ⟩ := exists_gamma h₁ h₁' h₂ h₂' hBC d₁ d₁' d₂
  have hN := GlobalTheory.T.adelicTwoStepMeasure_orthogonalBases_plane_compare F E σ hσ d b s _ J x₁ a₁ B₁ J₁ x₂ a₂ B₂ J₂ y₁ y₂ b₁ b₂ γ h₁ h₂ h₁'.2.1
    h₂'.2.1 h₁'.2.2.1 h₂'.2.2.1 hγ ν₁ ν₂ ν₁' ν₂' N₁ N₂ n₁ n₁' n₂ n₂' t₁ t₂
  set G : Matrix (Fin 2) (Fin 2) (AF F ⊗[F] E) :=
    (γ : Matrix (Fin 2) (Fin 2) E).map (inclR (F := F) (AF F)) with hG
  set G' : Matrix (Fin 2) (Fin 2) (AF F ⊗[F] E) :=
    ((γ⁻¹ : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E).map (inclR (F := F) (AF F)) with hG'
  have g1 : G * G' = 1 := by
    rw [hG, hG', ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have g2 : G' * G = 1 := by
    rw [hG, hG', ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hX : ratTup (F := F) (AF F) ![x₂ 0, B₂ *ᵥ y₂ 0] =
      lrAct 1 G (ratTup (F := F) (AF F) ![x₁ 0, B₁ *ᵥ y₁ 0]) := by
    rw [hγ, ratTup_lrAct]
  have cG : ∀ P : Matrix (Fin 2) (Fin 2) (AF F ⊗[F] E),
      Measurable (lrAct (M := M + 1 + 1) 1 P) := by
    intro P
    refine Continuous.measurable (continuous_pi fun a => continuous_pi fun i => ?_)
    simp only [lrAct, Matrix.one_mulVec]
    fun_prop
  have hι : ∀ h, emb (AF F) e₂ e₂' h = emb (AF F) e₁ e₁' h := by
    intro h
    obtain ⟨L, hL⟩ := leftInv h₁
    obtain ⟨L', hL'⟩ := leftInv h₁'
    have k1 := emb_fix (e' := e₂') he₂ h
    rw [hX, smul_lrAct] at k1
    have k2 := congrArg (lrAct 1 G') k1
    rw [lrAct_lrAct, lrAct_lrAct, g1, lrAct_one, lrAct_one] at k2
    obtain ⟨h', hh'⟩ := emb_surj (e' := e₁') hL he₁ _ k2
    have k3 := emb_rel he₁ he₁' h'
    have k4 := emb_rel he₂ he₂' h
    rw [← hBC, ← hh', k3] at k4
    have hLL : (L' * L) * (B₁ * C₁) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc L, hL, Matrix.one_mul, hL']
    rw [← hh', mt_inj _ (cancel_mat _ hLL k4)]
  obtain ⟨-, t, mt₁, ht⟩ := GlobalTheory.OrbitSection.measurableSet_orbit_and_exists_section (HA (AF F) σ J) (Fin 2 → Fin (M + 1 + 1) → AF F ⊗[F] E)
    (ratTup (F := F) (AF F) ![x₁ 0, B₁ *ᵥ y₁ 0])
  have mt₂ : Measurable fun Y => t (lrAct 1 G' Y) := mt₁.comp (cG G')
  have ht₂ : ∀ Y, (∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) ![x₂ 0, B₂ *ᵥ y₂ 0] = Y) →
      t (lrAct 1 G' Y) • ratTup (F := F) (AF F) ![x₂ 0, B₂ *ᵥ y₂ 0] = Y := by
    rintro Y ⟨g, rfl⟩
    rw [hX, smul_lrAct, smul_lrAct, lrAct_lrAct, g1, lrAct_one, ht _ ⟨g, rfl⟩]
  have cι : Continuous (emb (AF F) e₂ e₂') :=
    (continuous_subtype_val.comp (c₂ e₂ he₂).2).comp (continuous_subtype_val.comp (c₂' e₂' he₂').2)
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [unfold_two h₁ he₁ he₁' (c₁ e₁ he₁).2 (c₁' e₁' he₁').2 r₁' r₁ n₁ n₁' o₁ o₁' t₁ hf mt₁ ht,
    unfold_two h₂ he₂ he₂' (c₂ e₂ he₂).2 (c₂' e₂' he₂').2 r₂' r₂ n₂ n₂' o₂ o₂' t₂ hf mt₂ ht₂,
    hN, lintegral_map (meas_avg μ₀ cι hf mt₂) (cG G)]
  simp only [lrAct_lrAct, g1, lrAct_one, hι]

end Main

end GlobalTheory.GaugeSquare
