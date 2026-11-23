import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Lemmata.ProductIdentities.ProdInvZpowMulOfProdZpowEqOne

open Matrix MeasureTheory Formalism.BasicNotions.TH

noncomputable section

namespace Formalism.MainNotions.DIV.Inh

section DetExp

open NormedSpace

variable {n : Type} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_exp_entry (X : Matrix n n ℂ) (i j : n) :
    HasDerivAt (fun t : ℝ => (exp (t • X)) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, exp_zero, one_mul] at h
  let L : Matrix n n ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_det_of_one (A : ℝ → Matrix n n ℂ) (A' : Matrix n n ℂ) (h0 : A 0 = 1)
    (h : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) :
    HasDerivAt (fun t => (A t).det) A'.trace 0 := by
  first | exact Bl.ProductIdentities.goal1 .. | (apply Bl.ProductIdentities.goal1 <;> assumption) | (intros; apply Bl.ProductIdentities.goal1 <;> assumption)

theorem det_exp (X : Matrix n n ℂ) : (exp X).det = Complex.exp X.trace := by
  set φ : ℝ → ℂ := fun t => (exp (t • X)).det with hφ
  have hmul : ∀ s t, φ (s + t) = φ s * φ t := by
    intro s t
    simp only [hφ, add_smul]
    rw [Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t), det_mul]
  have h0 : HasDerivAt φ X.trace 0 :=
    hasDerivAt_det_of_one _ _ (by simp) (hasDerivAt_exp_entry X)
  have hd : ∀ t, HasDerivAt φ (φ t * X.trace) t := by
    intro t
    have h1 : HasDerivAt (fun s => φ (s - t)) X.trace t := by
      have h00 := h0
      rw [← sub_self t] at h00
      exact h00.comp_sub_const t t
    have h2 := h1.const_mul (φ t)
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    show φ s = φ t * φ (s - t)
    rw [← hmul]; congr 1; ring
  let ψ : ℝ → ℂ := fun t => φ t * Complex.exp (-((t : ℂ) * X.trace))
  have hψ : ∀ t, HasDerivAt ψ 0 t := by
    intro t
    have e0 : HasDerivAt (fun t : ℝ => -((t : ℂ) * X.trace)) (-(1 * X.trace)) t := by
      have h := ((hasDerivAt_id t).ofReal_comp.mul_const X.trace).fun_neg
      simpa using h
    have e1 := e0.cexp
    have h3 := (hd t).fun_mul e1
    have h4 : φ t * X.trace * Complex.exp (-((t : ℂ) * X.trace)) +
        φ t * (Complex.exp (-((t : ℂ) * X.trace)) * -(1 * X.trace)) = 0 := by ring
    rw [h4] at h3
    exact h3
  have hc := is_const_of_deriv_eq_zero (fun t => (hψ t).differentiableAt) (fun t => (hψ t).deriv) 1 0
  simp only [ψ, hφ, one_smul, zero_smul, exp_zero, det_one, Complex.ofReal_one, one_mul,
    Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one] at hc
  rw [Complex.exp_neg] at hc
  exact (eq_of_mul_inv_eq_one hc)

end DetExp

variable (p q : ℕ)

theorem cT_eq (M : Mat p q) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := rfl

theorem Jm_sq : Jm p q * Jm p q = 1 := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem mem_Upq_iff (g : GL (Ix p q) ℂ) :
    g ∈ Formalism.UG.Upq p q ↔ (g : Mat p q)ᴴ * Jm p q * (g : Mat p q) = Jm p q := Iff.rfl

def covSub : Subgroup (GL (Ix p q) ℂ × ℂˣ) where
  carrier := {x | x.1 ∈ Formalism.UG.Upq p q ∧ ((x.2 : ℂˣ) : ℂ) ^ 2 = ((x.1 : GL (Ix p q) ℂ) : Mat p q).det}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨mul_mem ha hb, by simp [mul_pow, ha', hb']⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    have h1 : ((a.1⁻¹ : GL (Ix p q) ℂ) : Mat p q).det * ((a.1 : GL (Ix p q) ℂ) : Mat p q).det = 1 := by
      rw [← det_mul, ← Units.val_mul]; simp
    show ((a.2⁻¹ : ℂˣ) : ℂ) ^ 2 = ((a.1⁻¹ : GL (Ix p q) ℂ) : Mat p q).det
    rw [Units.val_inv_eq_inv_val, inv_pow, ha']
    exact (eq_inv_of_mul_eq_one_left h1).symm

instance : LocallyCompactSpace (Mat p q) :=
  inferInstanceAs (LocallyCompactSpace (Ix p q → Ix p q → ℂ))

theorem covSub_closed : IsClosed (covSub p q : Set (GL (Ix p q) ℂ × ℂˣ)) := by
  have hv : Continuous fun x : GL (Ix p q) ℂ × ℂˣ => ((x.1 : GL (Ix p q) ℂ) : Mat p q) :=
    Units.continuous_val.comp continuous_fst
  have h1 : IsClosed {x : GL (Ix p q) ℂ × ℂˣ |
      ((x.1 : GL (Ix p q) ℂ) : Mat p q)ᴴ * Jm p q * ((x.1 : GL (Ix p q) ℂ) : Mat p q) = Jm p q} :=
    isClosed_eq ((hv.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hv) continuous_const
  have h2 : IsClosed {x : GL (Ix p q) ℂ × ℂˣ |
      ((x.2 : ℂˣ) : ℂ) ^ 2 = ((x.1 : GL (Ix p q) ℂ) : Mat p q).det} :=
    isClosed_eq ((Units.continuous_val.comp continuous_snd).pow 2) hv.matrix_det
  exact h1.inter h2

instance : LocallyCompactSpace (covSub p q) :=
  (covSub_closed p q).isClosedEmbedding_subtypeVal.locallyCompactSpace

variable {p q}

theorem exp_mul_exp_neg (X : Mat p q) : NormedSpace.exp X * NormedSpace.exp (-X) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl X))]; simp

theorem exp_neg_mul_exp (X : Mat p q) : NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl X))]; simp

def expU (X : Mat p q) : GL (Ix p q) ℂ :=
  ⟨NormedSpace.exp X, NormedSpace.exp (-X), exp_mul_exp_neg X, exp_neg_mul_exp X⟩

def expC (z : ℂ) : ℂˣ :=
  ⟨Complex.exp z, Complex.exp (-z), by rw [← Complex.exp_add]; simp, by rw [← Complex.exp_add]; simp⟩

theorem expU_mem {X : Mat p q} (h : X ∈ upq p q) : expU X ∈ Formalism.UG.Upq p q := by
  rw [mem_Upq_iff]
  show (NormedSpace.exp X)ᴴ * Jm p q * NormedSpace.exp X = Jm p q
  have hX : Xᴴ * Jm p q + Jm p q * X = 0 := h
  have hJ := Jm_sq p q
  have hinv : (Jm p q)⁻¹ = Jm p q := Matrix.inv_eq_right_inv hJ
  have hu : IsUnit (Jm p q) := ⟨⟨Jm p q, Jm p q, hJ, hJ⟩, rfl⟩
  have h1 : Xᴴ = Jm p q * (-X) * (Jm p q)⁻¹ := by
    rw [hinv]
    have : Xᴴ * Jm p q = -(Jm p q * X) := eq_neg_of_add_eq_zero_left hX
    calc Xᴴ = Xᴴ * (Jm p q * Jm p q) := by rw [hJ, Matrix.mul_one]
      _ = (Xᴴ * Jm p q) * Jm p q := by rw [Matrix.mul_assoc]
      _ = Jm p q * (-X) * Jm p q := by rw [this, Matrix.mul_neg]
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ hu, hinv]
  calc Jm p q * NormedSpace.exp (-X) * Jm p q * Jm p q * NormedSpace.exp X
      = Jm p q * (NormedSpace.exp (-X) * (Jm p q * Jm p q) * NormedSpace.exp X) := by
        simp only [Matrix.mul_assoc]
    _ = Jm p q := by rw [hJ, Matrix.mul_one, exp_neg_mul_exp, Matrix.mul_one]

theorem exp_pair_mem {X : Mat p q} (h : X ∈ upq p q) :
    (expU X, expC (X.trace / 2)) ∈ covSub p q := by
  refine ⟨expU_mem h, ?_⟩
  show Complex.exp (X.trace / 2) ^ 2 = (NormedSpace.exp X).det
  rw [det_exp, ← Complex.exp_nat_mul]
  congr 1; push_cast; ring

theorem smul_mem_upq {X : Mat p q} (h : X ∈ upq p q) (s : ℝ) : s • X ∈ upq p q := by
  have hX : Xᴴ * Jm p q + Jm p q * X = 0 := h
  show (s • X)ᴴ * Jm p q + Jm p q * (s • X) = 0
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

theorem zero_mem_upq : (0 : Mat p q) ∈ upq p q := by
  show (0 : Mat p q)ᴴ * Jm p q + Jm p q * 0 = 0
  simp

open Classical in

def exptStd (X : Mat p q) : covSub p q :=
  if h : X ∈ upq p q then ⟨(expU X, expC (X.trace / 2)), exp_pair_mem h⟩ else 1

theorem exptStd_of_mem {X : Mat p q} (h : X ∈ upq p q) :
    exptStd X = ⟨(expU X, expC (X.trace / 2)), exp_pair_mem h⟩ := dif_pos h

open scoped Matrix.Norms.Operator in
theorem continuous_matExp : Continuous (NormedSpace.exp : Mat p q → Mat p q) :=
  NormedSpace.exp_continuous

theorem exptStd_cont : ContinuousOn (exptStd (p := p) (q := q)) (upq p q) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous fun X : upq p q =>
      (⟨(expU (X : Mat p q), expC ((X : Mat p q).trace / 2)), exp_pair_mem X.2⟩ : covSub p q) := by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
    · refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · exact continuous_matExp.comp continuous_subtype_val
      · exact continuous_matExp.comp continuous_subtype_val.neg
    · have ht : Continuous fun X : upq p q => (X : Mat p q).trace / 2 :=
        (continuous_subtype_val.matrix_trace).div_const 2
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · exact Complex.continuous_exp.comp ht
      · exact Complex.continuous_exp.comp ht.neg
  refine hc.congr fun X => ?_
  exact (exptStd_of_mem X.2).symm

variable (p q)

def stdGrp : GrpData p q :=
  letI : MeasurableSpace (covSub p q) := borel _
  haveI : BorelSpace (covSub p q) := ⟨rfl⟩
  { G := covSub p q
    haar := Measure.haar
    cov := (MonoidHom.fst _ _).comp (covSub p q).subtype
    sq := (MonoidHom.snd _ _).comp (covSub p q).subtype
    cov_mem := fun x => x.2.1
    sq_sq := fun x => x.2.2
    bij := fun g hg w hw => ⟨⟨(g, w), hg, hw⟩, ⟨rfl, rfl⟩, fun y hy => Subtype.ext (Prod.ext hy.1 hy.2)⟩
    emb := Topology.IsEmbedding.subtypeVal
    expt := exptStd
    expt_cov := fun X hX => by rw [exptStd_of_mem hX]; rfl
    expt_cont := exptStd_cont
    expt_zero := by
      rw [exptStd_of_mem zero_mem_upq]
      refine Subtype.ext (Prod.ext (Units.ext ?_) (Units.ext ?_))
      · show NormedSpace.exp (0 : Mat p q) = 1
        exact NormedSpace.exp_zero
      · show Complex.exp ((0 : Mat p q).trace / 2) = 1
        simp
    expt_add := fun X hX s t => by
      rw [exptStd_of_mem (smul_mem_upq hX _), exptStd_of_mem (smul_mem_upq hX s),
        exptStd_of_mem (smul_mem_upq hX t)]
      refine Subtype.ext (Prod.ext (Units.ext ?_) (Units.ext ?_))
      · show NormedSpace.exp ((s + t) • X) = NormedSpace.exp (s • X) * NormedSpace.exp (t • X)
        rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)]
      · show Complex.exp (((s + t) • X).trace / 2) =
          Complex.exp ((s • X).trace / 2) * Complex.exp ((t • X).trace / 2)
        rw [← Complex.exp_add, add_smul, Matrix.trace_add, add_div] }

theorem nonempty_TH_GrpData : Nonempty (GrpData p q) := ⟨stdGrp p q⟩

section Emb

open scoped Kronecker

theorem Jm_apply {p q : ℕ} (a b : Ix p q) :
    Jm p q a b = if a = b then (if a.isLeft then 1 else -1) else 0 := by
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.one_apply]
  split_ifs <;> simp

variable (p q r s : ℕ)

def krMat (A : Mat p q) (B : Mat r s) : Mat (p * r + q * s) (p * s + q * r) :=
  Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s) (Matrix.kroneckerMap (· * ·) A B)

theorem krMat_mul (A A' : Mat p q) (B B' : Mat r s) :
    krMat p q r s (A * A') (B * B') = krMat p q r s A B * krMat p q r s A' B' := by
  simp only [krMat, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv]
  congr 1
  exact Matrix.mul_kronecker_mul A A' B B'

theorem krMat_one : krMat p q r s 1 1 = 1 := by
  simp only [krMat, Matrix.reindex_apply]
  have : Matrix.kroneckerMap (· * ·) (1 : Mat p q) (1 : Mat r s) = 1 := Matrix.one_kronecker_one
  rw [this, Matrix.submatrix_one_equiv]

theorem krMat_conjTranspose (A : Mat p q) (B : Mat r s) :
    (krMat p q r s A B)ᴴ = krMat p q r s Aᴴ Bᴴ := by
  simp only [krMat, Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
  congr 1
  exact Matrix.conjTranspose_kronecker A B

theorem krMat_Jm : krMat p q r s (Jm p q) (Jm r s) = Jm (p * r + q * s) (p * s + q * r) := by
  ext i j
  obtain ⟨l, rfl⟩ := (lineEquiv p q r s).surjective i
  obtain ⟨l', rfl⟩ := (lineEquiv p q r s).surjective j
  rw [Jm_apply, lineEquiv_isLeft]
  simp only [krMat, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.kroneckerMap_apply, Jm_apply, EmbeddingLike.apply_eq_iff_eq]
  rcases l with ⟨a, c⟩
  rcases l' with ⟨a', c'⟩
  by_cases h1 : a = a' <;> by_cases h2 : c = c' <;> simp [h1, h2, Prod.ext_iff]
  subst h1; subst h2
  rcases a with a | a <;> rcases c with c | c <;> simp [linePos]

theorem krMat_det (A : Mat p q) (B : Mat r s) :
    (krMat p q r s A B).det = A.det ^ (r + s) * B.det ^ (p + q) := by
  simp only [krMat]
  rw [Matrix.det_reindex_self]
  have := Matrix.det_kronecker A B
  simpa using this

def krGL : GL (Ix p q) ℂ × GL (Ix r s) ℂ →* GL (Ix (p * r + q * s) (p * s + q * r)) ℂ where
  toFun x := ⟨krMat p q r s x.1 x.2, krMat p q r s (x.1⁻¹ : GL (Ix p q) ℂ) (x.2⁻¹ : GL (Ix r s) ℂ),
    by rw [← krMat_mul, Units.mul_inv, Units.mul_inv, krMat_one],
    by rw [← krMat_mul, Units.inv_mul, Units.inv_mul, krMat_one]⟩
  map_one' := Units.ext (krMat_one p q r s)
  map_mul' x y := Units.ext (krMat_mul p q r s _ _ _ _)

theorem kr_mem (x : covSub p q) (y : covSub r s) :
    (krGL p q r s (x.1.1, y.1.1), x.1.2 ^ (r + s) * y.1.2 ^ (p + q)) ∈
      covSub (p * r + q * s) (p * s + q * r) := by
  refine ⟨?_, ?_⟩
  · rw [mem_Upq_iff]
    show (krMat p q r s x.1.1 y.1.1)ᴴ * Jm _ _ * krMat p q r s x.1.1 y.1.1 = Jm _ _
    rw [krMat_conjTranspose, ← krMat_Jm, ← krMat_mul, ← krMat_mul,
      (mem_Upq_iff p q _).1 x.2.1, (mem_Upq_iff r s _).1 y.2.1]
  · show (((x.1.2 ^ (r + s) * y.1.2 ^ (p + q) : ℂˣ)) : ℂ) ^ 2 = (krMat p q r s x.1.1 y.1.1).det
    rw [krMat_det, ← x.2.2, ← y.2.2]
    push_cast
    ring

def embStd : covSub p q × covSub r s →* covSub (p * r + q * s) (p * s + q * r) where
  toFun x := ⟨(krGL p q r s (x.1.1.1, x.2.1.1), x.1.1.2 ^ (r + s) * x.2.1.2 ^ (p + q)), kr_mem p q r s x.1 x.2⟩
  map_one' := Subtype.ext (Prod.ext (map_one (krGL p q r s)) (by simp))
  map_mul' x y := Subtype.ext (Prod.ext (map_mul (krGL p q r s) (x.1.1.1, x.2.1.1) (y.1.1.1, y.2.1.1))
    (by
      show (x.1.1.2 * y.1.1.2) ^ (r + s) * (x.2.1.2 * y.2.1.2) ^ (p + q) = _
      rw [mul_pow, mul_pow]; exact mul_mul_mul_comm _ _ _ _))

structure FockCore where
  H : Type
  [nacg : NormedAddCommGroup H]
  [ips : InnerProductSpace ℂ H]
  [cs : CompleteSpace H]
  Om : (stdGrp (p * r + q * s) (p * s + q * r)).G →* (H →L[ℂ] H)
  isom : ∀ g x, ‖Om g x‖ = ‖x‖
  cont : ∀ x, Continuous fun g => Om g x
  ι : Pol p q r s →ₗ[ℂ] H
  ι_inj : Function.Injective ι
  dense : Dense (Set.range ι)
  fockIP : ∀ α β, inner ℂ (ι (MvPolynomial.monomial α 1)) (ι (MvPolynomial.monomial β 1)) =
    if α = β then α.prod (fun _ k => (k.factorial : ℂ)) else 0
  der : ∀ Z ∈ upq (p * r + q * s) (p * s + q * r), ∀ P,
    HasDerivAt (fun t : ℝ => Om ((stdGrp (p * r + q * s) (p * s + q * r)).expt (t • Z)) (ι P))
      (ι (omAct p q r s
        (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm Z) P)) 0

attribute [instance] FockCore.nacg FockCore.ips FockCore.cs

variable {p q r s}

def FockCore.toFockData (C : FockCore p q r s) :
    FockData (stdGrp (p * r + q * s) (p * s + q * r)) (stdGrp p q) (stdGrp r s) where
  H := C.H
  Om := C.Om
  isom := C.isom
  cont := C.cont
  ι := C.ι
  ι_inj := C.ι_inj
  dense := C.dense
  fockIP := C.fockIP
  der := C.der
  emb := embStd p q r s
  emb_cov := fun _ _ => rfl
  emb_sq := fun _ _ => rfl

end Emb

section Checks

open MvPolynomial

variable {p q r s : ℕ}

abbrev Xm (l : Ln p q r s) : Module.End ℂ (Pol p q r s) := LinearMap.mulLeft ℂ (X l)

abbrev Dm (l : Ln p q r s) : Module.End ℂ (Pol p q r s) := (pderiv l).toLinearMap

theorem XX (l l' : Ln p q r s) : Xm l * Xm l' = Xm l' * Xm l := by
  ext1 P
  apply LinearMap.ext; intro P
  simp [mul_left_comm]

theorem DD (l l' : Ln p q r s) : Dm l * Dm l' = Dm l' * Dm l := by
  have h : ⁅(pderiv l : Derivation ℂ (Pol p q r s) (Pol p q r s)),
      (pderiv l' : Derivation ℂ (Pol p q r s) (Pol p q r s))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro i
    simp only [Derivation.commutator_apply, pderiv_X, Derivation.coe_zero, Pi.zero_apply]
    by_cases h1 : l' = i <;> by_cases h2 : l = i <;> simp [h1, h2]
  apply LinearMap.ext; intro P
  have := congrArg (fun D : Derivation ℂ (Pol p q r s) (Pol p q r s) => D P) h
  simp only [Derivation.commutator_apply, Derivation.coe_zero, Pi.zero_apply] at this
  exact sub_eq_zero.1 this

theorem DX (l l' : Ln p q r s) : Dm l * Xm l' = Xm l' * Dm l + if l = l' then 1 else 0 := by
  apply LinearMap.ext; intro P
  have hL : (Dm l * Xm l') P = pderiv l (X l' * P) := rfl
  have hR : (Xm l' * Dm l) P = X l' * pderiv l P := rfl
  rw [LinearMap.add_apply, hL, hR, Derivation.leibniz, pderiv_X]
  by_cases h : l = l'
  · subst h; simp
  · simp [h, Ne.symm h]

theorem ne_of_sign {l l' : Ln p q r s} (h : linePos l ≠ linePos l') : l ≠ l' := fun e => h (e ▸ rfl)

theorem low_rai (l l' : Ln p q r s) : lowB l * raiB l' = raiB l' * lowB l + if l = l' then 1 else 0 := by
  unfold lowB raiB
  cases h : linePos l <;> cases h' : linePos l'
  · simp only [Bool.false_eq_true, if_false]
    have := DX l' l
    rw [mul_neg, neg_mul, this]
    by_cases e : l = l'
    · subst e; simp
    · simp [e, Ne.symm e]
  · have e : l ≠ l' := ne_of_sign (by rw [h, h']; simp)
    simp only [Bool.false_eq_true, if_false, if_true, e, add_zero]
    exact XX l l'
  · have e : l ≠ l' := ne_of_sign (by rw [h, h']; simp)
    simp only [Bool.false_eq_true, if_false, if_true, e, add_zero]
    rw [mul_neg, neg_mul, DD]
  · simp only [if_true]
    exact DX l l'

theorem low_low (l l' : Ln p q r s) : lowB l * lowB l' = lowB l' * lowB l := by
  unfold lowB
  cases h : linePos l <;> cases h' : linePos l'
  · simp only [Bool.false_eq_true, if_false]; exact XX l l'
  · have e : l' ≠ l := ne_of_sign (by rw [h, h']; simp)
    simp only [Bool.false_eq_true, if_false, if_true]
    have := DX l' l
    simp only [e, if_false, add_zero] at this
    exact this.symm
  · have e : l ≠ l' := ne_of_sign (by rw [h, h']; simp)
    simp only [Bool.false_eq_true, if_false, if_true]
    have := DX l l'
    simp only [e, if_false, add_zero] at this
    exact this
  · simp only [if_true]; exact DD l l'

theorem rai_rai (l l' : Ln p q r s) : raiB l * raiB l' = raiB l' * raiB l := by
  unfold raiB
  cases h : linePos l <;> cases h' : linePos l'
  · simp only [Bool.false_eq_true, if_false]; rw [neg_mul_neg, neg_mul_neg]; exact DD l l'
  · have e : l ≠ l' := ne_of_sign (by rw [h, h']; simp)
    simp only [Bool.false_eq_true, if_false, if_true]
    have := DX l l'
    simp only [e, if_false, add_zero] at this
    rw [neg_mul, mul_neg, this]
  · have e : l' ≠ l := ne_of_sign (by rw [h, h']; simp)
    simp only [Bool.false_eq_true, if_false, if_true]
    have := DX l' l
    simp only [e, if_false, add_zero] at this
    rw [neg_mul, mul_neg, this]
  · simp only [if_true]; exact XX l l'

theorem omE_bracket (l l' m m' : Ln p q r s) :
    omE l l' * omE m m' - omE m m' * omE l l' =
      (if l' = m then omE l m' else 0) - (if m' = l then omE m l' else 0) := by
  have h1 := low_rai l' m
  have h2 := low_rai m' l
  have h3 := rai_rai l m
  have h4 := low_low l' m'
  set A := raiB l
  set B := lowB l'
  set C := raiB m
  set D := lowB m'
  have key : A * B * (C * D) - C * D * (A * B) =
      A * (if l' = m then 1 else 0) * D - C * (if m' = l then 1 else 0) * B := by
    have e1 : A * B * (C * D) = A * (B * C) * D := by noncomm_ring
    have e2 : C * D * (A * B) = C * (D * A) * B := by noncomm_ring
    rw [e1, e2, h1, h2]
    have e3 : ∀ d, A * (C * B + d) * D = (A * C) * (B * D) + A * d * D := by intro d; noncomm_ring
    have e4 : ∀ d, C * (A * D + d) * B = (C * A) * (D * B) + C * d * B := by intro d; noncomm_ring
    rw [e3, e4, h3, h4]; abel
  have hc : ∀ (c : ℂ) (T : Module.End ℂ (Pol p q r s)), (c • (1 : Module.End ℂ (Pol p q r s))) * T = T * (c • 1) := by
    intro c T; simp
  have hk : ∀ (P : Prop) [Decidable P] (T : Module.End ℂ (Pol p q r s)),
      (if P then (1 / 2 : ℂ) • (1 : Module.End ℂ (Pol p q r s)) else 0) * T =
        T * (if P then (1 / 2 : ℂ) • 1 else 0) := by
    intro P _ T; split_ifs
    · exact hc _ T
    · simp
  have expand : omE l l' * omE m m' - omE m m' * omE l l' = A * B * (C * D) - C * D * (A * B) := by
    simp only [omE]
    rw [add_mul, mul_add, mul_add, add_mul, mul_add, mul_add, hk (l = l') (C * D), hk (m = m') (A * B),
      hk (l = l') (if m = m' then (1 / 2 : ℂ) • 1 else 0)]
    abel
  rw [expand, key]
  by_cases a : l' = m <;> by_cases b : m' = l
  · subst a; subst b; simp [omE, A, B, C, D]
  · simp [a, b, omE, A, D, Ne.symm b]
  · simp [a, b, omE, C, B, Ne.symm a]
  · simp [a, b]

end Checks

section Skew

open MvPolynomial

variable {p q r s : ℕ}

def fac (α : Ln p q r s →₀ ℕ) : ℂ := α.prod (fun _ k => (k.factorial : ℂ))

theorem fac_succ (l : Ln p q r s) (α : Ln p q r s →₀ ℕ) :
    fac (Finsupp.single l 1 + α) = ((α l : ℂ) + 1) * fac α := by
  unfold fac
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l),
    ← Finset.mul_prod_erase Finset.univ (fun i => ((α i).factorial : ℂ)) (Finset.mem_univ l)]
  have : ∏ x ∈ Finset.univ.erase l, ((((Finsupp.single l 1 + α : Ln p q r s →₀ ℕ) x).factorial : ℕ) : ℂ) =
      ∏ x ∈ Finset.univ.erase l, (((α x).factorial : ℕ) : ℂ) :=
    Finset.prod_congr rfl (fun x hx => by
      simp [(Finset.ne_of_mem_erase hx).symm])
  rw [this]
  have h2 : (Finsupp.single l 1 + α : Ln p q r s →₀ ℕ) l = α l + 1 := by simp [add_comm]
  rw [h2, Nat.factorial_succ]
  push_cast
  ring

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : Pol p q r s →ₗ[ℂ] H)

def FockIP : Prop := ∀ α β, inner ℂ (ι (monomial α 1)) (ι (monomial β 1)) = if α = β then fac α else 0

def IsAdj (T T' : Module.End ℂ (Pol p q r s)) : Prop :=
  ∀ P Q, inner ℂ (ι (T P)) (ι Q) = inner ℂ (ι P) (ι (T' Q))

variable {ι}

theorem IsAdj.mul {T T' S S' : Module.End ℂ (Pol p q r s)} (h : IsAdj ι T T') (k : IsAdj ι S S') :
    IsAdj ι (T * S) (S' * T') := fun P Q => by
  show inner ℂ (ι (T (S P))) (ι Q) = inner ℂ (ι P) (ι (S' (T' Q)))
  rw [h, k]

theorem IsAdj.add {T T' S S' : Module.End ℂ (Pol p q r s)} (h : IsAdj ι T T') (k : IsAdj ι S S') :
    IsAdj ι (T + S) (T' + S') := fun P Q => by
  simp only [LinearMap.add_apply, map_add, inner_add_left, inner_add_right, h P Q, k P Q]

theorem IsAdj.smul {T T' : Module.End ℂ (Pol p q r s)} (c : ℂ) (h : IsAdj ι T T') :
    IsAdj ι (c • T) (star c • T') := fun P Q => by
  simp only [LinearMap.smul_apply, map_smul, inner_smul_left, inner_smul_right, h P Q]
  rfl

theorem IsAdj.symm {T T' : Module.End ℂ (Pol p q r s)} (h : IsAdj ι T T') : IsAdj ι T' T := fun P Q => by
  rw [← inner_conj_symm, ← h Q P, inner_conj_symm]

theorem IsAdj.zero : IsAdj ι 0 0 := fun P Q => by simp

theorem IsAdj.one : IsAdj ι 1 1 := fun _ _ => rfl

theorem IsAdj.sum {κ : Type} (t : Finset κ) {T T' : κ → Module.End ℂ (Pol p q r s)}
    (h : ∀ i ∈ t, IsAdj ι (T i) (T' i)) : IsAdj ι (∑ i ∈ t, T i) (∑ i ∈ t, T' i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using IsAdj.zero
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mono_eq (α : Ln p q r s →₀ ℕ) (a : ℂ) : (monomial α a : Pol p q r s) = a • monomial α 1 := by
  simp [smul_monomial]

theorem adj_XD (hIP : FockIP ι) (l : Ln p q r s) : IsAdj ι (Xm l) (Dm l) := by
  intro P Q
  show inner ℂ (ι (X l * P)) (ι Q) = inner ℂ (ι P) (ι (pderiv l Q))
  induction P using MvPolynomial.induction_on' with
  | add P₁ P₂ h₁ h₂ => simp only [mul_add, map_add, inner_add_left, h₁, h₂]
  | monomial α a =>
    induction Q using MvPolynomial.induction_on' with
    | add Q₁ Q₂ h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]
    | monomial β b =>
      have e1 : (X l * monomial α a : Pol p q r s) = a • monomial (Finsupp.single l 1 + α) 1 := by
        rw [X, monomial_mul, one_mul, mono_eq]
      rw [e1, pderiv_monomial, mono_eq β b, mono_eq α a, mono_eq (β - Finsupp.single l 1)]
      simp only [map_smul, inner_smul_left, inner_smul_right, hIP _ _]
      by_cases h : Finsupp.single l 1 + α = β
      · subst h
        rw [if_pos rfl, add_tsub_cancel_left, if_pos rfl, fac_succ]
        simp [add_comm]
        ring
      · rw [if_neg h]
        by_cases hβ : β l = 0
        · simp [hβ]
        · have : α ≠ β - Finsupp.single l 1 := by
            intro e
            apply h
            rw [e]
            apply add_tsub_cancel_of_le
            rw [Finsupp.single_le_iff]
            omega
          rw [if_neg this]; simp

def eps (l : Ln p q r s) : ℂ := if linePos l then 1 else -1

theorem eps_star (l : Ln p q r s) : star (eps l) = eps l := by unfold eps; split_ifs <;> simp

theorem eps_sq (l : Ln p q r s) : eps l * eps l = 1 := by unfold eps; split_ifs <;> simp

theorem adj_rai (hIP : FockIP ι) (l : Ln p q r s) : IsAdj ι (raiB l) (eps l • lowB l) := by
  unfold raiB lowB eps
  cases h : linePos l
  · simp only [Bool.false_eq_true, if_false]
    have := ((adj_XD hIP l).symm).smul (-1)
    simpa using this
  · simp only [if_true, one_smul]
    exact adj_XD hIP l

theorem adj_low (hIP : FockIP ι) (l : Ln p q r s) : IsAdj ι (lowB l) (eps l • raiB l) := by
  have := ((adj_rai hIP l).symm).smul (eps l)
  rw [smul_smul, eps_sq, one_smul, eps_star] at this
  exact this

theorem adj_omE (hIP : FockIP ι) (l l' : Ln p q r s) :
    IsAdj ι (omE l l') ((eps l * eps l') • omE l' l) := by
  have h1 := (adj_rai hIP l).mul (adj_low hIP l')
  have h2 : IsAdj ι (if l = l' then (1 / 2 : ℂ) • (1 : Module.End ℂ (Pol p q r s)) else 0)
      (if l = l' then (1 / 2 : ℂ) • 1 else 0) := by
    split_ifs
    · have := (IsAdj.one (ι := ι)).smul (1 / 2 : ℂ)
      simpa using this
    · exact IsAdj.zero
  have h3 := h1.add h2
  have e : eps l' • raiB l' * eps l • lowB l + (if l = l' then (1 / 2 : ℂ) • (1 : Module.End ℂ (Pol p q r s)) else 0) =
      (eps l * eps l') • omE l' l := by
    unfold omE
    rw [smul_add, smul_mul_smul_comm, mul_comm (eps l')]
    congr 1
    by_cases h : l = l'
    · subst h; simp [eps_sq]
    · simp [h, Ne.symm h]
  rw [e] at h3
  exact h3

theorem omAct_skew (hIP : FockIP ι) {Z : Mat (p * r + q * s) (p * s + q * r)}
    (hZ : Z ∈ upq (p * r + q * s) (p * s + q * r)) :
    IsAdj ι (omAct p q r s (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm Z))
      (-(omAct p q r s (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm Z))) := by
  set e := lineEquiv p q r s
  have hent : ∀ l l', star (Z (e l) (e l')) * (eps l * eps l') = -Z (e l') (e l) := by
    intro l l'
    have h0 : Zᴴ * Jm _ _ + Jm _ _ * Z = 0 := hZ
    have h1 := congrFun (congrFun h0 (e l')) (e l)
    simp only [Matrix.add_apply, Matrix.mul_apply, Jm_apply, Matrix.conjTranspose_apply, Matrix.zero_apply,
      mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      lineEquiv_isLeft, e] at h1
    have h2 : star (Z (e l) (e l')) * eps l + eps l' * Z (e l') (e l) = 0 := by
      unfold eps; simpa [e] using h1
    have h3 : star (Z (e l) (e l')) * eps l = -(eps l' * Z (e l') (e l)) := eq_neg_of_add_eq_zero_left h2
    calc star (Z (e l) (e l')) * (eps l * eps l') = (star (Z (e l) (e l')) * eps l) * eps l' := by ring
      _ = -((eps l' * eps l') * Z (e l') (e l)) := by rw [h3]; ring
      _ = _ := by rw [eps_sq, one_mul]
  rw [omAct_apply]
  have hs : IsAdj ι (∑ l, ∑ l', (Matrix.reindex e.symm e.symm Z) l l' • omE l l')
      (∑ l, ∑ l', star ((Matrix.reindex e.symm e.symm Z) l l') • ((eps l * eps l') • omE l' l)) :=
    IsAdj.sum _ fun l _ => IsAdj.sum _ fun l' _ => (adj_omE hIP l l').smul _
  have he : (∑ l, ∑ l', star ((Matrix.reindex e.symm e.symm Z) l l') • ((eps l * eps l') • omE l' l)) =
      -(∑ l, ∑ l', (Matrix.reindex e.symm e.symm Z) l l' • omE l l') := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_smul, ← neg_smul]
    congr 1
    simpa using hent l l'
  rw [he] at hs
  exact hs

end Skew

theorem FockCore.isFockIP {p q r s : ℕ} (C : FockCore p q r s) : FockIP C.ι := C.fockIP

section Compact

variable {p q : ℕ}

theorem Jm_definite (h : p = 0 ∨ q = 0) : Jm p q = 1 ∨ Jm p q = -1 := by
  rcases h with rfl | rfl
  · right
    ext a b
    rcases a with a | a
    · exact a.elim0
    rcases b with b | b
    · exact b.elim0
    simp [Jm, Formalism.UG.Jpq, Matrix.one_apply]
  · left
    ext a b
    rcases a with a | a
    swap
    · exact a.elim0
    rcases b with b | b
    swap
    · exact b.elim0
    simp [Jm, Formalism.UG.Jpq, Matrix.one_apply]

theorem unitary_of_mem (h : p = 0 ∨ q = 0) {g : GL (Ix p q) ℂ} (hg : g ∈ Formalism.UG.Upq p q) :
    (g : Mat p q) ∈ Matrix.unitaryGroup (Ix p q) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have h1 := (mem_Upq_iff p q g).1 hg
  rcases Jm_definite h with hJ | hJ
  · rw [hJ] at h1; rw [Matrix.star_eq_conjTranspose]; simpa using h1
  · rw [hJ] at h1; rw [Matrix.star_eq_conjTranspose]
    simpa using h1

def boxM (p q : ℕ) : Set (Mat p q) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) 1

theorem boxM_compact : IsCompact (boxM p q) :=
  isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _

theorem mem_boxM_of_unitary {M : Mat p q} (h : M ∈ Matrix.unitaryGroup (Ix p q) ℂ) : M ∈ boxM p q := by
  intro i _ j _
  simpa using entry_norm_bound_of_unitary h i j

theorem norm_sq_eq_one (h : p = 0 ∨ q = 0) (x : covSub p q) : ‖((x.1.2 : ℂˣ) : ℂ)‖ = 1 := by
  have h1 := x.2.2
  have hu := unitary_of_mem h x.2.1
  have hd : ‖((x.1.1 : GL (Ix p q) ℂ) : Mat p q).det‖ = 1 := by
    have := Matrix.det_of_mem_unitary hu
    exact CStarRing.norm_of_mem_unitary this
  rw [← h1, norm_pow] at hd
  have h0 : 0 ≤ ‖((x.1.2 : ℂˣ) : ℂ)‖ := norm_nonneg _
  nlinarith [hd, h0]

theorem covSub_compact (h : p = 0 ∨ q = 0) : CompactSpace (covSub p q) := by
  have e1 : Topology.IsClosedEmbedding (Units.embedProduct (Mat p q)) := Units.isClosedEmbedding_embedProduct
  have e2 : Topology.IsClosedEmbedding (Units.embedProduct ℂ) := Units.isClosedEmbedding_embedProduct
  have e3 := (e1.prodMap e2).comp (covSub_closed p q).isClosedEmbedding_subtypeVal
  have hK : IsCompact (((boxM p q) ×ˢ (MulOpposite.op '' boxM p q)) ×ˢ
      ((Metric.closedBall (0 : ℂ) 1) ×ˢ (MulOpposite.op '' Metric.closedBall (0 : ℂ) 1))) :=
    (boxM_compact.prod (boxM_compact.image MulOpposite.continuous_op)).prod
      ((isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).image MulOpposite.continuous_op))
  have hpre := e3.isCompact_preimage hK
  refine isCompact_univ_iff.1 (hpre.of_isClosed_subset isClosed_univ ?_ |>.of_isClosed_subset isClosed_univ subset_rfl)
  intro x _
  refine ⟨⟨mem_boxM_of_unitary (unitary_of_mem h x.2.1),
    ⟨_, mem_boxM_of_unitary (unitary_of_mem h (x⁻¹).2.1), rfl⟩⟩, ⟨?_, ⟨_, ?_, rfl⟩⟩⟩
  · simpa using (norm_sq_eq_one h x).le
  · simpa using (norm_sq_eq_one h x⁻¹).le

end Compact

section Triv

variable {p q : ℕ}

def gkTriv (p q : ℕ) : GKMod p q where
  V := ℂ
  act := 0
  lie := by intro X Y; simp
  kfin := fun v => ⟨⊤, inferInstance, trivial, fun _ _ _ _ => trivial⟩
  wts := fun v => by
    refine Submodule.mem_iSup_of_mem (0 : Ix p q → ℚ) ?_
    simp [wtSub]

def dsTriv (T : GrpData p q) [CompactSpace T.G] : DSRep T where
  U := { H := ℂ, π := 1, isom := fun _ _ => rfl, cont := fun _ => continuous_const }
  nontriv := inferInstanceAs (Nontrivial ℂ)
  irred := fun S _ _ => eq_bot_or_eq_top S
  fdeg := (T.haar Set.univ).toReal⁻¹
  fdeg_pos := inv_pos.2 (ENNReal.toReal_pos (NeZero.ne _) (measure_ne_top _ _))
  schur := fun (x y : ℂ) => by
    refine ⟨(integrable_const (‖inner ℂ y x‖ ^ 2) : Integrable (fun _ : T.G => ‖inner ℂ y x‖ ^ 2) T.haar), ?_⟩
    show ∫ _ : T.G, ‖inner ℂ y x‖ ^ 2 ∂T.haar = _
    rw [integral_const]
    simp [Measure.real, mul_pow]
    ring
  HK := gkTriv p q
  ι := LinearMap.id
  ι_inj := Function.injective_id
  ι_range := fun x => ⟨fun _ => inferInstanceAs (FiniteDimensional ℂ (Submodule.span ℂ _ : Submodule ℂ ℂ)),
    fun _ => ⟨x, rfl⟩⟩
  der := fun X _ v => by
    exact (hasDerivAt_const (0 : ℝ) (show ℂ from v) : HasDerivAt (fun _ : ℝ => (show ℂ from v)) (0 : ℂ) 0)

theorem nonempty_DSRep_definite (h : p = 0 ∨ q = 0) : Nonempty (DSRep (stdGrp p q)) :=
  haveI : CompactSpace (stdGrp p q).G := covSub_compact h
  ⟨dsTriv (stdGrp p q)⟩

end Triv

def gkZero (p q : ℕ) : GKMod p q where
  V := PUnit
  act := 0
  lie := by intro X Y; simp
  kfin := fun v => ⟨⊤, inferInstance, trivial, fun _ _ _ _ => trivial⟩
  wts := fun v => by rw [Subsingleton.elim v 0]; exact zero_mem _

theorem nonempty_TH_GKMod (p q : ℕ) : Nonempty (GKMod p q) := ⟨gkTriv p q⟩

theorem nonempty_TH_UGKMod (p q : ℕ) : Nonempty (UGKMod p q) :=
  ⟨{ M := gkZero p q
     ip := 0
     herm := fun _ _ => by simp
     pos := fun x hx => absurd (Subsingleton.elim (α := PUnit) x 0) hx
     adj := fun _ _ _ => by simp }⟩

theorem nonempty_TH_URep {p q : ℕ} (T : GrpData p q) : Nonempty (URep T) :=
  ⟨{ H := ℂ, π := 1, isom := fun _ _ => rfl, cont := fun _ => continuous_const }⟩

def FockExists : Prop := ∀ p q r s : ℕ, Nonempty (FockCore p q r s)

def DSExists : Prop := ∀ p q : ℕ, 1 ≤ p → 1 ≤ q → Nonempty (DSRep (stdGrp p q))

theorem nonempty_TH_FockData (hF : FockExists) (p q r s : ℕ) :
    Nonempty (FockData (stdGrp (p * r + q * s) (p * s + q * r)) (stdGrp p q) (stdGrp r s)) :=
  ⟨(hF p q r s).some.toFockData⟩

theorem nonempty_TH_DSRep (hD : DSExists) (p q : ℕ) : Nonempty (DSRep (stdGrp p q)) := by
  by_cases h : p = 0 ∨ q = 0
  · exact nonempty_DSRep_definite h
  · exact hD p q (by omega) (by omega)

theorem nonempty_TH_ProvA (hF : FockExists) (hD : DSExists) : Nonempty ProvA :=
  ⟨{ grp := stdGrp
     fock := fun p q r s => (nonempty_TH_FockData hF p q r s).some
     ds := fun p q _ => (nonempty_TH_DSRep hD p q).some }⟩

theorem of_ProvA (X : ProvA) : (∀ p q r s, Nonempty (FockData (X.grp (p * r + q * s) (p * s + q * r)) (X.grp p q) (X.grp r s))) ∧
    ∀ p q, Nonempty (DSRep (X.grp p q)) :=
  ⟨fun p q r s => ⟨X.fock p q r s⟩, fun p q => ⟨X.ds p q 0⟩⟩

end Formalism.MainNotions.DIV.Inh

end
