import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPinsRec
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.CoefficientSpaceWeights
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLetterEquivConjugate
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeneralLinearGroupCharEqOneOfDetEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteNotIsUnitOneAddSmul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqZeroOfMul

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LFCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField MvPolynomial Formalism.BasicNotions Formalism.L2.Pj Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.CoefficientSpaceWeights
open scoped Matrix

theorem exists_rep {G K V W : Type} [Monoid G] [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (io : V →ₗ[K] W) (hio : Function.Injective io) (R : G →* Module.End K W)
    (hst : ∀ g v, R g (io v) ∈ LinearMap.range io) :
    ∃ φ : G →* Module.End K V, ∀ g v, io (φ g v) = R g (io v) := by
  let f : G → Module.End K V := fun g => (LinearEquiv.ofInjective io hio).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range io) (R g ∘ₗ io) (hst g)
  have hf : ∀ g v, io (f g v) = R g (io v) := fun g v => LinearEquiv.ofInjective_symm_apply (h := hio) io _
  refine ⟨⟨⟨f, ?_⟩, fun g h => ?_⟩, hf⟩
  · ext v
    exact hio (by rw [hf, map_one]; rfl)
  · ext v
    exact hio (by rw [hf, map_mul, Module.End.mul_apply, Module.End.mul_apply, hf, hf])

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def uGL (γ : Matrix (Fin n) (Fin n) E) (h : γᴴ * γ = 1) : GL (Fin n) E := ⟨γ, γᴴ, mul_eq_one_comm.1 h, h⟩

theorem diag_unitary {t : Fin n → E} (ht : ∀ i, star (t i) * t i = 1) :
    (Matrix.diagonal t)ᴴ * Matrix.diagonal t = 1 := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact ht i

theorem det_norm_one {γ : Matrix (Fin n) (Fin n) E} (h : γᴴ * γ = 1) : star γ.det * γ.det = 1 := by
  rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, h, Matrix.det_one]

theorem exists_diag_det {γ : Matrix (Fin n) (Fin n) E} (h : γᴴ * γ = 1) :
    ∃ t : Fin n → E, (∀ i, star (t i) * t i = 1) ∧ (Matrix.diagonal t).det = γ.det := by
  cases n with
  | zero => exact ⟨fun _ => 1, fun i => i.elim0, by simp⟩
  | succ m =>
    refine ⟨Fin.cons γ.det fun _ => 1, fun i => ?_, by simp [Fin.prod_univ_succ]⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using det_norm_one h
    · simp

section Rho

variable {K ι : Type} [Field K] [NumberField K] [Fintype ι] (emb : ι → E →+* K) (lam : ι → DomWeight n)

theorem rhoVr_unitary (γ : Matrix (Fin n) (Fin n) E) (h : γᴴ * γ = 1) (v : VV K lam) :
    ((rhoVr emb lam (uGL γ h) v : VV K lam) : Pol K ι n) =
      (∏ τ, emb τ γ.det ^ (-(lam τ).detShift)) • Formalism.GradedWeylDivisibility.blockAct K (fun τ => γᴴ.map (emb τ)) (v : Pol K ι n) := by
  change detTwK lam (invTrK (embGL emb (uGL γ h))) • trAct (invTrK (embGL emb (uGL γ h))) (v : Pol K ι n) = _
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [detPow, Units.val_zpow_eq_zpow_val, zpow_neg, ← inv_zpow]
  congr 1
  change (γᴴ.map (emb τ))ᵀ.det = _
  rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_conjTranspose, ← map_inv₀,
    eq_inv_of_mul_eq_one_left (det_norm_one h)]

theorem natW_cast (μ : DomWeight n) (i : Fin n) : (μ.natW i : ℤ) = μ.w i - μ.detShift := by
  have : μ.detShift ≤ μ.w i := by
    rw [DomWeight.detShift, dif_pos i.pos]
    exact μ.anti (by rw [Fin.le_def]; have := i.isLt; simp only; omega)
  rw [DomWeight.natW, Int.toNat_of_nonneg (by omega)]

theorem rhoVr_diag {t : Fin n → E} (ht : ∀ i, star (t i) * t i = 1) (v : VV K lam)
    (hv : (v : Pol K ι n) = ten fun τ => extremal K n (lam τ)) :
    rhoVr emb lam (uGL _ (diag_unitary ht)) v = (∏ τ, ∏ i, emb τ (t i) ^ (-(lam τ).w i)) • v := by
  apply Subtype.ext
  rw [rhoVr_unitary, Submodule.coe_smul, hv, ten, map_prod]
  have e : ∀ τ, Formalism.GradedWeylDivisibility.blockAct K (fun τ => (Matrix.diagonal t)ᴴ.map (emb τ))
      (Formalism.GradedWeylDivisibility.blockEmb K τ (extremal K n (lam τ))) =
      (∏ i, (emb τ (t i))⁻¹ ^ (lam τ).natW i) • Formalism.GradedWeylDivisibility.blockEmb K τ (extremal K n (lam τ)) := fun τ => by
    rw [(Formalism.GradedWeylDivisibility.blockActTensor K K ι n n _).1, Matrix.diagonal_conjTranspose, Matrix.diagonal_map (map_zero _),
      extremal, Formalism.GradedWeylDivisibility.rowActDiagWeight K n n _ _ _
        (Formalism.GradedWeylDivisibility.hwRowWeight K n n le_rfl _ (natW_anti (lam τ))), map_smul]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.star_apply, eq_inv_of_mul_eq_one_left (ht i), map_inv₀]
    simp [Formalism.GradedWeylDivisibility.rowNu]
  simp only [e]
  rw [Finset.prod_smul, smul_smul, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Matrix.det_diagonal, map_prod, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h0 : emb τ (t i) ≠ 0 := (_root_.map_ne_zero _).2 (right_ne_zero_of_mul_eq_one (ht i))
  rw [← zpow_natCast, natW_cast, inv_zpow', ← zpow_add₀ h0]
  congr 1
  ring

theorem rhoVr_mem (Γ : ℚ → Matrix (Fin n) (Fin n) E) (hΓ : ∀ s, (Γ s)ᴴ * Γ s = 1)
    (hr : ∀ (σ : E →+* K) i j, (fun s => σ (Γ s i j)) ∈ ratFn K) (v : VV K lam) (ℓ : VV K lam →ₗ[K] K) :
    (fun s => ℓ (rhoVr emb lam (uGL _ (hΓ s)) v)) ∈ ratFn K := by
  obtain ⟨ℓ', hℓ⟩ := LinearMap.exists_extend ℓ
  have hd : ∀ (τ : ι) (e : ℤ), (fun s => emb τ (Γ s).det ^ e) ∈ ratFn K := fun τ e => by
    refine zpow_mem (f := fun s => emb τ (Γ s).det) ?_
      (fun s => (_root_.map_ne_zero _).2 (right_ne_zero_of_mul_eq_one (det_norm_one (hΓ s)))) e
    simp only [RingHom.map_det]
    exact det_mem fun i j => hr _ i j
  have h1 := aeval_mem (σ := ι × Fin n × Fin n) (fun s x b => ((Γ s)ᴴ.map (emb x.1)) x.2.1 b)
    (fun x b => (x.1, b, x.2.2)) (fun x b => hr ((emb x.1).comp (starRingEnd E)) b x.2.1) (v : Pol K ι n) ℓ'
  have := mul_mem (Subalgebra.prod_mem (ratFn K) (t := Finset.univ) fun τ _ => hd τ (-(lam τ).detShift)) h1
  convert this using 1
  funext s
  rw [← hℓ, LinearMap.comp_apply, Submodule.subtype_apply, rhoVr_unitary, map_smul, Pi.mul_apply, Finset.prod_apply]
  rfl

end Rho

section Letters

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H} (Dw : Datum H) (c : Coeff l)

theorem embF_conjugate (τ : E →+* ℂ) (x : E) : embF c (ComplexEmbedding.conjugate τ) x = embF c τ (star x) :=
  Subtype.ext (IsCMField.complexEmbedding_complexConj E τ x).symm

variable (n) in

def letRep : GL (Fin n) E →* Module.End c.F (MvPolynomial (LtN Dw n) c.F) :=
  ((renameEquiv c.F (Harm.thetaLetterEquiv Dw n)).toLinearEquiv.symm.conjRingEquiv : _ →* _).comp
    ((Harm.colRep c.F (Psi H) Dw.p Dw.q (Fin n)).comp (embGL (embPsi c)))

theorem rename_letRep (g : GL (Fin n) E) (P : MvPolynomial (LtN Dw n) c.F) :
    rename (Harm.thetaLetterEquiv Dw n) (letRep n Dw c g P) =
      Harm.colAct c.F (Psi H) Dw.p Dw.q (Fin n) (embGL (embPsi c) g) (rename (Harm.thetaLetterEquiv Dw n) P) :=
  (renameEquiv c.F (Harm.thetaLetterEquiv Dw n)).apply_symm_apply _

theorem letRep_unitary (γ : Matrix (Fin n) (Fin n) E) (h : γᴴ * γ = 1) (P : MvPolynomial (LtN Dw n) c.F) :
    letRep n Dw c (uGL γ h) P = gaStar c (γ.map (IsCMField.complexConj E)) P := by
  apply rename_injective _ (Harm.thetaLetterEquiv Dw n).injective
  rw [rename_letRep, Harm.colAct_apply]
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  refine DFunLike.congr_fun ?_ P
  refine MvPolynomial.algHom_ext fun ⟨τ, i, b⟩ => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, rename_X, Formalism.L2.Pj.gaStar, aeval_X]
  rcases Harm.half_cases (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate E)
    (Harm.not_mem_hostType_iff H) τ with hτ | ⟨τ, hτ, rfl⟩
  · rw [Harm.thetaLetterEquiv_of_mem Dw hτ, Harm.colSubst_X_xVar, Harm.rename_letB_of_mem Dw c hτ]
    rfl
  · rw [Harm.thetaLetterEquiv_conjugate Dw hτ, Harm.colSubst_X_yVar, Harm.rename_letB_conjugate Dw c hτ]
    congr 1
    funext k
    exact congrArg (embF c τ) (star_star (γ k b)).symm

theorem letRep_mem (a : (E →+* ℂ) × ℕ → ℕ) (g : GL (Fin n) E) {P : MvPolynomial (LtN Dw n) c.F}
    (hP : P ∈ Submodule.span c.F (HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))) :
    letRep n Dw c g P ∈
      Submodule.span c.F (HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) := by
  rw [← Submodule.mem_comap]
  refine Submodule.span_le.2 (fun Q hQ => ?_) hP
  rcases Harm.HHa_eq_zero_or_rowHighest (n := n) (K := c.F) (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate E)
    (Harm.not_mem_hostType_iff H) (fun _ => Harm.mult_of_mem Dw) (fun _ => Harm.mult_conjEmb_of_mem Dw)
    (fun τ i => a (τ, i)) with h0 | ⟨k, k', -, hk⟩
  · rw [h0 Q hQ]
    exact zero_mem _
  · refine Submodule.subset_span ((hk _).2 ?_)
    exact (rename_letRep Dw c g Q).symm ▸ Harm.colAct_mem_rowHighest _ ((hk Q).1 hQ)

theorem gaStar_mem (Γ : ℚ → Matrix (Fin n) (Fin n) E)
    (hr : ∀ (σ : E →+* c.F) i j, (fun s => σ (Γ s i j)) ∈ ratFn c.F) (P : MvPolynomial (LtN Dw n) c.F)
    (ℓ : MvPolynomial (LtN Dw n) c.F →ₗ[c.F] c.F) :
    (fun s => ℓ (gaStar c ((Γ s).map (IsCMField.complexConj E)) P)) ∈ ratFn c.F := by
  have := aeval_mem (σ := LtN Dw n) (σ' := LtN Dw n)
    (fun s x j => embF c x.1 (IsCMField.complexConj E (Γ s j x.2.2))) (fun x j => ⟨x.1, x.2.1, j⟩)
    (fun x j => hr ((embF c x.1).comp (starRingEnd E)) j x.2.2) P ℓ
  simpa only [Formalism.L2.Pj.gaStar, letB, Matrix.map_apply] using this

theorem gaStar_minorP (u : Fin n → E) (σ : E →+* ℂ) (i : ℕ) (hi : i < Dw.mult σ) (col : Fin (i + 1) → Fin n) :
    gaStar c (Matrix.diagonal u) (minorPolynomial c σ i hi col) = (∏ b, embF c σ (u (col b))) • minorPolynomial c σ i hi col := by
  rw [minorPolynomial, AlgHom.map_det, smul_eq_C_mul, map_prod, ← Matrix.det_mul_row]
  congr 1
  ext s b : 2
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Formalism.L2.Pj.gaStar, aeval_X, letB]
  rw [Finset.sum_eq_single (col b) (fun j _ hj => by rw [Matrix.diagonal_apply_ne _ hj, map_zero, map_zero, zero_mul])
    (by simp), Matrix.diagonal_apply_eq]

theorem mult_le (σ : E →+* ℂ) : Dw.mult σ ≤ Dw.p + Dw.q := by
  unfold Datum.mult
  split_ifs <;> omega

open Classical in

theorem gaStar_pG {a : (E →+* ℂ) × ℕ → ℕ} (ha : IsPartFam Dw a) (hn : Dw.p + Dw.q ≤ n) (u : Fin n → E) :
    gaStar c (Matrix.diagonal u) (pG (Dw := Dw) c a n) =
      (∏ σ : E →+* ℂ, ∏ b : Fin n, embF c σ (u (if InPsi H σ then b else b.rev)) ^ part Dw a σ b) •
        pG (Dw := Dw) c a n := by
  rw [pG, map_prod, ← Finset.prod_smul]
  refine Finset.prod_congr rfl fun σ _ => ?_
  have hm : Dw.mult σ ≤ n := (mult_le Dw σ).trans hn
  let x : ℕ → c.F := fun b => if h : b < n then embF c σ (u (if InPsi H σ then ⟨b, h⟩ else Fin.rev ⟨b, h⟩)) else 1
  have e : ∏ b : Fin n, embF c σ (u (if InPsi H σ then b else b.rev)) ^ part Dw a σ b =
      ∏ i : Fin (Dw.mult σ), (∏ b ∈ Finset.range (i + 1), x b) ^ aStep Dw a σ i := by
    have t := tele x (part Dw a σ) (part_anti ha σ) (Dw.mult σ)
    rw [show part Dw a σ (Dw.mult σ) = 0 from if_neg (lt_irrefl _), pow_zero, mul_one,
      Finset.prod_subset (Finset.range_mono hm) (f := fun b => x b ^ part Dw a σ b) (fun b _ hb => by
        rw [show part Dw a σ b = 0 from if_neg (by simpa using hb), pow_zero]),
      Finset.prod_range, Finset.prod_range] at t
    refine Eq.trans ?_ (t.symm.trans ?_)
    · refine Finset.prod_congr rfl fun b _ => ?_
      simp only [x, dif_pos b.isLt]
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [aStep, part, part, if_pos i.isLt]
  rw [e, map_prod, ← Finset.prod_smul]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi : i.val + 1 ≤ n := lt_of_lt_of_le i.isLt hm
  rw [dif_pos hi, map_pow, ← smul_pow]
  congr 1
  by_cases hσ : InPsi H σ
  · rw [if_pos hσ, gaStar_minorP, Finset.prod_range]
    congr 1
    refine Finset.prod_congr rfl fun b _ => ?_
    simp only [x, dif_pos (lt_of_lt_of_le b.isLt hi), if_pos hσ]
    rfl
  · rw [if_neg hσ, gaStar_minorP, Finset.prod_range, ← Equiv.prod_comp Fin.revPerm]
    congr 1
    refine Finset.prod_congr rfl fun b _ => ?_
    simp only [x, dif_pos (lt_of_lt_of_le b.isLt hi), if_neg hσ]
    congr 2
    apply Fin.ext
    have := b.isLt
    simp
    omega

theorem prod_emb {M : Type} [CommMonoid M] (F : (E →+* ℂ) → M) :
    ∏ σ, F σ = ∏ τ : Psi H, F τ.1 * F (ComplexEmbedding.conjugate τ.1) := by
  classical
  rw [← Fintype.prod_subtype_mul_prod_subtype (InPsi H), Finset.prod_mul_distrib]
  congr 1
  · convert rfl
  · refine (Fintype.prod_equiv (Equiv.subtypeEquiv (ComplexEmbedding.involutive_conjugate E).toPerm fun τ => ?_)
      _ _ fun τ => rfl).symm
    have := Harm.not_mem_hostType_iff H (ComplexEmbedding.conjugate τ)
    rw [show conjEmb (ComplexEmbedding.conjugate τ) = τ from ComplexEmbedding.involutive_conjugate E τ] at this
    exact this.symm

theorem gaStar_pG_vac {a : (E →+* ℂ) × ℕ → ℕ} (ha : IsPartFam Dw a) (hn : Dw.p + Dw.q ≤ n) (d : Psi H → ℤ)
    {t : Fin n → E} (ht : ∀ i, star (t i) * t i = 1) :
    vacChar c n d (Matrix.diagonal t) • gaStar c ((Matrix.diagonal t).map (IsCMField.complexConj E))
      (pG (Dw := Dw) c a n) =
      (∏ τ, ∏ i, embPsi c τ (t i) ^ (-(lamP Dw n ha d τ).w i)) • pG (Dw := Dw) c a n := by
  rw [Matrix.diagonal_map (map_zero _), gaStar_pG Dw c ha hn, smul_smul, prod_emb (H := H), vacChar,
    ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h1 : ¬ InPsi H (ComplexEmbedding.conjugate τ.1) := by
    have := Harm.not_mem_hostType_iff H τ.1
    exact fun h => this.2 h τ.2
  simp only [if_pos τ.2, if_neg h1]
  rw [Matrix.det_diagonal, map_prod, ← Finset.prod_zpow, ← Equiv.prod_comp Fin.revPerm
    (fun b => embF c (ComplexEmbedding.conjugate τ.1) (IsCMField.complexConj E (t b.rev)) ^
      part Dw a (ComplexEmbedding.conjugate τ.1) b), ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h0 : embF c τ.1 (t i) ≠ 0 := (_root_.map_ne_zero _).2 (right_ne_zero_of_mul_eq_one (ht i))
  have e1 : embF c τ.1 (IsCMField.complexConj E (t i)) = (embF c τ.1 (t i))⁻¹ := by
    rw [← map_inv₀, ← eq_inv_of_mul_eq_one_left (ht i)]; rfl
  have e2 : embF c (ComplexEmbedding.conjugate τ.1) (IsCMField.complexConj E (t i)) = embF c τ.1 (t i) := by
    rw [embF_conjugate]; exact congrArg _ (star_star _)
  simp only [Fin.revPerm_apply, Fin.rev_rev, e1, e2, embPsi, lamP]
  rw [← zpow_natCast, ← zpow_natCast, inv_zpow', ← zpow_add₀ h0, ← zpow_add₀ h0]
  congr 1
  ring

end Letters

theorem pow_eq_one_of_det {K V : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (ρ φ : GL (Fin n) E →* Module.End K V) (g : GL (Fin n) E) (hg : (g : Matrix (Fin n) (Fin n) E).det = 1) (s : K)
    (h : ∀ v, ρ g v = s • φ g v) : s ^ Module.finrank K V = 1 := by
  have e1 : LinearMap.det (ρ g) = 1 := congrArg Units.val (char_eq_one (LinearMap.det.comp ρ).toHomUnits g hg)
  have e2 : LinearMap.det (φ g) = 1 := congrArg Units.val (char_eq_one (LinearMap.det.comp φ).toHomUnits g hg)
  rwa [show ρ g = s • φ g from LinearMap.ext h, LinearMap.det_smul, e2, mul_one] at e1

theorem scalar_eq_of_diag {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (ρ φ : GL (Fin n) E →* Module.End K V) (w : V) (hw0 : w ≠ 0) (cga vac : Matrix (Fin n) (Fin n) E → K)
    (hsm' : ∀ γ (h : γᴴ * γ = 1) v, ρ (uGL γ h) v = cga γ • φ (uGL γ h) v)
    (hdiag : ∀ t : Fin n → E, (∀ i, star (t i) * t i = 1) → cga (Matrix.diagonal t) = vac (Matrix.diagonal t))
    (hdet : ∀ γ δ, γ.det = δ.det → vac γ = vac δ) (hvm : ∀ γ δ, vac (γ * δ) = vac γ * vac δ) (hv1 : vac 1 ≠ 0)
    (hrat : ∀ (Γ : ℚ → Matrix (Fin n) (Fin n) E) (hΓ : ∀ s, (Γ s)ᴴ * Γ s = 1),
      (∀ (σ : E →+* K) i j, (fun s => σ (Γ s i j)) ∈ ratFn K) → (fun s => vac (Γ s)) ∈ ratFn K ∧
        ∀ ℓ : V →ₗ[K] K, (fun s => ℓ (ρ (uGL _ (hΓ s)) w)) ∈ ratFn K ∧ (fun s => ℓ (φ (uGL _ (hΓ s)) w)) ∈ ratFn K)
    (γ : Matrix (Fin n) (Fin n) E) (hγ : γᴴ * γ = 1) : cga γ = vac γ := by
  have hφ0 : ∀ g, φ g w ≠ 0 := fun g h0 => hw0 (by
    rw [← Module.End.one_apply (R := K) w, ← map_one φ, ← inv_mul_cancel g, map_mul, Module.End.mul_apply, h0,
      map_zero])
  have hsm : ∀ γ (h : γᴴ * γ = 1), ρ (uGL γ h) = cga γ • φ (uGL γ h) := fun γ h => LinearMap.ext (hsm' γ h)
  have hun : ∀ {γ δ : Matrix (Fin n) (Fin n) E}, γᴴ * γ = 1 → δᴴ * δ = 1 → (γ * δ)ᴴ * (γ * δ) = 1 :=
    fun {γ δ} h h' => by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc γᴴ, h, Matrix.one_mul, h']
  have hmul : ∀ γ δ (h : γᴴ * γ = 1) (h' : δᴴ * δ = 1), cga (γ * δ) = cga γ * cga δ := fun γ δ h h' => by
    have e : uGL _ (hun h h') = uGL γ h * uGL δ h' := Units.ext rfl
    have e1 := hsm _ (hun h h')
    rw [e, map_mul ρ, hsm, hsm, smul_mul_smul_comm, ← map_mul] at e1
    exact (smul_left_injective K (hφ0 _) (LinearMap.congr_fun e1 w)).symm
  haveI : Nontrivial V := nontrivial_of_ne _ _ hw0
  have hN : Module.finrank K V ≠ 0 := Module.finrank_pos.ne'
  have hpow : ∀ γ (h : γᴴ * γ = 1), cga γ ^ Module.finrank K V = vac γ ^ Module.finrank K V := fun γ h => by
    obtain ⟨t, ht, hd⟩ := exists_diag_det h
    have hD := diag_unitary ht
    have hD' : (Matrix.diagonal t)ᴴᴴ * (Matrix.diagonal t)ᴴ = 1 := by
      rw [Matrix.conjTranspose_conjTranspose, mul_eq_one_comm.1 hD]
    have hd1 : (γ * (Matrix.diagonal t)ᴴ).det = 1 := by
      rw [Matrix.det_mul, Matrix.det_conjTranspose, hd, mul_comm, det_norm_one h]
    have e1 := pow_eq_one_of_det ρ φ (uGL _ (hun h hD')) hd1 _ (hsm' _ (hun h hD'))
    have e3 : γ = γ * (Matrix.diagonal t)ᴴ * Matrix.diagonal t := by rw [Matrix.mul_assoc, hD, Matrix.mul_one]
    rw [← hdet _ _ hd, ← hdiag t ht, congrArg cga e3, hmul _ _ (hun h hD') hD, mul_pow, e1, one_mul]
  have hone : cga 1 = vac 1 := by simpa using hdiag 1 (by simp)
  have hcay : ∀ γ, γᴴ * γ = 1 → IsUnit (1 + γ) → cga γ = vac γ := fun γ h h1 => by
    obtain ⟨Γ, hΓ, hΓ0, rfl, hr⟩ := exists_curve K γ h h1
    obtain ⟨ℓ₀, h₀⟩ := not_forall.1 (mt (Module.forall_dual_apply_eq_zero_iff K _).1 (hφ0 (uGL _ (hΓ 0))))
    obtain ⟨ℓ₁, h₁⟩ := not_forall.1 (mt (Module.forall_dual_apply_eq_zero_iff K _).1 (hφ0 (uGL _ (hΓ 1))))
    obtain ⟨hv, hℓ⟩ := hrat Γ hΓ hr
    have he : ∀ (ℓ : V →ₗ[K] K) (s : ℚ), ℓ (ρ (uGL _ (hΓ s)) w) = cga (Γ s) * ℓ (φ (uGL _ (hΓ s)) w) :=
      fun ℓ s => by rw [hsm', map_smul, smul_eq_mul]
    exact scalar_eq (c := fun s => cga (Γ s)) hN hv (hℓ ℓ₀).1 (hℓ ℓ₀).2 (hℓ ℓ₁).1 (hℓ ℓ₁).2
      (he ℓ₀) (he ℓ₁) (fun s => hpow _ (hΓ s)) (by rw [hΓ0, hone]) (by rwa [hΓ0]) h₀ h₁
  obtain ⟨z, hz, hz1⟩ := exists_scalar γ
  have hz' : ∀ _ : Fin n, star (star z) * star z = 1 := fun _ => by rw [star_star, mul_comm, hz]
  have hzγ : (z • γ)ᴴ * (z • γ) = 1 := by
    rw [Matrix.conjTranspose_smul, smul_mul_smul_comm, hz, hγ, one_smul]
  have e : γ = Matrix.diagonal (fun _ => star z) * (z • γ) := by
    rw [← Matrix.smul_eq_diagonal_mul, smul_smul, hz, one_smul]
  rw [e, hmul _ _ (diag_unitary hz') hzγ, hvm, hdiag _ hz', hcay _ hzγ hz1]

theorem exponents_eq_zero {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (m : Psi H → ℤ)
    (h : ∀ ζ : E, star ζ * ζ = 1 → ∏ τ : Psi H, τ.1 ζ ^ m τ = 1) : m = 0 := by
  classical
  have key : ∀ θ : E, star θ = -θ → ∑ τ : Psi H, (m τ : ℂ) * τ.1 θ = 0 := fun θ hθ => by
    have hd : ∀ τ : Psi H, HasDerivAt (fun s : ℂ => ((1 + s * τ.1 θ) / (1 - s * τ.1 θ)) ^ m τ)
        ((m τ : ℂ) * (2 * τ.1 θ)) 0 := fun τ => by
      have h1 : HasDerivAt (fun s : ℂ => (1 + s * τ.1 θ) / (1 - s * τ.1 θ)) (2 * τ.1 θ) 0 := by
        refine HasDerivAt.congr_deriv ((((hasDerivAt_id (0 : ℂ)).mul_const (τ.1 θ)).const_add 1).fun_div
          (((hasDerivAt_id (0 : ℂ)).mul_const (τ.1 θ)).const_sub 1) (by simp)) ?_
        simp; ring
      have h2 := (hasDerivAt_zpow (m τ) (1 : ℂ) (Or.inl one_ne_zero)).comp_of_eq 0 h1 (by simp)
      simpa [Function.comp_def] using h2
    have hp := HasDerivAt.fun_finsetProd (u := Finset.univ) fun τ _ => hd τ
    simp only [zero_mul, add_zero, sub_zero, div_one, one_zpow, Finset.prod_const_one, one_smul] at hp
    have hq : ∀ s : ℚ, ∏ τ : Psi H, ((1 + (s : ℂ) * τ.1 θ) / (1 - (s : ℂ) * τ.1 θ)) ^ m τ = 1 := fun s => by
      have hc : ∀ s : ℚ, star (1 + (s : E) * θ) = 1 - s * θ := fun s => by
        rw [star_add, star_one, star_mul', star_ratCast, hθ]; ring
      have hne : 1 + (s : E) * θ ≠ 0 := fun hk => by
        have := hc s
        rw [hk, star_zero] at this
        exact two_ne_zero (α := E) (by linear_combination hk - this)
      have hne' : 1 - (s : E) * θ ≠ 0 := by rw [← hc]; exact star_ne_zero.2 hne
      have h' := hc (-s)
      simp only [Rat.cast_neg, neg_mul, ← sub_eq_add_neg, sub_neg_eq_add] at h'
      have := h ((1 + s * θ) / (1 - s * θ)) (by
        rw [star_div₀, hc, h', div_mul_div_comm, mul_comm, div_self (mul_ne_zero hne hne')])
      simpa using this
    have hs : Filter.Tendsto (fun k : ℕ => (1 / ((k : ℂ) + 1))) Filter.atTop (nhdsWithin 0 {0}ᶜ) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Filter.Eventually.of_forall fun k =>
        one_div_ne_zero (Nat.cast_add_one_ne_zero k)⟩
    have ht := (hasDerivAt_iff_tendsto_slope_zero.1 hp).comp hs
    have h0 : ∑ τ : Psi H, (m τ : ℂ) * (2 * τ.1 θ) = 0 := by
      refine tendsto_nhds_unique ht (tendsto_const_nhds.congr fun k => ?_)
      have := hq (1 / (k + 1))
      push_cast at this
      simp only [Function.comp_apply, zero_add, this]
      simp
    have : 2 * ∑ τ : Psi H, (m τ : ℂ) * τ.1 θ = 0 := by
      rw [← h0, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    simpa using this
  have hli : LinearIndependent ℂ (fun σ : E →+* ℂ => (σ : E → ℂ)) :=
    (linearIndependent_monoidHom E ℂ).comp (fun σ : E →+* ℂ => (σ : E →* ℂ)) RingHom.coe_monoidHom_injective
  let μ : (E →+* ℂ) → ℂ := fun σ => if h : InPsi H σ then (m ⟨σ, h⟩ : ℂ) else
    -(m ⟨ComplexEmbedding.conjugate σ, (Harm.not_mem_hostType_iff H σ).1 h⟩ : ℂ)
  have hμ := Fintype.linearIndependent_iff.1 hli μ (by
    funext z
    have := prod_emb (H := H) (M := Multiplicative ℂ) fun σ => Multiplicative.ofAdd (μ σ * σ z)
    replace this : ∑ σ, μ σ * σ z = ∑ τ : Psi H, (μ τ.1 * τ.1 z +
      μ (ComplexEmbedding.conjugate τ.1) * ComplexEmbedding.conjugate τ.1 z) := this
    rw [Finset.sum_apply, Pi.zero_apply, ← key (z - star z) (by simp)]
    refine this.trans (Finset.sum_congr rfl fun τ _ => ?_)
    have h1 : ¬ InPsi H (ComplexEmbedding.conjugate τ.1) := fun h => (Harm.not_mem_hostType_iff H τ.1).2 h τ.2
    have h2 : τ.1 (star z) = ComplexEmbedding.conjugate τ.1 z := IsCMField.complexEmbedding_complexConj E τ.1 z
    simp only [μ, dif_pos τ.2, dif_neg h1, ComplexEmbedding.involutive_conjugate E τ.1, map_sub, h2]
    ring)
  funext τ
  have := hμ τ.1
  simp only [μ, dif_pos τ.2] at this
  exact_mod_cast this

section Scalar

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H} (c : Coeff l) (d : Psi H → ℤ)

theorem vacChar_congr {γ δ : Matrix (Fin n) (Fin n) E} (h : γ.det = δ.det) : vacChar c n d γ = vacChar c n d δ := by
  rw [vacChar, vacChar, h]

theorem vacChar_mul (γ δ : Matrix (Fin n) (Fin n) E) :
    vacChar c n d (γ * δ) = vacChar c n d γ * vacChar c n d δ := by
  simp only [vacChar, Matrix.det_mul, map_mul, mul_zpow, Finset.prod_mul_distrib]

theorem vacChar_mem (Γ : ℚ → Matrix (Fin n) (Fin n) E) (hΓ : ∀ s, (Γ s)ᴴ * Γ s = 1)
    (hr : ∀ (σ : E →+* c.F) i j, (fun s => σ (Γ s i j)) ∈ ratFn c.F) :
    (fun s => vacChar c n d (Γ s)) ∈ ratFn c.F := by
  have := Subalgebra.prod_mem (ratFn c.F) (t := Finset.univ) fun (τ : Psi H) _ =>
    zpow_mem (f := fun s => embPsi c τ (Γ s).det) (by
      simp only [RingHom.map_det]
      exact det_mem fun i j => hr (embPsi c τ) i j)
    (fun s => (_root_.map_ne_zero _).2 (right_ne_zero_of_mul_eq_one (det_norm_one (hΓ s)))) (-(d τ))
  convert this using 1
  funext s
  rw [Finset.prod_apply, vacChar]

end Scalar

section Comparison₂

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H} {Dw : Datum H} {c : Coeff l}
  {a : (E →+* ℂ) × ℕ → ℕ} {Ix : Type} [Fintype Ix]

theorem rhoM_coe (emb : Ix → E →+* c.F) (lam : Ix → DomWeight n) (g : GL (Fin n) E) :
    rhoM c emb lam (g : Matrix (Fin n) (Fin n) E) = rhoVr emb lam g := by
  rw [rhoM, dif_pos ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)]
  exact congrArg _ (Units.ext rfl)

theorem ne_zero_of_hwOK {lam : Ix → DomWeight n} {hw : VVc c lam} (h : hwOK c lam hw) : hw ≠ 0 := fun h0 => by
  have : ten (fun τ => extremal c.F n (lam τ)) = 0 := h.symm.trans (congrArg Subtype.val h0)
  obtain ⟨τ, -, hτ⟩ := Finset.prod_eq_zero_iff.1 this
  exact Formalism.GradedWeylDivisibility.hwNe c.F n n le_rfl _
    (rename_injective _ (Prod.mk_right_injective τ) (hτ.trans (map_zero _).symm))

variable {lam : Ix → DomWeight n} {io : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F} {hw : VVc c lam}
  {cga : Matrix (Fin n) (Fin n) E → c.F} {nab0 : Submodule (𝓞 c.F) (VVc c lam)}

theorem isPartFam_of_tie {emb : Ix → E →+* c.F} (hok : hwOK c lam hw)
    (h : IoLF (Dw := Dw) c a io (rhoM c emb lam) cga nab0 hw (pG (Dw := Dw) c a n)) : IsPartFam Dw a := by
  obtain ⟨-, hinj, hrange, -⟩ := h
  obtain ⟨Q, hQ, hQ0⟩ : ∃ Q ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)),
      Q ≠ 0 := by
    by_contra hne
    push Not at hne
    have := LinearMap.mem_range_self io hw
    rw [hrange, Submodule.span_eq_bot.2 hne, Submodule.mem_bot] at this
    exact ne_zero_of_hwOK hok (hinj (this.trans (map_zero io).symm))
  obtain ⟨-, h₂, h₃⟩ := (Harm.mem_HHa_iff_rename (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate E)
    (Harm.not_mem_hostType_iff H) (fun _ => Harm.mult_of_mem Dw) (fun _ => Harm.mult_conjEmb_of_mem Dw) _ Q).1 hQ
  have key (t : Psi H) (r r' : Fin Dw.p ⊕ Fin Dw.q) (hr : Harm.RowLT r r') :=
    Harm.rowDegree_le_of_rowAdd_eq hr.ne (fun e => hQ0 (rename_injective _ (Equiv.injective _)
      (e.trans (map_zero _).symm))) (h₂ t r) (h₂ t r') (h₃ t r r' hr)
  intro σ i j hij hj
  rcases hij.eq_or_lt with rfl | hlt
  · exact le_rfl
  rcases Harm.half_cases (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate E)
    (Harm.not_mem_hostType_iff H) σ with hσ | ⟨τ, hτ, rfl⟩
  · rw [Harm.mult_of_mem Dw hσ] at hj
    exact key ⟨σ, hσ⟩ (Sum.inl ⟨i, hlt.trans hj⟩) (Sum.inl ⟨j, hj⟩) hlt
  · replace hj : j < Dw.q := Harm.mult_conjEmb_of_mem Dw hτ ▸ hj
    exact key ⟨τ, hτ⟩ (Sum.inr ⟨i, hlt.trans hj⟩) (Sum.inr ⟨j, hj⟩) hlt

theorem exists_lift {emb : Ix → E →+* c.F}
    (h : IoLF (Dw := Dw) c a io (rhoM c emb lam) cga nab0 hw (pG (Dw := Dw) c a n)) :
    ∃ φ : GL (Fin n) E →* Module.End c.F (VVc c lam), (∀ g v, io (φ g v) = letRep n Dw c g (io v)) ∧
      ∀ γ (hγ : γᴴ * γ = 1) v, rhoVr emb lam (uGL γ hγ) v = cga γ • φ (uGL γ hγ) v := by
  obtain ⟨-, hinj, hrange, heq, -⟩ := h
  obtain ⟨φ, hφ⟩ := exists_rep io hinj (letRep n Dw c) fun g v => by
    rw [hrange]
    exact letRep_mem Dw c a g (hrange ▸ LinearMap.mem_range_self io v)
  refine ⟨φ, hφ, fun γ hγ v => hinj ?_⟩
  rw [map_smul io, hφ, letRep_unitary, ← heq γ hγ v]
  exact congrArg (fun f => io (f v)) (rhoM_coe emb lam (uGL γ hγ)).symm

theorem scalar_diag (e : Ix ≃ Psi H) (ha : IsPartFam Dw a) (d : Psi H → ℤ) (hok : hwOK c lam hw)
    (h : IoLF (Dw := Dw) c a io (rhoM c (fun x => embF c (e x).1) lam) cga nab0 hw (pG (Dw := Dw) c a n))
    {t : Fin n → E} (ht : ∀ i, star (t i) * t i = 1) :
    cga (Matrix.diagonal t) = vacChar c n d (Matrix.diagonal t) *
      ∏ x, ∏ i, embF c (e x).1 (t i) ^ ((lamP Dw n ha d (e x)).w i - (lam x).w i) := by
  obtain ⟨hn, hinj, -, heq, -, -, hhw, -⟩ := h
  have hD := diag_unitary ht
  have e1 := heq _ hD hw
  rw [show rhoM c _ lam (Matrix.diagonal t) = _ from rhoM_coe _ lam (uGL _ hD), rhoVr_diag _ _ ht hw hok,
    map_smul io, hhw] at e1
  have e2 := gaStar_pG_vac Dw c ha hn d ht
  have e3 := congrArg (vacChar c n d (Matrix.diagonal t) • ·) e1
  rw [smul_comm _ (cga _), e2, smul_smul, smul_smul] at e3
  have hp : pG (Dw := Dw) c a n ≠ 0 := fun h0 =>
    ne_zero_of_hwOK hok (hinj (hhw.trans (h0.trans (map_zero io).symm)))
  have e4 := smul_left_injective c.F hp e3
  have h0 : ∀ (σ : E →+* c.F) i, σ (t i) ≠ 0 := fun σ i =>
    (_root_.map_ne_zero _).2 (right_ne_zero_of_mul_eq_one (ht i))
  rw [← e.prod_comp] at e4
  refine mul_right_cancel₀ (Finset.prod_ne_zero_iff.2 fun x _ => Finset.prod_ne_zero_iff.2 fun i _ =>
    zpow_ne_zero _ (h0 _ i)) (e4.symm.trans ?_)
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [embPsi, ← zpow_add₀ (h0 _ i)]
  congr 1
  ring

theorem weight_eq_of_tie (e : Ix ≃ Psi H) (ha : IsPartFam Dw a) (hok : hwOK c lam hw)
    (h : IoLF (Dw := Dw) c a io (rhoM c (fun x => embF c (e x).1) lam) cga nab0 hw (pG (Dw := Dw) c a n)) :
    ∃ d : Psi H → ℤ, lam = fun x => lamP Dw n ha d (e x) := by
  obtain ⟨φ, -, hφ⟩ := exists_lift h
  haveI : Module.Finite c.F (VVc c lam) := Module.Finite.of_basis (bVV c.F lam)
  haveI : Nontrivial (VVc c lam) := nontrivial_of_ne _ _ (ne_zero_of_hwOK hok)
  have hN : Module.finrank c.F (VVc c lam) ≠ 0 := Module.finrank_pos.ne'
  generalize hNN : Module.finrank c.F (VVc c lam) = N at hN
  let κ : Ix → Fin n → ℤ := fun x i => (lamP Dw n ha 0 (e x)).w i - (lam x).w i
  have hκ : ∀ x i j, κ x i = κ x j := fun x i j => by
    have := exponents_eq_zero (fun τ => (κ (e.symm τ) i - κ (e.symm τ) j) * N) fun ζ hζ => by
      have hζ0 : ζ ≠ 0 := right_ne_zero_of_mul_eq_one hζ
      let t : Fin n → E := Pi.mulSingle i ζ * Pi.mulSingle j ζ⁻¹
      have ht : ∀ k, star (t k) * t k = 1 := fun k => by
        have h1 : star ζ⁻¹ * ζ⁻¹ = 1 := by rw [star_inv₀, ← mul_inv, hζ, inv_one]
        simp only [t, Pi.mul_apply, Pi.mulSingle_apply, star_mul']
        split_ifs <;> simp_all
      have hd : (Matrix.diagonal t).det = 1 := by
        simp [t, Finset.prod_mul_distrib, hζ0]
      have e1 := pow_eq_one_of_det _ φ (uGL _ (diag_unitary ht)) hd _ (hφ _ _)
      rw [hNN, scalar_diag e ha 0 hok h ht, vacChar, ← e.symm.prod_comp] at e1
      simp only [Pi.zero_apply, neg_zero, zpow_zero, Finset.prod_const_one, one_mul, Equiv.apply_symm_apply,
        ← Finset.prod_pow] at e1
      have e2 : ∏ τ : Psi H, embF c τ.1 ζ ^ ((κ (e.symm τ) i - κ (e.symm τ) j) * N) = 1 := by
        rw [← e1]
        refine Finset.prod_congr rfl fun τ _ => ?_
        have h0 : embF c τ.1 ζ ≠ 0 := (_root_.map_ne_zero _).2 hζ0
        rw [Finset.prod_pow, zpow_mul, zpow_natCast]
        congr 1
        simp only [t, Pi.mul_apply, map_mul, mul_zpow, Finset.prod_mul_distrib]
        rw [Finset.prod_eq_single i (fun k _ hk => by simp [hk]) (by simp),
          Finset.prod_eq_single j (fun k _ hk => by simp [hk]) (by simp), zpow_sub₀ h0]
        simp only [κ, div_eq_mul_inv, Pi.mulSingle_eq_same, map_inv₀, inv_zpow, Equiv.apply_symm_apply]
      have e3 := congrArg c.F.subtype e2
      rw [map_prod, map_one] at e3
      exact (Finset.prod_congr rfl fun τ _ => (map_zpow₀ (c.F.subtype : c.F →+* ℂ) (embF c τ.1 ζ) _).symm).trans e3
    have h1 := congrFun this (e x)
    simp only [Equiv.symm_apply_apply, Pi.zero_apply, mul_eq_zero, Nat.cast_eq_zero, hN, or_false] at h1
    exact sub_eq_zero.1 h1
  refine ⟨fun τ => if hn : 0 < n then -κ (e.symm τ) ⟨0, hn⟩ else 0, funext fun x => ?_⟩
  have : (lam x).w = (lamP Dw n ha (fun τ => if hn : 0 < n then -κ (e.symm τ) ⟨0, hn⟩ else 0) (e x)).w := by
    funext i
    have := hκ x ⟨0, i.pos⟩ i
    simp only [lamP, dif_pos i.pos, Equiv.symm_apply_apply, this]
    simp [κ, lamP]
  generalize lam x = μ, lamP Dw n ha _ (e x) = ν at this
  cases μ
  cases ν
  simpa using this

theorem scalar_eq_vacChar (e : Ix ≃ Psi H) (ha : IsPartFam Dw a) (d : Psi H → ℤ)
    (hl : lam = fun x => lamP Dw n ha d (e x)) (hok : hwOK c lam hw)
    (h : IoLF (Dw := Dw) c a io (rhoM c (fun x => embF c (e x).1) lam) cga nab0 hw (pG (Dw := Dw) c a n))
    (γ : Matrix (Fin n) (Fin n) E) (hγ : γᴴ * γ = 1) : cga γ = vacChar c n d γ := by
  obtain ⟨φ, hφ, hsm⟩ := exists_lift h
  haveI : Module.Finite c.F (VVc c lam) := Module.Finite.of_basis (bVV c.F lam)
  refine scalar_eq_of_diag (rhoVr (fun x => embF c (e x).1) lam) φ _ (ne_zero_of_hwOK hok) cga _
    hsm (fun t ht => ?_) (fun _ _ => vacChar_congr c d) (vacChar_mul c d) (by simp [vacChar])
    (fun Γ hΓ hr => ⟨vacChar_mem c d Γ hΓ hr, fun ℓ => ⟨rhoVr_mem _ _ Γ hΓ hr _ ℓ, ?_⟩⟩) γ hγ
  · rw [scalar_diag e ha d hok h ht, hl]
    simp
  · obtain ⟨r, hr'⟩ := io.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 h.2.1)
    convert gaStar_mem Dw c Γ hr (io hw) (ℓ ∘ₗ r) using 2 with s
    rw [← letRep_unitary Dw c _ (hΓ s), ← hφ, LinearMap.comp_apply, ← LinearMap.comp_apply r, hr', LinearMap.id_apply]

end Comparison₂

section Compare

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H} (Dw : Datum H) (c : Coeff l) (n : ℕ)
  {a : (E →+* ℂ) × ℕ → ℕ}

theorem space_eq (ha : IsPartFam Dw a) (d : Psi H → ℤ) : VVc c (lamP Dw n ha d) = CoefSp Dw c n ha d := rfl

theorem pins_of_ioLF {Ix : Type} [Fintype Ix] (e : Ix ≃ Psi H) (a : (E →+* ℂ) × ℕ → ℕ) (lam : Ix → DomWeight n)
    (io : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (hw : VVc c lam) (cga : Matrix (Fin n) (Fin n) E → c.F)
    (hok : hwOK c lam hw) (h : IoLF (Dw := Dw) c a io (rhoM c (fun x => embF c (e x).1) lam) cga
      (nab0M c (fun x => embF c (e x).1) lam) hw (pG (Dw := Dw) c a n)) :
    ∃ (ha : IsPartFam Dw a) (d : Psi H → ℤ), (lam = fun x => lamP Dw n ha d (e x)) ∧
      ∀ γ : Matrix (Fin n) (Fin n) E, γᴴ * γ = 1 → cga γ = vacChar c n d γ := by
  have ha := isPartFam_of_tie hok h
  obtain ⟨d, hd⟩ := weight_eq_of_tie e ha hok h
  exact ⟨ha, d, hd, scalar_eq_vacChar e ha d hd hok h⟩

end Compare

end GlobalTheory.LFCompare
