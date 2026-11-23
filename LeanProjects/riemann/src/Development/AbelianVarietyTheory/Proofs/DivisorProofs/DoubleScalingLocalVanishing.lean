import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksSubOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicIntertwine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharEqAddEquivAddHaarChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzAdelicEqSpanPure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentMapsForThetaTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumTwistedVacuumConditionDoubledLattic
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped Matrix Kronecker

noncomputable section

namespace GlobalTheory.DblSiegelScal

open Matrix MeasureTheory

section Algebra

variable {K : Type} [CommRing K] {β : Type} [Fintype β] [DecidableEq β]

theorem det_of_diag {a b c d T : Matrix β β K}
    (h : fromBlocks a b c d * (diagCols β : Matrix (β ⊕ β) β K) = (diagCols β : Matrix (β ⊕ β) β K) * T) :
    (fromBlocks a b c d).det = T.det * (d - b).det := by
  simp only [diagCols, fromRows_mul, fromBlocks_mul_fromRows, Matrix.mul_one, Matrix.one_mul, fromRows_ext_iff] at h
  have h6 : fromBlocks a b c d * fromBlocks 1 0 1 1 =
      fromBlocks 1 0 1 1 * (fromBlocks T b 0 (d - b) : Matrix (β ⊕ β) (β ⊕ β) K) := by
    simp [fromBlocks_multiply, h.1, h.2]
  simpa [det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁] using congrArg det h6

theorem adj_diag {P P' : Matrix (β ⊕ β) (β ⊕ β) K} {J T : Matrix β β K} (hJ : IsUnit J.det) (hP : IsUnit P.det)
    (hU : Pᵀ * fromBlocks J 0 0 (-J) * P' = fromBlocks J 0 0 (-J))
    (h : P * (diagCols β : Matrix (β ⊕ β) β K) = (diagCols β : Matrix (β ⊕ β) β K) * T) :
    ∃ T' : Matrix β β K, P' * (diagCols β : Matrix (β ⊕ β) β K) = (diagCols β : Matrix (β ⊕ β) β K) * T' ∧
      P.det * T'.det = T.det := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, P = fromBlocks a b c d := ⟨_, _, _, _, (fromBlocks_toBlocks P).symm⟩
  have hd := det_of_diag h
  have hT : IsUnit T.det := isUnit_of_mul_isUnit_left (hd ▸ hP)
  have h3 := congrArg (· * (diagCols β : Matrix (β ⊕ β) β K)) hU
  simp only [Matrix.mul_assoc] at h3
  obtain ⟨u, w, huw⟩ : ∃ u w, P' * (diagCols β : Matrix (β ⊕ β) β K) = fromRows u w := ⟨_, _, (fromRows_toRows _).symm⟩
  rw [huw] at h3 ⊢
  simp only [diagCols, fromBlocks_transpose, fromRows_mul, fromBlocks_mul_fromRows, Matrix.mul_one, Matrix.one_mul,
    Matrix.zero_mul, add_zero, zero_add, fromRows_ext_iff, Matrix.neg_mul, Matrix.mul_neg] at h h3 ⊢
  have e : Tᵀ * J * (u - w) = 0 := by
    have e1 : Tᵀ * (J * u) = aᵀ * (J * u) + bᵀ * (J * u) := by rw [← h.1, transpose_add, Matrix.add_mul]
    have e2 : Tᵀ * (J * w) = cᵀ * (J * w) + dᵀ * (J * w) := by rw [← h.2, transpose_add, Matrix.add_mul]
    rw [Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_sub, e1, e2]
    refine Eq.trans ?_ ((congrArg₂ (· + ·) h3.1 h3.2).trans (add_neg_cancel J))
    abel
  have hu : IsUnit (Tᵀ * J) := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [det_mul, det_transpose]; exact hT.mul hJ)
  obtain rfl : u = w := sub_eq_zero.1 (hu.mul_right_eq_zero.1 e)
  refine ⟨u, ⟨rfl, rfl⟩, ?_⟩
  have h4 : (d - b)ᵀ * J * u = J := by
    rw [transpose_sub, Matrix.mul_assoc, Matrix.sub_mul]
    refine Eq.trans ?_ ((congrArg Neg.neg h3.2).trans (neg_neg J))
    abel
  have h5 : (d - b).det * u.det = 1 := by
    have := congrArg det h4
    rw [det_mul, det_mul, det_transpose] at this
    exact hJ.mul_left_cancel (by linear_combination this)
  rw [hd, mul_assoc, h5, mul_one]

theorem mul_diagCols {α : Type} (z : Matrix α β K) : z * (diagCols β : Matrix (β ⊕ β) β K)ᵀ = fromCols z z := by
  rw [diagCols, transpose_fromRows, mul_fromCols, transpose_one, Matrix.mul_one]

theorem diagCols_map {L : Type} [CommRing L] (f : K →+* L) :
    (diagCols β : Matrix (β ⊕ β) β K).map f = diagCols β := by
  ext (i | i) j <;> by_cases hij : i = j <;> simp [diagCols, hij]

theorem symp_dbl_diag {R : Type} [CommRing R] [Algebra R K] (c : K →ₐ[R] K) {α : Type} [Fintype α] [DecidableEq α] (ξ : K)
    (JA : Matrix α α K) (JB : Matrix β β K) (x₁ x₂ z : Matrix α β K) :
    symp (R := R) c ξ JA (dbl JB) (fromCols x₁ x₂) (fromCols z z) = symp (R := R) c ξ JA JB (x₁ - x₂) z := by
  unfold symp
  congr 2
  unfold hTens
  simp only [dbl, Fintype.sum_sum_type, fromCols_apply_inl, fromCols_apply_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, mul_neg, neg_mul, Finset.sum_neg_distrib, Matrix.sub_apply, sub_mul,
    Finset.sum_sub_distrib]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem pairing_mul {α : Type} [Fintype α] (A : Matrix α α K) (Y : Matrix α β K) (B : Matrix β β K) (P : Matrix α β K) :
    ∑ k, ∑ l, (A * Y * B) k l * P k l = ∑ k, ∑ l, Y k l * (Aᵀ * P * Bᵀ) k l := by
  have e : ∀ M Q : Matrix α β K, ∑ k, ∑ l, M k l * Q k l = Matrix.trace (M * Qᵀ) := by
    intro M Q
    simp [Matrix.trace, Matrix.mul_apply]
  rw [e, e, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    show A * Y * B * Pᵀ = A * (Y * B * Pᵀ) by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, Matrix.transpose_transpose]

theorem exists_factor {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (ι : V →ₗ[ℂ] V')
    (S : Submodule ℂ V) (h : Set.InjOn ι S) (l : V →ₗ[ℂ] ℂ) : ∃ m : V' →ₗ[ℂ] ℂ, ∀ φ ∈ S, m (ι φ) = l φ := by
  obtain ⟨g, hg⟩ := (ι.domRestrict S).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 fun x y e => Subtype.ext (h x.2 y.2 e))
  exact ⟨l ∘ₗ S.subtype ∘ₗ g, fun φ hφ => congrArg (fun x : S => l x) (LinearMap.congr_fun hg ⟨φ, hφ⟩)⟩

end Algebra

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem form_comp_invT [Invertible (2 : k)] (ψ : AddChar k ℂ) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (m : (Matrix α (β ⊕ β) k → ℂ) →ₗ[ℂ] ℂ)
    (htr : ∀ C : Matrix α β k, ∀ f ∈ SB (Matrix α (β ⊕ β) k), m (fun Y => f (Y + fromCols C C)) = m f)
    (hmu : ∀ D : Matrix α β k, ∀ f ∈ SB (Matrix α (β ⊕ β) k),
      m (fun Y => ψ (∑ i, ∑ j, (Y.toCols₁ - Y.toCols₂) i j * D i j) * f Y) = m f)
    (g : GL (β ⊕ β) k) (T : GL β k)
    (h : g.val * (diagCols β : Matrix (β ⊕ β) β k) = (diagCols β : Matrix (β ⊕ β) β k) * T.val)
    {f : Matrix α (β ⊕ β) k → ℂ} (hf : f ∈ SB (Matrix α (β ⊕ β) k)) :
    m (fun Y => f (Y * (GlobalTheory.SplitFlip.invT g).val)) =
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet T) (Fintype.card α : ℂ) * m f := by
  let σ : α × β ≃ α × β := Equiv.refl _
  let e : Matrix α (β ⊕ β) k ≃ₜ (α × β ⊕ α × β → k) :=
    { toEquiv := (flat (dblNum σ)).toEquiv
      continuous_toFun := continuous_pi fun q => (continuous_id (X := Matrix α (β ⊕ β) k)).matrix_elem _ _
      continuous_invFun := continuous_matrix fun i j => continuous_apply ((dblNum σ).symm (i, j)) }
  have he : ∀ X Y : Matrix α β k, e (fromCols X Y) = Sum.elim (flat σ X) (flat σ Y) := flat_fromCols σ
  have s1 : ∀ φ ∈ SB (α × β ⊕ α × β → k), (fun Y => φ (e Y)) ∈ SB (Matrix α (β ⊕ β) k) := fun φ hφ =>
    ⟨hφ.1.comp_continuous e.continuous, hφ.2.comp_homeomorph e⟩
  have s2 : ∀ f ∈ SB (Matrix α (β ⊕ β) k), (fun x => f (e.symm x)) ∈ SB (α × β ⊕ α × β → k) := fun f hf =>
    ⟨hf.1.comp_continuous e.symm.continuous, hf.2.comp_homeomorph e.symm⟩
  let l := m ∘ₗ LinearMap.funLeft ℂ ℂ e
  have hl0 : ∀ f, l (fun x => f (e.symm x)) = m f := fun f =>
    congrArg m (funext fun Y => congrArg f (e.symm_apply_apply Y))
  have hl : ∀ x y : α × β → k, ∀ φ ∈ SB (α × β ⊕ α × β → k),
      l (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = l φ := by
    intro x y φ hφ
    obtain ⟨C, rfl⟩ := (flat σ).surjective x
    obtain ⟨D, rfl⟩ := (flat σ).surjective y
    have s3 : (fun Y => φ (e (Y + fromCols C C))) ∈ SB (Matrix α (β ⊕ β) k) :=
      ⟨(s1 φ hφ).1.comp_continuous (continuous_add_const _), (s1 φ hφ).2.comp_homeomorph (Homeomorph.addRight _)⟩
    refine Eq.trans ?_ ((hmu D _ s3).trans (htr C _ (s1 φ hφ)))
    refine congrArg m (funext fun Y => ?_)
    obtain ⟨Y₁, Y₂, rfl⟩ : ∃ Y₁ Y₂, Y = fromCols Y₁ Y₂ := ⟨_, _, (fromCols_toCols Y).symm⟩
    have ea : e (fromCols Y₁ Y₂ + fromCols C C) = e (fromCols Y₁ Y₂) + e (fromCols C C) := rfl
    show schr ψ _ φ (e _) = _
    rw [ea, he, he, schr]
    congr 2
    simp only [toCols₁_fromCols, toCols₂_fromCols, sumElim_dotProduct_sumElim, dotProduct_neg, add_neg_cancel, mul_zero,
      add_zero, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib, ← sub_eq_add_neg]
    simp only [dotProduct, Fintype.sum_prod_type]
    rfl
  let G : Matrix (α × β) (α × β) k := (1 : Matrix α α k) ⊗ₖ (T⁻¹).val
  have hG : G.det = ((GeneralLinearGroup.det T)⁻¹ ^ Fintype.card α : kˣ) := by
    rw [det_kronecker, det_one, one_pow, one_mul, ← map_inv, Units.val_pow_eq_pow_val]
    rfl
  let g₀ : GL (α × β) k := GeneralLinearGroup.mkOfDetNeZero G (hG ▸ Units.ne_zero _)
  have hg : GeneralLinearGroup.det g₀ = (GeneralLinearGroup.det T)⁻¹ ^ Fintype.card α := Units.ext hG
  have hgx : ∀ X : Matrix α β k, g₀.val.mulVec (flat σ X) = flat σ (X * (T⁻¹).valᵀ) := by
    intro X
    funext q
    show ∑ q', G q q' * X q'.1 q'.2 = (X * (T⁻¹).valᵀ) q.1 q.2
    rw [Fintype.sum_prod_type, mul_apply]
    simp [G, kroneckerMap_apply, one_apply, mul_comm]
  have h1 : (g⁻¹).val * (diagCols β : Matrix (β ⊕ β) β k) = (diagCols β : Matrix (β ⊕ β) β k) * (T⁻¹).val := by
    have := congrArg (fun N => (g⁻¹).val * N * (T⁻¹).val) h
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at this
    rw [this, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  let R : Matrix α (β ⊕ β) k ≃ₜ Matrix α (β ⊕ β) k :=
    { toFun := fun Y => Y * (GlobalTheory.SplitFlip.invT g).val
      invFun := fun Y => Y * ((GlobalTheory.SplitFlip.invT g)⁻¹).val
      left_inv := fun Y => by simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      right_inv := fun Y => by simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      continuous_toFun := continuous_id.matrix_mul continuous_const
      continuous_invFun := continuous_id.matrix_mul continuous_const }
  have hf' : (fun Y => f (Y * (GlobalTheory.SplitFlip.invT g).val)) ∈ SB (Matrix α (β ⊕ β) k) :=
    ⟨hf.1.comp_continuous R.continuous, hf.2.comp_homeomorph R⟩
  have key := diag_invariant_comp ψ hψ hψ1 l hl g₀ (s2 _ hf) (s2 _ hf') (fun x => by
    obtain ⟨X, rfl⟩ := (flat σ).surjective x
    rw [hgx, ← he, ← he, e.symm_apply_apply, e.symm_apply_apply, ← mul_diagCols, ← mul_diagCols,
      GlobalTheory.SplitFlip.invT_val, Matrix.mul_assoc, Matrix.mul_assoc, ← transpose_mul, ← transpose_mul, h1])
  rw [hl0 f, hl0 (fun Y => f (Y * (GlobalTheory.SplitFlip.invT g).val)), hg] at key
  rw [← key, ← mul_assoc, GlobalTheory.SplitFlip.apow, Complex.cpow_natCast, GlobalTheory.SplitWeil.nabs]
  have hpos : (0 : ℝ) < distribHaarChar k (GeneralLinearGroup.det T) := distribHaarChar_pos (A := k)
  have hne : ((distribHaarChar k (GeneralLinearGroup.det T) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  simp only [map_pow, map_inv, NNReal.coe_pow, NNReal.coe_inv, Complex.ofReal_pow, Complex.ofReal_inv]
  rw [← mul_pow, mul_inv_cancel₀ hne, one_pow, one_mul]

end Local

section Adelic

open GlobalTheory.SplitGLLift GlobalTheory.SplitIdele GlobalTheory.DblScal
open GlobalTheory.Div.CoordOpp (piW_cA incM_map_piW)
open scoped GlobalTheory.VacAny

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}

theorem exists_rest_ne (κ : Type) [Fintype κ] (v : Pl F) :
    ∃ R : (κ ⊕ κ → AF F) → ℂ, (∀ φ ∈ SB (κ ⊕ κ → Fv F v), Rest (evFin F v) φ R) ∧
      ∃ φ ∈ SB (κ ⊕ κ → Fv F v), GlobalTheory.DiagForm.lDiag F κ (tens (evFin F v) φ R) ≠ 0 := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨Φ, hΦ, h0⟩ := GlobalTheory.DiagForm.exists_lDiag_ne (F := F) (κ := κ)
  rw [GlobalTheory.WeylSpan.schA_eq_span_pure] at hΦ
  refine h0 ((Submodule.span_le (p := LinearMap.ker (GlobalTheory.DiagForm.lDiag F κ))).2 ?_ hΦ)
  rintro _ ⟨f, φs, h1, h2, rfl⟩
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φs h2
  have := hne r (fun φ hφ => ⟨hr, ?_⟩) (φs v) (h1 v)
  · rwa [hrt, Function.update_eq_self] at this
  · rw [hrt φ]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually φs v φ h2)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact h1 w

theorem exists_lift (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {α β : Type} (P₀ P₁ : Matrix α β (Fv F v)) :
    ∃ u : Matrix α β (AE F E), At (evFin F v) u ∧ u.map (piW t) = P₀ ∧ u.map (piW (t.comp σ)) = P₁ :=
  ⟨of fun i j => liftPair h t (P₀ i j, P₁ i j), fun a ha => Matrix.ext fun _ _ => at_liftPair h t _ a ha,
    Matrix.ext fun _ _ => piW_liftPair h t _, Matrix.ext fun _ _ => piW_comp_liftPair h t _⟩

omit [NumberField E] in

theorem at_det {β : Type} [Fintype β] [DecidableEq β] {N : Matrix β β (AE F E)} (h : At (evFin F v) (N - 1)) :
    At (evFin F v) (N.det - 1) := by
  intro a ha
  let I : Ideal (AE F E) := LinearMap.ker (LinearMap.lsmul (AE F E) (AE F E) (algebraMap (AF F) (AE F E) a))
  have hI : ∀ z, z ∈ I ↔ a • z = 0 := fun z => by
    rw [Algebra.smul_def]; rfl
  have e : (Ideal.Quotient.mk I).mapMatrix N = (Ideal.Quotient.mk I).mapMatrix 1 :=
    Matrix.ext fun i j => Ideal.Quotient.eq.2 ((hI _).2 (congrFun (congrFun (h a ha) i) j))
  rw [← hI, ← Ideal.Quotient.eq, RingHom.map_det, e, map_one, det_one, map_one]

theorem exists_siegel (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    (hJ : IsUnit (J.map t).det) (c : GL (Fin d) (Fv F v)) {p : UD σ J} (hp : p ∈ UDAt σ J (evFin F v))
    {T : Matrix (Fin d) (Fin d) (Fv F v)}
    (hT : (locMatD t c p).val * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) * T) :
    ∃ (T₀ : GL (Fin d) (Fv F v)) (y : (Fv F v)ˣ) (N : GL (Fin d) (AE F E)), T₀.val = T ∧
      (p : GL (Fin d ⊕ Fin d) (AE F E)).val * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
        (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * N.val ∧
      GeneralLinearGroup.det N = idl h t (GlobalTheory.SplitFlip.gdet T₀, y⁻¹) ∧
      GlobalTheory.SplitFlip.gdet (locMatD t c p) = GlobalTheory.SplitFlip.gdet T₀ * y := by
  set P := (p : GL (Fin d ⊕ Fin d) (AE F E)).val with hP
  have hPu : IsUnit P.det := Matrix.isUnits_det_units _
  have hc : (dsum c).val * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) = (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) * c.val := by
    simp [dsum, diagCols, fromBlocks_mul_fromRows, fromRows_mul]
  have hl : (locMatD t c p).val = ((dsum c)⁻¹).val * P.map (piW t) * (dsum c).val := rfl
  have h1 : P.map (piW t) * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) * (c.val * T * (c⁻¹).val) := by
    have := congrArg (fun Z => (dsum c).val * Z * (c⁻¹).val) hT
    simp only [hl, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, hc] at this
    rw [Matrix.mul_assoc (P.map _), hc, Matrix.mul_assoc, Matrix.mul_assoc _ c.val, Units.mul_inv, Matrix.mul_one] at this
    simpa only [Matrix.mul_assoc] using this
  have hU : (P.map (piW t))ᵀ * fromBlocks (J.map t) 0 0 (-J.map t) * P.map (piW (t.comp σ)) =
      fromBlocks (J.map t) 0 0 (-J.map t) := by
    have := congrArg (fun M => M.map (piW t)) (show Pᵀ * dbl (incM F J) * P.map (cA σ) = dbl (incM F J) from p.2)
    have e1 : (dbl (incM F J)).map (piW t) = fromBlocks (J.map t) 0 0 (-J.map t) := by
      rw [← incM_map_piW]
      ext (i | i) (j | j) <;> simp [dbl]
    have e2 : (P.map (cA σ)).map (piW t) = P.map (piW (t.comp σ)) := Matrix.ext fun i j => piW_cA σ t _
    simpa only [Matrix.map_mul, Matrix.transpose_map, e1, e2] using this
  have hd : ∀ τ : E →ₐ[F] Fv F v, ∀ {β : Type} [Fintype β] [DecidableEq β] (Z : Matrix β β (AE F E)),
      (Z.map (piW τ)).det = piW τ Z.det := fun τ _ _ _ Z => (RingHom.map_det _ _).symm
  obtain ⟨T', h2, h3⟩ := adj_diag hJ (hd t P ▸ hPu.map _) hU h1
  obtain ⟨u, hu, hu1, hu2⟩ := exists_lift h t (c.val * T * (c⁻¹).val - 1) (T' - 1)
  have m1 : (1 + u).map (piW t) = c.val * T * (c⁻¹).val := by
    rw [Matrix.map_add _ (map_add _), hu1, Matrix.map_one _ (map_zero _) (map_one _), add_sub_cancel]
  have m2 : (1 + u).map (piW (t.comp σ)) = T' := by
    rw [Matrix.map_add _ (map_add _), hu2, Matrix.map_one _ (map_zero _) (map_one _), add_sub_cancel]
  have hu' : At (evFin F v) (1 + u - 1) := by rwa [add_sub_cancel_left]
  have hΔ : ∀ τ : E →ₐ[F] Fv F v, (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E).map τ = diagCols (Fin d) :=
    fun τ => diagCols_map (τ : E →+* Fv F v)
  have hN := adelic_intertwine h t (g := P) (P := (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E)) hp hu'
    (by rw [m1, hΔ]; exact h1) (by rw [m2, hΔ]; exact h2)
  rw [show incM F (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E) = diagCols (Fin d) from
    diagCols_map (inclR (F := F) (E := E) (AF F) : E →+* AE F E)] at hN
  have hNu : IsUnit (1 + u).det := by
    have := hN
    rw [← fromBlocks_toBlocks P] at this
    have e := det_of_diag this
    rw [fromBlocks_toBlocks] at e
    exact isUnit_of_mul_isUnit_left (e ▸ hPu)
  have dT : (c.val * T * (c⁻¹).val).det = T.det := det_units_conj c T
  have hTu : IsUnit T.det := by rw [← dT, ← m1, hd]; exact hNu.map _
  have hT'u : IsUnit T'.det := by rw [← m2, hd]; exact hNu.map _
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).2 hTu).unit, hT'u.unit⁻¹, ((Matrix.isUnit_iff_isUnit_det _).2 hNu).unit, rfl, hN,
    Units.ext ?_, ?_⟩
  · rw [inv_inv, ← sub_eq_zero]
    refine eq_zero_of_at h t (fun a ha => ?_) ?_ ?_
    · rw [← sub_sub_sub_cancel_right _ _ 1, smul_sub, at_idl h t _ _ a ha, sub_zero]
      exact at_det hu' a ha
    · rw [map_sub, piW_idl, sub_eq_zero]
      exact (hd t (1 + u)).symm.trans (by rw [m1, dT]; rfl)
    · rw [map_sub, piW_comp_idl, sub_eq_zero]
      exact (hd (t.comp σ) (1 + u)).symm.trans (by rw [m2]; rfl)
  · refine eq_mul_inv_of_mul_eq (Units.ext ?_)
    show (locMatD t c p).val.det * T'.det = T.det
    rw [hl, det_units_conj', h3, dT]

theorem psi_symp (h : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (t : E →ₐ[F] Fv F v) {n d : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {K : Matrix (Fin d) (Fin d) E} (hJ : ∀ i j, σ (J j i) = J i j) (hK : ∀ i j, σ (K j i) = -K i j)
    {x z : Matrix (Fin n) (Fin d) (AE F E)} (hx : At (evFin F v) x) (hz : z.map (piW t) = 0) :
    ψ (symp (cA σ) (-1) (incM F J) (incM F K) x z) = GlobalTheory.LatVac.psiAt ψ v
      (∑ i, ∑ j, (x.map (piW t)) i j * (-(J.map t * z.map (piW (t.comp σ)) * (K.map t)ᵀ)) i j) := by
  have hA : At (evFin F v) (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F K) x z) := by
    intro a ha
    have h0 : ∀ i j, a • x i j = 0 := fun i j => congrFun (congrFun (hx a ha) i) j
    rw [symp, ← map_smul, ← mul_smul_comm, hTens]
    simp only [Finset.smul_sum, ← smul_mul_assoc, h0, zero_mul, Finset.sum_const_zero, mul_zero, map_zero]
  rw [GlobalTheory.VacAny.eq_atPlace_of_at v _ hA]
  show GlobalTheory.LatVac.psiAt ψ v (evFin F v _) = _
  rw [GlobalTheory.LinCoords.splitTrace' h v t J K hJ hK x z hx, hz]
  simp

end Adelic

open GlobalTheory.DblScal GlobalTheory.SplitIdele
open scoped GlobalTheory.VacAny

theorem scalar_siegel : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
      (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W.J)) dd χX (diagCols (Fin d)) omd →
      GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd → ∀ cd, GlobalTheory.DblScal.IsShapeD omd t c ιd cd →
      ∀ p ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v),
        (∃ T : Matrix (Fin d) (Fin d) (Fv F v),
          ((GlobalTheory.DblScal.locMatD t c p).val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (Fv F v)) *
            (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) =
            (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) * T) →
        cd p = (chrW χX t (GlobalTheory.SplitFlip.gdet (GlobalTheory.DblScal.locMatD t c p)) : ℂ) *
          GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (GlobalTheory.DblScal.locMatD t c p)) (-(n : ℂ) / 2) := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t b c dd omd hdd hW hloc ιd hι cd hcd p hp ⟨T, hT⟩
  have hcm : IsCMExt F E σ := hP.base.cm
  have hstd := hP.base.std
  have hX : IsUnit (X.J.map t).det :=
    isUnit_iff_ne_zero.2 (GlobalTheory.SplitIdele.det_map_ne_zero (GlobalTheory.SplitIdele.det_ne_zero_herm hP.herm) t)
  have hK : IsUnit (W.J.map t).det :=
    isUnit_iff_ne_zero.2 (GlobalTheory.SplitIdele.det_map_ne_zero (GlobalTheory.SplitIdele.det_ne_zero_skew hP.skew) t)
  obtain ⟨R, hR, φ₀, hφ₀, h0⟩ := exists_rest_ne (Fin n × Fin d) v
  let lam : ((Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ := GlobalTheory.DiagForm.lDiag F (Fin n × Fin d) ∘ₗ
    { toFun := fun φ => tens (evFin F v) φ R
      map_add' := fun _ _ => funext fun _ => add_mul _ _ _
      map_smul' := fun _ _ => funext fun _ => mul_assoc _ _ _ }
  have hlam : ∀ φ, lam φ = GlobalTheory.DiagForm.lDiag F (Fin n × Fin d) (tens (evFin F v) φ R) := fun _ => rfl
  obtain ⟨m, hm⟩ := exists_factor ιd _ hι.bij.injOn lam
  have hinv : ∀ z : Matrix (Fin n) (Fin d) (AE F E), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
      GlobalTheory.DiagForm.lDiag F _ (dd.rho B.ψ (fromCols z z) Φ) = GlobalTheory.DiagForm.lDiag F _ Φ := fun z Φ hΦ => by
    rw [Darboux.rho, hdd z z, GlobalTheory.DiagForm.lDiag_schr B.ψ _ _ hΦ]
  have hat : ∀ z : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) z → At (evFin F v) (fromCols z z) := fun z hz a ha => by
    ext i (j | j) <;> exact congrFun (congrFun (hz a ha) i) j
  have hrho : ∀ z : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) z → ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
      ∃ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), Acts (evFin F v) (dd.rho B.ψ (fromCols z z)) φ φ₁ ∧
        m (ιd φ₁) = m (ιd φ) := fun z hz φ hφ => by
    have h1 := GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v (GlobalTheory.LatVac.locCo dd v (fromCols z z)) φ hφ
    have h2 := GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ (hat z hz) φ
    refine ⟨_, h1, h2, ?_⟩
    rw [hm _ h1, hm _ hφ, hlam, hlam, ← h2 R (hR φ hφ), hinv z _ (hR φ hφ).2]
  have hco : ∀ Y₁ Y₂ : Matrix (Fin n) (Fin d) (Fv F v),
      (b⁻¹).val * fromCols (b.val * Y₁ * c.valᵀ) (b.val * Y₂ * c.valᵀ) * ((dsum c)⁻¹).valᵀ = fromCols Y₁ Y₂ := by
    intro Y₁ Y₂
    have e : ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), (b⁻¹).val * (b.val * Y * c.valᵀ) * (c⁻¹).valᵀ = Y := fun Y => by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, ← transpose_mul,
        Units.inv_mul, transpose_one, Matrix.mul_one]
    rw [show ((dsum c)⁻¹).val = fromBlocks (c⁻¹).val 0 0 (c⁻¹).val from rfl, mul_fromCols, fromBlocks_transpose, fromCols_mul_fromBlocks, transpose_zero, Matrix.mul_zero, Matrix.mul_zero,
      add_zero, zero_add, e, e]
  have htr : ∀ C : Matrix (Fin n) (Fin d) (Fv F v), ∀ f ∈ SB (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)),
      m (fun Y => f (Y + fromCols C C)) = m f := by
    intro C f hf
    obtain ⟨φ, hφ, rfl⟩ := hι.bij.surjOn hf
    obtain ⟨z, hz, z1, z2⟩ := exists_lift hcm t (b.val * C * c.valᵀ) 0
    obtain ⟨φ₁, hφ₁, ha, e⟩ := hrho z hz φ hφ
    rw [← e]
    refine congrArg m (funext fun Y => ?_)
    rw [hι.trans _ (hat z hz) (by rw [fromCols_map, z2, fromCols_zero]) φ hφ φ₁ hφ₁ ha Y, fromCols_map, z1, hco]
  have hmu : ∀ D : Matrix (Fin n) (Fin d) (Fv F v), ∀ f ∈ SB (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)),
      m (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, (Y.toCols₁ - Y.toCols₂) i j * D i j) * f Y) = m f := by
    intro D f hf
    obtain ⟨φ, hφ, rfl⟩ := hι.bij.surjOn hf
    obtain ⟨z, hz, z1, z2⟩ := exists_lift hcm t 0
      (-((X.J.map t)⁻¹ * ((b⁻¹).valᵀ * D * (c⁻¹).val) * ((W.J.map t)⁻¹)ᵀ))
    obtain ⟨φ₁, hφ₁, ha, e⟩ := hrho z hz φ hφ
    rw [← e]
    refine congrArg m (funext fun Y => ?_)
    obtain ⟨Y₁, Y₂, rfl⟩ : ∃ Y₁ Y₂, Y = fromCols Y₁ Y₂ := ⟨_, _, (fromCols_toCols Y).symm⟩
    obtain ⟨x₁, hx₁, a1, a2⟩ := exists_lift hcm t (b.val * Y₁ * c.valᵀ) 0
    obtain ⟨x₂, hx₂, b1, b2⟩ := exists_lift hcm t (b.val * Y₂ * c.valᵀ) 0
    have hx : At (evFin F v) (fromCols x₁ x₂) := fun a ha => by
      ext i (j | j)
      exacts [congrFun (congrFun (hx₁ a ha) i) j, congrFun (congrFun (hx₂ a ha) i) j]
    have key := hι.mult _ (hat z hz) (by rw [fromCols_map, z1, fromCols_zero]) φ hφ φ₁ hφ₁ ha _ hx
      (by rw [fromCols_map, a2, b2, fromCols_zero])
    rw [fromCols_map, a1, b1, hco, symp_dbl_diag, psi_symp hcm B.ψ t hP.herm.herm hP.skew.skew
      (fun a ha => by rw [smul_sub, hx₁ a ha, hx₂ a ha, sub_zero]) z1, Matrix.map_sub _ (map_sub _), a1, b1, z2,
      ← Matrix.sub_mul, ← Matrix.mul_sub, pairing_mul] at key
    rw [key, toCols₁_fromCols, toCols₂_fromCols]
    have e2 : b.valᵀ * -(X.J.map t * -((X.J.map t)⁻¹ * ((b⁻¹).valᵀ * D * (c⁻¹).val) * ((W.J.map t)⁻¹)ᵀ) * (W.J.map t)ᵀ) *
        c.valᵀᵀ = D := by
      rw [Matrix.mul_neg (X.J.map t), Matrix.neg_mul, neg_neg, transpose_transpose, ← Matrix.mul_assoc (X.J.map t),
        ← Matrix.mul_assoc (X.J.map t), Matrix.mul_nonsing_inv _ hX, Matrix.one_mul, Matrix.mul_assoc _ _ (W.J.map t)ᵀ,
        ← transpose_mul, Matrix.mul_nonsing_inv _ hK, transpose_one, Matrix.mul_one, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, ← transpose_mul, Units.inv_mul, transpose_one, Matrix.one_mul, Matrix.mul_assoc,
        Units.inv_mul, Matrix.mul_one]
    rw [e2]
  obtain ⟨T₀, y, N, rfl, hN, hdet, hp'⟩ := exists_siegel hcm t hK c hp hT
  obtain ⟨φ₁, hφ₁, ha⟩ := hloc p hp φ₀ hφ₀
  have k1 := hW.2.2 _ GlobalTheory.DiagForm.lDiag_adm (fun z Φ hΦ => by rw [mul_diagCols]; exact hinv z Φ hΦ) p N hN _
    (hR φ₀ hφ₀).2
  rw [ha R (hR φ₀ hφ₀), GlobalTheory.ModuNorm.modu_norm_eq_absE F E hcm.1, hdet, Fintype.card_fin,
    char_idl hcm χX hP.resX, ← hlam, ← hlam, ← hm _ hφ₁, hcd p hp φ₀ hφ₀ φ₁ hφ₁ ha, map_smul,
    form_comp_invT _ (GlobalTheory.SchrSB.continuous_psiAt _ hstd.1 v) (GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd v) m htr hmu _ T₀ hT
      (hι.bij.mapsTo hφ₀), hm _ hφ₀, Fintype.card_fin, smul_eq_mul, ← mul_assoc] at k1
  have k2 := mul_right_cancel₀ h0 k1
  refine mul_right_cancel₀ (GlobalTheory.SplitFlip.apow_ne_zero (GlobalTheory.SplitFlip.gdet T₀) (n : ℂ)) ?_
  have k3 := GlobalTheory.SplitFlip.apow_add (GlobalTheory.SplitFlip.gdet T₀) (-(n : ℂ) / 2) n
  rw [show -(n : ℂ) / 2 + n = n / 2 by ring] at k3
  rw [k2, hp', map_mul, Units.val_mul, GlobalTheory.SplitFlip.apow_mul, k3]
  ring

end GlobalTheory.DblSiegelScal

end
