import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt

noncomputable section

namespace PositivityTheory.ThKH.Iwas

open scoped Matrix TensorProduct nonZeroDivisors
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)}

def InD (z : E) : Prop := ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * z))

theorem InD.mul {z : E} (h : InD z) (b : 𝓞 E) : InD (z * (b : E)) := fun o => by
  have := h (o * b)
  rwa [show ((o * b : 𝓞 E) : E) * z = (o : E) * (z * b) by push_cast; ring] at this

theorem inD_iff (z : E) : InD z ↔ z ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [FractionalIdeal.mem_dual (by
    rw [← FractionalIdeal.coeIdeal_top]; exact FractionalIdeal.coeIdeal_ne_zero.2 top_ne_bot)]
  constructor
  · intro h a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨q, hq⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 (h o)
    refine ⟨q, ?_⟩
    rw [hq, Algebra.traceForm_apply, mul_comm]
  · intro h o
    obtain ⟨q, hq⟩ := h _ ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
    rw [Algebra.traceForm_apply] at hq
    rw [mul_comm]
    have : Algebra.trace ℚ E (z * (o : E)) = algebraMap ℤ ℚ q := by rw [hq]
    rw [this]; exact isIntegral_algebraMap

theorem exists_gen (w : HeightOneSpectrum (𝓞 E)) :
    ∃ δ : E, δ ≠ 0 ∧ InD δ ∧ ∀ z, InD z → w.valuation E z ≤ w.valuation E δ := by
  classical
  set I := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) with hI
  obtain ⟨S, hS⟩ : (I : Submodule (𝓞 E) E).FG := FractionalIdeal.fg_of_isNoetherianRing le_rfl I
  obtain ⟨δ, hδ, hmax⟩ := Finset.exists_max_image (insert 0 S) (w.valuation E) (Finset.insert_nonempty _ _)
  have hall : ∀ z ∈ (I : Submodule (𝓞 E) E), w.valuation E z ≤ w.valuation E δ := fun z hz => by
    rw [← hS] at hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact hmax x (Finset.mem_insert_of_mem hx)
    | zero => simp
    | add x y _ _ hx hy => exact (Valuation.map_add _ _ _).trans (max_le hx hy)
    | smul a x _ hx =>
      rw [Algebra.smul_def, map_mul]
      exact (mul_le_mul' (w.valuation_le_one a) hx).trans_eq (one_mul _)
  have hmem : δ ∈ (I : Submodule (𝓞 E) E) := by
    rcases Finset.mem_insert.1 hδ with rfl | h
    · exact zero_mem _
    · rw [← hS]; exact Submodule.subset_span h
  refine ⟨δ, fun h0 => ?_, (inD_iff δ).2 hmem, fun z hz => hall z ((inD_iff z).1 hz)⟩
  have h1 : (1 : E) ∈ I := FractionalIdeal.one_le_dual_one ℤ ℚ (FractionalIdeal.one_mem_one _)
  have := hall 1 h1
  simp [h0] at this

omit [NumberField F] in
theorem val_unit (h : w.under (𝓞 F) = v) {s : 𝓞 F} (hs : s ∉ v.asIdeal) : w.valuation E (algebraMap F E s) = 1 := by
  subst h
  exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) w (r := algebraMap (𝓞 F) (𝓞 E) s)).2 hs

omit [NumberField F] [NumberField E] in
theorem form_mulVec (J P : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    form σ J (P *ᵥ x) (P *ᵥ y) = x ⬝ᵥ (Pᵀ * J * P.map σ) *ᵥ fun i => σ (y i) := by
  have e : (fun i => σ ((P *ᵥ y) i)) = P.map σ *ᵥ fun i => σ (y i) :=
    funext fun i => RingHom.map_mulVec (σ : E →+* E) P y i
  rw [form, e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose]

theorem det_ne_zero {B : Base F E} {W : Spc F E n} {r s : ℕ} (hW : W.IsSkew σ B r s) : W.J.det ≠ 0 := by
  obtain ⟨u⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨hrs, A, hA⟩ := hW.sig u
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let P : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have key : Pᵀ * (Complex.I • W.J.map (B.emb u).1) * P.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    rfl
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_neg,
    Matrix.det_one, Matrix.det_mul, Matrix.det_mul] at hd
  intro h0
  have hm : (W.J.map (B.emb u).1).det = (B.emb u).1 W.J.det := (RingHom.map_det _ _).symm
  rw [Matrix.det_smul, hm, h0, map_zero, mul_zero, mul_zero, zero_mul, Fintype.card_fin, one_mul, mul_one] at hd
  exact pow_ne_zero s (neg_ne_zero.mpr one_ne_zero) hd.symm

theorem gram_bounds (h : w.under (𝓞 F) = v) {B : Base F E} {W : Spc F E n} {r s : ℕ} (hW : W.IsSkew σ B r s)
    (P : GL (Fin n) E) (h1 : ∀ j, ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ algebraMap F E s • (fun i => P.1 i j) ∈ W.L)
    (h2 : ∀ x ∈ W.L, ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ algebraMap F E s • ((P⁻¹).1 *ᵥ x) ∈ stdLattice E n) :
    ∃ (δ : E) (G' : Matrix (Fin n) (Fin n) E), δ ≠ 0 ∧ G' * (P.1ᵀ * W.J * P.1.map σ) = 1 ∧
      (∀ i j, w.valuation E ((P.1ᵀ * W.J * P.1.map σ) i j) ≤ w.valuation E δ) ∧
      ∀ i j, w.valuation E (δ * G' i j) ≤ 1 := by
  classical
  obtain ⟨δ, h0, hδ, hmax⟩ := exists_gen w
  set G := P.1ᵀ * W.J * P.1.map σ with hG
  have hGu : IsUnit G.det := by
    rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    have a1 : IsUnit P.1.det := (Matrix.isUnit_iff_isUnit_det _).1 P.isUnit
    have a2 : (P.1.map σ).det = σ P.1.det := (RingHom.map_det (σ : E →+* E) _).symm
    rw [a2]
    exact (a1.mul (det_ne_zero hW).isUnit).mul (a1.map σ)
  have hG' : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hGu
  refine ⟨δ, G⁻¹, h0, hG', fun i j => ?_, fun i j => ?_⟩
  · obtain ⟨a, ha, ha'⟩ := h1 i
    obtain ⟨b, hb, hb'⟩ := h1 j
    have e : ∀ (t : E) (k : Fin n), t • (fun i => P.1 i k) = P.1 *ᵥ Pi.single k t := fun t k => by
      ext l; simp [mul_comm]
    have := hmax _ ((hW.dual _).1 ha' _ hb')
    rw [e, e, form_mulVec, ← hG, show (fun l => σ (Pi.single (M := fun _ => E) j (algebraMap F E b) l)) =
      Pi.single j (algebraMap F E b) from funext fun l => by
        by_cases el : l = j
        · subst el; simp
        · simp [el]] at this
    rw [single_dotProduct, Matrix.mulVec_single, map_mul, val_unit h ha, one_mul] at this
    change w.valuation E (G i j * algebraMap F E b) ≤ _ at this
    rwa [map_mul, val_unit h hb, mul_one] at this
  · obtain ⟨S, hS⟩ := hW.lat.fg
    choose! f hf hf' using h2
    have hmemS : ∀ x ∈ S, x ∈ W.L := fun x hx => hS ▸ Submodule.subset_span hx
    have := v.isPrime
    let t : 𝓞 F := ∏ x ∈ S, f x
    have ht : t ∉ v.asIdeal := by
      intro hmem
      obtain ⟨x, hx, hx'⟩ := Ideal.IsPrime.prod_mem_iff.1 hmem
      exact hf x (hmemS x hx) hx'
    have ht' : ∀ x ∈ W.L, algebraMap F E t • ((P⁻¹).1 *ᵥ x) ∈ stdLattice E n := fun x hx => by
      rw [← hS] at hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        have e : t = (∏ y ∈ S.erase x, f y) * f x := (Finset.prod_erase_mul _ _ hx).symm
        have e' : algebraMap F E t = algebraMap F E (∏ y ∈ S.erase x, f y : 𝓞 F) * algebraMap F E (f x) := by
          rw [e, ← map_mul]; rfl
        rw [e', mul_smul]
        exact (stdLattice E n).smul_mem (algebraMap (𝓞 F) (𝓞 E) (∏ y ∈ S.erase x, f y)) (hf' x (hmemS x hx))
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.mulVec_add, smul_add]; exact add_mem hx hy
      | smul a x _ hx => rw [Matrix.mulVec_smul, smul_comm]; exact (stdLattice E n).smul_mem a hx
    let u : Fin n → E := (algebraMap F E t * δ) • G⁻¹ i
    have hy : P.1 *ᵥ u ∈ W.L := (hW.dual _).2 fun x hx => by
      obtain ⟨o, ho⟩ := ht' x hx i trivial
      have ex : x = P.1 *ᵥ ((P⁻¹).1 *ᵥ x) := by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      have e : form σ W.J (P.1 *ᵥ u) x = δ * ((RingOfIntegers.mapRingHom (σ : E →+* E) o : 𝓞 E) : E) := by
        rw [ex, form_mulVec, ← hG, Matrix.dotProduct_mulVec, Matrix.smul_vecMul,
          show G⁻¹ i ᵥ* G = Pi.single i 1 from funext fun l => by
            rw [← Matrix.mul_apply_eq_vecMul, hG', Matrix.one_apply, Pi.single_apply]; exact if_congr eq_comm rfl rfl,
          smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul]
        change _ = δ * σ (Algebra.linearMap (𝓞 E) E o)
        rw [ho, Pi.smul_apply, smul_eq_mul, map_mul, σ.commutes]
        ring
      change InD _
      rw [e]
      exact hδ.mul _
    obtain ⟨o, ho⟩ := hf' _ hy j trivial
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at ho
    have := w.valuation_le_one (K := E) o
    change w.valuation E (Algebra.linearMap (𝓞 E) E o) ≤ 1 at this
    rw [ho] at this
    simpa [u, val_unit h ht, val_unit h (hf _ hy)] using this

theorem exists_frame (hσ : IsCMExt F E σ) (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c) {B : Base F E} {W : Spc F E n} {r s : ℕ}
    (hW : W.IsSkew σ B r s) : ∃ a : GL (Fin n) (w.adicCompletion E), IsFrameAt w W.L a ∧
      ∃ l : w.adicCompletion E, l ≠ 0 ∧ a.1ᵀ * W.J.map (algebraMap E _) * a.1.map c = l • antiJ _ n := by
  have := hW.lat
  obtain ⟨ϖ, hU⟩ := exists_isUnramInv hσ hw hc
  obtain ⟨P, h1, h2⟩ := Frames.exists_rational_frame W.L v
  obtain ⟨δ, G', h0, hG', b1, b2⟩ := gram_bounds h hW P h1 h2
  set G := P.1ᵀ * W.J * P.1.map σ with hG
  let ι := algebraMap E (w.adicCompletion E)
  have hval : ∀ a : E, Valued.v (ι a) = w.valuation E a := fun a =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  let a : GL (Fin n) (w.adicCompletion E) := bc (toCompl h) (bc (inclR (Fv F v)) P)
  have ha : IsFrameAt w W.L a := fun z => by
    obtain ⟨y, rfl⟩ := exists_comp h z
    rw [← comp_mulVec, ← mem_latLoc_iff hw, ← Frames.frame_of_rational P h1 h2]
    exact forall_congr' fun i => (mem_intLoc_iff hw h _).symm
  have ea : a.1 = P.1.map ι := Matrix.ext fun i j => (toCompl_tmul h 1 _).trans (by rw [map_one, one_mul]; rfl)
  have eG : a.1ᵀ * W.J.map ι * a.1.map c = G.map ι := by
    rw [hG, Matrix.map_mul, Matrix.map_mul, ea]
    congr 1
    exact Matrix.ext fun i j => conj_algebraMap hc _
  obtain ⟨hcc, hv, hϖ, hϖv, ⟨x, hx, hx1⟩, -⟩ := id hU
  have hδ0 : Valued.v (ι δ) ≠ 0 := by simpa using h0
  let l : w.adicCompletion E := ϖ ^ (-WithZero.log (Valued.v (ι δ))) * (c x - x)
  have hl : Valued.v l = Valued.v (ι δ) := by
    rw [map_mul, hx1, mul_one, map_zpow₀, hϖv]
    change WithZero.exp (-1 : ℤ) ^ _ = _
    rw [← WithZero.exp_zsmul]
    conv_rhs => rw [← WithZero.exp_log hδ0]
    simp
  have hl0 : l ≠ 0 := fun e => hδ0 (by rw [← hl, e, map_zero])
  have hcl : c l = -l := by
    rw [map_mul, map_zpow₀, hϖ, map_sub, hcc]; ring
  have hsk : ∀ i j, σ (G j i) = -G i j := fun i j => by
    have e1 : W.J.map σ = -W.Jᵀ := Matrix.ext fun i j => hW.skew j i
    have e2 : (P.1.map σ).map σ = P.1 := Matrix.ext fun i j => conj_conj hσ _
    have e3 : G.map σ = -Gᵀ := by
      rw [hG, Matrix.map_mul (f := σ), Matrix.map_mul (f := σ)]
      change (P.1.map σ)ᵀ * W.J.map σ * (P.1.map σ).map σ = _
      rw [e1, e2]
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    exact congrFun (congrFun e3 j) i
  obtain ⟨H, hH, eH⟩ := Formalism.UG.P.cartan_exists_glint (Ov E w) (l⁻¹ • (G.map ι)ᵀ) (l • (G'.map ι)ᵀ)
    (by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hl0, one_smul, ← Matrix.transpose_mul,
      ← Matrix.map_mul, hG', Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one])
    (fun i j => by
      change Valued.v (l⁻¹ * ι (G j i)) ≤ 1
      rw [map_mul, map_inv₀, hl, hval, hval]
      rw [hval] at hδ0
      exact inv_mul_le_one_of_le₀ (b1 j i) zero_le)
    (fun i j => by
      change Valued.v (l * ι (G' j i)) ≤ 1
      rw [map_mul, hl, hval, hval, ← map_mul]
      exact b2 j i)
  obtain ⟨k, hk, ek⟩ := exists_congr_antiJ hU hH (by
    rw [eH]
    refine Matrix.ext fun i j => ?_
    change c (l⁻¹ * ι (G i j)) = l⁻¹ * ι (G j i)
    rw [map_mul, map_inv₀, hcl, conj_algebraMap hc, hsk, map_neg, inv_neg, neg_mul_neg])
  refine ⟨a * k, (isFrameAt_mul ha hk).1, l, hl0, ?_⟩
  have e1 : (antiJ (w.adicCompletion E) n)ᵀ = antiJ _ n := by
    ext i j
    simp [antiJ, add_comm i.val]
  rw [← e1, ← ek, eH, Units.val_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul, cT,
    Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_transpose, ← eG, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, mul_inv_cancel₀ hl0, one_smul]
  simp only [Matrix.mul_assoc]
  rfl

end PositivityTheory.ThKH.Iwas
