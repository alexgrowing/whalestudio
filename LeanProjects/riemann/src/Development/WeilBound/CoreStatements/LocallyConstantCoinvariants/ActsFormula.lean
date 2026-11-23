import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.EqZeroOfLocW
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumTensorProduct
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.DblCoordUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype κ] {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {ψ : AddChar (AF F) ℂ}

theorem schr_box {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ κ' : Type} [Fintype κ] [Fintype κ']
    (w : (κ ⊕ κ' → R) × (κ ⊕ κ' → R)) (φ₁ : (κ → R) → ℂ) (φ₂ : (κ' → R) → ℂ) :
    schr ψ w (boxFun φ₁ φ₂) = boxFun (schr ψ (w.1 ∘ Sum.inl, w.2 ∘ Sum.inl) φ₁) (schr ψ (w.1 ∘ Sum.inr, w.2 ∘ Sum.inr) φ₂) := by
  funext x
  simp only [schr, boxFun, dotProduct, Fintype.sum_sum_type, Function.comp_apply, mul_add, AddChar.map_add_eq_mul]
  rw [show (x + w.1) ∘ Sum.inl = x ∘ Sum.inl + w.1 ∘ Sum.inl from rfl, show (x + w.1) ∘ Sum.inr = x ∘ Sum.inr + w.1 ∘ Sum.inr from rfl]
  ring

theorem schr_zero' {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ] (φ : (κ → R) → ℂ) :
    schr ψ (0, 0) φ = φ := by
  funext x
  simp [schr]

def tensL (v : Pl F) (r : (κ → AF F) → ℂ) : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun φ := tens (evFin F v) φ r
  map_add' _ _ := funext fun _ => add_mul _ _ _
  map_smul' _ _ := funext fun _ => mul_assoc _ _ _

def boxL {R κ κ' : Type} (Φ₂ : (κ' → R) → ℂ) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ ⊕ κ' → R) → ℂ) where
  toFun Φ := boxFun Φ Φ₂
  map_add' _ _ := funext fun _ => add_mul _ _ _
  map_smul' _ _ := funext fun _ => mul_assoc _ _ _

theorem tens_box (φ₁ φ₂ : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ) :
    tens (evFin F v) (boxFun φ₁ φ₂) (boxFun r r) = boxFun (tens (evFin F v) φ₁ r) (tens (evFin F v) φ₂ r) :=
  funext fun _ => mul_mul_mul_comm _ _ _ _

theorem Grams.dbl (hG : Grams σ t JA JB) : Grams σ t JA (dbl JB) := by
  have e : ∀ f : AE F E →+* Fv F v, (GlobalTheory.WeilM.dbl JB).map f = fromBlocks (JB.map f) 0 0 (-JB.map f) := fun f => by
    rw [GlobalTheory.WeilM.dbl, fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _)]
  obtain ⟨ε, h1, h2, h3⟩ := hG.sym
  refine ⟨hG.uA, ?_, ε, h1, h2, ?_⟩
  · rw [e, Matrix.isUnit_iff_isUnit_det, det_fromBlocks_zero₂₁, det_neg]
    have := (Matrix.isUnit_iff_isUnit_det _).1 hG.uB
    exact this.mul ((isUnit_one.neg.pow _).mul this)
  · rw [e, e, h3, fromBlocks_transpose, fromBlocks_smul]
    simp

theorem acts_formula (hM : ModelEx) (hC : Cyc) (hA : AdSt) (hψ : IsStd ψ) (h : IsSec σ t sec) (hG : Grams σ t JA JB)
    {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ} {ι} (hι : LM t ψ d ι) {χ : Chr F E}
    {om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)} (hom : IsWeilB (cA σ) (adeleClass F) ψ (-1) JA JB d χ om)
    (g : UG (cA σ) JB) (ha : At (evFin F v) (((g : GL β (AE F E)) : Matrix β β (AE F E)) - 1)) (g₀ : GL β (Fv F v))
    (hg : ((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW t) = g₀) :
    ∀ φ ∈ SB (κ → Fv F v), ∃ φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) (om g) φ φ₁ ∧
      ι φ₁ = ((chrW χ t (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card α : ℂ) / 2)) • rmL g₀ (ι φ) := by
  obtain ⟨hs, dd, omd, hdd, hsd, hR, hbox⟩ := hom
  obtain ⟨hc, h1⟩ := (hA.psi F ψ hψ).2 v
  obtain ⟨j, hj, hj'⟩ := kd_exists_inv hι.bij
  obtain ⟨c, hcA⟩ := acts_scalar hA hψ h hG hι hj hs g ha g₀ hg
  suffices hcs : c = (chrW χ t (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card α : ℂ) / 2) from fun φ hφ =>
    have := hj _ (rmL_mem g₀ (hι.bij.1 hφ))
    ⟨_, Submodule.smul_mem _ _ this.1, hcA φ hφ, by rw [map_smul, this.2, hcs]⟩
  have hG2 := hG.dbl
  obtain ⟨ε, -, -, hε⟩ := hG2.sym
  obtain ⟨ι₂, hι₂⟩ := exists_lm hM hA hψ h hG2 dd
  obtain ⟨j₂, hj₂, -⟩ := kd_exists_inv hι₂.bij
  let X₀ : GL (β ⊕ β) (Fv F v) := ⟨fromBlocks 1 0 (-1) 1, fromBlocks 1 0 1 1, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩
  let P₀ : GL (β ⊕ β) (Fv F v) := ⟨fromBlocks g₀.1 0 (g₀.1 - 1) 1, fromBlocks (g₀⁻¹).1 0 ((g₀⁻¹).1 - 1) 1,
    by simp [fromBlocks_multiply, Matrix.sub_mul], by simp [fromBlocks_multiply, Matrix.sub_mul]⟩
  obtain ⟨x, hxa, hx⟩ := h.exists_ug hε hG2.uB X₀
  obtain ⟨p, hpa, hp⟩ := h.exists_ug hε hG2.uB P₀
  obtain ⟨gd, hgd⟩ := GlobalTheory.CompanionTheory.ThetaMember.exists_dbl_elem g
  obtain ⟨tt, hta, ht1, ht2⟩ := h.exists_gl g₀ 1
  have atm : ∀ {a b : Matrix (β ⊕ β) (β ⊕ β) (AE F E)}, At (evFin F v) (a - 1) → At (evFin F v) (b - 1) →
      At (evFin F v) (a * b - 1) := fun {a b} h1 h2 => by
    rw [show a * b - 1 = (a - 1) * b + (b - 1) by noncomm_ring]
    exact (h1.kd_mul_right _).kd_add h2
  have hga : At (evFin F v) (((gd : GL (β ⊕ β) (AE F E)) : Matrix (β ⊕ β) (β ⊕ β) (AE F E)) - 1) := by
    rw [hgd, kd_at_matrix]
    rintro (i | i) (k | k) u hu
    · simpa [one_apply] using kd_at_matrix.1 ha i k u hu
    all_goals simp [one_apply]
  have hxp : x * p = gd * x := h.ug_ext hG2.uB (atm hxa hpa) (atm hga hxa) (by
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, hx, hp, hgd, fromBlocks_map, hg,
      Matrix.map_zero _ (map_zero (piW t)), Matrix.map_one _ (map_zero (piW t)) (map_one _), X₀, P₀]
    simp [fromBlocks_multiply]
    abel)
  have cy : ∀ f : AE F E →+* Fv F v, (diagCols β : Matrix (β ⊕ β) β (AE F E)).map f = fromRows 1 1 := fun f => by
    rw [diagCols, fromRows_map, Matrix.map_one _ (map_zero _) (map_one _)]
  have hpt : ((p : GL (β ⊕ β) (AE F E)) : Matrix (β ⊕ β) (β ⊕ β) (AE F E)) * (diagCols β : Matrix (β ⊕ β) β (AE F E)) =
      (diagCols β : Matrix (β ⊕ β) β (AE F E)) * (tt : Matrix β β (AE F E)) := by
    refine h.extM ?_ ?_ ?_
    · have := (hpa.kd_mul_right (diagCols β)).kd_sub (hta.kd_mul_left (diagCols β))
      rwa [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, sub_sub_sub_cancel_right] at this
    · rw [Matrix.map_mul, Matrix.map_mul, hp, ht1, cy]
      simp [P₀, fromBlocks_mul_fromRows, fromRows_mul]
    · rw [Matrix.map_mul, Matrix.map_mul, ht2, cy, Units.val_one, Matrix.mul_one]
      have h2 := h.unit_rel p
      rw [hp] at h2
      have h3 : (P₀.1)ᵀ * (dbl JB).map (piW t) * fromRows (1 : Matrix β β (Fv F v)) (1 : Matrix β β (Fv F v)) =
          (dbl JB).map (piW t) * fromRows (1 : Matrix β β (Fv F v)) (1 : Matrix β β (Fv F v)) := by
        rw [dbl, fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _), Matrix.mul_assoc]
        simp [P₀, fromBlocks_transpose, fromBlocks_mul_fromRows, Matrix.sub_mul]
      obtain ⟨U, hU⟩ := ((Matrix.isUnit_transpose _).2 P₀.isUnit).mul hG2.uB
      have h4 := congrArg (fun m => (U⁻¹).1 * (m * fromRows (1 : Matrix β β (Fv F v)) (1 : Matrix β β (Fv F v)))) h2
      rwa [← h3, ← hU, Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc (U⁻¹).1 U.1, U.inv_mul, Matrix.one_mul,
        Matrix.one_mul] at h4
  obtain ⟨l, hl, hli, φ₀, hφ₀, r, hr, hrr, hne⟩ := hA.diag F κ ψ v
  have hl0 : ∀ z : Matrix α β (AE F E), ∀ Φ ∈ schA F (κ ⊕ κ), l (dd.rho ψ (fromCols z z) Φ) = l Φ := fun z Φ hΦ => by
    rw [Darboux.rho, hdd]; exact hli _ _ Φ hΦ
  have hsie := hR l hl (fun z Φ hΦ => by
    rw [diagCols, transpose_fromRows, transpose_one, mul_fromCols, Matrix.mul_one]; exact hl0 z Φ hΦ) p tt hpt
  have hdet : At (evFin F v) (((GeneralLinearGroup.det tt : (AE F E)ˣ) : AE F E) - 1) := by
    rw [kd_at_iff, smul_sub, GeneralLinearGroup.val_det_apply]
    have e1 : (1 - sgl v 1 : AF F) • ((tt : Matrix β β (AE F E)) - 1) = 0 := hta _ (by rw [map_sub, map_one, ev_sgl, sub_self])
    let q := Ideal.Quotient.mk (Ideal.span {algebraMap (AF F) (AE F E) (sgl v 1)})
    have e2 : q.mapMatrix (tt : Matrix β β (AE F E)) = 1 := Matrix.ext fun a b => by
      have e3 := kd_at_iff.1 (kd_at_matrix.1 hta a b)
      rw [← map_one q.mapMatrix]
      exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨_, by rw [mul_comm, ← Algebra.smul_def]; exact e3⟩)
    have e4 : q ((tt : Matrix β β (AE F E)).det - 1) = 0 := by rw [map_sub, RingHom.map_det, e2, det_one, map_one q, sub_self]
    obtain ⟨a, ea⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 e4)
    rw [← smul_sub, ← ea, mul_comm, ← Algebra.smul_def]
    exact kd_at_iff.1 (at_sgl_smul 1 a)
  obtain ⟨i1, i2⟩ := h.idele (GeneralLinearGroup.det tt) (gdet g₀) hdet
    (by rw [GeneralLinearGroup.val_det_apply, RingHom.map_det, RingHom.mapMatrix_apply, ht1]; rfl)
    (by rw [GeneralLinearGroup.val_det_apply, RingHom.map_det, RingHom.mapMatrix_apply, ht2, Units.val_one, det_one])
  rw [i1, i2] at hsie
  have hs' : ((GlobalTheory.SplitWeil.nabs (Fv F v) (gdet g₀) ^ ((Fintype.card α : ℝ) / 2) : ℝ) : ℂ) =
      apow (gdet g₀) ((Fintype.card α : ℂ) / 2) := by
    rw [apow, Complex.ofReal_cpow (GlobalTheory.SplitWeil.Model.nabs_pos _).le]; push_cast; rfl
  rw [hs'] at hsie
  set s := (chrW χ t (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card α : ℂ) / 2)
  have xx : ∀ Φ, omd x⁻¹ (omd x Φ) = Φ := fun Φ => by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  have k1 : ∀ Φ ∈ schA F (κ ⊕ κ), l (omd x⁻¹ (omd gd Φ)) = s * l (omd x⁻¹ Φ) := fun Φ hΦ => by
    rw [← hsie _ (hsd.pres x⁻¹ Φ hΦ), ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      show x⁻¹ * gd = p * x⁻¹ by rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hxp, mul_inv_cancel_right]]
  have k2 : ∀ u : Matrix α β (AE F E), At (evFin F v) u → u.map (piW (t.comp σ)) = 0 → ∀ Φ ∈ schA F (κ ⊕ κ),
      l (omd x⁻¹ (dd.rho ψ (fromCols u 0) Φ)) = l (omd x⁻¹ Φ) := fun u hu h0 Φ hΦ => by
    have e : actB (cA σ) x (fromCols u u) = fromCols u 0 := by
      have a1 : ∀ u' : Matrix α β (AE F E), At (evFin F v) u' → At (evFin F v) (fromCols u u') := fun u' h' a ha => by
        ext i (k | k)
        · exact kd_at_matrix.1 hu i k a ha
        · exact kd_at_matrix.1 h' i k a ha
      refine h.extM (((a1 u hu).kd_mul_right _).kd_sub (a1 0 fun _ _ => smul_zero _)) ?_ ?_
      · rw [actB, Matrix.map_mul, transpose_map, hx, fromCols_map, fromCols_map, Matrix.map_zero _ (map_zero _)]
        simp [X₀, fromBlocks_transpose, fromCols_mul_fromBlocks]
      · rw [actB, Matrix.map_mul, fromCols_map, fromCols_map, h0, Matrix.map_zero _ (map_zero _), fromCols_zero, Matrix.zero_mul]
    have := hsd.impl x (fromCols u u) _ (hsd.pres x⁻¹ Φ hΦ)
    rw [e, ← Module.End.mul_apply (omd x) (omd x⁻¹), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    rw [← this, xx, hl0 u _ (hsd.pres x⁻¹ Φ hΦ)]
  have hφne : φ₀ ≠ 0 := fun e => hne (by
    rw [e, show boxFun (tens (evFin F v) (0 : (κ → Fv F v) → ℂ) r) (tens (evFin F v) 0 r) = 0 from
      funext fun _ => by simp [boxFun, tens], map_zero])
  have hbS := GlobalTheory.CompanionTheory.WeilOneMember.boxFun_mem hφ₀ hφ₀
  have hbne : boxFun φ₀ φ₀ ≠ 0 := fun e => by
    obtain ⟨y, hy⟩ := Function.ne_iff.1 hφne
    exact mul_ne_zero hy hy (congrFun e (Sum.elim y y))
  have rest := hA.rest F κ v r φ₀ hφ₀ hφne hr
  obtain ⟨φ₁, hφ₁, φ₂, hφ₂, hnz⟩ : ∃ φ₁ ∈ SB (κ → Fv F v), ∃ φ₂ ∈ SB (κ → Fv F v),
      l (omd x⁻¹ (boxFun (tens (evFin F v) φ₁ r) (tens (evFin F v) φ₂ r))) ≠ 0 := by
    by_contra hno
    push_neg at hno
    obtain ⟨c₂, hc₂⟩ := acts_scalar hA hψ h hG2 hι₂ hj₂ hsd x hxa X₀ hx
    have := hC _ (κ ⊕ κ) (psiV ψ v) hc h1 _ hbS hbne (l ∘ₗ omd x⁻¹ ∘ₗ tensL v (boxFun r r)) (fun w => by
      rw [schr_box]
      exact (congrArg (fun Φ => l (omd x⁻¹ Φ)) (tens_box _ _ r)).trans (hno _ (schr_mem hc _ hφ₀) _ (schr_mem hc _ hφ₀))) _
      (Submodule.smul_mem _ c₂ (hj₂ _ (rmL_mem X₀ (hι₂.bij.1 hbS))).1)
    refine hne ?_
    rw [← tens_box, ← xx (tens _ _ _), hc₂ _ hbS _ hrr]
    exact this
  let m : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ := l ∘ₗ omd x⁻¹ ∘ₗ boxL (tens (evFin F v) φ₂ r) ∘ₗ tensL v r
  have bm : ∀ φ ∈ SB (κ → Fv F v), boxFun (tens (evFin F v) φ r) (tens (evFin F v) φ₂ r) ∈ schA F (κ ⊕ κ) := fun φ hφ =>
    GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ _ (rest φ hφ).2 _ (rest φ₂ hφ₂).2
  obtain ⟨a, hm⟩ := GlobalTheory.CompanionTheory.WeilCoinv.exists_eq_mul_apply_zero _ (α × β) (psiV ψ v) hc h1 (m ∘ₗ j) fun y Φ hΦ => by
    obtain ⟨u, hu, hco, h0⟩ := exists_coord h hG (0, y)
    obtain ⟨e1, e2⟩ := hj Φ hΦ
    have e3 : j (schr (psiV ψ v) (0, y) Φ) = schr (psiV ψ v) (locW v (d.e u)) (j Φ) := by
      rw [← hj' _ (schr_mem hc _ e1), hι.Heisenberg₂ u _ e1, hco, e2]
    have e4 := hA.Heisenberg₂ F κ ψ v (d.e u) (hu.kd_map d.e.toLinearMap) (j Φ) r (rest _ e1)
    change l (omd x⁻¹ (boxFun (tens _ (j _) r) _)) = l (omd x⁻¹ (boxFun (tens _ (j Φ) r) _))
    rw [e3, ← e4, ← k2 u hu (h0 rfl) _ (bm _ e1), Darboux.rho, hdd, schr_box, map_zero]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Prod.fst_zero, Prod.snd_zero, neg_zero, schr_zero']
  have hm' : ∀ φ ∈ SB (κ → Fv F v), m φ = a * ι φ 0 := fun φ hφ => by
    rw [← hm _ (hι.bij.1 hφ), LinearMap.comp_apply m j, hj' φ hφ]
  have f1 := k1 _ (bm φ₁ hφ₁)
  rw [hbox g gd hgd _ (rest _ hφ₁).2 _ (rest _ hφ₂).2, hcA φ₁ hφ₁ r (rest _ hφ₁)] at f1
  have f2 := hj _ (rmL_mem g₀ (hι.bij.1 hφ₁))
  change m (c • _) = s * m φ₁ at f1
  rw [map_smul, hm' _ f2.1, f2.2, rmL_apply, show toM (0 : α × β → Fv F v) = 0 from rfl, Matrix.zero_mul,
    show ofM (0 : Matrix α β (Fv F v)) = 0 from rfl, ← hm' _ hφ₁, smul_eq_mul] at f1
  exact mul_right_cancel₀ hnz f1

end PositivityTheory.KCo
