import Development.WeilBound.ThetaLifts.LatticeBasics.MemLam
import Development.WeilBound.ThetaLifts.LatticeBasics.BadStmt
import Development.WeilBound.ThetaLifts.LatticeBasics.LocMeas
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.PfDict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenAddSubgroup

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.SplitFlip PositivityTheory.KCo PositivityTheory.ThK.SplitDict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace Bmp

theorem near_units {A : Type} [Monoid A] [TopologicalSpace A] {U : Set Aˣ} (hU : U ∈ 𝓝 (1 : Aˣ)) :
    ∀ᶠ p in 𝓝 ((1, 1) : A × A), ∀ g : Aˣ, g.1 = p.1 → (g⁻¹).1 = p.2 → g ∈ U := by
  rw [Units.isInducing_embedProduct.nhds_eq_comap] at hU
  obtain ⟨V, hV, h⟩ := hU
  have c : Continuous fun p : A × A => (p.1, MulOpposite.op p.2) := continuous_fst.prodMk (MulOpposite.continuous_op.comp continuous_snd)
  filter_upwards [c.continuousAt.preimage_mem_nhds (x := (1, 1)) hV] with p hp g h1 h2
  exact h (show (g.1, MulOpposite.op (g⁻¹).1) ∈ V by rw [h1, h2]; exact hp)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {n d : ℕ}

theorem near_UA (h : PositivityTheory.KCo.IsSec σ t sec) {X : Spc F E n} (hu : IsUnit ((incM F X.J).map (piW t))) {U : Set (UA σ X.J)} (hU : U ∈ 𝓝 1) :
    ∀ᶠ p in 𝓝 ((1, 1) : Matrix (Fin n) (Fin n) (Fv F v) × Matrix (Fin n) (Fin n) (Fv F v)), ∀ g ∈ UAt σ X (evFin F v),
      (mat g).map (piW t) = p.1 → (mat g⁻¹).map (piW t) = p.2 → g ∈ U := by
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  obtain ⟨U', h1, h2⟩ := (mem_nhds_subtype _ _ _).1 hU
  obtain ⟨A, hA⟩ := hu
  have cs : Continuous (sgl v : Fv F v → AF F) := (continuous_const.prodMk (continuous_singleFin v) : Continuous fun a => ((0 : Ainf F), singleFin v a))
  let S : Matrix (Fin n) (Fin n) (Fv F v) → Matrix (Fin n) (Fin n) (Fv F v) → Matrix (Fin n) (Fin n) (AE F E) := fun p q =>
    1 + of fun i j => sgl v ((p - 1) i j) • sec (1, 0) + sgl v (((A⁻¹).1 * qᵀ * A.1 - 1) i j) • sec (0, 1)
  have cS : Continuous fun p : _ × _ => S p.1 p.2 := continuous_const.add (continuous_matrix fun i j =>
    ((cs.comp ((continuous_fst.sub continuous_const).matrix_elem i j)).smul continuous_const).add
    ((cs.comp ((((continuous_const.matrix_mul continuous_snd.matrix_transpose).matrix_mul continuous_const).sub
      continuous_const).matrix_elem i j)).smul continuous_const))
  have S1 : S 1 1 = 1 := by ext i j; simp [S]
  have eS : ∀ g : UA σ X.J, At (evFin F v) (mat g - 1) → mat g = S ((mat g).map (piW t)) ((mat g⁻¹).map (piW t)) := fun g hg => by
    refine h.extM ?_ ?_ ?_
    · rw [← sub_sub]
      exact hg.kd_sub (kd_at_matrix.2 fun i j => (at_sgl_smul _ _).kd_add (at_sgl_smul _ _))
    · ext i j
      simp [S, (h.smul _ _).1, h.fst, ev_sgl, one_apply, apply_ite (piW t)]
    · have e1 := h.unit_rel g
      have e2 : ((mat g⁻¹).map (piW t))ᵀ * ((mat g).map (piW t))ᵀ = 1 := by
        rw [← transpose_mul, ← Matrix.map_mul, show mat g * mat g⁻¹ = 1 from g.1.mul_inv, Matrix.map_one _ (map_zero _) (map_one _),
          transpose_one]
      have e3 : (mat g).map (piW (t.comp σ)) = (A⁻¹).1 * ((mat g⁻¹).map (piW t))ᵀ * A.1 := by
        rw [← hA] at e1
        conv_rhs => rw [← e1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ (_)ᵀ]
        erw [e2]
        rw [Matrix.mul_one, Units.inv_mul, Matrix.one_mul]
        rfl
      rw [e3]
      ext i j
      simp [S, (h.smul _ _).2, h.snd, ev_sgl, one_apply, apply_ite (piW (t.comp σ))]
  have c2 := cS.prodMk (cS.comp continuous_swap)
  filter_upwards [(c2.tendsto' (1, 1) (1, 1) (by simp [S1])).eventually (near_units h1)] with p hp g hg e1 e2
  have hg' : At (evFin F v) (mat g⁻¹ - 1) := by
    rw [show mat g⁻¹ - 1 = -mat g⁻¹ * (mat g - 1) by
      rw [mul_sub, neg_mul, show mat g⁻¹ * mat g = 1 from g.1.inv_mul]; simp [neg_add_eq_sub]]
    exact At.kd_mul_left hg _
  refine h2 (hp g.1 ((eS g hg).trans (by rw [e1, e2])) ((eS g⁻¹ hg').trans (by rw [inv_inv, e1, e2]; rfl)))

theorem exists_level {P : Matrix (Fin n) (Fin n) (Fv F v) × Matrix (Fin n) (Fin n) (Fv F v) → Prop} (hP : ∀ᶠ p in 𝓝 (1, 1), P p) :
    ∃ a : v.adicCompletionIntegers F, a ≠ 0 ∧ a ∈ IsLocalRing.maximalIdeal _ ∧
      ∀ p q, p - 1 ∈ lam (Fv F v) a n n → q - 1 ∈ lam (Fv F v) a n n → P (p, q) := by
  have := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have : CompactSpace (Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F)) := inferInstanceAs (CompactSpace (_ → _ → _))
  obtain ⟨w, w1, w0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (IsDiscreteValuationRing.not_a_field (v.adicCompletionIntegers F))
  have cm : Continuous fun α : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F) => α.map (algebraMap _ (Fv F v)) :=
    continuous_id.matrix_map continuous_subtype_val
  have h1 : ∀ᶠ a : Fv F v in 𝓝 0, ∀ y ∈ (Set.univ : Set (Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F) × Matrix _ _ _)),
      P (a • y.1.map (algebraMap _ _) + 1, a • y.2.map (algebraMap _ _) + 1) :=
    isCompact_univ.eventually_forall_of_forall_eventually fun y _ =>
      ((((continuous_fst.smul (cm.comp (continuous_fst.comp continuous_snd))).add continuous_const).prodMk
        ((continuous_fst.smul (cm.comp (continuous_snd.comp continuous_snd))).add continuous_const)).tendsto' (0, y) (1, 1)
        (by simp)).eventually hP
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((Valued.tendsto_zero_pow_of_v_lt_one (x := (w : Fv F v)) ((Valuation.mem_maximalIdeal_iff _ _).1 w1)).eventually h1)
  refine ⟨w ^ (N + 1), pow_ne_zero _ w0, Ideal.pow_mem_of_mem _ w1 _ N.succ_pos, fun p q ⟨α, hα⟩ ⟨β, hβ⟩ => ?_⟩
  exact (eq_add_of_sub_eq hα.symm) ▸ (eq_add_of_sub_eq hβ.symm) ▸ hN (N + 1) N.le_succ (α, β) trivial

theorem ind_mem {a : v.adicCompletionIntegers F} (ha : a ≠ 0) (Y₀ : Matrix (Fin n) (Fin d) (Fv F v)) :
    (fun Y => Set.indicator (lam (Fv F v) a n d : Set _) (fun _ => (1 : ℂ)) (Y - Y₀)) ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)) := by
  have := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have : CompactSpace (Matrix (Fin n) (Fin d) (v.adicCompletionIntegers F)) := inferInstanceAs (CompactSpace (_ → _ → _))
  have ha' : (a : Fv F v) ≠ 0 := fun h => ha (Subtype.ext h)
  have op : IsOpen ((lam (Fv F v) a n d).toAddSubgroup : Set (Matrix (Fin n) (Fin d) (Fv F v))) := by
    have o : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
    have e : ∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin d) (Fv F v)), ∀ i j, (a : Fv F v)⁻¹ * Y i j ∈ v.adicCompletionIntegers F :=
      eventually_all.2 fun i => eventually_all.2 fun j => by
        have c : Continuous fun Y : Matrix (Fin n) (Fin d) (Fv F v) => (a : Fv F v)⁻¹ * Y i j :=
          continuous_const.mul (continuous_id.matrix_elem i j)
        exact (c.tendsto' 0 0 (by simp)).eventually (o.mem_nhds (zero_mem _))
    refine AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (e.mono fun Y hY => mem_lam.2 ⟨fun i j => ⟨_, hY i j⟩, ?_⟩)
    exact Matrix.ext fun i j => mul_inv_cancel_left₀ ha' _
  have hf := GlobalTheory.WeilM.HaarUniq.indicator_mem ⟨_, op⟩ (isCompact_range
    (f := fun α : Matrix (Fin n) (Fin d) (v.adicCompletionIntegers F) => (a : Fv F v) • α.map (algebraMap _ (Fv F v)))
    (continuous_matrix fun i j => continuous_const.mul (continuous_subtype_val.comp (continuous_id.matrix_elem i j))))
  exact ⟨hf.1.comp_continuous (Homeomorph.subRight Y₀).continuous, hf.2.comp_homeomorph (Homeomorph.subRight Y₀)⟩

end Bmp

open Bmp in
theorem bump : Bump := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp hnd v hv
  obtain ⟨t⟩ : Nonempty (E →ₐ[F] Fv F v) := ⟨B.τ ⟨v, hv⟩⟩
  obtain ⟨⟨ι, hι⟩, -, -, k⟩ := dictX F E σ n d B X W M om χX χW hp.base ⟨_, _, hp.herm⟩ ⟨_, _, hp.skew⟩ hp.weil v t
  obtain ⟨⟨sec, h⟩, hsm⟩ := section_statement F E σ hp.base.cm v t
  have hG := grams h hp.herm hp.skew
  have n1 := near_UA h hG.uA ((Euler.isOpen_int (σ := σ) hp.herm.lat v).mem_nhds (one_mem _))
  have hv1 : ∀ᶠ y in 𝓝 (1 : Fv F v), ValuativeRel.valuation (Fv F v) y = 1 := by
    simpa [Filter.Eventually] using (ValuativeRel.valuation (Fv F v)).locally_const (x := 1) (by simp)
  have n2 := near_units (A := Matrix (Fin n) (Fin n) (Fv F v))
    (U := {g | chrW χW t (gdet g) = 1 ∧ ValuativeRel.valuation (Fv F v) (gdet g : Fv F v) = 1})
    (Eventually.and ((GeneralLinearGroup.continuous_det.tendsto' 1 1 (map_one _)).eventually
      ((hsm χW hp.hW).2.mem_nhds (one_mem _)))
      (((Units.continuous_val.comp GeneralLinearGroup.continuous_det).tendsto' 1 1 (by simp)).eventually hv1))
  obtain ⟨a, a0, a1, ha⟩ := exists_level (((continuous_fst.matrix_transpose.prodMk continuous_snd.matrix_transpose).tendsto'
    (1, 1) (1, 1) (by simp)).eventually (n1.and n2))
  let y : Matrix (Fin n) (Fin d) (v.adicCompletionIntegers F) := (1 : Matrix (Fin d) (Fin d) _).submatrix (Fin.castLE hnd) id
  have hy : y * yᵀ = 1 := by
    rw [transpose_submatrix, transpose_one, ← submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.one_mul,
      submatrix_one _ (Fin.castLE_injective hnd)]
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀, Y₀ = y.map (algebraMap _ (Fv F v)) := ⟨_, rfl⟩
  obtain ⟨φ, hφ, e⟩ := hι.bij.2.2 (ind_mem a0 Y₀)
  have mult : ∀ u, At (evFin F v) u → u.map (piW (t.comp σ)) = 0 → ∀ c : ℂ, (∀ Y, Y - Y₀ ∈ lam (Fv F v) a n d →
      psiV B.ψ v (trace (Yᵀ * -u.map (piW t))) = c) → Acts (evFin F v) (M.co.rho B.ψ u) φ (c • φ) := fun u hu h0 c hc => by
    have ac := adjoint_statement.Heisenberg₂ F _ B.ψ v _ (hu.kd_map M.co.e.toLinearMap) φ
    have mem := schr_mem ((adjoint_statement.psi F _ hp.base.std).2 v).1 (locW v (M.co.e.toLinearMap u)) hφ
    rw [← hι.bij.2.1 mem ((SB _).smul_mem c hφ) (funext fun Y => ?_)]
    · exact ac
    obtain ⟨x, hx, hcx, -⟩ := exists_coord h hG (ofM Y, 0)
    have := hι.mult u hu h0 φ hφ _ mem ac x hx (coord_snd.1 (congrArg Prod.snd hcx))
    rw [co_eq h, symp_eq h hG hx, hcx, dotProduct_zero, sub_zero, toM_ofM] at this
    rw [this, map_smul, Pi.smul_apply, smul_eq_mul, e]
    by_cases hY : Y - Y₀ ∈ lam (Fv F v) a n d
    · rw [← hc Y hY, ← dot_ofM]; rfl
    · simp [Set.indicator_of_notMem hY]
  refine ⟨φ, hφ, fun h0 => ?_, fun g hg => ?_⟩
  · have := congrFun e Y₀
    simp [h0] at this
  let g₀ := GeneralLinearGroup.map (piW t) g.1
  rcases dich (O := v.adicCompletionIntegers F) (psiV B.ψ v) (fun x => ⟨fun H => ⟨⟨x, (hp.base.psiP v hv x).1 fun z hz => H ⟨z, hz⟩⟩, rfl⟩,
    fun ⟨o, ho⟩ z => (hp.base.psiP v hv x).2 (ho ▸ o.2) z z.2⟩) a0 a1 y _ hy (invT g₀)⁻¹ with ⟨h1, h2⟩ | ⟨l, h1, h2⟩
  · obtain ⟨b1, b2⟩ := ha _ _ h1 h2
    obtain ⟨b2, b3⟩ := b2 g₀ rfl rfl
    obtain ⟨φ₁, m1, ac, e1⟩ := (k ι hι).1 g hg g₀ rfl φ hφ
    have key : ∀ Y, g₀.1ᵀ * Y - Y₀ ∈ lam (Fv F v) a n d ↔ Y - Y₀ ∈ lam (Fv F v) a n d := fun Y => by
      refine ⟨fun H => ?_, fun H => hY₀ ▸ keep h1 y (hY₀ ▸ H)⟩
      have := keep h2 y (hY₀ ▸ H)
      rwa [show g₀.1ᵀ = ((invT g₀)⁻¹).1 from rfl, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, ← hY₀] at this
    have e2 : ι φ₁ = ι φ := e1.trans (funext fun Y => by
      clear b1 ha k n1 n2 mult
      rw [omB, b2, apow_of_valuation_eq_one b3, show gdet (1 : GL (Fin d) (Fv F v)) = 1 from map_one _, map_one, apow_one,
        Units.val_one, Units.val_one, Matrix.mul_one, one_mul, one_mul, one_mul, one_mul, e]
      by_cases hY : Y - Y₀ ∈ lam (Fv F v) a n d
      · exact (Set.indicator_of_mem ((key Y).2 hY) _).trans (Set.indicator_of_mem hY fun _ => (1 : ℂ)).symm
      · exact (Set.indicator_of_notMem (mt (key Y).1 hY) _).trans (Set.indicator_of_notMem hY fun _ => (1 : ℂ)).symm)
    rw [hι.bij.2.1 m1 hφ e2] at ac
    exact Or.inl ⟨b1 g hg rfl rfl, ac⟩
  · rw [← hY₀] at h2
    let u₀ : Matrix (Fin n) (Fin d) (Fv F v) := of fun i j => -l (single i j 1)
    have el : ∀ Y, trace (Yᵀ * -u₀) = l Y := fun Y => by
      conv_rhs => rw [matrix_eq_sum_single Y]
      simp only [← dot_ofM, dotProduct, ofM, Fintype.sum_prod_type, map_sum, u₀, Matrix.neg_apply, of_apply, neg_neg]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [← smul_eq_mul, ← map_smul]; simp
    refine Or.inr ⟨secM sec u₀ 0, psiV B.ψ v (l Y₀), psiV B.ψ v (l (g₀.1ᵀ * Y₀)), h.atM _ _, fun H => h2 ?_,
      mult _ (h.atM _ _) (h.sndM _ _) _ fun Y hY => ?_,
      mult _ ((h.atM _ _).kd_mul_left _) (by rw [Matrix.map_mul, h.sndM, Matrix.mul_zero]) _ fun Y hY => ?_⟩
    · refine mul_right_cancel₀ ((psiV B.ψ v).val_isUnit (l Y₀)).ne_zero ?_
      rw [← AddChar.map_add_eq_mul, ← map_add, sub_add_cancel, one_mul, H]
      rfl
    · rw [h.fstM, el, ← sub_add_cancel Y Y₀, map_add, AddChar.map_add_eq_mul, (h1 _ hY).1, one_mul]
    · rw [Matrix.map_mul, h.fstM, ← Matrix.mul_neg, ← Matrix.mul_assoc, ← transpose_transpose (Yᵀ * _), transpose_mul,
        transpose_transpose, el, ← sub_add_cancel Y Y₀, Matrix.mul_add, map_add, AddChar.map_add_eq_mul]
      exact (congrArg (· * _) (h1 _ hY).2).trans (one_mul _)

end GlobalTheory.ThK.Dbl

end
