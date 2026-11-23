import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsComplSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin

noncomputable section

open scoped TensorProduct NNReal Matrix Topology
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWInt.Model

open GlobalTheory.SWLit GlobalTheory.SWWeil

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n m : ℕ}
  {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}

open Classical in

def ind (w g : UA σ J₂) (𝓓 : Set (unipN σ J₂)) (y : UA σ J₂) : ℂ := if ∃ x ∈ 𝓓, y = w * (x : UA σ J₂) * g then 1 else 0

omit [NumberField E] in

theorem ind_apply (w g : UA σ J₂) (𝓓 : Set (unipN σ J₂)) :
    (fun x : unipN σ J₂ => ind w g 𝓓 (w * x * g)) = 𝓓.indicator fun _ => 1 := by
  funext x
  by_cases h : x ∈ 𝓓
  · rw [Set.indicator_of_mem h, ind, if_pos ⟨x, h, rfl⟩]
  · rw [Set.indicator_of_notMem h, ind, if_neg]
    rintro ⟨y, hy, e⟩
    exact h ((Subtype.ext (mul_left_cancel (mul_right_cancel e)) : x = y) ▸ hy)

omit [NumberField E] in

theorem exists_intM_eq_one {νN : Measure (unipN σ J₂)} (h : IsNormN σ νN) (w g : UA σ J₂) :
    ∃ f, IntConv νN w f g ∧ intM νN w f g = 1 := by
  obtain ⟨-, 𝓓, h1, h2⟩ := h
  refine ⟨ind w g 𝓓, ?_, ?_⟩
  · rw [IntConv, ind_apply]
    exact (integrableOn_const (by rw [h2]; exact ENNReal.one_ne_top) : IntegrableOn (fun _ => (1 : ℂ)) 𝓓 νN).integrable_indicator₀
      h1.nullMeasurableSet
  · rw [intM, ind_apply, integral_indicator₀ h1.nullMeasurableSet, setIntegral_const, Measure.real, h2,
      ENNReal.toReal_one, one_smul]

omit [NumberField E] in

theorem coefM_pole {νN : Measure (unipN σ J₂)} {w : UA σ J₂} {f : UA σ J₂ → ℂ} (hf : ∀ g, IntConv νN w f g) :
    HasIntCont νN w (fun s => s⁻¹ • f) ∧ (∀ g, coefM νN w (fun s => s⁻¹ • f) 0 (-1) g = intM νN w f g) ∧
      (∀ g, contM νN w (fun s => s⁻¹ • f) 0 g = 0) ∧ ∀ g, contM νN w (fun s => s⁻¹ • f) (-1) g = -intM νN w f g := by
  have hm : ∀ g s, MeromorphicAt (fun s : ℂ => s⁻¹ * intM νN w f g) s := fun g s =>
    (MeromorphicAt.id s).inv.mul (.const _ _)
  have he : ∀ g, (fun s : ℂ => intM νN w (s⁻¹ • f) g) = fun s => s⁻¹ * intM νN w f g := fun g =>
    funext fun s => intM_smul _ _ _
  have hx : ∀ g, Cont.IsMerExt (fun s : ℂ => s⁻¹ * intM νN w f g) Set.univ fun s => s⁻¹ * intM νN w f g := fun g =>
    Cont.isMerExt_self Cont.isRightDomain_univ fun s _ => hm g s
  refine ⟨⟨⟨0, fun s _ g => (hf g).smul _⟩, fun g => ?_⟩, fun g => ?_, fun g => ?_, fun g => ?_⟩
  · rw [he]; exact ⟨_, hx g⟩
  · rw [coefM, he]
    refine Cont.CoeffAt.laurent_eq (((hx g).isExtAt trivial).coeffAt_of_tendsto (k := 1) ?_)
    refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs => ?_)
    have : s ≠ 0 := hs
    simp only [sub_zero, pow_one]
    field_simp
  · rw [contM, he]
    refine Cont.ValueAt.cont_eq ⟨_, (hx g).isExtAt trivial, Polynomial.C (intM νN w f g) * Polynomial.X, by simp, ?_⟩
    refine tendsto_const_nhds.congr fun s => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, sub_zero, mul_comm, sub_self]
  · rw [contM, he]
    refine Cont.ValueAt.cont_eq (Cont.HolValueAt.valueAt ⟨_, (hx g).isExtAt trivial, ?_, by simp⟩)
    exact (analyticAt_id.inv (by simp)).mul analyticAt_const

omit [NumberField E] in

theorem exists_ratN (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E} {l : E} (hl : l ≠ 0)
    (hJ : ∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) (h₂ : J₂ = dblGram finSumFinEquiv J) {T : GL (Fin (n + n)) E}
    (h : IsWittBasis σ J l T) (c : ℕ) :
    ∃ u : ratN σ J₂, inBasis σ T ((u : unipN σ J₂) : UA σ J₂) = blk 1 (c • 1) 0 1 := by
  have hG := WittModel.gram_of_isWittBasis hσ hl hJ h
  rw [← h₂] at hG
  have hm : (blk 1 (c • 1) 0 1 : Matrix (Fin (n + n)) (Fin (n + n)) E) * blk 1 (-(c • 1)) 0 1 = 1 := by
    rw [WittModel.blk_mul, ← WittModel.blk_one]; simp
  let w₀ : GL (Fin (n + n)) E := ⟨_, _, hm, mul_eq_one_comm.1 hm⟩
  have mp : ∀ {S : Type} [CommRing S] (f : E →+* S),
      (blk 1 (c • 1) 0 1 : Matrix (Fin (n + n)) (Fin (n + n)) E).map f = blk 1 (c • 1) 0 1 := fun f => by
    have : (c • (1 : Matrix (Fin n) (Fin n) E)).map f = c • 1 := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, map_nsmul, Matrix.one_apply, apply_ite f, map_one, map_zero]
    simp only [blk, ← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.map_one _ (map_zero f) (map_one f), this,
      Matrix.map_zero _ (map_zero f)]
  have hw : w₀.1ᵀ * blk 0 1 (-1) 0 * w₀.1.map σ = blk 0 1 (-1) 0 := by
    have e : w₀.1ᵀ = blk 1 0 (c • 1) 1 := by
      simp only [w₀, blk, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose, Matrix.transpose_one,
        Matrix.transpose_smul, Matrix.transpose_zero]
    have e' : w₀.1.map σ = blk 1 (c • 1) 0 1 := mp (σ : E →+* E)
    rw [e, e', WittModel.blk_mul, WittModel.blk_mul]
    simp
  have hT : T.1ᵀ * J₂ * T.1.map σ = l • blk 0 1 (-1) 0 := by
    rw [← hG, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hl, one_smul]
  have i1 : (T⁻¹).1ᵀ * T.1ᵀ = 1 := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have i2 : T.1.map σ * (T⁻¹).1.map σ = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have key : (T * w₀ * T⁻¹).1ᵀ * J₂ * (T * w₀ * T⁻¹).1.map σ = J₂ := by
    calc _ = (T⁻¹).1ᵀ * (w₀.1ᵀ * (T.1ᵀ * J₂ * T.1.map σ) * w₀.1.map σ) * (T⁻¹).1.map σ := by
          simp only [Units.val_mul, Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = (T⁻¹).1ᵀ * (T.1ᵀ * J₂ * T.1.map σ) * (T⁻¹).1.map σ := by
          rw [hT, Matrix.mul_smul, Matrix.smul_mul, hw]
      _ = ((T⁻¹).1ᵀ * T.1ᵀ) * J₂ * (T.1.map σ * (T⁻¹).1.map σ) := by simp only [Matrix.mul_assoc]
      _ = J₂ := by rw [i1, i2, Matrix.one_mul, Matrix.mul_one]
  have hU : Matrix.GeneralLinearGroup.map (inclR (AF F)) (T * w₀ * T⁻¹) ∈ UG (cA σ) (incM F J₂) := by
    have := congrArg (fun X => incM F X) key
    simp only [incM, Matrix.map_mul, Matrix.transpose_map] at this
    refine Eq.trans ?_ this
    congr 1
  let u : UA σ J₂ := ⟨_, hU⟩
  have hu : inBasis σ T u = blk 1 (c • 1) 0 1 := by
    change incM F (T⁻¹).1 * incM F (T * w₀ * T⁻¹).1 * incM F T.1 = _
    rw [incM, incM, incM, ← Matrix.map_mul, ← Matrix.map_mul, ← Units.val_mul, ← Units.val_mul,
      show T⁻¹ * (T * w₀ * T⁻¹) * T = w₀ by group]
    exact mp _
  have hN : u ∈ unipN σ J₂ := by
    obtain ⟨Z, -, hZ⟩ := h
    have hT' : incM F T.1 = blk 1 (incM F Z) 1 (-incM F Z) := by
      simp only [hZ, incM, blk, ← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.map_neg _ (map_neg (inclR (F := F) (E := E) (AF F)))]
    have hc : ∀ a b c d x y : Matrix (Fin n) (Fin n) (AE F E), blk a b c d * blockColumnMatrix x y = blockColumnMatrix (a * x + b * y) (c * x + d * y) :=
      fun a b c d x y => by
        rw [blk, blockColumnMatrix, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_mul_fromRows, blockColumnMatrix]
    have e1 : blockColumnMatrix (1 : Matrix (Fin n) (Fin n) (AE F E)) 1 = incM F T.1 * blockColumnMatrix 1 0 := by rw [hT']; erw [hc]; simp
    have e2 : mat u * incM F T.1 = incM F T.1 * blk 1 (c • 1) 0 1 := by
      rw [← hu, inBasis, ← Matrix.mul_assoc, ← Matrix.mul_assoc, incM_mul_inv, Matrix.one_mul]
    rw [mem_unipN_iff, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero, e1]
    erw [← Matrix.mul_assoc, e2, Matrix.mul_assoc, hc]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero]
    rfl
  exact ⟨⟨⟨u, hN⟩, ⟨_, rfl⟩⟩, hu⟩

omit [NumberField E] in

theorem infinite_ratN (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E} {l : E} (hl : l ≠ 0)
    (hJ : ∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) (h₂ : J₂ = dblGram finSumFinEquiv J) {T : GL (Fin (n + n)) E}
    (h : IsWittBasis σ J l T) (hn : 1 ≤ n) : Infinite (ratN σ J₂) := by
  choose u hu using exists_ratN hσ hl hJ h₂ h
  refine Infinite.of_injective u fun a b e => ?_
  have h1 := (hu a).symm.trans ((congrArg (fun x : ratN σ J₂ => inBasis σ T ((x : unipN σ J₂) : UA σ J₂)) e).trans (hu b))
  have h2 := congrFun (congrFun h1 (finSumFinEquiv (.inl ⟨0, hn⟩))) (finSumFinEquiv (.inr ⟨0, hn⟩))
  simp only [blk, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂, Matrix.smul_apply,
    Matrix.one_apply_eq] at h2
  rw [nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one] at h2
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  haveI : Nontrivial (AE F E) := inferInstanceAs (Nontrivial (AF F ⊗[F] E))
  haveI : CharZero (AE F E) := charZero_of_injective_algebraMap (algebraMap F (AE F E)).injective
  exact_mod_cast h2

theorem not_intConv_one (hcm : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} {l : E} (hl : l ≠ 0)
    (hJ : ∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) (h₂ : J₂ = dblGram finSumFinEquiv J) {T : GL (Fin (n + n)) E}
    (h : IsWittBasis σ J l T) (hn : 1 ≤ n) {νN : Measure (unipN σ J₂)} (hν : IsNormN σ νN) (w g : UA σ J₂) :
    ¬ IntConv νN w (fun _ => 1) g := by
  obtain ⟨h0, 𝓓, h1, h2⟩ := hν
  haveI := infinite_ratN (GlobalTheory.SiegelSet.sigma_sigma hcm) hl hJ h₂ h hn
  obtain ⟨hTG, -, hSC, hT2⟩ := GlobalTheory.UnipMass.topUA σ J₂
  haveI : BorelSpace (UA σ J₂) := ⟨rfl⟩
  haveI : Countable (ratN σ J₂) := GlobalTheory.UnipMass.countable_ratU' σ J₂ (unipN σ J₂)
  haveI : MeasurableConstSMul (ratN σ J₂) (unipN σ J₂) :=
    ⟨fun γ => (continuous_const.mul continuous_id : Continuous fun x : unipN σ J₂ => (γ : unipN σ J₂) * x).measurable⟩
  haveI : SMulInvariantMeasure (ratN σ J₂) (unipN σ J₂) νN := ⟨fun γ A _ => measure_preimage_mul νN (γ : unipN σ J₂) A⟩
  intro hc
  have h3 := h1.measure_eq_tsum Set.univ
  simp only [Set.smul_set_univ, Set.univ_inter, h2, ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero] at h3
  rcases integrable_const_iff.1 hc with h4 | h4
  · exact one_ne_zero h4
  · exact measure_ne_top νN _ h3

omit [NumberField E] in

theorem intM_rank_zero {J₂ : Matrix (Fin (0 + 0)) (Fin (0 + 0)) E} {νN : Measure (unipN σ J₂)} (hν : IsNormN σ νN)
    (w g : UA σ J₂) (f : UA σ J₂ → ℂ) : intM νN w f g = f g := by
  haveI : Subsingleton (UA σ J₂) := ⟨fun a b => Subtype.ext (Units.ext (Matrix.ext fun i => i.elim0))⟩
  obtain ⟨-, 𝓓, -, h2⟩ := hν
  have hu : νN Set.univ = 1 := by
    rcases Set.eq_empty_or_nonempty 𝓓 with e | e
    · rw [e, measure_empty] at h2; exact absurd h2 zero_ne_one
    · rw [← h2, Subsingleton.eq_univ_of_nonempty e]
  rw [intM, show (fun x : unipN σ J₂ => f (w * x * g)) = fun _ => f g from funext fun _ => congrArg f (Subsingleton.elim _ _),
    integral_const, Measure.real, hu, ENNReal.toReal_one, one_smul]

omit [NumberField E] in

theorem secSpace_bot_ne_bot {JV : Matrix (Fin m) (Fin m) E} {κ : Type} [Fintype κ]
    (om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ)) : secSpace om ⊥ ≠ ⊥ := by
  obtain ⟨φ, h, h0⟩ := GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F κ
  refine (Submodule.ne_bot_iff _).2 ⟨_, mem_secSpace.2 ⟨φ, h, (kFin_iff om ⊥ φ).2 ⟨ℂ ∙ φ, inferInstance, fun k hk => ?_⟩, rfl⟩,
    fun e => h0 ?_⟩
  · rw [Subgroup.mem_bot.1 hk, Prod.mk_one_one, map_one]; exact Submodule.mem_span_singleton_self φ
  · have := congrFun e 1
    rwa [Prod.mk_one_one, map_one] at this

theorem exists_case : ∃ (F E : Type) (_ : Field F) (_ : NumberField F) (_ : Field E) (_ : NumberField E) (_ : Algebra F E)
    (σ : E →ₐ[F] E) (J₂ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) E) (T : GL (Fin (2 + 2)) E) (w : UA σ J₂)
    (νN : Measure (unipN σ J₂)), ComplMet σ 1 1 False ∧ IsWeylElt σ T w ∧ IsNormN σ νN ∧
    w ∉ siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype ∧
    (∃ f, IntConv νN w f 1 ∧ intM νN w f 1 = 1) ∧ ¬ IntConv νN w (fun _ => 1) 1 := by
  obtain ⟨F, E, _, _, _, _, _, σ, h⟩ := exists_complMet
  obtain ⟨hcm, -, ψ, -, l, JV, J, J₂, hl, -, -, hJ, h₂, T, hT, χ, -, -, K, -, -, ⟨w, hw⟩, ⟨ν, hν⟩, -⟩ := h 1 1
  exact ⟨F, E, _, _, _, _, _, σ, J₂, T, w, ν, h 1 1, hw, hν, hw.not_mem_siegelOf hT (by norm_num), exists_intM_eq_one hν w 1,
    not_intConv_one hcm hl hJ h₂ hT (by norm_num) hν w 1⟩

end GlobalTheory.SWInt.Model

end
