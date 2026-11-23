import Development.WeilBound.ThetaLifts.LatticeBasics.LocUnr
import Development.WeilBound.ThetaLifts.LatticeBasics.LocUnrSplitA
import Development.WeilBound.ThetaLifts.LatticeBasics.LocUnrSplitL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormUniformiserEqInvAbsNorm

noncomputable section

namespace GlobalTheory.ThK.Dbl.Split

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open PositivityTheory.ThK PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locpair PositivityTheory.ThKH.Locrep
open GlobalTheory.Doubling (absE)
open GlobalTheory.SplitFlip (invT)
open Matrix (fromBlocks fromRows GeneralLinearGroup)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {v : Pl F} {Y : Spc F E n}

open ValuativeRel in
theorem val_equiv (v : Pl F) : (valuation (Fv F v)).IsEquiv (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))) :=
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  isEquiv _ _

theorem norm_unif (v : Pl F) : ‖(unifAt v : Fv F v)‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  simpa using congrArg NNReal.toReal (GlobalTheory.norm_uniformiser_eq_inv_absNorm F v _ (GlobalTheory.ChrWUnif.valued_unifAt v))

open ValuativeRel in
theorem lf (v : Pl F) : GlobalTheory.CompanionTheory.QL.LF (v.adicCompletionIntegers F).toSubring (unifAt v : Fv F v)
    (NormedField.toAbsoluteValue (Fv F v)) (Ideal.absNorm v.asIdeal) := by
  have he := val_equiv v
  have hu : valuation (Fv F v) (unifAt v : Fv F v) = uniformizer _ := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  have hO : ∀ y, y ∈ (v.adicCompletionIntegers F).toSubring ↔ valuation (Fv F v) y ≤ 1 := fun y => he.le_one_iff_le_one.symm
  refine ⟨Subring.ext hO, Units.ne_zero _, fun x => ?_, (GlobalTheory.LFun.SatBoundGL.resCard_completion v).symm, fun x hx => ?_, norm_unif v⟩
  · rw [← le_uniformizer_iff, ← hu]
    refine ⟨fun h => ⟨x / unifAt v, (hO _).2 ?_, (mul_div_cancel₀ _ (Units.ne_zero _)).symm⟩, ?_⟩
    · rw [map_div₀]; exact div_le_one_of_le₀ h zero_le'
    · rintro ⟨o, ho, rfl⟩; rw [map_mul]; exact mul_le_of_le_one_right' ((hO _).1 ho)
  · change ‖x‖ = 1
    rw [FinitePlace.norm_def, he.eq_one_iff_eq_one.1 hx]; simp

def chS (χ : Chr F E) (τ : E →ₐ[F] Fv F v) (s : ℂ) : (Fv F v)ˣ →* ℂ where
  toFun a := chrW χ τ a * ((‖a.1‖ : ℝ) : ℂ) ^ s
  map_one' := by simp
  map_mul' a b := by
    rw [map_mul, Units.val_mul, Units.val_mul, norm_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]; ring

theorem chS_apply (χ : Chr F E) (τ : E →ₐ[F] Fv F v) (s : ℂ) (a : (Fv F v)ˣ) :
    chS χ τ s a = chrW χ τ a * ((‖a.1‖ : ℝ) : ℂ) ^ s := rfl

theorem chS_unit {χ : Chr F E} {τ : E →ₐ[F] Fv F v} (h : UnrAt χ (splitPrime τ)) (s : ℂ) (u : (Fv F v)ˣ)
    (hu : NormedField.toAbsoluteValue (Fv F v) u = 1) : chS χ τ s u = 1 := by
  have : chrW χ τ u = 1 := h _ ((SplitTie.valued_complMap τ _ _).trans ((val_equiv v).eq_one_iff_eq_one.1
    (((GlobalTheory.CompanionTheory.QL.NormalisedValue.main (lf v)).2.2.2.2.2.2 _).1 hu)))
  change _ * ((‖u.1‖ : ℝ) : ℂ) ^ s = 1
  rw [this, show ‖u.1‖ = 1 from hu]; simp

theorem norm_unif_cpow (s : ℂ) : ((‖(unifAt v : Fv F v)‖ : ℝ) : ℂ) ^ s = npow v (-s) := by
  rw [norm_unif, Complex.ofReal_inv, Complex.ofReal_natCast, npow, Complex.cpow_neg,
    Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm)]

theorem chS_unif {χ : Chr F E} {τ : E →ₐ[F] Fv F v} (h : UnrAt χ (splitPrime τ)) (s : ℂ) :
    chS χ τ s (unifAt v) = val χ (splitPrime τ) * npow v (-s) := by
  rw [← GlobalTheory.ChrWUnif.chrW_unifAt F E χ v τ h, ← norm_unif_cpow]; rfl

theorem npow_nat (s : ℂ) (i : ℕ) : npow v (-s) * (Ideal.absNorm v.asIdeal : ℂ) ^ i = npow v (-(s - i)) := by
  rw [neg_sub', sub_neg_eq_add, LFun.npow_add, npow, npow, Complex.cpow_natCast]

theorem npow_lt {s : ℂ} {i : ℕ} (h : i < s.re) : ‖npow v (-s)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ i < 1 := by
  rw [← Complex.norm_natCast, ← norm_pow, ← norm_mul, npow_nat, norm_npow]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast one_lt_absNorm v) (by simpa using h)

section Alg

variable {k : Type} [Field k]

def bd (x y : GL (Fin n) k) : GL (Fin n ⊕ Fin n) k :=
  ⟨fromBlocks x.1 0 0 y.1, fromBlocks (x⁻¹).1 0 0 (y⁻¹).1, by simp [Matrix.fromBlocks_multiply], by simp [Matrix.fromBlocks_multiply]⟩

theorem bd_val (x y : GL (Fin n) k) : (bd x y).1 = fromBlocks x.1 0 0 y.1 := rfl

theorem bd_inv (x y : GL (Fin n) k) : ((bd x y)⁻¹).1 = fromBlocks (x⁻¹).1 0 0 (y⁻¹).1 := rfl

theorem bd_sub (x : GL (Fin n) k) (N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) {i j : Fin n → Fin n ⊕ Fin n}
    (hi : i ∈ ({.inl, .inr} : Set _)) (hj : j ∈ ({.inl, .inr} : Set _)) :
    (x⁻¹).1 * (N - 1).submatrix i j * x.1 = (((bd x x)⁻¹).1 * N * (bd x x).1 - 1).submatrix i j := by
  rw [show ((bd x x)⁻¹).1 * N * (bd x x).1 - 1 = ((bd x x)⁻¹).1 * (N - 1) * (bd x x).1 by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul]]
  generalize N - 1 = N
  rw [← Matrix.fromBlocks_toBlocks N]
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
    simp only [bd_val, bd_inv, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] <;> rfl

end Alg

theorem dual_conj {β : Type} [Fintype β] [DecidableEq β] {J a a' ε : GL β (Fv F v)} (h : a.1ᵀ * J.1 * a'.1 = ε.1) (x : GL β (Fv F v)) :
    (a'⁻¹).1 * (dual J (a * x * a⁻¹)).1 * a'.1 = (ε⁻¹).1 * (x⁻¹).1ᵀ * ε.1 := by
  have : ε = (invT a)⁻¹ * J * a' := Units.ext h.symm
  rw [← dual_val, ← Units.val_mul, ← Units.val_mul, this]
  congr 1
  simp only [dual, MonoidHom.comp_apply, map_mul invT, map_inv invT, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

end GlobalTheory.ThK.Dbl.Split

namespace GlobalTheory.ThK.Dbl

open Split
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open PositivityTheory.ThK PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locpair
open Matrix (fromBlocks fromRows GeneralLinearGroup)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option hygiene false in
local notation "𝟙" => (1 : Matrix (Fin n) (Fin n) (Fv F v))

theorem locUnrSplit : LocUnrSplit := by
  rintro F E _ _ _ _ _ σ B n Y r s hB hY χ - hr K e hK he v ⟨τ⟩ hu μ hμ hμ1 z f hz hf
  have hσ := hB.cm
  obtain ⟨J, b, b', h1, h2, hb, hb', hg⟩ := frames τ hσ hY
  have g1 : (dbl (incM F Y.J)).map (piW τ) = (bd J (-J)).1 := by
    simp [dbl, bd_val, Matrix.fromBlocks_map, Matrix.map_neg, h1]
  have g2 : (dbl (incM F Y.J)).map (piW (τ.comp σ)) = (bd J (-J)).1ᵀ := by
    simp [dbl, bd_val, Matrix.fromBlocks_map, Matrix.map_neg, h2, Matrix.fromBlocks_transpose]
  have gg : (bd b b).1ᵀ * (bd J (-J)).1 * (bd b' b').1 = (bd 1 (-1 : GL (Fin n) (Fv F v))).1 := by
    simp [bd_val, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, hg]
  let Λ : GL (Fin n) (Fv F v) →* UA σ Y.J := liftS hσ τ h1 h2
  let Λ₂ : GL (Fin n ⊕ Fin n) (Fv F v) →* G2 σ Y := liftS hσ τ g1 g2
  have a1 : ∀ x, (mat (Λ x)).map (piW τ) = x.1 := fun x => up_fst hσ τ x.1 (dual J x).1
  have a2 : ∀ x, (mat (Λ x)).map (piW (τ.comp σ)) = (dual J x).1 := fun x => up_snd hσ τ x.1 (dual J x).1
  have a3 : ∀ x, (mat (Λ x)).map (aw E v) = 1 := fun x => up_aw hσ τ x.1 (dual J x).1
  have l1 : ∀ x, (mat2 (Λ₂ x)).map (piW τ) = x.1 := fun x => up_fst hσ τ x.1 (dual (bd J (-J)) x).1
  have l2 : ∀ x, (mat2 (Λ₂ x)).map (piW (τ.comp σ)) = (dual (bd J (-J)) x).1 := fun x => up_snd hσ τ x.1 (dual (bd J (-J)) x).1
  have l3 : ∀ x, (mat2 (Λ₂ x)).map (aw E v) = 1 := fun x => up_aw hσ τ x.1 (dual (bd J (-J)) x).1
  have l4 : ∀ x, At (evFin F v) (mat2 (Λ₂ x) - 1) := fun x => up_at hσ τ x.1 (dual (bd J (-J)) x).1
  have one : ∀ {ι R : Type} [DecidableEq ι] [CommRing R] (φ : AE F E →+* R), (1 : Matrix ι ι _).map φ = 1 :=
    fun φ => Matrix.map_one _ (map_zero _) (map_one _)
  have zero : ∀ {R : Type} [CommRing R] (φ : AE F E →+* R), (0 : Matrix (Fin n) (Fin n) _).map φ = 0 :=
    fun φ => Matrix.map_zero _ (map_zero _)
  have emb : ∀ x, e (Λ x, 1) = Λ₂ (bd x 1) := fun x => Subtype.ext (Units.ext ((he _ _).trans (extS hσ τ ?_ ?_ ?_)))
  rotate_left
  · refine Eq.trans ?_ (l1 _).symm
    rw [Matrix.fromBlocks_map, zero, a1, show (mat 1).map (piW τ) = 1 from one _]
    rfl
  · refine Eq.trans ?_ (l2 _).symm
    rw [Matrix.fromBlocks_map, zero, a2,
      show (mat 1).map (piW (τ.comp σ)) = 1 from one _, dual_val, dual_val, bd_inv, bd_inv, bd_val]
    simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, inv_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one, Units.inv_mul]
  · refine Eq.trans ?_ (l3 _).symm
    rw [Matrix.fromBlocks_map, zero, a3, show (mat 1).map (aw E v) = 1 from one _,
      Matrix.fromBlocks_one]
  have o : ∀ {ι : Type} [DecidableEq ι] (i j : ι), (1 : Matrix ι ι (Fv F v)) i j ∈ v.adicCompletionIntegers F := fun i j => by
    rw [Matrix.one_apply]; split_ifs; exacts [one_mem _, zero_mem _]
  have key : ∀ x : GL (Fin n ⊕ Fin n) (Fv F v), (∀ i j, x.1 i j ∈ v.adicCompletionIntegers F) →
      (∀ i j, (x⁻¹).1 i j ∈ v.adicCompletionIntegers F) → At (evFin F v) (mat2 (Λ₂ (bd b b * x * (bd b b)⁻¹)) - 1) ∧
      ∀ i j : Fin n → Fin n ⊕ Fin n, i ∈ ({.inl, .inr} : Set _) → j ∈ ({.inl, .inr} : Set _) →
        ∀ z ∈ latW Y v, (mat2 (Λ₂ (bd b b * x * (bd b b)⁻¹)) - 1).submatrix i j *ᵥ z ∈ latW Y v := fun x hx hx' => by
    refine ⟨l4 _, fun i j hi hj => (stab_iff hσ τ hb hb' _).2 ⟨fun l m => ?_, fun l m => ?_⟩⟩
    · rw [← Matrix.submatrix_map, Matrix.map_sub _ (map_sub _), one, bd_sub _ _ hi hj,
        l1, ← Units.val_mul, ← Units.val_mul,
        show (bd b b)⁻¹ * (bd b b * x * (bd b b)⁻¹) * bd b b = x by group]
      exact sub_mem (hx _ _) (o _ _)
    · rw [← Matrix.submatrix_map, Matrix.map_sub _ (map_sub _), one, bd_sub _ _ hi hj,
        l2, dual_conj gg]
      refine sub_mem (sum_mem fun c _ => mul_mem (sum_mem fun d _ => mul_mem ?_ (hx' _ _)) ?_) (o _ _)
      · generalize i l = a
        rcases a with a | a <;> rcases d with d | d
        exacts [o a d, zero_mem _, zero_mem _, neg_mem (o a d)]
      · generalize j m = a
        rcases a with a | a <;> rcases c with c | c
        exacts [o c a, zero_mem _, zero_mem _, neg_mem (o c a)]
  have u1 := hu _ (splitPrime_under τ)
  have u2 := hu _ (splitPrime_under (τ.comp σ))
  have hφ : ∀ y : GL (Fin n) (Fv F v), ∃ t, IsGcd (v.adicCompletionIntegers F).toSubring y t ∧ f (e (Λ (b * y * b⁻¹), 1)) =
      chS χ (τ.comp σ) (z + n / 2) (GeneralLinearGroup.det y⁻¹) *
        (chS χ τ (z + n / 2) * chS χ (τ.comp σ) (z + n / 2)) (GeneralLinearGroup.det t) := fun y => by
    obtain ⟨t, κ, k1, k2, ht, hκ⟩ := exists_frame (lf v) y
    refine ⟨t, ht, ?_⟩
    let p := bd b b * (bd y 1 * κ⁻¹) * (bd b b)⁻¹
    have hp : p.1 * fromRows 𝟙 𝟙 = fromRows 𝟙 𝟙 * (b * t * b⁻¹).1 := by
      have : ((bd b b)⁻¹).1 * fromRows 𝟙 𝟙 = fromRows 𝟙 𝟙 * (b⁻¹).1 := by
        simp only [bd_inv, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul,
          add_zero, zero_add]
      simp only [p, Units.val_mul, Matrix.mul_assoc, this]
      rw [← Matrix.mul_assoc (κ⁻¹).1, hκ]
      simp only [bd_val, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, Matrix.one_mul, Matrix.zero_mul,
        add_zero, zero_add, Matrix.mul_assoc, Units.mul_inv_cancel_left, Units.val_one]
    obtain ⟨t', hp', dt⟩ := exists_dual J (J₂ := bd J (-J)) rfl hp
    let T := upG hσ τ (b * t * b⁻¹, t')
    have dg : ∀ {R : Type} [CommRing R] (φ : AE F E →+* R), (diagCols (Fin n) : Matrix _ _ (AE F E)).map φ =
        fromRows (1 : Matrix (Fin n) (Fin n) R) (1 : Matrix (Fin n) (Fin n) R) :=
      fun φ => by rw [diagCols, Matrix.fromRows_map, one]
    have par : mat2 (Λ₂ p) * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) =
        (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * T.1 := extS hσ τ
      (by rw [Matrix.map_mul, Matrix.map_mul, dg, l1, upG_val, up_fst, hp])
      (by rw [Matrix.map_mul, Matrix.map_mul, dg, l2, upG_val, up_snd,
        dual_val, hp'])
      (by rw [Matrix.map_mul, Matrix.map_mul, l3, upG_val, up_aw,
        Matrix.one_mul, Matrix.mul_one])
    have at1 : At (evFin F v) ((GeneralLinearGroup.det T).1 - 1) := by
      rw [show (GeneralLinearGroup.det T).1 = _ from det_liftM v _]
      change At _ (1 + GlobalTheory.EmbChart.tensAt E v _ - 1)
      rw [add_sub_cancel_left]; exact at_tensAt v _
    have d1 : piW τ (GeneralLinearGroup.det T).1 = (GeneralLinearGroup.det (b * t * b⁻¹)).1 :=
      (RingHom.map_det _ _).trans (congrArg Matrix.det (up_fst hσ τ (b * t * b⁻¹).1 t'.1))
    have d2 : piW (τ.comp σ) (GeneralLinearGroup.det T).1 = (GeneralLinearGroup.det t').1 :=
      (RingHom.map_det _ _).trans (congrArg Matrix.det (up_snd hσ τ (b * t * b⁻¹).1 t'.1))
    have e1 : bd (b * y * b⁻¹) 1 = p * (bd b b * κ * (bd b b)⁻¹) := by
      rw [show p * (bd b b * κ * (bd b b)⁻¹) = bd b b * bd y 1 * (bd b b)⁻¹ by simp only [p]; group]
      exact Units.ext (by simp only [Units.val_mul, bd_val, bd_inv, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
        add_zero, zero_add, Units.val_one, Matrix.mul_one, Units.mul_inv])
    have dκ : chS χ (τ.comp σ) (z + n / 2) (GeneralLinearGroup.det κ) = 1 := by
      have int : ∀ x : GL (Fin n ⊕ Fin n) (Fv F v), (∀ i j, x.1 i j ∈ (v.adicCompletionIntegers F).toSubring) →
          ‖(GeneralLinearGroup.det x).1‖ ≤ 1 := fun x hx => ((GlobalTheory.CompanionTheory.QL.NormalisedValue.main (lf v)).2.2.1 _).2 (by
        rw [GeneralLinearGroup.val_det_apply, Matrix.det_apply']
        exact sum_mem fun _ _ => mul_mem (intCast_mem _ _) (prod_mem fun _ _ => hx _ _))
      refine chS_unit u2 _ _ (le_antisymm (int κ k1) ?_)
      have := int _ k2
      rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at this
      exact (inv_le_one₀ (norm_pos_iff.2 (Units.ne_zero _))).1 this
    have dp : GeneralLinearGroup.det t' = GeneralLinearGroup.det t * (GeneralLinearGroup.det y⁻¹ * GeneralLinearGroup.det κ) := by
      have : GeneralLinearGroup.det (bd y 1) = GeneralLinearGroup.det y := Units.ext (by
        simp [bd_val, Matrix.det_fromBlocks_zero₂₁])
      rw [dt]
      simp only [p, map_mul, map_inv, this, mul_inv_cancel_comm, mul_inv, inv_inv]
    have hk : Λ₂ (bd b b * κ * (bd b b)⁻¹) ∈ K := Inert.mem_K hK (by
      rintro x (rfl | rfl)
      · exact key κ k1 k2
      · rw [← map_inv, show (bd b b * κ * (bd b b)⁻¹)⁻¹ = bd b b * κ⁻¹ * (bd b b)⁻¹ by group]
        exact key _ k2 k1)
    have dt' : GeneralLinearGroup.det (b * t * b⁻¹) = GeneralLinearGroup.det t := by
      rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    rw [emb, e1, map_mul, hf _ T par (l4 _) _ hk (l4 _), chi_at hσ τ χ at1 d1 d2,
      abs_at hσ τ at1, d1, d2, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _),
      mul_mul_mul_comm]
    change chS χ τ _ _ * chS χ (τ.comp σ) _ _ = _
    rw [dt', dp, map_mul, map_mul, dκ, MonoidHom.mul_apply]
    ring
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  let dn : UA σ Y.J →* GL (Fin n) (Fv F v) := (GeneralLinearGroup.map (piW τ)).comp (Subgroup.subtype _)
  let φ : locGrp σ Y v ≃ₜ* GL (Fin n) (Fv F v) :=
    { toFun := fun g => b⁻¹ * dn g.1 * b
      invFun := fun x => ⟨Λ (b * x * b⁻¹), Subgroup.subset_closure (up_at _ _ _ _)⟩
      left_inv := fun g => Subtype.ext ((congrArg Λ (show b * (b⁻¹ * dn g.1 * b) * b⁻¹ = dn g.1 by group)).trans (lift_down hσ τ h1 h2 (((USub σ Y v).closure_eq).le g.2)))
      right_inv := fun x => by
        change b⁻¹ * dn (Λ (b * x * b⁻¹)) * b = x
        rw [show dn (Λ (b * x * b⁻¹)) = b * x * b⁻¹ from Units.ext (a1 _)]; group
      map_mul' := fun _ _ => by simp only [Subgroup.coe_mul, map_mul]; group
      continuous_toFun := (continuous_const.mul (((Units.continuous_map (continuous_id.matrix_map (continuous_piW τ))).comp
        continuous_subtype_val).comp continuous_subtype_val)).mul continuous_const
      continuous_invFun := ((continuous_liftS hσ τ h1 h2).comp (by fun_prop)).subtype_mk _ }
  let m := φ.toHomeomorph.toMeasurableEquiv
  haveI : (μ.map m).IsHaarMeasure := φ.isHaarMeasure_map μ
  have hat : ∀ z ∈ latW Y v, At (evFin F v) z := fun z hz => ((mem_latW z).1 hz).1
  have st : ∀ g : UA σ Y.J, (∀ z ∈ latHat Y, At (evFin F v) z → mat g *ᵥ z ∈ latHat Y) ↔
      b⁻¹ * dn g * b ∈ GlobalTheory.CompanionTheory.QL.GLint (v.adicCompletionIntegers F).toSubring n := fun g => by
    have := dual_conj (ε := 1) hg (b⁻¹ * dn g * b)
    rw [show b * (b⁻¹ * dn g * b) * b⁻¹ = dn g by group, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] at this
    rw [Inert.stab_latW hat, stab_iff hσ τ hb hb', show (mat g).map (piW (τ.comp σ)) = _ from snd_eq τ h1 g]
    exact and_congr Iff.rfl ((Iff.of_eq (congrArg (fun M : Matrix _ _ _ => ∀ i j, M i j ∈ v.adicCompletionIntegers F) this)).trans
      forall_swap)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have bb : ∀ t : E →ₐ[F] Fv F v, UnrAt χ (splitPrime t) → ∀ i < n,
      ‖chS χ t (z + n / 2) (unifAt v)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ i < 1 := fun t ht i hi => by
    rw [chS_unif ht, norm_mul, norm_val, one_mul]
    have : (i : ℝ) < n := by exact_mod_cast hi
    exact npow_lt (by simp; linarith)
  have hC : (chS χ τ (z + n / 2) * chS χ (τ.comp σ) (z + n / 2)) (unifAt v) = npow v (-(2 * z + n)) := by
    rw [MonoidHom.mul_apply, chS_apply, chS_apply, mul_mul_mul_comm, chrW_mul hσ τ hr, norm_unif_cpow, ← LFun.npow_add, one_mul]
    congr 1; ring
  obtain ⟨i1, i2⟩ := doubling (lf v) (chS_unit u1 _) (chS_unit u2 _) (bb _ u1) (bb _ u2) (fun i hi => by
    have : (i : ℝ) < n := by exact_mod_cast hi
    rw [hC]; exact npow_lt (by simp; linarith)) (μ.map m) (by
    rw [m.map_apply, ← hμ1]
    congr 1
    ext g
    refine Iff.trans ?_ (show (_ ∧ _) ↔ IntAt v g.1 by simp only [IntAt, imp_and, forall_and]; rfl)
    rw [st, st, map_inv, show b⁻¹ * (dn g.1)⁻¹ * b = (b⁻¹ * dn g.1 * b)⁻¹ by group, inv_mem_iff, and_self]
    rfl) hφ
  have e2 : ∀ u : locGrp σ Y v, f (e (Λ (b * m u * b⁻¹), 1)) = f (e (u.1, 1)) := fun u =>
    congrArg (fun x : locGrp σ Y v => f (e (x.1, 1))) (φ.left_inv u)
  rw [integrable_map_equiv, Function.comp_def] at i1
  rw [integral_map_equiv] at i2
  simp only [e2] at i1 i2
  refine ⟨i1, ?_⟩
  rw [hC, ← Finset.prod_range_reflect, ← Finset.prod_mul_distrib] at i2
  rw [locD, if_pos ⟨τ⟩]
  convert i2 using 2
  · refine Finset.prod_congr rfl fun i hi => ?_
    have := Finset.mem_range.1 hi
    rw [npow_nat, one_pow, one_mul, npow, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    congr 3; push_cast; ring
  · classical
    rw [Lv, show Formalism.L2.Host.aboveF (L := E) F v = {splitPrime τ, splitPrime (τ.comp σ)} by
      ext u; simp [mem_aboveF, above_iff hσ τ], Finset.prod_pair (splitPrime_comp_ne hσ τ).symm, locL, locL, charFam_of_unrAt u1,
      charFam_of_unrAt u2, eulerFac_singleton, eulerFac_singleton, chS_unif u1, chS_unif u2, mul_assoc, mul_assoc, npow_nat]
    simp only [npow, SplitChart.absNorm_splitPrime]

end GlobalTheory.ThK.Dbl

end
