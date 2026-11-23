import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.SlopeE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.HarderNarasimhan.ShiftInvariance

open NumberField
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder Kronecker MatrixOrder

noncomputable section

namespace GlobalTheory.TestLat.SlopeModel

theorem exists_frame {N : ℕ} {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.PosDef) :
    ∃ X : Matrix (Fin N) (Fin N) ℂ, IsUnit X.det ∧ (X⁻¹)ᴴ * X⁻¹ = H := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hH.posSemidef.nonneg
  have hu : IsUnit B.det := by
    have h := (Matrix.isUnit_iff_isUnit_det _).1 hH.isUnit
    rw [hB, Matrix.det_mul] at h
    exact isUnit_of_mul_isUnit_right h
  refine ⟨B⁻¹, Matrix.isUnit_nonsing_inv_det B hu, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv B hu, hB]
  rfl

variable {K : Type} [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}

open NumberField in
open scoped Matrix ComplexOrder in
open scoped Kronecker MatrixOrder in
variable {K : Type} [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι] {n N : ℕ}
  {C : Type} in
omit [NumberField K] in
theorem _root_.GlobalTheory.TestLat.SlopeModel.sumGram_posDef (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam) [Finite C]
    (G : ι → Matrix (Fin n) (Fin n) K) (φ : K →+* ℂ) (hG : ∀ τ, ((G τ).map φ).PosDef) :
    ((_root_.GlobalTheory.TestLat.sumGram lam e G).map φ).PosDef := by
  classical
  choose B hB hBT using fun τ => _root_.Formalism.L2.DIV.ps_factor (hG τ).transpose
  obtain ⟨D, hD⟩ : ∃ D : ℂ, D = ∏ τ, ((G τ).map φ).det ^ (lam τ).detShift := ⟨_, rfl⟩
  have hDpos : 0 < D := by
    rw [hD]
    exact Finset.prod_pos fun τ _ => zpow_pos (hG τ).det_pos _
  have hDstar : star D = D := Complex.conj_eq_iff_im.mpr (Complex.pos_iff.mp hDpos).2.symm
  obtain ⟨w, hw⟩ : ∃ w : _root_.Formalism.L2.DIV.VVIdx lam → MvPolynomial (ι × Fin n × Fin n) ℂ,
      w = fun i => _root_.Formalism.GradedWeylDivisibility.blockAct ℂ B (MvPolynomial.map φ (_root_.Formalism.L2.DIV.bVVfun K lam i)) := ⟨_, rfl⟩
  have hcoef : ∀ i (m : ι × Fin n × Fin n →₀ ℕ),
      φ (star (MvPolynomial.coeff m (_root_.Formalism.L2.DIV.bVVfun K lam i))) =
        star (φ (MvPolynomial.coeff m (_root_.Formalism.L2.DIV.bVVfun K lam i))) := by
    intro i m
    obtain ⟨P, hP⟩ := _root_.Formalism.L2.DIV.bVVfun_int K lam i
    rw [hP, MvPolynomial.coeff_map]
    simp
  have hentry : ∀ a b, (_root_.GlobalTheory.TestLat.sumGram lam e G).map φ a b =
      if (e a).1 = (e b).1 then D * _root_.Formalism.L2.Col.nfL lam (w (e a).2) (w (e b).2) else 0 := by
    intro a b
    simp only [Matrix.map_apply, _root_.GlobalTheory.TestLat.sumGram, Matrix.of_apply]
    split_ifs
    · rw [_root_.Formalism.L2.DIV.pairK_apply, _root_.Formalism.L2.DIV.bVV_coe, _root_.Formalism.L2.DIV.bVV_coe, _root_.Formalism.L2.Col.map_pairP φ lam G B hBT _ _ (hcoef _), _root_.Formalism.L2.Col.nfL_apply, hD, hw]
    · exact map_zero φ
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro a b
    rw [hentry, hentry]
    by_cases h : (e a).1 = (e b).1
    · rw [if_pos h.symm, if_pos h, star_mul', hDstar, _root_.Formalism.L2.DIV.ps_nfL_symm]
    · rw [if_neg (Ne.symm h), if_neg h, star_zero]
  intro x hx
  rcases isEmpty_or_nonempty C with hC | hC
  · exact absurd (funext fun a => (hC.false (e a).1).elim) hx
  obtain ⟨c0⟩ := hC
  haveI : Finite (_root_.Formalism.L2.DIV.VVIdx lam) :=
    Finite.of_injective (fun i => e.symm (c0, i)) (fun i j h => by simpa using h)
  letI := Fintype.ofFinite C
  letI := Fintype.ofFinite (_root_.Formalism.L2.DIV.VVIdx lam)
  have hinv : (_root_.Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (B τ)⁻¹)).comp (_root_.Formalism.GradedWeylDivisibility.blockAct ℂ B) =
      AlgHom.id ℂ (MvPolynomial (ι × Fin n × Fin n) ℂ) := by
    rw [_root_.Formalism.L2.DIV.blockAct_comp]
    have h1 : (fun τ => B τ * (B τ)⁻¹) = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) :=
      funext fun τ => Matrix.mul_nonsing_inv _ (hB τ)
    rw [h1, _root_.Formalism.L2.DIV.blockAct_one]
  have hUinj : Function.Injective (_root_.Formalism.GradedWeylDivisibility.blockAct ℂ B :
      MvPolynomial (ι × Fin n × Fin n) ℂ → MvPolynomial (ι × Fin n × Fin n) ℂ) := by
    intro p q hpq
    have h2 := congrArg (_root_.Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (B τ)⁻¹)) hpq
    rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, hinv] at h2
    simpa using h2
  have hli : LinearIndependent ℂ w := by
    have h3 := _root_.Formalism.L2.Col.linearIndependent_map φ (_root_.Formalism.L2.DIV.bVVfun K lam) (_root_.Formalism.L2.DIV.bVVfun_spec K lam).1
    rw [hw]
    exact h3.map' (_root_.Formalism.GradedWeylDivisibility.blockAct ℂ B).toLinearMap (LinearMap.ker_eq_bot.mpr hUinj)
  obtain ⟨W, hW⟩ : ∃ W : C → MvPolynomial (ι × Fin n × Fin n) ℂ,
      W = fun c => ∑ i, x (e.symm (c, i)) • w i := ⟨_, rfl⟩
  have key : star x ⬝ᵥ ((_root_.GlobalTheory.TestLat.sumGram lam e G).map φ) *ᵥ x =
      D * ∑ c, _root_.Formalism.L2.Col.nfL lam (W c) (W c) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, hentry]
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    simp only [Equiv.apply_symm_apply]
    conv_lhs =>
      enter [2, c, 2, i, 2]
      rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    simp only [Equiv.apply_symm_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hW, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm (γ := _root_.Formalism.L2.DIV.VVIdx lam) (f := fun i j => D * _)]
    simp only [Complex.star_def, RingHom.id_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [key]
  refine mul_pos hDpos (Finset.sum_pos' (fun c _ => ?_) ?_)
  · by_cases hc : W c = 0
    · rw [hc]
      simp
    · exact (_root_.Formalism.L2.DIV.ps_nfL_pos lam _ hc).le
  · obtain ⟨a, ha⟩ : ∃ a, x a ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext h)
    refine ⟨(e a).1, Finset.mem_univ _, _root_.Formalism.L2.DIV.ps_nfL_pos lam _ ?_⟩
    intro h0
    rw [hW] at h0
    have h4 := Fintype.linearIndependent_iff.mp hli _ h0 (e a).2
    simp at h4
    exact ha h4

open NumberField in
open scoped Matrix ComplexOrder in
open scoped Kronecker MatrixOrder in
variable {K : Type} [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι] {n N : ℕ}
  {C : Type} in
omit [StarRing K] in
private lemma exists_isMetric_of_posDef_map (H : Matrix (Fin N) (Fin N) K)
    (hH : ∀ φ : K →+* ℂ, (H.map φ).PosDef) : ∃ X, _root_.GlobalTheory.TestLat.IsMetric H X := by
  choose B hB hT using fun v : InfinitePlace K => _root_.Formalism.L2.DIV.ps_factor (hH v.embedding)
  have hu : ∀ v, IsUnit ((B v)ᴴ).det := fun v => by
    rw [Matrix.det_conjTranspose]
    exact (hB v).star
  refine ⟨fun v => ((B v)ᴴ)⁻¹, fun v => ⟨Matrix.isUnit_nonsing_inv_det _ (hu v), ?_⟩⟩
  rw [Matrix.nonsing_inv_nonsing_inv _ (hu v), Matrix.conjTranspose_conjTranspose, ← hT]

open NumberField in
open scoped Matrix ComplexOrder in
open scoped Kronecker MatrixOrder in
variable {K : Type} [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι] {n N : ℕ}
  {C : Type} in
omit [StarRing K] in
theorem _root_.GlobalTheory.TestLat.SlopeModel.exists_isMetric (H : Matrix (Fin N) (Fin N) K)
    (hH : ∀ φ : K →+* ℂ, (H.map φ).PosDef) :
    (∃ X, _root_.GlobalTheory.TestLat.IsMetric H X) ∧ ∃ X, _root_.GlobalTheory.TestLat.IsMetric (H⁻¹)ᵀ X := by
  refine ⟨exists_isMetric_of_posDef_map H hH, exists_isMetric_of_posDef_map _ fun φ => ?_⟩
  rw [Matrix.transpose_map, _root_.Formalism.L2.Col.map_inv_matrix]
  exact (hH φ).inv.transpose

open NumberField in
open scoped Matrix ComplexOrder in
open scoped Kronecker MatrixOrder in
variable {K : Type} [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι] {n N : ℕ}
  {C : Type} in
omit [StarRing K] in

theorem _root_.GlobalTheory.TestLat.SlopeModel.nonempty_idx (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) : Nonempty (_root_.Formalism.L2.DIV.VVIdx lam) := by
  have h := _root_.Formalism.L2.Col.evV_extV_ne_zero (E := ℚ) (K := ℚ) (fun _ : ι => RingHom.id ℚ) (1 : Matrix (Fin n) (Fin n) ℚ)
    lam (Rat.castHom ℂ) ⟨fun _ => 1, fun _ => by simp⟩
  have hne : _root_.Formalism.L2.Col.extV ℚ lam ≠ 0 := fun h0 => h (by rw [h0, map_zero])
  haveI : Nontrivial ↥(_root_.Formalism.L2.DIV.VV ℚ lam) := nontrivial_of_ne _ _ hne
  exact (_root_.Formalism.L2.DIV.bVV ℚ lam).index_nonempty

def stdLat (E : Type) [Field E] [NumberField E] (n : ℕ) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)

theorem mem_stdLat {E : Type} [Field E] [NumberField E] {x : Fin n → E} :
    x ∈ stdLat E n ↔ ∀ i, IsIntegral ℤ (x i) := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  exact forall_congr' fun i => ⟨fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe, fun h => ⟨⟨x i, h⟩, rfl⟩⟩

theorem mem_range_iff {E : Type} [Field E] [NumberField E] {x : E} :
    x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x :=
  ⟨fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem single_mem_stdLat {E : Type} [Field E] [NumberField E] (i : Fin n) :
    (Pi.single i 1 : Fin n → E) ∈ stdLat E n := by
  refine mem_stdLat.2 fun j => ?_
  by_cases h : j = i
  · subst h; simpa using isIntegral_one
  · simpa [h] using isIntegral_zero

theorem stdLat_isLattice (E : Type) [Field E] [NumberField E] (n : ℕ) : Submodule.IsLattice E (stdLat E n) := by
  refine ⟨Submodule.fg_pi fun _ => ?_, ?_⟩
  · rw [Submodule.one_eq_span]
    exact Submodule.fg_span (Set.finite_singleton _)
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply]
    exact single_mem_stdLat i

theorem stdLat_selfDualE {E : Type} [Field E] [NumberField E] (cE : E →+* E) (n : ℕ) :
    IsSelfDualE cE (1 : Matrix (Fin n) (Fin n) E) (stdLat E n) := by
  have hf : ∀ x y : Fin n → E, Formalism.UG.hform cE (1 : Matrix (Fin n) (Fin n) E) x y = ∑ i, cE (x i) * y i := by
    intro x y
    simp [Formalism.UG.hform, Matrix.one_apply]
  refine ⟨stdLat_isLattice E n, fun y => ⟨fun hy x hx => ?_, fun h => mem_stdLat.2 fun i => ?_⟩⟩
  · rw [mem_range_iff, hf]
    exact IsIntegral.sum _ fun i _ =>
      ((mem_stdLat.1 hx i).map cE.toIntAlgHom).mul (mem_stdLat.1 hy i)
  · have := h _ (single_mem_stdLat i)
    rw [mem_range_iff, hf, Finset.sum_eq_single i] at this
    · simpa using this
    · intro b _ hb
      simp [hb]
    · simp

def wt (a : ℕ) : DomWeight 2 where
  w := ![a, 0]
  anti := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

abbrev K4 : Type := CyclotomicField 4 ℚ

instance isCyclotomicExtension_four_slopeModelField : IsCyclotomicExtension {4} ℚ K4 := by
  have h : @IsCyclotomicExtension {4} ℚ K4 _ _ (CyclotomicField.algebra 4 ℚ) := inferInstance
  convert h
  exact Subsingleton.elim _ _

instance isCMField_slopeModelField : IsCMField K4 := IsCyclotomicExtension.Rat.isCMField K4 (S := {4}) ⟨4, rfl, by norm_num⟩

theorem hypotheses_inhabited (a : ℕ) (ha : 1 ≤ a) (k : ℕ) :
    letI : StarRing K4 := IsCMField.starRing K4
    ∃ (v₀ : InfinitePlace K4) (cE : K4 →+* K4) (emb : Unit → K4 →+* K4) (lam : Unit → DomWeight 2)
      (J : Matrix (Fin 2) (Fin 2) K4) (L : Fin (k + 1) → Submodule (𝓞 K4) (Fin 2 → K4)) (N : ℕ)
      (e : Fin N ≃ Fin (k + 1) × VVIdx lam),
      IsTotallyComplex K4 ∧ Formalism.DivisionValues.IsConjAt v₀ ∧ cE ≠ RingHom.id _ ∧
      (∀ (φ : K4 →+* ℂ) (x : K4), φ (cE x) = starRingEnd ℂ (φ x)) ∧
      (∀ τ x, star (emb τ x) = emb τ (cE x)) ∧ (1 : ℝ) ≤ a ∧ SpreadLe lam a ∧ (lam ()).w 0 - (lam ()).w 1 = a ∧
      (∀ φ : K4 →+* ℂ, (J.map φ).PosDef) ∧ (∀ c, IsSelfDualE cE J (L c)) ∧ 0 < N ∧
      (∃ X, IsMetric ((sumGram lam e (gramK emb J))⁻¹)ᵀ X) ∧ (∃ X, IsMetric (sumGram lam e (gramK emb J)) X) ∧
      (∃ X, IsMetric ((sumGram lam e (gramKd emb J))⁻¹)ᵀ X) ∧ (∃ X, IsMetric (sumGram lam e (gramKd emb J)) X) := by
  letI : StarRing K4 := IsCMField.starRing K4
  have hone : ∀ φ : K4 →+* ℂ, ((1 : Matrix (Fin 2) (Fin 2) K4).map φ).PosDef := fun φ => by
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.PosDef.one
  let lam : Unit → DomWeight 2 := fun _ => wt a
  let e := (Fintype.equivFin (Fin (k + 1) × VVIdx lam)).symm
  have g1 : gramK (fun _ : Unit => RingHom.id K4) (1 : Matrix (Fin 2) (Fin 2) K4) = fun _ => 1 := by
    funext τ; simp [gramK]
  have g2 : gramKd (fun _ : Unit => RingHom.id K4) (1 : Matrix (Fin 2) (Fin 2) K4) = fun _ => 1 := by
    funext τ; simp [gramKd]
  have hm := exists_isMetric (sumGram lam e fun _ => (1 : Matrix (Fin 2) (Fin 2) K4))
    fun φ => sumGram_posDef lam e _ φ fun _ => hone φ
  haveI := nonempty_idx lam
  refine ⟨Classical.arbitrary _, (IsCMField.complexConj K4 : K4 →+* K4), fun _ => RingHom.id _, lam, 1,
    fun _ => stdLat K4 2, _, e, inferInstance, fun x => IsCMField.complexEmbedding_complexConj K4 _ x, ?_,
    fun φ x => IsCMField.complexEmbedding_complexConj K4 φ x, fun _ _ => rfl, by exact_mod_cast ha, ?_, ?_, hone,
    fun _ => stdLat_selfDualE _ 2, Fintype.card_pos, ?_, ?_, ?_, ?_⟩
  · intro h
    apply IsCMField.complexConj_ne_one K4
    ext x
    exact congrArg (fun f : K4 →+* K4 => f x) h
  · intro τ i j
    fin_cases i <;> fin_cases j <;> simp [lam, wt]
  · simp [lam, wt]
  · rw [g1]; exact hm.2
  · rw [g1]; exact hm.1
  · rw [g2]; exact hm.2
  · rw [g2]; exact hm.1

theorem hypothesesK (n : ℕ) :
    IsDefGram (1 : Matrix (Fin n) (Fin n) K) ∧ IsSelfDualK (1 : Matrix (Fin n) (Fin n) K) (stdLat K n) := by
  refine ⟨⟨Matrix.conjTranspose_one, fun a b => ?_, fun φ => ?_⟩, stdLat_isLattice K n, ?_⟩
  · rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.PosDef.one
  · have hm : ∀ x : K, x ∈ (1 : Submodule (𝓞 K) K) ↔ IsIntegral ℤ x := fun x => by
      rw [Submodule.mem_one]
      exact ⟨fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe, fun h => ⟨⟨x, h⟩, rfl⟩⟩
    ext x
    change (∀ y ∈ stdLat K n, star y ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) K) *ᵥ x) ∈ (1 : Submodule (𝓞 K) K)) ↔ _
    simp only [Matrix.one_mulVec, hm]
    refine ⟨fun h => mem_stdLat.2 fun i => ?_, fun hx y hy => ?_⟩
    · have := h _ (single_mem_stdLat i)
      simpa [Pi.star_single] using this
    · exact IsIntegral.sum _ fun i _ =>
        ((mem_stdLat.1 hy i).map (starRingEnd K).toIntAlgHom).mul (mem_stdLat.1 hx i)

theorem muDef_std [IsTotallyComplex K] (hN : 0 < N) :
    Formalism.HN.muDef (Pi.basisFun K (Fin N)) (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ))
      (Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin N)))) = 0 := by
  have hX : ∀ v : InfinitePlace K, IsUnit ((fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) v).det := fun _ => by simp
  have hne : Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin N))) ≠ ⊥ := by
    intro h
    have := Submodule.subset_span (R := 𝓞 K) (Set.mem_range_self (f := Pi.basisFun K (Fin N)) ⟨0, hN⟩)
    rw [h, SetLike.mem_coe, Submodule.mem_bot] at this
    exact (Pi.basisFun K (Fin N)).ne_zero _ this
  have h1 := (Formalism.HN.sizeMu K (Fin N → K) (Fin N) (Pi.basisFun K (Fin N)) _ hX _
    (Submodule.fg_span (Set.finite_range _)) hne).2.1
  have h2 := (Formalism.HN.htGram K (Fin N → K) (Fin N) (Pi.basisFun K (Fin N)) _ hX N (Pi.basisFun K (Fin N))
    (Pi.basisFun K (Fin N)).linearIndependent).1
  have h3 : ∀ v : InfinitePlace K, Formalism.HN.gramPl (Pi.basisFun K (Fin N)) (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) v
      (Pi.basisFun K (Fin N)) = 1 := by
    intro v
    ext a c
    simp only [Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, Matrix.of_apply, inv_one,
      Matrix.one_mulVec, Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single a]
    · by_cases h : a = c
      · simp [h]
      · simp [h, Ne.symm h]
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [h1, Formalism.HN.size, h2]
  simp [h3]

theorem bound_edges (f ν : ℕ) (R : ℝ) : bound f 0 R = 0 ∧ bound 0 ν R = 0 ∧ bound f 1 1 = 0 := by
  simp [bound]

end GlobalTheory.TestLat.SlopeModel
