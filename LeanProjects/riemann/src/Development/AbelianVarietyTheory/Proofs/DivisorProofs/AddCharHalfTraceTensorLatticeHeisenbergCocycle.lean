import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.VacCocycle

section General

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

set_option autoImplicit false in
open IsDedekindDomain NumberField MeasureTheory Matrix in
open Classical in
open scoped TensorProduct ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem _root_.GlobalTheory.VacCocycle.conj_hTens (hc : ∀ z, c (c z) = z) {JA : Matrix α α A}
    {JB : Matrix β β A} (hA : ∀ i j, c (JA j i) = JA i j) (hB : ∀ i j, c (JB j i) = -JB i j)
    (x y : Matrix α β A) :
    c (_root_.GlobalTheory.WeilM.hTens c JA JB y x) = -_root_.GlobalTheory.WeilM.hTens c JA JB x y := by
  unfold _root_.GlobalTheory.WeilM.hTens
  simp only [map_sum, map_mul, hc, hA, hB]
  simp only [← Finset.sum_neg_distrib]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, k, 2, i]; rw [Finset.sum_comm]
  conv_lhs => enter [2, k]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

set_option autoImplicit false in
open IsDedekindDomain NumberField MeasureTheory Matrix in
open Classical in
open scoped TensorProduct ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem _root_.GlobalTheory.VacCocycle.trace_conj (hc : ∀ z, c (c z) = z) (z : A) :
    Algebra.trace R A (c z) = Algebra.trace R A z :=
  Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)) z

end General

set_option autoImplicit false in
open IsDedekindDomain NumberField MeasureTheory Matrix in
open Classical in
open scoped TensorProduct ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
omit [DecidableEq α] [DecidableEq β] in
private lemma hTens_add_add (JA : Matrix α α A) (JB : Matrix β β A)
    (x y : Matrix α β A) :
    _root_.GlobalTheory.WeilM.hTens c JA JB (x + y) (x + y) =
      _root_.GlobalTheory.WeilM.hTens c JA JB x x + _root_.GlobalTheory.WeilM.hTens c JA JB x y +
        _root_.GlobalTheory.WeilM.hTens c JA JB y x + _root_.GlobalTheory.WeilM.hTens c JA JB y y := by
  unfold _root_.GlobalTheory.WeilM.hTens
  simp only [Matrix.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib]
  ring

set_option autoImplicit false in
open IsDedekindDomain NumberField MeasureTheory Matrix in
open Classical in
open scoped TensorProduct ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
private lemma addChar_symp_add_add (hc : ∀ z, c (c z) = z) {JA : Matrix α α A}
    {JB : Matrix β β A} (hA : ∀ i j, c (JA j i) = JA i j) (hB : ∀ i j, c (JB j i) = -JB i j)
    (ψ : AddChar R ℂ) {h : R} (hh : h * 2 = 1) {ξ : A} (hξ : c ξ = 1 - ξ) (x y : Matrix α β A)
    (h1 : ψ (_root_.GlobalTheory.WeilM.symp c ξ JA JB x y) = 1)
    (h2 : ψ (_root_.GlobalTheory.WeilM.symp c (-1) JA JB x y) = 1) :
    ψ (h * _root_.GlobalTheory.WeilM.symp c ξ JA JB (x + y) (x + y)) =
      ψ (h * _root_.GlobalTheory.WeilM.symp c ξ JA JB x x) *
        ψ (h * _root_.GlobalTheory.WeilM.symp c ξ JA JB y y) *
        ψ (-(h * _root_.GlobalTheory.WeilM.symp c (-1) JA JB x y)) := by
  unfold _root_.GlobalTheory.WeilM.symp at *
  have hswap : _root_.GlobalTheory.WeilM.hTens c JA JB y x =
      -c (_root_.GlobalTheory.WeilM.hTens c JA JB x y) := by
    rw [_root_.GlobalTheory.VacCocycle.conj_hTens c hc hA hB y x, neg_neg]
  have hconj : Algebra.trace R A (ξ * c (_root_.GlobalTheory.WeilM.hTens c JA JB x y)) =
      Algebra.trace R A (_root_.GlobalTheory.WeilM.hTens c JA JB x y) -
        Algebra.trace R A (ξ * _root_.GlobalTheory.WeilM.hTens c JA JB x y) := by
    rw [← _root_.GlobalTheory.VacCocycle.trace_conj c hc, map_mul, hc, hξ, sub_mul, one_mul, map_sub]
  have hm1 : Algebra.trace R A (-1 * _root_.GlobalTheory.WeilM.hTens c JA JB x y) =
      -Algebra.trace R A (_root_.GlobalTheory.WeilM.hTens c JA JB x y) := by
    rw [neg_one_mul, map_neg]
  have key : h * Algebra.trace R A (ξ * _root_.GlobalTheory.WeilM.hTens c JA JB (x + y) (x + y)) =
      h * Algebra.trace R A (ξ * _root_.GlobalTheory.WeilM.hTens c JA JB x x) +
        h * Algebra.trace R A (ξ * _root_.GlobalTheory.WeilM.hTens c JA JB y y) +
        -(h * Algebra.trace R A (-1 * _root_.GlobalTheory.WeilM.hTens c JA JB x y)) +
        (Algebra.trace R A (ξ * _root_.GlobalTheory.WeilM.hTens c JA JB x y) +
          Algebra.trace R A (-1 * _root_.GlobalTheory.WeilM.hTens c JA JB x y)) := by
    rw [hTens_add_add, hswap]
    simp only [mul_add, map_add, mul_neg, map_neg]
    rw [hconj]
    linear_combination (Algebra.trace R A (ξ * _root_.GlobalTheory.WeilM.hTens c JA JB x y) -
      Algebra.trace R A (_root_.GlobalTheory.WeilM.hTens c JA JB x y)) * hh + (h - 1) * hm1
  rw [key]
  simp only [AddChar.map_add_eq_mul]
  rw [h1, h2, mul_one, mul_one]

set_option autoImplicit false in
open IsDedekindDomain NumberField MeasureTheory Matrix in
open Classical in
open scoped TensorProduct ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in

theorem _root_.GlobalTheory.VacCocycle.psi_half_symp_add : ∀ {F E : Type} [Field F]
    [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E), B.IsGood σ →
    ∀ {n d : ℕ} (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ v : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F,
    ∀ γ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, ∀ γ' ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v,
      B.ψ (⅟(2 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) * _root_.GlobalTheory.WeilM.symp
          (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (θ : E))
          (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
          (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (γ + γ') (γ + γ')) =
        B.ψ (⅟(2 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) * _root_.GlobalTheory.WeilM.symp
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (θ : E))
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ) *
          B.ψ (⅟(2 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) * _root_.GlobalTheory.WeilM.symp
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (θ : E))
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ' γ') *
          B.ψ (-(⅟(2 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) * _root_.GlobalTheory.WeilM.symp
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ')) := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY θ hθ v γ hγ γ' hγ'
  have hσ : ∀ z, σ (σ z) = z := by
    have hcm := hB.cm
    unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt at hcm
    obtain ⟨-, -, -, hτ⟩ := hcm
    intro z
    let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
    apply τ.injective
    rw [hτ, hτ, star_star]
  have hcc : ∀ z, _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ z) = z := by
    have hcomp : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ).comp (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) = AlgHom.id _ _ := by
      unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA
      rw [← Algebra.TensorProduct.map_comp]
      have hσσ : σ.comp σ = AlgHom.id F E := AlgHom.ext hσ
      rw [hσσ, AlgHom.comp_id]
      exact Algebra.TensorProduct.map_id
    intro z
    exact DFunLike.congr_fun hcomp z
  have hinc : ∀ x : E, _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) x) =
      _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (σ x) := by
    intro x
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR
    simp
  have hA : ∀ i j, _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J j i) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J i j := by
    intro i j
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM
    rw [Matrix.map_apply, Matrix.map_apply, hinc, hX.herm]
  have hB' : ∀ i j, _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J j i) =
      -_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J i j := by
    intro i j
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM
    rw [Matrix.map_apply, Matrix.map_apply, hinc, hY.skew, map_neg]
  have hξ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (θ : E)) =
      1 - _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (θ : E) := by
    rw [hinc, eq_sub_of_add_eq' hθ, map_sub, map_one]
  have hone : (_root_.GlobalTheory.AdelicU.evFin F v) 1 ∈
      HeightOneSpectrum.adicCompletionIntegers F v := by
    rw [map_one]
    exact one_mem _
  have h1 := _root_.GlobalTheory.LatVacArith.psi_symp_latAtV σ B X Y r s r' s' hB hX hY v θ 1
    hone γ hγ γ' hγ'
  have h2 := _root_.GlobalTheory.LatVacArith.psi_symp_latAtV σ B X Y r s r' s' hB hX hY v (-1) 1
    hone γ hγ γ' hγ'
  rw [one_mul] at h1 h2
  have hm : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (((-1 : 𝓞 E) : E)) = -1 := by
    simp
  rw [hm] at h2
  exact addChar_symp_add_add (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) hcc hA hB' B.ψ
    (invOf_mul_self (2 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) hξ γ γ' h1 h2

end GlobalTheory.VacCocycle

end
