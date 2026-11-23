import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceHalfHeisenbergInvariantForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

open GlobalTheory.PlaceModel

namespace GlobalTheory.ProdForm

def iterForm {D : D7} {S A B T : HSp D} (o : OrthDec S A B) (ℓA : (WO A T → ℂ) →ₗ[ℂ] ℂ)
    (ℓB : (WO B T → ℂ) →ₗ[ℂ] ℂ) : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
  ℓA ∘ₗ LinearMap.pi fun a => ℓB ∘ₗ LinearMap.funLeft ℂ ℂ (fun b => (o.resS T).symm (a, b))

theorem iterForm_boxS {D : D7} {S A B T : HSp D} (o : OrthDec S A B) (ℓA : (WO A T → ℂ) →ₗ[ℂ] ℂ)
    (ℓB : (WO B T → ℂ) →ₗ[ℂ] ℂ) (fA : WO A T → ℂ) (fB : WO B T → ℂ) :
    iterForm o ℓA ℓB (o.boxS T fA fB) = ℓA fA * ℓB fB := by
  have h : (LinearMap.pi fun a => ℓB ∘ₗ LinearMap.funLeft ℂ ℂ (fun b => (o.resS T).symm (a, b)))
      (o.boxS T fA fB) = ℓB fB • fA := by
    funext a
    have : (LinearMap.funLeft ℂ ℂ (fun b => (o.resS T).symm (a, b))) (o.boxS T fA fB) = fA a • fB := by
      funext b
      simp [LinearMap.funLeft_apply, OrthDec.boxS]
    simp [this, mul_comm]
  rw [iterForm, LinearMap.comp_apply, h, map_smul, smul_eq_mul, mul_comm]

end GlobalTheory.ProdForm

namespace GlobalTheory.ProdForm

theorem exists_product_form : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B), ∀ e, IsSplitIdem D e → ∀ (ℓA : (WO A T → ℂ) →ₗ[ℂ] ℂ) (ℓB : (WO B T → ℂ) →ₗ[ℂ] ℂ), (∀ u : WO A T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ A T f → ℓA (heisO ψ A T u f) = ℓA f) → (∀ u : WO B T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ B T f → ℓB (heisO ψ B T u f) = ℓB f) → ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧ ∀ fA fB, IsThetaFunO ψ A T fA → IsThetaFunO ψ B T fB → ℓ (o.boxS T fA fB) = ℓA fA * ℓB fB := by
  intro D ψ hψ S A B T o e hs ℓA ℓB hA hB
  classical
  obtain ⟨he, hec, v, ε, hε, heq⟩ := id hs
  have hs' := GlobalTheory.SplitScalar.isSplitIdem_conj hs
  have he' : cA D e * cA D e = cA D e := hs'.1
  have heε' : algebraMap (AF D.host.F) (AE D) ε * cA D e = cA D e := by rw [← heq]; linear_combination he' + hec
  have c2 : cA D (cA D e) * cA D e = 0 := by rw [GlobalTheory.LatVac.cA_cA, hec]

  have hresA : ∀ u : WO S T, u ∈ half S T (cA D e) → ∀ i j, cA D e * (o.resS T u).1 i j = (o.resS T u).1 i j := by
    intro u hu i j
    have hu' : ∀ i j, cA D e * u i j = u i j := (isHalf_iff S T).2 hu
    simp only [OrthDec.resS_apply, Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, hu']
  have hresB : ∀ u : WO S T, u ∈ half S T (cA D e) → ∀ i j, cA D e * (o.resS T u).2 i j = (o.resS T u).2 i j := by
    intro u hu i j
    have hu' : ∀ i j, cA D e * u i j = u i j := (isHalf_iff S T).2 hu
    simp only [OrthDec.resS_apply, Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, hu']
  set l0 := iterForm o ℓA ℓB with hl0
  let gen : Set (WO S T → ℂ) := {f | ∃ fA fB, IsThetaFunO ψ A T fA ∧ IsThetaFunO ψ B T fB ∧ f = o.boxS T fA fB}
  let P : Submodule ℂ (WO S T → ℂ) := Submodule.span ℂ gen

  have hPst : ∀ u ∈ half S T (cA D e), ∀ p ∈ P, heisL S T ψ u p ∈ P := by
    intro u hu p hp
    induction hp using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨fA, fB, hfA, hfB, rfl⟩ := hf
      refine Submodule.subset_span ⟨_, _, GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hfA (o.resS T u).1,
        GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hfB (o.resS T u).2, ?_⟩
      exact o.heisO_boxS ψ T fA fB u
    | zero => rw [map_zero]; exact P.zero_mem
    | add a b _ _ ha hb => rw [map_add]; exact P.add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact P.smul_mem c ha
  have hl0P : ∀ u ∈ half S T (cA D e), ∀ p ∈ P, l0 (heisL S T ψ u p) = l0 p := by
    intro u hu p hp
    induction hp using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨fA, fB, hfA, hfB, rfl⟩ := hf
      change l0 (heisO ψ S T u (o.boxS T fA fB)) = _
      rw [o.heisO_boxS ψ T fA fB u, hl0, iterForm_boxS, iterForm_boxS, hA _ (hresA u hu) fA hfA,
        hB _ (hresB u hu) fB hfB]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, map_add, map_add, ha, hb]
    | smul c a _ ha => rw [map_smul, map_smul, map_smul, ha]

  let K : Submodule ℂ (WO S T → ℂ) :=
    Submodule.span ℂ {m | ∃ u ∈ half S T (cA D e), ∃ g ∈ {g | IsThetaFunO ψ S T g}, m = heisL S T ψ u g - g}
  have hsm : ∀ u ∈ half S T (cA D e), ∀ g ∈ {g | IsThetaFunO ψ S T g}, ∃ k : ℕ, 0 < k ∧ heisL S T ψ (k • u) g = g := by
    intro u hu g hg
    obtain ⟨U, hU, h⟩ := (show IsThetaFunO ψ S T g from hg).level
    obtain ⟨k, hk, hkU⟩ := GlobalTheory.SplitScalar.exists_nsmul_mem U hU (infPart_half hε heε' hu)
    exact ⟨k, hk, h _ hkU (infPart_half hε heε' ((half S T (cA D e)).nsmul_mem hu k))⟩
  have hPK : ∀ m ∈ P, m ∈ K → l0 m = 0 := by
    intro m hmP hmK
    obtain ⟨ι, s, y, hy, ⟨i, hi, hi0⟩, h⟩ := GlobalTheory.HalfCoinv.exists_sum_eq_zero (heisL_half S T ψ c2)
      (GlobalTheory.SplitScalar.heisO_zero ψ S T) hsm hmK
    have h1 : l0 (∑ j ∈ s, heisL S T ψ (y j) m) = (s.card : ℂ) * l0 m := by
      rw [map_sum, Finset.sum_congr rfl (fun j _ => hl0P (y j) (hy j) m hmP), Finset.sum_const, nsmul_eq_mul]
    rw [h, map_zero] at h1
    have hc : (s.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨i, hi⟩)
    exact (mul_eq_zero.1 h1.symm).resolve_left hc

  let fP : (WO S T → ℂ) →ₗ.[ℂ] ℂ := ⟨P, l0 ∘ₗ P.subtype⟩
  let fK : (WO S T → ℂ) →ₗ.[ℂ] ℂ := ⟨K, 0⟩
  have H : ∀ (x : fP.domain) (y : fK.domain), (x : WO S T → ℂ) = y → fP x = fK y := by
    intro x y hxy
    change l0 (x : WO S T → ℂ) = 0
    exact hPK _ x.2 (hxy ▸ y.2)
  obtain ⟨L, hL⟩ := LinearMap.exists_extend (fP.sup fK H).toFun
  have hLv : ∀ z : (fP.sup fK H).domain, L z = (fP.sup fK H) z := fun z => LinearMap.congr_fun hL z
  refine ⟨L, fun u hu f hf => ?_, fun fA fB hfA hfB => ?_⟩
  · have huY : u ∈ half S T (cA D e) := (isHalf_iff S T).1 hu
    have hk : heisO ψ S T u f - f ∈ K := Submodule.subset_span ⟨u, huY, f, hf, rfl⟩
    have hz : heisO ψ S T u f - f ∈ (fP.sup fK H).domain := by
      rw [LinearPMap.domain_sup]; exact Submodule.mem_sup_right hk
    have : L (heisO ψ S T u f - f) = 0 := by
      refine (hLv ⟨_, hz⟩).trans ((LinearPMap.sup_apply H (0 : fP.domain) ⟨_, hk⟩ ⟨_, hz⟩ (by simp)).trans ?_)
      change l0 0 + 0 = 0
      simp
    rwa [map_sub, sub_eq_zero] at this
  · have hp : o.boxS T fA fB ∈ P := Submodule.subset_span ⟨fA, fB, hfA, hfB, rfl⟩
    have hz : o.boxS T fA fB ∈ (fP.sup fK H).domain := by
      rw [LinearPMap.domain_sup]; exact Submodule.mem_sup_left hp
    refine (hLv ⟨_, hz⟩).trans ((LinearPMap.sup_apply H ⟨_, hp⟩ (0 : fK.domain) ⟨_, hz⟩ (by simp)).trans ?_)
    change l0 (o.boxS T fA fB) + 0 = _
    rw [add_zero, hl0, iterForm_boxS]

end GlobalTheory.ProdForm
