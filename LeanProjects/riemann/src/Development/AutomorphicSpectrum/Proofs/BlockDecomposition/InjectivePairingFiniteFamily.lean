import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRs
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WSum.Sep

variable {D : D7} {r : ℕ}

theorem theta_incA {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (x : D.host.E) :
    θ τ (infPart D (incA D x)) = tauE D τ x := by
  have h : infPart D (incA D x) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] x := by
    simp [infPart, incA, inclR]
  rw [h]
  exact (hθ τ).1 x

theorem pairF_eq {θ : InfFam D} (hθ : IsInfFam θ) (α : D.host.F) (a β : HermE D r) :
    pairF θ α a β =
      -∑ τ, (tauE D τ (algebraMap D.host.F D.host.E α * Matrix.trace (β.1 * a.1))).re := by
  unfold pairF lam
  simp only [← map_mul, theta_incA hθ]

def hermQ (D : D7) (r : ℕ) : Submodule ℚ (Matrix (Fin r) (Fin r) D.host.E) where
  carrier := {b | (b.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = b}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    ext i j
    have h1 := congrFun (congrFun ha i) j
    have h2 := congrFun (congrFun hb i) j
    simp only [Matrix.transpose_apply, Matrix.map_apply] at h1 h2 ⊢
    simp only [Matrix.add_apply, map_add, h1, h2]
  zero_mem' := by
    ext i j
    simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at *
    ext i j
    have h1 := congrFun (congrFun ha i) j
    simp only [Matrix.transpose_apply, Matrix.map_apply] at h1 ⊢
    simp only [Matrix.smul_apply, map_rat_smul, h1]

theorem tau_nonempty (D : D7) : Nonempty D.what₂.Tau := by
  obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace D.host.F) := inferInstance
  obtain ⟨τ, -⟩ := (GlobalTheory.CMTypePlaces.places_bijective D).2 w
  exact ⟨τ⟩

theorem mem_hermQ {b : Matrix (Fin r) (Fin r) D.host.E} :
    b ∈ hermQ D r ↔ ∀ i j, D.sp.cm.sig (b j i) = b i j := by
  constructor
  · intro h i j
    exact congrFun (congrFun h i) j
  · intro h
    exact Matrix.ext fun i j => h i j

def formH (α : D.host.F) (δ : Matrix (Fin r) (Fin r) D.host.E) : hermQ D r →+ ℝ :=
  AddMonoidHom.mk'
    (fun a => ∑ τ, (tauE D τ (algebraMap D.host.F D.host.E α * Matrix.trace (δ * a.1))).re)
    (by
      intro a b
      simp only [Submodule.coe_add, mul_add, Matrix.trace_add, map_add, Complex.add_re,
        Finset.sum_add_distrib])

theorem formH_apply (α : D.host.F) (δ : Matrix (Fin r) (Fin r) D.host.E) (a : hermQ D r) :
    formH α δ a =
      ∑ τ, (tauE D τ (algebraMap D.host.F D.host.E α * Matrix.trace (δ * a.1))).re := rfl

theorem formH_eq_zero {d : ℕ} (b : Module.Basis (Fin d) ℚ (hermQ D r)) {α : D.host.F}
    {δ : Matrix (Fin r) (Fin r) D.host.E} (h : ∀ k, formH α δ (b k) = 0) (a : hermQ D r) :
    formH α δ a = 0 := by
  have e : (formH α δ).toRatLinearMap = 0 := b.ext (fun k => by simpa using h k)
  simpa using LinearMap.congr_fun e a

theorem formH_sub_left (α : D.host.F) (b b' : Matrix (Fin r) (Fin r) D.host.E) (a : hermQ D r) :
    formH α (b - b') a = formH α b a - formH α b' a := by
  simp only [formH_apply, sub_mul, Matrix.trace_sub, mul_sub, map_sub, Complex.sub_re,
    Finset.sum_sub_distrib]

theorem pairF_eq_formH {θ : InfFam D} (hθ : IsInfFam θ) (α : D.host.F) (β : HermE D r)
    (a : hermQ D r) : pairF θ α ⟨a.1, a.2⟩ β = -formH α β.1 a :=
  pairF_eq hθ α ⟨a.1, a.2⟩ β

theorem formH_sub {θ : InfFam D} (hθ : IsInfFam θ) (α : D.host.F) (β β' : HermE D r)
    (a : hermQ D r) :
    formH α (β.1 - β'.1) a = pairF θ α ⟨a.1, a.2⟩ β' - pairF θ α ⟨a.1, a.2⟩ β := by
  have e := pairF_eq_formH hθ α β a
  have e' := pairF_eq_formH hθ α β' a
  have e'' := formH_sub_left α β.1 β'.1 a
  linarith

theorem trace_sq_ne_zero {δ : Matrix (Fin r) (Fin r) D.host.E} (hδ : δ ∈ hermQ D r) (h0 : δ ≠ 0) :
    Matrix.trace (δ * δ) ≠ 0 := by
  intro hn
  obtain ⟨τ⟩ := tau_nonempty D
  have hm := mem_hermQ.1 hδ
  have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
  have hc : ∀ i j, tauE D τ (δ j i) = starRingEnd ℂ (tauE D τ (δ i j)) := by
    intro i j
    rw [← hm j i]
    exact hcm.2.2.2 _ _
  have hs : ((∑ i, ∑ j, Complex.normSq (tauE D τ (δ i j)) : ℝ) : ℂ) = 0 := by
    have e : tauE D τ (Matrix.trace (δ * δ)) =
        ((∑ i, ∑ j, Complex.normSq (tauE D τ (δ i j)) : ℝ) : ℂ) := by
      push_cast
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, map_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hc i j, Complex.mul_conj]
    rw [← e, hn, map_zero]
  have hs' : (∑ i, ∑ j, Complex.normSq (tauE D τ (δ i j))) = 0 := by exact_mod_cast hs
  apply h0
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)).1 hs' i (Finset.mem_univ i)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => Complex.normSq_nonneg _)).1 h1 j (Finset.mem_univ j)
  have h3 : tauE D τ (δ i j) = 0 := Complex.normSq_eq_zero.1 h2
  simpa using h3

theorem sig_trace_sq {δ : Matrix (Fin r) (Fin r) D.host.E} (hδ : δ ∈ hermQ D r) :
    D.sp.cm.sig (Matrix.trace (δ * δ)) = Matrix.trace (δ * δ) := by
  have hm := mem_hermQ.1 hδ
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, map_mul, hm]
  rw [Finset.sum_comm]

theorem inv_smul_mem {δ : Matrix (Fin r) (Fin r) D.host.E} (hδ : δ ∈ hermQ D r) {x : D.host.E}
    (hx : D.sp.cm.sig x = x) : x⁻¹ • δ ∈ hermQ D r := by
  have hm := mem_hermQ.1 hδ
  refine mem_hermQ.2 fun i j => ?_
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, hx, hm]

theorem exists_separating : ∀ (D : D7) (r : ℕ) (θ : InfFam D), IsInfFam θ → ∀ α : D.host.F, α ≠ 0 →
    ∃ (d : ℕ) (a : Fin d → HermE D r),
      Function.Injective (fun (β : HermE D r) (k : Fin d) => pairF θ α (a k) β) := by
  intro D r θ hθ α hα
  let b := Module.finBasis ℚ (hermQ D r)
  refine ⟨_, fun k => ⟨(b k).1, (b k).2⟩, ?_⟩
  intro β β' h
  by_contra hne
  have hδ : β.1 - β'.1 ∈ hermQ D r :=
    sub_mem (show β.1 ∈ hermQ D r from β.2) (show β'.1 ∈ hermQ D r from β'.2)
  have hδ0 : β.1 - β'.1 ≠ 0 := sub_ne_zero.2 fun e => hne (Subtype.ext e)
  have hz : ∀ a, formH α (β.1 - β'.1) a = 0 := by
    refine formH_eq_zero b fun k => ?_
    rw [formH_sub hθ]
    have := congrFun h k
    exact sub_eq_zero.2 this.symm
  set δ := β.1 - β'.1 with hδdef
  have hn := trace_sq_ne_zero hδ hδ0
  have hαE : algebraMap D.host.F D.host.E α ≠ 0 := by
    simpa using hα
  set x := algebraMap D.host.F D.host.E α * Matrix.trace (δ * δ) with hx
  have hx0 : x ≠ 0 := mul_ne_zero hαE hn
  have hxs : D.sp.cm.sig x = x := by
    rw [hx, map_mul, sig_trace_sq hδ, AlgHom.commutes]
  have hv := hz ⟨x⁻¹ • δ, inv_smul_mem hδ hxs⟩
  rw [formH_apply] at hv
  have h1 : algebraMap D.host.F D.host.E α * Matrix.trace (δ * (x⁻¹ • δ)) = 1 := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← mul_assoc, mul_comm _ x⁻¹, mul_assoc,
      ← hx, inv_mul_cancel₀ hx0]
  simp only [h1, map_one, Complex.one_re, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hv
  haveI := tau_nonempty D
  have : (Fintype.card D.what₂.Tau : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact this hv

end GlobalTheory.CompanionTheory.WSum.Sep
