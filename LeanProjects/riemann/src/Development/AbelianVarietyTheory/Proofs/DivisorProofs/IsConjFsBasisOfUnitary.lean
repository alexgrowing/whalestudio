import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic
open scoped ContDiff

namespace GlobalTheory

open CxPts

section Pull

variable {k k' : Type} [CommRing k] [CommRing k'] {Y Y' : Scheme.{0}} {p : Y ⟶ Sp k}
  {p' : Y' ⟶ Sp k'} {σ : k →+* ℂ} {σ' : k' →+* ℂ} {D D' : ℕ} {f : Y' ⟶ Y}
  {m : CxPts p' σ' → CxPts p σ}

namespace CxPts

theorem continuous_of_comp (hm : ∀ z, (m z).1 = z.1 ≫ f) : Continuous m :=
  continuous_induced_rng.2
    (((Points.continuous_comp f).comp continuous_subtype_val).congr fun z => (hm z).symm)

theorem mem_ptsIn_preimage (hm : ∀ z, (m z).1 = z.1 ≫ f) {U : Y.Opens} {z : CxPts p' σ'} :
    z ∈ ptsIn p' σ' (f ⁻¹ᵁ U) ↔ m z ∈ ptsIn p σ U := by
  change _ ↔ ⊤ ≤ (m z).1 ⁻¹ᵁ U
  rw [hm]
  rfl

theorem ev_of_comp (hm : ∀ z, (m z).1 = z.1 ≫ f) (U : Y.Opens) (g : Γ(Y, U)) (z : CxPts p' σ') :
    ev p σ U g (m z) = ev p' σ' (f ⁻¹ᵁ U) (f.app U g) z := by
  rw [ev, ev, hm]
  exact valR_comp _ _ _ _

end CxPts

theorem AlgChart.holo_map (hm : ∀ z, (m z).1 = z.1 ≫ f) (c' : AlgChart p' σ' D')
    (c : AlgChart p σ D) : DifferentiableOn ℂ (c.e ∘ m ∘ c'.e.symm)
      (c'.e.target ∩ c'.e.symm ⁻¹' (m ⁻¹' c.e.source)) :=
  differentiableOn_euclidean.2 fun a => ((c'.holo _ (f.app _ (c.x a))).mono fun _ hv =>
    ⟨hv.1, (mem_ptsIn_preimage hm).2 (c.source_subset hv.2)⟩).congr fun _ hv =>
      (c.apply_eq _ hv.2 a).trans (ev_of_comp hm _ _ _)

namespace AnRead

variable {R : AnRead p σ D} {S : Set (CxPts p σ)}

theorem exists_eventuallyEq_comp (hm : ∀ z, (m z).1 = z.1 ≫ f) (c : AlgChart p' σ' D') {v : V D'}
    (hv : v ∈ c.e.target) {E : Type*} (g : CxPts p σ → E) :
    ∃ i, m (c.e.symm v) ∈ (R.chart i).e.source ∧
      (g ∘ m) ∘ c.e.symm =ᶠ[𝓝 v] (g ∘ (R.chart i).e.symm) ∘ (R.chart i).e ∘ m ∘ c.e.symm := by
  obtain ⟨i, hi⟩ := R.cover (m (c.e.symm v))
  exact ⟨i, hi, eventually_of_mem ((isOpen_over c.e ((R.chart i).e.open_source.preimage
    (continuous_of_comp hm))).mem_nhds ⟨hv, hi⟩)
    fun w hw => (congrArg g ((R.chart i).e.left_inv hw.2)).symm⟩

theorem HoloOn.comp_map {g : CxPts p σ → ℂ} (h : R.HoloOn S g) (hS : IsOpen S)
    (hm : ∀ z, (m z).1 = z.1 ≫ f) (R' : AnRead p' σ' D') : R'.HoloOn (m ⁻¹' S) (g ∘ m) :=
  fun j v hv => by
  obtain ⟨i, hi, e⟩ := exists_eventuallyEq_comp (R := R) hm (R'.chart j) hv.1 g
  have ho := isOpen_over (R'.chart j).e ((R.chart i).e.open_source.preimage (continuous_of_comp hm))
  exact ((((h i).differentiableAt ((isOpen_over _ hS).mem_nhds (mem_over _ hi hv.2))).comp v
    (((R'.chart j).holo_map hm (R.chart i)).differentiableAt
      (ho.mem_nhds ⟨hv.1, hi⟩))).congr_of_eventuallyEq e).differentiableWithinAt

theorem SmoothOn.comp_map {g : CxPts p σ → ℝ} (h : R.SmoothOn S g) (hS : IsOpen S)
    (hm : ∀ z, (m z).1 = z.1 ≫ f) (R' : AnRead p' σ' D') : R'.SmoothOn (m ⁻¹' S) (g ∘ m) :=
  fun j v hv => by
  obtain ⟨i, hi, e⟩ := exists_eventuallyEq_comp (R := R) hm (R'.chart j) hv.1 g
  have ho := isOpen_over (R'.chart j).e ((R.chart i).e.open_source.preimage (continuous_of_comp hm))
  have ht : ContDiffOn ℝ ∞ ((R.chart i).e ∘ m ∘ (R'.chart j).e.symm) _ :=
    (contDiffOn_piLp 2).2 fun a => contDiffOn_real ho
      (differentiableOn_euclidean.1 ((R'.chart j).holo_map hm (R.chart i)) a)
  exact ((((h i).contDiffAt ((isOpen_over _ hS).mem_nhds (mem_over _ hi hv.2))).comp v
    (ht.contDiffAt (ho.mem_nhds ⟨hv.1, hi⟩))).congr_of_eventuallyEq e).contDiffWithinAt

end AnRead

namespace Weight

variable {R : AnRead p σ D} {B : LB Y} {φ : Weight p σ B}

theorem IsSmooth.linComb (h : φ.IsSmooth R) {κ : Type} [Fintype κ] (f : κ → (Y' ⟶ Y)) (ε : κ → ℤ)
    (m : κ → CxPts p' σ' → CxPts p σ) (hm : ∀ a z, (m a z).1 = z.1 ≫ f a) (R' : AnRead p' σ' D') :
    (φ.linComb f ε m hm).IsSmooth R' := fun j c =>
  ContDiffOn.sum (f := fun a v => (ε a : ℝ) * φ.φ (j a) (m a ((R'.chart c).e.symm v))) fun a _ =>
    contDiffOn_const.mul ((((h (j a)).comp_map (isOpen_ptsIn _) (hm a) R').mono
      fun z hz => mem_of_mem_linComb (hm · z) hz a) c)

theorem IsSmooth.pull (h : φ.IsSmooth R) {q : Y' ⟶ Sp k} (f : Y' ⟶ Y) (hf : f ≫ p = q)
    (R' : AnRead q σ D') : (φ.pull f hf).IsSmooth R' :=
  h.linComb _ _ _ _ R'

end Weight

end Pull

section Conj

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ σ' : k →+* ℂ} {A B : LB Y}

theorem CxPts.ev_conj {y : CxPts p σ} {y' : CxPts p σ'} (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1)
    {U : Y.Opens} (hy : y ∈ ptsIn p σ U) (g : Γ(Y, U)) :
    ev p σ' U g y' = starRingEnd ℂ (ev p σ U g y) := by
  rw [ev, h]
  exact valR_conjHomeomorph y.1 U hy g

theorem sum_normSq_vecMul_unitary {α : Type*} [Fintype α] [DecidableEq α] {U : Matrix α α ℂ}
    (hU : U ∈ Matrix.unitaryGroup α ℂ) (w : α → ℂ) :
    ∑ a, ‖Matrix.vecMul w U a‖ ^ 2 = ∑ a, ‖w a‖ ^ 2 := by
  have key (x : α → ℂ) : ((∑ a, ‖x a‖ ^ 2 : ℝ) : ℂ) = x ⬝ᵥ star x := by
    simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.mul_conj', Complex.ofReal_sum,
      Complex.ofReal_pow]
  apply Complex.ofReal_injective
  rw [key, key, Matrix.star_vecMul, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.1 hU, Matrix.vecMul_one]

namespace Weight

theorem isConj_fsBasis_of_unitary {α : Type*} [Fintype α] [DecidableEq α] (hB : B.IsLB)
    (b : α → B.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤) {M M' U : Matrix α α ℂ}
    (hM : M.det ≠ 0) (hM' : M'.det ≠ 0) (hU : U ∈ Matrix.unitaryGroup α ℂ)
    (e : M' = M.map (starRingEnd ℂ) * U) :
    (fsBasis p σ hB b hb M hM).IsConj (fsBasis p σ' hB b hb M' hM') := fun i y y' h hy => by
  rw [fsBasis_φ, fsBasis_φ]
  congr 1
  have hv (j : α) : valR y'.1 (B.U i) ((b j).f i) = starRingEnd ℂ (valR y.1 (B.U i) ((b j).f i)) :=
    CxPts.ev_conj h hy _
  have := sum_normSq_vecMul_unitary hU fun a =>
    starRingEnd ℂ (∑ j, M j a * valR y.1 (B.U i) ((b j).f i))
  simp only [RCLike.norm_conj] at this
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) this
  congr 2
  simp only [e, hv, Matrix.mul_apply, Matrix.map_apply, Matrix.vecMul, dotProduct, map_sum, map_mul,
    Finset.sum_mul]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

theorem isConj_fsBasis {α : Type*} [Fintype α] [DecidableEq α] (hB : B.IsLB)
    (b : α → B.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤) {M M' : Matrix α α ℂ}
    (hM : M.det ≠ 0) (hM' : M'.det ≠ 0) (e : M' = M.map (starRingEnd ℂ)) :
    (fsBasis p σ hB b hb M hM).IsConj (fsBasis p σ' hB b hb M' hM') :=
  isConj_fsBasis_of_unitary hB b hb hM hM' (one_mem _) (e.trans (Matrix.mul_one _).symm)

variable {φ : Weight p σ B} {φ' : Weight p σ' B}

theorem IsConj.tens {ψ : Weight p σ A} {ψ' : Weight p σ' A} (h' : ψ.IsConj ψ') (h : φ.IsConj φ') :
    (ψ.tens φ).IsConj (ψ'.tens φ') := fun c y y' e hy =>
  congrArg₂ (· + ·) (h' c.1 y y' e (mem_ptsIn_inf.1 hy).1) (h c.2 y y' e (mem_ptsIn_inf.1 hy).2)

theorem IsConj.dual (h : φ.IsConj φ') : φ.dual.IsConj φ'.dual := fun i y y' e hy =>
  congrArg Neg.neg (h i y y' e hy)

theorem IsConj.linComb (h : φ.IsConj φ') {k' : Type} [CommRing k'] {Y' : Scheme.{0}}
    {q : Y' ⟶ Sp k'} {τ τ' : k' →+* ℂ} {κ : Type} [Fintype κ] (f : κ → (Y' ⟶ Y)) (ε : κ → ℤ)
    (m : κ → CxPts q τ → CxPts p σ) (hm : ∀ a z, (m a z).1 = z.1 ≫ f a)
    (m' : κ → CxPts q τ' → CxPts p σ') (hm' : ∀ a z, (m' a z).1 = z.1 ≫ f a) :
    (φ.linComb f ε m hm).IsConj (φ'.linComb f ε m' hm') := fun j z z' e hz =>
  Finset.sum_congr rfl fun a _ => congrArg (_ * ·) (h (j a) _ _
    (by rw [hm, hm', e, Category.assoc]) (mem_of_mem_linComb (hm · z) hz a))

theorem IsConj.zpow (h : φ.IsConj φ') (n : ℤ) : (φ.zpow n).IsConj (φ'.zpow n) :=
  h.linComb _ _ _ _ _ _

theorem IsConj.pull (h : φ.IsConj φ') {Y' : Scheme.{0}} {q : Y' ⟶ Sp k} (f : Y' ⟶ Y)
    (hf : f ≫ p = q) : (φ.pull f hf).IsConj (φ'.pull f hf) :=
  h.linComb _ _ _ _ _ _

end Weight

end Conj

end GlobalTheory
