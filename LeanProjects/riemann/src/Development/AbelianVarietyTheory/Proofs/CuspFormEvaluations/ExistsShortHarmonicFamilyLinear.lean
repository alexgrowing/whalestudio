import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TraceHermNondegenerate
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SpanGridPerpVecEqOrbitSpanOfLe
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.L1NormRowBlockLeadingMinorProductLe
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PushLettersIntCastOfIsHomogeneous

open NumberField ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.TB (perpVec)

namespace GlobalTheory.Harm

open GlobalTheory.MvPoly GlobalTheory.GridSize

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

variable (E n) in

noncomputable def conjVec : (Fin n → E) →ₛₗ[((IsCMField.ringOfIntegersComplexConj E).toRingEquiv :
    𝓞 E →+* 𝓞 E)] (Fin n → E) where
  toFun v k := cc (v k)
  map_add' v w := funext fun k => map_add (IsCMField.complexConj E) (v k) (w k)
  map_smul' a v := funext fun k => map_mul (IsCMField.complexConj E) (a : E) (v k)

@[simp] theorem conjVec_apply (v : Fin n → E) (k : Fin n) : conjVec E n v k = cc (v k) := rfl

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in

@[simp] theorem _root_.GlobalTheory.Harm.conjVec_conjVec (v : Fin n → E) :
    _root_.GlobalTheory.Harm.conjVec E n (_root_.GlobalTheory.Harm.conjVec E n v) = v := by
  funext k
  exact _root_.GlobalTheory.TraceDualMin.cc_cc (v k)

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in

theorem _root_.GlobalTheory.Harm.herm_conjVec (v w : Fin n → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 (_root_.GlobalTheory.Harm.conjVec E n v) (_root_.GlobalTheory.Harm.conjVec E n w)
      = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 w v := by
  simp only [_root_.GlobalTheory.DualFamily.herm_one_eq, _root_.GlobalTheory.Harm.conjVec_apply,
    _root_.GlobalTheory.TraceDualMin.cc_cc]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

noncomputable def conjLattice (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) :=
  Λ.map (conjVec E n)

variable {Λ : Submodule (𝓞 E) (Fin n → E)}

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
variable {Λ : Submodule (𝓞 E) (Fin n → E)} in

theorem _root_.GlobalTheory.Harm.mem_conjLattice {v : Fin n → E} :
    v ∈ _root_.GlobalTheory.Harm.conjLattice Λ ↔ _root_.GlobalTheory.Harm.conjVec E n v ∈ Λ := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [_root_.GlobalTheory.Harm.conjVec_conjVec]
    exact hw
  · intro hv
    exact ⟨_, hv, _root_.GlobalTheory.Harm.conjVec_conjVec v⟩

@[simp] theorem conjLattice_conjLattice : conjLattice (conjLattice Λ) = Λ := by
  ext v; rw [mem_conjLattice, mem_conjLattice, conjVec_conjVec]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
variable {Λ : Submodule (𝓞 E) (Fin n → E)} in

theorem _root_.GlobalTheory.Harm.conjLattice_selfDual (hfg : Λ.FG)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) → x ∈ Λ) :
    (_root_.GlobalTheory.Harm.conjLattice Λ).FG ∧
      (∀ x ∈ _root_.GlobalTheory.Harm.conjLattice Λ, ∀ y ∈ _root_.GlobalTheory.Harm.conjLattice Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) ∧
      ∀ x, (∀ y ∈ _root_.GlobalTheory.Harm.conjLattice Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) →
        x ∈ _root_.GlobalTheory.Harm.conjLattice Λ := by
  refine ⟨hfg.map _, ?_, ?_⟩
  · intro x hx y hy
    rw [_root_.GlobalTheory.Harm.mem_conjLattice] at hx hy
    have h := hint _ hy _ hx
    rwa [_root_.GlobalTheory.Harm.herm_conjVec] at h
  · intro x hx
    rw [_root_.GlobalTheory.Harm.mem_conjLattice]
    refine hdual _ fun y hy => ?_
    have hy' : _root_.GlobalTheory.Harm.conjVec E n y ∈ _root_.GlobalTheory.Harm.conjLattice Λ := by
      rw [_root_.GlobalTheory.Harm.mem_conjLattice, _root_.GlobalTheory.Harm.conjVec_conjVec]
      exact hy
    have h := _root_.GlobalTheory.TraceDualMin.isIntegral_cc (hx _ hy')
    rw [← _root_.GlobalTheory.DualFamily.herm_one_symm] at h
    have h2 := _root_.GlobalTheory.Harm.herm_conjVec (E := E) x (_root_.GlobalTheory.Harm.conjVec E n y)
    rw [_root_.GlobalTheory.Harm.conjVec_conjVec] at h2
    rw [h2]
    exact h

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
variable {Λ : Submodule (𝓞 E) (Fin n → E)} in
omit [IsCMField E] in

theorem _root_.GlobalTheory.Harm.one_le_rdE : 1 ≤ _root_.ReciprocityTheory.ChartRestriction.G.FD.rdE E := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.rdE _root_.ReciprocityTheory.ChartRestriction.G.FD.dE
  apply Real.one_le_rpow _ (by positivity)
  have h : (discr E : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero E
  have h' : (1 : ℝ) ≤ |((discr E : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (discr_ne_zero E)
  exact_mod_cast h'

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
variable {Λ : Submodule (𝓞 E) (Fin n → E)} in

theorem _root_.GlobalTheory.Harm.one_le_fdeg : 1 ≤ _root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E := by
  have h := _root_.GlobalTheory.ShortVectors.finrank_eq (E := E)
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  omega

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
variable {Λ : Submodule (𝓞 E) (Fin n → E)} in

theorem _root_.GlobalTheory.Harm.one_le_add_of_one_le_typeDegree {T : Type*} [Fintype T] {p q : ℕ}
    {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ} (ha : 1 ≤ _root_.GlobalTheory.Harm.typeDegree c c') :
    1 ≤ p + q := by
  by_contra hpq
  obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := by omega
  simp [_root_.GlobalTheory.Harm.typeDegree, _root_.GlobalTheory.Harm.partSize] at ha

variable (E n) in

noncomputable def hermPairing : (Fin n → E) →ₗ[E] ((Fin n → E) → E) where
  toFun x y := herm 1 x y
  map_add' x x' := funext fun y => by simp [herm_one_eq_sum, add_mul, Finset.sum_add_distrib]
  map_smul' r x := funext fun y => TraceDualMin.herm_smul_left r x y

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
variable {Λ : Submodule (𝓞 E) (Fin n → E)} in

theorem _root_.GlobalTheory.Harm.perpVec_hermPairing_mem
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) {p : ℕ}
    {e e' : Fin p → Fin n → E} {g : Fin n → E} (he : ∀ a, e a ∈ Λ) (he' : ∀ a, e' a ∈ Λ)
    (hg : g ∈ Λ) : _root_.ReciprocityTheory.ChartRestriction.G.TB.perpVec (_root_.GlobalTheory.Harm.hermPairing E n) e e' g ∈ Λ := by
  classical
  unfold _root_.ReciprocityTheory.ChartRestriction.G.TB.perpVec
  set M := _root_.ReciprocityTheory.ChartRestriction.G.TB.hMat (_root_.GlobalTheory.Harm.hermPairing E n) e e' with hM
  have hMint : ∀ i j, IsIntegral ℤ (M i j) := fun i j => hint _ (he' i) _ (he j)
  let Mo : Matrix (Fin p) (Fin p) (𝓞 E) := fun i j => ⟨M i j, hMint i j⟩
  have hMo : M = (algebraMap (𝓞 E) E).mapMatrix Mo := by ext i j; rfl
  have key : ∀ (c : 𝓞 E) (x : Fin n → E), x ∈ Λ → ((c : E) • x) ∈ Λ :=
    fun c x hx => Λ.smul_mem c hx
  apply Λ.sub_mem
  · rw [hMo, ← RingHom.map_det]
    exact key _ _ hg
  · refine Λ.sum_mem fun a _ => Λ.sum_mem fun a' _ => ?_
    have hga : IsIntegral ℤ (_root_.GlobalTheory.Harm.hermPairing E n g (e a)) := hint _ hg _ (he a)
    rw [hMo, ← RingHom.map_adjugate]
    have hc : (algebraMap (𝓞 E) E).mapMatrix Mo.adjugate a a'
        * _root_.GlobalTheory.Harm.hermPairing E n g (e a)
        = ((Mo.adjugate a a' * ⟨_, hga⟩ : 𝓞 E) : E) := by
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
      rfl
    rw [hc]
    exact key _ _ (he' a')

end GlobalTheory.Harm
