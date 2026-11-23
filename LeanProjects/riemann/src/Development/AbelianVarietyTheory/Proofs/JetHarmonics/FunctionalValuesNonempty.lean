import Mathlib
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Formalism.SharpRestriction.Divisibility.WeightFamilies
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.TraceFormDualSystem
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPosHermOfPositive

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LeastExponentCompare

open NumberField Formalism.MainNotions.ModuliIntegralCharts
open GlobalTheory.IndefiniteRowSideFullHecke.TraceFormDualSystem (bar balancedForms quad IsPosSemidef IsPosDef Exponent pairing pairingValues IsPhiC)
open GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace (IsBalancedSpace evalSum)
open GlobalTheory.IndefiniteRowSideFullHecke.PairingFromOuterAgreement (outer IsPosHerm)

variable {E : Type} [Field E] [NumberField E]

theorem finite_projective_iff (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] :
    (Module.Finite (𝓞 E) Y ∧ Module.Projective (𝓞 E) Y) ↔ (Module.Finite ℤ Y ∧ Module.Free ℤ Y) := by
  constructor
  · rintro ⟨hf, hp⟩
    have hfin : Module.Finite ℤ Y := Module.Finite.trans (𝓞 E) Y
    have hfl : Module.Flat ℤ Y := Module.Flat.trans ℤ (𝓞 E) Y
    exact ⟨hfin, inferInstance⟩
  · rintro ⟨hf, hfr⟩
    exact ⟨Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) Y, GlobalTheory.PointStepCompare.projective_of_free E⟩

variable [IsCMField E] {cj : E → E}

def IsConj (cj : E → E) : Prop := ∀ c : 𝓞 E, cj c = IsCMField.complexConj E (c : E)

variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

theorem isBalancedSpace (h : IsConj cj) : IsBalancedSpace E (SymB cj Y) := by
  intro β
  change ((∀ a b, β a b = β b a) ∧ ∀ (c c' : 𝓞 E), (c' : E) = cj (c : E) → ∀ a b, β (c • a) b = β a (c' • b)) ↔ _
  constructor
  · rintro ⟨hs, hb⟩
    refine ⟨hs, fun a x y => hb a _ ?_ x y⟩
    rw [h a, IsCMField.coe_ringOfIntegersComplexConj]
  · rintro ⟨hs, hb⟩
    refine ⟨hs, fun c c' hc x y => ?_⟩

    have hc' : c' = IsCMField.ringOfIntegersComplexConj E c := by
      apply RingOfIntegers.ext
      rw [hc, h c, IsCMField.coe_ringOfIntegersComplexConj]
    rw [hc']
    exact hb c x y

variable (Y) in

def formsEquiv (h : IsConj cj) : SymB cj Y ≃ₗ[ℝ] balancedForms E Y where
  toFun β := ⟨AddMonoidHom.mk' (fun x => ((β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) x).toAddMonoidHom)
      (fun x x' => by ext y; simp),
    ((isBalancedSpace h _).1 β.2).1, ((isBalancedSpace h _).1 β.2).2⟩
  invFun β := ⟨LinearMap.mk₂ ℤ (fun x y => β.1 x y) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp) (fun _ _ _ => by simp),
    (isBalancedSpace h _).2 ⟨β.2.1, β.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def Admissible (l : SymB cj Y →ₗ[ℝ] ℝ) : Prop :=
  (∀ β : SymB cj Y, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l β = z) ∧
    ∀ β : SymB cj Y, (∀ a, 0 ≤ (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → β ≠ 0 → 0 < l β

def functionalValues (b : SymB cj Y) : Set ℝ := {x | ∃ l : SymB cj Y →ₗ[ℝ] ℝ, Admissible l ∧ x = l b}

def exponentOfOuter {n : ℕ} (x x' : Fin n → Y) (hl : IsPosHerm E (outer E x x')) : Exponent E Y where
  form := AddMonoidHom.mk' (fun y => AddMonoidHom.mk' (fun y' => outer E x x' y y')
      (fun y' y'' => by simp [outer, mul_add, Finset.sum_add_distrib]))
    (fun y y'' => by ext y'; simp [outer, add_mul, Finset.sum_add_distrib])
  smul_left a y y' := by simp [outer, Finset.mul_sum, mul_assoc]
  hermitian := hl.1
  pos τ y hy := hl.2 y hy τ

variable [Module.Finite (𝓞 E) Y] [Module.Projective (𝓞 E) Y]

theorem exists_outer (e : Exponent E Y) : ∃ (n : ℕ) (x x' : Fin n → Y),
    (∀ y y', e.form y y' = outer E x x' y y') ∧ IsPosHerm E (outer E x x') := by
  obtain ⟨D⟩ := GlobalTheory.IndefiniteRowSideFullHecke.TraceFormDualSystem.nonempty_dualSystem E Y

  let g : Fin (D.n * D.n) ≃ Fin D.n × Fin D.n := finProdFinEquiv.symm
  let x : Fin (D.n * D.n) → Y := fun k => e.form (D.y (g k).1) (D.y (g k).2) • D.e (g k).1
  let x' : Fin (D.n * D.n) → Y := fun k => D.e (g k).2
  have hfo : ∀ y y', e.form y y' = outer E x x' y y' := by
    intro y y'
    rw [D.form_eq e y y']
    exact (Equiv.sum_comp g (fun p => y (e.form (D.y p.1) (D.y p.2) • D.e p.1) * bar E (y' (D.e p.2)))).symm
  refine ⟨D.n * D.n, x, x', hfo, ?_, ?_⟩
  · intro η η'
    rw [← hfo, ← hfo]
    exact e.hermitian η η'
  · intro η hη τ
    rw [← hfo]
    exact e.pos τ η hη

theorem exists_exponent (h : IsConj cj) {l : SymB cj Y →ₗ[ℝ] ℝ} (hl : Admissible l) :
    ∃ e : Exponent E Y, ∀ β, l β = pairing e (formsEquiv Y h β) := by
  obtain ⟨_, _⟩ := (finite_projective_iff (E := E) Y).1 ⟨inferInstance, inferInstance⟩
  obtain ⟨n, x, x', hpos, hval⟩ :=
    GlobalTheory.PointStepCompare.exists_exponent E (isBalancedSpace (Y := Y) h) l hl.1 hl.2
  refine ⟨exponentOfOuter x x' hpos, fun β => ?_⟩
  rw [hval β, GlobalTheory.IndefiniteRowSideFullHecke.TraceFormDualSystem.pairing_of_sum _ _ x x' (fun y y' => rfl)]
  rfl

theorem exists_functional (h : IsConj cj) {w : 𝓞 E} (hw : w + bar E w = 1) (e : Exponent E Y) :
    ∃ l : SymB cj Y →ₗ[ℝ] ℝ, Admissible l ∧ ∀ β, l β = pairing e (formsEquiv Y h β) := by
  obtain ⟨_, _⟩ := (finite_projective_iff (E := E) Y).1 ⟨inferInstance, inferInstance⟩
  obtain ⟨n, x, x', hfo, hpos⟩ := exists_outer e
  obtain ⟨l, hi, hp, hl⟩ := GlobalTheory.PointStepCompare.exists_functional E (isBalancedSpace (Y := Y) h) hw hpos
  refine ⟨l, ⟨hi, hp⟩, fun β => ?_⟩
  rw [hl β, GlobalTheory.IndefiniteRowSideFullHecke.TraceFormDualSystem.pairing_of_sum e _ x x' hfo]
  rfl

theorem exponent_ext (h : IsConj cj) {e e' : Exponent E Y}
    (hp : ∀ β, pairing e (formsEquiv Y h β) = pairing e' (formsEquiv Y h β)) : e = e' := by

  have hdiag : ∀ (f : Exponent E Y) (η : Module.Dual (𝓞 E) Y) (τ : E →+* ℂ),
      pairing f (formsEquiv Y h ⟨GlobalTheory.PointStepCompare.rankOne E η τ,
        (isBalancedSpace h _).2 (GlobalTheory.PointStepCompare.rankOne_balanced E η τ)⟩) = (τ (f.form η η : E)).re / 2 := by
    intro f η τ
    obtain ⟨n, x, x', hfo, -⟩ := exists_outer f
    rw [GlobalTheory.IndefiniteRowSideFullHecke.TraceFormDualSystem.pairing_of_sum f _ x x' hfo, hfo, GlobalTheory.PointStepCompare.re_outer E x x' η τ]
    rfl

  have him : ∀ (f : Exponent E Y) (η : Module.Dual (𝓞 E) Y) (τ : E →+* ℂ), (τ (f.form η η : E)).im = 0 := by
    intro f η τ
    have h2 : τ (f.form η η : E) = starRingEnd ℂ (τ (f.form η η : E)) := by
      conv_lhs => rw [f.hermitian η η]
      exact GlobalTheory.PointStepCompare.emb_bar E τ _
    have h3 := congrArg Complex.im h2
    rw [Complex.conj_im] at h3
    linarith
  have hself : ∀ η, e.form η η = e'.form η η := by
    intro η
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply RingOfIntegers.ext
    apply τ.injective
    apply Complex.ext
    · have h1 := hp ⟨GlobalTheory.PointStepCompare.rankOne E η τ,
        (isBalancedSpace h _).2 (GlobalTheory.PointStepCompare.rankOne_balanced E η τ)⟩
      rw [hdiag, hdiag] at h1
      linarith
    · rw [him e, him e']

  obtain ⟨a, ha⟩ : ∃ a : 𝓞 E, bar E a ≠ a := by
    by_contra hcon
    push Not at hcon
    apply IsCMField.complexConj_ne_one (K := E)
    apply AlgEquiv.ext
    intro z
    obtain ⟨u, v, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) z
    have hu : ∀ u : 𝓞 E, IsCMField.complexConj E (algebraMap (𝓞 E) E u) = algebraMap (𝓞 E) E u := by
      intro u
      have := congrArg (fun t : 𝓞 E => (t : E)) (hcon u)
      simpa using this
    rw [map_div₀, hu, hu, AlgEquiv.one_apply]

  have hform : ∀ y y', e.form y y' = e'.form y y' := by
    intro y y'
    have expand : ∀ (f : Exponent E Y) (c : 𝓞 E), f.form (y + c • y') (y + c • y') =
        f.form y y + c * bar E c * f.form y' y' + bar E c * f.form y y' + c * bar E (f.form y y') := by
      intro f c
      simp only [map_add, AddMonoidHom.add_apply, f.smul_left, f.smul_right]
      rw [f.hermitian y y']
      ring
    have E1 := (expand e 1).symm.trans ((hself _).trans (expand e' 1))
    have E2 := (expand e a).symm.trans ((hself _).trans (expand e' a))
    rw [hself y, hself y'] at E1 E2
    simp only [map_one, one_mul, mul_one] at E1
    have hprod : (a - bar E a) * (e.form y y' - e'.form y y') = 0 := by
      linear_combination a * E1 - E2
    rcases mul_eq_zero.1 hprod with h0 | h0
    · exact absurd (sub_eq_zero.1 h0).symm ha
    · exact sub_eq_zero.1 h0
  cases e
  cases e'
  congr 1
  exact AddMonoidHom.ext fun y => AddMonoidHom.ext fun y' => hform y y'

def exponentEquiv (h : IsConj cj) {w : 𝓞 E} (hw : w + bar E w = 1) :
    Exponent E Y ≃ {l : SymB cj Y →ₗ[ℝ] ℝ // Admissible l} :=
  Equiv.ofBijective
    (fun e => ⟨(exists_functional h hw e).choose, (exists_functional h hw e).choose_spec.1⟩)
    ⟨fun e e' he => exponent_ext h fun β => by
      rw [← (exists_functional h hw e).choose_spec.2, ← (exists_functional h hw e').choose_spec.2]
      exact LinearMap.congr_fun (congrArg Subtype.val he) β,
    fun l => by
      obtain ⟨e, he⟩ := exists_exponent h l.2
      exact ⟨e, Subtype.ext (LinearMap.ext fun β =>
        ((exists_functional h hw e).choose_spec.2 β).trans (he β).symm)⟩⟩

theorem functionalValues_nonempty (h : IsConj cj) (b : SymB cj Y) : (functionalValues b).Nonempty := by
  obtain ⟨_, _⟩ := (finite_projective_iff (E := E) Y).1 ⟨inferInstance, inferInstance⟩
  obtain ⟨l, hi, hp⟩ := GlobalTheory.PointStepCompare.exists_admissible E (isBalancedSpace (Y := Y) h)
  exact ⟨l b, l, ⟨hi, hp⟩, rfl⟩

section Host

open Formalism.BasicNotions

end Host

end GlobalTheory.LeastExponentCompare

end
