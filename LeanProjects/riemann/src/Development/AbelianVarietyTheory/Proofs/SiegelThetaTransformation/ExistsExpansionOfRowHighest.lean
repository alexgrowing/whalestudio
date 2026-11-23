import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NotIsIsoOfDefinite

section

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr

namespace GlobalTheory.Dict.CuspAny

theorem mem_minorSpan_of_rowHighest {T : Type} [Fintype T] {p q n : ℕ} {c : T → Fin p → ℕ}
    {c' : T → Fin q → ℕ} {P : Harm.Poly ℂ T p q (Fin n)} (hP : P ∈ Harm.rowHighest ℂ c c') :
    P ∈ GaussGauge.minorSpan (Fin n) c c' := by
  classical
  have h : p + q ≤ n + (p + q) := Nat.le_add_left _ _
  let A : Matrix (Fin n) (Fin (n + (p + q))) ℂ :=
    (1 : Matrix _ _ ℂ).submatrix (Fin.castAdd (p + q)) id
  have hA : A * Aᵀ = 1 := by
    ext i j
    simp [A, Matrix.mul_apply, Matrix.one_apply, eq_comm]
  have h1 : Harm.colSubst (fun _ : T => A) (fun _ => Aᵀ) P ∈ GaussGauge.minorSpan _ c c' :=
    GaussGauge.orbitSpan_le_minorSpan h c c'
      (Harm.rowHighest_eq_orbitSpan h c c' ℂ ▸ Harm.colSubst_mem_rowHighest (fun _ => hA) hP)
  have h2 : Harm.colSubst (fun _ : T => Aᵀ) (fun _ => A)
      (Harm.colSubst (fun _ : T => A) (fun _ => Aᵀ) P) = P := by
    rw [← AlgHom.comp_apply, Harm.colSubst_comp]
    simp only [hA]
    rw [Harm.colSubst_one, AlgHom.id_apply]
  rw [← h2]
  refine (Submodule.span_le (p := (GaussGauge.minorSpan (Fin n) c c').comap
    (Harm.colSubst (fun _ : T => Aᵀ) (fun _ => A)).toLinearMap)).2 ?_ h1
  rintro _ ⟨x, rfl⟩
  change Harm.colSubst (fun _ : T => Aᵀ) (fun _ => A) (Harm.minorProd c c' x.1 x.2) ∈
    GaussGauge.minorSpan (Fin n) c c'
  rw [Harm.colSubst_minorProd]
  exact GaussGauge.minorProd_mem_minorSpan _ _ _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {g : ℕ}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
  {q0 : ℕ} (hr : X.p0 + q0 = r) {n : ℕ} {c : X.Ψ → Fin q0 → ℕ} {c' : X.Ψ → Fin X.p0 → ℕ}

theorem exists_expansion_of_rowHighest (hs : IsSympl X bas) (hn : Even n)
    (hc : ∃ τ, (∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ c τ i) ∨
      ∃ i : Fin X.p0, i.val + 1 = X.p0 ∧ 1 ≤ c' τ i)
    (a b : Fin n → Fin g → ℝ) {P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)}
    (hP : P ∈ Harm.rowHighest ℂ c c') {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) :
    ∃ (A : (Fin n → Fin g → ℤ) → ℂ) (ν : (Fin n → Fin g → ℤ) → X.Ψ → ℝ),
      (Summable fun m => ‖A m‖) ∧
      (∀ s : X.Ψ → ℝ, HasSum (fun m => A m * cexp (4 * Real.pi * I * ∑ τ, (ν m τ : ℂ) * s τ))
        (thFr X hr bas idx n a b P (X.flow ξ (fun τ => (s τ : ℂ)) x))) ∧
      ∀ m, A m ≠ 0 → ν m ≠ 0 := by
  obtain ⟨bas', S, hs', hA⟩ := exists_isAdapted hs hξ.2.1
  obtain ⟨a', b', κ, -, -, hκ⟩ := exists_thFr_eq_mul idx hr hs hs' hn a b
  obtain ⟨A, hA1, hA2, hA3⟩ := hA.exists_expansion hr idx hs' hξ n a' b'
    (Harm.isHarmonic_of_mem_rowHighest hP) (mem_minorSpan_of_rowHighest hP) hc hx
  refine ⟨fun m => κ * A m, _, ?_, fun s => ?_,
    fun m hm h0 => hm (mul_eq_zero_of_right κ (hA3 m h0))⟩
  · simpa only [norm_mul] using hA1.mul_left ‖κ‖
  · have hxs := (FlowCoefficientBounds.flow_real X hξ hx s 0).1
    rw [hκ P _ hxs]
    simpa only [mul_assoc] using (hA2 _ hxs).mul_left κ

theorem mem_SS_of_eq_sum_thFr {J : Type} (s : Finset J) (t : J → ℂ) (a b : J → Fin n → Fin g → ℝ)
    {P : J → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)} {Q : Frame X.Ψ r → ℂ} (hs : IsSympl X bas)
    (hn : Even n)
    (hc : ∃ τ, (∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ c τ i) ∨
      ∃ i : Fin X.p0, i.val + 1 = X.p0 ∧ 1 ≤ c' τ i)
    (hP : ∀ j ∈ s, P j ∈ Harm.rowHighest ℂ c c')
    (hQ : ∀ x ∈ X.dom, Q x = ∑ j ∈ s, t j * thFr X hr bas idx n (a j) (b j) (P j) x)
    (hΓ : ∀ ga ∈ X.Γ, ∀ x ∈ X.dom, Q (lact ga x) = X.χ (wtOf X hr c c' n) ga * Q x) :
    Q ∈ X.SS (wtOf X hr c c' n) := by
  have hsec := isSec_of_eq_sum_thFr idx hr s t a b hs hP hQ hΓ
  refine FJZero.mem_SS_of_isModerate X _ Q hsec
    (isModerate_of_eq_sum_thFr idx hr s t a b hs hn hP hQ) fun ξ hξ x hx => ?_
  choose A ν h1 h2 h3 using fun j : s =>
    exists_expansion_of_rowHighest idx hr hs hn hc (a j) (b j) (hP j j.2) hξ hx
  have h4 (j : s) : Summable fun m => ‖t j * A j m‖ := by
    simpa only [norm_mul] using (h1 j).mul_left ‖t j‖
  refine FJZero.fj_eq_zero_of_isSec X _ Q hsec hξ hx
    (fun p : s × (Fin n → Fin g → ℤ) => t p.1 * A p.1 p.2)
    (hasSum_prod_of_fintype h4 fun j => (h4 j).of_norm.hasSum).1 (fun p => ν p.1 p.2)
    (fun u => ?_) 0 fun p hp => h3 _ _ (right_ne_zero_of_mul hp)
  rw [hQ _ (FlowCoefficientBounds.flow_real X hξ hx u 0).1, ← Finset.sum_coe_sort]
  refine (hasSum_prod_of_fintype
    (f := fun (j : s) m => t j * A j m * cexp (4 * Real.pi * I * ∑ τ, (ν j m τ : ℂ) * u τ))
    (fun j => ?_) fun j => ?_).2
  · refine (h4 j).congr fun m => ?_
    have h := FJZero.norm_expo (ν j m) u
    rw [FJZero.expo] at h
    rw [norm_mul (t j * A j m), h, mul_one]
  · simpa only [mul_assoc] using (h2 j u).mul_left (t j)

end GlobalTheory.Dict.CuspAny

end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.CuspAny

theorem mem_SS_of_eq_thP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ((∃ τ, ∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ k τ i) ∨ q0 = 0) → ∀ φ : TF n g, IsSB φ → ∀ P ∈ Harm.rowHighest ℂ k k', ∀ Q : Frame X.Ψ r → ℂ, (∀ x ∈ X.dom, Q x = thP X hr bas idx φ P x) → (∀ ga ∈ X.Γ, ∀ x ∈ X.dom, Q (lact ga x) = X.χ (wtOf X hr k k' n) ga * Q x) → Q ∈ X.SS (wtOf X hr k k' n) := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn k k' hk φ hφ P hP Q hQ hΓ
  obtain ⟨m, a, b, t, h⟩ := (GlobalTheory.SW.CharLink.harmonicTheta_eq_sum_thetaCharacteristic E r X g q0 hr bas idx n hs hn).2 φ hφ
  rcases hk with ⟨τ, hτ⟩ | h0
  · exact CuspAny.mem_SS_of_eq_sum_thFr idx hr Finset.univ t (fun j k i => (a j k i : ℝ))
      (fun j k i => (b j k i : ℝ)) (P := fun _ => P) hs hn ⟨τ, Or.inl hτ⟩ (fun _ _ => hP)
      (fun x hx => (hQ x hx).trans (h P x hx)) hΓ
  · exact ThFr.mem_SS_of_eq_sum_thFr idx hr Finset.univ t (fun j k i => (a j k i : ℝ))
      (fun j k i => (b j k i : ℝ)) (P := fun _ => P) hs hn
      (Or.inr (CuspClass.not_isIso_of_definite X (by omega))) (fun _ _ => hP)
      (fun x hx => (hQ x hx).trans (h P x hx)) hΓ

end GlobalTheory.Dict.CuspAny
