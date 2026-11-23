import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BarTorsionGenerators

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Objects

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

def IsJetLevel (l : Level H) (α : 𝓞 E) (q : ℕ) : Prop :=
  α ∈ Algebra.adjoin ℤ {H.w0} ∧ α * H.bar α = (q : 𝓞 E) ∧ Odd q ∧ q ∣ l.M ∧
    (∃ u ∈ Algebra.adjoin ℤ {H.w0}, ∃ v ∈ Algebra.adjoin ℤ {H.w0}, u * α + v * H.bar α = 1) ∧
    l.Mb ≤ Ideal.span {H.bar α}

def IsBarTorsion (Dw : Datum H) (l : Level H) (α : 𝓞 E) {n : ℕ} (x : Fin n → Dw.La) : Prop :=
  ∀ b, H.bar α • x b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)

variable {Dw : Datum H} {l : Level H}

def gens (Xo : Moduli Dw l) (c : Coeff l) (nab : NabV Xo c) (α : 𝓞 E) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    Set (Rul Xo c) :=
  {f | ∃ (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F),
    IsBarTorsion Dw l α x ∧ P ∈ harmA c a n ∧ IsThRule Xo c nab x P f}

def NoCommonZero (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (s : Set (Rul Xo c)) : Prop :=
  ∀ y : FrPt Xo c (CAt σ), ∃ f ∈ s, evR Xo c f y ≠ 0

theorem gens_subset_thGen (Xo : Moduli Dw l) (c : Coeff l) (nab : NabV Xo c) (α : 𝓞 E)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : gens Xo c nab α a n ⊆ thGen Xo c nab a n := by
  rintro f ⟨x, P, -, hP, hf⟩
  exact ⟨x, P, hP, hf⟩

theorem gens_eq_thGen (Xo : Moduli Dw l) (c : Coeff l) (nab : NabV Xo c) {α : 𝓞 E}
    (hα : l.Mb = Ideal.span {H.bar α}) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    gens Xo c nab α a n = thGen Xo c nab a n := by
  refine Set.Subset.antisymm (gens_subset_thGen Xo c nab α a n) ?_
  rintro f ⟨x, P, hP, hf⟩
  refine ⟨x, P, fun b => Submodule.smul_mem_smul ?_ Submodule.mem_top, hP, hf⟩
  rw [hα]; exact Ideal.subset_span rfl

theorem NoCommonZero.rd {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {s : Set (Rul Xo c)}
    (h : NoCommonZero Xo c σ s) {r : ℕ} (U : Unf Xo c σ r) (k : U.Comp) (x) (hx : x ∈ (U.X k).dom) :
    ∃ f ∈ s, rdU U f k x ≠ 0 := by
  obtain ⟨f, hf, h0⟩ := h (U.un k ⟨x, hx⟩)
  refine ⟨f, hf, ?_⟩
  show (open Classical in if h : x ∈ (U.X k).dom then toC (evR Xo c f (U.un k ⟨x, h⟩)) else 0) ≠ 0
  rw [dif_pos hx]; exact h0

end Objects

def LongNoCommonZero : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (α : 𝓞 D.host.E) (q : ℕ),
    D.R.r ≤ w.n → IsJetLevel T.Q.l α q → 4 * WeightAlgebra.DF w + 4 ≤ q →
    ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ →
      NoCommonZero (T.Q.Xo j) T.Q.c σ (gens (T.Q.Xo j) T.Q.c (T.nab j) α (wtA w) w.n)

def LongNoCommonZeroFree : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (nab : NabV Xo c),
    (∃ _ : StarRing (𝓞 E), IsNab Xo c nab) →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (α : 𝓞 E) (q : ℕ),
      (∀ τ, Antitone fun i => a (τ, i)) → Dw.p + Dw.q ≤ n → IsJetLevel l α q → 4 * Formalism.L2.Pj.DF Dw a + 4 ≤ q →
      ∀ σ : c.F →+* ℂ, GoodEmb c σ → NoCommonZero Xo c σ (gens Xo c nab α a n)

theorem LongNoCommonZero.full (hA : LongNoCommonZero) (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j)
    (w : WeightFamilies.Wt D j) (α : 𝓞 D.host.E) (hn : D.R.r ≤ w.n) (hα : IsJetLevel T.Q.l α T.Q.l.M)
    (hD : 4 * WeightAlgebra.DF w + 4 ≤ T.Q.l.M) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ) (k) (x)
    (hx : x ∈ ((T.U j σ).X k).dom) : ∃ f ∈ T.th j w, rdU (T.U j σ) f k x ≠ 0 := by
  obtain ⟨f, hf, h0⟩ := (hA D T h j hj w α _ hn hα hD σ hσ).rd (T.U j σ) k x hx
  exact ⟨f, gens_subset_thGen _ _ _ _ _ _ hf, h0⟩

end GlobalTheory.IndefiniteRowSideFullHecke.BarTorsionGenerators
