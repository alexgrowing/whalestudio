import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMajorantFlags
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodCmPointAtCmBasisFrame
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FramePolynomialEquivariantAndNeZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj GlobalTheory.LamT

namespace GlobalTheory.CMDetect

theorem exists_half_max {α : Type} (s : Set α) (f : α → ℝ) (C : ℝ) (hC : ∀ x ∈ s, f x ≤ C) {x₁ : α} (hx₁ : x₁ ∈ s)
    (hpos : 0 < f x₁) : ∃ z ∈ s, (∀ x ∈ s, f x ≤ 2 * f z) ∧ 0 < f z := by
  have hb : BddAbove (f '' s) := ⟨C, by rintro _ ⟨x, hx, rfl⟩; exact hC x hx⟩
  have hle : ∀ x ∈ s, f x ≤ sSup (f '' s) := fun x hx => le_csSup hb ⟨x, hx, rfl⟩
  have h1 := hle x₁ hx₁
  obtain ⟨_, ⟨z, hz, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (s := f '' s) ⟨_, x₁, hx₁, rfl⟩
    (show sSup (f '' s) / 2 < sSup (f '' s) by linarith)
  exact ⟨z, hz, fun x hx => by linarith [hle x hx], by linarith⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_maj_lower (X : FD.DataX E r) (hr : 0 < r) {z : FD.Frame X.Ψ r} (hz : z ∈ X.dom) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ ∀ v ∈ X.L', v ≠ 0 → s ^ 2 ≤ ∑ τ, X.maj z τ (FD.Data.emb τ.1 v) := by
  have hnn : ∀ τ v, 0 ≤ X.maj z τ v := fun τ v => FD.MajorantConjugateTransfer.maj_nonneg X.toData hz τ v
  have hc : ∀ τ, X.c τ = X.k0 := fun τ => by
    unfold FD.Data.c
    rw [X.ξ0_abs τ]
    ring
  have hk := X.minWeight_pos
  have hN : (0 : ℝ) < X.NC := by exact_mod_cast X.NC_pos
  have hla : 0 < X.firstMinimumSq z := Real.sqrt_pos.1 (AR.Up.ModeHalfC.first_minimum_pos X.toData hz (by
    by_contra h
    push Not at h
    have h1 : Submodule.span E (X.Λ : Set (Fin r → E)) = ⊥ := by
      rw [Submodule.span_eq_bot]
      exact h
    rw [X.Λ_span] at h1
    have : (Pi.single ⟨0, hr⟩ (1 : E) : Fin r → E) ∈ (⊤ : Submodule E (Fin r → E)) := Submodule.mem_top
    rw [h1, Submodule.mem_bot] at this
    have := congrFun this ⟨0, hr⟩
    simp at this))
  have hm : 0 < X.firstMinimumSq z / (X.k0 * (X.NC : ℝ) ^ 2) := by positivity
  refine ⟨Real.sqrt (min 1 (X.firstMinimumSq z / (X.k0 * (X.NC : ℝ) ^ 2))), Real.sqrt_pos.2 (lt_min one_pos hm),
    Real.sqrt_le_one.2 (min_le_left _ _), fun v hv hv0 => ?_⟩
  rw [Real.sq_sqrt (lt_min one_pos hm).le]
  refine (min_le_right _ _).trans ?_
  rw [div_le_iff₀ (by positivity)]
  have hb : BddBelow {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj z τ (FD.Data.emb τ.1 v)} := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, -, -, rfl⟩
    exact Finset.sum_nonneg fun τ _ => mul_nonneg (by rw [hc]; exact hk.le) (hnn τ _)
  have hne : (X.NC : E) • v ≠ 0 := smul_ne_zero (by exact_mod_cast X.NC_pos.ne') hv0
  have h1 : X.firstMinimumSq z ≤ ∑ τ, X.c τ * X.maj z τ (FD.Data.emb τ.1 ((X.NC : E) • v)) :=
    csInf_le hb ⟨_, X.NC_sub v hv, hne, rfl⟩
  refine h1.trans (le_of_eq ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e : FD.Data.emb τ.1 ((X.NC : E) • v) = (((X.NC : ℝ) : ℂ)) • FD.Data.emb τ.1 v := by
    funext a
    simp [FD.Data.emb]
  rw [e, FD.FlowMajorantFlags.maj_smul X.toData hz, hc]
  ring

theorem exists_cm_frame (X : FD.DataX E r) (Y : FD.Data E r) (hX : X.toData = Y) (hr : 0 < r) (la : FD.Wt Y.Ψ r)
    (P : FD.Frame Y.Ψ r → ℂ) (hP : Y.IsBddSec la P) {x₁ : FD.Frame Y.Ψ r} (hx₁ : x₁ ∈ Y.dom) (hne : P x₁ ≠ 0) :
    ∃ (La : ℝ) (x : FD.Frame Y.Ψ r) (lam : Fin r → Fin r → E), x ∈ Y.dom ∧ FD.LamBasis X La (hX ▸ x) lam ∧
      P x ≠ 0 := by
  subst hX
  obtain ⟨hS, C, hC⟩ := hP
  have hpos : 0 < X.pnorm la P x₁ := by
    have hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)), FD.dmin X.Gm x₁ τ i ≠ 0 := fun τ i h => by
      have := (hx₁ τ).2 i
      rw [h, Complex.zero_re, mul_zero] at this
      exact lt_irrefl _ this
    refine mul_pos (norm_pos_iff.2 hne) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
      Real.rpow_pos_of_pos ?_ _)
    exact norm_pos_iff.2 (div_ne_zero (hd τ _) (hd τ _))
  obtain ⟨z, hz, hhalf, hzpos⟩ := exists_half_max X.dom (X.pnorm la P) C hC hx₁ hpos
  obtain ⟨s, hs0, hs1, hs⟩ := exists_maj_lower X hr hz
  obtain ⟨x, lam, hx, hB, hPx, -⟩ := Formalism.L2.Pj.FundamentalDomainD5.t41H_statement r X la P z s (max 1 (∑ τ, X.spread la τ)) hS hz
    hhalf hzpos (le_max_right _ _) (le_max_left _ _) hr hs0 hs1 hs
  exact ⟨_, x, lam, hx, hB, hPx⟩

theorem exists_good_cmPt_frPoly_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r), IsUnf U → 0 < r → (∀ k, ∃ (Xx : FD.DataX E r) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), Xx.toData = U.X k ∧ 𝔄 ≠ 0 ∧ Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u}) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, F ≠ 0 → (∀ k, (U.X k).IsBddSec (laU U a n k) (rdU U F k)) → ∃ (z : CMPt Xo c) (La : ℝ), z.Good (Module.finrank ℚ E / 2) La ∧ ∀ G, IsFrPoly F z.y G → G ≠ 0 := by
  intro E _ _ _ H Dw l Xo c _ hstar r U hU hr hdat a n F hF hF0 hbdd
  classical
  have hinj := (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ r
    (Formalism.L2.PjFree.Unf.ofPj U) ((Formalism.L2.PjFree.isUnf_ofPj U).2 hU) a n).2 F hF
  have hex : ∃ k, ∃ x ∈ (U.X k).dom, rdU U F k x ≠ 0 := by
    by_contra h
    push Not at h
    exact hF0 (hinj h)
  obtain ⟨k, x₁, hx₁, hne₁⟩ := hex
  obtain ⟨Xx, 𝔄, hX, h𝔄, hΛ⟩ := hdat k
  obtain ⟨La, x, lam, hx, hB, hne⟩ := exists_cm_frame Xx (U.X k) hX hr _ _ (hbdd k) hx₁ hne₁
  obtain ⟨z, σ₁, hz, hzx⟩ := GlobalTheory.LamT.exists_good_cmPt_at_frame E H Dw l Xo c hstar r U hU hr k ⟨x, hx⟩ Xx hX 𝔄 h𝔄 hΛ
    La lam hB
  have hev : evR Xo c F (U.un k ⟨x, hx⟩) ≠ 0 := by
    intro h0
    apply hne
    change (if h : x ∈ (U.X k).dom then toC (evR Xo c F (U.un k ⟨x, h⟩)) else 0) = 0
    rw [dif_pos hx]
    exact h0
  exact ⟨z, La, hz, fun G hG =>
    (GlobalTheory.LamT.isFrPoly_equiv_and_ne_zero E H Dw l Xo c z.K z.y a n F hF G hG).2 _ σ₁ _ hzx hev⟩

end GlobalTheory.CMDetect
