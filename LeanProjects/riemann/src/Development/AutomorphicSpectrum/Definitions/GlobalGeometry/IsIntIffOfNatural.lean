import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFiniteExtAllModelsUniformised
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TypingsAgree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ref

open NumberField IsDedekindDomain IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

def periodForm {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {t : SAB H (Sp V)}
    (P : PELUnif (maximalIdeal V) t) {ϖ : V} (hϖ : Irreducible ϖ) {Q : P.D.toPre.X → ℤ}
    (hQ : QForm.IsQ P.D.toPre ϖ Q) : SymB (cjE E) P.D.toPre.X :=
  ⟨LinearMap.mk₂ ℤ (fun a b => (QForm.bHom hϖ P.D hQ a b : ℝ)) (by simp) (by simp) (by simp) (by simp),
    fun a b => by
      simp only [LinearMap.mk₂_apply, QForm.bHom_apply, QForm.bOf_comm P.D a b],
    fun x x' hx a b => by
      have hx' : x' = H.bar x := RingOfIntegers.ext (hx.trans (cjE_coe H x))
      subst hx'
      letI := H.starRing
      simp only [LinearMap.mk₂_apply, QForm.bHom_apply]
      exact congrArg _ (GlobalTheory.TorsionFactsCompare.bOf_balance P.D hϖ P.oD hQ x a b)⟩

theorem exists_isPhiAt {la : HeightOneSpectrum (𝓞 c.F)} {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ}
    (ho : OverLa la T.V io e) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1)
    (P : PELUnif (maximalIdeal T.V) I.G) (hP : P.TorsionIso) : ∃ t, IsPhiAt Xo c la T io y t := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  choose Q hQ using QForm.exists_QVal hϖ P.D
  have he : (e : ℝ) ≠ 0 := by exact_mod_cast ho.1.ne'
  have h2 : ∀ a, (periodForm P hϖ hQ : P.D.toPre.X →ₗ[ℤ] P.D.toPre.X →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ) := fun a => by
    show ((QForm.bOf P.D.toPre Q a a : ℤ) : ℝ) = _
    rw [← QForm.two_Q_eq hϖ P.D hQ]; push_cast; rfl
  refine ⟨phiC (cjE E) (periodForm P hϖ hQ) / e, e, ho, I, P, ϖ, Q, periodForm P hϖ hQ, hP, hϖ, hQ,
    fun _ _ => rfl, h2, fun a => ?_, by field_simp⟩
  rw [h2]
  by_cases ha : a = 0
  · rw [ha, QForm.Q_zero hϖ P.D hQ]; simp
  · have : (1 : ℝ) ≤ Q a := by exact_mod_cast QForm.Q_pos hϖ P.D hQ ha
    linarith

theorem nonempty_intData {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) : Nonempty (IntData Xo c T io y.1) := by
  obtain ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, θ, h5, w1, w2, σ, s1, θ2, r1, r2, k1, k2, k3, k4⟩ := y.2.2
  exact ⟨⟨G, t', m1, m2, ub, h1, h2, h3, h4, θ, h5, w1, w2, σ, s1, θ2, r1, r2, k1, k2, k3, k4⟩⟩

variable (Xo c) in

theorem unifAll_holds : UnifAll Xo c := by
  intro la T io e ho y hy
  obtain ⟨T', φV, φ, -, z, hi, hl, hf, hc, -, -, hz, hm, hU⟩ :=
    GlobalTheory.IntegralPull.exists_finite_ext_all_models_uniformised Xo c T io y e la ho hy
  obtain ⟨r, hr, hv⟩ := GlobalTheory.IntegralPull.exists_index (V' := T'.V) φV φ (RingHom.congr_fun hc)
  obtain ⟨I⟩ := nonempty_intData z
  obtain ⟨P, hP⟩ := hU I
  obtain ⟨t, ht⟩ := exists_isPhiAt (ho.bc φ hr hv) z I P hP
  exact ⟨T', φV, φ, r, z, t, ⟨hi, hl, hf, hc, hr, hv⟩, hm, hz, ht⟩

end GlobalTheory.CompanionTheory.Ar.Ref
