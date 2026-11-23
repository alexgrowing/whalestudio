import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormPlus
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HomExtOfGeometric
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsContraction
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove

namespace GlobalTheory.FiniteOrderConst

open GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient

theorem isHolTo_of_eqOn {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} {B : Set V}
    {y y' : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (e : ∀ b ∈ B, y' b = y b) : IsHolTo B y' := by
  intro U f
  have hs : {b ∈ B | ⊤ ≤ y' b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} :=
    Set.ext fun b => and_congr_right fun hb => by rw [e b hb]
  rw [hs]
  exact ⟨(h U f).1, (h U f).2.congr fun b hb => by rw [e b hb.1]⟩

theorem valAt'_top {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (f : Γ(X, ⊤)) : valAt' y ⊤ f = fnAt y f := by
  rw [valAt', dif_pos (show (⊤ : (Sp ℂ).Opens) ≤ y ⁻¹ᵁ ⊤ from le_rfl), valAt, fnAt]
  have : y.appLE ⊤ ⊤ le_rfl = y.appTop := Scheme.Hom.appLE_eq_app y
  exact congrArg (fun q => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (q.hom f)) this

theorem fnAt_eq_of_pow {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} {B : Set V}
    {a : V → (Sp ℂ ⟶ X)} (hB : IsPreconnected B) (h : IsHolTo B a) (f : Γ(X, ⊤)) {N : ℕ} (hN : 0 < N)
    (hp : ∀ b ∈ B, fnAt (a b) f ^ N = 1) {b b' : V} (hb : b ∈ B) (hb' : b' ∈ B) : fnAt (a b) f = fnAt (a b') f := by
  have hc : ContinuousOn (fun b => fnAt (a b) f) B := by
    have := (h ⊤ f).2.continuousOn
    simp only [valAt'_top] at this
    exact this.mono fun b hb => ⟨hb, le_rfl⟩
  have hfin : {z : ℂ | z ^ N = 1}.Finite :=
    (Polynomial.nthRoots N (1 : ℂ)).toFinset.finite_toSet.subset fun z hz => by
      simpa [Polynomial.mem_nthRoots hN] using hz
  exact hB.constant_of_mapsTo hfin.isDiscrete hc hp hb hb'

theorem const_on_period_space : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (f : Rul Xo c), f ∈ sec Xo c 0 0 → (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y y' : FrPt Xo c K), y'.x = y.x → evR Xo c f y' = evR Xo c f y) → (∃ N : ℕ, 0 < N ∧ ∀ y : FrPt Xo c (CAt σ), evR Xo c f y ^ N = 1) → ∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H Dw.p Dw.q ty → ∀ (i : Fin F.n) (P P' : (F.Di i).La →+ (Fin g → ℂ)) (y y' : FrPt Xo c (CAt σ)), IsPeriod (F.Di i) ty P → IsPeriod (F.Di i) ty P' → y.x = F.u i P → y'.x = F.u i P' → evR Xo c f y = evR Xo c f y' := by
  classical
  rintro E _ _ _ H Dw l Xo c σ f hf hfree ⟨N, hN, hp⟩ g ty F hty i P P' y y' hP hP' hy hy'
  let _ : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.FrameFreeRule.exists_fn E H Dw l Xo c f hf hfree
  obtain ⟨m, B, Q, -, hB, hconv, h0, hQ0, hQ, hall⟩ := GlobalTheory.PeriodChart.period_chart E H (F.Di i) g ty
    (by rw [(F.sig i).1, (F.sig i).2]; exact hty) P hP
  obtain ⟨b, ⟨hb, h, hh⟩, -⟩ := hall P' hP'
  have hbP : F.u i (Q b) = F.u i P' :=
    (F.fibre i (Q b) P' (hQ.1 b hb) hP').2 ⟨LinearEquiv.refl _ _, h, fun _ _ => rfl, fun a _ => ⟨0, by simp⟩,
      fun a => ⟨0, by simp⟩, hh⟩
  have hex : ∀ t, ∃ z : FrPt Xo c ℂ, t ∈ B → z.x = F.u i (Q t) := fun t => by
    by_cases ht : t ∈ B
    · obtain ⟨z, hz⟩ := GlobalTheory.NonIntegralFrameExample.exists_framed (c := c) (S := ℂ) (F.u i (Q t)) (F.over_σ i _ (hQ.1 t ht))
      exact ⟨z, fun _ => hz⟩
    · exact ⟨y, fun h => absurd h ht⟩
  choose z hz using hex
  have hhol : IsHolTo B fun t => basePt (z t) :=
    GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback _ _)
      (isHolTo_of_eqOn (F.hol i m B Q hB hQ).1 fun t ht => (pullback.lift_fst _ _ _).trans (hz t ht))
      (isHolTo_of_eqOn (GlobalTheory.HolFibre.isHolTo_const hB (spMap σ)) fun t _ => pullback.lift_snd _ _ _)
  have key := fnAt_eq_of_pow hconv.isPreconnected hhol f₀ hN
    (fun t _ => by rw [← hf₀ ℂ (z t)]; exact hp (z t)) h0 hb
  rw [← hf₀ ℂ, ← hf₀ ℂ] at key
  exact (hfree ℂ (z 0) y (hy.trans (by rw [hz 0 h0, hQ0]))).trans
    (key.trans (hfree ℂ y' (z b) ((hz b hb).trans (hbP.trans hy'.symm))))

end GlobalTheory.FiniteOrderConst
