import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FibreIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanNormSquareExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisBaseChangeLocalAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisLocalizationAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisOfLocalizationsAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactificationOpenOfClosed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeterminantSectionRule
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicEmbeddingValuationNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SemiabelianActionPullbackWeight

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.FlatRow

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

theorem eigStable {S : Scheme.{0}} (T : SAB H S) (c : Coeff l) : EigStable T c := by
  intro R R' _ _ g j x τ m v v' hv hv'
  obtain ⟨t, ⟨n⟩⟩ := exists_sab x T
  obtain ⟨t', ⟨n'⟩⟩ := exists_sab (spMap g) t
  obtain ⟨n'', e''⟩ := TraitDataOfIntrinsic.map_comp n' n rfl
  choose w hw using fun i => exists_lift n.cart (v i)
  choose w' hw' _ using fun i => existsUnique_isVecOver n'.cart.1 (w i)
  have hb := ((fibre_iff n.cart hw).2 n.act _).2 hv
  refine ((fibre_iff n''.cart (v := w') fun i => ?_).2 n''.act _).1 (GlobalTheory.T.isLieEigenbasis_of_localizations_atPrime E H R' t' _ m w' fun q _ => ?_)
  · change _ ≫ n''.φ = _
    rw [e'', ← Category.assoc, hw' i, Category.assoc, hw, hv']
  let p := q.comap g
  let gp : Localization.AtPrime p →+* Localization.AtPrime q := Localization.localRingHom p q g rfl
  have hg : gp.comp (algebraMap R _) = (algebraMap R' _).comp g :=
    RingHom.ext fun z => Localization.localRingHom_to_map p q g rfl z
  obtain ⟨tq, ⟨nq⟩⟩ := exists_sab (spMap (algebraMap R' (Localization.AtPrime q))) t'
  obtain ⟨tp, ⟨np⟩⟩ := exists_sab (spMap (algebraMap R (Localization.AtPrime p))) t
  obtain ⟨k, ek⟩ := TraitDataOfIntrinsic.map_comp nq n' rfl
  obtain ⟨k', ek'⟩ := TraitDataOfIntrinsic.map_cancel (g := spMap gp) k np
    (by rw [spMap_comp_spMap, spMap_comp_spMap, hg])
  choose wq hq _ using fun i => existsUnique_isVecOver nq.cart.1 (w' i)
  choose wp hp _ using fun i => existsUnique_isVecOver np.cart.1 (w i)
  refine ⟨tq, nq, wq, hq, ?_⟩
  have h₁ := GlobalTheory.T.isLieEigenbasis_localization_atPrime E H R p t tp np _ m w wp hb hp
  have h₂ := GlobalTheory.T.isLieEigenbasis_baseChange_localAlgebra E H l c _ _ ((algebraMap R _).comp j) gp tp tq k' τ m wp wq h₁ fun i =>
    EllComp.isVecOver_cancel np.cart.1 k'.cart.1 (hp i)
      (by rw [← ek', ek, hg]; exact EllComp.isVecOver_comp (hw' i) (hq i))
  rwa [← RingHom.comp_assoc, hg] at h₂

variable {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {U : (Xo.XF c).Opens} {τ : E →+* ℂ}

theorem isIso_fst (Y : Model Xo c (RingHom.id c.F)) : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
  have : IsIso (spMap (RingHom.id c.F)) := by
    rw [show spMap (RingHom.id c.F) = 𝟙 _ from Spec.map_id _]; infer_instance
  infer_instance

theorem isNormal_genFibre (Y : Model Xo c (RingHom.id c.F)) : Geo.Tor.IsNormalScheme (FramedFlatCoordinates.genFibre Y) := by
  intro x
  have := isIso_fst Y
  let e := (asIso ((pullback.fst Y.s (spMap (RingHom.id c.F))).stalkMap x)).commRingCatIsoToRingEquiv
  obtain ⟨h₁, h₂⟩ := Y.normal (pullback.fst Y.s (spMap (RingHom.id c.F)) x)
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem comb_one {R : Type} [CommRing R] {t : SAB H (Sp R)} {m : ℕ} {v : Fin m → (epsR R ⟶ t.G)}
    (hv : ∀ i, IsTangent (v i)) (i : Fin m) : IsLieComb ((1 : Matrix (Fin m) (Fin m) R) i) v (v i) := by
  have : (1 : Matrix (Fin m) (Fin m) R) i = Pi.single i 1 := by
    ext k; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [this]
  exact (LieComb.lieComb_algebra _ _ m v hv).2.2.2.1 i

section Algebraic

variable {L : Type} [Field L] [NumberField L] {j : c.F →+* L} {a : FramedFlatCoordinates.Framed Y U τ L j} {y : Sp L ⟶ Xo.XF c}
  {sig : FramedFlatCoordinates.Rule Y U τ}

end Algebraic

theorem exists_prime_mem {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 K) ∈ w.asIdeal := by
  have : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  have := w.isMaximal
  let _ := Ideal.Quotient.field w.asIdeal
  refine ⟨ringChar (𝓞 K ⧸ w.asIdeal), CharP.char_is_prime (𝓞 K ⧸ w.asIdeal) _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

def flatVal_vw (Dw : Datum H) (c : Coeff l) (τ : E →+* ℂ) {K : Type} [Field K] [NumberField K] (em : c.F →+* K)
    (𝔓 : HeightOneSpectrum (𝓞 K)) (ℓ : ℕ) (x : ℝ) : ℝ :=
  vAdd 𝔓 (ℓ : K) * x - Dw.q * (EigenvectorLieDegree.ordTwist H (EigenvectorLieDegree.embIn c em τ) 𝔓 : ℝ)

theorem IsSqNorm.pos {sig : FramedFlatCoordinates.Rule Y U τ} (hsig : FramedFlatCoordinates.VanishesNowhere sig) {s : c.F →+* ℂ} {κ : ℝ}
    (h : IsSqNorm sig s κ) : 0 < κ := by
  obtain ⟨a, _, _, _, _, _, _, _, _, _, _, -, -, -, -, -, h₁, h₂, rfl⟩ := h
  exact mul_pos (pow_pos (norm_pos_iff.2 (hsig _ _ a).ne_zero) 2) (div_pos h₁ h₂)

section Ties

variable {D : D7} {X : DivX D} (Lc : placeRankTwoOne.Loc D X) {j : ℕ} {Z : X.Comp j} {τ : D.what₂.Tau}
  {H : Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {Y : Model Xo c (RingHom.id c.F)} {U : (Xo.XF c).Opens} {em : c.F →+* D.what₂.LL}
  (Φ : FramedFlatCoordinates.sections Y U (DV.tauEmb D τ) →ₛₗ[em] X.geo.Fn (X.Yv j Z))

def SectionTie : Prop :=
  Function.Injective Φ ∧ (∀ sig, Φ sig ∈ X.geo.H0 (X.Yv j Z) (X.Lw j Z (placeRankTwoOne.detW D τ))) ∧
    ∀ sig, FramedFlatCoordinates.VanishesNowhere sig.1 → (Φ sig)⁻¹ ∈ X.geo.H0 (X.Yv j Z) (-(X.Lw j Z (placeRankTwoOne.detW D τ)))

def MetricTie : Prop :=
  ∀ sig, FramedFlatCoordinates.VanishesNowhere sig.1 → ∀ σ y,
    X.geo.pn (X.Yv j Z) σ _ (Lc.metH j Z τ σ) (X.geo.cx (X.Yv j Z) σ (Φ sig)) y ∈
      closure {κ | IsSqNorm sig.1 (σ.comp em) κ}

def LatticeTie : Prop :=
  ∀ sig, FramedFlatCoordinates.VanishesNowhere sig.1 → ∀ w y,
    ∃ (ℓ : ℕ) (_ : Fact ℓ.Prime) (K : Type) (_ : Field K) (i : K →+* ℂ_[ℓ]) (ψ : D.what₂.LL →+* K) (x : ℝ),
      (∀ a : 𝓞 D.what₂.LL, a ∈ (D.plEq w).asIdeal ↔ ‖i (ψ (a : D.what₂.LL))‖ < 1) ∧ IsValue sig.1 i (ψ.comp em) x ∧
      Lc.vF j Z τ w (Φ sig) y = flatVal_vw Dw c (DV.tauEmb D τ) em (D.plEq w) ℓ x

def ModuliTie : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ (Z : X.Comp j) (τ : D.what₂.Tau),
    ∃ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
      (Y : Model Xo c (RingHom.id c.F)) (U : (Xo.XF c).Opens) (em : c.F →+* D.what₂.LL)
      (Φ : FramedFlatCoordinates.sections Y U (DV.tauEmb D τ) →ₛₗ[em] X.geo.Fn (X.Yv j Z)),
      H.d = D.host.d ∧ (H.rt : D.host.E) = D.host.sqrtMinusD ∧ DV.tauEmb D τ (H.rt : D.host.E) = H.rt0 ∧
      IsDatW D j Dw ∧ l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1 ∧ (∀ z, D.what₂.embLL (em z) = (z : ℂ)) ∧
      EigenbasisGramSquares.IsGeomComponent Xo c U ∧ SectionTie Φ ∧ MetricTie Lc Φ ∧ LatticeTie Lc Φ

def TiedClass (𝒞 : FamClass) : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → ∃ XF : placeRankTwoOne.LocF Fm, ∀ x hx i, ModuliTie (XF x hx i)

end Ties

end GlobalTheory.FlatRow
