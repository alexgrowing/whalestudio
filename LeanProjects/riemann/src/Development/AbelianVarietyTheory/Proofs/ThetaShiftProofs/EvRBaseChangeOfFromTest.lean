import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcWitnessExistence.EnlargeCf
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcWitnessExistence.PolyFr
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.FrameCut
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions

namespace GlobalTheory.ArcQ

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_frBor_of_isReduced (hL : GlobalTheory.Reg.EvLaws Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {F : Rul Xo c} (hF : F ∈ sec Xo c a n) {S : Type} [CommRing S] [Algebra c.F S] [IsReduced S]
    (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S) (h : FrBor t y y') :
    evR Xo c F y' = wchar (ex Dw a n) t * evR Xo c F y := by
  rw [← sub_eq_zero]
  apply IsReduced.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro P hP
  let φ : S →ₐ[c.F] S ⧸ P := Ideal.Quotient.mkₐ c.F P
  obtain ⟨z, hz⟩ := hL.bc _ _ φ y
  obtain ⟨z', hz'⟩ := hL.bc _ _ φ y'
  obtain ⟨g, hg1, hg2, hg⟩ := ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c S).2.2.2 t y y').1 h
  have hc := ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c S).2.2.1 _ φ g _ y y' z z' hg hz).1 hz'
  let t' : Ix Dw → (S ⧸ P)ˣ := fun i => Units.map (φ : S →* S ⧸ P) (t i)
  have hb : FrBor t' z z' :=
    ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c (S ⧸ P)).2.2.2 t' z z').2
      ⟨fun τ => (g τ).map φ, fun τ i => by simp [t', hg1], fun τ i j hij => by simp [hg2 τ i j hij], hc⟩
  have hw := evR_frBor_of_isDomain hL hF t' z z' hb
  rw [GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF S _ φ y z hz,
    GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF S _ φ y' z' hz'] at hw
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change φ _ = 0
  rw [map_sub, hw, map_mul, sub_eq_zero]
  congr 1
  simp [wchar, t']

theorem evR_scale_of_isReduced (hL : GlobalTheory.Reg.EvLaws Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {F : Rul Xo c} (hF : F ∈ sec Xo c a n) {A T : Type} [CommRing A] [Algebra c.F A] [IsReduced A]
    [CommRing T] [Algebra c.F T] (φ : A →ₐ[c.F] T) (g : Tˣ) (y : FrPt Xo c A) (z z' : FrPt Xo c T)
    (hm : FrMap φ y z) (hb : FrBor (fun i => i.elim g fun _ => 1) z z') :
    evR Xo c F z' = (g : T) ^ n * φ (evR Xo c F y) := by
  classical
  obtain ⟨G, hG1, hG2, hG⟩ := ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c T).2.2.2 _ z z').1 hb
  let ι := Option (Σ τ : E →+* ℂ, Fin (Dw.mult τ) × Fin (Dw.mult τ))
  let R := MvPolynomial ι A
  let B := Localization.Away (MvPolynomial.X none : R)
  let v : ι → T := fun i => i.elim (g : T) fun x => G x.1 x.2.1 x.2.2
  let k₀ : R →ₐ[c.F] T := MvPolynomial.aevalTower φ v
  have hk₀ : IsUnit (k₀ (MvPolynomial.X none)) := by simp [k₀, v, R]
  let k : B →ₐ[c.F] T := IsLocalization.liftAlgHom (M := Submonoid.powers (MvPolynomial.X none : R)) (f := k₀)
    (by rintro ⟨_, m, rfl⟩; simpa only [map_pow] using hk₀.pow m)
  have hk : ∀ r : R, k (algebraMap R B r) = k₀ r := fun r => IsLocalization.lift_eq _ r
  let π : A →ₐ[c.F] B := IsScalarTower.toAlgHom c.F A B
  have hπ : k.comp π = φ := by
    ext x
    change k (algebraMap A B x) = φ x
    rw [IsScalarTower.algebraMap_apply A R B, hk]
    simp [k₀, R]
  have hu : IsUnit (algebraMap R B (MvPolynomial.X none)) := IsLocalization.Away.algebraMap_isUnit _
  let M : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) B := fun τ => Matrix.of fun i j =>
    if i = j then 1 else if i < j then 0 else algebraMap R B (MvPolynomial.X (some ⟨τ, i, j⟩))
  have hM1 : ∀ τ i, M τ i i = 1 := fun τ i => by simp [M]
  have hM2 : ∀ τ i j, i < j → M τ i j = 0 := fun τ i j hij => by simp [M, hij, hij.ne]
  have hMk : ∀ τ, (M τ).map k = G τ := fun τ => by
    ext i j
    by_cases h1 : i = j
    · subst h1; simp [hM1, hG1]
    · by_cases h2 : i < j
      · simp [hM2 τ i j h2, hG2 τ i j h2]
      · simp only [M, Matrix.map_apply, Matrix.of_apply, if_neg h1, if_neg h2, hk]
        simp [k₀, v, R]
  have hdet : ∀ τ, IsUnit (M τ).det := fun τ => by
    rw [Matrix.det_of_isLowerTriangular (M τ) (fun i j hij => hM2 τ i j hij)]
    simp [hM1]
  obtain ⟨u₀, hu₀⟩ := hL.bc _ _ π y
  obtain ⟨u, hchg⟩ := (GlobalTheory.T.frameChange_exists_unique_invertible E H Dw l Xo c B M _ u₀).1 hdet hu
  have h0 : FrMap k u₀ z := frMap_cancel (Xo := Xo) (c := c) _ _ _ π k y u₀ z hu₀ (by rw [hπ]; exact hm)
  have h1 : FrMap k u z' := by
    refine ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c B).2.2.1 _ k M _ u₀ u z z' hchg h0).2 ?_
    have e : k (algebraMap R B (MvPolynomial.X none)) = (g : T) := by rw [hk]; simp [k₀, v, R]
    rw [e, show (fun τ => (M τ).map k) = G from funext hMk]
    exact hG
  let t : Ix Dw → Bˣ := fun i => i.elim hu.unit fun _ => 1
  have hbu : FrBor t u₀ u :=
    ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c B).2.2.2 t u₀ u).2 ⟨M, fun τ i => by simp [t, hM1], hM2, hchg⟩
  rw [GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF B _ k u z' h1,
    evR_frBor_of_isReduced hL hF t u₀ u hbu,
    GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF A _ π y u₀ hu₀, map_mul, ← hπ]
  congr 1
  have e : wchar (ex Dw a n) t = algebraMap R B (MvPolynomial.X none) ^ n := by
    simp [wchar, t, ex, Fintype.prod_option]
  rw [e, map_pow, hk]
  simp [k₀, v, R]

end General

end GlobalTheory.ArcQ
