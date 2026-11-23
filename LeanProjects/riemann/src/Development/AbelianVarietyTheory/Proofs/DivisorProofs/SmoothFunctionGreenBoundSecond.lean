import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticHeightTensorAdditiveOnCurves
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfCurveCharInBadSetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfCurveCharNotInBadSetStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechPic

set_option autoImplicit false
noncomputable section

theorem GlobalTheory.FlatVertDeg.topSelf_comb_eq_zero : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → ∀ (D : D7) (O : Setup D), O.Core → 2 < D.R.f * (O.N - 1) →
    ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H) (B : ℝ), 2 ≤ B → ∀ (τ : D.what₂.Tau) (c : O.s.Comp)
    (g : (T.M c).Fun), (T.M c).Smooth g →
    (∀ σ x, x ∉ (T.M c).Z σ → g σ x = (T.F c).ph (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) σ x) →
    ∀ (ε : (𝓞 D.what₂.LL →+* ℂ) → Fin ((T.M c).n + 1))
      (π : ∀ σ, GlobalTheory.CxPts (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p σ → (T.M c).X (ε σ)),
    (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.IsDown (h.man c) ε π →
    ∀ (hu : ∀ σ y, GlobalTheory.CxPts.CInfAt ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun))) σ) y)
      (hc : ∀ σ σ', (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun))) σ)).IsConj
        (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun))) σ'))),
    ∀ (Z : Scheme.{0}) (i : Z ⟶ (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ] [Finite κ]
      [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 → topSelfIntersection κ ((comb (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (fnB ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun)))) hu hc)
      ((h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).gens (GlobalTheory.FlagAr.setB O.Y B))) (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (1 : ℤ) fun o' => o'.elim 0 fun x => if x.1 = τ then (-1 : ℤ) else 0)).B.pull i) 1 = 0 := by
  intro hXH P2 PH SW D O hO hf A T H h B hB τ c g hg hgz ε π hπ hu hc Z i _ _ κ _ _ _ hd
  have hX := (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.ar
  have : Module.Finite ℤ (𝓞 D.what₂.LL) := hX.finite
  have : IsProper (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p := (isProper_and_exists_isAmpleLB_of_isProjOver hX.isProjOver).1
  have hproj : IsProjOver (strHom κ Z) := by
    have : IsFinite (spMap (Int.castRingHom (𝓞 D.what₂.LL))) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := 𝓞 D.what₂.LL)).2 inferInstance
    have e : strHom κ Z ≫ spMap (Int.castRingHom κ) =
        i ≫ (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p ≫ spMap (Int.castRingHom (𝓞 D.what₂.LL)) := specZIsTerminal.hom_ext _ _
    have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by
      rw [e]; infer_instance
    have : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
    exact ProperCurve.isProjOver_of_isProper _ hd
  let F₀ : HermLB.IsomClass (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p → ℤ :=
    Quotient.lift (s := HermLB.isometrySetoid _) (fun L => topSelfIntersection κ (L.B.pull i) 1) fun L L' e => by
      have ⟨w, hw, _⟩ := HermLB.Isometric.pull e i rfl
      exact interNum_congr_lbIso κ _ (fun _ => (L.restr i).isLB) (fun _ => (L'.restr i).isLB) fun _ => ⟨w, hw⟩
  let F : HermLB.IsomClass (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p →+ ℤ := AddMonoidHom.mk' F₀ (by
    rintro ⟨L⟩ ⟨L'⟩
    exact HtTensCurve.topSelf_one_pull_tens hproj hd i L.isLB L'.isLB)
  have key {ι : Type} [Fintype ι] (L : ι → HermLB (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p) (e : ι → ℤ) :
      topSelfIntersection κ ((comb L e).B.pull i) 1 = ∑ x, e x * F (L x).icls := by
    change F (comb L e).icls = _
    rw [icls_comb, map_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [map_zsmul, smul_eq_mul]
  have hcore := if hp : ringChar κ ∈ GlobalTheory.FlagAr.setB O.Y B then
      GlobalTheory.T.top_self_curve_char_in_bad_set P2 PH SW D O hO hf B hB c (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c) τ Z i κ hd hp
    else GlobalTheory.T.top_self_curve_char_not_in_bad_set hXH P2 PH SW D O hO hf B hB c (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c) τ Z i κ hd hp A T H h rfl
  rw [key] at hcore ⊢
  rw [Fintype.sum_option]
  have hF (L : HermLB (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p) : F L.icls = topSelfIntersection κ (L.B.pull i) 1 := rfl
  have htriv : topSelfIntersection κ ((LB.triv (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.X).pull i) 1 = 0 := by
    have hl := LB.isLB_pull (LB.isLB_triv (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.X) i
    refine interNum_eq_zero_of_cls_eq_zero κ _ (fun _ => hl) 0 ?_
    rw [cls_pull (LB.isLB_triv _) i, cls_triv, map_zero]
  have h0 : F (fnB _ hu hc).icls = 0 := (hF _).trans htriv
  simp only [Option.elim_none, Option.elim_some]
  rw [h0, mul_zero, zero_add]
  exact hcore
