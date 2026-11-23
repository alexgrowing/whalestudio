import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryFormNonlocalMaximalStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitPhiOrder

theorem order_of_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c) (φ : InvFun (𝓞 E)) (EX : EffCartierData Z.X) (N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R)), SABMap t Z.t ξ → ∀ (P : PELUnif (maximalIdeal R) t), IsPhiDiv (comb 0 φ N φ) Z EX → IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → P.TorsionIso → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (f : R →+* W), Function.Injective f → IsLocalHom f → ∀ be ∈ levelForms H 1 P.D.toPre.X, FormAt P.D.toPre f ϖ be → ∃ n : ℕ, (n : ℝ) = N * φ.evalZ be ∧ idlAlong EX.idealSheaf (spMap f ≫ ξ) = Ideal.span {ϖ ^ n} := by
  intro E _ _ _ H D l Xo c Z φ EX N R _ _ _ ξ t mt P hphi hCN hEt hTor W _ _ _ hW ϖ hϖ f hfi hloc be hbe hform
  have hCN' := hCN
  obtain ⟨hNoeth, hIC, -, hChar⟩ := hCN'
  haveI := hNoeth
  haveI := hChar
  haveI := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨y, hy⟩ := DomFine.exists_generic_point (𝓞 c.F) c.F Z.X (Xo.XF c) Z.s Z.jQ Z.flat Z.proj Z.jQ_open
    Z.jQ_dense ξ hEt.1
  have hW' := hW
  obtain ⟨hdvr, hcpl, hch⟩ := hW'
  haveI := hdvr
  haveI := hcpl
  haveI := hch
  have hCNW : IsCN W := ⟨inferInstance, inferInstance, hcpl, hch⟩
  obtain ⟨t', mt', P', e, -, hcoord⟩ := pullSt E H R W f t P hCN hCNW hfi hloc hTor
  obtain ⟨mt''⟩ := TraitOrder.comp rfl mt mt'
  have j : Function.Injective ((algebraMap W (FractionRing W)).comp f) :=
    (IsFractionRing.injective W _).comp hfi
  let gK : FractionRing R →+* FractionRing W := IsFractionRing.lift j
  have eK : jK W ≫ spMap f = spMap gK ≫ jK R :=
    (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm
  have hr : Set.range (jK W ≫ spMap f ≫ ξ) ⊆ Set.range Z.j := by
    have hmor : spMap gK ≫ y ≫ Z.j = jK W ≫ spMap f ≫ ξ := by
      rw [← Category.assoc (jK W), eK, Category.assoc, ← hy]
      rfl
    rintro _ ⟨p, rfl⟩
    refine ⟨(spMap gK ≫ y) p, ?_⟩
    show (spMap gK ≫ y ≫ Z.j) p = _
    rw [hmor]

  let el : P'.D.toPre.X →ₗ[ℤ] P.D.toPre.X := e.toLinearMap.toAddMonoidHom.toIntLinearMap
  let be' : LinearMap.BilinForm ℤ P'.D.toPre.X := be.compl₁₂ el el
  have hbe' : ∀ a b, be' a b = be (e a) (e b) := fun _ _ => rfl
  obtain ⟨hs, hb, hd⟩ := hbe
  have hmem : be' ∈ levelForms H 1 P'.D.toPre.X := by
    refine ⟨fun a b => ?_, fun a y z => ?_, fun a b => ?_⟩
    · rw [hbe', hbe', hs]
    · show be (e (a • y)) (e z) = be (e y) (e (H.bar a • z))
      rw [e.map_smul, e.map_smul]; exact hb a (e y) (e z)
    · simp
  have hmon : IsMonomial P'.D.toPre ![ϖ] ![be'] := by
    intro a
    obtain ⟨r, k, hr0, hk, hc⟩ := hform (e a)
    obtain ⟨u, hu⟩ := hcoord a r hr0
    obtain ⟨v, hv⟩ := hc
    refine ⟨u * v⁻¹, ![k], fun i => ?_, ?_⟩
    · fin_cases i; simpa [hbe'] using hk
    · have e0 : f r = ϖ ^ k * ((v⁻¹ : Wˣ) : W) := by rw [← hv]; simp [mul_assoc]
      have e1 : (u : W) * f r = ((u * v⁻¹ : Wˣ) : W) * ∏ i, ![ϖ] i ^ ![k] i := by
        rw [e0]; simp [Fin.prod_univ_one]; ring
      rw [← e1]; exact hu
  obtain ⟨n, hn, hid⟩ := hphi W hW ϖ hϖ (spMap f ≫ ξ) t' mt'' P' hr be' hmem hmon
  refine ⟨n, ?_, hid⟩
  have e2 : φ.evalZ be' = φ.evalZ be :=
    InvFun.eval_equiv φ e (fun a b => ((be a b : ℤ) : ℝ))
  have e3 : (comb 0 φ N φ).evalZ be' = N * φ.evalZ be' := by
    simp only [InvFun.evalZ, InvFun.eval, comb]; push_cast; ring
  rw [hn, e3]
  exact congrArg ((N : ℝ) * ·) e2

theorem eval_nsmul {O : Type} [CommRing O] (φ : InvFun O) (hφ : IsTame φ) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] (k : ℕ) (B : X → X → ℝ) : φ.eval X (fun a b => k * B a b) = k * φ.eval X B := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [φ.eval_eq hr, φ.eval_eq hr]
  exact hφ.1 n k _

theorem order_of_nonlocal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c) (φ : InvFun (𝓞 E)) (EX : EffCartierData Z.X) (N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R)), SABMap t Z.t ξ → ∀ (P : PELUnif (maximalIdeal R) t), IsTame φ → IsPhiDiv (comb 0 φ N φ) Z EX → IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → P.TorsionIso → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (ψ : R →+* W), Function.Injective ψ → ¬ (∀ r ∈ maximalIdeal R, ψ r ∈ maximalIdeal W) → ∀ be ∈ levelForms H 1 P.D.toPre.X, FormAt P.D.toPre ψ ϖ be → ∃ n : ℕ, (n : ℝ) = N * φ.evalZ be ∧ idlAlong EX.idealSheaf (spMap ψ ≫ ξ) = Ideal.span {ϖ ^ n} := by
  intro E _ _ _ H D l Xo c Z φ EX N R _ _ _ ξ t mt P hφ hphi hCN hEt hTor V _ _ _ hV ϖ hϖ ψ hψi hnl be hbe hF
  have hCN' := hCN
  obtain ⟨hNoeth, hIC, -, hChar⟩ := hCN'
  haveI := hNoeth
  haveI := hChar
  haveI := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨y, hy⟩ := DomFine.exists_generic_point (𝓞 c.F) c.F Z.X (Xo.XF c) Z.s Z.jQ Z.flat Z.proj Z.jQ_open
    Z.jQ_dense ξ hEt.1
  have hV' := hV
  obtain ⟨hdvr, hcpl, hch⟩ := hV
  haveI := hdvr
  haveI := hcpl
  haveI := hch
  have j0 : Function.Injective ((algebraMap V (FractionRing V)).comp ψ) :=
    (IsFractionRing.injective V _).comp hψi
  let gam : FractionRing R →+* FractionRing V := IsFractionRing.lift j0
  have hsq : jK V ≫ spMap ψ = spMap gam ≫ jK R :=
    (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j0)).symm
  let χ : Sp V ⟶ Z.X := spMap ψ ≫ ξ
  have hZ : jK V ≫ χ = (spMap gam ≫ y) ≫ Z.j := by
    show jK V ≫ spMap ψ ≫ ξ = _
    rw [← Category.assoc, hsq, Category.assoc, ← hy, Category.assoc]
    rfl
  obtain ⟨t₁, ⟨m₁⟩⟩ := GlobalTheory.TraitOrder.exists_pull χ Z.t
  obtain ⟨mR⟩ := GlobalTheory.TraitOrder.cancel rfl mt m₁
  let T : CDVR := { V := V }
  have hp := GlobalTheory.GoodTrait.polAt_of_point Z m₁ (jK V) (spMap gam ≫ y) hZ.symm
  obtain ⟨T', f, u, hi, hl, ⟨mu⟩, ⟨P'⟩⟩ := exists_unif_ext T t₁ hp
  obtain ⟨n'⟩ := GlobalTheory.TraitOrder.comp rfl m₁ mu
  obtain ⟨nR⟩ := GlobalTheory.TraitOrder.comp rfl mR mu
  have hW' : CDvr T'.V := ⟨T'.dvr, T'.cpl, T'.ch0⟩
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible T'.V
  obtain ⟨be', hbe', hmon, -⟩ := exists_periodForm P' hϖ'
  have j : Function.Injective ((algebraMap T'.V (FractionRing T'.V)).comp f) :=
    (IsFractionRing.injective T'.V _).comp hi
  let g' : FractionRing V →+* FractionRing T'.V := IsFractionRing.lift j
  have e₀ : jK T'.V ≫ spMap f = spMap g' ≫ jK V :=
    (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm
  have e₁ : jK T'.V ≫ spMap f ≫ χ = (spMap g' ≫ spMap gam ≫ y) ≫ Z.j := by
    rw [← Category.assoc, e₀, Category.assoc, hZ]; simp only [Category.assoc]
  have hr : Set.range (jK T'.V ≫ spMap f ≫ χ) ⊆ Set.range Z.j := by
    rintro _ ⟨p, rfl⟩
    exact ⟨(spMap g' ≫ spMap gam ≫ y) p, by rw [e₁]; rfl⟩
  obtain ⟨k', hk', hid⟩ := hphi T'.V hW' ϖ' hϖ' _ u n' P' hr be' hbe' hmon
  obtain ⟨r, e, hrs, hfe, hre⟩ := GlobalTheory.T.boundary_form_nonlocal_maximal E H R t P hCN hTor V hV' ϖ hϖ ψ hψi hnl be hbe hF T' f hi hl u nR P' ϖ'
    hϖ' be' hbe' hmon
  have hval : φ.evalZ be' = e * φ.evalZ be := by
    unfold InvFun.evalZ
    rw [← φ.eval_comp hrs (fun a b => (be' a b : ℝ))]
    have h1 : (fun a b => ((be' (r a) (r b) : ℤ) : ℝ)) = fun a b => (e : ℝ) * ((be a b : ℤ) : ℝ) := by
      funext a b
      rw [hre, Int.cast_mul, Int.cast_natCast]
    rw [h1, eval_nsmul φ hφ]
  rw [GlobalTheory.TraitOrder.idlAlong_comp] at hid
  have hne : idlAlong EX.idealSheaf χ ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.map_bot] at hid
    exact pow_ne_zero k' hϖ'.ne_zero (Ideal.span_singleton_eq_bot.1 hid.symm)
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  rw [hn, Ideal.map_span, Set.image_singleton, map_pow] at hid
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hfe
    exact hϖ.not_isUnit ((isUnit_map_iff f ϖ).1 (associated_one_iff_isUnit.1 hfe))
  obtain ⟨w, hw⟩ := hfe
  have hf' : f ϖ = ϖ' ^ e * ↑w⁻¹ := by
    rw [← hw, mul_assoc, Units.mul_inv, mul_one]
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.1 hid
  have hen : e * n = k' := by
    refine IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ' hϖ' (w⁻¹ ^ n * v) 1 (e * n) k' ?_
    calc ((w⁻¹ ^ n * v : T'.Vˣ) : T'.V) * ϖ' ^ (e * n) = (ϖ' ^ e * ↑w⁻¹) ^ n * v := by push_cast; ring
      _ = (f ϖ) ^ n * v := by rw [hf']
      _ = ((1 : T'.Vˣ) : T'.V) * ϖ' ^ k' := by rw [hv, Units.val_one, one_mul]
  refine ⟨n, ?_, hn⟩
  have e3 : (comb 0 φ N φ).evalZ be' = N * φ.evalZ be' := by
    simp only [InvFun.evalZ, InvFun.eval, comb]; push_cast; ring
  have hk'' : ((e * n : ℕ) : ℝ) = N * (e * φ.evalZ be) := by
    rw [hen, hk', e3, hval]
  push_cast at hk''
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 he0) (by rw [hk'']; ring)

theorem order_along_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c) (g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) (EX : EffCartierData Z.X) (N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R)), SABMap t Z.t ξ → ∀ (P : PELUnif (maximalIdeal R) t) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs → Refines H (min D.p D.q) φs 𝒩 φ → 0 < N → IsPhiDiv (comb 0 φ N φ) Z EX → IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso → ConeZ E φs P.D.toPre.X m γ → InCone P.D.toPre γ → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (f : R →+* W), Function.Injective f → ∀ be ∈ levelForms H 1 P.D.toPre.X, FormAt P.D.toPre f ϖ be → ∃ n : ℕ, (n : ℝ) = N * φ.evalZ be ∧ idlAlong EX.idealSheaf (spMap f ≫ ξ) = Ideal.span {ϖ ^ n} := by
  intro E _ _ _ H D l Xo c Z g φs 𝒩 φ EX N R _ _ _ ξ t mt P m γ hg hfan href hN hphi hCN hEt hun hTor hcone hin
    W _ _ _ hW ϖ hϖ f hfi be hbe hform
  by_cases hl : ∀ r ∈ maximalIdeal R, f r ∈ maximalIdeal W
  · have hloc : IsLocalHom f := ⟨fun a ha => by
      by_contra h
      exact (mem_maximalIdeal _).1 (hl a ((mem_maximalIdeal a).2 h)) ha⟩
    exact order_of_local E H D l Xo c Z φ EX N R ξ t mt P hphi hCN hEt hTor W hW ϖ hϖ f hfi hloc be hbe hform
  · exact order_of_nonlocal E H D l Xo c Z φ EX N R ξ t mt P href.2.2.2.2.1 hphi hCN hEt hTor W hW ϖ hϖ f hfi hl be hbe
      hform

end GlobalTheory.TraitPhiOrder
