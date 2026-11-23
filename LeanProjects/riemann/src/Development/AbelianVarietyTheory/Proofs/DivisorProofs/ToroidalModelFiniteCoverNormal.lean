import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocGrLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelFlagHeightFirst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisOfSplitTorsion
import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
import Formalism.LocalToGlobal.ProjectiveLattices.FrCovA
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwoLat.GrLoc

open GlobalTheory.ShFam.Pad.Guard GlobalTheory.TangentOrigin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)

theorem comb_scale {K : Type} [CommRing K] {x : Sp K ⟶ Z.X} {r : ℕ}
    {u : Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left)} (hu : ∀ i, IsTanAtG Z.t x (u i)) (k : K) (a : Fin r → K)
    (w : Sp (DualNumber K) ⟶ Z.t.G.left) :
    IsCombAtG Z.t x (fun i => spMap (epsMul k) ≫ u i) a w ↔ IsCombAtG Z.t x u (fun i => k * a i) w := by
  have h1 : ∀ i, IsCombAtG Z.t x u (fun j => (Matrix.diagonal fun _ : Fin r => k) j i) (spMap (epsMul k) ≫ u i) := by
    intro i
    have := comb_smul hu (isCombAtG_single Z.t x hu i) k
    convert this using 2 with j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  have h2 : ∀ w', IsCombAtG Z.t x (fun i => spMap (epsMul k) ≫ u i) a w' → IsCombAtG Z.t x u (fun i => k * a i) w' := by
    intro w' h
    have := Formalism.L2.Pj.tanLinG u hu _ _ a w' h1 h
    convert this using 2 with j
    simp [Matrix.mulVec_diagonal]
  refine ⟨h2 w, fun h => ?_⟩
  obtain ⟨w', -, hw'⟩ := exists_comb (fun i => comb_tan hu (h1 i)) a
  rwa [comb_unique hu h (h2 w' hw')]

theorem isEigBasis_scale {K : Type} [CommRing K] {φ : c.F →+* K} {x : Sp K ⟶ Z.X} {τ : E →+* ℂ} {r : ℕ}
    {u : Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left)} (hu : IsEigBasis Z φ x τ u) {k n : K} (hk : k * n = 1) :
    IsEigBasis Z φ x τ (fun i => spMap (epsMul k) ≫ u i) := by
  refine ⟨fun i => Trans.isEigTan_smul Z (hu.1 i) k, fun w hw => ?_⟩
  obtain ⟨a, ha, hq⟩ := hu.2 w hw
  refine ⟨fun i => n * a i, ?_, fun b hb => ?_⟩
  · refine (comb_scale Z (fun i => (hu.1 i).1) k _ w).2 ?_
    simpa only [← mul_assoc, hk, one_mul] using ha
  · have := hq _ ((comb_scale Z (fun i => (hu.1 i).1) k _ w).1 hb)
    funext i
    rw [← this, ← mul_assoc, mul_comm n k, hk, one_mul]

theorem dual_eps {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    spMap (dualMap ψ) ≫ spMap (epsMul a) = spMap (epsMul (ψ a)) ≫ spMap (dualMap ψ) := by
  rw [sp_comp, sp_comp]
  congr 1
  refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [Formalism.L2.Pj.dualMap, epsMul, mul_comm]

theorem isUnit_nat {K : Type} [CommRing K] (φ : c.F →+* K) {n : ℕ} (hn : n ≠ 0) : IsUnit (n : K) := by
  simpa using ((Nat.cast_ne_zero.2 hn : ((n : ℕ) : c.F) ≠ 0).isUnit).map φ

theorem over_struct {F : Type} [Field F] (e : F ≃+* c.F) {K : Type} [CommRing K] (y : Sp K ⟶ gen Z) (ψ : F →+* K)
    (h : y ≫ genStr Z ≫ spMap e.toRingHom = spMap ψ) :
    y ≫ genι Z ≫ Z.s = spMap ((ψ.comp e.symm.toRingHom).comp β) := by
  have h1 : genι Z ≫ Z.s = genStr Z ≫ spMap β := Limits.pullback.condition
  have h2 : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
    rw [sp_comp, show e.toRingHom.comp e.symm.toRingHom = RingHom.id _ from by ext; simp]
    exact Spec.map_id _
  rw [h1, ← sp_comp, ← sp_comp, ← h]
  simp only [Category.assoc]
  rw [reassoc_of% h2]

theorem evalPt_bc {K K' : Type} [CommRing K] [CommRing K'] (ψ : K →+* K') {X W : Scheme.{0}} (x : Sp K ⟶ W) (j : W ⟶ X)
    (U : X.Opens) (hx : ⊤ ≤ (x ≫ j) ⁻¹ᵁ U) (hx' : ⊤ ≤ ((spMap ψ ≫ x) ≫ j) ⁻¹ᵁ U) :
    evalPt ((spMap ψ ≫ x) ≫ j) U hx' = ψ.comp (evalPt (x ≫ j) U hx) := by
  have h : (spMap ψ ≫ x) ≫ j = spMap ψ ≫ x ≫ j := Category.assoc _ _ _
  generalize (spMap ψ ≫ x) ≫ j = y at h hx'
  subst h
  exact RingHom.ext fun f => evalPt_spMap_comp ψ (x ≫ j) U hx hx' f

theorem exists_int {K C : Type} [Field K] [CommRing C] (O : ValuationSubring K) (O' : Subring C) (ι : K →+* C)
    (hι : ∀ a ∈ O, ι a ∈ O') {X : Scheme.{0}} (y : Sp K ⟶ X) (xt : Sp O ⟶ X) (h : spMap O.subtype ≫ xt = y)
    (U : X.Opens) (ht : ⊤ ≤ xt ⁻¹ᵁ U) (hy : ⊤ ≤ y ⁻¹ᵁ U) :
    ∃ ψ : Γ(X, U) →+* O', O'.subtype.comp ψ = ι.comp (evalPt y U hy) := by
  subst h
  exact ⟨((ι.comp O.subtype).codRestrict O' fun a => hι _ a.2).comp (evalPt xt U ht),
    RingHom.ext fun f => congrArg ι (evalPt_spMap_comp _ xt U ht hy f).symm⟩

def GrSpan (p : ℕ) [Fact p.Prime] (φ : c.F →+* ℂ_[p]) (y : Sp ℂ_[p] ⟶ Z.X) (τ : E →+* ℂ) {r : ℕ}
    (u : Fin r → (Sp (DualNumber ℂ_[p]) ⟶ Z.t.G.left)) (Q : ℂ_[p] → Prop) : Prop :=
  ∀ w, IsEigTan Z φ y τ w →
    ((∃ a : Fin r → ℂ_[p], (∀ i, Q (a i)) ∧ IsCombAtG Z.t y u a w) ↔ InGr Z φ y (latDR Z.t y) τ w)

theorem GrSpan.scale {p : ℕ} [Fact p.Prime] {φ : c.F →+* ℂ_[p]} {y : Sp ℂ_[p] ⟶ Z.X} {τ : E →+* ℂ} {r : ℕ}
    {u : Fin r → (Sp (DualNumber ℂ_[p]) ⟶ Z.t.G.left)} {N : ℕ} (hu : IsUnit (N : ℂ_[p]))
    (ht : ∀ i, IsTanAtG Z.t y (u i)) (h : GrSpan Z p φ y τ u fun a => ‖(N : ℂ_[p]) * a‖ ≤ 1) :
    GrSpan Z p φ y τ (fun i => spMap (epsMul (Ring.inverse (N : ℂ_[p]))) ≫ u i) fun a => ‖a‖ ≤ 1 := by
  intro w hw
  refine Iff.trans ?_ (h w hw)
  simp only [comb_scale Z ht]
  refine ⟨fun ⟨a, ha, hc⟩ => ⟨_, fun i => ?_, hc⟩, fun ⟨a, ha, hc⟩ => ⟨_, ha, ?_⟩⟩
  · rw [← mul_assoc, Ring.mul_inverse_cancel _ hu, one_mul]; exact ha i
  · simpa only [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul] using hc

theorem grSpan_of_grBasis {R : Type} [CommRing R] {x : Sp R ⟶ Z.X} {τ : E →+* ℂ} {r : ℕ} (h : GrBasis Z x τ r) :
    ∃ (N : ℕ) (u : Fin r → (Sp (DualNumber R) ⟶ Z.t.G.left)), N ≠ 0 ∧
      (∀ (K : Type) [CommRing K] (ψ : R →+* K) (φ : c.F →+* K), spMap ψ ≫ x ≫ Z.s = spMap (φ.comp β) →
        IsEigBasis Z φ (spMap ψ ≫ x) τ (fun i => spMap (dualMap ψ) ≫ u i)) ∧
      ∀ (p : ℕ) [Fact p.Prime] (ψ : R →+* ↥(intO ℂ_[p])) (φ : c.F →+* ℂ_[p]),
        spMap ((intO ℂ_[p]).subtype.comp ψ) ≫ x ≫ Z.s = spMap (φ.comp β) →
          GrSpan Z p φ (spMap ((intO ℂ_[p]).subtype.comp ψ) ≫ x) τ
            (fun i => spMap (dualMap ((intO ℂ_[p]).subtype.comp ψ)) ≫ u i) fun a => ‖(N : ℂ_[p]) * a‖ ≤ 1 :=
  h

theorem isLocGrLat_of_forall {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F) {X W : Scheme.{0}} (jB : W ⟶ X)
    (πB : W ⟶ gen Z) (r : ℕ) (τ : E →+* ℂ) (U : X.Opens) (u : LocAssign Z r jB U)
    (h : ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (hp : (resP v).Prime) (ε : TrueGeo.Ext v)
      (xg : Sp (AlgebraicClosure F) ⟶ W) (xt : Sp ε.O ⟶ X),
      xg ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap (algebraMap F (AlgebraicClosure F)) →
      spMap ε.O.subtype ≫ xt = xg ≫ jB → ⊤ ≤ xt ⁻¹ᵁ U → ∀ (hx : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ U),
        haveI : Fact (resP v).Prime := ⟨hp⟩
        ∀ w, IsEigTan Z (((ioOf (resP v) ε).comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom)
          (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z) τ w →
        ((∃ a : Fin r → ℂ_[resP v], (∀ i, ‖a i‖ ≤ 1) ∧ IsCombAtG Z.t (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z)
            (fun i => spMap (dualMap (ioOf (resP v) ε)) ≫ u _ xg hx i) a w) ↔
          InGr Z (((ioOf (resP v) ε).comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom)
            (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z)
            (latDR Z.t (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z)) τ w)) :
    IsLocGrLat Z e jB πB r τ U u :=
  h

theorem isLocGrLat_of_grSpan {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F) {X W : Scheme.{0}} (jB : W ⟶ X)
    (πB : W ⟶ gen Z) (r : ℕ) (τ : E →+* ℂ) (U : X.Opens) (u : LocAssign Z r jB U)
    (h : ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) [Fact (resP v).Prime] (ε : TrueGeo.Ext v)
      (xg : Sp (AlgebraicClosure F) ⟶ W) (xt : Sp ε.O ⟶ X),
      xg ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap (algebraMap F (AlgebraicClosure F)) →
      spMap ε.O.subtype ≫ xt = xg ≫ jB → ⊤ ≤ xt ⁻¹ᵁ U → ∀ (hx : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ U),
        GrSpan Z (resP v) (((ioOf (resP v) ε).comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom)
          (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z) τ
          (fun i => spMap (dualMap (ioOf (resP v) ε)) ≫ u _ xg hx i) fun a => ‖a‖ ≤ 1) :
    IsLocGrLat Z e jB πB r τ U u :=
  isLocGrLat_of_forall Z e jB πB r τ U u fun v hp => @h v ⟨hp⟩

end GlobalTheory.TwoLat.GrLoc

namespace GlobalTheory.TwoLat

open GlobalTheory.ShFam.Pad.Guard GlobalTheory.TangentOrigin

theorem exists_locFrame_of_grBasis : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F)
    {X W : Scheme.{0}} (jB : W ⟶ X) (πB : W ⟶ gen Z) (ρ : X ⟶ Z.X), jB ≫ ρ = πB ≫ genι Z →
    ∀ (U : X.Opens) (hU : IsAffineOpen U) (τ : E →+* ℂ) (r : ℕ),
    GlobalTheory.TwoLat.GrBasis Z (R := Γ(X, U)) (hU.fromSpec ≫ ρ) τ r →
    ∃ u : LocAssign Z r jB U, IsLocFrame Z e jB πB r τ U u ∧ GlobalTheory.TwoLat.IsLocGrLat Z e jB πB r τ U u := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ _ e X W jB πB ρ hρ U hU τ r hb
  obtain ⟨N, u, hN, hg, hl⟩ := GrLoc.grSpan_of_grBasis Z hb
  have hpt : ∀ {K : Type} [CommRing K] (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U),
      spMap (evalPt (x ≫ jB) U hx) ≫ hU.fromSpec ≫ ρ = x ≫ πB ≫ genι Z := by
    intro K _ x hx
    rw [← hρ, ← Category.assoc x, ← Category.assoc]
    exact congrArg (· ≫ ρ) (eq_spec_fromSpec hU (x ≫ jB) hx).symm
  have hun : ∀ {K : Type} [CommRing K] (x : Sp K ⟶ W), IsUnit (N : K) := fun x =>
    GrLoc.isUnit_nat (Spec.preimage (x ≫ πB ≫ genStr Z)).hom hN
  have hnat : ∀ (K K' : Type) [CommRing K] [CommRing K'] (ψ : K →+* K') (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U)
      (i : Fin r), spMap (dualMap ψ) ≫ spMap (epsMul (Ring.inverse (N : K))) ≫
        spMap (dualMap (evalPt (x ≫ jB) U hx)) ≫ u i =
      spMap (epsMul (Ring.inverse (N : K'))) ≫ spMap (dualMap (ψ.comp (evalPt (x ≫ jB) U hx))) ≫ u i := by
    intro K K' _ _ ψ x hx i
    have h1 : ψ (Ring.inverse (N : K)) = Ring.inverse (N : K') := by
      have h2 : ψ (Ring.inverse (N : K)) * (N : K') = 1 := by
        rw [← map_natCast ψ, ← map_mul, Ring.inverse_mul_cancel _ (hun x), map_one]
      exact ((Ring.eq_mul_inverse_iff_mul_eq _ _ _ (hun (spMap ψ ≫ x))).2 h2).trans (one_mul _)
    rw [← Category.assoc, GrLoc.dual_eps, h1, Category.assoc, GlobalTheory.HTPres.bc_bc]
  have hstr : ∀ {K : Type} [CommRing K] (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U) (ψ : F →+* K),
      x ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap ψ →
      spMap (evalPt (x ≫ jB) U hx) ≫ (hU.fromSpec ≫ ρ) ≫ Z.s = spMap ((ψ.comp e.symm.toRingHom).comp β) := by
    intro K _ x hx ψ h
    rw [← Category.assoc, hpt x hx, ← GrLoc.over_struct Z e (x ≫ πB) ψ (by simpa only [Category.assoc] using h)]
    simp only [Category.assoc]
  refine ⟨fun K _ x hx i => spMap (epsMul (Ring.inverse (N : K))) ≫ spMap (dualMap (evalPt (x ≫ jB) U hx)) ≫ u i,
    ⟨fun K _ x hx ψ h => ?_, fun K K' _ _ ψ x hx hx' i => ?_⟩,
    GrLoc.isLocGrLat_of_grSpan Z e jB πB r τ U _ fun v _ ε xg xt h1 h2 h3 hx => ?_⟩
  · have h4 := hg K _ _ (hstr x hx ψ h)
    rw [hpt x hx] at h4
    exact GrLoc.isEigBasis_scale Z h4 (Ring.inverse_mul_cancel _ (hun x))
  · have h4 := hnat K K' ψ x hx i
    rw [← GrLoc.evalPt_bc ψ x jB U hx hx'] at h4
    exact h4.symm
  · obtain ⟨_, hio, -⟩ := ioOf_spec F v ε
    have hy : ⊤ ≤ ((spMap (ioOf (resP v) ε) ≫ xg) ≫ jB) ⁻¹ᵁ U := fun p _ => hx (Set.mem_univ _)
    have h5 := (GrLoc.evalPt_bc (ioOf (resP v) ε) xg jB U hx hy).symm
    obtain ⟨ψ₀, h6⟩ := GrLoc.exists_int ε.O (intO ℂ_[resP v]) (ioOf (resP v) ε) (fun a ha => (hio a).2 ha) _ xt h2 U
      h3 hx
    have h4 : (spMap (ioOf (resP v) ε) ≫ xg) ≫ πB ≫ genStr Z ≫ spMap e.toRingHom =
        spMap ((ioOf (resP v) ε).comp (algebraMap F (AlgebraicClosure F))) := by
      rw [Category.assoc, h1, sp_comp]
    have h7 := hstr _ hy _ h4
    have h8 := hg _ _ _ h7
    have h9 := hl (resP v) ψ₀ _ (by rw [h6, h5]; exact h7)
    rw [h6, h5, hpt _ hy, Category.assoc] at h9
    rw [hpt _ hy, Category.assoc] at h8
    have h10 := funext (hnat _ _ (ioOf (resP v) ε) xg hx)
    rw [h5] at h10
    rw [h10]
    exact GrLoc.GrSpan.scale Z (hun (spMap (ioOf (resP v) ε) ≫ xg)) (fun i => (h8.1 i).1) h9

end GlobalTheory.TwoLat

end
