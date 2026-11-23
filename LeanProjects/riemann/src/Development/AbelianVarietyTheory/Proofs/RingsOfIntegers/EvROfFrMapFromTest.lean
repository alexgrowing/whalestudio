import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IndepPts
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsFiniteExtensionIntegralFramedPointLiftCoveStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsFiniteExtUniformisedChartRationalTorsionStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsThetaValData
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortThetaValueFieldEqMapSubfieldDataStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TotalDegreeLeOfRowDeg
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem GlobalTheory.PlaceInt.evR_of_frMap_fromTest {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) (f : Rul Xo c)
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {K₁ K₂ : Type} [CommRing K₁] [Algebra c.F K₁] [CommRing K₂] [Algebra c.F K₂] (φ : K₁ →ₐ[c.F] K₂)
    (y₁ : FrPt Xo c K₁) (hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y₁)
    (y₂ : FrPt Xo c K₂) (hm : FrMap φ y₁ y₂) : evR Xo c f y₂ = φ (evR Xo c f y₁) := by
  obtain ⟨p, ψ, y', hy'⟩ := hT
  unfold evR
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.evalAt_eq_of _ _ hWD f hf p ψ y' y₁ hy',
    ReciprocityTheory.ChartRestriction.G.PullbackSections.evalAt_eq_of _ _ hWD f hf p (φ.comp ψ) y' y₂ (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans ψ φ hy' hm)]
  rfl

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.PlaceInt.short_value_on_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [StarRing (𝓞 E)], d.IsLev → IsNab d.Xo₂ d.c₂ d.nab₂ → ∀ m₀ : ℕ, (∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ ^ m₀ = 1) → ∀ (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w → ∀ (x0 : Fin n → Dw.La) (g : Rul Xo c), g ∈ sec Xo c w n → IsShortRule Xo c d Λ N x0 P g → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), T.FinRes → ∃ (T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ) (io₂ : d.c₂.F →+* T'.Fr) (y₂ : IntFr d.Xo₂ d.c₂ T' io₂) (C : IntegralChartA3 d.Xo₂ d.c₂ T' io₂ y₂) (ζ : T'.Fr) (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO d.Xo₂ (xOf y₂) ⟶ d.Xo₂.univ.t.G)) (tp : (Fin n → LevQ Dw d.l₂) → Fin n → (ptO d.Xo₂ (xOf y₂) ⟶ d.Xo₂.univ.t.G)) (F : (Fin n → LevQ Dw d.l₂) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow d.Xo₂.univ.t.G d.Xo₂.univ.t.PP.L ((N : ℤ) ^ 2) (ptO d.Xo₂ (xOf y₂)))), 0 < e ∧ (∀ a : T.Fr, vV T'.V (iT a) = (e : ℤ) * vV T.V a) ∧ T'.FinRes ∧ (∀ a : c.F, io₂ (d.eF a) = iT (io a)) ∧ Good3 C ∧ AllRat d.Xo₂ (xOf y₂) (N ^ 2) ∧ ζ ^ m₀ = 1 ∧ (∀ i, InZh d.Xo₂ Λ N (z i)) ∧ GeoInj d.Xo₂ (xOf y₂) z ∧ (∀ q b, tp q b ^ N = levPt d.Xo₂ (xOf y₂) (levRep (q b)) ∧ ∃ j : ℕ, KilledBy d.Xo₂ (d.l₂.Mb ^ j) (tp q b)) ∧ (∀ q i b, IsUUOver d.Xo₂.univ.t.G d.Xo₂.univ.t.PP N (sOf1 y₂) (z i b) (tp q b) (F q i b)) ∧ (letI := io₂.toAlgebra; iT (evI y g) = ζ * (io₂ ((d.eF (betaH (Dw := Dw) c Λ))⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : d.c₂.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw d.l₂) : d.c₂.F))⁻¹ * ((N : d.c₂.F) ^ (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P).totalDegree)⁻¹) * ∑ᶠ q : Fin n → LevQ Dw d.l₂, io₂ (d.w x0 q) * ∑ i, hv d.Xo₂ d.c₂ d.nab₂ y₂.1 (N ^ 2) (fun b => sqN d.Xo₂ N (F q i b)) (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P))) := by
  intro E _ _ _ H Dw l Xo c n d _ hlev hnab m₀ hm₀ Λ N hU hT hL w P hP x0 g hg hsh T io y hfin
  have laws : Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨T₁, i₁, e₁, y₁, io₁, z₁, ⟨he₁, hv₁, φ₁, hφ₁, hm₁⟩, hfin₁, hio₁, hover⟩ :=
    GlobalTheory.T.exists_finiteExtension_integralFramedPoint_lift_cover E H Dw l Xo c n d hlev T io y hfin
  have hN : 0 < N := hL.1.pos
  obtain ⟨T₂, i₂, e₂, z₂, C, ⟨he₂, hv₂, φ₂, hφ₂, hm₂⟩, hfin₂, hgood, hrat⟩ :=
    GlobalTheory.T.exists_finiteExt_uniformisedChart_rationalTorsion E H Dw d.l₂ d.Xo₂ d.c₂ hnab.1 T₁ io₁ z₁ hfin₁ (N ^ 2) (pow_pos hN 2)
  letI a0 : Algebra c.F T.Fr := io.toAlgebra
  letI a1 : Algebra c.F T₁.Fr := (i₁.comp io).toAlgebra
  letI b1 : Algebra d.c₂.F T₁.Fr := io₁.toAlgebra
  letI b2 : Algebra d.c₂.F T₂.Fr := (i₂.comp io₁).toAlgebra
  obtain ⟨z, tp, F, hz, hinj, htp, hF⟩ :=
    (GlobalTheory.RatData.exists_thetaVal_data E H Dw d.l₂ d.Xo₂ d.c₂ T₂.Fr z₂.1).2 n Λ N hU hL hrat
  obtain ⟨k, _, _, jk, -⟩ : ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (jk : T₂.Fr →+* k), True :=
    ⟨AlgebraicClosure T₂.Fr, inferInstance, inferInstance, algebraMap _ _, trivial⟩
  letI ak : Algebra c.F k := ((jk.comp i₂).comp (i₁.comp io)).toAlgebra
  letI bk : Algebra d.c₂.F k := (jk.comp (i₂.comp io₁)).toAlgebra
  let ψ₁ : T₁.Fr →ₐ[c.F] k := { jk.comp i₂ with commutes' := fun _ => rfl }
  let ψ₂ : T₂.Fr →ₐ[d.c₂.F] k := { jk with commutes' := fun _ => rfl }
  obtain ⟨yk, hyk⟩ := GlobalTheory.FramedBaseChange.exists_frMap laws E H Dw l Xo c _ _ ψ₁ y₁.1
  obtain ⟨zk, hzk⟩ := GlobalTheory.FramedBaseChange.exists_frMap laws E H Dw d.l₂ d.Xo₂ d.c₂ _ _ ψ₂ z₂.1
  have hc1 : ∀ a : c.F, algebraMap d.c₂.F T₁.Fr (d.eF a) = algebraMap c.F T₁.Fr a := hio₁
  have hck : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a := fun a =>
    congrArg (fun t => jk (i₂ t)) (hio₁ a)
  have hoverk : FrOver d zk yk :=
    (GlobalTheory.frames_lift_to_cover laws E H Dw l Xo c n d).2.1 T₁.Fr hc1 k hck ψ₁ (ψ₂.comp φ₂)
      (by
        show jk.comp φ₂.toRingHom = jk.comp i₂
        rw [hφ₂])
      y₁.1 z₁.1 yk zk hover hyk (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans φ₂ ψ₂ hm₂ hzk)
  obtain ⟨v, hv, hev⟩ := hsh k hck yk zk hoverk
  have hPh := ((GlobalTheory.PlaceInt.eF_transfer E H Dw l Xo c n d Λ).2.1 w P hP).1.1
  have hval := GlobalTheory.T.shortThetaValue_field_eq_map_subfield_data E H Dw d.l₂ d.Xo₂ d.c₂ hnab.1 d.nab₂ hnab n Λ N hU hT hL w _ hPh (d.w x0) _
    T₂.Fr k ψ₂ z₂.1 zk hzk z tp F hz hinj htp hF v hv
  have e1 : evR Xo c g yk = (ψ₁.comp φ₁) (evR Xo c g y.1) :=
    GlobalTheory.PlaceInt.evR_of_frMap_fromTest (GlobalTheory.Frames.algebraic_laws laws.secBaseChange E H Dw l Xo c).2.2.1 g hg.1 _ y.1 y.2.1 yk
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans φ₁ ψ₁ hm₁ hyk)
  have e2 : evR d.Xo₂ d.c₂ d.cδ zk = ψ₂ (evR d.Xo₂ d.c₂ d.cδ z₂.1) :=
    GlobalTheory.PlaceInt.evR_of_frMap_fromTest (GlobalTheory.Frames.algebraic_laws laws.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂).2.2.1 d.cδ hlev.2.2.2.2.2.2.2.1.1 _ z₂.1 z₂.2.1 zk hzk
  refine ⟨T₂, i₂.comp i₁, e₂ * e₁, i₂.comp io₁, z₂, C, evR d.Xo₂ d.c₂ d.cδ z₂.1, z, tp, F, Nat.mul_pos he₂ he₁, ?_, hfin₂,
    fun a => congrArg i₂ (hio₁ a), hgood, hrat, hm₀ _ _, hz, hinj, htp, hF, ?_⟩
  · intro a
    rw [RingHom.comp_apply, hv₂, hv₁]
    push_cast
    ring
  · apply jk.injective
    rw [e1, e2, hval, ← map_mul] at hev
    have e3 : jk ((i₂.comp i₁) (evI y g)) = (ψ₁.comp φ₁) (evR Xo c g y.1) := by
      show jk (i₂ (i₁ (evR Xo c g y.1))) = jk (i₂ (φ₁.toRingHom (evR Xo c g y.1)))
      rw [hφ₁]
    rw [e3, hev]
    rfl
