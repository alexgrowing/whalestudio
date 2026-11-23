import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.DualLattices.ExistsPrimitiveRoot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PeriodDatumSignCharactersMemEvalImage
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLiftPrincipallyPolarisedAbelianSquareZeroStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsCharacterPairSerStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianFunctorNilChartOfNilpotentChartStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinearPartPairingSeriesEqHeightStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JacobianMulTangentChartMatrixIntertwinesStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTangentChartMatrixOfBasisStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPeriodTowerDatumOfAbelianSchemeSymmetricBuStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CardTorsionOfPolarisedAbelianSchemeLiftStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubeTrivialAndFiniteFlatSurjectiveMulAbelianScheStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SmoothOfRelativeDimensionOfGrpPullbackLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsGeneratorOfRosatiAdjointLambdaBundleStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HodgeTateDatumHypothesesPeriodTowerStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ChF

private theorem thetaBar_surj (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) :
    Function.Surjective (Ainf.thetaBar p O hv ε hε) := by
  intro y
  obtain ⟨a, rfl⟩ := Ainf.theta_surj p O hv y
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

private theorem thetaBar_mul (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
    (x y : Ainf.R0 p O ε) (hx : x ∈ RingHom.ker (Ainf.thetaBar p O hv ε hε))
    (hy : y ∈ RingHom.ker (Ainf.thetaBar p O hv ε hε)) : x * y = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have ha : a ∈ RingHom.ker (WittVector.fontaineTheta O p) := RingHom.mem_ker.2 (RingHom.mem_ker.1 hx)
  have hb : b ∈ RingHom.ker (WittVector.fontaineTheta O p) := RingHom.mem_ker.2 (RingHom.mem_ker.1 hy)
  rw [Ainf.ker_theta p O hv ε hε] at ha hb
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hb
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact ⟨c * d, by ring⟩

private theorem htd_of_dat {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] (C : Type) [Field C]
    (v : Valuation C NNReal) (Tw : ATowerL R₀ p) [Algebra (Tw.O : Type) C] (hv : v.Integers (Tw.O : Type))
    (hp : ¬IsUnit (p : (Tw.O : Type))) (hc : IsAdicComplete (Ideal.span {(p : (Tw.O : Type))}) (Tw.O : Type))
    [Algebra ℤ_[p] (Tw.O : Type)] (g : ℕ) (OE : Type) [CommRing OE] [StarRing OE]
    (B : BX R₀) (F : FGLaw (Tw.O : Type) g)
    (Y : ∀ R : LAlg R₀, LHom Tw.O R → (Fin g → (R : Type)) → B.G R) (hY : BXChart B Tw.O F.F Y)
    (α : OE → Fin g → PS (Tw.O : Type) 1 g) (hα : ∀ a j, MvPowerSeries.constantCoeff (α a j) = 0)
    (A : OE → OEnd B Tw.O)
    (hA : ∀ b (R : LAlg R₀) (s : LHom Tw.O R) (a : Fin g → (R : Type)), (∀ i, IsNilpotent (a i)) →
      (A b).f s (Y R s a) = Y R s (fun j => nv s.1.toRingHom (α b j) ![a]))
    (Dt : DualTower Tw) (cp : (Tw.O : Type)) (D : Dat p g B Tw Dt (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp)
    (h₁ : D.H.P = 0) (h₂ : D.H.PL = 0)
    (h₃ : ∀ a {R S : LAlg R₀} (s : LHom Tw.O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker)
      (m : Fin g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (D.H.ρL (1 ⊗ₜ[ℤ] a) k l) * i) →
      (A a).f s (B.tg π hπ (D.ch.gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m k)) :
    ∃ (H : HodgeTateDatum p g v (Tw.O : Type) (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (S : Matrix (Fin g) (Fin g) (Tw.O : Type)),
      H.P = 0 ∧ H.PL = 0 ∧ IsUnit S ∧ (∀ a : OE, lin (α a) * S = S * H.ρL (1 ⊗ₜ[ℤ] a)) ∧
      ∀ i, ∃ u : PS (Tw.O : Type) 1 g, IsCh F.F u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i := by
  have hinj : Function.Injective (algebraMap (Tw.O : Type) C) := hv.hom_inj
  have hdom : IsDomain (Tw.O : Type) := Function.Injective.isDomain (algebraMap (Tw.O : Type) C) hinj
  obtain ⟨S, hSu, hS⟩ := GlobalTheory.T.exists_tangentChartMatrix_of_basis R₀ B Tw.O g F Y hY D.ch.gb
  refine ⟨GlobalTheory.EvClose.htdOfDat D C v hdom hinj, S, h₁, h₂, hSu, ?_, ?_⟩
  · intro a
    exact GlobalTheory.T.jacobian_mul_tangentChartMatrix_intertwines R₀ B Tw.O g F Y hY D.ch.gb S hS (A a) (α a) (D.H.ρL (1 ⊗ₜ[ℤ] a)) (hα a)
      (hA a) (h₃ a)
  · intro i
    obtain ⟨u, hu, hpair⟩ := GlobalTheory.T.exists_character_pairSer_alt R₀ B Tw.O g F Y hY p hp hc (D.L.τ i) (D.L.τ_tors i)
      (D.L.τ_compat i)
    have hcc : MvPowerSeries.constantCoeff u = 1 := by
      unfold IsCh at hu
      exact hu.1
    refine ⟨u, hu, ?_⟩
    rw [GlobalTheory.T.linear_part_pairing_series_eq_height R₀ B p Tw Dt g Y D.ch.gb S hS (D.L.τ i) u hcc hpair (D.L.ht i) (D.L.ht_spec i)]
    funext l
    exact (D.L.Ht_eq l i).symm

private theorem htd_of_tower (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
    (Tw : ATowerL (Ainf.R0 p O ε) p) (hTw : Tw = Ainf.ainfTowerL p O hv ε hε)
    [Algebra (Tw.O : Type) C] (hv' : v.Integers (Tw.O : Type))
    [hp : Fact ¬IsUnit (p : (Tw.O : Type))]
    [hc : IsAdicComplete (Ideal.span {(p : (Tw.O : Type))}) (Tw.O : Type)]
    [Algebra ℤ_[p] (Tw.O : Type)]
    (T : Type) [CommRing T] [IsNoetherianRing T] (P₀ : Out.PolAV (Geo.Tor.Sp T)) (io : T →+* (Tw.O : Type))
    (P : Out.PolAV (Geo.Tor.Sp (Tw.O : Type))) (φ : P.A.left ⟶ P₀.A.left)
    (h₁ : Geo.Tor.IsGrpPullback P.A P₀.A (Geo.Tor.spMap io) φ) (h₂ : Geo.Tor.LBIso P.L (P₀.L.pull φ))
    (h₃ : P.g = P₀.g) (h₄ : 1 ≤ P.g) (OE : Type) [CommRing OE] [StarRing OE] (o : P.OAct OE)
    (F : FGLaw (Tw.O : Type) P.g) (X : Fam P.A P.g) (hX : NilChart P.A F.F X)
    (α : OE → Fin P.g → PS (Tw.O : Type) 1 P.g) (hα : ∀ a, Reads X X (o.act a) (α a)) :
    ∃ (H : HodgeTateDatum p P.g v (Tw.O : Type) (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) Tw.c)
      (S : Matrix (Fin P.g) (Fin P.g) (Tw.O : Type)),
      H.P = 0 ∧ H.PL = 0 ∧ IsUnit S ∧ (∀ a : OE, lin (α a) * S = S * H.ρL (1 ⊗ₜ[ℤ] a)) ∧
      ∀ i, ∃ u : PS (Tw.O : Type) 1 P.g, IsCh F.F u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i := by
  subst hTw
  have hπs : Function.Surjective
      (algebraMap (Ainf.R0 p O ε) ((Ainf.ainfTowerL p O hv ε hε).O : Type)) :=
    thetaBar_surj p O hv ε hε
  have hπk : RingHom.ker
      (algebraMap (Ainf.R0 p O ε) ((Ainf.ainfTowerL p O hv ε hε).O : Type)) ^ 2 = ⊥ := by
    rw [pow_two (RingHom.ker
      (algebraMap (Ainf.R0 p O ε) ((Ainf.ainfTowerL p O hv ε hε).O : Type))), eq_bot_iff]
    refine Ideal.mul_le.2 fun x hx y hy => ?_
    rw [Ideal.mem_bot]
    exact thetaBar_mul p O hv ε hε x y hx hy
  obtain ⟨G, _, _, Q, ψ, ψ₂, hGab, hQ, hQ1, hQ2, hQs, hQa, hQp, hψ, hsq, hlam⟩ :=
    GlobalTheory.T.exists_lift_principally_polarised_abelian_square_zero p C v ((Ainf.ainfTowerL p O hv ε hε).O : Type) hv' T P₀ io P φ h₁ h₂ h₃ h₄
      (Ainf.R0 p O ε) (algebraMap _ _) hπs hπk
  haveI : IsLocalRing (Ainf.R0 p O ε) :=
    Ainf.local_of_surj_sq _ hπs fun k hk => thetaBar_mul p O hv ε hε k k hk hk
  have hsm : SmoothOfRelativeDimension P.g G.hom :=
    GlobalTheory.T.smoothOfRelativeDimension_of_grpPullback_localRing (Ainf.R0 p O ε) _ (algebraMap _ _) G P.A ψ P.g hGab hψ P.smoothDim
  have hM := LB.isLB_pull hQ (lift (𝟙 G) (𝟙 G)).left
  obtain ⟨hθ, hmult⟩ := GlobalTheory.T.cube_trivial_and_finite_flat_surjective_mul_abelianScheme (Ainf.R0 p O ε) G _ Q hGab hM hQa hQ
  have hfin := hmult p (Fact.out : p.Prime).one_le
  letI : Algebra (Ainf.R0 p O ε) C :=
    ((algebraMap ((Ainf.ainfTowerL p O hv ε hε).O : Type) C).comp
      (algebraMap (Ainf.R0 p O ε) ((Ainf.ainfTowerL p O hv ε hε).O : Type))).toAlgebra
  haveI : IsScalarTower (Ainf.R0 p O ε) ((Ainf.ainfTowerL p O hv ε hε).O : Type) C :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hpC : ((p : ℕ) : C) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hcard := GlobalTheory.T.card_torsion_of_polarisedAbelianScheme_lift (Ainf.R0 p O ε) ((Ainf.ainfTowerL p O hv ε hε).O : Type) C G P ψ hψ p hpC
  have hinv : ∀ a, cjZ OE (cjZ OE a) = a := fun a => by simp [cjZ]
  have hros : ∀ a, ∃ t : LB.Gen (LB.LinComb Q (K := Fin 2)
      ![(lift (fst P.A P.A ≫ o.toRingAct.act a) (snd P.A P.A)).left ≫ ψ₂,
        (lift (fst P.A P.A) (snd P.A P.A ≫ o.toRingAct.act (cjZ OE a))).left ≫ ψ₂] ![1, -1]),
      t.IsGen := fun a =>
    GlobalTheory.T.exists_generator_of_rosatiAdjoint_lambdaBundle _ P _ Q ψ₂ hQ hlam _ _ (o.toRingAct.hom a) (o.toRingAct.hom _) (o.rosati a)
  obtain ⟨B, e, Ad, he1, he2, he3, hAd, Dt, D, hD1, hD2, hD3, -⟩ :=
    GlobalTheory.T.exists_periodTowerDatum_of_abelianScheme_symmetricBundle p O hv ε hε P.g G Q hGab hsm hQ hθ hQ1 hQ2 hQs hfin.1 hfin.2.1 hfin.2.2 hv'
      (fun x hx => hQp _ x hx) (hcard.trans (by rw [h₃])) P.A ψ ψ₂ P.isAb hψ hsq OE (cjZ OE)
      o.toRingAct hinv hros
  obtain ⟨Y, hY, hYact⟩ := GlobalTheory.T.abelianFunctorNilChart_of_nilpotent_chart (Ainf.R0 p O ε) G B e he1 he2 he3
    (Ainf.ainfTowerL p O hv ε hε).O P.A ψ hψ P.g F.F X hX
  have hα0 : ∀ a j, MvPowerSeries.constantCoeff (α a j) = 0 := by
    intro a j
    have h := hα a
    unfold Reads at h
    exact h.1 j
  exact htd_of_dat p C v (Ainf.ainfTowerL p O hv ε hε) hv' hp.out hc P.g OE B F Y hY α hα0
    (fun a => (Ad a).a) (fun b R s a ha => hYact _ (α b) (Ad b).a (hα b) (hAd b) R s a ha) Dt _ D
    hD1 hD2 hD3

theorem exists_htd_chars : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (T : Type) [CommRing T] [IsNoetherianRing T] (P₀ : Out.PolAV (Geo.Tor.Sp T)) (io : T →+* O) (P : Out.PolAV (Geo.Tor.Sp O)) (φ : P.A.left ⟶ P₀.A.left), Geo.Tor.IsGrpPullback P.A P₀.A (Geo.Tor.spMap io) φ → Geo.Tor.LBIso P.L (P₀.L.pull φ) → P.g = P₀.g → 1 ≤ P.g → ∀ (g : ℕ), P.g = g → ∀ (OE : Type) [CommRing OE] [StarRing OE] (o : P.OAct OE) (F : FGLaw O g) (X : Fam P.A g), NilChart P.A F.F X → ∀ α : OE → Fin g → PS O 1 g, (∀ a, Reads X X (o.act a) (α a)) → ∃ (cp : O) (_ : HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (S : Matrix (Fin g) (Fin g) O), H.P = 0 ∧ H.PL = 0 ∧ IsUnit S ∧ (∀ a : OE, lin (α a) * S = S * H.ρL (1 ⊗ₜ[ℤ] a)) ∧ ∀ i, ∃ u : PS O 1 g, IsCh F.F u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ T _ _ P₀ io P φ h₁ h₂ h₃ h₄ g hg OE _ _ o F X hX α hα
  subst hg
  obtain ⟨ε, hε⟩ := exists_eps (p := p) (C := C) (v := v) (O := O) hv
  letI : Algebra ((Ainf.ainfTowerL p O hv ε hε).O : Type) C := ‹Algebra O C›
  haveI : Fact ¬IsUnit (p : ((Ainf.ainfTowerL p O hv ε hε).O : Type)) := ‹Fact ¬IsUnit (p : O)›
  haveI : IsAdicComplete (Ideal.span {(p : ((Ainf.ainfTowerL p O hv ε hε).O : Type))})
      ((Ainf.ainfTowerL p O hv ε hε).O : Type) := ‹IsAdicComplete (Ideal.span {(p : O)}) O›
  letI : Algebra ℤ_[p] ((Ainf.ainfTowerL p O hv ε hε).O : Type) := ‹Algebra ℤ_[p] O›
  refine ⟨(Ainf.ainfTowerL p O hv ε hε).c, GlobalTheory.T.hodgeTate_datum_hypotheses_period_tower p O hv ε hε OE, ?_⟩
  exact htd_of_tower p C v O hv ε hε (Ainf.ainfTowerL p O hv ε hε) rfl hv T P₀ io P φ h₁ h₂ h₃ h₄
    OE o F X hX α hα

end GlobalTheory.ChF
