import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.DualLattices.ExistsPrimitiveRoot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PeriodDatumSignCharactersMemEvalImage
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTateMatricesLink
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPolAVFiniteTypeSubring
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
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualTowerHodgeTateDatumStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.Ar.GR

private theorem thetaBar_surj (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) :
    Function.Surjective (Ainf.thetaBar p O hv ε hε) := by
  intro b
  obtain ⟨a, rfl⟩ := Ainf.theta_surj p O hv b
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

private theorem thetaBar_mul (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
    (x y : Ainf.R0 p O ε) (hx : x ∈ RingHom.ker (Ainf.thetaBar p O hv ε hε))
    (hy : y ∈ RingHom.ker (Ainf.thetaBar p O hv ε hε)) : x * y = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have ha : a ∈ RingHom.ker (WittVector.fontaineTheta O p) := hx
  have hb : b ∈ RingHom.ker (WittVector.fontaineTheta O p) := hy
  rw [Ainf.ker_theta p O hv ε hε, Ideal.mem_span_singleton'] at ha hb
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton'.2 ⟨a' * b', by ring⟩

private theorem ptOf_act {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] (g : ℕ) (B : BX R₀) (O : LAlg R₀)
    (τ : Ix g → ℕ → B.G O) (h0 : ∀ i, p • τ i 0 = 0) (f : B.G O →+ B.G O)
    (M : Matrix (Ix g) (Ix g) ℤ_[p])
    (hf : ∀ j, f (τ j 0) = ∑ k, (PadicInt.toZModPow (0 + 1) (M k j)).val • τ k 0) (t : TT p g) :
    f (ptOf B τ (red p g t)) = ptOf B τ (red p g (M *ᵥ t)) := by
  have hsum : ∀ (s : Finset (Ix g)) (c : Ix g → ZMod p) (x : B.G O), p • x = 0 →
      (∑ j ∈ s, c j).val • x = ∑ j ∈ s, (c j).val • x := by
    intro s c x hx
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert b s hb ih =>
      rw [Finset.sum_insert hb, Finset.sum_insert hb, GlobalTheory.TateMatrices.val_add_smul _ _ x hx, ih]
  simp only [ptOf, red, map_sum, map_nsmul, hf]
  have hred : ∀ k, PadicInt.toZMod ((M *ᵥ t) k) = ∑ j, PadicInt.toZMod (M k j) * PadicInt.toZMod (t j) := by
    intro k
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  simp only [hred]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hsum _ _ _ (h0 k)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, GlobalTheory.TateMatrices.val_mul_smul _ _ _ (h0 k), GlobalTheory.TateMatrices.toZMod_val_smul _ _ (h0 k)]

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
      (∀ i, ∃ u : PS (Tw.O : Type) 1 g, IsCh F.F u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i) ∧
      H.AA.carrier = D.evImg C ∧ H.ρ = D.H.ρ := by
  obtain ⟨S, hS, hT⟩ := GlobalTheory.T.exists_tangentChartMatrix_of_basis R₀ B Tw.O g F Y hY D.ch.gb
  refine ⟨GlobalTheory.EvClose.htdOfDat D C v (Function.Injective.isDomain _ hv.hom_inj) hv.hom_inj, S, h₁, h₂, hS,
    fun a => ?_, fun i => ?_, rfl, rfl⟩
  · exact GlobalTheory.T.jacobian_mul_tangentChartMatrix_intertwines R₀ B Tw.O g F Y hY D.ch.gb S hT (A a) (α a) _ (hα a) (hA a) (h₃ a)
  · obtain ⟨u, hu, hP⟩ := GlobalTheory.T.exists_character_pairSer_alt R₀ B Tw.O g F Y hY p hp hc (D.L.τ i) (D.L.τ_tors i) (D.L.τ_compat i)
    refine ⟨u, hu, ?_⟩
    rw [GlobalTheory.T.linear_part_pairing_series_eq_height R₀ B p Tw Dt g Y D.ch.gb S hT (D.L.τ i) u hu.1 hP (D.L.ht i) (D.L.ht_spec i)]
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
    [Algebra ℤ_[p] (Tw.O : Type)] (hvp : v (p : C) < 1)
    (T : Type) [CommRing T] [IsNoetherianRing T] (P₀ : Out.PolAV (Geo.Tor.Sp T)) (io : T →+* (Tw.O : Type))
    (P : Out.PolAV (Geo.Tor.Sp (Tw.O : Type))) (φ : P.A.left ⟶ P₀.A.left)
    (h₁ : Geo.Tor.IsGrpPullback P.A P₀.A (Geo.Tor.spMap io) φ) (h₂ : Geo.Tor.LBIso P.L (P₀.L.pull φ))
    (h₃ : P.g = P₀.g) (h₄ : 1 ≤ P.g) (OE : Type) [CommRing OE] [StarRing OE] (o : P.OAct OE)
    (F : FGLaw (Tw.O : Type) P.g) (X : Fam P.A P.g) (hX : NilChart P.A F.F X)
    (α : OE → Fin P.g → PS (Tw.O : Type) 1 P.g) (hα : ∀ a, Reads X X (o.act a) (α a)) :
    ∃ (H : HodgeTateDatum p P.g v (Tw.O : Type) (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) Tw.c)
      (S : Matrix (Fin P.g) (Fin P.g) (Tw.O : Type))
      (pt : Nb p P.g → (sp (R₀ := (Tw.O : Type)) (Tw.O : Type) ⟶ P.A)),
      H.P = 0 ∧ H.PL = 0 ∧ IsUnit S ∧ (∀ a : OE, lin (α a) * S = S * H.ρL (1 ⊗ₜ[ℤ] a)) ∧
      (∀ i, ∃ u : PS (Tw.O : Type) 1 P.g, IsCh F.F u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i) ∧
      IsTorsPts P.A p pt ∧ (∀ T : TorsRep P.A p, H.AA.carrier = torsFun C T pt) ∧
      ∀ (a : OE) (t : TT p P.g), pt (red p P.g (H.ρ (1 ⊗ₜ[ℤ] a) *ᵥ t)) = pt (red p P.g t) ≫ o.act a := by
  have hsurj : Function.Surjective (algebraMap (Ainf.R0 p O ε) (Tw.O : Type)) := by
    subst hTw; exact thetaBar_surj p O hv ε hε
  have hmul : ∀ x y : Ainf.R0 p O ε, x ∈ RingHom.ker (algebraMap (Ainf.R0 p O ε) (Tw.O : Type)) →
      y ∈ RingHom.ker (algebraMap (Ainf.R0 p O ε) (Tw.O : Type)) → x * y = 0 := by
    subst hTw; exact thetaBar_mul p O hv ε hε
  have hker : RingHom.ker (algebraMap (Ainf.R0 p O ε) (Tw.O : Type)) ^ 2 = ⊥ := by
    refine (pow_two _).trans (eq_bot_iff.2 ?_)
    exact Ideal.mul_le.2 fun x hx y hy => (Submodule.mem_bot _).2 (hmul x y hx hy)
  haveI : IsLocalRing (Ainf.R0 p O ε) := Ainf.local_of_surj_sq _ hsurj (fun k hk => hmul k k hk hk)
  obtain ⟨G, iG, cG, Q, ψ, ψ₂, hab, hQ, t₁, t₂, hsym, hamp, hnd, hpb, hsq, hΛ⟩ :=
    GlobalTheory.T.exists_lift_principally_polarised_abelian_square_zero p C v (Tw.O : Type) hv' T P₀ io P φ h₁ h₂ h₃ h₄ _ _ hsurj hker
  letI : Algebra (Ainf.R0 p O ε) C :=
    ((algebraMap (Tw.O : Type) C).comp (algebraMap (Ainf.R0 p O ε) (Tw.O : Type))).toAlgebra
  haveI : IsScalarTower (Ainf.R0 p O ε) (Tw.O : Type) C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hp0 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hsm := GlobalTheory.T.smoothOfRelativeDimension_of_grpPullback_localRing _ _ _ G P.A ψ P.g hab hpb P.smoothDim
  obtain ⟨hθ, hn⟩ := GlobalTheory.T.cube_trivial_and_finite_flat_surjective_mul_abelianScheme _ G _ Q hab (LB.isLB_pull hQ _) hamp hQ
  obtain ⟨hf₁, hf₂, hf₃⟩ := hn p hp0
  have hcard := GlobalTheory.T.card_torsion_of_polarisedAbelianScheme_lift _ _ C G P ψ hpb p (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hros := fun a : OE =>
    GlobalTheory.T.exists_generator_of_rosatiAdjoint_lambdaBundle _ P _ Q ψ₂ hQ hΛ _ _ (o.hom a) (o.hom (star a)) (o.rosati a)
  have key : ∃ (B : BX (Ainf.R0 p O ε)) (e : ∀ R : LAlg (Ainf.R0 p O ε), B.G R → (sp (R₀ := (Ainf.R0 p O ε)) (R : Type) ⟶ G)) (Ad : OE → OAdj B Tw.O), (∀ R, Function.Bijective (e R)) ∧ (∀ R x y, e R (x + y) = e R x * e R y) ∧ (∀ {R S : LAlg (Ainf.R0 p O ε)} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) ∧ (∀ a, (∀ {R : LAlg (Ainf.R0 p O ε)} (s : LHom Tw.O R) (x : B.G R) (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ P.A), x'.left ≫ ψ = (e R x).left → (x' ≫ o.act a).left ≫ ψ = (e R ((Ad a).a.f s x)).left)) ∧ ∃ (Dt : DualTower Tw) (D : Dat p P.g B Tw Dt (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) Tw.c), D.H.P = 0 ∧ D.H.PL = 0 ∧ (∀ a {R S : LAlg (Ainf.R0 p O ε)} (s : LHom Tw.O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin P.g) (i : π.ker) (m : Fin P.g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (D.H.ρL (1 ⊗ₜ[ℤ] a) k l) * i) → (Ad a).a.f s (B.tg π hπ (D.ch.gb l ⊗ₜ[(Ainf.R0 p O ε)] i)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[(Ainf.R0 p O ε)] m k)) ∧ (∀ a j, (Ad a).a.f (LHom.id Tw.O) (D.L.τ j 0) = ∑ k, (PadicInt.toZModPow (0 + 1) (D.H.ρ (1 ⊗ₜ[ℤ] a) k j)).val • D.L.τ k 0) := by
    subst hTw
    obtain ⟨B, e, Ad, k₁, k₂, k₃, k₄, Dt, D, k₅, k₆, k₇, k₈⟩ :=
      GlobalTheory.T.exists_periodTowerDatum_of_abelianScheme_symmetricBundle p O hv ε hε P.g G Q hab hsm hQ hθ t₁ t₂ hsym hf₁ hf₂ hf₃ hv' (hnd _) hcard
        P.A ψ ψ₂ P.isAb hpb hsq OE (cjZ OE) o.toRingAct (fun a => star_star a) hros
    exact ⟨B, e, Ad, k₁, k₂, k₃, k₄, Dt, D, k₅, k₆, k₇, fun a j => k₈ a j 0⟩
  obtain ⟨B, e, Ad, k₁, k₂, k₃, k₄, Dt, D, k₅, k₆, k₇, k₈⟩ := key
  obtain ⟨Y, hY, hR⟩ := GlobalTheory.T.abelianFunctorNilChart_of_nilpotent_chart _ G B e k₁ k₂ k₃ Tw.O P.A ψ hpb P.g F.F X hX
  obtain ⟨H, S, e₁, e₂, e₃, e₄, e₅, e₆, e₇⟩ :=
    htd_of_dat p C v Tw hv' hp.out hc P.g OE B F Y hY α (fun a => (hα a).1) (fun a => (Ad a).a)
      (fun b => hR _ _ _ (hα b) (k₄ b)) Dt Tw.c D k₅ k₆ k₇
  obtain ⟨pt, hpt, hT, hE⟩ :=
    GlobalTheory.T.dual_tower_hodge_tate_datum p C v P.g B Tw Dt hv' hvp _ (sigE p OE) Tw.c D G e k₁ k₂ k₃ P.A ψ hpb
  refine ⟨H, S, pt, e₁, e₂, e₃, e₄, e₅, hT, fun T => e₆.trans (hE T), fun a t => ?_⟩
  have h0 : ∀ i, p • D.L.τ i 0 = 0 := fun i => by
    have h := D.L.τ_tors i 0
    rwa [zero_add, pow_one] at h
  have hAct := ptOf_act p P.g B Tw.O D.L.τ h0 ((Ad a).a.f (LHom.id Tw.O)) (D.H.ρ (1 ⊗ₜ[ℤ] a)) (k₈ a) t
  have hA := k₄ a (LHom.id Tw.O) (ptOf B D.L.τ (red p P.g t)) (pt (red p P.g t)) (hpt _)
  rw [hAct] at hA
  rw [e₇]
  apply Over.OverMorphism.ext
  apply hpb.1.hom_ext
  · rw [hpt]
    exact hA.symm
  · simp

theorem exists_htd_act : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (P : Out.PolAV (Geo.Tor.Sp O)), 1 ≤ P.g → ∀ (g : ℕ), P.g = g → ∀ (OE : Type) [CommRing OE] [StarRing OE] (o : P.OAct OE) (F : FGLaw O g) (X : Fam P.A g), NilChart P.A F.F X → ∀ α : OE → Fin g → PS O 1 g, (∀ a, Reads X X (o.act a) (α a)) → ∃ (cp : O) (_ : HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (S : Matrix (Fin g) (Fin g) O) (pt : Nb p g → (sp (R₀ := O) O ⟶ P.A)), H.P = 0 ∧ H.PL = 0 ∧ IsUnit S ∧ (∀ a : OE, lin (α a) * S = S * H.ρL (1 ⊗ₜ[ℤ] a)) ∧ (∀ i, ∃ u : PS O 1 g, IsCh F.F u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i) ∧ IsTorsPts P.A p pt ∧ (∀ T : TorsRep P.A p, H.AA.carrier = torsFun C T pt) ∧ ∀ (a : OE) (t : TT p g), pt (red p g (H.ρ (1 ⊗ₜ[ℤ] a) *ᵥ t)) = pt (red p g t) ≫ o.act a := by
  intro p _ C _ _ _ v O _ iA hv iF iC iZ P h₄ g hg OE _ _ o F X hX α hα
  subst hg
  haveI : IsDomain O := Function.Injective.isDomain _ hv.hom_inj
  haveI : IsLocalRing O := Ainf.O_local O hv
  obtain ⟨R, P₀, φ, hft, hg₀, h₁, h₂⟩ := GlobalTheory.KeyTf.exists_polAV_finiteType_subring O P
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have hvp : v (p : C) < 1 := by
    have h := lt_of_le_of_ne (hv.map_le_one (p : O)) fun h => iF.out (hv.isUnit_iff_valuation_eq_one.2 h)
    simpa using h
  obtain ⟨ε, hε⟩ := exists_eps (p := p) C v O hv
  exact ⟨_, GlobalTheory.T.hodgeTate_datum_hypotheses_period_tower p O hv ε hε OE,
    @htd_of_tower p _ C _ _ _ v O _ _ _ _ hv ε hε _ rfl iA hv iF
      iC iZ hvp R _ _ P₀ R.subtype P φ h₁ h₂ hg₀.symm h₄ OE _ _ o F X hX α hα⟩

end GlobalTheory.CompanionTheory.Ar.GR
