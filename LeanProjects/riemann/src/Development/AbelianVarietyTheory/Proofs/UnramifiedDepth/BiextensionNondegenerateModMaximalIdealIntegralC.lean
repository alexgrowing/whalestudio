import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushHomBijective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationTriplesCompleteDVRTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueFrameSer
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AlphaPMultiplicativeCharacterEqOneStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqOneOfTangentVectorEqOneStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPthRootTorusPointNilpotentAugmentedExtStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AlphaPHomomorphismCubicalWeilTrivialRationalTorsStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubicalWeilTrivialOfLocalArtinianPointsStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIsTorusExtensionOnPointsModIdealStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianPartProjectionRespectsOrthogonalityStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFiniteExtensionSplitSpecialFibrePointStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTorusExtensionPointsPullbackFieldPointStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralFramedPointModelPolarisedGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFormalChartPointNilpotentCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.UniversalChartPointsOverFieldPointStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FramePartialLawsNilpotentCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NotNondegenerateOfDegenerateSeriesDirectionStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAlgClosedResidueFieldValuedFieldStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsRingHomValuationRingOfEmbOKStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DegenerateDirectionOfNotNondegenerateStatement

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

section Steps

variable {Ω : Type} [Field Ω] {p : ℕ} [Fact p.Prime] [CharP Ω p] {S S' : Scheme.{0}} {s : Sp Ω ⟶ S} {s' : Sp Ω ⟶ S'}
  {G : Over S} [GrpObj G] {B : Over S'} [GrpObj B] {X : Type} [AddCommGroup X] {τ : PtHom s s' G B} {io : TorHom s G X}

theorem pow_p_of_sq {A : Type} [CommRing A] {e : A} (he : e ^ 2 = 0) : e ^ p = 0 :=
  pow_eq_zero_of_le (Fact.out : p.Prime).two_le he

theorem eps_pow : (DualNumber.eps : DualNumber Ω) ^ p = 0 :=
  pow_p_of_sq (by rw [pow_two, DualNumber.eps_mul_eps])

theorem eq_one_of_torus (h : IsTorExt s s' G B X τ io) {g : Fam s G} (hg : IsAlpha p s G g)
    (h1 : τ _ (g (DualNumber Ω) DualNumber.eps) = 1) : g (DualNumber Ω) DualNumber.eps = 1 := by
  classical
  have h2 := GlobalTheory.T.eq_one_of_tangent_vector_eq_one Ω p S' s' B _ (hg.map h) h1
  have h3 : ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), ∃ χ, a ^ p = 0 → io A χ = g A a := fun A _ _ a => by
    by_cases ha : a ^ p = 0
    · obtain ⟨χ, hχ⟩ := (h.2.2.2.1 A _).1 (h2 A a ha)
      exact ⟨χ, fun _ => hχ⟩
    · exact ⟨1, fun k => absurd k ha⟩
  choose χ hχ using h3
  have h4 : χ (DualNumber Ω) DualNumber.eps = 1 := MonoidHom.ext fun x =>
    GlobalTheory.T.alphaP_multiplicativeCharacter_eq_one Ω p (fun A _ _ a => χ A a x) (fun A A' _ _ _ _ f a ha => by
      have ha' : f a ^ p = 0 := by rw [← map_pow, ha, map_zero]
      have : χ A' (f a) = (Units.map (f : A →* A')).comp (χ A a) :=
        h.2.2.1 A' (by rw [hχ A' _ ha', h.2.1, hχ A a ha, hg.1 A A' f a ha])
      exact DFunLike.congr_fun this x) (fun A _ _ a a' ha ha' => by
      have hs : (a + a') ^ p = 0 := by
        rcases subsingleton_or_nontrivial A with _ | _
        · exact Subsingleton.elim _ _
        · have := charP_of_injective_algebraMap (algebraMap Ω A).injective p
          rw [add_pow_char, ha, ha', add_zero]
      have : χ A (a + a') = χ A a * χ A a' :=
        h.2.2.1 A (by rw [map_mul, hχ A _ hs, hχ A a ha, hχ A a' ha', hg.2 A a a' ha ha'])
      exact DFunLike.congr_fun this x) _ _ eps_pow
  rw [← hχ _ _ eps_pow, h4, map_one]

variable [IsCommMonObj G] [IsCommMonObj B] {L : RigLB G} {c : CubicalStr G L} {M : RigLB B} {c' : CubicalStr B M}

theorem Orth.map [Module.Free ℤ X] [Module.Finite ℤ X] (h : IsTorExt s s' G B X τ io) (ht : Transfer p c c' τ)
    {g : Fam s G} (hg : IsAlpha p s G g) (ho : Orth p s G c g) : Orth p s' B c' (fun A _ _ a => τ A (g A a)) := by
  intro A _ _ π hπ e he y hy hyp
  have hp := (Fact.out : p.Prime).ne_zero
  obtain ⟨x, hx, rfl⟩ := h.2.2.2.2 A π hπ y hy
  obtain ⟨χ, hχ⟩ := (h.2.2.2.1 A (x ^ p)).1 (by rw [map_pow, hyp])
  have h1 : (Units.map (π : A →* Ω)).comp χ = 1 :=
    h.2.2.1 Ω (by rw [h.2.1, hχ, MonObj.comp_pow, hx, one_pow, map_one])
  obtain ⟨A', _, _, f, π', χ', hf, hc, hn, h2, h3⟩ := GlobalTheory.T.exists_pth_root_torus_point_nilpotent_augmented_ext Ω p X A π hπ χ fun a =>
    congrArg Units.val (DFunLike.congr_fun h1 a)
  have h4 : (Units.map (π' : A' →* Ω)).comp χ' = 1 := MonoidHom.ext fun a => Units.ext (h2 a)
  have k := ht A' _ _ (ho A' π' hn (f e) (by rw [← map_pow, he, map_zero]) ((homAt s f ≫ x) * (io A' χ')⁻¹)
    (by rw [MonObj.comp_mul, GrpObj.comp_inv, ← h.2.1, h4, map_one, inv_one, _root_.mul_one, ← Category.assoc, hom_comp,
      hc, hx])
    (by rw [mul_pow, inv_pow, ← map_pow, h3, h.2.1, hχ, MonObj.comp_pow, mul_inv_cancel]))
  rw [hg.1 A A' f e (pow_p_of_sq he), map_mul, map_inv, (h.2.2.2.1 A' _).2 ⟨χ', rfl⟩, inv_one, _root_.mul_one,
    h.1, h.1] at k
  exact cubWeil_of_injective f hf ((hg.map h).pow_eq_one hp (pow_p_of_sq he)) hyp k

theorem NonDeg.of_torExt [Module.Free ℤ X] [Module.Finite ℤ X] (h : IsTorExt s s' G B X τ io) (ht : Transfer p c c' τ)
    (hB : NonDeg p s' B c') : NonDeg p s G c := fun _ hg ho =>
  eq_one_of_torus h hg (hB _ (hg.map h) (ho.map h ht hg))

theorem NonDeg.of_perf [IsAlgClosed Ω] (hf : IsFinite ((𝟙 G) ^ p : G ⟶ G).left) (hP : Perf p G c) :
    NonDeg p s G c := by
  intro g hg ho
  have hp := (Fact.out : p.Prime).ne_zero
  have : Module.Finite Ω (DualNumber Ω) := inferInstanceAs (Module.Finite Ω (Ω × Ω))
  refine hP _ _ (hg.pow_eq_one hp eps_pow) (GlobalTheory.T.cubicalWeil_trivial_of_localArtinian_points Ω S s G L c p hf (DualNumber Ω) _ (hg.pow_eq_one hp eps_pow)
    fun A _ _ π hπ f y hy => ?_)
  have he : f DualNumber.eps ^ 2 = 0 := by rw [← map_pow, pow_two, DualNumber.eps_mul_eps, map_zero]
  have hx : (homAt s π ≫ y) ^ p = 1 := by rw [← MonObj.comp_pow, hy, MonObj.comp_one]
  have k₁ := GlobalTheory.T.alphaP_homomorphism_cubicalWeil_trivial_rational_torsion Ω p S s G L c g hg _ hx A _ (pow_p_of_sq he)
  have k₂ := ho A π hπ _ he (y * (homAt s (Algebra.ofId Ω A) ≫ homAt s π ≫ y)⁻¹)
    (by rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc (homAt s π), hom_comp,
      Subsingleton.elim (π.comp (Algebra.ofId Ω A)) (AlgHom.id Ω Ω), hom_id, Category.id_comp, mul_inv_cancel])
    (by rw [mul_pow, inv_pow, hy, k₁.2.1, inv_one, _root_.mul_one])
  have k := cubWeil_mul_right k₂ k₁
  rwa [inv_mul_cancel_right, hg.1 _ A f _ eps_pow] at k

end Steps

theorem perf_of_polAV {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (P : Out.PolAV (Sp O))
    [IsCommMonObj P.A] [IsNoetherianRing O] (L : RigLB P.A) (hL : L.L = P.L) (c : CubicalStr P.A L) {n : ℕ} (hn : 1 ≤ n) :
    IsFinite ((𝟙 P.A) ^ n : P.A ⟶ P.A).left ∧ Perf n P.A c := by
  have hl := GlobalTheory.firstFiveLaws.1
  let K := AlgebraicClosure (FractionRing O)
  have hi : Function.Injective (algebraMap O K) := by
    rw [IsScalarTower.algebraMap_eq O (FractionRing O) K]
    exact (algebraMap (FractionRing O) K).injective.comp (IsFractionRing.injective O _)
  have : CharZero K := charZero_of_injective_algebraMap hi
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨f₁, f₂, f₃⟩ := GlobalTheory.T.finite_flat_surjective_mul_by_n_abelianScheme hl O P.A P.isAb P.L P.isLB P.ample n hn
  refine ⟨f₁, GlobalTheory.T.eq_one_of_cubWeil_trivial_of_generic O K hi P.A P.g P.smoothDim L c n hn f₁ f₂
    ((hl.mulN _ P n hn).2.2.2.2 K _ hnK) fun y hy hp => ?_⟩
  have ht := CubNondeg.main hl _ P.A P.isAb L c K _ n hnK f₁ f₂ f₃ y hy hp
  rw [hL] at ht
  obtain ⟨u, hu⟩ := ht
  exact P.ktriv K _ y fun _ => ⟨⊤, trivial, _, LB.isGen_genPull _ u hu _⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem nonDeg_of_polAt {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.LN.CDvr V) (t : SAB H (Sp V))
    (ht : GlobalTheory.LN.PolAt t (Out.jK V)) {Ω : Type} [Field Ω] [IsAlgClosed Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p]
    (β : V →+* Ω) (hβ : ∀ a ∈ maximalIdeal V, β a = 0) : NonDeg p (spMap β) t.G t.cub := by
  obtain ⟨W, _, _, _, f, β', t', m, hW, hf, hβ', ht', hs⟩ := GlobalTheory.T.exists_finite_extension_split_special_fibre_point E H V hV t ht Ω β hβ
  obtain ⟨τ, io, h₁, h₂⟩ := GlobalTheory.T.exists_torusExtension_points_pullback_fieldPoint E H _ _ _ t t' m Ω (spMap β) (spMap β') (by
    rw [← hf]; exact (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom β')).symm) p
  refine NonDeg.of_torExt h₁ h₂ ?_
  obtain ⟨P, -⟩ := GlobalTheory.LN.uDvrSt_holds E H W hW t' ht' hs
  obtain ⟨τ', io', k₁, k₂⟩ := GlobalTheory.T.exists_isTorusExtensionOnPoints_mod_ideal W _ P.D.toPre t'.G (P.U.gt 0) Ω β' hβ'
  have k₃ := GlobalTheory.T.abelianPart_projection_respects_orthogonality W _ P.D P.A t'.G P.U.toUnifPre Ω β' hβ' τ' k₂ p
  have := hW.1
  have := hW.2.2
  obtain ⟨f₁, f₂⟩ := perf_of_polAV P.D.toPre.P ⟨_, P.D.toPre.rig, P.D.toPre.P.isLB, P.D.toPre.rig_gen⟩ rfl
    P.D.toPre.cub (Fact.out : p.Prime).one_le
  have k₄ := NonDeg.of_torExt k₁ k₃ (NonDeg.of_perf f₁ f₂)
  have key : ∀ (L : RigLB t'.G) (_ : L = t'.PP) (c : CubicalStr t'.G L), NonDeg p (spMap β') t'.G c →
      NonDeg p (spMap β') t'.G t'.cub := by
    rintro L rfl c hc
    rwa [PtGermCompare.cubical_unique (PtGermCompare.surjective_cube P.U.toUnifPre) t'.cub c]
  exact key _ P.bundle _ k₄

theorem ev_map_eq_one {R R' : Type} [CommRing R] [CommRing R'] (β : R →+* R') {d : ℕ} (f : PS R 3 d)
    (a : Fin 3 → Germ.Pt R 2 d) (a' : Fin 3 → Germ.Pt R' 2 d) (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0)
    (h' : ∀ j i, a' j i = MvPowerSeries.map β (a j i)) (h : ev a f = 1) : ev a' (MvPowerSeries.map β f) = 1 := by
  have := MvPowerSeries.map_subst (a := fun q : Fin 3 × Fin d => a q.1 q.2)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => ha q.1 q.2) (h := β) f
  rw [show MvPowerSeries.subst (fun q : Fin 3 × Fin d => a q.1 q.2) f = 1 from h, map_one] at this
  unfold ev
  simp only [h']
  exact this.symm

theorem ndg_at_chart : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) [StarRing (NumberField.RingOfIntegers E)], NondegenerateCharts Xo c := by
  intro E _ _ _ H Dw l Xo c inst hstar T io y C3 C _ _ V ι' hι k Y hY
  obtain rfl := PowGerm.starSt E H inst hstar
  letI := H.starRing
  letI := io.toAlgebra
  by_contra hN
  obtain ⟨Ω, _, _, _, ρ, hρ⟩ := GlobalTheory.T.exists_algClosed_residueField_valuedField C V Y.algClosed
  obtain ⟨j, hj, hjm⟩ := GlobalTheory.T.exists_ringHom_valuationRing_of_embOK T C V ι' hι
  have : Fact V.l.Prime := ⟨V.l_prime⟩
  obtain ⟨BT, hF, -, h1, h2, -⟩ := integralChart_formalBiext E H Dw l Xo c T io y C3
  have hF0 : ∀ i, MvPowerSeries.constantCoeff (C3.FT i) = 0 := fun i => hF ▸ BT.G.const i
  have e : V.RR.subtype.comp j = ι'.comp (algebraMap T.V T.Fr) := RingHom.ext hj
  have hD := GlobalTheory.T.degenerate_direction_of_not_nondegenerate C V _ _ Y T.V j C3.FT C3.ph2T hF0
    (fun i => by rw [hY.F, e, MvPowerSeries.map_comp]; exact congrArg _ (C3.gen.1.1 i))
    (by rw [hY.ph2, e, MvPowerSeries.map_comp]; exact congrArg _ C3.gen.1.2.2.2.1) Ω ρ hρ hN
  obtain ⟨P, hP, hL⟩ := GlobalTheory.T.exists_formalChart_point_nilpotent_coordinates E H T.V C3.I.G _ _ _ _ _ _ C3.chartT hF0 Ω (ρ.comp j)
  refine GlobalTheory.T.not_nondegenerate_of_degenerate_series_direction Ω V.l _ _ C3.I.G.G _ C3.I.G.cub _ _ (MvPowerSeries.map (ρ.comp j) C3.ph1T) _ P
    (fun i => by rw [MvPowerSeries.constantCoeff_map, hF0, map_zero]) ?_ ?_ ?_ hL
    (GlobalTheory.T.universalChart_points_over_field_point E H T.V C3.I.G _ _ (PowGerm.univSt_holds E H Dw l Xo c T io y C3) Ω _ P hP)
    (GlobalTheory.T.frame_partial_laws_nilpotent_coordinates E H T.V C3.I.G _ _ _ _ _ _ _ _ _ C3.frameT hF0 Ω _ P hP) hD
    (nonDeg_of_polAt ⟨T.dvr, T.cpl, T.ch0⟩ C3.I.G (GlobalTheory.T.integralFramedPoint_model_polarised_generic_fibre E H Dw l Xo c T io y.1 C3.I) V.l _
      fun a ha => (hρ _).2 (hjm a ha))
  · refine ev_map_eq_one _ _ _ _ ?_ ?_ (h1 ▸ BT.cocycleLeft_zero_fst) <;> intro a b <;> fin_cases a <;> simp [pt]
  · refine ev_map_eq_one _ _ _ _ ?_ ?_ (h1 ▸ BT.cocycleLeft_zero_snd) <;> intro a b <;> fin_cases a <;> simp [pt]
  · refine ev_map_eq_one _ _ _ _ ?_ ?_ (h2 ▸ BT.cocycleRight_zero_fst) <;> intro a b <;> fin_cases a <;> simp [pt]

end GlobalTheory.AlphaPair
end
