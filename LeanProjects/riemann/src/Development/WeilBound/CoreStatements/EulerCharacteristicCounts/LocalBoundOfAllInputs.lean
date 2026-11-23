import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LatticeOpenCompactNhdsBasisStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CupFlipContinuousCocycleStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.FontaineBoundsAllRecordsStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.TateFilQuotAllRecordsStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.Adm8AllRecordsStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.FundamentalSequenceContinuityAllStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.BlochKatoDimensionRightExactStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.BlochKatoCokernelOfDualityEulerStatement
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.ExistsCochain

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace PositivityTheory.LocalTateOrthogonality.Bk

section Cochains

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem B1_le_Z1f (A : GRep G Qp LL O) : B1 A.ρ ≤ finiteCocycles PD A.ρ := by
  rintro _ ⟨v, rfl⟩
  refine ⟨⟨?_, fun g h => ?_⟩, v ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  · have : cob A.ρ v = fun g => A.ρ g v + -v := funext fun g => sub_eq_add_neg _ _
    rw [this]
    exact (A.cont v).add continuous_const
  · change A.ρ (g * h) v - v = A.ρ g v - v + A.ρ g (A.ρ h v - v)
    rw [map_mul, Module.End.mul_apply, map_sub]
    abel
  · change (A.ρ g v - v) ⊗ₜ[Qp] (1 : B) = A.ρ g v ⊗ₜ[Qp] PD.actB g 1 - _
    rw [map_one, sub_tmul]

theorem lc_mk {V X : Type} [AddCommGroup V] [Module O V] [TopologicalSpace V] [ContinuousAdd V]
    [TopologicalSpace X] {M : Submodule O V} (hM : IsOpen (M : Set V)) {c : X → V}
    (hc : Continuous c) : IsLocallyConstant fun g => (Submodule.Quotient.mk (c g) : V ⧸ M) := by
  refine IsLocallyConstant.iff_isOpen_fiber.mpr fun y => ?_
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have : (fun g => (Submodule.Quotient.mk (c g) : V ⧸ M)) ⁻¹' {Submodule.Quotient.mk y} =
      (fun g => c g + -y) ⁻¹' (M : Set V) := by
    ext g
    simp [Submodule.Quotient.eq, sub_eq_add_neg]
  rw [this]
  exact hM.preimage (hc.add continuous_const)

variable {PD}

theorem cobO_of_cobL [ContinuousAdd LL] {L1 : Lattice (O := O) (charRep (cycLL PD LL))}
    (hL1 : IsOpen (L1.T : Set LL)) {z : G × G → LL} (h : CobL PD z) : CobO PD L1 z := by
  obtain ⟨f, hf, rfl⟩ := h
  exact ⟨fun g => Submodule.Quotient.mk (f g), ⟨lc_mk hL1 hf, fun _ => trivial⟩, rfl⟩

variable {A A' : GRep G Qp LL O} {LA : Lattice (O := O) A.ρ} {LA' : Lattice (O := O) A'.ρ}
  {m : A.V →ₗ[LL] A'.V →ₗ[LL] LL} {L1 : Lattice (O := O) (charRep (cycLL PD LL))}

omit [TopologicalSpace G] [TopologicalSpace LL] in
theorem mk_liftD {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (c : V ⧸ L.T) :
    Submodule.Quotient.mk (liftD L c) = c := (Submodule.Quotient.mk_surjective L.T c).choose_spec

def pairD (hL1 : L1.T = LinearMap.range (Algebra.linearMap O LL)) (hm : IsDualLat1 PD LA LA' m) :
    ↥LA.T →+ (A'.V ⧸ LA'.T) →ₗ[O] (LL ⧸ L1.T) :=
  AddMonoidHom.mk' (fun t => LA'.T.mapQ L1.T ((m t.1).restrictScalars O) fun y hy => by
      obtain ⟨a, ha⟩ := (hm.2 y).1 hy t.1 t.2
      rw [hL1]
      exact ⟨a, ha.symm⟩)
    fun t t' => by
      apply Submodule.linearMap_qext
      ext y
      simp

theorem mk_cupLD (hL1 : L1.T = LinearMap.range (Algebra.linearMap O LL))
    (hm : IsDualLat1 PD LA LA' m) (d : G → A.V) (hd : ∀ g, d g ∈ LA.T) (c : G → A'.V ⧸ LA'.T)
    (p : G × G) : (Submodule.Quotient.mk (cupLD LA' m d c p) : LL ⧸ L1.T) =
      pairD hL1 hm ⟨d p.1, hd _⟩ (actD LA' p.1 (c p.2)) := by
  conv_rhs => rw [← mk_liftD LA' (c p.2)]
  rfl

theorem cobO_cup_iff (hL1 : L1.T = LinearMap.range (Algebra.linearMap O LL))
    (hm : IsDualLat1 PD LA LA' m) (d : G → A.V) (hd : ∀ g, d g ∈ LA.T) (b : G → A'.V) :
    CobO PD L1 (cupLD LA' m d fun g => Submodule.Quotient.mk (b g)) ↔
      CobO PD L1 (cupL A'.ρ m d b) := by
  unfold CobO
  simp only [mk_cupLD hL1 hm d hd]
  rfl

theorem cont_pair [IsTopologicalRing LL] (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL) :
    Continuous fun p : A.V × A'.V => m p.1 p.2 :=
  IsModuleTopology.continuous_bilinear_of_finite_left m

theorem exists_of_mem_HfD {c : G → A'.V ⧸ LA'.T} (hc : c ∈ HfD PD LA') :
    ∃ b ∈ finiteCocycles PD A'.ρ, c = fun g => Submodule.Quotient.mk (b g) := by
  obtain ⟨_, ⟨b, hb, rfl⟩, _, ⟨x, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hc
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨b + cob A'.ρ x, (finiteCocycles PD A'.ρ).add_mem hb (B1_le_Z1f PD A' ⟨x, rfl⟩), rfl⟩

theorem hfD_le (hT : IsOpen (LA'.T : Set A'.V)) : HfD PD LA' ≤ divisibleCocycles LA' := by
  intro c hc
  obtain ⟨b, hb, rfl⟩ := exists_of_mem_HfD hc
  refine ⟨lc_mk hT hb.1.1, fun g h => ?_⟩
  change _ = Submodule.Quotient.mk (b g + A'.ρ g (b h))
  exact congrArg Submodule.Quotient.mk (hb.1.2 g h)

end Cochains

theorem bkA_core (D : D7) (h8 : LocalSituation.adm8 D) (l : ℕ) [Fact l.Prime] (K : FinExt l)
    (hL : DualL ((D.loc l).PD K))
    (hEu : ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O]
      [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O →
      ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL),
        IsDual1 ((D.loc l).PD K) A.ρ A'.ρ P →
        finrank LL (H1V A.ρ) ≤
          finrank LL ↥(H0V A.ρ) + finrank LL ↥(H0V A'.ρ) + finrank ℚ_[l] ↥K.1 * finrank LL A.V)
    (hdim : LocalSituation.bkADim ((D.loc l).PD K)) : bkACore ((D.loc l).PD K) := by
  intro LL _ _ _ O _ _ hO A A' m hdR hm
  have ho := PositivityTheory.LocalTateOrthogonality.Orth.tdOrth D l K LL O hO A A' m hm hdR
  have hdR' := (h8 l K).1 LL O hO A A' m hdR hm
  have e1 := hdim LL O hO A hdR
  have e2 := hdim LL O hO A' hdR'
  have e3 := (h8 l K).2 LL O hO A A' m hdR hm
  have e4 := hEu LL O hO A A' m hm
  have e6 := hm.2.2.2
  unfold IsDR at hdR hdR'
  rw [← e6] at hdR'
  have hc : finrank LL (H1V A.ρ) ≤
      finrank LL (FiniteCohomology ((D.loc l).PD K) A.ρ) + finrank LL (FiniteCohomology ((D.loc l).PD K) A'.ρ) := by
    omega
  obtain ⟨h1, h2⟩ := hL LL O hO A A' m hm (finiteCocycles ((D.loc l).PD K) A.ρ) (finiteCocycles ((D.loc l).PD K) A'.ρ)
    (B1_le_Z1f _ A) (fun _ h => h.1) (B1_le_Z1f _ A') (fun _ h => h.1) ho hc
  exact ⟨fun a ha => ⟨ho a, h1 a ha⟩, fun b hb => ⟨fun h a ha => ho a ha b h, h2 b hb⟩⟩

theorem bkB_core (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (hD : DualD ((D.loc l).PD K))
    (hC : CobLO ((D.loc l).PD K)) (hA : bkACore ((D.loc l).PD K)) : bkBCore ((D.loc l).PD K) := by
  intro LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hdR hm
  obtain ⟨hA1, -⟩ := hA LL O hO A A' m hdR hm.1
  have := hO.2.2.2.1
  have hO' : IsOpen (L1.T : Set LL) := by rw [hL1]; exact hO.2.2.2.2
  obtain ⟨⟨hdom, hdvr, -⟩, -⟩ := id hO
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hTo : IsOpen (LA'.T : Set A'.V) := (GlobalTheory.T.lattice_open_compact_nhds_basis D l K LL O hO A' LA' ϖ hϖ).1
  obtain ⟨-, hF⟩ := GlobalTheory.T.cup_flip_continuous_cocycle D l K LL O hO A A' m hm.1
  have h1 : ∀ d ∈ latticeFiniteCocycles ((D.loc l).PD K) LA, ∀ s ∈ HfD ((D.loc l).PD K) LA',
      CobO ((D.loc l).PD K) L1 (cupLD LA' m d s) := fun d hd s hs => by
    obtain ⟨b, hb, rfl⟩ := exists_of_mem_HfD hs
    rw [cobO_cup_iff hL1 hm d fun g => hd.1.2 g trivial]
    exact cobO_of_cobL hO' ((hA1 d hd.1.1).1 hd.2 b hb)
  have h2 : ∀ d ∈ latticeCocycles LA, (∀ s ∈ HfD ((D.loc l).PD K) LA', CobO ((D.loc l).PD K) L1 (cupLD LA' m d s)) →
      d ∈ latticeFiniteCocycles ((D.loc l).PD K) LA := fun d hd H => by
    refine ⟨hd, (hA1 d hd.1).2 fun b hb => ?_⟩
    refine (hC LL O hO L1 hL1 _ (hF d hd.1 b hb.1).1).2 fun u => ?_
    have h3 := (cobO_cup_iff hL1 hm d (fun g => hd.2 g trivial) (u • b)).1
      (H _ (Submodule.mem_sup_left ⟨u • b, (finiteCocycles ((D.loc l).PD K) A'.ρ).smul_mem u hb, rfl⟩))
    convert h3 using 1
    funext p
    simp [cupL]
  refine ⟨fun s hs => ⟨fun h d hd => h1 d hd s h, fun H => ?_⟩,
    fun d hd => ⟨fun h s _ hs => h1 d h s hs, fun H => h2 d hd fun s hs => H s (hfD_le hTo hs) hs⟩⟩
  exact hD LL O hO L1 hL1 A A' LA LA' m hm _ le_sup_right (hfD_le hTo) s hs
    fun d hd H' => H d (h2 d hd H')

theorem bkA_of_all (hAll : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), All ((D.loc l).PD K)) :
    ∀ D : D7, LocalSituation.adm5 D → LocalSituation.adm6 D → LocalSituation.adm7 D → LocalSituation.adm8 D → ∀ (l : ℕ) [Fact l.Prime]
      (K : FinExt l), LocalSituation.bkADim ((D.loc l).PD K) → bkACore ((D.loc l).PD K) := by
  intro D _ _ _ h8 l _ K hdim
  obtain ⟨-, -, -, -, -, -, -, hEu, hL⟩ := hAll D l K
  exact bkA_core D h8 l K hL (fun LL _ _ _ O _ _ hO A A' P hP => (hEu LL O hO A A' P hP).2.le) hdim

theorem bkB_of_all (hAll : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), All ((D.loc l).PD K)) :
    ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), bkACore ((D.loc l).PD K) →
      bkBCore ((D.loc l).PD K) := by
  intro D l _ K hA
  obtain ⟨-, -, -, hD, hC, -⟩ := hAll D l K
  exact bkB_core D l K hD hC hA

theorem local_bounds_give (hT : Formalism.GaloisCohomology.LocalTateDualityK) (hE : Formalism.GaloisCohomology.LocalEulerCharK)
    (hA : ∀ D : D7, LocalSituation.adm5 D → LocalSituation.adm6 D → LocalSituation.adm7 D → LocalSituation.adm8 D → ∀ (l : ℕ) [Fact l.Prime]
      (K : FinExt l), LocalSituation.bkADim ((D.loc l).PD K) → bkACore ((D.loc l).PD K))
    (hB : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), bkACore ((D.loc l).PD K) →
      bkBCore ((D.loc l).PD K)) (D : D7) : LocalSituation.Conclusion5 D := by
  intro l _ K
  have h5 := GlobalTheory.T.localSituation_adm5_of_D7 D
  have h6 := GlobalTheory.T.localSituation_adm6_of_D7 D
  have h7 := GlobalTheory.T.localSituation_adm7_of_D7 D
  have h8 := GlobalTheory.T.localSituation_adm8_forall D
  have hd := GlobalTheory.T.blochKato_dimension_rightExact D h5 h6 h7 l K
  have ha := hA D h5 h6 h7 h8 l K hd.1
  have hb := hB D l K ha
  have hc := GlobalTheory.T.blochKato_cokernel_of_duality_euler hT hE D l K ha hb
  exact ⟨ha, hd.1, hd.2, hb, hc⟩

theorem local_bound_of_all_inputs : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    (∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), All ((D.loc l).PD K)) → ∀ D : D7, LocalSituation.Conclusion5 D :=
  fun hT hE hAll => local_bounds_give hT hE (bkA_of_all hAll) (bkB_of_all hAll)

end PositivityTheory.LocalTateOrthogonality.Bk
