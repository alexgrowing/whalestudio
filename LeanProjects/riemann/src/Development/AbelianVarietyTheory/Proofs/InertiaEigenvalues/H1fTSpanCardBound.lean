import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryMemBlochKatoCocycles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1fDeRham
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.H1fGeneratorsAlt

section Eval

variable {G V LL : Type} [Field LL] [AddCommGroup V] [Module LL V]

theorem exists_finset_eval (W : Submodule LL (G → V)) [Module.Finite LL ↥W] :
    ∃ s : Finset G, ∀ c ∈ W, (∀ g ∈ s, c g = 0) → c = 0 := by
  classical
  let Ks : Finset G → Submodule LL (G → V) := fun s =>
    W ⊓ ⨅ g ∈ s, LinearMap.ker (LinearMap.proj (R := LL) (φ := fun _ : G => V) g)
  have hmem : ∀ s c, c ∈ Ks s ↔ c ∈ W ∧ ∀ g ∈ s, c g = 0 := by
    intro s c
    simp [Ks, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  obtain ⟨s, -, hs⟩ := (measure fun s => finrank LL ↥(Ks s)).wf.has_min Set.univ ⟨∅, trivial⟩
  refine ⟨s, fun c hc h0 => ?_⟩
  by_contra hne
  obtain ⟨g, hg⟩ : ∃ g, c g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hlt : Ks (insert g s) < Ks s := by
    refine lt_of_le_of_ne (fun x hx => ?_) fun heq => ?_
    · rw [hmem] at hx ⊢
      exact ⟨hx.1, fun g' hg' => hx.2 g' (Finset.mem_insert_of_mem hg')⟩
    · have h1 : c ∈ Ks s := (hmem s c).2 ⟨hc, h0⟩
      rw [← heq, hmem] at h1
      exact hg (h1.2 g (Finset.mem_insert_self g s))
  haveI : Module.Finite LL ↥(Ks s) := Submodule.finiteDimensional_of_le inf_le_left
  exact hs (insert g s) trivial (Submodule.finrank_lt_finrank_of_lt hlt)

theorem fg_of_le_of_values {O : Type} [CommRing O] [IsNoetherianRing O] [Algebra O LL] [Module O V]
    [IsScalarTower O LL V] (W : Submodule LL (G → V)) [Module.Finite LL ↥W]
    (T : Submodule O V) (hT : T.FG) (N : Submodule O (G → V)) (hNW : N ≤ W.restrictScalars O)
    (hNT : ∀ c ∈ N, ∀ g, c g ∈ T) : N.FG := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_eval W
  haveI : IsNoetherian O ↥T := isNoetherian_of_fg_of_noetherian T hT
  let φ : ↥N →ₗ[O] (↥s → ↥T) :=
    { toFun := fun c i => ⟨(c : G → V) i, hNT _ c.2 _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := by
    intro c c' h
    apply Subtype.ext
    rw [← sub_eq_zero]
    refine hs _ (W.sub_mem (hNW c.2) (hNW c'.2)) fun g hg => ?_
    have := congrArg (fun f => ((f ⟨g, hg⟩ : ↥T) : V)) h
    simpa [φ, sub_eq_zero] using this
  haveI : IsNoetherian O ↥N := isNoetherian_of_injective φ hφ
  exact Module.Finite.iff_fg.1 inferInstance

end Eval

section Cohomology

open GlobalTheory.H1fGeneratorBoundAlt GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {ρ : Representation LL G V}
    [TopologicalSpace G] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul LL V]
    {O : Type} [CommRing O] [Algebra O LL] [IsDomain O] [IsDiscreteValuationRing O]
    [IsFractionRing O LL] [Module O V] [IsScalarTower O LL V]

theorem finite_Z1f_of_H1fV [FiniteDimensional LL V] (hρ : ∀ x, Continuous fun g => ρ g x)
    [Module.Finite LL (FiniteCohomology PD ρ)] : Module.Finite LL ↥(finiteCocycles PD ρ) := by
  have hle : B1 ρ ≤ finiteCocycles PD ρ := by
    rintro _ ⟨x, rfl⟩
    exact coboundary_mem_blochKatoCocycles PD hρ x
  haveI : Module.Finite LL ↥(B1 ρ) := LinearMap.finiteDimensional_range _
  haveI : Module.Finite LL ↥((B1 ρ).comap (finiteCocycles PD ρ).subtype) :=
    Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe hle).symm
  haveI : IsNoetherian LL ↥(finiteCocycles PD ρ) :=
    isNoetherian_of_range_eq_ker ((B1 ρ).comap (finiteCocycles PD ρ).subtype).subtype
      (Submodule.mkQ _) (by rw [Submodule.range_subtype, Submodule.ker_mkQ])
  infer_instance

theorem finite_Z1fT_of (L : Lattice (O := O) ρ) [Module.Finite LL ↥(finiteCocycles PD ρ)] :
    Module.Finite O ↥(latticeFiniteCocycles PD L) :=
  Module.Finite.iff_fg.2 (fg_of_le_of_values (finiteCocycles PD ρ) L.T L.fg (latticeFiniteCocycles PD L) inf_le_right
    fun _ hc g => hc.1.2 g (Set.mem_univ g))

theorem exists_generators_H1fT' [FiniteDimensional LL V] (L : Lattice (O := O) ρ)
    (hρ : ∀ x, Continuous fun g => ρ g x) [Module.Finite LL (FiniteCohomology PD ρ)]
    {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ m : ℕ, GeneratedByAtMost (latticeFiniteCohomology PD L) m ∧
      m + finrank LL ↥(H0V ρ) ≤ finrank LL (FiniteCohomology PD ρ) + h0ModResidueDim L ϖ := by
  classical
  haveI hI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  haveI := L.free
  haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.2 L.fg
  haveI := finite_Z1f_of_H1fV PD hρ
  haveI := finite_Z1fT_of PD L
  haveI : Module.IsTorsionFree O LL := inferInstance
  haveI : Module.IsTorsionFree O V := Module.IsTorsionFree.trans LL
  haveI : Module.Free O ↥(latticeFiniteCocycles PD L) := inferInstance
  obtain ⟨m, z, hz, hm⟩ := exists_generators (Ideal.span {ϖ}) (cobT PD L hρ)
  refine ⟨m, ⟨Finset.univ.image fun i => classT PD L (z i), ?_, ?_⟩, ?_⟩
  · have := congrArg (Submodule.map (classT PD L)) hz
    rw [Submodule.map_sup, ← ker_classT, Submodule.map_top, range_classT,
      (Submodule.map_le_iff_le_comap.2 le_rfl : (LinearMap.ker (classT PD L)).map (classT PD L) ≤ ⊥).antisymm bot_le,
      sup_bot_eq, Submodule.map_span, ← Set.range_comp] at this
    rw [← this, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rfl
  · simpa using Finset.card_image_le (s := Finset.univ) (f := fun i => classT PD L (z i))
  · haveI := finite_latMod L (Ideal.span {ϖ})
    have h1 := Submodule.finrank_mono (ker_redMap_le PD L hρ (Ideal.span {ϖ}))
    have h2 := finrank_bloch_kato_cocycles PD hρ
    have h3 := finrank_lattice L
    have h4 : finrank O ↥(latticeFiniteCocycles PD L) ≤ finrank LL ↥(finiteCocycles PD ρ) :=
      finrank_le_of_injective (W := ↥(finiteCocycles PD ρ))
        { toFun := fun c => ⟨c, c.2.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl } fun _ _ h =>
          Subtype.ext (congrArg (fun c : ↥(finiteCocycles PD ρ) => (c : G → V)) h)
    have h5 : finrank (O ⧸ Ideal.span {ϖ}) ↥(LinearMap.ker (redMap (Ideal.span {ϖ}) (cobT PD L hρ))) ≤
      h0ModResidueDim L ϖ := h1
    omega

end Cohomology

open GlobalTheory.H1fGeneratorBoundAlt GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions

theorem h1fT_generators : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ T : LocLat ↥(GK K) ℚ_[l] LL O, IsDR (P.PD K) T.ρ → ∃ s : Finset (LatticeCohomology T.L), Submodule.span O (s : Set (LatticeCohomology T.L)) = latticeFiniteCohomology (P.PD K) T.L ∧ s.card + finrank LL ↥(H0V T.ρ) ≤ finrank LL (FiniteCohomology (P.PD K) T.ρ) + finrank LL T.V := by
  intro l _ P AI hTied K LL _ _ _ O _ _ hO T hDR
  have hH1f := (GlobalTheory.SeqDim.h1f_finrank l P AI hTied K LL O hO (toGRep T) hDR).1
  obtain ⟨⟨hD, hDVR, hF⟩, -⟩ := hO
  haveI : IsTopologicalAddGroup T.V := IsModuleTopology.topologicalAddGroup LL T.V
  haveI : Module.Finite LL (FiniteCohomology (P.PD K) T.ρ) := hH1f
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, ⟨s, hs, hc⟩, hm⟩ := exists_generators_H1fT' (P.PD K) T.L T.cont hϖ
  have h5 := h0_mod_uniformizer_le_rank T.L hϖ
  have h3 := finrank_lattice T.L
  exact ⟨s, hs, by omega⟩

end GlobalTheory.H1fGeneratorsAlt
