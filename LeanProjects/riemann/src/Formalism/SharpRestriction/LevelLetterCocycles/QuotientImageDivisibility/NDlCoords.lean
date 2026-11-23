import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.MemZeroSubCoe
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.FrobeniusUniformizerPowDvd

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

section GenM

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {LL : Type} [Field LL]
  [Algebra O LL] [IsFractionRing O LL] {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M]
  {U : Type} [AddCommGroup U] [Module LL U]

theorem genM (φ : M →+ U) (hφ : ∀ (c : O) (x : M), φ (c • x) = algebraMap O LL c • φ x) {m : ℕ}
    (hm : Module.finrank LL ↥(Submodule.span LL (Set.range φ)) ≤ m) :
    ∃ s : Finset M, s.card ≤ m ∧ ∀ x : M, ∃ y ∈ Submodule.span O (↑s : Set M), φ (x - y) = 0 := by
  let A : Submodule O M := ⊤
  let φ' : ↥A →+ U := φ.comp A.subtype.toAddMonoidHom
  have hφ' : ∀ (c : O) (x : ↥A), φ' (c • x) = algebraMap O LL c • φ' x := fun c x => hφ c x
  have hr : Set.range φ' = Set.range φ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩; exact ⟨⟨x, trivial⟩, rfl⟩
  have hm' : Module.finrank LL ↥(Submodule.span LL (Set.range φ')) ≤ m := by rwa [hr]
  obtain ⟨-, Q, i1, i2, ob, hker, hgen, -⟩ :=
    pstep_rank (lenO := 0) (m := m) (c := 0) A φ' hφ' hm'
  obtain ⟨sQ, hsQ, hspan⟩ := hgen trivial
  obtain ⟨t, ht, htN, hNt⟩ := Formalism.MainNotions.RamifiedCoefficientChains.exists_gen_of_le_span sQ (LinearMap.range ob)
    (by rw [hspan]; exact le_top)
  have hpre : ∀ q : ↥t, ∃ x : ↥A, ob x = q := fun q => htN q.2
  choose f hf using hpre
  refine ⟨Finset.univ.image (fun q : ↥t => ((f q : ↥A) : M)), ?_, fun x => ?_⟩
  · refine Finset.card_image_le.trans ?_
    simp only [Finset.card_univ, Fintype.card_coe]
    exact ht.trans hsQ
  · have hx : ob ⟨x, trivial⟩ ∈ Submodule.span O (↑t : Set Q) := hNt ⟨_, rfl⟩
    rw [Submodule.mem_span_finset] at hx
    obtain ⟨a, -, hax⟩ := hx
    set y : M := ∑ q : ↥t, a q • ((f q : ↥A) : M) with hy
    refine ⟨y, Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ q)))), ?_⟩
    have hoby : ob ⟨y, trivial⟩ = ob ⟨x, trivial⟩ := by
      have e : (⟨y, trivial⟩ : ↥A) = ∑ q : ↥t, a q • f q := Subtype.ext (by simp [hy])
      rw [e, map_sum, ← hax]
      rw [← Finset.sum_coe_sort t]
      exact Finset.sum_congr rfl fun q _ => by rw [map_smul, hf q]
    have h0 : ob (⟨x, trivial⟩ - ⟨y, trivial⟩) = 0 := by rw [map_sub, hoby, sub_self]
    have hz := (hker _).1 h0
    have := (mem_zeroSub_coe A φ' hφ' (⟨x, trivial⟩ - ⟨y, trivial⟩)).1 hz
    simpa [φ'] using this

end GenM

section Frame

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem NDl_coords (i : ZMod n) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) :
    ∃ (d : ℕ) (b : Fin d → W.DD T), (∀ k, b k ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ∧
      ∀ y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i, ∃ α : Fin d → O,
        Formalism.MainNotions.ArcLiftingSetup.cmpD W T y = ∑ k, algebraMap O LL (α k) • Formalism.MainNotions.ArcLiftingSetup.cmpD W T (b k) := by
  obtain ⟨d, b, hb⟩ := Formalism.MainNotions.UnusedSlot80.Relay2.frame_exists W T i hmod
  have hbN : ∀ k, b k ∈ W.N T := fun k => (hb.1 k).1.1
  have hbl : ∀ k, (letE i : LetA O n) • b k = b k := fun k =>
    Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T i (hb.1 k).2
  refine ⟨d, b, fun k => ⟨hbN k, hbl k, (hb.1 k).1.2⟩, fun y hy => ?_⟩
  have hy' : y ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T i y := hy
  have hyi : Formalism.MainNotions.LiftingTheory.InNΔi W T i y :=
    Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_of W T i ⟨hy'.1, hy'.2.2⟩ hy'.2.1
  obtain ⟨a, ⟨-, hya⟩, -⟩ := hb.2 y hyi
  refine ⟨fun k => PowerSeries.constantCoeff ((a k) i), ?_⟩
  rw [hya, cmpD_sum W T _ _ (fun k _ => (W.N T).smul_mem _ (hbN k))]
  exact Finset.sum_congr rfl fun k _ => cmpD_smul_letter W T i (a k) (hbN k) (hbl k)

end Frame

end Formalism.MainNotions.N.Pv.LocalLengthBound
