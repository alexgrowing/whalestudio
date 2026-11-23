import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.LineLattice

theorem exists_generator {LL : Type} [Field LL] {O : Type} [CommRing O] [IsDomain O]
    [Algebra O LL] [IsFractionRing O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] (T : Submodule O V) [Module.Free O T]
    (hsp : Submodule.span LL (T : Set V) = ⊤) (h1 : Module.finrank LL V = 1) :
    ∃ v : V, v ≠ 0 ∧ T = Submodule.span O {v} := by
  classical
  have hfin : Module.Finite LL V := Module.finite_of_finrank_eq_succ h1
  let b := Module.Free.chooseBasis O T
  have hli : LinearIndependent O (fun i => (b i : V)) :=
    b.linearIndependent.map' T.subtype T.ker_subtype
  have hli' : LinearIndependent LL (fun i => (b i : V)) :=
    (LinearIndependent.iff_fractionRing O LL).1 hli
  have hT : T = Submodule.span O (Set.range fun i => (b i : V)) := by
    have h := congrArg (Submodule.map T.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
    exact h.symm
  have hfi : Finite (Module.Free.ChooseBasisIndex O T) := hli'.finite
  letI := Fintype.ofFinite (Module.Free.ChooseBasisIndex O T)
  have hc := hli'.fintype_card_le_finrank
  rw [h1] at hc
  have hsub : Subsingleton (Module.Free.ChooseBasisIndex O T) :=
    Fintype.card_le_one_iff_subsingleton.1 hc
  rcases isEmpty_or_nonempty (Module.Free.ChooseBasisIndex O T) with he | ⟨⟨i⟩⟩
  · exfalso
    rw [Set.range_eq_empty, Submodule.span_empty] at hT
    have hb : Submodule.span LL (T : Set V) = ⊥ := by
      rw [hT]; simp
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ h1
    exact bot_ne_top (hb.symm.trans hsp)
  · refine ⟨b i, hli.ne_zero i, ?_⟩
    refine hT.trans ?_
    congr 1
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      rw [Subsingleton.elim j i]; rfl
    · rintro rfl
      exact ⟨i, rfl⟩

theorem lattice_rank_one {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O]
    [IsDomain O] [Algebra O LL] [IsFractionRing O LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V} (L : Lattice (O := O) ρ)
    (h1 : Module.finrank LL V = 1) :
    (∃ e : LL ≃ₗ[LL] V, ∀ x : LL, e x ∈ L.T ↔ x ∈ Set.range (algebraMap O LL)) ∧
    ∀ a : O, a ≠ 0 →
      Nonempty (↥(Submodule.torsionBy O (V ⧸ L.T) a) ≃ₗ[O] (O ⧸ Ideal.span {a})) := by
  haveI := L.free
  obtain ⟨v, hv, hT⟩ := exists_generator L.T L.span h1
  have hsurj : ∀ w : V, ∃ c : LL, c • v = w := (finrank_eq_one_iff_of_nonzero' v hv).1 h1
  have hmem : ∀ x : LL, x • v ∈ L.T ↔ x ∈ Set.range (algebraMap O LL) := by
    intro x
    rw [hT, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [← algebraMap_smul LL c v] at hc
      exact smul_left_injective LL hv hc
    · rintro ⟨c, rfl⟩
      exact ⟨c, (algebraMap_smul LL c v).symm⟩
  refine ⟨⟨LinearEquiv.ofBijective (LinearMap.toSpanSingleton LL V v)
    ⟨smul_left_injective LL hv, hsurj⟩, hmem⟩, ?_⟩
  intro a ha
  have ha' : algebraMap O LL a ≠ 0 := by
    simpa using ha
  have hx : L.T.mkQ ((algebraMap O LL a)⁻¹ • v) ∈ Submodule.torsionBy O (V ⧸ L.T) a := by
    rw [Submodule.mem_torsionBy_iff, ← map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, ← algebraMap_smul LL a, smul_smul, hmem,
      mul_inv_cancel₀ ha']
    exact ⟨1, map_one _⟩
  let f : O →ₗ[O] Submodule.torsionBy O (V ⧸ L.T) a :=
    LinearMap.toSpanSingleton O _ ⟨_, hx⟩
  have hf : ∀ c : O, (f c : V ⧸ L.T) =
      L.T.mkQ ((algebraMap O LL c * (algebraMap O LL a)⁻¹) • v) := by
    intro c
    rw [← smul_smul, algebraMap_smul, map_smul]
    rfl
  have hfs : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨w, rfl⟩ := L.T.mkQ_surjective y
    obtain ⟨x, rfl⟩ := hsurj w
    rw [Submodule.mem_torsionBy_iff, ← map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, ← algebraMap_smul LL a, smul_smul, hmem] at hy
    obtain ⟨c, hc⟩ := hy
    refine ⟨c, Subtype.ext ?_⟩
    rw [hf, hc, mul_comm (algebraMap O LL a) x, mul_assoc, mul_inv_cancel₀ ha', mul_one]
  have hk : LinearMap.ker f = Ideal.span {a} := by
    ext c
    rw [LinearMap.mem_ker, Subtype.ext_iff, hf, Ideal.mem_span_singleton']
    rw [Submodule.coe_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmem]
    constructor
    · rintro ⟨d, hd⟩
      refine ⟨d, IsFractionRing.injective O LL ?_⟩
      rw [map_mul, hd, mul_assoc, inv_mul_cancel₀ ha', mul_one]
    · rintro ⟨d, rfl⟩
      refine ⟨d, ?_⟩
      rw [map_mul, mul_assoc, mul_inv_cancel₀ ha', mul_one]
  exact ⟨(f.quotKerEquivOfSurjective hfs).symm.trans (Submodule.quotEquivOfEq _ _ hk)⟩

end GlobalTheory.LineLattice
