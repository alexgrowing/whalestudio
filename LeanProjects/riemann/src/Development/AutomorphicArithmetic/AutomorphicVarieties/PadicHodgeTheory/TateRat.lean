import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteLevelCyclotomicOfOpenEmbedding
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.NonemptyCohomologyRestrictScalarsLinearEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteLevelOfFiniteLevelMod
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LatticeCochainsFinGenOfFinLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LatticeCohomologyFiniteAndGrowthOfFinGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsInvariantLatticeOpenEmbedding
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RankCohomologyRationalEqRankLattice
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CardQuotientPowSubmoduleGrowsFinrank
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CardCoinvariantsModPowEqModPowCoinvariants
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FinrankCoinvariantsEqFinrankLatticeCoinvariants
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem grows_le {l : ℕ} (hl : 1 < l) {a : ℕ → ℕ} {s t : ℕ} (h : Grows l a s) (h' : Grows l a t) :
    s ≤ t := by
  obtain ⟨_, h⟩ := h
  obtain ⟨C, h'⟩ := h'
  have := (Nat.pow_le_pow_iff_right hl).1 ((h (C + 1) C.succ_pos).1.trans (h' (C + 1) C.succ_pos).2)
  by_contra hc
  have : (C + 1) * (t + 1) ≤ (C + 1) * s := Nat.mul_le_mul_left _ (by omega)
  nlinarith

private theorem grows_unique {l : ℕ} (hl : 1 < l) {a b : ℕ → ℕ} {s t : ℕ} (h : Grows l a s) (h' : Grows l b t)
    (e : ∀ m, a m = b m) : s = t := by
  obtain rfl : a = b := funext e
  exact le_antisymm (grows_le hl h h') (grows_le hl h' h)

private theorem grows_mul {l : ℕ} {a b : ℕ → ℕ} {s t : ℕ} (h : Grows l a s) (h' : Grows l b t) :
    Grows l (fun m => a m * b m) (s + t) := by
  obtain ⟨C, h⟩ := h
  obtain ⟨D, h'⟩ := h'
  refine ⟨C + D, fun m hm => ⟨?_, ?_⟩⟩
  · rw [mul_add, pow_add]
    exact Nat.mul_le_mul (h m hm).1 (h' m hm).1
  · rw [show m * (s + t) + (C + D) = (m * s + C) + (m * t + D) by ring, pow_add]
    exact Nat.mul_le_mul (h m hm).2 (h' m hm).2

private theorem grows_pow (l n d : ℕ) : Grows l (fun m => (l ^ (m * n)) ^ d) (d * n) :=
  ⟨0, fun m _ => by
    have : (l ^ (m * n)) ^ d = l ^ (m * (d * n)) := by rw [← pow_mul]; congr 1; ring
    simp [this]⟩

private theorem tate_lattice {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {χ : G →* ℤ_[l]ˣ} {d : ℕ} (hF : FinLevel l G χ d) {n : ℕ}
    (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) :
    Module.Finite ℤ_[l] (H1 ρ) ∧ Module.Finite ℤ_[l] (H2 ρ) ∧
      finrank ℤ_[l] (H1 ρ) = finrank ℤ_[l] ↥(H0 ρ) + finrank ℤ_[l] (H2 ρ) + d * n ∧
      finrank ℤ_[l] (H2 ρ) = finrank ℤ_[l] ((Fin n → ℤ_[l]) ⧸ coSub χ ρ) := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hm := fun m => hF _ (redRep ρ m) (contAction_redRep h m)
  obtain ⟨f1, f2, g0, g1, g2⟩ := UpperTheory.lattice_cohomology_finite_and_growth_of_finGen ρ h (UpperTheory.latticeCochains_finGen_of_finLevel hF ρ h) fun m => ⟨(hm m).1, (hm m).2.1⟩
  refine ⟨f1, f2, grows_unique hl g1 (grows_mul (grows_mul g0 g2) (grows_pow l n d)) fun m => ?_,
    grows_unique hl g2 (UpperTheory.card_quotient_powSubmodule_grows_finrank l _) fun m => ?_⟩
  · rw [(hm m).2.2.2.1, card_quot_lSub]
  · rw [(hm m).2.2.2.2, UpperTheory.card_coinvariants_mod_pow_eq_mod_pow_coinvariants]

private theorem tate_Q {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] {χ : G →* ℤ_[l]ˣ} {d : ℕ} (hF : FinLevel l G χ d)
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul ℚ_[l] V]
    (ρ : Representation ℚ_[l] G V) (h : ContAction ρ) :
    Module.Finite ℚ_[l] (H1 ρ) ∧ Module.Finite ℚ_[l] (H2 ρ) ∧
      finrank ℚ_[l] (H1 ρ) = finrank ℚ_[l] ↥(H0 ρ) + finrank ℚ_[l] (H2 ρ) + d * finrank ℚ_[l] V ∧
      finrank ℚ_[l] (H2 ρ) =
        finrank ℚ_[l] (V ⧸ coSub ((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) ρ) := by
  letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨ρT, j, hT, hj, he, hs⟩ := UpperTheory.exists_invariant_lattice_openEmbedding ρ h
  obtain ⟨r0, r1, r2⟩ := UpperTheory.rank_cohomology_rational_eq_rank_lattice ρ h ρT j hT hj he hs
  obtain ⟨f1, f2, e1, e2⟩ := tate_lattice hF ρT hT
  have q0 : finrank ℚ_[l] ↥(H0 ρ) = finrank ℤ_[l] ↥(H0 ρT) := congrArg Cardinal.toNat r0
  have q1 : finrank ℚ_[l] (H1 ρ) = finrank ℤ_[l] (H1 ρT) := congrArg Cardinal.toNat r1
  have q2 : finrank ℚ_[l] (H2 ρ) = finrank ℤ_[l] (H2 ρT) := congrArg Cardinal.toNat r2
  refine ⟨Module.rank_lt_aleph0_iff.1 (r1 ▸ Module.rank_lt_aleph0 _ _),
    Module.rank_lt_aleph0_iff.1 (r2 ▸ Module.rank_lt_aleph0 _ _), ?_, ?_⟩
  · rw [q0, q1, q2, e1]
  · rw [q2, e2, UpperTheory.finrank_coinvariants_eq_finrank_lattice_coinvariants χ ρ ρT j hj.injective he hs]

private theorem finrank_H0dual {G E V : Type} [Group G] [Field E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (χ : G →* Eˣ) (ρ : Representation E G V) :
    finrank E ↥(H0dual χ ρ) = finrank E (V ⧸ coSub χ ρ) := by
  have : H0dual χ ρ = (coSub χ ρ).dualAnnihilator := by
    ext f
    rw [Submodule.mem_dualAnnihilator]
    constructor
    · intro hf w hw
      refine (Submodule.span_le (p := LinearMap.ker f)).2 ?_ hw
      rintro _ ⟨g, x, rfl⟩
      simp [hf g x]
    · intro hf g x
      have := hf _ (Submodule.subset_span ⟨g, x, rfl⟩)
      simpa [sub_eq_zero] using this
  rw [this, ← (Submodule.dualQuotEquivDualAnnihilator _).finrank_eq, Subspace.dual_finrank_eq]

private theorem coSub_res {Q E G V : Type} [Field Q] [Field E] [Algebra Q E] [Group G] [AddCommGroup V]
    [Module E V] [Module Q V] [IsScalarTower Q E V] (χ : G →* Qˣ) (χ' : G →* Eˣ)
    (hχ : ∀ g, ((χ' g : Eˣ) : E) = algebraMap Q E (χ g : Qˣ)) (ρ : Representation E G V) :
    coSub χ (resCoef Q ρ) = (coSub χ' ρ).restrictScalars Q := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨g, x, rfl⟩
    exact Submodule.subset_span ⟨g, x, by rw [hχ, algebraMap_smul]; rfl⟩
  · intro y hy
    have key : ∀ c : E, c • y ∈ coSub χ (resCoef Q ρ) := by
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨g, x, rfl⟩ := hy
        intro c
        refine Submodule.subset_span ⟨g, c • x, ?_⟩
        change _ = ρ g (c • x) - _
        rw [hχ, algebraMap_smul, smul_sub, map_smul, smul_comm c (χ g : Q)]
      | zero => intro c; simp
      | add a b _ _ ha hb => intro c; rw [smul_add]; exact add_mem (ha c) (hb c)
      | smul a b _ hb => intro c; rw [smul_smul]; exact hb _
    simpa using key 1

theorem UpperTheory.V.Loc.tateRat :
    LocalPublishedTheorems → ∀ {v l : ℕ} [Fact v.Prime] [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ v) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρ : Representation E G V), ContAction ρ → Module.Finite E (H1 ρ) ∧ Module.Finite E (H2 ρ) ∧ finrank E (H1 ρ) = finrank E ↥(H0 ρ) + finrank E (H2 ρ) + (if v = l then φ.range.index * finrank E V else 0) ∧ finrank E (H2 ρ) = finrank E ↥(H0dual ((cycA v l E).comp φ) ρ) := by
  intro hP v l _ _ G _ _ _ φ hφ E _ _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ h
  haveI : CompactSpace G := by
    have hc : IsClosed (φ.range : Set (GQ v)) := φ.range.isClosed_of_isOpen hφ.isOpen_range
    exact (⟨hφ.isEmbedding, hc⟩ : IsClosedEmbedding φ).compactSpace
  haveI : ContinuousConstSMul ℚ_[l] V := ⟨fun c => by
    simpa only [algebraMap_smul] using continuous_const_smul (T := V) (algebraMap ℚ_[l] E c)⟩
  haveI : FiniteDimensional E V := Module.Finite.of_restrictScalars_finite ℚ_[l] E V
  obtain ⟨f1, f2, e1, e2⟩ := tate_Q (UpperTheory.finite_level_of_finite_level_mod l G _ _ (UpperTheory.finiteLevel_cyclotomic_of_openEmbedding hP φ hφ)) (resCoef ℚ_[l] ρ) h
  obtain ⟨⟨a0⟩, ⟨a1⟩, ⟨a2⟩, -⟩ := UpperTheory.nonempty_cohomology_restrictScalars_linearEquiv ℚ_[l] ρ
  haveI := Module.Finite.equiv a1
  haveI := Module.Finite.equiv a2
  have hd : 0 < finrank ℚ_[l] E := finrank_pos
  rw [coSub_res ((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp ((cyc v l).comp φ))
      ((cycA v l E).comp φ)
      (fun g => IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E ((cyc v l (φ g) : ℤ_[l]ˣ) : ℤ_[l])) ρ,
    (Submodule.Quotient.restrictScalarsEquiv ℚ_[l] _).finrank_eq, a2.finrank_eq,
    ← finrank_mul_finrank ℚ_[l] E (H2 ρ), ← finrank_mul_finrank ℚ_[l] E (V ⧸ _)] at e2
  rw [a0.finrank_eq, a1.finrank_eq, a2.finrank_eq, ← finrank_mul_finrank ℚ_[l] E (H2 ρ),
    ← finrank_mul_finrank ℚ_[l] E (H1 ρ), ← finrank_mul_finrank ℚ_[l] E ↥(H0 ρ),
    ← finrank_mul_finrank ℚ_[l] E V] at e1
  refine ⟨Module.Finite.of_restrictScalars_finite ℚ_[l] E _, Module.Finite.of_restrictScalars_finite ℚ_[l] E _,
    Nat.eq_of_mul_eq_mul_left hd ?_, ?_⟩
  · rw [e1]
    split_ifs <;> ring
  · rw [finrank_H0dual]
    exact Nat.eq_of_mul_eq_mul_left hd e2
