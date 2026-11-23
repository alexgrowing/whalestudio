import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisOfFullLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenOfFgOfSpanEqTop
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfNormLeOne
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GoodOAdicCompleteCompactBasisStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LatTop

section General

variable {LL O V : Type} [Field LL] [CommRing O] [IsDomain O] [Algebra O LL] [IsFractionRing O LL]
  [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]

theorem exists_basis (M : Submodule O V) (hfg : M.FG) (hfree : Module.Free O M)
    (hspan : Submodule.span LL (M : Set V) = ⊤) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι LL V),
      ∀ x, x ∈ M ↔ ∀ i, ∃ a : O, b.repr x i = algebraMap O LL a := by
  haveI : Module.Finite O M := Module.Finite.iff_fg.2 hfg
  have hfull : ∀ v : V, ∃ c : O, c ≠ 0 ∧ ∃ m : M, algebraMap O LL c • v = (m : V) := by
    intro v
    have hv : v ∈ Submodule.span LL (M : Set V) := by rw [hspan]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_ne_zero, ⟨x, hx⟩, by simp⟩
    | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, m, hm⟩ := hx
      obtain ⟨d, hd, m', hm'⟩ := hy
      refine ⟨c * d, mul_ne_zero hc hd, d • m + c • m', ?_⟩
      have e1 : ((d • m + c • m' : M) : V) =
          algebraMap O LL d • (m : V) + algebraMap O LL c • (m' : V) := by
        simp [algebraMap_smul]
      rw [e1, ← hm, ← hm', map_mul, smul_add, smul_smul, smul_smul,
        mul_comm (algebraMap O LL d)]
    | smul a x _ hx =>
      obtain ⟨c, hc, m, hm⟩ := hx
      obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors O) a
      refine ⟨d * c, mul_ne_zero (nonZeroDivisors.ne_zero d.2) hc, n • m, ?_⟩
      have e1 : ((n • m : M) : V) = algebraMap O LL n • (m : V) := by simp [algebraMap_smul]
      simp only at hnd
      rw [e1, ← hm, ← hnd, map_mul, smul_smul, smul_smul]
      congr 1
      ring
  obtain ⟨b, hb, hr⟩ := GlobalTheory.Cyc.exists_basis_of_fullLattice (R := O) (F := LL) (M := M) (V := V)
    M.subtype.toAddMonoidHom Subtype.val_injective
    (fun c m => by simp [algebraMap_smul]) (by simpa using hfull) (Module.Free.chooseBasis O M)
  refine ⟨_, inferInstance, b, fun x => ⟨fun hx i => ⟨_, hr ⟨x, hx⟩ i⟩, fun h => ?_⟩⟩
  choose a ha using h
  rw [← b.sum_repr x]
  refine M.sum_mem fun i _ => ?_
  rw [ha i, algebraMap_smul]
  refine M.smul_mem _ ?_
  rw [hb i]
  exact (Module.Free.chooseBasis O M i).2

theorem mem_of_dual_dual {V' : Type} [AddCommGroup V'] [Module LL V'] [FiniteDimensional LL V]
    [FiniteDimensional LL V'] (M : Submodule O V) (hfg : M.FG) (hfree : Module.Free O M)
    (hspan : Submodule.span LL (M : Set V) = ⊤) (M' : Set V') (P : V →ₗ[LL] V' →ₗ[LL] LL)
    (hinj : ∀ y, (∀ x, P x y = 0) → y = 0) (hrank : finrank LL V = finrank LL V')
    (hM' : ∀ y, y ∈ M' ↔ ∀ x ∈ M, ∃ a : O, P x y = algebraMap O LL a)
    (x : V) (hx : ∀ y ∈ M', ∃ a : O, P x y = algebraMap O LL a) : x ∈ M := by
  obtain ⟨ι, _, b, hb⟩ := exists_basis M hfg hfree hspan
  have hi : Function.Injective P.flip := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    exact hinj y fun x => by simpa using LinearMap.congr_fun hy x
  have hs : Function.Surjective P.flip :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Subspace.dual_finrank_eq, hrank])).1 hi
  have hy : ∀ i, ∃ y : V', ∀ v, P v y = b.repr v i := fun i => by
    obtain ⟨y, hy⟩ := hs (b.coord i)
    exact ⟨y, fun v => by simpa using LinearMap.congr_fun hy v⟩
  choose y hy using hy
  rw [hb]
  intro i
  have hyi : y i ∈ M' := (hM' _).2 fun v hv => by
    obtain ⟨a, ha⟩ := (hb v).1 hv i
    exact ⟨a, by rw [hy, ha]⟩
  obtain ⟨a, ha⟩ := hx _ hyi
  exact ⟨a, by rw [← hy, ha]⟩

variable [TopologicalSpace LL] [IsTopologicalRing LL] [TopologicalSpace V] [IsModuleTopology LL V]

theorem isCompact_lattice (hC : IsCompact (Set.range (algebraMap O LL))) (M : Submodule O V)
    (hfg : M.FG) (hfree : Module.Free O M) (hspan : Submodule.span LL (M : Set V) = ⊤) :
    IsCompact (M : Set V) := by
  obtain ⟨ι, _, b, hb⟩ := exists_basis M hfg hfree hspan
  haveI := IsModuleTopology.toContinuousSMul LL V
  haveI := IsModuleTopology.toContinuousAdd LL V
  have hc : Continuous fun c : ι → LL => ∑ i, c i • b i :=
    continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const
  have he : (M : Set V) = (fun c : ι → LL => ∑ i, c i • b i) ''
      Set.pi Set.univ (fun _ => Set.range (algebraMap O LL)) := by
    ext x
    constructor
    · intro hx
      refine ⟨fun i => b.repr x i, fun i _ => ?_, b.sum_repr x⟩
      obtain ⟨a, ha⟩ := (hb x).1 hx i
      exact ⟨a, ha.symm⟩
    · rintro ⟨c, hc', rfl⟩
      rw [SetLike.mem_coe, hb]
      intro i
      obtain ⟨a, ha⟩ := hc' i (Set.mem_univ i)
      exact ⟨a, by rw [b.repr_sum_self, ha]⟩
  rw [he]
  exact (isCompact_univ_pi fun _ => hC).image hc

theorem hasBasis_lattice (M : Submodule O V) (hopen : IsOpen (M : Set V))
    (hcomp : IsCompact (M : Set V)) (ϖ : O) (hϖ : ϖ ≠ 0)
    (hB : (nhds (0 : LL)).HasBasis (fun _ : ℕ => True)
      (fun n => (fun o : O => algebraMap O LL (ϖ ^ n * o)) '' Set.univ)) :
    (nhds (0 : V)).HasBasis (fun _ : ℕ => True) (fun n => (fun x => ϖ ^ n • x) '' (M : Set V)) := by
  haveI := IsModuleTopology.toContinuousSMul LL V
  have hne : ∀ n : ℕ, algebraMap O LL (ϖ ^ n) ≠ 0 := fun n => by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O LL)]
    exact pow_ne_zero n hϖ
  refine Filter.hasBasis_iff.2 fun t => ⟨fun ht => ?_, ?_⟩
  · have hn : IsOpen ((fun p : LL × V => p.1 • p.2) ⁻¹' interior t) :=
      isOpen_interior.preimage continuous_smul
    obtain ⟨u, v, hu, -, h0, hv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := (0 : LL)))
      hcomp hn (by
        rintro ⟨a, x⟩ ⟨ha, -⟩
        have ha' : a = 0 := ha
        simpa [ha'] using mem_interior_iff_mem_nhds.2 ht)
    obtain ⟨n, -, hn⟩ := hB.mem_iff.1 (hu.mem_nhds (h0 rfl))
    refine ⟨n, trivial, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have h1 : algebraMap O LL (ϖ ^ n) ∈ u := hn ⟨1, trivial, by simp⟩
    have h2 := huv (Set.mk_mem_prod h1 (hv hx))
    have h3 : algebraMap O LL (ϖ ^ n) • x ∈ t := interior_subset h2
    rwa [algebraMap_smul] at h3
  · rintro ⟨n, -, hn⟩
    have hU : IsOpen ((fun y : V => (algebraMap O LL (ϖ ^ n))⁻¹ • y) ⁻¹' (M : Set V)) :=
      hopen.preimage (continuous_const_smul _)
    refine Filter.mem_of_superset (hU.mem_nhds (by simp)) fun y hy => hn ⟨_, hy, ?_⟩
    show ϖ ^ n • (algebraMap O LL (ϖ ^ n))⁻¹ • y = y
    rw [← algebraMap_smul LL (ϖ ^ n), smul_smul, mul_inv_cancel₀ (hne n), one_smul]

theorem exists_pow_smul_mem {G : Type} [TopologicalSpace G] [CompactSpace G] (M : Submodule O V)
    (hopen : IsOpen (M : Set V)) (ϖ : O)
    (hB : (nhds (0 : LL)).HasBasis (fun _ : ℕ => True)
      (fun n => (fun o : O => algebraMap O LL (ϖ ^ n * o)) '' Set.univ))
    (c : G → V) (hc : Continuous c) : ∃ n : ℕ, ∀ g, ϖ ^ n • c g ∈ M := by
  haveI := IsModuleTopology.toContinuousSMul LL V
  have hcov : Set.range c ⊆ ⋃ n : ℕ, {x : V | ϖ ^ n • x ∈ M} := by
    rintro _ ⟨g, rfl⟩
    have hU : IsOpen ((fun a : LL => a • c g) ⁻¹' (M : Set V)) :=
      hopen.preimage (continuous_id.smul continuous_const)
    obtain ⟨n, -, hn⟩ := hB.mem_iff.1 (hU.mem_nhds (by simp))
    have h1 : algebraMap O LL (ϖ ^ n) • c g ∈ M := hn ⟨1, trivial, by simp⟩
    rw [algebraMap_smul] at h1
    exact Set.mem_iUnion.2 ⟨n, h1⟩
  have hop : ∀ n : ℕ, IsOpen {x : V | ϖ ^ n • x ∈ M} := fun n => by
    have : {x : V | ϖ ^ n • x ∈ M} = (fun x : V => algebraMap O LL (ϖ ^ n) • x) ⁻¹' (M : Set V) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, algebraMap_smul]
    rw [this]
    exact hopen.preimage (continuous_const_smul _)
  have hdir : Directed (· ⊆ ·) fun n : ℕ => {x : V | ϖ ^ n • x ∈ M} :=
    Monotone.directed_le (f := fun n : ℕ => {x : V | ϖ ^ n • x ∈ M}) fun m n hmn x hx => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      have : ϖ ^ (m + k) • x = ϖ ^ k • ϖ ^ m • x := by rw [smul_smul, pow_add, mul_comm]
      show ϖ ^ (m + k) • x ∈ M
      rw [this]
      exact M.smul_mem _ hx
  obtain ⟨n, hn⟩ := (isCompact_range hc).elim_directed_cover _ hop hcov hdir
  exact ⟨n, fun g => hn ⟨g, rfl⟩⟩

end General

theorem lattice_top : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → IsOpen (LA.T : Set A.V) ∧ (nhds (0 : A.V)).HasBasis (fun _ : ℕ => True) (fun n => (fun x => ϖ ^ n • x) '' (LA.T : Set A.V)) ∧ IsCompact (LA.T : Set A.V) ∧ (∀ c : ↥(GK K) → A.V, Continuous c → ∃ n : ℕ, ∀ g, ϖ ^ n • c g ∈ LA.T) ∧ ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 ((D.loc l).PD K) LA LA' P → IsDualLat1 ((D.loc l).PD K) LA' LA P.flip := by
  intro D l _ K LL _ _ _ O _ _ hO A LA ϖ hϖ
  have I := GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hO ϖ hϖ
  obtain ⟨⟨hd, hdvr, hfr⟩, hfd, hmt, htr, hop⟩ := hO
  obtain ⟨-, -, hC, -, hB, -⟩ := I
  haveI := hd
  haveI := hfr
  haveI := htr
  haveI : CompactSpace ↥(GK K) := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK K
  have hopen : IsOpen (LA.T : Set A.V) :=
    GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hop LA.T LA.fg LA.span
  have hcomp : IsCompact (LA.T : Set A.V) := isCompact_lattice hC LA.T LA.fg LA.free LA.span
  refine ⟨hopen, hasBasis_lattice LA.T hopen hcomp ϖ hϖ.ne_zero hB, hcomp,
    fun c hc => exists_pow_smul_mem LA.T hopen ϖ hB c hc, ?_⟩
  rintro A' LA' P ⟨⟨h1, h2, h3, h4⟩, h5⟩
  refine ⟨⟨fun g y x => h1 g x y, h3, h2, h4.symm⟩, fun x => ⟨fun hx y hy => (h5 y).1 hy x hx, fun hx => ?_⟩⟩
  exact mem_of_dual_dual LA.T LA.fg LA.free LA.span (LA'.T : Set A'.V) P h3 h4 h5 x hx

end GlobalTheory.CompanionTheory.LatTop
