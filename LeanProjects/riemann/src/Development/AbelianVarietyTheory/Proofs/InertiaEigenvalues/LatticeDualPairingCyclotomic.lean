import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TatePairingLatticeQuotientsNondegenerateStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionCocycleUniformizerPowSmulMemStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTorsionCocycleFiniteLevelLiftStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLatticeCocyclesModUniformizerPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLimitCocycleOfCompatibleModPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompatibleSeqOfFiniteNonemptyStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TateOrth

section Gen
variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

theorem mem_span_smul_top (L : Lattice (O := O) ρ) (a : O) (x : ↥L.T) :
    x ∈ (Ideal.span {a} • ⊤ : Submodule O ↥L.T) ↔ ∃ y : ↥L.T, x = a • y := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, Submodule.mem_top, rfl⟩

theorem stable_span_smul_top (L : Lattice (O := O) ρ) (a : O) :
    StableSub L (Ideal.span {a} • ⊤ : Submodule O ↥L.T) := by
  intro g x hx
  rw [mem_span_smul_top] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  exact ⟨actT L g y, map_smul _ _ _⟩

theorem factor_actQ (L : Lattice (O := O) ρ) {I J : Submodule O ↥L.T} (hI : StableSub L I)
    (hJ : StableSub L J) (hIJ : I ≤ J) (g : G) (x : ↥L.T ⧸ I) :
    Submodule.factor hIJ (actQ L I hI g x) = actQ L J hJ g (Submodule.factor hIJ x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective I x
  rfl

theorem factor_mem_Z1Q [TopologicalSpace G] (L : Lattice (O := O) ρ) {I J : Submodule O ↥L.T}
    (hI : StableSub L I) (hJ : StableSub L J) (hIJ : I ≤ J) {z : G → ↥L.T ⧸ I}
    (hz : z ∈ quotientCocycles L I hI) : (fun g => Submodule.factor hIJ (z g)) ∈ quotientCocycles L J hJ := by
  refine ⟨hz.1.comp _, fun g h => ?_⟩
  simp only [hz.2 g h, map_add, factor_actQ L hI hJ hIJ]

end Gen

theorem mem_BD_of_orthogonal : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ c ∈ divisibleCocycles LA', (∀ d ∈ latticeCocycles LA, CobO (P.PD K) L1 (cupLD LA' m d c)) → c ∈ BD LA' := by
  intro hT l _ P K LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hm c hc horth
  obtain ⟨hDom, hDVR, hFrac⟩ := hO.1
  haveI := hDom; haveI := hDVR; haveI := hFrac
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  set π := algebraMap O LL ϖ with hπdef
  have hπ : π ≠ 0 := by
    intro h
    exact hϖ.ne_zero (IsFractionRing.injective O LL (by rw [← hπdef, h, map_zero]))
  by_contra hcB
  obtain ⟨r, hr⟩ := GlobalTheory.T.torsionCocycle_uniformizer_pow_smul_mem l K LL O hO A' LA' ϖ hϖ c hc
  let I : ℕ → Submodule O ↥LA.T := fun k => Ideal.span {ϖ ^ (r + k)} • ⊤
  have hI : ∀ k, StableSub LA (I k) := fun k => stable_span_smul_top LA _
  let Φ : ∀ k, (↥(GK K) → ↥LA.T ⧸ I k) → ↥(GK K) × ↥(GK K) → LL := fun k z x =>
    m (Formalism.MainNotions.LocalSituation.liftQ LA (I k) (z x.1)) (A'.ρ x.1 (liftD LA' (c x.2)))
  let Y : ∀ k, Set (↥(GK K) → ↥LA.T ⧸ I k) := fun k =>
    {z | z ∈ quotientCocycles LA (I k) (hI k) ∧ ¬ CobO (P.PD K) L1 (Φ k z)}
  have hle : ∀ k, I (k + 1) ≤ I k := fun k =>
    Submodule.smul_mono_left (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ (by omega)))
  have hle0 : ∀ k, I k ≤ I 0 := fun k =>
    Submodule.smul_mono_left (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ (by omega)))
  let f : ∀ k, (↥(GK K) → ↥LA.T ⧸ I (k + 1)) → (↥(GK K) → ↥LA.T ⧸ I k) := fun k z g =>
    Submodule.factor (hle k) (z g)

  have hmemPow : ∀ (j : ℕ) (x : ↥LA.T), x ∈ (Ideal.span {ϖ ^ j} • ⊤ : Submodule O ↥LA.T) →
      ∃ t ∈ LA.T, (x : A.V) = π ^ j • t := by
    intro j x hx
    obtain ⟨y, rfl⟩ := (mem_span_smul_top LA _ x).1 hx
    exact ⟨y, y.2, by rw [Submodule.coe_smul, hπdef, ← map_pow, algebraMap_smul]⟩
  have hliftMem : ∀ (J : Submodule O ↥LA.T) (x : ↥LA.T ⧸ J), Formalism.MainNotions.LocalSituation.liftQ LA J x ∈ LA.T :=
    fun J x => (Submodule.Quotient.mk_surjective J x).choose.2
  have hspec : ∀ (J : Submodule O ↥LA.T) (x : ↥LA.T ⧸ J), ∃ y : ↥LA.T,
      (y : A.V) = Formalism.MainNotions.LocalSituation.liftQ LA J x ∧ Submodule.Quotient.mk y = x := fun J x =>
    ⟨_, rfl, (Submodule.Quotient.mk_surjective J x).choose_spec⟩
  have hlift2 : ∀ k (x : ↥LA.T ⧸ I k) (y : ↥LA.T), x = Submodule.Quotient.mk y →
      ∃ t ∈ LA.T, Formalism.MainNotions.LocalSituation.liftQ LA (I k) x - (y : A.V) = π ^ (r + k) • t := by
    intro k x y hxy
    obtain ⟨y0, hy0, hmk0⟩ := hspec (I k) x
    have hmem : y0 - y ∈ I k := (Submodule.Quotient.eq _).1 (hmk0.trans hxy)
    obtain ⟨t, ht, he⟩ := hmemPow (r + k) _ hmem
    exact ⟨t, ht, by rw [← hy0, ← he, Submodule.coe_sub]⟩
  have hcong : ∀ (k : ℕ) (a b : A.V) (y : A'.V) (t : A.V), t ∈ LA.T → a - b = π ^ k • t →
      π ^ k • y ∈ LA'.T → m a y - m b y ∈ Set.range (algebraMap O LL) := by
    intro k a b y t ht hab hy
    obtain ⟨e, he⟩ := (hm.2 _).1 hy t ht
    have : m a y - m b y = m t (π ^ k • y) := by
      rw [← LinearMap.sub_apply, ← map_sub, hab, LinearMap.map_smul₂, (m t).map_smul]
    exact ⟨e, by rw [this, he]⟩
  have hcobO : ∀ z z' : ↥(GK K) × ↥(GK K) → LL, (∀ x, z x - z' x ∈ Set.range (algebraMap O LL)) →
      (CobO (P.PD K) L1 z → CobO (P.PD K) L1 z') := by
    intro z z' hzz hz
    have : (fun x => (Submodule.Quotient.mk (z x) : LL ⧸ L1.T)) =
        fun x => Submodule.Quotient.mk (z' x) := by
      funext x
      rw [Submodule.Quotient.eq, hL1]
      obtain ⟨e, he⟩ := hzz x
      exact ⟨e, he⟩
    unfold CobO at hz ⊢
    rwa [← this]
  have hT'pow : ∀ (k : ℕ) (g h : ↥(GK K)), π ^ (r + k) • A'.ρ g (liftD LA' (c h)) ∈ LA'.T := by
    intro k g h
    rw [← map_smul, add_comm, pow_add, mul_smul]
    apply LA'.stable
    rw [hπdef, ← map_pow, algebraMap_smul]
    exact LA'.T.smul_mem _ (hr h)

  have hfin : ∀ k, (Y k).Finite := fun k =>
    (GlobalTheory.T.finite_latticeCocycles_mod_uniformizer_pow hT l K LL O hO A LA ϖ hϖ (r + k) (hI k)).subset (fun z hz => hz.1)
  have hne : ∀ k, (Y k).Nonempty := by
    intro k
    have hI' : StableSub LA' (Ideal.span {ϖ ^ (r + k)} • ⊤ : Submodule O ↥LA'.T) :=
      stable_span_smul_top LA' _
    obtain ⟨c', hc'Z, hc'B, hc'l⟩ :=
      GlobalTheory.T.exists_torsionCocycle_finite_level_lift l K LL O hO A' LA' ϖ hϖ c hc hcB r hr (r + k) (by omega) hI'
    have h2 := (GlobalTheory.T.tate_pairing_lattice_quotients_nondegenerate hT l P K LL O hO L1 hL1 A A' LA LA' m hm ϖ hϖ (r + k) (hI k) hI').2 c' hc'Z
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    apply hc'B
    apply h2
    intro z hz
    have hzY : z ∉ Y k := by rw [hemp]; exact fun h => h
    have hC : CobO (P.PD K) L1 (Φ k z) := by
      by_contra hn; exact hzY ⟨hz, hn⟩
    refine hcobO _ _ ?_ hC
    intro x
    obtain ⟨t, ht, hteq⟩ := hc'l x.2
    obtain ⟨e, he⟩ := (hm.2 _).1 (LA'.stable x.1 t ht) _ (hliftMem (I k) (z x.1))
    refine ⟨-e, ?_⟩
    rw [map_neg, ← he]
    simp only [Φ, hteq, map_add, map_smul, smul_eq_mul, ← hπdef]
    rw [inv_pow]
    field_simp
    ring
  have hmap : ∀ k, ∀ z ∈ Y (k + 1), f k z ∈ Y k := by
    rintro k z ⟨hz, hnc⟩
    refine ⟨factor_mem_Z1Q LA (hI (k + 1)) (hI k) (hle k) hz, fun hc' => hnc (hcobO _ _ ?_ hc')⟩
    intro x
    obtain ⟨t, ht, hteq⟩ := hlift2 k (f k z x.1) ⟨_, hliftMem (I (k + 1)) (z x.1)⟩ (by
      obtain ⟨y0, hy0, hmk0⟩ := hspec (I (k + 1)) (z x.1)
      have hy : (⟨_, hliftMem (I (k + 1)) (z x.1)⟩ : ↥LA.T) = y0 := Subtype.ext hy0.symm
      rw [hy]
      show Submodule.factor (hle k) (z x.1) = _
      rw [← hmk0]
      rfl)
    exact hcong (r + k) _ _ _ t ht hteq (hT'pow k x.1 x.2)
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_compatible_seq_of_finite_nonempty' (fun k => ↥(GK K) → ↥LA.T ⧸ I k) f Y hfin hne hmap
  let w : ℕ → ↥(GK K) → ↥LA.T := fun k g => (Submodule.Quotient.mk_surjective (I k) (s k g)).choose
  have hwk : ∀ k g, (Submodule.Quotient.mk (w k g) : ↥LA.T ⧸ I k) = s k g := fun k g =>
    (Submodule.Quotient.mk_surjective (I k) (s k g)).choose_spec
  have hI'I : ∀ k, I k ≤ (Ideal.span {ϖ ^ k} • ⊤ : Submodule O ↥LA.T) := fun k =>
    Submodule.smul_mono_left (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ (by omega)))
  have hI' : ∀ n : ℕ, StableSub LA (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T) := fun n =>
    stable_span_smul_top LA _
  have hwZ : ∀ n, (fun g => (Submodule.Quotient.mk (w n g) :
      ↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T))) ∈ quotientCocycles LA _ (hI' n) := by
    intro n
    have := factor_mem_Z1Q LA (hI n) (hI' n) (hI'I n) (hs n).1.1
    convert this using 1
    funext g
    rw [← hwk n g]
    rfl
  have hstep : ∀ k g, w (k + 1) g - w k g ∈ I k := by
    intro k g
    apply (Submodule.Quotient.eq _).1
    rw [hwk k g, ← (hs k).2]
    show _ = Submodule.factor (hle k) (s (k + 1) g)
    rw [← hwk (k + 1) g]
    rfl
  obtain ⟨d, hdZ, hd⟩ := GlobalTheory.T.exists_limit_cocycle_of_compatible_mod_pow l K LL O hO A LA ϖ hϖ hI' w hwZ (fun n g => hI'I n (hstep n g))
  have htele : ∀ n g, w n g - w 0 g ∈ I 0 := by
    intro n g
    induction n with
    | zero => simp
    | succ n ih =>
      have := (I 0).add_mem (hle0 n (hstep n g)) ih
      rwa [sub_add_sub_cancel] at this
  apply (hs 0).1.2
  refine hcobO _ _ ?_ (horth d hdZ)
  intro x
  obtain ⟨t1, ht1, hdt⟩ := hd r x.1
  have he : t1 + (w r x.1 - w 0 x.1) ∈ I 0 := (I 0).add_mem ht1 (htele r x.1)
  obtain ⟨u, hu, hue⟩ := hmemPow (r + 0) _ he
  obtain ⟨t3, ht3, ht3e⟩ := hlift2 0 (s 0 x.1) (w 0 x.1) (hwk 0 x.1).symm
  refine hcong (r + 0) _ _ _ (u - t3) (LA.T.sub_mem hu ht3) ?_ (hT'pow 0 x.1 x.2)
  rw [smul_sub, ← hue, ← ht3e, hdt]
  simp only [Submodule.coe_add, Submodule.coe_sub]
  abel

end GlobalTheory.TateOrth
