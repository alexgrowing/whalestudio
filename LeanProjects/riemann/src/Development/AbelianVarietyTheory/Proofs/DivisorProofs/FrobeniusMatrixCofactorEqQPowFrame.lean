import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeHeightsFromHodgeJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpIffMultNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcretePeriodDeRhamModuleFinrankLe
import Formalism.PieriBlockIdeals.PieriColumnMinors.HeightDescentMinors

set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.WachPlace.FrameHeight

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {f : ℕ}
    (W : LocWach PD LL O v f)

theorem φD_smul_A (T : LocLat G Qp LL O) (a : LetA O f) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O f) W.EE a) x
  rwa [algebraMap_smul, W.φE_ext, algebraMap_smul] at this

theorem φpull_le_span {n : ℕ} (T : LocLat G Qp LL O) (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) :
    W.φpull T ≤ Submodule.span (LetA O f) (Set.range fun j => W.φD T (b j : W.DD T)) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  have e := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
  simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at e
  rw [← e, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [φD_smul_A]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem exists_inv {n : ℕ} (T : LocLat G Qp LL O) (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T))
    (PA : Matrix (Fin n) (Fin n) (LetA O f))
    (hφ : ∀ k, W.φD T (b k : W.DD T) = ∑ m, PA m k • (b m : W.DD T)) (h : ℕ) (i : ZMod f)
    (h5 : ∀ y ∈ W.Nl T i, W.Q ^ h • y ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (i - 1))) :
    ∃ Qm : Matrix (Fin n) (Fin n) (PowerSeries O),
      (PA.map fun a => a i) * Qm = (W.Q i ^ h) • (1 : Matrix (Fin n) (Fin n) (PowerSeries O)) := by
  have hsp : ∀ k, ∃ c : Fin n → LetA O f,
      ∑ j, c j • W.φD T (b j : W.DD T) = W.Q ^ h • (letE i : LetA O f) • (b k : W.DD T) := by
    intro k
    have hy : (letE i : LetA O f) • (b k : W.DD T) ∈ W.Nl T i :=
      Submodule.mem_map_of_mem (b k).2
    have h1 := h5 _ hy
    have hle : Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (i - 1)) ≤ W.φpull T :=
      Submodule.span_mono (Set.image_mono (by
        rintro _ ⟨x, hx, rfl⟩
        exact (W.N T).smul_mem _ hx))
    exact (Submodule.mem_span_range_iff_exists_fun (LetA O f)).1 (φpull_le_span W T b (hle h1))
  choose c hc using hsp
  have hli : LinearIndependent (LetA O f) fun m => (b m : W.DD T) :=
    b.linearIndependent.map' (W.N T).subtype (Submodule.ker_subtype _)
  have key : ∀ k m, ∑ j, c k j * PA m j = if m = k then W.Q ^ h * (letE i : LetA O f) else 0 := by
    intro k
    have e1 : ∑ m, (∑ j, c k j * PA m j - if m = k then W.Q ^ h * (letE i : LetA O f) else 0) •
        (b m : W.DD T) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
        if_true, Finset.sum_smul, mul_smul]
      rw [← hc k, sub_eq_zero, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hφ, Finset.smul_sum]
    intro m
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ e1 m)
  refine ⟨Matrix.of fun j k => c k j i, ?_⟩
  refine Matrix.ext fun m k => ?_
  have e2 := congrFun (key k m) i
  simp only [Finset.sum_apply, Pi.mul_apply] at e2
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  simp only [Matrix.map_apply, Matrix.of_apply]
  rw [show (∑ j, PA m j i * c k j i) = ∑ j, c k j i * PA m j i from
    Finset.sum_congr rfl fun j _ => mul_comm _ _, e2]
  by_cases hmk : m = k
  · simp [hmk, letE]
  · simp [hmk]

end Generic

end GlobalTheory.WachPlace.FrameHeight

namespace GlobalTheory.WachPlace.FrameHeight

theorem frame_height : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ) (n h : ℕ) (γ : ((HW l).W K 1 LL hA.2.2).Gam) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T)) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)), GlobalTheory.AdmLoc.CrysWith ((D.loc l).PD K) ((HW l).W K 1 LL hA.2.2).emb T.ρ U → (∀ i, ∀ u ∈ U i, 0 ≤ u ∧ u ≤ (h : ℤ)) → IsFrame ((HW l).W K 1 LL hA.2.2) T γ b N → ∀ i, ∃ Q : Mx (PowerSeries ↥(OL LL)) n n, (N.P i).map (inc l ↥(OL LL)) * Q = (q l ↥(OL LL) ^ h) • (1 : Mx (PowerSeries ↥(OL LL)) n n) := by
  intro D HW F Cm l _ K LL hA T U n h γ b N hU hb hfr i
  have hJ : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet ((HW l).W K 1 LL hA.2.2) T (fun _ => 0) (fun _ => h) := by
    intro τ i' hτ a ha
    haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ).1
    have h1 := (GlobalTheory.Per.JumpMult.jump_iff_of_finite ((D.loc l).PD K) T.ρ τ a).2.2.1 ha
    rw [hU.2 i' τ (fun x => DFunLike.congr_fun hτ x) a] at h1
    have h2 := hb i' a (Multiset.count_ne_zero.1 (by exact_mod_cast h1))
    exact ⟨by simpa using h2.1, h2.2⟩
  have h5 := (GlobalTheory.NL.Heights.heights_from_jumps D HW F Cm l K 1 LL hA.2.2 T (fun _ => 0) (fun _ => h)
    hU.1 hJ).2.1 i
  obtain ⟨Qm, hQm⟩ := exists_inv ((HW l).W K 1 LL hA.2.2) T b
    (fun m k => fun i => inc l ↥(OL LL) (N.P i m k)) hfr.2.1 h i h5
  have hq : ((HW l).W K 1 LL hA.2.2).Q i = q l ↥(OL LL) := by
    have e1 : ((HW l).W K 1 LL hA.2.2).Q = ((HW l).W K 1 LL hA.2.2).q := by
      unfold LocWach.Q
      rw [(HW l).W_s K 1 LL hA.2.2]
      rfl
    rw [e1]
    change ((HW l).W K 1 LL hA.2.2).q₀ = q l ↥(OL LL)
    have e2 := ((HW l).W K 1 LL hA.2.2).q₀_def
    rw [(D.loc l).PD_p K, ← (q_multiplicative_holds l ↥(OL LL)).1] at e2
    refine PowerSeries.ext fun j => ?_
    have e3 := congrArg (PowerSeries.coeff (j + 1)) e2
    simpa only [PowerSeries.coeff_succ_X_mul] using e3
  refine ⟨Qm, ?_⟩
  rw [← hq]
  exact hQm

end GlobalTheory.WachPlace.FrameHeight

end
