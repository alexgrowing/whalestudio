import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.LocalRingStructure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LetterSandwichOfFrobMatrices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.CriterionWithoutRoot

noncomputable section

namespace GlobalTheory.HeightsClauseCompare

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.DeltaInvariantLattices TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.LocalRingStructure
open GlobalTheory.WachLettersCompare (mem_Nl_iff letE_smul_mem φD_smulA neZero_letters Q_pow_smul_cancel
  letE_mul_self)

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem isOver_iff (i : ZMod n) (τ : K →ₐ[Qp] LL) : IsOver W i τ ↔ OverLetter W τ i :=
  ⟨fun h => AlgHom.ext h, fun h c => DFunLike.congr_fun h c⟩

theorem jumps_iff (M h : ZMod n → ℕ) : JumpsBounded W T M h ↔ JumpsLet W T M h :=
  ⟨fun H τ i hτ => H i τ ((isOver_iff W i τ).2 hτ), fun H i τ hτ => H τ i ((isOver_iff W i τ).1 hτ)⟩

theorem φA_letE (i : ZMod n) : W.φA (letE (i - 1)) = letE i := by
  funext j
  change W.φ₀ ((letE (i - 1) : LetA O n) (j - 1)) = _
  by_cases hj : j = i
  · subst hj
    simp [letE]
  · have : j - 1 ≠ i - 1 := fun h => hj (sub_left_injective h)
    simp [letE, hj, this]

theorem pole_iff (i : ZMod n) (m : ℕ) :
    (∀ y ∈ phiStar W T i, W.Q ^ m • y ∈ W.Nl T i) ↔
      ∀ x ∈ W.Nl T (i - 1), W.Q ^ m • W.φD T x ∈ W.N T := by
  constructor
  · intro H x hx
    exact ((mem_Nl_iff W T i _).1 (H _ (Submodule.subset_span ⟨x, hx, rfl⟩))).1
  · intro H y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      refine (mem_Nl_iff W T i _).2 ⟨H x hx, ?_⟩
      have h1 := ((mem_Nl_iff W T (i - 1) x).1 hx).2
      rw [smul_comm, ← φA_letE W i, ← φD_smulA, h1]
    | zero => simp
    | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ _ ha

theorem partA_iff (M h : ZMod n → ℕ) : PartA W T M h ↔
    (∀ i, ∀ x ∈ W.Nl T (i - 1), W.Q ^ (M i) • W.φD T x ∈ W.N T) ∧
      (∀ i, ∀ y ∈ W.Nl T i, W.Q ^ (h i) • y ∈ φspan W T (W.Nl T (i - 1))) :=
  ⟨fun H => ⟨fun i => (pole_iff W T i _).1 (H i).1, fun i => (H i).2⟩,
    fun H i => ⟨(pole_iff W T i _).2 (H.1 i), H.2 i⟩⟩

theorem simple_zero (i : ZMod n) (ζ : LL) (hζ : QRoot W i ζ) :
    ∃ w : PowerSeries LL, IsUnit w ∧ W.lev i ζ W.Q = PowerSeries.X * w := by
  have hp := ((GlobalTheory.WachHeightTest.qRoot_iff W i ζ).1 hζ).2
  obtain ⟨w, hw⟩ := PowerSeries.X_dvd_iff.2 hζ.2.2
  refine ⟨w, ?_, hw⟩
  rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  intro h0
  obtain ⟨w', hw'⟩ := PowerSeries.X_dvd_iff.2 h0
  obtain ⟨E, hE, hd, hlev⟩ := W.lev_π i ζ ⟨_, hp⟩
  have hs : W.s = W.s - 1 + 1 := by have := W.s_pos; omega
  have h1 : W.lev i ζ W.Q * ((PowerSeries.C ζ * E) ^ (PD.p ^ (W.s - 1)) - 1) =
      E ^ (PD.p ^ W.s) - 1 := by
    rw [GlobalTheory.WachHeightTest.Q_eq]
    simp only [map_sum, map_pow, map_add, map_one, hlev]
    rw [geom_sum_mul, ← pow_mul, ← pow_succ, ← hs, mul_pow, ← map_pow, hp.pow_eq_one, map_one,
      one_mul]
  have h2 : PowerSeries.X ^ 2 ∣ E ^ (PD.p ^ W.s) - 1 := by
    rw [← h1, hw, hw']
    exact Dvd.dvd.mul_right ⟨w', by ring⟩ _
  have h3 := PowerSeries.X_pow_dvd_iff.1 h2 1 (by norm_num)
  have h4 : PowerSeries.coeff 1 E = 1 := by
    have := congrArg (PowerSeries.coeff 0) hd
    rw [PowerSeries.coeff_derivative] at this
    simpa [hE] using this
  rw [map_sub, PowerSeries.coeff_one_pow, h4, hE] at h3
  simp [PowerSeries.coeff_one] at h3
  exact GlobalTheory.WachHeightTest.p_ne_zero W h3.1

def Van (i : ZMod n) (ζ : LL) (x : W.DD T) : Prop :=
  ∀ k : ℕ, W.Q ^ k • x ∈ W.N T → W.Q ^ k • x ∈ vanI W i ζ k • W.N T

theorem mem_vanI {i : ZMod n} {ζ : LL} {k : ℕ} {a : LetA O n} :
    a ∈ vanI W i ζ k ↔ PowerSeries.X ^ k ∣ W.lev i ζ a := by
  simp only [vanI, Ideal.mem_comap, Ideal.mem_span_singleton]

theorem mem_smul_iff {ι : Type} [Fintype ι] (nb : Module.Basis ι (LetA O n) ↥(W.N T))
    (I : Ideal (LetA O n)) (y : W.DD T) (hy : y ∈ W.N T) :
    y ∈ I • W.N T ↔ ∀ j, nb.repr ⟨y, hy⟩ j ∈ I := by
  constructor
  · intro h
    have key : ∃ h : y ∈ W.N T, ∀ j, nb.repr ⟨y, h⟩ j ∈ I := by
      refine Submodule.smul_induction_on h (fun a ha z hz => ⟨(W.N T).smul_mem a hz, fun j => ?_⟩) ?_
      · have e : (⟨a • z, (W.N T).smul_mem a hz⟩ : ↥(W.N T)) = a • (⟨z, hz⟩ : ↥(W.N T)) := rfl
        rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul]
        exact I.mul_mem_right _ ha
      · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨(W.N T).add_mem ha hb, fun j => ?_⟩
        have e : (⟨a + b, (W.N T).add_mem ha hb⟩ : ↥(W.N T)) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
        rw [e, map_add, Finsupp.add_apply]
        exact I.add_mem (ha' j) (hb' j)
    exact key.2
  · intro h
    have h1 := congrArg Subtype.val (nb.sum_repr ⟨y, hy⟩)
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at h1
    rw [← h1]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (h j) (nb j).2

theorem van_of_one {ι : Type} [Fintype ι] (nb : Module.Basis ι (LetA O n) ↥(W.N T))
    {i : ZMod n} {ζ : LL} (hζ : QRoot W i ζ) {x : W.DD T} {k : ℕ} (hk : W.Q ^ k • x ∈ W.N T)
    (h : W.Q ^ k • x ∈ vanI W i ζ k • W.N T) : Van W T i ζ x := by
  intro k' hk'
  obtain ⟨w, hw, hQ⟩ := simple_zero W i ζ hζ
  rw [mem_smul_iff W T nb _ _ hk] at h
  rw [mem_smul_iff W T nb _ _ hk']
  intro j
  have e : W.Q ^ k' • (⟨_, hk⟩ : ↥(W.N T)) = W.Q ^ k • (⟨_, hk'⟩ : ↥(W.N T)) :=
    Subtype.ext (smul_comm _ _ _)
  have e2 := congrArg (fun z => W.lev i ζ (nb.repr z j)) e
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, map_pow, hQ] at e2
  obtain ⟨c, hc⟩ := (mem_vanI W).1 (h j)
  rw [hc] at e2
  rw [mem_vanI, ← (hw.pow k).dvd_mul_left]
  refine ⟨w ^ k' * c, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero k (PowerSeries.X_ne_zero (R := LL)))
  rw [mul_pow, mul_pow] at e2
  linear_combination -e2

theorem lev_letE (i : ZMod n) (ζ : LL) : W.lev i ζ (letE i) = 1 := by
  have := W.lev_letter i ζ (1 - letE i) (by simp [letE])
  rw [map_sub, map_one] at this
  exact (sub_eq_zero.1 this).symm

theorem memLoc_iff {ι : Type} [Fintype ι] (nb : Module.Basis ι (LetA O n) ↥(W.N T))
    {i : ZMod n} {ζ : LL} (hζ : QRoot W i ζ) {y : W.DD T} (hy : MemInv W T i y) :
    MemLoc W T i ζ y ↔ Van W T i ζ y := by
  obtain ⟨w, hw, hQ⟩ := simple_zero W i ζ hζ
  constructor
  · rintro ⟨k, hk, z, hz⟩
    have hk' := ((mem_Nl_iff W T i _).1 hk).1
    refine van_of_one W T nb hζ hk' ((mem_smul_iff W T nb _ _ hk').2 fun j => ?_)
    have hle : W.Nl T i ≤ W.N T := fun x hx => ((mem_Nl_iff W T i _).1 hx).1
    let f : ↥(W.Nl T i) →ₗ[LetA O n] LocRing W i ζ :=
      (Algebra.linearMap (LetA O n) (LocRing W i ζ)).comp
        ((nb.coord j).comp (Submodule.inclusion hle))
    have h1 := congrArg (f.liftBaseChange (LocRing W i ζ)) hz
    rw [map_smul, LinearMap.liftBaseChange_tmul, one_smul, smul_eq_mul] at h1
    rw [mem_vanI]
    have h2 : W.lev i ζ (nb.repr ⟨_, hk'⟩ j) = W.lev i ζ (W.Q ^ k) *
      (show PowerSeries LL from f.liftBaseChange (LocRing W i ζ) z) := h1
    rw [h2, map_pow, hQ, mul_pow, mul_assoc]
    exact dvd_mul_right _ _
  · intro H
    obtain ⟨k, hk⟩ := hy
    obtain ⟨hk', he⟩ := (mem_Nl_iff W T i _).1 hk
    refine ⟨k, hk, ?_⟩
    have key : ∀ m ∈ vanI W i ζ k • W.N T, ∃ (hm : (letE i : LetA O n) • m ∈ W.Nl T i)
        (z : Nloc W T i ζ), (1 : LocRing W i ζ) ⊗ₜ[LetA O n] (⟨_, hm⟩ : ↥(W.Nl T i)) =
          (algebraMap (LetA O n) (LocRing W i ζ) (W.Q ^ k)) • z := by
      intro m hm
      refine Submodule.smul_induction_on hm (fun a ha z hz => ?_) ?_
      · refine ⟨letE_smul_mem W T i ((W.N T).smul_mem a hz), ?_⟩
        have hd : W.lev i ζ (W.Q ^ k) ∣ W.lev i ζ a := by
          rw [map_pow, hQ, mul_pow, (hw.pow k).mul_right_dvd]
          exact (mem_vanI W).1 ha
        obtain ⟨c, hc⟩ := hd
        refine ⟨(show LocRing W i ζ from c) ⊗ₜ[LetA O n]
          (⟨_, letE_smul_mem W T i hz⟩ : ↥(W.Nl T i)), ?_⟩
        have e : (⟨_, letE_smul_mem W T i ((W.N T).smul_mem a hz)⟩ : ↥(W.Nl T i)) =
            a • (⟨_, letE_smul_mem W T i hz⟩ : ↥(W.Nl T i)) := Subtype.ext (smul_comm _ _ _)
        rw [e, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul,
          Algebra.smul_def, mul_one]
        congr 1
      · rintro a b ⟨ha, za, ha'⟩ ⟨hb, zb, hb'⟩
        refine ⟨by rw [smul_add]; exact Submodule.add_mem _ ha hb, za + zb, ?_⟩
        rw [smul_add _ za zb, ← ha', ← hb', ← TensorProduct.tmul_add]
        congr 1
        exact Subtype.ext (smul_add _ _ _)
    obtain ⟨hm, z, hz⟩ := key _ (H k hk')
    refine ⟨z, ?_⟩
    rw [← hz]
    congr 1
    exact Subtype.ext he.symm

theorem fixed_of_memInv {i : ZMod n} {y : W.DD T} (hy : MemInv W T i y) :
    (letE i : LetA O n) • y = y := by
  obtain ⟨k, hk⟩ := hy
  refine Q_pow_smul_cancel W T k ?_
  rw [smul_comm]
  exact ((mem_Nl_iff W T i _).1 hk).2

theorem van_other {i i' : ZMod n} (h : i' ≠ i) (ζ : LL) {y : W.DD T}
    (hy : (letE i : LetA O n) • y = y) : Van W T i' ζ y := by
  intro k hk
  rw [← hy, smul_comm]
  refine Submodule.smul_mem_smul ?_ hk
  rw [mem_vanI, W.lev_letter i' ζ _ (by simp [letE, h])]
  exact dvd_zero _

theorem van_letE_iff {ι : Type} [Fintype ι] (nb : Module.Basis ι (LetA O n) ↥(W.N T))
    {i : ZMod n} {ζ : LL} (hζ : QRoot W i ζ) {x : W.DD T} (hx : ∃ k : ℕ, W.Q ^ k • x ∈ W.N T) :
    Van W T i ζ ((letE i : LetA O n) • x) ↔ Van W T i ζ x := by
  obtain ⟨k, hk⟩ := hx
  have hk' : W.Q ^ k • (letE i : LetA O n) • x ∈ W.N T := by
    rw [smul_comm]; exact (W.N T).smul_mem _ hk
  constructor
  · intro H
    refine van_of_one W T nb hζ hk ?_
    have e : W.Q ^ k • x = W.Q ^ k • (letE i : LetA O n) • x + (1 - letE i : LetA O n) • W.Q ^ k • x := by
      rw [smul_comm (W.Q ^ k) (letE i : LetA O n), ← add_smul, add_sub_cancel, one_smul]
    rw [e]
    refine Submodule.add_mem _ (H k hk') (Submodule.smul_mem_smul ?_ hk)
    rw [mem_vanI, map_sub, map_one, lev_letE, sub_self]
    exact dvd_zero _
  · intro H
    refine van_of_one W T nb hζ hk' ?_
    rw [smul_comm]
    exact Submodule.smul_mem _ _ (H k hk)

include W in
theorem mem_N_iff (x : W.DD T) : x ∈ W.N T ↔ ∀ i, (letE i : LetA O n) • x ∈ W.Nl T i := by
  refine ⟨fun h i => letE_smul_mem W T i h, fun h => ?_⟩
  haveI := neZero_letters W
  have e : (∑ i, letE i : LetA O n) = 1 := Finset.univ_sum_single (1 : LetA O n)
  rw [← one_smul (LetA O n) x, ← e, Finset.sum_smul]
  exact Submodule.sum_mem _ fun i _ => ((mem_Nl_iff W T i _).1 (h i)).1

theorem partB_iff {ι : Type} [Fintype ι] (nb : Module.Basis ι (LetA O n) ↥(W.N T))
    (hO : ∀ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ W.s) → ∃ c : O, algebraMap O LL c = ζ) :
    PartB W T ↔ ∀ x : W.DD T, (∃ k : ℕ, W.Q ^ k • x ∈ W.N T) →
      (x ∈ W.N T ↔ ∀ i ζ, QRoot W i ζ → ∀ k : ℕ, W.Q ^ k • x ∈ W.N T →
        W.Q ^ k • x ∈ vanI W i ζ k • W.N T) := by
  have hr : ∀ i ζ, QRoot W i ζ ↔ IsPrimitiveRoot ζ (PD.p ^ W.s) := fun i ζ =>
    (GlobalTheory.WachHeightTest.qRoot_iff W i ζ).trans ⟨fun h => h.2, fun h => ⟨hO ζ h, h⟩⟩
  constructor
  · intro H x hx
    have hi : ∀ i, MemInv W T i ((letE i : LetA O n) • x) := fun i => by
      obtain ⟨k, hk⟩ := hx
      exact ⟨k, by rw [smul_comm]; exact letE_smul_mem W T i hk⟩
    rw [mem_N_iff W T x]
    refine forall_congr' fun i => ?_
    rw [H i _ (hi i)]
    refine forall_congr' fun ζ => ?_
    rw [← hr i ζ]
    refine imp_congr_right fun hζ => ?_
    rw [memLoc_iff W T nb hζ (hi i), van_letE_iff W T nb hζ hx]
    rfl
  · intro H i y hy
    have he := fixed_of_memInv W T hy
    have hx : ∃ k : ℕ, W.Q ^ k • y ∈ W.N T := by
      obtain ⟨k, hk⟩ := hy
      exact ⟨k, ((mem_Nl_iff W T i _).1 hk).1⟩
    rw [mem_Nl_iff, and_iff_left he, H y hx]
    constructor
    · intro h ζ hζ
      exact (memLoc_iff W T nb ((hr i ζ).2 hζ) hy).2 (h i ζ ((hr i ζ).2 hζ))
    · intro h i' ζ hζ
      by_cases hi : i' = i
      · subst hi
        exact (memLoc_iff W T nb hζ hy).1 (h ζ ((hr _ ζ).1 hζ))
      · exact van_other W T hi ζ he

theorem partAB_iff {ι : Type} [Fintype ι] (nb : Module.Basis ι (LetA O n) ↥(W.N T))
    (hO : ∀ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ W.s) → ∃ c : O, algebraMap O LL c = ζ)
    (M h : ZMod n → ℕ) : PartA W T M h ∧ PartB W T ↔ p5 W T M h := by
  rw [partA_iff, partB_iff W T nb hO, and_assoc]
  rfl

theorem partC_iff {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW]
    {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA) (M h : ℕ) : PartC E T M h ↔ wachInfiniteLevelJumpBound W E T M h := Iff.rfl

end Generic

theorem letterMax_eq {l : ℕ} [Fact l.Prime] (K : FinExt l)
    (m : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ) : letterMax K m = mx m := by
  haveI := letters_neZero K
  unfold letterMax mx
  exact Finset.sup_univ_eq_ciSup m

theorem partAB_iff_good {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (hg : Good K s LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (hT : IsCrys (P.PD K) T.ρ) (M h : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ) :
    PartA (H.W K s LL hg) T M h ∧ PartB (H.W K s LL hg) T ↔ p5 (H.W K s LL hg) T M h := by
  obtain ⟨nb⟩ := GlobalTheory.NL.N_basis_loc H K s LL hg T hT
  refine partAB_iff _ T nb (fun ζ hζ => ⟨⟨ζ, ?_⟩, rfl⟩) M h
  exact IsIntegral.of_pow (pow_pos (P.PD K).hp.pos _) (by rw [hζ.pow_eq_one]; exact isIntegral_one)

theorem heights_iff_loc (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) (C : LocCmpT l P AI H F) :
    HeightsFromJumps l P AI H F C ↔
      (∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (hg : Good K s LL), P5W (H.W K s LL hg)) ∧
      (∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (hg : Good K s LL),
        WachInfiniteLevelBound (H.W K s LL hg) (F.E K s LL hg).tie) := by
  constructor
  · intro h
    refine ⟨fun K s LL hg T M h' hT hJ => ?_, fun K s LL hg T M h' hT hJ => ?_⟩
    · have := h K s LL hg T hT M h' ((jumps_iff _ T M h').2 hJ)
      exact (partAB_iff_good H K s LL hg T hT M h').1 ⟨this.1, this.2.1⟩
    · have := (h K s LL hg T hT M h' ((jumps_iff _ T M h').2 hJ)).2.2
      rwa [letterMax_eq, letterMax_eq, partC_iff] at this
  · rintro ⟨h1, h2⟩ K s LL hg T hT M h' hJ
    have hJ' := (jumps_iff _ T M h').1 hJ
    have := (partAB_iff_good H K s LL hg T hT M h').2 (h1 K s LL hg T M h' hT hJ')
    refine ⟨this.1, this.2, ?_⟩
    rw [letterMax_eq, letterMax_eq, partC_iff]
    exact h2 K s LL hg T M h' hT hJ'

theorem heights_iff (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (C : CmpOf D.loc D.locA HW F) :
    (∀ (l : ℕ) [Fact l.Prime], HeightsFromJumps l (D.loc l) (D.locA l) (HW l) (F l) (C l)) ↔
      P5 D HW F ∧ p5eL D.loc D.locA HW F :=
  ⟨fun h => ⟨fun l _ => ((heights_iff_loc l _ _ _ _ _).1 (h l)).1,
      fun l _ => ((heights_iff_loc l _ _ _ _ _).1 (h l)).2⟩,
    fun h l _ => (heights_iff_loc l _ _ _ _ _).2 ⟨h.1 l, h.2 l⟩⟩

end GlobalTheory.HeightsClauseCompare
