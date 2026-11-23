import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SaturatedAndIsogenyInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingsCyclotomic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeomSumOneAddPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.QuoFree

theorem finite_of_killed {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M]
    [Module A M] [Module R M] [IsScalarTower R A M] [hM : Module.Finite A M] (q : A)
    (hq : ∀ m : M, q • m = 0) (F : Finset A)
    (hF : ∀ a : A, ∃ c, a - q * c ∈ Submodule.span R (F : Set A)) : Module.Finite R M := by
  obtain ⟨Gs, hG⟩ := hM.fg_top
  set P := Submodule.span R (Set.image2 (· • ·) (F : Set A) (Gs : Set M)) with hPdef
  have key : ∀ b ∈ Submodule.span R (F : Set A), ∀ g ∈ Gs, b • g ∈ P := by
    intro b hb g hg
    induction hb using Submodule.span_induction with
    | mem f hf => exact Submodule.subset_span ⟨f, hf, g, hg, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [add_smul]; exact add_mem hx hy
    | smul r x _ hx => rw [smul_assoc]; exact Submodule.smul_mem _ r hx
  have hsplit : ∀ (a : A) (g : M), g ∈ Gs → a • g ∈ P := by
    intro a g hg
    obtain ⟨c, hc⟩ := hF a
    have : a • g = (a - q * c) • g := by
      rw [sub_smul, mul_comm, mul_smul, hq, smul_zero, sub_zero]
    rw [this]
    exact key _ hc g hg
  let P' : Submodule A M :=
    { carrier := P
      add_mem' := fun ha hb => P.add_mem ha hb
      zero_mem' := P.zero_mem
      smul_mem' := by
        intro a m hm
        induction hm using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨f, hf, g, hg, rfl⟩ := hx
          change a • (f • g) ∈ P
          rw [← mul_smul]
          exact hsplit _ g hg
        | zero => simp
        | add x y _ _ hx hy => rw [smul_add]; exact P.add_mem hx hy
        | smul r x _ hx => rw [smul_comm]; exact P.smul_mem r hx }
  have htop : P = ⊤ := by
    refine eq_top_iff.2 fun m _ => ?_
    have hm : m ∈ Submodule.span A (Gs : Set M) := by rw [hG]; trivial
    have hle : Submodule.span A (Gs : Set M) ≤ P' := Submodule.span_le.2 fun g hg => by
      have := hsplit 1 g hg
      rwa [one_smul] at this
    exact hle hm
  refine ⟨?_⟩
  rw [← htop]
  exact Submodule.fg_span (Set.Finite.image2 _ F.finite_toSet Gs.finite_toSet)

theorem coe_poly_eq_sum {O : Type} [CommRing O] (D : ℕ) (r : Polynomial O) (hr : r.degree < D) :
    (r : PowerSeries O) = ∑ k ∈ Finset.range D, r.coeff k • (PowerSeries.X : PowerSeries O) ^ k := by
  ext m
  simp only [Polynomial.coeff_coe, map_sum, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with hm
  · rfl
  · exact Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hr (by exact_mod_cast not_lt.1 hm))

theorem div_letters {O : Type} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (n : ℕ) [NeZero n] (g : PowerSeries O)
    (hg : g.map (IsLocalRing.residue O) ≠ 0) :
    ∃ F : Finset (LetA O n), ∀ a : LetA O n, ∃ c,
      a - (fun _ => g) * c ∈ Submodule.span O (F : Set (LetA O n)) := by
  classical
  have H : g.IsWeierstrassDivisor := PowerSeries.IsWeierstrassDivisor.of_map_ne_zero hg
  set D := (g.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O))).order.toNat
  refine ⟨(Finset.univ ×ˢ Finset.range D).image
    (fun p : ZMod n × ℕ => (Pi.single p.1 ((PowerSeries.X : PowerSeries O) ^ p.2) : LetA O n)), ?_⟩
  intro a
  refine ⟨fun i => H.div (a i), ?_⟩
  have hdecomp : a - (fun _ => g) * (fun i => H.div (a i)) =
      ∑ i : ZMod n, ∑ k ∈ Finset.range D,
        (H.mod (a i)).coeff k • (Pi.single i ((PowerSeries.X : PowerSeries O) ^ k) : LetA O n) := by
    funext j
    have hd := H.isWeierstrassDivisionAt_div_mod (a j)
    rw [Pi.sub_apply, Pi.mul_apply]
    rw [show a j - g * H.div (a j) = ((H.mod (a j) : Polynomial O) : PowerSeries O) from
      sub_eq_iff_eq_add'.2 hd.eq_mul_add]
    rw [coe_poly_eq_sum D _ hd.degree_lt, Finset.sum_apply,
      Finset.sum_eq_single j]
    · rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Pi.smul_apply, Pi.single_eq_same]
    · intro b _ hb
      rw [Finset.sum_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
    · simp
  rw [hdecomp]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun k hk =>
    Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp only [Finset.coe_image, Finset.coe_product, Finset.coe_univ, Set.mem_image, Set.mem_prod,
    Set.mem_univ, true_and, Finset.mem_coe, Finset.mem_range]
  exact ⟨(i, k), Finset.mem_range.1 hk, rfl⟩

theorem dvd_pow_of_nonunit {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {c p : O} (hc : c ≠ 0) (hp : ¬ IsUnit p) : ∃ k : ℕ, c ∣ p ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  have h1 : ϖ ∣ p := by
    have : p ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hp
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
    exact this
  exact ⟨k, (Units.mul_left_dvd).2 (pow_dvd_pow_of_dvd h1 k)⟩

theorem QQ_pow_map_ne {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (hl : ¬ IsUnit ((l : ℕ) : O)) (s : ℕ) (hs : 1 ≤ s) (y : ℕ) :
    (GlobalTheory.Cyc.QQ l O s ^ y).map (IsLocalRing.residue O) ≠ 0 := by
  obtain ⟨b, hb⟩ := (GlobalTheory.Cyc.XX_QQ_properties l O s hs).2.2.2.1
  have hl0 : ((l : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O)]
    exact (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 hl)
  have hl1 : ((l : ℕ) : PowerSeries (IsLocalRing.ResidueField O)) = 0 := by
    rw [← map_natCast (PowerSeries.C (R := IsLocalRing.ResidueField O)), hl0, map_zero]
  rw [map_pow, hb, map_add, map_mul, map_natCast, map_pow, PowerSeries.map_X, hl1, zero_mul, add_zero,
    ← pow_mul]
  exact pow_ne_zero _ PowerSeries.X_ne_zero

end GlobalTheory.NL.QuoFree

namespace GlobalTheory.NL.QuoFree

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem torsionFree_quo [IsDomain O] [IsDiscreteValuationRing O] (hp : ¬ IsUnit ((PD.p : ℕ) : O))
    (T : LocLat G Qp LL O) (hsat : wachSaturated W T) (S : Submodule (LetA O n) (W.DD T)) :
    Module.IsTorsionFree O (quo W T S (W.N T)) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun c z hz => ?_
  rcases eq_or_ne c 0 with hc | hc
  · exact Or.inl hc
  right
  induction z using Submodule.Quotient.induction_on with
  | H x =>
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hz
  rw [Submodule.Quotient.mk_eq_zero]
  simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul_of_tower] at hz ⊢
  obtain ⟨k, d, hd⟩ := dvd_pow_of_nonunit hc hp
  refine hsat (x : W.DD T) ⟨k, ?_⟩
  rw [GlobalTheory.NL.Isog.pow_smul_eq, hd, mul_comm, mul_smul, ← algebraMap_smul (LetA O n) d]
  exact (W.N T).smul_mem _ hz

theorem finite_quo (T : LocLat G Qp LL O) (q : LetA O n)
    (hq : IsUnit (algebraMap (LetA O n) W.EE q)) (F : Finset (LetA O n))
    (hF : ∀ a : LetA O n, ∃ c, a - q * c ∈ Submodule.span O (F : Set (LetA O n))) :
    Module.Finite O (quo W T (invN W T q) (W.N T)) := by
  set u : W.EE := ↑(hq.unit⁻¹)
  have hinv : ∀ x : W.DD T, q • (u • x) = x := by
    intro x
    rw [← algebraMap_smul W.EE q (u • x), smul_smul]
    have : algebraMap (LetA O n) W.EE q * u = 1 := hq.mul_val_inv
    rw [this, one_smul]
  let φu : W.DD T →ₗ[LetA O n] W.DD T := (LinearMap.lsmul W.EE (W.DD T) u).restrictScalars (LetA O n)
  have hS : invN W T q = (W.N T).map φu := by
    ext z
    constructor
    · intro hz
      refine ⟨q • z, hz, ?_⟩
      change u • (q • z) = z
      rw [← algebraMap_smul W.EE q z, smul_smul, mul_comm, hq.mul_val_inv, one_smul]
    · rintro ⟨x, hx, rfl⟩
      change q • (u • x) ∈ W.N T
      rw [hinv]
      exact hx
  haveI : Module.Finite (LetA O n) ↥(invN W T q) := by
    rw [hS]
    exact Module.Finite.iff_fg.2 ((W.N_fg T).map φu)
  haveI : Module.Finite (LetA O n) (quo W T (invN W T q) (W.N T)) :=
    Module.Finite.quotient (LetA O n) _
  refine finite_of_killed q (fun m => ?_) F hF
  induction m using Submodule.Quotient.induction_on with
  | H x =>
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul_of_tower]
  exact x.2

end Generic

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem quo_free_finite : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ y : ℕ, Module.Free ↥(OL LL) (quo W T (invN W T (W.Q ^ y)) (W.N T)) ∧ Module.Finite ↥(OL LL) (quo W T (invN W T (W.Q ^ y)) (W.N T)) := by
  intro D HW F l _ K s LL h W T hT y
  obtain ⟨hdvr, hcomp, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  haveI := hdvr
  haveI := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hQ : ∀ i, W.Q i = GlobalTheory.Cyc.QQ l ↥(OL LL) s := by
    obtain ⟨_, _, _, _, _, hQ, _⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
    exact hQ
  have hQy : W.Q ^ y = fun _ => GlobalTheory.Cyc.QQ l ↥(OL LL) s ^ y := by
    funext i
    rw [Pi.pow_apply, hQ]
  have hunit : IsUnit (algebraMap (AA K LL) W.EE (W.Q ^ y)) := by
    have := ((GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.2.2 0).2
    rw [pow_zero, AlgHom.one_apply] at this
    rw [map_pow]
    exact this.pow y
  have hp : ¬ IsUnit ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) := by
    rw [(D.loc l).PD_p K]
    exact hl
  have hsat := (GlobalTheory.NL.Isog.saturated_and_isogeny_invariant D HW F l K s LL h).1 T hT
  haveI := hcomp
  obtain ⟨Fs, hFs⟩ := div_letters (Module.finrank ℚ_[l] ↥(K0 K)) (GlobalTheory.Cyc.QQ l ↥(OL LL) s ^ y)
    (QQ_pow_map_ne hl s h.1 y)
  haveI hfin : Module.Finite ↥(OL LL) (quo W T (invN W T (W.Q ^ y)) (W.N T)) :=
    finite_quo W T (W.Q ^ y) hunit Fs (by rw [hQy]; exact hFs)
  haveI := torsionFree_quo W hp T hsat (invN W T (W.Q ^ y))
  exact ⟨Module.free_of_finite_type_torsion_free', hfin⟩

end GlobalTheory.NL.QuoFree
