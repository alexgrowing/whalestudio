import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvFilD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt

section
open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.MemLoc
open scoped Formalism.Per

namespace Bridge.TateSpanAlt

theorem exists_ev {L A : Type*} [Field L] [CommRing A] (t : A)
    [hc : IsAdicComplete (Ideal.span {t}) A] (ι : L →+* A) :
    ∃ ev : PowerSeries L →+* A, (∀ c, ev (PowerSeries.C c) = ι c) ∧ ev PowerSeries.X = t := by
  letI : WithIdeal A := ⟨Ideal.span {t}⟩
  letI : UniformSpace L := ⊥
  haveI : DiscreteUniformity L := ⟨rfl⟩
  have hadic : IsAdic (Ideal.span {t}) := rfl
  obtain ⟨h1, h2⟩ := (hadic.isAdicComplete_iff).1 hc
  haveI : IsLinearTopology A A := Ideal.isLinearTopology (Ideal.span {t})
  have hι : Continuous ι := continuous_of_discreteTopology
  have ht : PowerSeries.HasEval t := by
    refine (WithIdeal.isTopologicallyNilpotent_of_mem ?_)
    exact Ideal.mem_span_singleton_self t
  refine ⟨PowerSeries.eval₂Hom hι ht, fun c => ?_, ?_⟩
  · rw [PowerSeries.coe_eval₂Hom]; exact PowerSeries.eval₂_C _ _ _
  · rw [PowerSeries.coe_eval₂Hom]; exact PowerSeries.eval₂_X _ _

theorem ev_sub {L A : Type*} [Field L] [CommRing A] (t : A) (ι : L →+* A)
    (ev : PowerSeries L →+* A) (hC : ∀ c, ev (PowerSeries.C c) = ι c) (hX : ev PowerSeries.X = t)
    (f : PowerSeries L) (M : ℕ) :
    t ^ M ∣ ev f - ∑ k ∈ Finset.range M, ι (PowerSeries.coeff k f) * t ^ k := by
  have h : (PowerSeries.X : PowerSeries L) ^ M ∣
      f - ∑ k ∈ Finset.range M, PowerSeries.C (PowerSeries.coeff k f) * PowerSeries.X ^ k := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    simp [map_sum, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, hm]
  have := map_dvd ev h
  simpa [map_sum, hC, hX] using this

theorem ev_dvd_iff {L A : Type*} [Field L] [CommRing A] [IsDomain A] (t : A) (ht0 : t ≠ 0)
    (htu : ¬ IsUnit t) (ι : L →+* A)
    (ev : PowerSeries L →+* A) (hC : ∀ c, ev (PowerSeries.C c) = ι c) (hX : ev PowerSeries.X = t)
    (f : PowerSeries L) (M : ℕ) :
    t ^ M ∣ ev f ↔ (PowerSeries.X : PowerSeries L) ^ M ∣ f := by
  constructor
  · induction M with
    | zero => simp
    | succ n ih =>
      intro h
      obtain ⟨g, rfl⟩ := ih ((pow_dvd_pow t n.le_succ).trans h)
      rw [map_mul, map_pow, hX, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero n ht0)] at h
      rw [pow_succ]
      refine mul_dvd_mul_left _ ?_
      rw [PowerSeries.X_dvd_iff]
      by_contra hg
      have hu : IsUnit g := PowerSeries.isUnit_iff_constantCoeff.2 (Ne.isUnit hg)
      exact htu (isUnit_of_dvd_unit h (hu.map ev))
  · intro h
    simpa [hX] using map_dvd ev h

open Reformulated.AutPerF Formalism in
open scoped Formalism.Per in

theorem main (l : ℕ) [Fact l.Prime] {B L : Type*} [CommRing B] [Field L]
    (e : B ≃+* BdR l (Per.OC l)) (Fil : ℤ → B → Prop)
    (hF : ∀ a x, Fil a x ↔ e x ∈ BdR.fil l (Per.OC l) a) (t : B) (π : BdRPlus l (Per.OC l))
    (hπ : RingHom.ker (BdRPlus.theta l (Per.OC l)) = Ideal.span {π})
    (ht : e t = algebraMap _ _ π) (ι : L →+* B) (hι : ∀ x, Fil 0 (ι x)) :
    ∃ ev : PowerSeries L →+* B,
      (∀ f (M : ℕ), Fil M (ev f - ∑ k ∈ Finset.range M, ι (PowerSeries.coeff k f) * t ^ k)) ∧
      (∀ f (M : ℕ), Fil M (ev f) ↔ (PowerSeries.X : PowerSeries L) ^ M ∣ f) ∧ IsUnit t ∧
      (∀ (a : ℤ) (b : B), Fil (a + 1) (t * b) ↔ Fil a b) ∧ ∀ b, (∀ a, Fil a b) → b = 0 := by
  have hinj : Function.Injective (algebraMap (BdRPlus l (Per.OC l)) (BdR l (Per.OC l))) :=
    BdR.algebraMap_injective
  have h0 := BdR.algebraMap_ne_zero hπ
  have hirr := (BdRPlus.irreducible_iff π).2 hπ
  choose j hj using fun x => (BdR.mem_fil_zero_iff _).1 ((hF _ _).1 (hι x))
  let ι₀ : L →+* BdRPlus l (Per.OC l) :=
    { toFun := j
      map_one' := hinj (by rw [hj]; simp)
      map_mul' := fun x y => hinj (by rw [map_mul, hj, hj, hj, map_mul, map_mul])
      map_zero' := hinj (by rw [hj]; simp)
      map_add' := fun x y => hinj (by rw [map_add, hj, hj, hj, map_add, map_add]) }
  have hj' : ∀ x, algebraMap _ (BdR l (Per.OC l)) (ι₀ x) = e (ι x) := hj
  haveI : IsAdicComplete (Ideal.span {π}) (BdRPlus l (Per.OC l)) := by
    rw [← hπ]; infer_instance
  obtain ⟨ev, hC, hX⟩ := exists_ev π ι₀
  have key : ∀ (M : ℕ) (y : BdRPlus l (Per.OC l)),
      algebraMap _ (BdR l (Per.OC l)) y ∈ BdR.fil l (Per.OC l) M ↔ π ^ M ∣ y := fun M y => by
    rw [BdR.algebraMap_mem_fil_iff, BdRPlus.fil, hπ, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  refine ⟨e.symm.toRingHom.comp ((algebraMap _ (BdR l (Per.OC l))).comp ev), fun f M => ?_,
    fun f M => ?_, ?_, fun a b => ?_, fun b hb => ?_⟩
  · have := (key M _).2 (ev_sub π ι₀ ev hC hX f M)
    rw [hF]
    convert this using 1
    simp [map_sum, hj', ht]
  · rw [hF, ← ev_dvd_iff π hirr.ne_zero hirr.not_isUnit ι₀ ev hC hX, ← key]
    simp
  · have := (h0.isUnit).map e.symm
    rwa [← ht, e.symm_apply_apply] at this
  · rw [hF, hF, map_mul, ht, BdR.mem_fil_iff hπ, BdR.mem_fil_iff hπ]
    refine exists_congr fun c => ?_
    rw [zpow_add_one₀ h0, mul_comm _ (algebraMap _ _ π), mul_assoc, mul_right_inj' h0]
  · exact e.injective (by
      rw [map_zero]; exact BdR.eq_zero_of_forall_mem_fil fun a => (hF _ _).1 (hb a))

open Reformulated.AutPerF Formalism in
open scoped Formalism.Per in

theorem exists_gen (l : ℕ) [Fact l.Prime] (x : BdR l (Per.OC l))
    (h1 : x ∈ BdR.fil l (Per.OC l) 1) (h2 : x ∉ BdR.fil l (Per.OC l) 2) :
    ∃ π : BdRPlus l (Per.OC l), RingHom.ker (BdRPlus.theta l (Per.OC l)) = Ideal.span {π} ∧
      x = algebraMap _ _ π := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat l (Per.OC l)) := inferInstance
  have hξ := BdRPlus.ker_theta ϖ
  obtain ⟨c, hc⟩ := (BdR.mem_fil_iff hξ 1 x).1 h1
  have hu : IsUnit c := by
    rw [BdRPlus.isUnit_iff_theta_ne_zero, Ne, BdRPlus.theta_eq_zero_iff_dvd ϖ]
    rintro ⟨d, rfl⟩
    exact h2 ((BdR.mem_fil_iff hξ 2 x).2 ⟨d, by rw [hc, map_mul, zpow_one, zpow_two, mul_assoc]⟩)
  exact ⟨BdRPlus.xi ϖ * c, by rw [Ideal.span_singleton_mul_right_unit hu, hξ],
    by rw [hc, zpow_one, map_mul]⟩

open Reformulated.AutPerF Formalism in
open scoped Formalism.Per in
theorem main' (l : ℕ) [Fact l.Prime] {B L : Type*} [CommRing B] [Field L]
    (e : B ≃+* Per.BdR l) (Fil : ℤ → B → Prop)
    (hF : ∀ a x, Fil a x ↔ e x ∈ Per.FilD l a) (t : B) (h1 : Fil 1 t) (h2 : ¬ Fil 2 t)
    (ι : L →+* B) (hι : ∀ x, Fil 0 (ι x)) :
    ∃ ev : PowerSeries L →+* B,
      (∀ f (M : ℕ), Fil M (ev f - ∑ k ∈ Finset.range M, ι (PowerSeries.coeff k f) * t ^ k)) ∧
      (∀ f (M : ℕ), Fil M (ev f) ↔ (PowerSeries.X : PowerSeries L) ^ M ∣ f) ∧ IsUnit t ∧
      (∀ (a : ℤ) (b : B), Fil (a + 1) (t * b) ↔ Fil a b) ∧ ∀ b, (∀ a, Fil a b) → b = 0 := by
  obtain ⟨π, hπ, ht⟩ := exists_gen l (e t) ((hF _ _).1 h1) (fun h => h2 ((hF _ _).2 h))
  exact main l e Fil hF t π hπ ht ι hι

open Reformulated.AutPerF in

theorem mem_zero_of_isIntegral (l : ℕ) [Fact l.Prime] {F B : Type*} [Field F] [CommRing B]
    [Algebra F B] (e : B ≃+* BdR l (Per.OC l))
    (h : ∀ c : F, ∃ y : BdRPlus l (Per.OC l), algebraMap _ _ y = e (algebraMap F B c))
    {x : B} (hx : IsIntegral F x) : e x ∈ BdR.fil l (Per.OC l) 0 := by
  rw [BdR.mem_fil_zero_iff, ← IsIntegrallyClosed.isIntegral_iff]
  obtain ⟨q, hq, h0⟩ := hx
  have hl : q.map (e.toRingHom.comp (algebraMap F B)) ∈
      Polynomial.lifts (algebraMap (BdRPlus l (Per.OC l)) (BdR l (Per.OC l))) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    exact h _
  obtain ⟨r, hr, -, hm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (hq.map _)
  refine ⟨r, hm, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hr, ← Polynomial.eval₂_eq_eval_map]
  have := Polynomial.hom_eval₂ q (algebraMap F B) e.toRingHom x
  rw [h0, map_zero] at this
  exact this.symm

theorem mem_zero (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K : FinExt l) {x : P.R.BdR} (hx : IsIntegral ℚ_[l] x) : x ∈ (P.PD K).Fil 0 := by
  refine (T.fil K 0 x).2 (mem_zero_of_isIntegral l _ (fun c => ?_) hx)
  obtain ⟨y, h1, -⟩ := T.om (algebraMap ℚ_[l] (Om l) c)
  rw [← IsScalarTower.algebraMap_apply] at h1
  exact ⟨y, h1.symm⟩

theorem reduction (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K LL : FinExt l) (s : ℕ) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR)
    (h1 : GlobalTheory.NL.tS P s ∈ (P.PD K).Fil 1) (h2 : GlobalTheory.NL.tS P s ∉ (P.PD K).Fil 2) :
    ∃ ev : PowerSeries ↥LL.1 →+* P.R.BdR,
      (∀ f (M : ℕ), (ev f - ∑ k ∈ Finset.range M, ι (PowerSeries.coeff k f) * GlobalTheory.NL.tS P s ^ k) ∈
        (P.PD K).Fil M) ∧
      (∀ f (M : ℕ), ev f ∈ (P.PD K).Fil M ↔ (PowerSeries.X : PowerSeries ↥LL.1) ^ M ∣ f) ∧
      IsUnit (GlobalTheory.NL.tS P s) ∧
      (∀ (a : ℤ) (b : P.R.BdR), GlobalTheory.NL.tS P s * b ∈ (P.PD K).Fil (a + 1) ↔ b ∈ (P.PD K).Fil a) ∧
      ∀ b : P.R.BdR, (∀ a, b ∈ (P.PD K).Fil a) → b = 0 :=
  main' l _ (fun a x => x ∈ (P.PD K).Fil a) (fun a x => T.fil K a x) _ h1 h2 ι.toRingHom
    (fun x => by
      haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
      exact mem_zero l P AI T K ((IsIntegral.of_finite ℚ_[l] x).map ι))

theorem smul_mem (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K : FinExt l) (c : ℚ_[l]) (a : ℤ) (x : P.R.BdR) (hx : x ∈ (P.PD K).Fil a) :
    c • x ∈ (P.PD K).Fil a := by
  have h0 := (T.fil K 0 _).1 (mem_zero l P AI T K (isIntegral_algebraMap (x := c)))
  refine (T.fil K a _).2 ?_
  rw [Algebra.smul_def, map_mul]
  have := Reformulated.AutPerF.BdR.mul_mem_fil (p := l) (R := Per.OC l) h0 ((T.fil K a _).1 hx)
  rw [zero_add] at this
  exact this

theorem tS_mem_iff (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K : FinExt l) (s : ℕ) (a : ℤ) :
    GlobalTheory.NL.tS P s ∈ (P.PD K).Fil a ↔ P.ιB P.tB ∈ (P.PD K).Fil a := by
  refine ⟨fun h => ?_, smul_mem l P AI T K _ a _⟩
  have := smul_mem l P AI T K ((l : ℚ_[l]) ^ s) a _ h
  rwa [GlobalTheory.NL.tS, smul_smul, mul_inv_cancel₀
    (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)), one_smul] at this

theorem reduction' (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K LL : FinExt l) (s : ℕ) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR)
    (h1 : P.ιB P.tB ∈ (P.PD K).Fil 1) (h2 : P.ιB P.tB ∉ (P.PD K).Fil 2) :
    ∃ ev : PowerSeries ↥LL.1 →+* P.R.BdR,
      (∀ f (M : ℕ), (ev f - ∑ k ∈ Finset.range M, ι (PowerSeries.coeff k f) * GlobalTheory.NL.tS P s ^ k) ∈
        (P.PD K).Fil M) ∧
      (∀ f (M : ℕ), ev f ∈ (P.PD K).Fil M ↔ (PowerSeries.X : PowerSeries ↥LL.1) ^ M ∣ f) ∧
      IsUnit (GlobalTheory.NL.tS P s) ∧
      (∀ (a : ℤ) (b : P.R.BdR), GlobalTheory.NL.tS P s * b ∈ (P.PD K).Fil (a + 1) ↔ b ∈ (P.PD K).Fil a) ∧
      ∀ b : P.R.BdR, (∀ a, b ∈ (P.PD K).Fil a) → b = 0 :=
  reduction l P AI T K LL s ι ((tS_mem_iff l P AI T K s 1).2 h1)
    (fun h => h2 ((tS_mem_iff l P AI T K s 2).1 h))

end Bridge.TateSpanAlt

theorem Bridge.exists_power_series_evaluation : ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (P : Formalism.BasicNotions.LocPrime l) (AI : Formalism.BasicNotions.LocAinf l P) (T : Formalism.BasicNotions.LocTied l P AI) (K LL : Formalism.BasicNotions.Loc.FinExt l) (s : ℕ) (ι : ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K)) →ₐ[ℚ_[l]] P.R.BdR), ∃ (ev : PowerSeries ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K)) →+* P.R.BdR), (∀ (f : PowerSeries ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) (M : ℕ), HSub.hSub (α := P.R.BdR) (β := P.R.BdR) (DFunLike.coe (β := fun (x : PowerSeries ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) ↦ P.R.BdR) ev f : P.R.BdR) (∑ k ∈ Finset.range M, HMul.hMul (α := P.R.BdR) (DFunLike.coe (α := ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) (β := fun (x : ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) ↦ P.R.BdR) ι (DFunLike.coe (F := LinearMap (R := ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) (RingHom.id ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) (PowerSeries ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) (β := fun (x : PowerSeries ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) ↦ ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) (PowerSeries.coeff k) f : ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) : P.R.BdR) (GlobalTheory.NL.tS P s ^ k) : P.R.BdR) ∈ (P.PD K).Fil M.cast) ∧ (∀ (f : PowerSeries ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) (M : ℕ), Membership.mem (α := P.R.BdR) ((P.PD K).Fil M.cast) (DFunLike.coe (β := fun (x : PowerSeries ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) ↦ P.R.BdR) ev f : P.R.BdR) ↔ HPow.hPow (α := PowerSeries ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) PowerSeries.X M ∣ f) ∧ IsUnit (GlobalTheory.NL.tS P s) ∧ (∀ (a : ℤ) (b : P.R.BdR), GlobalTheory.NL.tS P s * b ∈ (P.PD K).Fil (a + OfNat.ofNat 1) ↔ b ∈ (P.PD K).Fil a) ∧ ∀ (b : P.R.BdR), (∀ (a : ℤ), b ∈ (P.PD K).Fil a) → b = OfNat.ofNat 0 := by
  intro l _ P AI T K LL s ι
  have h1 := (P.PD K).mem_filtration_one
  have h2 := (P.PD K).not_mem_filtration_two
  rw [P.PD_ι, P.period_datum_t_eq] at h1 h2
  exact Bridge.TateSpanAlt.reduction' l P AI T K LL s ι h1 h2

end

noncomputable section

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.NL.EvdR

section General

variable {L A : Type*} [Field L] [CommRing A] (c : L →+* A) (t : A)

def part (M : ℕ) (f : PowerSeries L) : A := Polynomial.eval₂RingHom c t (PowerSeries.trunc M f)

theorem dvd_part_sub (M : ℕ) (f : PowerSeries L) (q : Polynomial L)
    (h : ∀ k < M, PowerSeries.coeff k f = q.coeff k) :
    t ^ M ∣ part c t M f - Polynomial.eval₂RingHom c t q := by
  have h1 : Polynomial.X ^ M ∣ PowerSeries.trunc M f - q := by
    rw [Polynomial.X_pow_dvd_iff]
    intro k hk
    rw [Polynomial.coeff_sub, PowerSeries.coeff_trunc, if_pos hk, h k hk, sub_self]
  have h2 := map_dvd (Polynomial.eval₂RingHom c t) h1
  rw [map_sub, map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] at h2
  exact h2

theorem mem_iff (n : ℕ) (x : A) : x ∈ (Ideal.span {t} ^ n • ⊤ : Submodule A A) ↔ t ^ n ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

variable [IsAdicComplete (Ideal.span {t}) A]

theorem eq_zero_of_dvd (x : A) (h : ∀ n, t ^ n ∣ x) : x = 0 :=
  IsHausdorff.haus (I := Ideal.span {t}) inferInstance x fun n => by
    rw [SModEq.zero, mem_iff]; exact h n

theorem exists_lim (f : PowerSeries L) : ∃ x : A, ∀ M, t ^ M ∣ x - part c t M f := by
  obtain ⟨x, hx⟩ := IsPrecomplete.prec (I := Ideal.span {t}) inferInstance
    (f := fun M => part c t M f) fun {m n} h => by
      rw [SModEq.sub_mem, mem_iff]
      exact dvd_part_sub c t m f _ fun k hk => by
        rw [PowerSeries.coeff_trunc, if_pos (hk.trans_le h)]
  exact ⟨x, fun M => by rw [← mem_iff, ← SModEq.sub_mem]; exact (hx M).symm⟩

theorem exists_ev : ∃ ev : PowerSeries L →+* A, ∀ f M, t ^ M ∣ ev f - part c t M f := by
  choose e he using exists_lim c t
  have key : ∀ f x, (∀ M, t ^ M ∣ x - part c t M f) → e f = x := fun f x h => by
    refine sub_eq_zero.1 (eq_zero_of_dvd t _ fun n => ?_)
    have := dvd_sub (he f n) (h n)
    rwa [sub_sub_sub_cancel_right] at this
  refine ⟨⟨⟨⟨e, key _ _ fun M => ?_⟩, fun f g => key _ _ fun M => ?_⟩, key _ _ fun M => ?_,
    fun f g => key _ _ fun M => ?_⟩, he⟩
  · have := dvd_part_sub c t M 1 1 fun k _ => by
      rw [PowerSeries.coeff_one, Polynomial.coeff_one]
    rw [map_one] at this
    exact dvd_sub_comm.1 this
  · have h := dvd_part_sub c t M (f * g) (PowerSeries.trunc M f * PowerSeries.trunc M g) fun k hk => by
      rw [PowerSeries.coeff_mul, Polynomial.coeff_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_pos (by omega), if_pos (by omega)]
    rw [map_mul] at h
    have h' := dvd_sub (dvd_add ((he f M).mul_right (e g)) ((he g M).mul_left (part c t M f))) h
    convert h' using 1
    simp only [part]
    ring
  · simp [part]
  · have h' := dvd_add (he f M) (he g M)
    convert h' using 1
    simp only [part, map_add]
    ring

end General

theorem exists_ev_tied (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K LL : FinExt l) (s : ℕ) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) :
    ∃ ev : PowerSeries ↥LL.1 →+* P.R.BdR,
      (∀ (f : PowerSeries ↥LL.1) (M : ℕ),
        ev f - ∑ k ∈ Finset.range M, ι (PowerSeries.coeff k f) * tS P s ^ k ∈ (P.PD K).Fil (M : ℤ)) ∧
      (∀ (f : PowerSeries ↥LL.1) (M : ℕ), ev f ∈ (P.PD K).Fil (M : ℤ) ↔ PowerSeries.X ^ M ∣ f) ∧
      IsUnit (tS P s) ∧
      (∀ (a : ℤ) (b : P.R.BdR), tS P s * b ∈ (P.PD K).Fil (a + 1) ↔ b ∈ (P.PD K).Fil a) ∧
      ∀ b : P.R.BdR, (∀ a : ℤ, b ∈ (P.PD K).Fil a) → b = 0 := by
  first | exact Bridge.exists_power_series_evaluation | exact Bridge.exists_power_series_evaluation .. | (intros; apply Bridge.exists_power_series_evaluation <;> assumption)

theorem exists_ev_dR : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (s : ℕ) (ι : ↥LL.1 →ₐ[ℚ_[l]] (D.loc l).R.BdR), ∃ ev : PowerSeries ↥LL.1 →+* (D.loc l).R.BdR, (∀ (f : PowerSeries ↥LL.1) (M : ℕ), ev f - ∑ k ∈ Finset.range M, ι (PowerSeries.coeff k f) * tS (D.loc l) s ^ k ∈ ((D.loc l).PD K).Fil (M : ℤ)) ∧ (∀ (f : PowerSeries ↥LL.1) (M : ℕ), ev f ∈ ((D.loc l).PD K).Fil (M : ℤ) ↔ PowerSeries.X ^ M ∣ f) ∧ IsUnit (tS (D.loc l) s) ∧ (∀ (a : ℤ) (b : (D.loc l).R.BdR), tS (D.loc l) s * b ∈ ((D.loc l).PD K).Fil (a + 1) ↔ b ∈ ((D.loc l).PD K).Fil a) ∧ ∀ b : (D.loc l).R.BdR, (∀ a : ℤ, b ∈ ((D.loc l).PD K).Fil a) → b = 0 :=
  fun D l _ K LL s ι => exists_ev_tied l _ _ (D.locT l) K LL s ι

end GlobalTheory.NL.EvdR
