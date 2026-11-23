import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ExpRules
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationPullbackOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.KillerLevCoreOf
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExistsXPowMul
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.QpEqUnit
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.JumpsLetExists
import Formalism.SharpRestriction.LevelLetterCocycles.CardBasisEq
import Formalism.SharpRestriction.LevelLetterCocycles.UniformizerMemDeltaInvariants
import Formalism.SharpRestriction.LevelLetterCocycles.EqZeroOfPowDvd
import Formalism.SharpRestriction.LevelLetterCocycles.LemmaDN0OfAdmits

section

noncomputable section

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries
open Formalism.MainNotions.CrystallineLiftingInputs (DL pullJ)

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

abbrev Ring9 : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))

theorem letE_mul_self' (c : ZMod n) : (letE c : LetA O n) * letE c = letE c := by
  funext k
  simp only [Pi.mul_apply, letE, Pi.single_apply]
  split_ifs <;> simp

theorem cc_π₀₁ (hR : Ring9 W) : constantCoeff W.π₀₁ = 0 := by
  obtain ⟨w, hw⟩ := hR.2.2.1
  have h1 := congrFun hw 0
  change W.π₀₁ = _ at h1
  have hp : PD.p - 1 ≠ 0 := by have := PD.hp.two_le; omega
  rw [h1]
  simp [letπ, Pi.mul_apply, Pi.pow_apply, hp]

theorem hasSubst (hR : Ring9 W) : HasSubst W.π₀₁ := HasSubst.of_constantCoeff_zero (cc_π₀₁ W hR)

theorem evaluation_apply (f : PowerSeries O) (i : ZMod n) : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f i = subst W.π₀₁ f := rfl

theorem evalZero_mul (hR : Ring9 W) (f g : PowerSeries O) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (f * g) = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f * Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W g := by
  funext i
  simp only [evaluation_apply, Pi.mul_apply, subst_mul (hasSubst W hR)]

theorem evaluation_add (hR : Ring9 W) (f g : PowerSeries O) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (f + g) = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f + Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W g := by
  funext i
  simp only [evaluation_apply, Pi.add_apply, subst_add (hasSubst W hR)]

def at0H (hR : Ring9 W) : PowerSeries O →ₐ[O] LetA O n :=
  AlgHom.pi fun _ => substAlgHom (hasSubst W hR)

theorem evaluation_eq_homomorphism (hR : Ring9 W) (f : PowerSeries O) : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f = at0H W hR f := by
  funext i
  simp [at0H, evaluation_apply, coe_substAlgHom]

theorem eq_zero_of_X_pow_dvd {R : Type} [CommRing R] (d : PowerSeries R)
    (h : ∀ N : ℕ, (X : PowerSeries R) ^ N ∣ d) : d = 0 := by
  ext m
  simpa using (X_pow_dvd_iff.1 (h (m + 1))) m (Nat.lt_succ_self m)

theorem fix_subst (hR : Ring9 W) (g : PowerSeries O →ₐ[O] PowerSeries O) (hg : g W.π₀₁ = W.π₀₁)
    (f : PowerSeries O) : g (subst W.π₀₁ f) = subst W.π₀₁ f := by
  have ha := hasSubst W hR
  rw [← sub_eq_zero]
  apply eq_zero_of_X_pow_dvd
  intro N
  obtain ⟨h, hh⟩ : (X : PowerSeries O) ^ N ∣ f - (trunc N f : PowerSeries O) := by
    rw [X_pow_dvd_iff]
    intro m hm
    simp [coeff_trunc, hm]
  have hf : f = (trunc N f : PowerSeries O) + X ^ N * h := by rw [← hh]; ring
  have e1 : subst W.π₀₁ f = Polynomial.aeval W.π₀₁ (trunc N f) + W.π₀₁ ^ N * subst W.π₀₁ h := by
    conv_lhs => rw [hf]
    rw [← coe_substAlgHom ha, map_add, map_mul, map_pow, coe_substAlgHom ha, subst_coe ha, subst_X ha]
  rw [e1, map_add, map_mul, map_pow, hg, ← Polynomial.aeval_algHom_apply, hg]
  have e2 : Polynomial.aeval W.π₀₁ (trunc N f) + W.π₀₁ ^ N * g (subst W.π₀₁ h) -
      (Polynomial.aeval W.π₀₁ (trunc N f) + W.π₀₁ ^ N * subst W.π₀₁ h) =
      W.π₀₁ ^ N * (g (subst W.π₀₁ h) - subst W.π₀₁ h) := by ring
  rw [e2]
  exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (X_dvd_iff.2 (cc_π₀₁ W hR)) N) _

theorem γ₀_π₀₁ {δ : W.Gam} (hδ : δ ∈ W.DelF) : W.γ₀ δ W.π₀₁ = W.π₀₁ := by
  have h := congrFun (Formalism.MainNotions.RamifiedCoefficientChains.S9.LD.uniformizer_mem_delta_invariants W δ hδ) 0
  simpa [LocWach.γA, letγ, LocWach.π₀] using h

theorem evaluation_mem_invariants (hR : Ring9 W) (f : PowerSeries O) : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f ∈ W.AΔ := by
  intro δ hδ
  funext i
  simp only [LocWach.γA, letγ, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply, evaluation_apply]
  exact fix_subst W hR (W.γ₀ δ) (γ₀_π₀₁ W hδ) f

theorem subst_inj (hR : Ring9 W) {f f' : PowerSeries O} (h : subst W.π₀₁ f = subst W.π₀₁ f') : f = f' := by
  obtain ⟨F, -, hF⟩ := hR.2.1 (Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f) (evaluation_mem_invariants W hR f)
  have h1 := hF (fun _ => f) (fun i => rfl)
  have h2 := hF (fun _ => f') (fun i => by rw [evaluation_apply, h]; rfl)
  exact congrFun (h1.trans h2.symm) 0

theorem evaluation_letter_injective (hR : Ring9 W) {f f' : PowerSeries O} (c : ZMod n)
    (h : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f * letE c = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f' * letE c) : f = f' := by
  apply subst_inj W hR
  have := congrFun h c
  simpa [evaluation_apply, letE] using this

theorem invariant_letter_eq_evaluation (hR : Ring9 W) {a : LetA O n} (ha : a ∈ W.AΔ) (c : ZMod n) :
    ∃ f : PowerSeries O, a * letE c = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f * letE c := by
  obtain ⟨F, hF, -⟩ := hR.2.1 a ha
  refine ⟨F c, ?_⟩
  funext i
  by_cases hi : i = c
  · subst hi
    simp only [Pi.mul_apply, letE, Pi.single_eq_same, mul_one, evaluation_apply]
    exact hF i
  · simp [letE, Pi.single_apply, hi]

theorem EE_p_nzd (hO : ∀ c : O, ((PD.p : ℕ) : O) * c = 0 → c = 0) (y : W.EE)
    (hy : ((PD.p : ℕ) : W.EE) * y = 0) : y = 0 := by
  have hk : ∀ k : ℕ, ((PD.p : ℕ) : W.EE) ^ k ∣ y := by
    intro k
    obtain ⟨a, m, hm⟩ := W.EE_dense y k
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hm
    have h1 : algebraMap (LetA O n) W.EE (((PD.p : ℕ) : LetA O n) * a) ∈
        Ideal.span {((PD.p : ℕ) : W.EE) ^ (k + 1)} := by
      rw [Ideal.mem_span_singleton']
      refine ⟨-z, ?_⟩
      rw [map_mul, map_natCast]
      linear_combination (-((PD.p : ℕ) : W.EE)) * hz +
        (-(algebraMap (LetA O n) W.EE (letπ ^ m))) * hy
    obtain ⟨b, hb⟩ := W.EE_sat _ (k + 1) h1
    have hab : a = ((PD.p : ℕ) : LetA O n) ^ k * b :=
      Formalism.MainNotions.UnusedSlot80.SatW.p_cancel hO (by rw [hb]; ring)
    obtain ⟨u, hu⟩ := W.EE_π
    have e1 : y * (u : W.EE) ^ m = ((PD.p : ℕ) : W.EE) ^ k * (z + algebraMap (LetA O n) W.EE b) := by
      rw [hu]
      rw [hab] at hz
      simp only [map_mul, map_pow, map_natCast] at hz
      linear_combination (-1 : W.EE) * hz
    refine ⟨(z + algebraMap (LetA O n) W.EE b) * ((u⁻¹ : W.EEˣ) : W.EE) ^ m, ?_⟩
    calc y = y * (u : W.EE) ^ m * ((u⁻¹ : W.EEˣ) : W.EE) ^ m := by
          rw [mul_assoc, ← mul_pow, Units.mul_inv, one_pow, mul_one]
      _ = _ := by rw [e1, mul_assoc]
  apply W.EE_complete.toIsHausdorff.haus y
  intro k
  rw [SModEq.sub_mem, sub_zero]
  obtain ⟨c, hc⟩ := hk k
  rw [hc, ← smul_eq_mul]
  exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) k) trivial

theorem EE_p_pow_nzd (hO : ∀ c : O, ((PD.p : ℕ) : O) * c = 0 → c = 0) (s : ℕ) (y : W.EE)
    (hy : ((PD.p : ℕ) : W.EE) ^ s * y = 0) : y = 0 := by
  induction s generalizing y with
  | zero => simpa using hy
  | succ s ih =>
    apply EE_p_nzd W hO
    apply ih
    rw [← hy]; ring

theorem q_unit (hR : Ring9 W) : IsUnit (algebraMap (LetA O n) W.EE W.q) := by
  obtain ⟨h3, -⟩ := Formalism.MainNotions.UnusedSlot80.SatW.ring_clauses W hR
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  rw [hw, Formalism.MainNotions.UnusedSlot80.SatW.Eat_π₀]
  exact Formalism.MainNotions.UnusedSlot80.SatW.isUnit_EE_of_UPi W
    ((Formalism.MainNotions.UnusedSlot80.SatW.UPi.unit _ w).mul (Formalism.MainNotions.UnusedSlot80.SatW.UPi_π₀ W h3).add_p)

end Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT

end

section

noncomputable section

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries
open Formalism.MainNotions.CrystallineLiftingInputs (DL pullJ)

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

section SpanCopy

open Formalism.MainNotions.UnusedSlot80.PhiPowers Formalism.MainNotions.UnusedSlot80.SatW Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.UnusedSlot80.SatPW

theorem span_phi_top (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (hs : W.s = 1) {r : ℕ}
    (b : Fin r → W.DD T) (hb : ∀ j, b j ∈ W.NΔ T)
    (huniq : ∀ x ∈ W.N T, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j)
    (hq : IsUnit (algebraMap (LetA O n) W.EE W.q)) (e : ℕ) :
    Submodule.span W.EE (Set.range fun j => ((W.φD T) ^ e) (b j)) = ⊤ := by
  have hli : LinearIndependent (LetA O n) (fun j => (⟨b j, (hb j).1⟩ : W.N T)) := by
    refine Fintype.linearIndependent_iff.2 fun g hg => ?_
    have h1 : (∑ j, g j • b j) = 0 := by
      have := congrArg Subtype.val hg
      simpa using this
    obtain ⟨a0, _, hu⟩ := huniq 0 (W.N T).zero_mem
    have e1 := hu g h1.symm
    have e2 := hu 0 (by simp)
    intro i
    rw [e1, ← e2]
    rfl
  have hsp : ⊤ ≤ Submodule.span (LetA O n) (Set.range fun j => (⟨b j, (hb j).1⟩ : W.N T)) := by
    rintro ⟨x, hx⟩ _
    obtain ⟨a, ha, _⟩ := huniq x hx
    have : (⟨x, hx⟩ : W.N T) = ∑ j, a j • (⟨b j, (hb j).1⟩ : W.N T) := by
      apply Subtype.ext
      simp [ha]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let bN : Module.Basis (Fin r) (LetA O n) (W.N T) := Module.Basis.mk hli hsp
  let bD : Module.Basis (Fin r) W.EE (W.DD T) := IsBaseChange.basis bN (W.N_base T hT)
  have hbD : ∀ j, bD j = b j := fun j => by
    simp [bD, IsBaseChange.basis_apply, bN]
  have hspan : Submodule.span W.EE (Set.range b) = ⊤ := by
    rw [← bD.span_eq]
    congr 1
    ext x
    simp [hbD]
  have hφ : ∀ j, b j ∈ Submodule.span W.EE (Set.range fun i => W.φD T (b i)) := by
    intro j
    obtain ⟨k, hk⟩ := W.N_φinv T (b j) (hb j).1
    have hQ : ((letφ (n := n) W.φ₀ ^ (W.s - 1)) (fun _ => W.q₀)) = W.q := by
      rw [hs]; rfl
    rw [hQ] at hk
    have hA : Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))) ≤
        (Submodule.span W.EE (Set.range fun i => W.φD T (b i))).restrictScalars (LetA O n) := by
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨a, ha, _⟩ := huniq y hy
      rw [ha, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [φD_smulA, ← algebraMap_smul W.EE]
      rw [Submodule.restrictScalars_mem]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
    have h1 := hA hk
    obtain ⟨u, hu⟩ := hq.pow k
    have h2 : b j = ((u⁻¹ : W.EEˣ) : W.EE) • (W.q ^ k • b j) := by
      rw [← algebraMap_smul W.EE (W.q ^ k), smul_smul, map_pow, ← hu, Units.inv_mul, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  exact span_φ_pow W T b hspan hφ e

end SpanCopy

theorem coord_inj (T : LocLat G Qp LL O) {R : ℕ} (b : Fin R → W.DD T) (hb : ∀ j, b j ∈ W.N T)
    (huniq : ∀ x ∈ W.N T, ∃! a : Fin R → LetA O n, x = ∑ j, a j • b j) {g g' : Fin R → LetA O n}
    (h : ∑ j, g j • b j = ∑ j, g' j • b j) : g = g' := by
  have hx : ∑ j, g j • b j ∈ W.N T := Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hb j)
  obtain ⟨a, -, ha⟩ := huniq _ hx
  rw [ha g rfl, ha g' h]

theorem γD_φpow (T : LocLat G Qp LL O) (g : W.Gam) (j : ℕ) (x : W.DD T) :
    W.γD T g (((W.φD T) ^ j) x) = ((W.φD T) ^ j) (W.γD T g x) := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← W.φγ_comm, ih]

theorem E_phi (T : LocLat G Qp LL O) {i : ZMod n} {y : W.DD T} (hy : (letE i : LetA O n) • y = y)
    (j : ℕ) : (letE (i + (j : ZMod n)) : LetA O n) • ((W.φD T) ^ j) y = ((W.φD T) ^ j) y := by
  conv_rhs => rw [← hy, Formalism.MainNotions.UnusedSlot80.SatPW.φD_pow_smulA, Formalism.MainNotions.UnusedSlot80.SatPW.φA_pow_letE]

theorem isBas_letter (hR : Ring9 W) (T : LocLat G Qp LL O) {R : ℕ} (b : Fin R → W.DD T)
    (hb : ∀ j, b j ∈ W.NΔ T) (huniq : ∀ x ∈ W.N T, ∃! a : Fin R → LetA O n, x = ∑ j, a j • b j)
    (hΔ : ∀ x ∈ W.NΔ T, ∃ a : Fin R → LetA O n, (∀ j, a j ∈ W.AΔ) ∧ x = ∑ j, a j • b j) (i : ZMod n) :
    IsBas W T i (fun k => (letE i : LetA O n) • b k) := by
  refine ⟨fun k => ⟨(W.N T).smul_mem _ (hb k).1, ?_, fun δ hδ => ?_⟩, fun x hx hxD => ?_⟩
  · rw [smul_smul, letE_mul_self']
  · rw [Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA' W T, Formalism.MainNotions.UnusedSlot80.KL.γA_letE W, (hb k).2 δ hδ]
  · obtain ⟨α, hα, hx'⟩ := hΔ x ⟨hx, hxD.2⟩
    choose f hf using fun k => invariant_letter_eq_evaluation W hR (hα k) i
    have hex : x = ∑ k, at0 W (f k) • ((letE i : LetA O n) • b k) := by
      calc x = (letE i : LetA O n) • x := hxD.1.symm
        _ = ∑ k, (α k * letE i) • b k := by
          rw [hx', Finset.smul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [smul_smul, mul_comm]
        _ = ∑ k, at0 W (f k) • ((letE i : LetA O n) • b k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hf k, smul_smul]
    refine ⟨f, hex, fun y hy => ?_⟩
    funext k
    apply evaluation_letter_injective W hR i
    have := coord_inj W T b (fun j => (hb j).1) huniq
      (g := fun k => at0 W (y k) * letE i) (g' := fun k => at0 W (f k) * letE i)
      (by simp only [mul_smul]; rw [← hy, ← hex])
    exact congrFun this k

theorem pullJ_repr (T : LocLat G Qp LL O) {R : ℕ} (b : Fin R → W.DD T) (i : ZMod n)
    (hb' : IsBas W T i (fun k => (letE i : LetA O n) • b k)) (j : ℕ) {x : W.DD T}
    (hx : x ∈ pullJ W T i j) :
    ∃ α : Fin R → LetA O n, x = ∑ m, α m • ((W.φD T) ^ j) ((letE i : LetA O n) • b m) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨y0, ⟨hy0, hy0D⟩, rfl⟩ := hy
    obtain ⟨a, ha, -⟩ := hb'.2 y0 hy0 hy0D
    refine ⟨fun m => (W.φA ^ j) (at0 W (a m)), ?_⟩
    conv_lhs => rw [ha]
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Formalism.MainNotions.UnusedSlot80.SatPW.φD_pow_smulA]
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨α, rfl⟩ := hx
    obtain ⟨β, rfl⟩ := hy
    exact ⟨α + β, by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
  | smul a x _ hx =>
    obtain ⟨α, rfl⟩ := hx
    exact ⟨fun m => a * α m, by simp only [Finset.smul_sum, smul_smul]⟩

theorem transfer (hR : Ring9 W) (T : LocLat G Qp LL O) {R r : ℕ} (c : ZMod n) (u : Fin r → W.DD T)
    (hu : ∀ k, (letE c : LetA O n) • u k = u k) (v : Fin R → W.DD T) (β : Fin R → Fin r → LetA O n)
    (hv : ∀ m, v m = ∑ k, β m k • u k) (ψ : Fin R → Fin r → PowerSeries O)
    (hψ : ∀ m k, β m k * letE c = at0 W (ψ m k) * letE c) (f : Fin R → PowerSeries O) :
    ∑ m, at0 W (f m) • v m = ∑ k, at0 W (∑ m, f m * ψ m k) • u k := by
  have h1 : ∀ m k, β m k • u k = at0 W (ψ m k) • u k := by
    intro m k
    rw [← hu k, smul_smul, smul_smul, hψ]
  simp_rw [hv, h1, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [evaluation_eq_homomorphism W hR, map_sum, map_mul, Finset.sum_smul]

end Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT

end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries
open Formalism.MainNotions.CrystallineLiftingInputs (DL pullJ)

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem exist_bL (hR : Ring9 W) (T : LocLat G Qp LL O) {R : ℕ} (b : Fin R → W.DD T)
    (hb : ∀ m, b m ∈ W.NΔ T) (i : ZMod n) (hb' : IsBas W T i (fun k => (letE i : LetA O n) • b k))
    (j : ℕ) (hli : LinearIndependent W.EE fun m => ((W.φD T) ^ j) (b m)) {x : W.DD T}
    (hx : x ∈ pullJ W T i j) (hxD : DL W T (i + (j : ZMod n)) x) :
    ∃ f : Fin R → PowerSeries O, x = ∑ m, at0 W (f m) • ((W.φD T) ^ j) ((letE i : LetA O n) • b m) := by
  obtain ⟨α, hα⟩ := pullJ_repr W T b i hb' j hx
  have hinv : ∀ m, α m * letE (i + (j : ZMod n)) ∈ W.AΔ := by
    intro m δ hδ
    have h1 : ∑ m, α m • ((W.φD T) ^ j) ((letE i : LetA O n) • b m) =
        ∑ m, W.γA δ (α m) • ((W.φD T) ^ j) ((letE i : LetA O n) • b m) := by
      calc ∑ m, α m • ((W.φD T) ^ j) ((letE i : LetA O n) • b m) = x := hα.symm
        _ = W.γD T δ x := (hxD.2 δ hδ).symm
        _ = _ := by
          rw [hα, map_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA' W T, γD_φpow, Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA' W T,
            Formalism.MainNotions.UnusedSlot80.KL.γA_letE W, (hb m).2 δ hδ]
    have h2 := Formalism.MainNotions.UnusedSlot80.SatPW.coeff_eq W T b i j hli _ _ h1 m
    rw [map_mul, Formalism.MainNotions.UnusedSlot80.KL.γA_letE W, ← h2]
  choose f hf using fun m => invariant_letter_eq_evaluation W hR (hinv m) (i + (j : ZMod n))
  refine ⟨f, ?_⟩
  rw [hα]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hE := E_phi W T (y := (letE i : LetA O n) • b m) (by rw [smul_smul, letE_mul_self']) j
  have h3 : α m * letE (i + (j : ZMod n)) = at0 W (f m) * letE (i + (j : ZMod n)) := by
    rw [← hf m, mul_assoc, letE_mul_self']
  rw [← hE, smul_smul, smul_smul, h3]

theorem evaluation_single_sum (hR : Ring9 W) (T : LocLat G Qp LL O) {r : ℕ} (k : Fin r) (u : Fin r → W.DD T) :
    ∑ k', at0 W ((Pi.single k (1 : PowerSeries O) : Fin r → PowerSeries O) k') • u k' = u k := by
  rw [Finset.sum_eq_single k]
  · simp [evaluation_eq_homomorphism W hR]
  · intro k' _ hk'
    simp [evaluation_eq_homomorphism W hR, Pi.single_apply, hk']
  · simp

theorem pullback_coordinates (hR : Ring9 W) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (hs : W.s = 1) {R : ℕ}
    (b : Fin R → W.DD T) (hb : ∀ m, b m ∈ W.NΔ T)
    (huniq : ∀ x ∈ W.N T, ∃! a : Fin R → LetA O n, x = ∑ j, a j • b j)
    (hΔ : ∀ x ∈ W.NΔ T, ∃ a : Fin R → LetA O n, (∀ j, a j ∈ W.AΔ) ∧ x = ∑ j, a j • b j) (i : ZMod n)
    {r : ℕ} (e : Fin r → W.DD T) (he : IsBas W T i e) (j : ℕ) :
    ∀ x ∈ pullJ W T i j, DL W T (i + (j : ZMod n)) x →
      ∃! a : Fin r → PowerSeries O, x = ∑ k, at0 W (a k) • ((W.φD T) ^ j) (e k) := by
  intro x hx hxD
  have hb' := isBas_letter W hR T b hb huniq hΔ i
  have hli := Formalism.MainNotions.UnusedSlot80.SatPW.linInd_φ_pow W T hT hs b hb huniq (q_unit W hR) j
  set b' : Fin R → W.DD T := fun k => (letE i : LetA O n) • b k with hb'def
  choose C hC hCu using fun k => hb'.2 (e k) (he.1 k).1 (he.1 k).2
  choose D hD hDu using fun m => he.2 (b' m) (hb'.1 m).1 (hb'.1 m).2
  have hvD : ∀ m, ((W.φD T) ^ j) (b' m) =
      ∑ k, (W.φA ^ j) (at0 W (D m k)) • ((W.φD T) ^ j) (e k) := by
    intro m
    conv_lhs => rw [hD m]
    rw [map_sum]
    simp only [Formalism.MainNotions.UnusedSlot80.SatPW.φD_pow_smulA]
  have hvC : ∀ k, ((W.φD T) ^ j) (e k) =
      ∑ m, (W.φA ^ j) (at0 W (C k m)) • ((W.φD T) ^ j) (b' m) := by
    intro k
    conv_lhs => rw [hC k]
    rw [map_sum]
    simp only [Formalism.MainNotions.UnusedSlot80.SatPW.φD_pow_smulA]
  choose ψD hψD using fun m k => invariant_letter_eq_evaluation W hR
    (Formalism.MainNotions.UnusedSlot80.PhiPowers.φA_pow_mem_AΔ W (evaluation_mem_invariants W hR (D m k)) j) (i + (j : ZMod n))
  choose ψC hψC using fun k m => invariant_letter_eq_evaluation W hR
    (Formalism.MainNotions.UnusedSlot80.PhiPowers.φA_pow_mem_AΔ W (evaluation_mem_invariants W hR (C k m)) j) (i + (j : ZMod n))
  have huE : ∀ k, (letE (i + (j : ZMod n)) : LetA O n) • ((W.φD T) ^ j) (e k) = ((W.φD T) ^ j) (e k) :=
    fun k => E_phi W T (he.1 k).2.1 j
  have hvE : ∀ m, (letE (i + (j : ZMod n)) : LetA O n) • ((W.φD T) ^ j) (b' m) = ((W.φD T) ^ j) (b' m) :=
    fun m => E_phi W T (hb'.1 m).2.1 j

  have hstar : ∀ k k', ∑ m, C k m * D m k' = (Pi.single k (1 : PowerSeries O) : Fin r → PowerSeries O) k' := by
    intro k
    have h1 : e k = ∑ k', at0 W (∑ m, C k m * D m k') • e k' := by
      conv_lhs => rw [hC k]
      exact transfer W hR T i e (fun k => (he.1 k).2.1) b' (fun m k => at0 W (D m k)) hD D
        (fun _ _ => rfl) (C k)
    obtain ⟨a0, -, ha0⟩ := he.2 (e k) (he.1 k).1 (he.1 k).2
    have e1 := ha0 _ h1
    have e2 := ha0 (Pi.single k 1) (evaluation_single_sum W hR T k e).symm
    intro k'
    exact congrFun (e1.trans e2.symm) k'

  have hstar2 : ∀ k k', ∑ m, ψC k m * ψD m k' =
      (Pi.single k (1 : PowerSeries O) : Fin r → PowerSeries O) k' := by
    intro k k'
    apply evaluation_letter_injective W hR (i + (j : ZMod n))
    have hE2 := letE_mul_self' (O := O) (i + (j : ZMod n))
    calc at0 W (∑ m, ψC k m * ψD m k') * letE (i + (j : ZMod n))
        = ∑ m, (at0 W (ψC k m) * letE (i + (j : ZMod n))) * (at0 W (ψD m k') * letE (i + (j : ZMod n))) := by
          simp only [evaluation_eq_homomorphism W hR, map_sum, map_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun m _ => ?_
          conv_rhs => rw [show ∀ a b c : LetA O n, a * c * (b * c) = a * b * (c * c) from
            fun a b c => by ring]
          rw [hE2]
      _ = ∑ m, ((W.φA ^ j) (at0 W (C k m)) * letE (i + (j : ZMod n))) *
            ((W.φA ^ j) (at0 W (D m k')) * letE (i + (j : ZMod n))) := by
          simp_rw [hψC, hψD]
      _ = (W.φA ^ j) (at0 W (∑ m, C k m * D m k')) * letE (i + (j : ZMod n)) := by
          simp only [evaluation_eq_homomorphism W hR, map_sum, map_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun m _ => ?_
          calc _ = (W.φA ^ j) (at0H W hR (C k m)) * (W.φA ^ j) (at0H W hR (D m k')) *
                (letE (i + (j : ZMod n)) * letE (i + (j : ZMod n))) := by ring
            _ = _ := by rw [hE2]
      _ = at0 W ((Pi.single k (1 : PowerSeries O) : Fin r → PowerSeries O) k') * letE (i + (j : ZMod n)) := by
          rw [hstar k k']
          by_cases hk : k' = k
          · subst hk; simp [evaluation_eq_homomorphism W hR]
          · simp [evaluation_eq_homomorphism W hR, Pi.single_apply, hk]

  obtain ⟨f, hf⟩ := exist_bL W hR T b hb i hb' j hli hx hxD
  have hex : x = ∑ k, at0 W (∑ m, f m * ψD m k) • ((W.φD T) ^ j) (e k) := by
    rw [hf]
    exact transfer W hR T (i + (j : ZMod n)) (fun k => ((W.φD T) ^ j) (e k)) huE
      (fun m => ((W.φD T) ^ j) (b' m)) _ hvD ψD hψD f
  refine ⟨_, hex, fun a ha => ?_⟩

  have hto : ∀ g : Fin r → PowerSeries O, ∑ k, at0 W (g k) • ((W.φD T) ^ j) (e k) =
      ∑ m, at0 W (∑ k, g k * ψC k m) • ((W.φD T) ^ j) (b' m) := fun g =>
    transfer W hR T (i + (j : ZMod n)) (fun m => ((W.φD T) ^ j) (b' m)) hvE
      (fun k => ((W.φD T) ^ j) (e k)) _ hvC ψC hψC g
  have hcmp : ∀ m, ∑ k, a k * ψC k m = ∑ k, (∑ m', f m' * ψD m' k) * ψC k m := by
    intro m
    have h1 := Formalism.MainNotions.UnusedSlot80.SatPW.coeff_eq W T b i j hli
      (fun m => at0 W (∑ k, a k * ψC k m)) (fun m => at0 W (∑ k, (∑ m', f m' * ψD m' k) * ψC k m))
      (by rw [← hto, ← hto, ← ha, ← hex]) m
    exact evaluation_letter_injective W hR _ h1
  have hrec : ∀ g : Fin r → PowerSeries O, ∀ k', g k' = ∑ m, (∑ k, g k * ψC k m) * ψD m k' := by
    intro g k'
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hstar2]
    simp [Pi.single_apply]
  funext k'
  rw [hrec a k', hrec (fun k => ∑ m', f m' * ψD m' k) k']
  simp_rw [hcmp]

theorem pullback_saturated (hO : ∀ c : O, ((PD.p : ℕ) : O) * c = 0 → c = 0) (hR : Ring9 W)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (hs : W.s = 1) {R : ℕ}
    (b : Fin R → W.DD T) (hb : ∀ m, b m ∈ W.NΔ T)
    (huniq : ∀ x ∈ W.N T, ∃! a : Fin R → LetA O n, x = ∑ j, a j • b j)
    (hΔ : ∀ x ∈ W.NΔ T, ∃ a : Fin R → LetA O n, (∀ j, a j ∈ W.AΔ) ∧ x = ∑ j, a j • b j) (i : ZMod n)
    (j : ℕ) (x : W.DD T) (s : ℕ) (hx : ((PD.p : ℕ) : O) ^ s • x ∈ pullJ W T i j) :
    x ∈ pullJ W T i j := by
  have hb' := isBas_letter W hR T b hb huniq hΔ i
  have hli := Formalism.MainNotions.UnusedSlot80.SatPW.linInd_φ_pow W T hT hs b hb huniq (q_unit W hR) j
  have hsp := span_phi_top W T hT hs b hb huniq (q_unit W hR) j
  have hx' : ((PD.p : ℕ) : LetA O n) ^ s • x ∈ pullJ W T i j := by
    rwa [← map_natCast (algebraMap O (LetA O n)), ← map_pow, algebraMap_smul]
  obtain ⟨α, hα⟩ := pullJ_repr W T b i hb' j hx'
  have hxm : x ∈ Submodule.span W.EE (Set.range fun m => ((W.φD T) ^ j) (b m)) := by
    rw [hsp]; trivial
  obtain ⟨ε, hε⟩ := (Submodule.mem_span_range_iff_exists_fun W.EE).1 hxm
  have hφb' : ∀ m, ((W.φD T) ^ j) ((letE i : LetA O n) • b m) =
      (letE (i + (j : ZMod n)) : LetA O n) • ((W.φD T) ^ j) (b m) := fun m => by
    rw [Formalism.MainNotions.UnusedSlot80.SatPW.φD_pow_smulA, Formalism.MainNotions.UnusedSlot80.SatPW.φA_pow_letE]
  have hcoef : ∀ m, ((PD.p : ℕ) : W.EE) ^ s * ε m =
      algebraMap (LetA O n) W.EE (α m * letE (i + (j : ZMod n))) := by
    have e1 : ∑ m, (((PD.p : ℕ) : W.EE) ^ s * ε m) • ((W.φD T) ^ j) (b m) =
        ((PD.p : ℕ) : LetA O n) ^ s • x := by
      rw [← hε, Finset.smul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_smul, ← algebraMap_smul W.EE (((PD.p : ℕ) : LetA O n) ^ s), map_pow, map_natCast]
    have e2 : ∑ m, algebraMap (LetA O n) W.EE (α m * letE (i + (j : ZMod n))) • ((W.φD T) ^ j) (b m) =
        ((PD.p : ℕ) : LetA O n) ^ s • x := by
      rw [hα]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [algebraMap_smul, hφb', smul_smul]
    have h0 : ∑ m, (((PD.p : ℕ) : W.EE) ^ s * ε m -
        algebraMap (LetA O n) W.EE (α m * letE (i + (j : ZMod n)))) • ((W.φD T) ^ j) (b m) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [e1, e2, sub_self]
    intro m
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h0 m)
  have hβ : ∀ m, ∃ β : LetA O n, α m * letE (i + (j : ZMod n)) = ((PD.p : ℕ) : LetA O n) ^ s * β := by
    intro m
    apply W.EE_sat
    rw [← hcoef m, Ideal.mem_span_singleton']
    exact ⟨ε m, mul_comm _ _⟩
  choose β hβ using hβ
  have hεβ : ∀ m, ε m = algebraMap (LetA O n) W.EE (β m) := by
    intro m
    apply sub_eq_zero.1
    apply EE_p_pow_nzd W hO s
    rw [mul_sub, hcoef m, hβ m, map_mul, map_pow, map_natCast, sub_self]
  have hβE : ∀ m, β m * letE (i + (j : ZMod n)) = β m := by
    intro m
    apply Formalism.MainNotions.UnusedSlot80.SatW.p_pow_cancel hO s
    rw [← mul_assoc, ← hβ m, mul_assoc, letE_mul_self', hβ m]
  rw [← hε]
  refine Submodule.sum_mem _ fun m _ => ?_
  rw [hεβ m, algebraMap_smul, ← hβE m, mul_smul, ← hφb' m]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hb'.1 m, rfl⟩)

end Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem basTool_of [NeZero n] [IsDomain O] [IsFractionRing O LL] (W : LocWach PD LL O v n)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) : BasTool W := by
  have hO := Formalism.MainNotions.UnusedSlot80.SatW.p_nzd_O W (IsFractionRing.injective O LL)
  rintro ⟨hbij, hs, hp⟩ T hT i
  obtain ⟨-, -, hA⟩ := h9 T hT hs hp
  obtain ⟨hR, ⟨R, b, hb, huniq, hΔ⟩, -⟩ := hA (Formalism.MainNotions.UnusedSlot80.SatW.finrank_one_of_bij' hbij)
  have hRk : R = Module.finrank LL T.V :=
    (Formalism.MainNotions.RamifiedCoefficientChains.S9.RankN.card_basis_eq W T hT b (fun m => (hb m).1) huniq).trans
      (Formalism.MainNotions.RamifiedCoefficientChains.S9.RankN.finrank_lat T)
  subst hRk
  exact ⟨⟨_, BT.isBas_letter W hR T b hb huniq hΔ i⟩, fun r e he j =>
    ⟨BT.pullback_coordinates W hR T hT hs b hb huniq hΔ i e he j,
      fun x s hx => BT.pullback_saturated W hO hR T hT hs b hb huniq hΔ i j x s hx⟩⟩

end Formalism.MainNotions.RamifiedCoefficientChains.Sh

end

section

noncomputable section

open Classical PowerSeries

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh.DT

section Flag

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

structure FlagStep (F : ℤ → Submodule K V) (top : ℤ) (k : ℕ) where
  s : Set V
  ind : LinearIndepOn K id s
  sub : s ⊆ (F (top - k) : Set V)
  spn : (F (top - k) : Set V) ⊆ Submodule.span K s

def flagSets (F : ℤ → Submodule K V) (hF : Antitone F) (top : ℤ) (h0 : F top = ⊥) :
    (k : ℕ) → FlagStep F top k
  | 0 => ⟨∅, linearIndepOn_empty K id, Set.empty_subset _, by simp [h0]⟩
  | k + 1 =>
    let P := flagSets F hF top h0 k
    have hst : P.s ⊆ (F (top - ((k + 1 : ℕ) : ℤ)) : Set V) :=
      P.sub.trans (SetLike.coe_subset_coe.2 (hF (by push_cast; omega)))
    ⟨P.ind.extend hst, P.ind.linearIndepOn_extend hst, P.ind.extend_subset hst,
      P.ind.subset_span_extend hst⟩

theorem flagSets_zero (F : ℤ → Submodule K V) (hF : Antitone F) (top : ℤ) (h0 : F top = ⊥) :
    (flagSets F hF top h0 0).s = ∅ := rfl

theorem flagSets_succ (F : ℤ → Submodule K V) (hF : Antitone F) (top : ℤ) (h0 : F top = ⊥) (k : ℕ) :
    (flagSets F hF top h0 k).s ⊆ (flagSets F hF top h0 (k + 1)).s :=
  (flagSets F hF top h0 k).ind.subset_extend
    ((flagSets F hF top h0 k).sub.trans (SetLike.coe_subset_coe.2 (hF (by push_cast; omega))))

theorem flag_basis [FiniteDimensional K V] (F : ℤ → Submodule K V) (hF : Antitone F) (lo : ℤ) (N : ℕ)
    (hlo : F lo = ⊤) (hhi : F (lo + N) = ⊥) :
    ∃ (b : Module.Basis (Fin (Module.finrank K V)) K V) (α : Fin (Module.finrank K V) → ℤ),
      (∀ k, lo ≤ α k ∧ α k < lo + N) ∧ (∀ k, b k ∈ F (α k)) ∧
      (∀ a, ∀ y ∈ F a, ∀ k, α k < a → b.coord k y = 0) ∧
      (∀ a, ((Finset.univ.filter fun k => a ≤ α k).card : ℕ) = Module.finrank K (F a)) := by
  set top : ℤ := lo + (N : ℤ) with htop
  let S := flagSets F hF top hhi
  have hmono : ∀ j k, j ≤ k → (S j).s ⊆ (S k).s := by
    intro j k hjk
    induction k, hjk using Nat.le_induction with
    | base => exact le_rfl
    | succ k _ ih => exact ih.trans (flagSets_succ F hF top hhi k)
  have hN : top - (N : ℤ) = lo := by rw [htop]; ring
  have hind : LinearIndependent K (fun x : (S N).s => (x : V)) := (S N).ind
  have hsp : ⊤ ≤ Submodule.span K (Set.range fun x : (S N).s => (x : V)) := by
    rw [Subtype.range_coe]
    intro y _
    have : y ∈ F (top - N) := by rw [hN, hlo]; trivial
    exact (S N).spn this
  let B0 : Module.Basis (S N).s K V := Module.Basis.mk hind hsp
  haveI : Finite (S N).s := Module.Finite.finite_basis B0
  haveI : Fintype (S N).s := Fintype.ofFinite _
  have hcard : Fintype.card (S N).s = Module.finrank K V := (Module.finrank_eq_card_basis B0).symm
  let eqv : (S N).s ≃ Fin (Module.finrank K V) := Fintype.equivFinOfCardEq hcard
  let b : Module.Basis (Fin (Module.finrank K V)) K V := B0.reindex eqv
  have hbk : ∀ k, b k = ((eqv.symm k : (S N).s) : V) := fun k => by
    simp [b, B0, Module.Basis.reindex_apply, Module.Basis.mk_apply]
  have hex : ∀ k, ∃ j, ((eqv.symm k : (S N).s) : V) ∈ (S j).s := fun k => ⟨N, (eqv.symm k).2⟩
  let lev : Fin (Module.finrank K V) → ℕ := fun k => Nat.find (hex k)
  have hlev_mem : ∀ k, ((eqv.symm k : (S N).s) : V) ∈ (S (lev k)).s := fun k => Nat.find_spec (hex k)
  have hlev_le : ∀ k j, ((eqv.symm k : (S N).s) : V) ∈ (S j).s → lev k ≤ j :=
    fun k j h => Nat.find_min' (hex k) h
  have hlevN : ∀ k, lev k ≤ N := fun k => hlev_le k N (eqv.symm k).2
  have hlev1 : ∀ k, 1 ≤ lev k := by
    intro k
    by_contra h0
    have h0' : lev k = 0 := by omega
    have := hlev_mem k
    rw [h0'] at this
    exact this
  have hmem_iff : ∀ k j, ((eqv.symm k : (S N).s) : V) ∈ (S j).s ↔ lev k ≤ j := fun k j =>
    ⟨hlev_le k j, fun h => hmono _ _ h (hlev_mem k)⟩
  refine ⟨b, fun k => top - lev k, fun k => ⟨?_, ?_⟩, fun k => ?_, ?_, ?_⟩
  · have := hlevN k; dsimp only; omega
  · have := hlev1 k; dsimp only; omega
  · rw [hbk]; exact (S (lev k)).sub (hlev_mem k)
  · intro a y hy k hk
    dsimp only at hk
    by_cases hatop : top ≤ a
    · have : y = 0 := by
        have h1 : F a ≤ F top := hF hatop
        rw [hhi] at h1
        exact (Submodule.mem_bot K).1 (h1 hy)
      rw [this, map_zero]
    · have hlo' : lo < a := by have := hlevN k; omega
      set j : ℕ := (top - a).toNat with hj
      have hja : top - (j : ℤ) = a := by rw [hj]; omega
      have hyS : y ∈ Submodule.span K (S j).s := by
        have : y ∈ F (top - j) := by rw [hja]; exact hy
        exact (S j).spn this
      have hkj : ¬ lev k ≤ j := by omega
      rw [Module.Basis.coord_apply, Module.Basis.repr_reindex_apply]
      clear hy
      induction hyS using Submodule.span_induction with
      | mem g hg =>
        have hgN : g ∈ (S N).s := hmono j N (by omega) hg
        have : g = B0 ⟨g, hgN⟩ := by simp [B0, Module.Basis.mk_apply]
        rw [this, Module.Basis.repr_self, Finsupp.single_apply, if_neg]
        intro heq
        apply hkj
        rw [← hmem_iff, ← heq]
        exact hg
      | zero => simp
      | add x z _ _ hx hz => simp [hx, hz]
      | smul c x _ hx => simp [hx]
  · intro a
    by_cases halo : a ≤ lo
    · have hFa : F a = ⊤ := top_unique (hlo ▸ hF halo)
      rw [hFa, finrank_top]
      rw [Finset.filter_true_of_mem (fun k _ => by have := hlevN k; dsimp only; omega), Finset.card_univ,
        Fintype.card_fin]
    · by_cases hatop : top ≤ a
      · have hFa : F a = ⊥ := le_bot_iff.1 (hhi ▸ hF hatop)
        rw [hFa, finrank_bot]
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro k _
        have := hlev1 k; dsimp only; omega
      · set j : ℕ := (top - a).toNat with hj
        have hja : top - (j : ℤ) = a := by rw [hj]; omega
        have hjN : j ≤ N := by omega
        have hspan : F a = Submodule.span K (S j).s := by
          apply le_antisymm
          · intro y hy
            have : y ∈ F (top - j) := by rw [hja]; exact hy
            exact (S j).spn this
          · rw [Submodule.span_le]
            intro y hy
            have := (S j).sub hy
            rwa [hja] at this
        haveI : Finite (S j).s := Set.Finite.subset (Set.toFinite _) (hmono j N hjN)
        haveI : Fintype (S j).s := Fintype.ofFinite _
        rw [hspan, finrank_span_set_eq_card (S j).ind]
        have hfilt : (Finset.univ.filter fun k => a ≤ top - (lev k : ℤ)) =
            Finset.univ.filter fun k => ((eqv.symm k : (S N).s) : V) ∈ (S j).s := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmem_iff]
          omega
        rw [hfilt]
        have hinj : Function.Injective fun k : Fin (Module.finrank K V) => ((eqv.symm k : (S N).s) : V) :=
          fun k k' h => eqv.symm.injective (Subtype.ext h)
        rw [← Finset.card_image_of_injective _ hinj]
        congr 1
        ext g
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
        constructor
        · rintro ⟨k, hk, rfl⟩; exact hk
        · intro hg
          refine ⟨eqv ⟨g, hmono j N hjN hg⟩, ?_, ?_⟩ <;> simp [hg]

end Flag

section Mat

theorem det_rowpow {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type} [CommRing R] (x : R) (nn : ι → ℕ)
    (A A₀ : Matrix ι ι R) (h : ∀ a c, A a c = x ^ nn a * A₀ a c) :
    A.det = x ^ (∑ a, nn a) * A₀.det := by
  have : A = Matrix.of fun a c => x ^ nn a * A₀ a c := by ext a c; simp [h]
  rw [this, Matrix.det_mul_column, Finset.prod_pow_eq_pow_sum]

theorem order_X_pow_mul_of {L : Type} [Field L] (N : ℕ) (f : PowerSeries L) (hf : constantCoeff f ≠ 0) :
    (X ^ N * f : PowerSeries L).order = N := by
  have h0 : f.order = 0 := by
    rw [show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, PowerSeries.order_eq_nat]
    exact ⟨by rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply], fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  rw [PowerSeries.order_mul, PowerSeries.order_X_pow, h0, add_zero]

end Mat

section Ser

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

def cv (g : PowerSeries L) (y : ℤ → M) (k : ℤ) : M := ∑ᶠ j : ℕ, coeff j g • y (k - j)

def ser (κ : M →ₗ[L] L) (s₀ : ℕ) (y : ℤ → M) : PowerSeries L :=
  PowerSeries.mk fun j => κ (y ((j : ℤ) - s₀))

theorem ser_cv (κ : M →ₗ[L] L) (s₀ : ℕ) (g : PowerSeries L) (y : ℤ → M)
    (hy : ∀ k < -(s₀ : ℤ), y k = 0) : ser κ s₀ (cv g y) = g * ser κ s₀ y := by
  ext j
  rw [ser, PowerSeries.coeff_mk, cv, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (j + 1))]
  · rw [map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [map_smul, ser, PowerSeries.coeff_mk, smul_eq_mul]
    congr 3
    push_cast [hij]
    ring
  · intro i hi
    rw [Function.mem_support] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    apply hi
    rw [hy _ (by omega), smul_zero]

theorem ser_sum {ι : Type} (s : Finset ι) (κ : M →ₗ[L] L) (s₀ : ℕ) (y : ι → ℤ → M) :
    ser κ s₀ (fun k => ∑ a ∈ s, y a k) = ∑ a ∈ s, ser κ s₀ (y a) := by
  ext j
  simp [ser, map_sum]

theorem ser_shift (κ : M →ₗ[L] L) (s₀ : ℕ) (y : ℤ → M) (m : ℤ) (hm : -(s₀ : ℤ) ≤ m)
    (hv : ∀ j < m, κ (y j) = 0) :
    ser κ s₀ y = X ^ (m + s₀).toNat * PowerSeries.mk fun j => κ (y ((j : ℤ) + m)) := by
  ext j
  rw [PowerSeries.coeff_X_pow_mul', ser, PowerSeries.coeff_mk]
  split_ifs with h
  · rw [PowerSeries.coeff_mk]
    congr 2
    push_cast [h]
    omega
  · exact hv _ (by omega)

end Ser

end Formalism.MainNotions.RamifiedCoefficientChains.Sh.DT

end

section

noncomputable section

open Classical PowerSeries

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh.DT

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.CrystallineLiftingInputs (DL pullJ)

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def Yp (PD : PeriodData G Qp K₀ K B BdR) (O : Type) [CommRing O] : PowerSeries O :=
  X + ((PD.p : ℕ) : PowerSeries O)

def levA (hR : BT.Ring9 W) (i : ZMod n) (ζ : LL) : PowerSeries O →ₐ[O] PowerSeries LL :=
  (W.lev i ζ).comp (BT.at0H W hR)

theorem evaluation_X (hR : BT.Ring9 W) : BT.at0H W hR X = W.π₀ := by
  funext j
  simp [BT.at0H, coe_substAlgHom, subst_X (BT.hasSubst W hR)]
  rfl

theorem evaluation_at_uniformizer_power (hR : BT.Ring9 W) : BT.at0H W hR (Yp PD O) = Formalism.MainNotions.LiftingTheory.qp W := by
  rw [Yp, map_add, evaluation_X, map_natCast]
  rfl

theorem evaluation_uniformizer_pow (hR : BT.Ring9 W) (k : ℕ) : at0 W (Yp PD O ^ k) = Formalism.MainNotions.LiftingTheory.qp W ^ k := by
  rw [BT.evaluation_eq_homomorphism W hR, map_pow, evaluation_at_uniformizer_power]

theorem levA_Yp (hR : BT.Ring9 W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (i : ZMod n) (ζ : LL)
    (hζ : IsPrimitiveRoot ζ PD.p) :
    ∃ u : PowerSeries LL, IsUnit u ∧ levA W hR i ζ (Yp PD O) = u * X := by
  obtain ⟨⟨u, hu, he⟩, -, -⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.expRing_of W hR hA i ζ hζ
  exact ⟨u, hu, by rw [levA, AlgHom.comp_apply, evaluation_at_uniformizer_power, he]⟩

theorem yp_pow_dvd [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hinj : Function.Injective (algebraMap O LL)) (hpm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (hR : BT.Ring9 W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (i : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (g : PowerSeries O) (b : ℕ) (hg : (X : PowerSeries LL) ^ b ∣ levA W hR i ζ g) :
    ∃ h : PowerSeries O, g = Yp PD O ^ b * h := by
  obtain ⟨u, hu, hY⟩ := levA_Yp W hR hA i ζ hζ
  have hres : PowerSeries.map (IsLocalRing.residue O) (Yp PD O) = X ^ 1 := by
    rw [Yp, map_add, map_X, map_natCast, pow_one]
    have h1 : ((PD.p : ℕ) : IsLocalRing.ResidueField O) = 0 := by
      rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
      exact hpm
    have h2 : ((PD.p : ℕ) : PowerSeries (IsLocalRing.ResidueField O)) = 0 := by
      rw [← map_natCast (PowerSeries.C (R := IsLocalRing.ResidueField O)), h1, map_zero]
    rw [h2, add_zero]
  have hu0 : constantCoeff u ≠ 0 := fun h0 =>
    (PowerSeries.isUnit_iff_constantCoeff.1 hu).ne_zero h0
  have hXval : levA W hR i ζ X = PowerSeries.C (-(PD.p : LL)) + levA W hR i ζ (Yp PD O) := by
    rw [Yp, map_add, map_natCast, ← map_natCast (PowerSeries.C (R := LL)), ← add_assoc, add_comm _ (levA W hR i ζ X),
      add_assoc, ← map_add]
    simp
  refine Formalism.MainNotions.RamifiedCoefficientChains.S9.Ring.dvd_of_vanish hinj (Yp PD O) 1 hres {-(PD.p : LL)} (by simp)
    (fun _ => levA W hR i ζ) (fun _ => levA W hR i ζ (Yp PD O)) (fun c hc => ?_) (fun c _ => ?_)
    (fun c _ => ?_) (fun c _ => ?_) b g (fun c _ => hg)
  · rw [Finset.mem_singleton] at hc
    rw [hc, hXval]
  · rw [hY, map_mul, constantCoeff_X, mul_zero]
  · rw [hY, show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_mul_X,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hu0
  · rw [hY]; exact dvd_mul_left _ _

theorem Yp_ne_zero [Nontrivial O] : Yp PD O ≠ 0 := by
  intro h
  have h1 : coeff 1 (Yp PD O) = 1 := by
    rw [Yp, map_add, coeff_X, ← map_natCast (PowerSeries.C (R := O)), coeff_C]
    simp
  rw [h, map_zero] at h1
  exact zero_ne_one h1

theorem det_unit_pow [IsDomain O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hinj : Function.Injective (algebraMap O LL)) (hpm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (hR : BT.Ring9 W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (i : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (g g' : PowerSeries O) (Kx : ℕ) (hgg : g * g' = Yp PD O ^ Kx) :
    ∃ (u : PowerSeries O) (w : ℕ), IsUnit u ∧ g = u * Yp PD O ^ w ∧
      (levA W hR i ζ g).order = w := by
  obtain ⟨u, hu, hY⟩ := levA_Yp W hR hA i ζ hζ
  have hu0 : constantCoeff u ≠ 0 := fun h0 =>
    (PowerSeries.isUnit_iff_constantCoeff.1 hu).ne_zero h0
  have hlev : levA W hR i ζ g * levA W hR i ζ g' = X ^ Kx * u ^ Kx := by
    rw [← map_mul, hgg, map_pow, hY, mul_pow, mul_comm]
  have hord : (levA W hR i ζ g).order + (levA W hR i ζ g').order = Kx := by
    rw [← PowerSeries.order_mul, hlev, order_X_pow_mul_of]
    rw [map_pow]; exact pow_ne_zero _ hu0
  have hfin : (levA W hR i ζ g).order ≠ ⊤ := by
    intro h; rw [h, top_add] at hord; exact ENat.top_ne_natCast _ hord
  have hfin' : (levA W hR i ζ g').order ≠ ⊤ := by
    intro h; rw [h, add_top] at hord; exact ENat.top_ne_natCast _ hord
  set w := (levA W hR i ζ g).order.toNat with hw
  set w' := (levA W hR i ζ g').order.toNat with hw'
  have hwe : (levA W hR i ζ g).order = w := (ENat.natCast_toNat hfin).symm
  have hwe' : (levA W hR i ζ g').order = w' := (ENat.natCast_toNat hfin').symm
  have hsum : w + w' = Kx := by
    rw [hwe, hwe'] at hord; exact_mod_cast hord
  obtain ⟨h, hh⟩ := yp_pow_dvd W hinj hpm hR hA i ζ hζ g w (by rw [hw]; exact PowerSeries.X_pow_order_dvd)
  obtain ⟨h', hh'⟩ := yp_pow_dvd W hinj hpm hR hA i ζ hζ g' w' (by rw [hw']; exact PowerSeries.X_pow_order_dvd)
  have hone : h * h' = 1 := by
    have e1 : Yp PD O ^ Kx * (h * h') = Yp PD O ^ Kx * 1 := by
      calc Yp PD O ^ Kx * (h * h') = (Yp PD O ^ w * h) * (Yp PD O ^ w' * h') := by
            rw [← hsum, pow_add]; ring
        _ = g * g' := by rw [← hh, ← hh']
        _ = Yp PD O ^ Kx * 1 := by rw [hgg, mul_one]
    exact mul_left_cancel₀ (pow_ne_zero _ Yp_ne_zero) e1
  exact ⟨h, w, IsUnit.of_mul_eq_one _ hone, by rw [hh]; ring, hwe⟩

end Formalism.MainNotions.RamifiedCoefficientChains.Sh.DT

end

section

noncomputable section

open Classical PowerSeries

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh.DT

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.CrystallineLiftingInputs (DL pullJ)

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem mul_single (hR : BT.Ring9 W) (T : LocLat G Qp LL O) (i : ZMod n) {r R : ℕ}
    (u : Fin r → W.DD T) (hu : IsBas W T i u) (w : Fin R → W.DD T)
    (C : Fin r → Fin R → PowerSeries O) (hC : ∀ k, u k = ∑ m, at0 W (C k m) • w m)
    (D : Fin R → Fin r → PowerSeries O) (hD : ∀ m, w m = ∑ k, at0 W (D m k) • u k) :
    ∀ k k', ∑ m, C k m * D m k' = (Pi.single k (1 : PowerSeries O) : Fin r → PowerSeries O) k' := by
  intro k
  have h1 : u k = ∑ k', at0 W (∑ m, C k m * D m k') • u k' := by
    conv_lhs => rw [hC k]
    exact BT.transfer W hR T i u (fun k => (hu.1 k).2.1) w (fun m k => at0 W (D m k)) hD D
      (fun _ _ => rfl) (C k)
  obtain ⟨a0, -, ha0⟩ := hu.2 (u k) (hu.1 k).1 (hu.1 k).2
  have e1 := ha0 _ h1
  have e2 := ha0 (Pi.single k 1) (BT.evaluation_single_sum W hR T k u).symm
  intro k'
  exact congrFun (e1.trans e2.symm) k'

theorem isBas_card [IsDomain O] [IsFractionRing O LL] [NeZero n] (hR : BT.Ring9 W)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) {R : ℕ} (b : Fin R → W.DD T) (hb : ∀ m, b m ∈ W.NΔ T)
    (huniq : ∀ x ∈ W.N T, ∃! a : Fin R → LetA O n, x = ∑ j, a j • b j)
    (hΔ : ∀ x ∈ W.NΔ T, ∃ a : Fin R → LetA O n, (∀ j, a j ∈ W.AΔ) ∧ x = ∑ j, a j • b j) (i : ZMod n)
    {r : ℕ} (e : Fin r → W.DD T) (he : IsBas W T i e) : r = Module.finrank LL T.V := by
  have hb' := BT.isBas_letter W hR T b hb huniq hΔ i
  choose C hC using fun k => (hb'.2 (e k) (he.1 k).1 (he.1 k).2).exists
  choose D hD using fun m => (he.2 ((letE i : LetA O n) • b m) (hb'.1 m).1 (hb'.1 m).2).exists
  have h1 := mul_single W hR T i e he _ C hC D hD
  have h2 := mul_single W hR T i _ hb' e D hD C hC
  let Cm : Matrix (Fin r) (Fin R) (PowerSeries O) := Matrix.of C
  let Dm : Matrix (Fin R) (Fin r) (PowerSeries O) := Matrix.of D
  have hCD : Cm * Dm = 1 := by
    ext k k'
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Cm, Dm, Matrix.of_apply]
    rw [h1 k k', Pi.single_apply]
    by_cases hk : k' = k
    · subst hk; simp
    · simp [hk, Ne.symm hk]
  have hDC : Dm * Cm = 1 := by
    ext m m'
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Cm, Dm, Matrix.of_apply]
    rw [h2 m m', Pi.single_apply]
    by_cases hm : m' = m
    · subst hm; simp
    · simp [hm, Ne.symm hm]
  let eqv : (Fin r → PowerSeries O) ≃ₗ[PowerSeries O] (Fin R → PowerSeries O) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' Dm) (Matrix.toLin' Cm)
      (by rw [← Matrix.toLin'_mul, hDC, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, hCD, Matrix.toLin'_one])
  have hrR : r = R := by
    have := eqv.finrank_eq
    simpa using this
  rw [hrR]
  exact (Formalism.MainNotions.RamifiedCoefficientChains.S9.RankN.card_basis_eq W T hT b (fun m => (hb m).1) huniq).trans
    (Formalism.MainNotions.RamifiedCoefficientChains.S9.RankN.finrank_lat T)

theorem qp_mem_AΔ : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ :=
  W.AΔ.add_mem (Formalism.MainNotions.RamifiedCoefficientChains.S9.LD.uniformizer_mem_delta_invariants W) (W.AΔ.natCast_mem _)

theorem letE_span_phi (hR : BT.Ring9 W) (T : LocLat G Qp LL O) {R : ℕ} (b : Fin R → W.DD T)
    (hb : ∀ m, b m ∈ W.NΔ T) (huniq : ∀ x ∈ W.N T, ∃! a : Fin R → LetA O n, x = ∑ j, a j • b j)
    (hΔ : ∀ x ∈ W.NΔ T, ∃ a : Fin R → LetA O n, (∀ j, a j ∈ W.AΔ) ∧ x = ∑ j, a j • b j) (i : ZMod n)
    {y : W.DD T} (hy : y ∈ Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T)))) :
    (letE i : LetA O n) • y ∈ pullJ W T (i - 1) 1 := by
  have hb' := BT.isBas_letter W hR T b hb huniq hΔ (i - 1)
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨z0, hz0, rfl⟩ := hz
    obtain ⟨a, ha, -⟩ := huniq z0 hz0
    have e2 : ((W.φD T) ^ 1) ((letE (i - 1) : LetA O n) • z0) = (letE i : LetA O n) • W.φD T z0 := by
      rw [Formalism.MainNotions.UnusedSlot80.SatPW.φD_pow_smulA, Formalism.MainNotions.UnusedSlot80.SatPW.φA_pow_letE, pow_one,
        show i - 1 + ((1 : ℕ) : ZMod n) = i by push_cast; ring]
    have h1 : (letE i : LetA O n) • W.φD T z0 =
        ∑ j, (W.φA ^ 1) (a j) • ((W.φD T) ^ 1) ((letE (i - 1) : LetA O n) • b j) := by
      rw [← e2, ha, Finset.smul_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_comm, Formalism.MainNotions.UnusedSlot80.SatPW.φD_pow_smulA]
    rw [h1]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hb'.1 j, rfl⟩)
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [smul_add]; exact Submodule.add_mem _ hx hz
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem exists_Pinv (hR : BT.Ring9 W) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (hs : W.s = 1)
    {R : ℕ} (b : Fin R → W.DD T) (hb : ∀ m, b m ∈ W.NΔ T)
    (huniq : ∀ x ∈ W.N T, ∃! a : Fin R → LetA O n, x = ∑ j, a j • b j)
    (hΔ : ∀ x ∈ W.NΔ T, ∃ a : Fin R → LetA O n, (∀ j, a j ∈ W.AΔ) ∧ x = ∑ j, a j • b j) (i : ZMod n)
    {r : ℕ} (e e' : Fin r → W.DD T) (he : IsBas W T i e) (he' : IsBas W T (i - 1) e') (M : ℕ)
    (P : Matrix (Fin r) (Fin r) (PowerSeries O))
    (hP : ∀ k, Formalism.MainNotions.LiftingTheory.qp W ^ M • W.φD T (e' k) = ∑ m, at0 W (P m k) • e m) :
    ∃ (P' : Matrix (Fin r) (Fin r) (PowerSeries O)) (Kx : ℕ), P * P' = (Yp PD O ^ Kx) • 1 := by
  obtain ⟨U, hU⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.qp_eq_unit W hs hR
  have hQq : W.Q = W.q := by simp [LocWach.Q, hs]
  have hk : ∀ m, ∃ k : ℕ, Formalism.MainNotions.LiftingTheory.qp W ^ k • e m ∈ pullJ W T (i - 1) 1 := by
    intro m
    obtain ⟨k, hk⟩ := W.N_φinv T (e m) (he.1 m).1
    have hQ : ((letφ (n := n) W.φ₀ ^ (W.s - 1)) (fun _ => W.q₀)) = W.q := by rw [hs]; rfl
    rw [hQ] at hk
    refine ⟨k, ?_⟩
    have h2 : Formalism.MainNotions.LiftingTheory.qp W ^ k • e m ∈ Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))) := by
      rw [hU, hQq, mul_pow, mul_smul]
      exact Submodule.smul_mem _ _ hk
    have h3 := letE_span_phi W hR T b hb huniq hΔ i h2
    rwa [smul_comm, (he.1 m).2.1] at h3
  choose k hk using hk
  set K0 := Finset.univ.sup k with hK0
  have hmem : ∀ m, Formalism.MainNotions.LiftingTheory.qp W ^ K0 • e m ∈ pullJ W T (i - 1) 1 := by
    intro m
    have hle : k m ≤ K0 := Finset.le_sup (Finset.mem_univ m)
    rw [show K0 = (K0 - k m) + k m by omega, pow_add, mul_smul]
    exact Submodule.smul_mem _ _ (hk m)
  have hqΔ := qp_mem_AΔ W
  have hDL : ∀ m, DL W T (i - 1 + ((1 : ℕ) : ZMod n)) (Formalism.MainNotions.LiftingTheory.qp W ^ K0 • e m) := by
    intro m
    rw [show i - 1 + ((1 : ℕ) : ZMod n) = i by push_cast; ring]
    refine ⟨by rw [smul_comm, (he.1 m).2.1], fun δ hδ => ?_⟩
    rw [Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA' W T, map_pow, hqΔ δ hδ, (he.1 m).2.2 δ hδ]
  choose Pc hPc using fun m =>
    (BT.pullback_coordinates W hR T hT hs b hb huniq hΔ (i - 1) e' he' 1 _ (hmem m) (hDL m)).exists
  let P' : Matrix (Fin r) (Fin r) (PowerSeries O) := Matrix.of fun k' m => Pc m k'
  refine ⟨P', M + K0, Matrix.ext fun m' m => ?_⟩
  have hxN : Formalism.MainNotions.LiftingTheory.qp W ^ (M + K0) • e m ∈ W.N T := (W.N T).smul_mem _ (he.1 m).1
  have hxD : DL W T i (Formalism.MainNotions.LiftingTheory.qp W ^ (M + K0) • e m) := by
    refine ⟨by rw [smul_comm, (he.1 m).2.1], fun δ hδ => ?_⟩
    rw [Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA' W T, map_pow, hqΔ δ hδ, (he.1 m).2.2 δ hδ]
  obtain ⟨a0, -, ha0⟩ := he.2 _ hxN hxD
  have r1 : Formalism.MainNotions.LiftingTheory.qp W ^ (M + K0) • e m =
      ∑ m'', at0 W (((Yp PD O ^ (M + K0)) • (1 : Matrix (Fin r) (Fin r) (PowerSeries O))) m'' m) • e m'' := by
    rw [Finset.sum_eq_single m]
    · rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, evaluation_uniformizer_pow W hR]
    · intro m'' _ hm
      rw [Matrix.smul_apply, Matrix.one_apply_ne hm, smul_zero, BT.evaluation_eq_homomorphism W hR, map_zero, zero_smul]
    · simp
  have r2 : Formalism.MainNotions.LiftingTheory.qp W ^ (M + K0) • e m = ∑ m'', at0 W ((P * P') m'' m) • e m'' := by
    calc Formalism.MainNotions.LiftingTheory.qp W ^ (M + K0) • e m
        = Formalism.MainNotions.LiftingTheory.qp W ^ M • (Formalism.MainNotions.LiftingTheory.qp W ^ K0 • e m) := by rw [smul_smul, ← pow_add]
      _ = Formalism.MainNotions.LiftingTheory.qp W ^ M • ∑ k', at0 W (Pc m k') • ((W.φD T) ^ 1) (e' k') := by rw [← hPc m]
      _ = ∑ k', at0 W (Pc m k') • (Formalism.MainNotions.LiftingTheory.qp W ^ M • W.φD T (e' k')) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun k' _ => ?_
          rw [smul_comm, pow_one]
      _ = ∑ k', at0 W (Pc m k') • ∑ m'', at0 W (P m'' k') • e m'' := by simp_rw [hP]
      _ = ∑ m'', at0 W ((P * P') m'' m) • e m'' := by
          simp only [Matrix.mul_apply, P', Matrix.of_apply, BT.evaluation_eq_homomorphism W hR, map_sum, map_mul,
            Finset.smul_sum, smul_smul, Finset.sum_smul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun m'' _ => Finset.sum_congr rfl fun k' _ => ?_
          rw [mul_comm]
  have e1 := ha0 _ r1
  have e2 := ha0 _ r2
  exact congrFun (e2.trans e1.symm) m'

end Formalism.MainNotions.RamifiedCoefficientChains.Sh.DT

end

section

noncomputable section

open Classical PowerSeries

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh.DT

section CV

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

theorem cv_eq_sum (g : PowerSeries L) (y : ℤ → M) (m : ℤ) (hy : ∀ k < m, y k = 0) (k : ℤ) (K : ℕ)
    (hK : k - K < m) : cv g y k = ∑ j ∈ Finset.range K, coeff j g • y (k - j) := by
  unfold cv
  apply finsum_eq_sum_of_support_subset
  intro j hj
  rw [Function.mem_support] at hj
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  apply hj
  rw [hy _ (by omega), smul_zero]

theorem cv_vanish (g : PowerSeries L) (y : ℤ → M) (m : ℤ) (hy : ∀ k < m, y k = 0) :
    ∀ k < m, cv g y k = 0 := by
  intro k hk
  unfold cv
  rw [finsum_eq_zero_of_forall_eq_zero]
  intro j
  rw [hy _ (by omega), smul_zero]

theorem cv_lead (g : PowerSeries L) (y : ℤ → M) (m : ℤ) (hy : ∀ k < m, y k = 0) (e : ℕ)
    (hg : ∀ j < e, coeff j g = 0) : cv g y (m + e) = coeff e g • y m := by
  rw [cv_eq_sum g y m hy (m + e) (e + 1) (by push_cast; omega), Finset.sum_range_succ,
    Finset.sum_eq_zero (fun j hj => by rw [hg j (Finset.mem_range.mp hj), zero_smul]), zero_add]
  congr 2
  ring

theorem cv_mem (S : Submodule L M) (g : PowerSeries L) (y : ℤ → M) (m : ℤ) (hy : ∀ k < m, y k = 0)
    (hS : ∀ k, y k ∈ S) (k : ℤ) : cv g y k ∈ S := by
  rw [cv_eq_sum g y m hy k (k - m + 1).toNat (by omega)]
  exact Submodule.sum_mem _ fun j _ => S.smul_mem _ (hS _)

theorem coeff_X_pow_mul_lt (e j : ℕ) (hj : j < e) (f : PowerSeries L) : coeff j (X ^ e * f) = 0 := by
  rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

end CV

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.CrystallineLiftingInputs (DL pullJ)

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem levN_smul' (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (a : LetA O n) (x : ↥(W.N T)) :
    W.levN T i ζ (a • x) = cv (W.lev i ζ a) (W.levN T i ζ x) :=
  funext fun k => W.levN_smul T i ζ a x k

theorem levN_sum_smul (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) {r : ℕ} (a : Fin r → LetA O n)
    (x : Fin r → ↥(W.N T)) :
    W.levN T i ζ (∑ k, a k • x k) = fun j => ∑ k, cv (W.lev i ζ (a k)) (W.levN T i ζ (x k)) j := by
  rw [map_sum]
  funext j
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [levN_smul']

theorem lev_Q_pow (hs : W.s = 1) (i : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) (k : ℕ) :
    ∃ u : PowerSeries LL, W.lev i ζ (W.Q ^ k) = X ^ k * u := by
  obtain ⟨u, hu, -⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.lev_q_simple W i ζ hζ
  have hQq : W.Q = W.q := by simp [LocWach.Q, hs]
  exact ⟨u ^ k, by rw [hQq, map_pow, hu, mul_pow]⟩

theorem lead_F (hR : BT.Ring9 W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL)
    (_hζ : IsPrimitiveRoot ζ PD.p)
    (hA1 : ∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) (j : ℤ),
      W.levN T i ζ ⟨_, hk⟩ j ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i ∧ (j < k → W.levN T i ζ ⟨_, hk⟩ j = 0))
    {r : ℕ} (e' : Fin r → W.DD T) (he' : ∀ k, e' k ∈ W.N T) (M : ℕ)
    (hmem : ∀ k, Formalism.MainNotions.LiftingTheory.qp W ^ M • W.φD T (e' k) ∈ W.N T) (k : Fin r) (j : ℤ) :
    (j < M → W.levN T i ζ ⟨_, hmem k⟩ j = 0) ∧ W.levN T i ζ ⟨_, hmem k⟩ j ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i := by
  obtain ⟨U, hU⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.qp_eq_unit W hA.2.1 hR
  have hy : W.Q ^ M • W.φD T (e' k) ∈ W.N T := by
    have : W.Q ^ M • W.φD T (e' k) = ((U⁻¹ : (LetA O n)ˣ) : LetA O n) ^ M • (Formalism.MainNotions.LiftingTheory.qp W ^ M • W.φD T (e' k)) := by
      rw [hU, smul_smul, mul_pow, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
    rw [this]; exact (W.N T).smul_mem _ (hmem k)
  have heq : (⟨_, hmem k⟩ : ↥(W.N T)) = ((U : LetA O n) ^ M) • (⟨_, hy⟩ : ↥(W.N T)) := by
    apply Subtype.ext
    simp only [SetLike.val_smul]
    rw [smul_smul, ← mul_pow, hU]
  have hv := hA1 ⟨e' k, he' k⟩ M hy
  rw [heq, levN_smul']
  refine ⟨fun hj => cv_vanish _ _ M (fun j hj => (hv j).2 hj) j hj, ?_⟩
  exact cv_mem _ _ _ M (fun j hj => (hv j).2 hj) (fun j => (hv j).1) j

theorem lead_F_span (hR : BT.Ring9 W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL)
    (hζ : IsPrimitiveRoot ζ PD.p)
    (hA1 : ∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) (j : ℤ),
      W.levN T i ζ ⟨_, hk⟩ j ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i ∧ (j < k → W.levN T i ζ ⟨_, hk⟩ j = 0))
    (hA2 : Submodule.span LL {w | ∃ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T),
      w = W.levN T i ζ ⟨_, hk⟩ k} = Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i)
    {R : ℕ} (b : Fin R → W.DD T) (hb : ∀ m, b m ∈ W.NΔ T)
    (huniq : ∀ x ∈ W.N T, ∃! a : Fin R → LetA O n, x = ∑ j, a j • b j)
    (hΔ : ∀ x ∈ W.NΔ T, ∃ a : Fin R → LetA O n, (∀ j, a j ∈ W.AΔ) ∧ x = ∑ j, a j • b j)
    {r : ℕ} (e' : Fin r → W.DD T) (he' : IsBas W T (i - 1) e') (M : ℕ)
    (hmem : ∀ k, Formalism.MainNotions.LiftingTheory.qp W ^ M • W.φD T (e' k) ∈ W.N T) :
    Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i ≤ Submodule.span LL (Set.range fun k => W.levN T i ζ ⟨_, hmem k⟩ M) := by
  have hs : W.s = 1 := hA.2.1
  obtain ⟨uq, huq, hlq⟩ := levA_Yp W hR hA i ζ hζ
  have hlqp : W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W) = uq * X := by
    rw [← hlq, levA, AlgHom.comp_apply, evaluation_at_uniformizer_power]
  have huq0 : constantCoeff uq ≠ 0 := fun h0 => (PowerSeries.isUnit_iff_constantCoeff.1 huq).ne_zero h0
  have hb' := BT.isBas_letter W hR T b hb huniq hΔ (i - 1)
  rw [← hA2, Submodule.span_le]
  rintro w ⟨x, k', hk, rfl⟩
  set Sp := Submodule.span LL (Set.range fun k => W.levN T i ζ ⟨_, hmem k⟩ M) with hSp

  obtain ⟨a, ha, -⟩ := huniq x x.2
  choose Gm hGm using fun j => (he'.2 _ (hb'.1 j).1 (hb'.1 j).2).exists
  set β : Fin r → LetA O n := fun k => ∑ j, a j * at0 W (Gm j k) with hβ
  have c1 : (letE (i - 1) : LetA O n) • (x : W.DD T) = ∑ k, β k • e' k := by
    conv_lhs => rw [ha]
    rw [Finset.smul_sum]
    simp_rw [smul_comm (letE (i - 1) : LetA O n), hGm, Finset.smul_sum, smul_smul, hβ, Finset.sum_smul]
    rw [Finset.sum_comm]
  have hφl : W.φA (letE (i - 1) : LetA O n) = letE i := by
    have := Formalism.MainNotions.UnusedSlot80.SatPW.φA_pow_letE W (i - 1) 1
    rw [pow_one, show i - 1 + ((1 : ℕ) : ZMod n) = i by push_cast; ring] at this
    exact this
  have c2 : (letE i : LetA O n) • (W.Q ^ k' • W.φD T x) =
      ∑ k, (W.Q ^ k' * W.φA (β k)) • W.φD T (e' k) := by
    rw [smul_comm, ← hφl, ← Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.φD_smulA W T, c1, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.φD_smulA W T, smul_smul]
  have hYi : (letE i : LetA O n) • (W.Q ^ k' • W.φD T x) ∈ W.N T := (W.N T).smul_mem _ hk
  have hlevY : W.levN T i ζ ⟨_, hYi⟩ = W.levN T i ζ ⟨_, hk⟩ :=
    Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.levN_letE W T i ζ ⟨_, hk⟩ hYi
  have c3 : Formalism.MainNotions.LiftingTheory.qp W ^ M • (⟨_, hYi⟩ : ↥(W.N T)) =
      ∑ k, (W.Q ^ k' * W.φA (β k)) • (⟨_, hmem k⟩ : ↥(W.N T)) := by
    apply Subtype.ext
    simp only [SetLike.val_smul, Submodule.coe_sum]
    rw [c2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_comm]
  have c4 := congrArg (fun z => W.levN T i ζ z ((k' : ℤ) + M)) c3
  rw [levN_smul', hlevY, levN_sum_smul] at c4
  have hv := fun j => hA1 x k' hk j
  rw [cv_lead _ _ (k' : ℤ) (fun j hj => (hv j).2 hj) M (fun j hj => by
    rw [map_pow, hlqp, mul_pow, mul_comm]; exact coeff_X_pow_mul_lt M j hj _)] at c4
  have hcoef : coeff M (W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ M)) = constantCoeff uq ^ M := by
    rw [map_pow, hlqp, mul_pow, mul_comm, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]
  rw [hcoef] at c4
  beta_reduce at c4
  have hrhs : ∑ k, cv (W.lev i ζ (W.Q ^ k' * W.φA (β k))) (W.levN T i ζ ⟨_, hmem k⟩) ((k' : ℤ) + M) ∈ Sp := by
    refine Submodule.sum_mem _ fun k _ => ?_
    obtain ⟨u', hu'⟩ := lev_Q_pow W hs i ζ hζ k'
    rw [add_comm, cv_lead _ _ (M : ℤ) (fun j hj => (lead_F W hR hA T i ζ hζ hA1 e' (fun k => (he'.1 k).1)
      M hmem k j).1 hj) k' (fun j hj => by rw [map_mul, hu', mul_assoc]; exact coeff_X_pow_mul_lt k' j hj _)]
    exact Sp.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩)
  rw [← c4] at hrhs
  have hne : constantCoeff uq ^ M ≠ 0 := pow_ne_zero _ huq0
  have := Sp.smul_mem (constantCoeff uq ^ M)⁻¹ hrhs
  rw [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  exact this

end Formalism.MainNotions.RamifiedCoefficientChains.Sh.DT

end

section
noncomputable section

open Classical PowerSeries

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh.DT

section Gen

variable {L : Type} [Field L]

theorem constantCoeff_det {r : ℕ} (A : Matrix (Fin r) (Fin r) (PowerSeries L)) :
    constantCoeff A.det = (A.map constantCoeff).det := by
  rw [RingHom.map_det]; rfl

theorem order_of_rows {r : ℕ} (Em E0 Fm F0 Pl : Matrix (Fin r) (Fin r) (PowerSeries L)) (nE : Fin r → ℕ)
    (nF : ℕ) (hE : ∀ a c, Em a c = X ^ nE a * E0 a c) (hF : ∀ a c, Fm a c = X ^ nF * F0 a c)
    (hmul : Fm = Em * Pl) (hE0 : constantCoeff E0.det ≠ 0) (hF0 : constantCoeff F0.det ≠ 0) :
    ∃ w : ℕ, Pl.det.order = w ∧ (w : ℤ) + ∑ a, (nE a : ℤ) = r * nF := by
  have d1 := det_rowpow X (fun _ => nF) Fm F0 hF
  have d2 := det_rowpow X nE Em E0 hE
  have d3 : Fm.det = Em.det * Pl.det := by rw [hmul, Matrix.det_mul]
  rw [d1, d2] at d3
  have o1 := order_X_pow_mul_of (∑ _a : Fin r, nF) _ hF0
  have o2 := order_X_pow_mul_of (∑ a, nE a) _ hE0
  have h3 := congrArg PowerSeries.order d3
  rw [o1, PowerSeries.order_mul, o2] at h3
  have hfin : Pl.det.order ≠ ⊤ := by
    intro h; rw [h, add_top] at h3; exact ENat.top_ne_natCast _ h3.symm
  refine ⟨Pl.det.order.toNat, (ENat.natCast_toNat hfin).symm, ?_⟩
  rw [← ENat.natCast_toNat hfin] at h3
  have h4 : (∑ _a : Fin r, nF) = (∑ a, nE a) + Pl.det.order.toNat := by exact_mod_cast h3
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h4
  have h5 : ((r * nF : ℕ) : ℤ) = ((∑ a, nE a : ℕ) : ℤ) + (Pl.det.order.toNat : ℤ) := by exact_mod_cast h4
  push_cast at h5
  linarith

theorem cancel_rows {r : ℕ} (Em E0 Xm X0 Bl : Matrix (Fin r) (Fin r) (PowerSeries L)) (nE : Fin r → ℕ)
    (hE : ∀ a c, Em a c = X ^ nE a * E0 a c) (hX : ∀ a c, Xm a c = X ^ nE a * X0 a c)
    (hmul : Xm = Em * Bl) (hX0 : constantCoeff X0.det ≠ 0) : constantCoeff E0.det ≠ 0 := by
  have h0 : X0 = E0 * Bl := by
    refine Matrix.ext fun a c => ?_
    apply mul_left_cancel₀ (pow_ne_zero (nE a) (PowerSeries.X_ne_zero (R := L)))
    rw [← hX, hmul, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hE]; ring
  rw [h0, Matrix.det_mul, map_mul] at hX0
  exact left_ne_zero_of_mul hX0

end Gen

end Formalism.MainNotions.RamifiedCoefficientChains.Sh.DT

end

section

noncomputable section

open Classical PowerSeries

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh.DT

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct
open Formalism.MainNotions.CrystallineLiftingInputs (DL pullJ)

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem exponent (hR : BT.Ring9 W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL)
    (hζ : IsPrimitiveRoot ζ PD.p) (τ : K →ₐ[Qp] LL) (hιD : Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i = DdRE PD T.ρ τ)
    (hA1 : ∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) (j : ℤ),
      W.levN T i ζ ⟨_, hk⟩ j ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i ∧ (j < k → W.levN T i ζ ⟨_, hk⟩ j = 0))
    (hA2 : Submodule.span LL {w | ∃ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T),
      w = W.levN T i ζ ⟨_, hk⟩ k} = Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i)
    (h3 : ∀ (x : ↥(W.N T)) (k : ℤ), W.levN T i ζ ((letE i : LetA O n) • x) k ∈
      Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i ⊓ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-k))
    (h4 : ∀ (k : ℤ), ∀ w ∈ FildR PD T.ρ τ (-k), ∃ (x : ↥(W.N T)) (c : LL), c ≠ 0 ∧
      (∀ j < k, c • W.levN T i ζ ((letE i : LetA O n) • x) j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j + 1)) ∧
      c • W.levN T i ζ ((letE i : LetA O n) • x) k - w ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-k + 1))
    {R : ℕ} (b : Fin R → W.DD T) (hb : ∀ m, b m ∈ W.NΔ T)
    (huniq : ∀ x ∈ W.N T, ∃! a : Fin R → LetA O n, x = ∑ j, a j • b j)
    (hΔ : ∀ x ∈ W.NΔ T, ∃ a : Fin R → LetA O n, (∀ j, a j ∈ W.AΔ) ∧ x = ∑ j, a j • b j)
    {r : ℕ} (e e' : Fin r → W.DD T) (he : IsBas W T i e) (he' : IsBas W T (i - 1) e') (M : ℕ)
    (P : Matrix (Fin r) (Fin r) (PowerSeries O))
    (hP : ∀ k, Formalism.MainNotions.LiftingTheory.qp W ^ M • W.φD T (e' k) = ∑ m, at0 W (P m k) • e m)
    (bF : Module.Basis (Fin r) LL ↥(DdRE PD T.ρ τ)) (α : Fin r → ℤ) (H : ℤ) (hαH : ∀ ℓ, α ℓ < H)
    (hH : ∀ a, H ≤ a → FildR PD T.ρ τ a = ⊥)
    (hbF : ∀ ℓ, ((bF ℓ : ↥(DdRE PD T.ρ τ)) : T.V ⊗[Qp] BdR) ∈ FildR PD T.ρ τ (α ℓ))
    (hcoord : ∀ a (y : ↥(DdRE PD T.ρ τ)), (y : T.V ⊗[Qp] BdR) ∈ FildR PD T.ρ τ a → ∀ ℓ, α ℓ < a →
      bF.coord ℓ y = 0) :
    ∃ w : ℕ, (levA W hR i ζ P.det).order = w ∧ (w : ℤ) = M * r + ∑ ℓ, α ℓ := by
  classical

  choose κ hκ using fun ℓ => LinearMap.exists_extend (p := DdRE PD T.ρ τ) (bF.coord ℓ)
  have hκD : ∀ ℓ (y : ↥(DdRE PD T.ρ τ)), κ ℓ (y : T.V ⊗[Qp] BdR) = bF.coord ℓ y := fun ℓ y =>
    LinearMap.congr_fun (hκ ℓ) y
  have hFilD : ∀ a, FildR PD T.ρ τ a ≤ DdRE PD T.ρ τ := fun a => inf_le_left
  have hκv : ∀ ℓ a y, y ∈ FildR PD T.ρ τ a → α ℓ < a → κ ℓ y = 0 := by
    intro ℓ a y hy hlt
    rw [show y = ((⟨y, hFilD a hy⟩ : ↥(DdRE PD T.ρ τ)) : T.V ⊗[Qp] BdR) from rfl, hκD]
    exact hcoord a ⟨y, hFilD a hy⟩ hy ℓ hlt
  have hmemF : ∀ a y, y ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i → y ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a →
      y ∈ FildR PD T.ρ τ a := by
    intro a y hy hf
    rw [hιD] at hy
    exact Formalism.MainNotions.RamifiedCoefficientChains.S9.Hodge.mem_of_mem_filC PD T.ρ τ (FildR PD T.ρ τ a) (hFilD a) hy hf

  set En : Fin r → ℤ → T.V ⊗[Qp] BdR := fun m => W.levN T i ζ ⟨e m, (he.1 m).1⟩ with hEn
  have hEfil : ∀ m j, En m j ∈ FildR PD T.ρ τ (-j) := by
    intro m j
    have h := h3 ⟨e m, (he.1 m).1⟩ j
    have hs : (letE i : LetA O n) • (⟨e m, (he.1 m).1⟩ : ↥(W.N T)) = ⟨e m, (he.1 m).1⟩ :=
      Subtype.ext (he.1 m).2.1
    rw [hs] at h
    exact hmemF _ _ h.1 h.2
  set s₀ : ℕ := H.toNat + M with hs₀
  have hEv : ∀ m, ∀ j < -(s₀ : ℤ), En m j = 0 := by
    intro m j hj
    have := hEfil m j
    rw [hH (-j) (by omega)] at this
    exact (Submodule.mem_bot LL).1 this

  have hmem : ∀ k, Formalism.MainNotions.LiftingTheory.qp W ^ M • W.φD T (e' k) ∈ W.N T := fun k => by
    rw [hP k]
    exact Submodule.sum_mem _ fun m _ => (W.N T).smul_mem _ (he.1 m).1
  set Fn : Fin r → ℤ → T.V ⊗[Qp] BdR := fun k => W.levN T i ζ ⟨_, hmem k⟩ with hFn
  have hlevA : ∀ f, levA W hR i ζ f = W.lev i ζ (at0 W f) := fun f => by
    rw [levA, AlgHom.comp_apply, BT.evaluation_eq_homomorphism W hR]
  have hFrel : ∀ k, Fn k = fun j => ∑ m, cv (levA W hR i ζ (P m k)) (En m) j := by
    intro k
    have hsub : (⟨_, hmem k⟩ : ↥(W.N T)) = ∑ m, (at0 W (P m k)) • (⟨e m, (he.1 m).1⟩ : ↥(W.N T)) := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, SetLike.val_smul]
      exact hP k
    simp only [hFn, hEn]
    rw [hsub, levN_sum_smul]
    simp_rw [hlevA]
  have hFlead := fun k j => lead_F W hR hA T i ζ hζ hA1 e' (fun k => (he'.1 k).1) M hmem k j

  let Em : Matrix (Fin r) (Fin r) (PowerSeries LL) := Matrix.of fun ℓ m => ser (κ ℓ) s₀ (En m)
  let E0 : Matrix (Fin r) (Fin r) (PowerSeries LL) :=
    Matrix.of fun ℓ m => PowerSeries.mk fun j => κ ℓ (En m ((j : ℤ) + -α ℓ))
  have hE : ∀ ℓ m, Em ℓ m = X ^ ((-α ℓ + s₀).toNat) * E0 ℓ m := by
    intro ℓ m
    have := hαH ℓ
    exact ser_shift (κ ℓ) s₀ (En m) (-α ℓ) (by omega)
      (fun j hj => hκv ℓ (-j) _ (hEfil m j) (by omega))
  let Fm : Matrix (Fin r) (Fin r) (PowerSeries LL) := Matrix.of fun ℓ k => ser (κ ℓ) s₀ (Fn k)
  let F0 : Matrix (Fin r) (Fin r) (PowerSeries LL) :=
    Matrix.of fun ℓ k => PowerSeries.mk fun j => κ ℓ (Fn k ((j : ℤ) + M))
  have hF : ∀ ℓ k, Fm ℓ k = X ^ (((M : ℤ) + s₀).toNat) * F0 ℓ k := by
    intro ℓ k
    exact ser_shift (κ ℓ) s₀ (Fn k) M (by omega)
      (fun j hj => by rw [show Fn k j = 0 from (hFlead k j).1 hj, map_zero])
  let Pl : Matrix (Fin r) (Fin r) (PowerSeries LL) := P.map (levA W hR i ζ)
  have hmul : Fm = Em * Pl := by
    refine Matrix.ext fun ℓ k => ?_
    simp only [Fm, Em, Pl, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply]
    rw [hFrel k, ser_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [ser_cv (κ ℓ) s₀ _ _ (hEv m), mul_comm]

  have hF0 : constantCoeff F0.det ≠ 0 := by
    rw [constantCoeff_det]
    have hvD : ∀ k, Fn k M ∈ DdRE PD T.ρ τ := fun k => by rw [← hιD]; exact (hFlead k M).2
    let vv : Fin r → ↥(DdRE PD T.ρ τ) := fun k => ⟨Fn k M, hvD k⟩
    have hspan : ⊤ ≤ Submodule.span LL (Set.range vv) := by
      intro y _
      have hy : (y : T.V ⊗[Qp] BdR) ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i := by rw [hιD]; exact y.2
      have h1 := lead_F_span W hR hA T i ζ hζ hA1 hA2 b hb huniq hΔ e' he' M hmem hy
      have h2 : Set.range (fun k => W.levN T i ζ ⟨_, hmem k⟩ M) = (DdRE PD T.ρ τ).subtype '' Set.range vv := by
        rw [← Set.range_comp]; rfl
      rw [h2, ← Submodule.map_span] at h1
      obtain ⟨y', hy', hyy⟩ := h1
      rwa [← Subtype.ext hyy]
    have hli : LinearIndependent LL vv :=
      linearIndependent_of_top_le_span_of_card_eq_finrank hspan
        (by rw [Fintype.card_fin, Module.finrank_eq_card_basis bF, Fintype.card_fin])
    let Bv : Module.Basis (Fin r) LL ↥(DdRE PD T.ρ τ) := Module.Basis.mk hli hspan
    have hmat : F0.map constantCoeff = bF.toMatrix Bv := by
      refine Matrix.ext fun ℓ k => ?_
      simp only [F0, Matrix.map_apply, Matrix.of_apply, Module.Basis.toMatrix_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, Bv, Module.Basis.mk_apply]
      rw [← Module.Basis.coord_apply, ← hκD]
      simp [vv]
    rw [hmat]
    intro h0
    have := congrArg Matrix.det (Module.Basis.toMatrix_mul_toMatrix_flip bF Bv)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this

  have hE0 : constantCoeff E0.det ≠ 0 := by
    choose xs cs hcs hlow hdiag using fun ℓ => h4 (-α ℓ) (bF ℓ) (by rw [neg_neg]; exact hbF ℓ)
    have hb'i := BT.isBas_letter W hR T b hb huniq hΔ i
    choose Hc hHc using fun j => (he.2 _ (hb'i.1 j).1 (hb'i.1 j).2).exists
    choose aa haa using fun ℓ => (huniq _ (xs ℓ).2).exists
    let β : Fin r → Fin r → LetA O n := fun m ℓ => ∑ j, aa ℓ j * at0 W (Hc j m)
    set Xn : Fin r → ℤ → T.V ⊗[Qp] BdR := fun ℓ => W.levN T i ζ ((letE i : LetA O n) • xs ℓ) with hXn
    have hXrel : ∀ ℓ, Xn ℓ = fun j => ∑ m, cv (W.lev i ζ (β m ℓ)) (En m) j := by
      intro ℓ
      have hsub : (letE i : LetA O n) • xs ℓ = ∑ m, β m ℓ • (⟨e m, (he.1 m).1⟩ : ↥(W.N T)) := by
        apply Subtype.ext
        simp only [Submodule.coe_sum, SetLike.val_smul]
        rw [haa ℓ, Finset.smul_sum]
        simp_rw [smul_comm (letE i : LetA O n), hHc, Finset.smul_sum, smul_smul, β, Finset.sum_smul]
        rw [Finset.sum_comm]
      simp only [hXn]
      rw [hsub, levN_sum_smul]
    have hXfil : ∀ ℓ j, Xn ℓ j ∈ FildR PD T.ρ τ (-j) := fun ℓ j =>
      hmemF _ _ (h3 (xs ℓ) j).1 (h3 (xs ℓ) j).2
    let Xm : Matrix (Fin r) (Fin r) (PowerSeries LL) := Matrix.of fun ℓ' ℓ => ser (κ ℓ') s₀ (Xn ℓ)
    let X0 : Matrix (Fin r) (Fin r) (PowerSeries LL) :=
      Matrix.of fun ℓ' ℓ => PowerSeries.mk fun j => κ ℓ' (Xn ℓ ((j : ℤ) + -α ℓ'))
    let Bl : Matrix (Fin r) (Fin r) (PowerSeries LL) := Matrix.of fun m ℓ => W.lev i ζ (β m ℓ)
    have hX : ∀ ℓ' ℓ, Xm ℓ' ℓ = X ^ ((-α ℓ' + s₀).toNat) * X0 ℓ' ℓ := by
      intro ℓ' ℓ
      have := hαH ℓ'
      exact ser_shift (κ ℓ') s₀ (Xn ℓ) (-α ℓ') (by omega)
        (fun j hj => hκv ℓ' (-j) _ (hXfil ℓ j) (by omega))
    have hXmul : Xm = Em * Bl := by
      refine Matrix.ext fun ℓ' ℓ => ?_
      simp only [Xm, Em, Bl, Matrix.of_apply, Matrix.mul_apply]
      rw [hXrel ℓ, ser_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [ser_cv (κ ℓ') s₀ _ _ (hEv m), mul_comm]
    have hX0 : constantCoeff X0.det ≠ 0 := by
      rw [constantCoeff_det]
      set C0 := X0.map constantCoeff with hC0
      have hC0e : ∀ ℓ' ℓ, C0 ℓ' ℓ = κ ℓ' (Xn ℓ (-α ℓ')) := by
        intro ℓ' ℓ
        simp [hC0, X0, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      let M' : Matrix (Fin r) (Fin r) LL := Matrix.of fun ℓ' ℓ => cs ℓ * C0 ℓ' ℓ
      have hM'e : ∀ ℓ' ℓ, M' ℓ' ℓ = κ ℓ' (cs ℓ • Xn ℓ (-α ℓ')) := by
        intro ℓ' ℓ
        simp only [M', Matrix.of_apply, hC0e, map_smul, smul_eq_mul]
      have hBT : M'.BlockTriangular α := by
        intro ℓ' ℓ hlt
        rw [hM'e]
        have hin : cs ℓ • Xn ℓ (-α ℓ') ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i :=
          Submodule.smul_mem _ _ (h3 (xs ℓ) (-α ℓ')).1
        have hlo := hlow ℓ (-α ℓ') (by omega)
        have hf := hmemF _ _ hin hlo
        exact hκv ℓ' _ _ hf (by omega)
      have hblock : ∀ a, M'.toSquareBlock α a = 1 := by
        intro a
        refine Matrix.ext fun ⟨ℓ', h'⟩ ⟨ℓ, h⟩ => ?_
        simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
        rw [hM'e]
        have hαe : α ℓ' = α ℓ := h'.trans h.symm
        rw [hαe]
        have hin : cs ℓ • Xn ℓ (-α ℓ) - (bF ℓ : T.V ⊗[Qp] BdR) ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i := by
          refine Submodule.sub_mem _ (Submodule.smul_mem _ _ (h3 (xs ℓ) (-α ℓ)).1) ?_
          rw [hιD]; exact (bF ℓ).2
        have hf := hmemF _ _ hin (hdiag ℓ)
        have h0 := hκv ℓ' _ _ hf (by omega)
        rw [map_sub, sub_eq_zero] at h0
        rw [h0, hκD, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
          Matrix.one_apply]
        by_cases hll : ℓ = ℓ'
        · subst hll; simp
        · rw [if_neg hll, if_neg]
          intro hq
          exact hll (congrArg Subtype.val hq).symm
      have hdetM : M'.det = 1 := by
        rw [hBT.det]
        simp [hblock]
      have hdetM' : M'.det = (∏ ℓ, cs ℓ) * C0.det := Matrix.det_mul_row cs C0
      rw [hdetM'] at hdetM
      exact right_ne_zero_of_mul_eq_one hdetM
    exact cancel_rows Em E0 Xm X0 Bl _ hE hX hXmul hX0
  obtain ⟨w, hw, hwe⟩ := order_of_rows Em E0 Fm F0 Pl _ _ hE hF hmul hE0 hF0
  have hPl : Pl.det = levA W hR i ζ P.det := by
    rw [← AlgHom.coe_toRingHom, RingHom.map_det]; rfl
  refine ⟨w, hPl ▸ hw, ?_⟩
  have hn : ∀ ℓ, (((-α ℓ + s₀).toNat : ℕ) : ℤ) = -α ℓ + s₀ := fun ℓ => by
    have := hαH ℓ; omega
  have hm : ((((M : ℤ) + s₀).toNat : ℕ) : ℤ) = M + s₀ := by omega
  simp only [hn, hm, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hwe
  linarith

end Formalism.MainNotions.RamifiedCoefficientChains.Sh.DT

end

section

noncomputable section

open Classical PowerSeries

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh.DT

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

theorem sum_alpha {d : ℕ} (α : Fin d → ℤ) (lo top : ℤ) (hα : ∀ k, lo ≤ α k ∧ α k < top) (f : ℤ → ℕ)
    (hcount : ∀ a, ((Finset.univ.filter fun k => a ≤ α k).card : ℕ) = f a) :
    ∑ k, α k = ∑ a ∈ Finset.Ico lo top, a * ((f a : ℤ) - f (a + 1)) := by
  have h1 : ∑ k, α k = ∑ a ∈ Finset.Ico lo top, ∑ k ∈ Finset.univ.filter (fun k => α k = a), α k :=
    (Finset.sum_fiberwise_of_maps_to (fun k _ => Finset.mem_Ico.2 (hα k)) α).symm
  rw [h1]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_congr rfl (fun k hk => (Finset.mem_filter.1 hk).2), Finset.sum_const, nsmul_eq_mul,
    mul_comm, ← hcount a, ← hcount (a + 1)]
  congr 1
  simp only [Finset.card_filter]
  push_cast
  rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> omega

end Formalism.MainNotions.RamifiedCoefficientChains.Sh.DT

end

section

noncomputable section

open Classical PowerSeries

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem detTool_of [NeZero n] [IsDomain O] [IsFractionRing O LL] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hPt : Formalism.MainNotions.LiftingTheory.CaseA W → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
      ∃ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ i ∧ Pt i ζ τ)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (hpm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (hζ₀ : ∃ ζ : LL, IsPrimitiveRoot ζ PD.p) : DetTool W := by
  classical
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  intro hA T Mi hi hT hJ i τ hτ r e e' he he' M P hP
  have hs : W.s = 1 := hA.2.1
  obtain ⟨-, -, hA9⟩ := h9 T hT hs hA.2.2
  obtain ⟨hR, ⟨R, b, hb, huniq, hΔ⟩, -⟩ := hA9 (Formalism.MainNotions.UnusedSlot80.SatW.finrank_one_of_bij' hA.1)
  have hr : r = Module.finrank LL T.V := DT.isBas_card W hR T hT b hb huniq hΔ i e he
  obtain ⟨ζ, hζ⟩ := hζ₀
  obtain ⟨τ', hτ', hPt'⟩ := hPt hA i ζ hζ
  have hττ : τ' = τ := (Formalism.MainNotions.N.Pv.LocalLengthBound.tauOf_unique W hA.1 i τ' hτ').trans
    (Formalism.MainNotions.N.Pv.LocalLengthBound.tauOf_unique W hA.1 i τ hτ).symm
  have hPtτ : Pt i ζ τ := hττ ▸ hPt'
  obtain ⟨⟨hA1, hA2⟩, h3, h4'⟩ := (h4 T hT).2 i ζ τ hPtτ
  obtain ⟨-, hτQ⟩ := hQ hA.1 T.V T.ρ hT
  obtain ⟨hfd, hdim, -⟩ := hτQ τ
  haveI := hfd
  have hιD := Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.ιDi_eq W hA.1 hQ T hT i τ hτ
  obtain ⟨lo, hlo⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_lo PD T.ρ τ
  obtain ⟨Ht, hHt⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_hi PD T.ρ τ
  set lo' := min lo Ht with hlo'
  set Nf : ℕ := (Ht - lo').toNat with hNf
  have hlN : lo' + (Nf : ℤ) = Ht := by omega
  let F : ℤ → Submodule LL ↥(DdRE PD T.ρ τ) := fun a =>
    (FildR PD T.ρ τ a).comap (DdRE PD T.ρ τ).subtype
  have hFa : Antitone F := fun a c hac =>
    Submodule.comap_mono (Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_anti PD T.ρ τ hac)
  have hFlo : F lo' = ⊤ := by
    simp only [F]
    rw [hlo lo' (min_le_left _ _), Submodule.comap_subtype_self]
  have hFhi : F (lo' + Nf) = ⊥ := by
    simp only [F]
    rw [hlN, hHt Ht le_rfl, Submodule.comap_bot, Submodule.ker_subtype]
  obtain ⟨bF0, α0, hrange, hmemα, hcoord0, hcount⟩ := DT.flag_basis F hFa lo' Nf hFlo hFhi
  have hd : Module.finrank LL ↥(DdRE PD T.ρ τ) = r := by rw [hdim, hr]
  let eqv := finCongr hd
  let bF := bF0.reindex eqv
  let α : Fin r → ℤ := fun ℓ => α0 (eqv.symm ℓ)
  have hbF : ∀ ℓ, ((bF ℓ : ↥(DdRE PD T.ρ τ)) : T.V ⊗[Qp] BdR) ∈ FildR PD T.ρ τ (α ℓ) := by
    intro ℓ
    simp only [bF, Module.Basis.reindex_apply]
    exact hmemα (eqv.symm ℓ)
  have hcoord : ∀ a (y : ↥(DdRE PD T.ρ τ)), (y : T.V ⊗[Qp] BdR) ∈ FildR PD T.ρ τ a → ∀ ℓ, α ℓ < a →
      bF.coord ℓ y = 0 := by
    intro a y hy ℓ hlt
    simp only [bF, Module.Basis.coord_apply, Module.Basis.repr_reindex_apply]
    rw [← Module.Basis.coord_apply]
    exact hcoord0 a y hy (eqv.symm ℓ) hlt
  have hαH : ∀ ℓ, α ℓ < Ht := fun ℓ => by
    have := (hrange (eqv.symm ℓ)).2
    simp only [α]
    omega
  obtain ⟨w₀, hw₀, hw₀e⟩ := DT.exponent W hR hA T i ζ hζ τ hιD hA1 hA2 h3 h4' b hb huniq hΔ e e' he he'
    M P hP bF α Ht hαH (fun a ha => hHt a ha) hbF hcoord
  obtain ⟨P', Kx, hPP'⟩ := DT.exists_Pinv W hR T hT hs b hb huniq hΔ i e e' he he' M P hP
  have hdd : P.det * P'.det = DT.Yp PD O ^ (Kx * r) := by
    rw [← Matrix.det_mul, hPP', Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← pow_mul]
  obtain ⟨u, w, hu, hdet, hord⟩ := DT.det_unit_pow W hinj hpm hR hA i ζ hζ P.det P'.det (Kx * r) hdd
  have hww : w = w₀ := by
    have := hord.symm.trans hw₀
    exact_mod_cast this
  refine ⟨u, w, hu, hdet, ?_⟩
  rw [hww, hw₀e]
  congr 1
  have hsumα : ∑ ℓ, α ℓ = ∑ k, α0 k := by
    simp only [α]
    exact Equiv.sum_comp eqv.symm α0
  have hfin : ∀ a, (Module.finrank LL ↥(F a) : ℤ) = Module.finrank LL ↥(FildR PD T.ρ τ a) := by
    intro a
    exact_mod_cast (Submodule.comapSubtypeEquivOfLe
      (inf_le_left : FildR PD T.ρ τ a ≤ DdRE PD T.ρ τ)).finrank_eq
  have hcnt := DT.sum_alpha α0 lo' Ht (fun k => ⟨(hrange k).1, by have := (hrange k).2; omega⟩)
    (fun a => Module.finrank LL ↥(F a)) hcount
  rw [hsumα, hcnt]
  have hmult : ∀ a, ((Module.finrank LL ↥(F a) : ℤ) - Module.finrank LL ↥(F (a + 1))) =
      multV PD T.ρ τ a := by
    intro a; rw [hfin, hfin]; rfl
  simp_rw [hmult]
  have hz1 : ∀ a, a ∉ Finset.Ico lo' Ht → multV PD T.ρ τ a = 0 := by
    intro a ha
    rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at ha
    unfold multV
    rcases ha with ha | ha
    · rw [hlo a (by omega), hlo (a + 1) (by omega), sub_self]
    · rw [hHt a ha, hHt (a + 1) (by omega), sub_self]
  have hz2 : ∀ a, a ∉ Finset.Icc (-(Mi i : ℤ)) (hi i : ℤ) → multV PD T.ρ τ a = 0 := by
    intro a ha
    apply Formalism.MainNotions.N.Pv.LocalLengthBound.rk_multV_of_not_jump
    intro hj
    exact ha (Finset.mem_Icc.2 (Set.mem_Icc.1 (hJ i τ hτ a hj)))
  have e1 : ∑ a ∈ Finset.Ico lo' Ht, a * multV PD T.ρ τ a =
      ∑ a ∈ Finset.Ico lo' Ht ∪ Finset.Icc (-(Mi i : ℤ)) (hi i : ℤ), a * multV PD T.ρ τ a :=
    Finset.sum_subset Finset.subset_union_left (fun a _ ha => by rw [hz1 a ha, mul_zero])
  have e2 : ∑ a ∈ Finset.Icc (-(Mi i : ℤ)) (hi i : ℤ), a * multV PD T.ρ τ a =
      ∑ a ∈ Finset.Ico lo' Ht ∪ Finset.Icc (-(Mi i : ℤ)) (hi i : ℤ), a * multV PD T.ρ τ a :=
    Finset.sum_subset Finset.subset_union_right (fun a _ ha => by rw [hz2 a ha, mul_zero])
  rw [e1, e2]

end Formalism.MainNotions.RamifiedCoefficientChains.Sh

end
