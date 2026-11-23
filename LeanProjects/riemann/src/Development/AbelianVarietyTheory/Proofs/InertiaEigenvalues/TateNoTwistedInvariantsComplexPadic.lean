import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFilGradedSymbolToTateTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaDeRhamFilZeroConcretePeriod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfTateTwistInvariantFiniteExtension
import Formalism.SharpRestriction.LevelLetterCocycles.NormOfVOne
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.TateChiQ
open GlobalTheory.MemLoc
open GlobalTheory.MemLoc.TateTwist (Fz Vz bound decomp Vz_stable le_natDegree pow_mem_Fz σC_algebraMap)
variable {l : ℕ} [Fact l.Prime]

theorem zeta_pow (ζ : ℕ → Om l) (χ : GQ l →* ℤ_[l]ˣ) (cZ0 : ζ 0 = 1) (cZs : ∀ m, ζ (m + 1) ^ l = ζ m) (cZ1 : ζ 1 ≠ 1)
    (cχ : ∀ (g : GQ l) (m : ℕ) (x : Om l), x ^ (l ^ m) = 1 → g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val) (n m : ℕ) : ζ (n + m) ^ l ^ m = ζ n := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', pow_mul, ← add_assoc, cZs, ih]

theorem zeta_prim (ζ : ℕ → Om l) (χ : GQ l →* ℤ_[l]ˣ) (cZ0 : ζ 0 = 1) (cZs : ∀ m, ζ (m + 1) ^ l = ζ m) (cZ1 : ζ 1 ≠ 1)
    (cχ : ∀ (g : GQ l) (m : ℕ) (x : Om l), x ^ (l ^ m) = 1 → g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val) (n : ℕ) : IsPrimitiveRoot (ζ n) (l ^ n) := by
  cases n with
  | zero => simp [cZ0]
  | succ n =>
    have h := orderOf_eq_prime_pow (x := ζ (n + 1)) (p := l) (n := n)
      (by rw [add_comm n 1, zeta_pow ζ χ cZ0 cZs cZ1 cχ]; exact cZ1)
      (by have := zeta_pow ζ χ cZ0 cZs cZ1 cχ 0 (n + 1); rwa [zero_add, cZ0] at this)
    rw [← h]
    exact IsPrimitiveRoot.orderOf _

theorem Fz_mono (ζ : ℕ → Om l) (χ : GQ l →* ℤ_[l]ˣ) (cZ0 : ζ 0 = 1) (cZs : ∀ m, ζ (m + 1) ^ l = ζ m) (cZ1 : ζ 1 ≠ 1)
    (cχ : ∀ (g : GQ l) (m : ℕ) (x : Om l), x ^ (l ^ m) = 1 → g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val) : Monotone fun n => Fz (ζ n) := by
  intro a b hab
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [IntermediateField.adjoin_simple_le_iff, ← zeta_pow ζ χ cZ0 cZs cZ1 cχ a m]
  exact pow_mem_Fz _ _

theorem chi_eq_one (ζ : ℕ → Om l) (χ : GQ l →* ℤ_[l]ˣ) (cZ0 : ζ 0 = 1) (cZs : ∀ m, ζ (m + 1) ^ l = ζ m) (cZ1 : ζ 1 ≠ 1)
    (cχ : ∀ (g : GQ l) (m : ℕ) (x : Om l), x ^ (l ^ m) = 1 → g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val) (g : GQ l) (hg : g ∈ (⨆ n, Fz (ζ n)).fixingSubgroup) : χ g = 1 := by
  ext
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  have : NeZero (l ^ n) := ⟨(pow_pos (Fact.out : l.Prime).pos _).ne'⟩
  have h1 := cχ g n _ (zeta_prim ζ χ cZ0 cZs cZ1 cχ n).pow_eq_one
  have h2 : g (ζ n) = ζ n := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _
    ((le_iSup (fun n => Fz (ζ n)) n) (IntermediateField.mem_adjoin_simple_self _ _))
  rw [h2] at h1
  have h3 : (PadicInt.toZModPow n (χ g : ℤ_[l])).val ≡ 1 [MOD l ^ n] := by
    have h5 := (isOfFinOrder_iff_pow_eq_one.2 ⟨_, NeZero.pos (l ^ n), (zeta_prim ζ χ cZ0 cZs cZ1 cχ n).pow_eq_one⟩).pow_eq_pow_iff_modEq.1
      (h1.symm.trans (pow_one _).symm)
    rwa [← (zeta_prim ζ χ cZ0 cZs cZ1 cχ n).eq_orderOf] at h5
  have h4 := (ZMod.natCast_eq_natCast_iff _ _ _).2 h3
  simpa using h4

theorem exists_gamma (ζ : ℕ → Om l) (χ : GQ l →* ℤ_[l]ˣ) (cZ0 : ζ 0 = 1) (cZs : ∀ m, ζ (m + 1) ^ l = ζ m) (cZ1 : ζ 1 ≠ 1)
    (cχ : ∀ (g : GQ l) (m : ℕ) (x : Om l), x ^ (l ^ m) = 1 → g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val) (n : ℕ) (hn : 1 ≤ n) (j : ℕ) (hj : j ≠ 0) :
    ∃ g ∈ (Fz (ζ n)).fixingSubgroup, (χ g : ℤ_[l]) ^ j ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have h1 := le_natDegree n j _ hn (zeta_prim ζ χ cZ0 cZs cZ1 cχ (n + j))
  rw [zeta_pow ζ χ cZ0 cZs cZ1 cχ] at h1
  set z := ζ (n + j) with hz
  set F := Fz (ζ n)
  have hint : IsIntegral F z := Algebra.IsIntegral.isIntegral z
  have hsep : (minpoly F z).Separable := (minpoly.irreducible hint).separable
  rw [← Polynomial.card_rootSet_eq_natDegree (K := Om l) hsep (IsAlgClosed.splits _)] at h1
  have h2 : (minpoly F z).rootSet (Om l) ⊆
      ((Polynomial.nthRoots j (1 : ℤ_[l])).toFinset.image
        fun t => z ^ (PadicInt.toZModPow (n + j) t).val : Finset (Om l)) := by
    intro r hr
    obtain ⟨s, hs⟩ := minpoly.exists_algEquiv_of_root' hint.isAlgebraic (Polynomial.aeval_eq_zero_of_mem_rootSet hr)
    have hg : s.restrictScalars ℚ_[l] ∈ F.fixingSubgroup :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => s.commutes ⟨x, hx⟩
    rw [Finset.coe_image]
    refine ⟨χ (s.restrictScalars ℚ_[l]), ?_, ?_⟩
    · simpa [Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hj)] using hcon _ hg
    · exact (cχ _ _ _ (zeta_prim ζ χ cZ0 cZs cZ1 cχ (n + j)).pow_eq_one).symm.trans hs
  have h3 := Set.ncard_le_ncard h2 (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at h3
  have h4 := h1.trans (h3.trans (Finset.card_image_le.trans
    ((Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _))))
  exact absurd h4 (not_le.2 (Nat.lt_pow_self (Fact.out : l.Prime).one_lt))

theorem estimate (ζ : ℕ → Om l) (χ : GQ l →* ℤ_[l]ˣ) (cZ0 : ζ 0 = 1) (cZs : ∀ m, ζ (m + 1) ^ l = ζ m) (cZ1 : ζ 1 ≠ 1)
    (cχ : ∀ (g : GQ l) (m : ℕ) (x : Om l), x ^ (l ^ m) = 1 → g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val) (n : ℕ) (hn : 1 ≤ n) (g : GQ l) (hg : g ∈ (Fz (ζ n)).fixingSubgroup)
    (c : ℚ_[l]) (y₀ y : Om l) (h₀ : y₀ ∈ Fz (ζ n)) (hy : y ∈ ⨆ k, Fz (ζ k)) :
    ∃ b : Om l, ‖(l : Om l)‖ * ‖b - y₀‖ ≤ ‖y - y₀‖ ∧
      ‖(l : Om l)‖ * (‖c - 1‖ * ‖b‖) ≤ ‖g y * algebraMap _ _ c - y‖ := by
  have hy' : y ∈ ((⨆ k, Fz (ζ k) : IntermediateField _ _) : Set (Om l)) := hy
  rw [IntermediateField.coe_iSup_of_directed (Fz_mono ζ χ cZ0 cZs cZ1 cχ).directed_le, Set.mem_iUnion] at hy'
  obtain ⟨m, hm⟩ := hy'
  have hm' : y ∈ Fz (ζ (n + m)) := Fz_mono ζ χ cZ0 cZs cZ1 cχ (Nat.le_add_left m n) hm
  rw [← zeta_pow ζ χ cZ0 cZs cZ1 cχ n m] at hg h₀
  obtain ⟨b, hb, w, hw, rfl⟩ := decomp _ (l ^ m) y hm'
  have hz := zeta_prim ζ χ cZ0 cZs cZ1 cχ (n + m)
  refine ⟨b, ?_, ?_⟩
  · have := bound n m _ hn hz (b - y₀) w (sub_mem hb h₀) hw
    rwa [sub_add_eq_add_sub] at this
  · have hc : ∀ d : ℚ_[l], algebraMap _ (Om l) d ∈ Fz (ζ (n + m) ^ l ^ m) := fun d =>
      IntermediateField.algebraMap_mem _ d
    have := bound n m _ hn hz (algebraMap _ _ (c - 1) * b) (algebraMap _ _ c * g w - w)
      (mul_mem (hc _) hb) (sub_mem ((Vz _ _).smul_mem ⟨_, hc c⟩ (Vz_stable n m _ hz g hg w hw)) hw)
    rw [norm_mul, norm_algebraMap'] at this
    convert this using 2
    rw [map_add, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg b hb, map_sub, map_one]
    ring

theorem full (ζ : ℕ → Om l) (χ : GQ l →* ℤ_[l]ˣ) (cZ0 : ζ 0 = 1) (cZs : ∀ m, ζ (m + 1) ^ l = ζ m) (cZ1 : ζ 1 ≠ 1)
    (cχ : ∀ (g : GQ l) (m : ℕ) (x : Om l), x ^ (l ^ m) = 1 → g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val) (i : ℤ) (x : ℂ_[l]) (hi : i ≠ 0)
    (hx : ∀ g : GQ l, Per.σC g x * (algebraMap ℚ_[l] ℂ_[l] ((χ g : ℤ_[l]) : ℚ_[l])) ^ i = x) : x = 0 := by
  have hcl := GlobalTheory.MemLoc.ax_sen_tate l (⨆ k, Fz (ζ k)).fixingSubgroup x fun g hg => by
    simpa [chi_eq_one ζ χ cZ0 cZs cZ1 cχ g hg] using hx g
  have happ : ∀ ε > 0, ∃ y ∈ ⨆ k, Fz (ζ k), ‖x - (y : ℂ_[l])‖ < ε := by
    intro ε hε
    obtain ⟨_, ⟨y, hy, rfl⟩, h⟩ := Metric.mem_closure_iff.1 hcl ε hε
    refine ⟨y, ?_, by rwa [dist_eq_norm] at h⟩
    rw [← InfiniteGalois.fixedField_fixingSubgroup (⨆ k, Fz (ζ k))]
    exact (IntermediateField.mem_fixedField_iff _ _).2 hy
  have hl : 0 < ‖(l : Om l)‖ := norm_pos_iff.2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  set L := ‖(l : Om l)‖
  have key : ∀ ε > 0, L * ‖x‖ ≤ (L + 3) * ε := by
    intro ε hε
    obtain ⟨y₀, hy₀, hxy₀⟩ := happ ε hε
    have hy' : y₀ ∈ ((⨆ k, Fz (ζ k) : IntermediateField _ _) : Set (Om l)) := hy₀
    rw [IntermediateField.coe_iSup_of_directed (Fz_mono ζ χ cZ0 cZs cZ1 cχ).directed_le, Set.mem_iUnion] at hy'
    obtain ⟨m, hm⟩ := hy'
    have hm' : y₀ ∈ Fz (ζ (m + 1)) := Fz_mono ζ χ cZ0 cZs cZ1 cχ (Nat.le_succ m) hm
    obtain ⟨g, hg, hgc⟩ := exists_gamma ζ χ cZ0 cZs cZ1 cχ (m + 1) (Nat.le_add_left 1 m) i.natAbs (Int.natAbs_ne_zero.2 hi)
    set c : ℚ_[l] := ((χ g : ℤ_[l]) : ℚ_[l]) ^ i with hc
    have hc1 : c ≠ 1 := by
      intro h
      apply hgc
      apply Subtype.ext
      have : ((χ g : ℤ_[l]) : ℚ_[l]) ^ i.natAbs = 1 := by
        rw [← zpow_natCast]
        rcases Int.natAbs_eq_iff.1 (rfl : i.natAbs = _) with h' | h'
        · rw [← h', ← hc, h]
        · rw [← neg_eq_iff_eq_neg] at h'
          rw [← h', zpow_neg, ← hc, h, inv_one]
      simpa using this
    have hcn : ‖c‖ = 1 := by
      rw [hc, norm_zpow, PadicInt.padic_norm_e_of_padicInt, PadicInt.norm_units, one_zpow]
    have hd : 0 < ‖c - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hc1)
    obtain ⟨y, hy, hxy⟩ := happ (min ε (‖c - 1‖ * ε / 2)) (lt_min hε (by positivity))
    obtain ⟨b, hb1, hb2⟩ := estimate ζ χ cZ0 cZs cZ1 cχ (m + 1) (Nat.le_add_left 1 m) g hg c y₀ y hm' hy
    have hca : ((algebraMap ℚ_[l] (Om l) c : Om l) : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] c := rfl
    have hcC : ‖algebraMap ℚ_[l] ℂ_[l] c‖ = 1 := by
      rw [← hca, PadicComplex.norm_extends, norm_algebraMap', hcn]
    have e1 : ‖y - y₀‖ ≤ 2 * ε := by
      rw [← PadicComplex.norm_extends, UniformSpace.Completion.coe_sub]
      have := norm_sub_le (x - (y₀ : ℂ_[l])) (x - (y : ℂ_[l]))
      rw [sub_sub_sub_cancel_left] at this
      linarith [min_le_left ε (‖c - 1‖ * ε / 2)]
    have e2 : ‖g y * algebraMap _ _ c - y‖ ≤ ‖c - 1‖ * ε := by
      rw [← PadicComplex.norm_extends, UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_mul,
        hca, ← GlobalTheory.RingBasics.σC_coe]
      have hxg := hx g
      rw [← map_zpow₀, ← hc] at hxg
      have := norm_sub_le (x - (y : ℂ_[l])) (Per.σC g (x - (y : ℂ_[l])) * algebraMap ℚ_[l] ℂ_[l] c)
      rw [norm_mul, GlobalTheory.RingBasics.norm_σC, hcC, map_sub, sub_mul, hxg, sub_sub_sub_cancel_left] at this
      linarith [min_le_right ε (‖c - 1‖ * ε / 2)]
    have e3 : L * ‖b‖ ≤ ε := by
      have : ‖c - 1‖ * (L * ‖b‖) ≤ ‖c - 1‖ * ε := by linarith
      exact le_of_mul_le_mul_left this hd
    have e4 : ‖y₀‖ ≤ ‖b‖ + ‖b - y₀‖ := by
      have := norm_sub_le b (b - y₀)
      rwa [sub_sub_cancel] at this
    have e5 : ‖x‖ ≤ ε + ‖y₀‖ := by
      have := norm_add_le (x - (y₀ : ℂ_[l])) (y₀ : ℂ_[l])
      rw [sub_add_cancel, PadicComplex.norm_extends] at this
      linarith
    nlinarith [mul_le_mul_of_nonneg_left e4 hl.le, mul_le_mul_of_nonneg_left e5 hl.le]
  have : L * ‖x‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := key (ε / (L + 3)) (by positivity)
    rwa [mul_div_cancel₀ _ (by positivity), ← zero_add ε] at this
  exact norm_le_zero_iff.1 (by by_contra h; nlinarith [mul_pos hl (not_le.1 h)])

def chiZ (P : LocPrime l) : GQ l →* ℤ_[l]ˣ where
  toFun g := PadicInt.mkUnits (Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators.chiQ_norm P g)
  map_one' := Units.ext (Subtype.ext (by simp [PadicInt.mkUnits]))
  map_mul' g h := Units.ext (Subtype.ext (by simp [PadicInt.mkUnits, PadicInt.coe_mul]; rfl))

theorem chiZ_coe (P : LocPrime l) (g : GQ l) :
    (((chiZ P g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) := by
  simp [chiZ, PadicInt.mkUnits]

theorem chiZ_cyc (P : LocPrime l) (g : GQ l) (m : ℕ) (x : Om l) (hx : x ^ (l ^ m) = 1) :
    g x = x ^ (PadicInt.toZModPow m (chiZ P g : ℤ_[l])).val := by
  obtain ⟨a, ha, hga⟩ := P.χQ_cyc g m x hx
  have h1 : ‖(chiZ P g : ℤ_[l]) - (a : ℤ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    rw [PadicInt.norm_def, PadicInt.coe_sub, chiZ_coe, PadicInt.coe_natCast]
    exact ha
  have h2 := (PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 h1
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero, map_natCast] at h2
  rw [h2, ZMod.val_natCast, hga, ← pow_eq_pow_mod a hx]

theorem twist_fin (ζ : ℕ → Om l) (χ : GQ l →* ℤ_[l]ˣ) (cZ0 : ζ 0 = 1) (cZs : ∀ m, ζ (m + 1) ^ l = ζ m) (cZ1 : ζ 1 ≠ 1)
    (cχ : ∀ (g : GQ l) (m : ℕ) (x : Om l), x ^ (l ^ m) = 1 → g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val) :
    ∀ (K : FinExt l) (i : ℤ) (x : ℂ_[l]), i ≠ 0 → (∀ g ∈ GK K, Per.σC g x * (algebraMap ℚ_[l] ℂ_[l] ((χ g : ℤ_[l]) : ℚ_[l])) ^ i = x) → x = 0 := by
  intro K i x hi hx
  have hK := K.2
  have hidx : (GK K).index ≠ 0 := by
    rw [GK, ← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  have hfin : Fintype (GQ l ⧸ GK K) := Subgroup.fintypeOfIndexNeZero hidx
  set a : GQ l → ℂ_[l] := fun g => (algebraMap ℚ_[l] ℂ_[l] ((χ g : ℤ_[l]) : ℚ_[l])) ^ i with ha
  have amul : ∀ g h, a (g * h) = a g * a h := fun g h => by
    simp only [ha, map_mul, Units.val_mul, PadicInt.coe_mul, mul_zpow]
  have afix : ∀ g h, Per.σC g (a h) = a h := fun g h => by
    simp only [ha, map_zpow₀, σC_algebraMap]
  have ane : ∀ g, a g ≠ 0 := fun g => by
    have h1 : a 1 = 1 := by simp [ha]
    have := amul g g⁻¹
    rw [mul_inv_cancel, h1] at this
    exact left_ne_zero_of_mul_eq_one this.symm
  set f : GQ l → ℂ_[l] := fun g => Per.σC g x * a g with hf
  have fmul : ∀ g h, f (g * h) = Per.σC g (f h) * a g := fun g h => by
    simp only [hf, GlobalTheory.RingBasics.σC_mul, amul, map_mul, afix]
    ring
  have fout : ∀ g : GQ l, f (g : GQ l ⧸ GK K).out = f g := fun g => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (GK K) g
    rw [hh, fmul]
    exact congrArg (fun t => Per.σC g t * a g) (hx h h.2)
  have hprod := full ζ χ cZ0 cZs cZ1 cχ (i * Fintype.card (GQ l ⧸ GK K)) (∏ q : GQ l ⧸ GK K, f q.out)
    (mul_ne_zero hi (by exact_mod_cast Fintype.card_ne_zero)) fun g => by
      rw [zpow_mul, zpow_natCast, map_prod, ← Finset.card_univ, ← Finset.prod_const,
        ← Finset.prod_mul_distrib, ← Equiv.prod_comp (MulAction.toPerm g) fun q : GQ l ⧸ GK K => f q.out]
      refine Finset.prod_congr rfl fun q _ => ?_
      have e : MulAction.toPerm g q = ((g * q.out : GQ l) : GQ l ⧸ GK K) := by
        rw [MulAction.toPerm_apply, ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
      rw [e, fout, fmul]
  obtain ⟨q, -, hq⟩ := Finset.prod_eq_zero_iff.1 hprod
  exact (map_eq_zero _).1 ((mul_eq_zero.1 hq).resolve_right (ane _))

end GlobalTheory.TateChiQ

namespace GlobalTheory.TateChiQ
open GlobalTheory.MemLoc.TateTwist (σC_algebraMap)

theorem tate_chiQ : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (m : ℤ), m ≠ 0 → ∀ x : ℂ_[l], (∀ g : ↥(GK K), Per.σC (g : GQ l) x = ((((P.χQ (g : GQ l)) ^ m : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * x) → x = 0 := by
  intro l _ P AI _ K m hm x hx
  refine twist_fin P.ζQ (chiZ P) P.ζQ_zero P.ζQ_succ P.ζQ_one (chiZ_cyc P) K (-m) x (neg_ne_zero.2 hm) fun g hg => ?_
  have h1 := hx ⟨g, hg⟩
  have e : ((((P.χQ g) ^ m : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) = (algebraMap ℚ_[l] ℂ_[l] ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])) ^ m := by
    have e0 : ((((P.χQ g) ^ m : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] ((((P.χQ g) ^ m : ℚ_[l]ˣ) : ℚ_[l])) := rfl
    rw [e0, Units.val_zpow_eq_zpow_val, map_zpow₀]
  have hne : algebraMap ℚ_[l] ℂ_[l] ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) ≠ 0 :=
    (map_ne_zero _).2 (Units.ne_zero _)
  change Per.σC g x = _ at h1
  rw [chiZ_coe, h1, e, zpow_neg, mul_assoc, mul_comm x, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ hne), one_mul]

end GlobalTheory.TateChiQ
