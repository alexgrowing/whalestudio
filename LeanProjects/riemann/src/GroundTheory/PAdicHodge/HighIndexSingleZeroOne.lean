import Mathlib
import GroundTheory.PAdicHodge.RobbaSeries
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent

set_option linter.unusedSectionVars false

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem Laurent.convergesAt_single {K : Type*} [NontriviallyNormedField K] (n₀ : ℤ) (k : K)
    (ρ : ℝ) : ConvergesAt (Pi.single n₀ k) ρ := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(Set.finite_singleton n₀).compl_mem_cofinite] with n hn
  simp [Pi.single_apply, show n ≠ n₀ from hn]

@[ext]
structure AnnulusRing (I : Set ℝ) where

  coeff : ℤ → K
  convergesAt' : ∀ ρ ∈ I, 0 < ρ → ConvergesAt coeff ρ

@[ext]
structure Robba where

  coeff : ℤ → K
  exists_convergesAt' : ∃ r < 1, ∀ ρ, r ≤ ρ → ρ < 1 → 0 < ρ → ConvergesAt coeff ρ

variable {K}

namespace AnnulusRing

variable {I : Set ℝ}

theorem convergesAt (f : AnnulusRing K I) {ρ : ℝ} (hρ : ρ ∈ I) (hρ0 : 0 < ρ) :
    ConvergesAt f.coeff ρ :=
  f.convergesAt' ρ hρ hρ0

theorem coeff_injective : Function.Injective (coeff : AnnulusRing K I → ℤ → K) :=
  fun _ _ h => AnnulusRing.ext h

instance : Zero (AnnulusRing K I) := ⟨⟨0, fun _ _ _ => convergesAt_zero⟩⟩
instance : One (AnnulusRing K I) := ⟨⟨Pi.single 0 1, fun ρ _ _ => convergesAt_single 0 1 ρ⟩⟩
instance : Add (AnnulusRing K I) :=
  ⟨fun f g => ⟨f.coeff + g.coeff, fun ρ h h0 => (f.convergesAt h h0).add h0 (g.convergesAt h h0)⟩⟩
instance : Neg (AnnulusRing K I) := ⟨fun f => ⟨-f.coeff, fun ρ h h0 => (f.convergesAt h h0).neg⟩⟩
instance : Sub (AnnulusRing K I) :=
  ⟨fun f g => ⟨f.coeff - g.coeff, fun ρ h h0 => (f.convergesAt h h0).sub h0 (g.convergesAt h h0)⟩⟩
instance : SMul K (AnnulusRing K I) :=
  ⟨fun k f => ⟨k • f.coeff, fun ρ h h0 => (f.convergesAt h h0).smul k⟩⟩
instance : SMul ℕ (AnnulusRing K I) :=
  ⟨fun k f => ⟨k • f.coeff, fun ρ h h0 => by
    simpa [ConvergesAt, nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul K] using
      (f.convergesAt h h0).smul (k : K)⟩⟩
instance : SMul ℤ (AnnulusRing K I) :=
  ⟨fun k f => ⟨k • f.coeff, fun ρ h h0 => by
    simpa [ConvergesAt, zsmul_eq_mul, ← Int.cast_smul_eq_zsmul K] using
      (f.convergesAt h h0).smul (k : K)⟩⟩
instance : Mul (AnnulusRing K I) :=
  ⟨fun f g => ⟨cmul f.coeff g.coeff, fun ρ h h0 => (f.convergesAt h h0).cmul h0 (g.convergesAt h h0)⟩⟩

@[simp] theorem coeff_zero : (0 : AnnulusRing K I).coeff = 0 := rfl
@[simp] theorem coeff_one : (1 : AnnulusRing K I).coeff = Pi.single 0 1 := rfl
@[simp] theorem coeff_add (f g : AnnulusRing K I) : (f + g).coeff = f.coeff + g.coeff := rfl
@[simp] theorem coeff_neg (f : AnnulusRing K I) : (-f).coeff = -f.coeff := rfl
@[simp] theorem coeff_sub (f g : AnnulusRing K I) : (f - g).coeff = f.coeff - g.coeff := rfl
@[simp] theorem coeff_smul (k : K) (f : AnnulusRing K I) : (k • f).coeff = k • f.coeff := rfl
@[simp] theorem coeff_nsmul (k : ℕ) (f : AnnulusRing K I) : (k • f).coeff = k • f.coeff := rfl
@[simp] theorem coeff_zsmul (k : ℤ) (f : AnnulusRing K I) : (k • f).coeff = k • f.coeff := rfl
theorem coeff_mul (f g : AnnulusRing K I) : (f * g).coeff = cmul f.coeff g.coeff := rfl

instance : AddCommGroup (AnnulusRing K I) :=
  coeff_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

variable [hI : Fact (∃ ρ ∈ I, 0 < ρ)]

def radius (I : Set ℝ) [hI : Fact (∃ ρ ∈ I, 0 < ρ)] : ℝ := hI.out.choose

theorem radius_mem : radius I ∈ I := hI.out.choose_spec.1

theorem radius_pos : 0 < radius I := hI.out.choose_spec.2

theorem conv (f : AnnulusRing K I) : ConvergesAt f.coeff (radius I) :=
  f.convergesAt radius_mem radius_pos

instance : CommRing (AnnulusRing K I) :=
  { (inferInstance : AddCommGroup (AnnulusRing K I)) with
    mul_assoc := fun f g h => AnnulusRing.ext (cmul_assoc radius_pos f.conv g.conv h.conv)
    one_mul := fun f => AnnulusRing.ext (single_zero_one_cmul f.coeff)
    mul_one := fun f => AnnulusRing.ext (cmul_single_zero_one f.coeff)
    left_distrib := fun f g h => AnnulusRing.ext (cmul_add radius_pos f.conv g.conv h.conv)
    right_distrib := fun f g h => AnnulusRing.ext (add_cmul radius_pos f.conv g.conv h.conv)
    zero_mul := fun f => AnnulusRing.ext (zero_cmul f.coeff)
    mul_zero := fun f => AnnulusRing.ext (cmul_zero f.coeff)
    mul_comm := fun f g => AnnulusRing.ext (cmul_comm f.coeff g.coeff) }

def coeffHom : AnnulusRing K I →+ (ℤ → K) where
  toFun := coeff
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module K (AnnulusRing K I) :=
  Function.Injective.module K coeffHom coeff_injective fun _ _ => rfl

instance : Algebra K (AnnulusRing K I) :=
  Algebra.ofModule (fun k f g => AnnulusRing.ext (smul_cmul k f.coeff g.coeff))
    (fun k f g => AnnulusRing.ext (cmul_smul k f.coeff g.coeff))

def T : AnnulusRing K I := ⟨Pi.single 1 1, fun ρ _ _ => convergesAt_single 1 1 ρ⟩

def restrict {J : Set ℝ} [Fact (∃ ρ ∈ J, 0 < ρ)] (hJ : J ⊆ I) : AnnulusRing K I →ₐ[K] AnnulusRing K J where
  toFun f := ⟨f.coeff, fun ρ h h0 => f.convergesAt (hJ h) h0⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem coeff_restrict {J : Set ℝ} [Fact (∃ ρ ∈ J, 0 < ρ)] (hJ : J ⊆ I)
    (f : AnnulusRing K I) : (restrict hJ f).coeff = f.coeff := rfl

end AnnulusRing

abbrev AnnulusRing.halfOpen (K : Type*) [NontriviallyNormedField K] (r : ℝ) :=
  AnnulusRing K (Set.Ico r 1)

instance AnnulusRing.fact_ico {r : ℝ} [hr : Fact (r < 1)] : Fact (∃ ρ ∈ Set.Ico r 1, 0 < ρ) :=
  ⟨⟨max r (1 / 2), ⟨le_max_left _ _, max_lt hr.out (by norm_num)⟩,
    lt_of_lt_of_le (by norm_num) (le_max_right _ _)⟩⟩

namespace Robba

theorem coeff_injective : Function.Injective (coeff : Robba K → ℤ → K) :=
  fun _ _ h => Robba.ext h

theorem exists_common (f g : Robba K) : ∃ r, 0 < r ∧ r < 1 ∧ ∀ ρ, r ≤ ρ → ρ < 1 →
    ConvergesAt f.coeff ρ ∧ ConvergesAt g.coeff ρ := by
  obtain ⟨r₁, hr₁, h₁⟩ := f.exists_convergesAt'
  obtain ⟨r₂, hr₂, h₂⟩ := g.exists_convergesAt'
  refine ⟨max (max r₁ r₂) (1 / 2), by positivity, max_lt (max_lt hr₁ hr₂) (by norm_num),
    fun ρ hρ hρ1 => ?_⟩
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by norm_num) ((le_max_right _ _).trans hρ)
  exact ⟨h₁ ρ ((le_max_left _ _).trans ((le_max_left _ _).trans hρ)) hρ1 hρ0,
    h₂ ρ ((le_max_right _ _).trans ((le_max_left _ _).trans hρ)) hρ1 hρ0⟩

theorem exists_common₃ (f g h : Robba K) : ∃ ρ, 0 < ρ ∧ ConvergesAt f.coeff ρ ∧
    ConvergesAt g.coeff ρ ∧ ConvergesAt h.coeff ρ := by
  obtain ⟨r, hr0, hr1, hfg⟩ := exists_common f g
  obtain ⟨s, hs0, hs1, hgh⟩ := exists_common g h
  refine ⟨max r s, lt_max_of_lt_left hr0, (hfg _ (le_max_left _ _) (max_lt hr1 hs1)).1,
    (hfg _ (le_max_left _ _) (max_lt hr1 hs1)).2, (hgh _ (le_max_right _ _) (max_lt hr1 hs1)).2⟩

instance : Zero (Robba K) := ⟨⟨0, ⟨0, one_pos, fun _ _ _ _ => convergesAt_zero⟩⟩⟩
instance : One (Robba K) := ⟨⟨Pi.single 0 1, ⟨0, one_pos, fun ρ _ _ _ => convergesAt_single 0 1 ρ⟩⟩⟩
instance : Add (Robba K) :=
  ⟨fun f g => ⟨f.coeff + g.coeff, by
    obtain ⟨r, hr0, hr1, h⟩ := exists_common f g
    exact ⟨r, hr1, fun ρ h1 h2 h3 => (h ρ h1 h2).1.add h3 (h ρ h1 h2).2⟩⟩⟩
instance : Neg (Robba K) :=
  ⟨fun f => ⟨-f.coeff, by
    obtain ⟨r, hr, h⟩ := f.exists_convergesAt'
    exact ⟨r, hr, fun ρ h1 h2 h3 => (h ρ h1 h2 h3).neg⟩⟩⟩
instance : Sub (Robba K) :=
  ⟨fun f g => ⟨f.coeff - g.coeff, by
    obtain ⟨r, hr0, hr1, h⟩ := exists_common f g
    exact ⟨r, hr1, fun ρ h1 h2 h3 => (h ρ h1 h2).1.sub h3 (h ρ h1 h2).2⟩⟩⟩
instance : SMul K (Robba K) :=
  ⟨fun k f => ⟨k • f.coeff, by
    obtain ⟨r, hr, h⟩ := f.exists_convergesAt'
    exact ⟨r, hr, fun ρ h1 h2 h3 => (h ρ h1 h2 h3).smul k⟩⟩⟩
instance : SMul ℕ (Robba K) :=
  ⟨fun k f => ⟨k • f.coeff, by
    obtain ⟨r, hr, h⟩ := f.exists_convergesAt'
    exact ⟨r, hr, fun ρ h1 h2 h3 => by
      simpa [ConvergesAt, nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul K] using
        (h ρ h1 h2 h3).smul (k : K)⟩⟩⟩
instance : SMul ℤ (Robba K) :=
  ⟨fun k f => ⟨k • f.coeff, by
    obtain ⟨r, hr, h⟩ := f.exists_convergesAt'
    exact ⟨r, hr, fun ρ h1 h2 h3 => by
      simpa [ConvergesAt, zsmul_eq_mul, ← Int.cast_smul_eq_zsmul K] using
        (h ρ h1 h2 h3).smul (k : K)⟩⟩⟩
instance : Mul (Robba K) :=
  ⟨fun f g => ⟨cmul f.coeff g.coeff, by
    obtain ⟨r, hr0, hr1, h⟩ := exists_common f g
    exact ⟨r, hr1, fun ρ h1 h2 h3 => (h ρ h1 h2).1.cmul h3 (h ρ h1 h2).2⟩⟩⟩

@[simp] theorem coeff_zero : (0 : Robba K).coeff = 0 := rfl
@[simp] theorem coeff_one : (1 : Robba K).coeff = Pi.single 0 1 := rfl
@[simp] theorem coeff_add (f g : Robba K) : (f + g).coeff = f.coeff + g.coeff := rfl
@[simp] theorem coeff_neg (f : Robba K) : (-f).coeff = -f.coeff := rfl
@[simp] theorem coeff_sub (f g : Robba K) : (f - g).coeff = f.coeff - g.coeff := rfl
@[simp] theorem coeff_smul (k : K) (f : Robba K) : (k • f).coeff = k • f.coeff := rfl
theorem coeff_mul (f g : Robba K) : (f * g).coeff = cmul f.coeff g.coeff := rfl

instance : AddCommGroup (Robba K) :=
  coeff_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

instance : CommRing (Robba K) :=
  { (inferInstance : AddCommGroup (Robba K)) with
    mul_assoc := fun f g h => by
      obtain ⟨ρ, hρ, hf, hg, hh⟩ := exists_common₃ f g h
      exact Robba.ext (cmul_assoc hρ hf hg hh)
    one_mul := fun f => Robba.ext (single_zero_one_cmul f.coeff)
    mul_one := fun f => Robba.ext (cmul_single_zero_one f.coeff)
    left_distrib := fun f g h => by
      obtain ⟨ρ, hρ, hf, hg, hh⟩ := exists_common₃ f g h
      exact Robba.ext (cmul_add hρ hf hg hh)
    right_distrib := fun f g h => by
      obtain ⟨ρ, hρ, hf, hg, hh⟩ := exists_common₃ f g h
      exact Robba.ext (add_cmul hρ hf hg hh)
    zero_mul := fun f => Robba.ext (zero_cmul f.coeff)
    mul_zero := fun f => Robba.ext (cmul_zero f.coeff)
    mul_comm := fun f g => Robba.ext (cmul_comm f.coeff g.coeff) }

def coeffHom : Robba K →+ (ℤ → K) where
  toFun := coeff
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module K (Robba K) :=
  Function.Injective.module K coeffHom coeff_injective fun _ _ => rfl

instance : Algebra K (Robba K) :=
  Algebra.ofModule (fun k f g => Robba.ext (smul_cmul k f.coeff g.coeff))
    (fun k f g => Robba.ext (cmul_smul k f.coeff g.coeff))

end Robba

namespace AnnulusRing

variable {r : ℝ} [Fact (r < 1)]

def toRobba : AnnulusRing.halfOpen K r →ₐ[K] Robba K where
  toFun f := ⟨f.coeff, ⟨r, Fact.out, fun ρ h1 h2 h3 => f.convergesAt ⟨h1, h2⟩ h3⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem coeff_toRobba (f : AnnulusRing.halfOpen K r) : (toRobba f).coeff = f.coeff := rfl

theorem toRobba_injective : Function.Injective (toRobba : AnnulusRing.halfOpen K r → Robba K) :=
  fun _ _ h => AnnulusRing.ext (congrArg Robba.coeff h)

theorem toRobba_restrict {s : ℝ} [Fact (s < 1)] (hrs : r ≤ s) (f : AnnulusRing.halfOpen K r) :
    toRobba (restrict (J := Set.Ico s 1) (Set.Ico_subset_Ico_left hrs) f) = toRobba f := rfl

end AnnulusRing

namespace Robba

theorem exists_toRobba (f : Robba K) : ∃ (r : ℝ) (_ : Fact (r < 1)) (g : AnnulusRing.halfOpen K r),
    AnnulusRing.toRobba g = f := by
  obtain ⟨r, hr, h⟩ := f.exists_convergesAt'
  exact ⟨r, ⟨hr⟩, ⟨f.coeff, fun ρ hρ h0 => h ρ hρ.1 hρ.2 h0⟩, rfl⟩

end Robba

namespace Laurent

theorem gaussNorm_single_zero_one {ρ : ℝ} (hρ : 0 < ρ) :
    gaussNorm (Pi.single 0 (1 : K)) ρ = 1 := by
  refine le_antisymm (gaussNorm_le fun n => ?_) ?_
  · by_cases hn : n = 0
    · subst hn; simp
    · simp [Pi.single_apply, hn]
  · simpa using (convergesAt_single 0 (1 : K) ρ).le_gaussNorm 0

theorem domSet_single_zero_one {ρ : ℝ} (hρ : 0 < ρ) :
    domSet (Pi.single 0 (1 : K)) ρ = {0} := by
  ext n
  simp only [domSet, Set.mem_setOf_eq, gaussNorm_single_zero_one hρ, Set.mem_singleton_iff]
  by_cases hn : n = 0
  · subst hn; simp
  · simp [Pi.single_apply, hn]

theorem lowIndex_single_zero_one {ρ : ℝ} (hρ : 0 < ρ) :
    lowIndex (Pi.single 0 (1 : K)) ρ = 0 := by
  rw [lowIndex, domSet_single_zero_one hρ, csInf_singleton]

theorem highIndex_single_zero_one {ρ : ℝ} (hρ : 0 < ρ) :
    highIndex (Pi.single 0 (1 : K)) ρ = 0 := by
  rw [highIndex, domSet_single_zero_one hρ, csSup_singleton]

end Laurent

namespace Robba

def bounded (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] :
    Subring (Robba K) where
  carrier := {f | BddAbove (Set.range fun n => ‖f.coeff n‖)}
  mul_mem' {f g} hf hg := by
    obtain ⟨A, hA⟩ := hf
    obtain ⟨B, hB⟩ := hg
    refine ⟨max A 0 * max B 0, Set.forall_mem_range.2 fun n => ?_⟩
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun i => ?_
    rw [norm_mul]
    exact mul_le_mul ((hA ⟨i, rfl⟩).trans (le_max_left _ _))
      ((hB ⟨n - i, rfl⟩).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
  one_mem' := ⟨1, Set.forall_mem_range.2 fun n => by
    by_cases hn : n = 0
    · subst hn; simp
    · simp [Pi.single_apply, hn]⟩
  add_mem' {f g} hf hg := by
    obtain ⟨A, hA⟩ := hf
    obtain ⟨B, hB⟩ := hg
    exact ⟨A + B, Set.forall_mem_range.2 fun n =>
      (norm_add_le _ _).trans (add_le_add (hA ⟨n, rfl⟩) (hB ⟨n, rfl⟩))⟩
  zero_mem' := ⟨0, Set.forall_mem_range.2 fun n => by simp⟩
  neg_mem' {f} hf := by
    obtain ⟨A, hA⟩ := hf
    exact ⟨A, Set.forall_mem_range.2 fun n => by simpa using hA ⟨n, rfl⟩⟩

theorem mem_bounded {f : Robba K} :
    f ∈ bounded K ↔ BddAbove (Set.range fun n => ‖f.coeff n‖) := Iff.rfl

theorem mem_bounded_of_mul_eq_one {f g : Robba K} (h : f * g = 1) : f ∈ bounded K := by
  obtain ⟨r, hr0, hr1, hc⟩ := exists_common f g
  have hfg : cmul f.coeff g.coeff = Pi.single 0 1 := congrArg Robba.coeff h
  have hne : (Pi.single 0 (1 : K) : ℤ → K) ≠ 0 := fun h0 => by
    simpa using congrFun h0 0
  have hf0 : f.coeff ≠ 0 := fun h0 => hne (by rw [← hfg, h0, zero_cmul])
  have hg0 : g.coeff ≠ 0 := fun h0 => hne (by rw [← hfg, h0, cmul_zero])
  have pos : ∀ ρ, r ≤ ρ → 0 < ρ := fun ρ hρ => hr0.trans_le hρ

  have key : ∀ ρ, r ≤ ρ → ρ < 1 → lowIndex f.coeff ρ = highIndex f.coeff ρ ∧
      lowIndex g.coeff ρ = -lowIndex f.coeff ρ ∧ highIndex g.coeff ρ = -lowIndex f.coeff ρ := by
    intro ρ h1 h2
    have hρ := pos ρ h1
    obtain ⟨cf, cg⟩ := hc ρ h1 h2
    have e1 := lowIndex_cmul hρ cf cg hf0 hg0
    have e2 := highIndex_cmul hρ cf cg hf0 hg0
    rw [hfg, lowIndex_single_zero_one hρ] at e1
    rw [hfg, highIndex_single_zero_one hρ] at e2
    have l1 := lowIndex_le_highIndex hρ cf hf0
    have l2 := lowIndex_le_highIndex hρ cg hg0
    refine ⟨by omega, by omega, by omega⟩

  have mono : ∀ ρ ρ', r ≤ ρ → ρ < ρ' → ρ' < 1 → lowIndex f.coeff ρ = lowIndex f.coeff ρ' := by
    intro ρ ρ' h1 h12 h2
    have h1' : r ≤ ρ' := h1.trans h12.le
    have hρ1 : ρ < 1 := h12.trans h2
    have a1 := highIndex_le_lowIndex (pos ρ h1) h12 (hc ρ h1 hρ1).1 (hc ρ' h1' h2).1 hf0
    have a2 := highIndex_le_lowIndex (pos ρ h1) h12 (hc ρ h1 hρ1).2 (hc ρ' h1' h2).2 hg0
    obtain ⟨k1, k2, k3⟩ := key ρ h1 hρ1
    obtain ⟨k1', k2', k3'⟩ := key ρ' h1' h2
    omega
  set N := lowIndex f.coeff r
  have hN : ∀ ρ, r ≤ ρ → ρ < 1 → ∀ n, ‖f.coeff n‖ * ρ ^ n ≤ ‖f.coeff N‖ * ρ ^ N := by
    intro ρ h1 h2 n
    have hL : lowIndex f.coeff ρ = N := by
      rcases h1.lt_or_eq with h | h
      · exact (mono r ρ le_rfl h h2).symm
      · subst h; rfl
    have hmem := lowIndex_mem (pos ρ h1) (hc ρ h1 h2).1 hf0
    rw [hL] at hmem
    rw [show ‖f.coeff N‖ * ρ ^ N = gaussNorm f.coeff ρ from hmem]
    exact (hc ρ h1 h2).1.le_gaussNorm n
  refine ⟨‖f.coeff N‖, Set.forall_mem_range.2 fun n => ?_⟩
  have hlim : Tendsto (fun ρ : ℝ => ‖f.coeff N‖ * ρ ^ (N - n)) (𝓝[<] 1)
      (𝓝 (‖f.coeff N‖ * (1 : ℝ) ^ (N - n))) :=
    (((continuousAt_zpow₀ (1 : ℝ) (N - n) (Or.inl one_ne_zero)).tendsto).const_mul _).mono_left
      nhdsWithin_le_nhds
  rw [one_zpow, mul_one] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT hr1] with ρ hρ
  have hρ0 := pos ρ hρ.1.le
  have := hN ρ hρ.1.le hρ.2 n
  have hpos : 0 < ρ ^ n := zpow_pos hρ0 n
  rw [show ρ ^ (N - n) = ρ ^ N / ρ ^ n by rw [zpow_sub₀ hρ0.ne'], mul_div_assoc',
    le_div_iff₀ hpos]
  exact this

theorem isUnit_iff {f : Robba K} :
    IsUnit f ↔ ∃ g : (bounded K)ˣ, ((g : bounded K) : Robba K) = f := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : (u : Robba K) ∈ bounded K := mem_bounded_of_mul_eq_one u.mul_inv
    have h2 : ((u⁻¹ : (Robba K)ˣ) : Robba K) ∈ bounded K := mem_bounded_of_mul_eq_one u.inv_mul
    exact ⟨⟨⟨u, h1⟩, ⟨_, h2⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩, rfl⟩
  · rintro ⟨g, rfl⟩
    exact (Units.map (bounded K).subtype.toMonoidHom g).isUnit

theorem isUnit_iff_isUnit_bounded {f : Robba K} :
    IsUnit f ↔ ∃ hf : f ∈ bounded K, IsUnit (⟨f, hf⟩ : bounded K) := by
  rw [isUnit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨(g : bounded K).2, g.isUnit⟩
  · rintro ⟨hf, u, hu⟩
    exact ⟨u, by rw [hu]⟩

end Robba

namespace Laurent

theorem cmul_single_left (k : ℤ) (c : K) (x : ℤ → K) :
    cmul (Pi.single k c) x = fun n => c * x (n - k) := by
  funext n
  unfold cmul
  rw [tsum_eq_single k fun i hi => by simp [Pi.single_apply, hi]]
  simp

end Laurent

namespace Robba

def single (k : ℤ) (c : K) : Robba K :=
  ⟨Pi.single k c, ⟨0, one_pos, fun ρ _ _ _ => convergesAt_single k c ρ⟩⟩

@[simp] theorem coeff_single (k : ℤ) (c : K) : (single k c).coeff = Pi.single k c := rfl

theorem coeff_single_mul (k : ℤ) (c : K) (f : Robba K) :
    (single k c * f).coeff = fun n => c * f.coeff (n - k) :=
  cmul_single_left k c f.coeff

theorem single_mul_single (k l : ℤ) (c d : K) : single k c * single l d = single (k + l) (c * d) := by
  ext n
  rw [coeff_single_mul]
  simp only [coeff_single, Pi.single_apply, sub_eq_iff_eq_add]
  split_ifs with h1 h2 h2 <;> first | (exfalso; omega) | simp

@[simp] theorem single_zero_one : single 0 (1 : K) = 1 := rfl

theorem isUnit_single (k : ℤ) {c : K} (hc : c ≠ 0) : IsUnit (single k c) := by
  have h : single k c * single (-k) c⁻¹ = 1 := by
    rw [single_mul_single, add_neg_cancel, mul_inv_cancel₀ hc, single_zero_one]
  exact ⟨⟨single k c, single (-k) c⁻¹, h, by rw [mul_comm]; exact h⟩, rfl⟩

def T : Robba K := single 1 1

theorem isUnit_T : IsUnit (T : Robba K) := isUnit_single 1 one_ne_zero

theorem single_mem_bounded (k : ℤ) (c : K) : single k c ∈ bounded K :=
  ⟨‖c‖, Set.forall_mem_range.2 fun n => by
    by_cases hn : n = k
    · subst hn; simp
    · simp [Pi.single_apply, hn]⟩

end Robba

end GroundTheory.PAdicHodge
