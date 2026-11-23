import Mathlib
import GroundTheory.PAdicHodge.ThetaBDeRhamPlusFieldCycloUnitBdRZpow
import GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne
import GroundTheory.PAdicHodge.AdmissibleField
set_option maxSynthPendingDepth 1

noncomputable section

open IsLocalRing TensorProduct Module

namespace GroundTheory.PAdicHodge

variable {p : ℕ} [Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p
local notation "Fil" => IsPerfectoidField.fil ℂ_[p] p

section Algebra

variable (p) in

def algClToBdRField : PadicAlgCl p →+* 𝔹dR := (algebraMap 𝔹 𝔹dR).comp (algClToBdR p).toRingHom

instance algebraAlgClBDeRham : Algebra (PadicAlgCl p) 𝔹dR := (algClToBdRField p).toAlgebra

instance algebraPadicBDeRham : Algebra ℚ_[p] 𝔹dR :=
  ((algebraMap 𝔹 𝔹dR).comp (algebraMap ℚ_[p] 𝔹)).toAlgebra

theorem algebraMap_padic_bDeRham (q : ℚ_[p]) :
    algebraMap ℚ_[p] 𝔹dR q = algebraMap 𝔹 𝔹dR (algebraMap ℚ_[p] 𝔹 q) := rfl

theorem algebraMap_algCl_bDeRham (x : PadicAlgCl p) :
    algebraMap (PadicAlgCl p) 𝔹dR x = algebraMap 𝔹 𝔹dR (algClToBdR p x) := rfl

instance isScalarTower_padic_bDeRhamPlus_bDeRham : IsScalarTower ℚ_[p] 𝔹 𝔹dR :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance isScalarTower_padic_algCl_bDeRham : IsScalarTower ℚ_[p] (PadicAlgCl p) 𝔹dR :=
  IsScalarTower.of_algebraMap_eq fun q => by
    change algebraMap 𝔹 𝔹dR (algebraMap ℚ_[p] 𝔹 q) =
      algebraMap 𝔹 𝔹dR (algClToBdR p (algebraMap ℚ_[p] (PadicAlgCl p) q))
    rw [AlgHom.commutes]

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem algebraMap_intermediateField_bDeRham (k : K) :
    algebraMap K 𝔹dR k = algebraMap 𝔹 𝔹dR (algClToBdR p k) := rfl

instance isScalarTower_padic_intermediateField_bDeRham : IsScalarTower ℚ_[p] K 𝔹dR :=
  IsScalarTower.of_algebraMap_eq fun q => by
    change algebraMap 𝔹 𝔹dR (algebraMap ℚ_[p] 𝔹 q) =
      algebraMap 𝔹 𝔹dR (algClToBdR p (algebraMap ℚ_[p] (PadicAlgCl p) q))
    rw [AlgHom.commutes]

variable {K}

theorem gal_smul_algebraMap_intermediateField_bDeRham (σ : Gal(PadicAlgCl p/K)) (k : K) :
    σ • algebraMap K 𝔹dR k = algebraMap K 𝔹dR k := by
  rw [algebraMap_intermediateField_bDeRham, gal_smul_algebraMap_bDeRham, gal_smul_algClToBdR]
  congr 2
  exact AlgEquiv.commutes σ k

theorem gal_smul_algebraMap_padic_bDeRham (σ : Gal(PadicAlgCl p/K)) (q : ℚ_[p]) :
    σ • algebraMap ℚ_[p] 𝔹dR q = algebraMap ℚ_[p] 𝔹dR q := by
  rw [algebraMap_padic_bDeRham, gal_smul_algebraMap_bDeRham, gal_smul_algebraMap_bdR]

instance smulCommClass_gal_intermediateField_bDeRham :
    SMulCommClass Gal(PadicAlgCl p/K) K 𝔹dR where
  smul_comm σ k x := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', gal_smul_algebraMap_intermediateField_bDeRham]

instance smulCommClass_gal_padic_bDeRham : SMulCommClass Gal(PadicAlgCl p/K) ℚ_[p] 𝔹dR where
  smul_comm σ q x := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', gal_smul_algebraMap_padic_bDeRham]

end Algebra

section Level

theorem bDeRham_exists_mem_fil (x : 𝔹dR) : ∃ i : ℤ, x ∈ Fil i := by
  have hx : x ∈ ⨆ i, Fil i := by
    rw [IsPerfectoidField.iSup_fil]
    exact Submodule.mem_top
  exact (Submodule.mem_iSup_of_directed _
    (IsPerfectoidField.fil_antitone ℂ_[p] p).directed_le).1 hx

theorem bDeRham_exists_not_mem_fil {x : 𝔹dR} (hx : x ≠ 0) : ∃ i : ℤ, x ∉ Fil i := by
  by_contra h
  push Not at h
  apply hx
  have : x ∈ ⨅ i, Fil i := (Submodule.mem_iInf _).2 h
  rwa [IsPerfectoidField.iInf_fil, Submodule.mem_bot] at this

theorem bDeRham_exists_level {x : 𝔹dR} (hx : x ≠ 0) : ∃ i : ℤ, x ∈ Fil i ∧ x ∉ Fil (i + 1) := by
  obtain ⟨j, hj⟩ := bDeRham_exists_not_mem_fil hx
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, x ∈ Fil z → z ≤ b := by
    refine ⟨j, fun z hz => ?_⟩
    by_contra hlt
    push Not at hlt
    exact hj (IsPerfectoidField.fil_antitone ℂ_[p] p hlt.le hz)
  obtain ⟨i, hi, hmax⟩ := Int.exists_greatest_of_bdd hbdd (bDeRham_exists_mem_fil x)
  exact ⟨i, hi, fun h => by have := hmax _ h; omega⟩

theorem bDeRham_exists_forall_mem_fil {ι : Type*} (s : Finset ι) (c : ι → 𝔹dR) :
    ∃ i : ℤ, ∀ j ∈ s, c j ∈ Fil i := by
  classical
  refine Finset.induction_on s ⟨0, by simp⟩ ?_
  rintro a s - ⟨i, hi⟩
  obtain ⟨i', hi'⟩ := bDeRham_exists_mem_fil (c a)
  refine ⟨min i i', fun j hj => ?_⟩
  rcases Finset.mem_insert.1 hj with rfl | hj
  · exact IsPerfectoidField.fil_antitone ℂ_[p] p (min_le_right _ _) hi'
  · exact IsPerfectoidField.fil_antitone ℂ_[p] p (min_le_left _ _) (hi j hj)

theorem grMap_zero_algebraMap (b : 𝔹) (h : algebraMap 𝔹 𝔹dR b ∈ Fil 0) :
    IsPerfectoidField.grMap maximalIdeal_eq_span_tBdR 0 ⟨algebraMap 𝔹 𝔹dR b, h⟩ =
      thetaAlgHom p b := by
  have e : algebraMap 𝔹 𝔹dR b = algebraMap 𝔹 𝔹dR (tBdR p) ^ (0 : ℤ) * algebraMap 𝔹 𝔹dR b := by
    rw [zpow_zero, one_mul]
  have h' : algebraMap 𝔹 𝔹dR (tBdR p) ^ (0 : ℤ) * algebraMap 𝔹 𝔹dR b ∈ Fil 0 := by
    rw [← e]
    exact h
  have : (⟨algebraMap 𝔹 𝔹dR b, h⟩ : Fil 0) = ⟨_, h'⟩ := Subtype.ext e
  rw [this, IsPerfectoidField.grMap_mk, thetaAlgHom_apply]

end Level

section Invariants

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem grMap_mem_invariants {i : ℤ} (x : Fil i)
    (hx : ∀ σ : Gal(PadicAlgCl p/K), σ • (x : 𝔹dR) = x) :
    IsPerfectoidField.grMap maximalIdeal_eq_span_tBdR i x ∈ (cpTwistRep K i).invariants := by
  rw [ContRepresentation.mem_invariants]
  intro σ
  rw [← grMap_tBdR_gal_smul σ x]
  congr 1
  exact Subtype.ext (hx σ)

variable [FiniteDimensional ℚ_[p] K]

theorem mem_fil_succ_of_invariant {i : ℤ} (hi : i ≠ 0) {x : 𝔹dR} (hxi : x ∈ Fil i)
    (hx : ∀ σ : Gal(PadicAlgCl p/K), σ • x = x) : x ∈ Fil (i + 1) := by
  have h := grMap_mem_invariants K ⟨x, hxi⟩ hx
  rw [cpTwistRep_invariants_eq_bot K hi, Submodule.mem_bot] at h
  exact (IsPerfectoidField.grMap_eq_zero_iff maximalIdeal_eq_span_tBdR ⟨x, hxi⟩).1 h

theorem level_eq_zero_of_invariant {x : 𝔹dR} (hx : ∀ σ : Gal(PadicAlgCl p/K), σ • x = x)
    {i : ℤ} (hi : x ∈ Fil i) (hi' : x ∉ Fil (i + 1)) : i = 0 := by
  by_contra h
  exact hi' (mem_fil_succ_of_invariant K h hi hx)

theorem bDeRham_fixed (x : 𝔹dR) (hx : ∀ σ : Gal(PadicAlgCl p/K), σ • x = x) :
    ∃ k : K, algebraMap K 𝔹dR k = x := by
  by_cases h0 : x = 0
  · exact ⟨0, by rw [map_zero, h0]⟩
  obtain ⟨i, hi, hi'⟩ := bDeRham_exists_level h0
  obtain rfl := level_eq_zero_of_invariant K hx hi hi'
  have hinv := grMap_mem_invariants K ⟨x, hi⟩ hx
  rw [cpTwistRep_invariants_zero K] at hinv
  obtain ⟨k, hk⟩ := hinv
  refine ⟨k, ?_⟩
  rw [algebraMap_intermediateField_bDeRham]
  by_contra hne
  have hy0 : x - algebraMap 𝔹 𝔹dR (algClToBdR p k) ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hyinv : ∀ σ : Gal(PadicAlgCl p/K), σ • (x - algebraMap 𝔹 𝔹dR (algClToBdR p k)) =
      x - algebraMap 𝔹 𝔹dR (algClToBdR p k) := fun σ => by
    rw [smul_sub, hx σ, ← algebraMap_intermediateField_bDeRham,
      gal_smul_algebraMap_intermediateField_bDeRham]
  have hk0 : algebraMap 𝔹 𝔹dR (algClToBdR p k) ∈ Fil 0 :=
    (IsPerfectoidField.mem_fil_zero_iff ℂ_[p] p).2 ⟨_, rfl⟩
  have hgr0 := grMap_zero_algebraMap (algClToBdR p k) hk0
  rw [thetaAlgHom_algClToBdR] at hgr0
  have hy : x - algebraMap 𝔹 𝔹dR (algClToBdR p k) ∈ Fil 0 := Submodule.sub_mem _ hi hk0
  have hgr : IsPerfectoidField.grMap maximalIdeal_eq_span_tBdR 0
      (⟨x - algebraMap 𝔹 𝔹dR (algClToBdR p k), hy⟩ : Fil 0) = 0 := by
    have e : (⟨x - algebraMap 𝔹 𝔹dR (algClToBdR p k), hy⟩ : Fil 0) =
        ⟨x, hi⟩ - ⟨algebraMap 𝔹 𝔹dR (algClToBdR p k), hk0⟩ := rfl
    rw [e, map_sub, hgr0, ← hk, Algebra.linearMap_apply, algebraMap_intermediateField_cp, sub_self]
  have hy1 : x - algebraMap 𝔹 𝔹dR (algClToBdR p k) ∈ Fil (0 + 1) :=
    (IsPerfectoidField.grMap_eq_zero_iff maximalIdeal_eq_span_tBdR _).1 hgr
  obtain ⟨j, hj, hj'⟩ := bDeRham_exists_level hy0
  obtain rfl := level_eq_zero_of_invariant K hyinv hj hj'
  exact hj' hy1

theorem bDeRhamPlus_fixed (b : 𝔹) (hb : ∀ σ : Gal(PadicAlgCl p/K), σ • b = b) :
    ∃ k : K, algClToBdR p k = b := by
  obtain ⟨k, hk⟩ := bDeRham_fixed K (algebraMap 𝔹 𝔹dR b) fun σ => by
    rw [gal_smul_algebraMap_bDeRham, hb σ]
  exact ⟨k, IsPerfectoidField.algebraMap_bDeRham_injective hk⟩

theorem invariantRing_bDeRham :
    invariantRing Gal(PadicAlgCl p/K) ℚ_[p] 𝔹dR = (IsScalarTower.toAlgHom ℚ_[p] K 𝔹dR).range :=
  invariantRing_eq_range (bDeRham_fixed K)

end Invariants

section DeRham

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem isRegular_bDeRham : IsRegular Gal(PadicAlgCl p/K) ℚ_[p] 𝔹dR :=
  isRegular_of_field _ _ _

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/K) V)

abbrev DdR : Submodule K (𝔹dR ⊗[ℚ_[p]] V) := DBK Gal(PadicAlgCl p/K) ℚ_[p] K 𝔹dR ρ

def IsDeRham : Prop := IsAdmissible 𝔹dR ρ

variable [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] V]

theorem finiteDimensional_DdR : FiniteDimensional K (DdR K ρ) :=
  (isRegular_bDeRham K).finiteDimensional_DBK ρ (bDeRham_fixed K)

theorem finrank_DdR_le : finrank K (DdR K ρ) ≤ finrank ℚ_[p] V :=
  (isRegular_bDeRham K).finrank_DBK_le ρ (bDeRham_fixed K)

omit [FiniteDimensional ℚ_[p] V] in

theorem isDeRham_iff_finrank : IsDeRham K ρ ↔ finrank K (DdR K ρ) = finrank ℚ_[p] V :=
  isAdmissible_iff_finrank_DBK ρ (bDeRham_fixed K)

omit [FiniteDimensional ℚ_[p] K] in

theorem IsDeRham.comparison_bijective (h : IsDeRham K ρ) :
    Function.Bijective (comparison 𝔹dR ρ) :=
  ((isRegular_bDeRham K).isAdmissible_iff_bijective ρ).1 h

end DeRham

section Filtration

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (V : Type*) [AddCommGroup V]
  [Module ℚ_[p] V]

def filTensor (i : ℤ) : Submodule K (𝔹dR ⊗[ℚ_[p]] V) :=
  Submodule.span K {x | ∃ b ∈ Fil i, ∃ v : V, x = b ⊗ₜ v}

variable {K V}

theorem mem_filTensor_iff {ι : Type*} [Fintype ι] (v : Basis ι ℚ_[p] V) {i : ℤ}
    {x : 𝔹dR ⊗[ℚ_[p]] V} :
    x ∈ filTensor K V i ↔ ∀ j, (Algebra.TensorProduct.basis 𝔹dR v).repr x j ∈ Fil i := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, w, rfl⟩ := hx
      intro j
      rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
        smul_eq_mul, mul_comm, algebraMap_padic_bDeRham, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hb
    | zero => simp
    | add x y _ _ hx hy =>
      intro j
      rw [map_add, Finsupp.add_apply]
      exact add_mem (hx j) (hy j)
    | smul k x _ hx =>
      intro j
      rw [← algebraMap_smul 𝔹dR k x, map_smul, Finsupp.smul_apply, smul_eq_mul,
        algebraMap_intermediateField_bDeRham, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (hx j)
  · intro h
    rw [← (Algebra.TensorProduct.basis 𝔹dR v).sum_repr x]
    refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨_, h j, v j, ?_⟩
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

variable (K V) in

theorem filTensor_antitone : Antitone (filTensor K V) := fun _ _ hij =>
  Submodule.span_mono fun _ ⟨b, hb, w, hx⟩ =>
    ⟨b, IsPerfectoidField.fil_antitone ℂ_[p] p hij hb, w, hx⟩

variable [FiniteDimensional ℚ_[p] V]

theorem exists_mem_filTensor (x : 𝔹dR ⊗[ℚ_[p]] V) : ∃ i : ℤ, x ∈ filTensor K V i := by
  let v := Module.finBasis ℚ_[p] V
  obtain ⟨i, hi⟩ := bDeRham_exists_forall_mem_fil Finset.univ
    ((Algebra.TensorProduct.basis 𝔹dR v).repr x)
  exact ⟨i, (mem_filTensor_iff v).2 fun j => hi j (Finset.mem_univ j)⟩

theorem exists_not_mem_filTensor {x : 𝔹dR ⊗[ℚ_[p]] V} (hx : x ≠ 0) :
    ∃ i : ℤ, x ∉ filTensor K V i := by
  let v := Module.finBasis ℚ_[p] V
  have : (Algebra.TensorProduct.basis 𝔹dR v).repr x ≠ 0 := by
    rwa [Ne, LinearEquiv.map_eq_zero_iff]
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.1 this
  obtain ⟨i, hi⟩ := bDeRham_exists_not_mem_fil hj
  exact ⟨i, fun h => hi ((mem_filTensor_iff v).1 h j)⟩

theorem exists_forall_mem_filTensor {ι : Type*} (s : Finset ι) (x : ι → 𝔹dR ⊗[ℚ_[p]] V) :
    ∃ i : ℤ, ∀ j ∈ s, x j ∈ filTensor K V i := by
  classical
  refine Finset.induction_on s ⟨0, by simp⟩ ?_
  rintro a s - ⟨i, hi⟩
  obtain ⟨i', hi'⟩ := exists_mem_filTensor (K := K) (x a)
  refine ⟨min i i', fun j hj => ?_⟩
  rcases Finset.mem_insert.1 hj with rfl | hj
  · exact filTensor_antitone K V (min_le_right _ _) hi'
  · exact filTensor_antitone K V (min_le_left _ _) (hi j hj)

variable (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/K) V)

variable (K) in

def filDdR (i : ℤ) : Submodule K (𝔹dR ⊗[ℚ_[p]] V) := DdR K ρ ⊓ filTensor K V i

omit [FiniteDimensional ℚ_[p] V] in
variable (K) in

theorem filDdR_antitone : Antitone (filDdR K ρ) := fun _ _ hij =>
  inf_le_inf_left _ (filTensor_antitone K V hij)

omit [FiniteDimensional ℚ_[p] V] in
theorem filDdR_le (i : ℤ) : filDdR K ρ i ≤ DdR K ρ := inf_le_left

variable [FiniteDimensional ℚ_[p] K]

variable (K) in

theorem exists_filDdR_eq_top : ∃ a : ℤ, filDdR K ρ a = DdR K ρ := by
  have := finiteDimensional_DdR K ρ
  have : Module.Free K (DdR K ρ) := Module.Free.of_divisionRing K (DdR K ρ)
  let d := Module.finBasis K (DdR K ρ)
  obtain ⟨a, ha⟩ := exists_forall_mem_filTensor (K := K) Finset.univ fun l => (d l : 𝔹dR ⊗[ℚ_[p]] V)
  refine ⟨a, le_antisymm inf_le_left fun x hx => ⟨hx, ?_⟩⟩
  have hsum := congrArg Subtype.val (d.sum_repr ⟨x, hx⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
  rw [← hsum]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (ha l (Finset.mem_univ l))

variable (K) in

theorem exists_filDdR_eq_bot : ∃ b : ℤ, filDdR K ρ b = ⊥ := by
  have := finiteDimensional_DdR K ρ
  have key : ∀ n : ℕ, ∀ i : ℤ, finrank K (filDdR K ρ i) ≤ n → ∃ b : ℤ, filDdR K ρ b = ⊥ := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have : FiniteDimensional K (filDdR K ρ i) :=
        Submodule.finiteDimensional_of_le (filDdR_le ρ i)
      exact ⟨i, Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hi)⟩
    | succ n ih =>
      intro i hi
      by_cases hbot : filDdR K ρ i = ⊥
      · exact ⟨i, hbot⟩
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      obtain ⟨j, hj⟩ := exists_not_mem_filTensor (K := K) hx0
      have hij : i ≤ j := by
        by_contra hlt
        push Not at hlt
        exact hj (filTensor_antitone K V hlt.le hx.2)
      have hlt : filDdR K ρ j < filDdR K ρ i :=
        lt_of_le_of_ne (filDdR_antitone K ρ hij) fun heq => hj (heq ▸ hx).2
      have : FiniteDimensional K (filDdR K ρ i) :=
        Submodule.finiteDimensional_of_le (filDdR_le ρ i)
      exact ih j (Nat.lt_succ_iff.1 ((Submodule.finrank_lt_finrank_of_lt hlt).trans_le hi))
  exact key _ 0 le_rfl

end Filtration

end GroundTheory.PAdicHodge
