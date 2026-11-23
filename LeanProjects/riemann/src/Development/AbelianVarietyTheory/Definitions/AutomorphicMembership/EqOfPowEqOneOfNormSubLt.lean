import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module

namespace GlobalTheory.Pst

section Unram

variable {l : ℕ} [Fact l.Prime]

theorem eq_of_pow_eq_one_of_norm_sub_lt {x y : Om l} {m : ℕ} (hm : ¬ l ∣ m) (hx : x ^ m = 1)
    (hy : y ^ m = 1) (h : ‖x - y‖ < 1) : x = y := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have hy1 : ‖y‖ = 1 := by
    have := congrArg norm hy
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).mp this
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy1
  by_contra hne
  set z := x / y with hz
  have hz1 : z ≠ 1 := fun h1 => hne (by rwa [hz, div_eq_one_iff_eq hy0] at h1)
  have hzm : z ^ m = 1 := by rw [hz, div_pow, hx, hy, div_one]
  have hzn : ‖z - 1‖ < 1 := by
    rw [hz, div_sub_one hy0, norm_div, hy1, div_one]; exact h
  have hz0 : ‖z‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (z - 1) 1
    rw [sub_add_cancel, norm_one] at this
    exact this.trans (max_le hzn.le le_rfl)
  have hsum : ∑ i ∈ Finset.range m, z ^ i = 0 := by
    have := geom_sum_mul z m
    rw [hzm, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hz1)
  have hpow : ∀ i : ℕ, ‖z ^ i - 1‖ < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : z ^ (i + 1) - 1 = z * (z ^ i - 1) + (z - 1) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hzn)
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hz0).trans_lt ih
  have hall : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, z ^ i - (n : Om l)‖ < 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : ∑ i ∈ Finset.range (n + 1), z ^ i - ((n + 1 : ℕ) : Om l) =
          (∑ i ∈ Finset.range n, z ^ i - (n : Om l)) + (z ^ n - 1) := by
        rw [Finset.sum_range_succ]; push_cast; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (hpow n))
  have h1 := hall m
  rw [hsum, zero_sub, norm_neg, ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends,
    Padic.norm_natCast_lt_one_iff] at h1
  exact hm h1

theorem norm_eq_one_of_pow_eq_one {x : Om l} {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1) : ‖x‖ = 1 := by
  have := congrArg norm hx
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').mp this

theorem kur_algHom_ext {B : Type*} [Semiring B] [Algebra ℚ_[l] B] {f g : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] B}
    (h : ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → f c = g c) : f = g :=
  IntermediateField.adjoin_algHom_ext ℚ_[l] fun _ ⟨m, h0, hm, hx⟩ => h _ m h0 hm (Subtype.ext hx)

variable (l) in

def frobUr : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) := (GlobalTheory.MemLoc.exists_frobenius_Kur l).choose

theorem frobUr_root (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ) (h0 : 0 < m) (hm : ¬ l ∣ m) (hc : c ^ m = 1) :
    frobUr l c = c ^ l := (GlobalTheory.MemLoc.exists_frobenius_Kur l).choose_spec c m h0 hm hc

theorem frobUr_bijective : Function.Bijective (frobUr l) :=
  Algebra.IsAlgebraic.algHom_bijective _

def adjExt (x : Om l) : FinExt l :=
  ⟨IntermediateField.adjoin ℚ_[l] {x},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)⟩

theorem mem_adjExt (x : Om l) : x ∈ (adjExt x).1 := IntermediateField.mem_adjoin_simple_self _ x

def supExt (K K' : FinExt l) : FinExt l :=
  ⟨K.1 ⊔ K'.1, haveI := K.2; haveI := K'.2; IntermediateField.finiteDimensional_sup _ _⟩

def mapExt (g : GQ l) (K : FinExt l) : FinExt l :=
  ⟨K.1.map (g : Om l →ₐ[ℚ_[l]] Om l),
    haveI := K.2; (K.1.equivMap (g : Om l →ₐ[ℚ_[l]] Om l)).toLinearEquiv.finiteDimensional⟩

theorem mem_GK {K : FinExt l} {g : GQ l} : g ∈ GK K ↔ ∀ x ∈ K.1, g x = x :=
  IntermediateField.mem_fixingSubgroup_iff _ _

theorem conj_mem_GK {K : FinExt l} {g h : GQ l} (hh : h ∈ GK (mapExt g K)) : g⁻¹ * h * g ∈ GK K := by
  rw [mem_GK] at hh ⊢
  intro x hx
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hh (g x) ⟨x, hx, rfl⟩, ← AlgEquiv.mul_apply,
    inv_mul_cancel, AlgEquiv.one_apply]

variable (P : LocPrime l)

theorem phiB_algebraMap (c : ↥(MaximalUnramifiedExtension l)) :
    P.φB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (frobUr l c) := by
  have : P.φB.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B) =
      (IsScalarTower.toAlgHom ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B).comp (frobUr l) := by
    refine kur_algHom_ext fun c m h0 hm hc => ?_
    have hc' : (c : Om l) ^ m = 1 := congrArg Subtype.val hc
    let x : ↥(K0 (adjExt (c : Om l))) := ⟨c, mem_adjExt _, c.2⟩
    have hx : x ^ m = 1 := Subtype.ext hc'
    have h1 := (P.PD (adjExt (c : Om l))).φ_K₀ x
    rw [P.PD_φ] at h1
    have h2 : (((P.PD (adjExt (c : Om l))).σ x : ↥(K0 (adjExt (c : Om l)))) : Om l) = (c : Om l) ^ l := by
      refine eq_of_pow_eq_one_of_norm_sub_lt hm ?_ (by rw [← pow_mul, mul_comm, pow_mul, hc', one_pow])
        (P.PD_σ _ x (norm_eq_one_of_pow_eq_one h0 hc').le)
      have : (P.PD (adjExt (c : Om l))).σ x ^ m = 1 := by rw [← map_pow, hx, map_one]
      exact congrArg Subtype.val this
    rw [AlgHom.comp_apply, AlgHom.comp_apply, frobUr_root c m h0 hm hc]
    refine h1.trans ?_
    exact congrArg (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) (Subtype.ext h2)
  exact AlgHom.congr_fun this c

theorem phiSt_algebraMap (c : ↥(MaximalUnramifiedExtension l)) :
    phiSt P (algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c) = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) (frobUr l c) := by
  rw [Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, phiSt_C, phiB_algebraMap]

theorem actSt_algebraMap (g : GQ l) (c c' : ↥(MaximalUnramifiedExtension l)) (h : g (c : Om l) = (c' : Om l)) :
    actSt P g (algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c) = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c' := by
  rw [Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, actSt_C, P.actQ_Kur g c c' h]

end Unram

section Dst

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)
  (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
  (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

def onB : End ℚ_[l] (Bst P) →+* End LL (V ⊗[ℚ_[l]] Bst P) where
  toFun f := AlgebraTensorModule.map LinearMap.id f
  map_one' := by ext; simp
  map_mul' f g := by ext; simp
  map_zero' := by ext; simp
  map_add' f g := by ext; simp [tmul_add]

def phiV : End LL (V ⊗[ℚ_[l]] Bst P) := onB P LL V (phiSt P).toLinearMap

def monV : End LL (V ⊗[ℚ_[l]] Bst P) := onB P LL V (monSt P)

def mulV : ↥(MaximalUnramifiedExtension l) →+* End LL (V ⊗[ℚ_[l]] Bst P) :=
  (onB P LL V).comp (((Algebra.lmul ℚ_[l] (Bst P) : Bst P →ₐ[ℚ_[l]] End ℚ_[l] (Bst P)) :
    Bst P →+* End ℚ_[l] (Bst P)).comp (algebraMap ↥(MaximalUnramifiedExtension l) (Bst P)))

def crisIncl : V ⊗[ℚ_[l]] P.R.B →ₗ[LL] V ⊗[ℚ_[l]] Bst P :=
  AlgebraTensorModule.map LinearMap.id (CAlgHom : P.R.B →ₐ[ℚ_[l]] Bst P).toLinearMap

variable {LL V}

@[simp] theorem onB_tmul (f : End ℚ_[l] (Bst P)) (v : V) (b : Bst P) :
    onB P LL V f (v ⊗ₜ b) = v ⊗ₜ f b := rfl

@[simp] theorem phiV_tmul (v : V) (b : Bst P) : phiV P LL V (v ⊗ₜ b) = v ⊗ₜ phiSt P b := rfl

@[simp] theorem monV_tmul (v : V) (b : Bst P) : monV P LL V (v ⊗ₜ b) = v ⊗ₜ monSt P b := rfl

@[simp] theorem mulV_tmul (c : ↥(MaximalUnramifiedExtension l)) (v : V) (b : Bst P) :
    mulV P LL V c (v ⊗ₜ b) = v ⊗ₜ (algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c * b) := rfl

@[simp] theorem crisIncl_tmul (v : V) (b : P.R.B) : crisIncl P LL V (v ⊗ₜ b) = v ⊗ₜ C b := rfl

theorem end_ext {f g : End LL (V ⊗[ℚ_[l]] Bst P)} (h : ∀ v b, f (v ⊗ₜ b) = g (v ⊗ₜ b)) : f = g :=
  AlgebraTensorModule.ext h

theorem phiV_injective : Function.Injective (phiV P LL V) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := V) (phiSt P).toLinearMap (phiSt_injective P)

theorem crisIncl_injective : Function.Injective (crisIncl P LL V) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := V)
    (CAlgHom : P.R.B →ₐ[ℚ_[l]] Bst P).toLinearMap C_injective

theorem monV_phiV : monV P LL V * phiV P LL V = (l : LL) • (phiV P LL V * monV P LL V) :=
  end_ext P fun v b => by
    rw [End.mul_apply, phiV_tmul, monV_tmul, monSt_phiSt, LinearMap.smul_apply, End.mul_apply,
      monV_tmul, phiV_tmul, tmul_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem phiV_mulV (c : ↥(MaximalUnramifiedExtension l)) :
    phiV P LL V * mulV P LL V c = mulV P LL V (frobUr l c) * phiV P LL V :=
  end_ext P fun v b => by simp only [End.mul_apply, phiV_tmul, mulV_tmul, map_mul, phiSt_algebraMap]

theorem monV_mulV (c : ↥(MaximalUnramifiedExtension l)) : monV P LL V * mulV P LL V c = mulV P LL V c * monV P LL V :=
  end_ext P fun v b => by
    simp only [End.mul_apply, monV_tmul, mulV_tmul, Polynomial.algebraMap_apply, monSt_C_mul]

theorem exists_monV_pow_eq_zero (x : V ⊗[ℚ_[l]] Bst P) : ∃ n : ℕ, (monV P LL V ^ n) x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul v b =>
    obtain ⟨n, hn⟩ := exists_monSt_pow_eq_zero P b
    exact ⟨n, by rw [monV, ← map_pow, onB_tmul, hn, tmul_zero]⟩
  | add x y hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    rw [map_add]
    nth_rewrite 1 [add_comm m n]
    rw [pow_add, pow_add, End.mul_apply, End.mul_apply, hm, hn, map_zero, map_zero, add_zero]

variable {K : FinExt l} (ρ : Representation LL ↥(GK K) V)

def stRep : Representation LL ↥(GK K) (V ⊗[ℚ_[l]] Bst P) where
  toFun g := AlgebraTensorModule.map (ρ g) (actSt P (g : GQ l)).toLinearMap
  map_one' := by ext; simp
  map_mul' g h := end_ext P fun v b => by simp [AlgHom.mul_apply]

@[simp] theorem stRep_tmul (g : ↥(GK K)) (v : V) (b : Bst P) :
    stRep P ρ g (v ⊗ₜ b) = ρ g v ⊗ₜ actSt P (g : GQ l) b := rfl

theorem stRep_crisIncl (g : ↥(GK K)) (x : V ⊗[ℚ_[l]] P.R.B) :
    stRep P ρ g (crisIncl P LL V x) = crisIncl P LL V (actVB (P.PD K) ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, P.PD_actB]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem phiV_stRep (g : ↥(GK K)) : phiV P LL V * stRep P ρ g = stRep P ρ g * phiV P LL V :=
  end_ext P fun v b => by simp only [End.mul_apply, phiV_tmul, stRep_tmul, phiSt_actSt]

theorem monV_stRep (g : ↥(GK K)) : monV P LL V * stRep P ρ g = stRep P ρ g * monV P LL V :=
  end_ext P fun v b => by simp only [End.mul_apply, monV_tmul, stRep_tmul, monSt_actSt]

theorem stRep_mulV (g : ↥(GK K)) (c c' : ↥(MaximalUnramifiedExtension l)) (h : (g : GQ l) (c : Om l) = (c' : Om l)) :
    stRep P ρ g * mulV P LL V c = mulV P LL V c' * stRep P ρ g :=
  end_ext P fun v b => by
    simp only [End.mul_apply, stRep_tmul, mulV_tmul, map_mul, actSt_algebraMap P _ c c' h]

def Dst : Submodule LL (V ⊗[ℚ_[l]] Bst P) := ⨅ g, LinearMap.ker (stRep P ρ g - LinearMap.id)

theorem mem_Dst {x : V ⊗[ℚ_[l]] Bst P} : x ∈ Dst P ρ ↔ ∀ g, stRep P ρ g x = x := by
  simp [Dst, sub_eq_zero]

def IsSst : Prop := finrank LL ↥(Dst P ρ) = finrank ℚ_[l] ↥(K0 K) * finrank LL V

abbrev resTo {K' : FinExt l} (h : K.1 ≤ K'.1) : Representation LL ↥(GK K') V :=
  ρ.comp (Subgroup.inclusion (GK_le h))

theorem mem_Dst_resTo {K' : FinExt l} (h : K.1 ≤ K'.1) {x : V ⊗[ℚ_[l]] Bst P} :
    x ∈ Dst P (resTo ρ h) ↔ ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → stRep P ρ g x = x := by
  rw [mem_Dst]
  exact ⟨fun hx g hg => hx ⟨g, hg⟩, fun hx g => hx ⟨g, GK_le h g.2⟩ g.2⟩

def Dpst : Submodule LL (V ⊗[ℚ_[l]] Bst P) where
  carrier := {x | ∃ (K' : FinExt l) (h : K.1 ≤ K'.1), x ∈ Dst P (resTo ρ h)}
  zero_mem' := ⟨K, le_rfl, zero_mem _⟩
  add_mem' := by
    rintro x y ⟨K₁, h₁, hx⟩ ⟨K₂, h₂, hy⟩
    rw [mem_Dst_resTo] at hx hy
    refine ⟨supExt K₁ K₂, h₁.trans le_sup_left, (mem_Dst_resTo P ρ _).mpr fun g hg => ?_⟩
    rw [map_add, hx g (GK_le (K' := supExt K₁ K₂) le_sup_left hg),
      hy g (GK_le (K' := supExt K₁ K₂) le_sup_right hg)]
  smul_mem' := by
    rintro c x ⟨K₁, h₁, hx⟩
    exact ⟨K₁, h₁, Submodule.smul_mem _ c hx⟩

theorem mem_Dpst {x : V ⊗[ℚ_[l]] Bst P} : x ∈ Dpst P ρ ↔
    ∃ K' : FinExt l, ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → stRep P ρ g x = x := by
  constructor
  · rintro ⟨K', h, hx⟩
    exact ⟨K', (mem_Dst_resTo P ρ h).mp hx⟩
  · rintro ⟨K', hx⟩
    exact ⟨supExt K K', le_sup_left, (mem_Dst_resTo P ρ _).mpr fun g hg =>
      hx g (GK_le (K' := supExt K K') le_sup_right hg)⟩

theorem Dst_resTo_le {K' : FinExt l} (h : K.1 ≤ K'.1) : Dst P (resTo ρ h) ≤ Dpst P ρ :=
  fun _ hx => ⟨K', h, hx⟩

theorem Dpst_resTo {K' : FinExt l} (h : K.1 ≤ K'.1) : Dpst P (resTo ρ h) = Dpst P ρ := by
  ext x
  rw [mem_Dpst, mem_Dpst]
  constructor
  · rintro ⟨K₁, hx⟩
    exact ⟨supExt K' K₁, fun g hg => hx ⟨g, GK_le (K' := supExt K' K₁) le_sup_left hg⟩
      (GK_le (K' := supExt K' K₁) le_sup_right hg)⟩
  · rintro ⟨K₁, hx⟩
    exact ⟨K₁, fun g hg => hx ⟨g, GK_le h g.2⟩ hg⟩

theorem mem_Dpst_of_commute {T : End LL (V ⊗[ℚ_[l]] Bst P)}
    (hT : ∀ g, T * stRep P ρ g = stRep P ρ g * T) (x : V ⊗[ℚ_[l]] Bst P) (hx : x ∈ Dpst P ρ) :
    T x ∈ Dpst P ρ := by
  obtain ⟨K', hx⟩ := (mem_Dpst P ρ).mp hx
  refine (mem_Dpst P ρ).mpr ⟨K', fun g hg => ?_⟩
  rw [← End.mul_apply, ← hT, End.mul_apply, hx g hg]

theorem stRep_mem_Dpst (g : ↥(GK K)) (x : V ⊗[ℚ_[l]] Bst P) (hx : x ∈ Dpst P ρ) :
    stRep P ρ g x ∈ Dpst P ρ := by
  obtain ⟨K', hx⟩ := (mem_Dpst P ρ).mp hx
  refine (mem_Dpst P ρ).mpr ⟨mapExt g K', fun h hh => ?_⟩
  have := congrArg (stRep P ρ g) (hx (g⁻¹ * h * g) (conj_mem_GK hh))
  rwa [← End.mul_apply, ← map_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, map_mul,
    End.mul_apply] at this

theorem mulV_mem_Dpst (c : ↥(MaximalUnramifiedExtension l)) (x : V ⊗[ℚ_[l]] Bst P) (hx : x ∈ Dpst P ρ) :
    mulV P LL V c x ∈ Dpst P ρ := by
  obtain ⟨K', hx⟩ := (mem_Dpst P ρ).mp hx
  refine (mem_Dpst P ρ).mpr ⟨supExt K' (adjExt (c : Om l)), fun g hg => ?_⟩
  have h1 : (g : GQ l) (c : Om l) = c :=
    mem_GK.mp (GK_le (K := adjExt (c : Om l)) le_sup_right hg) _ (mem_adjExt _)
  rw [← End.mul_apply, stRep_mulV P ρ g c c h1, End.mul_apply, hx g (GK_le (K := K') le_sup_left hg)]

def phiD : End LL ↥(Dpst P ρ) := (phiV P LL V).restrict (mem_Dpst_of_commute P ρ (phiV_stRep P ρ))

def monD : End LL ↥(Dpst P ρ) := (monV P LL V).restrict (mem_Dpst_of_commute P ρ (monV_stRep P ρ))

def actD : Representation LL ↥(GK K) ↥(Dpst P ρ) where
  toFun g := (stRep P ρ g).restrict (stRep_mem_Dpst P ρ g)
  map_one' := LinearMap.ext fun x => Subtype.ext (by simp)
  map_mul' g h := LinearMap.ext fun x => Subtype.ext (by simp)

def mulD : ↥(MaximalUnramifiedExtension l) →+* End LL ↥(Dpst P ρ) where
  toFun c := (mulV P LL V c).restrict (mulV_mem_Dpst P ρ c)
  map_one' := LinearMap.ext fun x => Subtype.ext (by simp)
  map_mul' g h := LinearMap.ext fun x => Subtype.ext (by simp)
  map_zero' := LinearMap.ext fun x => Subtype.ext (by simp)
  map_add' g h := LinearMap.ext fun x => Subtype.ext (by simp)

@[simp] theorem coe_phiD (x : ↥(Dpst P ρ)) : (phiD P ρ x : V ⊗[ℚ_[l]] Bst P) = phiV P LL V x := rfl

@[simp] theorem coe_monD (x : ↥(Dpst P ρ)) : (monD P ρ x : V ⊗[ℚ_[l]] Bst P) = monV P LL V x := rfl

@[simp] theorem coe_actD (g : ↥(GK K)) (x : ↥(Dpst P ρ)) :
    (actD P ρ g x : V ⊗[ℚ_[l]] Bst P) = stRep P ρ g x := rfl

@[simp] theorem coe_mulD (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρ)) :
    (mulD P ρ c x : V ⊗[ℚ_[l]] Bst P) = mulV P LL V c x := rfl

theorem phiD_actD (g : ↥(GK K)) : phiD P ρ * actD P ρ g = actD P ρ g * phiD P ρ :=
  LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (phiV_stRep P ρ g) x)

theorem monD_actD (g : ↥(GK K)) : monD P ρ * actD P ρ g = actD P ρ g * monD P ρ :=
  LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (monV_stRep P ρ g) x)

theorem monD_phiD : monD P ρ * phiD P ρ = (l : LL) • (phiD P ρ * monD P ρ) :=
  LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (monV_phiV P) x.1)

theorem phiD_mulD (c : ↥(MaximalUnramifiedExtension l)) : phiD P ρ * mulD P ρ c = mulD P ρ (frobUr l c) * phiD P ρ :=
  LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (phiV_mulV P c) x.1)

theorem monD_mulD (c : ↥(MaximalUnramifiedExtension l)) : monD P ρ * mulD P ρ c = mulD P ρ c * monD P ρ :=
  LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (monV_mulV P c) x.1)

theorem actD_mulD (g : ↥(GK K)) (c c' : ↥(MaximalUnramifiedExtension l)) (h : (g : GQ l) (c : Om l) = (c' : Om l)) :
    actD P ρ g * mulD P ρ c = mulD P ρ c' * actD P ρ g :=
  LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (stRep_mulV P ρ g c c' h) x.1)

theorem phiD_injective : Function.Injective (phiD P ρ) :=
  fun _ _ h => Subtype.ext (phiV_injective P (congrArg Subtype.val h))

def DpstUr : Type := ↥(Dpst P ρ)

instance : AddCommGroup (DpstUr P ρ) := inferInstanceAs (AddCommGroup ↥(Dpst P ρ))

instance : Module ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) := Module.compHom ↥(Dpst P ρ) (mulD P ρ)

def toUr : ↥(Dpst P ρ) ≃+ DpstUr P ρ := AddEquiv.refl _

theorem smul_toUr (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρ)) : c • toUr P ρ x = toUr P ρ (mulD P ρ c x) := rfl

def urEnd (T : End LL ↥(Dpst P ρ)) (hT : ∀ c, T * mulD P ρ c = mulD P ρ c * T) :
    End ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) where
  toFun x := toUr P ρ (T ((toUr P ρ).symm x))
  map_add' x y := by simp only [map_add]
  map_smul' c x := LinearMap.congr_fun (hT c) x

def IsPst : Prop := Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) = Module.rank ℚ_[l] V

variable [FiniteDimensional ℚ_[l] V]

theorem isPst_iff : IsPst P ρ ↔ FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) ∧
    finrank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) = finrank ℚ_[l] V := by
  constructor
  · intro h
    refine ⟨Module.rank_lt_aleph0_iff.mp (by rw [h]; exact Module.rank_lt_aleph0 _ _), ?_⟩
    rw [finrank, finrank, h]
  · rintro ⟨h1, h2⟩
    rw [IsPst, ← finrank_eq_rank, ← finrank_eq_rank, h2]

variable {P ρ}

theorem IsPst.finiteDimensional (h : IsPst P ρ) : FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) :=
  ((isPst_iff P ρ).mp h).1

omit [FiniteDimensional ℚ_[l] V] in

theorem phiD_bijective [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] : Function.Bijective (phiD P ρ) := by
  refine ⟨phiD_injective P ρ, ?_⟩
  let j : DpstUr P ρ →+ DpstUr P ρ := (phiD P ρ).toAddMonoidHom
  have hj : ∀ (c : ↥(MaximalUnramifiedExtension l)) (x : DpstUr P ρ), j (c • x) = frobUr l c • j x :=
    fun c x => LinearMap.congr_fun (phiD_mulD P ρ c) x
  have hli := (finBasis ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)).linearIndependent.map_of_surjective_injective
    (frobUr l) j frobUr_bijective.2
    (fun x hx => phiD_injective P ρ (hx.trans (map_zero (phiD P ρ)).symm)) hj
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by simp)
  intro y
  have hy : toUr P ρ y ∈ Submodule.span ↥(MaximalUnramifiedExtension l) (Set.range (j ∘ finBasis ↥(MaximalUnramifiedExtension l) (DpstUr P ρ))) := by
    rw [hsp]; trivial
  have key : ∀ z ∈ Submodule.span ↥(MaximalUnramifiedExtension l) (Set.range (j ∘ finBasis ↥(MaximalUnramifiedExtension l) (DpstUr P ρ))),
      ∃ x, j x = z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact ⟨_, rfl⟩
    | zero => exact ⟨0, map_zero _⟩
    | add a b _ _ ha hb =>
      obtain ⟨a, rfl⟩ := ha; obtain ⟨b, rfl⟩ := hb; exact ⟨a + b, map_add _ _ _⟩
    | smul c a _ ha =>
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨c, rfl⟩ := frobUr_bijective.2 c
      exact ⟨c • a, hj c a⟩
  exact key _ hy

omit [FiniteDimensional ℚ_[l] V] in

theorem isNilpotent_monD [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] : IsNilpotent (monD P ρ) := by
  have hp : ∀ (n : ℕ) (x : ↥(Dpst P ρ)), (urEnd P ρ (monD P ρ) (monD_mulD P ρ) ^ n) (toUr P ρ x) =
      toUr P ρ ((monD P ρ ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [pow_succ, pow_succ, End.mul_apply, End.mul_apply, ← ih]; rfl
  have hc : ∀ (n : ℕ) (x : ↥(Dpst P ρ)),
      (((monD P ρ ^ n) x : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) = (monV P LL V ^ n) x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [pow_succ, pow_succ, End.mul_apply, End.mul_apply, ih]; rfl
  obtain ⟨n, hn⟩ : IsNilpotent (urEnd P ρ (monD P ρ) (monD_mulD P ρ)) := by
    rw [Module.End.isNilpotent_iff_of_finite]
    intro x
    obtain ⟨x, rfl⟩ := (toUr P ρ).surjective x
    obtain ⟨n, hn⟩ := exists_monV_pow_eq_zero P (LL := LL) x.1
    exact ⟨n, by rw [hp, show (monD P ρ ^ n) x = 0 from Subtype.ext ((hc n x).trans hn), map_zero]⟩
  exact ⟨n, LinearMap.ext fun x => (toUr P ρ).injective (by rw [← hp, hn]; rfl)⟩

omit [FiniteDimensional ℚ_[l] V] in

theorem exists_actD_eq_one [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] : ∃ K' : FinExt l,
    ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → (∀ c, actD P ρ g * mulD P ρ c = mulD P ρ c * actD P ρ g) →
      actD P ρ g = 1 := by
  let b := finBasis ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)
  choose F hF using fun i => (mem_Dpst P ρ).mp ((toUr P ρ).symm (b i)).2
  have := fun i => (F i).2
  refine ⟨⟨⨆ i, (F i).1, inferInstance⟩, fun g hg hc => ?_⟩
  have h1 : urEnd P ρ (actD P ρ g) hc = 1 := b.ext fun i =>
    Subtype.ext (hF i g (GK_le (K := F i) (le_iSup (fun i => (F i).1) i) hg))
  exact LinearMap.ext fun x => LinearMap.congr_fun h1 (toUr P ρ x)

end Dst

end GlobalTheory.Pst
