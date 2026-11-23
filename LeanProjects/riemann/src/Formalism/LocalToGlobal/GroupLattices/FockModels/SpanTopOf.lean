import Formalism.LocalToGlobal.GroupLattices.FockModels.SwRowGenMonomial
import Formalism.LocalToGlobal.GroupLattices.FockModels.ElementaryDivisorBasis
import Formalism.SharpRestriction.GrowthBounds.GLWeightTheory

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

section Rep

variable (K : Type) [Field K] (k : ℕ) (ν : Fin k → ℕ)

abbrev PK := MvPolynomial (Fin k × Fin k) K
abbrev VK := ↥(dualWeyl K k k ν)

def EV : GLOps k K (VK K k ν) := fun a b =>
  (DL K a b).restrict (fun x hx => by
    rw [DL_apply, sw_Dop_rowDiv]; exact rowDivStable K k k ν a b 1 x hx)

variable {K k ν}

def Rel (u : Module.End K (VK K k ν)) (U : Module.End K (PK K k)) : Prop :=
  ∀ x : VK K k ν, ((u x : VK K k ν) : PK K k) = U x

theorem rel_EV (a b : Fin k) : Rel (EV K k ν a b) (DL K a b) := fun _ => rfl
theorem rel_one : Rel (1 : Module.End K (VK K k ν)) 1 := fun _ => rfl
theorem rel_zero : Rel (0 : Module.End K (VK K k ν)) 0 := fun _ => rfl

theorem rel_mul {u u' : Module.End K (VK K k ν)} {U U' : Module.End K (PK K k)} (h1 : Rel u U)
    (h2 : Rel u' U') : Rel (u * u') (U * U') := fun x => by
  rw [Module.End.mul_apply, Module.End.mul_apply, h1, h2]

theorem rel_sub {u u' : Module.End K (VK K k ν)} {U U' : Module.End K (PK K k)} (h1 : Rel u U)
    (h2 : Rel u' U') : Rel (u - u') (U - U') := fun x => by
  rw [LinearMap.sub_apply, LinearMap.sub_apply, AddSubgroupClass.coe_sub, h1, h2]

theorem rel_smul (c : K) {u : Module.End K (VK K k ν)} {U : Module.End K (PK K k)} (h1 : Rel u U) :
    Rel (c • u) (c • U) := fun x => by
  rw [LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_smul, h1]

theorem rel_pow {u : Module.End K (VK K k ν)} {U : Module.End K (PK K k)} (h1 : Rel u U) (j : ℕ) :
    Rel (u ^ j) (U ^ j) := by
  induction j with
  | zero => rw [pow_zero, pow_zero]; exact rel_one
  | succ j ih => rw [pow_succ, pow_succ]; exact rel_mul ih h1

theorem rel_list {I : Type} (l : List I) (f : I → Module.End K (VK K k ν)) (g : I → Module.End K (PK K k))
    (h : ∀ i, Rel (f i) (g i)) : Rel (l.map f).prod (l.map g).prod := by
  induction l with
  | nil => exact rel_one
  | cons i l ih => rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons]; exact rel_mul (h i) ih

theorem rel_inj {u u' : Module.End K (VK K k ν)} {U : Module.End K (PK K k)} (h1 : Rel u U) (h2 : Rel u' U) :
    u = u' := LinearMap.ext fun x => Subtype.ext ((h1 x).trans (h2 x).symm)

theorem rel_divPow [CharZero K] (a b : Fin k) (hab : a ≠ b) (j : ℕ) :
    Rel (divPowE (EV K k ν) a b j) (rowDivL K a b j) := by
  intro x
  have h1 : Rel (divPowE (EV K k ν) a b j) (((j.factorial : K)⁻¹) • (DL K a b) ^ j) :=
    rel_smul _ (rel_pow (rel_EV a b) j)
  rw [h1 x, LinearMap.smul_apply, ← sw_pow_ne K a b hab, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast j.factorial_ne_zero), one_smul]
  rfl

theorem rel_binom [CharZero K] (a : Fin k) (j : ℕ) :
    Rel (binomE (EV K k ν) a j) (rowDivL K a a j) := by
  intro x
  have h1 : Rel (binomE (EV K k ν) a j) (((j.factorial : K)⁻¹) •
      ((List.range j).map fun i : ℕ => DL K (n := k) a a - (i : K) • (1 : Module.End K (PK K k))).prod) :=
    rel_smul _ (rel_list _ _ _ fun i => rel_sub (rel_EV a a) (rel_smul _ rel_one))
  rw [h1 x, LinearMap.smul_apply, ← sw_pow_eq K a, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast j.factorial_ne_zero), one_smul]
  rfl

theorem rel_mon [CharZero K] (u : Module.End K (VK K k ν)) (hu : u ∈ UZmon (EV K k ν)) :
    ∃ w, ∀ x : VK K k ν, ((u x : VK K k ν) : PK K k) = applyWord K w x := by
  unfold UZmon at hu
  induction hu using Submonoid.closure_induction with
  | mem u hu =>
    rcases hu with ⟨a, b, j, hab, rfl⟩ | ⟨a, j, rfl⟩
    · exact ⟨[(a, b, j)], fun x => rel_divPow a b hab j x⟩
    · exact ⟨[(a, a, j)], fun x => rel_binom a j x⟩
  | one => exact ⟨[], fun x => rfl⟩
  | mul u v _ _ hu hv =>
    obtain ⟨w1, h1⟩ := hu
    obtain ⟨w2, h2⟩ := hv
    refine ⟨w1 ++ w2, fun x => ?_⟩
    rw [Module.End.mul_apply, h1, h2]
    simp [applyWord, List.foldr_append]

theorem wt_mem (x : VK K k ν) (μ : Fin k → ℕ) (hx : IsWeightedHomogeneous (rowW k k) (x : PK K k) μ) :
    x ∈ weightSp (EV K k ν) (fun a => (μ a : ℤ)) := by
  unfold weightSp
  rw [Submodule.mem_iInf]
  intro a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
  apply Subtype.ext
  rw [Submodule.coe_smul, Int.cast_natCast, ← sw_euler K a μ _ hx]
  rfl

theorem fin_VK : FiniteDimensional K (VK K k ν) := by
  obtain ⟨b, hb, -⟩ := sSBasis K k k ν
  have : Finite ↥(ssIdx k k ν) := (sSIdxFinite k k ν).to_subtype
  have h := FiniteDimensional.span_of_finite K (Set.finite_range b)
  rw [hb.2.1] at h
  exact h

theorem span_top_of {I : Type} (f : I → VK K k ν)
    (hf : Submodule.span K (Set.range fun i => (f i : PK K k)) = dualWeyl K k k ν) :
    Submodule.span K (Set.range f) = ⊤ := by
  rw [← comap_span_coe (O := K) (Kf := K) (dualWeyl K k k ν) f, hf, eq_top_iff]
  intro x _
  exact x.2

theorem isGLRep : IsGLRep (EV K k ν) := by
  have := fin_VK (K := K) (k := k) (ν := ν)
  refine ⟨fun a b c d => ?_, fun x => ⟨⊤, inferInstance, trivial, fun _ _ _ _ => trivial⟩, ?_⟩
  · apply rel_inj (U := DL K a b * DL K c d - DL K c d * DL K a b)
    · exact rel_sub (rel_mul (rel_EV a b) (rel_EV c d)) (rel_mul (rel_EV c d) (rel_EV a b))
    · rw [sw_rel]
      refine rel_sub ?_ ?_ <;> split_ifs <;> first | exact rel_EV _ _ | exact rel_zero
  · obtain ⟨b, hb, -⟩ := sSBasis K k k ν
    have hm : ∀ i, b i ∈ dualWeyl K k k ν := fun i => by
      rw [← hb.2.1]; exact Submodule.subset_span ⟨i, rfl⟩
    rw [eq_top_iff, ← span_top_of (fun i => (⟨b i, hm i⟩ : VK K k ν)) hb.2.1, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.mem_iSup_of_mem _ (wt_mem _ (rowWt i.1) (hb.2.2 i))

variable (K k ν)

def hwV (hν : Antitone ν) : VK K k ν := ⟨hw K le_rfl ν, hwMem K k k le_rfl ν hν⟩

variable {K k ν}

theorem rowNu_self : rowNu (r := k) ν = ν := by
  funext a
  simp [rowNu]

theorem isHWV (hν : Antitone ν) : IsHWV (EV K k ν) (fun a => (ν a : ℤ)) (hwV K k ν hν) := by
  refine ⟨fun h => hwNe K k k le_rfl ν (congrArg Subtype.val h), ?_, fun a b hab => ?_⟩
  · have := wt_mem (hwV K k ν hν) (rowNu (r := k) ν) (hwRowWeight K k k le_rfl ν hν)
    rwa [rowNu_self] at this
  · apply Subtype.ext
    show Dop K a b (hw K le_rfl ν) = 0
    rw [sw_Dop_rowDiv]
    exact hwRaise K k k le_rfl ν a b 1 hab le_rfl

theorem stab_list {V : Type} [AddCommGroup V] [Module K V] (T : Submodule K V) (l : List (Module.End K V))
    (h : ∀ g ∈ l, ∀ x ∈ T, g x ∈ T) : ∀ x ∈ T, l.prod x ∈ T := by
  induction l with
  | nil => intro x hx; simpa using hx
  | cons g l ih =>
    intro x hx
    rw [List.prod_cons, Module.End.mul_apply]
    exact h g (List.mem_cons_self) _ (ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) x hx)

theorem gen_top [CharZero K] (hν : Antitone ν) :
    Submodule.span K {x | ∃ u ∈ Umon (EV K k ν), x = u (hwV K k ν hν)} = ⊤ := by
  set T := Submodule.span K {x | ∃ u ∈ Umon (EV K k ν), x = u (hwV K k ν hν)} with hT
  have hE : ∀ a b, ∀ x ∈ T, EV K k ν a b x ∈ T := by
    intro a b
    have h1 : T ≤ T.comap (EV K k ν a b) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, hu, rfl⟩
      exact Submodule.subset_span ⟨EV K k ν a b * u,
        Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu, rfl⟩
    exact fun x hx => h1 hx
  have hdiv : ∀ a b j, ∀ x ∈ T, divPowE (EV K k ν) a b j x ∈ T := by
    intro a b j x hx
    unfold divPowE
    rw [LinearMap.smul_apply, ← List.prod_replicate]
    exact Submodule.smul_mem _ _ (stab_list T _ (fun g hg => by
      rw [List.eq_of_mem_replicate hg]; exact hE a b) x hx)
  have hbin : ∀ a j, ∀ x ∈ T, binomE (EV K k ν) a j x ∈ T := by
    intro a j x hx
    unfold binomE
    rw [LinearMap.smul_apply]
    refine Submodule.smul_mem _ _ (stab_list T _ (fun g hg => ?_) x hx)
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    intro y hy
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact Submodule.sub_mem _ (hE a a y hy) (Submodule.smul_mem _ _ hy)
  have hw : ∀ w, ∃ y ∈ T, (y : PK K k) = applyWord K w (hw K le_rfl ν) := by
    intro w
    induction w with
    | nil => exact ⟨hwV K k ν hν, Submodule.subset_span ⟨1, Submonoid.one_mem _, rfl⟩, rfl⟩
    | cons c w ih =>
      obtain ⟨a, b, j⟩ := c
      obtain ⟨y, hy, hyw⟩ := ih
      by_cases hab : a = b
      · subst hab
        refine ⟨binomE (EV K k ν) a j y, hbin a j y hy, ?_⟩
        rw [rel_binom a j y, hyw]
        rfl
      · refine ⟨divPowE (EV K k ν) a b j y, hdiv a b j y hy, ?_⟩
        rw [rel_divPow a b hab j y, hyw]
        rfl
  choose f hfT hf using hw
  have h2 : Submodule.span K (Set.range fun w => (f w : PK K k)) = dualWeyl K k k ν := by
    refine Eq.trans ?_ (sw_weyl_eq K k k le_rfl ν hν)
    unfold weyl
    congr 2
    funext w
    exact hf w
  rw [eq_top_iff, ← span_top_of f h2, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  exact hfT w

theorem isIrrHW [CharZero K] (hν : Antitone ν) :
    IsIrrHW (EV K k ν) (fun a => (ν a : ℤ)) (hwV K k ν hν) :=
  ⟨isGLRep, fun a b hab => by
    show ((ν b : ℕ) : ℤ) ≤ ((ν a : ℕ) : ℤ)
    exact_mod_cast hν hab, isHWV hν, gen_top hν⟩

end Rep

end Formalism.L2.G.Model
