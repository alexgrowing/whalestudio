import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars
import Development.AbelianVarietyTheory.Definitions.Divisors.CupPair

noncomputable def UpperTheory.Reformulated.B.KoszulComplexHomotopy.Stab :
    {S E : Type} →
      [inst : CommRing S] →
        [inst_1 : Algebra ℂ S] →
          [inst_2 : AddCommGroup E] →
            [inst_3 : _root_.Module ℂ E] → (S →ₐ[ℂ] Module.End ℂ E) → Subalgebra ℂ S → Submodule ℂ E → Prop :=
    fun {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [_root_.Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E)
        (R : Subalgebra ℂ S) (M : Submodule ℂ E) ↦
      ∀ r ∈ R, ∀ m ∈ M, ((act : S → Module.End ℂ E) r : E → E) m ∈ M

noncomputable def UpperTheory.Reformulated.B.KoszulComplexHomotopy.wd :
    {k : Type} →
      [inst : Field k] →
        {ι : Type} →
          [LinearOrder ι] →
            {E : Type} →
              [inst_2 : AddCommGroup E] →
                [inst_3 : _root_.Module k E] → (ι → Module.End k E) → (Finset ι → E) →ₗ[k] Finset ι → E :=
    fun {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [_root_.Module k E]
        (w : ι → Module.End k E) ↦
      LinearMap.pi fun (t : Finset ι) ↦ ∑ i ∈ t, GlobalTheory.cubeSign t i • w i ∘ₗ LinearMap.proj (t.erase i)

noncomputable def UpperTheory.Reformulated.B.KoszulComplexHomotopy.acx :
    {k : Type} →
      [inst : Field k] →
        {ι : Type} →
          [LinearOrder ι] →
            {E : Type} →
              [inst_2 : AddCommGroup E] →
                [inst_3 : _root_.Module k E] →
                  (Finset ι → Submodule k E) → (ι → Module.End k E) → GlobalTheory.PD.Cx k (Finset ι → E) :=
    fun {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [_root_.Module k E]
        (A : Finset ι → Submodule k E) (w : ι → Module.End k E) ↦
      { C := fun (n : ℤ) ↦ Submodule.pi Set.univ fun (s : Finset ι) ↦ if (↑s.card : ℤ) = n then A s else ⊥,
        D := UpperTheory.Reformulated.B.KoszulComplexHomotopy.wd w : GlobalTheory.PD.Cx k (Finset ι → E) }

noncomputable def UpperTheory.Reformulated.B.KoszulComplexHomotopy.kos :
    {S E : Type} →
      [inst : CommRing S] →
        [inst_1 : Algebra ℂ S] →
          [inst_2 : AddCommGroup E] →
            [inst_3 : _root_.Module ℂ E] →
              (S →ₐ[ℂ] Module.End ℂ E) → {κ : Type} → [LinearOrder κ] → Submodule ℂ E → (κ → S) → GlobalTheory.PD.Cx ℂ (Finset κ → E) :=
    fun {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [_root_.Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E)
        {κ : Type} [LinearOrder κ] (M : Submodule ℂ E) (r : κ → S) ↦
      UpperTheory.Reformulated.B.KoszulComplexHomotopy.acx (fun (x : Finset κ) ↦ M) fun (l : κ) ↦ (act : S → Module.End ℂ E) (r l)

noncomputable def UpperTheory.Reformulated.B.KoszulComplexHomotopy.InSp :
    {S κ : Type} → [inst : CommRing S] → [inst_1 : Algebra ℂ S] → [Fintype κ] → Subalgebra ℂ S → (κ → S) → S → Prop :=
    fun {S κ : Type} [CommRing S] [Algebra ℂ S] [Fintype κ] (R : Subalgebra ℂ S) (r : κ → S) (g : S) ↦
      ∃ (a : κ → S), (∀ (l : κ), a l ∈ R) ∧ g = ∑ l : κ, a l * r l

noncomputable def UpperTheory.Reformulated.B.KoszulComplexHomotopy.Htpy :
    Prop :=
    ∀ (S E : Type) [inst : CommRing S] [inst_1 : Algebra ℂ S] [inst_2 : AddCommGroup E] [inst_3 : _root_.Module ℂ E]
      (act : S →ₐ[ℂ] Module.End ℂ E) (κ : Type) [inst_4 : LinearOrder κ] [inst_5 : Fintype κ] (R : Subalgebra ℂ S)
      (M : Submodule ℂ E) (r : κ → S),
      UpperTheory.Reformulated.B.KoszulComplexHomotopy.Stab act R M →
        ∀ (n : ℤ),
          ∀ c ∈ (UpperTheory.Reformulated.B.KoszulComplexHomotopy.kos act M r).Z n,
            ∀ (g : S),
              UpperTheory.Reformulated.B.KoszulComplexHomotopy.InSp R r g →
                (fun (L : Finset κ) ↦ ((act : S → Module.End ℂ E) g : E → E) (c L)) ∈ (UpperTheory.Reformulated.B.KoszulComplexHomotopy.kos act M r).B n

noncomputable def UpperTheory.Reformulated.B.KoszulComplexHomotopy.KE :
    {M : Type} → [inst : AddCommGroup M] → [inst_1 : _root_.Module ℂ M] → GlobalTheory.PD.Cx ℂ M → ℤ → Prop :=
    fun {M : Type} [AddCommGroup M] [_root_.Module ℂ M] (C : GlobalTheory.PD.Cx ℂ M) (d : ℤ) ↦ ∀ m < d, C.Z m ≤ C.B m

noncomputable def UpperTheory.Reformulated.B.KoszulComplexHomotopy.KoszulExactBelowLengthOfWeaklyRegular :
    Prop :=
    ∀ (d : ℕ) (R N : Type) [inst : CommRing R] [inst_1 : Algebra ℂ R] [inst_2 : AddCommGroup N] [inst_3 : _root_.Module R N]
      [inst_4 : _root_.Module ℂ N] [inst_5 : IsScalarTower ℂ R N] (κ : Type) [inst_6 : LinearOrder κ] [inst_7 : Fintype κ]
      (r : κ → R) (f : List R),
      f.length = d →
        RingTheory.Sequence.IsWeaklyRegular N f →
          (∀ g ∈ f, UpperTheory.Reformulated.B.KoszulComplexHomotopy.InSp ⊤ r g) →
            UpperTheory.Reformulated.B.KoszulComplexHomotopy.KE (UpperTheory.Reformulated.B.KoszulComplexHomotopy.kos (Algebra.lsmul ℂ ℂ N) ⊤ r) (↑d : ℤ)

namespace UpperTheory.Reformulated.B.KoszulComplexHomotopy

section Helpers

variable {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {κ : Type} [LinearOrder κ]

private def dd (r : κ → R) (c : Finset κ → N) : Finset κ → N :=
  fun t => ∑ i ∈ t, GlobalTheory.cubeSign t i • r i • c (t.erase i)

private theorem dd_map {N' : Type} [AddCommGroup N'] [Module R N'] (φ : N →ₗ[R] N') (r : κ → R)
    (c : Finset κ → N) (t : Finset κ) : dd r (fun s => φ (c s)) t = φ (dd r c t) := by
  simp [dd, map_sum]

private theorem dd_add (r : κ → R) (a b : Finset κ → N) (t : Finset κ) :
    dd r (fun s => a s + b s) t = dd r a t + dd r b t := by
  simp [dd, Finset.sum_add_distrib]

private theorem dd_deg (r : κ → R) (c : Finset κ → N) (n : ℤ)
    (hc : ∀ s : Finset κ, (s.card : ℤ) ≠ n - 1 → c s = 0) (t : Finset κ) (ht : (t.card : ℤ) ≠ n) :
    dd r c t = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  have h := Finset.card_erase_add_one hi
  rw [hc _ (by omega), smul_zero, smul_zero]

private theorem dd_dd [Module ℂ N] (r : κ → R) (c : Finset κ → N) (t : Finset κ) :
    dd r (dd r c) t = 0 := by
  let F : κ → κ → N := fun i j =>
    if j ≠ i then (GlobalTheory.cubeSign t i * GlobalTheory.cubeSign (t.erase i) j) • (r i * r j) • c ((t.erase i).erase j)
    else 0
  have h1 : dd r (dd r c) t = ∑ i ∈ t, ∑ j ∈ t, F i j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [F]
    rw [← Finset.sum_filter, Finset.filter_ne', dd, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul, mul_smul, smul_comm (r i)]
  have h2 : ∀ i ∈ t, ∀ j ∈ t, F i j + F j i = 0 := by
    intro i hi j hj
    by_cases h : j = i
    · simp [F, h]
    · simp only [F]
      rw [if_pos h, if_pos (Ne.symm h), GlobalTheory.cubeSign_mul_erase hi hj (Ne.symm h), mul_comm (r j),
        Finset.erase_right_comm (a := j), neg_smul, neg_add_cancel]
  have h3 : (∑ i ∈ t, ∑ j ∈ t, F i j) + ∑ i ∈ t, ∑ j ∈ t, F j i = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun j hj => h2 i hi j hj
  rw [Finset.sum_comm (f := fun i j => F j i), ← two_smul ℂ] at h3
  rw [h1]
  exact (smul_eq_zero.1 h3).resolve_left two_ne_zero

variable [Algebra ℂ R] [Module ℂ N] [IsScalarTower ℂ R N]

private theorem kos_D (r : κ → R) (c : Finset κ → N) :
    (kos (Algebra.lsmul ℂ ℂ N) ⊤ r).D c = dd r c := by
  funext t
  simp [kos, acx, wd, dd]

private theorem kos_C (r : κ → R) (c : Finset κ → N) (n : ℤ) :
    c ∈ (kos (Algebra.lsmul ℂ ℂ N) ⊤ r).C n ↔ ∀ s : Finset κ, (s.card : ℤ) ≠ n → c s = 0 := by
  simp only [kos, acx, Submodule.mem_pi, Set.mem_univ, true_imp_iff]
  refine forall_congr' fun s => ?_
  by_cases h : (s.card : ℤ) = n <;> simp [h]

private theorem kos_Z (r : κ → R) (c : Finset κ → N) (n : ℤ) :
    c ∈ (kos (Algebra.lsmul ℂ ℂ N) ⊤ r).Z n ↔
      (∀ s : Finset κ, (s.card : ℤ) ≠ n → c s = 0) ∧ dd r c = 0 := by
  rw [GlobalTheory.PD.Cx.Z, Submodule.mem_inf, kos_C, LinearMap.mem_ker, kos_D]

private theorem kos_B (r : κ → R) (c : Finset κ → N) (n : ℤ) :
    c ∈ (kos (Algebra.lsmul ℂ ℂ N) ⊤ r).B n ↔
      ∃ b : Finset κ → N, (∀ s : Finset κ, (s.card : ℤ) ≠ n - 1 → b s = 0) ∧ dd r b = c := by
  simp only [GlobalTheory.PD.Cx.B, Submodule.mem_map, kos_C, kos_D]

end Helpers

end UpperTheory.Reformulated.B.KoszulComplexHomotopy

open scoped Pointwise in
theorem UpperTheory.Reformulated.B.KoszulComplexHomotopy.koszulExactBelowLengthOfWeaklyRegular_of_htpy :
    UpperTheory.Reformulated.B.KoszulComplexHomotopy.Htpy → UpperTheory.Reformulated.B.KoszulComplexHomotopy.KoszulExactBelowLengthOfWeaklyRegular := by
  intro H d
  induction d with
  | zero =>
    intro R N _ _ _ _ _ _ κ _ _ r f _ _ _ m hm c hc
    have h0 : c = 0 := funext fun s => ((kos_Z r c m).1 hc).1 s (by omega)
    rw [h0]
    exact Submodule.zero_mem _
  | succ d ih =>
    intro R N _ _ _ _ _ _ κ _ _ r f hlen hreg hsp m hm c hc
    obtain _ | ⟨g, f⟩ := f
    · simp at hlen
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hreg
    obtain ⟨hg, hf⟩ := hreg
    have hB := H R N (Algebra.lsmul ℂ ℂ N) κ ⊤ ⊤ r (fun _ _ _ _ => Submodule.mem_top) m c hc g
      (hsp g List.mem_cons_self)
    obtain ⟨b, hb, hbc⟩ := (kos_B r _ m).1 hB
    have hbc' : ∀ s, dd r b s = g • c s := fun s => congrFun hbc s
    let P : Submodule R N := g • (⊤ : Submodule R N)
    have hP : ∀ x : N, P.mkQ x = 0 ↔ ∃ y, g • y = x := by
      intro x
      simp [P, Submodule.mem_smul_pointwise_iff_exists]
    have IH := ih R (N ⧸ P) κ r f (by simpa using hlen) hf
      (fun x hx => hsp x (List.mem_cons_of_mem _ hx)) (m - 1) (by omega)
    have hZ : (fun s => P.mkQ (b s)) ∈ (kos (Algebra.lsmul ℂ ℂ (N ⧸ P)) ⊤ r).Z (m - 1) := by
      rw [kos_Z]
      refine ⟨fun s hs => by rw [hb s hs, map_zero], funext fun s => ?_⟩
      rw [dd_map, hbc']
      exact (hP _).2 ⟨_, rfl⟩
    obtain ⟨a, ha, hab⟩ := (kos_B r _ _).1 (IH hZ)
    have hlift : ∀ s : Finset κ, ∃ x : N, P.mkQ x = a s ∧ ((s.card : ℤ) ≠ m - 1 - 1 → x = 0) := by
      intro s
      by_cases hs : (s.card : ℤ) = m - 1 - 1
      · obtain ⟨x, hx⟩ := P.mkQ_surjective (a s)
        exact ⟨x, hx, fun h => absurd hs h⟩
      · exact ⟨0, by rw [ha s hs, map_zero], fun _ => rfl⟩
    choose a' ha' ha0 using hlift
    have hdiv : ∀ s, ∃ y, g • y = b s - dd r a' s := by
      intro s
      rw [← hP, map_sub, ← dd_map, funext ha', hab, sub_self]
    choose y hy using hdiv
    rw [kos_B]
    refine ⟨y, fun s hs => hg ?_, funext fun s => hg ?_⟩
    · show g • y s = g • (0 : N)
      rw [hy, hb s hs, dd_deg r a' _ ha0 s hs, sub_zero, smul_zero]
    · show g • dd r y s = g • c s
      have e : b = fun s => dd r a' s + (LinearMap.lsmul R N g) (y s) := by
        funext s
        rw [LinearMap.lsmul_apply, hy, add_sub_cancel]
      rw [← hbc', e, dd_add, dd_dd, dd_map, zero_add, LinearMap.lsmul_apply]
