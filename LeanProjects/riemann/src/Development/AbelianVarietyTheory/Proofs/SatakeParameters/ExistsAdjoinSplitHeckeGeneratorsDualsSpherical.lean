import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalDoubleCosetLabelIffDecreasingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeSplitTopDegreeRecursionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeScalarLabelCompEqShiftDownSplitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitGen

theorem top_step : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), conjPl P ≠ P → ∀ d : List ℤ, IsLab V P d → (∀ x ∈ d, 0 ≤ x) → (∃ x ∈ d, 0 < x) → ∃ m : ℕ, 0 < m ∧ ∃ c : List ℤ →₀ ℂ, (∀ d' ∈ c.support, (∀ x ∈ d', 0 ≤ x) ∧ d'.sum = d.sum ∧ (d'.map fun x => x ^ 2).sum < (d.map fun x => x ^ 2).sum) ∧ ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P (Finsupp.single (d.map fun x => if 0 < x then x - 1 else x) 1) (opOf π P (Finsupp.single (dualLab (splitLab V.rank (d.filter fun x => 0 < x).length)) 1) u) = (m : ℂ) • opOf π P (Finsupp.single d 1) u + opOf π P c u := GlobalTheory.T.sphericalHecke_split_top_degree_recursion

theorem central_shift : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), conjPl P ≠ P → ∀ (d : List ℤ) (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P (Finsupp.single (splitLab V.rank V.rank) 1) (opOf π P (Finsupp.single d 1) u) = opOf π P (Finsupp.single (d.map fun x => x - 1) 1) u := GlobalTheory.T.sphericalHecke_scalarLabel_comp_eq_shiftDown_split

section Gen

variable {D : D7} (V : HSp D) (P : Pl D.host.E) {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M)

def gens : Set (Module.End ℂ M) :=
  {x | ∃ k, k ≤ V.rank ∧ (x = opOf π P (Finsupp.single (splitLab V.rank k) 1) ∨
    x = opOf π P (Finsupp.single (dualLab (splitLab V.rank k)) 1))}

def Good (c : List ℤ →₀ ℂ) : Prop :=
  ∃ a ∈ Algebra.adjoin ℂ (gens V P π), ∀ u : M, (∀ k ∈ hyp V P, π k u = u) → a u = opOf π P c u

variable {V P π}

theorem opOf_eq_sum (c : List ℤ →₀ ℂ) (u : M) :
    opOf π P c u = ∑ d ∈ c.support, c d • opOf π P (Finsupp.single d 1) u := by
  rw [opOf, Finsupp.sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [LinearMap.smul_apply, GlobalTheory.SphLabelOps.opOf_single, LinearMap.sum_apply]

theorem good_of_support {c : List ℤ →₀ ℂ} (h : ∀ d ∈ c.support, Good V P π (Finsupp.single d 1)) :
    Good V P π c := by
  classical
  choose a ha he using h
  refine ⟨∑ d ∈ c.support.attach, c d • a d.1 d.2, Subalgebra.sum_mem _ fun d _ => Subalgebra.smul_mem _ (ha _ _) _,
    fun u hu => ?_⟩
  rw [opOf_eq_sum, LinearMap.sum_apply, ← Finset.sum_attach c.support]
  exact Finset.sum_congr rfl fun d _ => by rw [LinearMap.smul_apply, he _ _ u hu]

theorem good_gen {x : Module.End ℂ M} (hx : x ∈ gens V P π) : x ∈ Algebra.adjoin ℂ (gens V P π) :=
  Algebra.subset_adjoin hx

theorem good_nonlab {d : List ℤ} (h : ¬ IsLab V P d) : Good V P π (Finsupp.single d 1) := by
  refine ⟨0, Subalgebra.zero_mem _, fun u _ => ?_⟩
  rw [GlobalTheory.SphLabelOps.opOf_single, Hk3.rep, dif_neg h, Finset.sum_empty, LinearMap.zero_apply]

theorem fixed_opOf (c : List ℤ →₀ ℂ) {u : M} (hu : ∀ k ∈ hyp V P, π k u = u) : ∀ k ∈ hyp V P, π k (opOf π P c u) = opOf π P c u :=
  (GlobalTheory.SphLabelOps.label_operators V P).2.1 c M π u hu

theorem good_nonneg (hP : conjPl P ≠ P) : ∀ s q : ℕ, ∀ d : List ℤ, (∀ x ∈ d, 0 ≤ x) → d.sum = (s : ℤ) →
    (d.map fun x => x ^ 2).sum = (q : ℤ) → Good V P π (Finsupp.single d 1) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ihs =>
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ihq =>
  intro d hd hs hq
  by_cases hl : IsLab V P d
  swap
  · exact good_nonlab hl
  by_cases hpos : ∃ x ∈ d, 0 < x
  · obtain ⟨m, hm, c, hc, hrel⟩ := top_step V P hP d hl hd hpos
    set d1 := d.map fun x => if 0 < x then x - 1 else x with hd1
    have hd1n : ∀ x ∈ d1, 0 ≤ x := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      have := hd y hy
      split_ifs <;> omega
    have hlt : d1.sum < d.sum := by
      have := List.sum_lt_sum (l := d) (fun x => if 0 < x then x - 1 else x) id
        (fun x _ => by simp only [id]; split_ifs <;> omega)
        (by obtain ⟨x, hx, hx0⟩ := hpos; exact ⟨x, hx, by simp only [id]; rw [if_pos hx0]; omega⟩)
      simpa using this
    have hs1 : 0 ≤ d1.sum := List.sum_nonneg hd1n
    have hq1 : 0 ≤ (d1.map fun x => x ^ 2).sum := List.sum_nonneg fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
      positivity
    have g1 : Good V P π (Finsupp.single d1 1) :=
      ihs d1.sum.toNat (by omega) _ d1 hd1n (by omega) (Int.toNat_of_nonneg hq1).symm
    have gc : Good V P π c := good_of_support fun d' hd' => by
      obtain ⟨h1, h2, h3⟩ := hc d' hd'
      have h4 : 0 ≤ (d'.map fun x => x ^ 2).sum := List.sum_nonneg fun x hx => by
        obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
        positivity
      exact ihq _ (by omega) d' h1 (by omega) (Int.toNat_of_nonneg h4).symm
    obtain ⟨a1, ha1, e1⟩ := g1
    obtain ⟨ac, hac, ec⟩ := gc
    set k := (d.filter fun x => 0 < x).length
    have hk : k ≤ V.rank := by
      have := ((GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing V P d).1 hl).1
      rw [← this]
      exact List.length_filter_le _ _
    refine ⟨(m : ℂ)⁻¹ • (a1 * opOf π P (Finsupp.single (dualLab (splitLab V.rank k)) 1) - ac),
      Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Subalgebra.mul_mem _ ha1 (good_gen ⟨k, hk, Or.inr rfl⟩)) hac) _,
      fun u hu => ?_⟩
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply, e1 _ (fixed_opOf _ hu), hrel M π u hu,
      ec u hu, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hm', one_smul]
  · push_neg at hpos
    have h0 : d = splitLab V.rank 0 := by
      have hlen := ((GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing V P d).1 hl).1
      rw [splitLab, Nat.sub_zero, List.replicate_zero, List.append_nil, ← hlen]
      exact List.eq_replicate_iff.2 ⟨rfl, fun x hx => le_antisymm (hpos x hx) (hd x hx)⟩
    refine ⟨_, good_gen ⟨0, Nat.zero_le _, Or.inl rfl⟩, fun u _ => by rw [h0]⟩

theorem shift (hP : conjPl P ≠ P) (u : M) (hu : ∀ k ∈ hyp V P, π k u = u) :
    ∀ (j : ℕ) (d : List ℤ), ((opOf π P (Finsupp.single (splitLab V.rank V.rank) 1)) ^ j)
      (opOf π P (Finsupp.single (d.map fun x => x + (j : ℤ)) 1) u) = opOf π P (Finsupp.single d 1) u := by
  intro j
  induction j with
  | zero => intro d; simp
  | succ j ih =>
    intro d
    rw [pow_succ, Module.End.mul_apply, central_shift V P hP _ M π u hu, List.map_map, ← ih d]
    congr 4
    refine List.map_congr_left fun x _ => ?_
    simp only [Function.comp_apply, Nat.cast_succ]
    ring

end Gen

theorem gen_split : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), conjPl P ≠ P → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (d : List ℤ), ∃ a ∈ Algebra.adjoin ℂ {x : Module.End ℂ M | ∃ k, k ≤ V.rank ∧ (x = opOf π P (Finsupp.single (splitLab V.rank k) 1) ∨ x = opOf π P (Finsupp.single (dualLab (splitLab V.rank k)) 1))}, ∀ u : M, (∀ k ∈ hyp V P, π k u = u) → a u = opOf π P (Finsupp.single d 1) u := by
  intro D V P hP M _ _ π d
  set t : ℕ := (d.map fun x => (-x).toNat).sum
  have ht : ∀ x ∈ d.map (fun x => x + (t : ℤ)), 0 ≤ x := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun x : ℤ => (-x).toNat) hx)
    omega
  have hs : 0 ≤ (d.map fun x => x + (t : ℤ)).sum := List.sum_nonneg ht
  have hq : 0 ≤ ((d.map fun x => x + (t : ℤ)).map fun x => x ^ 2).sum := List.sum_nonneg fun x hx => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    positivity
  obtain ⟨a, ha, he⟩ := good_nonneg (V := V) (P := P) (π := π) hP _ _ _ ht (Int.toNat_of_nonneg hs).symm
    (Int.toNat_of_nonneg hq).symm
  refine ⟨(opOf π P (Finsupp.single (splitLab V.rank V.rank) 1)) ^ t * a,
    Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (good_gen ⟨V.rank, le_rfl, Or.inl rfl⟩) _) ha, fun u hu => ?_⟩
  rw [Module.End.mul_apply, he u hu, shift hP u hu]

end GlobalTheory.SplitGen
