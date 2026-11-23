import Mathlib

noncomputable section

namespace GroundTheory.Automorphic

namespace PeterssonComplement

open Polynomial

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H)

def orthIn (U : Submodule ℂ V) : Submodule ℂ V where
  carrier := {v | ∀ u ∈ U, inner ℂ (ι u) (ι v) = 0}
  zero_mem' u _ := by rw [map_zero, inner_zero_right]
  add_mem' {v w} hv hw u hu := by rw [map_add, inner_add_right, hv u hu, hw u hu, add_zero]
  smul_mem' c v hv u hu := by rw [map_smul, inner_smul_right, hv u hu, mul_zero]

variable {ι}

theorem mem_orthIn {U : Submodule ℂ V} {v : V} :
    v ∈ orthIn ι U ↔ ∀ u ∈ U, inner ℂ (ι u) (ι v) = 0 := Iff.rfl

theorem disjoint_orthIn (hι : Function.Injective ι) (U : Submodule ℂ V) : Disjoint U (orthIn ι U) := by
  rw [Submodule.disjoint_def]
  intro v hvU hvO
  have h := hvO v hvU
  rw [inner_self_eq_zero] at h
  exact hι (h.trans (map_zero ι).symm)

theorem sup_orthIn_eq_top (U : Submodule ℂ V)
    (h : ∀ v : V, ∃ W : Submodule ℂ V, FiniteDimensional ℂ W ∧ v ∈ W ∧
      ∀ u ∈ U, ∃ u' ∈ U ⊓ W, ∀ w ∈ W, inner ℂ (ι u) (ι w) = inner ℂ (ι u') (ι w)) :
    U ⊔ orthIn ι U = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨W, hWf, hvW, hW⟩ := h v
  set M : Submodule ℂ H := (U ⊓ W).map ι with hM
  have : FiniteDimensional ℂ (U ⊓ W : Submodule ℂ V) :=
    Submodule.finiteDimensional_of_le (inf_le_right : U ⊓ W ≤ W)
  have : FiniteDimensional ℂ M := by rw [hM]; infer_instance
  have hp : M.starProjection (ι v) ∈ M := Submodule.starProjection_apply_mem M (ι v)
  obtain ⟨a, haUW, hax⟩ := Submodule.mem_map.1 hp
  have horth : ι v - M.starProjection (ι v) ∈ Mᗮ := Submodule.sub_starProjection_mem_orthogonal _
  refine Submodule.mem_sup.2 ⟨a, haUW.1, v - a, fun u hu => ?_, add_sub_cancel _ _⟩
  obtain ⟨u', hu'UW, hu'⟩ := hW u hu
  rw [hu' (v - a) (W.sub_mem hvW haUW.2), map_sub, hax]
  exact Submodule.inner_right_of_mem_orthogonal (Submodule.mem_map_of_mem hu'UW) horth

theorem inner_aeval_map_left {T : Module.End ℂ V}
    (hT : ∀ x y, inner ℂ (ι (T x)) (ι y) = inner ℂ (ι x) (ι (T y))) (p : ℝ[X]) (x y : V) :
    inner ℂ (ι (aeval T (p.map (algebraMap ℝ ℂ)) x)) (ι y) =
      inner ℂ (ι x) (ι (aeval T (p.map (algebraMap ℝ ℂ)) y)) := by
  have hcomm : ∀ q : ℂ[X], ∀ z, T (aeval T q z) = aeval T q (T z) := by
    intro q z
    have h := (Commute.all (X : ℂ[X]) q).map (aeval T)
    rw [aeval_X] at h
    exact congrArg (fun L : Module.End ℂ V => L z) h.eq
  revert x y
  induction p using Polynomial.induction_on with
  | C a =>
    intro x y
    simp only [Polynomial.map_C, aeval_C, Module.algebraMap_end_apply, map_smul, inner_smul_left,
      inner_smul_right, Complex.coe_algebraMap, Complex.conj_ofReal]
  | add p q hp hq =>
    intro x y
    simp only [Polynomial.map_add, map_add, LinearMap.add_apply, inner_add_left, inner_add_right, hp, hq]
  | monomial k a ih =>
    intro x y
    have e : ((C a * X ^ (k + 1) : ℝ[X]).map (algebraMap ℝ ℂ)) =
        (C a * X ^ k : ℝ[X]).map (algebraMap ℝ ℂ) * X := by
      rw [pow_succ, ← mul_assoc, Polynomial.map_mul, Polynomial.map_X]
    rw [e, map_mul, aeval_X, Module.End.mul_apply, Module.End.mul_apply, ih (T x) y, hT, hcomm]

theorem aeval_mem {T : Module.End ℂ V} {Z : Submodule ℂ V} (hZ : ∀ z ∈ Z, T z ∈ Z) (q : ℂ[X]) :
    ∀ z ∈ Z, aeval T q z ∈ Z := by
  induction q using Polynomial.induction_on with
  | C a =>
    intro z hz
    rw [aeval_C, Module.algebraMap_end_apply]
    exact Z.smul_mem a hz
  | add p q hp hq =>
    intro z hz
    rw [map_add, LinearMap.add_apply]
    exact Z.add_mem (hp z hz) (hq z hz)
  | monomial k a ih =>
    intro z hz
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, Module.End.mul_apply]
    exact ih _ (hZ z hz)

theorem exists_apply_eq_zero_inner_eq (hι : Function.Injective ι) {T : Module.End ℂ V}
    (hT : ∀ x y, inner ℂ (ι (T x)) (ι y) = inner ℂ (ι x) (ι (T y))) (p : ℝ[X])
    (Z : Submodule ℂ V) [FiniteDimensional ℂ Z] (hZ : ∀ z ∈ Z, T z ∈ Z) {x : V} (hx : x ∈ Z) :
    ∃ m ∈ Z, aeval T (p.map (algebraMap ℝ ℂ)) m = 0 ∧
      ∀ w, aeval T (p.map (algebraMap ℝ ℂ)) w = 0 →
        inner ℂ (ι x) (ι w) = inner ℂ (ι m) (ι w) := by
  set S := aeval T (p.map (algebraMap ℝ ℂ)) with hS
  have hSym : ∀ a b, inner ℂ (ι (S a)) (ι b) = inner ℂ (ι a) (ι (S b)) :=
    inner_aeval_map_left hT p
  have hSZ : ∀ z ∈ Z, S z ∈ Z := aeval_mem hZ _
  set S' : Z →ₗ[ℂ] Z := S.restrict hSZ with hS'
  have hdisj : Disjoint (LinearMap.ker S') (LinearMap.range S') := by
    rw [Submodule.disjoint_def]
    rintro y hyk ⟨z, rfl⟩
    have h1 : S (S z) = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 hyk)
    have h2 : inner ℂ (ι (S z)) (ι (S z)) = 0 := by rw [hSym, h1, map_zero, inner_zero_right]
    rw [inner_self_eq_zero, ← map_zero ι] at h2
    exact Subtype.ext (hι h2)
  have hcompl : IsCompl (LinearMap.ker S') (LinearMap.range S') :=
    (Submodule.isCompl_iff_disjoint _ _ (by
      rw [add_comm, LinearMap.finrank_range_add_finrank_ker])).2 hdisj
  obtain ⟨m, hm, r, ⟨z, rfl⟩, hmr⟩ :=
    Submodule.mem_sup.1 (hcompl.sup_eq_top ▸ Submodule.mem_top : (⟨x, hx⟩ : Z) ∈ _)
  refine ⟨m, m.2, congrArg Subtype.val (LinearMap.mem_ker.1 hm), fun w hw => ?_⟩
  have hxe : x = (m : V) + S z := congrArg Subtype.val hmr.symm
  rw [hxe, map_add, inner_add_left, hSym, hw, map_zero, inner_zero_right, add_zero]

theorem apply_aeval_comm (T : Module.End ℂ V) (q : ℂ[X]) (z : V) : T (aeval T q z) = aeval T q (T z) := by
  have h := (Commute.all (X : ℂ[X]) q).map (aeval T)
  rw [aeval_X] at h
  exact congrArg (fun L : Module.End ℂ V => L z) h.eq

theorem sup_orthIn_eq_top_of_symmetric (U : Submodule ℂ V) (hι : Function.Injective ι)
    {T : Module.End ℂ V} (hT : ∀ x y, inner ℂ (ι (T x)) (ι y) = inner ℂ (ι x) (ι (T y)))
    (hUT : ∀ u ∈ U, T u ∈ U)
    (h : ∀ v : V, ∃ V₀ : Submodule ℂ V, v ∈ V₀ ∧ (∀ z ∈ V₀, T z ∈ V₀) ∧
      (∀ x ∈ V₀, ∃ p : ℝ[X], aeval T (p.map (algebraMap ℝ ℂ)) x = 0 ∧
        FiniteDimensional ℂ (V₀ ⊓ LinearMap.ker (aeval T (p.map (algebraMap ℝ ℂ))) : Submodule ℂ V)) ∧
      ∀ u ∈ U, ∃ e ∈ U ⊓ V₀, ∀ w ∈ V₀, inner ℂ (ι u) (ι w) = inner ℂ (ι e) (ι w)) :
    U ⊔ orthIn ι U = ⊤ := by
  refine sup_orthIn_eq_top U fun v => ?_
  obtain ⟨V₀, hv, hV₀T, hfin, havg⟩ := h v
  obtain ⟨p, hpv, hpfin⟩ := hfin v hv
  refine ⟨V₀ ⊓ LinearMap.ker (aeval T (p.map (algebraMap ℝ ℂ))), hpfin, ⟨hv, hpv⟩, fun u hu => ?_⟩
  obtain ⟨e, ⟨heU, heV₀⟩, he⟩ := havg u hu
  obtain ⟨q, hqe, hqfin⟩ := hfin e heV₀
  set Z : Submodule ℂ V := U ⊓ (V₀ ⊓ LinearMap.ker (aeval T (q.map (algebraMap ℝ ℂ)))) with hZ
  have : FiniteDimensional ℂ Z := Submodule.finiteDimensional_of_le (inf_le_right : Z ≤ _)
  have hZT : ∀ z ∈ Z, T z ∈ Z := by
    rintro z ⟨hzU, hzV₀, hzk⟩
    refine ⟨hUT z hzU, hV₀T z hzV₀, ?_⟩
    show T z ∈ LinearMap.ker _
    rw [LinearMap.mem_ker, ← apply_aeval_comm, LinearMap.mem_ker.1 (hzk : z ∈ LinearMap.ker _), map_zero]
  obtain ⟨m, ⟨hmU, hmV₀, -⟩, hmk, hm⟩ :=
    exists_apply_eq_zero_inner_eq hι hT p Z hZT (⟨heU, heV₀, hqe⟩ : e ∈ Z)
  exact ⟨m, ⟨hmU, hmV₀, hmk⟩, fun w ⟨hwV₀, hwk⟩ => (he w hwV₀).trans (hm w hwk)⟩

theorem map_mem_orthIn {U : Submodule ℂ V} {A A' : V → V}
    (hA : ∀ x y, inner ℂ (ι (A' x)) (ι y) = inner ℂ (ι x) (ι (A y))) (hU : ∀ u ∈ U, A' u ∈ U)
    {v : V} (hv : v ∈ orthIn ι U) : A v ∈ orthIn ι U := fun u hu => by
  rw [← hA]
  exact hv _ (hU u hu)

end PeterssonComplement

end GroundTheory.Automorphic
