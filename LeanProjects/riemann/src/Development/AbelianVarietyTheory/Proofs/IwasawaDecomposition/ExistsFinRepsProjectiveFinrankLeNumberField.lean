import Mathlib
open NumberField

namespace GlobalTheory
namespace ProjModClasses

variable {R : Type} [CommRing R] [IsDomain R] [IsDedekindDomain R]

noncomputable def rep (c : ClassGroup R) : Ideal R :=
  ((ClassGroup.mk0_surjective (R := R) c).choose : Ideal R)

theorem rep_mem (c : ClassGroup R) : rep c ∈ nonZeroDivisors (Ideal R) :=
  (ClassGroup.mk0_surjective (R := R) c).choose.2

theorem mk0_rep (c : ClassGroup R) : ClassGroup.mk0 ⟨rep c, rep_mem c⟩ = c :=
  (ClassGroup.mk0_surjective (R := R) c).choose_spec

instance ideal_projective (I : Ideal R) : Module.Projective R I := by
  have : Module.FinitePresentation R I := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

theorem map_mulLeft_eq (x : R) (I : Ideal R) :
    Submodule.map (LinearMap.mulLeft R x) I = Ideal.span {x} * I := by
  ext z
  rw [Ideal.mem_span_singleton_mul, Submodule.mem_map]
  simp [LinearMap.mulLeft_apply]

noncomputable def mulEquiv {x : R} (hx : x ≠ 0) (I : Ideal R) :
    I ≃ₗ[R] (Ideal.span {x} * I : Ideal R) :=
  (Submodule.equivMapOfInjective (LinearMap.mulLeft R x) (mul_right_injective₀ hx) I).trans
    (LinearEquiv.ofEq _ _ (map_mulLeft_eq x I))

theorem nonempty_equiv_of_mk0_eq {I J : nonZeroDivisors (Ideal R)}
    (h : ClassGroup.mk0 I = ClassGroup.mk0 J) : Nonempty ((I : Ideal R) ≃ₗ[R] (J : Ideal R)) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 h
  exact ⟨(mulEquiv hx I).trans ((LinearEquiv.ofEq _ _ hxy).trans (mulEquiv hy J).symm)⟩

abbrev Model {r : ℕ} (c : Fin r → ClassGroup R) : Type := ∀ j, (rep (c j) : Ideal R)

noncomputable def consLin {r : ℕ} (d : ClassGroup R) (c : Fin r → ClassGroup R) :
    (↥(rep d) × Model c) ≃ₗ[R] Model (Fin.cons d c : Fin (r + 1) → ClassGroup R) :=
  { Fin.consEquiv (fun j => ↥(rep ((Fin.cons d c : Fin (r + 1) → ClassGroup R) j))) with
    map_add' := fun a b => by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j <;> rfl
    map_smul' := fun s a => by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j <;> rfl }

theorem exists_equiv_model : ∀ (r : ℕ) (X : Type) [AddCommGroup X] [Module R X] [Module.Finite R X]
    [Module.Projective R X], Module.finrank R X = r →
    ∃ c : Fin r → ClassGroup R, Nonempty (X ≃ₗ[R] Model c)
  | 0, X, _, _, _, _, h => by
    have : Subsingleton X := by
      by_contra hX
      rw [not_subsingleton_iff_nontrivial] at hX
      have := (Module.finrank_pos_iff (R := R) (M := X)).2 hX
      omega
    exact ⟨Fin.elim0, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
  | r + 1, X, _, _, _, _, h => by
    have hX : Nontrivial X := (Module.finrank_pos_iff (R := R) (M := X)).1 (by omega)
    obtain ⟨x, hx⟩ := exists_ne (0 : X)
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero R hx
    set I : Ideal R := LinearMap.range f with hIdef
    have hI : I ≠ ⊥ := fun h0 => hf (by
      have : f x ∈ I := LinearMap.mem_range_self f x
      rw [h0] at this
      simpa using this)
    let g : X →ₗ[R] I := f.rangeRestrict
    have hg : Function.Surjective g := LinearMap.surjective_rangeRestrict f
    obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hg
    let K := LinearMap.ker g
    have hex : Function.Exact K.subtype g := LinearMap.exact_subtype_ker_map g
    let e := ((hex.splitSurjectiveEquiv Subtype.val_injective) ⟨s, hs⟩).1
    have he := ((hex.splitSurjectiveEquiv Subtype.val_injective) ⟨s, hs⟩).2
    haveI : Module.Projective R K := by
      refine Module.Projective.of_split K.subtype (LinearMap.fst R K I ∘ₗ e.toLinearMap) ?_
      ext y
      have h1 : (K.subtype y) = e.symm (y, 0) := by
        rw [he.1]; rfl
      show ((e (K.subtype y)).1 : X) = (y : X)
      rw [h1]
      simp

    have hrk := LinearMap.rank_range_add_rank_ker g
    rw [LinearMap.range_eq_top.2 hg, rank_top] at hrk
    have hIne : Nontrivial I := Submodule.nontrivial_iff_ne_bot.2 hI
    have hI1 : Module.finrank R I = 1 := by
      have a := (Module.finrank_pos_iff (R := R) (M := I)).2 hIne
      have b : Module.finrank R I ≤ 1 := (Submodule.finrank_le I).trans (by simp)
      omega
    have hK : Module.finrank R K = r := by
      have := congrArg Cardinal.toNat hrk
      rw [Cardinal.toNat_add (Module.rank_lt_aleph0 R I) (Module.rank_lt_aleph0 R K)] at this
      change Module.finrank R I + Module.finrank R K = Module.finrank R X at this
      omega
    obtain ⟨c, ⟨eK⟩⟩ := exists_equiv_model r K hK
    have hmem : I ∈ nonZeroDivisors (Ideal R) := mem_nonZeroDivisors_of_ne_zero hI
    obtain ⟨eI⟩ := nonempty_equiv_of_mk0_eq (I := ⟨I, hmem⟩)
      (J := ⟨rep (ClassGroup.mk0 ⟨I, hmem⟩), rep_mem _⟩) (mk0_rep _).symm
    exact ⟨Fin.cons (ClassGroup.mk0 ⟨I, hmem⟩) c,
      ⟨e.trans ((LinearEquiv.prodComm R K I).trans ((eI.prodCongr eK).trans (consLin _ c)))⟩⟩

end ProjModClasses
open ProjModClasses in

theorem exists_fin_reps_projective_finrank_le :
    ∀ (E : Type) [Field E] [NumberField E] (q : ℕ), ∃ (n : ℕ) (R : Fin n → ModuleCat.{0} (𝓞 E)),
    (∀ k, Module.Finite (𝓞 E) (R k) ∧ Module.Projective (𝓞 E) (R k) ∧ Module.finrank (𝓞 E) (R k) ≤ q) ∧
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∃ k, Nonempty (X ≃ₗ[𝓞 E] R k) := by
  intro E _ _ q
  let T := Σ r : Fin (q + 1), (Fin r → ClassGroup (𝓞 E))
  let g : T → ModuleCat.{0} (𝓞 E) := fun t => ModuleCat.of (𝓞 E) (Model t.2)
  let P : T → Prop := fun t => Module.Finite (𝓞 E) (g t) ∧ Module.Projective (𝓞 E) (g t) ∧
    Module.finrank (𝓞 E) (g t) ≤ q
  let S := {t : T // P t}
  haveI : Finite S := inferInstance
  let eS := Finite.equivFin S
  refine ⟨Nat.card S, fun k => g (eS.symm k).1, fun k => (eS.symm k).2, ?_⟩
  intro X _ _ _ _ hq
  obtain ⟨c, ⟨eX⟩⟩ := exists_equiv_model (R := 𝓞 E) (Module.finrank (𝓞 E) X) X rfl
  let t : T := ⟨⟨Module.finrank (𝓞 E) X, Nat.lt_succ_of_le hq⟩, c⟩
  have ht : P t := by
    refine ⟨Module.Finite.equiv eX, Module.Projective.of_equiv eX, ?_⟩
    change Module.finrank (𝓞 E) (Model c) ≤ q
    rw [← eX.finrank_eq]
    exact hq
  refine ⟨eS ⟨t, ht⟩, ?_⟩
  show Nonempty (X ≃ₗ[𝓞 E] (g (eS.symm (eS ⟨t, ht⟩)).1))
  rw [Equiv.symm_apply_apply]
  exact ⟨eX⟩

end GlobalTheory
