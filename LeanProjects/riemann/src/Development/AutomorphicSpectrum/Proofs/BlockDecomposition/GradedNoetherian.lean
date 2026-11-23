import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing

set_option autoImplicit false

noncomputable section

open DirectSum

namespace GlobalTheory.CompanionTheory.GE.GNoeth

variable {R : Type} [CommRing R] {M : ℕ → Type} [∀ e, AddCommGroup (M e)] [∀ e, Module R (M e)]

def shiftOp (T : ∀ e, M e →ₗ[R] M (e + 1)) : Module.End R (⨁ e, M e) :=
  DirectSum.toModule R ℕ _ (fun e => DirectSum.lof R ℕ M (e + 1) ∘ₗ T e)

theorem shiftOp_lof (T : ∀ e, M e →ₗ[R] M (e + 1)) (e : ℕ) (x : M e) :
    shiftOp T (DirectSum.lof R ℕ M e x) = DirectSum.lof R ℕ M (e + 1) (T e x) := by
  simp only [shiftOp, DirectSum.toModule_lof, LinearMap.comp_apply]

theorem shiftOp_succ (T : ∀ e, M e →ₗ[R] M (e + 1)) (y : ⨁ e, M e) (e : ℕ) :
    shiftOp T y (e + 1) = T e (y e) := by
  induction y using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    rw [← DirectSum.lof_eq_of R, shiftOp_lof, DirectSum.lof_eq_of, DirectSum.lof_eq_of]
    by_cases h : i = e
    · subst h; simp [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (by omega), DirectSum.of_eq_of_ne _ _ _ (by omega), map_zero]
  | add a b ha hb => simp only [map_add, DirectSum.add_apply, ha, hb]

theorem shiftOp_zero (T : ∀ e, M e →ₗ[R] M (e + 1)) (y : ⨁ e, M e) :
    shiftOp T y 0 = 0 := by
  induction y using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    rw [← DirectSum.lof_eq_of R, shiftOp_lof, DirectSum.lof_eq_of]
    exact DirectSum.of_eq_of_ne _ _ _ (by omega)
  | add a b ha hb => simp only [map_add, DirectSum.add_apply, ha, hb, add_zero]

theorem eventually_zero (f : ⨁ e, M e) : ∃ n : ℕ, ∀ e, n ≤ e → f e = 0 := by
  induction f using DirectSum.induction_on with
  | zero => exact ⟨0, fun _ _ => rfl⟩
  | of i x =>
    refine ⟨i + 1, fun e he => DirectSum.of_eq_of_ne _ _ _ (by omega)⟩
  | add a b ha hb =>
    obtain ⟨n, hn⟩ := ha
    obtain ⟨m, hm⟩ := hb
    exact ⟨max n m, fun e he => by
      rw [DirectSum.add_apply, hn e (le_of_max_le_left he), hm e (le_of_max_le_right he), add_zero]⟩

theorem lof_mem {L : ∀ e, Submodule R (M e)} (i : ℕ) {x : M i} (hx : x ∈ L i) (j : ℕ) :
    DirectSum.lof R ℕ M i x j ∈ L j := by
  rw [DirectSum.lof_eq_of]
  by_cases h : i = j
  · subst h; simpa [DirectSum.of_eq_same] using hx
  · rw [DirectSum.of_eq_of_ne _ _ _ (by omega)]; exact zero_mem _

theorem gradedNoeth : GradedNoeth := by
  classical
  intro R _ _ k M _ _ _ T hT d hgen L hL
  have hEc : ∀ i j, shiftOp (T i) * shiftOp (T j) = shiftOp (T j) * shiftOp (T i) := by
    intro i j
    apply DirectSum.linearMap_ext
    intro e
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, Module.End.mul_apply, shiftOp_lof]
    rw [hT i j e x]
  let Sset : Finset (Module.End R (⨁ e, M e)) := Finset.univ.image (fun i => shiftOp (T i))
  have hSset : ∀ a, a ∈ (Sset : Set (Module.End R (⨁ e, M e))) → ∃ i, shiftOp (T i) = a := by
    intro a ha
    simpa [Sset] using ha
  have hcomm : ∀ a ∈ (Sset : Set (Module.End R (⨁ e, M e))),
      ∀ b ∈ (Sset : Set (Module.End R (⨁ e, M e))), a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := hSset a ha
    obtain ⟨j, rfl⟩ := hSset b hb
    exact hEc i j
  let S := Algebra.adjoin R (Sset : Set (Module.End R (⨁ e, M e)))
  letI : CommRing S := Algebra.adjoinCommRingOfComm R hcomm
  haveI : Algebra.FiniteType R S :=
    (Subalgebra.fg_iff_finiteType S).1 (Subalgebra.fg_adjoin_finset _)
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  have hEmem : ∀ i, shiftOp (T i) ∈ S := fun i => Algebra.subset_adjoin (by simp [Sset])
  have hfin : ∀ e, ∃ g : Finset (M e), Submodule.span R (g : Set (M e)) = ⊤ := fun e =>
    Module.Finite.fg_top (R := R) (M := M e)
  choose gens hgens using hfin
  let G0 : Set (⨁ e, M e) :=
    ⋃ e ∈ Finset.range (d + 1), DirectSum.lof R ℕ M e '' (gens e : Set (M e))
  have hG0 : G0.Finite :=
    (Finset.finite_toSet _).biUnion fun e _ => (Finset.finite_toSet _).image _
  let P : Submodule S (⨁ e, M e) := Submodule.span S G0
  have hbase : ∀ e, e ≤ d → ∀ m : M e, DirectSum.lof R ℕ M e m ∈ P := by
    intro e he m
    have hm : m ∈ Submodule.span R (gens e : Set (M e)) := by rw [hgens e]; trivial
    induction hm using Submodule.span_induction with
    | mem x hx =>
      exact Submodule.subset_span (Set.mem_biUnion (Finset.mem_range.2 (by omega)) ⟨x, hx, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact P.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_of_tower_mem P c hx
  have hall : ∀ e (m : M e), DirectSum.lof R ℕ M e m ∈ P := by
    intro e
    induction e with
    | zero => exact hbase 0 (Nat.zero_le _)
    | succ e ih =>
      by_cases he : e + 1 ≤ d
      · exact hbase _ he
      · intro m
        have hm : m ∈ ⨆ i, LinearMap.range (T i e) := by rw [hgen e (by omega)]; trivial
        refine Submodule.iSup_induction _ (motive := fun m => DirectSum.lof R ℕ M (e + 1) m ∈ P)
          hm ?_ ?_ ?_
        · intro i x hx
          obtain ⟨y, rfl⟩ := hx
          have h1 : DirectSum.lof R ℕ M (e + 1) (T i e y) =
              (⟨shiftOp (T i), hEmem i⟩ : S) • DirectSum.lof R ℕ M e y :=
            (shiftOp_lof (T i) e y).symm
          rw [h1]
          exact P.smul_mem _ (ih y)
        · simp
        · intro x y hx hy
          rw [map_add]
          exact P.add_mem hx hy
  have hP : ∀ y : ⨁ e, M e, y ∈ P := by
    intro y
    induction y using DirectSum.induction_on with
    | zero => exact P.zero_mem
    | of i x => rw [← DirectSum.lof_eq_of R]; exact hall i x
    | add a b ha hb => exact P.add_mem ha hb
  have htop : P = ⊤ := eq_top_iff.2 fun y _ => hP y
  haveI : Module.Finite S (⨁ e, M e) := ⟨Submodule.fg_def.2 ⟨G0, hG0, htop⟩⟩
  have hstab : ∀ x ∈ S, ∀ y : ⨁ e, M e, (∀ e, y e ∈ L e) → ∀ e, x y e ∈ L e := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hSset x hx
      intro y hy e
      cases e with
      | zero => rw [shiftOp_zero]; exact zero_mem _
      | succ e => rw [shiftOp_succ]; exact hL i e (Submodule.mem_map_of_mem (hy e))
    | algebraMap r =>
      intro y hy e
      rw [Module.algebraMap_end_apply, DirectSum.smul_apply]
      exact (L e).smul_mem r (hy e)
    | add x x' _ _ hx hx' =>
      intro y hy e
      rw [LinearMap.add_apply, DirectSum.add_apply]
      exact (L e).add_mem (hx y hy e) (hx' y hy e)
    | mul x x' _ _ hx hx' =>
      intro y hy e
      rw [Module.End.mul_apply]
      exact hx _ (hx' y hy) e
  let N : Submodule S (⨁ e, M e) :=
    { carrier := {y | ∀ e, y e ∈ L e}
      add_mem' := fun {a b} ha hb e => by
        rw [DirectSum.add_apply]; exact (L e).add_mem (ha e) (hb e)
      zero_mem' := fun e => by rw [DirectSum.zero_apply]; exact zero_mem _
      smul_mem' := fun s y hy => hstab s.1 s.2 y hy }
  have hQ : ∀ e, ∀ x ∈ S, ∃ c : R, ∀ y : ⨁ e, M e, (∀ e', y e' ∈ L e') →
      x y (e + 1) - c • y (e + 1) ∈ ⨆ i, (L e).map (T i e) := by
    intro e x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hSset x hx
      refine ⟨0, fun y hy => ?_⟩
      rw [zero_smul, sub_zero, shiftOp_succ]
      exact Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem (hy e))
    | algebraMap r =>
      refine ⟨r, fun y hy => ?_⟩
      rw [Module.algebraMap_end_apply, DirectSum.smul_apply, sub_self]
      exact zero_mem _
    | add x x' _ _ hx hx' =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨c', hc'⟩ := hx'
      refine ⟨c + c', fun y hy => ?_⟩
      have h2 := Submodule.add_mem _ (hc y hy) (hc' y hy)
      convert h2 using 1
      rw [LinearMap.add_apply, DirectSum.add_apply, add_smul]
      abel
    | mul x x' _ hx'S hx hx' =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨c', hc'⟩ := hx'
      refine ⟨c * c', fun y hy => ?_⟩
      have h2 := Submodule.add_mem _ (hc _ (hstab x' hx'S y hy)) (Submodule.smul_mem _ c (hc' y hy))
      convert h2 using 1
      rw [Module.End.mul_apply, smul_sub, mul_smul]
      abel
  obtain ⟨F, hF⟩ := IsNoetherian.noetherian N
  choose nf hnf using (eventually_zero : ∀ f : ⨁ e, M e, ∃ n : ℕ, ∀ e, n ≤ e → f e = 0)
  refine ⟨F.sup nf, fun e he => le_antisymm (iSup_le fun i => hL i e) ?_⟩
  intro x hx
  let Ne : Submodule S (⨁ e, M e) :=
    { carrier := {y | y ∈ N ∧ y (e + 1) ∈ ⨆ i, (L e).map (T i e)}
      add_mem' := fun {a b} ha hb => ⟨N.add_mem ha.1 hb.1, by
        rw [DirectSum.add_apply]; exact Submodule.add_mem _ ha.2 hb.2⟩
      zero_mem' := ⟨N.zero_mem, by rw [DirectSum.zero_apply]; exact zero_mem _⟩
      smul_mem' := fun s y hy => by
        obtain ⟨c, hc⟩ := hQ e s.1 s.2
        refine ⟨N.smul_mem s hy.1, ?_⟩
        have h3 := Submodule.add_mem _ (hc y hy.1) (Submodule.smul_mem _ c hy.2)
        rw [sub_add_cancel] at h3
        exact h3 }
  have hNle : N ≤ Ne := by
    rw [← hF, Submodule.span_le]
    intro f hf
    refine ⟨by rw [← hF]; exact Submodule.subset_span hf, ?_⟩
    have h4 : nf f ≤ F.sup nf := Finset.le_sup hf
    rw [hnf f (e + 1) (by omega)]
    exact zero_mem _
  have hxN : DirectSum.lof R ℕ M (e + 1) x ∈ N := fun j => lof_mem (e + 1) hx j
  have h5 := (hNle hxN).2
  rwa [DirectSum.lof_eq_of, DirectSum.of_eq_same] at h5

end GlobalTheory.CompanionTheory.GE.GNoeth
