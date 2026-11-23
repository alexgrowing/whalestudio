import Formalism.WachLatticeTwists.Statement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.RowCol

open Module

theorem length_le_of_killed {O : Type*} [CommRing O] (b : O) {X : Type*} [AddCommGroup X]
    [Module O X] {ι : Type*} [Fintype ι] (g : (ι → O) →ₗ[O] X) (hg : Function.Surjective g)
    (hb : ∀ x : X, b • x = 0) :
    Module.length O X ≤ (Fintype.card ι : ℕ∞) * Module.length O (O ⧸ Ideal.span {b}) := by
  classical
  let gi : ι → (O →ₗ[O] X) := fun i =>
    LinearMap.toSpanSingleton O X (g (fun j => if i = j then 1 else 0))
  have hker : ∀ i, Ideal.span {b} ≤ LinearMap.ker (gi i) := by
    intro i
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact LinearMap.mem_ker.mpr (hb _)
  let h : (ι → O ⧸ Ideal.span {b}) →ₗ[O] X :=
    ∑ i, (Submodule.liftQ (Ideal.span {b}) (gi i) (hker i)).comp (LinearMap.proj i)
  have hs : Function.Surjective h := by
    intro x
    obtain ⟨v, rfl⟩ := hg x
    refine ⟨fun i => Submodule.Quotient.mk (v i), ?_⟩
    simp only [h, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Submodule.liftQ_apply, gi, LinearMap.toSpanSingleton_apply]
    conv_rhs => rw [pi_eq_sum_univ v]
    rw [map_sum]
    simp only [map_smul]
  calc Module.length O X ≤ Module.length O (ι → O ⧸ Ideal.span {b}) :=
        Module.length_le_of_surjective h hs
    _ = _ := by rw [Module.length_pi, ENat.card_eq_coe_fintype_card]

theorem length_le_of_killed_pow {O : Type*} [CommRing O] (b : O) : ∀ (e : ℕ) {X : Type*}
    [AddCommGroup X] [Module O X] {ι : Type*} [Fintype ι] (g : (ι → O) →ₗ[O] X),
    Function.Surjective g → (∀ x : X, b ^ e • x = 0) →
    Module.length O X ≤
      (e : ℕ∞) * ((Fintype.card ι : ℕ∞) * Module.length O (O ⧸ Ideal.span {b})) := by
  intro e
  induction e with
  | zero =>
    intro X _ _ ι _ g _ hb
    have : Subsingleton X := ⟨fun x y => by
      have hx := hb x
      have hy := hb y
      simp only [pow_zero, one_smul] at hx hy
      rw [hx, hy]⟩
    rw [Module.length_eq_zero_iff.mpr this]
    exact zero_le
  | succ e ih =>
    intro X _ _ ι _ g hg hb
    let φ : X →ₗ[O] X := b • LinearMap.id
    let Y : Submodule O X := LinearMap.range φ
    have hlen := Module.length_eq_add_of_exact Y.subtype Y.mkQ Y.injective_subtype Y.mkQ_surjective
      (LinearMap.exact_subtype_mkQ Y)
    let gY : (ι → O) →ₗ[O] Y := φ.rangeRestrict.comp g
    have hgY : Function.Surjective gY := (LinearMap.surjective_rangeRestrict φ).comp hg
    have hbY : ∀ y : Y, b ^ e • y = 0 := by
      intro y
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp y.2
      apply Subtype.ext
      simp only [Submodule.coe_smul, Submodule.coe_zero]
      rw [← hx]
      show b ^ e • (b • x) = 0
      rw [smul_smul, ← pow_succ]
      exact hb x
    have hY := ih gY hgY hbY
    have hbQ : ∀ z : X ⧸ Y, b • z = 0 := by
      intro z
      obtain ⟨x, rfl⟩ := Y.mkQ_surjective z
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact LinearMap.mem_range.mpr ⟨x, rfl⟩
    have hQ := length_le_of_killed b (Y.mkQ.comp g) (Y.mkQ_surjective.comp hg) hbQ
    rw [hlen]
    calc _ ≤ (e : ℕ∞) * ((Fintype.card ι : ℕ∞) * Module.length O (O ⧸ Ideal.span {b})) +
          (Fintype.card ι : ℕ∞) * Module.length O (O ⧸ Ideal.span {b}) := add_le_add hY hQ
      _ = _ := by push_cast; ring

end Formalism.RepresentationBoundsCohomology.RowCol

open Module in
theorem Formalism.RepresentationBoundsCohomology.rowColength : Formalism.RepresentationBoundsCohomology.StatRowColength := by
  intro O _ _ _ M _ _ _ I ℓ e hI
  classical
  set T := Submodule.torsion O M with hT
  haveI : Module.Free O (M ⧸ T) := Module.free_of_finite_type_torsion_free'
  let bQ := Module.Free.chooseBasis O (M ⧸ T)
  choose m hm using fun i => T.mkQ_surjective (bQ i)
  have hli : LinearIndependent O m := by
    apply LinearIndependent.of_comp T.mkQ
    have hc : T.mkQ ∘ m = bQ := funext hm
    rw [hc]
    exact bQ.linearIndependent
  have hcard := hli.fintype_card_le_finrank
  let G0 : (Module.Free.ChooseBasisIndex O (M ⧸ T) → O) →ₗ[O] M :=
    ∑ i, (LinearMap.toSpanSingleton O M (m i)).comp (LinearMap.proj i)
  have hG0 : ∀ c, G0 c = ∑ i, c i • m i := by
    intro c
    simp [G0]
  let N : Submodule O (M ⧸ I) := LinearMap.range (I.mkQ.comp T.subtype)
  let G : (Module.Free.ChooseBasisIndex O (M ⧸ T) → O) →ₗ[O] ((M ⧸ I) ⧸ N) :=
    N.mkQ.comp (I.mkQ.comp G0)
  have hGs : Function.Surjective G := by
    intro y
    obtain ⟨z, rfl⟩ := N.mkQ_surjective y
    obtain ⟨x, rfl⟩ := I.mkQ_surjective z
    refine ⟨fun i => bQ.repr (T.mkQ x) i, ?_⟩
    have h1 : T.mkQ (G0 (fun i => bQ.repr (T.mkQ x) i)) = T.mkQ x := by
      rw [hG0, map_sum]
      simp only [map_smul, hm]
      exact bQ.sum_repr (T.mkQ x)
    have h2 : G0 (fun i => bQ.repr (T.mkQ x) i) - x ∈ T := by
      rw [← Submodule.Quotient.eq]
      exact h1
    show N.mkQ (I.mkQ (G0 _)) = N.mkQ (I.mkQ x)
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply]
    apply (Submodule.Quotient.eq N).mpr
    refine LinearMap.mem_range.mpr ⟨⟨_, h2⟩, ?_⟩
    simp
  have hGk : ∀ p : (M ⧸ I) ⧸ N, ((ℓ : O) ^ e) • p = 0 := by
    intro p
    obtain ⟨z, rfl⟩ := N.mkQ_surjective p
    obtain ⟨x, rfl⟩ := I.mkQ_surjective z
    have h0 : I.mkQ (((ℓ : O) ^ e) • x) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hI x
    rw [← map_smul, ← map_smul, h0, map_zero]
  have hP := Formalism.RepresentationBoundsCohomology.RowCol.length_le_of_killed_pow ((ℓ : O)) e G hGs hGk
  have hlen := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
    (LinearMap.exact_subtype_mkQ N)
  have hN : Module.length O N ≤ Module.length O T :=
    Module.length_le_of_surjective (I.mkQ.comp T.subtype).rangeRestrict
      (LinearMap.surjective_rangeRestrict _)
  rw [hlen, add_comm]
  refine add_le_add ?_ hN
  have hcard' : ((Fintype.card (Module.Free.ChooseBasisIndex O (M ⧸ T)) : ℕ) : ℕ∞) ≤
      (Module.finrank O M : ℕ∞) := by exact_mod_cast hcard
  calc _ ≤ (e : ℕ∞) * ((Fintype.card (Module.Free.ChooseBasisIndex O (M ⧸ T)) : ℕ∞) *
        Module.length O (O ⧸ Ideal.span {(ℓ : O)})) := hP
    _ = (Fintype.card (Module.Free.ChooseBasisIndex O (M ⧸ T)) : ℕ∞) *
        ((e : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})) := mul_left_comm _ _ _
    _ ≤ _ := mul_le_mul' hcard' le_rfl
