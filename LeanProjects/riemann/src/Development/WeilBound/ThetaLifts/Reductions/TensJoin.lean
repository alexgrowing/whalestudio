import Development.WeilBound.ThetaLifts.CartanFactorisation.TensMax

noncomputable section

open scoped TensorProduct
open PiTensorProduct

namespace PositivityTheory.ThKR.Join

open PositivityTheory.ThKF.Unit

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem upd_comp (u : ∀ j, V j →ₗ[ℂ] V j) (i : ι) (a : V i →ₗ[ℂ] V i) :
    map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i a) ∘ₗ map u = map (Function.update u i (a ∘ₗ u i)) := by
  rw [← map_comp]
  congr 1
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem position_st {A : ι → Type} (act : ∀ i, A i → Module.End ℂ (V i)) (P : Submodule ℂ (⨂[ℂ] i, V i))
    (hP : ∀ i a, ∀ x ∈ P, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ P) (i : ι)
    (u : Module.End ℂ (V i)) (hu : u ∈ Algebra.adjoin ℂ (Set.range (act i))) :
    ∀ x ∈ P, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i u) x ∈ P := by
  induction hu using Algebra.adjoin_induction with
  | mem u hu => obtain ⟨a, rfl⟩ := hu; exact hP i a
  | algebraMap c =>
    intro x hx
    rw [Algebra.algebraMap_eq_smul_one, PiTensorProduct.map_update_smul, show (1 : Module.End ℂ (V i)) = LinearMap.id from rfl,
      Function.update_eq_self, map_id]
    exact P.smul_mem c hx
  | add a b _ _ ha hb =>
    intro x hx
    rw [PiTensorProduct.map_update_add]
    exact P.add_mem (ha x hx) (hb x hx)
  | mul a b _ _ ha hb =>
    intro x hx
    have := LinearMap.congr_fun (upd_comp (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i b) i a) x
    rw [Function.update_idem, Function.update_self] at this
    exact (show _ = map (Function.update _ i (a * b)) x from this) ▸ ha _ (hb x hx)

theorem map_st {A : ι → Type} (act : ∀ i, A i → Module.End ℂ (V i)) (P : Submodule ℂ (⨂[ℂ] i, V i))
    (hP : ∀ i a, ∀ x ∈ P, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ P)
    (u : ∀ i, Module.End ℂ (V i)) (hu : ∀ i, u i ∈ Algebra.adjoin ℂ (Set.range (act i))) : ∀ x ∈ P, map u x ∈ P := by
  have h : ∀ S : Finset ι, ∀ x ∈ P, map (fun i => if i ∈ S then u i else (LinearMap.id : V i →ₗ[ℂ] V i)) x ∈ P := fun S => by
    induction S using Finset.induction_on with
    | empty => intro x hx; simpa using hx
    | insert j S hj ih =>
      intro x hx
      have h1 := position_st act P hP j (u j) (hu j) _ (ih x hx)
      rw [← LinearMap.comp_apply, upd_comp] at h1
      have e : (fun i => if i ∈ insert j S then u i else (LinearMap.id : V i →ₗ[ℂ] V i)) =
          Function.update (fun i => if i ∈ S then u i else (LinearMap.id : V i →ₗ[ℂ] V i)) j
            (u j ∘ₗ if j ∈ S then u j else LinearMap.id) := by
        funext i
        by_cases h : i = j
        · subst h; simp [hj]
        · simp [h]
      rw [e]
      exact h1
  simpa using h Finset.univ

theorem tens_join {A : ι → Type} (act : ∀ i, A i → Module.End ℂ (V i)) (K Z : ∀ i, Submodule ℂ (V i))
    (hr : ∀ i, Module.rank ℂ (V i) ≤ Cardinal.aleph0) (h1 : ∀ i, K i ≠ ⊤) (h2 : ∀ i a, ∀ x ∈ K i, act i a x ∈ K i)
    (h3 : ∀ i N, K i ≤ N → (∀ a, ∀ x ∈ N, act i a x ∈ N) → N = K i ∨ N = ⊤) (v : ∀ i, V i)
    (h4 : ∀ i (t : List (V i)), (∀ x ∈ t, x ∈ K i) → ∀ y,
      ∃ u ∈ Algebra.adjoin ℂ (Set.range (act i)), u (v i) - y ∈ Z i ∧ ∀ x ∈ t, u x ∈ Z i)
    (P P' : Submodule ℂ (⨂[ℂ] i, V i)) (hZ : ∀ (f : ∀ i, V i) i, f i ∈ Z i → tprod ℂ f ∈ P)
    (hZ' : ∀ (f : ∀ i, V i) i, f i ∈ Z i → tprod ℂ f ∈ P')
    (hP : ∀ i a, ∀ x ∈ P, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ P)
    (hP' : ∀ i a, ∀ x ∈ P', map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ P')
    (e : P ⊔ P' = ⊤) : P = ⊤ ∨ P' = ⊤ := by
  let R : Submodule ℂ (⨂[ℂ] i, V i) := Submodule.span ℂ {x | ∃ (f : ∀ i, V i) (i : ι), f i ∈ K i ∧ x = tprod ℂ f}
  have hR : ∀ (f : ∀ i, V i) i, f i ∈ K i → tprod ℂ f ∈ R := fun f i h => Submodule.subset_span ⟨f, i, h, rfl⟩
  have Rst : ∀ i a, R ≤ R.comap (map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a))) := fun i a =>
    Submodule.span_le.2 (by
      rintro _ ⟨f, j, hj, rfl⟩
      show map _ (tprod ℂ f) ∈ R
      rw [map_tprod]
      refine hR _ j ?_
      by_cases h : j = i
      · subst h; simpa using h2 j a _ hj
      · simpa [Function.update_of_ne h] using hj)
  have nak : ∀ Q : Submodule ℂ (⨂[ℂ] i, V i), (∀ (f : ∀ i, V i) i, f i ∈ Z i → tprod ℂ f ∈ Q) →
      (∀ i a, ∀ x ∈ Q, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ Q) →
      Q ⊔ R = ⊤ → Q = ⊤ := fun Q q1 q2 q3 => by
    have fin : ∀ x ∈ R, ∃ t : ∀ i, List (V i), (∀ i, ∀ y ∈ t i, y ∈ K i) ∧
        ∀ u : ∀ i, Module.End ℂ (V i), (∀ i, ∀ y ∈ t i, u i y ∈ Z i) → map u x ∈ Q := fun x hx => by
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, i, hi, rfl⟩ := hx
        refine ⟨Function.update (fun _ => []) i [f i], fun j y hy => ?_, fun u hu => ?_⟩
        · by_cases h : j = i
          · subst h
            rw [Function.update_self, List.mem_singleton] at hy
            exact hy ▸ hi
          · simp [Function.update_of_ne h] at hy
        · rw [map_tprod]
          exact q1 _ i (hu i _ (by simp))
      | zero => exact ⟨fun _ => [], by simp, fun u _ => by simp⟩
      | add a b _ _ ha hb =>
        obtain ⟨s, s1, s2⟩ := ha
        obtain ⟨t, t1, t2⟩ := hb
        refine ⟨fun i => s i ++ t i, fun i y hy => (List.mem_append.1 hy).elim (s1 i y) (t1 i y), fun u hu => ?_⟩
        rw [map_add]
        exact Q.add_mem (s2 u fun i y hy => hu i y (List.mem_append_left _ hy))
          (t2 u fun i y hy => hu i y (List.mem_append_right _ hy))
      | smul c a _ ha =>
        obtain ⟨s, s1, s2⟩ := ha
        exact ⟨s, s1, fun u hu => by rw [map_smul]; exact Q.smul_mem c (s2 u hu)⟩
    obtain ⟨p, hp, x, hx, e⟩ := Submodule.mem_sup.1 (q3 ▸ Submodule.mem_top : tprod ℂ v ∈ Q ⊔ R)
    obtain ⟨t, t1, t2⟩ := fin x hx
    refine eq_top_iff.2 fun y _ => ?_
    induction y using PiTensorProduct.induction_on with
    | smul_tprod c f =>
      choose u u1 u2 u3 using fun i => h4 i (t i) (t1 i) (f i)
      have a1 : map u (tprod ℂ v) ∈ Q := by
        rw [← e, map_add]
        exact Q.add_mem (map_st act Q q2 u u1 p hp) (t2 u u3)
      have a2 : map u (tprod ℂ v) - tprod ℂ f ∈ Q := ker_le Z Q q1 (by
        rw [LinearMap.mem_ker, map_sub, map_tprod, map_tprod, map_tprod, sub_eq_zero]
        congr 1
        funext i
        exact (Submodule.Quotient.eq _).2 (u2 i))
      exact Q.smul_mem c (by simpa using Q.sub_mem a1 a2)
    | add x y hx hy => exact Q.add_mem (hx trivial) (hy trivial)
  have le : ∀ Q : Submodule ℂ (⨂[ℂ] i, V i), (∀ (f : ∀ i, V i) i, f i ∈ Z i → tprod ℂ f ∈ Q) →
      (∀ i a, ∀ x ∈ Q, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ Q) →
      Q ≤ R ∨ Q = ⊤ := fun Q q1 q2 =>
    (tens_max act K hr h1 h2 h3 R hR (Q ⊔ R) le_sup_right (fun i a x hx => by
      obtain ⟨p, hp, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add]
      exact Submodule.add_mem_sup (q2 i a p hp) (Rst i a hy))).imp (le_sup_left.trans ·) (nak Q q1 q2)
  rcases le P hZ hP with a | a
  · rcases le P' hZ' hP' with b | b
    · exact Or.inl (nak P hZ hP (top_le_iff.1 (e ▸ sup_le le_sup_left (b.trans le_sup_right))))
    · exact Or.inr b
  · exact Or.inl a

end PositivityTheory.ThKR.Join

end
