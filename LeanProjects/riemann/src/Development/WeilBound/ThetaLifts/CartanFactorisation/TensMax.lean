import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.Tensor

noncomputable section

open scoped TensorProduct
open PiTensorProduct

namespace PositivityTheory.ThKF.Unit

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem ker_le (K : ∀ i, Submodule ℂ (V i)) (R : Submodule ℂ (⨂[ℂ] i, V i)) (hR : ∀ (f : ∀ i, V i) i, f i ∈ K i → tprod ℂ f ∈ R) :
    LinearMap.ker (map fun i => (K i).mkQ) ≤ R := by
  choose σ hσ using fun i => (K i).mkQ.exists_rightInverse_of_surjective (K i).range_mkQ
  have hd : ∀ i x, x - σ i ((K i).mkQ x) ∈ K i := fun i x => by
    rw [← Submodule.Quotient.mk_eq_zero]
    show (K i).mkQ _ = 0
    rw [map_sub, ← LinearMap.comp_apply (K i).mkQ (σ i), hσ, LinearMap.id_apply, sub_self]
  have h1 : ∀ (f : ∀ i, V i) (S : Finset ι), tprod ℂ f - tprod ℂ (fun i => if i ∈ S then σ i ((K i).mkQ (f i)) else f i) ∈ R := by
    intro f S
    induction S using Finset.induction_on with
    | empty => simp
    | insert j S hj ih =>
      let g : ∀ i, V i := fun i => if i ∈ S then σ i ((K i).mkQ (f i)) else f i
      have e1 : g = Function.update g j (f j) := by
        rw [eq_comm, Function.update_eq_self_iff]; simp [g, hj]
      have e2 : (fun i => if i ∈ insert j S then σ i ((K i).mkQ (f i)) else f i) = Function.update g j (σ j ((K j).mkQ (f j))) := by
        funext i
        by_cases h : i = j
        · subst h; simp
        · simp [g, h]
      have h3 := hR (Function.update g j (f j - σ j ((K j).mkQ (f j)))) j (by simpa using hd j (f j))
      rw [MultilinearMap.map_update_sub, ← e1, ← e2] at h3
      have h4 := R.add_mem (show tprod ℂ f - tprod ℂ g ∈ R from ih) h3
      rwa [sub_add_sub_cancel] at h4
  have h2 : ∀ x, x - map σ (map (fun i => (K i).mkQ) x) ∈ R := fun x => by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod c f =>
      rw [map_smul, map_smul, ← smul_sub, map_tprod, map_tprod]
      simpa using R.smul_mem c (h1 f Finset.univ)
    | add x y hx hy => rw [map_add, map_add, add_sub_add_comm]; exact R.add_mem hx hy
  intro x hx
  have := h2 x
  rwa [LinearMap.mem_ker.1 hx, map_zero, sub_zero] at this

theorem tens_max {A : ι → Type} (act : ∀ i, A i → Module.End ℂ (V i)) (K : ∀ i, Submodule ℂ (V i))
    (hr : ∀ i, Module.rank ℂ (V i) ≤ Cardinal.aleph0) (h1 : ∀ i, K i ≠ ⊤) (h2 : ∀ i a, ∀ x ∈ K i, act i a x ∈ K i)
    (h3 : ∀ i N, K i ≤ N → (∀ a, ∀ x ∈ N, act i a x ∈ N) → N = K i ∨ N = ⊤)
    (R : Submodule ℂ (⨂[ℂ] i, V i)) (hR : ∀ (f : ∀ i, V i) i, f i ∈ K i → tprod ℂ f ∈ R) (P : Submodule ℂ (⨂[ℂ] i, V i))
    (hRP : R ≤ P)
    (hP : ∀ i a, ∀ x ∈ P, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ P) :
    P ≤ R ∨ P = ⊤ := by
  let q : ∀ i, A i → Module.End ℂ (V i ⧸ K i) := fun i a => (K i).mapQ (K i) (act i a) (h2 i a)
  let π := map fun i => (K i).mkQ
  have hk := ker_le K R hR
  have := PositivityTheory.KReal.tensorIrr ι A (fun i => V i ⧸ K i) q (fun i => (rank_quotient_le _).trans (hr i))
    (fun i => Submodule.Quotient.nontrivial_iff.2 (h1 i))
    (fun i N hN => by
      rcases h3 i (N.comap (K i).mkQ) (fun x hx => by simp [(Submodule.Quotient.mk_eq_zero _).2 hx])
        (fun a x hx => hN a _ hx) with e | e
      · refine Or.inl (eq_bot_iff.2 fun y hy => ?_)
        obtain ⟨x, rfl⟩ := (K i).mkQ_surjective y
        exact (Submodule.Quotient.mk_eq_zero _).2 (e ▸ hy : x ∈ K i)
      · refine Or.inr (eq_top_iff.2 fun y _ => ?_)
        obtain ⟨x, rfl⟩ := (K i).mkQ_surjective y
        exact (e ▸ Submodule.mem_top : x ∈ N.comap (K i).mkQ))
    (P.map π) (by
      rintro i a _ ⟨x, hx, rfl⟩
      refine ⟨_, hP i a x hx, ?_⟩
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← map_comp, ← map_comp]
      congr 2
      funext j
      by_cases h : j = i
      · subst h; simp only [Function.update_self]; rfl
      · simp [Function.update_of_ne h])
  rcases this with e | e
  · exact Or.inl fun x hx => hk ((Submodule.eq_bot_iff _).1 e _ ⟨x, hx, rfl⟩)
  · refine Or.inr (eq_top_iff.2 fun x _ => ?_)
    obtain ⟨y, hy, e'⟩ : π x ∈ P.map π := e ▸ Submodule.mem_top
    have : x - y ∈ P := hRP (hk (show π (x - y) = 0 by rw [map_sub, e', sub_self]))
    simpa using P.add_mem this hy

end PositivityTheory.ThKF.Unit

end
