import Mathlib

open Module

namespace UpperTheory.V.Z.Sym.Tf

variable {Λ M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]

private theorem iter_lemma (n : Λ → End ℂ M) (Θ : End ℂ M) (σ : Λ → Λ) (h : ∀ a, Θ * n a = n (σ a) * Θ) :
    ∀ (k : ℕ) (b : Λ), Θ ^ k * n b = n (σ^[k] b) * Θ ^ k := by
  intro k
  induction k with
  | zero => intro b; simp
  | succ k ih =>
    intro b
    rw [pow_succ, mul_assoc, h, ← mul_assoc, ih, mul_assoc, Function.iterate_succ_apply]

private theorem mul_pow_eq_prod_range_iterate_mul_pow_of_semiconj (n : Λ → End ℂ M) (Θ : End ℂ M) (σ : Λ → Λ) (h : ∀ a, Θ * n a = n (σ a) * Θ)
    (a : Λ) : ∀ k : ℕ, (n a * Θ) ^ k = ((List.range k).map (fun i => n (σ^[i] a))).prod * Θ ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, mul_assoc, ← mul_assoc (Θ ^ k), iter_lemma n Θ σ h]
    simp [List.range_succ, pow_succ, mul_assoc]

private theorem list_prod_mem_ideal_pow_length {R : Type} [CommRing R] (I : Ideal R) :
    ∀ l : List R, (∀ x ∈ l, x ∈ I) → l.prod ∈ I ^ l.length := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x l ih =>
    intro hl
    rw [List.prod_cons, List.length_cons, pow_succ']
    exact Ideal.mul_mem_mul (hl x (by simp)) (ih fun y hy => hl y (by simp [hy]))

private theorem exists_prod_range_iterate_eq_zero_of_commute_of_isNilpotent (n : Λ → End ℂ M) (σ : Λ → Λ) (hc : ∀ a b, Commute (n a) (n b))
    (hn : ∀ a, IsNilpotent (n a)) (a : Λ) :
    ∃ m : ℕ, ((List.range m).map (fun i => n (σ^[i] a))).prod = 0 := by
  let A := Algebra.adjoin ℂ (Set.range n)
  letI : CommRing A := Algebra.adjoinCommRingOfComm ℂ (by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact hc x y)
  haveI : IsArtinianRing A := IsArtinianRing.of_finite ℂ A
  obtain ⟨m, hm⟩ := IsArtinianRing.isNilpotent_nilradical (R := A)
  let g : ℕ → A := fun i => ⟨n (σ^[i] a), Algebra.subset_adjoin ⟨σ^[i] a, rfl⟩⟩
  have hmem : ∀ i, g i ∈ nilradical A := by
    intro i
    obtain ⟨k, hk⟩ := hn (σ^[i] a)
    exact ⟨k, Subtype.ext (by simpa [g] using hk)⟩
  have hP := list_prod_mem_ideal_pow_length (nilradical A) ((List.range m).map g) (by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hmem i)
  simp only [List.length_map, List.length_range, hm, Ideal.zero_eq_bot, Ideal.mem_bot] at hP
  refine ⟨m, ?_⟩
  have h2 := congrArg A.val hP
  rw [map_list_prod, map_zero, List.map_map] at h2
  exact h2

theorem trace_nil (n : Λ → End ℂ M) (Θ : End ℂ M) (σ : Λ → Λ) (hc : ∀ a b, Commute (n a) (n b)) (hn : ∀ a, IsNilpotent (n a))
    (h : ∀ a, Θ * n a = n (σ a) * Θ) (a : Λ) : LinearMap.trace ℂ M (n a * Θ) = 0 := by
  obtain ⟨m, hm⟩ := exists_prod_range_iterate_eq_zero_of_commute_of_isNilpotent n σ hc hn a
  have hnil : IsNilpotent (n a * Θ) := ⟨m, by rw [mul_pow_eq_prod_range_iterate_mul_pow_of_semiconj n Θ σ h a m, hm, zero_mul]⟩
  exact (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero

abbrev Vg (u : Λ → End ℂ M) (χ : Λ → ℂ) : Submodule ℂ M := ⨅ a, (u a).maxGenEigenspace (χ a)

theorem Vg_maps {u : Λ → End ℂ M} (hc : ∀ a b, Commute (u a) (u b)) (a : Λ) (χ : Λ → ℂ) : Set.MapsTo (u a) (Vg u χ) (Vg u χ) := by
  intro v hv
  simp only [Vg, SetLike.mem_coe, Submodule.mem_iInf] at hv ⊢
  intro b
  exact Module.End.mapsTo_maxGenEigenspace_of_comm (hc b a) (χ b) (hv b)

theorem Vg_indep {u : Λ → End ℂ M} (hc : ∀ a b, Commute (u a) (u b)) : iSupIndep (Vg u) :=
  End.independent_iInf_maxGenEigenspace_of_forall_mapsTo u fun i j φ => End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ

theorem Vg_int [DecidableEq (Λ → ℂ)] {u : Λ → End ℂ M} (hc : ∀ a b, Commute (u a) (u b)) : DirectSum.IsInternal (Vg u) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (Vg_indep hc)
  exact Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute u
    (fun i j _ => hc i j) (fun i => Module.End.iSup_maxGenEigenspace_eq_top (u i))

theorem trace_Vg {u : Λ → End ℂ M} (hc : ∀ a b, Commute (u a) (u b)) (χ : Λ → ℂ) (Θ : End ℂ M) (σ : Λ → Λ)
    (hΘ : Set.MapsTo Θ (Vg u χ) (Vg u χ)) (h : ∀ a, ∀ v ∈ Vg u χ, Θ (u a v) = u (σ a) (Θ v)) (hχ : ∀ a, χ (σ a) = χ a) (a : Λ)
    (h' : Set.MapsTo (u a * Θ) (Vg u χ) (Vg u χ)) :
    LinearMap.trace ℂ (Vg u χ) ((u a * Θ).restrict h') = LinearMap.trace ℂ (Vg u χ) (Θ.restrict hΘ) * χ a := by
  have key : ∀ (f : End ℂ M) (hf : Set.MapsTo f (Vg u χ) (Vg u χ)) (x : Vg u χ),
      ((f.restrict hf x : Vg u χ) : M) = f x := fun _ _ _ => rfl
  have hNm : ∀ b, Set.MapsTo (u b - algebraMap ℂ (End ℂ M) (χ b)) (Vg u χ) (Vg u χ) := by
    intro b v hv
    have h1 := Vg_maps hc b χ hv
    simp only [SetLike.mem_coe] at h1 hv ⊢
    simp only [LinearMap.sub_apply, Module.algebraMap_end_apply]
    exact Submodule.sub_mem _ h1 (Submodule.smul_mem _ _ hv)
  let N : Λ → End ℂ (Vg u χ) := fun b => (u b - algebraMap ℂ (End ℂ M) (χ b)).restrict (hNm b)
  let T : End ℂ (Vg u χ) := Θ.restrict hΘ
  have hNc : ∀ b c, Commute (N b) (N c) := by
    intro b c
    show N b * N c = N c * N b
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    have e := LinearMap.congr_fun (hc b c).eq (w : M)
    simp only [Module.End.mul_apply] at e
    simp only [N, Module.End.mul_apply, key, LinearMap.sub_apply,
      Module.algebraMap_end_apply, map_sub, map_smul, e]
    module
  have hNn : ∀ b, IsNilpotent (N b) := by
    intro b
    exact Module.End.isNilpotent_restrict_of_le (q := (u b).maxGenEigenspace (χ b)) (iInf_le _ b)
      ((u b).isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (χ b))
  have hTN : ∀ b, T * N b = N (σ b) * T := by
    intro b
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    have e := h b w w.2
    simp only [T, N, Module.End.mul_apply, key, LinearMap.sub_apply,
      Module.algebraMap_end_apply, map_sub, map_smul, e]
    rw [hχ]
  have hsplit : (u a * Θ).restrict h' = N a * T + χ a • T := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp only [N, T, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Submodule.coe_add, Submodule.coe_smul, key, LinearMap.sub_apply,
      Module.algebraMap_end_apply]
    abel
  rw [hsplit, map_add, map_smul, trace_nil N T σ hNc hNn hTN a, zero_add, smul_eq_mul, mul_comm]

end UpperTheory.V.Z.Sym.Tf
