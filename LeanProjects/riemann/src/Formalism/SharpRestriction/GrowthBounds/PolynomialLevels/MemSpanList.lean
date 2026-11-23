import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.CommPresIsoSub

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.NormalSetCounting

open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords

section JU

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (E : ι → GLOps n K V) (ee : ι → (Fin n → ℤ) → Module.End K V)

theorem ee_pres (hee : ∀ i mu, IsIsoProj (E i) mu (ee i mu))
    (hdec : ∀ i (G : V), ∃ T : Finset (Fin n → ℤ), G = ∑ mu ∈ T, ee i mu G ∧ ∀ mu, ee i mu G ∈ isoSub (E i) mu)
    (hcomm : ∀ i i' mu mu', ee i mu * ee i' mu' = ee i' mu' * ee i mu)
    (i i' : ι) (mu nu : Fin n → ℤ) (x : V) (hx : x ∈ isoSub (E i') nu) : ee i mu x ∈ isoSub (E i') nu := by
  obtain ⟨_, _, h2⟩ := hdec i' (ee i mu x)
  have h1 : ee i' nu x = x := (hee i' nu).1 x hx
  have h3 : ee i mu x = ee i' nu (ee i mu x) := by
    have h4 := congrArg (fun f : Module.End K V => f x) (hcomm i i' mu nu)
    simp only [Module.End.mul_apply] at h4
    rw [← h4, h1]
  rw [h3]
  exact h2 nu

theorem mem_span_list (hee : ∀ i mu, IsIsoProj (E i) mu (ee i mu))
    (hdec : ∀ i (G : V), ∃ T : Finset (Fin n → ℤ), G = ∑ mu ∈ T, ee i mu G ∧ ∀ mu, ee i mu G ∈ isoSub (E i) mu)
    (hcomm : ∀ i i' mu mu', ee i mu * ee i' mu' = ee i' mu' * ee i mu) (l : List ι) (y : V) :
    y ∈ Submodule.span K {x : V | ∃ lam : ι → Fin n → ℤ, ∀ i ∈ l, x ∈ isoSub (E i) (lam i)} := by
  induction l generalizing y with
  | nil => exact Submodule.subset_span ⟨fun _ _ => 0, by simp⟩
  | cons i l ih =>
    have key : Submodule.span K {x : V | ∃ lam : ι → Fin n → ℤ, ∀ j ∈ l, x ∈ isoSub (E j) (lam j)} ≤
        Submodule.span K {x : V | ∃ lam : ι → Fin n → ℤ, ∀ j ∈ i :: l, x ∈ isoSub (E j) (lam j)} := by
      rw [Submodule.span_le]
      rintro x ⟨lam, hlam⟩
      obtain ⟨T, hT, hmem⟩ := hdec i x
      show x ∈ Submodule.span K {x : V | ∃ lam : ι → Fin n → ℤ, ∀ j ∈ i :: l, x ∈ isoSub (E j) (lam j)}
      rw [hT]
      refine Submodule.sum_mem _ fun mu _ => Submodule.subset_span ⟨Function.update lam i mu, ?_⟩
      intro j hj
      by_cases hji : j = i
      · subst hji
        rw [Function.update_self]
        exact hmem mu
      · rw [Function.update_of_ne hji]
        exact ee_pres E ee hee hdec hcomm i j mu (lam j) x (hlam j ((List.mem_cons.mp hj).resolve_left hji))
    exact key (ih y)

private theorem list_prod_isoProj_apply_eq_ite (hee : ∀ i mu, IsIsoProj (E i) mu (ee i mu)) (ka lam : ι → Fin n → ℤ) (x : V)
    (hx : ∀ i, x ∈ isoSub (E i) (lam i)) (l : List ι) :
    (l.map (fun i => ee i (ka i))).prod x = if ∀ i ∈ l, lam i = ka i then x else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih]
    by_cases h : ∀ i ∈ l, lam i = ka i
    · rw [if_pos h]
      by_cases ha : lam a = ka a
      · have hall : ∀ i ∈ a :: l, lam i = ka i := by
          intro i hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact ha
          · exact h i hi
        rw [if_pos hall]
        exact (hee a (ka a)).1 x (by rw [← ha]; exact hx a)
      · have hno : ¬ ∀ i ∈ a :: l, lam i = ka i := fun hh => ha (hh a (List.mem_cons.mpr (Or.inl rfl)))
        rw [if_neg hno]
        exact (hee a (ka a)).2 (lam a) ha x (hx a)
    · have hno : ¬ ∀ i ∈ a :: l, lam i = ka i := fun hh => h fun i hi => hh i (List.mem_cons.mpr (Or.inr hi))
      rw [if_neg h, if_neg hno, map_zero]

theorem jproj_eq (hee : ∀ i mu, IsIsoProj (E i) mu (ee i mu))
    (hdec : ∀ i (G : V), ∃ T : Finset (Fin n → ℤ), G = ∑ mu ∈ T, ee i mu G ∧ ∀ mu, ee i mu G ∈ isoSub (E i) mu)
    (hcomm : ∀ i i' mu mu', ee i mu * ee i' mu' = ee i' mu' * ee i mu) (ka : ι → Fin n → ℤ)
    (e : Module.End K V) (he : IsJProj E {ka} e) (y : V) : e y = jointE ee ka y := by
  have hy := mem_span_list E ee hee hdec hcomm Finset.univ.toList y
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨lam, hlam⟩ := hx
    have hx' : ∀ i, x ∈ isoSub (E i) (lam i) := fun i => hlam i (Finset.mem_toList.mpr (Finset.mem_univ i))
    have hxj : x ∈ jIso E lam := by
      simp only [jIso, Submodule.mem_iInf]
      exact hx'
    unfold jointE
    rw [list_prod_isoProj_apply_eq_ite E ee hee ka lam x hx']
    by_cases h : lam = ka
    · rw [if_pos (fun i _ => congrFun h i)]
      exact he.1 lam h x hxj
    · have hno : ¬ ∀ i ∈ (Finset.univ : Finset ι).toList, lam i = ka i :=
        fun hh => h (funext fun i => hh i (Finset.mem_toList.mpr (Finset.mem_univ i)))
      rw [if_neg hno]
      exact he.2 lam h x hxj
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
  | smul c a _ ha => rw [map_smul, map_smul, ha]

theorem jproj_ne (hee : ∀ i mu, IsIsoProj (E i) mu (ee i mu))
    (hdec : ∀ i (G : V), ∃ T : Finset (Fin n → ℤ), G = ∑ mu ∈ T, ee i mu G ∧ ∀ mu, ee i mu G ∈ isoSub (E i) mu)
    (hcomm : ∀ i i' mu mu', ee i mu * ee i' mu' = ee i' mu' * ee i mu) (ka : ι → Fin n → ℤ)
    (e : Module.End K V) (he : IsJProj E {ka} e) (y : V) (hy : e y ≠ 0) (i : ι) : ee i (ka i) y ≠ 0 := by
  intro h0
  apply hy
  have hfix : ∀ z : V, ee i (ka i) (jointE ee ka z) = jointE ee ka z := by
    intro z
    have hz := mem_span_list E ee hee hdec hcomm Finset.univ.toList z
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨lam, hlam⟩ := hx
      have hx' : ∀ j, x ∈ isoSub (E j) (lam j) := fun j => hlam j (Finset.mem_toList.mpr (Finset.mem_univ j))
      unfold jointE
      rw [list_prod_isoProj_apply_eq_ite E ee hee ka lam x hx']
      split_ifs with h
      · exact (hee i (ka i)).1 x (by rw [← h i (Finset.mem_toList.mpr (Finset.mem_univ i))]; exact hx' i)
      · exact map_zero _
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
    | smul c a _ ha => rw [map_smul, map_smul, ha]
  have hc : Commute (ee i (ka i)) (jointE ee ka) := by
    unfold jointE
    apply Commute.list_prod_right
    intro b hb
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hb
    exact hcomm i j (ka i) (ka j)
  rw [jproj_eq E ee hee hdec hcomm ka e he y, ← hfix y, ← Module.End.mul_apply, hc.eq, Module.End.mul_apply, h0, map_zero]

end JU

end Formalism.MainNotions.NormalSetCounting
