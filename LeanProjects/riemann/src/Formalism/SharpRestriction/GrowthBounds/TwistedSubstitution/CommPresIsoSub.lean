import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.PlaneCoeff

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.G

section Commutant

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V)

theorem comm_Umon (A : Module.End K V) (hA : ∀ a b, A * E a b = E a b * A) : ∀ u ∈ Umon E, A * u = u * A := by
  intro u hu
  unfold Umon at hu
  induction hu using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨ab, rfl⟩ := hx
    exact hA ab.1 ab.2
  | one => simp
  | mul x y _ _ hx hy => rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]

theorem umon_mul_E (u : Module.End K V) (hu : u ∈ Umon E) (a b : Fin n) : E a b * u ∈ Umon E :=
  Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu

theorem E_pres_isoSub (a b : Fin n) (mu : Fin n → ℤ) : ∀ x ∈ isoSub E mu, E a b x ∈ isoSub E mu := by
  intro x hx
  unfold isoSub at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hy
    apply Submodule.subset_span
    exact ⟨E a b * u, umon_mul_E E u hu a b, v, hv, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

theorem comm_pres_isoSub (A : Module.End K V) (hA : ∀ a b, A * E a b = E a b * A) (mu : Fin n → ℤ) :
    ∀ x ∈ isoSub E mu, A x ∈ isoSub E mu := by
  intro x hx
  unfold isoSub at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hy
    have h1 : A (u v) = u (A v) := by
      have := comm_Umon E A hA u hu
      simpa only [Module.End.mul_apply] using congrArg (fun f => f v) this
    rw [h1]
    by_cases h0 : A v = 0
    · rw [h0, map_zero]; exact Submodule.zero_mem _
    · apply Submodule.subset_span
      refine ⟨u, hu, A v, ⟨h0, ?_, ?_⟩, rfl⟩
      · have hw := hv.2.1
        simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker] at hw ⊢
        intro a
        have hc : E a a (A v) = A (E a a v) := by
          simpa only [Module.End.mul_apply] using (congrArg (fun f => f v) (hA a a)).symm
        have hwa := hw a
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hwa ⊢
        rw [hc, ← map_smul, ← map_sub, hwa, map_zero]
      · intro a b hab
        have hc : E a b (A v) = A (E a b v) := by
          simpa only [Module.End.mul_apply] using (congrArg (fun f => f v) (hA a b)).symm
        rw [hc, hv.2.2 a b hab, map_zero]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

theorem comm_isoProj (A : Module.End K V) (hA : ∀ mu, ∀ x ∈ isoSub E mu, A x ∈ isoSub E mu)
    (ee : (Fin n → ℤ) → Module.End K V) (hee : ∀ mu, IsIsoProj E mu (ee mu))
    (hdec : ∀ G : V, ∃ T : Finset (Fin n → ℤ), G = ∑ mu ∈ T, ee mu G ∧ ∀ mu, ee mu G ∈ isoSub E mu)
    (lam : Fin n → ℤ) : ee lam * A = A * ee lam := by
  have hproj : ∀ mu y, y ∈ isoSub E mu → ee lam y = if mu = lam then y else 0 := by
    intro mu y hy
    split_ifs with h
    · subst h; exact (hee mu).1 y hy
    · exact (hee lam).2 mu h y hy
  refine LinearMap.ext fun x => ?_
  obtain ⟨T, hx, hm⟩ := hdec x
  simp only [Module.End.mul_apply]
  have hAx : A x = ∑ mu ∈ T, A (ee mu x) := by
    conv_lhs => rw [hx]
    rw [map_sum]
  have hex : ee lam x = ∑ mu ∈ T, ee lam (ee mu x) := by
    conv_lhs => rw [hx]
    rw [map_sum]
  rw [hAx, hex, map_sum, map_sum]
  refine Finset.sum_congr rfl fun mu _ => ?_
  rw [hproj mu _ (hA mu _ (hm mu)), hproj mu _ (hm mu)]
  split_ifs <;> simp

theorem isoProj_comm_E (ee : (Fin n → ℤ) → Module.End K V) (hee : ∀ mu, IsIsoProj E mu (ee mu))
    (hdec : ∀ G : V, ∃ T : Finset (Fin n → ℤ), G = ∑ mu ∈ T, ee mu G ∧ ∀ mu, ee mu G ∈ isoSub E mu)
    (lam : Fin n → ℤ) (a b : Fin n) : ee lam * E a b = E a b * ee lam :=
  comm_isoProj E (E a b) (fun mu => E_pres_isoSub E a b mu) ee hee hdec lam

end Commutant

section Family

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (E : ι → GLOps n K V) (ee : ι → (Fin n → ℤ) → Module.End K V)

def jointE (ka : ι → Fin n → ℤ) : Module.End K V :=
  ((Finset.univ : Finset ι).toList.map fun i => ee i (ka i)).prod

theorem prod_split (l : List (Module.End K V)) (hl : ∀ x ∈ l, ∀ y ∈ l, x * y = y * x) (a : Module.End K V)
    (ha : a ∈ l) : ∃ rest : Module.End K V, l.prod = a * rest ∧ l.prod = rest * a := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    have hcl : ∀ x ∈ l, ∀ y ∈ l, x * y = y * x := fun x hx y hy =>
      hl x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
    have hcomm : ∀ c ∈ b :: l, c * l.prod = l.prod * c := by
      intro c hc
      have : Commute c l.prod := Commute.list_prod_right _ _ fun y hy => hl c hc y (List.mem_cons_of_mem _ hy)
      exact this.eq
    rcases List.mem_cons.1 ha with h | h
    · subst h
      exact ⟨l.prod, by simp, by rw [List.prod_cons, hcomm a (List.mem_cons_self)]⟩
    · obtain ⟨rest, h1, h2⟩ := ih hcl h
      refine ⟨b * rest, ?_, ?_⟩
      · rw [List.prod_cons, h1, ← mul_assoc, hl b List.mem_cons_self a (List.mem_cons_of_mem _ h), mul_assoc]
      · rw [List.prod_cons, h2, mul_assoc]

variable {E ee}

theorem jointE_comm (hcomm : ∀ i i' mu mu', ee i mu * ee i' mu' = ee i' mu' * ee i mu) (ka : ι → Fin n → ℤ) :
    ∀ x ∈ (Finset.univ : Finset ι).toList.map (fun i => ee i (ka i)),
      ∀ y ∈ (Finset.univ : Finset ι).toList.map (fun i => ee i (ka i)), x * y = y * x := by
  intro x hx y hy
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  obtain ⟨i', -, rfl⟩ := List.mem_map.1 hy
  exact hcomm i i' _ _

theorem jointE_factor (hcomm : ∀ i i' mu mu', ee i mu * ee i' mu' = ee i' mu' * ee i mu) (ka : ι → Fin n → ℤ) (i : ι) :
    ∃ rest, jointE ee ka = ee i (ka i) * rest ∧ jointE ee ka = rest * ee i (ka i) :=
  prod_split _ (jointE_comm hcomm ka) _ (List.mem_map.2 ⟨i, Finset.mem_toList.2 (Finset.mem_univ i), rfl⟩)

theorem jointE_isJProj (hee : ∀ i mu, IsIsoProj (E i) mu (ee i mu))
    (hcomm : ∀ i i' mu mu', ee i mu * ee i' mu' = ee i' mu' * ee i mu) (ka : ι → Fin n → ℤ) :
    IsJProj E {ka} (jointE ee ka) := by
  constructor
  · intro lam hlam x hx
    rw [Set.mem_singleton_iff] at hlam
    subst hlam
    have hfix : ∀ i, ee i (lam i) x = x := fun i =>
      (hee i (lam i)).1 x ((Submodule.mem_iInf _).1 hx i)
    unfold jointE
    induction (Finset.univ : Finset ι).toList with
    | nil => simp
    | cons i l ih => rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, hfix]
  · intro mu hmu x hx
    have hne : mu ≠ ka := fun h => hmu (Set.mem_singleton_iff.2 h)
    obtain ⟨i, hi⟩ : ∃ i, mu i ≠ ka i := by
      by_contra h
      push Not at h
      exact hne (funext h)
    obtain ⟨rest, -, h2⟩ := jointE_factor hcomm ka i
    rw [h2, Module.End.mul_apply, (hee i (ka i)).2 (mu i) hi x ((Submodule.mem_iInf _).1 hx i), map_zero]

theorem jointE_mem (hcomm : ∀ i i' mu mu', ee i mu * ee i' mu' = ee i' mu' * ee i mu)
    (hdec : ∀ i (G : V), ∃ T : Finset (Fin n → ℤ), G = ∑ mu ∈ T, ee i mu G ∧ ∀ mu, ee i mu G ∈ isoSub (E i) mu)
    (ka : ι → Fin n → ℤ) (F : V) (i : ι) : jointE ee ka F ∈ isoSub (E i) (ka i) := by
  obtain ⟨rest, h1, -⟩ := jointE_factor hcomm ka i
  rw [h1, Module.End.mul_apply]
  obtain ⟨_, _, h⟩ := hdec i (rest F)
  exact h (ka i)

theorem jointE_pres (P : Submodule K V) (hP : ∀ i mu, ∀ F ∈ P, ee i mu F ∈ P) (ka : ι → Fin n → ℤ) :
    ∀ F ∈ P, jointE ee ka F ∈ P := by
  intro F hF
  unfold jointE
  induction (Finset.univ : Finset ι).toList with
  | nil => simpa using hF
  | cons i l ih => rw [List.map_cons, List.prod_cons, Module.End.mul_apply]; exact hP i _ _ ih

theorem list_selfadj (B : V → V → K) (l : List (Module.End K V)) (hc : ∀ x ∈ l, ∀ y ∈ l, x * y = y * x)
    (hB : ∀ a ∈ l, ∀ F G, B (a F) G = B F (a G)) : ∀ F G, B (l.prod F) G = B F (l.prod G) := by
  induction l with
  | nil => intro F G; simp
  | cons a l ih =>
    intro F G
    have hcl : ∀ x ∈ l, ∀ y ∈ l, x * y = y * x := fun x hx y hy =>
      hc x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
    have hBl : ∀ b ∈ l, ∀ F G, B (b F) G = B F (b G) := fun b hb => hB b (List.mem_cons_of_mem _ hb)
    rw [List.prod_cons, Module.End.mul_apply, hB a List.mem_cons_self, ih hcl hBl, ← Module.End.mul_apply]
    have : Commute a l.prod :=
      Commute.list_prod_right _ _ fun y hy => hc _ List.mem_cons_self y (List.mem_cons_of_mem _ hy)
    rw [this.eq]

theorem jointE_selfadj (hcomm : ∀ i i' mu mu', ee i mu * ee i' mu' = ee i' mu' * ee i mu) (B : V → V → K)
    (hB : ∀ i mu F G, B (ee i mu F) G = B F (ee i mu G)) (ka : ι → Fin n → ℤ) (F G : V) :
    B (jointE ee ka F) G = B F (jointE ee ka G) := by
  refine list_selfadj B _ (jointE_comm hcomm ka) ?_ F G
  intro a ha
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
  exact hB i (ka i)

end Family

end Formalism.MainNotions.TestSideWords
