import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.GdotSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem UpperTheory.V.Ws.single_diag_mem_of_inverse_differences_mem {A : Type} [CommRing A] (E : Subring A)
    (S : Subalgebra E (M4 A)) (d : Fin 4 → A) (hd : Matrix.diagonal d ∈ S) (hE : ∀ i, d i ∈ E)
    (i j1 j2 j3 : Fin 4) (hc : ∀ k, k = i ∨ k = j1 ∨ k = j2 ∨ k = j3)
    (n1 : j1 ≠ i) (n2 : j2 ≠ i) (n3 : j3 ≠ i) (u1 u2 u3 : A) (m1 : u1 ∈ E) (m2 : u2 ∈ E) (m3 : u3 ∈ E)
    (e1 : u1 * (d i - d j1) = 1) (e2 : u2 * (d i - d j2) = 1) (e3 : u3 * (d i - d j3) = 1) :
    Matrix.single i i (1 : A) ∈ S := by
  have hF : ∀ a b : A, a ∈ E → b ∈ E → (Matrix.diagonal (fun k => a * (d k - b)) : M4 A) ∈ S := by
    intro a b ha hb
    have h : (Matrix.diagonal (fun k => a * (d k - b)) : M4 A) =
        (⟨a, ha⟩ : E) • (Matrix.diagonal d - algebraMap E (M4 A) ⟨b, hb⟩) := by
      ext k l
      by_cases hkl : k = l
      · subst hkl
        simp [Matrix.diagonal_apply, Algebra.algebraMap_eq_smul_one, Matrix.one_apply, Subring.smul_def, mul_sub]
      · simp [Matrix.diagonal_apply, Algebra.algebraMap_eq_smul_one, Matrix.one_apply, hkl, Subring.smul_def]
    rw [h]
    exact S.smul_mem (S.sub_mem hd (S.algebraMap_mem _)) _
  have hP := S.mul_mem (S.mul_mem (hF u1 (d j1) m1 (hE j1)) (hF u2 (d j2) m2 (hE j2)))
    (hF u3 (d j3) m3 (hE j3))
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal] at hP
  convert hP using 1
  ext k l
  by_cases hkl : k = l
  · subst hkl
    by_cases hki : k = i
    · subst hki
      simp [Matrix.single_apply, e1, e2, e3]
    · rcases hc k with h | h | h | h
      · exact absurd h hki
      · subst h; simp [Matrix.single_apply, Ne.symm n1]
      · subst h; simp [Matrix.single_apply, Ne.symm n2]
      · subst h; simp [Matrix.single_apply, Ne.symm n3]
  · simp [Matrix.single_apply, Matrix.diagonal_apply, hkl]
    rintro rfl rfl
    exact absurd rfl hkl

private theorem UpperTheory.V.Ws.single_mem_of_diag {A : Type} [CommRing A] (E : Subring A) (S : Subalgebra E (M4 A)) (d : Fin 4 → A)
    (hd : Matrix.diagonal d ∈ S) (hE : ∀ i, d i ∈ E) (hu : ∀ i j, i ≠ j → ∃ u ∈ E, u * (d i - d j) = 1) (i : Fin 4) :
    Matrix.single i i (1 : A) ∈ S := by
  fin_cases i
  · obtain ⟨u1, m1, e1⟩ := hu 0 1 (by decide)
    obtain ⟨u2, m2, e2⟩ := hu 0 2 (by decide)
    obtain ⟨u3, m3, e3⟩ := hu 0 3 (by decide)
    exact UpperTheory.V.Ws.single_diag_mem_of_inverse_differences_mem E S d hd hE 0 1 2 3 (by decide) (by decide) (by decide) (by decide)
      u1 u2 u3 m1 m2 m3 e1 e2 e3
  · obtain ⟨u1, m1, e1⟩ := hu 1 0 (by decide)
    obtain ⟨u2, m2, e2⟩ := hu 1 2 (by decide)
    obtain ⟨u3, m3, e3⟩ := hu 1 3 (by decide)
    exact UpperTheory.V.Ws.single_diag_mem_of_inverse_differences_mem E S d hd hE 1 0 2 3 (by decide) (by decide) (by decide) (by decide)
      u1 u2 u3 m1 m2 m3 e1 e2 e3
  · obtain ⟨u1, m1, e1⟩ := hu 2 0 (by decide)
    obtain ⟨u2, m2, e2⟩ := hu 2 1 (by decide)
    obtain ⟨u3, m3, e3⟩ := hu 2 3 (by decide)
    exact UpperTheory.V.Ws.single_diag_mem_of_inverse_differences_mem E S d hd hE 2 0 1 3 (by decide) (by decide) (by decide) (by decide)
      u1 u2 u3 m1 m2 m3 e1 e2 e3
  · obtain ⟨u1, m1, e1⟩ := hu 3 0 (by decide)
    obtain ⟨u2, m2, e2⟩ := hu 3 1 (by decide)
    obtain ⟨u3, m3, e3⟩ := hu 3 2 (by decide)
    exact UpperTheory.V.Ws.single_diag_mem_of_inverse_differences_mem E S d hd hE 3 0 1 2 (by decide) (by decide) (by decide) (by decide)
      u1 u2 u3 m1 m2 m3 e1 e2 e3

theorem UpperTheory.V.Ws.sxMonoZero :
    ∀ {A Γ : Type} [CommRing A] [Group Γ] (E : Subring A) (r : Γ →* M4 A) (g0 : Γ), (∀ g, ∃ ν ∈ E, IsGSp ν (r g)) → (∀ g, (r g).trace ∈ E) → (r g0).IsDiag → (∀ i, r g0 i i ∈ E) → (∀ i j, i ≠ j → ∃ u ∈ E, u * (r g0 i i - r g0 j j) = 1) → mono r 0 ⊆ E := by
  intro A Γ _ _ E r g0 hν htr hdiag hE hu
  let S : Subalgebra E (M4 A) := Algebra.adjoin E (Set.range r)
  have hcl : ∀ y ∈ Submonoid.closure (Set.range r), ∃ g, r g = y := by
    intro y hy
    induction hy using Submonoid.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨1, map_one r⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a * b, map_mul r a b⟩
  have hsp : ∀ x ∈ S, x ∈ Submodule.span E (Submonoid.closure (Set.range r) : Set (M4 A)) := by
    intro x hx
    rw [← Algebra.adjoin_eq_span]
    exact hx
  have htrSp : ∀ x ∈ Submodule.span E (Submonoid.closure (Set.range r) : Set (M4 A)),
      Matrix.trace x ∈ E := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hcl y hy
      exact htr g
    | zero =>
      rw [Matrix.trace_zero]
      exact E.zero_mem
    | add y z _ _ hy hz =>
      rw [Matrix.trace_add]
      exact E.add_mem hy hz
    | smul c y _ hy =>
      show Matrix.trace ((c : A) • y) ∈ E
      rw [Matrix.trace_smul, smul_eq_mul]
      exact E.mul_mem c.2 hy
  have htrS : ∀ x ∈ S.toSubring, Matrix.trace x ∈ E := fun x hx => htrSp x (hsp x hx)
  have hadj0 : adj (0 : M4 A) = 0 := by
    have h0 := (grp A).2.2.2.1 0 0
    simpa using h0
  have hadjSp : ∀ x ∈ Submodule.span E (Submonoid.closure (Set.range r) : Set (M4 A)),
      adj x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hcl y hy
      obtain ⟨ν, hνE, hG⟩ := hν g
      have hinv : r g * r g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      rw [(grp A).2.2.2.2.2.2.1 ν (r g) (r g⁻¹) hG hinv]
      exact S.smul_mem (Algebra.subset_adjoin ⟨g⁻¹, rfl⟩) (⟨ν, hνE⟩ : E)
    | zero =>
      rw [hadj0]
      exact S.zero_mem
    | add y z _ _ hy hz =>
      rw [(grp A).2.2.1]
      exact S.add_mem hy hz
    | smul c y _ hy =>
      show adj ((c : A) • y) ∈ S
      rw [(grp A).2.2.2.1]
      exact S.smul_mem hy c
  have hadjS : ∀ x ∈ S.toSubring, adj x ∈ S.toSubring := fun x hx => hadjSp x (hsp x hx)
  have hdg : Matrix.diagonal (fun i => r g0 i i) = r g0 := (Matrix.isDiag_iff_diagonal_diag _).1 hdiag
  have hsing : ∀ i, Matrix.single i i (1 : A) ∈ S.toSubring := by
    intro i
    refine UpperTheory.V.Ws.single_mem_of_diag E S (fun i => r g0 i i) ?_ hE hu i
    rw [hdg]
    exact Algebra.subset_adjoin ⟨g0, rfl⟩
  intro x hx
  obtain ⟨L, hL0, rfl⟩ := hx
  have hres := sxGma E S.toSubring hsing htrS hadjS (L.map fun a => (r a.1, a.2))
    (by
      intro y hy
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 hy
      exact Algebra.subset_adjoin ⟨a.1, rfl⟩)
    (by rw [List.map_map]; exact hL0)
  rw [List.map_map] at hres
  exact hres
