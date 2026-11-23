import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
import Mathlib.Topology.Algebra.ClopenNhdofOne

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.close_map :
    ∀ (Ph B Z : Type) [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph] [CompactSpace Ph] [TotallyDisconnectedSpace Ph] [Group B] [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [CompactSpace Z] [TotallyDisconnectedSpace Z] (Γ : ℕ → Type) [∀ N, Group (Γ N)] (π : ∀ N, Ph →* Γ N) (πo : Ph →* B) (p : ∀ N, Γ N →* Z) (po : B →* Z) (U : Ultrafilter ℕ) (a : ∀ N, Γ N) (b : B) (z : Z), Continuous (po.comp πo) → (∀ W : OpenNormalSubgroup Z, ∀ᶠ N in (U : Filter ℕ), ∀ g, p N (π N g) * (po (πo g))⁻¹ ∈ W) → (∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), Close (π N) πo V.toSubgroup (a N) b) → (∀ W : OpenNormalSubgroup Z, ∀ᶠ N in (U : Filter ℕ), p N (a N) * z⁻¹ ∈ W) → po b = z := by
  intro Ph B Z _ _ _ _ _ _ _ _ _ _ _ Γ _ π πo p po U a b z hf hp hclose ha
  set f : Ph →* Z := po.comp πo with hfdef
  have key : ∀ W : OpenNormalSubgroup Z, po b * z⁻¹ ∈ W := by
    intro W
    let V : OpenNormalSubgroup Ph :=
      { toOpenSubgroup := ⟨W.toSubgroup.comap f, W.isOpen.preimage hf⟩
        isNormal' := Subgroup.Normal.comap W.isNormal' f }
    obtain ⟨N, h1, h2, h3⟩ := ((hp W).and ((hclose V).and (ha W))).exists
    obtain ⟨g, g', hg, hg', hV⟩ := h2
    have hV' : f (g⁻¹ * g') ∈ W := hV
    have e1 := h1 g
    rw [hg] at e1
    have hb : po b = f g' := by simp [hfdef, hg']
    have hn : f g' * (f g)⁻¹ ∈ W := by
      have hc := W.isNormal'.conj_mem _ hV' (f g)
      have he : f g * f (g⁻¹ * g') * (f g)⁻¹ = f g' * (f g)⁻¹ := by
        simp [map_mul, map_inv, mul_assoc]
      rw [he] at hc
      exact hc
    have hx : po b * z⁻¹ = (f g' * (f g)⁻¹) * (p N (a N) * (f g)⁻¹)⁻¹ * (p N (a N) * z⁻¹) := by
      rw [hb]; group
    rw [hx]
    exact W.mul_mem (W.mul_mem hn (W.inv_mem e1)) h3
  by_contra hne
  have hx1 : po b * z⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.mp h)
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton (x := po b * z⁻¹)) (by simpa [eq_comm] using hx1)
  exact hH (key H) rfl
