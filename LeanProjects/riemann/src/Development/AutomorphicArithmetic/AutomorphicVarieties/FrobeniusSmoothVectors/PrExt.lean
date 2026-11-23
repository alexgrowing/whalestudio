import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_ext :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (C : Type) [CommRing C] (r r' : F.Γ →* GG n C), (∀ s, (r s).right = F.del s) → (∀ s, (r' s).right = F.del s) → (r F.c).mat = (r' F.c).mat → (∀ s : F.G0, (r s).mat = (r' s).mat) → r = r' := by
  intro l _ k _ _ F C₀ n hF C _ r r' h h' hc h0
  have key : ∀ s, (r s).mat = (r' s).mat → r s = r' s := fun s hs =>
    SemidirectProduct.ext (Units.ext hs) ((h s).trans (h' s).symm)
  refine MonoidHom.ext fun s => ?_
  rcases Int.units_eq_one_or (F.del s) with hs | hs
  · exact key s (h0 ⟨s, hs⟩)
  · have hm : s * F.c ∈ F.del.ker := by
      rw [MonoidHom.mem_ker, map_mul, hs, hF.del_c]
      simp
    have e := key _ (h0 ⟨s * F.c, hm⟩)
    rw [map_mul, map_mul, key _ hc] at e
    exact mul_right_cancel e
