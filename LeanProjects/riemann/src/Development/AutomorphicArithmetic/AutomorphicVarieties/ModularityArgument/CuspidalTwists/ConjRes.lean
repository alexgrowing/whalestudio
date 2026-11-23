import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix

private theorem low_ne {Γ R : Type} [Group Γ] [Field R] (y a : Γ → R) (hy : ∀ g h, y (g * h) = y g * a h + y h)
    (g0 g : Γ) (h0 : y g0 = 0) (ha : a g0 ≠ 1) (hg : y g ≠ 0) : y (g * g0 * g⁻¹) ≠ 0 := by
  intro h
  have e1 := hy (g * g0 * g⁻¹) g
  rw [inv_mul_cancel_right, hy, h, h0] at e1
  have e2 : y g * (a g0 - 1) = 0 := by linear_combination e1
  rcases mul_eq_zero.1 e2 with e | e
  · exact hg e
  · exact ha (sub_eq_zero.1 e)

private theorem conj_res {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [hF : IsGalois ℚ F]
    (g : G ℚ Ω) (s : G F Ω) : ∃ t : G F Ω, resQ F t = g * resQ F s * g⁻¹ := by
  haveI : IsGalois ℚ Ω := {}
  have hN : F.fixingSubgroup.Normal := (InfiniteGalois.normal_iff_isGalois F).2 (by convert hF <;> exact Subsingleton.elim _ _)
  have hs : resQ F s ∈ F.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact s.commutes ⟨x, hx⟩
  exact ⟨F.fixingSubgroupEquiv ⟨_, hN.conj_mem _ hs g⟩, rfl⟩

private theorem tn_21 {R : Type} [CommRing R] (a b : M2 R) : UpperTheory.V.Cu.tn a b 2 1 = -(a 1 0 * b 1 1) := by
  rfl

private theorem tn_30 {R : Type} [CommRing R] (a b : M2 R) : UpperTheory.V.Cu.tn a b 3 0 = a 1 0 * b 0 0 := by
  rfl

theorem UpperTheory.V.Cu.entOf4 : EntOf4 := by
  intro Ω _ _ _ l _ d T hT hO R _ f hf
  have hU : ∀ y : d.c₁.O, IsUnit y → f y ≠ 0 := fun y hy => (hy.map f).ne_zero
  have h00 : ∀ g, f (d.ρ₁ g 0 0) = f (inc d.h (UpperTheory.V.Cu.Phi d.D d.T₀.pr d.k g)) := fun g => by
    have := hf _ (d.mod.red g).1
    rwa [map_sub, sub_eq_zero] at this
  have h11 : ∀ g, f (d.ρ₁ g 1 1) = 1 := fun g => by
    have := hf _ (d.mod.red g).2.1
    rwa [map_sub, sub_eq_zero, map_one] at this
  have t00 : ∀ g, f (d.τ g 0 0) = 1 := fun g => by
    have := hf _ (d.tau.red g).1
    rwa [map_sub, sub_eq_zero, map_one] at this
  have t11 : ∀ g, f (d.τ g 1 1) ≠ 0 := fun g => by
    by_cases hg : g ∈ d.K'.fixingSubgroup
    · rw [(d.tau.on g hg).1, t00]
      exact one_ne_zero
    · rw [(d.tau.off g hg).1, map_neg, t00]
      exact neg_ne_zero.2 one_ne_zero
  have hPhi : Raw.bar (UpperTheory.V.Cu.Phi d.D d.T₀.pr d.k) (resQ T.F T.g0) ≠ 1 := by
    intro e
    apply hO.dist 0 3 (by decide)
    rw [hT.pr, d.tw.red0, d.tw.red3, e, mul_one]
  have ha : f (d.ρ₁ (resQ T.F T.g0) 0 0) ≠ 1 := by
    rw [h00]
    intro e
    have hu : IsUnit ((UpperTheory.V.Cu.Phi d.D d.T₀.pr d.k (resQ T.F T.g0) : d.c.O) - 1) := by
      by_contra hn
      apply hPhi
      have : residue d.c.O ((UpperTheory.V.Cu.Phi d.D d.T₀.pr d.k (resQ T.F T.g0) : d.c.O) - 1) = 0 :=
        (residue_eq_zero_iff _).2 hn
      rwa [map_sub, map_one, sub_eq_zero] at this
    apply hU _ (hu.map (inc d.h))
    rw [map_sub, map_sub, e, map_one, map_one, sub_self]
  obtain ⟨g, hg⟩ := d.mod.ne
  have hg' : f (d.ρ₁ g 1 0) ≠ 0 := hU _ (by by_contra hn; exact hg hn)
  have key : ∃ t : G T.F Ω, f (d.ρ₁ (resQ T.F t) 1 0) ≠ 0 := by
    by_cases h0 : f (d.ρ₁ (resQ T.F T.g0) 1 0) = 0
    · obtain ⟨t, ht⟩ := conj_res T.F g T.g0
      refine ⟨t, ?_⟩
      rw [ht]
      refine low_ne (fun g => f (d.ρ₁ g 1 0)) (fun g => f (d.ρ₁ g 0 0)) (fun g h => ?_) _ g h0 ha hg'
      simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add, h11, one_mul]
    · exact ⟨T.g0, h0⟩
  obtain ⟨t, ht⟩ := key
  have hδ : f (toC d.h d.δ (resQ T.F t) : d.c₁.O) ≠ 0 := hU _ (Units.isUnit _)
  have ent : ∀ i j, ((d.Q T).map f).r t i j =
      f (toC d.h d.δ (resQ T.F t) : d.c₁.O) * f (UpperTheory.V.Cu.tn (d.ρ₁ (resQ T.F t)) (d.τ (resQ T.F t)) i j) := fun i j => by
    rw [← map_mul]
    rfl
  refine ⟨⟨t, 2, 1, by decide, ?_⟩, ⟨t, 3, 0, by decide, ?_⟩⟩
  · rw [ent, tn_21, map_neg, map_mul]
    exact mul_ne_zero hδ (neg_ne_zero.2 (mul_ne_zero ht (t11 _)))
  · rw [ent, tn_30, map_mul, t00, mul_one]
    exact mul_ne_zero hδ ht

end
