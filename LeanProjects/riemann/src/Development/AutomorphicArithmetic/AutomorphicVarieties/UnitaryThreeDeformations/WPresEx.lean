import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ConjPushMat
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.WeightedEntrySubMemIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.WPresGen

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem hom_ext_ker {Γ R : Type} [Group Γ] [CommRing R] {η : Γ →* ℤˣ} {c : Γ} (hc : η c = -1)
    {r r' : Γ →* GG 3 R} (h : ∀ g, (r g).right = (r' g).right) (e : (r c).mat = (r' c).mat)
    (h' : ∀ g, η g = 1 → (r g).mat = (r' g).mat) : r = r' := by
  have k : ∀ g, (r g).mat = (r' g).mat → r g = r' g := fun g hg =>
    SemidirectProduct.ext (Units.ext hg) (h g)
  refine MonoidHom.ext fun g => ?_
  rcases Int.units_eq_one_or (η g) with hg | hg
  · exact k g (h' g hg)
  · have h1 : η (g * c⁻¹) = 1 := by rw [map_mul, map_inv, hg, hc]; rfl
    rw [← inv_mul_cancel_right g c, map_mul r, map_mul r', k _ (h' _ h1), k c e]

private theorem scale_const {O R R' Γ : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    [Group Γ] (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ) (f f' : R →ₐ[O] R') (t : R'ˣ) (g : Γ) (a b : Fin 3) :
    f' (algebraMap O R ((r0 η Ψ g).mat a b)) = ((t ^ wt a b : R'ˣ) : R') * f (algebraMap O R ((r0 η Ψ g).mat a b)) := by
  rw [AlgHom.commutes, AlgHom.commutes]
  by_cases h : a = b
  · subst h
    simp [wt]
  · simp [GG.mat, tor_val, Matrix.diagonal_apply_ne _ h]

theorem UpperTheory.V.UnitaryThreeInertia.exists_adapted :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (u : Γ →* GG 3 R), F.IsUniv g₁ u →
    ∃ W : WPres O ℤ R, F.Adapted u W ∧ Frame.Minimal W := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ _ R _ _ _ u hu
  let x : {g // F.η g = 1} × Fin 3 × Fin 3 → R := fun s =>
    (u s.1).mat s.2.1 s.2.2 - algebraMap O R ((r0 F.η F.Ψ s.1).mat s.2.1 s.2.2)
  let w : {g // F.η g = 1} × Fin 3 × Fin 3 → ℤ := fun s => wt s.2.1 s.2.2
  have hpush : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R'), F.IsPt g₁ (push f u) := by
    intro R' _ _ _ f
    haveI : IsLocalHom f := ⟨fun a ha => by_contra fun hn => algHom_mem_max f (x := a) hn ha⟩
    exact isPt_push F f g₁ u hu.pt
  have hiff : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f f' : R →ₐ[O] R') (t : R'ˣ),
      (∀ s, f' (x s) = ((t ^ w s : R'ˣ) : R') * f (x s)) ↔ push f' u = conjBy (tor R' t) (push f u) := by
    intro R' _ _ _ f f' t
    refine ⟨fun h => hom_ext_ker hF.ηc (fun g => ((conjBy_tor (push f u) t).2.1 g).symm) ?_ fun g hg => ?_,
      fun h s => ?_⟩
    · rw [(hpush R' f').norm.atc, (isPt_tor F g₁ _ t (hpush R' f)).norm.atc]
    · ext a b
      rw [(conjBy_tor (push f u) t).1]
      have := h (⟨g, hg⟩, a, b)
      simp only [x, w, map_sub, mul_sub] at this
      rw [scale_const F.η F.Ψ f f' t, sub_left_inj] at this
      exact this
    · simp only [x, w, map_sub, mul_sub]
      rw [scale_const F.η F.Ψ f f' t, entry_mem u _ _ _ R' f f' t h]
  obtain ⟨W, h1, h2, h3⟩ := exists_wpres_of_coord (O := O) x w (fun s => hu.pt.red s.1 s.2.1 s.2.2)
    (fun R' _ _ _ f f' h => by
      have e := (hiff R' f' f 1).1 fun s => by simp [h s]
      have e' : push f u = push f' u := e.trans (MonoidHom.ext fun g => by simp [conjBy])
      exact (hu.univ R' _ (hpush R' f')).unique e' rfl)
    (fun R' _ _ _ f t => by
      obtain ⟨f', hf', -⟩ := hu.univ R' _ (isPt_tor F g₁ _ t (hpush R' f))
      exact ⟨f', (hiff R' f f' t).2 hf'⟩)
  refine ⟨W, ⟨fun i => ?_, fun j => Submodule.ext fun y => (h2 j y).trans ?_⟩, h3⟩
  · obtain ⟨s, e1, e2⟩ := h1 i
    exact ⟨s.1, s.2.1, s.2.2, s.1.2, e1, e2⟩
  · exact ⟨fun h R' _ _ _ f f' t e => h R' f f' t ((hiff R' f f' t).2 e),
      fun h R' _ _ _ f f' t e => h R' f f' t ((hiff R' f f' t).1 e)⟩
