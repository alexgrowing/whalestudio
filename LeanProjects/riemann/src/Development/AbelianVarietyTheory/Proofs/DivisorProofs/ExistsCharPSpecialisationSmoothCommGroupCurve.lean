import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalPrimeCharNotMemFiniteTypeIntStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenSmoothOfRelativeDimensionOfGeneriStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenGeometricallyConnectedFibresOfGenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenSectionsDistinctInFibresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveBaseChangeTwoDistinctPointsOfFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFgSubringDescentGroupSectionsCurveStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianReductionAlongIsogenyStrictHenselian
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CharPSpec

theorem spMap_comp_eq' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {f : A →+* B} {g : B →+* C}
    {h : A →+* C} (e : g.comp f = h) : spMap g ≫ spMap f = spMap h := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]

theorem exists_charP_specialization : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, 1 ≤ m → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → ∀ (P : Polynomial k), P ≠ 0 → ∀ (u : Sp (Localization.Away P) ⟶ G.left) (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) → spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u → ∃ (k' : Type) (_ : Field k') (_ : IsAlgClosed k') (p : ℕ) (_ : Fact p.Prime) (_ : CharP k' p) (G' : Over (Sp k')) (_ : GrpObj G'), GlobalTheory.SS.SmConn G' ∧ SmoothOfRelativeDimension g G'.hom ∧ (m : k') ≠ 0 ∧ (∃ s' : Finset (𝟙_ (Over (Sp k')) ⟶ G'), (∀ x ∈ s', x ^ m = 1) ∧ s'.card = s.card) ∧ ∃ (P' : Polynomial k') (_ : P' ≠ 0) (u' : Sp (Localization.Away P') ⟶ G'.left) (a' b' : Localization.Away P' →ₐ[k'] k'), u' ≫ G'.hom = spMap (algebraMap k' (Localization.Away P')) ∧ spMap a'.toRingHom ≫ u' ≠ spMap b'.toRingHom ≫ u' := by
  intro k _ _ _ G _ hG g hg m hm s hs P hP u a b hu hab
  classical
  have hm0 : (m : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨R, G₁, _, hfg, hmR, hcomm, hsm, hsep, hqc, hgc, hrd, ⟨s₁, hcard, hs₁, hdist⟩, P₁, hP₁, u₁, α, β, hα, hβ,
    hu₁, hαβ⟩ := GlobalTheory.T.exists_fg_subring_descent_group_sections_curve k G hG g hg m hm hm0 s hs P hP u a b hu hab
  haveI : Algebra.FiniteType ℤ R := hfg
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have hinj : Function.Injective R.subtype := Subtype.val_injective
  obtain ⟨f₁, hf₁, H₁⟩ := GlobalTheory.T.exists_basicOpen_smoothOfRelativeDimension_of_generic R G₁ hsm hqc k R.subtype hinj g hrd
  obtain ⟨f₂, hf₂, H₂⟩ := GlobalTheory.T.exists_basicOpen_geometricallyConnected_fibres_of_generic R G₁ hsm hqc k R.subtype hinj hgc
  obtain ⟨f₃, hf₃, H₃⟩ := GlobalTheory.T.exists_basicOpen_sections_distinct_in_fibres R G₁ hsep k R.subtype hinj (s₁.image fun x => x.left)
    (by
      intro x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
      exact Over.w y)
    (by
      intro x hx y hy hxy
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
      exact hdist x' hx' y' hy' fun h => hxy (by rw [h]))
  have hsec : ∀ (c₀ : R) (hc₀ : IsUnit (Polynomial.evalRingHom c₀ P₁)),
      spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hc₀) ≫ u₁ ≫ G₁.hom = 𝟙 _ := by
    intro c₀ hc₀
    rw [hu₁, spMap_comp_eq' (h := RingHom.id R)]
    · show Spec.map (CommRingCat.ofHom (RingHom.id R)) = _
      rw [CommRingCat.ofHom_id, Spec.map_id]
    · ext r
      rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply R (Polynomial R) (Localization.Away P₁),
        IsLocalization.Away.lift_eq]
      simp
  obtain ⟨f₄, hf₄, H₄⟩ := GlobalTheory.T.exists_basicOpen_sections_distinct_in_fibres R G₁ hsep k R.subtype hinj
    {spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hα) ≫ u₁,
      spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hβ) ≫ u₁}
    (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rw [Category.assoc]; exact hsec α hα
      · rw [Finset.mem_singleton.mp hx, Category.assoc]; exact hsec β hβ)
    (by
      intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with rfl | hx <;> rcases Finset.mem_insert.mp hy with rfl | hy
      · exact absurd rfl hxy
      · rw [Finset.mem_singleton.mp hy]; exact hαβ
      · rw [Finset.mem_singleton.mp hx]; exact Ne.symm hαβ
      · rw [Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hy] at hxy; exact absurd rfl hxy)
  have hlc : R.subtype P₁.leadingCoeff ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]
    exact Polynomial.leadingCoeff_ne_zero.mpr hP₁
  set f := f₁ * f₂ * f₃ * f₄ * P₁.leadingCoeff with hfdef
  have hf : f ≠ 0 := by
    intro h
    have := congrArg R.subtype h
    rw [map_zero, hfdef] at this
    simp only [map_mul] at this
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hf₁ hf₂) hf₃) hf₄) hlc) this
  obtain ⟨M, hM, hfM, p, hp, hpM⟩ := GlobalTheory.T.exists_maximal_prime_char_not_mem_finiteType_int R f hf
  letI := Ideal.Quotient.field M
  let ψ : R →+* AlgebraicClosure (R ⧸ M) := (algebraMap (R ⧸ M) _).comp (Ideal.Quotient.mk M)
  have hψ : ∀ r, r ∉ M → IsUnit (ψ r) := by
    intro r hr
    refine isUnit_iff_ne_zero.mpr ?_
    rw [RingHom.comp_apply, map_ne_zero_iff _ (algebraMap (R ⧸ M) _).injective]
    exact fun h => hr (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hu := hψ f hfM
  simp only [hfdef, map_mul, IsUnit.mul_iff] at hu
  obtain ⟨⟨⟨⟨u1, u2⟩, u3⟩, u4⟩, u5⟩ := hu
  haveI : Fact p.Prime := ⟨hp⟩
  have hpF : CharP (AlgebraicClosure (R ⧸ M)) p := by
    rw [CharP.charP_iff_prime_eq_zero hp, ← map_natCast ψ, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr hpM, map_zero]
  refine ⟨AlgebraicClosure (R ⧸ M), inferInstance, inferInstance, p, inferInstance, hpF,
    (Over.pullback (spMap ψ)).obj G₁, inferInstance, ?_, H₁ _ ψ u1, ?_, ?_, ?_⟩
  · refine ⟨inferInstance, ?_, ?_, ?_, H₂ _ ψ u2⟩
    · show Smooth (pullback.snd _ _); infer_instance
    · show IsSeparated (pullback.snd _ _); infer_instance
    · show QuasiCompact (pullback.snd _ _); infer_instance
  · rw [← map_natCast ψ]
    exact (hmR.map ψ).ne_zero
  · refine ⟨s₁.image (GlobalTheory.IsogRed.sec (spMap ψ)), ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      rw [← GlobalTheory.IsogRed.sec_pow, hs₁ y hy]
      simpa using (GlobalTheory.IsogRed.sec_pow (spMap ψ) y 0).trans (pow_zero _)
    · rw [← hcard]
      refine Finset.card_image_of_injOn fun x hx y hy hxy => ?_
      by_contra hne
      have e := congrArg (fun z => z.left ≫ pullback.fst G₁.hom (spMap ψ)) hxy
      simp only [GlobalTheory.IsogRed.sec_left] at e
      exact H₃ _ ψ u3 x.left (Finset.mem_image_of_mem _ hx) y.left (Finset.mem_image_of_mem _ hy)
        (fun h => hne (Over.OverMorphism.ext h)) e
  · exact GlobalTheory.T.curve_baseChange_two_distinct_points_of_field R _ ψ G₁ P₁ u₁ α β hα hβ hu₁ u5
      (H₄ _ ψ u4 _ (Finset.mem_insert_self _ _) _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        (fun h => hαβ (by rw [h])))

end GlobalTheory.CharPSpec
