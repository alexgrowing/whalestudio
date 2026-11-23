import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

theorem affSmooth_mvPolynomial (R : Type) [CommRing R] [Nontrivial R] (r : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension r R (MvPolynomial (Fin r) R) := by
  have : Algebra.IsStandardSmooth R (MvPolynomial (Fin r) R) :=
    Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential.2
      ⟨inferInstance, _, KaehlerDifferential.mvPolynomialBasis R _, by
        rintro _ ⟨i, rfl⟩
        exact ⟨MvPolynomial.X i, (KaehlerDifferential.mvPolynomialBasis_apply R _ i).symm⟩⟩
  exact (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth _).2 (by
    rw [rank_eq_card_basis (KaehlerDifferential.mvPolynomialBasis R _), Fintype.card_fin])

theorem affSmooth_of_range_eq {R S K : Type} [CommRing R] [Nontrivial R] [CommRing S] [CommRing K] {r : ℕ}
    (ψ : R →+* S) (j : S →+* K) (hj : Function.Injective j) (t : Fin r → K)
    (hg : Function.Injective (MvPolynomial.eval₂Hom (j.comp ψ) t))
    (h : (MvPolynomial.eval₂Hom (j.comp ψ) t).range = j.range) :
    ψ.IsStandardSmoothOfRelativeDimension r := by
  let g := MvPolynomial.eval₂Hom (j.comp ψ) t
  let e : MvPolynomial (Fin r) R ≃+* S :=
    (RingEquiv.ofBijective g.rangeRestrict
      ⟨fun _ _ h => hg (congrArg Subtype.val h), g.rangeRestrict_surjective⟩).trans
      ((RingEquiv.subringCongr h).trans (RingEquiv.ofBijective j.rangeRestrict
        ⟨fun _ _ h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩).symm)
  have he : ∀ P, j (e P) = g P := fun P =>
    congrArg Subtype.val ((RingEquiv.ofBijective j.rangeRestrict
        ⟨fun _ _ h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩).apply_symm_apply _)
  have : ψ = e.toRingHom.comp (algebraMap R (MvPolynomial (Fin r) R)) :=
    RingHom.ext fun a => hj (by
      show _ = j (e (MvPolynomial.C a))
      rw [he]
      exact (MvPolynomial.eval₂Hom_C (j.comp ψ) t a).symm)
  rw [this]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _ e
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap _).2 (affSmooth_mvPolynomial R r))

variable {F : Type} [Field F] {Ω Ω' : Type} [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']

theorem AffCover.smoothOfRelativeDimension {M : RatModel F Ω} {M' : RatModel F Ω'} {φ : Ω →ₐ[F] Ω'}
    {f : M'.Z ⟶ M.Z} {r : ℕ} (h : AffCover M M' φ f r) : SmoothOfRelativeDimension r f := by
  refine ⟨fun z => ?_⟩
  obtain ⟨U, W, t, hU, hW, hz, hUW, hind, hR⟩ := h.2 z
  have e : U ≤ f ⁻¹ᵁ W := hUW
  have nU : (U : Set M'.Z).Nonempty := ⟨z, hz⟩
  have nW : (W : Set M.Z).Nonempty := ⟨f z, hUW z hz⟩
  have : Nontrivial Γ(M.Z, W) := (M.res W nW).domain_nontrivial
  have hc : (M'.res U nU).comp (f.appLE W U e).hom = (φ : Ω →+* Ω').comp (M.res W nW) := RingHom.ext fun a => by
    show M'.res U nU _ = φ (M.res W nW a)
    rw [M.res_apply, M'.res_apply, ← h.1.valF_app nW a]
    exact M'.valF_resG e nU (f.app W a)
  refine ⟨W, hW, U, hU, hz, e, affSmooth_of_range_eq _ (M'.res U nU) (M'.res_injective U nU) t ?_ ?_⟩
  · rw [hc, injective_iff_map_eq_zero]
    intro P hP
    apply MvPolynomial.map_injective _ (M.res_injective W nW)
    rw [map_zero]
    apply hind
    rw [MvPolynomial.eval₂_map]
    exact hP
  · rw [hc, M'.range_res, hR]
    have hm : ∀ a, (φ : Ω →+* Ω').comp (M.res W nW) a ∈ φ '' (M.ringOn W : Set Ω) := fun a =>
      ⟨_, (RatModel.mem_ringOn_iff_exists nW).2 ⟨a, (M.res_apply W nW a).symm⟩, rfl⟩
    have hm' : ∀ x ∈ M.ringOn W,
        φ x ∈ (MvPolynomial.eval₂Hom ((φ : Ω →+* Ω').comp (M.res W nW)) t).range := fun x hx => by
      obtain ⟨a, rfl⟩ := (RatModel.mem_ringOn_iff_exists nW).1 hx
      exact ⟨MvPolynomial.C a, by rw [MvPolynomial.eval₂Hom_C, ← M.res_apply W nW]; rfl⟩
    apply le_antisymm
    · rintro _ ⟨P, rfl⟩
      rw [Subalgebra.mem_toSubring]
      induction P using MvPolynomial.induction_on with
      | C a => rw [MvPolynomial.eval₂Hom_C]; exact Algebra.subset_adjoin (Or.inl (hm a))
      | add P Q hP hQ => rw [map_add]; exact add_mem hP hQ
      | mul_X P i hP =>
        rw [map_mul, MvPolynomial.eval₂Hom_X']
        exact mul_mem hP (Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩))
    · intro x hx
      rw [Subalgebra.mem_toSubring] at hx
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        rcases hx with ⟨y, hy, rfl⟩ | ⟨i, rfl⟩
        · exact hm' y hy
        · exact ⟨MvPolynomial.X i, MvPolynomial.eval₂Hom_X' _ _ i⟩
      | algebraMap c => rw [← φ.commutes]; exact hm' _ (Subalgebra.algebraMap_mem _ c)
      | add x y _ _ hx hy => exact add_mem hx hy
      | mul x y _ _ hx hy => exact mul_mem hx hy

theorem affCover_smooth (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r d : ℕ)
    (h : AffCover M M' φ f r) (hd : SmoothOfRelativeDimension d M.s) :
    SmoothOfRelativeDimension (d + r) M'.s := by
  have := h.smoothOfRelativeDimension
  rw [← h.1.inducedModelMorphism_comp_structureMap, Nat.add_comm]
  infer_instance

end GlobalTheory.FlagBundle
