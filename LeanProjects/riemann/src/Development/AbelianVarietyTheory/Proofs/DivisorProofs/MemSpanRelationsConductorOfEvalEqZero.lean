import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PinchKernel

theorem mem_span_of_eval_eq_zero (R R' D E ν σ : Type) [CommRing R] [CommRing R'] [CommRing D] [CommRing E]
    (a : R →+* R') (c : Ideal R) [Algebra (R ⧸ c) D] (χ : R' →+* E) (ψ : D →+* E) (ζ : ν → D)
    (F : σ → MvPolynomial ν R)
    (hsurj : Function.Surjective (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D))
    (hker : RingHom.ker (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D) =
      Ideal.span (Set.range fun s ↦ MvPolynomial.map (Ideal.Quotient.mk c) (F s)))
    (hpo : IsPushout (CommRingCat.ofHom ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c)))
      (CommRingCat.ofHom a) (CommRingCat.ofHom ψ) (CommRingCat.ofHom χ))
    (G : MvPolynomial ν R') (hG : MvPolynomial.eval₂ χ (fun s ↦ ψ (ζ s)) G = 0) :
    G ∈ Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)) ⊔
      (c.map a).map (MvPolynomial.C : R' →+* MvPolynomial ν R') := by
  classical
  set J : Ideal (MvPolynomial ν R') := Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)) ⊔
      (c.map a).map (MvPolynomial.C : R' →+* MvPolynomial ν R') with hJ
  let mkJ : MvPolynomial ν R' →+* MvPolynomial ν R' ⧸ J := Ideal.Quotient.mk J
  have hc : ∀ r ∈ c, (mkJ.comp ((MvPolynomial.C : R' →+* MvPolynomial ν R').comp a)) r = 0 := by
    intro r hr
    simp only [RingHom.comp_apply, mkJ]
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hr))
  let base : R ⧸ c →+* MvPolynomial ν R' ⧸ J :=
    Ideal.Quotient.lift c (mkJ.comp ((MvPolynomial.C : R' →+* MvPolynomial ν R').comp a)) hc
  let φ : MvPolynomial ν (R ⧸ c) →+* MvPolynomial ν R' ⧸ J :=
    MvPolynomial.eval₂Hom base (fun s ↦ mkJ (MvPolynomial.X s))
  have hφC : ∀ r : R, φ (MvPolynomial.C (Ideal.Quotient.mk c r)) = mkJ (MvPolynomial.C (a r)) := by
    intro r
    simp [φ, base]
  have hφmap : ∀ P : MvPolynomial ν R,
      φ (MvPolynomial.map (Ideal.Quotient.mk c) P) = mkJ (MvPolynomial.map a P) := by
    intro P
    have h : φ.comp (MvPolynomial.map (Ideal.Quotient.mk c)) = mkJ.comp (MvPolynomial.map a) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp only [RingHom.comp_apply, MvPolynomial.map_C]
        exact hφC r
      · intro s
        simp [φ]
    exact RingHom.congr_fun h P
  let q : MvPolynomial ν (R ⧸ c) →+* D := (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D)
  have hkerφ : RingHom.ker q ≤ RingHom.ker φ := by
    have hq : RingHom.ker q = Ideal.span (Set.range fun s ↦ MvPolynomial.map (Ideal.Quotient.mk c) (F s)) := by
      rw [← hker]; rfl
    rw [hq, Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, hφmap, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.subset_span ⟨s, rfl⟩)
  let dA : D →+* MvPolynomial ν R' ⧸ J :=
    q.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨φ, hkerφ⟩
  have hdA : ∀ p, dA (q p) = φ p := fun p =>
    RingHom.liftOfRightInverse_comp_apply q _ _ ⟨φ, hkerφ⟩ p
  have hqX : ∀ s, q (MvPolynomial.X s) = ζ s := fun s => by simp [q]
  have hqC : ∀ x : R ⧸ c, q (MvPolynomial.C x) = algebraMap (R ⧸ c) D x := fun x => by
    simp [q]
  have w : CommRingCat.ofHom ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c)) ≫ CommRingCat.ofHom dA =
      CommRingCat.ofHom a ≫ CommRingCat.ofHom (mkJ.comp (MvPolynomial.C : R' →+* MvPolynomial ν R')) := by
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [← hqC, hdA, hφC]
  let desc := hpo.desc (CommRingCat.ofHom dA) (CommRingCat.ofHom (mkJ.comp (MvPolynomial.C : R' →+* MvPolynomial ν R'))) w
  have hinl : ∀ x : D, desc.hom (ψ x) = dA x := fun x => by
    have := congrArg (fun f => f.hom x) (hpo.inl_desc (CommRingCat.ofHom dA)
      (CommRingCat.ofHom (mkJ.comp (MvPolynomial.C : R' →+* MvPolynomial ν R'))) w)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
    exact this
  have hinr : ∀ x : R', desc.hom (χ x) = mkJ (MvPolynomial.C x) := fun x => by
    have := congrArg (fun f => f.hom x) (hpo.inr_desc (CommRingCat.ofHom dA)
      (CommRingCat.ofHom (mkJ.comp (MvPolynomial.C : R' →+* MvPolynomial ν R'))) w)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
    exact this
  have hΦ : desc.hom.comp (MvPolynomial.eval₂Hom χ (fun s ↦ ψ (ζ s))) = mkJ := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      exact hinr x
    · intro s
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      rw [hinl, ← hqX, hdA]
      simp [φ]
  have h0 : mkJ G = 0 := by
    rw [← hΦ, RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, hG, map_zero]
  exact (Ideal.Quotient.eq_zero_iff_mem).1 h0

end GlobalTheory.PinchKernel
