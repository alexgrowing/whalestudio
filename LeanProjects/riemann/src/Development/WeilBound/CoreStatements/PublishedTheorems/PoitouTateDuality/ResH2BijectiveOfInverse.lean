import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmp
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs

noncomputable section

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem resH2_bijective_of_inverse {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {R M : Type} [CommRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (rho : Representation R G M) (ψ : H →* G) (hψ : Continuous ψ)
    (χ : G →* H) (hχ : Continuous χ) (h1 : ∀ g, ψ (χ g) = g) (h2 : ∀ h, χ (ψ h) = h) :
    Function.Bijective (resH2 rho ψ hψ) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      rw [Submodule.Quotient.mk_eq_zero]
      rw [resH2, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem _ _).1 hx
      refine (separated_dvr_second_cohomology_mem _ _).2 ⟨c ∘ χ, hc.comp hχ, ?_⟩
      funext p
      have e := congrFun hcf (χ p.1, χ p.2)
      simp only [Submodule.coe_subtype] at e ⊢
      change _ = z.1 (ψ (χ p.1), ψ (χ p.2)) at e
      rw [h1, h1] at e
      rw [← e]
      simp [d1, h1]
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      refine ⟨Submodule.Quotient.mk ⟨fun p => z.1 (χ p.1, χ p.2),
        z.2.1.comp (hχ.prodMap hχ), fun g h k => ?_⟩, ?_⟩
      · have e := z.2.2 (χ g) (χ h) (χ k)
        simp only [map_mul]
        change rho (ψ (χ g)) _ - _ + _ - _ = 0 at e
        rw [h1] at e
        exact e
      · rw [resH2, Submodule.mapQ_apply]
        congr 1
        apply Subtype.ext
        funext p
        change z.1 (χ (ψ p.1), χ (ψ p.2)) = z.1 p
        rw [h2, h2]

theorem resCmp2B {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (θ : G ≃ₜ* H) {ι : Type} {Lv Hv : ι → Type}
    [∀ v, Group (Lv v)] [∀ v, TopologicalSpace (Lv v)] [∀ v, IsTopologicalGroup (Lv v)]
    [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)]
    (lam : ∀ v, Lv v →* G) (hlam : ∀ v, Continuous (lam v)) (φ : ∀ v, Hv v →ₜ* H)
    (ev : ∀ v, Hv v ≃* Lv v) (hev1 : ∀ v, Continuous (ev v)) (hev2 : ∀ v, Continuous (ev v).symm)
    (hev : ∀ v σ, θ (lam v (ev v σ)) = φ v σ) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (hc : ContAction rho)
    (A : Rep.{0} (ULift.{0} ℤ) H) [IsDiscreteRep A] (eM : M ≃+ A.V)
    (hM : ∀ g m, eM (rho g m) = A.ρ (θ g) (eM m)) :
    ∃ (E : H2 rho ≃+ cohomology A 2)
      (Ev : ∀ v, H2 (rho.comp (lam v)) ≃+ cohomology (Rep.res (φ v).toMonoidHom A) 2),
      ∀ v x, Ev v (resH2 rho (lam v) (hlam v) x) = ptRes φ A v 2 (E x) := by
  have hθs : Continuous (θ.symm : H ≃* G).toMonoidHom := θ.symm.continuous
  let rho' : Representation R H M := rho.comp (θ.symm : H ≃* G).toMonoidHom
  have hM' : ∀ h m, eM (rho' h m) = A.ρ h (eM m) := fun h m => by
    show eM (rho (θ.symm h) m) = _
    rw [hM]
    exact congrArg (fun t => A.ρ t (eM m)) (θ.apply_symm_apply h)
  obtain ⟨e2, he2a, he2b⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 H R M rho' A eM hM'
  have bij := resH2_bijective_of_inverse rho (θ.symm : H ≃* G).toMonoidHom hθs
    (θ : G ≃* H).toMonoidHom θ.continuous (fun g => θ.symm_apply_apply g)
    (fun h => θ.apply_symm_apply h)
  let r2 : H2 rho ≃ₗ[R] H2 rho' := LinearEquiv.ofBijective _ bij
  have hloc : ∀ v, ∀ σ m, eM (((rho.comp (lam v)).comp (ev v).toMonoidHom) σ m) =
      (Rep.res (φ v).toMonoidHom A).ρ σ (eM m) := fun v σ m => by
    show eM (rho (lam v (ev v σ)) m) = A.ρ (φ v σ) (eM m)
    rw [hM, hev]
  choose ev2 hev2a hev2b using fun v => PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 (Hv v) R M
    ((rho.comp (lam v)).comp (ev v).toMonoidHom) (Rep.res (φ v).toMonoidHom A) eM (hloc v)
  have bijv := fun v => resH2_bijective_of_inverse (rho.comp (lam v)) (ev v).toMonoidHom (hev1 v)
    (ev v).symm.toMonoidHom (hev2 v) (fun g => (ev v).apply_symm_apply g)
    (fun h => (ev v).symm_apply_apply h)
  let rv : ∀ v, H2 (rho.comp (lam v)) ≃ₗ[R] H2 ((rho.comp (lam v)).comp (ev v).toMonoidHom) :=
    fun v => LinearEquiv.ofBijective _ (bijv v)
  refine ⟨r2.toAddEquiv.trans e2, fun v => (rv v).toAddEquiv.trans (ev2 v), fun v x => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨y, hy⟩ := he2a (restrictCocycles2 rho (θ.symm : H ≃* G).toMonoidHom hθs z)
    have hE : e2 (r2 (Submodule.Quotient.mk z)) = cohomologyπ A 2 y := he2b _ y hy
    show ev2 v (rv v (resH2 rho (lam v) (hlam v) (Submodule.Quotient.mk z))) =
      ptRes φ A v 2 (e2 (r2 (Submodule.Quotient.mk z)))
    rw [hE]
    have hP : ptRes φ A v 2 (cohomologyπ A 2 y) =
        cohomologyπ _ 2 (cocyclesMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) 2 y) := by
      unfold ptRes
      exact congrArg (fun f => f.hom y) (cohomologyπ_cohomologyMapAlong (φ v).toMonoidHom
        (continuous_toMonoidHom (φ v)) (𝟙 _) 2)
    rw [hP]
    apply hev2b v
    intro s
    rw [cochainOf_cocycleι_cocyclesMapAlong]
    dsimp only
    rw [hy]
    change eM (z.1 (θ.symm (φ v (s 0)), θ.symm (φ v (s 1)))) =
      eM (z.1 (lam v (ev v (s 0)), lam v (ev v (s 1))))
    rw [← hev, ← hev]
    exact congrArg (fun t => eM (z.1 t))
      (Prod.ext (θ.symm_apply_apply _) (θ.symm_apply_apply _))

end PositivityTheory.Lit1.PTN
