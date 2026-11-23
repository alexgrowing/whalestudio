import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.ResH1BijectiveOfInverse
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.ResH2BijectiveOfInverse

noncomputable section

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem resCmpChar0' {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (θ : G ≃ₜ* H) {ι : Type} {Lv Hv : ι → Type}
    [∀ v, Group (Lv v)] [∀ v, TopologicalSpace (Lv v)] [∀ v, IsTopologicalGroup (Lv v)]
    [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)]
    (lam : ∀ v, Lv v →* G) (hlam : ∀ v, Continuous (lam v)) (φ : ∀ v, Hv v →ₜ* H)
    (ev : ∀ v, Hv v ≃* Lv v) (hev1 : ∀ v, Continuous (ev v)) (hev2 : ∀ v, Continuous (ev v).symm)
    (hev : ∀ v σ, θ (lam v (ev v σ)) = φ v σ) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (hc : ContAction rho)
    (A : Rep.{0} (ULift.{0} ℤ) H) [IsDiscreteRep A] (eM : M ≃+ A.V)
    (hM : ∀ g m, eM (rho g m) = A.ρ (θ g) (eM m)) :
    ∃ (E : ↥(H0 rho) ≃+ cohomology A 0)
      (Ev : ∀ v, ↥(H0 (rho.comp (lam v))) ≃+ cohomology (Rep.res (φ v).toMonoidHom A) 0),
      (∀ v x, Ev v (resH0 rho (lam v)  x) = ptRes φ A v 0 (E x)) ∧
      (∀ (z : ↥(H0 rho)) (x : cocycles A 0),
        (∀ s : Fin 0 → H, cochainOf A (cocycleι A 0 x) s = eM z.1) →
        E z = cohomologyπ A 0 x) ∧
      (∀ v (z : ↥(H0 (rho.comp (lam v)))) (x : cocycles (Rep.res (φ v).toMonoidHom A) 0),
        (∀ s : Fin 0 → Hv v, cochainOf _ (cocycleι _ 0 x) s = eM z.1) →
        Ev v z = cohomologyπ _ 0 x) := by
  have hθs : Continuous (θ.symm : H ≃* G).toMonoidHom := θ.symm.continuous
  let rho' : Representation R H M := rho.comp (θ.symm : H ≃* G).toMonoidHom
  have hM' : ∀ h m, eM (rho' h m) = A.ρ h (eM m) := fun h m => by
    show eM (rho (θ.symm h) m) = _
    rw [hM]
    exact congrArg (fun t => A.ρ t (eM m)) (θ.apply_symm_apply h)
  obtain ⟨e0, he0⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc0 H R M rho' A eM hM'
  have hEq : H0 rho = H0 rho' := by
    ext m
    constructor
    · intro hm h
      exact hm _
    · intro hm g
      have := hm (θ g)
      change rho (θ.symm (θ g)) m = m at this
      rwa [θ.symm_apply_apply] at this
  let r0 : ↥(H0 rho) ≃ₗ[R] ↥(H0 rho') := LinearEquiv.ofEq _ _ hEq
  have hloc : ∀ v, ∀ σ m, eM (((rho.comp (lam v)).comp (ev v).toMonoidHom) σ m) =
      (Rep.res (φ v).toMonoidHom A).ρ σ (eM m) := fun v σ m => by
    show eM (rho (lam v (ev v σ)) m) = A.ρ (φ v σ) (eM m)
    rw [hM, hev]
  choose ev0 hev0 using fun v => PositivityTheory.LocalTateOrthogonality.Gcoh.gc0 (Hv v) R M
    ((rho.comp (lam v)).comp (ev v).toMonoidHom) (Rep.res (φ v).toMonoidHom A) eM (hloc v)
  have hEqv : ∀ v, H0 (rho.comp (lam v)) = H0 ((rho.comp (lam v)).comp (ev v).toMonoidHom) := by
    intro v
    ext m
    constructor
    · intro hm h
      exact hm _
    · intro hm g
      have := hm ((ev v).symm g)
      change rho (lam v (ev v ((ev v).symm g))) m = m at this
      rwa [MulEquiv.apply_symm_apply] at this
  let rv : ∀ v, ↥(H0 (rho.comp (lam v))) ≃ₗ[R] ↥(H0 ((rho.comp (lam v)).comp (ev v).toMonoidHom)) :=
    fun v => LinearEquiv.ofEq _ _ (hEqv v)
  refine ⟨r0.toAddEquiv.trans e0, fun v => (rv v).toAddEquiv.trans (ev0 v), fun v z => ?_, fun z x hx => ?_, fun v z x hx => ?_⟩
  have hz' : (z : M) ∈ H0 rho' := hEq ▸ z.2
  obtain ⟨x, hx⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.exists_coc A 0 (fun _ => eM z.1) (IsLocallyConstant.const _) (by
      refine (PositivityTheory.LocalTateOrthogonality.Gcoh.d_comp rho' A eM hM' 0 fun _ => z.1).trans ?_
      funext s
      rw [PositivityTheory.LocalTateOrthogonality.Gcoh.dn_zero, hz' (s 0), sub_self]
      exact map_zero eM)
  have hE : e0 (r0 z) = cohomologyπ A 0 x := he0 _ x (fun s => congrFun hx s)
  show ev0 v (rv v (resH0 rho (lam v) z)) = ptRes φ A v 0 (e0 (r0 z))
  rw [hE]
  have hP : ptRes φ A v 0 (cohomologyπ A 0 x) =
      cohomologyπ _ 0 (cocyclesMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) 0 x) := by
    unfold ptRes
    exact congrArg (fun f => f.hom x) (cohomologyπ_cohomologyMapAlong (φ v).toMonoidHom
      (continuous_toMonoidHom (φ v)) (𝟙 _) 0)
  rw [hP]
  apply hev0 v
  intro s
  rw [cochainOf_cocycleι_cocyclesMapAlong]
  dsimp only
  rw [hx]
  rfl
  · show e0 (r0 z) = _
    exact he0 _ x (fun s => hx s)
  · show ev0 v (rv v z) = _
    exact hev0 v _ x (fun s => hx s)

theorem resCmpChar1' {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (θ : G ≃ₜ* H) {ι : Type} {Lv Hv : ι → Type}
    [∀ v, Group (Lv v)] [∀ v, TopologicalSpace (Lv v)] [∀ v, IsTopologicalGroup (Lv v)]
    [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)]
    (lam : ∀ v, Lv v →* G) (hlam : ∀ v, Continuous (lam v)) (φ : ∀ v, Hv v →ₜ* H)
    (ev : ∀ v, Hv v ≃* Lv v) (hev1 : ∀ v, Continuous (ev v)) (hev2 : ∀ v, Continuous (ev v).symm)
    (hev : ∀ v σ, θ (lam v (ev v σ)) = φ v σ) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (hc : ContAction rho)
    (A : Rep.{0} (ULift.{0} ℤ) H) [IsDiscreteRep A] (eM : M ≃+ A.V)
    (hM : ∀ g m, eM (rho g m) = A.ρ (θ g) (eM m)) :
    ∃ (E : H1 rho ≃+ cohomology A 1)
      (Ev : ∀ v, H1 (rho.comp (lam v)) ≃+ cohomology (Rep.res (φ v).toMonoidHom A) 1),
      (∀ v x, Ev v (resH1 rho (lam v) (hlam v) x) = ptRes φ A v 1 (E x)) ∧
      (∀ (z : ↥(Z1 rho)) (x : cocycles A 1),
        (∀ s : Fin 1 → H, cochainOf A (cocycleι A 1 x) s = eM (z.1 (θ.symm (s 0)))) →
        E (Submodule.Quotient.mk z) = cohomologyπ A 1 x) ∧
      (∀ v (z : ↥(Z1 (rho.comp (lam v)))) (x : cocycles (Rep.res (φ v).toMonoidHom A) 1),
        (∀ s : Fin 1 → Hv v, cochainOf _ (cocycleι _ 1 x) s = eM (z.1 (ev v (s 0)))) →
        Ev v (Submodule.Quotient.mk z) = cohomologyπ _ 1 x) := by
  have hθs : Continuous (θ.symm : H ≃* G).toMonoidHom := θ.symm.continuous
  let rho' : Representation R H M := rho.comp (θ.symm : H ≃* G).toMonoidHom
  have hM' : ∀ h m, eM (rho' h m) = A.ρ h (eM m) := fun h m => by
    show eM (rho (θ.symm h) m) = _
    rw [hM]
    simp
  obtain ⟨e1, he1a, he1b⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 H R M rho' A eM hM'
  have bij := resH1_bijective_of_inverse rho (θ.symm : H ≃* G).toMonoidHom hθs
    (θ : G ≃* H).toMonoidHom θ.continuous (fun g => θ.symm_apply_apply g) (fun h => θ.apply_symm_apply h)
  let r1 : H1 rho ≃ₗ[R] H1 rho' := LinearEquiv.ofBijective _ bij
  have hloc : ∀ v, ∀ σ m, eM (((rho.comp (lam v)).comp (ev v).toMonoidHom) σ m) =
      (Rep.res (φ v).toMonoidHom A).ρ σ (eM m) := fun v σ m => by
    show eM (rho (lam v (ev v σ)) m) = A.ρ (φ v σ) (eM m)
    rw [hM, hev]
  choose ev1 hev1a hev1b using fun v => PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 (Hv v) R M
    ((rho.comp (lam v)).comp (ev v).toMonoidHom) (Rep.res (φ v).toMonoidHom A) eM (hloc v)
  have bijv := fun v => resH1_bijective_of_inverse (rho.comp (lam v)) (ev v).toMonoidHom (hev1 v)
    (ev v).symm.toMonoidHom (hev2 v) (fun g => (ev v).apply_symm_apply g) (fun h => (ev v).symm_apply_apply h)
  let rv : ∀ v, H1 (rho.comp (lam v)) ≃ₗ[R] H1 ((rho.comp (lam v)).comp (ev v).toMonoidHom) :=
    fun v => LinearEquiv.ofBijective _ (bijv v)
  refine ⟨r1.toAddEquiv.trans e1, fun v => (rv v).toAddEquiv.trans (ev1 v), fun v x => ?_, fun z x hx => ?_, fun v z x hx => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨y, hy⟩ := he1a (restrictCocycles1 rho (θ.symm : H ≃* G).toMonoidHom hθs z)
    have hE : e1 (r1 (Submodule.Quotient.mk z)) = cohomologyπ A 1 y := he1b _ y hy
    show ev1 v (rv v (resH1 rho (lam v) (hlam v) (Submodule.Quotient.mk z))) =
      ptRes φ A v 1 (e1 (r1 (Submodule.Quotient.mk z)))
    rw [hE]
    have hP : ptRes φ A v 1 (cohomologyπ A 1 y) =
        cohomologyπ _ 1 (cocyclesMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) 1 y) := by
      unfold ptRes
      exact congrArg (fun f => f.hom y) (cohomologyπ_cohomologyMapAlong (φ v).toMonoidHom
        (continuous_toMonoidHom (φ v)) (𝟙 _) 1)
    rw [hP]
    apply hev1b v
    intro s
    rw [cochainOf_cocycleι_cocyclesMapAlong]
    dsimp only
    rw [hy]
    change eM (z.1 (θ.symm (φ v (s 0)))) = eM (z.1 (lam v (ev v (s 0))))
    rw [← hev]
    exact congrArg (fun t => eM (z.1 t)) (θ.symm_apply_apply _)
  · show e1 (r1 (Submodule.Quotient.mk z)) = _
    exact he1b (restrictCocycles1 rho (θ.symm : H ≃* G).toMonoidHom hθs z) x (fun s => by rw [hx s]; rfl)
  · show ev1 v (rv v (Submodule.Quotient.mk z)) = _
    exact hev1b v (restrictCocycles1 (rho.comp (lam v)) (ev v).toMonoidHom (hev1 v) z) x (fun s => by rw [hx s]; rfl)

theorem resCmpChar2' {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
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
      (∀ v x, Ev v (resH2 rho (lam v) (hlam v) x) = ptRes φ A v 2 (E x)) ∧
      (∀ (z : ↥(Z2 rho)) (x : cocycles A 2),
        (∀ s : Fin 2 → H, cochainOf A (cocycleι A 2 x) s = eM (z.1 (θ.symm (s 0), θ.symm (s 1)))) →
        E (Submodule.Quotient.mk z) = cohomologyπ A 2 x) ∧
      (∀ v (z : ↥(Z2 (rho.comp (lam v)))) (x : cocycles (Rep.res (φ v).toMonoidHom A) 2),
        (∀ s : Fin 2 → Hv v, cochainOf _ (cocycleι _ 2 x) s = eM (z.1 (ev v (s 0), ev v (s 1)))) →
        Ev v (Submodule.Quotient.mk z) = cohomologyπ _ 2 x) := by
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
  refine ⟨r2.toAddEquiv.trans e2, fun v => (rv v).toAddEquiv.trans (ev2 v), fun v x => ?_, fun z x hx => ?_, fun v z x hx => ?_⟩
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
  · show e2 (r2 (Submodule.Quotient.mk z)) = _
    exact he2b (restrictCocycles2 rho (θ.symm : H ≃* G).toMonoidHom hθs z) x (fun s => by rw [hx s]; rfl)
  · show ev2 v (rv v (Submodule.Quotient.mk z)) = _
    exact hev2b v (restrictCocycles2 (rho.comp (lam v)) (ev v).toMonoidHom (hev1 v) z) x (fun s => by rw [hx s]; rfl)

end PositivityTheory.Lit1.PTN
