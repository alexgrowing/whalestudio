import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTateA

open CategoryTheory MonoidalCategory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace CompanionTheory.LocalTateOrthogonality.Gcoh

attribute [local instance 2000] Rep.hV2

section Core

variable {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M M' P : Type} [AddCommGroup M] [Module (ZMod n) M] [AddCommGroup M'] [Module (ZMod n) M']
  [AddCommGroup P] [Module (ZMod n) P]
  [TopologicalSpace M] [DiscreteTopology M] [TopologicalSpace M'] [DiscreteTopology M']
  [TopologicalSpace P] [DiscreteTopology P]
  (rho : Representation (ZMod n) G M) (rho' : Representation (ZMod n) G M')
  (rhoP : Representation (ZMod n) G P) (b : M →ₗ[ZMod n] M' →ₗ[ZMod n] P)
  (hbc : Continuous fun p : M × M' => b p.1 p.2)
  (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))
  (A D : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] [IsDiscreteRep D]
  [IsDiscreteRep (dualRep D A)]
  (eA : M ≃+ A.V) (hA : ∀ g m, eA (rho g m) = A.ρ g (eA m))
  (eD : P ≃+ D.V) (hD : ∀ g m, eD (rhoP g m) = D.ρ g (eD m))
  (eB : M' ≃+ (dualRep D A).V) (hB : ∀ g y, eB (rho' g y) = (dualRep D A).ρ g (eB y))
  (hev : ∀ x y, (eB y : A →ₗ[ULift.{0} ℤ] D) (eA x) = eD (b x y))
  (t : cohomology D 2 ≃+ ZMod n)

omit [DiscreteTopology M] in
include hA in
theorem exists_cocycle_zero [IsTopologicalAddGroup M] [ContinuousConstSMul (ZMod n) M]
    (m : H0 rho) :
    ∃ x : cocycles A 0, ∀ s, cochainOf A (cocycleι A 0 x) s = eA m.1 := by
  obtain ⟨z, -, hz⟩ := exists_cocycle_H0Iso_inv A ⟨eA m.1, fun g => by
    rw [← hA, (mem_riemannRochSpace_iff_regularAt_everywhere rho m.1).1 m.2 g]⟩
  exact ⟨z, fun s => by rw [hz]⟩

include hA hD hB hev in
theorem cup_product_H0_H2_bijective (h0 : Sgc0) (h2 : Sgc2)
    (hd : Function.Bijective (dualityMap D (rfl : 0 + 2 = 2) t.toAddMonoidHom A)) :
    Function.Bijective (cupProductH0H2 rho rho' rhoP b hbc hbe) := by
  obtain ⟨e0, he0⟩ := h0 G (ZMod n) M rho A eA hA
  obtain ⟨e2, hex, he2⟩ := h2 G (ZMod n) M' rho' (dualRep D A) eB hB
  obtain ⟨eP, -, heP⟩ := h2 G (ZMod n) P rhoP D eD hD
  refine bij_transport _ _ e0 e2 (eP.trans t) (fun m y => ?_) hd
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨x, hx⟩ := exists_cocycle_zero rho A eA hA m
  obtain ⟨w, hw⟩ := hex z
  rw [he0 m x hx, he2 z w hw, dualityMap_apply, cupPairing_cohomologyπ, AddEquiv.trans_apply]
  refine congrArg t (heP (cupCocycleH0Z2 rho rho' rhoP b hbc hbe m z) _ fun s => ?_)
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, hx, hw, ← hB]
  refine (evalPairing_tmul D A _ _).trans ?_
  rw [hev, cupCocycleH0Z2_apply]
  congr 2
  simp [Fin.partialProd]

include hA hD hB hev in
theorem cup_product_H2_H0_bijective (h0 : Sgc0) (h2 : Sgc2)
    (hd : Function.Bijective (dualityMap D (rfl : 2 + 0 = 2) t.toAddMonoidHom A)) :
    Function.Bijective (cupProductH2H0 rho rho' rhoP b hbc hbe) := by
  obtain ⟨e0, he0⟩ := h0 G (ZMod n) M' rho' (dualRep D A) eB hB
  obtain ⟨e2, hex, he2⟩ := h2 G (ZMod n) M rho A eA hA
  obtain ⟨eP, -, heP⟩ := h2 G (ZMod n) P rhoP D eD hD
  refine bij_transport _ _ e2 e0 (eP.trans t) (fun y m => ?_) hd
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨x, hx⟩ := exists_cocycle_zero rho' (dualRep D A) eB hB m
  obtain ⟨w, hw⟩ := hex z
  rw [he0 m x hx, he2 z w hw, dualityMap_apply, cupPairing_cohomologyπ, AddEquiv.trans_apply]
  refine congrArg t (heP (cupCocycleZ2H0 rho rho' rhoP b hbc hbe z m) _ fun s => ?_)
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, hx, hw, ← hB]
  refine (evalPairing_tmul D A _ _).trans ?_
  rw [hev, cupCocycleZ2H0_apply, (mem_riemannRochSpace_iff_regularAt_everywhere rho' m.1).1 m.2]

include hA hD hB hev in
theorem cup_product_H1_H1_bijective (h1 : Sgc1) (h2 : Sgc2) (hc : ContAction rho')
    (hd : Function.Bijective (dualityMap D (rfl : 1 + 1 = 2) t.toAddMonoidHom A)) :
    Function.Bijective (cupProductH1H1 rho rho' rhoP b hbc hbe hc) := by
  obtain ⟨e1, hex1, he1⟩ := h1 G (ZMod n) M rho A eA hA
  obtain ⟨e1', hex1', he1'⟩ := h1 G (ZMod n) M' rho' (dualRep D A) eB hB
  obtain ⟨eP, -, heP⟩ := h2 G (ZMod n) P rhoP D eD hD
  refine bij_transport _ _ e1 e1' (eP.trans t) (fun y y' => ?_) hd
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ y'
  obtain ⟨x, hx⟩ := hex1 z
  obtain ⟨w, hw⟩ := hex1' z'
  rw [he1 z x hx, he1' z' w hw, dualityMap_apply, cupPairing_cohomologyπ, AddEquiv.trans_apply]
  refine congrArg t (heP (cupCocycleZ1Z1 rho rho' rhoP b hbc hbe hc z z') _ fun s => ?_)
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, hx, hw, ← hB]
  refine (evalPairing_tmul D A _ _).trans ?_
  rw [hev, cupCocycleZ1Z1_apply]
  congr 2
  simp [Fin.partialProd]

end Core

end CompanionTheory.LocalTateOrthogonality.Gcoh
