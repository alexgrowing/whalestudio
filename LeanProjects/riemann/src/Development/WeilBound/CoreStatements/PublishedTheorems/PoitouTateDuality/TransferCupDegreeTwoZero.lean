import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsCup
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmp

noncomputable section

open CategoryTheory MonoidalCategory TensorProduct GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem transfer_cup_degree_two_zero {Lv Hv : Type} [Group Lv] [TopologicalSpace Lv] [IsTopologicalGroup Lv]
    [Group Hv] [TopologicalSpace Hv] [IsTopologicalGroup Hv] (ev : Hv ≃* Lv)
    (hevc : Continuous ev.toMonoidHom) {R : Type} [CommRing R] {M M' P : Type}
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [DiscreteTopology M']
    [AddCommGroup P] [Module R P] [TopologicalSpace P] [DiscreteTopology P]
    (rho : Representation R Lv M) (rho' : Representation R Lv M') (rhoP : Representation R Lv P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))
    (A B C : Rep.{0} (ULift.{0} ℤ) Hv) [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (eA : M ≃+ A.V) (eB : M' ≃+ B.V)
    (heA : ∀ σ m, eA (rho (ev σ) m) = A.ρ σ (eA m))
    (heB : ∀ σ m, eB (rho' (ev σ) m) = B.ρ σ (eB m))
    (μ : A ⊗ B ⟶ C) (rel : P → C.V → Prop)
    (hbμ : ∀ x y, rel (b x y) (μ.hom (eA x ⊗ₜ[ULift.{0} ℤ] eB y)))
    (E : H2 rho ≃+ cohomology A 2)
    (hE : ∀ (z : ↥(Z2 rho)) (x : cocycles A 2),
      (∀ s, cochainOf A (cocycleι A 2 x) s = eA (z.1 (ev (s 0), ev (s 1)))) →
        E (Submodule.Quotient.mk z) = cohomologyπ A 2 x)
    (E' : ↥(H0 rho') ≃+ cohomology B 0)
    (hE' : ∀ (z : ↥(H0 rho')) (x : cocycles B 0),
      (∀ s, cochainOf B (cocycleι B 0 x) s = eB z.1) → E' z = cohomologyπ B 0 x)
    {Q : Type} [AddCommGroup Q] (jp : H2 rhoP →+ Q) (J : cohomology C 2 →+ Q)
    (hJ : ∀ (W : ↥(Z2 rhoP)) (x : cocycles C 2),
      (∀ s, rel (W.1 (ev (s 0), ev (s 1))) (cochainOf C (cocycleι C 2 x) s)) →
        jp (Submodule.Quotient.mk W) = - J (cohomologyπ C 2 x))
    (z : ↥(Z2 rho)) (m : ↥(H0 rho')) :
    jp (cupProductH2H0 rho rho' rhoP b hb hbe (Submodule.Quotient.mk z) m) =
      - J (cupPairing μ (rfl : 2 + 0 = 2) (E (Submodule.Quotient.mk z)) (E' m)) := by
  obtain ⟨e2, he2a, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 Hv R M (rho.comp ev.toMonoidHom) A eA heA
  obtain ⟨x2, hx2⟩ := he2a (restrictCocycles2 rho ev.toMonoidHom hevc z)
  have hm : ∀ σ, (rho'.comp ev.toMonoidHom) σ m.1 = m.1 := fun σ => (mem_riemannRochSpace_iff_regularAt_everywhere rho' m.1).1 m.2 (ev σ)
  obtain ⟨x0, hx0⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.exists_coc B 0 (fun _ => eB m.1) (IsLocallyConstant.const _)
    (by
      refine (PositivityTheory.LocalTateOrthogonality.Gcoh.d_comp (rho'.comp ev.toMonoidHom) B eB heB 0 fun _ => m.1).trans ?_
      funext s
      rw [PositivityTheory.LocalTateOrthogonality.Gcoh.dn_zero, hm (s 0), sub_self]
      exact map_zero eB)
  have hmB : ∀ σ, B.ρ σ (eB m.1) = eB m.1 := fun σ => by
    rw [← heB]
    exact congrArg eB (hm σ)
  have hEz : E (Submodule.Quotient.mk z) = cohomologyπ A 2 x2 := hE z x2 (fun s => hx2 s)
  have hEm : E' m = cohomologyπ B 0 x0 := hE' m x0 (fun s => congrFun hx0 s)
  rw [hEz, hEm, cupPairing_cohomologyπ]
  refine hJ (cupCocycleZ2H0 rho rho' rhoP b hb hbe z m) _ (fun s => ?_)
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles]
  rw [show (cochainOf _ (cocycleι _ 0 x0) fun j : Fin 0 => s ⟨2 + j, by omega⟩) = eB m.1 from
    congrFun hx0 _]
  rw [hmB]
  rw [show (cochainOf _ (cocycleι _ 2 x2) fun i : Fin 2 => s ⟨i, by omega⟩) =
    eA (z.1 (ev (s 0), ev (s 1))) from by rw [hx2]; rfl]
  exact hbμ _ _

end PositivityTheory.Lit1.PTN
