import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.NineAddOfFound2Fun

noncomputable section

open CategoryTheory GroundTheory.ProfCoh

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

set_option maxHeartbeats 1000000 in
theorem nineAdd_of_found3 {N : ℕ} [NeZero N]
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {α : Type} (S : Finset α) [Fintype ↥(↑S : Set α)] {Hv : ↥(↑S : Set α) → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
    [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
    (D : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep D] (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M]
    [Finite M] (inv : ∀ v, cohomology (Rep.res (φ v).toMonoidHom D) 2 →+ QZ)
    (δ₁ : (cohomology (dualRep D M) 2 →+ QZ) →+ cohomology M 1)
    (δ₂ : (cohomology (dualRep D M) 1 →+ QZ) →+ cohomology M 2)
    (hx : Function.Injective (ptGlobalToLocal φ M 0).hom ∧
      Function.Exact (ptGlobalToLocal φ M 0).hom (ptLocalDualMap φ D M inv (show 0 + 2 = 2 from rfl)) ∧
      Function.Exact (ptLocalDualMap φ D M inv (show 0 + 2 = 2 from rfl)) δ₁ ∧
      Function.Exact δ₁ (ptGlobalToLocal φ M 1).hom ∧
      Function.Exact (ptGlobalToLocal φ M 1).hom (ptLocalDualMap φ D M inv (show 1 + 1 = 2 from rfl)) ∧
      Function.Exact (ptLocalDualMap φ D M inv (show 1 + 1 = 2 from rfl)) δ₂ ∧
      Function.Exact δ₂ (ptGlobalToLocal φ M 2).hom ∧
      Function.Exact (ptGlobalToLocal φ M 2).hom (ptLocalDualMap φ D M inv (show 2 + 0 = 2 from rfl)) ∧
      Function.Surjective (ptLocalDualMap φ D M inv (show 2 + 0 = 2 from rfl)))

    {H0 H1 H2 : Type} [AddCommGroup H0] [Module (ZMod N) H0] [AddCommGroup H1] [Module (ZMod N) H1]
    [AddCommGroup H2] [Module (ZMod N) H2]
    {L0 L1 L2 : S → Type} [∀ k, AddCommGroup (L0 k)] [∀ k, Module (ZMod N) (L0 k)]
    [∀ k, AddCommGroup (L1 k)] [∀ k, Module (ZMod N) (L1 k)]
    [∀ k, AddCommGroup (L2 k)] [∀ k, Module (ZMod N) (L2 k)]
    {Y0 Y1 Y2 : Type} [AddCommGroup Y0] [Module (ZMod N) Y0] [AddCommGroup Y1] [Module (ZMod N) Y1]
    [AddCommGroup Y2] [Module (ZMod N) Y2]
    {W0 W1 W2 : S → Type} [∀ k, AddCommGroup (W0 k)] [∀ k, Module (ZMod N) (W0 k)]
    [∀ k, AddCommGroup (W1 k)] [∀ k, Module (ZMod N) (W1 k)]
    [∀ k, AddCommGroup (W2 k)] [∀ k, Module (ZMod N) (W2 k)]
    (res0 : ∀ k, H0 →ₗ[ZMod N] L0 k) (res1 : ∀ k, H1 →ₗ[ZMod N] L1 k)
    (res2 : ∀ k, H2 →ₗ[ZMod N] L2 k)
    (rs0 : ∀ k, Y0 →ₗ[ZMod N] W0 k) (rs1 : ∀ k, Y1 →ₗ[ZMod N] W1 k) (rs2 : ∀ k, Y2 →ₗ[ZMod N] W2 k)
    (P0 : ∀ k, L0 k → W2 k → ZMod N) (P1 : ∀ k, L1 k → W1 k → ZMod N)
    (P2 : ∀ k, L2 k → W0 k → ZMod N)
    (f0 : H0 →ₗ[ZMod N] ∀ k, L0 k) (f1 : (∀ k, L0 k) →ₗ[ZMod N] Module.Dual (ZMod N) Y2)
    (f3 : H1 →ₗ[ZMod N] ∀ k, L1 k) (f4 : (∀ k, L1 k) →ₗ[ZMod N] Module.Dual (ZMod N) Y1)
    (f6 : H2 →ₗ[ZMod N] ∀ k, L2 k) (f7 : (∀ k, L2 k) →ₗ[ZMod N] Module.Dual (ZMod N) Y0)
    (hf0 : ∀ x k, f0 x k = res0 k x) (hf3 : ∀ x k, f3 x k = res1 k x)
    (hf6 : ∀ x k, f6 x k = res2 k x)
    (hf1 : ∀ x y, f1 x y = ∑ k, P0 k (x k) (rs2 k y))
    (hf4 : ∀ x y, f4 x y = ∑ k, P1 k (x k) (rs1 k y))
    (hf7 : ∀ x y, f7 x y = ∑ k, P2 k (x k) (rs0 k y))
    {BM0 : (H0 ≃+ cohomology M 0) → Prop}
    {CM0 : (∀ k : S, L0 k ≃+ cohomology (Rep.res (φ ⟨k.1, Finset.mem_coe.2 k.2⟩).toMonoidHom M) 0) → Prop}
    (hM0 : ∃ (E : H0 ≃+ cohomology M 0) (Ev : ∀ k : S, L0 k ≃+ cohomology (Rep.res (φ ⟨k.1, Finset.mem_coe.2 k.2⟩).toMonoidHom M) 0),
      (∀ k x, Ev k (res0 k x) = ptRes (fun v : S => φ ⟨v.1, Finset.mem_coe.2 v.2⟩) M k 0 (E x)) ∧ BM0 E ∧ CM0 Ev)
    {TranslateJetMomentLawAnyIdempotentLevel : (H1 ≃+ cohomology M 1) → Prop}
    {JInvariantIntegrality : (∀ k : S, L1 k ≃+ cohomology (Rep.res (φ ⟨k.1, Finset.mem_coe.2 k.2⟩).toMonoidHom M) 1) → Prop}
    (hM1 : ∃ (E : H1 ≃+ cohomology M 1) (Ev : ∀ k : S, L1 k ≃+ cohomology (Rep.res (φ ⟨k.1, Finset.mem_coe.2 k.2⟩).toMonoidHom M) 1),
      (∀ k x, Ev k (res1 k x) = ptRes (fun v : S => φ ⟨v.1, Finset.mem_coe.2 v.2⟩) M k 1 (E x)) ∧ TranslateJetMomentLawAnyIdempotentLevel E ∧ JInvariantIntegrality Ev)
    {LocallyConstantJetMomentLawAnyIdempotentLevel : (H2 ≃+ cohomology M 2) → Prop}
    {CM2 : (∀ k : S, L2 k ≃+ cohomology (Rep.res (φ ⟨k.1, Finset.mem_coe.2 k.2⟩).toMonoidHom M) 2) → Prop}
    (hM2 : ∃ (E : H2 ≃+ cohomology M 2) (Ev : ∀ k : S, L2 k ≃+ cohomology (Rep.res (φ ⟨k.1, Finset.mem_coe.2 k.2⟩).toMonoidHom M) 2),
      (∀ k x, Ev k (res2 k x) = ptRes (fun v : S => φ ⟨v.1, Finset.mem_coe.2 v.2⟩) M k 2 (E x)) ∧ LocallyConstantJetMomentLawAnyIdempotentLevel E ∧ CM2 Ev)
    {BD0 : (Y0 ≃+ cohomology (dualRep D M) 0) → Prop}
    {weightDegreeConstant : (∀ k : S, W0 k ≃+ cohomology (Rep.res (φ ⟨k.1, Finset.mem_coe.2 k.2⟩).toMonoidHom (dualRep D M)) 0) → Prop}
    (hD0 : ∃ (E : Y0 ≃+ cohomology (dualRep D M) 0) (Ev : ∀ k : S, W0 k ≃+ cohomology (Rep.res (φ ⟨k.1, Finset.mem_coe.2 k.2⟩).toMonoidHom (dualRep D M)) 0),
      (∀ k x, Ev k (rs0 k x) = ptRes (fun v : S => φ ⟨v.1, Finset.mem_coe.2 v.2⟩) (dualRep D M) k 0 (E x)) ∧ BD0 E ∧ weightDegreeConstant Ev)
    {BD1 : (Y1 ≃+ cohomology (dualRep D M) 1) → Prop}
    {CD1 : (∀ k : S, W1 k ≃+ cohomology (Rep.res (φ ⟨k.1, Finset.mem_coe.2 k.2⟩).toMonoidHom (dualRep D M)) 1) → Prop}
    (hD1 : ∃ (E : Y1 ≃+ cohomology (dualRep D M) 1) (Ev : ∀ k : S, W1 k ≃+ cohomology (Rep.res (φ ⟨k.1, Finset.mem_coe.2 k.2⟩).toMonoidHom (dualRep D M)) 1),
      (∀ k x, Ev k (rs1 k x) = ptRes (fun v : S => φ ⟨v.1, Finset.mem_coe.2 v.2⟩) (dualRep D M) k 1 (E x)) ∧ BD1 E ∧ CD1 Ev)
    {BD2 : (Y2 ≃+ cohomology (dualRep D M) 2) → Prop}
    {CD2 : (∀ k : S, W2 k ≃+ cohomology (Rep.res (φ ⟨k.1, Finset.mem_coe.2 k.2⟩).toMonoidHom (dualRep D M)) 2) → Prop}
    (hD2 : ∃ (E : Y2 ≃+ cohomology (dualRep D M) 2) (Ev : ∀ k : S, W2 k ≃+ cohomology (Rep.res (φ ⟨k.1, Finset.mem_coe.2 k.2⟩).toMonoidHom (dualRep D M)) 2),
      (∀ k x, Ev k (rs2 k x) = ptRes (fun v : S => φ ⟨v.1, Finset.mem_coe.2 v.2⟩) (dualRep D M) k 2 (E x)) ∧ BD2 E ∧ CD2 Ev)
    (hQ0 : ∀ Ev Fv, CM0 Ev → CD2 Fv → ∀ (k : S) a b, zmodToQZ N (P0 k a b) =
      - inv ⟨k.1, Finset.mem_coe.2 k.2⟩ (cupPairing (ptLocalEval φ D M ⟨k.1, Finset.mem_coe.2 k.2⟩) (rfl : 0 + 2 = 2) (Ev k a) (Fv k b)))
    (hQ1 : ∀ Ev Fv, JInvariantIntegrality Ev → CD1 Fv → ∀ (k : S) a b, zmodToQZ N (P1 k a b) =
      inv ⟨k.1, Finset.mem_coe.2 k.2⟩ (cupPairing (ptLocalEval φ D M ⟨k.1, Finset.mem_coe.2 k.2⟩) (rfl : 1 + 1 = 2) (Ev k a) (Fv k b)))
    (hQ2 : ∀ Ev Fv, CM2 Ev → weightDegreeConstant Fv → ∀ (k : S) a b, zmodToQZ N (P2 k a b) =
      - inv ⟨k.1, Finset.mem_coe.2 k.2⟩ (cupPairing (ptLocalEval φ D M ⟨k.1, Finset.mem_coe.2 k.2⟩) (rfl : 2 + 0 = 2) (Ev k a) (Fv k b))) :
    NineAdd f0 f1 f3 f4 f6 f7 := by
  obtain ⟨E0, Ev0, sq0, -, c0⟩ := hM0
  obtain ⟨E1, Ev1, sq1, -, c1⟩ := hM1
  obtain ⟨E2, Ev2, sq2, -, c2⟩ := hM2
  obtain ⟨F0, Fv0, tq0, -, d0⟩ := hD0
  obtain ⟨F1, Fv1, tq1, -, d1⟩ := hD1
  obtain ⟨F2, Fv2, tq2, -, d2⟩ := hD2
  exact nineAdd_of_found2 φ (finsetCoeEquiv S) D M inv δ₁ δ₂ hx res0 res1 res2 rs0 rs1 rs2 P0 P1 P2 f0 f1 f3 f4 f6 f7
    hf0 hf3 hf6 hf1 hf4 hf7 E0 E1 E2 Ev0 Ev1 Ev2 F0 F1 F2 Fv0 Fv1 Fv2 sq0 sq1 sq2 tq0 tq1 tq2
    (hQ0 Ev0 Fv2 c0 d2) (hQ1 Ev1 Fv1 c1 d1) (hQ2 Ev2 Fv0 c2 d0)

end PositivityTheory.Lit1.PTN
