import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsNineAdd
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsNineAddIntro
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDualQZ
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PfNineAddFSCReindex

noncomputable section

open CategoryTheory GroundTheory.ProfCoh

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

set_option maxHeartbeats 1000000 in

theorem nineAdd_of_found2 {N : ℕ} [NeZero N]
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {ι : Type} [Fintype ι] {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
    [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
    {κ : Type} [Fintype κ] (e : κ ≃ ι)
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
    {L0 L1 L2 : κ → Type} [∀ k, AddCommGroup (L0 k)] [∀ k, Module (ZMod N) (L0 k)]
    [∀ k, AddCommGroup (L1 k)] [∀ k, Module (ZMod N) (L1 k)]
    [∀ k, AddCommGroup (L2 k)] [∀ k, Module (ZMod N) (L2 k)]
    {Y0 Y1 Y2 : Type} [AddCommGroup Y0] [Module (ZMod N) Y0] [AddCommGroup Y1] [Module (ZMod N) Y1]
    [AddCommGroup Y2] [Module (ZMod N) Y2]
    {W0 W1 W2 : κ → Type} [∀ k, AddCommGroup (W0 k)] [∀ k, Module (ZMod N) (W0 k)]
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

    (E0 : H0 ≃+ cohomology M 0) (E1 : H1 ≃+ cohomology M 1) (E2 : H2 ≃+ cohomology M 2)
    (Ev0 : ∀ k, L0 k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom M) 0)
    (Ev1 : ∀ k, L1 k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom M) 1)
    (Ev2 : ∀ k, L2 k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom M) 2)
    (F0 : Y0 ≃+ cohomology (dualRep D M) 0) (F1 : Y1 ≃+ cohomology (dualRep D M) 1)
    (F2 : Y2 ≃+ cohomology (dualRep D M) 2)
    (Fv0 : ∀ k, W0 k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom (dualRep D M)) 0)
    (Fv1 : ∀ k, W1 k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom (dualRep D M)) 1)
    (Fv2 : ∀ k, W2 k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom (dualRep D M)) 2)
    (sq0 : ∀ k x, Ev0 k (res0 k x) = ptRes φ M (e k) 0 (E0 x))
    (sq1 : ∀ k x, Ev1 k (res1 k x) = ptRes φ M (e k) 1 (E1 x))
    (sq2 : ∀ k x, Ev2 k (res2 k x) = ptRes φ M (e k) 2 (E2 x))
    (tq0 : ∀ k y, Fv0 k (rs0 k y) = ptRes φ (dualRep D M) (e k) 0 (F0 y))
    (tq1 : ∀ k y, Fv1 k (rs1 k y) = ptRes φ (dualRep D M) (e k) 1 (F1 y))
    (tq2 : ∀ k y, Fv2 k (rs2 k y) = ptRes φ (dualRep D M) (e k) 2 (F2 y))
    (hQ0 : ∀ k a b, zmodToQZ N (P0 k a b) =
      - inv (e k) (cupPairing (ptLocalEval φ D M (e k)) (rfl : 0 + 2 = 2) (Ev0 k a) (Fv2 k b)))
    (hQ1 : ∀ k a b, zmodToQZ N (P1 k a b) =
      inv (e k) (cupPairing (ptLocalEval φ D M (e k)) (rfl : 1 + 1 = 2) (Ev1 k a) (Fv1 k b)))
    (hQ2 : ∀ k a b, zmodToQZ N (P2 k a b) =
      - inv (e k) (cupPairing (ptLocalEval φ D M (e k)) (rfl : 2 + 0 = 2) (Ev2 k a) (Fv0 k b))) :
    NineAdd f0 f1 f3 f4 f6 f7 := by
  obtain ⟨i0, x1, x2, x3, x4, x5, x6, x7, s7⟩ := hx
  have hL : ∀ {r : ℕ} {H : Type} [AddCommGroup H] [Module (ZMod N) H] {L : κ → Type}
      [∀ k, AddCommGroup (L k)] [∀ k, Module (ZMod N) (L k)] (res : ∀ k, H →ₗ[ZMod N] L k)
      (f : H →ₗ[ZMod N] ∀ k, L k) (hf : ∀ x k, f x k = res k x) (E : H ≃+ cohomology M r)
      (Ev : ∀ k, L k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom M) r)
      (sq : ∀ k x, Ev k (res k x) = ptRes φ M (e k) r (E x)) (x : H),
      (ptGlobalToLocal φ M r).hom (E x) =
        ((1 : ℤˣ) : ℤ) • ((AddEquiv.piCongrRight Ev).trans
          (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e)) (f x) := by
    intro r H _ _ L _ _ res f hf E Ev sq x
    rw [Units.val_one, one_smul]
    rw [locSq_reindex φ e M r (fun k => (res k).toAddMonoidHom) E Ev sq x]
    rw [AddEquiv.trans_apply]
    refine congrArg _ (funext fun k => ?_)
    rw [AddEquiv.piCongrRight_apply, hf]
    rfl
  have hT : ∀ {r s : ℕ} (h : r + s = 2) {L : κ → Type} [∀ k, AddCommGroup (L k)]
      [∀ k, Module (ZMod N) (L k)] {Y : Type} [AddCommGroup Y] [Module (ZMod N) Y]
      {W : κ → Type} [∀ k, AddCommGroup (W k)] [∀ k, Module (ZMod N) (W k)]
      (rs : ∀ k, Y →ₗ[ZMod N] W k) (P : ∀ k, L k → W k → ZMod N)
      (f : (∀ k, L k) →ₗ[ZMod N] Module.Dual (ZMod N) Y)
      (hf : ∀ x y, f x y = ∑ k, P k (x k) (rs k y))
      (Ev : ∀ k, L k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom M) r)
      (F : Y ≃+ cohomology (dualRep D M) s)
      (Fv : ∀ k, W k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom (dualRep D M)) s)
      (tq : ∀ k y, Fv k (rs k y) = ptRes φ (dualRep D M) (e k) s (F y)) (ε : ℤˣ)
      (hQ : ∀ k a b, (ε : ℤ) • zmodToQZ N (P k a b) =
        inv (e k) (cupPairing (ptLocalEval φ D M (e k)) h (Ev k a) (Fv k b))) (x : ∀ k, L k),
      ptLocalDualMap φ D M inv h (((AddEquiv.piCongrRight Ev).trans
          (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e)) x) =
        (ε : ℤ) • dualQZ F (f x) := by
    intro r s h L _ _ Y _ _ W _ _ rs P f hf Ev F Fv tq ε hQ x
    refine AddMonoidHom.ext fun y => ?_
    rw [AddEquiv.trans_apply]
    change ptLocalDualMap φ D M inv h (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e
      (fun k => Ev k (x k))) y = _
    rw [ptLocalDualMap_reindex, AddMonoidHom.smul_apply, dualQZ_apply, hf, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hQ, tq, AddEquiv.apply_symm_apply, ptLocalPairing_apply]
  exact nineAdd_intro (ptGlobalToLocal φ M 0).hom.toAddMonoidHom
    (ptLocalDualMap φ D M inv (show 0 + 2 = 2 from rfl)) δ₁
    (ptGlobalToLocal φ M 1).hom.toAddMonoidHom (ptLocalDualMap φ D M inv (show 1 + 1 = 2 from rfl)) δ₂
    (ptGlobalToLocal φ M 2).hom.toAddMonoidHom (ptLocalDualMap φ D M inv (show 2 + 0 = 2 from rfl))
    E0 ((AddEquiv.piCongrRight Ev0).trans
      (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) 0) e)) (dualQZ F2)
    E1 ((AddEquiv.piCongrRight Ev1).trans
      (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) 1) e)) (dualQZ F1)
    E2 ((AddEquiv.piCongrRight Ev2).trans
      (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) 2) e)) (dualQZ F0)
    ![1, -1, 1, 1, 1, -1]
    (hL res0 f0 hf0 E0 Ev0 sq0) (hT _ rs2 P0 f1 hf1 Ev0 F2 Fv2 tq2 (-1) (fun k a b => by rw [hQ0, Units.val_neg, Units.val_one, neg_one_zsmul, neg_neg]))
    (hL res1 f3 hf3 E1 Ev1 sq1) (hT _ rs1 P1 f4 hf4 Ev1 F1 Fv1 tq1 1 (fun k a b => by rw [hQ1, Units.val_one, one_smul]))
    (hL res2 f6 hf6 E2 Ev2 sq2) (hT _ rs0 P2 f7 hf7 Ev2 F0 Fv0 tq0 (-1) (fun k a b => by rw [hQ2, Units.val_neg, Units.val_one, neg_one_zsmul, neg_neg]))
    i0 x1 x2 x3 x4 x5 x6 x7 s7

end PositivityTheory.Lit1.PTN
