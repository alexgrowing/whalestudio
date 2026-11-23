import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSec
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.TorsionZeroCountTwist
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AbTriv

variable {X X' S S' : Scheme.{0}} {N : LB X}

theorem exists_normalised (hN : N.IsLB) {p : X ⟶ S} {e : S ⟶ X} (he : e ≫ p = 𝟙 S)
    (c : LB.Gen (N.pull e)) (hc : c.IsGen) {π : X' ⟶ X} {p' : X' ⟶ S'} {g : S' ⟶ S}
    (h : IsPullback π p' p g) (ht : Triv (N.pull π)) :
    ∃ t : LB.Gen (N.pull π), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (b : Z ⟶ S) (z : Z) (J),
      Good N z J → r ≫ π = b ≫ e → val t r z J = val c b z J := by
  obtain ⟨t, ht⟩ := ht
  let n : X' ⟶ X' := h.lift ((π ≫ p) ≫ e) p' (by rw [Category.assoc, he, Category.comp_id, h.w])
  have n₁ : n ≫ π = (π ≫ p) ≫ e := h.lift_fst _ _ _
  have n₂ : n ≫ p' = p' := h.lift_snd _ _ _
  obtain ⟨t', ht', hv⟩ := exists_gen hN (K' := PUnit) (φ' := fun _ => π) (ε' := fun _ => 1)
    (fun V _ k => by
      refine (Fintype.prod_sum_type _).trans ?_
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, n₁, mul_inv_cancel,
        _root_.mul_one])
    (LB.mulGen N _ _ _ _ t (LB.mulGen N _ _ _ _ (LB.pullGen N _ _ c (π ≫ p))
      (LB.invGen N _ _ (LB.pullGen N _ _ t n))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hc _)
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht n))))
  refine ⟨t', ht', fun Z r b z J hJ hr => ?_⟩
  have hb : r ≫ π ≫ p = b := by rw [← Category.assoc, hr, Category.assoc, he, Category.comp_id]
  have hn : r ≫ n = r := h.hom_ext
    (by rw [Category.assoc, n₁, ← Category.assoc, hb, hr]) (by rw [Category.assoc, n₂])
  rw [hv Z r z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, hn, hb, mul_comm (val c b z J),
    mul_inv_cancel_left]

theorem triv_of_pull_id (h : Triv (N.pull (𝟙 X))) : Triv N := by
  obtain ⟨t, ht⟩ := h
  have le : ∀ i, N.U i ≤ (N.pull (𝟙 X)).U (fun _ => i) := fun i x hx => mem_pull.2 hx
  refine ⟨⟨fun i => res (le i) (t.s fun _ => i)⟩, fun i j => unit_ext fun x hx => ?_⟩
  have e := gen_trans ht (𝟙 X) x (le i hx.1) (le j hx.2)
  simp only [trF, Finset.univ_unique, Finset.prod_singleton, zpow_one, Category.id_comp] at e
  refine ((gm_res _ x _ hx _).trans (gm_res _ x _ hx.1 _)).trans (e.trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ((gm_res _ x _ hx _).trans (gm_res _ x _ hx.2 _)))

theorem eq_top_of_closed_fibre {V : Type} [CommRing V] [IsLocalRing V] (p : X ⟶ Spec (CommRingCat.of V))
    [UniversallyClosed p] (U : X.Opens) (h : ∀ x, p x = IsLocalRing.closedPoint V → x ∈ U) : U = ⊤ := by
  have hc : IsClosed (p '' (U : Set X)ᶜ) := p.isClosedMap _ U.isOpen.isClosed_compl
  have := DVR.eq_top_of_closedPoint_mem (V := V) ⟨_, hc.isOpen_compl⟩ (by
    rintro ⟨x, hx, e⟩
    exact hx (h x e))
  refine eq_top_iff.2 fun x _ => by_contra fun hx => ?_
  have hm : p x ∈ (⊤ : (Spec (CommRingCat.of V)).Opens) := trivial
  rw [← this] at hm
  exact hm ⟨x, hx, rfl⟩

theorem closedPoint_mem_range {V : Type} [CommRing V] [IsLocalRing V] (e : ℕ) :
    IsLocalRing.closedPoint V ∈ Set.range (thick V (IsLocalRing.maximalIdeal V) e) := by
  have h := range_comap_of_surjective _ _
    (Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal V ^ (e + 1)))
  refine h.ge ?_
  rw [Ideal.mk_ker]
  exact Ideal.pow_le_self (Nat.succ_ne_zero e)

theorem triv_of_forall_thick : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (B : Over (Spec (CommRingCat.of V))) [GrpObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ N : LB B.left, N.IsLB → (∀ e, Triv (N.pull (fstG (IsLocalRing.maximalIdeal V) e B).left)) → Triv N := by
  intro hG V _ _ _ hV B _ hB hp N hN ht
  let I := IsLocalRing.maximalIdeal V
  let o : Spec (CommRingCat.of V) ⟶ B.left := (η[B]).left
  have ho : o ≫ B.hom = 𝟙 _ := Over.w η[B]
  obtain ⟨c, hc⟩ := DVR.exists_gen_of_local N hN (K := PUnit) (fun _ => o) (fun _ => 1)
  have pb : ∀ e, IsPullback (fstG I e B).left (thickObj V I e B).hom B.hom (thick V I e) :=
    fun e => IsPullback.of_hasPullback B.hom (thick V I e)
  choose t tg tv using fun e => exists_normalised hN ho c hc (pb e) (ht e)
  have tm : ∀ e, thickMap V I e B ≫ (fstG I (e + 1) B).left = (fstG I e B).left := fun e =>
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have compat : ∀ e z J, Good N z J → val (t (e + 1)) (thickMap V I e B) z J = val (t e) (𝟙 _) z J := by
    intro e z J hJ
    let a := (pb e).lift (thick V I e ≫ o) (𝟙 _) (by rw [Category.assoc, ho, Category.comp_id, Category.id_comp])
    have a₁ : a ≫ (fstG I e B).left = thick V I e ≫ o := (pb e).lift_fst _ _ _
    have key := gen_unique' hN (fun U _ k => by simp only [tm e]) (thickObj V I e B).hom a ((pb e).lift_snd _ _ _)
      (hG _ _ (TLinPf.isAb_pullback (thick V I e) B hB)).2 (tg e)
      (DVR.pullGen_isGen _ _ _ _ (tg (e + 1)) (thickMap V I e B))
      (fun y J hJ => (tv e _ a _ y J hJ a₁).trans ((val_pull hJ _ _ _).trans
        (tv (e + 1) _ _ _ y J hJ (by rw [Category.assoc, tm e, a₁]))).symm) _ (𝟙 _) z J hJ
    rw [val_pull hJ, Category.id_comp] at key
    exact key.symm
  obtain ⟨s, hs, -⟩ := GlobalTheory.SecAlg.existsUnique_sec V I hV B hB.smooth hp N hN (fun e => genSec (t e) (tg e))
    (fun e z J hJ => (sval_genSec _ _ _ z hJ).trans
      ((congrArg Units.val (compat e z J hJ)).trans (sval_genSec _ _ _ z hJ).symm))
  have := hB.proper
  have top : nonzeroLocus s = ⊤ := eq_top_of_closed_fibre B.hom _ fun x hx => by
    have hm : x ∈ Set.range (pullback.fst B.hom (thick V I 0)) := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, hx]
      exact closedPoint_mem_range 0
    obtain ⟨z, rfl⟩ := hm
    choose J hJ using fun ψ : ((Over.map (thick V I 0)).obj (thickObj V I 0 B)).left ⟶ B.left =>
      exists_chart hN (ψ z)
    refine (TwistZero.mem_nonzeroLocus_iff s (fstG I 0 B).left z hJ).2 ?_
    rw [hs 0 z J hJ, sval_genSec _ _ _ z hJ]
    exact Units.isUnit _
  refine triv_of_pull_id (TwistZero.triv_of_sec hN s fun y J hJ => ?_)
  exact (TwistZero.mem_nonzeroLocus_iff s (𝟙 _) y hJ).1 (by rw [top]; trivial)

end GlobalTheory.AbTriv
