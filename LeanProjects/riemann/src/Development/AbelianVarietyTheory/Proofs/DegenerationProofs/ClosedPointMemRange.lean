import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSchemeCubicalBundleExistsAndMaps
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqTopOfClosedFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.TowerAlg

theorem closedPoint_mem_range {R : Type} [CommRing R] [IsLocalRing R] {I : Ideal R} (hI : I ≠ ⊤) (e : ℕ) :
    IsLocalRing.closedPoint R ∈ Set.range (thick R I e) := by
  have h := range_comap_of_surjective _ _ (Ideal.Quotient.mk_surjective (I := I ^ (e + 1)))
  refine h.ge ?_
  rw [Ideal.mk_ker]
  exact (Ideal.pow_le_self (Nat.succ_ne_zero e)).trans (IsLocalRing.le_maximalIdeal hI)

theorem triv_of_forall_thick (hG : GlobalFnsSt) (hS : SecAlgSt) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    {I : Ideal V} (hI : I ≠ ⊤) (hV : IsAdicComplete I V) (B : Over (Spec (CommRingCat.of V))) [GrpObj B]
    (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) (N : LB B.left) (hN : N.IsLB)
    (ht : ∀ e, Triv (N.pull (fstG I e B).left)) : Triv N := by
  let o : Spec (CommRingCat.of V) ⟶ B.left := (η[B]).left
  have ho : o ≫ B.hom = 𝟙 _ := Over.w η[B]
  obtain ⟨c, hc⟩ := DVR.exists_gen_of_local N hN (K := PUnit) (fun _ => o) (fun _ => 1)
  have pb : ∀ e, IsPullback (fstG I e B).left (thickObj V I e B).hom B.hom (thick V I e) :=
    fun e => IsPullback.of_hasPullback B.hom (thick V I e)
  choose t tg tv using fun e => AbTriv.exists_normalised hN ho c hc (pb e) (ht e)
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
  obtain ⟨s, hs, -⟩ := hS V I hV B hB.smooth hp N hN (fun e => genSec (t e) (tg e))
    (fun e z J hJ => (sval_genSec _ _ _ z hJ).trans
      ((congrArg Units.val (compat e z J hJ)).trans (sval_genSec _ _ _ z hJ).symm))
  have := hB.proper
  have top : nonzeroLocus s = ⊤ := AbTriv.eq_top_of_closed_fibre B.hom _ fun x hx => by
    have hm : x ∈ Set.range (pullback.fst B.hom (thick V I 0)) := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, hx]
      exact closedPoint_mem_range hI 0
    obtain ⟨z, rfl⟩ := hm
    choose J hJ using fun ψ : ((Over.map (thick V I 0)).obj (thickObj V I 0 B)).left ⟶ B.left =>
      exists_chart hN (ψ z)
    refine (TwistZero.mem_nonzeroLocus_iff s (fstG I 0 B).left z hJ).2 ?_
    rw [hs 0 z J hJ, sval_genSec _ _ _ z hJ]
    exact Units.isUnit _
  refine AbTriv.triv_of_pull_id (TwistZero.triv_of_sec hN s fun y J hJ => ?_)
  exact (TwistZero.mem_nonzeroLocus_iff s (𝟙 _) y hJ).1 (by rw [top]; trivial)

theorem triv_pull_of_gen {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    (hw : LBIso L' (L.pull F)) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {ε : K → ℤ}
    (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) (r : Z ⟶ Y') (π : Z ⟶ Y)
    (hc : ∀ k, (r ≫ φ' k) ≫ F = π ≫ φ k) : Triv ((LB.LinComb L φ ε).pull π) := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨t, ht, -⟩ := exists_up ((isGen_iff w).1 hw) hL hL' _ (DVR.pullGen_isGen _ _ _ _ ha r)
  refine (KerPow.pull_iff φ ε π).2 ?_
  rw [← (funext hc : (fun k => (r ≫ φ' k) ≫ F) = fun k => π ≫ φ k)]
  exact ⟨t, ht⟩

section Level
variable {S S' Z : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']
  {f : S' ⟶ S} {F : B'.left ⟶ B.left}

omit [IsCommMonObj B] [IsCommMonObj B'] in

theorem toBase_mul (h : IsGrpPullback B' B f F) (T : Over S') (x y : T ⟶ B') :
    toBase h.1.w (x * y) = toBase h.1.w x * toBase h.1.w y :=
  Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm

theorem triv_theta (h : IsGrpPullback B' B f F) (M' : CP B') {L : LB B.left} (hL : L.IsLB)
    (hw : LBIso M'.L.L (L.pull F)) (π : Z ⟶ (G3 B).left) (z : Z ⟶ S') (hz : π ≫ (G3 B).hom = z ≫ f) :
    Triv ((Theta B L).pull π) := by
  let ρ : Over.mk ((Over.mk z).hom ≫ f) ⟶ G3 B := Over.homMk π hz
  let x : Fin 3 → (Over.mk z ⟶ B') := fun i =>
    Over.homMk (h.1.lift (ρ ≫ x3 B i).left z (Over.w (ρ ≫ x3 B i))) (h.1.lift_snd _ _ _)
  let β := toBaseHom (toBase_mul h) (Over.mk z)
  have hx : ∀ i, β (x i) = ρ ≫ x3 B i := fun i => Over.OverMorphism.ext (h.1.lift_fst _ _ _)
  let r : Over.mk z ⟶ G3 B' := lift (x 0) (lift (x 1) (x 2))
  have hr : ∀ i, r ≫ x3 B' i = x i := fun i => by fin_cases i <;> simp [r, x3]
  refine triv_pull_of_gen hL M'.L.isLB hw (φ := thφ B (x3 B)) (φ' := thφ B' (x3 B')) (ε := thε) M'.c.t M'.c.isGen
    r.left π fun I => ?_
  have e : β (r ≫ psum B' (x3 B') I.down) = ρ ≫ psum B (x3 B) I.down :=
    (psum_hom (β.comp (preHom r)) (x3 B') I.down).trans ((congrArg (fun q => psum B q I.down) (funext fun i =>
      (congrArg β (hr i)).trans (hx i))).trans (psum_hom (preHom ρ) (x3 B) I.down).symm)
  exact congrArg (fun q => q.left) e

theorem triv_sym (h : IsGrpPullback B' B f F) (M' : CP B') {L : LB B.left} (hL : L.IsLB)
    (hw : LBIso M'.L.L (L.pull F)) (π : Z ⟶ B.left) (z : Z ⟶ S') (hz : π ≫ B.hom = z ≫ f) :
    Triv ((LB.LinComb L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]).pull π) := by
  let x : Over.mk z ⟶ B' := Over.homMk (h.1.lift π z hz) (h.1.lift_snd _ _ _)
  have hx : x.left ≫ F = π := h.1.lift_fst _ _ _
  refine triv_pull_of_gen hL M'.L.isLB hw M'.sym M'.sym_gen x.left π fun k => ?_
  fin_cases k
  · exact (inv_left_comp (toBase_mul h) x).trans (congrArg (· ≫ _) hx)
  · exact ((congrArg (· ≫ F) (Category.comp_id _)).trans hx).trans (Category.comp_id _).symm

end Level

section Pack
variable (hG : GlobalFnsSt) (hS : SecAlgSt) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
  (hI : I ≠ ⊤) (hc : IsAdicComplete I R) {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
  [∀ e, GrpObj (Y e)] [∀ e, IsCommMonObj (Y e)] (N : ∀ e, CP (Y e)) {B : Over (Spec (CommRingCat.of R))} [GrpObj B]
  [IsCommMonObj B] (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) {b : ∀ e, (Y e).left ⟶ B.left}
  (hg : ∀ e, IsGrpPullback (Y e) B (thick R I e) (b e)) {M : LB B.left} (hM : M.IsLB)
  (hiso : ∀ e, LBIso (N e).L.L (M.pull (b e)))
include hG hS hI hc hB hp hg hM hiso

theorem triv_theta_alg : Triv (Theta B M) :=
  triv_of_forall_thick hG hS hI hc (G3 B)
    (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hB (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hB hB))
    (isProjBy_tensor R _ _ hp (isProjBy_tensor R _ _ hp hp)) (Theta B M) (LB.isLB_linComb hM _ _) fun e =>
      triv_theta (hg e) (N e) hM (hiso e) (fstG I e (G3 B)).left (pullback.snd (G3 B).hom (thick R I e))
        (pullback.condition (f := (G3 B).hom) (g := thick R I e))

theorem triv_sym_alg : Triv (LB.LinComb M (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]) :=
  triv_of_forall_thick hG hS hI hc B hB hp _ (LB.isLB_linComb hM _ _) fun e =>
    triv_sym (hg e) (N e) hM (hiso e) (fstG I e B).left (pullback.snd B.hom (thick R I e))
      (pullback.condition (f := B.hom) (g := thick R I e))

theorem exists_cp_alg (hY : ∀ e, IsAbelianScheme (Y e)) :
    ∃ Q : CP B, Q.L.L = M ∧ ∀ e, IsCPPullback (N e) Q (thick R I e) (b e) := by
  obtain ⟨r, hr⟩ := DVR.exists_gen_of_local M hM (K := PUnit) (fun _ => eSec B) (fun _ => 1)
  obtain ⟨Q, hQ⟩ := AbPackage.exists_cp hG hB ⟨M, r, hM, hr⟩ (triv_theta_alg hG hS hI hc N hB hp hg hM hiso)
    (triv_sym_alg hG hS hI hc N hB hp hg hM hiso)
  have e₀ : Q.L.L = M := congrArg (fun q => q.L) hQ
  refine ⟨Q, e₀, fun e => ⟨hg e, ?_⟩⟩
  obtain ⟨w, hw⟩ : LBIso (N e).L.L (Q.L.L.pull (b e)) := by rw [e₀]; exact hiso e
  exact AbPackage.exists_isCPMap_of_iso hG (hY e) Q (N e) (toBase_mul (hg e)) w hw

end Pack

end GlobalTheory.TowerAlg
end
