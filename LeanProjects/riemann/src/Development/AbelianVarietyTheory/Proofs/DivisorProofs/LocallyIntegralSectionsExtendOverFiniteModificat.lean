import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfCompEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteModificationIntegralElementsRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtLIPreimageMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorizationThroughFiniteModificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreSectionsInjectiveFlatIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreimageOfLocalPreimagesInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAffineChartCoverOverModificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPulledBackPowerSectionOfLocalLiftsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumMulPulledBackFunctionsGenericFibreEqStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

private theorem secK_extend_locInt {X X' Y Z : Scheme.{0}} (L : LB X) (f : X' ⟶ X) (l : Y ⟶ X')
    (α : Y ⟶ X) (e : l ≫ f = α) {k : ℕ} (σ : SecK L f k) (s : SecK L α k) (j' : Fin 1 → L.ι)
    (hσ : (l.app (LB.wchart L (K := Fin 1) (fun _ => f) j')).hom (σ.f j') =
      (Y.presheaf.map (homOfLE (extLI_le_wchart L f l α e j')).op).hom (s.f j'))
    (p' : Z ⟶ Y) (z : Z) (hz : (p' ≫ l) z ∈ LB.wchart L (K := Fin 1) (fun _ => f) j') :
    gs (p' ≫ l) z (LB.wchart L (K := Fin 1) (fun _ => f) j') (σ.f j') =
      gs p' z (LB.wchart L (K := Fin 1) (fun _ => α) j') (s.f j') := by
  have hz' : p' z ∈ LB.wchart L (K := Fin 1) (fun _ => α) j' := extLI_le_wchart L f l α e j' hz
  unfold gs
  rw [dif_pos hz, dif_pos hz']
  calc _ = (p'.stalkMap z).hom (Y.presheaf.germ (l ⁻¹ᵁ LB.wchart L (K := Fin 1) (fun _ => f) j') (p' z) hz
          ((l.app (LB.wchart L (K := Fin 1) (fun _ => f) j')).hom (σ.f j'))) :=
        (Scheme.Hom.germ_stalkMap_apply p' _ z hz _).symm
    _ = (p'.stalkMap z).hom (Y.presheaf.germ (l ⁻¹ᵁ LB.wchart L (K := Fin 1) (fun _ => f) j') (p' z) hz
          ((Y.presheaf.map (homOfLE (extLI_le_wchart L f l α e j')).op).hom (s.f j'))) := by rw [hσ]
    _ = (p'.stalkMap z).hom (Y.presheaf.germ (LB.wchart L (K := Fin 1) (fun _ => α) j') (p' z) hz' (s.f j')) := by
        congr 1
        exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
    _ = _ := Scheme.Hom.germ_stalkMap_apply p' _ z hz' _

theorem extend_locInt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : IsPullback α t G.hom M.gp) (I : Type) [Finite I] (k : I → ℕ) (s : ∀ i, SecK L α (k i)), (∀ i, LocInt M G L α t hpb.w (s i)) → ∃ (M' : Modif R) (h : M'.S ⟶ M.S), IsFinite h ∧ M'.gp ≫ h = M.gp ∧ h ≫ M.π = M'.π ∧ ∀ i, ∃ σ : SecK L (pullback.fst G.hom h) (k i), Agree L σ (s i) := by
  intro R _ _ _ _ _ M G hsm hqc hgi L hL Y α t hpb I _ k s hs
  obtain ⟨n, j, W, U, hcov, hWj, hWU, hWaff, hUaff⟩ := GlobalTheory.T.exists_finite_affine_chart_cover_over_modification R M G hqc L hL
  have key : ∀ (i : I) (b : Fin n), ∃ (nn : ℕ) (c : Fin nn → Γ(G.left, W b))
      (bb : Fin nn → Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U b)),
      (∀ m, (M.gp.app (U b)).hom.IsIntegralElem (bb m)) ∧
      (Y.presheaf.map (homOfLE (locInt_le_chart L α (j b) (W b) (hWj b))).op).hom ((s i).f (fun _ => j b)) =
        ∑ m, (α.app (W b)).hom (c m) *
          (t.appLE (M.gp ⁻¹ᵁ U b) (α ⁻¹ᵁ W b) (locInt_le_gen G.hom α t M.gp hpb.w (W b) (U b) (hWU b))).hom (bb m) :=
    fun i b => hs i (j b) (W b) (U b) (hWj b) (hWU b) (hWaff b) (hUaff b)
  choose nn c bb hint heq using key
  let Ix := Σ (p : I × Fin n), Fin (nn p.1 p.2)
  let e : Ix ≃ Fin (Nat.card Ix) := Finite.equivFin Ix
  obtain ⟨M', h, hgp, hfin, hπ, hlift⟩ := GlobalTheory.T.exists_finiteModification_integral_elements_regular R M (Nat.card Ix) (fun q => U (e.symm q).1.2)
    (fun q => bb (e.symm q).1.1 (e.symm q).1.2 (e.symm q).2) (fun q => hUaff _) (fun q => hint _ _ _)
  have hlift' : ∀ x : Ix, ∃ cc : Γ(M'.S, h ⁻¹ᵁ U x.1.2),
      (M'.gp.appLE (h ⁻¹ᵁ U x.1.2) (M.gp ⁻¹ᵁ U x.1.2) (le_preimage_of_comp_eq M.gp M'.gp h hgp (U x.1.2))).hom cc =
        bb x.1.1 x.1.2 x.2 := by
    intro x
    have hx := hlift (e x)
    rw [Equiv.symm_apply_apply] at hx
    exact hx
  choose cc hcc using hlift'
  refine ⟨M', h, hfin, hgp, hπ, fun i => ?_⟩
  obtain ⟨l, hl1, hl2⟩ : ∃ l : Y ⟶ pullback G.hom h,
      l ≫ pullback.fst G.hom h = α ∧ l ≫ pullback.snd G.hom h = t ≫ M'.gp :=
    ⟨pullback.lift α (t ≫ M'.gp) (by rw [hpb.w, Category.assoc, hgp]), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  have hout : IsPullback (l ≫ pullback.fst G.hom h) t G.hom (M'.gp ≫ h) := by
    rw [hl1, hgp]; exact hpb
  have hpb' : IsPullback l t (pullback.snd G.hom h) M'.gp :=
    IsPullback.of_right hout hl2 (IsPullback.of_hasPullback G.hom h)
  haveI := hsm
  haveI : Flat G.hom := inferInstance
  have hflat : Flat (pullback.snd G.hom h) := inferInstance
  have hinj := GlobalTheory.T.genericFibre_sections_injective_flat_integral (FractionRing R) (pullback.snd G.hom h) M'.gp l t hpb' hflat M'.integral M'.dominant
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_pulledBackPowerSection_of_local_lifts L (pullback.fst G.hom h) l α hl1 (k i) hinj (s i) n j
    (fun b => pullback.fst G.hom h ⁻¹ᵁ W b) ((pullback.fst G.hom h).iSup_preimage_eq_top hcov)
    (fun b => extLI_preimage_mono _ (hWj b)) (fun b => by
      obtain ⟨y, hy⟩ := GlobalTheory.T.sum_mul_pulledBack_functions_genericFibre_eq G.hom h M.gp M'.gp hgp (pullback.fst G.hom h) (pullback.snd G.hom h)
        pullback.condition α t hpb.w l hl1 hl2 (W b) (U b) (hWU b) (nn i b) (c i b) (bb i b)
        (fun m => cc ⟨(i, b), m⟩) (fun m => hcc ⟨(i, b), m⟩)
      refine ⟨y, hy.trans ?_⟩
      rw [← heq i b]
      exact extLI_res_res _ _ _ _)
  refine ⟨σ, ?_⟩
  intro Z p p' hp z J hJ
  have hp2 : p ≫ pullback.snd G.hom h = p' ≫ t ≫ M'.gp := by
    have := GlobalTheory.T.factorization_through_finite_modification R M M' h hfin hgp Z (p ≫ pullback.snd G.hom h) (p' ≫ t) (by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, hp, Category.assoc, hpb.w, Category.assoc])
    rw [this, Category.assoc]
  have hpl : p = p' ≫ l := pullback.hom_ext (by rw [hp, Category.assoc, hl1]) (by rw [hp2, Category.assoc, hl2])
  subst hpl
  unfold sval
  simp only []
  rw [Category.assoc, hl1]
  have hJ' : ∀ ψ : Z ⟶ G.left, ψ z ∈ L.U (J ψ) := hJ
  have hz : (p' ≫ l) z ∈ LB.wchart L (K := Fin 1) (fun _ => pullback.fst G.hom h) (fun _ => J (p' ≫ α)) := by
    unfold LB.wchart
    simp only [TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    intro _
    convert hJ' (p' ≫ α) using 1
    rw [← hl1]
    simp
  exact secK_extend_locInt L (pullback.fst G.hom h) l α hl1 σ (s i) _ (hσ _) p' z hz

end GlobalTheory.Mum
