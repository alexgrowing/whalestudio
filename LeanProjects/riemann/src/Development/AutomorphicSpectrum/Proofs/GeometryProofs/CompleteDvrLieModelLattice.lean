import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRingStatement

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
private theorem exists_unitary_diagonal_of_isHermitian {X : Scheme.{0}} (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X)
    (c : centre (FinRd.Roots.gen T zV) ⤳ centre zV) :
    X.presheaf.stalkSpecializes c ≫ Scheme.stalkClosedPointTo (FinRd.Roots.gen T zV) =
      Scheme.stalkClosedPointTo zV ≫ CommRingCat.ofHom (algebraMap T.V T.Fr) := by
  have c' := IsLocalRing.specializes_closedPoint
    ((Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) (IsLocalRing.closedPoint T.Fr))
  have e2 := Scheme.stalkClosedPointTo_comp (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) zV
  have e3 := Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom (algebraMap T.V T.Fr))
  have e4 := ΓSpecIso_hom_stalkClosedPointIso_inv (CommRingCat.of T.V)
  have e4' : (stalkClosedPointIso (CommRingCat.of T.V)).inv =
      (Scheme.ΓSpecIso (CommRingCat.of T.V)).inv ≫
        (Spec (CommRingCat.of T.V)).presheaf.germ ⊤ (IsLocalRing.closedPoint _) trivial := by
    rw [← e4, Iso.inv_hom_id_assoc]
  have e6 := TopCat.Presheaf.germ_stalkSpecializes (Spec (CommRingCat.of T.V)).presheaf
    (U := ⊤) (y := IsLocalRing.closedPoint _) trivial c'
  have e5 : (Spec (CommRingCat.of T.V)).presheaf.stalkSpecializes c' ≫
      Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) =
      (stalkClosedPointIso (CommRingCat.of T.V)).hom ≫ CommRingCat.ofHom (algebraMap T.V T.Fr) := by
    rw [← Iso.inv_comp_eq, e4', Category.assoc]
    erw [reassoc_of% e6]
    erw [e3]
    rw [Iso.inv_hom_id_assoc]
  change X.presheaf.stalkSpecializes c ≫ Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ zV) = _
  rw [e2]
  erw [Scheme.Hom.stalkSpecializes_stalkMap_assoc zV _ _ c']
  rw [e5, Scheme.stalkClosedPointTo, Category.assoc]

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.complete_dvr_lie_model_lattice : ∀ (X : AlgebraicGeometry.Scheme.{0}) (G : CategoryTheory.Over X) [CategoryTheory.GrpObj G] [CategoryTheory.IsCommMonObj G] (Ω : Type) [Field Ω] (ξ : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X) (L₀ : Type) [AddCommGroup L₀] [Module Ω L₀] (M : LieModel G ξ L₀) (T : CDVR) (zV : AlgebraicGeometry.Spec (CommRingCat.of T.V) ⟶ X) (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel G (FinRd.Roots.gen T zV) EC) (A : Subring Ω) (evT : A →+* T.Fr), IsCptGen ξ → AlgebraicGeometry.Smooth G.hom → ∀ (h : genPt ξ ⤳ centre zV), genPt ξ ⤳ centre (FinRd.Roots.gen T zV) → FinRd.Roots.ReadsPt ξ A T evT zV → ∀ (L : Lat ξ L₀) (r : ℕ) (b e : Fin r → L₀) (Tm : Matrix (Fin r) (Fin r) Ω) (w : Fin r → EC) (hT : ∀ i j, Tm i j ∈ A), L.IsFrameAt b ⟨centre zV, h⟩ → (∀ i, b i = ∑ j, Tm i j • e j) → (∀ j, M.ValAt (FinRd.Roots.gen T zV) (e j) (MC.pt (w j))) → M.fibAt L zV MC = Submodule.span T.V (Set.range fun i => ∑ j, evT ⟨Tm i j, hT i j⟩ • w j) := by
  intro X G _ _ Ω _ ξ L₀ _ _ M T zV EC _ _ _ _ MC A evT hX _ h hz hR L r b e Tm w hT hF hb hw
  obtain ⟨-, hF2⟩ := hF
  have c : centre (FinRd.Roots.gen T zV) ⤳ centre zV :=
    zV.base.hom.map_specializes (IsLocalRing.specializes_closedPoint _)
  have hK : ∀ s, (Scheme.stalkClosedPointTo (FinRd.Roots.gen T zV)).hom
      (ConcreteCategory.hom (X.presheaf.stalkSpecializes c) s) =
      algebraMap T.V T.Fr ((Scheme.stalkClosedPointTo zV).hom s) := by
    intro s
    have := DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (exists_unitary_diagonal_of_isHermitian T zV c)) s
    first
      | exact this
      | simpa only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] using this
  have hsc : ∀ {x : L₀} {y : EC}, M.ValAt (FinRd.Roots.gen T zV) x (MC.pt y) →
      ∀ s : X.presheaf.stalk (centre (FinRd.Roots.gen T zV)),
        M.ValAt (FinRd.Roots.gen T zV) (genMap ξ ⟨centre (FinRd.Roots.gen T zV), hz⟩ s • x)
          (MC.pt ((Scheme.stalkClosedPointTo (FinRd.Roots.gen T zV)).hom s • y)) := by
    intro x y hxy s
    have := LieModel.ValAt.smul hxy hz s
    rwa [← LieModel.pt_smul] at this
  have hzero : ∀ {x : L₀} {y : EC}, M.ValAt (FinRd.Roots.gen T zV) x (MC.pt y) →
      M.ValAt (FinRd.Roots.gen T zV) 0 (MC.pt 0) := by
    intro x y hxy
    have := hsc hxy 0
    rw [map_zero, zero_smul] at this
    erw [map_zero, zero_smul] at this
    exact this
  have hsum : ∀ (s : Finset (Fin r)) (f : Fin r → L₀) (g : Fin r → EC),
      M.ValAt (FinRd.Roots.gen T zV) 0 (MC.pt 0) →
      (∀ j ∈ s, M.ValAt (FinRd.Roots.gen T zV) (f j) (MC.pt (g j))) →
        M.ValAt (FinRd.Roots.gen T zV) (∑ j ∈ s, f j) (MC.pt (∑ j ∈ s, g j)) := by
    intro s f g h0 hf
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, MC.add]
      exact LieModel.ValAt.add (hf a (Finset.mem_insert_self a s))
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
  have hA : ∀ (a : A) (j : Fin r),
      M.ValAt (FinRd.Roots.gen T zV) ((a : Ω) • e j) (MC.pt (evT a • w j)) := by
    intro a j
    obtain ⟨h1, s, hs1, hs2⟩ := hR a
    have := hsc (hw j) s
    rw [hs1, hs2] at this
    exact this
  have hv : ∀ i, M.ValAt (FinRd.Roots.gen T zV) (b i)
      (MC.pt (∑ j, evT ⟨Tm i j, hT i j⟩ • w j)) := by
    intro i
    rw [hb i]
    exact hsum _ _ _ (hzero (hw i)) (fun j _ => hA ⟨Tm i j, hT i j⟩ j)
  unfold LieModel.fibAt
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro w' ⟨h', x, hx, hxv⟩
    have hx' : x ∈ Submodule.span (regAt ξ ⟨centre zV, h⟩) (Set.range b) := by
      rw [← hF2]
      exact hx
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hx'
    choose s hs using fun i => RingHom.mem_range.mp (cf i).2
    have key : M.ValAt (FinRd.Roots.gen T zV) x
        (MC.pt (∑ i, algebraMap T.V T.Fr ((Scheme.stalkClosedPointTo zV).hom (s i)) •
          ∑ j, evT ⟨Tm i j, hT i j⟩ • w j)) := by
      rw [← hcf]
      refine hsum _ _ _ (hzero hxv) fun i _ => ?_
      have := hsc (hv i) (ConcreteCategory.hom (X.presheaf.stalkSpecializes c) (s i))
      rw [LieTangent.genMap_specializes ⟨centre zV, h⟩ hz c, hK, hs i] at this
      rw [Subring.smul_def]
      exact this
    have hw' := MC.inj (LieModel.ValAt.unique hX hxv key)
    rw [hw']
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨h, b i, ?_, hv i⟩
    rw [hF2]
    exact Submodule.subset_span ⟨i, rfl⟩
