import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsLieCombOneIffComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLieBasisPullbackGeneric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyEvenBC

theorem keyOn_pullback : ∀ (A B K : Type) [CommRing A] [CommRing B] [CommRing K] (f : A →+* B) (h : B →+* K) (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (x : KeyIn K) (y : Fin x.P.g → (epsR A ⟶ G)), IsSemiAbelian G → IsLieBasis y → NzFib σ → KeyOn (h.comp f) x G L σ y → ∀ [IsCommMonObj ((Over.pullback (spMap f)).obj G)], ∃ (L' : RigLB ((Over.pullback (spMap f)).obj G)) (σ' : L'.L.Sec) (y' : Fin x.P.g → (epsR B ⟶ (Over.pullback (spMap f)).obj G)), LBIso (L.L.pull (pullback.fst G.hom (spMap f))) L'.L ∧ IsLieBasis y' ∧ NzFib σ' ∧ KeyOn h x ((Over.pullback (spMap f)).obj G) L' σ' y' := by
  intro A B K _ _ _ f h G _ _ L σ x y hG hy hσ hK _
  obtain ⟨φ, he, ψ, F, hφ, hψ, hrig, hsec, hF1, hF2, hFv⟩ := hK
  have hP := isGrpPullback_pullback G (spMap f)
  have sqφ : φ ≫ G.hom = (x.P.A.hom ≫ spMap h) ≫ spMap f := by
    rw [Category.assoc, ← spMap_comp]
    exact hφ.1.w
  obtain ⟨φ', hφ', hfst, hsnd⟩ : ∃ φ' : x.P.A.left ⟶ ((Over.pullback (spMap f)).obj G).left,
      IsGrpPullback x.P.A ((Over.pullback (spMap f)).obj G) (spMap h) φ' ∧ φ' ≫ pullback.fst G.hom (spMap f) = φ ∧
        φ' ≫ ((Over.pullback (spMap f)).obj G).hom = x.P.A.hom ≫ spMap h := by
    refine ⟨pullback.lift φ (x.P.A.hom ≫ spMap h) sqφ, ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    refine IsGrpPullback.cancel hP ?_ (pullback.lift_snd _ _ _)
    rw [pullback.lift_fst, ← spMap_comp]
    exact hφ
  subst hfst
  have hL := L.isLB
  have hL' : (L.L.pull (pullback.fst G.hom (spMap f))).IsLB := LB.isLB_pull hL _
  have heF : eSec ((Over.pullback (spMap f)).obj G) ≫ pullback.fst G.hom (spMap f) = spMap f ≫ eSec G :=
    PolBaseChange.eSec_comm hP
  let L' : RigLB ((Over.pullback (spMap f)).obj G) :=
    ⟨L.L.pull (pullback.fst G.hom (spMap f)), rigPullOf (G' := ((Over.pullback (spMap f)).obj G)) (pullback.fst G.hom (spMap f)) (spMap f) heF L.L L.rig, hL',
      Out.LBxP.isGen_pullAlong L.L (pullback.fst G.hom (spMap f)) (spMap f) (fun _ : PUnit => eSec G) (fun _ => 1)
        (fun _ => eSec ((Over.pullback (spMap f)).obj G)) (fun _ => heF) L.rig L.rigGen⟩
  have he' : eSec x.P.A ≫ φ' = spMap h ≫ eSec ((Over.pullback (spMap f)).obj G) := PolBaseChange.eSec_comm hφ'
  have pw := (isGen_iff (L := L.L) (F := pullback.fst G.hom (spMap f)) (idIso _)).1 (idIso_isGen hL')
  obtain ⟨σ', hσ'⟩ := sec_pull_down pw hL hL' σ
  have pψ := (isGen_iff ψ).1 hψ
  obtain ⟨w', T⟩ := exists_cancel hL (idIso (L.L.pull (pullback.fst G.hom (spMap f)))) ψ pw pψ hL' x.P.isLB
  have H : PMaps (idIso (L.L.pull (pullback.fst G.hom (spMap f)))) (K := PUnit)
      (fun _ => eSec ((Over.pullback (spMap f)).obj G)) (fun _ => eSec G) (fun _ => 1) L'.rig L.rig (spMap f) :=
    (maps_iff _ _ _ _ L'.rig L.rig (spMap f) L'.rig (rigPull_le (G' := ((Over.pullback (spMap f)).obj G)) (pullback.fst G.hom (spMap f)) (spMap f) heF L.L) (fun _ => rfl)).1 (idIso_maps L')
  have H'' : PMaps ψ (K := PUnit) (fun _ => eSec x.P.A) (fun _ => eSec G) (fun _ => 1) x.rig L.rig
      (spMap h ≫ spMap f) := by
    rw [← spMap_comp]
    exact (maps_iff ψ _ _ _ x.rig L.rig (spMap (h.comp f)) _ (rigPull_le (G' := x.P.A) (φ' ≫ pullback.fst G.hom (spMap f)) (spMap (h.comp f)) he L.L)
      (fun _ => rfl)).1 hrig
  have H' := T.pmaps_cancel hL (fun _ => he') H H''
  have hrig' : LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ' (spMap h) he' L'.L L'.rig) :=
    (maps_iff w' _ _ _ x.rig L'.rig (spMap h) _ (rigPull_le φ' (spMap h) he' L'.L) (fun _ => rfl)).2 H'

  have hsec' : ∀ (j : (L'.L.pull φ').ι) (i : x.P.L.ι) (hh : (L'.L.pull φ').U j ⊓ x.P.L.U i ≤ φ' ⁻¹ᵁ L'.L.U (j PUnit.unit)),
      (φ'.appLE _ _ hh).hom (σ'.f (j PUnit.unit)) =
        (show Γ(x.P.A.left, (L'.L.pull φ').U j ⊓ x.P.L.U i) from (w'.s (j, i)).val) * resG _ inf_le_right (x.th.f i) := by
    refine GlobalTheory.KeyPow.appLE_eq_of_stalk w' σ' x.th ?_
    intro z J k hJ hk
    have ha : (pullback.fst G.hom (spMap f)) (φ' z) ∈ L.L.U (J PUnit.unit) := mem_pull.1 hJ
    have hW : (𝟙 x.P.A.left) z ∈ (L.L.pull (φ' ≫ pullback.fst G.hom (spMap f))).U (fun _ => J PUnit.unit) ⊓ x.P.L.U k :=
      ⟨mem_pull.2 ha, hk⟩
    have s2 : gs (𝟙 _ ≫ φ' ≫ pullback.fst G.hom (spMap f)) z _ (σ.f (J PUnit.unit)) =
        (gw ψ (𝟙 _) z (J PUnit.unit) k).val * gs (𝟙 _) z _ (x.th.f k) := by
      have e := congrArg (gs (𝟙 _) z ((L.L.pull (φ' ≫ pullback.fst G.hom (spMap f))).U (fun _ => J PUnit.unit) ⊓ x.P.L.U k))
        (hsec (fun _ => J PUnit.unit) k (fun x hx => mem_pull.1 hx.1))
      exact (gs_appLE (φ' ≫ pullback.fst G.hom (spMap f)) _ _ _ (𝟙 _) z hW _).symm.trans (e.trans ((gs_mul _ z _ hW _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ z _ hW _) (gs_res _ z _ hW _))))
    have e1 := hσ' _ (𝟙 _ ≫ φ') z (J PUnit.unit) J ha hJ
    have e3 := T _ (𝟙 _) z (J PUnit.unit) J k ha hJ hk
    rw [Category.assoc] at e1
    rw [e1, e3, Units.val_mul, _root_.mul_assoc] at s2
    exact (Units.mul_right_inj _).1 s2
  have hnz : NzFib (L := L'.L) σ' := by
    intro s
    obtain ⟨z, hz, hz'⟩ := hσ (spMap f s)
    obtain ⟨y0, rfl, hy0⟩ := Scheme.exists_preimage_of_isPullback hP.1 z s hz
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    refine ⟨y0, hy0, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
    have u₁ : IsUnit (gs (pullback.fst G.hom (spMap f)) y0 _ (σ.f k)) := by
      rw [gs_stalkMap _ y0 _ hk]; exact u.map _
    have e := hσ' _ (𝟙 _) y0 k (fun _ => k) hk (mem_pull.2 hk)
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)

  have := hG.smooth
  have sq : ∀ i, (spMap (Chart.dualMapR f) ≫ (y i).left) ≫ G.hom = (epsR B).hom ≫ spMap f := fun i => by
    rw [Category.assoc, Over.w]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let y' : Fin x.P.g → (epsR B ⟶ ((Over.pullback (spMap f)).obj G)) := fun i =>
    Over.homMk (hP.1.lift _ _ (sq i)) (hP.1.lift_snd _ _ _)
  have hy' : ∀ i, (y' i).left ≫ pullback.fst G.hom (spMap f) = spMap (Chart.dualMapR f) ≫ (y i).left :=
    fun i => hP.1.lift_fst _ _ _
  have hadd : ∀ (a b : B) (w : Chart.sp (DualNumber B) ⟶ ((Over.pullback (spMap f)).obj G)), Chart.IsTan w →
      Chart.spMap (Chart.scaleD (a + b)) ≫ w = (Chart.spMap (Chart.scaleD a) ≫ w) * (Chart.spMap (Chart.scaleD b) ≫ w) :=
    fun a b w hw => GlobalTheory.LieMultiple.scale_add ((Chart.isTan_iff w).1 hw) a b
  have hT : ∀ i, IsTangent (y' i) := fun i => by
    refine hP.1.hom_ext ?_ ?_
    · rw [Category.assoc, hy', show η[((Over.pullback (spMap f)).obj G)].left = eSec ((Over.pullback (spMap f)).obj G) from rfl, heF, ← Category.assoc]
      have e0 := hy.1 i
      rw [IsTangent] at e0
      rw [show eSec G = η[G].left from rfl, ← e0, ← Category.assoc]
      congr 1
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      refine RingHom.ext fun a => ?_
      simp [Chart.dualMapR]
    · rw [Category.assoc, Over.w (y' i), Over.w η[((Over.pullback (spMap f)).obj G)]]
      show Spec.map _ ≫ Spec.map _ = 𝟙 _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      convert Spec.map_id (CommRingCat.of B)
      ext a; simp
  have hLie : IsLieBasis y' := Chart.frameLieBCR G hy f hP hadd hT hy'

  have hF' : F = (Chart.dualMapR h).comp (Chart.dualMapR f) := by
    refine GlobalTheory.KeyExtLie.dnRingHom_ext (fun a => ?_) ?_
    · have e1 := hF1 a
      simp only [TrivSqZeroExt.algebraMap_eq_inl] at e1
      rw [e1]
      simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
    · rw [hF2]
      ext <;> simp [Chart.dualMapR]
  have hv' : ∀ i, (x.v i).left ≫ φ' = spMap (Chart.dualMapR h) ≫ (y' i).left := fun i => by
    refine hP.1.hom_ext ?_ ?_
    · rw [Category.assoc, hFv i, Category.assoc, hy', ← Category.assoc, hF', spMap_comp]
    · rw [Category.assoc, hsnd, ← Category.assoc, Over.w (x.v i), Category.assoc, Over.w (y' i)]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨L', σ', y', ⟨idIso _, idIso_isGen hL'⟩, hLie, hnz, φ', he', w', Chart.dualMapR h, hφ',
    (isGen_iff w').2 (T.pgen_cancel hL pw pψ), hrig', hsec', fun a => ?_, ?_, hv'⟩
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

end GlobalTheory.KeyEvenBC
