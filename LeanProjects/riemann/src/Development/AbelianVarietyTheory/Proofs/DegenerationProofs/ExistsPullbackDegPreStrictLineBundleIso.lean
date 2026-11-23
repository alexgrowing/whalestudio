import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrict
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open TopologicalSpace
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData GlobalTheory.DegPull

namespace GlobalTheory.StrictPull

theorem exists_isPullDeg_of_strict (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    (φ : R →+* R') (D : DegPre R) (W : (Spec (CommRingCat.of R)).Opens) (hW : Nonempty (PsiOn D W))
    (hη : (specOf φ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ W)
    (P' : PolAV (Spec (CommRingCat.of R'))) (F : P'.A.left ⟶ D.P.A.left)
    (gp : IsGrpPullback P'.A D.P.A (specOf φ) F) (w : LB.Iso P'.L (D.P.L.pull F)) (hw : w.IsGen) (hs : Strict w) :
    ∃ (D' : DegPre R') (hD : IsPullDeg φ D D'), D'.P.g = P'.g ∧ Strict hD.w := by
  obtain ⟨ψW⟩ := hW
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf φ))
  subst he
  have hF := gp.1
  have hw' := (isGen_iff w).1 hw
  have hE : eSec P'.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = specOf φ ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  obtain ⟨rig, hrig, Hrig⟩ := exists_pmaps hw' D.P.isLB P'.isLB (K := PUnit) (φ' := fun _ => eSec P'.A)
    (φ := fun _ => eSec D.P.A) (ε := fun _ => 1) (specOf φ) (fun _ => hE) D.rig D.rig_gen
  obtain ⟨cub⟩ := nonempty_cubical_pull gp D.cub ⟨P'.L, rig, P'.isLB, hrig⟩ hw'
  obtain ⟨sym, hsym, hsr⟩ := exists_sym_pull gp D.P.isLB P'.isLB hw' D.sym D.sym_gen D.sym_rig
  obtain ⟨c, hc⟩ : ∃ c : D.X → (𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ P'.A), ∀ x,
      (c x).left ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = specOf φ ≫ (D.c x).left :=
    ⟨fun x => Over.homMk (hF.lift (specOf φ ≫ (D.c x).left) (𝟙 _) (by
      rw [Category.assoc, Over.w, Category.id_comp]; exact Category.comp_id _)) (hF.lift_snd _ _ _),
      fun x => hF.lift_fst _ _ _⟩
  have cadd : ∀ a b, c (a + b) = padd P'.A (c a) (c b) := fun a b => by
    refine Over.OverMorphism.ext (hF.hom_ext ?_ (by rw [Over.w, Over.w]))
    have u : (toUnit (Over.mk ((𝟙_ (Over (Spec (CommRingCat.of R')))).hom ≫ specOf φ))).left = specOf φ :=
      Category.id_comp _
    have m := gp.2 _ (c a) (c b) (toUnit _ ≫ D.c a) (toUnit _ ≫ D.c b)
      (by rw [hc, Over.comp_left, u]) (by rw [hc, Over.comp_left, u])
    rw [← MonObj.comp_mul, Over.comp_left, u] at m
    rw [hc, D.c_add]
    exact m
  obtain ⟨g, hg⟩ : ∃ g : (TK R').left ⟶ (TW W).left, g ≫ W.ι = jK R' ≫ specOf φ :=
    ⟨IsOpenImmersion.lift W.ι (jK R' ≫ specOf φ) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hy : jK R' y = genericPoint (Spec (CommRingCat.of R')) := by
        rw [genericPoint_eq_bot_of_affine]
        apply PrimeSpectrum.ext
        show Ideal.comap (algebraMap R' (FractionRing R')) (PrimeSpectrum.asIdeal y) = ⊥
        rw [@Ideal.eq_bot_of_prime _ _ (PrimeSpectrum.asIdeal y) (PrimeSpectrum.isPrime y)]
        exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R' (FractionRing R'))
      show specOf φ (jK R' y) ∈ W
      rw [hy]; exact hη), IsOpenImmersion.lift_fac _ _ _⟩
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c x).left =
      ptK (c x) ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) := fun x => by
    show g ≫ W.ι ≫ (D.c x).left = (jK R' ≫ (c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => ptK (c x) ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi x) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen x) g)
  choose psi hpsi vpsi using fun x => exists_down_val hw' D.P.isLB P'.isLB (K := PUnit)
    (φ' := fun _ => ptK (c x)) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  let D' : DegPre R' :=
    { P := P', rig := rig, rig_gen := hrig, cub := cub, sym := sym, sym_gen := hsym, sym_rig := hsr, X := D.X,
      c := c, c_add := cadd, psi := psi, psi_gen := hpsi }
  refine ⟨D',
    ⟨e, e_hom, w, hw, hE, ?_, AddEquiv.refl _, hc, W, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl, hs⟩
  · exact (maps_iff w _ (fun _ => eSec D.P.A) _ rig D.rig (specOf φ) _
      (rigPull_le (G' := P'.A) (G := D.P.A) _ (specOf φ) hE D.P.L) (fun _ => rfl)).2 Hrig
  · refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))

def polPull {S S' : Scheme.{0}} (P : PolAV S) (f : S' ⟶ S) : PolAV S' where
  A := (Over.pullback f).obj P.A
  isAb := TLinPf.isAb_pullback f P.A P.isAb
  g := P.g
  smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    (isGrpPullback_pullback P.A f).1 P.smoothDim
  L := P.L.pull (pullback.fst P.A.hom f)
  isLB := pull_isLB P.isLB _
  rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback P.A f) P.rigid
  sym := PolBaseChange.sym_pull (isGrpPullback_pullback P.A f) P.sym
  ample :=
    haveI := P.isAb.proper
    AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample (IsPullback.of_hasPullback P.A.hom f)
  ktriv := by
    obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (pull_isLB P.isLB (pullback.fst P.A.hom f))
    exact kTriv_pull (isGrpPullback_pullback P.A f) P.isLB (pull_isLB P.isLB _) ((isGen_iff w).1 hw) P.ktriv

theorem exists_isPullDeg_strict : Laws → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (W : (Spec (CommRingCat.of R)).Opens), Nonempty (PsiOn D W) → (specOf φ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ W → ∃ (D' : DegPre R') (hD : IsPullDeg φ D D'), D'.P.g = D.P.g ∧ Strict hD.w := by
  intro _ R R' _ _ _ _ φ D W hW hη
  obtain ⟨w, hw, hs⟩ := exists_strict D.P.isLB (pullback.fst D.P.A.hom (specOf φ))
  exact exists_isPullDeg_of_strict R R' φ D W hW hη (polPull D.P (specOf φ)) (pullback.fst D.P.A.hom (specOf φ))
    (isGrpPullback_pullback D.P.A (specOf φ)) w hw hs

end GlobalTheory.StrictPull
