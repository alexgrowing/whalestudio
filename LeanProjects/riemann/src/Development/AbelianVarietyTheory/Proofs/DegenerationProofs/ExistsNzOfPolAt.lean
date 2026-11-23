import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecUnitClosedFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

namespace GlobalTheory.Ex.OneGen

open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic in

theorem exists_sec_pull_locus {X Y : Scheme.{0}} {L : LB X} (s : LB.Sec L) (φ : Y ⟶ X) :
    ∃ s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)),
      nonzeroLocus s' = φ ⁻¹ᵁ nonzeroLocus s := by
  have l : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => φ) j ≤ φ ⁻¹ᵁ L.U (j 0) :=
    fun j => LB.wchart_le L _ j 0
  have v : ∀ (j : Fin 1 → L.ι) (z : Y), z ∈ LB.wchart L (fun _ : Fin 1 => φ) j →
      gs (𝟙 Y) z _ ((Y.presheaf.map (homOfLE (l j)).op).hom ((φ.app _).hom (s.f (j 0)))) =
        gs (𝟙 Y ≫ φ) z (L.U (j 0)) (s.f (j 0)) := fun j z hj =>
    (gs_res _ z _ hj _).trans (gs_pull _ φ z _ (l j hj) _)
  let s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)) :=
    { f := fun j => (Y.presheaf.map (homOfLE (l j)).op).hom ((φ.app _).hom (s.f (j 0)))
      compat := fun j j' => fn_ext fun z hz => by
        have hm : (𝟙 Y ≫ φ) z ∈ L.U (j 0) ⊓ L.U (j' 0) := ⟨l j hz.1, l j' hz.2⟩
        have g : (trF (L := L) (fun _ : Fin 1 => φ) (fun _ => 1) (𝟙 Y) z j j').val =
            gs (𝟙 Y ≫ φ) z (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)).val := by
          refine Eq.trans ?_ (gs_unit _ z _ hm _).symm
          exact congrArg Units.val ((Fin.prod_univ_one _).trans (zpow_one _))
        refine ((gs_res (𝟙 Y) z _ hz _).trans (v j z hz.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) z _ hz _ _).trans
          (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) z _ hz _).trans
            ((congrArg Units.val (gm_linComb L _ _ (𝟙 Y) z j j' hz.1 hz.2)).trans g))
              ((gs_res (𝟙 Y) z _ hz _).trans (v j' z hz.2)))).symm)
        exact (gs_res _ z _ hm _).symm.trans ((congrArg (gs _ z _) (s.compat (j 0) (j' 0))).trans
          ((gs_mul _ z _ hm _ _).trans (congrArg _ (gs_res _ z _ hm _)))) }
  have b : ∀ (j : Fin 1 → L.ι) (y : Y), y ∈ Y.basicOpen (s'.f j) ↔
      y ∈ LB.wchart L (fun _ : Fin 1 => φ) j ∧ φ y ∈ X.basicOpen (s.f (j 0)) := fun j y => by
    change y ∈ Y.basicOpen ((Y.presheaf.map (homOfLE (l j)).op).hom ((φ.app _).hom (s.f (j 0)))) ↔ _
    rw [Scheme.basicOpen_res]
    exact and_congr_right fun _ => (SetLike.ext_iff.1 (Scheme.preimage_basicOpen φ (s.f (j 0))) y).symm
  refine ⟨s', SetLike.ext fun y => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j 0, ((b j y).1 hj).2⟩
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show φ y ∈ nonzeroLocus s from h)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, (b _ y).2
      ⟨Set.mem_iInter.2 fun _ => X.basicOpen_le _ hi, hi⟩⟩

theorem isUnit_sval_iff {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    IsUnit (sval s r z J) ↔ r z ∈ nonzeroLocus s := by
  have key : ∀ (U : Y.Opens) (_ : r z ∈ U) (f : Γ(Y, U)), IsUnit (gs r z U f) ↔ IsUnit (gs (𝟙 Y) (r z) U f) :=
    fun U h f => by rw [gs_stalkMap r z U h, isUnit_map_iff]
  refine ⟨fun h => (mem_nonzeroLocus s _).2 ⟨_, hJ.mem φ r, (key _ (hJ.mem φ r) _).1 h⟩, fun h => ?_⟩
  obtain ⟨j, hj, hu⟩ := (mem_nonzeroLocus s _).1 h
  rw [sval, sec_trans s r z (hJ.mem φ r) hj]
  exact (Units.isUnit _).mul ((key _ hj _).2 hu)

theorem nz_pullS {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) {T : Over S}
    (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)) (hσ : ∀ y : T.left, ∃ g, (fst T G).left g = y ∧ g ∈ nonzeroLocus σ)
    {V : Type} [CommRing V] [IsLocalRing V] (χ : Sp V ⟶ S) (h : Over.mk χ ⟶ T) :
    NZ G L χ (VVRank.pullS G _ h σ) := by
  obtain ⟨g, hg, hn⟩ := hσ (h.left (closedPoint V))
  have P : IsPullback (h ▷ G).left (fst (Over.mk χ) G).left (fst T G).left h.left := by
    refine IsPullback.of_right (h₁₂ := (snd T G).left) (v₁₃ := G.hom) (h₂₂ := T.hom) ?_ ?_
      (IsPullback.of_hasPullback T.hom G.hom).flip
    · rw [VVRank.whisker_snd_left, Over.w h]
      exact (IsPullback.of_hasPullback χ G.hom).flip
    · rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
  obtain ⟨g', h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback P g (closedPoint V) hg
  refine ⟨g', h₂, ?_⟩
  obtain ⟨J, hJ⟩ := exists_good' hL g'
  have u := (isUnit_sval_iff (φ := fun _ : Fin 1 => (snd T G).left) σ (𝟙 _ ≫ (h ▷ G).left) g' hJ).2
    (by rw [Category.id_comp, h₁]; exact hn)
  exact (isUnit_sval_iff (φ := fun _ : Fin 1 => (snd (Over.mk χ) G).left) _ (𝟙 _) g' hJ).1
    ((congrArg IsUnit (VVRank.sv_pullS G _ h σ (𝟙 _) g' hJ)).mpr u)

theorem exists_sec_nz_up {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
    {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ) {L₀ : LB G.left} {L₁ : LB A.left}
    {w : LB.Iso L₁ (L₀.pull φ)} (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (h : GlobalTheory.LN.ThetaNZ A L₁) :
    ∃ σ : LB.Sec (LPow G L₀ ((1 : ℕ) : ℤ) (Over.mk f)),
      ∀ y : (Over.mk f).left, ∃ g, (fst (Over.mk f) G).left g = y ∧ g ∈ nonzeroLocus σ := by
  obtain ⟨θ, hθ⟩ := h
  let T : Over S' := Over.mk (𝟙 S')
  obtain ⟨s, hs⟩ := exists_sec_pull_locus θ (snd T A).left
  have hτ : (𝟙 S' : T.left ⟶ (Over.mk f).left) ≫ (Over.mk f).hom = T.hom ≫ f := rfl
  have : IsIso (𝟙 S' : T.left ⟶ (Over.mk f).left) := IsIso.id S'
  obtain ⟨σ, hσ⟩ := exists_secRel_up (T := T) (T₀ := Over.mk f) hp (𝟙 S') hτ hw hL₀ hL₁ (a := ((1 : ℕ) : ℤ)) s
  refine ⟨σ, fun y => ?_⟩
  obtain ⟨g, i, hg, hi⟩ := hθ y
  obtain ⟨z, h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback T.hom A.hom) y g hg.symm
  have hz : z ∈ nonzeroLocus s := by
    rw [hs]
    change pullback.snd T.hom A.hom z ∈ nonzeroLocus θ
    rw [h₂]
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  obtain ⟨J, hJ⟩ := exists_good' hL₀ z
  obtain ⟨J', hJ'⟩ := exists_good' hL₁ z
  have e₁ := psi_fst' (T := T) (T₀ := Over.mk f) hp (𝟙 S') hτ
  refine ⟨psi (T := T) (T₀ := Over.mk f) hp (𝟙 S') hτ z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, e₁]
    exact h₁
  have u := (isUnit_sval_iff (φ := fun _ : Fin 1 => (snd T A).left) s (𝟙 _) z hJ').2 hz
  have e := hσ _ (𝟙 _) z J J' hJ hJ'
  rw [Category.id_comp] at e
  exact (isUnit_sval_iff (φ := fun _ : Fin 1 => (snd (Over.mk f) G).left) σ _ z hJ).1
    ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))

theorem exists_nz_of_polAt : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (χ : Sp W ⟶ S) (t' : SAB H (Sp W)) (_ : SABMap t' t χ), GlobalTheory.LN.PolAt t' (jK W) → ∃ σ : LB.Sec (LPow t.G t.PP.L ((1 : ℕ) : ℤ) (Over.mk χ)), ∀ (W' : Type) [CommRing W'] [IsLocalRing W'] (i : W →+* W') (χ' : Sp W' ⟶ S) (h : spMap i ≫ χ = χ'), NZ t.G t.PP.L χ' (VVRank.pullS t.G _ (Over.homMk (spMap i) h : Over.mk χ' ⟶ Over.mk χ) σ) := by
  intro h₁ h₂ E _ _ _ H S t W _ _ _ χ t' m hp
  obtain ⟨w, hw, -⟩ := m.lin
  obtain ⟨σ, hσ⟩ := exists_sec_nz_up m.cart hw t.PP.isLB t'.PP.isLB
    (GlobalTheory.ThetaDvr.thetaNZ_of_polAt h₁ h₂ E H W t' hp)
  exact ⟨σ, fun W' _ _ i χ' h => nz_pullS t.G t.PP.isLB σ hσ χ' _⟩

end GlobalTheory.Ex.OneGen
