import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPullCubicalOfIso
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemiAbelianHomExtensionUnique
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGenOfGenericFibre
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRigidifiedExtensionOfGenericFibre

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.TripleModel

open GlobalTheory.PrimNorm GlobalTheory.MulPull

section Charts

variable {Y Y' : Scheme.{0}}

def chartQuotOut (M N : LB Y) (f : Y' ⟶ Y) :
    ChartPull ((LB.div M N).pull f) (LB.div (M.pull f) (N.pull f)) (𝟙 Y') :=
  have le : ∀ J : PUnit → M.ι × N.ι, ((LB.div M N).pull f).U J ≤
      (M.pull f).U (fun _ => (J PUnit.unit).1) ⊓ (N.pull f).U (fun _ => (J PUnit.unit).2) := fun J y hy =>
    ⟨mem_pull.2 ((mem_pull (L := LB.div M N)).1 hy).1, mem_pull.2 ((mem_pull (L := LB.div M N)).1 hy).2⟩
  { idx := fun J => (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
    le := le
    g := fun y J J' hJ hJ' => by
      refine (gm_pull_g (LB.div M N) f (𝟙 Y') y J J' hJ hJ').trans ((gm_div N M (𝟙 Y' ≫ f) y _ _
        ⟨(mem_pull (L := LB.div M N)).1 hJ, (mem_pull (L := LB.div M N)).1 hJ'⟩).trans (Eq.symm
          ((gm_div (N.pull f) (M.pull f) (𝟙 Y') y (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
          (fun _ => (J' PUnit.unit).1, fun _ => (J' PUnit.unit).2) ⟨le J hJ, le J' hJ'⟩).trans ?_)))
      exact congrArg₂ (fun a b => a * b⁻¹) (gm_pull_g M f (𝟙 Y') y _ _ (le J hJ).1 (le J' hJ').1)
        (gm_pull_g N f (𝟙 Y') y _ _ (le J hJ).2 (le J' hJ').2) }

def chartQuotIn (M N : LB Y) (f : Y' ⟶ Y) :
    ChartPull (LB.div (M.pull f) (N.pull f)) ((LB.div M N).pull f) (𝟙 Y') :=
  have le : ∀ p : (PUnit → M.ι) × (PUnit → N.ι), (M.pull f).U p.1 ⊓ (N.pull f).U p.2 ≤
      ((LB.div M N).pull f).U (fun _ => (p.1 PUnit.unit, p.2 PUnit.unit)) := fun p y hy =>
    (mem_pull (L := LB.div M N)).2 ⟨mem_pull.1 hy.1, mem_pull.1 hy.2⟩
  { idx := fun p _ => (p.1 PUnit.unit, p.2 PUnit.unit)
    le := le
    g := fun y p q hp hq => ((chartQuotOut M N f).g y _ _ (le p hp) (le q hq)).symm }

end Charts

section Cubical

theorem isPullCubical_of_lbIso (hG : Out.GlobalFnsSt) {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G']
    [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (hA : IsAbelianScheme G') {f : S' ⟶ S} {α : G'.left ⟶ G.left}
    (gp : IsGrpPullback G' G f α) {L' : RigLB G'} {L : RigLB G}
    (c' : CubicalStr G' L') (c : CubicalStr G L) (h : LBIso L'.L (L.L.pull α)) :
    (cubeMapOf gp).IsPullCubical c' c := by
  obtain ⟨w, hw⟩ := h
  have hw' := (isGen_iff w).1 hw
  obtain ⟨a, ha, hm⟩ := DegPull.exists_pmaps (K := PUnit) hw' L.isLB L'.isLB (φ' := fun _ => eSec G')
    (φ := fun _ => eSec G) (ε := fun _ => 1) (cubeMapOf gp).e (fun _ => (cubeMapOf gp).e_comm) L.rig L.rigGen
  obtain ⟨u, hu⟩ := HeckePoint.exists_unit_ratio L'.isLB a L'.rig ha L'.rigGen
  let w₁ : LB.Iso L'.L (L.L.pull α) :=
    ⟨fun p => w.s p * res (U := G'.hom ⁻¹ᵁ ⊤) (fun _ _ => trivial) (pullU G'.hom ⊤ u)⟩
  have g₁ : ∀ (Y : Scheme.{0}) (f : Y ⟶ G'.left) (y : Y) j k, α (f y) ∈ L.L.U j → f y ∈ L'.L.U k →
      gw w₁ f y j k = gw w f y j k * gm (f ≫ G'.hom) y ⊤ u := fun Y f y j k hj hk =>
    (map_mul _ _ _).trans (congrArg _ ((gm_res f y _ (show f y ∈ (L.L.pull α).U (fun _ => j) ⊓ L'.L.U k from
      ⟨mem_pull.2 hj, hk⟩) _).trans (gm_pull f G'.hom y ⊤ trivial u)))
  have hw₁ : PGen w₁ := fun Y f y j j' k k' hj hj' hk hk' => by
    rw [g₁ Y f y j k hj hk, g₁ Y f y j' k' hj' hk', hw' Y f y j j' k k' hj hj' hk hk', _root_.mul_assoc]
  refine (isPullCubical_iff _ c c').2 ⟨w₁, hw₁, fun Z r z p q hp hq => ?_, ?_⟩
  · refine (hm Z r z p q hp hq).trans ?_
    have e : (r ≫ eSec G') ≫ G'.hom = r := by
      rw [Category.assoc, show eSec G' ≫ G'.hom = 𝟙 _ from Over.w η[G'], Category.comp_id]
    have e₂ := g₁ Z (r ≫ eSec G') z _ _ (hp default) (hq default)
    rw [e] at e₂
    rw [hu Z r z q (Set.mem_iInter.2 hq), Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one]
    exact (_root_.mul_assoc _ _ _).symm.trans (congrArg (· * _) e₂.symm)
  · let e : 𝟙_ (Over S') ⟶ G3 G' := lift 1 (lift 1 1)
    have s₁ := (hG _ _ hA).2
    have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ α = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
      fun I => (cubeMapOf gp).psum_comm I.down
    refine EvenPull.pmaps_of_section (φ' := thφ G' (x3 G')) (φ := thφ G (x3 G)) (ε := thε) hw₁ L.isLB L'.isLB
      (cubeMapOf gp).F3 hψ c'.t c'.isGen
      c.t c.isGen (G3 G').hom e.left (Over.w e) (AbLaw.Cube.surj_tensor hG hA (AbLaw.Cube.surj_tensor hG hA s₁))
      (fun y J J' hJ hJ' => ?_)
    have a₁ : e.left ≫ (cubeMapOf gp).F3 =
        (lift (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G) (lift 1 1)).left := hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      have o := congrArg (fun q => q.left) (map_one (pushHom gp (𝟙_ (Over S'))))
      have e₁ : e ≫ x3 G' i = 1 := by fin_cases i <;> simp [e, x3]
      have e₂ : lift (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G) (lift 1 1) ≫ x3 G i = 1 := by
        fin_cases i <;> simp [x3]
      rw [e₁, e₂]
      exact o
    have b₁ := (isCub_cubV c (T := Over.mk ((𝟙_ (Over S')).hom ≫ f)) hJ).face 1 1
    have b₂ := (isCub_cubV c' (T := 𝟙_ (Over S')) hJ').face 1 1
    have b₃ := prod_cub (1 : 𝟙_ (Over S') ⟶ G') 1 1 (fun ψ => gw w₁ ψ y (J (ψ ≫ α)) (J' ψ))
    refine Eq.trans ((congrArg (fun q => val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t q y J) a₁).trans b₁)
      (Eq.symm ?_)
    refine (congrArg₂ (· * ·) b₃ b₂).trans ?_
    simp

end Cubical

section Ample

variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

end Ample

section Extend

variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {A : Over (Sp R)} [GrpObj A] {B : Over (Sp K)} [GrpObj B] {φ : B.left ⟶ A.left} {L : LB A.left} {L' : LB B.left}

end Extend

section Points

variable {S S' : Scheme.{0}} {A : Over S} [GrpObj A] {B : Over S'} [GrpObj B] {j : S' ⟶ S} {φ : B.left ⟶ A.left}

abbrev fibre (T : Over S) (j : S' ⟶ S) : Over S' := Over.mk (pullback.snd T.hom j)

abbrev fibreProj (T : Over S) (j : S' ⟶ S) : Over.mk ((fibre T j).hom ≫ j) ⟶ T :=
  Over.homMk (pullback.fst T.hom j) pullback.condition

end Points

section Triple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (hLaws : Out.Laws) (t₀ : SAB H (Sp K)) {A : Over (Sp R)} [GrpObj A] {φ : t₀.G.left ⟶ A.left}
  (hA : IsAbelianScheme A) (gp : IsGrpPullback t₀.G A (spMap (algebraMap R K)) φ)
  {L : LB A.left} (hL : L.IsLB) (hr : Out.Rigidified A L) (i : LBIso t₀.PP.L (L.pull φ))

include hLaws hA gp hL hr i

end Triple

end GlobalTheory.TripleModel
