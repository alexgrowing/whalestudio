import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHom
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCechDataPullbackOfLineBundleOnOpenStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorIsoExtendFromOpenContainingChartsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedPartialLineBundlesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.RigidBundleGlue

variable {X Y Z : Scheme.{0}}

theorem exists_gen_of_lbIso {P Q : LB X} (hP : P.IsLB) (hQ : Q.IsLB) (h : LBIso P Q)
    (H : ∃ t : LB.Gen P, t.IsGen) : ∃ t : LB.Gen Q, t.IsGen := by
  obtain ⟨w, hw⟩ := h.chartPull (chartPullId P) (chartPullPull Q (𝟙 X) (𝟙 X) rfl)
  obtain ⟨t, ht⟩ := H
  obtain ⟨a, ha⟩ := gen_chartPull (chartPullPull P (𝟙 X) (𝟙 X) rfl) t ht
  obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hQ hP a ha
  exact gen_chartPull (chartPullUnpull Q _ (Category.id_comp _)) c hc

theorem LBIso.pull {P Q : LB X} (h : LBIso P Q) (f : Y ⟶ X) : LBIso (P.pull f) (Q.pull f) :=
  h.chartPull (chartPullPull P f f rfl) (chartPullPull Q f f rfl)

def chartPullComp (L : LB X) (f : Y ⟶ X) (g : Z ⟶ Y) (c : Z ⟶ X) (e : c = g ≫ f) :
    ChartPull (L.pull c) ((L.pull f).pull g) (𝟙 Z) := by
  subst e
  exact chartPullIn L (fun _ : PUnit => f) (fun _ => 1) g

theorem eq_one_of_section {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) {e : S ⟶ A.left}
    (he : e ≫ A.hom = 𝟙 S) (V : S.Opens) (u : Γ(A.left, A.hom ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (A.hom ⁻¹ᵁ V))
    (hu : (e.appLE _ V h).hom u = 1) : u = 1 := by
  have := hA.smooth
  have := hA.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected
  have := GlobalFunctions.isIso_app FlatFibreInjective.injective_baseChange exists_noetherian_model_of_smooth A.hom V
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (A.hom.app V)).2 u
  have k : ∀ (q : S ⟶ S) (_ : q = 𝟙 S) (l : V ≤ q ⁻¹ᵁ V), (q.appLE V V l).hom a = a := by
    rintro _ rfl l
    have : (𝟙 S : S ⟶ S).appLE V V l = 𝟙 _ := by
      simp [Scheme.Hom.appLE]
      exact S.presheaf.map_id _
    rw [this]; rfl
  have h₁ : (e.appLE _ V h).hom ((A.hom.app V).hom a) = a :=
    (congrArg (fun q => q.hom a) (Scheme.Hom.comp_appLE e A.hom V V h)).symm.trans (k (e ≫ A.hom) he h)
  rw [h₁.symm.trans hu, map_one]

theorem eSec_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : eSec G' ≫ φ = f ≫ eSec G := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]

theorem exists_glue : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → ∀ (M : ∀ i, LB (G i).left) (B : I → I → Scheme.{0}) (a : ∀ i j, B i j ⟶ (G i).left) (b : ∀ i j, B i j ⟶ (G j).left), (∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j)) → (∀ i, (M i).IsLB) → (∀ i, Out.Rigidified (G i) (M i)) → (∀ i j, LBIso ((M i).pull (a i j)) ((M j).pull (b i j))) → ∃ L : LB A.left, L.IsLB ∧ Out.Rigidified A L ∧ ∀ i, LBIso (M i) (L.pull (ψ i)) := by
  intro S I U A _ G _ ψ hU hψ hA _ M B a b hB hM hr hiso
  have oi : ∀ i, IsOpenImmersion (ψ i) := fun i => CoverGlue.isOpenImmersion (hψ i).1
  choose N hN₁ hN₂ hN₃ hN₄ using fun i => GlobalTheory.T.exists_cechData_pullback_of_lineBundle_on_open _ _ (ψ i) (M i) (hM i)
  have hR : ∀ i x, x ∈ (ψ i).opensRange ↔ A.hom x ∈ U i := fun i x => CoverGlue.mem_range (hψ i).1 x
  have hNU : ∀ i k, (N i).U k ≤ (ψ i).opensRange := fun i k => (le_iSup (N i).U k).trans (hN₁ i).le
  let e : S ⟶ A.left := eSec A
  have he : e ≫ A.hom = 𝟙 S := Over.w η[A]
  obtain ⟨L, hL, hLr, hLi⟩ := GlobalTheory.T.exists_glue_rigidified_partial_line_bundles A.left S A.hom e I U N he (eq_one_of_section A hA he) hU
    (fun i => (hN₁ i).trans (TopologicalSpace.Opens.ext (Set.ext (hR i)))) hN₂
    (fun i => by
      refine (GlobalTheory.T.generator_iso_extend_from_open_containing_charts S (U i).toScheme (U i).ι).1 _ (fun k s hs => ?_) ?_
      · have h₁ := (hR i _).1 (hNU i _ (mem_pull.1 hs))
        rw [← Scheme.Hom.comp_apply, he] at h₁
        exact ⟨⟨s, h₁⟩, rfl⟩
      · let e' : (U i).toScheme ⟶ (G i).left := eSec (G i)
        have hc : e' ≫ ψ i = (U i).ι ≫ e := eSec_comm (hψ i)
        obtain ⟨t, ht⟩ := exists_gen_of_lbIso (pull_isLB (hM i) e') (pull_isLB (hN₃ i) e')
          (LBIso.pull (hN₄ i) e') (hr i)
        obtain ⟨t', ht'⟩ := gen_chartPull (chartPullComp (N i) (ψ i) e' _ hc.symm) t ht
        exact gen_chartPull (chartPullOut (N i) (fun _ : PUnit => e) (fun _ => 1) (U i).ι _ fun _ => rfl) t' ht')
    (fun i j => by
      have : IsOpenImmersion (a i j) :=
        MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hB i j).flip (oi j)
      refine (GlobalTheory.T.generator_iso_extend_from_open_containing_charts A.left (B i j) (a i j ≫ ψ i)).2 _ _ (fun k l x hx => ?_) ?_
      · obtain ⟨y, hy⟩ := hNU i k hx.1
        obtain ⟨y', hy'⟩ := hNU j l hx.2
        obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback (hB i j) y y' (hy.trans hy'.symm)
        exact ⟨z, by rw [Scheme.Hom.comp_apply, hz, hy]⟩
      · refine LBIso.chartPull (chartPullComp (N i) (ψ i) (a i j) _ rfl)
          (chartPullComp (N j) (ψ j) (b i j) _ (hB i j).w) ?_
        exact ((LBIso.pull (hN₄ i) (a i j)).symm.trans (pull_isLB (hN₃ i) _) (pull_isLB (hM i) _)
          (pull_isLB (hM j) _) (hiso i j)).trans (pull_isLB (hN₃ i) _) (pull_isLB (hM j) _) (pull_isLB (hN₃ j) _)
          (LBIso.pull (hN₄ j) (b i j)))
  exact ⟨L, hL, hLr, fun i => (hN₄ i).trans (hM i) (hN₃ i) (pull_isLB hL _) (LBIso.pull (hLi i) (ψ i))⟩

end GlobalTheory.RigidBundleGlue
