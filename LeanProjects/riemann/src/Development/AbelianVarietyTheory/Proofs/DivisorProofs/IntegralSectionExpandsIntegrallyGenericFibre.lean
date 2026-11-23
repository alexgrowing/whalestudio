import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsFOfIntegral
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralDegenerationFamilyBaseChangeExtensionFie
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RegTiePfA
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaSpecialise

namespace GlobalTheory.IntExpand

theorem gs_secPull {X Y Z : Scheme.{0}} {L : LB X} (s : L.Sec) (φ : Y ⟶ X) (r : Z ⟶ Y) (z : Z)
    (j : (L.pull φ).ι) (hz : r z ∈ (L.pull φ).U j) :
    gs r z ((L.pull φ).U j) ((GlobalTheory.Cartier.secPull s φ).f j) = gs (r ≫ φ) z (L.U (j PUnit.unit)) (s.f (j PUnit.unit)) := by
  unfold GlobalTheory.Cartier.secPull
  exact (gs_res r z _ hz _).trans (gs_pull r φ z _ (Set.mem_iInter.1 hz PUnit.unit) _)

theorem gs_secMaps {X Z : Scheme.{0}} {A B : LB X} {w : LB.Iso A B} {a : A.Sec} {b : B.Sec}
    (h : GlobalTheory.Cartier.SecMaps w a b) (r : Z ⟶ X) (z : Z) (p : B.ι) (q : A.ι) (hp : r z ∈ B.U p)
    (hq : r z ∈ A.U q) :
    gs r z (B.U p) (b.f p) = ↑(gm r z ((B.div A).U (p, q)) (w.s (p, q))) * gs r z (A.U q) (a.f q) := by
  have e := congrArg (gs r z (B.U p ⊓ A.U q)) (h.on p q (W := B.U p ⊓ A.U q) inf_le_left inf_le_right)
  have hm : r z ∈ B.U p ⊓ A.U q := ⟨hp, hq⟩
  rw [gs_mul r z _ hm] at e
  unfold resG at e
  rw [gs_res r z _ hm, gs_res r z _ hm, gs_res r z _ hm] at e
  rw [e, gs_unit r z _ (by exact hm)]
  rfl

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D A G), ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre), w₀.IsGen → ∀ (s : A.L.Sec) (σ : U.LG.L.Sec), GlobalTheory.Cartier.SecMaps w₀ (GlobalTheory.Cartier.secPull s U.gen.hom.left) (GlobalTheory.Cartier.secPull σ (pullback.fst G.hom (jK V))) → ∀ (C : Type) [Field C] [Algebra (FractionRing V) C], ∃ (σ₁ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (th : GlobalTheory.UT.SecA A C 1) (ϑ : Fam D.toPre C 1), (∀ (i : U.LG.L.ι) (h : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i), σ₁.f (fun _ => i) = resG _ h (σ.f i)) ∧ (∀ e, U.ExpandsAt e 1 σ₁ f) ∧ MBLow.IsPolAVSectionInverseImage A (TFK (R := V) C) s th ∧ U.ExpandsF C 1 w₀ th ϑ ∧ ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C α) (DegPre.famε 1) (ϑ.s α) (D.toPre.famφB α) (DegPre.famε 1) (f α) (DegPre.prB D.toPre C).left 1 := by
  intro V _ _ _ _ hV D A G _ _ hG U w₀ hw s σ hS C _ _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let σ₁ : H0 U.LG.L 1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.secOne U.LG.L σ
  have h1 : ∀ (i : U.LG.L.ι) (h : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i), σ₁.f (fun _ => i) = resG _ h (σ.f i) := fun i h =>
    fn_ext fun x hx => (ReciprocityTheory.ChartRestriction.G.PullbackSections.gs_pull1 U.LG.L (𝟙 _) σ (𝟙 _) x _ hx).trans (by
      rw [Category.comp_id]; exact (gs_res (𝟙 _) x h hx (σ.f i)).symm)
  let sK : U.SecK 1 := genericSec U.toUnifPre 1 σ₁
  have hsK : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => ((1 : ℕ) : ℤ)) sK (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) σ₁ (pullback.fst G.hom (jK V)) 1 :=
    (secScal_one_iff U.LG.isLB).2 fun y J hJ => (sval_pullOver _ _ _ _ hJ).symm
  obtain ⟨E, hE, -⟩ := (U.expand 1 le_rfl).1 sK
  obtain ⟨f, hf, hEf⟩ := GlobalTheory.ExpInt.main V ϖ hϖ D A G U.toUnifPre 1 σ₁ sK hsK E hE
  obtain ⟨ϑ, hϑ⟩ := GlobalTheory.FamBaseChange.main GlobalTheory.globalFns_holds V _ D 1 E f hEf C
  let th : GlobalTheory.UT.SecA A C 1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.pull1 A.L (snd (TFK (R := V) C) A.A).left s
  have hth : MBLow.IsPolAVSectionInverseImage A (TFK (R := V) C) s th := by
    refine fun i h => fn_ext fun x hx => ?_
    exact (ReciprocityTheory.ChartRestriction.G.PullbackSections.gs_pull1 A.L _ s (𝟙 _) x _ hx).trans (gs_appLE _ _ _ h (𝟙 _) x hx (s.f i)).symm
  have n₁ : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
  obtain ⟨u, hu, hu₁⟩ := GlobalTheory.ThetaBaseChange.exists_unpull hw _ n₁ rfl
  have ht : PSec u (fun _ : Fin 1 => (snd (TFK (R := V) C) A.A).left) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ))
      ((snd (TFK (R := V) C) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V)) th σ₁ := by
    intro Z r z p q hp hq
    obtain ⟨p0, rfl⟩ : ∃ p0, p = fun _ => p0 := ⟨p 0, funext fun k => congrArg p (Subsingleton.elim k 0)⟩
    obtain ⟨q0, rfl⟩ : ∃ q0, q = fun _ => q0 := ⟨q 0, funext fun k => congrArg q (Subsingleton.elim k 0)⟩
    have hp0 := hp 0
    have hq0 := hq 0
    have e1 := hu₁ Z (r ≫ (snd (TFK (R := V) C) A.A).left) z p0 q0 hp0 hq0
    have c2 : ((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) ≫ U.gen.hom.left =
        r ≫ (snd (TFK (R := V) C) A.A).left := by
      rw [Category.assoc, n₁, Category.comp_id]
    have mB : ((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) z ∈
        (U.LG.L.pull (pullback.fst G.hom (jK V))).U (fun _ => p0) := Set.mem_iInter.2 fun _ => hp0
    have mA : ((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) z ∈
        (A.L.pull U.gen.hom.left).U (fun _ => q0) := Set.mem_iInter.2 fun _ => by
      show (((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) ≫ U.gen.hom.left) z ∈ A.L.U q0
      rw [c2]; exact hq0
    have e2 := GlobalTheory.IntExpand.gs_secMaps hS _ z (fun _ => p0) (fun _ => q0) mB mA
    rw [GlobalTheory.IntExpand.gs_secPull _ _ _ _ _ mB, GlobalTheory.IntExpand.gs_secPull _ _ _ _ _ mA, c2] at e2
    refine (ReciprocityTheory.ChartRestriction.G.PullbackSections.gs_pull1 U.LG.L (𝟙 _) σ
      (r ≫ (snd (TFK (R := V) C) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V)) z (fun _ => p0)
      (Set.mem_iInter.2 fun _ => by exact hp0)).trans ?_
    refine Eq.trans ?_ (congrArg (fun t => _ * t)
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.gs_pull1 A.L _ s r z (fun _ => q0) (Set.mem_iInter.2 fun _ => hq0)).symm)
    rw [Fin.prod_univ_one]
    dsimp only
    rw [Nat.cast_one, zpow_one, e1]
    have c1 : (r ≫ (snd (TFK (R := V) C) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V)) ≫ 𝟙 G.left =
        ((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) ≫ pullback.fst G.hom (jK V) := by
      simp only [Category.assoc, Category.comp_id]
    rw [c1]
    exact e2
  refine ⟨σ₁, f, th, ϑ, h1, hf, hth, expandsF_of_integral U.toUnifPre C hu₁ σ₁ f hf ϑ ?_ th ht, hϑ⟩
  intro α y J hJ
  exact (((secScal_one_iff D.toPre.P.isLB).1 (hϑ α)) y J hJ).symm

end GlobalTheory.IntExpand
