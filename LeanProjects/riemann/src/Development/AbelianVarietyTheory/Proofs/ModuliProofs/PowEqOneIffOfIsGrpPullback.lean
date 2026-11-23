import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsDominantGeometricPointOfIsPreimmersion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory.UU

namespace GlobalTheory.TorsionSection

theorem pow_eq_one_iff_left {S : Scheme.{0}} {G T : Over S} [GrpObj G] (y : T ⟶ G) (n : ℕ) :
    y ^ n = 1 ↔ y.left ≫ (mulN G n).left = T.hom ≫ η[G].left := by
  have e : (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
    rw [Hom.one_def, Over.comp_left]; rfl
  rw [← e, ← Over.comp_left, GrpTangent.comp_mulN]
  exact ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h⟩

theorem pow_eq_one_iff_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' T : Over S'} [GrpObj G]
    [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) (y : T ⟶ G')
    (n : ℕ) :
    y ^ n = 1 ↔ (y.left ≫ F) ≫ (mulN G n).left = (T.hom ≫ f) ≫ η[G].left := by
  let φ : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) := MonoidHom.mk' (Out.toBase h.1.w)
    fun a b => Over.OverMorphism.ext (h.2 T a b _ _ rfl rfl).symm
  have hφ : Function.Injective φ := fun a b hab => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg Over.Hom.left hab) ((Over.w a).trans (Over.w b).symm))
  rw [← map_eq_one_iff φ hφ, map_pow]
  exact pow_eq_one_iff_left (φ y) n

theorem exists_section_extending_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (X U : Scheme.{0}) (j : U ⟶ X) (s : U ⟶ Sp B) (o : Obj D l b s) (t : SAB H X) (μ₀ : SABMap o.t t j), IsLocallyNoetherian X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsUnit (l.A : Γ(X, ⊤)) → ∀ (k : Type) [Field k] (x : Sp k ⟶ X) (p : Over.mk x ⟶ t.G), p ^ l.A = 1 → ∃ (a : D.La) (V : Scheme.{0}) (v : V ⟶ X) (_ : IsOpenImmersion v) (σ : V ⟶ t.G.left) (xV : Sp k ⟶ V), xV ≫ v = x ∧ σ ≫ t.G.hom = v ∧ pullback.fst v j ≫ σ = pullback.snd v j ≫ (o.etaA a).left ≫ μ₀.φ ∧ xV ≫ σ = p.left := by
  intro E _ _ _ H D l B _ b X U j s o t μ₀ hX hN h₁ h₂ h₃ h₄ hA k _ x p hp
  have := t.semi.smooth
  have := t.semi.separated
  have hP := GrpTangent.isPullback_torsion t.G l.A
  have hEt := GrpTangent.etale_torsion t.G hA
  have hι : (torsion.ι t.G l.A).left ≫ t.G.hom = (torsion t.G l.A).hom := Over.w _
  have hsep : IsSeparated (torsion t.G l.A).hom := by
    have : IsSeparated ((mulN t.G l.A).left ≫ t.G.hom) := by rw [Over.w]; infer_instance
    exact MorphismProperty.of_isPullback (P := @IsSeparated) hP (IsSeparated.of_comp _ t.G.hom)
  have := D.fin
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : AddGroup.FG D.La := Module.Finite.iff_addGroup_fg.mp this
  let K : AddSubgroup D.La := (nsmulAddMonoidHom (α := D.La) l.A).range
  have : K.FiniteIndex := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg _ l.A_pos.ne'
  let e : Multiplicative D.La →* (𝟙_ (Over U) ⟶ o.t.G) :=
    MonoidHom.mk' (fun a => o.etaA a.toAdd) fun a c => o.etaA_add _ _
  have hpow (a : D.La) : o.etaA a ^ l.A = 1 :=
    (map_pow e (.ofAdd a) l.A).symm.trans (o.etaA_ker a)
  have hout (a : D.La) : o.etaA (QuotientAddGroup.mk (s := K) a).out = o.etaA a := by
    obtain ⟨⟨_, c, rfl⟩, hc⟩ := QuotientAddGroup.mk_out_eq_add K a
    rw [hc, o.etaA_add]
    exact (congrArg (o.etaA a * ·) (o.etaA_ker c)).trans (_root_.mul_one _)
  have hw (a : D.La) : ((o.etaA a).left ≫ μ₀.φ) ≫ (mulN t.G l.A).left = j ≫ η[t.G].left :=
    ((pow_eq_one_iff_of_isGrpPullback μ₀.cart (o.etaA a) l.A).mp (hpow a)).trans
      (congrArg (· ≫ _) (Category.id_comp j))
  let σ (a : D.La) : U ⟶ (torsion t.G l.A).left := hP.lift _ _ (hw a)
  have hσ (a : D.La) : σ a ≫ (torsion.ι t.G l.A).left = (o.etaA a).left ≫ μ₀.φ := hP.lift_fst _ _ _
  let p' : Sp k ⟶ (torsion t.G l.A).left := hP.lift p.left x ((pow_eq_one_iff_left p l.A).mp hp)
  obtain ⟨i, W, hW, hW₁, hW₂⟩ := exists_opens_isOpenImmersion_extending_section X U j hN h₁ h₂ h₃ h₄
    (torsion t.G l.A).left (torsion t.G l.A).hom (D.La ⧸ K) (fun i => σ i.out) hEt hsep
    (fun i => hP.lift_snd _ _ _) (fun Ω _ _ u y hy => by
      have hy' : (y ≫ (torsion.ι t.G l.A).left) ≫ t.G.hom = u ≫ j := by
        rw [Category.assoc, hι, hy]
      let z : Over.mk u ⟶ o.t.G := Over.homMk (μ₀.cart.1.lift _ _ hy') (μ₀.cart.1.lift_snd _ _ _)
      have hz : z.left ≫ μ₀.φ = y ≫ (torsion.ι t.G l.A).left := μ₀.cart.1.lift_fst _ _ _
      have hzA : z ^ l.A = 1 := by
        refine (pow_eq_one_iff_of_isGrpPullback μ₀.cart z l.A).mpr ?_
        rw [hz, Category.assoc, hP.w, reassoc_of% hy]
        exact (Category.assoc _ _ _).symm
      obtain ⟨β, hβ⟩ := Spec.map_surjective (u ≫ s)
      obtain ⟨-, I, -, hI, -⟩ := o.geom Ω u β.hom hβ.symm
      obtain ⟨a, ha⟩ := (I.onto l.A l.A_pos z).mp hzA
      refine ⟨QuotientAddGroup.mk a, hP.hom_ext ?_ ?_⟩
      · rw [Category.assoc, hσ, hout, ← hz, ← ha, ← hI, Over.comp_left, Category.assoc]
        rfl
      · rw [hy, Category.assoc, hP.lift_snd])
    (p' (IsLocalRing.closedPoint k))
  have hr : Set.range p' ⊆ Set.range W.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Subsingleton.elim w (IsLocalRing.closedPoint k), Scheme.Opens.range_ι]
    exact hW
  refine ⟨i.out, W, W.ι ≫ (torsion t.G l.A).hom, hW₁, W.ι ≫ (torsion.ι t.G l.A).left,
    IsOpenImmersion.lift W.ι p' hr, ?_, ?_, ?_, ?_⟩
  · rw [IsOpenImmersion.lift_fac_assoc]; exact hP.lift_snd _ _ _
  · rw [Category.assoc, hι]
  · rw [reassoc_of% hW₂, hσ]
  · rw [IsOpenImmersion.lift_fac_assoc]; exact hP.lift_fst _ _ _

end GlobalTheory.TorsionSection
