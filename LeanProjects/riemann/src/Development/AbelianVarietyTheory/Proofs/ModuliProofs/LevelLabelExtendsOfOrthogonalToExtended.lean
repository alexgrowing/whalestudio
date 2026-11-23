import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsToricTorsionCubWeilOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEqNsmulOfForallDvdOfBijective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PowEqOneIffOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelDvdFormOfCubWeilOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGeometricPointRootOfUnityEqOneOfIsDominant
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfIsPullbackIsDominant
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOneLeft
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory.UU

namespace GlobalTheory.Coisotropic

theorem isReduced_of_isNormalScheme {X : Scheme.{0}} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := (h x).1
    infer_instance
  exact isReduced_of_isReduced_stalk X

theorem isDominant_fst {X U V : Scheme.{0}} (j : U ⟶ X) (v : V ⟶ X) [IsDominant j] [IsOpenImmersion v] :
    IsDominant (pullback.fst v j) := by
  refine ⟨?_⟩
  rw [DenseRange, Scheme.Pullback.range_fst]
  exact j.denseRange.preimage v.isOpenEmbedding.isOpenMap

theorem section_ext {X U Y V : Scheme.{0}} {j : U ⟶ X} {q : Y ⟶ X} (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) [IsDominant j]
    [IsSeparated q] (v : V ⟶ X) [IsOpenImmersion v] {σ σ' : V ⟶ Y} (h : σ ≫ q = σ' ≫ q)
    (e : pullback.fst v j ≫ σ = pullback.fst v j ≫ σ') : σ = σ' := by
  have := isReduced_of_isNormalScheme hn
  have : IsReduced V := isReduced_of_isOpenImmersion v
  have := isDominant_fst j v
  exact ext_of_isDominant_of_isSeparated q h (pullback.fst v j) e

theorem extension_unique : ∀ (X U Y : Scheme.{0}) (j : U ⟶ X) (q : Y ⟶ X) (e : U ⟶ Y), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsDominant j → IsSeparated q → ∀ (V V' T : Scheme.{0}) (v : V ⟶ X) (v' : V' ⟶ X), IsOpenImmersion v → IsOpenImmersion v' → ∀ (σ : V ⟶ Y) (σ' : V' ⟶ Y) (y : T ⟶ V) (y' : T ⟶ V'), y ≫ v = y' ≫ v' → σ ≫ q = v → σ' ≫ q = v' → pullback.fst v j ≫ σ = pullback.snd v j ≫ e → pullback.fst v' j ≫ σ' = pullback.snd v' j ≫ e → y ≫ σ = y' ≫ σ' := by
  intro X U Y j q e hn _ _ V V' T v v' _ _ σ σ' y y' hy e1 e2 e3 e4
  have key : pullback.fst v v' ≫ σ = pullback.snd v v' ≫ σ' := by
    refine section_ext (j := j) (q := q) hn (pullback.fst v v' ≫ v)
      (by rw [Category.assoc, Category.assoc, e1, e2, pullback.condition]) ?_
    have a := pullback.lift (pullback.fst (pullback.fst v v' ≫ v) j ≫ pullback.fst v v') _
      (by rw [Category.assoc]; exact pullback.condition) ≫= e3
    have b := pullback.lift (pullback.fst (pullback.fst v v' ≫ v) j ≫ pullback.snd v v') _
      (by rw [Category.assoc, ← pullback.condition]; exact pullback.condition) ≫= e4
    rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc] at a b
    exact a.trans b.symm
  have := pullback.lift y y' hy ≫= key
  rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this

theorem extension_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (X U : Scheme.{0}) (j : U ⟶ X) (s : U ⟶ Sp B) (o : Obj D l b s) (t : SAB H X) (μ₀ : SABMap o.t t j), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsDominant j → ∀ (V : Scheme.{0}) (v : V ⟶ X), IsOpenImmersion v → ∀ (a : D.La) (σ : Over.mk v ⟶ t.G), pullback.fst v j ≫ σ.left = pullback.snd v j ≫ (o.etaA a).left ≫ μ₀.φ → σ ^ l.A = 1 := by
  intro E _ _ _ H D l B _ b X U j s o t μ₀ hn _ V v _ a σ hσ
  have := t.semi.separated
  let hw := μ₀.cart.1.w
  have hmul : ∀ (T : Over U) (x y : T ⟶ o.t.G), Out.toBase hw (x * y) = Out.toBase hw x * Out.toBase hw y :=
    fun T x y => Over.OverMorphism.ext (μ₀.cart.2 T x y _ _ rfl rfl).symm
  have he : o.etaA a ^ l.A = 1 := by
    have h0 : o.etaA 0 = 1 := by simpa using o.etaA_ker 0
    have : ∀ n : ℕ, o.etaA (n • a) = o.etaA a ^ n := fun n => by
      induction n with
      | zero => simpa using h0
      | succ n ih => rw [succ_nsmul, o.etaA_add, ih, pow_succ]
    rw [← this, o.etaA_ker]
  let T : Over U := Over.mk (pullback.snd v j)
  let β := toBaseHom hmul T
  let ρ : Over.mk (T.hom ≫ j) ⟶ Over.mk v := Over.homMk (pullback.fst v j) pullback.condition
  have h1 : ρ ≫ σ = β (toUnit T ≫ o.etaA a) := by
    refine Over.OverMorphism.ext ?_
    have : (toUnit T).left = pullback.snd v j := (Category.comp_id _).symm.trans (Over.w (toUnit T))
    change pullback.fst v j ≫ σ.left = ((toUnit T).left ≫ (o.etaA a).left) ≫ μ₀.φ
    rw [this, hσ, Category.assoc]
  have h2 : ρ ≫ σ ^ l.A = ρ ≫ 1 := by
    rw [MonObj.comp_pow, h1, ← map_pow, ← MonObj.comp_pow, he, MonObj.comp_one, map_one, MonObj.comp_one]
  refine Over.OverMorphism.ext (section_ext (j := j) (q := t.G.hom) hn v ?_ (congrArg Over.Hom.left h2))
  rw [Over.w, Over.w]

theorem lattice_rank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), Module.Free ℤ D.La ∧ Module.Finite ℤ D.La ∧ Module.finrank ℤ D.La = 2 * (Module.finrank ℚ E / 2 * (D.p + D.q)) := by
  intro E _ _ _ H D
  have := D.fin
  exact ⟨datum_free_int D, Module.Finite.trans (𝓞 E) D.La, datum_finrank_int D⟩

end GlobalTheory.Coisotropic

theorem GlobalTheory.extends_of_orthogonal_to_extended : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X) (s : U ⟶ Sp B) (o : Obj D l b s) (t : SAB H X) (μ₀ : SABMap o.t t j), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsUnit (l.A : Γ(X, ⊤)) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (a : D.La), (∀ a', (∃ (W : X.Opens) (σ : W.toScheme ⟶ t.G.left), Set.range x ⊆ W ∧ σ ≫ t.G.hom = W.ι ∧ pullback.fst W.ι j ≫ σ = pullback.snd W.ι j ≫ (o.etaA a').left ≫ μ₀.φ) → (l.A : ℤ) ∣ D.EF a a') → (∃ (W : X.Opens) (σ : W.toScheme ⟶ t.G.left), Set.range x ⊆ W ∧ σ ≫ t.G.hom = W.ι ∧ pullback.fst W.ι j ≫ σ = pullback.snd W.ι j ≫ (o.etaA a).left ≫ μ₀.φ) := by
  intro hL _ hL3 E _ _ _ H D l B _ b X U _ j s o t μ₀ hn h1 h2 h3 h4 hA k _ _ x a ha
  have hk : ((l.A : ℕ) : k) ≠ 0 := by
    have := (hA.map x.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
    rw [map_natCast, map_natCast] at this
    exact this.ne_zero
  obtain ⟨hfr, hfi, hrk⟩ := GlobalTheory.Coisotropic.lattice_rank E H D
  have hg := GlobalTheory.smoothOfRelativeDimension_of_isPullback_isDominant X U _ _ j t.G.hom o.t.G.hom μ₀.φ _ μ₀.cart.1 h3 t.semi.smooth
    (GlobalTheory.obj_isAbelianScheme_dim_rigidified_sym E H D l B b U s o).2.1
  obtain ⟨T, hT1, hT2, hT3⟩ := GlobalTheory.exists_toric_torsion_cubWeil_one hL3 X t.G t.semi t.PP t.cub _ l.A k x hg hk
  let P := {p : Over.mk x ⟶ t.G // p ^ l.A = 1}
  let R : D.La → P → Prop := fun a p => ∃ (V : Scheme.{0}) (v : V ⟶ X) (_ : IsOpenImmersion v) (σ : V ⟶ t.G.left) (xV : Sp k ⟶ V), xV ≫ v = x ∧ σ ≫ t.G.hom = v ∧ pullback.fst v j ≫ σ = pullback.snd v j ≫ (o.etaA a).left ≫ μ₀.φ ∧ xV ≫ σ = p.1.left
  have hR : ∀ a p, R a p → ∃ (W : X.Opens) (σ : W.toScheme ⟶ t.G.left), Set.range x ⊆ W ∧ σ ≫ t.G.hom = W.ι ∧ pullback.fst W.ι j ≫ σ = pullback.snd W.ι j ≫ (o.etaA a).left ≫ μ₀.φ := by
    rintro a p ⟨V, v, hv, σ, xV, e1, e2, e3, -⟩
    refine ⟨v.opensRange, v.isoOpensRange.inv ≫ σ, ?_, ?_, ?_⟩
    · rintro _ ⟨z, rfl⟩
      exact ⟨xV z, by rw [← e1]; rfl⟩
    · rw [Category.assoc, e2, Scheme.Hom.isoOpensRange_inv_comp]
    · have hc : (pullback.fst v.opensRange.ι j ≫ v.isoOpensRange.inv) ≫ v = pullback.snd v.opensRange.ι j ≫ j := by
        rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, pullback.condition]
      have := pullback.lift _ _ hc ≫= e3
      rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc] at this
  have hcT : Nat.card (Subtype.val ⁻¹' T : Set P) = Nat.card T :=
    Nat.card_congr ⟨fun p => ⟨p.1.1, p.2⟩, fun τ => ⟨⟨τ.1, hT1 _ τ.2⟩, τ.2⟩, fun _ => rfl, fun _ => rfl⟩
  obtain ⟨p, hp⟩ := GlobalTheory.exists_rel_of_forall_dvd_of_card_mul D.La D.EF D.unimod l.A l.A_pos P (Subtype.val ⁻¹' T) R
    (by
      intro a c p h
      simpa only [R, o.etaA_add, o.etaA_ker, _root_.mul_one] using h)
    (by
      rintro a p p' ⟨V, v, hv, σ, xV, e1, e2, e3, e4⟩ ⟨V', v', hv', σ', xV', e1', e2', e3', e4'⟩
      refine Subtype.ext (Over.OverMorphism.ext ?_)
      rw [← e4, ← e4']
      exact GlobalTheory.Coisotropic.extension_unique X U _ j t.G.hom _ hn h3 t.semi.separated V V' _ v v' hv hv' σ σ' xV xV' (e1.trans e1'.symm)
        e2 e2' e3 e3')
    (fun p => GlobalTheory.TorsionSection.exists_section_extending_level E H D l B b X U j s o t μ₀ inferInstance hn h1 h2 h3 h4 hA k x p.1 p.2)
    (by rw [hcT, hrk]; exact hT3)
    (by
      rintro a p a' p' ⟨V, v, hv, σ, xV, e1, e2, e3, e4⟩ hp ⟨V', v', hv', σ', xV', e1', e2', e3', e4'⟩
      let w : pullback v v' ⟶ X := pullback.fst v v' ≫ v
      let τ : Over.mk w ⟶ t.G := Over.homMk (pullback.fst v v' ≫ σ) (by change (_ ≫ σ) ≫ _ = _ ≫ v; rw [Category.assoc, e2])
      let τ' : Over.mk w ⟶ t.G := Over.homMk (pullback.snd v v' ≫ σ') (by change (_ ≫ σ') ≫ _ = _ ≫ v; rw [Category.assoc, e2', pullback.condition])
      have key : ∀ {Z : Scheme.{0}} (z : Z ⟶ pullback v v') (u : Z ⟶ U), z ≫ w = u ≫ j →
          z ≫ τ.left = u ≫ (o.etaA a).left ≫ μ₀.φ ∧ z ≫ τ'.left = u ≫ (o.etaA a').left ≫ μ₀.φ := by
        intro Z z u hz
        constructor
        · have := pullback.lift (z ≫ pullback.fst v v') u (by rw [Category.assoc]; exact hz) ≫= e3
          rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc] at this
        · have := pullback.lift (z ≫ pullback.snd v v') u
            (by rw [Category.assoc, ← pullback.condition]; exact hz) ≫= e3'
          rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc] at this
      have hτ := GlobalTheory.Coisotropic.extension_pow E H D l B b X U j s o t μ₀ hn h3 _ w inferInstance a τ (key _ _ pullback.condition).1
      have hτ' := GlobalTheory.Coisotropic.extension_pow E H D l B b X U j s o t μ₀ hn h3 _ w inferInstance a' τ' (key _ _ pullback.condition).2
      obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil t.cub hτ hτ'
      let y : Sp k ⟶ pullback v v' := pullback.lift xV xV' (e1.trans e1'.symm)
      let ρ : Over.mk x ⟶ Over.mk w := Over.homMk y ((pullback.lift_fst_assoc _ _ _ _).trans e1)
      have r1 : ρ ≫ τ = p.1 := Over.OverMorphism.ext ((pullback.lift_fst_assoc _ _ _ _).trans e4)
      have r2 : ρ ≫ τ' = p'.1 := Over.OverMorphism.ext ((pullback.lift_snd_assoc _ _ _ _).trans e4')
      have hx := hζ.comp ρ
      rw [r1, r2] at hx
      have hx1 := congrArg Units.val (hx.unique (hT2 _ hp _ p'.2))
      obtain ⟨K, _, _, u, z, hz, hz1⟩ := GlobalTheory.exists_geometricPoint_rootOfUnity_eq_one_of_isDominant X U _ j w h3 inferInstance ζ.val l.A
        (by rw [← Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]) k y hk hx1
      let ρ' : Over.mk (u ≫ j) ⟶ Over.mk w := Over.homMk z hz
      have hu := hζ.comp ρ'
      have e : Units.map ρ'.left.appTop.hom.toMonoidHom ζ = 1 := Units.ext hz1
      rw [e] at hu
      exact GlobalTheory.Coisotropic.level_dvd_form_of_cubWeil_one hL E H D l B b X U j s o t μ₀ K u a a' _ _ (key z u hz).1 (key z u hz).2 hu)
    a (fun a' p' h => ha a' (hR a' p' h))
  exact hR a p hp
