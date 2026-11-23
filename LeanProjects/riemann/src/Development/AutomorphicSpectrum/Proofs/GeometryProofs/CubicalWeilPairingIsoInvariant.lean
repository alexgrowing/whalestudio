import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsAbLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonDegAtOfSabMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CubicalTripleTrivialStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.CubIso

section Local
variable {X Y Z : Scheme.{0}} {A B : LB X}

def isoGerm (w : LB.Iso A B) (f : Y ⟶ X) (y : Y) (j : B.ι) (k : A.ι) : (Y.presheaf.stalk y)ˣ :=
  gm f y (B.U j ⊓ A.U k) (w.s (j, k))

theorem isoGerm_trans {w : LB.Iso A B} (hw : w.IsGen) (f : Y ⟶ X) (y : Y) {j j' : B.ι} {k k' : A.ι}
    (hj : f y ∈ B.U j) (hj' : f y ∈ B.U j') (hk : f y ∈ A.U k) (hk' : f y ∈ A.U k') :
    isoGerm w f y j k = gm f y _ (B.g j j') * (gm f y _ (A.g k k'))⁻¹ * isoGerm w f y j' k' := by
  have hm : f y ∈ B.U j ⊓ A.U k ⊓ (B.U j' ⊓ A.U k') := ⟨⟨hj, hk⟩, hj', hk'⟩
  have h := congrArg (gm f y (B.U j ⊓ A.U k ⊓ (B.U j' ⊓ A.U k'))) (hw (j, k) (j', k'))
  have e : gm f y (B.U j ⊓ A.U k ⊓ (B.U j' ⊓ A.U k')) ((LB.div B A).g (j, k) (j', k')) =
      gm f y _ (B.g j j') * (gm f y _ (A.g k k'))⁻¹ := by
    show gm f y _ (res _ (B.g j j') * (res _ (A.g k k'))⁻¹) = _
    rw [map_mul, map_inv, gm_res f y _ hm, gm_res f y _ hm]
  exact (gm_res f y _ hm _).symm.trans (h.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) e (gm_res f y _ hm _))))

variable {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem prod_isoGerm_trans {w : LB.Iso A B} (hw : w.IsGen) (r : Z ⟶ Y) (z : Z) {p p' : K → B.ι} {q q' : K → A.ι}
    (hp : r z ∈ LB.wchart B φ p) (hp' : r z ∈ LB.wchart B φ p') (hq : r z ∈ LB.wchart A φ q)
    (hq' : r z ∈ LB.wchart A φ q') :
    ∏ k, isoGerm w (r ≫ φ k) z (p k) (q k) ^ ε k =
      trF (L := B) φ ε r z p p' * (trF (L := A) φ ε r z q q')⁻¹ * ∏ k, isoGerm w (r ≫ φ k) z (p' k) (q' k) ^ ε k := by
  rw [trF, trF, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [isoGerm_trans hw (r ≫ φ k) z (Set.mem_iInter.1 hp k) (Set.mem_iInter.1 hp' k) (Set.mem_iInter.1 hq k)
    (Set.mem_iInter.1 hq' k), mul_zpow, mul_zpow, _root_.inv_zpow]

theorem exists_ratio (hA : A.IsLB) (hB : B.IsLB) {w : LB.Iso A B} (hw : w.IsGen) {a : LB.Gen (LB.LinComb A φ ε)}
    {b : LB.Gen (LB.LinComb B φ ε)} (ha : a.IsGen) (hb : b.IsGen) :
    ∃ v : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → B.ι) (q : K → A.ι),
      r z ∈ LB.wchart B φ p → r z ∈ LB.wchart A φ q →
      gm r z (LB.wchart B φ p) (b.s p) = gm r z ⊤ v * (∏ k, isoGerm w (r ≫ φ k) z (p k) (q k) ^ ε k) *
        gm r z (LB.wchart A φ q) (a.s q) := by
  let Wc : (K → B.ι) × (K → A.ι) → Y.Opens := fun P => LB.wchart B φ P.1 ⊓ LB.wchart A φ P.2
  have le : ∀ P k, Wc P ≤ φ k ⁻¹ᵁ (B.U (P.1 k) ⊓ A.U (P.2 k)) := fun P k =>
    le_inf (inf_le_left.trans (LB.wchart_le B φ P.1 k)) (inf_le_right.trans (LB.wchart_le A φ P.2 k))
  let I : ∀ P, Γ(Y, Wc P)ˣ := fun P => res (inf_le_left : Wc P ≤ LB.wchart B φ P.1) (b.s P.1) *
    (res (inf_le_right : Wc P ≤ LB.wchart A φ P.2) (a.s P.2))⁻¹ *
    (∏ k, res (le P k) (pullU (φ k) _ (w.s (P.1 k, P.2 k))) ^ ε k)⁻¹
  have hI : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) P, r z ∈ Wc P → gm r z (Wc P) (I P) =
      gm r z (LB.wchart B φ P.1) (b.s P.1) * (gm r z (LB.wchart A φ P.2) (a.s P.2))⁻¹ *
        (∏ k, isoGerm w (r ≫ φ k) z (P.1 k) (P.2 k) ^ ε k)⁻¹ := by
    intro Z r z P hz
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _)
      ((map_inv _ _ ).trans (congrArg _ (gm_res r z _ hz _))))) ((map_inv _ _).trans (congrArg _ ?_)))
    refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
    exact (gm_res r z (le P k) hz _).trans (gm_pull r (φ k) z _ (le P k hz) _)
  obtain ⟨v, hv⟩ := glue_unit ⊤ Wc (fun _ => le_top) (fun x _ => by
      choose p hp using fun k => exists_chart hB (φ k x)
      choose q hq using fun k => exists_chart hA (φ k x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(p, q), Set.mem_iInter.2 hp, Set.mem_iInter.2 hq⟩) I (fun P Q x hx => by
      rw [hI _ _ x P hx.1, hI _ _ x Q hx.2, gen_trans hb (𝟙 Y) x hx.1.1 hx.2.1, gen_trans ha (𝟙 Y) x hx.1.2 hx.2.2,
        prod_isoGerm_trans hw (𝟙 Y) x hx.1.1 hx.2.1 hx.1.2 hx.2.2]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  refine ⟨v, fun Z r z p q hp hq => ?_⟩
  have hz : r z ∈ Wc (p, q) := ⟨hp, hq⟩
  have e := (gm_res r z (le_top : Wc (p, q) ≤ ⊤) hz v).symm.trans ((congrArg (gm r z (Wc (p, q))) (hv (p, q))).trans
    (hI Z r z (p, q) hz))
  rw [e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem appTop_eq_one (r : Z ⟶ Y) (v : Γ(Y, ⊤)ˣ) (h : ∀ z, gm r z ⊤ v = 1) : r.appTop.hom v.val = 1 := by
  have e : Units.map r.appTop.hom.toMonoidHom v = 1 :=
    unit_ext fun z _ => by rw [← gm_top r z v, h z, map_one]
  exact congrArg Units.val e

end Local

section Cube
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L₁ L₂ : RigLB G}

theorem exists_cube_ratio {w : LB.Iso L₁.L L₂.L} (hw : w.IsGen) (c₁ : CubicalStr G L₁) (c₂ : CubicalStr G L₂) :
    ∃ v : Γ((G ⊗ G ⊗ G).left, ⊤)ˣ, ∀ (T : Over S) (z : T.left) (J₁ : (T.left ⟶ G.left) → L₁.L.ι)
      (J₂ : (T.left ⟶ G.left) → L₂.L.ι), Good L₁.L z J₁ → Good L₂.L z J₂ →
      ∀ (W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ), (∀ x, W x = isoGerm w x.left z (J₂ x.left) (J₁ x.left)) →
      ∀ a b d : T ⟶ G, cubV c₂ z J₂ a b d * W (a * b) * W (a * d) * W (b * d) * W 1 =
        gm (lift a (lift b d)).left z ⊤ v * (W (a * b * d) * W a * W b * W d) * cubV c₁ z J₁ a b d := by
  obtain ⟨v, hv⟩ := exists_ratio (φ := thφ G (x3 G)) (ε := thε) (a := c₁.t) (b := c₂.t) L₁.isLB L₂.isLB hw
    c₁.isGen c₂.isGen
  refine ⟨v, fun T z J₁ J₂ h₁ h₂ W hW a b d => ?_⟩
  have e := hv T.left (lift a (lift b d)).left z (fun I => J₂ ((lift a (lift b d)).left ≫ thφ G (x3 G) I))
    (fun I => J₁ ((lift a (lift b d)).left ≫ thφ G (x3 G) I)) (h₂.mem _ _) (h₁.mem _ _)
  have f := prod_cub a b d (fun q => isoGerm w q z (J₂ q) (J₁ q))
  have e' : cubV c₂ z J₂ a b d = gm (lift a (lift b d)).left z ⊤ v *
      (∏ I : thK.{0}, isoGerm w ((lift a (lift b d)).left ≫ thφ G (x3 G) I) z
        (J₂ ((lift a (lift b d)).left ≫ thφ G (x3 G) I)) (J₁ ((lift a (lift b d)).left ≫ thφ G (x3 G) I)) ^ thε I) *
      cubV c₁ z J₁ a b d := e
  rw [e', f, hW, hW, hW, hW, hW, hW, hW, hW]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem cube_ratio_faces {w : LB.Iso L₁.L L₂.L} (c₁ : CubicalStr G L₁) (c₂ : CubicalStr G L₂)
    {v : Γ((G ⊗ G ⊗ G).left, ⊤)ˣ}
    (hv : ∀ (T : Over S) (z : T.left) (J₁ : (T.left ⟶ G.left) → L₁.L.ι)
      (J₂ : (T.left ⟶ G.left) → L₂.L.ι), Good L₁.L z J₁ → Good L₂.L z J₂ →
      ∀ (W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ), (∀ x, W x = isoGerm w x.left z (J₂ x.left) (J₁ x.left)) →
      ∀ a b d : T ⟶ G, cubV c₂ z J₂ a b d * W (a * b) * W (a * d) * W (b * d) * W 1 =
        gm (lift a (lift b d)).left z ⊤ v * (W (a * b * d) * W a * W b * W d) * cubV c₁ z J₁ a b d)
    (T : Over S) (x y : T ⟶ G) :
    (lift (1 : T ⟶ G) (lift x y)).left.appTop.hom v.val = 1 ∧
      (lift x (lift (1 : T ⟶ G) y)).left.appTop.hom v.val = 1 ∧
      (lift x (lift y (1 : T ⟶ G))).left.appTop.hom v.val = 1 := by
  refine ⟨appTop_eq_one _ v fun z => ?_, appTop_eq_one _ v fun z => ?_, appTop_eq_one _ v fun z => ?_⟩
  all_goals
    obtain ⟨J₁, h₁⟩ := exists_good_pt L₁.isLB z
    obtain ⟨J₂, h₂⟩ := exists_good_pt L₂.isLB z
  · have e := hv T z J₁ J₂ h₁ h₂ _ (fun _ => rfl) 1 x y
    rw [(isCub_cubV c₁ h₁).face, (isCub_cubV c₂ h₂).face] at e
    simp only [_root_.one_mul, _root_.mul_one] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'
  · have e := hv T z J₁ J₂ h₁ h₂ _ (fun _ => rfl) x 1 y
    rw [(isCub_cubV c₁ h₁).face₂, (isCub_cubV c₂ h₂).face₂] at e
    simp only [_root_.one_mul, _root_.mul_one] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'
  · have e := hv T z J₁ J₂ h₁ h₂ _ (fun _ => rfl) x y 1
    rw [(isCub_cubV c₁ h₁).face₃, (isCub_cubV c₂ h₂).face₃] at e
    simp only [_root_.one_mul, _root_.mul_one] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'

end Cube

theorem cubWeil_of_lbIso : ∀ (G : Over (Sp ℂ)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → TorusExtension G → ∀ (L₁ L₂ : RigLB G) (c₁ : CubicalStr G L₁) (c₂ : CubicalStr G L₂), LBIso L₁.L L₂.L → ∀ (N : ℕ) (x y : 𝟙_ (Over (Sp ℂ)) ⟶ G) (ζ : Γ(Sp ℂ, ⊤)ˣ), CubWeil c₁ N x y ζ → CubWeil c₂ N x y ζ := by
  intro G _ _ hs te L₁ L₂ c₁ c₂ hiso N x y ζ h
  obtain ⟨w, hw⟩ := hiso
  obtain ⟨v, hv⟩ := exists_cube_ratio hw c₁ c₂
  have hone := GlobalTheory.T.cubical_triple_trivial ℂ G hs te v (cube_ratio_faces c₁ c₂ hv)
  refine ⟨h.1, h.2.1, fun z J₂ h₂ => ?_⟩
  obtain ⟨J₁, h₁⟩ := exists_good_pt L₁.isLB z
  let W : (𝟙_ (Over (Sp ℂ)) ⟶ G) → _ := fun a => isoGerm w a.left z (J₂ a.left) (J₁ a.left)
  refine cubN_ratio_twist (MonoidHom.id _) W (fun a b d => ?_) h.1 h.2.1 (h.2.2 z J₁ h₁)
  have e := hv _ z J₁ J₂ h₁ h₂ W (fun _ => rfl) a b d
  have g : gm (lift a (lift b d)).left z ⊤ v = 1 := by
    rw [gm_top]
    have : Units.map (lift a (lift b d)).left.appTop.hom.toMonoidHom v = 1 := Units.ext (hone a b d)
    rw [this, map_one]
  rw [g, _root_.one_mul] at e
  exact e

end GlobalTheory.CompanionTheory.Ar.CubIso
