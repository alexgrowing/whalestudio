import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LbIsoLinComb
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Balanced
open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem stalkMap_inj {Y Z : Scheme.{0}} (r : Z ⟶ Y) [Flat r] (z : Z) : Function.Injective (r.stalkMap z).hom := by
  let _ := (r.stalkMap z).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (r z)) (Z.presheaf.stalk z) := Flat.stalkMap r z
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (r z)) (Z.presheaf.stalk z)) := inferInstanceAs (IsLocalHom (r.stalkMap z).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (r z)) (B := Z.presheaf.stalk z)
  exact FaithfulSMul.algebraMap_injective _ _

theorem surjective_spMap {K k : Type} [Field K] [Field k] (β : K →+* k) : Surjective (spMap β) :=
  ⟨fun _ => ⟨default, Subsingleton.elim _ _⟩⟩

theorem epi_spMap {K k : Type} [Field K] [Field k] (β : K →+* k) : Epi (spMap β) := by
  have : Flat (spMap β) := inferInstance
  have := surjective_spMap β
  exact Flat.epi_of_flat_of_surjective _

theorem val_descend {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (t : LB.Gen (LB.LinComb L φ ε))
    (t' : LB.Gen (LB.LinComb L φ' ε')) (r : Z ⟶ Y) [Flat r] [Surjective r]
    (h : ∀ z J, Good L z J → val t r z J = val t' r z J) (y : Y) (J) (hJ : Good L y J) :
    val t (𝟙 Y) y J = val t' (𝟙 Y) y J := by
  have : Epi r := Flat.epi_of_flat_of_surjective r
  obtain ⟨z, rfl⟩ := r.surjective y
  obtain ⟨J', hJ', e⟩ := exists_good L hL z (fun ψ : Y ⟶ X => r ≫ ψ) J
    (fun a b e => congrArg J ((cancel_epi r).1 e)) (fun ψ => hJ ψ)
  have := h z J' hJ'
  rw [val_of t r z J' (fun k => J (𝟙 Y ≫ φ k)) (fun k => by rw [Category.id_comp]; exact e _),
    val_of t' r z J' (fun k => J (𝟙 Y ≫ φ' k)) (fun k => by rw [Category.id_comp]; exact e _)] at this
  have h₁ := hJ.mem φ (𝟙 Y)
  have h₂ := hJ.mem φ' (𝟙 Y)
  have k : ∀ (U : Y.Opens) (_ : r z ∈ U) (a : Γ(Y, U)ˣ),
      (gm r z U a).val = (r.stalkMap z).hom (gm (𝟙 Y) (r z) U a).val := fun U hU a => by
    rw [gm_val r z U hU, gm_val _ (r z) U hU]
    exact (Scheme.Hom.germ_stalkMap_apply r U z hU _).symm
  exact Units.ext (stalkMap_inj r z ((k _ h₁ _).symm.trans ((congrArg Units.val this).trans (k _ h₂ _))))

section Ext
variable {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
  [Algebra (FractionRing R) F'] (f : F →+* F')
  (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')

theorem gtExt_injective (D : DegPre R) : Function.Injective (gtExt D f hf) := fun g g' h => by
  have := epi_spMap f
  have := surjective_spMap f
  have : Flat (spMap f) := inferInstance
  refine gt_ext_val (Over.OverMorphism.ext ((cancel_epi (spMap f)).1 ?_)) fun χ y J hJ => ?_
  · exact ((eq_gtExt_iff f hf g _).1 rfl).1.symm.trans (((eq_gtExt_iff f hf g' _).1 h).1)
  · refine val_descend D.P.isLB (g.s χ) (g'.s χ) (spMap f) (fun z J hJ => ?_) y J hJ
    exact (gtExt_val f hf g χ hJ).symm.trans ((congrArg (fun q => charVal q χ z J) h).trans (gtExt_val f hf g' χ hJ))

variable {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G} (E : EndU U)

theorem act_unique {g g₁ g₂ : GtPtF D.toPre F} (h₁ : E.Act g g₁) (h₂ : E.Act g g₂) : g₁ = g₂ :=
  gt_ext_val (h₁.1.trans h₂.1.symm) fun χ y J hJ => (h₁.2 χ y J hJ).trans (h₂.2 χ y J hJ).symm

theorem act_gtExt {g g' : GtPtF D.toPre F} (h : E.Act g g') : E.Act (gtExt _ f hf g) (gtExt _ f hf g') := by
  refine ⟨by rw [gtExt_b, gtExt_b, h.1, Category.assoc], fun χ z J hJ => ?_⟩
  have c : LB.Gen.Corr D.toPre.P.L _ _ _ _ (g'.s χ)
      (LB.mulGen D.toPre.P.L _ _ _ _ (g.s (E.h χ)) (LB.pullGen D.toPre.P.L _ _ (E.u χ) g.b.left)) :=
    corr_of_val D.toPre.P.isLB fun y J hJ => (h.2 χ y J hJ).trans (Eq.trans (congrArg₂ (· * ·) rfl (by
      rw [val_pull hJ, Category.id_comp])) (val_mul hJ _ _ _).symm)
  refine (gtExt_val f hf g' χ hJ).trans ((val_corr hJ c _).trans ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (gtExt_val f hf g _ hJ).symm ((val_pull hJ _ _ _).trans ?_))))
  rw [gtExt_b]; rfl

end Ext

section Adjoint

theorem adj_add {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L)
    (a a' : G ⟶ G) (h : LBIso (cubeLB G ![fst G G ≫ a, snd G G] L.L) (cubeLB G ![fst G G, snd G G ≫ a'] L.L)) (m : ℕ) :
    LBIso (cubeLB G ![fst G G ≫ (a * 𝟙 G ^ m), snd G G] L.L) (cubeLB G ![fst G G, snd G G ≫ (a' * 𝟙 G ^ m)] L.L) := by
  have hc := PrimNorm.diff₃_ptCls (T := G ⊗ G) L.isLB ⟨c.t, c.isGen⟩
  have p : ∀ (x y : G ⊗ G ⟶ G) (m : ℕ), PrimNorm.diff₂ (PrimNorm.ptCls L.L (G ⊗ G)) (x ^ m) y =
      PrimNorm.diff₂ (PrimNorm.ptCls L.L (G ⊗ G)) x y ^ m := fun x y m =>
    map_pow (MonoidHom.mk' (fun x => PrimNorm.diff₂ (PrimNorm.ptCls L.L (G ⊗ G)) x y)
      fun u v => PrimNorm.diff₂_mul_left hc u v y) x m
  have q : ∀ (x : G ⊗ G ⟶ G) (b : G ⟶ G), x ≫ (b * 𝟙 G ^ m) = (x ≫ b) * x ^ m := fun x b =>
    (map_mul (preHom x) _ _).trans (congrArg _ ((map_pow (preHom x) _ _).trans
      (congrArg (· ^ m) (Category.comp_id x))))
  refine (PrimNorm.lbIso_iff L.isLB _ _ _ _).2 ((PrimNorm.prod_square_id _ _ (PrimNorm.cls L.L)).trans
    (Eq.trans ?_ (PrimNorm.prod_square_id _ _ (PrimNorm.cls L.L)).symm))
  show PrimNorm.diff₂ (PrimNorm.ptCls L.L (G ⊗ G)) _ _ = PrimNorm.diff₂ (PrimNorm.ptCls L.L (G ⊗ G)) _ _
  rw [q, q, PrimNorm.diff₂_mul_left hc, PrimNorm.diff₂_mul_right hc, PrimNorm.diff₂_ptCls_adj L.isLB h, p,
    PrimNorm.diff₂_comm (fst G G) (snd G G ^ m), p, PrimNorm.diff₂_comm (snd G G)]

theorem adj_pull {B B' : Scheme.{0}} (f : B' ⟶ B) (G : Over B) [GrpObj G] [IsCommMonObj G] {L : LB G.left}
    {L' : LB ((Over.pullback f).obj G).left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hb : LBIso L' (L.pull (pullback.fst G.hom f))) (a a' : G ⟶ G)
    (ha : LBIso (cubeLB G ![fst G G ≫ a, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ a'] L)) :
    LBIso (cubeLB ((Over.pullback f).obj G) ![fst _ _ ≫ (Over.pullback f).map a, snd _ _] L')
      (cubeLB ((Over.pullback f).obj G) ![fst _ _, snd _ _ ≫ (Over.pullback f).map a'] L') := by
  have h := isGrpPullback_pullback G f
  let G' := (Over.pullback f).obj G
  let φ : G'.left ⟶ G.left := pullback.fst G.hom f
  have pa : ∀ (w : G ⟶ G) {T : Over B'} (x : T ⟶ G'),
      pushPt h.1.w (x ≫ (Over.pullback f).map w) = pushPt h.1.w x ≫ w := fun w T x =>
    Over.OverMorphism.ext (by
      have hw : ((Over.pullback f).map w).left ≫ φ = φ ≫ w.left := pullback.lift_fst _ _ _
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hw, Category.assoc])
  have hB : (L.pull φ).IsLB := pull_isLB hL φ
  have h₁ : LBIso (cubeLB G' ![fst G' G' ≫ (Over.pullback f).map a, snd G' G'] (L.pull φ))
      (cubeLB G' ![fst G' G', snd G' G' ≫ (Over.pullback f).map a'] (L.pull φ)) := by
    let U := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))
    refine LBIso.chartPull (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) ha
    · fin_cases i
      · exact (pa _ _).trans (by simp [U])
      · simp [U]
    · fin_cases i
      · simp [U]
      · exact (pa _ _).trans (by simp [U])
  exact LBIso.trans (DVR.linComb_isLB L' hL' _ _) (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _)
    (GlobalTheory.PowPrimitive.lbIso_linComb hb _ _)
    (LBIso.trans (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _) h₁
      (GlobalTheory.PowPrimitive.lbIso_linComb hb.symm _ _))

end Adjoint

theorem exists_add_injective {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (h h' : X →+ X) :
    ∃ m : ℕ, (Function.Injective fun x => h x + m • x) ∧ Function.Injective fun x => h' x + m • x := by
  have key : ∀ h : X →+ X, {m : ℕ | ¬ Function.Injective fun x => h x + m • x}.Finite := fun h => by
    let f : Module.End ℤ X := h.toIntLinearMap
    have fin : (f.charpoly.rootSet ℤ).Finite := Polynomial.rootSet_finite _ _
    refine Set.Finite.subset (fin.preimage (f := fun m : ℕ => -(m : ℤ)) (fun a _ b _ e => by simpa using e)) ?_
    intro m hm
    simp only [Function.Injective, Set.mem_setOf_eq, not_forall] at hm
    obtain ⟨x, y, e, hxy⟩ := hm
    have ev : f.HasEigenvector (-(m : ℤ)) (x - y) := by
      refine ⟨Module.End.mem_eigenspace_iff.2 ?_, sub_ne_zero.2 hxy⟩
      show h (x - y) = _
      rw [map_sub, neg_smul, natCast_zsmul, smul_sub]
      linear_combination (norm := abel) e
    have := Module.End.aeval_apply_of_hasEigenvector (p := f.charpoly) ev
    rw [LinearMap.aeval_self_charpoly, LinearMap.zero_apply] at this
    refine (Polynomial.mem_rootSet).2 ⟨f.charpoly_monic.ne_zero, ?_⟩
    simpa [sub_ne_zero.2 hxy] using this.symm
  obtain ⟨m, hm⟩ := ((key h).union (key h')).exists_notMem
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hm
  exact ⟨m, hm⟩

end GlobalTheory.Balanced
end
