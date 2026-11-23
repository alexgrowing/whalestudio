import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsE8IsSharpBasis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescentStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGoodThetaComplexClassE8SharpStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.E8SharpObjectFibreFromComplexCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyThetaFamilyOverOpenClosureStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueMapToThetaFamilyOpenPartStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaClosureOpenFamilyQprojFlatReducedExtStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeRingKrullDimThetaFamilyGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfFlatDedekindTangentLeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBoundStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIffEighthPowerPullbackStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChangeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerShapeDependsOnlyOnMatricesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEighthPowerPrincipalSiegelOfDenseStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmpleStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCyclotomicBaseRingInvertingPrimeStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SiegelFromSharp

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_id (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _

def restrictBase {h k : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} (j : B →+* B') (hj : j ζ = ζ')
    {S : Scheme.{0}} {s' : S ⟶ Sp B'} (c : SiegPre h k ζ' s') : SiegPre h k ζ (s' ≫ spMap j) where
  A := c.A
  ab := c.ab
  P := c.P
  isLB := c.isLB
  rig₁ := c.rig₁
  rig₂ := c.rig₂
  symm := c.symm
  lev := c.lev
  lev_add := c.lev_add
  lev_tors := c.lev_tors
  geom := by
    intro K _ _ x β z hx hz
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ s')
    refine c.geom K x φ.hom z hφ.symm ?_
    have : spMap (φ.hom.comp j) = spMap β := by
      rw [← spMap_comp, ← hx, ← Category.assoc, ← hφ]; rfl
    have e : φ.hom.comp j = β := congrArg CommRingCat.Hom.hom (Spec.map_injective this)
    rw [hz, ← e, ← hj]; rfl

theorem finiteType_of_isQProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsQProjOver f) :
    QuasiCompact f ∧ LocallyOfFiniteType f := by
  obtain ⟨N, i, hi, hq, rfl⟩ := h
  have := isProper_str R N
  exact ⟨inferInstance, inferInstance⟩

theorem dirMap_base {o K : Type} [CommRing o] [Field K] {r : ℕ} (β : o →+* K) (lam : (Fin r → K) →ₗ[K] K) :
    spMap (dirMap lam) ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) =
      constPt (spMap (dirMap lam)) ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) := by
  simp only [constPt, Category.assoc, spMap_comp]
  congr 1
  ext x <;> simp [dirMap]

theorem constPt_comp {K : Type} [Field K] {X Y : Scheme.{0}} (x : Sp (DualNumber K) ⟶ X) (f : X ⟶ Y) :
    constPt x ≫ f = constPt (x ≫ f) := by
  simp only [constPt, Category.assoc]

theorem nonempty_siegelFamily (L1 : Out.Laws) (L2 : Out.Laws2)
    (L3 : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
    {h g p n N' : ℕ} (hh : 1 ≤ h) (hp : p.Prime) {W : Matrix (Fin 8) (Fin 8) ℤ} {J : Type} [Finite J]
    {a : J → Matrix (Fin 8) (Fin 8) ℤ} {w w' : J}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} (hW : IsE8 W) (hbas : IsSharpBasis W bas)
    (hw : (W + W.transpose) * a w = W) (hw' : (W + W.transpose) * a w' = W.transpose)
    (hu : ∀ u v, ∃ j, a j = Matrix.single u v 1) {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ}
    (h3 : 3 ≤ N') (hodd : Odd N') {o : Type} [CommRing o] {b : TBase o (N' ^ 2)} {em : o →+* ℂ}
    (j : o →+* ZP p (N' ^ 2)) (har : ArBase em) (hj : j (b.ζ : o) = zetaZP p (N' ^ 2))
    (hconst : ∀ (K : Type) [Field K] (y : Sp (DualNumber K) ⟶ Sp (ZP p (N' ^ 2))), y = constPt y)
    (good : GoodClass em (SharpClass (b := b) W a bas em) Mat κ w w' (h * (h + 1) / 2))
    (F : WFam n em (SharpClass (b := b) W a bas em) Mat κ)
    (rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s'), IsReduced S →
      Dense (fromSet em (SharpClass (b := b) W a bas em) t) → t.FibShape Mat κ →
      ∃! f : S ⟶ F.U.toScheme, f ≫ F.U.ι ≫ F.Y.s = s' ∧ TMap t F.univ f) :
    Nonempty (SiegelFamily h p (N' ^ 2)) := by
  have hk : Odd (N' ^ 2) := hodd.pow
  have hk3 : 3 ≤ N' ^ 2 := by nlinarith
  have hζ : b.ζ ^ N' ^ 2 = 1 := by
    refine Units.ext (har.2.2 ?_)
    rw [Units.val_pow_eq_pow_val, map_pow, (b.prim ℂ em).pow_eq_one, Units.val_one, map_one]
  haveI : IsDedekindDomain o := har.1
  haveI : CharZero o := RingHom.charZero em
  obtain ⟨hq, hflat, hred, htan⟩ := GlobalTheory.T.thetaClosureOpenFamily_qproj_flat_reduced_ext L1 L2 o g n N' J b em _ Mat κ F hodd
  obtain ⟨hqc, hft⟩ := finiteType_of_isQProjOver (hq.resolve_right (not_not.2 inferInstance))
  haveI : IsLocallyNoetherian F.U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (F.U.ι ≫ F.Y.s)
  obtain ⟨c, hc, hsharp⟩ := GlobalTheory.T.exists_eighthPower_principalSiegel_of_dense L1 L2 L3 h g W J a bas hW hbas hu _ o b em _ _ F.univ hk F.dense

  have pull : ∀ (S : Scheme.{0}) (s : S ⟶ Sp o) (c' : SiegPre h (N' ^ 2) (b.ζ : o) s) (t : TObj g (N' ^ 2) J b s)
      (f : S ⟶ F.U.toScheme), c'.Principal → IsSharp W a bas t c' → (SiegPB c' c f ↔ TMap t F.univ f) := by
    intro S s c' t f h1 h2
    have := GlobalTheory.T.siegelPullback_iff_eighthPower_pullback L1 L2 h g W J a bas hW hbas _ o b _ _ _ _ c c' F.univ t f hc h1 hsharp h2
    exact ⟨this.1, this.2 hu⟩
  have hsm : SmoothOfRelativeDimension (h * (h + 1) / 2) (F.U.ι ≫ F.Y.s) := by
    refine GlobalTheory.T.smoothOfRelativeDimension_of_flat_dedekind_tangent_le o _ _ _ har.2.1 hflat hft
      (GlobalTheory.T.le_ringKrullDim_thetaFamily_genericFibre L1 L2 g n N' J Mat κ w w' o b em _ _ F h3 hodd har good) ?_
    intro K _ _ r β x hx hlam
    obtain ⟨p1, p2, -⟩ := GlobalTheory.T.siegelPre_pullback_principal_ringChange h (N' ^ 2) o o (b.ζ : o) (b.ζ : o) (RingHom.id o) _ _ _
      (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β)) x rfl (by rw [spMap_id, Category.comp_id, hx])
    obtain ⟨c', hc'⟩ := p1 c
    have hp' := p2 c c' hc' hc
    obtain ⟨t', ht'⟩ := GlobalTheory.T.exists_thetaObject_eighthPower_principalSiegel L1 L2 h g W J a bas hW hbas _ o b _ _ c' hk hk3 hζ hp'
    have hm : TMap t' F.univ x := (pull _ _ c' t' x hp' ht').1 hc'
    refine GlobalTheory.T.siegelFamily_tangent_dimension_bound L1 L2 L3 h g W J a bas hW hbas w w' hw hw' _ o b K r β t' c' hp' ht' ?_
    intro lam t'' m1 m2
    refine hlam lam ?_
    rw [← constPt_comp]
    refine htan (DualNumber K) _ _ _ t'' ?_ (((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ F.univ t' t'').2 x _ hm).1 m1)
      (((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ F.univ t' t'').2 x _ hm).1 m2)
    rw [Category.assoc, Category.assoc, hx]
    exact dirMap_base β lam
  obtain ⟨q1, q2, -⟩ := GlobalTheory.T.siegelPre_pullback_principal_ringChange h (N' ^ 2) o _ (b.ζ : o) _ j _ _ (F.U.ι ≫ F.Y.s)
    (pullback.snd (F.U.ι ≫ F.Y.s) (spMap j)) (pullback.fst _ _) hj pullback.condition
  obtain ⟨u, hupb⟩ := q1 c
  have hup := q2 c u hupb hc
  refine ⟨⟨pullback (F.U.ι ≫ F.Y.s) (spMap j), pullback.snd _ _,
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hsm, inferInstance, u, hup, ?_, ?_⟩⟩
  · intro C O _ _ _ _ _ _ _ _ hO hpC β c₁ hgen hamp
    have hp₁ : c₁.Principal := GlobalTheory.T.principal_siegel_of_generic_principal_special_ample L1 L2 h _ hk hk3 _ _ C O hO p hp hpC β c₁ hgen hamp
    have hp₀ : (restrictBase j hj c₁).Principal := hp₁
    obtain ⟨t, ht⟩ := GlobalTheory.T.exists_thetaObject_eighthPower_principalSiegel L1 L2 h g W J a bas hW hbas _ o b _ _ (restrictBase j hj c₁) hk hk3 hζ hp₀
    have hfrom := GlobalTheory.T.fromC_sharpClass_fibre_of_charZero L1 L2 h g W J a w w' bas hW hbas hw hw' hu N' o b em har _ _ t _ hp₀ ht C
      (spMap (algebraMap O C))
    haveI : IsDomain O := hO.1.isDomain _
    have hdense : Dense (fromSet em (SharpClass (b := b) W a bas em) t) := by
      have hd : DenseRange (PrimeSpectrum.comap (algebraMap O C)) := by
        rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot _).1 hO.1]
        exact bot_le
      exact Dense.mono (fun z hz => ⟨C, inferInstance, _, hz, hfrom⟩) hd
    have hshape : t.Shape Mat κ := by
      obtain ⟨_, _, _, _, _, _, _, tc, -, -, -, -, -, htc⟩ := hfrom
      have hs := (good.shape tc htc).1
      obtain ⟨cc, hcc, hcs⟩ := htc
      exact GlobalTheory.T.eighthPower_shape_depends_only_on_matrices L1 L2 h g W J a bas hW hbas _ o b Mat κ _ _ _ _ cc _ tc t hh inferInstance hcc hp₀ hcs ht hs
    obtain ⟨f, ⟨hf, hm⟩, -⟩ := rep _ _ t inferInstance hdense fun K _ _ x t' hx =>
      (GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w w' _ _ _ _ x t t' hx).1 hshape
    have hpb : SiegPB c₁ c f := (pull _ _ (restrictBase j hj c₁) t f hp₀ ht).2 hm
    refine ⟨pullback.lift f (spMap β) hf, pullback.lift_snd _ _ _, ?_⟩
    refine ((GlobalTheory.T.siegelPullback_id_comp_cancel h _ _ _ _ _ _ _ _ _ _ _ _ _ c u c₁ _ _).2 hupb).2 ?_
    rwa [pullback.lift_fst]
  · intro K _ x c₁ m1 m2
    have hp₁ : c₁.Principal := (GlobalTheory.T.siegelPre_pullback_principal_ringChange h (N' ^ 2) _ _ _ _ (RingHom.id _) _ _ _ _ x rfl
      (by rw [spMap_id, Category.comp_id])).2.1 u c₁ m1 hup
    have hp₀ : (restrictBase j hj c₁).Principal := hp₁
    obtain ⟨t, ht⟩ := GlobalTheory.T.exists_thetaObject_eighthPower_principalSiegel L1 L2 h g W J a bas hW hbas _ o b _ _ (restrictBase j hj c₁) hk hk3 hζ hp₀
    have n1 := (pull _ _ (restrictBase j hj c₁) t _ hp₀ ht).1
      (((GlobalTheory.T.siegelPullback_id_comp_cancel h _ _ _ _ _ _ _ _ _ _ _ _ _ c u c₁ _ _).2 hupb).1 m1)
    have n2 := (pull _ _ (restrictBase j hj c₁) t _ hp₀ ht).1
      (((GlobalTheory.T.siegelPullback_id_comp_cancel h _ _ _ _ _ _ _ _ _ _ _ _ _ c u c₁ _ _).2 hupb).1 m2)
    have e : x ≫ pullback.snd _ _ = constPt x ≫ pullback.snd _ _ := by
      rw [constPt_comp]; exact hconst K _
    refine pullback.hom_ext (htan (DualNumber K) _ _ _ t ?_ n1 n2) e
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, e, Category.assoc]

theorem exists_siegelFamily : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → N0 := by
  intro L1 L2 L3 L4 h p n hh hp hn hodd hnp
  obtain ⟨W, hW, hb⟩ := exists_isE8_isSharpBasis
  obtain ⟨bas, hbas⟩ := hb h
  have hinv : (W + W.transpose) * (W + W.transpose)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [hW.2]; exact isUnit_one)
  let a : (Fin 8 × Fin 8) ⊕ Bool → Matrix (Fin 8) (Fin 8) ℤ :=
    Sum.elim (fun uv => Matrix.single uv.1 uv.2 1)
      (fun e => (W + W.transpose)⁻¹ * (if e then W else W.transpose))
  have hw : (W + W.transpose) * a (.inr true) = W := by
    change _ * (_ * W) = W
    rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have hw' : (W + W.transpose) * a (.inr false) = W.transpose := by
    change _ * (_ * W.transpose) = W.transpose
    rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have hu : ∀ u v, ∃ j, a j = Matrix.single u v 1 := fun u v => ⟨.inl (u, v), rfl⟩
  obtain ⟨Mat, κ, hcl⟩ := GlobalTheory.T.isGoodThetaComplexClass_E8Sharp L1 L2 L3 L4 h _ W _ a _ _ bas hW hbas hw hw' hu
  obtain ⟨j₁, h₁⟩ := hcl n hn hodd
  obtain ⟨j₂, h₂⟩ := GlobalTheory.T.nonempty_thetaFamily_over_open_closure L1 L2 _ _ Mat κ n (.inr true) (.inr false) hn hodd
  obtain ⟨j₃, h₃⟩ := GlobalTheory.T.existsUnique_map_to_thetaFamily_openPart L1 L2 _ _ Mat κ n (.inr true) (.inr false) hn hodd
  obtain ⟨m, hm⟩ : ∃ m, m = j₁ + j₂ + j₃ + 1 := ⟨_, rfl⟩
  have hn3 : 3 ≤ n := by
    have := hn.two_le
    obtain ⟨e, he⟩ := hodd
    omega
  have h3 : 3 ≤ n ^ m := hn3.trans (Nat.le_self_pow (by omega) n)
  obtain ⟨o, _, b, em, j, har, hj, -, hconst⟩ :=
    GlobalTheory.T.exists_cyclotomic_base_ring_inverting_prime n (m * 2) p ((n ^ m) ^ 2) hn hp hnp (by omega) (pow_mul n m 2).symm
  have good := h₁ m (by omega) _ rfl o b em
  obtain ⟨F⟩ := h₂ m (by omega) o b em _ _ har good
  refine ⟨m * 2, hn3.trans (Nat.le_self_pow (by omega) n), ?_⟩
  rw [pow_mul]
  exact nonempty_siegelFamily L1 L2 L3 hh hp hW hbas hw hw' hu h3 hodd.pow j har hj hconst good F
    (h₃ m (by omega) o b em _ _ har good F)

end GlobalTheory.SiegelFromSharp
end
