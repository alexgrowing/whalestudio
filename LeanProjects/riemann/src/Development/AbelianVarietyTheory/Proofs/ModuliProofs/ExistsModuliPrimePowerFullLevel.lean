import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPrimitiveRootMapOfNatCastNeZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibresStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsWeilIsRoot
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELOfTmap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TangentLeDimStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverBaseChangeAndFiniteRestrict
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfDimOfDirectionsLe
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGrpPullbackOfIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ActOfGenerators
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeRingKrullDimThetaFamilyGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyThetaFamilyOverOpenClosureStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueMapToThetaFamilyOpenPartStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaClosureOpenFamilyQprojFlatReducedExtStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGoodThetaComplexClassUnitaryFullLevelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectFibreFromComplexCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEquivStdSymp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MinimalAndDimLe

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.FullLevel

theorem finiteDimensional_KA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    FiniteDimensional ℚ (KA l) := by
  have hA := l.A_pos
  refine IntermediateField.finiteDimensional_adjoin ?_
  intro x hx
  rcases hx with rfl | hx
  · have h2 : H.rt0 ^ 2 = algebraMap ℚ ℂ (-(H.d : ℚ)) := by
      rw [H.sqrt_neg_disc_sq]; simp
    have hi : IsIntegral ℚ (H.rt0 ^ 2) := by rw [h2]; exact isIntegral_algebraMap
    exact IsIntegral.of_pow two_pos hi
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    have hz : IsPrimitiveRoot (zeta l.A) l.A := by
      unfold zeta; exact Complex.isPrimitiveRoot_exp l.A hA.ne'
    refine IsIntegral.of_pow hA ?_
    rw [hz.pow_eq_one]; exact isIntegral_one

private theorem constPt_comp' {k : Type} [Field k] {X Y : Scheme.{0}} (x : Sp (DualNumber k) ⟶ X)
    (f : X ⟶ Y) : constPt (x ≫ f) = constPt x ≫ f := by
  simp only [constPt, Category.assoc]

theorem moduli_of_family (hL : Out.Laws) (hL2 : Out.Laws2)
    (hth : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {g : ℕ} {J : Type} (a : J → 𝓞 E)
    (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (hbas : IsSympBasis D bas) (hw : a w = H.w0)
    (hw' : a w' = H.bar H.w0) (hgen : Subring.closure (Set.range a) = ⊤) (l : Level H) (hMA : l.M ∣ l.A)
    {o : Type} [CommRing o] [IsDomain o] [Algebra o (KA l)] [hfr : IsFractionRing o (KA l)] (b : TBase o l.A) (ρ : o)
    (hρ : algebraMap o (KA l) ρ = (baseKA l).ρ) (hζ : algebraMap o (KA l) (b.ζ : o) = (baseKA l).ζ)
    {U : Scheme.{0}} (sU : U ⟶ Sp o) (tU : TObj g l.A J b sU) (τU : SAB H U) (hq : IsQProjOver sU)
    (hτ : IsPEL D a bas ρ tU τU)
    (hdim : ∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ U), IsOpenImmersion x →
      x ≫ sU = spMap (algebraMap o R) → ∀ q ∈ minimalPrimes (FractionRing o ⊗[o] R),
        (D.dim : WithBot ℕ∞) ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q))
    (hinj : ∀ (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ U) (s' : Sp R ⟶ Sp o) (t : TObj g l.A J b s'),
      x ≫ sU = y ≫ sU → TMap t tU x → TMap t tU y → x = y)
    (hrep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (t : TObj g l.A J b s') (τ : SAB H S), IsReduced S →
      IsPEL D a bas ρ t τ → (∀ (K : Type) [Field K], (Sp K ⟶ S) → CharZero K) →
      ∃! f : S ⟶ U, f ≫ sU = s' ∧ TMap t tU f) :
    Nonempty (Moduli D l) := by
  classical
  obtain ⟨X, p, sX, sq⟩ : ∃ (X : Scheme.{0}) (p : X ⟶ U) (sX : X ⟶ Sp (KA l)),
      IsPullback p sX sU (spMap (algebraMap o (KA l))) := ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  have hqX : IsQProjOver sX := isQProjOver_of_isPullback_spMap _ sq hq
  have hlft : LocallyOfFiniteType sX := lft_of_qproj hqX
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : FiniteDimensional ℚ (KA l) := finiteDimensional_KA l
  haveI : Algebra.IsAlgebraic ℚ (KA l) := Algebra.IsAlgebraic.of_finite ℚ (KA l)
  obtain ⟨tX, htX⟩ := tObj_pull o g l.A J b U X sU (sX ≫ spMap (algebraMap o (KA l))) p tU sq.w
  obtain ⟨τX, hτX⟩ := exists_isPEL_of_tmap E H D g J a bas l.A o b ρ U X sU
    (sX ≫ spMap (algebraMap o (KA l))) tU tX τU p sq.w htX hτ
  obtain ⟨ob, hob⟩ := ThetaToObj.exists_obj_under hL hL2 E H D g J a bas l o b ρ X sX tX τX hMA hbas hfr hρ hζ
    (Or.inr inferInstance) hτX
  have hsep : ∀ (R : Type) [CommRing R] [IsLocalRing R] (x1 x2 : Sp R ⟶ X) (s' : Sp R ⟶ Sp o)
      (t' : TObj g l.A J b s'), TMap t' tX x1 → TMap t' tX x2 → x1 ≫ sX = x2 ≫ sX → x1 = x2 := by
    intro R _ _ x1 x2 s' t' h1 h2 hs
    refine sq.hom_ext ?_ hs
    refine hinj R _ _ s' t' ?_ (TMap.comp h1 htX) (TMap.comp h2 htX)
    rw [Category.assoc, Category.assoc, sq.w, ← Category.assoc, hs, Category.assoc]
  refine ⟨{ X := X, s := sX, qproj := hqX, smooth := ?_, univ := ob, rep := ?_, unram := ?_ }⟩
  · refine smoothOfRelativeDimension_of_dim_of_directions_le (KA l) X sX D.dim hlft ?_ ?_
    · intro R _ _ x hx _ q hq'
      haveI : IsOpenImmersion (x ≫ sq.isoPullback.hom) := inferInstance
      exact dim_generic_chart sU _ hdim R (x ≫ sq.isoPullback.hom) q hq'
    · intro K' _ _ r β x hxs hdir
      have hρsq : ρ ^ 2 = -(H.d : o) := by
        apply IsFractionRing.injective o (KA l)
        rw [map_pow, hρ, (baseKA l).ρ_sq]; simp
      have hb : x ≫ sX ≫ spMap (algebraMap o (KA l)) =
          spMap ((algebraMap K' (TrivSqZeroExt K' (Fin r → K'))).comp (β.comp (algebraMap o (KA l)))) := by
        rw [← Category.assoc, hxs, ← spMap_comp]
      obtain ⟨t1, ht1⟩ := tObj_pull o g l.A J b X _ (sX ≫ spMap (algebraMap o (KA l))) _ x tX hb
      obtain ⟨τ1, hτ1⟩ := exists_isPEL_of_tmap E H D g J a bas l.A o b ρ X _
        (sX ≫ spMap (algebraMap o (KA l))) _ tX t1 τX x hb ht1 hτX
      haveI : CharZero K' := charZero_of_hom (spMap β)
      refine T.tangent_le_dim_alt hL hL2 hth E H D g J a w w' bas l.A o b ρ K' r (β.comp (algebraMap o (KA l))) t1 τ1
        hw hw' hρsq hτ1 ?_
      intro lam t' h1 h2
      apply hdir lam
      rw [constPt_comp']
      refine hsep (DualNumber K') _ _ _ t' (TMap.comp h1 ht1) (TMap.comp h2 ht1) ?_
      simpa only [constPt_comp'] using eq_constPt ((spMap (dirMap lam) ≫ x) ≫ sX)
  · intro S s' hS o'
    obtain ⟨t', ht'u, ht'p⟩ := ObjTheta.exists_tObj hL hL2 E H D g J a bas l (KA l) o (baseKA l) b ρ
      (algebraMap o (KA l)) S s' o' hbas hρ hζ
    have hch : ∀ (K : Type) [Field K], (Sp K ⟶ S) → CharZero K := fun K _ y => charZero_of_hom (y ≫ s')
    obtain ⟨f, ⟨hf1, hf2⟩, hfu⟩ := hrep S (s' ≫ spMap (algebraMap o (KA l))) t' o'.t hS ht'p hch
    have hiff := fun (f' : S ⟶ X) => UnderMap.objMap_iff_tMap hL hL2 E H D g J a bas l (KA l) o (baseKA l) b X S
      sX s' (sX ≫ spMap (algebraMap o (KA l))) (s' ≫ spMap (algebraMap o (KA l))) ob o' tX t' f' hMA hgen hob ht'u
    refine ⟨sq.lift f s' hf1, ⟨sq.lift_snd _ _ _, (hiff _).mpr (TMap.cancel htX (by rw [sq.lift_fst]; exact hf2))⟩, ?_⟩
    rintro f2 ⟨hf2s, hm⟩
    have htm : TMap t' tX f2 := (hiff f2).mp hm
    apply sq.hom_ext
    · rw [sq.lift_fst]
      apply hfu
      refine ⟨?_, TMap.comp htm htX⟩
      rw [Category.assoc, sq.w, ← Category.assoc, hf2s]
    · rw [sq.lift_snd, hf2s]
  · intro k _ x o' hm1 hm2
    obtain ⟨t', ht'u, -⟩ := ObjTheta.exists_tObj hL hL2 E H D g J a bas l (KA l) o (baseKA l) b ρ
      (algebraMap o (KA l)) _ (x ≫ sX) o' hbas hρ hζ
    have hiff := fun (f' : Sp (DualNumber k) ⟶ X) => UnderMap.objMap_iff_tMap hL hL2 E H D g J a bas l (KA l) o
      (baseKA l) b X _ sX (x ≫ sX) (sX ≫ spMap (algebraMap o (KA l))) ((x ≫ sX) ≫ spMap (algebraMap o (KA l)))
      ob o' tX t' f' hMA hgen hob ht'u
    refine hsep (DualNumber k) x (constPt x) _ t' ((hiff x).mp hm1) ((hiff _).mp hm2) ?_
    simpa only [constPt_comp'] using eq_constPt (x ≫ sX)

theorem exists_generating_family {E : Type} [Field E] [NumberField E] (u u' : 𝓞 E) :
    ∃ (J : Type) (_ : Finite J) (a : J → 𝓞 E) (w w' : J), a w = u ∧ a w' = u' ∧ Subring.closure (Set.range a) = ⊤ := by
  classical
  let bs := NumberField.RingOfIntegers.basis E
  refine ⟨Option (Option (Module.Free.ChooseBasisIndex ℤ (𝓞 E))), inferInstance,
    fun i => Option.elim i u (fun i' => Option.elim i' u' (fun k => bs k)), none, some none, rfl, rfl, ?_⟩
  rw [eq_top_iff]
  intro x hx0
  clear hx0
  have hx : x ∈ Submodule.span ℤ (Set.range bs) := by rw [bs.span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    exact Subring.subset_closure ⟨some (some k), rfl⟩
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul n y _ hy => exact zsmul_mem hy n

end GlobalTheory.ZM.FullLevel

open GlobalTheory.ZM.FullLevel in

theorem GlobalTheory.ZM.exists_moduli_prime_power_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n : ℕ), 1 ≤ D.p + D.q → n.Prime → Odd n → ∃ j : ℕ, ∀ l : Level H, l.M = n → l.A = (n ^ j) ^ 2 → Nonempty (Moduli D l) := by
  intro hL hL2 hth hU E _ _ _ H D n hpq hn hodd
  obtain ⟨bas, hbas⟩ := ZM.exists_isSympBasis E H D
  obtain ⟨J, hJ, a, w, w', hw, hw', hgen⟩ := exists_generating_family (E := E) H.w0 (H.bar H.w0)
  obtain ⟨Mat, κ, hGood⟩ := T.isGoodThetaComplexClass_unitaryFullLevel hL hL2 hth hU E H D _ J a w w' bas hpq hbas hw hw' hgen
  obtain ⟨j₁, hj₁⟩ := hGood n hn hodd
  obtain ⟨j₂, hj₂⟩ := T.nonempty_thetaFamily_over_open_closure hL hL2 _ J Mat κ n w w' hn hodd
  obtain ⟨j₃, hj₃⟩ := T.existsUnique_map_to_thetaFamily_openPart hL hL2 _ J Mat κ n w w' hn hodd
  refine ⟨max (max j₁ j₂) (max j₃ 1), ?_⟩
  intro l hM hA
  have hj1 : j₁ ≤ max (max j₁ j₂) (max j₃ 1) := le_max_of_le_left (le_max_left _ _)
  have hj2 : j₂ ≤ max (max j₁ j₂) (max j₃ 1) := le_max_of_le_left (le_max_right _ _)
  have hj3 : j₃ ≤ max (max j₁ j₂) (max j₃ 1) := le_max_of_le_right (le_max_left _ _)
  have hj0 : 1 ≤ max (max j₁ j₂) (max j₃ 1) := le_max_of_le_right (le_max_right _ _)
  generalize max (max j₁ j₂) (max j₃ 1) = j at hj1 hj2 hj3 hj0 hA
  obtain ⟨o, _, b, em, ρ, _, har, hfr, hem, hρ, hζ⟩ := IntegersAway.exists_tBase_fractionRing E H l
  cases l
  dsimp only at hA hM
  subst hA
  have hM' := hM.symm
  subst hM'
  haveI := har.1
  have hemρ : em ρ = H.rt0 := by rw [← hem, hρ]; rfl
  have h3n : 3 ≤ n := by
    have h2 := hn.two_le
    have hne : n ≠ 2 := by
      rintro rfl
      exact (Nat.not_odd_iff_even.mpr even_two) hodd
    omega
  have hN3 : 3 ≤ n ^ j := le_trans h3n (Nat.le_self_pow (by omega) n)
  have hoddN : Odd (n ^ j) := hodd.pow
  have hGd := hj₁ j hj1 (n ^ j) rfl o b em ρ hemρ
  obtain ⟨F⟩ := hj₂ j hj2 o b em _ D.dim har hGd
  obtain ⟨hqU, -, hredU, hinjU⟩ := T.thetaClosureOpenFamily_qproj_flat_reduced_ext hL hL2 o _ n (n ^ j) J b em _ Mat κ F hoddN
  have hqU' : IsQProjOver (F.U.ι ≫ F.Y.s) := hqU.resolve_right (not_not.mpr inferInstance)
  haveI := hredU
  haveI := lft_of_qproj hqU'
  haveI : IsLocallyNoetherian F.U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (F.U.ι ≫ F.Y.s)
  obtain ⟨τU, hτU⟩ := T.exists_isPELTriple_of_dense_fibres hL hL2 hth E H D _ J a bas w w' hpq hbas hw hw' hgen _ o b em ρ F.U.toScheme
    (F.U.ι ≫ F.Y.s) F.univ hemρ har.2.2 F.dense
  refine moduli_of_family hL hL2 hth D a w w' bas hbas hw hw' hgen _
    (dvd_pow (dvd_pow_self n (by omega)) two_ne_zero) b ρ hρ hζ (F.U.ι ≫ F.Y.s) F.univ τU hqU' hτU
    (T.le_ringKrullDim_thetaFamily_genericFibre hL hL2 _ n (n ^ j) J Mat κ w w' o b em _ D.dim F hN3 hoddN har hGd) hinjU ?_
  intro S s' t τ hS hP hch
  refine hj₃ j hj3 o b em _ D.dim har hGd F S s' t hS ?_ ?_
  · refine Dense.mono ?_ dense_univ
    intro p _
    haveI := hch _ (S.fromSpecResidueField p)
    exact ⟨_, inferInstance, S.fromSpecResidueField p,
      ⟨IsLocalRing.closedPoint _, Scheme.fromSpecResidueField_apply p _⟩,
      T.pelObject_fibre_from_complex_charZero hL hL2 E H D _ J a w w' bas hpq hbas hw hw' hgen (n ^ j) o b em ρ hemρ har S s' t τ hP _ _⟩
  · intro K _ _ x t' hT
    haveI := hch K x
    obtain ⟨K₀, _, β, i, e, t₀, tx, tc, -, -, htx, htx0, htc0, hC⟩ :=
      T.pelObject_fibre_from_complex_charZero hL hL2 E H D _ J a w w' bas hpq hbas hw hw' hgen (n ^ j) o b em ρ hemρ har S s' t τ hP K x
    have s1 := (hGd.shape tc hC).1
    have s2 := ((shape_prim_pull_and_descend o _ _ J b Mat κ w w' _ _ _ _ _ t₀ tc htc0).2.2 K₀ rfl
      inferInstance inferInstance).1 s1
    have s3 := (shape_prim_pull_and_descend o _ _ J b Mat κ w w' _ _ _ _ _ t₀ tx htx0).1 s2
    have htt : TMap t' tx (𝟙 _) := TMap.cancel htx (by rw [Category.id_comp]; exact hT)
    exact (shape_prim_pull_and_descend o _ _ J b Mat κ w w' _ _ _ _ _ tx t' htt).1 s3
