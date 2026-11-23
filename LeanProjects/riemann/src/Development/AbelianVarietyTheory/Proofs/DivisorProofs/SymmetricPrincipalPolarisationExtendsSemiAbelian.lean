import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallHeightOneExistsDvdMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIntegralOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfInfLeInfRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenUnitMulSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonOfNotNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianGermPrimeIdealMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianGermInjectiveClosedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionSquareUnitsLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSquareFactorizationSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsAmplePowSectionsCuttingOutClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianMulNatSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowFlatLocallyQuasiFinite
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecLinOfSecScal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdScalB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitOfAssociated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoSmulPolarisationClassGenericDiagonalDoublingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEqMulSqOfFaithfullyFlatHeightOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.SymExtend

open GlobalTheory.CechPic

theorem stalkMap_comp_base {R : Type} [CommRing R] {G : Over (Sp R)} (f : G ⟶ G) (x : G.left) :
    (f.left.stalkMap x).hom.comp ((G.left.presheaf.germ ⊤ (f.left x) trivial).hom.comp ((G.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) =
      (G.left.presheaf.germ ⊤ x trivial).hom.comp ((G.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) := by
  ext a
  have e := Scheme.Hom.germ_stalkMap_apply f.left ⊤ x trivial
    (G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
  refine e.trans ?_
  conv_rhs => rw [← Over.w f]
  rfl

theorem exists_open_unit_mul_sq (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hA : AdmBase R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (L2 : LB G.left) (h2 : L2.IsLB) (h : L2.Sec)
    (Lθ : LB (pullback G.hom (jK R))) (hθ : Lθ.IsLB) (θ : Lθ.Sec) (hc : (∀ j i, ∃ w : Γ(pullback G.hom (jK R), pullback.fst G.hom (jK R) ⁻¹ᵁ L2.U j ⊓ Lθ.U i)ˣ, ((pullback G.hom (jK R)).presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) ^ 2 = (w : Γ(pullback G.hom (jK R), pullback.fst G.hom (jK R) ⁻¹ᵁ L2.U j ⊓ Lθ.U i)) * ((pullback G.hom (jK R)).presheaf.map (homOfLE inf_le_left).op).hom (((pullback.fst G.hom (jK R)).app (L2.U j)).hom (h.f j)))) (hs : (∀ (x' : G.left) (k : L2.ι), ((𝟙 G) ^ 2 : G ⟶ G).left x' ∈ L2.U k → gs ((𝟙 G) ^ 2 : G ⟶ G).left x' (L2.U k) (h.f k) ≠ 0 ∧ ∃ (u : (G.left.presheaf.stalk x')ˣ) (g : G.left.presheaf.stalk x'), gs ((𝟙 G) ^ 2 : G ⟶ G).left x' (L2.U k) (h.f k) = u * g ^ 2))
    (x : G.left) (hx : G.hom x = closedPoint R) :
    ∃ V : G.left.Opens, x ∈ V ∧ ∃ a : Γ(G.left, V), a ≠ 0 ∧ ∀ j, ∃ u : Γ(G.left, V ⊓ L2.U j)ˣ, (G.left.presheaf.map (homOfLE inf_le_right).op).hom (h.f j) = (u : Γ(G.left, V ⊓ L2.U j)) * (G.left.presheaf.map (homOfLE inf_le_left).op).hom a ^ 2 := by
  have hfl := (GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow _ G hG 2 two_ne_zero).1
  have hsu := GlobalTheory.SemiAbSurj.surjective_pow _ G hG 2 two_ne_zero
  generalize ((𝟙 G) ^ 2 : G ⟶ G) = f at hs hfl hsu
  obtain ⟨x', rfl⟩ := f.left.surjective x
  have hx' : G.hom x' = closedPoint R := by
    rw [← hx, ← Scheme.Hom.comp_apply, Over.w f]
  obtain ⟨hD, hN, hIC⟩ := GlobalTheory.SquareNear.stalk_props R hA G hG (f.left x')
  obtain ⟨hD', hN', hIC'⟩ := GlobalTheory.SquareNear.stalk_props R hA G hG x'
  obtain ⟨k, hk⟩ := exists_chart h2 (f.left x')
  obtain ⟨hne, u, g, hug⟩ := hs x' k hk
  rw [gs_stalkMap _ _ _ hk, gs_eq (𝟙 G.left) (f.left x') _ hk] at hne hug
  let _ := (f.left.stalkMap x').hom.toAlgebra
  have : Module.Flat (G.left.presheaf.stalk (f.left x')) (G.left.presheaf.stalk x') := Flat.stalkMap f.left x'
  have : IsLocalHom (algebraMap (G.left.presheaf.stalk (f.left x')) (G.left.presheaf.stalk x')) :=
    inferInstanceAs (IsLocalHom (f.left.stalkMap x').hom)
  have : Module.FaithfullyFlat (G.left.presheaf.stalk (f.left x')) (G.left.presheaf.stalk x') :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hne₀ : (G.left.presheaf.germ (L2.U k) (f.left x') hk).hom (h.f k) ≠ 0 := fun e =>
    hne ((congrArg (f.left.stalkMap x').hom e).trans (map_zero _))
  have hsq : ∃ (u : (G.left.presheaf.stalk x')ˣ) (g : G.left.presheaf.stalk x'),
      algebraMap (G.left.presheaf.stalk (f.left x')) (G.left.presheaf.stalk x')
        ((G.left.presheaf.germ (L2.U k) (f.left x') hk).hom (h.f k)) = u * g ^ 2 := ⟨u, g, hug⟩
  have hinj := GlobalTheory.Mum.LocalInj.base_to_stalk_injective R hA G hG (f.left x')
  have hpr := GlobalTheory.Mum.ideal_map_stalk_isPrime_of_closedPoint R hA G hG (f.left x') hx
  have hpr' := GlobalTheory.Mum.ideal_map_stalk_isPrime_of_closedPoint R hA G hG x' hx'
  have hhor := GlobalTheory.SqHorizontal.horizontal R hA G hG L2 h Lθ hθ θ hc (f.left x') k hk
  rw [← stalkMap_comp_base f x'] at hpr'
  generalize ((G.left.presheaf.germ ⊤ (f.left x') trivial).hom.comp ((G.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) = σ at hinj hpr hpr' hhor
  have Hp : ∀ p : Ideal (G.left.presheaf.stalk (f.left x')), p.IsPrime → p.height = 1 →
      ∃ a b c : G.left.presheaf.stalk (f.left x'), b ∉ p ∧ c ∉ p ∧
        b * (G.left.presheaf.germ (L2.U k) (f.left x') hk).hom (h.f k) = c * a ^ 2 := by
    intro p hp h1
    by_cases hq : Ideal.comap σ p = ⊥
    · exact hhor p hp hq
    · have hqp : (Ideal.comap σ p).IsPrime := Ideal.comap_isPrime _ p
      have hP := hpr _ hqp
      have heq : Ideal.map σ (Ideal.comap σ p) = p := by
        by_contra hne'
        have hlt := lt_of_le_of_ne (Ideal.map_comap_le (f := σ) (K := p)) hne'
        have h1' : (Ideal.map σ (Ideal.comap σ p)).height < 1 :=
          (Ideal.height_strict_mono_of_isPrime hlt).trans_le h1.le
        rw [ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot] at h1'
        exact hq ((Ideal.map_eq_bot_iff_of_injective hinj).1 h1')
      refine GlobalTheory.T.exists_mul_eq_mul_sq_of_faithfullyFlat_height_one _ _ _ hne₀ hsq p hp h1 ?_
      have := hpr' _ hqp
      rwa [← Ideal.map_map, heq] at this
  obtain ⟨u₀, a, hua⟩ := isUnit_mul_sq_of_faithfullyFlat _ (G.left.presheaf.stalk x') _ hne₀ hsq Hp
  have ha : a ≠ 0 := by
    rintro rfl
    apply hne₀
    rw [hua]
    simp
  exact GlobalTheory.Mum.unit_mul_sq_spread G.left L2 h (f.left x') k hk u₀ a ha hua

theorem exists_unit_mul_of_sq_sec {X : Scheme.{0}} [IsIntegral X] [GlobalTheory.IsNormalScheme X] (W : X.Opens)
    {s t : Γ(X, W)} (c : Γ(X, W)ˣ) (ht : Nonempty W → t ≠ 0) (h : s ^ 2 = c * t ^ 2) :
    ∃ w : Γ(X, W)ˣ, s = w * t := by
  by_cases hW : Nonempty W
  · have ht := ht hW
    have h1 : t ∣ s := (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 ⟨c, by rw [h, mul_comm]⟩
    have h2 : s ∣ t := (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1
      ⟨(c⁻¹ : Γ(X, W)ˣ), by rw [h, mul_right_comm, Units.mul_inv, _root_.one_mul]⟩
    obtain ⟨w, hw⟩ := associated_of_dvd_dvd h1 h2
    exact ⟨w, by rw [← hw, mul_comm]⟩
  · obtain rfl : W = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hW ⟨⟨x, hx⟩⟩
    exact ⟨1, Subsingleton.elim _ _⟩

theorem res_ne_zero {X : Scheme.{0}} [IsIntegral X] {V W : X.Opens} (hW : W ≤ V) {a : Γ(X, V)} (ha : a ≠ 0)
    [Nonempty W] : (X.presheaf.map (homOfLE hW).op).hom a ≠ 0 := fun h0 =>
  ha (map_injective_of_isIntegral X (homOfLE hW) (h0.trans (map_zero _).symm))

theorem res_mem_nonZeroDivisors {X : Scheme.{0}} [IsIntegral X] {V W : X.Opens} (hW : W ≤ V) {a : Γ(X, V)}
    (ha : a ≠ 0) : (X.presheaf.map (homOfLE hW).op).hom a ∈ nonZeroDivisors Γ(X, W) := by
  by_cases hn : Nonempty W
  · exact mem_nonZeroDivisors_of_ne_zero (res_ne_zero hW ha)
  · obtain rfl : W = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hn ⟨⟨x, hx⟩⟩
    rw [Subsingleton.elim ((X.presheaf.map (homOfLE hW).op).hom a) 1]
    exact Submonoid.one_mem _

theorem extends_near (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hA : AdmBase R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (L2 : LB G.left) (h2 : L2.IsLB) (h : L2.Sec)
    (Lθ : LB (pullback G.hom (jK R))) (hθ : Lθ.IsLB) (θ : Lθ.Sec) (hc : (∀ j i, ∃ w : Γ(pullback G.hom (jK R), pullback.fst G.hom (jK R) ⁻¹ᵁ L2.U j ⊓ Lθ.U i)ˣ, ((pullback G.hom (jK R)).presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) ^ 2 = (w : Γ(pullback G.hom (jK R), pullback.fst G.hom (jK R) ⁻¹ᵁ L2.U j ⊓ Lθ.U i)) * ((pullback G.hom (jK R)).presheaf.map (homOfLE inf_le_left).op).hom (((pullback.fst G.hom (jK R)).app (L2.U j)).hom (h.f j)))) (hs : (∀ (x' : G.left) (k : L2.ι), ((𝟙 G) ^ 2 : G ⟶ G).left x' ∈ L2.U k → gs ((𝟙 G) ^ 2 : G ⟶ G).left x' (L2.U k) (h.f k) ≠ 0 ∧ ∃ (u : (G.left.presheaf.stalk x')ˣ) (g : G.left.presheaf.stalk x'), gs ((𝟙 G) ^ 2 : G ⟶ G).left x' (L2.U k) (h.f k) = u * g ^ 2)) :
    ∃ (O : G.left.Opens) (N : LB O.toScheme), (∀ g : G.left, G.hom g = closedPoint R → g ∈ O) ∧ N.IsLB ∧
      LBIso (N.pull (pullback.fst O.ι (pullback.fst G.hom (jK R)))) (Lθ.pull (pullback.snd O.ι (pullback.fst G.hom (jK R)))) := by
  have hY := fun (x : {x : G.left // G.hom x = closedPoint R}) =>
    exists_open_unit_mul_sq R hA G hG L2 h2 h Lθ hθ θ hc hs x.1 x.2
  choose V hxV a ha hu using hY
  obtain ⟨hsq, hθa⟩ := GlobalTheory.SqGlue.main R hA G hG L2 h2 h _ θ hc _ V a ha hu
  haveI : IsIntegrallyClosed R := hA.2.2.1
  haveI : IsNoetherianRing R := hA.1
  haveI : Smooth G.hom := hG.smooth
  haveI : GeometricallyConnected G.hom := hG.geomConnected
  haveI : IsIntegral G.left := GlobalTheory.isIntegral_left_of_isSemiAbelian G
  haveI : GlobalTheory.IsNormalScheme G.left := GlobalTheory.isNormalScheme_of_smooth G.hom
  haveI : IsIntegral (pullback G.hom (jK R)) := GlobalTheory.isIntegral_pullback_of_smooth G.hom (jK R)
  haveI : GlobalTheory.IsNormalScheme (pullback G.hom (jK R)) := GlobalTheory.isNormalScheme_of_smooth (pullback.snd G.hom (jK R))
  have hgen : ∀ k, ((pullback.fst G.hom (jK R)).app (V k)).hom (a k) ≠ 0 := fun k h0 =>
    ha k (GlobalTheory.ExpInt.generic_app_injective G (V k) (h0.trans (map_zero _).symm))
  obtain ⟨O, N, hO, hN, hiso⟩ := GlobalTheory.LocalEqGlue.exists_lb_of_localEq G.left _ (pullback.fst G.hom (jK R)) Lθ θ _ V a
    (fun k W hW => res_mem_nonZeroDivisors hW (ha k)) (fun k W hW => res_mem_nonZeroDivisors hW (hgen k))
    (fun k l => by
      obtain ⟨c, hc⟩ := hsq k l
      exact exists_unit_mul_of_sq_sec _ c (fun _ => res_ne_zero _ (ha l)) hc)
    (fun k i => by
      obtain ⟨w, hw⟩ := hθa k i
      exact exists_unit_mul_of_sq_sec _ w (fun _ => res_ne_zero _ (hgen k)) hw)
  exact ⟨O, N, fun g hg => hO ⟨g, hg⟩ (hxV ⟨g, hg⟩), hN, hiso⟩

theorem exists_odd_sec {X : Scheme.{0}} [Nonempty X] {L : LB X} (hL : GlobalTheory.IsAmpleLB L) :
    ∃ (t : ℕ) (θ : (lbPow L (2 * t + 1)).Sec) (i : (lbPow L (2 * t + 1)).ι), θ.f i ≠ 0 := by
  obtain ⟨t, ht⟩ := Filter.eventually_atTop.1 (GlobalTheory.CutOutSections.eventually_isGenerated_lbPow hL)
  obtain ⟨θ, hθ⟩ := (ht (2 * t + 1) (by omega)).exists_mem (Classical.arbitrary X)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hθ
  refine ⟨t, θ, i, fun e => ?_⟩
  rw [e, Scheme.basicOpen_zero] at hi
  exact hi

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ L₁ : LB G.left, L₁.IsLB ∧ LBIso (L₁.pull (pullback.fst G.hom (jK R))) (A.L.pull gen.hom.left) := by
  intro R _ _ _ hA G _ _ hG A gen hgen PP hext
  have hL : (A.L.pull gen.hom.left).IsLB := LB.isLB_pull A.isLB _
  have hP : (PP.pull (lift (𝟙 G) (𝟙 G) : G ⟶ G2 G).left).IsLB := LB.isLB_pull hext.1 _
  obtain ⟨h2c, φ, hφ, h4c⟩ := GlobalTheory.T.two_smul_polarisation_class_generic_diagonal_doubling R G A gen hgen PP hext _ _ hL hP rfl rfl
  haveI : Smooth G.hom := hG.smooth
  haveI : GeometricallyConnected G.hom := hG.geomConnected
  haveI : IsIntegral (pullback G.hom (jK R)) := GlobalTheory.isIntegral_pullback_of_smooth G.hom (jK R)
  haveI : IsIso gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map gen.hom))
  have hamp : GlobalTheory.IsAmpleLB (X := pullback G.hom (jK R)) (A.L.pull gen.hom.left) :=
    (GlobalTheory.isAmpleLB_of_relAmple_of_isAffine A.A A.isLB A.ample).pull_of_isAffineHom gen.hom.left
  have hK : Function.Surjective (pullback.snd G.hom (jK R)).appTop.hom := by
    have e : pullback.snd G.hom (jK R) = gen.hom.left ≫ A.A.hom := (Over.w gen.hom).symm
    haveI : IsIso gen.hom.left.appTop := inferInstanceAs (IsIso (gen.hom.left.app ⊤))
    rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso gen.hom.left.appTop).2.comp (GlobalTheory.ExpansionTotal.globalFns _ A.A A.isAb).2
  obtain ⟨t, θ, hθ⟩ := exists_odd_sec hamp
  generalize (PP.pull (lift (𝟙 G) (𝟙 G) : G ⟶ G2 G).left) = P at hP h2c
  have hLθ := GlobalTheory.isLB_lbPow hL (2 * t + 1)
  have hL2 := GlobalTheory.isLB_lbPow hP (2 * t + 1)
  have eθ := cls_lbPow hL (2 * t + 1) hLθ
  obtain ⟨h, hc, hs⟩ := exists_sec_sq_of_double R hA G hG hK _ hLθ θ hθ _ hL2
    (by rw [cls_lbPow hP, map_nsmul, ← h2c, smul_comm]; exact congrArg (2 • ·) eθ) φ hφ
    (by
      refine (congrArg (pull φ) eθ).trans (Eq.trans ?_ (congrArg (4 • ·) eθ).symm)
      rw [map_nsmul, smul_comm]
      exact congrArg ((2 * t + 1) • ·) h4c)
  obtain ⟨O, N, hO, hN, hiso⟩ := extends_near R hA G hG _ hL2 h _ hLθ θ hc hs
  obtain ⟨N', hN', eN'⟩ := cls_surj (cls N hN - t • pull O.ι (cls P hP))
  have e₁ := (cls_eq_iff (LB.isLB_pull hN _) (LB.isLB_pull hLθ _)).2 hiso
  rw [cls_pull hN, cls_pull hLθ] at e₁
  obtain ⟨L', hL', hI⟩ := GlobalTheory.Mum.lb_extends_of_extLam R hA G hG _ PP hL hext O hO N' hN'
    ((cls_eq_iff (LB.isLB_pull hN' _) (LB.isLB_pull hL _)).1 (by
      rw [cls_pull hN', eN', map_sub, e₁, map_nsmul, ← pull_comp, pullback.condition, pull_comp, ← h2c]
      refine Eq.trans ?_ (cls_pull hL _ _).symm
      refine (congrArg (fun z => pull (pullback.snd O.ι (pullback.fst G.hom (jK R))) z - _) eθ).trans ?_
      rw [map_nsmul, map_nsmul, smul_smul, add_smul, one_smul, mul_comm t 2, add_sub_cancel_left]))
  exact ⟨L', hL', hI.symm⟩

end GlobalTheory.SymExtend
