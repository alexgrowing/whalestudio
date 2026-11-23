import Mathlib
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantValuationsUnitsEveryCosetStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPrimGenerator
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicBaseEmbedsValuationAlgebraicClosure
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoUniformisationsOfIsoDegenerationDataStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegDataIsPullDeg
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatementsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelEndomorphismsSpreadOverBasicOpen
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AbelianSchemeHomExtendsDedekindOfIsGrpPullbackAl
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianHomExtensionOfLawsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnitStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasThStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SmoothOfRelativeDimensionOfFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ThetaCrit

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap (f'.comp f) = spMap f' ≫ spMap f := Spec.map_comp _ _

theorem exists_model (hS : GlobalTheory.SS.SemistablePol) {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k}
    (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V)
    (t : TObj g k J b (spMap (algebraMap V K) ≫ spMap β)) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (φ : V →+* W)
      (ψ : K →+* FractionRing W) (tK : TObj g k J b (spMap (algebraMap W (FractionRing W)) ≫ spMap φ ≫ spMap β))
      (G : Over (Sp W)) (_ : GrpObj G) (gen : (Over.pullback (Out.jK W)).obj G ≅ tK.A),
      IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap W (FractionRing W)).comp φ ∧
      IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ TMap tK t (spMap ψ) ∧ IsMonHom gen.hom ∧ GlobalTheory.SS.SplitSemi W G := by
  obtain ⟨W, L, _, _, _, _, _, _, _, _, hcomm, -, hloc, hc, G, _, ⟨e, he⟩, hG⟩ := hS V K ‹_› t.pol
  let ε : L →+* FractionRing W := (IsLocalization.algEquiv (nonZeroDivisors W) L (FractionRing W) : L →+* _)
  let ψ : K →+* FractionRing W := ε.comp (algebraMap K L)
  have hε : ε.comp (algebraMap W L) = algebraMap W (FractionRing W) :=
    RingHom.ext (IsLocalization.algEquiv (nonZeroDivisors W) L (FractionRing W)).commutes
  have hψ : ψ.comp (algebraMap V K) = (algebraMap W (FractionRing W)).comp (algebraMap V W) := by
    rw [RingHom.comp_assoc, ← hcomm, ← RingHom.comp_assoc, hε]
  obtain ⟨tK, hK⟩ := GlobalTheory.tObj_pull o g k J b _ _ _
    (spMap (algebraMap W (FractionRing W)) ≫ spMap (algebraMap V W) ≫ spMap β) (spMap ψ) t
    (by rw [← Category.assoc, ← spMap_comp, hψ, spMap_comp, Category.assoc])
  obtain ⟨χ, hχ, -⟩ := id hK
  have e₁ : spMap ε ≫ spMap (algebraMap W L) = Out.jK W := by rw [← spMap_comp, hε]
  have a₁ := ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback t.pol.A _)).congr (Category.id_comp _) rfl
  let m : ((Over.pullback (Out.jK W)).obj G).left ⟶ ((Over.pullback (spMap (algebraMap W L))).obj G).left :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap ε) (by rw [Category.assoc, e₁, pullback.condition])
  have a₂ : IsGrpPullback ((Over.pullback (Out.jK W)).obj G) ((Over.pullback (spMap (algebraMap W L))).obj G)
      (spMap ε) m := (isGrpPullback_pullback G _).cancel
    ((isGrpPullback_pullback G (Out.jK W)).congr e₁.symm (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  obtain ⟨gen, hgen, -⟩ := grpPullback_iso ((a₂.comp a₁).congr (spMap_comp _ _).symm rfl) hχ
  exact ⟨W, inferInstance, inferInstance, inferInstance, algebraMap V W, ψ, tK, G, inferInstance, gen, hloc, hψ, hc, hK,
    hgen, hG⟩

section
open Out UT NormTheta

theorem isThetaPtOver_of_eq {S : Scheme.{0}} (P : PolAV S) (m : ℕ) {T : Over S} {I : Type} (x : I → (T ⟶ P.A))
    (w : I → Γ(T.left, ⊤)) {k : ℤ} (hk : k = (m : ℤ) ^ 2) (th : LB.Sec (LPow P.A P.L 1 T))
    (s₁ : LB.Sec (LPow P.A P.L k T))
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![k, -1]))
    (τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ P.A).left) (fun _ => k)))
    (U : I → ThetaGrp P.A P.L k T) (s₂ : I → LB.Sec (LPow P.A P.L k T))
    (h₁ : IsGenSec P.A P.L 1 th) (h₂ : α.IsGen) (h₃ : τ.IsGen)
    (h₄ : IsTwistPull P.A P.L (mulT P.A T m) (snd T P.A ^ m) (lift_snd _ _) k 1 α th s₁)
    (h₅ : ∀ i, SymLift P.A P.L k (m ^ 2) (x i) (U i)) (h₆ : ∀ i, IsActOf P.A P.L k (U i) s₁ (s₂ i))
    (h₇ : ∀ i, IsValueAt P.A P.L k (s₂ i) 1 τ (w i)) : IsThetaPtOver P m x w := by
  subst hk
  exact ⟨th, s₁, α, τ, U, s₂, w, 1, h₁, h₂, h₃, h₄, h₅, h₆, h₇, fun _ => (_root_.one_mul _).symm⟩

theorem isThetaPt_of_normalised (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R]
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) {F : Type} [Field F] [Algebra (FractionRing R) F]
    {ρ : LB.Gen (A.L.pull (eSec A.A))} (hρ : ρ.IsGen) {m : ℕ} (hm : Odd m) (hu : (m : F) ≠ 0) {th : SecA A F 1}
    (hth : IsGenSec A.A A.L 1 th) {I : Type} (i₀ : I) (x : I → (TFK (R := R) F ⟶ A.A)) (c : I → F)
    (h : ∀ i, ∃ σ, ThC A ρ m th (x i) σ (c i)) :
    IsThetaPt A m x (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) := by
  have hL := A.isLB
  let T := TFK (R := R) F
  choose σ α s₁ θ hα hn hs₁ hθ ht hc using h
  have es : ∀ i, s₁ i = s₁ i₀ := fun i => by
    have ea := gen_unique hL (fst T A.A).left (ptSecT A.A 1).left ptSec_fst
      (CommPairing.surj_fst hG A.isAb T) (hα i) (hα i₀) (fun y J hJ => by
        have a := (val_corr hJ (hn i) (𝟙 _)).trans (val_corr hJ (hn i₀) (𝟙 _)).symm
        rwa [val_pull hJ, val_pull hJ, Category.id_comp] at a)
    exact sec_ext (sec_ext_val hL fun y J hJ =>
      (ThetaLin.sval_of_isTwistPull A.A (hs₁ i) _ y hJ).trans
        (Eq.trans (by rw [ea _ _ y J hJ]) (ThetaLin.sval_of_isTwistPull A.A (hs₁ i₀) _ y hJ).symm))
  have H : IsThetaPtOver A m x (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) :=
    isThetaPtOver_of_eq A m x _ (Nat.cast_pow m 2) th (s₁ i₀) (α i₀) (rigT A.A A.L ρ T _) θ σ hth (hα i₀)
      (rigT_isGen hρ _) (hs₁ i₀) hθ (fun i => es i ▸ ht i)
      (fun i => ThetaCoord.isValueAt_of_sv (T := T) (w := 1) hL (rigT_isGen hρ _) (hc i))
  let r : T ⟶ overRes (T := T) ⊤ := Over.homMk T.left.topIso.inv (by
    show T.left.topIso.inv ≫ (⊤ : T.left.Opens).ι ≫ T.hom = T.hom
    rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp])
  have hh : r ≫ overResι (T := T) ⊤ = 𝟙 T := Over.OverMorphism.ext T.left.toIso_inv_ι
  have hi : overResι (T := T) ⊤ ≫ r = 𝟙 _ := by
    haveI : Mono (overResι (T := T) ⊤) := Over.mono_of_mono_left _ (hk := inferInstanceAs (Mono (⊤ : T.left.Opens).ι))
    rw [← cancel_mono (overResι (T := T) ⊤), Category.assoc, hh, Category.comp_id, Category.id_comp]
  refine ⟨hm, ?_, fun _ => ⟨⊤, trivial, ThetaCoord.isThetaPtOver_pull A H _ r hi⟩⟩
  have := (IsUnit.mk0 _ hu).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  rwa [map_natCast] at this

end

theorem subsingleton_of_divisible {X : Type} [AddCommGroup X] [Module.Free ℤ X] {d : ℕ} (hd : 2 ≤ d)
    (h : ∀ x : X, ∃ y, x = d • y) : Subsingleton X := by
  let b := Module.Free.chooseBasis ℤ X
  have : IsEmpty (Module.Free.ChooseBasisIndex ℤ X) := ⟨fun i => by
    obtain ⟨y, hy⟩ := h (b i)
    have e := congrArg (fun x => b.repr x i) hy
    simp only [Module.Basis.repr_self, Finsupp.single_eq_same, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul] at e
    have := Int.eq_one_of_mul_eq_one_right (Int.natCast_nonneg d) e.symm
    omega⟩
  exact b.repr.injective.subsingleton

attribute [local instance] TorusExt.gtGroup in

theorem subsingleton_characters (h₁ : Out.Laws) (h₂ : Out.Laws2) (hT : GlobalTheory.ZH.UTorsSt) {o : Type} [CommRing o]
    {g n j : ℕ} {J : Type} {b : TBase o ((n ^ j) ^ 2)} (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [CharZero W] (hc : IsAdicComplete (IsLocalRing.maximalIdeal W) W) {s : Sp (FractionRing W) ⟶ Sp o}
    (t : TObj g ((n ^ j) ^ 2) J b s) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (D : Out.DegData W (IsLocalRing.maximalIdeal W)) (U : Out.Unif (IsLocalRing.maximalIdeal W) D t.pol G)
    (hn : 2 ≤ n) (ho : Odd n) (hj : 2 ≤ j) (hu : IsUnit ((n ^ j : ℕ) : W)) (v : Ix g ((n ^ j) ^ 2) → W)
    (hv : t.HasTh (𝟙 _) (fun a => algebraMap W (FractionRing W) (v a)))
    (hC : Coset n (n ^ j) v (IsLocalRing.maximalIdeal W)) : Subsingleton D.toPre.X := by
  obtain ⟨hL, k₁, k₂, k₃, k₄⟩ := GlobalTheory.T.uniformization_laws_and_expansion_statements
  have hA : Out.AdmBase W (IsLocalRing.maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  choose Q hQ using DVR.QForm.exists_QVal hϖ D
  let F := AlgebraicClosure (FractionRing W)
  obtain ⟨ν, hν⟩ := GlobalTheory.adic_base_embeds_valuation_algebraic_closure.2 W ϖ hϖ
  obtain ⟨ρ, hρ⟩ := t.pol.rigid
  obtain ⟨w₀, hw⟩ := (GlobalTheory.UT.EvalZero.value_at_origin hL W _ hA D t.pol G hG U F).2.1 ρ hρ
  obtain ⟨th, ϑ, hE, hP, hth⟩ := GlobalTheory.UT.exists_prim_generator hL k₁ k₂ k₃ k₄ W hc ϖ hϖ D Q hQ F ν hν t.pol G hG U w₀ hw.1
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hd : n ^ (i + 1) / n = n ^ i := by rw [pow_succ, Nat.mul_div_cancel _ (by omega)]
  have hm : Odd (n ^ (i + 1)) := ho.pow
  have hM : 1 ≤ (n ^ (i + 1)) ^ 2 := pow_pos hm.pos 2
  haveI : NeZero ((n ^ (i + 1)) ^ 2) := ⟨by omega⟩
  haveI := t.ab.comm
  obtain ⟨ua₁, ua₂⟩ := GlobalTheory.T.theta_constant_valuations_units_every_coset hL k₁ k₂ k₃ k₄ W hc ϖ hϖ D Q hQ F ν hν t.pol G hG U w₀ ρ hw th ϑ hE hP _ hm hu
  obtain ⟨f, f₁, f₂, -, f₄, -⟩ := hT W hc t.pol G D U F _ hM
  let z : Out.TFK (R := W) F ⟶ Out.baseOver (Sp (FractionRing W)) :=
    Over.homMk (spMap (algebraMap (FractionRing W) F)) (Category.comp_id _)
  let pt : Fin (2 * g) → (Out.TFK (R := W) F ⟶ t.A) := fun l => z ≫ t.pt l
  have hpt : ∀ l, pt l ^ ((n ^ (i + 1)) ^ 2) = 1 := fun l => by
    rw [← MonObj.comp_pow, t.torsion, MonObj.comp_one]
  let x : Ix g ((n ^ (i + 1)) ^ 2) → (Out.TFK (R := W) F ⟶ t.A) := fun a => ThetaCoord.lab pt a
  have hx : (fun a => z ≫ t.lab a) = x := funext fun a => VVRank.comp_linComb z _ _
  have onto : ∀ y : Out.TFK (R := W) F ⟶ t.A, y ^ ((n ^ (i + 1)) ^ 2) = 1 → ∃ a, x a = y := fun y hy =>
    (t.bij F _ y hy).exists
  have uq := fun a => GlobalTheory.existsUnique_thetaConst hL W t.pol F ρ hρ _ hm th (x a) (ThetaCoord.lab_pow hpt a)
  choose q hq hq' using uq
  have hF : ((n ^ (i + 1) : ℕ) : F) ≠ 0 := by
    have := (hu.map (algebraMap W (FractionRing W))).map (algebraMap (FractionRing W) F)
    rw [map_natCast, map_natCast] at this
    exact this.ne_zero
  have hc₁ : t.HasTh (spMap (algebraMap (FractionRing W) F)) (fun a => (q a).2) := by
    have := isThetaPt_of_normalised h₁.globalFns t.pol hρ hm hF hth 0 x (fun a => (q a).2) fun a => ⟨_, hq a⟩
    rw [← hx] at this
    exact this
  have hc₂ := GlobalTheory.hasTh_baseChange h₂ o g _ J b _ s t _ F (algebraMap (FractionRing W) F) _ _ hv
  rw [Category.comp_id] at hc₂
  have unit : ∀ a, v a ∉ IsLocalRing.maximalIdeal W →
      ν (algebraMap (FractionRing W) F (algebraMap W (FractionRing W) (v a))) = 0 := fun a ha => by
    obtain ⟨y, hy⟩ : IsUnit (v a) := by_contra ha
    rw [← hy]; exact DVR.GC.v_alg_unit hν y
  obtain ⟨c₀, hc₀⟩ := hC 0
  obtain ⟨u, hu'⟩ := GlobalTheory.T.thetaConstants_unique_up_to_unit h₁ h₂ o g _ J b _ s t F _ _ _ hc₂ hc₁
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, rfl⟩)
      (((by_contra hc₀ : IsUnit _).map (algebraMap W (FractionRing W))).map (algebraMap (FractionRing W) F)))
  have tors : ∀ p, f p ^ ((n ^ (i + 1)) ^ 2) = 1 := fun p => ((f₁ p _).2 rfl w₀ hw.1).1
  have hB := D.tau_bimult
  have u₀ : ν u = 0 := by
    refine le_antisymm ?_ ?_
    · obtain ⟨p', x', σ, c, -, hp', -, hx', h0⟩ := ua₂ n hn (dvd_pow_self n (by omega)) (TorusExt.qkZero hB F _) _ rfl
        ((f₁ _ _).2 rfl)
      obtain ⟨a, rfl⟩ := onto x' (hp' w₀ hw.1).1
      have e : c = (q a).2 := congrArg Prod.snd (hq' a (σ, c) hx')
      rw [e, hu' a, ν.map_mul] at h0
      exact (le_add_of_nonneg_right (DVR.GC.v_alg_nonneg hϖ hν _)).trans h0.le
    · obtain ⟨p, hp⟩ := f₂ _ (ThetaCoord.lab_pow hpt (0 + (n ^ (i + 1) / n) • c₀))
      have := (ua₁ p _ _ _ ((f₁ _ _).2 hp.symm) (hq _)).1 0 fun χ => div_nonneg (by
        rcases eq_or_ne (n ^ (i + 1) • χ + p.y) 0 with h | h
        · rw [h, DVR.QForm.Q_zero hϖ D hQ]; simp
        · exact_mod_cast zero_le_one.trans (DVR.QForm.Q_pos hϖ D hQ h)) (Nat.cast_nonneg _)
      rwa [hu', ν.map_mul, unit _ hc₀, add_zero] at this
  have comb : ∀ (d : ℕ) (p p' : Out.QkPt D.toPre F ((n ^ (i + 1)) ^ 2)),
      ∃ r, f r = f p * f p' ^ d ∧ r.y = p.y + d • p'.y := fun d p p' => by
    induction d with
    | zero => exact ⟨p, by rw [pow_zero, _root_.mul_one], by rw [zero_smul, add_zero]⟩
    | succ d ih =>
      obtain ⟨r, r₁, r₂⟩ := ih
      refine ⟨TorusExt.qkAdd hB r p', ?_, ?_⟩
      · rw [f₄ _ _ _ (TorusExt.qkAdd_qkAdd hB r p'), r₁, pow_succ (f p'), _root_.mul_assoc]
      · show r.y + p'.y = _
        rw [r₂, succ_nsmul, add_assoc]
  refine subsingleton_of_divisible (d := n ^ i) (hn.trans (Nat.le_self_pow (by omega) n)) fun χ => ?_
  obtain ⟨g₀, hg₀⟩ := (GlobalTheory.UT.gt_onto_divisible_kernel hL W _ hA D F).2.1 _ hM (TorusExt.iota hB F χ)
  let p := TorusExt.qkMk hB χ g₀ ((TorusExt.isNsmul_iff_eq _ _ _).1 hg₀).symm
  obtain ⟨a, ha⟩ := onto _ (tors p)
  obtain ⟨c, hc'⟩ := hC a
  obtain ⟨p', hp'⟩ := f₂ _ (ThetaCoord.lab_pow hpt c)
  obtain ⟨r, r₁, r₂⟩ := comb (n ^ (i + 1) / n) p p'
  have e : x (a + (n ^ (i + 1) / n) • c) = f r := by
    rw [r₁, hp', ← ha]
    exact (ThetaCoord.lab_add hpt _ _).trans (congrArg _ (ThetaCoord.lab_nsmul hpt _ _))
  obtain ⟨y, hy⟩ := (ua₁ r _ _ _ ((f₁ _ _).2 e) (hq _)).2 (by rw [hu', ν.map_mul, unit _ hc', u₀, add_zero])
  refine ⟨n • y - p'.y, ?_⟩
  rw [smul_sub, ← mul_smul, ← pow_succ, ← hy, r₂, hd]
  exact (add_sub_cancel_right _ _).symm

theorem exists_pol_model (h₁ : Out.Laws) (h₂ : Out.Laws2) (W : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] (hc : IsAdicComplete (IsLocalRing.maximalIdeal W) W)
    (A : Out.PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (D : Out.DegData W (IsLocalRing.maximalIdeal W)) (U : Out.Unif (IsLocalRing.maximalIdeal W) D A G)
    [Subsingleton D.toPre.X] :
    ∃ (P : Out.PolAV (Sp W)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (Out.jK W) φ ∧ LBIso A.L (P.L.pull φ) := by
  have hA : Out.AdmBase W (IsLocalRing.maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨O, hO, hψ⟩ := GlobalTheory.T.uniformization_laws_and_expansion_statements.1.2.2.2.2.psiOnExists W _ hA D
  obtain ⟨D', hD, -, -⟩ := GlobalTheory.exists_degData_isPullDeg h₁.polBaseChange h₁.globalFns W W _ _ (RingHom.id W)
    (Ideal.map_id _).le D O hψ (by
      rw [show Out.specOf (RingHom.id W) = 𝟙 _ from Spec.map_id _]; exact hO)
  have : Subsingleton D'.toPre.X := hD.xe.injective.subsingleton
  obtain ⟨A', χ, hχ₀, -, hm, c, hc'⟩ := h₁.polBaseChange _ _ (Out.jK W) D'.toPre.P
  have hχ : IsGrpPullback A'.A D'.toPre.P.A (Out.jK W) χ :=
    ⟨hχ₀, fun T x y x₀ y₀ hx hy => by
      rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hχ₀.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hχ₀.w y),
        ← hm]
      rfl⟩
  obtain ⟨eA, hA', e₁⟩ := grpPullback_iso (isGrpPullback_pullback D'.toPre.P.A (Out.jK W)) hχ
  have hw : LBIso (A'.L.pull eA.hom.left) (D'.toPre.P.L.pull (pullback.fst D'.toPre.P.A.hom (Out.jK W))) :=
    GenSpread.lbIso_pull_of_lbIso (LBIso.symm ⟨c, hc'⟩) _ e₁.symm
  let U' : Out.Unif (IsLocalRing.maximalIdeal W) D' A' D'.toPre.P.A := ⟨SelfUnif.selfPre D' A' eA hA' hw, fun k _ =>
    SelfUnif.expBij D' A' eA hA' hw h₁.globalFns (IsAdicComplete.le_jacobson_bot _) k⟩
  obtain ⟨ψ, bc, hψ', -, e₂, ⟨wL, hwL, -⟩⟩ := GlobalTheory.T.exists_iso_uniformisations_of_iso_degeneration_data h₁ h₂ W _ hA rfl D D' A A' G D'.toPre.P.A hG
    (isSemiAbelian_of_isAbelianScheme _ D'.toPre.P.isAb) U U' hD
  have l₁ : LBIso D'.toPre.P.L (U.LG.L.pull ψ.hom.left) := e₂ ▸ ⟨wL, hwL⟩
  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have : IsMonHom ψ.symm.hom := inferInstanceAs (IsMonHom ψ.inv)
  let φ₀ : A.A.left ⟶ G.left := U.gen.inv.left ≫ pullback.fst G.hom (Out.jK W)
  have g₀ : IsGrpPullback A.A G (Out.jK W) φ₀ :=
    ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G _)).congr (Category.id_comp _) rfl
  have i₁ : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have i₂ : ψ.inv.left ≫ ψ.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have l₂ : LBIso (A.L.pull (𝟙 _)) (U.LG.L.pull φ₀) := GenSpread.lbIso_pull_comp U.gen.inv.left i₁.symm rfl U.ext
  have l₃ : LBIso (D'.toPre.P.L.pull (φ₀ ≫ ψ.inv.left)) (U.LG.L.pull φ₀) :=
    GenSpread.lbIso_pull_of_lbIso l₁ _ (by rw [Category.assoc, i₂, Category.comp_id])
  have l₄ : LBIso A.L (A.L.pull (𝟙 _)) :=
    LBIso.chartPull (chartPullUnpull A.L _ rfl) (chartPullId _) (lbIso_refl (pull_isLB A.isLB _))
  exact ⟨D'.toPre.P, φ₀ ≫ ψ.inv.left, (g₀.comp (isGrpPullback_of_iso ψ.symm)).congr (Category.comp_id _) rfl,
    (l₄.trans A.isLB (pull_isLB A.isLB _) (pull_isLB U.LG.isLB _) l₂).trans A.isLB (pull_isLB U.LG.isLB _)
      (pull_isLB D'.toPre.P.isLB _) l₃.symm⟩

theorem exists_obj_model (h₁ : Out.Laws) (h₂ : Out.Laws2) {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k}
    (W K : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K] [Algebra W K] [IsFractionRing W K]
    (β : o →+* W) {sK : Sp K ⟶ Sp o} (hs : spMap (algebraMap W K) ≫ spMap β = sK) (t : TObj g k J b sK)
    (P : Out.PolAV (Sp W)) (φ : t.A.left ⟶ P.A.left) (hφ : IsGrpPullback t.A P.A (spMap (algebraMap W K)) φ)
    (hL : LBIso t.L (P.L.pull φ)) {s : Sp W ⟶ Sp o} (hs' : spMap β = s) :
    ∃ t' : TObj g k J b s, TMap t t' (spMap (algebraMap W K)) := by
  have := P.isAb.proper
  have hex : ValuativeCriterion.Existence P.A.hom :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed P.A.hom)).1
  have hp : ∀ i, ∃ p : Out.baseOver (Sp W) ⟶ P.A, (t.pt i).left ≫ φ = spMap (algebraMap W K) ≫ p.left := fun i => by
    obtain ⟨⟨l, l₁, l₂⟩⟩ := (hex
      { R := W, K := K, i₁ := (t.pt i).left ≫ φ, i₂ := 𝟙 _
        commSq := ⟨by
          rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w (t.pt i)]
          exact (Category.id_comp _).trans (Category.comp_id _).symm⟩ }).exists_lift
    exact ⟨Over.homMk l l₂, l₁.symm⟩
  choose p hp using hp
  have ha : ∀ i, ∃ a : P.A ⟶ P.A, (t.act i).left ≫ φ = φ ≫ a.left := fun i => by
    obtain ⟨a, -, ha, -⟩ := GlobalTheory.abelianScheme_hom_extends_dedekind_of_isGrpPullback (GlobalTheory.T.semiAbelianHomExtension_of_laws h₁ h₂) W K P.A P.A t.A t.A
      φ φ P.isAb P.isAb hφ hφ (t.act i) (t.hom i)
    exact ⟨a, ha⟩
  choose a ha using ha
  have hd := GlobalTheory.CM.smoothOfRelativeDimension_of_fibre W K _ P.A _ φ t.A.hom g P.isAb hφ.1 t.dim
  have : IsSchemeTheoreticallyDominant (spMap (algebraMap W K)) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ (IsFractionRing.injective W K)
  have : PreconnectedSpace (Sp W) := inferInstanceAs (PreconnectedSpace (PrimeSpectrum W))
  have hk : 0 < k := Nat.pos_of_ne_zero fun h0 => by
    have := b.unit.map β
    rw [h0, Nat.cast_zero, map_zero] at this
    exact not_isUnit_zero this
  subst hs'
  exact SpreadLevel.exists_extension h₁ (spMap β) (spMap (algebraMap W K)) hs hk
    (SpreadLevel.unitS_spMap_pow β b.ζ k (IsFractionRing.injective W K (by
      rw [map_pow, map_one]; exact (b.prim K ((algebraMap W K).comp β)).pow_eq_one)))
    t { P with g := g, smoothDim := hd } φ rfl hφ hL p hp a ha

theorem hasTh_unit_mul {o : Type} [CommRing o] {g N : ℕ} {J : Type} {b : TBase o (N ^ 2)} {S : Scheme.{0}}
    {s : S ⟶ Sp o} (t : TObj g (N ^ 2) J b s) {R : Type} [CommRing R] {x : Sp R ⟶ S} {v : Ix g (N ^ 2) → R}
    (h : t.HasTh x v) {r : R} (hr : IsUnit r) : t.HasTh x (fun a => r * v a) := by
  refine ⟨h.1, h.2.1, fun p => ?_⟩
  obtain ⟨V, hV, th, s₁, α, τ, U, s₂, w, u, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := h.2.2 p
  refine ⟨V, hV, th, s₁, α, τ, U, s₂, w,
    Out.unitRes (T := Over.mk x) V (hr.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).unit * u, a₁, a₂, a₃, a₄, a₅, a₆, a₇,
    fun i => ?_⟩
  refine (congrArg V.ι.appTop.hom (map_mul _ _ _)).trans ((map_mul _ _ _).trans ?_)
  exact (congrArg (fun q : Γ((Out.overRes (T := Over.mk x) V).left, ⊤) => (_ : Γ((Out.overRes (T := Over.mk x) V).left, ⊤)) * q)
    (a₈ i)).trans (_root_.mul_assoc _ _ _).symm

theorem hasTh_of_generic (h₁ : Out.Laws) (h₂ : Out.Laws2) {o : Type} [CommRing o] {g n N : ℕ} {J : Type}
    {b : TBase o (N ^ 2)} (W K : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K] [Algebra W K]
    [IsFractionRing W K] {s : Sp W ⟶ Sp o} {sK : Sp K ⟶ Sp o} (t' : TObj g (N ^ 2) J b s) (t : TObj g (N ^ 2) J b sK)
    (h : TMap t t' (spMap (algebraMap W K))) (hn : 2 ≤ n) (hN : n ∣ N) (v : Ix g (N ^ 2) → W)
    (hv : t.HasTh (𝟙 _) (fun a => algebraMap W K (v a))) (hu : ∃ a, IsUnit (v a)) : t'.HasTh (𝟙 _) v := by
  obtain ⟨R, _, x, v₀, hx, hp, h₀⟩ := GlobalTheory.ThetaLocal.exists_hasTh h₁ h₂ o g N J b _ s t' hv.1 (IsLocalRing.closedPoint W)
  have hr : Set.range (𝟙 (Sp W) :) ⊆ Set.range x := fun y _ =>
    (IsLocalRing.specializes_closedPoint y).mem_open x.isOpenEmbedding.isOpen_range hp
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (IsOpenImmersion.lift x (𝟙 (Sp W)) hr)
  have e : spMap σ.hom ≫ x = 𝟙 _ := (congrArg (· ≫ x) hσ).trans (IsOpenImmersion.lift_fac _ _ _)
  have hW := GlobalTheory.hasTh_baseChange h₂ o g N J b _ s t' R W σ.hom x v₀ h₀
  rw [e] at hW
  have hK := GlobalTheory.hasTh_baseChange h₂ o g N J b _ s t' W K (algebraMap W K) _ _ hW
  have hv' := (GlobalTheory.hasTh_iff_of_tmap o g N J b _ s t' _ sK t _ K _ _ h).1 hv
  rw [Category.comp_id] at hK
  rw [Category.id_comp] at hv'
  obtain ⟨c, hc⟩ := GlobalTheory.T.thetaCosetNonvanishing_of_hasTh h₁ h₂ o g N J b _ s t' n W _ _ _ hn hN hW
    (IsLocalRing.maximalIdeal.isMaximal W).isPrime 0
  obtain ⟨y, hy⟩ : IsUnit (σ.hom (v₀ (0 + (N / n) • c))) := by_contra hc
  obtain ⟨u, hu'⟩ := GlobalTheory.T.thetaConstants_unique_up_to_unit h₁ h₂ o g N J b _ s t' K _ _ _ hK hv'
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, rfl⟩) ((hy ▸ y.isUnit).map (algebraMap W K)))
  have key : ∀ a, v a = (v (0 + (N / n) • c) * ↑y⁻¹) * σ.hom (v₀ a) := fun a => IsFractionRing.injective W K (by
    rw [map_mul, map_mul, hu', hu', ← hy, mul_assoc (u : K), ← map_mul, y.mul_inv, map_one, _root_.mul_one])
  obtain ⟨a₀, ha₀⟩ := hu
  rw [funext key]
  exact hasTh_unit_mul t' hW (isUnit_of_mul_isUnit_left (key a₀ ▸ ha₀))

theorem good_reduction_of_theta_point : Out.Laws → Out.Laws2 → GlobalTheory.SS.SemistablePol → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → ∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a)) := by
  intro h₁ h₂ hS hU hT g n J w w' hn ho
  refine ⟨2, fun j hj o _ b V K _ _ _ _ _ _ _ _ _ β t v hp hv hC => ?_⟩
  obtain ⟨W, _, _, _, φ, ψ, tK, G, _, gen, hφ, hψ, hc, hK, hgen, hG, hE⟩ := exists_model hS V K β t
  have : CharZero (FractionRing W) := charZero_of_injective_ringHom ψ.injective
  have : CharZero W := RingHom.charZero (algebraMap W (FractionRing W))
  have := hG.comm
  have hp' : tK.Prim w w' := (GlobalTheory.shape_prim_pull_and_descend o g _ J b (fun _ => 0) 0 w w' _ _ _ _ _ t tK hK).2.1 hp
  have hS' : GlobalTheory.ZH.HypS tK.pol.A tK.pol.L := ⟨tK.act w, tK.act w', tK.hom w, tK.hom w', hp'.1, hp'.2.2, hp'.2.1⟩
  obtain ⟨D, U, -⟩ := hU W hc tK.pol G hG hE hS' gen hgen
  have hvK : tK.HasTh (𝟙 _) (fun a => algebraMap W (FractionRing W) (φ (v a))) := by
    have a := GlobalTheory.hasTh_baseChange h₂ o g _ J b _ _ t _ _ ψ _ _ hv
    rw [Category.comp_id, ← Category.id_comp (spMap ψ)] at a
    have e : (fun a => algebraMap W (FractionRing W) (φ (v a))) = fun a => ψ (algebraMap V K (v a)) :=
      funext fun a => (RingHom.congr_fun hψ (v a)).symm
    rw [e]
    exact (GlobalTheory.hasTh_iff_of_tmap o g _ J b _ _ t _ _ tK _ _ _ _ hK).2 a
  have hC' : Coset n (n ^ j) (fun a => φ (v a)) (IsLocalRing.maximalIdeal W) := fun a =>
    (hC a).imp fun c hc h => hc fun hu => h (hu.map φ)
  have hu : IsUnit ((n ^ j : ℕ) : W) := by
    have := b.unit.map (φ.comp β)
    rw [map_natCast, Nat.cast_pow] at this
    exact (isUnit_pow_iff two_ne_zero).1 this
  have := subsingleton_characters h₁ h₂ hT W hc tK G hG D U hn.two_le ho hj hu _ hvK hC'
  obtain ⟨P, χ, hχ, hL⟩ := exists_pol_model h₁ h₂ W hc tK.pol G hG D U
  have e : spMap (φ.comp β) = spMap φ ≫ spMap β := Spec.map_comp _ _
  obtain ⟨t', ht'⟩ := exists_obj_model h₁ h₂ W (FractionRing W) (φ.comp β) (by rw [e]) tK P χ hχ hL e
  refine ⟨W, FractionRing W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    φ, ψ, t', tK, hφ, hψ, hK, ht', hasTh_of_generic h₁ h₂ W _ t' tK ht' hn.two_le (dvd_pow_self n (by omega)) _ hvK ?_⟩
  obtain ⟨c, hc⟩ := hC' 0
  exact ⟨_, by_contra hc⟩

end GlobalTheory.ThetaCrit
end
