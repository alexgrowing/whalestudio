import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PrimAn
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcInTraceArc
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsInverseUnitTower
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RosatiAdjIffLamEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingActIffOAct
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOfCmTriplePullback
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolUnifReparam
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DeterminantConditionOfDiagonalCMAction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPELObjectOfPrimitivePeriodMapUniformised
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HasGenPull
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TripleProductTorusPeriodicBounded
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSymmetricIffExistsGen

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ArcCM.CxFibre

open ReciprocityTheory.ChartRestriction.G.DVR in

theorem exists_primGen {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) (f : G ⟶ G) [IsMonHom f]
    (h : LBIso L.L (cubeLB G ![𝟙 G, f] L.L)) :
    ∃ w : LB.Gen (LB.LinComb L.L (K := Fin 4)
        ![(padd G (𝟙 _) f).left, 𝟙 G.left, f.left, (toUnit G ≫ η[G]).left] ![1, -2, -1, 2]),
      w.IsGen ∧ LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ w (eSec G)) (LB.oneGen L.L) := by
  obtain ⟨⟨ρ, hρ, -⟩, -⟩ := GlobalTheory.JetSer.exists_unique_normPrim S G L f h
  have h0 := (HasGen.of_gen ρ hρ).neg.add (GlobalTheory.PullGenG.hasGen_one L)
  obtain ⟨u, hu⟩ := h0.gen L.isLB (K' := Fin 4)
    ![(padd G (𝟙 _) f).left, 𝟙 G.left, f.left, (toUnit G ≫ η[G]).left] ![1, -2, -1, 2] (by
      have h1' : (toUnit G ≫ η[G] : G ⟶ G) = 1 := rfl
      simp [fsum, Fin.sum_univ_four, Fin.sum_univ_five, GlobalTheory.JetSer.primφ, GlobalTheory.JetSer.primε, lf_single, padd_eq_mul, h1',
        Finsupp.single_neg, single_two, single_neg_two, Matrix.vecHead, Matrix.vecTail]
      abel)
  have hone : (LB.oneGen L.L (Y := (𝟙_ (Over S)).left)).IsGen := by
    intro i j
    show res _ 1 = _ * res _ 1
    rw [map_one, map_one, _root_.mul_one]
    simp [LB.LinComb]
    rfl
  refine exists_normalized_to L.isLB _ _ u hu G.hom (eSec G) (Over.w η[G]) _ _ _ hone ?_
  have h1 : (η[G] : 𝟙_ _ ⟶ G) = 1 := by rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have e : (fun k => eSec G ≫ (![(padd G (𝟙 _) f).left, 𝟙 G.left, f.left, (toUnit G ≫ η[G]).left] : Fin 4 → _) k) =
      fun _ => (η[G]).left := by
    funext i
    fin_cases i
    · show (η[G]).left ≫ (padd G (𝟙 _) f).left = _
      rw [← Over.comp_left, padd_eq_mul, MonObj.comp_mul, Category.comp_id, IsMonHom.one_hom, h1, _root_.mul_one]
    · exact Category.comp_id _
    · show (η[G]).left ≫ f.left = _
      rw [← Over.comp_left, IsMonHom.one_hom]
    · show (η[G]).left ≫ (toUnit G ≫ η[G]).left = _
      rw [← Over.comp_left, ← Category.assoc, toUnit_unique (η[G] ≫ toUnit G) (𝟙 _), Category.id_comp]
  rw [e, fsum_empty]
  simp [fsum, Fin.sum_univ_four, ← Finsupp.single_add]

theorem chi_eq {G : Over (Sp ℂ)} [GrpObj G] {L : LB G.left} (hL : L.IsLB) (f : G ⟶ G)
    (w : LB.Gen (LB.LinComb L (K := Fin 4)
        ![(padd G (𝟙 _) f).left, 𝟙 G.left, f.left, (toUnit G ≫ η[G]).left] ![1, -2, -1, 2])) (hw : w.IsGen)
    {g : ℕ} (u : HolUnif G L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (h : u.IsAH Hm χ)
    (W : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hW : ∀ z, u.ex (W z) = u.ex z ≫ f) (l m : u.Λ) (hm : (m : Fin g → ℂ) = W l) :
    χ l = Complex.exp (Real.pi * Complex.I * ((hermForm Hm l m).im : ℂ)) := by
  have he0 : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem
  have per : ∀ a ∈ u.Λ, ∀ z, u.ex (z + a) = u.ex z := fun a ha z => by
    rw [u.ex_add, (u.ker a).2 ha, _root_.mul_one]
  obtain ⟨h1, κ, hκ, h2⟩ := FrameUnits.gen_linComb_in_frame u hL h (fun z => (u.ex z).left) u.hol
    (by
      obtain ⟨R, hR⟩ := FrameUnits.exists_period_norm_le u
      refine ⟨R, fun z => ?_⟩
      obtain ⟨l, hl, h⟩ := hR z
      exact ⟨l, fun w => by rw [per l hl], h⟩)
    _ _ ![LinearMap.id + W, LinearMap.id, W, 0]
    (by
      intro k z
      fin_cases k
      · exact congrArg (fun m => m.left) (show u.ex z ≫ (𝟙 _ * f) = u.ex (z + W z) by
          rw [MonObj.comp_mul, Category.comp_id, ← hW, u.ex_add])
      · exact Category.comp_id _
      · exact congrArg (fun m => m.left) (hW z).symm
      · exact congrArg (fun m => m.left) ((MonObj.comp_one (u.ex z)).trans he0.symm)) w hw
  obtain ⟨j, hj⟩ := PullHermitian.exists_chart (u.ex 0).left hL
  have hj' : ∀ a : u.Λ, ⊤ ≤ (u.ex a).left ⁻¹ᵁ L.U j := fun a => by
    rw [← zero_add (a : Fin g → ℂ), per _ a.2]; exact hj
  have e0 := h2 (fun _ => j) 0 (fun k => by rw [map_zero]; exact hj)
  have e1 := h2 (fun _ => j) l (fun k => by
    fin_cases k
    · simpa [hm] using hj' (l + m)
    · exact hj' l
    · simpa [hm] using hj' m
    · exact hj)
  have e2 : u.ex l = u.ex 0 := by rw [← zero_add (l : Fin g → ℂ), per _ l.2]
  rw [e2, e0] at e1
  have e3 := mul_left_cancel₀ hκ e1
  have hs := h1 l l
  have fr : ∀ a : u.Λ, u.fr j 0 = χ a * Complex.exp (Real.pi / 2 * hermForm Hm a a) * u.fr j a := fun a => by
    simpa [hermForm] using h.2.2.2 a j 0 hj
  have a1 := fr l
  have a2 := fr m
  have a3 := fr (l + m)
  rw [FrameValue.chi_add hL h l m] at a3
  have n0 := u.fr_ne j 0 hj
  have n1 := u.fr_ne j _ (hj' l)
  have n2 := u.fr_ne j _ (hj' m)
  have c1 := FrameValue.chi_ne_zero h l
  have c2 := FrameValue.chi_ne_zero h m
  simp only [Fin.prod_univ_four, Fin.sum_univ_four, map_zero] at e3 hs
  simp [← hm] at e3 hs
  have x : Complex.exp (Real.pi / 2 * hermForm Hm (l + m) (l + m)) =
      Complex.exp (Real.pi / 2 * hermForm Hm l l) ^ 2 * Complex.exp (Real.pi / 2 * hermForm Hm m m) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    have z : hermForm Hm 0 0 = 0 := by simp [hermForm]
    push_cast
    linear_combination (Real.pi / 2 : ℂ) * hs - Real.pi * z
  rw [Submodule.coe_add, x] at a3
  field_simp at e3
  have n3 := Complex.exp_ne_zero (Real.pi / 2 * hermForm Hm l l)
  have n4 := Complex.exp_ne_zero (Real.pi / 2 * hermForm Hm m m)
  have key : ∀ f₀ f₁ f₂ f₃ x y s a b : ℂ, x * y * a ^ 2 * b * f₁ ^ 2 * f₂ ≠ 0 → f₀ = x * a * f₁ → f₀ = y * b * f₂ →
      f₀ = x * y * s * (a ^ 2 * b) * f₃ → f₁ ^ 2 * f₂ = f₃ * f₀ ^ 2 → x = s := by
    intro f₀ f₁ f₂ f₃ x y s a b n p q r t
    refine mul_left_cancel₀ n ?_
    linear_combination (-(f₀ + x * a * f₁) * (y * b * f₂)) * p - f₀ ^ 2 * q + f₀ ^ 2 * r - x * y * s * a ^ 2 * b * t
  exact key _ _ _ _ _ _ _ _ _ (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero c1 c2)
    (pow_ne_zero _ n3)) n4) (pow_ne_zero _ n1)) n2) a1 a2 a3 (by linear_combination e3.resolve_right n0)

theorem lieMult_card (unif : ThetaUnifAV) {E : Type} [Field E] [NumberField E] (P : Out.PolAV (Sp ℂ)) {g : ℕ}
    (hg : g = P.g) (u : HolUnif P.A P.L g) (act : OAct (𝓞 E) P.A) (ty : Fin g → (E →+* ℂ))
    (hact : ∀ (a : 𝓞 E) z, u.ex (fun i => ty i (a : E) * z i) = u.ex z ≫ act.act a) (τ₀ : E →+* ℂ) :
    LieMult act (𝟙 (Sp ℂ)) (τ₀.comp (algebraMap (𝓞 E) E)) (Nat.card {i // ty i = τ₀}) := by
  subst hg
  obtain ⟨h₁, h₂, -⟩ := GlobalTheory.AnyUnif.tangent_and_unimodular unif P u
  have hs : Smooth P.A.hom := P.isAb.smooth
  obtain ⟨v, hv, heig⟩ := GlobalTheory.exists_lieBasis_of_holUnif P.A P.L P.g u hs h₁ h₂
  have h := GlobalTheory.lieMult_of_eigenbasis ℂ (𝓞 E) P.A act P.g v (fun i => (ty i).comp (algebraMap (𝓞 E) E)) hs hv
    (fun i a => heig _ _ (act.hom a) (hact a) i) (τ₀.comp (algebraMap (𝓞 E) E))
  convert h using 1
  exact Nat.card_congr (Equiv.subtypeEquivRight fun i =>
    ⟨fun e => by rw [e], fun e => IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) e⟩)

open FibreUnif in

theorem exists_holUnif_of_exp (hT : ThetaUnifAV) {S : Scheme.{0}} {G : Over S} [GrpObj G] {L₀ : LB G.left}
    (hL₀ : L₀.IsLB) (t : Sp ℂ ⟶ S) (P : Out.PolAV (Sp ℂ)) (rig : LB.Gen (P.L.pull (eSec P.A))) (hrig : rig.IsGen)
    (φ : P.A.left ⟶ G.left) (hp : IsGrpPullback P.A G t φ) (hiso : LBIso P.L (L₀.pull φ)) {g : ℕ}
    (Λ : Submodule ℤ (Fin g → ℂ)) (hd : DiscreteTopology Λ) (hfull : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (herm : Hm.IsHermitian) (pos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (Ef : Λ → Λ → ℤ) (hEf' : ∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im)
    (e : (Fin g → ℂ) → (Over.mk t ⟶ G)) (holG : IsHolTo Set.univ fun z => (e z).left)
    (add : ∀ z w, e (z + w) = e z * e w) (onto : Function.Surjective e) (ker : ∀ z, e z = 1 ↔ z ∈ Λ)
    (weil : ∀ (k : ℕ) (a b : Λ) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) →
      Out.WeilIs G L₀ k (e ((k : ℂ)⁻¹ • (a : Fin g → ℂ))) (e ((k : ℂ)⁻¹ • (b : Fin g → ℂ))) (unitOn c)) :
    ∃ (u : HolUnif P.A P.L g) (χ : u.Λ → ℂ), g = P.g ∧ u.Λ = Λ ∧ u.IsAH Hm χ ∧ u.IsRig rig ∧
      (∀ (j : ℕ) θ, u.IsThetaFn Hm χ j θ → ∃ s, u.IsFnPow j s θ) ∧ ∀ z, (u.ex z).left ≫ φ = (e z).left := by
  obtain ⟨w, hw⟩ := hiso
  obtain ⟨u, Hm₀, χ, Ef₀, hAH, hR, ht₁, ht₂, -, hth, hEf, -, hweil⟩ := hT P rig hrig
  have inj : ∀ x y : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, x.left ≫ φ = y.left ≫ φ → x = y := fun x y h =>
    Over.OverMorphism.ext (hp.1.hom_ext h (by rw [Over.w x, Over.w y]))
  have lift : ∀ x₀ : Over.mk t ⟶ G, ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, x.left ≫ φ = x₀.left := fun x₀ =>
    ⟨Over.homMk (hp.1.lift x₀.left (𝟙 _) ((Over.w x₀).trans (Category.id_comp _).symm)) (hp.1.lift_snd _ _ _),
      hp.1.lift_fst _ _ _⟩
  choose Φ hΦ using lift
  have Φmul : ∀ x y, Φ (x * y) = Φ x * Φ y := fun x y => inj _ _ (by
    rw [hΦ, ← hp.2 _ (Φ x) (Φ y) (pushPt hp.1.w (Φ x)) (pushPt hp.1.w (Φ y)) rfl rfl]
    exact mul_left_congr (Category.id_comp _).symm _ _ _ _ (hΦ x).symm (hΦ y).symm)
  have Φinj : Function.Injective Φ := fun x y h => Over.OverMorphism.ext (by rw [← hΦ, ← hΦ, h])
  have Φsurj : Function.Surjective Φ := fun x =>
    ⟨Over.homMk (x.left ≫ φ) ((Over.w (pushPt hp.1.w x)).trans (Category.id_comp _)), inj _ _ (hΦ _)⟩
  have Φone : Φ 1 = 1 := by
    have := Φmul 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have hol : IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun z => (Φ (e z)).left) :=
    isHolTo_of_isPullback hp.1 (e := fun z => (Φ (e z)).left) (fun z => Over.w (Φ (e z)))
      (by simpa only [hΦ] using holG)
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo P.A P.isAb P.L P.g g u ht₁ ht₂ (fun z => Φ (e z))
    (fun z z' => by rw [add, Φmul]) hol
  have hΛ : ∀ z, F z ∈ u.Λ ↔ z ∈ Λ := fun z => by
    rw [← u.ker, hF, ← ker, ← Φone, Φinj.eq_iff]
  have cΛ : (u.Λ : Set (Fin P.g → ℂ)).Countable := by
    have := u.discrete
    exact (countable_of_Lindelof_of_discrete : Countable u.Λ)
  have cP : (Λ : Set (Fin g → ℂ)).Countable := (countable_of_Lindelof_of_discrete : Countable Λ)
  have Finj : Function.Injective F := (injective_iff_map_eq_zero F).2 fun z hz =>
    eq_zero_of_smul_mem_countable cP fun t => (hΛ _).1 (by rw [map_smul, hz, smul_zero]; exact u.Λ.zero_mem)
  have Fsurj : Function.Surjective F := surjective_of_countable F cΛ fun v => by
    obtain ⟨x₀, hx₀⟩ := Φsurj (u.ex v)
    obtain ⟨z, rfl⟩ := onto x₀
    refine ⟨z, (u.ker _).1 ?_⟩
    have := u.ex_add (v - F z) (F z)
    rw [sub_add_cancel, hF, hx₀] at this
    exact right_eq_mul.1 this
  have hex : ∀ z, (u.ex (F z)).left ≫ φ = (e z).left := fun z => by rw [hF, hΦ]
  have him : ∀ a ∈ Λ, ∀ b ∈ Λ, (hermForm Hm₀ (F a) (F b)).im = (hermForm Hm a b).im := fun a ha b hb => by
    let a' : u.Λ := ⟨F a, (hΛ _).2 ha⟩
    let b' : u.Λ := ⟨F b, (hΛ _).2 hb⟩
    refine (hEf a' b').symm.trans ((congrArg _ (int_eq_of_exp_eq fun k hk => ?_)).trans (hEf' ⟨a, ha⟩ ⟨b, hb⟩))
    have h₁ := hweil k a' b' (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have h₂ := weil k ⟨a, ha⟩ ⟨b, hb⟩ (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
    have h₃ := weil_eq_of_grpPullback hp hL₀ P.isLB w hw (Z := Sp ℂ) (t := t) (t' := 𝟙 _)
      (Category.id_comp _).symm k (u.ex ((k : ℂ)⁻¹ • F a)) (u.ex ((k : ℂ)⁻¹ • F b)) _ _
      (by rw [← hex, map_smul]) (by rw [← hex, map_smul]) _ _ h₁ h₂
    exact congrArg Units.val (unitOn_injective h₃)
  have hH : ∀ z z', hermForm Hm₀ (F z) (F z') = hermForm Hm z z' := by
    have e : (PeriodObject.imForm Hm₀).compl₁₂ (F.restrictScalars ℝ) (F.restrictScalars ℝ) = PeriodObject.imForm Hm :=
      LinearMap.ext_on hfull fun z hz => LinearMap.ext_on hfull fun z' hz' => him z hz z' hz'
    have im : ∀ z z', (hermForm Hm₀ (F z) (F z')).im = (hermForm Hm z z').im := fun z z' =>
      LinearMap.congr_fun (LinearMap.congr_fun e z) z'
    intro z z'
    refine Complex.ext ?_ (im z z')
    have := im (Complex.I • z) z'
    simpa [hermForm, smul_dotProduct] using this
  let T := LinearEquiv.ofBijective F ⟨Finj, Fsurj⟩
  have hg : g = P.g := by simpa using T.finrank_eq
  subst hg
  refine ⟨holUnifReparam u T (fun _ => 1) (differentiable_const _) (fun _ => one_ne_zero), fun l => χ ⟨F l, l.2⟩, rfl,
    Submodule.ext hΛ, ⟨herm, pos, fun l => hAH.2.2.1 _, fun l i z hz => ?_⟩, fun j hj => ?_, fun j θ hθ => ?_, hex⟩
  · have := hAH.2.2.2 ⟨F l, l.2⟩ i (F z) hz
    change u.fr i (F z) / 1 = _ * Complex.exp (_ * hermForm Hm z l + _ * hermForm Hm l l) * (u.fr i (F (z + l)) / 1)
    rw [div_one, div_one, map_add, ← hH, ← hH]
    exact this
  · change u.fr _ (F 0) / 1 = _
    rw [map_zero, div_one]
    exact hR j hj
  · obtain ⟨s, hs, -⟩ := (hth j).2 (fun z => θ (T.symm z))
      ⟨hθ.1.comp T.symm.toContinuousLinearEquiv.differentiable, fun l z => by
        have h := hθ.2 ⟨T.symm l, show T (T.symm l) ∈ u.Λ by simp⟩ (T.symm z)
        have a : ∀ v, F (T.symm v) = v := T.apply_symm_apply
        simp only [← hH, a] at h
        beta_reduce
        rw [map_add]
        exact h⟩
    refine ⟨s, fun i z hz => ?_⟩
    have := hs i (T z) hz
    beta_reduce at this
    rw [T.symm_apply_apply] at this
    change _ = θ z * (u.fr _ (T z) / 1) ^ j
    rw [div_one]
    exact this

theorem exists_fibre_of_eq {O R : Type} [CommRing O] [StarRing O] [CommRing R] {σ : R →+* ℂ} {B : Out.PolAV (Sp R)}
    {act : O → (B.A ⟶ B.A)} {P P' : Out.PolAV (Sp ℂ)} (h : P' = P) {oa : P.OAct O} {oa' : P'.OAct O} (h' : HEq oa' oa)
    (φ : P.A.left ⟶ B.A.left) (h₁ : IsPolFibre σ B P φ) (h₂ : ∀ a, (oa.act a).left ≫ φ = φ ≫ (act a).left) :
    ∃ φ' : P'.A.left ⟶ B.A.left, IsPolFibre σ B P' φ' ∧ ∀ a, (oa'.act a).left ≫ φ' = φ' ≫ (act a).left := by
  subst h
  obtain rfl := eq_of_heq h'
  exact ⟨φ, h₁, h₂⟩

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem exists_arcIn_fibre : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (B : GlobalTheory.CM.PAT H (Sp R)) (σR : R →+* ℂ), GoodEmb c σ → IsUnf U → l.A = 1 → letI := H.starRing; ∀ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂) (ex : (Fin A.gB → ℂ) → (Over.mk (spMap σR) ⟶ B.t.G)), OnOrbit Uw k ξ' x A gam ξ → Module.finrank (𝓞 E) A.X = 1 → (∀ y y', (2 * l.M' : ℤ) ∣ A.be y y') → PrimAn H A → AbDat H A DB tyB eB → DB.p = Dw.p - 1 → DB.q = Dw.q - 1 → 1 ≤ Dw.p → 1 ≤ Dw.q → GlobalTheory.CM.IsExp B σR DB tyB (A.abelian₂.subtype.toAddMonoidHom.comp eB.toAddMonoidHom) ex → ∃ (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn aC) (hA : Λ.A = A) (φ : aC.D₀.P.A.left ⟶ B.pol.A.left), IsPolFibre σR B.pol aC.D₀.P φ ∧ (∀ a, (aC.oa.onB.act a).left ≫ φ = φ ≫ (B.t.act.act a).left) ∧ ∀ v, Λ.toGtAn₀.Lifts (aC.eta v) (cast (congrArg AnArc.La hA.symm) (gam (Uw.F.t (Uw.ik k) v))) := by
  intro hK E _ _ _ H Dw l Xo c _ _ σ r U Uw k ξ' x R _ _ _ B σR hσ _ hA1
  let _ := H.starRing
  intro A gam ξ DB tyB eB ex ⟨hgam, _, T₀, hT₀⟩ hrk hbe ⟨hχ, hψ⟩ ⟨hF, hty, _, hEF, _⟩ hp hq hp1 hq1
    ⟨_, hol, add, onto, ker, lin, weil⟩
  obtain ⟨T, m, hg⟩ := GlobalTheory.CM.PAT.exists_pullback E H _ _ (spMap σR) B
  obtain ⟨-, hiso⟩ := GlobalTheory.CM.PAT.exists_of_sabMap E H _ _ _ B _ m
  obtain ⟨w₀, hw₀, -⟩ := m.lin
  obtain ⟨sym, hsym, hsym'⟩ := (GlobalTheory.isSymmetric_iff_exists_gen _ _ T.t.PP).1 T.t.sym
  have := T.t.act.hom H.w0
  obtain ⟨w, hw, hw'⟩ := exists_primGen T.t.PP (T.t.act.act H.w0) T.t.prim
  let oa : T.pol.OAct (𝓞 E) := ⟨T.t.act.toRingAct, fun a =>
    (GlobalTheory.RosLam.rosatiAdj_iff_lamEq hK.laws.globalFns _ T.pol _ _ (T.t.act.hom a) (T.t.act.hom _)).2 (by
      change GlobalTheory.CM.LamEq _ _ _ _ _ (T.t.act.act (H.bar a))
      simpa [GlobalTheory.CM.LamEq] using T.t.adj a)⟩
  obtain ⟨u, χ, hgP, lam, hAH, hrig, hθ, hex⟩ := exists_holUnif_of_exp hK.theta B.t.PP.isLB (spMap σR) T.pol T.t.PP.rig
    T.t.PP.rigGen m.φ m.cart ⟨w₀, hw₀⟩ A.abelian₂ A.discrete A.full A.Hm A.Hm_herm A.Hm_pos (fun a b => A.Ef a b) A.Ef_eq
    ex hol add onto
    (fun z => (ker z).trans ⟨fun ⟨a, ha⟩ => ha ▸ (eB a).2, fun hz => ⟨eB.symm ⟨z, hz⟩, by simp⟩⟩)
    (fun n a b c hn hc => by
      obtain ⟨a, rfl⟩ := eB.surjective a
      obtain ⟨b, rfl⟩ := eB.surjective b
      exact weil n a b c hn (by rw [hEF]; exact hc))
  have hact : ∀ (a : 𝓞 E) z, u.ex (fun i => tyB i (a : E) * z i) = u.ex z ≫ T.t.act.act a := fun a z =>
    Over.OverMorphism.ext (m.cart.1.hom_ext (by
      rw [hex, lin, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc, hex])
      (by rw [Over.w, Over.w]))
  have hact' : ∀ (a : 𝓞 E) z, u.ex (A.F a z) = u.ex z ≫ T.t.act.act a := fun a z => by
    rw [← hact]; exact congrArg u.ex (funext (hF a z))
  obtain rfl : χ = fun b : u.Λ => A.chi ⟨b, lam.le b.2⟩ := funext fun a => by
    rw [chi_eq T.t.PP.isLB _ w hw u A.Hm χ hAH (A.F H.w0) (hact' _) a
      ⟨_, lam.ge (A.F_mem H.w0 a (lam.le a.2))⟩ rfl, hχ]
    have h₁ := A.Ef_eq_im (A.FLam H.w0 ⟨a, lam.le a.2⟩) ⟨a, lam.le a.2⟩
    rw [← A.H_conj, Complex.conj_im] at h₁
    have h₂ : (hermForm A.Hm a (A.F H.w0 a)).im = -(A.Ef (A.FLam H.w0 ⟨a, lam.le a.2⟩) ⟨a, lam.le a.2⟩ : ℤ) := by
      rw [h₁, neg_neg]; rfl
    generalize A.Ef (A.FLam H.w0 ⟨a, lam.le a.2⟩) ⟨a, lam.le a.2⟩ = n at h₂
    rw [h₂, ← Complex.exp_neg_pi_mul_I, ← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  obtain ⟨s, hs, -⟩ := hT₀ ((T₀ + 1 : ℝ) * Complex.I) (by simp)
  obtain ⟨f, f₁, f₂, f₃, f₄⟩ := familyUnif_lattice_genus E H Dw l Xo _ _ _ Uw.F (Uw.ik k) _ (Uw.period k ⟨_, hs⟩)
  obtain ⟨a, Λ, hA, hP, -, -, -, hoa, -, heta, -⟩ := GlobalTheory.ArcOfModel.exists_arcIn hK.laws hK.laws2 Dw l
    (RingHom.id c.F) σ T.pol T.t.PP.rig T.t.PP.rigGen T.t.cub sym hsym hsym' oa ⟨w, hw, hw'⟩ A u lam hAH hrig
    (fun j _ => hθ j) hact' hψ (Module.nontrivial_of_finrank_pos (R := 𝓞 E) (hrk ▸ one_pos)) hbe _ gam hgam
    (Uw.F.t (Uw.ik k)) f (fun _ => 1) f₁ (fun n hn v => ((f₂ n hn).1 v).1) (fun n hn => (f₂ n hn).2)
    (fun n hn v v' => by simpa using f₃ n hn v v') f₄
    (fun v => ⟨f l.A v - Uw.F.t (Uw.ik k) v, by rw [hA1]; simp⟩)
    (fun z hz => by
      rw [hA1] at hz ⊢
      obtain rfl : z = 1 := Subtype.ext (by simpa [zeta] using hz)
      simp [Complex.exp_neg])
    (fun ρ hρ τ => by
      obtain ⟨τ₀, rfl⟩ := GlobalTheory.PeriodPoint.exists_embedding (RingHom.id ℂ) τ
      have hρ' : σ ρ = H.rt0 := by
        rw [← hσ]
        exact congrArg σ (Subtype.ext hρ)
      refine ⟨_, lieMult_card hK.theta T.pol hgP u _ tyB hact τ₀, ?_⟩
      rw [hrk, hρ']
      split_ifs with h
      · rw [(hty τ₀).1 h]; omega
      · rw [(hty τ₀).2 h]; omega)
  obtain ⟨φ, h₁, h₂⟩ := exists_fibre_of_eq (B := B.pol) (act := B.t.act.act) hP hoa m.φ ⟨hg, m.cart, hiso⟩ m.act
  refine ⟨a, Λ, hA, φ, h₁, h₂, fun v q hq => ?_⟩
  rw [(TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing ℂ) ℂ) (RingHom.comp_id _) _).unique hq (heta v)]
  exact qk_equiv_refl a.bimult _

end GlobalTheory.ArcCM.CxFibre
