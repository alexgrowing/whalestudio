import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInIsoElliptic
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DifferentiableAtDerivAtZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConstOfSqMulTendstoZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPeriodPairOfLatticeInLine
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsWeierstrassCoordinatesOnLine
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.EllipticKey

open Filter Topology GlobalTheory.WeierstrassCurve

theorem hasDerivAt_of_eq_unit_mul {g : ℕ} {Z e θ : (Fin g → ℂ) → ℂ} (hZ : DifferentiableAt ℂ Z 0)
    (he : DifferentiableAt ℂ e 0) (h : ∀ᶠ z in 𝓝 0, Z z = e z * θ z) (he0 : e 0 = 1) (hZ0 : Z 0 = 0)
    (w : Fin g → ℂ) : HasDerivAt (fun t : ℂ => θ (t • w)) (fderiv ℂ Z 0 w) 0 := by
  have hl : HasDerivAt (fun t : ℂ => t • w) w 0 := by simpa using (hasDerivAt_id (0 : ℂ)).smul_const w
  have hc : Tendsto (fun t : ℂ => t • w) (𝓝 0) (𝓝 0) := by simpa using hl.continuousAt.tendsto
  have d : ∀ {F : (Fin g → ℂ) → ℂ}, DifferentiableAt ℂ F 0 →
      HasDerivAt (fun t : ℂ => F (t • w)) (fderiv ℂ F 0 w) 0 := fun {F} hF => by
    have h4 : HasFDerivAt F (fderiv ℂ F 0) ((0 : ℂ) • w) := by rw [zero_smul]; exact hF.hasFDerivAt
    exact h4.comp_hasDerivAt (0 : ℂ) hl
  have hne : ∀ᶠ z in 𝓝 0, e z ≠ 0 := he.continuousAt.eventually_ne (by rw [he0]; exact one_ne_zero)
  have h1 := (d hZ).div (d he) (by simp [he0])
  simp only [zero_smul, he0, hZ0, _root_.mul_one, zero_mul, sub_zero, one_pow, div_one] at h1
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hc h, hc hne] with t h1 h2
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at h1 h2
  simp only [Pi.div_apply, h1]
  field_simp

theorem thetaChar_neg (τ : Matrix (Fin 1) (Fin 1) ℂ) (a b z : Fin 1 → ℂ)
    (h : (a 0 = 0 ∧ b 0 = 1 / 2) ∨ ((a 0 = 0 ∨ a 0 = 1 / 2) ∧ b 0 = 0)) :
    thetaChar τ a b (-z) = thetaChar τ a b z := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (k : ℂ) = 2 * a 0 := by
    rcases h with ⟨h, -⟩ | ⟨h | h, -⟩
    exacts [⟨0, by simp [h]⟩, ⟨0, by simp [h]⟩, ⟨1, by simp [h]⟩]
  unfold thetaChar
  rw [← (Equiv.subLeft (fun _ : Fin 1 => -k)).tsum_eq]
  refine tsum_congr fun n => ?_
  rw [Complex.exp_eq_exp_iff_exists_int]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_one, Equiv.subLeft_apply, Pi.add_apply, Pi.sub_apply,
    Pi.neg_apply, Int.cast_sub, Int.cast_neg, hk]
  rcases h with ⟨h, h'⟩ | ⟨-, h'⟩
  · exact ⟨-n 0, by rw [h, h']; push_cast; ring⟩
  · exact ⟨0, by rw [h']; push_cast; ring⟩

theorem det_pow_div_eq {g : ℕ} (hg : g = 1) (τ M : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ)
    (hab : charHalf g a b) (hτ : (τ.map Complex.im).PosDef) (i : Fin g)
    (hd : HasDerivAt (fun t : ℂ => c * thetaChar τ a b (t • (2 * Real.pi * Complex.I)⁻¹ • M i)) (-1) 0)
    (L : PeriodPair) (hL : ∀ z : ℂ, z ∈ L.lattice ↔ ∃ m n : Fin g → ℤ,
      z • (2 * Real.pi * Complex.I)⁻¹ • M i = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) :
    M.det ^ 4 / c ^ 8 = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := by
  subst hg
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have him : 0 < (τ 0 0).im := by simpa using hτ.diag_pos (i := 0)
  have hodd : a 0 = 1 / 2 ∧ b 0 = 1 / 2 := by
    by_contra hn
    have h := fun z => thetaChar_neg τ a b z (by have := hab.1 0; have := hab.2 0; tauto)
    have h2 : HasDerivAt (fun t : ℂ => c * thetaChar τ a b (t • (2 * Real.pi * Complex.I)⁻¹ • M 0)) (-1) (-0) := by
      rwa [neg_zero]
    have h3 := h2.comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))
    simp only [Function.comp_def, neg_smul, h] at h3
    have := h3.unique hd
    norm_num at this
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hpi' : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hM : M 0 0 ≠ 0 := fun h => by
    have e : M 0 = 0 := funext fun i => by rw [Subsingleton.elim i 0]; exact h
    simp only [e, smul_zero] at hd
    simpa using hd.unique (hasDerivAt_const _ _)
  have hc : c ≠ 0 := fun h => by
    simp only [h, zero_mul] at hd
    simpa using hd.unique (hasDerivAt_const _ _)
  let t : UpperHalfPlane := ⟨τ 0 0, him⟩
  set p : ℂ := 2 * Real.pi * Complex.I / M 0 0 with hp
  have hD : HasDerivAt (fun z : ℂ => thetaChar (g := 1) !![(t : ℂ)] ![1 / 2] ![1 / 2] ![z]) (c⁻¹ * (-1 * p)) 0 := by
    have h2 : HasDerivAt (fun t : ℂ => c * thetaChar τ a b (t • (2 * Real.pi * Complex.I)⁻¹ • M 0)) (-1) (0 * p) := by
      rwa [zero_mul]
    have h3 := (h2.comp (0 : ℂ) (hasDerivAt_mul_const p)).const_mul c⁻¹
    refine h3.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
    beta_reduce
    rw [Function.comp_apply, inv_mul_cancel_left₀ hc]
    congr 1
    · ext i j; fin_cases i; fin_cases j; rfl
    · ext i; fin_cases i; exact hodd.1.symm
    · ext i; fin_cases i; exact hodd.2.symm
    · ext i
      fin_cases i
      change z = z * p * ((2 * Real.pi * Complex.I)⁻¹ * M 0 0)
      rw [hp]
      field_simp
  have hJ := GlobalTheory.JacobiDeriv.deriv_thetaChar_pow_eight t
  rw [hD.deriv] at hJ
  rw [← latticeCurve_Δ, latticeCurve_Δ_eq_discriminant (a := p) (τ := t) (div_ne_zero hpi hM) fun x => ?_]
  · have hI : Complex.I ^ 4 = 1 := Complex.I_pow_four
    have e : ModularForm.discriminant t = (c⁻¹ * (-1 * p)) ^ 8 / (2 * Real.pi) ^ 8 := by
      rw [hJ]; field_simp
    rw [e, hp, Matrix.det_fin_one]
    field_simp
    exact hI
  · rw [hL]
    constructor
    · rintro ⟨m, n, h⟩
      refine ⟨n 0, m 0, ?_⟩
      have := congrFun h 0
      simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_one] at this
      change p * (n 0 * τ 0 0 + m 0) = x
      rw [add_comm, mul_comm _ (τ 0 0), ← this, hp]
      field_simp
    · rintro ⟨m, n, rfl⟩
      refine ⟨![n], ![m], funext fun i => ?_⟩
      fin_cases i
      change p * (m * τ 0 0 + n) * ((2 * Real.pi * Complex.I)⁻¹ * M 0 0) = n + ∑ j, τ 0 j * ((![m] j : ℤ) : ℂ)
      rw [Fin.sum_univ_one, Matrix.cons_val_zero, hp]
      field_simp
      ring

theorem ex_zero_left {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) :
    (u.ex 0).left = eSec A := by
  rw [(u.ker 0).2 u.Λ.zero_mem, Hom.one_def]
  simp [eSec]

theorem valAt'_iso_mul_fr {A : Over (Sp ℂ)} [GrpObj A] {L N : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (w : LB.Iso L N) {rig : LB.Gen (L.pull (eSec A))} {r : LB.Gen (N.pull (eSec A))} (hr : ∀ j, r.s j = 1)
    (hu : u.IsRig rig) (hw : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec A) (fun _ => 1)) rig r)
    (j : N.ι) (i : L.ι) (h : ⊤ ≤ eSec A ⁻¹ᵁ (N.U j ⊓ L.U i)) :
    valAt' (eSec A) (N.U j ⊓ L.U i) (w.s (j, i)).val * u.fr i 0 = 1 := by
  have hi : ⊤ ≤ (L.pull (eSec A)).U (fun _ => i) := fun y hy => Set.mem_iInter.2 fun _ => (h hy).2
  have hj : ⊤ ≤ (N.pull (eSec A)).U (fun _ => j) := fun y hy => Set.mem_iInter.2 fun _ => (h hy).1
  have hij : ⊤ ≤ 𝟙 (Sp ℂ) ⁻¹ᵁ ((N.pull (eSec A)).U (fun _ => j) ⊓ (L.pull (eSec A)).U (fun _ => i)) := le_inf hj hi
  have e := congrArg (fun a => valAt' (𝟙 (Sp ℂ)) _ (Units.val a)) (hw (fun _ => j, fun _ => i))
  simp only [Units.val_mul, valAt'_mul] at e
  rw [hu (fun _ => i) hi]
  refine Eq.trans ?_ (e.symm.trans ((valAt'_res _ inf_le_left _ hij).trans
    ((congrArg (fun a => valAt' (𝟙 (Sp ℂ)) _ (Units.val a)) (hr _)).trans (valAt'_one _ hj))))
  congr 1
  · simp only [LB.linCombIso, id, Finset.univ_unique, zpow_one]
    refine Eq.symm ((congrArg (fun a => valAt' (𝟙 (Sp ℂ)) _ (Units.val a)) (Finset.prod_singleton _ _)).trans ?_)
    exact (valAt'_appLE (𝟙 (Sp ℂ)) (eSec A) (N.U j ⊓ L.U i) _ (le_top.trans h) (w.s (j, i)).val hij).trans
      (by rw [Category.id_comp])
  · exact (valAt'_res _ inf_le_right _ hij).symm

theorem hasDerivAt_originFn {R : Type} [CommRing R] (W : WeierstrassCurve R) (s : R →+* ℂ) {A : Over (Sp ℂ)} [GrpObj A]
    {L : LB A.left} (hL : L.IsLB) {g : ℕ} (u : HolUnif A L g) (φ : A.left ⟶ scheme W)
    (he : eSec A ≫ φ = spMap s ≫ zero W) (w : LB.Iso L ((originLB W).pull φ)) (th : L.Sec) (θ : (Fin g → ℂ) → ℂ)
    (hθ : u.IsFn th θ)
    (hth : ∀ (j : ((originLB W).pull φ).ι) (i : L.ι)
      (h : ((originLB W).pull φ).U j ⊓ L.U i ≤ φ ⁻¹ᵁ (originLB W).U (j PUnit.unit)),
      (φ.appLE _ _ h).hom ((originSec W).f (j PUnit.unit)) =
        (show Γ(A.left, ((originLB W).pull φ).U j ⊓ L.U i) from (w.s (j, i)).val) * resG _ inf_le_right (th.f i))
    (hrig : ∀ j i, ⊤ ≤ eSec A ⁻¹ᵁ (((originLB W).pull φ).U j ⊓ L.U i) →
      valAt' (eSec A) (((originLB W).pull φ).U j ⊓ L.U i) (w.s (j, i)).val * u.fr i 0 = 1)
    (v : epsR ℂ ⟶ A)
    (h : IsUnimodularSol (W.map ((algebraMap ℂ (DualNumber ℂ)).comp s)) ![DualNumber.eps, -1, 0])
    (hv : v.left ≫ φ = ptHom W ((algebraMap ℂ (DualNumber ℂ)).comp s) ![DualNumber.eps, -1, 0] h)
    (w₀ : Fin g → ℂ) (hd : u.IsDiff w₀ v) : HasDerivAt (fun t : ℂ => θ (t • w₀)) (-1) 0 := by
  have h0 := ex_zero_left u
  obtain ⟨i, hi⟩ : ∃ i, eSec A (default : PrimeSpectrum ℂ) ∈ L.U i :=
    TopologicalSpace.Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ _))
  let j : ((originLB W).pull φ).ι := fun _ => true
  let V : A.left.Opens := ((originLB W).pull φ).U j ⊓ L.U i
  have hV : V ≤ φ ⁻¹ᵁ originOpen W := inf_le_left.trans (LB.wchart_le (originLB W) (fun _ => φ) j PUnit.unit)
  have hz : ⊤ ≤ (eSec A ≫ φ) ⁻¹ᵁ originOpen W := by
    rw [he, Scheme.Hom.comp_preimage, zero_preimage_originOpen]
    exact le_rfl
  have hV0 : ⊤ ≤ eSec A ⁻¹ᵁ V := (top_le_preimage_iff_mem _ _).2
    ⟨Set.mem_iInter.2 fun _ => (top_le_preimage_iff_mem _ _).1 hz, hi⟩
  have hn : ∀ U : A.left.Opens, V ≤ U → {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U} ∈ 𝓝 (0 : Fin g → ℂ) := fun U hU =>
    (u.hol U 0).1.mem_nhds (by rw [Set.mem_setOf_eq, h0]; exact top_le_preimage_mono _ hU hV0)
  let U₁ : A.left.Opens := φ ⁻¹ᵁ coordOpen W 1
  have hV1 : V ≤ U₁ := hV.trans (φ.preimage_mono (originOpen_le W))
  let f : Γ(A.left, U₁) := (φ.app (coordOpen W 1)).hom (ratio W 1 0)
  have hf : ∀ x : Sp ℂ ⟶ A.left, ⊤ ≤ x ⁻¹ᵁ V →
      valAt' x U₁ f = valAt' (x ≫ φ) (originOpen W) (originParam W) := fun x hx =>
    (valAt'_comp x φ _ _).trans (valAt'_res (x ≫ φ) (originOpen_le W) (ratio W 1 0)
      (top_le_preimage_mono x hV hx)).symm
  have key := hasDerivAt_of_eq_unit_mul (Z := fun z => valAt' (u.ex z).left U₁ f)
    (e := fun z => valAt' (u.ex z).left V (w.s (j, i)).val * u.fr i z) (θ := θ)
    ((u.hol U₁ f).2.differentiableAt (hn _ hV1))
    (((u.hol V _).2.differentiableAt (hn _ le_rfl)).mul ((u.fr_hol i).differentiableAt (hn _ inf_le_right)))
    ?_ (by simp only [h0]; exact hrig j i hV0) ?_ w₀
  · have h1 : ⊤ ≤ ptHom W ((algebraMap ℂ (DualNumber ℂ)).comp s) ![DualNumber.eps, -1, 0] h ⁻¹ᵁ coordOpen W 1 := by
      rw [ptHom_preimage_coordOpen]
      intro p _ hp
      exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp isUnit_one.neg)
    have h2 : ⊤ ≤ v.left ⁻¹ᵁ U₁ := by
      rw [← Scheme.Hom.comp_preimage, hv]
      exact h1
    rw [← hd _ h2] at key
    have e := evalPt_ptHom_ratioOn_mul _ _ h le_rfl h1 0
    have e2 : ∀ (k : Sp (DualNumber ℂ) ⟶ scheme W) (hk : ⊤ ≤ k ⁻¹ᵁ coordOpen W 1),
        v.left ≫ φ = k → (v.left.appLE U₁ ⊤ h2).hom f = (k.appLE (coordOpen W 1) ⊤ hk).hom (ratio W 1 0) := by
      rintro _ hk rfl
      rw [Scheme.Hom.comp_appLE]
      rfl
    rw [e2 _ h1 hv] at key
    have e3 := congrArg TrivSqZeroExt.snd e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_neg, _root_.mul_one,
      TrivSqZeroExt.snd_neg, DualNumber.snd_eps] at e3
    exact (neg_eq_iff_eq_neg.1 e3) ▸ key
  · filter_upwards [hn V le_rfl] with z hz
    have e := congrArg (valAt' (u.ex z).left V) (hth j i hV)
    rw [hf _ hz, _root_.mul_assoc, mul_comm _ (θ z), ← hθ i z (top_le_preimage_mono _ inf_le_right hz),
      ← valAt'_res _ (inf_le_right : V ≤ L.U i) _ hz]
    exact (valAt'_appLE _ φ _ V hV _ hz).symm.trans (e.trans (valAt'_mul _ V _ _))
  · beta_reduce
    rw [h0, hf _ hV0, valAt'_eq_valAt _ hz]
    have k : ∀ (x : Sp ℂ ⟶ scheme W) (hx : ⊤ ≤ x ⁻¹ᵁ originOpen W), x = spMap s ≫ zero W →
        TangentOrigin.evalPt x _ hx (originParam W) = 0 := by
      rintro _ hx rfl
      rw [TangentOrigin.evalPt_spMap_comp _ _ _ (zero_preimage_originOpen W).ge]
      exact (congrArg _ (originValue_originParam W)).trans (map_zero _)
    exact k _ hz he

theorem exists_keyIn_value_eq_discriminant' (R : Type) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] :
    ∃ x : KeyIn R, x.P.g = 1 ∧ ∀ (s : R →+* ℂ) (x' : KeyIn ℂ) (τ M : Matrix (Fin x'.P.g) (Fin x'.P.g) ℂ)
      (a b : Fin x'.P.g → ℂ) (c : ℂ), KeyPB x' x s → charHalf x'.P.g a b → NormalAt x' τ M a b c →
      M.det ^ 4 / c ^ 8 = s W.Δ := by
  obtain ⟨v, ⟨h, hv⟩, hb⟩ := exists_isLieBasis_ellPolAV W
  have hr : LB.Gen.IsGen (L := (ellPolAV W).L.pull (eSec (ellPolAV W).A)) ⟨fun _ => 1⟩ := by
    rw [eSec_ellPolAV]
    exact isGen_one_pull_zero W
  refine ⟨⟨ellPolAV W, le_rfl, _, hr, ellTheta W, fun p => ?_, ![v], hb⟩, rfl, ?_⟩
  · obtain ⟨x, hx, hx'⟩ := exists_mem_coordOpen_two W p
    exact ⟨x, hx, (nonzeroLocus_originSec W).ge hx'⟩
  rintro s x' τ M a b c ⟨φ, he, w, hg, F, hpb, -, hrig, hth, hF, hF', hvec⟩ hab ⟨u, -, hτ, hΛ, hu, hθ, hd⟩
  replace hg : x'.P.g = 1 := hg
  let i : Fin x'.P.g := (0 : Fin 1).cast hg.symm
  have hρ : F.comp (algebraMap R (DualNumber R)) = (algebraMap ℂ (DualNumber ℂ)).comp s := RingHom.ext hF
  have hP : (F ∘ ![DualNumber.eps, -1, 0]) = ![DualNumber.eps, -1, 0] := by
    ext1 j; fin_cases j
    · exact hF'
    · simp
    · simp
  have h' := h.map_comp F
  rw [hρ, hP] at h'
  have he' : eSec x'.P.A ≫ φ = spMap s ≫ zero W := he.trans (congrArg _ (eSec_ellPolAV W))
  have hv' : (x'.v i).left ≫ φ = ptHom W ((algebraMap ℂ (DualNumber ℂ)).comp s) ![DualNumber.eps, -1, 0] h' :=
    (hvec i).trans ((congrArg (spMap F ≫ ·) hv).trans
      ((SpecMap_ptHom W _ _ h _).trans (ptHom_congr W _ _ _ hρ hP _)))
  obtain ⟨hw, x, y, t, hx, hy, hper, heq, ht, ht0, ht1, hty, hlim⟩ :=
    UnifCoord.exists_coord_on_line R W s x'.P.A φ (x'.v i) h' hpb.1 he' hv' x'.P.L x'.P.g u _ (hd i)
  obtain ⟨L, hL⟩ := GlobalTheory.exists_periodPair_of_lattice_in_line x'.P.g u.Λ _ hg hw u.discrete u.full
  have hset : (L.lattice : Set ℂ) = {z | z • (2 * Real.pi * Complex.I)⁻¹ • M i ∈ u.Λ} := Set.ext hL
  have key := GlobalTheory.invariants_eq_of_periodic_solution L (W.map s) x y t 1 one_ne_zero (hset ▸ hx) (hset ▸ hy)
    (fun l hl => hper l ((hL l).1 hl)) (fun z hz => heq z fun e => hz ((hL z).2 e)) ht ht0 ht1 hty hlim
  simp only [one_pow, _root_.one_mul, WeierstrassCurve.map_Δ] at key
  rw [key.2.2]
  refine det_pow_div_eq hg τ M a b c hab hτ i ?_ L fun z => (hL z).trans (hΛ _)
  exact hasDerivAt_originFn W s x'.P.isLB u φ he' w x'.th _ hθ hth
    (valAt'_iso_mul_fr u w (fun _ => (congrArg _ (map_one _)).trans (map_one _)) hu hrig) (x'.v i) h' hv' _ (hd i)

theorem exists_keyIn_value_eq_discriminant : ThetaUnifAV → ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic], ∃ x : KeyIn R, x.P.g = 1 ∧ ∀ (s : R →+* ℂ) (x' : KeyIn ℂ) (τ M : Matrix (Fin x'.P.g) (Fin x'.P.g) ℂ) (a b : Fin x'.P.g → ℂ) (c : ℂ), KeyPB x' x s → charHalf x'.P.g a b → c ≠ 0 → NormalAt x' τ M a b c → M.det ^ 4 / c ^ 8 = s W.Δ := by
  intro _ R _ W _
  obtain ⟨x, hx, h⟩ := exists_keyIn_value_eq_discriminant' R W
  exact ⟨x, hx, fun s x' τ M a b c h₁ h₂ _ h₃ => h s x' τ M a b c h₁ h₂ h₃⟩

end GlobalTheory.EllipticKey
