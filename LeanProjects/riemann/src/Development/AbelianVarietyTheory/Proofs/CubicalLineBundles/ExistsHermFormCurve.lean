import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsDiagonalCoordinates
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsHomFamilyComplex
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilPairingEqOfIsomorphicCubePairings
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilEqIffHermFormEqComplex
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegersOfCmFieldConjStructure
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveLieCharacterOfAdjoinGenerator
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearLiftOfIsMonHomPolAV

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.TenExp

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem countable_lattice : (u.Λ : Set (Fin g → ℂ)).Countable := by
  have := u.discrete
  exact (countable_of_Lindelof_of_discrete : Countable u.Λ)

theorem lift_unique {U : Type*} [AddCommGroup U] [Module ℂ U] {F F' : U →ₗ[ℂ] (Fin g → ℂ)}
    (h : ∀ z, u.ex (F z) = u.ex (F' z)) : F = F' :=
  linear_eq_of_countable (countable_lattice u) fun z => (u.ker _).1 (by
    have e := u.ex_add (F z - F' z) (F' z)
    rw [sub_add_cancel, h] at e
    exact mul_eq_right.1 e.symm)

theorem ex_smul_of_isLieComb (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) {v : epsR ℂ ⟶ P.A}
    (hv : IsLieBasis ![v]) (f : P.A ⟶ P.A) [hf : IsMonHom f] {a : ℂ} (ha : IsLieComb ![a] ![v] (v ≫ f)) (z : Fin P.g → ℂ) :
    u.ex (a • z) = u.ex z ≫ f := by
  obtain ⟨h₁, h₂⟩ := TorusTransfer.tangent_bijective u P.smoothDim
  obtain ⟨F, hF⟩ := exists_linear_lift_of_isMonHom_polAV P P P.L P.L u u f hf
  have hv0 : IsTangent v := hv.1 0
  obtain ⟨w, hw, -⟩ := h₁ v hv0
  have key : ∀ c x v', IsTangent v' → u.IsDiff x v' → IsLieComb ![c] ![v] v' → x = c • w := fun c x v' ht hd hc => by
    have e : v' = CMCurveTest.scaleVec c v := Over.OverMorphism.ext ((LieChar.isLieComb_one_iff _ _ _).1 hc)
    exact (h₁ v' ht).unique hd (e ▸ CMCurveTest.isDiff_scaleVec u hw c)
  have hFw := key a _ _ (HomLinear.isTangent_comp f hv0) (HomLinear.isDiff_comp u u f F hF hv0 hw) ha
  obtain ⟨v', ⟨ht, hd⟩, -⟩ := h₂ z
  obtain ⟨c, hc, -⟩ := hv.2 v' ht
  obtain ⟨c, rfl⟩ : ∃ c', c = ![c'] := ⟨c 0, by funext i; fin_cases i; rfl⟩
  rw [← hF, key c z v' ht hd hc, map_smul, hFw, smul_comm]

theorem exists_hermForm_curve (hT : ThetaUnifAV) (P : Out.PolAV (Sp ℂ)) (hg : P.g = 1) (u₀ : HolUnif P.A P.L P.g)
    {d : ℕ} (hd : 0 < d) {c : ℂ} (hc : c ≠ 0) (hΛ : PureType.IsQuadLattice u₀.Λ d c) :
    ∃ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ)
      (G : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ)), u.IsAH Hm χ ∧ (∀ z, u.ex (G z) = u₀.ex z) ∧
      ∀ z w : ℂ, hermForm Hm (G fun _ => c * z) (G fun _ => c * w) = 2 * z * starRingEnd ℂ w / Real.sqrt d := by
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, -, -, hE, hb, -⟩ := hT P rig hrig
  obtain ⟨G, hG⟩ := exists_linear_lift_of_isMonHom_polAV P P P.L P.L u₀ u (𝟙 _) inferInstance
  simp only [Category.comp_id] at hG
  let i₀ : Fin P.g := ⟨0, by omega⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℂ, ∀ z : ℂ, (G fun _ => z) = fun _ => κ * z := ⟨G (fun _ => 1) i₀, fun z => by
    have e : (fun _ => z : Fin P.g → ℂ) = z • fun _ => (1 : ℂ) := by funext i; simp
    rw [e, map_smul, PureType.eq_const hg (G _) i₀]
    funext i
    simp [mul_comm]⟩
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    have : (LinearMap.id : (Fin P.g → ℂ) →ₗ[ℂ] _) = 0 := lift_unique u₀ fun z => by
      rw [LinearMap.id_apply, LinearMap.zero_apply, ← hG, ← hG, map_zero, PureType.eq_const hg z i₀, hκ]
      simp only [zero_mul]
      rfl
    exact one_ne_zero (congrFun (DFunLike.congr_fun this 1) i₀)
  have hΛ' : PureType.IsQuadLattice u.Λ d (κ * c) := fun z => by
    have e : z = G fun _ => κ⁻¹ * z i₀ := by
      rw [hκ, mul_inv_cancel_left₀ hκ0]
      exact PureType.eq_const hg z i₀
    rw [← u.ker, e, hG, u₀.ker, hΛ, hκ]
    refine exists₂_congr fun m n => ⟨fun h => ?_, fun h => ?_⟩
    · rw [congrFun h i₀, _root_.mul_assoc]
    · funext _
      exact mul_left_cancel₀ hκ0 ((congrFun h i₀).trans (_root_.mul_assoc _ _ _))
  refine ⟨u, Hm, χ, G, hAH, hG, fun z w => ?_⟩
  rw [hκ, hκ, ← PureType.hermForm_of_isQuadLattice hg hd (mul_ne_zero hκ0 hc) hΛ' hAH.1 hAH.2.1 hE hb.2]
  simp only [_root_.mul_assoc]

end Unif

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_isExp (T : PAT H (Sp ℂ)) (D : Datum H) (u : HolUnif T.t.G T.t.PP.L T.g)
    {Hm : Matrix (Fin T.g) (Fin T.g) ℂ} (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin T.g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) (P : D.La →+ (Fin T.g → ℂ))
    (hi : Function.Injective P) (hΛ : ∀ v, v ∈ u.Λ ↔ v ∈ P.range)
    (hE : ∀ a b, (hermForm Hm (P a) (P b)).im = D.EF a b)
    (hW : ∀ (k : ℕ) (a b : D.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a b : ℂ) / k) →
      Out.WeilIs T.t.G T.t.PP.L k (u.ex ((k : ℂ)⁻¹ • P a)) (u.ex ((k : ℂ)⁻¹ • P b)) (unitOn c))
    (r : 𝓞 E → Module.End ℂ (Fin T.g → ℂ)) (hr : ∀ s z, u.ex (r s z) = u.ex z ≫ T.t.act.act s)
    (hrP : ∀ s a, r s (P a) = P (s • a)) {g : ℕ} (B : (Fin T.g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (ty : Fin g → (E →+* ℂ))
    (hB : ∀ (s : 𝓞 E) v j, B (r s v) j = ty j (s : E) * B v j) :
    ∃ e : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ T.t.G),
      IsExp T (RingHom.id ℂ) D ty (B.toAddEquiv.toAddMonoidHom.comp P) e ∧ ∀ z, (e (B z)).left = (u.ex z).left := by
  have hrange : ∀ z, z ∈ (B.toAddEquiv.toAddMonoidHom.comp P).range ↔ B.symm z ∈ u.Λ := fun z => by
    rw [hΛ]
    exact exists_congr fun a => B.eq_symm_apply.symm
  have hper : IsPeriod D ty (B.toAddEquiv.toAddMonoidHom.comp P) := by
    have key := PureType.hermForm_mulVec (LinearMap.toMatrix' B.symm.toLinearMap) Hm
    simp only [LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe] at key
    refine ⟨fun s a i => ?_, B.injective.comp hi, ?_, ?_, _,
      Matrix.isHermitian_mul_mul_conjTranspose (LinearMap.toMatrix' B.symm.toLinearMap).transpose hH,
      fun z hz => ?_, fun a b => ?_⟩
    · exact (congrArg (fun v => B v i) (hrP s a).symm).trans (hB s _ i)
    · have := u.discrete
      refine DiscreteTopology.of_continuous_injective
        (f := fun z : (B.toAddEquiv.toAddMonoidHom.comp P).range => (⟨B.symm z, (hrange _).1 z.2⟩ : u.Λ))
        ((B.symm.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _)
        fun z w h => Subtype.ext (B.symm.injective (congrArg Subtype.val h))
    · have e : Set.range (B.toAddEquiv.toAddMonoidHom.comp P) = (B.restrictScalars ℝ).toLinearMap '' u.Λ := by
        ext z
        refine (hrange z).trans ⟨fun h => ⟨_, h, B.apply_symm_apply z⟩, ?_⟩
        rintro ⟨v, hv, rfl⟩
        exact (B.symm_apply_apply v).symm ▸ hv
      rw [e, ← Submodule.map_span, u.full, Submodule.map_top, LinearEquiv.range]
    · rw [key]
      exact hpos _ (B.symm.map_ne_zero_iff.2 hz)
    · rw [key, ← hE]
      simp
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
  unfold IsExp
  rw [hid]
  refine ⟨fun z => u.ex (B.symm z), ⟨hper, fun U f => ?_, fun z w => ?_, u.ex_onto.comp B.symm.surjective,
    fun z => (u.ker _).trans (hrange z).symm, fun s z => ?_, fun k a b c hk hc => ?_⟩, fun z => by simp⟩
  · simp only [Set.mem_univ, true_and]
    let ψ := LinearMap.toContinuousLinearMap B.symm.toLinearMap
    exact ⟨(u.hol U f).1.preimage ψ.continuous, (u.hol U f).2.comp ψ.differentiableOn fun _ h => h⟩
  · exact (congrArg u.ex (map_add _ _ _)).trans (u.ex_add _ _)
  · refine Eq.trans (congrArg u.ex ?_) (hr s _)
    rw [LinearEquiv.symm_apply_eq]
    funext j
    rw [hB, LinearEquiv.apply_symm_apply]
  · have e : ∀ a, B.symm ((k : ℂ)⁻¹ • (B.toAddEquiv.toAddMonoidHom.comp P) a) = (k : ℂ)⁻¹ • P a := fun a => by simp
    simp only [e]
    exact hW k a b c hk hc

set_option maxHeartbeats 400000 in

theorem exists_isExp_of_isTen : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ω : ℂ) (C : Ell H ℂ ω) (u₀ : HolUnif C.P.A C.P.L C.P.g) (c : ℂ) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (T : PAT H (Sp ℂ)) (t : IsTen C D h T), c ≠ 0 → PureType.IsQuadLattice u₀.Λ H.d c → 0 < ((ε : ℤ) : ℝ) * ω.im → IsKForm D ε h → (D.q = 0 ∧ 2 * ω - 1 = H.rt0) ∨ (D.p = 0 ∧ 2 * ω - 1 = -H.rt0) →
  ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ T.t.G)), IsTypeFn H D.p D.q ty ∧ IsExp T (RingHom.id ℂ) D ty Pe e ∧ (∀ a (z : ℂ), (e (z • Pe a)).left = (u₀.ex (fun _ => c * z) ≫ t.ten.tmul a).left) ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (f : D.La →+ V), (∀ a, f (H.w0 • a) = ω • f a) → ∃ F : (Fin g → ℂ) →ₗ[ℂ] V, ∀ a, F (Pe a) = f a := by
  intro hT hL E _ _ _ H ω C u₀ c D ε h T t hc hΛ hε hh hsig
  obtain ⟨τ₀, hτ, hτv⟩ := LieChar.ell_char E H ℂ ω C
  have hact : ∀ o z, u₀.ex (τ₀ o • z) = u₀.ex z ≫ C.act.act o := fun o z =>
    ex_smul_of_isLieComb C.P u₀ C.basis _ (hf := C.act.hom o) (hτv o) z
  have hgen : ∀ o : OK H, ∃ m n : ℤ, o = m + n * wK H := fun o => by
    obtain ⟨m, hm, -⟩ := (OK_isDedekindDomain_and_projective E H).2.1 o
    exact ⟨_, _, hm⟩
  have hd : (0 : ℝ) < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast H.d_prime.pos)
  have hrt : H.rt0 ≠ 0 := fun h0 => by
    have := H.sqrt_neg_disc_sq
    rw [h0] at this
    exact H.d_prime.ne_zero (by simpa using this)
  have hω : ω = (1 + Complex.I * Real.sqrt H.d) / 2 ∨ ω = 1 - (1 + Complex.I * Real.sqrt H.d) / 2 := by
    have e : (2 * ω - 1) ^ 2 = (Complex.I * Real.sqrt H.d) ^ 2 := by
      rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
      rcases hsig with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h, H.sqrt_neg_disc_sq]
    exact (sq_eq_sq_iff_eq_or_eq_neg.1 e).imp (fun h => by linear_combination h / 2) fun h => by
      linear_combination h / 2
  have hεω : ((ε : ℤ) : ℝ) * ω.im = Real.sqrt H.d / 2 := by
    rcases Int.units_eq_one_or ε with rfl | rfl <;> rcases hω with rfl | rfl <;> simp at hε ⊢ <;> linarith
  have hsemi : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (f : D.La →+ V), (∀ a, f (H.w0 • a) = ω • f a) →
      ∀ (o : OK H) a, f (o • a) = τ₀ o • f a := fun V _ _ f hf o a => by
    obtain ⟨m, n, rfl⟩ := hgen o
    rw [add_smul, mul_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_add, map_zsmul, map_zsmul,
      show wK H • a = H.w0 • a from rfl, hf]
    simp [hτ, add_smul, mul_smul, Int.cast_smul_eq_zsmul]
  obtain ⟨rig, hrig⟩ := T.pol.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, -, -, hE, -, hW⟩ := hT T.pol rig hrig
  choose F hF using fun a => exists_linear_lift_of_isMonHom_polAV C.P T.pol _ _ u₀ u (t.ten.tmul a) inferInstance
  choose R hR using fun s => exists_linear_lift_of_isMonHom_polAV T.pol T.pol _ _ u u (T.t.act.act s) (T.t.act.hom s)
  let P : D.La →+ (Fin T.g → ℂ) := AddMonoidHom.mk' (fun a => F a fun _ => c) fun a b => by
    have : F (a + b) = F a + F b := lift_unique u fun z => by
      rw [LinearMap.add_apply, u.ex_add, hF, hF, hF, t.ten.tmul_add, MonObj.comp_mul]
    rw [this, LinearMap.add_apply]
  have hFz : ∀ a (z : ℂ), F a (fun _ => c * z) = z • P a := fun a z => by
    refine Eq.trans (congrArg (F a) ?_) (map_smul (F a) z _)
    funext _
    simp [mul_comm]
  have hPz : ∀ (z : ℂ) a, u.ex (z • P a) = u₀.ex (fun _ => c * z) ≫ t.ten.tmul a := fun z a => by rw [← hFz, hF]
  have hRP : ∀ s a, R s (P a) = P (s • a) := fun s a => by
    have : R s ∘ₗ F a = F (s • a) := lift_unique u fun z => by
      rw [LinearMap.comp_apply, hR, hF, hF, t.lin, Category.assoc]
    exact DFunLike.congr_fun this _
  have hP : ∀ (o : OK H) a, P (o • a) = τ₀ o • P a := fun o a => by
    have : F (o • a) = τ₀ o • F a := lift_unique u fun z => by
      rw [LinearMap.smul_apply, ← map_smul, hF, hF, hact, t.ten.tmul_smul', Category.assoc]
    exact DFunLike.congr_fun this _
  have hform : ∀ a b, (hermForm Hm (P a) (P b)).im = D.EF a b := fun a b => by
    obtain ⟨u₁, H₁, χ₁, G, hAH₁, hG, hH₁⟩ := exists_hermForm_curve hT C.P C.dim u₀ H.d_prime.pos hc hΛ
    have := (weilEq_iff_hermForm_eq hT hL C.P C.P T.pol C.P u₀ u₀ u u₁ Hm H₁ χ χ₁ hAH hAH₁ _ _ _ _ (F a) (F b)
      (τ₀ (h a b) • G) G (hF a) (hF b) (fun z => by rw [LinearMap.smul_apply, ← map_smul, hG, hact])
      (fun z => by rw [hG, Category.comp_id])).1
      (weilEq_of_lamEq hL ℂ C.P C.P T.pol C.P _ _ _ _ inferInstance inferInstance (C.act.hom _) inferInstance
        (t.lam a b)) (fun _ => c * 1) (fun _ => c * 1)
    have e : τ₀ (h a b) • (fun _ => c * 1 : Fin C.P.g → ℂ) = fun _ => c * τ₀ (h a b) := by
      funext _
      simp [mul_comm]
    rw [hFz, hFz, one_smul, one_smul, LinearMap.smul_apply, ← map_smul, e, hH₁] at this
    have e' : h a b = (((ε : ℤ) * (D.EF (H.w0 • a) b - D.EF a b) : ℤ) : OK H) +
        (((ε : ℤ) * D.EF a b : ℤ) : OK H) * wK H := Subtype.ext (hh a b)
    rw [this, e', map_add, map_mul, map_intCast, map_intCast, hτ, map_one, _root_.mul_one, Complex.div_ofReal_im]
    simp only [Complex.mul_im, Complex.add_im, Complex.intCast_im, Complex.intCast_re, Complex.re_ofNat,
      Complex.im_ofNat]
    push_cast
    field_simp
    linear_combination (2 * (D.EF a b : ℝ)) * hεω
  have hi : Function.Injective P := (injective_iff_map_eq_zero _).2 fun a ha => D.unimod.1 (by
    ext b
    have := hform a b
    rw [ha] at this
    simp only [hermForm, zero_dotProduct, Complex.zero_im] at this
    rw [map_zero, LinearMap.zero_apply]
    exact_mod_cast this.symm)
  let _ : Algebra (OK H) ℂ := τ₀.toAlgebra
  let e₀ : ℂ →ₗ[OK H] Serre.Pts C.act (𝟙_ _) :=
    { toFun := fun z => Serre.Pts.mk _ (u₀.ex fun _ => c * z)
      map_add' := fun z w => Serre.Pts.ext (Eq.trans (congrArg u₀.ex (funext fun _ => mul_add _ _ _)) (u₀.ex_add _ _))
      map_smul' := fun o z => Serre.Pts.ext (Eq.trans (congrArg u₀.ex (funext fun _ => mul_left_comm _ _ _))
        (hact o _)) }
  let ex : (Fin T.g → ℂ) →+ Serre.Pts (Serre.comapAct T.t.act (algebraMap (OK H) (𝓞 E))) (𝟙_ _) :=
    AddMonoidHom.mk' (fun z => Serre.Pts.mk _ (u.ex z)) fun z w => Serre.Pts.ext (u.ex_add z w)
  have hex : ∀ v, ex v = 0 ↔ v ∈ u.Λ := u.ker
  let i₀ : Fin C.P.g := ⟨0, by rw [C.dim]; exact one_pos⟩
  obtain ⟨hsp, hker, huniv⟩ := tensor_unif (t.ten.equiv (𝟙_ _)) e₀
    (fun x => by
      obtain ⟨z, hz⟩ := u₀.ex_onto x.hom
      refine ⟨c⁻¹ * z i₀, Serre.Pts.ext (Eq.trans (congrArg u₀.ex ?_) hz)⟩
      rw [mul_inv_cancel_left₀ hc]
      exact (PureType.eq_const C.dim z i₀).symm)
    (fun z => by
      refine (u₀.ker _).trans ((hΛ _).trans ⟨?_, ?_⟩)
      · rintro ⟨m, n, e⟩
        have e := mul_left_cancel₀ hc (congrFun e i₀)
        rcases hω with hω | hω
        · exact ⟨m + n * wK H, show τ₀ _ = z by simp [e, hτ, hω]⟩
        · exact ⟨m + n * (1 - wK H), show τ₀ _ = z by simp [e, hτ, hω]⟩
      · rintro ⟨o, rfl⟩
        obtain ⟨m, n, rfl⟩ := hgen o
        have e : algebraMap (OK H) ℂ (m + n * wK H) = m + n * ω := show τ₀ _ = _ by simp [hτ]
        rw [e]
        rcases hω with hω | hω
        · exact ⟨m, n, funext fun _ => by linear_combination c * n * hω⟩
        · exact ⟨m + n, -n, funext fun _ => by push_cast; linear_combination c * n * hω⟩)
    ex (by simp only [hex]; exact countable_lattice u) P hP hi
    (fun z a => Serre.Pts.ext ((hPz z a).trans (t.ten.hom_equiv_tmul a (e₀ z)).symm))
  have ext : ∀ f f' : Module.End ℂ (Fin T.g → ℂ), (∀ a, f (P a) = f' (P a)) → f = f' := fun f f' e =>
    LinearMap.ext_on_range hsp e
  let r : 𝓞 E →+* Module.End ℂ (Fin T.g → ℂ) := RingHom.mk'
    { toFun := R
      map_one' := ext _ _ fun a => by rw [hRP, one_smul]; rfl
      map_mul' := fun s s' => ext _ _ fun a => by rw [Module.End.mul_apply, hRP, hRP, hRP, mul_smul] }
    fun s s' => ext _ _ fun a => (hRP _ _).trans (by
      rw [add_smul, map_add, ← hRP, ← hRP]; rfl)
  obtain ⟨g, B, ty, hB⟩ := exists_diagonal_coordinates r
  have hΛP : ∀ v, v ∈ u.Λ ↔ v ∈ P.range := fun v => (hex v).symm.trans (hker v)
  obtain ⟨e, he, heB⟩ := exists_isExp T D u hAH.1 hAH.2.1 P hi hΛP hform (fun k a b c hk hc => by
    have hEf : Ef ⟨P a, (hΛP _).2 ⟨a, rfl⟩⟩ ⟨P b, (hΛP _).2 ⟨b, rfl⟩⟩ = D.EF a b :=
      Int.cast_injective (α := ℝ)
        ((hE ⟨P a, (hΛP _).2 ⟨a, rfl⟩⟩ ⟨P b, (hΛP _).2 ⟨b, rfl⟩⟩).trans (hform a b))
    exact hW k ⟨P a, (hΛP _).2 ⟨a, rfl⟩⟩ ⟨P b, (hΛP _).2 ⟨b, rfl⟩⟩ c hk (by rw [hEf]; exact hc)) R hR hRP B ty hB
  have hu : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (f : D.La →+ V), (∀ a, f (H.w0 • a) = ω • f a) →
      ∃ F : (Fin g → ℂ) →ₗ[ℂ] V, ∀ a, F ((B.toAddEquiv.toAddMonoidHom.comp P) a) = f a := fun V _ _ f hf => by
    obtain ⟨F, hF⟩ := huniv V f (hsemi V f hf)
    exact ⟨F ∘ₗ B.symm.toLinearMap, fun a => by simp [hF]⟩
  refine ⟨g, ty, _, e, fun τ => ?_, he, fun a z => ?_, hu⟩
  · have := D.fin
    have hcard := card_type (ty := ty) (P := B.toAddEquiv.toAddMonoidHom.comp P) he.1.1
      (by
        have : Set.range (B.toAddEquiv.toAddMonoidHom.comp P) = B.toLinearMap '' Set.range P := Set.range_comp B P
        rw [this, ← Submodule.map_span, hsp, Submodule.map_top, LinearEquiv.range])
      (w := H.w0) (ω := ω) (fun a => by
        have : P (H.w0 • a) = ω • P a := hτ ▸ hP (wK H) a
        simp [this]) (hu ℂ) τ
    rw [D.rank] at hcard
    have h2 : 2 * τ H.w0 = 1 + τ H.rt := by
      simpa [map_ofNat] using congrArg (fun x : 𝓞 E => τ x) H.two_weight_eq_one_add_root
    have h3 : τ H.rt ^ 2 = H.rt0 ^ 2 := by
      rw [H.sqrt_neg_disc_sq]
      simpa using congrArg (fun x : 𝓞 E => τ x) H.rt_sq
    rcases hsig with ⟨h0, hs⟩ | ⟨h0, hs⟩
    · rw [h0] at hcard ⊢
      exact ⟨fun e => hcard.1 (by linear_combination (h2 + e - hs) / 2),
        fun e => hcard.2 fun e' => e (by linear_combination 2 * e' + hs - h2)⟩
    · rw [h0, zero_add] at hcard
      rw [h0]
      exact ⟨fun e => hcard.2 fun e' => hrt (by linear_combination (2 * e' + hs - h2 - e) / 2),
        fun e => hcard.1 (by linear_combination (h2 + (sq_eq_sq_iff_eq_or_eq_neg.1 h3).resolve_left e - hs) / 2)⟩
  · rw [← hPz, ← heB, map_smul]
    rfl

end GlobalTheory.CM.TenExp
