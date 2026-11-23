import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.EllipticFibrePrincipalData
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsKroneckerCharIff
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsEtaMeanOfIsKroneckerChar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConjAction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.T2SpacePtsOverOfIsSeparated
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsDerivAt0NotIsDerivAlong

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexConjugate

noncomputable section
namespace GlobalTheory.CM.FamCompare

open GlobalTheory.IndefiniteRowSideFullHecke

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isKroneckerChar_iff (χ : DirichletCharacter ℂ H.d) : IsKroneckerChar χ ↔ χ = EllipticFibrePrincipalData.chi H :=
  Compare.isKroneckerChar_iff χ

theorem logOm_eq [NeZero H.d] {χ : DirichletCharacter ℂ H.d} (h : IsKroneckerChar χ) :
    logOm E χ = (EllipticFibrePrincipalData.logOm H : ℝ) :=
  Compare.logOm_eq h

theorem logOm_quadratic [NeZero H.d] {χ : DirichletCharacter ℂ H.d} (h : IsKroneckerChar χ) {K : Type} [Field K]
    [NumberField K] (h2 : Module.finrank ℚ K = 2) (hD : discr K = -H.d) :
    logOm K χ = ((EllipticFibrePrincipalData.logOm H + Real.log (rootDiscr E / √H.d) : ℝ) : ℂ) := by
  rw [Compare.logOm_eq_logOmCurve h h2 hD]
  have h₁ : (0 : ℝ) < rootDiscr E := by
    rw [rootDiscr_def]
    exact Real.rpow_pos_of_pos (by exact_mod_cast abs_pos.2 (discr_ne_zero E)) _
  have h₂ : (0 : ℝ) < √H.d := Real.sqrt_pos.2 (Nat.cast_pos.2 H.d_prime.pos)
  have h₃ : (2 * Real.pi) ≠ 0 := by positivity
  congr 1
  show _ = Real.eulerMascheroniConstant + Real.log (2 * Real.pi / rootDiscr E) - LogarithmicDifferentialCharacter.dlogL H + _
  rw [LogarithmicDifferentialCharacter.logOmCurve, Real.log_div h₃ h₁.ne', Real.log_div h₃ h₂.ne', Real.log_div h₁.ne' h₂.ne']
  ring

section Curve

variable {R R' : Type} [CommRing R] [CommRing R'] {ω : R} {ω' : R'}

theorem ellMap_iff (C' : Ell H R' ω') (C : Ell H R ω) (f : R →+* R') (φ : C'.P.A.left ⟶ C.P.A.left) :
    EllMap C' C f φ ↔ EllipticFibrePrincipalData.IsEllFibre f C C' φ :=
  ⟨fun ⟨a, b, c, d⟩ => ⟨a.symm, b, d, c⟩, fun h => ⟨h.val.symm, h.fib, h.vec, h.act⟩⟩

theorem isPrincipalAt_iff (C : Ell H R ω) (s : R →+* ℂ) : C.IsPrincipalAt s ↔ EllipticFibrePrincipalData.IsPrincipalAt C s := Iff.rfl

variable {M : Type} [Field M] [NumberField M] {w : 𝓞 M}

theorem hasPeriod_iff (C : Ell H (𝓞 M) w) (x : ℝ) : C.HasPeriod x ↔ EllipticFibrePrincipalData.IsLogPeriod C x :=
  exists_congr fun _ => and_congr (forall_congr' fun _ => and_congr_right fun _ =>
    ⟨fun h => (h _).2 rfl, fun h _ => ⟨CMCurveCompare.isLieNormSq_unique (C.basis.1 0) h, fun e => e ▸ h⟩⟩) eq_comm

theorem hasPeriod_logOm_iff [NeZero H.d] {χ : DirichletCharacter ℂ H.d} (h : IsKroneckerChar χ) {K : Type} [Field K]
    [NumberField K] (h2 : Module.finrank ℚ K = 2) (hD : discr K = -H.d) (C : Ell H (𝓞 M) w) :
    C.HasPeriod (logOm K χ).re ↔ EllipticFibrePrincipalData.HasPeriod C := by
  rw [logOm_quadratic h h2 hD, Complex.ofReal_re, hasPeriod_iff]
  rfl

end Curve

section Family

variable {R : Type} [CommRing R] {ω : R}

def conjEll (C : Ell H R ω) : Ell H R (1 - ω) where
  P := C.P
  dim := C.dim
  act := Serre.comapAct C.act (EllConj.barK H)
  v := C.v
  basis := C.basis
  eig := EllConj.isLieComb_one_sub C.v (C.basis.1 0) ω (C.act.act (wK H)) _
    (by rw [Serre.comapAct_act, ← C.act.add, EllConj.barK_wK_add, C.act.one]) C.eig
  adj x y h := C.adj _ _ (congrArg H.bar h)
  prim := LBIso.trans C.P.isLB (DVR.linComb_isLB _ C.P.isLB _ _) (DVR.linComb_isLB _ C.P.isLB _ _) C.prim
    (EllConj.lbIso_of_adj C.P.isLB (C.adj (EllConj.barK H (wK H)) (wK H) (HostModel.bar_bar H _).symm))

theorem isLinearHom_iff {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (a : OAct (OK H) A) (b : OAct (OK H) B)
    (f : A ⟶ B) : Serre.IsLinearHom a b f ↔ IsMonHom f ∧ a.act (wK H) ≫ f = f ≫ b.act (wK H) := by
  refine ⟨fun h => ⟨h.1, h.2 _⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, ?_⟩⟩
  let N : Subring (OK H) :=
    { carrier := {c | a.act c ≫ f = f ≫ b.act c}
      mul_mem' := fun {x y} (hx : _ = _) (hy : _ = _) => show _ = _ by
        rw [a.mul, b.mul, Category.assoc, hy, ← Category.assoc, hx, Category.assoc]
      one_mem' := show _ = _ by rw [a.one, b.one, Category.id_comp, Category.comp_id]
      add_mem' := fun {x y} (hx : _ = _) (hy : _ = _) => show _ = _ by
        rw [a.add, b.add, MonObj.mul_comp, MonObj.comp_mul, hx, hy]
      zero_mem' := show _ = _ by rw [Serre.act_zero, Serre.act_zero, MonObj.one_comp, MonObj.comp_one]
      neg_mem' := fun {x} (hx : _ = _) => show _ = _ by
        have e₁ : (a.act (-x) ≫ f) * (a.act x ≫ f) = 1 := by
          rw [← MonObj.mul_comp, ← a.add, neg_add_cancel, Serre.act_zero, MonObj.one_comp]
        have e₂ : (f ≫ b.act (-x)) * (f ≫ b.act x) = 1 := by
          rw [← MonObj.comp_mul, ← b.add, neg_add_cancel, Serre.act_zero, MonObj.comp_one]
        exact mul_right_cancel (e₁.trans (hx ▸ e₂.symm)) }
  rintro ⟨c, hc⟩
  show (⟨c, hc⟩ : OK H) ∈ N
  induction hc using Algebra.adjoin_induction with
  | mem x hx =>
    obtain rfl : x = H.w0 := hx
    exact h₂
  | algebraMap r => exact (show ((r : ℤ) : OK H) = ⟨algebraMap ℤ (𝓞 E) r, _⟩ from Subtype.ext (by simp)) ▸ intCast_mem N r
  | add x y hx hy k₁ k₂ => exact N.add_mem k₁ k₂
  | mul x y hx hy k₁ k₂ => exact N.mul_mem k₁ k₂

theorem barK_wK : EllConj.barK H (wK H) = EllipticFibrePrincipalData.wSide H false :=
  eq_sub_of_add_eq (EllConj.barK_wK_add H)

theorem barK_kForm (D : Datum H) (ε : ℤˣ) (x y : D.La) :
    EllConj.barK H (EllipticFibrePrincipalData.kForm D ε true x y) = EllipticFibrePrincipalData.kForm D ε false x y := by
  rw [EllipticFibrePrincipalData.kForm, EllipticFibrePrincipalData.kForm, map_add, map_mul, map_intCast, map_intCast, ← barK_wK]
  rfl

theorem isKForm_iff {D : Datum H} {ε : ℤˣ} (h : D.La → D.La → OK H) : IsKForm D ε h ↔ h = EllipticFibrePrincipalData.kForm D ε true :=
  ⟨fun a => Compare.isKForm_unique a (EllipticFibrePrincipalData.isKForm_kForm D ε), fun e => e ▸ EllipticFibrePrincipalData.isKForm_kForm D ε⟩

variable {C : Ell H R ω} {T : PAT H (Sp R)} {D : Datum H} {L : Submodule (𝓞 E) D.La} {φ : L → (C.P.A ⟶ T.t.G)}
  {ε : ℤˣ} {h : D.La → D.La → OK H}

theorem isFam_iff (hh : IsKForm D ε h) : IsFam C T h L φ ↔ EllipticFibrePrincipalData.IsHomFam C T.t L ε true φ := by
  obtain rfl := (isKForm_iff h).1 hh
  simp only [IsFam, isLinearHom_iff]
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨fun x => (a x).1, b, c, fun x => (a x).2, d⟩,
    fun k => ⟨fun x => ⟨k.hom x, k.side x⟩, k.add, k.smul, k.lam⟩⟩

theorem isFam_conj_iff (hh : IsKForm D ε h) : IsFam (conjEll C) T h L φ ↔ EllipticFibrePrincipalData.IsHomFam C T.t L ε false φ := by
  obtain rfl := (isKForm_iff h).1 hh
  have e₁ : (conjEll C).act.act (wK H) = C.act.act (EllipticFibrePrincipalData.wSide H false) := congrArg C.act.act barK_wK
  have e₂ : ∀ a b, (conjEll C).act.act (EllipticFibrePrincipalData.kForm D ε true a b) = C.act.act (EllipticFibrePrincipalData.kForm D ε false a b) :=
    fun a b => congrArg C.act.act (barK_kForm D ε a b)
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨fun x => (a x).1, b, c, fun x => e₁ ▸ (a x).2 (wK H), fun x y => e₂ x y ▸ d x y⟩,
    fun k => ⟨fun x => (isLinearHom_iff _ _ _).2 ⟨k.hom x, e₁.symm ▸ k.side x⟩, k.add, k.smul,
      fun x y => (e₂ x y).symm ▸ k.lam x y⟩⟩

end Family

theorem deriv_of_hol {S : Scheme.{0}} (P : Out.PolAV S) (y : Sp ℂ ⟶ S) {g : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ P.A)}
    (ha : ∀ z w, e (z + w) = e z * e w) (hs : Function.Surjective e) (hh : IsHolTo Set.univ fun z => (e z).left)
    (hc : {z | e z = 1}.Countable) : PointUnif.IsExp e := by
  obtain ⟨Q, φ, -, hφ, hL⟩ := PureType.exists_baseChange polBaseChange_holds y P
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨u, -, -, -, -, -, h₁, h₂, -⟩ := thetaUnifAV_all Q rig hrig
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (𝟙_ (Over (Sp ℂ)) ⟶ Q.A) ≃* (Over.mk y ⟶ P.A), ∀ p, (Φ p).left = p.left ≫ φ := by
    have key : ∀ t, (𝟙_ (Over (Sp ℂ))).hom ≫ y = t →
        ∃ Φ : (𝟙_ (Over (Sp ℂ)) ⟶ Q.A) ≃* (Over.mk t ⟶ P.A), ∀ p, (Φ p).left = p.left ≫ φ := by
      rintro _ rfl
      exact ⟨ObjPull.pushEquiv hφ _, fun _ => rfl⟩
    exact key y (Category.id_comp y)
  have he := PointUnif.isExp_push hφ u h₁ h₂ Φ hΦ
  have := P.isAb.proper
  have := u.discrete
  have : IsZLattice ℝ u.Λ := ⟨u.full⟩
  obtain ⟨F, hF⟩ := UnifPoint.IsExp.exists_linearEquiv (e := fun z => Φ (u.ex z)) he u.Λ
    (fun z => (map_eq_one_iff Φ Φ.injective).trans (u.ker z)) ha hs hh hc
  have := he.comp_equiv F
  simpa only [hF] using this

theorem isExp_iff {R : Type} [CommRing R] (T : PAT H (Sp R)) (σ : R →+* ℂ) (D : Datum H) {g : ℕ}
    (ty : Fin g → (E →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk (spMap σ) ⟶ T.t.G)) :
    IsExp T σ D ty Pe e ↔ EllipticFibrePrincipalData.IsExp T.t (spMap σ) D ty Pe e := by
  refine ⟨fun ⟨a, b, c, d, f, l, w⟩ => ?_, fun h => ⟨h.period, h.hol, h.add, h.onto, h.ker, h.lin, h.weil⟩⟩
  have hc : {z | e z = 1}.Countable := by
    obtain ⟨_, _⟩ := PeriodCompare.finiteDimensional D
    have : Countable D.La := Finsupp.Countable.of_moduleFinite (R := ℤ)
    exact (Set.countable_range Pe).mono fun z hz => (f z).1 hz
  have k := deriv_of_hol T.pol (spMap σ) c d b hc
  exact ⟨a, c, d, f, l, b, k.2.2.2.1, k.2.2.2.2, w⟩

section Degree

variable {K : Type} [Field K] [NumberField K]

theorem isThetaDeg_iff (x : KeyIn K) (δ : ℝ) : IsThetaDeg x δ ↔ EllipticFibrePrincipalData.IsThetaDegOn x δ := by
  rw [Compare.isThetaDeg_iff]
  refine exists₂_congr fun oa nth => and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [add_comm, one_div, inv_mul_eq_div]

theorem isThetaDeg_key_iff (P : Out.PolAV (Sp (𝓞 K))) (δ : ℝ) :
    (∃ (F : GenFib P) (hg : _) (rig : _) (hr : _) (th : _) (hth : _), IsThetaDeg (F.key hg rig hr th hth) δ) ↔
      EllipticFibrePrincipalData.IsThetaDeg P δ := by
  rw [Compare.isDegDeOf_iff]
  exact exists₂_congr fun x φ => and_congr_right fun _ => (Compare.isThetaDeg_iff x δ).symm.trans (isThetaDeg_iff x δ)

end Degree

section Lattice

variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} {hP : IsPeriod D ty Pe} {p q : ℕ}

theorem principal_root_re_zero_im_sq (H : Host E) : H.rt0.re = 0 ∧ H.rt0.im ≠ 0 := by
  have hd : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
  have h₁ := congrArg Complex.re H.sqrt_neg_disc_sq
  have h₂ := congrArg Complex.im H.sqrt_neg_disc_sq
  simp [pow_two] at h₁ h₂
  have him : H.rt0.im ≠ 0 := fun h => by
    rw [h] at h₁
    nlinarith [mul_self_nonneg H.rt0.re]
  exact ⟨mul_right_cancel₀ him (by linarith), him⟩

theorem bar_rt (H : Host E) : H.bar H.rt = -H.rt := by
  have h : H.rt = 2 * H.w0 - 1 := by rw [H.two_weight_eq_one_add_root]; ring
  rw [h, map_sub, map_mul, map_one, HostModel.cmHost_bar_halfIntegerGenerator, map_ofNat]
  ring

theorem orth_of_pure (hP : IsPeriod D ty Pe) {x y : D.La} (hx : x ∈ PureType.lat hP H.rt0)
    (hy : y ∈ PureType.lat hP (-H.rt0)) : D.EF x y = 0 := by
  obtain ⟨Hm, -, -, hE⟩ := hP.2.2.2.2
  have hd : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
  have h₁ := hE (H.rt • x) (H.rt • y)
  rw [D.adj, smul_smul, bar_rt, neg_mul, ← sq, H.rt_sq, neg_neg, Nat.cast_smul_eq_nsmul, map_nsmul,
    PureType.period_rt_smul hP hx, PureType.period_rt_smul hP hy] at h₁
  have h₂ : hermForm Hm (H.rt0 • Pe x) (-H.rt0 • Pe y) = (-(H.d : ℝ) : ℝ) * hermForm Hm (Pe x) (Pe y) := by
    have e : star (-H.rt0) = H.rt0 := Complex.ext (by simp [(principal_root_re_zero_im_sq H).1]) (by simp)
    simp only [hermForm, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, e]
    rw [← _root_.mul_assoc, ← sq, H.sqrt_neg_disc_sq]
    simp
  rw [h₂, Complex.im_ofReal_mul, hE, nsmul_eq_mul] at h₁
  push_cast at h₁
  exact_mod_cast (mul_eq_zero.1 (show (H.d : ℝ) * D.EF x y = 0 by linarith)).resolve_left hd.ne'

theorem eq_zero_of_sum (Z : CMLat hP p q) (hpq : p + q = D.p + D.q) (x : ∀ j : Fin p ⊕ Fin q, (Z.D₁ j.isLeft).La)
    (hx : ∑ j, Z.f j (x j) = 0) : x = 0 := by
  classical
  have := D.fin
  have hnt : ∀ b, Nontrivial (Z.D₁ b).La := fun b =>
    Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [Z.finrank_D₁]; exact one_pos)
  choose a ha using fun b => exists_ne (0 : (Z.D₁ b).La)
  have key : ∀ y : ∀ j : Fin p ⊕ Fin q, (Z.D₁ j.isLeft).La,
      ∃ (r : 𝓞 E) (s : Fin p ⊕ Fin q → 𝓞 E), r ≠ 0 ∧ ∀ j, r • y j = s j • a _ := fun y => by
    choose r s hr e using fun j : Fin p ⊕ Fin q => CMLat.exists_smul_eq_smul (Z.finrank_D₁ _) (ha j.isLeft) (y j)
    refine ⟨∏ j, r j, fun j => (∏ i ∈ Finset.univ.erase j, r i) * s j, Finset.prod_ne_zero_iff.2 fun j _ => hr j,
      fun j => ?_⟩
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_smul, mul_smul, e]
  let N := Submodule.span (𝓞 E) (Set.range fun j : Fin p ⊕ Fin q => Z.f j (a _))
  have htor : Module.IsTorsion (𝓞 E) (D.La ⧸ N) := fun y => by
    obtain ⟨y, rfl⟩ := N.mkQ_surjective y
    obtain ⟨n, hn, hs⟩ := Z.span
    obtain ⟨z, hz⟩ := hs y
    obtain ⟨r, s, hr, e⟩ := key z
    refine ⟨⟨r * n, mem_nonZeroDivisors_of_ne_zero (mul_ne_zero hr (by exact_mod_cast hn.ne'))⟩, ?_⟩
    rw [Submonoid.mk_smul, ← map_smul, mul_smul, Nat.cast_smul_eq_nsmul, hz, Finset.smul_sum]
    refine (Submodule.Quotient.mk_eq_zero N).2 (N.sum_mem fun j _ => ?_)
    rw [← map_smul, e, map_smul]
    exact N.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
  have h₁ := Submodule.finrank_quotient_add_finrank N
  rw [Module.finrank_eq_zero_iff_isTorsion.2 htor, D.rank, zero_add] at h₁
  have hli : LinearIndependent (𝓞 E) fun j : Fin p ⊕ Fin q => Z.f j (a _) :=
    linearIndependent_iff_card_eq_finrank_span.2 (by rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, hpq]; exact h₁.symm)
  obtain ⟨r, s, hr, e⟩ := key x
  have h₂ := Fintype.linearIndependent_iff.1 hli s (by
    simp only [← map_smul, ← e]
    simp only [map_smul, ← Finset.smul_sum, hx, smul_zero])
  funext j
  have := (Z.D₁ j.isLeft).proj
  exact (smul_eq_zero.1 ((e j).trans (by rw [h₂, zero_smul]))).resolve_left hr

def blockP (Z : CMLat hP p q) (j : Fin p) : (Z.D₁ true).La →ₗ[𝓞 E] D.La := Z.f (.inl j)

def blockM (Z : CMLat hP p q) (j : Fin q) : (Z.D₁ false).La →ₗ[𝓞 E] D.La := Z.f (.inr j)

theorem isLatData_of_cmLat (Z : CMLat hP p q) (hs : D.p = p ∧ D.q = q) {Λ : ℝ}
    (hb : ∀ j (τ : E →+* ℂ), √‖τ (Z.hh j : E)‖ ≤ Λ) :
    EllipticFibrePrincipalData.IsLatData (Z.D₁ true) (Z.D₁ false) D (blockP Z) (blockM Z)
      (fun j => Z.hh (.inl j)) (fun j => Z.hh (.inr j)) Λ := by
  have key : ∀ (x : Fin p → (Z.D₁ true).La) (y : Fin q → (Z.D₁ false).La),
      ∑ j, blockP Z j (x j) + ∑ j, blockM Z j (y j) = 0 → x = 0 ∧ y = 0 := fun x y h => by
    have := eq_zero_of_sum Z (by omega) (fun j => Sum.rec x y j) (by rw [Fintype.sum_sum_type]; exact h)
    exact ⟨funext fun j => congrFun this (.inl j), funext fun j => congrFun this (.inr j)⟩
  refine ⟨Z.sigP, Z.sigM, hs, fun x y (h : _ + _ = _ + _) => ?_, fun z => ?_,
    fun i j x y => orth_of_pure hP (Z.pure (.inl i) x) (Z.pure (.inr j) y), fun x hx => ?_, fun y hy => ?_,
    fun j => Z.form (.inl j), fun j => Z.form (.inr j), fun j => hb _, fun j => hb _⟩
  · have := key (x.1 - y.1) (x.2 - y.2) (by
      simp only [Pi.sub_apply, map_sub, Finset.sum_sub_distrib]
      rw [sub_add_sub_comm, h, sub_self])
    exact Prod.ext (sub_eq_zero.1 this.1) (sub_eq_zero.1 this.2)
  · obtain ⟨n, hn, h⟩ := Z.span
    obtain ⟨x, hx⟩ := h z
    exact ⟨n, hn, fun j => x (.inl j), fun j => x (.inr j), hx.trans (Fintype.sum_sum_type _)⟩
  · exact EllipticFibrePrincipalData.im_mul_form_pos hP H.sqrt_neg_disc_sq (Submodule.sum_mem _ fun j _ => Z.pure (.inl j) _)
      fun h => hx (key x 0 (by simpa using h)).1
  · have := EllipticFibrePrincipalData.im_mul_form_pos hP (ρ := -H.rt0) (by rw [neg_sq, H.sqrt_neg_disc_sq])
      (Submodule.sum_mem _ fun j (_ : j ∈ Finset.univ) => Z.pure (.inr j) (y j))
      fun h => hy (key 0 y (by simp only [Pi.zero_apply, map_zero, Finset.sum_const_zero, zero_add]; exact h)).2
    rw [Complex.neg_im, neg_mul] at this
    exact neg_pos.1 this

theorem isPointOf_of_cmLat (Z : CMLat hP p q) :
    EllipticFibrePrincipalData.IsPointOf (blockP Z) (blockM Z) ty Pe :=
  ⟨PeriodCompare.isTypeFn_of_isPeriod hP, hP, fun j => Z.pure (.inl j), fun j => Z.pure (.inr j)⟩

def cmLatOf (hP : IsPeriod D ty Pe) {D₁ D₂ : Datum H} {lp : Fin p → (D₁.La →ₗ[𝓞 E] D.La)}
    {lm : Fin q → (D₂.La →ₗ[𝓞 E] D.La)} {hp : Fin p → 𝓞 E} {hm : Fin q → 𝓞 E} {Λ : ℝ}
    (h : EllipticFibrePrincipalData.IsLatData D₁ D₂ D lp lm hp hm Λ) (k : EllipticFibrePrincipalData.IsPointOf lp lm ty Pe) : CMLat hP p q where
  D₁ b := Bool.rec D₂ D₁ b
  sigP := h.sig₁
  sigM := h.sig₂
  f j := Sum.rec lp lm j
  pure j := Sum.rec k.2.2.1 k.2.2.2 j
  hh j := Sum.rec hp hm j
  form j := Sum.rec h.LocFacts₂ h.formM j
  span := by
    have := D.fin
    refine (Compare.span_iff (O := 𝓞 E) (N := fun j : Fin p ⊕ Fin q => (Bool.rec D₂ D₁ j.isLeft : Datum H).La)
      fun j => Sum.rec lp lm j).2 fun z => ?_
    obtain ⟨n, hn, x, y, e⟩ := h.span z
    exact ⟨n, hn, e ▸ add_mem (Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem (.inl j) ⟨x j, rfl⟩)
      (Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem (.inr j) ⟨y j, rfl⟩)⟩

theorem cmLat_ext {Z Z' : CMLat hP p q} (h₁ : Z.D₁ = Z'.D₁) (h₂ : HEq Z.f Z'.f) (h₃ : Z.hh = Z'.hh) : Z = Z' := by
  cases Z
  cases Z'
  cases h₁
  cases h₂
  cases h₃
  rfl

theorem cmLatOf_blocks (Z : CMLat hP p q) {Λ : ℝ} (h : EllipticFibrePrincipalData.IsLatData (Z.D₁ true) (Z.D₁ false) D (blockP Z) (blockM Z)
    (fun j => Z.hh (.inl j)) (fun j => Z.hh (.inr j)) Λ) (k : EllipticFibrePrincipalData.IsPointOf (blockP Z) (blockM Z) ty Pe) :
    cmLatOf hP h k = Z := by
  refine cmLat_ext (funext fun b => by cases b <;> rfl) ?_ (funext fun j => by cases j <;> rfl)
  refine Function.hfunext rfl fun j j' e => ?_
  cases e
  cases j <;> rfl

abbrev Blocks (D : Datum H) (p q : ℕ) : Type 1 :=
  Σ D₁ D₂ : Datum H, (Fin p → (D₁.La →ₗ[𝓞 E] D.La)) × (Fin q → (D₂.La →ₗ[𝓞 E] D.La)) × (Fin p → 𝓞 E) × (Fin q → 𝓞 E)

def latEquiv (hP : IsPeriod D ty Pe) (p q : ℕ) (Λ : ℝ) :
    {Z : CMLat hP p q // (D.p = p ∧ D.q = q) ∧ ∀ j (τ : E →+* ℂ), √‖τ (Z.hh j : E)‖ ≤ Λ} ≃
      {X : Blocks D p q // EllipticFibrePrincipalData.IsLatData X.1 X.2.1 D X.2.2.1 X.2.2.2.1 X.2.2.2.2.1 X.2.2.2.2.2 Λ ∧
        EllipticFibrePrincipalData.IsPointOf X.2.2.1 X.2.2.2.1 ty Pe} where
  toFun Z := ⟨⟨Z.1.D₁ true, Z.1.D₁ false, blockP Z.1, blockM Z.1, fun j => Z.1.hh (.inl j),
    fun j => Z.1.hh (.inr j)⟩, isLatData_of_cmLat Z.1 Z.2.1 Z.2.2, isPointOf_of_cmLat Z.1⟩
  invFun X := ⟨cmLatOf hP X.2.1 X.2.2, X.2.1.sig, fun j => Sum.rec X.2.1.boundP X.2.1.boundM j⟩
  left_inv Z := Subtype.ext (cmLatOf_blocks Z.1 (isLatData_of_cmLat Z.1 Z.2.1 Z.2.2) (isPointOf_of_cmLat Z.1))
  right_inv := by
    rintro ⟨⟨A, B, a, b, c, d⟩, _⟩
    exact Subtype.ext rfl

theorem exists_bound (Z : CMLat hP p q) : ∃ Λ : ℝ, ∀ j (τ : E →+* ℂ), √‖τ (Z.hh j : E)‖ ≤ Λ := by
  obtain ⟨c, hc⟩ := (Set.finite_range fun x : (Fin p ⊕ Fin q) × (E →+* ℂ) => √‖x.2 (Z.hh x.1 : E)‖).bddAbove
  exact ⟨c, fun j τ => hc ⟨(j, τ), rfl⟩⟩

end Lattice

section Point

open scoped TensorProduct

theorem nonneg_span {M : Type} [AddCommGroup M] (B : LinearMap.BilinForm ℤ M) (N : Submodule ℤ M) (t : ℝ)
    (h : ∀ m ∈ N, 0 ≤ t * B m m) {x : ℝ ⊗[ℤ] M} (hx : x ∈ Submodule.span ℝ ((fun m => (1 : ℝ) ⊗ₜ[ℤ] m) '' N)) :
    0 ≤ t * B.baseChange ℝ x x := by
  obtain ⟨n, c, v, rfl⟩ := Submodule.mem_span_set'.1 hx
  choose m hm e using fun i => (v i).2
  simp only [← e]
  have key : ∀ c : Fin n → ℝ, B.baseChange ℝ (∑ i, c i • (1 : ℝ) ⊗ₜ[ℤ] m i) (∑ i, c i • (1 : ℝ) ⊗ₜ[ℤ] m i) =
      ∑ i, ∑ j, c i * c j * B (m j) (m i) := fun c => by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.BilinForm.baseChange_tmul,
      smul_eq_mul, zsmul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [key]
  have hd : DenseRange (Pi.map fun (_ : Fin n) (a : ℚ) => (a : ℝ)) := DenseRange.piMap fun _ => Rat.denseRange_cast
  refine hd.induction_on (p := fun c => 0 ≤ t * ∑ i, ∑ j, c i * c j * (B (m j) (m i) : ℝ)) c
    (isClosed_le continuous_const (by fun_prop)) fun a => ?_
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) a
  choose k hk using hb
  have hb0 : ((b : ℤ) : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero b.2
  have hk' : ∀ i, (k i : ℝ) = (b : ℤ) * (a i : ℝ) := fun i => by
    have := congrArg (fun z : ℚ => (z : ℝ)) (hk i)
    simpa using this
  have h₁ := h (∑ i, k i • m i) (N.sum_mem fun i _ => N.smul_mem _ (hm i))
  have h₂ : ((B (∑ i, k i • m i) (∑ i, k i • m i) : ℤ) : ℝ) =
      ((b : ℤ) : ℝ) ^ 2 * ∑ i, ∑ j, (a i : ℝ) * a j * (B (m j) (m i) : ℝ) := by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    push_cast
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hk', hk']; ring
  rw [h₂, mul_left_comm] at h₁
  exact (mul_nonneg_iff_of_pos_left (by positivity)).1 h₁

theorem exists_complexStructure {V : Type} [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V)
    (halt : ∀ x y, B x y = -B y x) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (R : V →ₗ[ℝ] V) {t : ℝ} (ht : t ≠ 0)
    (hR : ∀ x, R (R x) = -(t ^ 2) • x) (hB : ∀ x y, B (R x) y = -B x (R y)) {W₁ W₂ : Submodule ℝ V}
    (hs : W₁ ⊔ W₂ = ⊤) (ho : ∀ x ∈ W₁, ∀ y ∈ W₂, B x y = 0) (s₁ : ∀ x ∈ W₁, R x ∈ W₁) (s₂ : ∀ x ∈ W₂, R x ∈ W₂)
    (p₁ : ∀ x ∈ W₁, 0 ≤ t * B (R x) x) (p₂ : ∀ x ∈ W₂, 0 ≤ -t * B (R x) x) :
    ∃ J : V →ₗ[ℝ] V, (∀ x ∈ W₁, J x = t⁻¹ • R x) ∧ (∀ x ∈ W₂, J x = -t⁻¹ • R x) ∧ (∀ x, J (J x) = -x) ∧
      (∀ x y, B (J x) (J y) = B x y) ∧ ∀ x, x ≠ 0 → 0 < B (J x) x := by
  have dec : ∀ x, ∃ a ∈ W₁, ∃ b ∈ W₂, a + b = x := fun x => Submodule.mem_sup.1 (hs ▸ Submodule.mem_top)
  have ho' : ∀ x ∈ W₂, ∀ y ∈ W₁, B x y = 0 := fun x hx y hy => by rw [halt, ho y hy x hx, neg_zero]
  have hc : IsCompl W₁ W₂ := ⟨Submodule.disjoint_def.2 fun x h₁ h₂ => hnd x fun y => by
    obtain ⟨a, ha, b, hb, rfl⟩ := dec y
    rw [map_add, ho' x h₂ a ha, ho x h₁ b hb, add_zero], codisjoint_iff.2 hs⟩
  let J := LinearMap.ofIsCompl hc (t⁻¹ • R ∘ₗ W₁.subtype) (-t⁻¹ • R ∘ₗ W₂.subtype)
  have j₁ : ∀ x ∈ W₁, J x = t⁻¹ • R x := fun x hx => LinearMap.ofIsCompl_apply_left hc (⟨x, hx⟩ : W₁)
  have j₂ : ∀ x ∈ W₂, J x = -t⁻¹ • R x := fun x hx => LinearMap.ofIsCompl_apply_right hc (⟨x, hx⟩ : W₂)
  have hJ : ∀ x, J (J x) = -x := fun x => by
    obtain ⟨a, ha, b, hb, rfl⟩ := dec x
    rw [map_add, j₁ a ha, j₂ b hb, map_add, map_smul, map_smul, j₁ _ (s₁ a ha), j₂ _ (s₂ b hb), hR, hR]
    match_scalars <;> field_simp
  have hsk : ∀ x y, B (J x) y = -B x (J y) := fun x y => by
    obtain ⟨a, ha, b, hb, rfl⟩ := dec x
    obtain ⟨c, hc, d, hd, rfl⟩ := dec y
    simp only [map_add, j₁ a ha, j₂ b hb, j₁ c hc, j₂ d hd, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hB, ho a ha _ (s₂ d hd), ho' b hb _ (s₁ c hc)]
    ring
  have hnn : ∀ x, 0 ≤ B (J x) x := fun x => by
    obtain ⟨a, ha, b, hb, rfl⟩ := dec x
    have e : B (J (a + b)) (a + b) = (t * B (R a) a + -t * B (R b) b) / t ^ 2 := by
      simp only [map_add, j₁ a ha, j₂ b hb, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        ho _ (s₁ a ha) b hb, ho' _ (s₂ b hb) a ha]
      field_simp
      ring
    rw [e]
    exact div_nonneg (add_nonneg (p₁ a ha) (p₂ b hb)) (sq_nonneg t)
  refine ⟨J, j₁, j₂, hJ, fun x y => by rw [hsk, hJ, map_neg, neg_neg], fun x hx => (hnn x).lt_of_ne fun h => hx ?_⟩
  have hsy : LinearMap.IsSymm (B.compLeft J) := ⟨fun x y => by
    show B (J x) y = B (J y) x
    rw [hsk, ← halt]⟩
  have h₁ := ((B.compLeft J).apply_apply_same_eq_zero_iff hnn hsy (x := x)).1 h.symm
  have h₂ : J x = 0 := hnd _ fun y => LinearMap.congr_fun h₁ y
  rw [← neg_eq_zero, ← hJ, h₂, map_zero]

theorem baseChange_skew {M : Type} [AddCommGroup M] (B : LinearMap.BilinForm ℤ M) (f g : M →ₗ[ℤ] M)
    (h : ∀ x y, B (f x) y = -B x (g y)) (x y : ℝ ⊗[ℤ] M) :
    B.baseChange ℝ (f.baseChange ℝ x) y = -B.baseChange ℝ x (g.baseChange ℝ y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' k k' => simp only [map_add, LinearMap.add_apply, k, k', neg_add]
  | tmul r x =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' k k' => simp only [map_add, k, k', neg_add]
    | tmul r' y => simp [h]

theorem baseChange_alt (D : Datum H) (x y : ℝ ⊗[ℤ] D.La) : D.EF.baseChange ℝ x y = -D.EF.baseChange ℝ y x := by
  have h : ∀ x y, D.EF x y = -D.EF y x := fun x y => by
    have := D.alt (x + y)
    simp only [map_add, LinearMap.add_apply, D.alt] at this
    linarith
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' k k' => simp only [map_add, LinearMap.add_apply, k, k', neg_add]
  | tmul r x =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' k k' => simp only [map_add, LinearMap.add_apply, k, k', neg_add]
    | tmul r' y => simp [h x y, mul_comm]

open PeriodMapPresentation in

theorem exists_period (D : Datum H) (N₁ N₂ : Submodule (𝓞 E) D.La) (hs : ∀ z, ∃ n : ℕ, 0 < n ∧ n • z ∈ N₁ ⊔ N₂)
    (ho : ∀ x ∈ N₁, ∀ y ∈ N₂, D.EF x y = 0) (p₁ : ∀ x ∈ N₁, 0 ≤ H.rt0.im * D.EF (H.w0 • x) x)
    (p₂ : ∀ x ∈ N₂, H.rt0.im * D.EF (H.w0 • x) x ≤ 0) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (hty : Geo.Tor.IsTypeFn H D.p D.q ty) :
    ∃ (Pe : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty Pe),
      N₁ ≤ PureType.lat hP H.rt0 ∧ N₂ ≤ PureType.lat hP (-H.rt0) := by
  obtain ⟨_, _⟩ := PeriodCompare.finiteDimensional D
  obtain ⟨hre, him⟩ := principal_root_re_zero_im_sq H
  have hsq : H.rt0.im ^ 2 = H.d := by
    have := congrArg Complex.re H.sqrt_neg_disc_sq
    simp [pow_two, hre] at this
    rw [sq, this]
  let W : Submodule (𝓞 E) D.La → Submodule ℝ (ℝ ⊗[ℤ] D.La) := fun N =>
    Submodule.span ℝ ((fun m => (1 : ℝ) ⊗ₜ[ℤ] m) '' (N.restrictScalars ℤ : Submodule ℤ D.La))
  have hW : ∀ N m, m ∈ N → (1 : ℝ) ⊗ₜ[ℤ] m ∈ W N := fun N m hm => Submodule.subset_span ⟨m, hm, rfl⟩
  have act : ∀ (a : 𝓞 E) (r : ℝ) (m : D.La), actR D a (r ⊗ₜ m) = r ⊗ₜ (a • m) := fun _ _ _ => rfl
  have st : ∀ N (a : 𝓞 E), ∀ x ∈ W N, actR D a x ∈ W N := fun N a =>
    show W N ≤ (W N).comap (actR D a) from Submodule.span_le.2 (by
      rintro _ ⟨m, hm, rfl⟩
      exact hW N _ (N.smul_mem a hm))
  have mul : ∀ (a b : 𝓞 E) x, actR D a (actR D b x) = actR D (a * b) x := fun a b x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' k k' => simp only [map_add, k, k']
    | tmul r m => rw [act, act, act, mul_smul]
  have two : ∀ m, D.EF (H.rt • m) m = 2 * D.EF (H.w0 • m) m := fun m => by
    have : D.EF ((2 * H.w0) • m) m = D.EF ((1 + H.rt) • m) m := by rw [H.two_weight_eq_one_add_root]
    rw [two_mul, add_smul, add_smul, one_smul, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, D.alt] at this
    linarith
  have nn : ∀ (N : Submodule (𝓞 E) D.La) (t : ℝ), (∀ m ∈ N, 0 ≤ t * D.EF (H.w0 • m) m) →
      ∀ x ∈ W N, 0 ≤ t * D.EF.baseChange ℝ (actR D H.rt x) x := fun N t h x hx => by
    have := nonneg_span (D.EF.compLeft (DistribMulAction.toLinearMap ℤ D.La H.rt)) (N.restrictScalars ℤ) t
      (fun m hm => by
        show 0 ≤ t * (D.EF (H.rt • m) m : ℝ)
        rw [two]
        push_cast
        linarith [h m hm]) hx
    refine this.trans_eq (congrArg _ ?_)
    have k : (D.EF.compLeft (DistribMulAction.toLinearMap ℤ D.La H.rt)).baseChange ℝ =
        (D.EF.baseChange ℝ).compLeft (actR D H.rt) := by
      ext a b
      simp [act]
      rfl
    rw [k]
    rfl
  have htop : W N₁ ⊔ W N₂ = ⊤ :=
    (top_le_iff.1 fun x _ => by
      induction x using TensorProduct.induction_on with
      | zero => exact zero_mem _
      | add x x' k k' => exact add_mem (k trivial) (k' trivial)
      | tmul r m =>
        obtain ⟨n, hn, h⟩ := hs m
        obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 h
        have : r ⊗ₜ[ℤ] m = (r / n) • ((1 : ℝ) ⊗ₜ[ℤ] a + (1 : ℝ) ⊗ₜ[ℤ] b) := by
          rw [← TensorProduct.tmul_add, e, TensorProduct.tmul_smul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
            div_mul_cancel₀ _ (Nat.cast_ne_zero.2 hn.ne'), TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.add_mem_sup (hW _ a ha) (hW _ b hb)))
  obtain ⟨J₀, -, -, hJ₀, -⟩ := D.dom
  obtain ⟨J, j₁, j₂, hJ, hinv, hpos⟩ := exists_complexStructure (D.EF.baseChange ℝ) (baseChange_alt D)
    (fun x hx => by_contra fun h => (hJ₀ x h).ne' (by rw [baseChange_alt, hx, neg_zero])) (actR D H.rt) him
    (fun x => by
      rw [mul, ← sq, H.rt_sq, hsq]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x x' k k' => simp only [map_add, k, k', smul_add]
      | tmul r m =>
        rw [act, neg_smul, Nat.cast_smul_eq_nsmul, TensorProduct.tmul_neg, neg_smul, Nat.cast_smul_eq_nsmul,
          TensorProduct.tmul_smul])
    (baseChange_skew _ _ _ fun x y => by
      show D.EF (H.rt • x) y = -D.EF x (H.rt • y)
      rw [D.adj, bar_rt, neg_smul, map_neg])
    htop
    (fun x hx y hy => by
      refine Submodule.span_induction₂ (p := fun x y _ _ => D.EF.baseChange ℝ x y = 0) ?_ (by simp) (by simp)
        (fun _ _ _ _ _ _ k k' => by simp [k, k']) (fun _ _ _ _ _ _ k k' => by simp [k, k'])
        (fun _ _ _ _ _ k => by simp [k]) (fun _ _ _ _ _ k => by simp [k]) hx hy
      rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      simp [ho a ha b hb])
    (st N₁ _) (st N₂ _) (nn N₁ _ p₁) (nn N₂ _ fun m hm => by linarith [p₂ m hm])
  have hcomm : ∀ a, J ∘ₗ actR D a = actR D a ∘ₗ J := fun a => LinearMap.ext fun x => by
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : x ∈ W N₁ ⊔ W N₂)
    simp only [LinearMap.comp_apply, map_add, j₁ u hu, j₂ v hv, j₁ _ (st N₁ a u hu), j₂ _ (st N₂ a v hv), map_smul, mul,
      mul_comm]
  have hdom := PeriodCompare.mem_domain D hJ hcomm hinv hpos
  let ρ : 𝓞 E →+* Module.End ℝ (ℝ ⊗[ℤ] D.La) :=
    (Module.End.baseChangeHom ℤ ℝ D.La : Module.End ℤ D.La →+* Module.End ℝ (ℝ ⊗[ℤ] D.La)).comp
      (Algebra.lsmul ℤ ℤ D.La : 𝓞 E →ₐ[ℤ] Module.End ℤ D.La)
  obtain ⟨e, heJ, heρ⟩ := PeriodNonempty.exists_diag_real J hJ ρ ty fun a => by
    have k := (hdom.2.2.2.2 a).trans (PeriodNonempty.sum_type H hty (a : E)).symm
    have k₁ := congrArg Complex.re k
    have k₂ := congrArg Complex.im k
    simp only [Complex.sub_re, Complex.sub_im, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_mul_re, Complex.I_mul_im] at k₁ k₂
    exact ⟨hcomm a, show LinearMap.trace ℝ _ (actR D a) = _ by linarith,
      show LinearMap.trace ℝ _ (J ∘ₗ actR D a) = _ by linarith⟩
  let Pe : D.La →+ (Fin g → ℂ) := AddMonoidHom.mk' (fun x => e (1 ⊗ₜ x)) fun x y => by
    rw [TensorProduct.tmul_add, map_add]
  have hP : IsPeriod D ty Pe :=
    PeriodCompare.isPeriod_of_presents hdom ⟨e, fun _ => rfl, heJ, fun a v => funext (heρ a v)⟩
  have pure : ∀ (t : ℝ) (r : ℂ), t ≠ 0 → r = t * Complex.I → ∀ m, J (1 ⊗ₜ m) = t⁻¹ • actR D H.rt (1 ⊗ₜ m) →
      m ∈ PureType.lat hP r := fun t r ht hr m hm j hj => by
    have k := congrFun (heJ (1 ⊗ₜ m)) j
    rw [hm, map_smul, Pi.smul_apply, Pi.smul_apply, show e (actR D H.rt (1 ⊗ₜ m)) j = _ from heρ H.rt _ j,
      Complex.real_smul, smul_eq_mul, Complex.ofReal_inv,
      inv_mul_eq_iff_eq_mul₀ (Complex.ofReal_ne_zero.2 ht), ← _root_.mul_assoc, ← hr] at k
    exact (mul_eq_zero.1 ((sub_mul _ _ _).trans (sub_eq_zero.2 k))).resolve_left (sub_ne_zero.2 hj)
  exact ⟨Pe, hP, fun m hm => pure _ _ him (Complex.ext (by simp [hre]) (by simp)) m (j₁ _ (hW _ m hm)),
    fun m hm => pure (-H.rt0.im) _ (neg_ne_zero.2 him) (Complex.ext (by simp [hre]) (by simp)) m
      (by rw [j₂ _ (hW _ m hm), inv_neg])⟩

variable {D₁ D₂ D : Datum H} {p q : ℕ} {lp : Fin p → (D₁.La →ₗ[𝓞 E] D.La)} {lm : Fin q → (D₂.La →ₗ[𝓞 E] D.La)}
  {hp : Fin p → 𝓞 E} {hm : Fin q → 𝓞 E} {Λ : ℝ}

theorem mem_iSup_range {O M N : Type} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] {n : ℕ}
    (f : Fin n → (N →ₗ[O] M)) {a : M} (h : a ∈ ⨆ j, LinearMap.range (f j)) : ∃ x : Fin n → N, a = ∑ j, f j (x j) := by
  refine Submodule.iSup_induction _ (motive := fun a => ∃ x : Fin n → N, a = ∑ j, f j (x j)) h ?_ ⟨0, by simp⟩ ?_
  · rintro i _ ⟨b, rfl⟩
    refine ⟨Pi.single i b, ?_⟩
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero]) (by simp), Pi.single_eq_same]
  · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by simp [Finset.sum_add_distrib]⟩

theorem exists_isPointOf (h : EllipticFibrePrincipalData.IsLatData D₁ D₂ D lp lm hp hm Λ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (hty : IsTypeFn H D.p D.q ty) : ∃ Pe, EllipticFibrePrincipalData.IsPointOf lp lm ty Pe := by
  obtain ⟨Pe, hP, k₁, k₂⟩ := exists_period D (⨆ j, LinearMap.range (lp j)) (⨆ j, LinearMap.range (lm j))
    (fun z => by
      obtain ⟨n, hn, x, y, e⟩ := h.span z
      exact ⟨n, hn, e ▸ Submodule.add_mem_sup
        (Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j ⟨x j, rfl⟩)
        (Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j ⟨y j, rfl⟩)⟩)
    (fun x hx y hy => by
      obtain ⟨x, rfl⟩ := mem_iSup_range lp hx
      obtain ⟨y, rfl⟩ := mem_iSup_range lm hy
      simp [h.orth])
    (fun x hx => by
      obtain ⟨x, rfl⟩ := mem_iSup_range lp hx
      by_cases k : x = 0
      · simp [k]
      · exact (h.pos x k).le)
    (fun y hy => by
      obtain ⟨y, rfl⟩ := mem_iSup_range lm hy
      by_cases k : y = 0
      · simp [k]
      · exact (h.neg y k).le) hty
  exact ⟨Pe, hty, hP, fun j x => k₁ (Submodule.mem_iSup_of_mem j ⟨x, rfl⟩),
    fun j y => k₂ (Submodule.mem_iSup_of_mem j ⟨y, rfl⟩)⟩

def blocks {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} {hP : IsPeriod D ty Pe} (Z : CMLat hP p q) :
    Blocks D p q :=
  ⟨Z.D₁ true, Z.D₁ false, blockP Z, blockM Z, fun j => Z.hh (.inl j), fun j => Z.hh (.inr j)⟩

theorem isLatData_iff (X : Blocks D p q) (Λ : ℝ) {g : ℕ} {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H D.p D.q ty) :
    EllipticFibrePrincipalData.IsLatData X.1 X.2.1 D X.2.2.1 X.2.2.2.1 X.2.2.2.2.1 X.2.2.2.2.2 Λ ↔
      ∃ (Pe : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty Pe) (Z : CMLat hP p q),
        blocks Z = X ∧ (D.p = p ∧ D.q = q) ∧ ∀ j (τ : E →+* ℂ), √‖τ (Z.hh j : E)‖ ≤ Λ := by
  constructor
  · intro h
    obtain ⟨Pe, k⟩ := exists_isPointOf h hty
    obtain ⟨Z, hZ⟩ := (latEquiv k.2.1 p q Λ).surjective ⟨X, h, k⟩
    exact ⟨Pe, k.2.1, Z.1, congrArg Subtype.val hZ, Z.2⟩
  · rintro ⟨Pe, hP, Z, rfl, a, b⟩
    exact isLatData_of_cmLat Z a b

end Point

theorem typings_agree (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    (∀ χ : DirichletCharacter ℂ H.d, (IsKroneckerChar χ ↔ χ = EllipticFibrePrincipalData.chi H) ∧
      (IsKroneckerChar χ → logOm E χ = (EllipticFibrePrincipalData.logOm H : ℝ))) ∧
    (∀ (R R' : Type) [CommRing R] [CommRing R'] (ω : R) (ω' : R') (C' : Ell H R' ω') (C : Ell H R ω) (f : R →+* R')
      (φ : C'.P.A.left ⟶ C.P.A.left), EllMap C' C f φ ↔ EllipticFibrePrincipalData.IsEllFibre f C C' φ) ∧
    (∀ (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (s : R →+* ℂ), C.IsPrincipalAt s ↔ EllipticFibrePrincipalData.IsPrincipalAt C s) ∧
    (∀ (M : Type) [Field M] [NumberField M] (ω : 𝓞 M) (C : Ell H (𝓞 M) ω),
      (∀ x, C.HasPeriod x ↔ EllipticFibrePrincipalData.IsLogPeriod C x) ∧
      ∀ (χ : DirichletCharacter ℂ H.d) (K : Type) [Field K] [NumberField K], IsKroneckerChar χ →
        Module.finrank ℚ K = 2 → discr K = -H.d → (C.HasPeriod (logOm K χ).re ↔ EllipticFibrePrincipalData.HasPeriod C)) ∧
    (∀ (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (T : PAT H (Sp R)) (D : Datum H) (L : Submodule (𝓞 E) D.La)
      (φ : L → (C.P.A ⟶ T.t.G)) (ε : ℤˣ) (h : D.La → D.La → OK H), (IsKForm D ε h ↔ h = EllipticFibrePrincipalData.kForm D ε true) ∧
      (IsKForm D ε h → (IsFam C T h L φ ↔ EllipticFibrePrincipalData.IsHomFam C T.t L ε true φ) ∧
        (IsFam (conjEll C) T h L φ ↔ EllipticFibrePrincipalData.IsHomFam C T.t L ε false φ))) ∧
    (∀ (S : Scheme.{0}) (I : Type) [Fintype I] (B : I → Over S) [∀ i, GrpObj (B i)] (A : Over S) [GrpObj A]
      [IsCommMonObj A] (φ : ∀ i, B i ⟶ A), (∀ i, IsMonHom (φ i)) → ∀ (k : Type) [Field k] (t : Sp k ⟶ S),
      OntoAt φ t ↔ ∀ y : Over.mk t ⟶ A, ∃ x : ∀ i, Over.mk t ⟶ B i, y = ∏ i, x i ≫ φ i) ∧
    (∀ (R : Type) [CommRing R] (T : PAT H (Sp R)) (σ : R →+* ℂ) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ))
      (Pe : D.La →+ (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk (spMap σ) ⟶ T.t.G)),
      IsExp T σ D ty Pe e ↔ EllipticFibrePrincipalData.IsExp T.t (spMap σ) D ty Pe e) ∧
    (∀ (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (p q : ℕ),
      (∀ (Pe : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty Pe),
        (∀ Λ : ℝ, ∃ e : {Z : CMLat hP p q // (D.p = p ∧ D.q = q) ∧ ∀ j (τ : E →+* ℂ), √‖τ (Z.hh j : E)‖ ≤ Λ} ≃
            {X : Blocks D p q // EllipticFibrePrincipalData.IsLatData X.1 X.2.1 D X.2.2.1 X.2.2.2.1 X.2.2.2.2.1 X.2.2.2.2.2 Λ ∧
              EllipticFibrePrincipalData.IsPointOf X.2.2.1 X.2.2.2.1 ty Pe}, ∀ Z, (e Z).1 = blocks Z.1) ∧
        ∀ Z : CMLat hP p q, ∃ Λ : ℝ, ∀ j (τ : E →+* ℂ), √‖τ (Z.hh j : E)‖ ≤ Λ) ∧
      (IsTypeFn H D.p D.q ty → ∀ (X : Blocks D p q) (Λ : ℝ),
        EllipticFibrePrincipalData.IsLatData X.1 X.2.1 D X.2.2.1 X.2.2.2.1 X.2.2.2.2.1 X.2.2.2.2.2 Λ ↔
          ∃ (Pe : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty Pe) (Z : CMLat hP p q),
            blocks Z = X ∧ (D.p = p ∧ D.q = q) ∧ ∀ j (τ : E →+* ℂ), √‖τ (Z.hh j : E)‖ ≤ Λ)) ∧
    (∀ (K : Type) [Field K] [NumberField K] (δ : ℝ), (∀ x : KeyIn K, IsThetaDeg x δ ↔ EllipticFibrePrincipalData.IsThetaDegOn x δ) ∧
      ∀ P : Out.PolAV (Sp (𝓞 K)),
        (∃ (F : GenFib P) (hg : _) (rig : _) (hr : _) (th : _) (hth : _), IsThetaDeg (F.key hg rig hr th hth) δ) ↔
          EllipticFibrePrincipalData.IsThetaDeg P δ) :=
  ⟨fun χ => ⟨isKroneckerChar_iff χ, logOm_eq⟩, fun _ _ _ _ _ _ => ellMap_iff, fun _ _ _ => isPrincipalAt_iff,
    fun _ _ _ _ C => ⟨hasPeriod_iff C, fun _ _ _ _ h h2 hD => hasPeriod_logOm_iff h h2 hD C⟩,
    fun _ _ _ _ _ _ _ _ _ h => ⟨isKForm_iff h, fun k => ⟨isFam_iff k, isFam_conj_iff k⟩⟩,
    fun _ _ _ _ _ _ _ _ φ hφ _ _ t => Compare.ontoAt_iff φ hφ t, fun _ _ T σ D _ => isExp_iff T σ D,
    fun _ _ _ p q => ⟨fun _ hP => ⟨fun Λ => ⟨latEquiv hP p q Λ, fun _ => rfl⟩, exists_bound⟩,
      fun hty X Λ => isLatData_iff X Λ hty⟩,
    fun _ _ _ δ => ⟨fun x => isThetaDeg_iff x δ, fun P => isThetaDeg_key_iff P δ⟩⟩

end GlobalTheory.CM.FamCompare
end
