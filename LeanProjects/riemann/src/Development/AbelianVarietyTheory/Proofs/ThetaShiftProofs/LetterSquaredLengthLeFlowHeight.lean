import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSubspaceIsometric
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AnVecTorusLetter
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtExponentialDerivativeBijectiveTangent
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HermFormRsmulRight
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsLocalRingDual
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsIntegralDiscrMulOfTraceInt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmMetrisedLineLengthsEqSectionLieNorms
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SplitBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsSplit
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTauCanonicalIffOfIsPullDegTauBimult
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieBasisCoordinatesBijectiveTangent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.LetterLen

section Scale

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

variable {A A' : Type} [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] {f : A →+* A'} {D₀ : DegPre A}
  {D₁ : DegPre A'} (p : IsPullDeg f D₀ D₁)

theorem isPull_scale {a : A} {ν ω : GtPt D₀ (epsR A)} {ν₁ ω₁ : GtPt D₁ (epsR A')} (h : LetBC p ν ν₁)
    (h' : LetBC p ω ω₁) (hs : GtPt.IsPull (spMap (epsScaleR a)) ν ω) :
    GtPt.IsPull (spMap (epsScaleR (f a))) ν₁ ω₁ := by
  have gp := pull_grp p
  rw [ArcQBC.letBC_iff] at h h'
  have e : spMap (dualMap f) ≫ spMap (epsScaleR a) = spMap (epsScaleR (f a)) ≫ spMap (dualMap f) :=
    LieCombBaseChange.dualMap_epsScale f a
  have o : spMap (epsScaleR (f a)) ≫ (epsR A').hom = (epsR A').hom :=
    (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext fun x => by
      simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]))
  have hb : ω₁.b.left = spMap (epsScaleR (f a)) ≫ ν₁.b.left := by
    refine gp.1.hom_ext ?_ ?_
    · refine h'.1.trans ?_
      rw [hs.1, ← Category.assoc, e, Category.assoc, ← h.1]
      exact (Category.assoc _ _ _).symm
    · rw [Category.assoc, Over.w, Over.w, o]
  refine ⟨hb, fun χ => corr_of_val D₁.P.isLB fun y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D₀.P.isLB y
  have e₁ := ConstFam.pmaps_val (h'.2 χ).1 (h'.2 χ).2 (𝟙 _) hJ hJ'
  have e₂ := ConstFam.pmaps_val (h.2 χ).1 (h.2 χ).2 (𝟙 _ ≫ spMap (epsScaleR (f a))) hJ hJ'
  have e₃ := (val_corr hJ (hs.2 (p.xe χ)) (𝟙 _ ≫ spMap (dualMap f))).trans (val_pull hJ _ _ _)
  have g : ∀ k, (𝟙 _ ≫ spMap (epsScaleR (f a))) ≫ DegPre.gtφT D₁ (epsR A') ν₁.b χ k =
      𝟙 _ ≫ DegPre.gtφT D₁ (epsR A') ω₁.b χ k := fun k => by
    rw [TorusCoord.gtφT_eq ω₁.b]
    exact (TorusCoord.comp_eq_of_left ν₁.b ω₁.b _ _
      ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·) hb.symm))).1 χ k
  have m : (𝟙 _ ≫ spMap (dualMap f)) ≫ spMap (epsScaleR a) =
      (𝟙 _ ≫ spMap (epsScaleR (f a))) ≫ spMap (dualMap f) := by rw [Category.assoc, e, Category.assoc]
  simp only [g] at e₂
  have e₄ := e₁.symm.trans (e₃.trans ((congrArg (fun r => val (ν.s (p.xe χ)) r y J) m).trans e₂))
  exact (mul_left_cancel e₄).trans (val_pull hJ' _ _ _).symm

theorem exists_vec (v : epsR A ⟶ D₀.P.A) (hv : IsTangent v) :
    ∃ v₁ : epsR A' ⟶ D₁.P.A, v₁.left ≫ prj p = spMap (dualMap f) ≫ v.left ∧ IsTangent v₁ := by
  have gp := pull_grp p
  have w : (spMap (dualMap f) ≫ v.left) ≫ D₀.P.A.hom = (epsR A').hom ≫ spMap f := by
    rw [Category.assoc, Over.w, ArcQBC.dual_base]
  have e := gp.1.lift_fst _ _ w
  exact ⟨Over.homMk (gp.1.lift _ _ w) (gp.1.lift_snd _ _ w), e, IsVecOver.isTangent gp e hv⟩

end Scale

open Classical in

theorem map_proj {E : Type} [Field E] [NumberField E] {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (S : Set (Fin g → ℂ)) (hS : Submodule.span ℝ S = ⊤)
    (h : ∀ (a : 𝓞 E), ∀ v ∈ S, L (fun j => ty j (a : E) * v j) = fun j => ty j (a : E) * L v j) (ρ : E →+* ℂ)
    (v : Fin g → ℂ) : L (fun j => if ty j = ρ then v j else 0) = fun j => if ty j = ρ then L v j else 0 := by
  have h₁ : ∀ (a : 𝓞 E) v, L (fun j => ty j (a : E) * v j) = fun j => ty j (a : E) * L v j := fun a v => by
    have hv : v ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx => exact h a x hx
    | zero => funext j; simp [show (fun _ : Fin g => (0 : ℂ)) = 0 from rfl]
    | add x y _ _ hx hy =>
      have : (fun j => ty j (a : E) * (x + y) j) = (fun j => ty j (a : E) * x j) + fun j => ty j (a : E) * y j := by
        funext j; simp [mul_add]
      rw [this, map_add, map_add, hx, hy]
      funext j; simp [mul_add]
    | smul r x _ hx =>
      have : (fun j => ty j (a : E) * (r • x) j) = (r : ℂ) • (fun j => ty j (a : E) * x j) := by
        funext j; simp; ring
      rw [this, map_smul, hx, show r • x = (r : ℂ) • x from rfl, map_smul]
      funext j; simp; ring
  have h₂ : ∀ i j, ty i ≠ ty j → L (Pi.single j 1) i = 0 := fun i j hij => by
    by_contra hne
    refine hij (ArchLen.emb_ext fun a => mul_right_cancel₀ hne ?_)
    have := congrFun (h₁ a (Pi.single j 1)) i
    have e : (fun k => ty k (a : E) * (Pi.single j 1 : Fin g → ℂ) k) = ty j (a : E) • (Pi.single j 1 : Fin g → ℂ) := by
      funext k
      by_cases hk : k = j
      · subst hk; simp
      · simp [hk]
    rw [e, map_smul] at this
    exact this.symm
  have h₃ : ∀ u : Fin g → ℂ, ∀ i, L u i = ∑ j, u j * L (Pi.single j 1) i := fun u i => by
    rw [LinearMap.pi_apply_eq_sum_univ L u, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : (fun k => if j = k then (1 : ℂ) else 0) = Pi.single j 1 := by
      funext k; simp [Pi.single_apply, eq_comm]
    rw [this]; rfl
  funext i
  rw [h₃, h₃ v]
  split_ifs with hi
  · refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · rfl
    · rw [h₂ i j (fun q => hj (q.symm.trans hi))]; simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hj
    · rw [h₂ i j (fun q => hi (q.trans hj))]; simp
    · simp

theorem exists_pull_form {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) :
    ∃ Hm' : Matrix (Fin g) (Fin g) ℂ, Hm'.IsHermitian ∧ ∀ z w, hermForm Hm' z w = hermForm Hm (L z) (L w) := by
  obtain ⟨B, rfl⟩ := Matrix.toLin'.surjective L
  refine ⟨B.transpose * Hm * B.transpose.conjTranspose, Matrix.isHermitian_mul_mul_conjTranspose _ hH, fun z w => ?_⟩
  simp only [hermForm, Matrix.toLin'_apply]
  rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec z,
    Matrix.vecMul_transpose, ← Matrix.mulVec_transpose]
  rfl

theorem eq_zero_of_trace {E : Type} [Field E] [NumberField E] {x : E}
    (h : ∀ a : 𝓞 E, Algebra.trace ℚ E ((a : E) * x) = 0) : x = 0 := by
  refine (traceForm_nondegenerate ℚ E).1 x fun y => ?_
  rw [← (integralBasis E).sum_repr y, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul, Algebra.traceForm_apply, integralBasis_apply, _root_.mul_comm x]
  exact smul_eq_zero_of_right _ (h _)

theorem herm_swap {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (u v : Fin r → E) :
    herm X.Gm v u = cc (herm X.Gm u v) := by
  simp only [herm, cc, map_sum, map_mul, IsCMField.complexConj_apply_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← X.Gm_herm a b, cc]
  ring

theorem le_sq_of_log {y b m : ℝ} (hb : 0 < b) (hm : 1 ≤ m) (h : Real.log y / 2 ≤ Real.log b) : y ≤ (b * m) ^ 2 := by
  have h₁ : y ≤ b ^ 2 := by
    by_contra hn
    have := Real.log_lt_log (pow_pos hb 2) (not_le.1 hn)
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  exact h₁.trans (pow_le_pow_left₀ hb.le (le_mul_of_one_le_right hb.le hm) 2)

theorem letter_length_le : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (n' : ℕ) (La c₁ : ℝ) (s : CMIn a e th jj n' La c₁) (em : K₁ →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (aC : ArcIn Dw l β ℂ (σ.comp β)) (p : Out.IsPullDeg em a.D₀ aC.D₀) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y aC χ) (Ha : HolArc Y σ aC χ W Uw.F) (k : U.Comp) (ξ' : Fin r → E) (x x'' : (U.X k).dom) (sf : (U.X k).Ψ → ℂ) (w₁ : ℂ) (L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ)) (gm : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La) (ep : ℝ) (Hm : Matrix (Fin Uw.g) (Fin Uw.g) ℂ), σ = em.comp (algebraMap c.F K₁) → GoodEmb c σ → IsUnf U → InBC em (a.restrict β) aC p → 1 ≤ La → 0 < ep → (U.X k).IsIso ξ' → Ha.T < w₁.im → (∀ v, Uw.Pm k x (gm v) = L (Ha.Pw w₁ v)) → (∀ v v', (Uw.F.Di (Uw.ik k)).EF (gm v) (gm v') = (Uw.F.Di Ha.i).EF v v') → (∃ t, (∀ v', -(Uw.F.Di Ha.i).EF t v' = s.ξ (p.xe (Ha.y v'))) ∧ (Uw.φ k (gm t) : Fin r → E) = ξ') → x''.1 = (U.X k).flow ξ' sf x.1 → (∀ τ, (U.X k).tt ξ' x''.1 τ = ep) → IsRiem Uw.F (Uw.ik k) (Uw.Pm k x'') Hm → ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (eC : Out.GtPt aC.D₀ (epsR ℂ)) (z : Fin Uw.g → ℂ), LetBC p (e τ i) eC → AnVec Ha eC z → Real.pi * (hermForm Hm (L z) (L z)).re ≤ (La * Real.sqrt (max 1 ep⁻¹) * (s.line τ i).n em) ^ 2 := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ a e th jj n' La c₁ s em _ _ σ r U Uw O _ β Y aC p χ W Ha k ξ' x x'' sf w₁ L gm
    ep Hm hσ hG hU hBC hLa hep hξ hw hP hEF ⟨t, ht, htξ⟩ hx htt hH τ i eC z hL hz
  classical
  letI := H.starRing
  have hGl : Out.GlobalFnsSt := hK.laws.globalFns
  obtain ⟨hlin, -, -, -, Hm₀, hH₀⟩ := Uw.period k x
  obtain ⟨hlin', -, -, hspan', -⟩ := Ha.period w₁ hw
  obtain ⟨hab, htor⟩ := ArchLen.lengths_along_flow E H Dw l Xo c σ r U Uw k ξ' x x'' sf Hm₀ Hm hG hU hξ hx hH₀ hH
  obtain ⟨nn, hN, -, -, hnn, hy, -⟩ := holArc_nilpotent E H Dw l Xo c σ O β Y aC χ W _ _ Uw.F Ha
  have hPw : ∀ v, Ha.y v = 0 → Ha.Pw w₁ v = Ha.P₀ v := fun v hv => by
    rw [Ha.Pw_eq, hN, hnn v hv, map_zero, smul_zero, add_zero]
  have ht0 : ∀ v', Ha.y v' = 0 → (Uw.F.Di Ha.i).EF t v' = 0 := fun v' hv' => by
    have := ht v'
    rwa [hv', map_zero, map_zero, neg_eq_zero] at this
  have hm : 1 ≤ Real.sqrt (max 1 ep⁻¹) := Real.one_le_sqrt.2 (le_max_left _ _)
  have htan : GtTanR eC := ArcQBC.gtTanR_of_letBC p hGl hL (s.tan τ i)
  unfold CMIn.line
  cases hk : s.kind τ i with
  | none =>
    obtain ⟨hb, hd⟩ := s.xi τ i hk
    obtain ⟨hsm, hadd, -⟩ := pairE_properties E a.D₀.X s.ξ
    let φ₀ : a.D₀.X →+ K₁ := AddMonoidHom.mk' (fun x => labK c K₁ τ (cc (pairE s.ξ x))) fun x y => by
      rw [hadd]; simp [cc]
    obtain ⟨b₂, d₂⟩ := (TorusTangent.main hGl K₁ a.D₀).2.2 ℂ aC.D₀ em p φ₀ (e τ i) eC hb hd hL
    let ξC : Module.Dual ℤ aC.D₀.X := s.ξ.comp p.xe.toIntLinearEquiv.toLinearMap
    have hpair : ∀ y, pairE (E := E) ξC y = pairE s.ξ (p.xe y) := fun y =>
      Finset.sum_congr rfl fun j _ => congrArg (fun q => _ * ((s.ξ q : ℤ) : E)) (hBC.2.1 _ y)
    have hv : ∀ y, xiVal (conjEmb (relab c σ τ)) ξC y = em (φ₀ (p.xe y)) := fun y => by
      rw [(pairE_properties E aC.D₀.X ξC).2.2.2.2, hpair]
      refine (ArchLen.emb_cc (relab c σ τ) _).symm.trans ?_
      exact RingHom.congr_fun hσ _
    have ha := anVec_torusLetter hGl E H Dw l Xo c σ O β Y aC χ W _ _ Uw.F Ha ξC t (conjEmb (relab c σ τ)) eC ht htan b₂
      fun y j hj => (d₂ y j hj).trans (congrArg _ (hv y).symm)
    have hcc : conjEmb (conjEmb (relab c σ τ)) = relab c σ τ := by ext u; simp [conjEmb]
    rw [hcc] at ha
    have hz' := ((ExpTan.anVec_bijective hGl E H Dw l Xo c σ O β Y aC χ W _ _ Uw.F Ha).1 eC htan).unique hz ha
    have hLz : L z = (2 * Real.pi * Complex.I : ℂ)⁻¹ • fun j => if (Uw.e j).1 = τ then Uw.Pm k x (gm t) j else 0 := by
      have := map_proj (fun j => relab c σ (Uw.e j).1) L.toLinearMap _ hspan' (by
        rintro u _ ⟨v, rfl⟩
        funext j
        have e₁ : (fun j => relab c σ (Uw.e j).1 (u : E) * Ha.Pw w₁ v j) = Ha.Pw w₁ (u • v) :=
          funext fun j => (hlin' u v j).symm
        rw [e₁, LinearEquiv.coe_coe, ← hP, ← hP, map_smul, hlin]) (relab c σ τ) (Ha.Pw w₁ t)
      simp only [(ArchLen.relab_inj c σ).eq_iff, LinearEquiv.coe_coe] at this hz'
      rw [hP, ← this, ← map_smul, hz', hPw t (hy t ht0)]
      congr 1
      funext j
      simp
    obtain ⟨τ', hτ'⟩ : ∃ τ' : (U.X k).Ψ, τ'.1 = relab c σ τ ∨ conjEmb τ'.1 = relab c σ τ := by
      by_cases hm : relab c σ τ ∈ (U.X k).Ψ
      · exact ⟨⟨_, hm⟩, Or.inl rfl⟩
      · refine ⟨⟨conjEmb (relab c σ τ), ?_⟩, Or.inr hcc⟩
        by_contra h'
        exact hm (((U.X k).cmType _).2 h')
    have key := htor (gm t) htξ τ τ' hτ'
    rw [htt] at key
    have hs : ∀ (q : ℂ) (u : Fin Uw.g → ℂ), (hermForm Hm (q • u) (q • u)).re = ‖q‖ ^ 2 * (hermForm Hm u u).re :=
      fun q u => by
        rw [← Complex.re_ofReal_mul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
        simp only [hermForm, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
        congr 1
        rw [Complex.star_def]; ring
    have hn : ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
      simp [abs_of_pos Real.pi_pos]
    rw [hLz, hs, hn]
    have hπ := Real.pi_gt_three
    have h1 : Real.pi * (2 * Real.pi)⁻¹ ^ 2 ≤ 1 := by
      rw [inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]
      nlinarith
    have h2 : (0 : ℝ) ≤ Real.pi * (2 * Real.pi)⁻¹ ^ 2 := by positivity
    have h3 : ep⁻¹ ≤ max 1 ep⁻¹ := le_max_right _ _
    have h4 : max 1 ep⁻¹ ≤ (La * Real.sqrt (max 1 ep⁻¹) * 1) ^ 2 := by
      rw [_root_.mul_one, mul_pow, Real.sq_sqrt (by positivity)]
      exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hLa)
    refine le_trans ?_ (h3.trans h4)
    rw [← _root_.mul_assoc]
    refine (mul_le_mul_of_nonneg_left ?_ h2).trans (mul_le_of_le_one_left (inv_pos.2 hep).le h1)
    convert key
  | some m =>
    obtain ⟨w, hw₁, hw₂⟩ := s.eta τ i m hk
    have htw : IsTangent w := by
      obtain ⟨w', hw1, hw2⟩ := s.L_good.2.2.1 m
      obtain rfl : w = w' := by
        refine Over.OverMorphism.ext (s.good.2.2.2.1.1.1.hom_ext ?_ ((Over.w w).trans (Over.w w').symm))
        unfold LamLetters.IsLetter at hw₁ hw1
        cases hq : s.L.src m with
        | inl q => rw [hq] at hw₁ hw1; exact hw₁.trans hw1.symm
        | inr q => rw [hq] at hw₁ hw1; exact hw₁.trans hw1.symm
      exact GlobalTheory.Reg.isTangent_of_isLieComb s.basis.1 hw2
    have hpos : 0 < (s.L.ℓ m).n em := by
      have := s.L_good.2.2.2 m
      cases hq : s.L.src m with
      | inl q => rw [hq] at this; exact this ▸ (s.good.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 q.2).1.2 em
      | inr q => rw [hq] at this; exact this ▸ (s.good.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 q.2).1.2 em
    obtain ⟨wC, hwC, htC⟩ := exists_vec p w htw
    obtain ⟨hc, -⟩ := (TauCanPull.tauCan_iff_of_isPullDeg hK K₁ ℂ em a.D₀ aC.D₀ p n' em.injective a.bimult
      aC.bimult).1 s.tau
    obtain ⟨sC, hsC⟩ := exists_isSplit hK ℂ aC.D₀ n' s.n_pos hc
    have hsc := isPull_scale p (SplitBC.split_baseChange hK K₁ ℂ em a.D₀ aC.D₀ p n' s.sB sC em.injective s.split hsC
      w wC hwC).2 hL hw₂
    rw [map_inv₀, map_natCast] at hsc
    obtain ⟨V, hV, hV'⟩ := AbelianLetters.exists_subspace_isometric hK.laws hK.laws2 E H Dw l Xo c σ O β Y aC χ W _ _
      Uw.F Ha n' sC s.n_pos hsC.1 hsC.2.1 hsC.2.2
    obtain ⟨hzV, hlen⟩ := hV' wC eC z htC hsc hz
    obtain ⟨y, hy₁, hy₂⟩ := ((NormTie.lengths_eq_norms hK E H Dw l c K₁ a e th jj n' La c₁ s em).2.2.2 aC.D₀ p).2
      m w wC hw₁ hwC
    obtain ⟨Hm₁, hh, hf⟩ := exists_pull_form Hm₀ hH₀.1 L.toLinearMap
    simp only [LinearEquiv.coe_coe] at hf
    have hy₃ := hlen w₁ Hm₁ y hw ⟨hh, fun u hu => hf u u ▸ hH₀.2.1 _ (L.map_ne_zero_iff.2 hu), fun u v => by
      rw [hf, ← hP, ← hP, hH₀.2.2, hEF]⟩ hy₁
    have horth : ∀ v, Ha.y v = 0 → herm (U.X k).Gm (Uw.φ k (gm v) : Fin r → E) ξ' = 0 := fun v hv => by
      have := eq_zero_of_trace (x := cc (-(U.X k).ξ0) * herm (U.X k).Gm (Uw.φ k (gm v) : Fin r → E) ξ') fun u => by
        have e₁ := Uw.iso k (gm t) (gm (u • v))
        rw [hEF, ht0 _ (by rw [map_smul, hv, smul_zero]), htξ, map_smul, map_smul] at e₁
        have s1 : ((u • Uw.φ k (gm v) : (U.X k).Λ) : Fin r → E) = (u : E) • (Uw.φ k (gm v) : Fin r → E) := rfl
        rw [s1, herm_swap, ArchLen.herm_smul_left] at e₁
        have e₂ := Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ)
          ((u : E) * (cc (-(U.X k).ξ0) * herm (U.X k).Gm (Uw.φ k (gm v) : Fin r → E) ξ'))
        rw [← e₂]
        refine Eq.trans ?_ (e₁.symm.trans (by simp))
        congr 1
        simp only [cc, AlgEquiv.coe_restrictScalars', map_mul, IsCMField.complexConj_apply_apply]
        ring
      exact (mul_eq_zero.1 this).resolve_left
        ((map_ne_zero (IsCMField.complexConj E)).2 (neg_ne_zero.2 (U.X k).ξ0_ne))
    have hsame := hab (V.map L.toLinearMap) (by
      rintro _ ⟨u, hu, rfl⟩
      refine Submodule.span_mono ?_ (Submodule.apply_mem_span_image_of_mem_span (L.toLinearMap.restrictScalars ℝ) (hV u hu))
      rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨gm v, horth v hv, by rw [hP, hPw v hv]; rfl⟩) (L z) ⟨z, hzV, rfl⟩
    rw [hsame, ← hf, mul_right_comm]
    have hLa' : 0 < La := one_pos.trans_le hLa
    exact le_sq_of_log (mul_pos hLa' hpos) hm (hy₃ ▸ hy₂ hLa')

end GlobalTheory.LetterLen
