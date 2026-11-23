import Development.WeilBound.ThetaLifts.LatticeBasics.Unfold0
import Development.WeilBound.ThetaLifts.LatticeBasics.FdEqZero
import Development.WeilBound.ThetaLifts.LatticeBasics.OffOpenAlt
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.UnipUGood
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingZeroMeanNormalizedSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumSetIntegralFundamentalDomainEqZeroByOrbits

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKEnd (unipU IsCusp)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
  {χ : Chr F E} {z : ℂ} {f : G2 σ Y → ℂ} {e : UA σ Y.J × UA σ Y.J →* G2 σ Y}

theorem absE_det' (d0 : Y.J.det ≠ 0) (h : UA σ Y.J) : absE F E (Matrix.GeneralLinearGroup.det h.1) = 1 := by
  have u : IsUnit (incM F Y.J).det := by
    rw [incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact d0.isUnit.map _
  have e := congrArg Matrix.det (show (mat h)ᵀ * incM F Y.J * (mat h).map (cA σ) = incM F Y.J from h.2)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_right_comm, u.mul_eq_right,
    show ((mat h).map (cA σ)).det = sigR (AF F) σ (mat h).det from (RingHom.map_det (sigR (AF F) σ) _).symm] at e
  have e2 : Matrix.GeneralLinearGroup.det h.1 * GlobalTheory.Doubling.conjUnit σ (Matrix.GeneralLinearGroup.det h.1) = 1 := Units.ext e
  have e3 := congrArg (absE F E) e2
  rw [map_mul, GlobalTheory.Doubling.absE_conjUnit, map_one] at e3
  exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 (by rw [sq, e3])

theorem Law.diag' (h : Law χ z f) (d0 : Y.J.det ≠ 0) (he : ∀ h h', IsEmb h h' (e (h, h'))) (g : UA σ Y.J) (x) :
    f (e (g, g) * x) * detInv χ g = f x := by
  rw [h _ _ x (he g g).par, absE_det' d0, detInv, mul_right_comm]; simp

variable (σ Y) in

abbrev Cos : Type := Quotient (QuotientGroup.rightRel ((par2 σ Y).subgroupOf (rat2 σ Y)))

theorem cos_eq {a b : rat2 σ Y} : (Quotient.mk _ a : Cos σ Y) = Quotient.mk _ b ↔ b.1 * a.1⁻¹ ∈ par2 σ Y :=
  Quotient.eq.trans (QuotientGroup.rightRel_apply.trans Subgroup.mem_subgroupOf)

theorem out_rel (γ : rat2 σ Y) : γ.1 * ((Quotient.mk _ γ : Cos σ Y).out.1)⁻¹ ∈ par2 σ Y :=
  cos_eq.1 (Quotient.mk _ γ : Cos σ Y).out_eq

theorem Law.out (h : Law χ z f) (hχ : IsHecke F E χ) (γ : rat2 σ Y) (x) : eisTerm f x (Quotient.mk _ γ) = f (γ.1 * x) :=
  (h.rat hχ (out_rel γ) (mul_mem γ.2 (inv_mem (Quotient.out _ : rat2 σ Y).2)) _).symm.trans (by simp [mul_assoc])

def rmul (c : rat2 σ Y) : Cos σ Y → Cos σ Y :=
  Quotient.map' (· * c) fun a b h => QuotientGroup.rightRel_apply.2 (by simpa using QuotientGroup.rightRel_apply.1 h)

theorem Law.rmul_eq (h : Law χ z f) (hχ : IsHecke F E χ) (c : rat2 σ Y) (q : Cos σ Y) (x) :
    eisTerm f x (rmul c q) = eisTerm f (c.1 * x) q := by
  induction q using Quotient.ind with
  | _ γ => exact (h.out hχ (γ * c) x).trans ((congrArg f (mul_assoc _ _ _)).trans (h.out hχ γ _).symm)

theorem Law.eis_rat (h : Law χ z f) (hχ : IsHecke F E χ) {Ê : G2 σ Y → ℂ} (hs : ∀ x, HasSum (eisTerm f x) (Ê x)) {c : G2 σ Y}
    (hc : c ∈ rat2 σ Y) (x) : Ê (c * x) = Ê x := by
  let u : Cos σ Y ≃ Cos σ Y := ⟨rmul ⟨c, hc⟩, rmul ⟨c, hc⟩⁻¹, fun q => by
    induction q using Quotient.ind with
    | _ γ => exact congrArg (Quotient.mk _) (mul_inv_cancel_right _ _), fun q => by
    induction q using Quotient.ind with
    | _ γ => exact congrArg (Quotient.mk _) (inv_mul_cancel_right _ _)⟩
  refine (hs _).unique ?_
  convert u.hasSum_iff.2 (hs x) using 1
  exact funext fun q => (h.rmul_eq hχ ⟨c, hc⟩ q x).symm

def ratE (he : ∀ h h', IsEmb h h' (e (h, h'))) (δ : ratU σ Y.J) : rat2 σ Y := ⟨e (1, δ), (he _ _).rat (one_mem _) δ.2⟩

@[reducible] def cosAct (he : ∀ h h', IsEmb h h' (e (h, h'))) : MulAction (ratU σ Y.J) (Cos σ Y) where
  smul δ := rmul (ratE he δ⁻¹)
  one_smul q := by
    induction q using Quotient.ind with
    | _ γ => exact congrArg (Quotient.mk _) (Subtype.ext (by simp [ratE, show ((1, 1) : UA σ Y.J × UA σ Y.J) = 1 from rfl]))
  mul_smul a b q := by
    induction q using Quotient.ind with
    | _ γ => exact congrArg (Quotient.mk _) (Subtype.ext (by simp [ratE, mul_assoc, ← map_mul]))

def Neg (e : UA σ Y.J × UA σ Y.J →* G2 σ Y) (q : Cos σ Y) : Prop := ¬ ∃ δ ∈ ratU σ Y.J, q.out.1 * (e (1, δ))⁻¹ ∈ par2 σ Y

theorem neg_iff (he : ∀ h h', IsEmb h h' (e (h, h'))) (q : Cos σ Y) : Neg e q ↔ ¬ ∃ δ, Quotient.mk _ (ratE he δ) = q :=
  not_congr ⟨fun ⟨δ, h1, h2⟩ => ⟨⟨δ, h1⟩, ((cos_eq (a := ratE he ⟨δ, h1⟩) (b := q.out)).2 h2).trans q.out_eq⟩,
    fun ⟨δ, h⟩ => ⟨δ, δ.2, (cos_eq (a := ratE he δ) (b := q.out)).1 (h.trans q.out_eq.symm)⟩⟩

theorem ratE_inj (he : ∀ h h', IsEmb h h' (e (h, h'))) : Function.Injective fun δ => (Quotient.mk _ (ratE he δ) : Cos σ Y) :=
  fun δ δ' h => by
    obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 ((cos_eq (a := ratE he δ) (b := ratE he δ')).1 h)
    change IsPar (e (1, δ') * (e (1, δ))⁻¹) t at ht
    rw [← map_inv, ← map_mul, isPar_iff, he] at ht
    simp only [diagCols, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, Matrix.mul_one, Matrix.zero_mul, add_zero, zero_add,
      Matrix.one_mul] at ht
    obtain ⟨a, b⟩ := Matrix.fromRows_inj ht
    have : (1 : UA σ Y.J) * 1⁻¹ = δ'.1 * δ.1⁻¹ := Subtype.ext (Units.ext (a.trans b.symm))
    rw [inv_one, mul_one, eq_mul_inv_iff_mul_eq, one_mul] at this
    exact Subtype.ext this

theorem mem_stab (he : ∀ h h', IsEmb h h' (e (h, h'))) (q : Cos σ Y) (x : UA σ Y.J) :
    x ∈ (@MulAction.stabilizer _ _ _ (cosAct he) q).map (ratU σ Y.J).subtype ↔
      x ∈ ratU σ Y.J ∧ q.out.1 * e (1, x) * q.out.1⁻¹ ∈ par2 σ Y := by
  have k : ∀ δ : ratU σ Y.J, δ ∈ @MulAction.stabilizer _ _ _ (cosAct he) q ↔ q.out.1 * e (1, δ) * q.out.1⁻¹ ∈ par2 σ Y := fun δ => by
    change rmul (ratE he δ⁻¹) q = q ↔ _
    conv_lhs => rw [← q.out_eq]
    refine (cos_eq (a := q.out * ratE he δ⁻¹)).trans ?_
    change q.out.1 * (q.out.1 * e (1, δ.1⁻¹))⁻¹ ∈ par2 σ Y ↔ _
    rw [mul_inv_rev, ← map_inv, Prod.inv_mk, inv_one, inv_inv, mul_assoc]
  exact ⟨fun ⟨δ, h, e⟩ => e ▸ ⟨δ.2, (k δ).1 h⟩, fun h => ⟨⟨x, h.1⟩, (k _).2 h.2, rfl⟩⟩

open Classical in
theorem unfoldC (hO : OffOpen) (hU : PositivityTheory.ThKEnd.Grp.UnipUGood) {B : Base F E} {r s : ℕ} (hB : B.IsGood σ) (hY : Y.IsSkew σ B r s)
    (d0 : Y.J.det ≠ 0) [LocallyCompactSpace (UA σ Y.J)] [SecondCountableTopology (UA σ Y.J)] [T2Space (UA σ Y.J)]
    (hχ : IsHecke F E χ) (he : ∀ h h', IsEmb h h' (e (h, h'))) (ce : Continuous e) (cf : Continuous f) (hf : Law χ z f)
    {Ê : G2 σ Y → ℂ} (hs : ∀ x, HasSum (eisTerm f x) (Ê x)) {μ : Measure (UA σ Y.J)} {D : Set (UA σ Y.J)} (hμ : μ.IsHaarMeasure)
    (hD : IsFundamentalDomain (ratU σ Y.J) D μ) (hi : Integrable (fun g => f (e (1, g))) μ) {φ : UA σ Y.J → ℂ} (hφ : IsRapid φ)
    (hc : IsCusp Y φ) (h : UA σ Y.J) (hfin : ∑' q : Cos σ Y, ∫⁻ x in D, ‖eisTerm f (e (h, x)) q * detInv χ x * φ x‖ₑ ∂μ ≠ ⊤) :
    ∫ h' in D, Ê (e (h, h')) * detInv χ h' * φ h' ∂μ = ∫ g, f (e (1, g)) * detInv χ g * φ (h * g) ∂μ := by
  haveI := countable_ratU (σ := σ) (Y := Y)
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : Countable (rat2 σ Y) := by
    haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
    haveI : Countable (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) := inferInstanceAs (Countable (_ → _ → E))
    haveI : Countable (GL (Fin n ⊕ Fin n) E) := Units.val_injective.countable
    exact (Set.countable_range (Matrix.GeneralLinearGroup.map (n := Fin n ⊕ Fin n) (inclR (F := F) (E := E) (AF F)))).preimage
      Subtype.val_injective
  letI := cosAct he
  let T : Cos σ Y → UA σ Y.J → ℂ := fun q x => eisTerm f (e (h, x)) q * detInv χ x * φ x
  have cK : ∀ q, Continuous fun x => eisTerm f (e (h, x)) q * detInv χ x := fun q =>
    (cf.comp (continuous_const.mul (ce.comp (Continuous.prodMk_right h)))).mul (continuous_detInv hχ)
  have cT : ∀ q, Continuous (T q) := fun q => (cK q).mul hφ.1
  have sa : Summable fun q => ∫ x in D, T q x ∂μ := Summable.of_norm_bounded (ENNReal.summable_toReal hfin) fun q =>
    toReal_enorm (∫ x in D, T q x ∂μ) ▸ ENNReal.toReal_mono (ENNReal.ne_top_of_tsum_ne_top hfin q) (enorm_integral_le_lintegral_enorm _)
  have nd : ∀ (δ : ratU σ Y.J) q, Neg e (δ • q) ↔ Neg e q := fun δ q => by
    rw [neg_iff he, neg_iff he]
    have k : ∀ (δ η : ratU σ Y.J), δ • (Quotient.mk _ (ratE he η) : Cos σ Y) = Quotient.mk _ (ratE he (η * δ⁻¹)) := fun δ η =>
      congrArg (Quotient.mk _) (Subtype.ext (by simp [ratE, ← map_mul]))
    exact not_congr ⟨fun ⟨η, hη⟩ => ⟨η * δ⁻¹⁻¹, by rw [← k, hη, inv_smul_smul]⟩, fun ⟨η, hη⟩ => ⟨η * δ⁻¹, by rw [← k, hη]⟩⟩
  have neg : ∑' q, ∫ x in D, (if Neg e q then T q x else 0) ∂μ = 0 := by
    refine GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero _ μ (ratU σ Y.J) (Cos σ Y) D hD (fun q x => if Neg e q then T q x else 0)
      (fun q => by split_ifs; exacts [(cT q).measurable, measurable_const]) (fun δ q x => ?_)
      (ne_top_of_le_ne_top hfin (ENNReal.tsum_le_tsum fun q => lintegral_mono fun x => by split_ifs; exacts [le_rfl, by simp]))
      fun q 𝓖 h𝓖 ig => ?_
    · rw [nd]
      refine if_congr Iff.rfl ?_ rfl
      change eisTerm f _ (rmul _ q) * _ * _ = _
      rw [hf.rmul_eq hχ, detInv_mul, detInv_rat hχ δ.2, one_mul, hφ.2.1 _ δ.2]
      simp [T, ratE, ← map_mul]
    by_cases hq : Neg e q
    swap
    · simp [hq]
    simp only [if_pos hq] at ig ⊢
    obtain ⟨U, u1, u2, u3, u4⟩ := hO F E σ B n Y r s hB hY e he _ q.out.2 hq
    obtain ⟨g, -⟩ := hU F E σ hB.cm n Y (.inr hY.skew) d0 U
    obtain ⟨κ, 𝓜, k1, k2, k3⟩ := g.ex
    have st := mem_stab he q
    have mv : ∀ δ x, q.out.1 * e (h, δ * x) = q.out.1 * e (1, δ) * q.out.1⁻¹ * (q.out.1 * e (h, x)) := fun δ x => by
      simp [mul_assoc, ← map_mul]
    refine GlobalTheory.UnfoldNormal.unfold_zero_mean _ μ _ (unipU σ Y U) (Set.Countable.mono (fun x hx => ((st x).1 hx).1)
      (Set.countable_coe_iff.1 countable_ratU)).to_subtype g.closed (fun δ hδ => u4 δ ((st δ).1 hδ).1 ((st δ).1 hδ).2) κ 𝓜 k1 ?_
      (by simp [k3]) _ φ (cK q).measurable hφ.1.measurable (fun m hm x => ?_) (fun δ hδ x => ?_)
      (fun δ hδ => hφ.2.1 δ ((st δ).1 hδ).1) (hc U u1 u2 κ 𝓜 k1 k2) 𝓖 h𝓖 ig
    · refine (Subgroup.ext fun m => ?_ : (ratU σ Y.J).subgroupOf (unipU σ Y U) =
        ((MulAction.stabilizer (ratU σ Y.J) q).map (ratU σ Y.J).subtype).subgroupOf (unipU σ Y U)) ▸ k2
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, st]
      exact ⟨fun h => ⟨h, mem_parabolic_GL2_iff.2 ((u3 m m.2).imp fun _ => And.left)⟩, And.left⟩
    · obtain ⟨t, t1, t2, t3⟩ := u3 m hm
      simp only [eisTerm]
      rw [mv, hf _ t _ t1, t2, detInv_mul, detInv, t3]; simp
    · simp only [eisTerm]
      rw [mv, hf.rat hχ ((st δ).1 hδ).2 (mul_mem (mul_mem q.out.2 ((he _ _).rat (one_mem _) ((st δ).1 hδ).1)) (inv_mem q.out.2)),
        detInv_mul, detInv_rat hχ ((st δ).1 hδ).1, one_mul]
  obtain ⟨C, hC⟩ := hφ.2.2 0
  let k : UA σ Y.J → ℂ := fun g => f (e (1, g)) * detInv χ g * φ (h * g)
  have ik : Integrable k μ := by
    simp only [k, mul_assoc]
    exact hi.mul_bdd (c := C) ((continuous_detInv hχ).mul (hφ.1.comp (continuous_const_mul h))).aestronglyMeasurable
      (.of_forall fun g => by simpa [norm_detInv] using hC (h * g))
  have op : ∀ δ : ratU σ Y.J, ∀ x, T (Quotient.mk _ (ratE he δ)) x = k (h⁻¹ * (δ • x)) := fun δ x => by
    simp only [k, T, hf.out hχ, ratE, Subgroup.smul_def, smul_eq_mul]
    rw [← Law.diag' hf d0 he h (e (1, h⁻¹ * _)), ← map_mul, ← map_mul, detInv_mul, detInv_mul, detInv_rat hχ δ.2, mul_inv_cancel_left,
      hφ.2.1 _ δ.2]
    have : detInv χ h * detInv χ h⁻¹ = 1 := by rw [← detInv_mul, mul_inv_cancel, detInv_rat hχ (one_mem _)]
    simp only [Prod.mk_mul_mk, one_mul, mul_one, mul_inv_cancel_left]
    linear_combination (-(f (e (h, δ * x)) * detInv χ x * φ x)) * this
  have sb : ∀ (p : Cos σ Y → Prop) [DecidablePred p], Summable fun q => if p q then ∫ x in D, T q x ∂μ else 0 := fun p _ =>
    Summable.of_norm_bounded sa.norm fun q => by split_ifs; exacts [le_rfl, by simp]
  calc _ = ∫ x in D, ∑' q, T q x ∂μ := integral_congr_ae (.of_forall fun x => (((hs _).mul_right _).mul_right _).tsum_eq.symm)
    _ = ∑' q, ∫ x in D, T q x ∂μ := integral_tsum (fun q => (cT q).aestronglyMeasurable) hfin
    _ = ∑' q, ((if Neg e q then ∫ x in D, T q x ∂μ else 0) + if ¬ Neg e q then ∫ x in D, T q x ∂μ else 0) :=
        tsum_congr fun q => by by_cases hq : Neg e q <;> simp [hq]
    _ = ∑' q, if ¬ Neg e q then ∫ x in D, T q x ∂μ else 0 := by
        rw [(sb (Neg e)).tsum_add (sb fun q => ¬ Neg e q), add_eq_right]
        refine Eq.trans ?_ neg
        exact tsum_congr fun q => by by_cases hq : Neg e q <;> simp [hq]
    _ = ∑' δ : ratU σ Y.J, ∫ x in D, k (h⁻¹ * (δ • x)) ∂μ := by
        rw [← (ratE_inj he).tsum_eq]
        · exact tsum_congr fun δ => by rw [if_pos (by rw [neg_iff he, not_not]; exact ⟨δ, rfl⟩)]; simp only [op]
        · intro q hq
          by_contra hn
          exact hq (if_neg (not_not.2 ((neg_iff he q).2 hn)))
    _ = _ := by
        rw [← hD.integral_eq_tsum'' (fun x => k (h⁻¹ * x)) (ik.comp_mul_left h⁻¹), integral_mul_left_eq_self k]

end GlobalTheory.ThK.Dbl

end
