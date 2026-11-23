import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusEigenvaluesTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowN
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.LineOfNotIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Sd

section Real

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E]

private noncomputable def diagR (E : Type) [Field E] [NumberField E] [IsTotallyReal E] : E →+* TR.Rinf E :=
  (TR.pInf E).comp (algebraMap E (Ad E))

private theorem infDiag_eqR (k : Eˣ) : infDiag k = TR.infId E (Units.map (diagR E).toMonoidHom k) := by
  classical
  have h : ((infDiag k : Ideles E) : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace E, w.Completion) →* AdeleRing (𝓞 E) E :=
      MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)
    change ∏ w : InfinitePlace E, ι (Pi.mulSingle w (algebraMap E w.Completion k)) =
      ι (fun w => algebraMap E w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [h]
  refine Prod.ext ?_ ?_
  · change _ = 1 - TR.infEq E 1 + TR.infEq E ((TR.infEq E).symm (algebraMap E (InfiniteAdeleRing E) k))
    simp
  · change (1 : Af E) = 1 - 0 + 0
    simp

private theorem denseRange_diagR : DenseRange (diagR E) := by
  have hc : Continuous (TR.infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)
  exact (TR.infEq E).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hc

private theorem denseRange_unitsR : DenseRange (Units.map (diagR E).toMonoidHom) := by
  refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ => ?_
  obtain ⟨k, v, hv, hk⟩ := denseRange_diagR.exists_mem_open (Units.isOpenEmbedding_val.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have h0 : k ≠ 0 := by
    rintro rfl
    exact v.ne_zero (hk.trans (map_zero _))
  exact ⟨v, hv, Units.mk0 k h0, Units.ext hk.symm⟩

private theorem diagR_mk (φ : E →+* ℂ) (k : E) : ((diagR E k (InfinitePlace.mk φ) : ℝ) : ℂ) = φ k := by
  have hr := IsTotallyReal.isReal (InfinitePlace.mk φ)
  have e : diagR E k (InfinitePlace.mk φ) = InfinitePlace.embedding_of_isReal hr k :=
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hr (WithAbs.toAbs _ k)
  rw [e, InfinitePlace.embedding_of_isReal_apply,
    InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hr)]

private theorem chiInf_pos {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) (u : (TR.Rinf E)ˣ)
    (hu : ∀ v, 0 < u.val v) :
    ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ n φ := by
  have hc : ∀ v, Continuous fun u : (TR.Rinf E)ˣ => u.val v := fun v => (continuous_apply v).comp Units.continuous_val
  have ho : IsOpen {u : (TR.Rinf E)ˣ | ∀ v, 0 < u.val v} := by
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (hc v)
  have hcl : IsClosed {u : (TR.Rinf E)ˣ |
      ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ n φ} :=
    isClosed_eq (Units.continuous_val.comp (TR.continuous_chiInf χ)) (continuous_finsetProd _ fun φ _ =>
      (Complex.continuous_ofReal.comp (hc _)).zpow₀ _ fun u => Or.inl
        (Complex.ofReal_ne_zero.2 (TR.unit_ne_zero u _)))
  refine closure_minimal ?_ hcl (denseRange_unitsR.open_subset_closure_inter ho hu)
  rintro _ ⟨hk, k, rfl⟩
  have h1 := h k fun φ => by
    have h2 := hk (InfinitePlace.mk (Complex.ofRealHom.comp φ))
    have h3 := diagR_mk (Complex.ofRealHom.comp φ) (k : E)
    exact h2.trans_eq (Complex.ofReal_injective h3)
  rw [HChar.inf, MonoidHom.comp_apply, infDiag_eqR] at h1
  refine h1.trans (Finset.prod_congr rfl fun φ _ => ?_)
  exact congrArg (· ^ n φ) (diagR_mk φ (k : E)).symm

private theorem expo_abs (k : ℕ) (v : InfinitePlace E) : TR.expo (Model.absPow E k) v = k := by
  classical
  refine TR.expo_eq_of_exp _ v _ fun t => ?_
  rw [chiInf_pos (GlobalTheory.Published.CharAboveModel.absPow_isAlgPos E k) _ fun w => Real.exp_pos _]
  simp only [TR.expU_val, Complex.ofReal_exp, ← Complex.exp_int_mul]
  rw [← Complex.exp_sum, Finset.sum_eq_single v.embedding]
  · simp
  · intro φ _ h
    have e : InfinitePlace.mk φ ≠ v := by
      rintro rfl
      exact h (InfinitePlace.embedding_mk_eq_of_isReal
        (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))).symm
    simp [Pi.single_eq_of_ne e]
  · simp

end Real

private theorem charEig_cyc_pow {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (k : ℕ) (w : HeightOneSpectrum (𝓞 F)) (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) :
    CharEig ι (cycBar F Ω l ^ k) w ((Model.absPow F k).val w : ℂˣ) := by
  intro A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h1 : cycZ F Ω l s = 1 := Units.ext (PadicInt.ext_of_toZModPow.mp fun n => by
      rw [cycZ_toZModPow_eq hw hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
      simp)
    rw [MonoidHom.pow_apply, cycBar, MonoidHom.comp_apply, h1, map_one, one_pow]
  · have h2 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
      change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
      rw [cycZ_of_isFrob hw hA hσ, map_natCast, map_natCast]
    rw [map_inv, Units.val_inv_eq_inv_val, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, h2,
      (Model.absPow_isAbsPow F k).2.1 w, Complex.cpow_neg, Complex.ofReal_natCast, Complex.cpow_natCast, map_inv₀,
      map_pow, map_natCast]
    rfl

private theorem attR_tw_cyc {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    {π : TR.CuspSub F n} (hA : AttR ι r π) (k : ℕ) :
    ∃ π' : TR.CuspSub F n, AttR ι (tw r (cycBar F Ω l ^ k)) π' ∧
      ∀ v (m : Fin n → ℤ), π.HasInfChar v (infOf m) → π'.HasInfChar v (infOf fun i => m i + k) := by
  refine ⟨π.twist (Model.absPow F k), ⟨(UpperTheory.galoisRep_irreducibility_criterion.1 _ (G F Ω) _ n r).2.2 _ hA.1, ?_⟩, fun v m h => ?_⟩
  · have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : l.Prime).ne_zero
    have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ((l : ℕ) : 𝓞 F) ∉ v.asIdeal :=
      (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
    filter_upwards [hA.2, hl] with w ⟨B, hB, hE⟩ hw
    refine ⟨_, hB.twist ((Model.absPow_isAbsPow F k).1 w), ?_⟩
    have h4 := UpperTheory.frobenius_eigenvalues_twist F Ω l ι n r _ w _ _ hE (charEig_cyc_pow ι k w hw)
    convert h4 using 1
    simp only [algSat, Multiset.bind_singleton, Multiset.map_map, Multiset.pure_def, Multiset.bind_def]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, Units.val_mul, mul_assoc]
  · have h1 := h.twist (Model.absPow F k)
    rw [expo_abs] at h1
    convert h1 using 1
    simp only [infOf, Multiset.map_map]
    refine Multiset.map_congr rfl fun i _ => ?_
    simp only [Function.comp_apply]
    push_cast
    ring

section Local

variable {l : ℕ} [Fact l.Prime]

private theorem norm_of_cong {a : (Qbar l)ˣ} (h : Cong a 1) : ‖(a : Qbar l)‖ = 1 := by
  have := IsUltrametricDist.norm_eq_of_add_norm_lt_max (x := (a : Qbar l)) (y := -1)
    (by rw [← sub_eq_add_neg, norm_neg, norm_one]; exact lt_of_lt_of_le h (le_max_right _ _))
  rw [this, norm_neg, norm_one]

variable (l) in
private def U1 : Subgroup (Qbar l)ˣ where
  carrier := {a | Cong a 1}
  one_mem' := by simp [Cong]
  mul_mem' {a b} ha hb := by
    have h := IsUltrametricDist.norm_add_le_max (((a : Qbar l) - 1) * b) ((b : Qbar l) - 1)
    rw [norm_mul, norm_of_cong hb, mul_one, show ((a : Qbar l) - 1) * b + (b - 1) = a * b - 1 by ring] at h
    exact h.trans_lt (max_lt ha hb)
  inv_mem' {a} ha := by
    have h : ‖((a⁻¹ : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv, norm_of_cong ha, inv_one]
    change ‖((a⁻¹ : (Qbar l)ˣ) : Qbar l) - 1‖ < 1
    rw [show ((a⁻¹ : (Qbar l)ˣ) : Qbar l) - 1 = (a⁻¹ : (Qbar l)ˣ) * (1 - a) by rw [mul_sub, Units.inv_mul, mul_one],
      norm_mul, h, one_mul, norm_sub_rev]
    exact ha

private theorem cong_iff {a b : (Qbar l)ˣ} (hb : ‖(b : Qbar l)‖ = 1) : Cong a b ↔ a * b⁻¹ ∈ U1 l := by
  change _ ↔ ‖((a * b⁻¹ : (Qbar l)ˣ) : Qbar l) - 1‖ < 1
  rw [Cong, show (a : Qbar l) - b = (((a * b⁻¹ : (Qbar l)ˣ) : Qbar l) - 1) * b by
    rw [sub_mul, Units.val_mul, mul_assoc, Units.inv_mul, mul_one, one_mul], norm_mul, hb, mul_one]

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]

private theorem cyc_val (s : G F Ω) :
    ((cycBar F Ω l s : (Qbar l)ˣ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((cycZ F Ω l s : ℤ_[l]) : ℚ_[l]) := rfl

private theorem cyc_mem (s : G F Ω) {j : ℤ} (hj : (l : ℤ) - 1 ∣ j) : cycBar F Ω l s ^ j ∈ U1 l := by
  obtain ⟨j, rfl⟩ := hj
  rw [zpow_mul, show (l : ℤ) - 1 = ((l - 1 : ℕ) : ℤ) by rw [Nat.cast_pred (Fact.out : l.Prime).pos], zpow_natCast]
  refine zpow_mem ?_ j
  have e : ((cycBar F Ω l s ^ (l - 1) : (Qbar l)ˣ) : Qbar l) - ((1 : (Qbar l)ˣ) : Qbar l) =
      algebraMap ℚ_[l] (Qbar l) ((((cycZ F Ω l s : ℤ_[l]) ^ (l - 1) - 1 : ℤ_[l])) : ℚ_[l]) := by
    rw [Units.val_pow_eq_pow_val, cyc_val]; simp
  change ‖_ - _‖ < 1
  rw [e, norm_algebraMap']
  change ‖(cycZ F Ω l s : ℤ_[l]) ^ (l - 1) - 1‖ < 1
  rw [← PadicInt.mem_nonunits, ← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow,
    map_one, ZMod.pow_card_sub_one_eq_one, sub_self]
  exact ((cycZ F Ω l s).isUnit.map _).ne_zero

variable [NumberField F] [IsAlgClosure F Ω]

private theorem dec_cong {A : ValuationSubring Ω} {w : Pl F} (hA : IsPlaceOver A w) (χ : ↥(Dec (F := F) A) →* (Qbar l)ˣ)
    (hc : Continuous fun g => (χ g : Qbar l)) (hI : ∀ g : ↥(Dec (F := F) A), (g : G F Ω) ∈ Ine (F := F) A → χ g ∈ U1 l)
    (hF : ∀ σ : ↥(Dec (F := F) A), IsFrob A (normV w) (σ : G F Ω) → χ σ ∈ U1 l) (g : ↥(Dec (F := F) A)) :
    χ g ∈ U1 l := by
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  have h1 := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A w hA ⟨σ, hσ.1⟩ hσ
  have ho : IsOpen (((U1 l).comap χ : Subgroup _) : Set ↥(Dec (F := F) A)) :=
    isOpen_lt (hc.sub continuous_const).norm continuous_const
  have h2 := Subgroup.topologicalClosure_minimal _ (sup_le ((Subgroup.zpowers_le).2 (hF ⟨σ, hσ.1⟩ hσ))
    fun x (hx : x ∈ (Ine (F := F) A).subgroupOf (Dec (F := F) A)) => hI x hx : _ ≤ (U1 l).comap χ)
    (Subgroup.isClosed_of_isOpen _ ho)
  rw [h1] at h2
  exact h2 (Subgroup.mem_top g)

private theorem ordAt_tw {r : G F Ω →* GL (Fin 2) (Qbar l)} (hr : Continuous r) {s : ℤ} (hs : (l : ℤ) - 1 ∣ s)
    {ψ₀ ψ₁ : G F Ω →* (Qbar l)ˣ} (hd : Matrix.GeneralLinearGroup.det.comp r = cycBar F Ω l ^ s * (ψ₀ * ψ₁))
    (hc : Continuous ψ₀) (h0 : ∀ g, ‖(ψ₀ g : Qbar l)‖ = 1) (h1 : ∀ g, ‖(ψ₁ g : Qbar l)‖ = 1)
    {A : ValuationSubring Ω} {w : Pl F} (hA : IsPlaceOver A w) (hI : Ine (F := F) A ≤ ψ₀.ker)
    {m : Fin 2 → ℤ} (hm : (l : ℤ) - 1 ∣ m 0) {κ : Fin 2 → ↥(Dec (F := F) A) →* (Qbar l)ˣ}
    (hκ : IsFlagOn r (Dec (F := F) A) κ)
    (hκI : ∀ i (g : ↥(Dec (F := F) A)), (g : G F Ω) ∈ Ine (F := F) A → κ i g = cycBar F Ω l g ^ m i)
    (hκF : ∀ σ : ↥(Dec (F := F) A), IsFrob A (normV w) (σ : G F Ω) →
      Cong (κ 0 σ⁻¹ * cycBar F Ω l (σ : G F Ω) ^ m 0) (ψ₀ (σ : G F Ω)⁻¹))
    {k : ℕ} (hk : (l : ℤ) - 1 ∣ k) :
    OrdAt (tw r (cycBar F Ω l ^ k)) (fun i => m i + k) ![ψ₀, ψ₁] A := by
  refine ⟨_, (shapeFacts l _ 2 r (cycBar F Ω l ^ k)).2.2.1 _ κ hκ, fun i g hg => ?_, ?_⟩
  · simp [hκI i g hg, zpow_add]
  obtain ⟨P, hP⟩ := hκ
  have e0 : ∀ g : ↥(Dec (F := F) A), κ 0 g * (ψ₀ g)⁻¹ ∈ U1 l := by
    refine dec_cong hA (κ 0 * (ψ₀.comp (Dec (F := F) A).subtype)⁻¹) ?_ (fun g hg => ?_) fun σ hσ => ?_
    · have c1 : Continuous fun g : ↥(Dec (F := F) A) => (P * r g * P⁻¹ : GL (Fin 2) (Qbar l)) 0 0 :=
        (Units.continuous_val.comp ((continuous_const.mul (hr.comp continuous_subtype_val)).mul
          continuous_const)).matrix_elem 0 0
      simp only [(hP _).2] at c1
      exact c1.mul (Units.continuous_val.comp (hc.comp continuous_subtype_val).inv)
    · change κ 0 g * (ψ₀ g)⁻¹ ∈ _
      rw [hκI 0 g hg, MonoidHom.mem_ker.1 (hI hg), inv_one, mul_one]
      exact cyc_mem _ hm
    · have := (U1 l).mul_mem ((U1 l).inv_mem ((cong_iff (h0 _)).1 (hκF σ hσ))) (cyc_mem (σ : G F Ω) hm)
      convert this using 1
      change κ 0 σ * (ψ₀ σ)⁻¹ = _
      simp only [map_inv]
      apply Units.ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
  have ed : ∀ g : ↥(Dec (F := F) A), κ 0 g * κ 1 g = cycBar F Ω l g ^ s * (ψ₀ g * ψ₁ g) := fun g => by
    have h2 : Matrix.GeneralLinearGroup.det (r g) = cycBar F Ω l g ^ s * (ψ₀ g * ψ₁ g) := DFunLike.congr_fun hd (g : G F Ω)
    have h3 : Matrix.GeneralLinearGroup.det (P * r g * P⁻¹) = Matrix.GeneralLinearGroup.det (r g) := by
      rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    rw [← h2, ← h3]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, (hP g).2, (hP g).2, (hP g).1 1 0 (by decide)]
    simp
  have hk' : ∀ g : G F Ω, cycBar F Ω l g ^ k ∈ U1 l := fun g => by simpa using cyc_mem g hk
  refine Fin.forall_fin_two.2 ⟨fun g => (cong_iff (h0 _)).2 ?_, fun g => (cong_iff (h1 _)).2 ?_⟩
  · convert (U1 l).mul_mem (e0 g) (hk' g) using 1
    change κ 0 g * cycBar F Ω l g ^ k * (ψ₀ g)⁻¹ = _
    rw [mul_right_comm]
  · convert (U1 l).mul_mem ((U1 l).mul_mem ((U1 l).inv_mem (e0 g)) (cyc_mem (g : G F Ω) hs)) (hk' g) using 1
    change κ 1 g * cycBar F Ω l g ^ k * (ψ₁ g)⁻¹ = _
    rw [← mul_left_cancel_iff (a := κ 0 g), ← mul_assoc, ← mul_assoc, ed]
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp

private theorem exists_ine (A : ValuationSubring Ω) (hv : A.valuation (l : Ω) < 1) {H : Subgroup (G F Ω)}
    (hH : IsOpen (H : Set (G F Ω))) {n : ℤ} (hn : n ≠ 0) : ∃ g ∈ H, g ∈ Ine (F := F) A ∧ cycBar F Ω l g ^ n ≠ 1 := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  obtain ⟨u, hu⟩ := GlobalTheory.CycDec.exists_unit_infinite_order l
  obtain ⟨σ, hσ, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv u
  let K : IntermediateField ℚ Ω := (IsScalarTower.toAlgHom ℚ F Ω).fieldRange
  have : FiniteDimensional ℚ K :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ F Ω)).toLinearEquiv.finiteDimensional
  have : Finite ((Ω ≃ₐ[ℚ] Ω) ⧸ K.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ K.fixingSubgroup_isOpen
  have : K.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := K.fixingSubgroup)) σ
  let g : G F Ω := { (σ ^ N).toRingEquiv with
    commutes' := fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem _ ⟨x, rfl⟩ }
  have hD : σ ^ N ∈ Ine (F := ℚ) A := pow_mem hσ N
  have hg : g ∈ Ine (F := F) A := ⟨hD.1, hD.2⟩
  have hc : cycZ F Ω l g = u ^ N := by rw [← hσu, ← map_pow]; rfl
  have : Finite (G F Ω ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨M, hM, -, hMH⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (H := H) Subgroup.FiniteIndex.index_ne_zero g
  refine ⟨_, hMH, pow_mem hg M, fun h => ?_⟩
  have hinj : Function.Injective
      (Units.map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom) :=
    Units.map_injective ((algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective)
  refine hu ((N : ℤ) * M * n) (mul_ne_zero (by positivity) hn) (hinj ?_)
  rw [map_one, ← h, cycBar, MonoidHom.comp_apply, map_pow (cycZ F Ω l), hc, zpow_mul, zpow_mul, zpow_natCast,
    zpow_natCast, map_zpow]

private theorem irrOpen_of (hl : l ≠ 2) {r : G F Ω →* GL (Fin 2) (Qbar l)} {ξ : G F Ω →* (Qbar l)ˣ}
    (hn : ∀ g, ‖(ξ g : Qbar l)‖ = 1) (hi : IsIrr r) (hres : ResSum r ![1, ξ]) (hsq : ∃ g, ¬ Cong (ξ g ^ 2) 1)
    {A : ValuationSubring Ω} (hv : A.valuation (l : Ω) < 1) {k : ℤ} (hk : k ≠ 0) {ψ} (ho : OrdAt r ![k, 0] ψ A) :
    IrrOpen r := by
  intro H hH
  obtain ⟨κ, ⟨P, hP⟩, hκ, -⟩ := ho
  obtain ⟨g₀, hg₀⟩ := hsq
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have : Finite (G F Ω ⧸ H) := H.quotient_finite_of_isOpen hH
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hO : IsOpen (H.normalCore : Set (G F Ω)) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (H.normalCore_isClosed (H.isClosed_of_isOpen hH))
  have h1 : IsIrr (r.comp H.normalCore.subtype) := by
    by_contra hI
    refine hg₀ ((sIabs l hl _ r ξ hn hi hres _ inferInstance ?_ hI).2 g₀)
    obtain ⟨g, hgH, hg, hne⟩ := exists_ine A hv hO hk
    refine ⟨g, hgH, ?_⟩
    let s : ↥(Dec (F := F) A) := ⟨g, Ine_le_Dec A hg⟩
    have e : ((P * r g * P⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly =
        (r g : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly := by
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
      exact Matrix.charpoly_units_conj P _
    rw [← e, Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => (hP s).1 i j hij), Fin.prod_univ_two,
      (hP s).2, (hP s).2, hκ 0 s hg, hκ 1 s hg]
    refine separable_X_sub_C.mul separable_X_sub_C (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 fun h => hne ?_).isUnit)
    simpa using Units.ext h
  exact ⟨h1.1, fun _ _ _ => Submodule.mem_top, fun W hW hI => h1.2.2 W hW fun g v hv => hI ⟨g, H.normalCore_le g.2⟩ v hv⟩

end Local

private theorem cont_units {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv
