import Development.WeilBound.ThetaLifts.SmallCones.UnfParH
import Development.WeilBound.ThetaLifts.SmallCones.MatCancel
import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod

noncomputable section

namespace PositivityTheory.ThKCT.Unf

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKCT.Fr PositivityTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.SW (hypJ)

section Ring

variable {K : Type} [CommRing K]

theorem conj_iff {n : Type} [Fintype n] [DecidableEq n] (s : K →+* K) {ξ : K} (hξ : IsUnit ξ) {J J' : Matrix n n K} (a : GL n K)
    (ha : ξ • (a.1ᵀ * J * a.1.map s)ᵀ = J') {g h : Matrix n n K} (e : g * a.1 = a.1 * h) :
    (h.map s)ᵀ * J' * h = J' ↔ gᵀ * J * g.map s = J := by
  have e1 : (h.map s)ᵀ * J' * h = ξ • (a.1ᵀ * (gᵀ * J * g.map s) * a.1.map s)ᵀ := by
    have : a.1ᵀ * (gᵀ * J * g.map s) * a.1.map s = (g * a.1)ᵀ * J * (g * a.1).map s := by
      simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
    rw [this, e, ← ha]
    simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc, Matrix.transpose_transpose, Matrix.mul_smul,
      Matrix.smul_mul]
  have u1 : IsUnit a.1ᵀ := (Matrix.isUnit_transpose _).2 a.isUnit
  have u2 : IsUnit (a.1.map s) := a.isUnit.map s.mapMatrix
  rw [e1, ← ha, hξ.smul_left_cancel, Matrix.transpose_inj, u2.mul_left_inj, u1.mul_right_inj]

def fc {n m : ℕ} (x y : Fin n → K) (ι : Matrix (Fin n) (Fin m) K) : Matrix (Fin n) (Fin (m + 2)) K :=
  Matrix.of fun i => Fin.cons (x i) (Fin.cons (y i) (ι i))

theorem fc_cols {n m : ℕ} {x y : Fin n → K} {ι : Matrix (Fin n) (Fin m) K} {g : Matrix (Fin n) (Fin n) K} {a b d : K}
    {r w : Fin m → K} {U : Matrix (Fin m) (Fin m) K} (e : g * fc x y ι = fc x y ι * pm a b r d w U) :
    g *ᵥ x = a • x ∧ g *ᵥ y = b • x + d • y + ι *ᵥ w ∧ g * ι = Matrix.vecMulVec x r + ι * U := by
  refine ⟨funext fun i => ?_, funext fun i => ?_, Matrix.ext fun i j => ?_⟩
  · have := congrFun (congrFun e i) 0
    simpa [fc, pm, blk, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.mulVec, dotProduct, mul_comm] using this
  · have := congrFun (congrFun e i) 1
    simpa [fc, pm, blk, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.mulVec, dotProduct, mul_comm, add_assoc] using this
  · have := congrFun (congrFun e i) j.succ.succ
    simpa [fc, pm, blk, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMulVec_apply] using this

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem conjEx (h : IsCMExt F E σ) {n : ℕ} {J J' : Matrix (Fin n) (Fin n) E} {ξ : E} (hξ : ξ ≠ 0) (A : GL (Fin n) E)
    (hA : ξ • (A.1ᵀ * J * A.1.map σ)ᵀ = J') : ∃ Φ : HeckeCharacterZeroLocus.SiegelWeilU.HA (AF F) σ J' ≃ₜ* UA σ J,
      (∀ g, mat (Φ g) * incM F A.1 = incM F A.1 * g.1.val) ∧
      ∀ g, HeckeCharacterZeroLocus.SiegelWeilU.HA.mat (AF F) σ J' g ∈ HeckeCharacterZeroLocus.SiegelWeilU.HFin (AF F) σ J' → Φ g ∈ ratU σ J := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  haveI : IsTopologicalRing (AE F E) := (GlobalTheory.T.tensor_locally_compact_ring F E σ h (AF F)).1
  let a : GL (Fin n) (AE F E) := Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) A
  have ha : inclR (F := F) (AF F) ξ • (a.1ᵀ * incM F J * a.1.map (cA σ : AE F E →+* AE F E))ᵀ = incM F J' := by
    rw [← hA]
    ext i j
    simp only [Matrix.smul_apply, Matrix.transpose_apply, Matrix.mul_apply, incM, Matrix.map_apply, smul_eq_mul, map_mul, map_sum]
    rfl
  have k := fun (g g' : GL (Fin n) (AE F E)) (e : g * a = a * g') =>
    conj_iff (cA σ : AE F E →+* AE F E) ((IsUnit.mk0 ξ hξ).map _) a ha (congrArg Units.val e)
  refine ⟨{ toFun := fun g => ⟨a * g.1 * a⁻¹, (k _ g.1 (inv_mul_cancel_right _ _)).1 g.2⟩
            invFun := fun g => ⟨a⁻¹ * g.1 * a, (k g.1 _ (by group)).2 g.2⟩
            left_inv := fun g => Subtype.ext (show a⁻¹ * (a * g.1 * a⁻¹) * a = g.1 by group)
            right_inv := fun g => Subtype.ext (show a * (a⁻¹ * g.1 * a) * a⁻¹ = g.1 by group)
            map_mul' := fun g g' => Subtype.ext (show a * (g.1 * g'.1) * a⁻¹ = a * g.1 * a⁻¹ * (a * g'.1 * a⁻¹) by group)
            continuous_toFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
            continuous_invFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _ },
    fun g => congrArg Units.val (inv_mul_cancel_right (a * g.1) a), ?_⟩
  rintro g ⟨u, -, hu⟩
  refine Subgroup.mem_subgroupOf.2 ⟨A * u * A⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv]
  exact congrArg (fun z => a * z * a⁻¹) hu

variable {B : Base F E} {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {i₀ i₁ r s : ℕ}

theorem parEx (hB : B.IsGood σ) (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) :
    ∃ (N : Type) (_ : TopologicalSpace N) (_ : SecondCountableTopology N) (_ : MeasurableSpace N) (_ : BorelSpace N)
      (μN : Measure N) (_ : SigmaFinite μN) (_ : IsFiniteMeasureOnCompacts μN) (nn : N → UA σ Y.J)
      (ι : UA σ Y₁.J →* UA σ Y.J) (mm : (AE F E)ˣ →* UA σ Y.J) (χ : (AE F E)ˣ →* ℝ≥0),
      Par μN nn ι mm χ ∧ (∀ a, χ a * absE F E a ^ (n₁ + 1) = 1) ∧ (∀ u, u ∈ unip σ Y H ↔ ∃ p, u = nn p) ∧
      (∀ t g, IsLevi H t g (ι g * mm t)) ∧ (∀ p, ∃ R : N → N, MeasurePreserving R μN μN ∧ ∀ x, nn x * nn p = nn (R x)) ∧
      ∃ C : Set N, IsCompact C ∧ ∀ p, ∃ q, nn q ∈ ratU σ Y.J ∧ ∃ p' ∈ C, nn q * nn p = nn p' := by
  have hσ := hB.cm
  have hss := PositivityTheory.ThKG.Tow.Levi.sig_sig hσ
  obtain rfl := hH.rank
  obtain ⟨ε, hε, -⟩ := exists_eps hY
  obtain ⟨ε', A', hfr⟩ := isFr hB hY hH
  have hd : IsUnit Y₁.J.det := hfr.isUnit_det (det_ne hY).isUnit
  obtain ⟨ξ, hξ, hξs⟩ := PositivityTheory.ThKF.exists_scale hσ ε
  have hsξ : σ ξ ≠ 0 := (map_ne_zero σ).2 hξ
  have h1 : ∀ i j, σ (Y₁.J j i) = ((ε : ℤ) : E) * Y₁.J i j := fun i j => by
    have e : ∀ i j, Y₁.J i j = form σ Y.J (fun k => H.ι k i) (fun k => H.ι k j) := fun i j => by
      rw [← hH.gram, Matrix.mul_assoc]; rfl
    rw [e, e, form_eps hss hε]
  have hJ : HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ (ξ • Y₁.Jᵀ) := by
    refine ⟨fun i j => ?_, ?_⟩
    · simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, map_mul, hξs, h1 j i]
      linear_combination (ξ * Y₁.J j i) * eps_sq (E := E) ε
    · rw [Matrix.det_smul, Matrix.det_transpose]
      exact mul_ne_zero (pow_ne_zero _ hξ) hd.ne_zero
  set y' : Fin (n₁ + 2) → E := (σ ξ)⁻¹ • H.y with hy'
  have hA : ξ • ((fc H.x y' H.ι)ᵀ * Y.J * (fc H.x y' H.ι).map σ)ᵀ = hypJ (ξ • Y₁.Jᵀ) := by
    have col : ∀ j, (fun i => H.ι i j) = H.ι *ᵥ Pi.single j 1 := fun j => by ext i; simp
    have l1 : ∀ (c : E) x y, form σ Y.J (c • x) y = c * form σ Y.J x y := fun c x y => smul_dotProduct _ _ _
    have l2 : ∀ (c : E) x y, form σ Y.J x (c • y) = σ c * form σ Y.J x y := fun c x y => by
      simp only [form, dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have z : ∀ x y, form σ Y.J x y = 0 → form σ Y.J y x = 0 := fun x y h => by
      rw [← hss (form σ Y.J y x), form_eps hss hε, h, mul_zero, map_zero]
    have yx : form σ Y.J H.y H.x = ((ε : ℤ) : E) := by
      rw [← hss (form σ Y.J H.y H.x), form_eps hss hε, hH.xy, mul_one, map_intCast]
    have o1 : ∀ j, form σ Y.J (fun i => H.ι i j) H.x = 0 := fun j => by rw [col]; exact (hH.orth _).1
    have o2 : ∀ j, form σ Y.J (fun i => H.ι i j) y' = 0 := fun j => by rw [col, hy', l2, (hH.orth _).2, mul_zero]
    ext a b
    have ent : (ξ • ((fc H.x y' H.ι)ᵀ * Y.J * (fc H.x y' H.ι).map σ)ᵀ) a b =
        ξ * form σ Y.J (fun i => fc H.x y' H.ι i b) (fun i => fc H.x y' H.ι i a) := by rw [Matrix.mul_assoc]; rfl
    rw [ent]
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun a => ?_) a) a <;>
      refine Fin.cases ?_ (fun b => Fin.cases ?_ (fun b => ?_) b) b
    · exact mul_eq_zero_of_right _ hH.xx
    · show ξ * form σ Y.J y' H.x = 1
      rw [hy', l1, yx, ← mul_assoc, mul_right_comm, mul_comm ξ, ← hξs, mul_inv_cancel₀ hsξ]
    · exact mul_eq_zero_of_right _ (o1 _)
    · show ξ * form σ Y.J H.x y' = 1
      rw [hy', l2, hH.xy, map_inv₀, hss, mul_one, mul_inv_cancel₀ hξ]
    · show ξ * form σ Y.J y' y' = 0
      rw [hy', l1, l2, hH.yy, mul_zero, mul_zero, mul_zero]
    · exact mul_eq_zero_of_right _ (o2 _)
    · exact mul_eq_zero_of_right _ (z _ _ (o1 _))
    · exact mul_eq_zero_of_right _ (z _ _ (o2 _))
    · show _ = ξ * Y₁.J b a
      rw [← hH.gram, Matrix.mul_assoc]; rfl
  have hu : IsUnit (fc H.x y' H.ι) := by
    have e := congrArg Matrix.det hA
    have e2 := Matrix.isUnit_det_of_left_inverse (hyp_inv (Matrix.nonsing_inv_mul _ (Ne.isUnit hJ.2)))
    rw [← e, Matrix.det_smul, Matrix.det_transpose, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at e2
    exact (Matrix.isUnit_iff_isUnit_det _).2
      (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right e2)))
  obtain ⟨Φ, p1, p2⟩ := conjEx hσ hξ hu.unit hA
  obtain ⟨Ψ, q1, -⟩ := conjEx (J := Y₁.J) hσ hξ 1 (J' := ξ • Y₁.Jᵀ) (by simp [Matrix.map_one _ (map_zero σ) (map_one σ)])
  obtain ⟨N, _, _, _, _, μN, _, _, nn, ι, mm, χ, p₀, hP, c1, n0, hval, hdec, hR, C, hC, hcov⟩ := parH hσ hJ
  have one : incM F (1 : Matrix (Fin n₁) (Fin n₁) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have q2 : ∀ g, (Ψ.symm g).1.val = mat g := fun g => by
    have := q1 (Ψ.symm g)
    rw [Units.val_one, one, Matrix.mul_one, Matrix.one_mul, Ψ.apply_symm_apply] at this
    exact this.symm
  have eA : incM F (fc H.x y' H.ι) = fc (incV F H.x) (incV F y') (incM F H.ι) := by
    ext i j
    refine Fin.cases rfl (fun j => Fin.cases rfl (fun j => rfl) j) j
  have ey : incV F H.y = inclR (F := F) (AF F) (σ ξ) • incV F y' := funext fun i => by
    simp only [incV, hy', Pi.smul_apply, smul_eq_mul, ← map_mul, mul_inv_cancel_left₀ hsξ]
  have cols : ∀ p g (t : (AE F E)ˣ), ∃ (b : AE F E) (r w : Fin n₁ → AE F E), (p = p₀ → b = 0 ∧ r = 0 ∧ w = 0) ∧
      mat (Φ (nn p * ι (Ψ.symm g) * mm t)) *ᵥ incV F H.x = t.1 • incV F H.x ∧
      mat (Φ (nn p * ι (Ψ.symm g) * mm t)) *ᵥ incV F y' = b • incV F H.x + cA σ (t⁻¹).1 • incV F y' + incM F H.ι *ᵥ w ∧
      mat (Φ (nn p * ι (Ψ.symm g) * mm t)) * incM F H.ι = Matrix.vecMulVec (incV F H.x) r + incM F H.ι * mat g := fun p g t => by
    obtain ⟨b, r, w, e1, e2⟩ := hval p (Ψ.symm g) t
    have := p1 (nn p * ι (Ψ.symm g) * mm t)
    rw [e1, q2, hu.unit_spec, eA] at this
    exact ⟨b, r, w, e2, fc_cols this⟩
  refine ⟨N, inferInstance, inferInstance, inferInstance, inferInstance, μN, inferInstance, inferInstance, _, _, _, χ,
    hP.transport Φ Ψ, c1, fun u => ⟨fun hu' => ?_, ?_⟩, fun t g => ?_, fun p => ?_, C, hC, fun p => ?_⟩
  · obtain ⟨u1, u2⟩ := mem_unip.1 hu'
    obtain ⟨p, v, e⟩ := hdec (Φ.symm u) 1 (by
      have e1 := congrArg (· *ᵥ Pi.single 0 1) (p1 (Φ.symm u))
      have e2 : incM F hu.unit.1 *ᵥ Pi.single 0 1 = incV F H.x := by
        rw [hu.unit_spec, eA, Matrix.mulVec_single_one]; rfl
      simp only [← Matrix.mulVec_mulVec, Φ.apply_symm_apply] at e1
      rw [e2, u1, ← e2] at e1
      rw [Units.val_one, one_smul]
      exact (Matrix.mulVec_injective_of_isUnit (hu.unit.isUnit.map (inclR (F := F) (AF F)).mapMatrix) e1).symm)
    obtain ⟨b, r, w, -, -, -, e3⟩ := cols p (Ψ v) 1
    rw [Ψ.symm_apply_apply, ← e, Φ.apply_symm_apply] at e3
    have hv : Ψ v = 1 := mat_inj (Matrix.toLin'.injective (LinearMap.ext fun z => by
      obtain ⟨a, ha⟩ := u2 z
      rw [Matrix.mulVec_mulVec, e3, Matrix.add_mulVec, Matrix.vecMulVec_mulVec, ← Matrix.mulVec_mulVec, op_smul_eq_smul] at ha
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, mat_one, Matrix.one_mulVec]
      exact (hfr.ad.indep (t := 0) (t' := 0) (congrArg (· + _) ((add_comm _ _).trans ha))).1))
    refine ⟨p, ?_⟩
    rw [(map_eq_one_iff Ψ Ψ.injective).1 hv, map_one, map_one, mul_one, mul_one] at e
    rw [← e, Φ.apply_symm_apply]
  · rintro ⟨p, rfl⟩
    obtain ⟨b, r, w, -, e1, -, e3⟩ := cols p 1 1
    rw [map_one, map_one, map_one, mul_one, mul_one] at e1 e3
    refine mem_unip.2 ⟨e1.trans (one_smul _ _), fun z => ⟨r ⬝ᵥ z, ?_⟩⟩
    rw [Matrix.mulVec_mulVec, e3, Matrix.add_mulVec, Matrix.vecMulVec_mulVec, mat_one, Matrix.mul_one, op_smul_eq_smul]
    exact add_comm _ _
  · obtain ⟨b, r, w, e0, e1, e2, e3⟩ := cols p₀ g t
    obtain ⟨rfl, rfl, rfl⟩ := e0 rfl
    rw [n0, one_mul, map_mul] at e1 e2 e3
    refine ⟨e1, ?_, e3.trans (add_eq_right.2 (Matrix.ext fun i j => mul_zero (incV F H.x i)))⟩
    rw [ey, Matrix.mulVec_smul, smul_comm]
    exact congrArg _ (e2.trans (by simp))
  · obtain ⟨R, a, b⟩ := hR p
    exact ⟨R, a, fun x => by rw [← map_mul, b]⟩
  · obtain ⟨q, a, p', b, c⟩ := hcov p
    exact ⟨q, p2 _ a, p', b, by rw [← map_mul, c]⟩

end PositivityTheory.ThKCT.Unf

end
