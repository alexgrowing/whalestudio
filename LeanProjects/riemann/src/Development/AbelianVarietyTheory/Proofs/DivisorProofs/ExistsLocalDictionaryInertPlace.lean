import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixTrivialOffInertPlaceUnitaryAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicLatticeAtFinitePlaceIffInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhere
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocDict

open GlobalTheory.InertBigCell

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)}

theorem isConjAt_conjW (σ : E →ₐ[F] E) (hw : Formalism.UG.IsInertAt F E v w) :
    IsConjAt σ (under_eq_of_isInertAt hw) (conjW σ hw) := fun y => by
  show toCompl _ (sigR (Fv F v) σ ((InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm (toCompl _ y))) = _
  congr 2
  exact (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm_apply_apply y

theorem conjW_conjW (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (hw : Formalism.UG.IsInertAt F E v w)
    (x : w.adicCompletion E) : conjW σ hw (conjW σ hw x) = x := by
  obtain ⟨y, rfl⟩ := InertChart.toCompl_surjective (under_eq_of_isInertAt hw) x
  rw [isConjAt_conjW σ hw, isConjAt_conjW σ hw]
  congr 1
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem iotaW_mulVec (hw : Formalism.UG.IsInertAt F E v w) {l m : Type} [Fintype m]
    (M : Matrix l m (w.adicCompletion E)) (y : m → w.adicCompletion E) :
    (fun i => iotaW hw ((M *ᵥ y) i)) = M.map (iotaW hw) *ᵥ fun i => iotaW hw (y i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, iotaW_mul]

theorem map_iotaW_mul (hw : Formalism.UG.IsInertAt F E v w) {l m p : Type} [Fintype m]
    (M : Matrix l m (w.adicCompletion E)) (N : Matrix m p (w.adicCompletion E)) :
    M.map (iotaW hw) * N.map (iotaW hw) = (M * N).map (iotaW hw) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, iotaW_mul]

theorem one_map_iotaW (hw : Formalism.UG.IsInertAt F E v w) (n : ℕ) :
    (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map (iotaW hw) =
      iotaW hw 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem herm_gram {R : Type} [CommRing R] (τ : R →+* R) (hτ : ∀ x, τ (τ x) = x) {n : ℕ}
    (A M : Matrix (Fin n) (Fin n) R) (hM : ∀ i j, τ (M i j) = M j i) (i j : Fin n) :
    τ ((Formalism.UG.cT τ A * M * A) i j) = (Formalism.UG.cT τ A * M * A) j i := by
  simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hτ, hM,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem isUnit_of_val_eq_one {t : Formalism.UG.Ov E w} (ht : Valued.v (t : w.adicCompletion E) = 1) : IsUnit t := by
  have h0 : (t : w.adicCompletion E) ≠ 0 := fun h0 => by rw [h0, map_zero] at ht; exact zero_ne_one ht
  have hm : (t : w.adicCompletion E)⁻¹ ∈ Formalism.UG.Ov E w := by
    show _ ∈ w.adicCompletionIntegers E
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, ht, inv_one]
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hm⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

end GlobalTheory.InertLocDict

namespace GlobalTheory.InertLocDict

open GlobalTheory.InertBigCell

theorem exists_local_dictionary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∃ (O : Type) (_ : CommRing O) (c : O →+* O) (ι : O →ₙ+* AE F E) (P Q : Matrix (Fin n) (Fin n) (AE F E))
      (JL : Matrix (Fin n) (Fin n) O),
      IsLocalRing O ∧ (∀ x, c (c x) = x) ∧ IsUnit (2 : O) ∧ (∃ x : O, IsUnit (c x - x)) ∧
      Function.Injective ι ∧ At (evFin F v) (ι 1) ∧ (∀ y : AE F E, At (evFin F v) y → ι 1 * y = y) ∧
      (∀ x, cA σ (ι x) = ι (c x)) ∧
      P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧ Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧
      ι 1 • P = P ∧ ι 1 • Q = Q ∧
      (∀ i j, c (JL j i) = JL i j) ∧ IsUnit JL.det ∧ Pᵀ * incM F X.J * P.map (cA σ) = JL.map ι ∧
      ∀ z : Fin n → AE F E, z ∈ GlobalTheory.InertSph.latAt X v ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i) := by
  intro F E _ _ _ _ _ σ B n r s X hB hX v w hw
  have h := under_eq_of_isInertAt hw
  have hc : IsConjAt σ h (conjW σ hw) := isConjAt_conjW σ hw
  have hσ : ∀ x, σ (σ x) = x := InertChart.conj_conj hB.cm
  haveI : IsLocalRing (Formalism.UG.Ov E w) := inferInstanceAs (IsLocalRing (w.adicCompletionIntegers E))
  let c : Formalism.UG.Ov E w →+* Formalism.UG.Ov E w :=
    ((conjW σ hw).comp (Formalism.UG.Ov E w).subtype).codRestrict (Formalism.UG.Ov E w)
      (fun x => InertChart.conj_mem hw hc x.2)
  let ι : Formalism.UG.Ov E w →ₙ+* AE F E :=
    { toFun := fun x => iotaW hw (x : w.adicCompletion E)
      map_mul' := fun x y => iotaW_mul hw _ _
      map_zero' := map_zero _
      map_add' := fun x y => map_add _ _ _ }
  have hι : ∀ x, ι x = iotaW hw (x : w.adicCompletion E) := fun _ => rfl
  have hι1 : ι 1 = iotaW hw 1 := rfl
  have hcv : ∀ x, ((c x : Formalism.UG.Ov E w) : w.adicCompletion E) = conjW σ hw x := fun _ => rfl
  obtain ⟨a, ha⟩ := InertChart.exists_isFrameAt (L := X.L) hw hX.lat.fg hX.lat.span_eq_top
  have hJ : (X.Jᵀ).det ≠ 0 := by
    rw [Matrix.det_transpose]; exact GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm σ B hX
  obtain ⟨Bm, ⟨k, hk⟩, eB⟩ := InertChart.exists_gram hw hc hJ
    (GlobalTheory.HermSelfDualLoc.isSelfDualAt_transpose F E σ B n X r s hB hX v) ha
  have hkij : ∀ i j, ((k.1 i j : Formalism.UG.Ov E w) : w.adicCompletion E) = Bm.1 i j := fun i j => by
    rw [← hk]; rfl
  have hBt : Bm.1ᵀ = a.1ᵀ * X.J.map (algebraMap E (w.adicCompletion E)) * a.1.map (conjW σ hw) := by
    rw [eB, Matrix.transpose_mul, Matrix.transpose_mul, Formalism.UG.cT, Matrix.transpose_transpose, Matrix.transpose_map,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  refine ⟨Formalism.UG.Ov E w, inferInstance, c, ι, a.1.map (iotaW hw), (a⁻¹).1.map (iotaW hw), k.1ᵀ, inferInstance,
    fun x => Subtype.ext (conjW_conjW σ hσ hw x), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have h2 : (2 : w.adicCompletion E) ≠ 0 := by
      rw [← map_ofNat (algebraMap E (w.adicCompletion E)) 2]
      exact (map_ne_zero _).2 two_ne_zero
    have hm : (2 : w.adicCompletion E)⁻¹ ∈ Formalism.UG.Ov E w := by
      have := complMap_mem h (GlobalTheory.InertLocField.half_mem v (hB.inert v w hw).1)
      rwa [complMap_algebraMap, map_inv₀, map_inv₀, map_ofNat, map_ofNat] at this
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hm⟩, Subtype.ext (mul_inv_cancel₀ h2)⟩
  ·
    obtain ⟨x, hx⟩ := InertChart.exists_conj_sub_unit hB.cm hw
    have hval : ∀ a : E, Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a := fun a =>
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    have hxm : algebraMap E (w.adicCompletion E) (x : E) ∈ Formalism.UG.Ov E w := by
      show _ ∈ w.adicCompletionIntegers E
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval]; exact w.valuation_le_one x
    refine ⟨⟨_, hxm⟩, ?_⟩
    refine isUnit_of_val_eq_one ?_
    show Valued.v (conjW σ hw (algebraMap E _ (x : E)) - algebraMap E _ (x : E)) = 1
    rw [InertChart.conj_algebraMap hc, ← map_sub, hval, hx]
  · exact fun x y hxy => Subtype.ext (iotaW_injective hw hxy)
  · rw [hι1, iotaW_apply]; exact GlobalTheory.InertLocField.at_liftT v _
  · intro y hy
    have h1 := hy _ (GlobalTheory.InertLocField.evFin_one_sub v)
    rw [sub_smul, one_smul, sub_eq_zero] at h1
    rw [hι1, iotaW_one, ← Algebra.smul_def]
    exact h1.symm
  · intro x
    rw [hι, hι, hcv, iotaW_conjW]
  · rw [map_iotaW_mul, Units.mul_inv, one_map_iotaW, hι1]
  · rw [map_iotaW_mul, Units.inv_mul, one_map_iotaW, hι1]
  · ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, hι1, ← iotaW_mul, one_mul]
  · ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, hι1, ← iotaW_mul, one_mul]
  · intro i j
    apply Subtype.ext
    rw [hcv, Matrix.transpose_apply, Matrix.transpose_apply, hkij, hkij, eB]
    refine herm_gram (conjW σ hw) (conjW_conjW σ hσ hw) a.1 (X.Jᵀ.map (algebraMap E (w.adicCompletion E)))
      (fun p q => ?_) i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, InertChart.conj_algebraMap hc, hX.herm]
  · rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).1 k.isUnit
  · have e1 : (a.1.map (iotaW hw))ᵀ = (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • (0 : Matrix (Fin n) (Fin n) (AE F E)) +
        a.1ᵀ.map (iotaW hw) := by
      rw [smul_zero, zero_add, Matrix.transpose_map]
    have e2 : (a.1.map (iotaW hw)).map (cA σ) = (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • (0 : Matrix (Fin n) (Fin n) (AE F E)) +
        (a.1.map (conjW σ hw)).map (iotaW hw) := by
      rw [smul_zero, zero_add]
      ext i j
      simp only [Matrix.map_apply, iotaW_conjW]
    rw [e1, e2, incM_split hw X.J,
      idem_split_mul _ (iotaW hw) (one_sub_idem v) (one_sub_mul_iotaW hw) (iotaW_mul hw),
      idem_split_mul _ (iotaW hw) (one_sub_idem v) (one_sub_mul_iotaW hw) (iotaW_mul hw),
      Matrix.zero_mul, Matrix.zero_mul, smul_zero, zero_add, ← hBt]
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, hι, hkij]
  · intro z
    rw [GlobalTheory.InertSphLat.mem_latAt_iff hw X z]
    constructor
    · rintro ⟨u, hu, rfl⟩
      have e : a.1 *ᵥ ((a⁻¹).1 *ᵥ u) = u := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      have hint := (ha ((a⁻¹).1 *ᵥ u)).2 (by rw [e]; exact hu)
      refine ⟨fun i => ⟨_, hint i⟩, ?_⟩
      show (fun i => iotaW hw (u i)) = a.1.map (iotaW hw) *ᵥ fun i => iotaW hw (((a⁻¹).1 *ᵥ u) i)
      rw [← iotaW_mulVec, e]
    · rintro ⟨b, rfl⟩
      refine ⟨a.1 *ᵥ fun i => (b i : w.adicCompletion E), (ha _).1 fun i => (b i).2, ?_⟩
      rw [iotaW_mulVec]
      rfl

end GlobalTheory.InertLocDict
