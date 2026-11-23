import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualTupleIdealsCastAdd

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

section FormAlg

variable {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
variable {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) in
theorem _root_.GlobalTheory.SnMass.VolN.form_smul_left' (c : E) (x y : Fin n → E) :
    _root_.GlobalTheory.SgAlg.form σ J (c • x) y = c * _root_.GlobalTheory.SgAlg.form σ J x y := by
  unfold _root_.GlobalTheory.SgAlg.form
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
variable {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) in
theorem _root_.GlobalTheory.SnMass.VolN.form_smul_right' (c : E) (x y : Fin n → E) :
    _root_.GlobalTheory.SgAlg.form σ J x (c • y) = σ c * _root_.GlobalTheory.SgAlg.form σ J x y := by
  simp only [_root_.GlobalTheory.SgAlg.form, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul,
    Finset.mul_sum, mul_assoc]

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
variable {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) in
theorem _root_.GlobalTheory.SnMass.VolN.form_sub_left' (x x' y : Fin n → E) :
    _root_.GlobalTheory.SgAlg.form σ J (x - x') y =
      _root_.GlobalTheory.SgAlg.form σ J x y - _root_.GlobalTheory.SgAlg.form σ J x' y := by
  unfold _root_.GlobalTheory.SgAlg.form
  rw [Matrix.mulVec_sub, dotProduct_sub]

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
variable {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) in
theorem _root_.GlobalTheory.SnMass.VolN.form_sum_left' {ι : Type} (S : Finset ι) (g : ι → Fin n → E)
    (y : Fin n → E) :
    _root_.GlobalTheory.SgAlg.form σ J (∑ c ∈ S, g c) y = ∑ c ∈ S, _root_.GlobalTheory.SgAlg.form σ J (g c) y := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [_root_.GlobalTheory.SgAlg.form]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    simp [_root_.GlobalTheory.SgAlg.form, Matrix.mulVec_add, dotProduct_add]

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
variable {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) in
theorem _root_.GlobalTheory.SnMass.VolN.form_conj (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j)
    (x y : Fin n → E) :
    σ (_root_.GlobalTheory.SgAlg.form σ J x y) = _root_.GlobalTheory.SgAlg.form σ J y x := by
  simp only [_root_.GlobalTheory.SgAlg.form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
variable {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) in
theorem _root_.GlobalTheory.SnMass.VolN.pairM_apply' {a b : Type} [Fintype a] [Fintype b]
    (P' : Matrix (Fin n) b E) (P : Matrix (Fin n) a E)
    (i : a) (j : b) :
    _root_.GlobalTheory.SgAlg.pairM σ J P' P i j =
      _root_.GlobalTheory.SgAlg.form σ J (fun l => P' l j) (fun l => P l i) := by
  simp only [_root_.GlobalTheory.SgAlg.pairM, _root_.GlobalTheory.SgAlg.cT, _root_.GlobalTheory.SgAlg.form,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, dotProduct, Matrix.mulVec,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

def projF {r : ℕ} (e g : Fin r → Fin n → E) (u : Fin n → E) : Fin n → E :=
  u - ∑ c, form σ J u (g c) • e c - ∑ c, form σ J u (e c) • g c

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
variable {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) in
theorem _root_.GlobalTheory.SnMass.VolN.projF_orth {r : ℕ} (e g : Fin r → Fin n → E)
    (hee : ∀ c d, _root_.GlobalTheory.SgAlg.form σ J (e c) (e d) = 0)
    (hgg : ∀ c d, _root_.GlobalTheory.SgAlg.form σ J (g c) (g d) = 0)
    (hge : ∀ c d, _root_.GlobalTheory.SgAlg.form σ J (g c) (e d) = if c = d then 1 else 0)
    (heg : ∀ c d, _root_.GlobalTheory.SgAlg.form σ J (e c) (g d) = if c = d then 1 else 0)
    (u : Fin n → E) (b : Fin r) :
    _root_.GlobalTheory.SgAlg.form σ J (_root_.GlobalTheory.SnMass.VolN.projF σ J e g u) (e b) = 0 ∧
      _root_.GlobalTheory.SgAlg.form σ J (_root_.GlobalTheory.SnMass.VolN.projF σ J e g u) (g b) = 0 := by
  unfold _root_.GlobalTheory.SnMass.VolN.projF
  constructor <;>
    simp [_root_.GlobalTheory.SnMass.VolN.form_sub_left', _root_.GlobalTheory.SnMass.VolN.form_sum_left',
      _root_.GlobalTheory.SnMass.VolN.form_smul_left', hee, hgg, hge, heg]

end FormAlg

section Lat

variable {E : Type} [Field E] [NumberField E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) in

theorem _root_.GlobalTheory.SnMass.VolN.form_mem_inv (hσ : ∀ x, σ (σ x) = x)
    {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hΛ : ∀ v ∈ Λ, ∀ w ∈ Λ, _root_.GlobalTheory.SgAlg.form σ J v w ∈ (algebraMap (𝓞 E) E).range)
    {I : FractionalIdeal (𝓞 E)⁰ E} (h0 : I ≠ 0) (hs : _root_.GlobalTheory.SnMass.FrameDual.Stab σ I)
    {g v : Fin n → E}
    (hg : ∀ x ∈ I, x • g ∈ Λ) (hv : v ∈ Λ) : _root_.GlobalTheory.SgAlg.form σ J v g ∈ I⁻¹ := by
  rw [FractionalIdeal.mem_inv_iff h0]
  intro y hy
  have h1 := hΛ v hv _ (hg _ (hs y hy))
  rw [_root_.GlobalTheory.SnMass.VolN.form_smul_right', hσ, RingHom.mem_range] at h1
  rw [FractionalIdeal.mem_one_iff, mul_comm]
  exact h1

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) in
theorem _root_.GlobalTheory.SnMass.VolN.projF_mem (hσ : ∀ x, σ (σ x) = x)
    {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hΛ : ∀ v ∈ Λ, ∀ w ∈ Λ, _root_.GlobalTheory.SgAlg.form σ J v w ∈ (algebraMap (𝓞 E) E).range) {r : ℕ}
    (𝔞 : Fin r → FractionalIdeal (𝓞 E)⁰ E) (h0 : ∀ c, 𝔞 c ≠ 0)
    (hs : ∀ c, _root_.GlobalTheory.SnMass.FrameDual.Stab σ (𝔞 c))
    (e g : Fin r → Fin n → E) (he : ∀ c, ∀ x ∈ 𝔞 c, x • e c ∈ Λ)
    (hg : ∀ c, ∀ x ∈ (𝔞 c)⁻¹, x • g c ∈ Λ)
    {v : Fin n → E} (hv : v ∈ Λ) : _root_.GlobalTheory.SnMass.VolN.projF σ J e g v ∈ Λ := by
  unfold _root_.GlobalTheory.SnMass.VolN.projF
  refine Λ.sub_mem (Λ.sub_mem hv (Λ.sum_mem fun c _ => ?_)) (Λ.sum_mem fun c _ => ?_)
  · have h := _root_.GlobalTheory.SnMass.VolN.form_mem_inv σ J hσ hΛ (inv_ne_zero (h0 c))
      (_root_.GlobalTheory.SnMass.FrameDual.Stab.inv hσ (hs c) (h0 c)) (hg c) hv
    rw [inv_inv] at h
    exact he c _ h
  · exact hg c _ (_root_.GlobalTheory.SnMass.VolN.form_mem_inv σ J hσ hΛ (h0 c) (hs c) (he c) hv)

end Lat

section Cx

variable {E : Type} [Field E] {n : ℕ}

def mv (φ : E →+* ℂ) (x : Fin n → E) : Fin n → ℂ := fun i => φ (x i)

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
variable {E : Type} [Field E] {n : ℕ} in
theorem _root_.GlobalTheory.SnMass.VolN.herm_model {H B M : Matrix (Fin n) (Fin n) ℂ} (h : Bᴴ * H * B = M)
    (x y : Fin n → ℂ) :
    _root_.Formalism.QuantumDeterminants.herm H (B *ᵥ x) (B *ᵥ y) = _root_.Formalism.QuantumDeterminants.herm M x y := by
  unfold _root_.Formalism.QuantumDeterminants.herm
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, h]

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
variable {E : Type} [Field E] {n : ℕ} in
theorem _root_.GlobalTheory.SnMass.VolN.herm_smul_right' (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (x y : Fin n → ℂ) :
    _root_.Formalism.QuantumDeterminants.herm H x (c • y) = star c * _root_.Formalism.QuantumDeterminants.herm H x y := by
  simp [_root_.Formalism.QuantumDeterminants.herm, star_smul, smul_dotProduct]

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
variable {E : Type} [Field E] {n : ℕ} in
theorem _root_.GlobalTheory.SnMass.VolN.herm_bvec_right (H : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ)
    (i : Fin n) :
    _root_.Formalism.QuantumDeterminants.herm H x (_root_.Formalism.QuantumDeterminants.bvec i) = (H *ᵥ x) i := by
  simp [_root_.Formalism.QuantumDeterminants.herm, _root_.Formalism.QuantumDeterminants.bvec]

end Cx

section Model

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
private theorem Hpk_esI_applyFlagMeasures (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    _root_.Formalism.QuantumDeterminants.Hpk k r (_root_.Formalism.QuantumDeterminants.esI k r a) j = if j = _root_.Formalism.QuantumDeterminants.eI k r a then 1 else 0 := by
  simp only [_root_.Formalism.QuantumDeterminants.Hpk, _root_.Formalism.QuantumDeterminants.esI, _root_.Formalism.QuantumDeterminants.eI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
theorem _root_.GlobalTheory.SnMass.VolN.mulVec_esI (k r : ℕ) (a : Fin r)
    (x : Fin (2 * r + k + 1) → ℂ) :
    x (_root_.Formalism.QuantumDeterminants.eI k r a) = (_root_.Formalism.QuantumDeterminants.Hpk k r *ᵥ x) (_root_.Formalism.QuantumDeterminants.esI k r a) := by
  simp only [Matrix.mulVec, dotProduct, Hpk_esI_applyFlagMeasures, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Model

section Main

variable {E : Type} [Field E] [NumberField E]

end Main

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in

theorem _root_.GlobalTheory.SnMass.VolN.row_mem_homLat : ∀ (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ)
    (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E)
    (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ),
    _root_.GlobalTheory.SnMass.VolN.IsVolData σ J Λ P f T A s →
      ∀ γ ∈ _root_.GlobalTheory.SnMass.VolN.GN (σ : E →+* E) J Λ P, ∀ a : Fin r,
        (fun w (l : Fin (k + 1)) => _root_.GlobalTheory.SnMass.VolN.gM A γ w (_root_.Formalism.QuantumDeterminants.eI k r a) (_root_.Formalism.QuantumDeterminants.wI k r l)) ∈
          _root_.GlobalTheory.SnMass.VolN.homLat (σ : E →+* E) J Λ P f A (_root_.GlobalTheory.SgGlob.dInv E (r - a.val)) (s a) := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV γ hγ a
  obtain ⟨⟨-, -, -, hτ⟩, -, ⟨hJh, hJdet⟩, hSD, ⟨-, hPP⟩, ⟨hfP, hff⟩, hSpan, hModel, hs, hAd⟩ := hV
  obtain ⟨⟨hγiso, -, -⟩, hγΛ⟩ := hγ
  have hσ : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := by
    intro x
    apply (Classical.arbitrary (InfinitePlace E)).embedding.injective
    simp only [AlgHom.coe_toRingHom, hτ, star_star]
  have hee : ∀ c d, _root_.GlobalTheory.SgAlg.form (σ : E →+* E) J (fun i => P i (Fin.castSucc c))
      (fun i => P i (Fin.castSucc d)) = 0 := by
    intro c d
    have h := congrFun (congrFun hPP d.castSucc) c.castSucc
    rw [_root_.GlobalTheory.SnMass.VolN.pairM_apply'] at h
    refine h.trans ?_
    simp [_root_.GlobalTheory.SgAlg.TF, Matrix.diagonal_apply, Fin.castSucc_ne_last]
  have hgg : ∀ c d, _root_.GlobalTheory.SgAlg.form (σ : E →+* E) J (fun i => f i c) (fun i => f i d) = 0 := by
    intro c d
    have h := congrFun (congrFun hff d) c
    rw [_root_.GlobalTheory.SnMass.VolN.pairM_apply'] at h
    exact h
  have hge : ∀ c d, _root_.GlobalTheory.SgAlg.form (σ : E →+* E) J (fun i => f i c)
      (fun i => P i (Fin.castSucc d)) = if c = d then 1 else 0 := by
    intro c d
    have h := congrFun (congrFun hfP d.castSucc) c
    rw [_root_.GlobalTheory.SnMass.VolN.pairM_apply', Matrix.of_apply] at h
    simp only [Fin.castSucc_inj] at h
    refine h.trans ?_
    by_cases hcd : c = d
    · subst hcd; simp
    · simp [hcd, Ne.symm hcd]
  have heg : ∀ c d, _root_.GlobalTheory.SgAlg.form (σ : E →+* E) J (fun i => P i (Fin.castSucc c))
      (fun i => f i d) = if c = d then 1 else 0 := by
    intro c d
    rw [← _root_.GlobalTheory.SnMass.VolN.form_conj (σ : E →+* E) J hσ hJh, hge]
    by_cases hcd : c = d
    · subst hcd; simp
    · simp [hcd, Ne.symm hcd]
  have hdet : IsUnit γ.det := by
    refine isUnit_iff_ne_zero.mpr fun h0 => hJdet ?_
    have h := congrArg Matrix.det hγiso
    rwa [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, eq_comm] at h
  have hinvΛ : ∀ v ∈ Λ, γ⁻¹ *ᵥ v ∈ Λ := by
    intro v hv
    unfold _root_.GlobalTheory.SgGlob.latMap at hγΛ
    rw [← hγΛ] at hv
    obtain ⟨u', hu', rfl⟩ := hv
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul γ hdet] using hu'
  have hΛ : ∀ v ∈ Λ, ∀ w ∈ Λ, _root_.GlobalTheory.SgAlg.form (σ : E →+* E) J v w ∈
      (algebraMap (𝓞 E) E).range := fun v hv => (hSD.2 v).1 hv
  have he : ∀ c, ∀ x ∈ _root_.GlobalTheory.SgGlob.dInv E (r - c.val),
      x • (fun i => P i (Fin.castSucc c)) ∈ Λ := by
    intro c x hx
    apply hSpan
    unfold _root_.GlobalTheory.SnMass.tupLat
    refine Submodule.subset_span ⟨Fin.castAdd r c.castSucc, x, by rwa [_root_.GlobalTheory.SnMass.FrameDual.frameDualTupleIdeals_castAdd], ?_⟩
    ext i
    simp [_root_.GlobalTheory.SnMass.sideM]
  have hg : ∀ c, ∀ x ∈ (_root_.GlobalTheory.SgGlob.dInv E (r - c.val))⁻¹, x • (fun i => f i c) ∈ Λ := by
    intro c x hx
    apply hSpan
    unfold _root_.GlobalTheory.SnMass.tupLat
    refine Submodule.subset_span ⟨Fin.natAdd (r + 1) c, x, by rwa [_root_.GlobalTheory.SnMass.FrameDual.frameDualTupleIdeals_natAdd], ?_⟩
    ext i
    simp [_root_.GlobalTheory.SnMass.sideM]
  set u : Fin (2 * r + k + 1) → E := γ⁻¹ *ᵥ (fun i => f i a) with hu
  have hγu : γ *ᵥ u = fun i => f i a := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv γ hdet, Matrix.one_mulVec]
  set t : Fin (2 * r + k + 1) → E := _root_.GlobalTheory.SnMass.VolN.projF (σ : E →+* E) J
    (fun c i => P i (Fin.castSucc c)) (fun c i => f i c) u with ht
  unfold _root_.GlobalTheory.SnMass.VolN.homLat _root_.GlobalTheory.SnMass.VolN.midLat
  simp only [Set.mem_setOf_eq]
  refine ⟨t, ⟨fun b => _root_.GlobalTheory.SnMass.VolN.projF_orth _ J _ _ hee hgg hge heg u b,
    fun c hc => ?_⟩, fun w l => ?_⟩
  · have hsm : c • t = _root_.GlobalTheory.SnMass.VolN.projF (σ : E →+* E) J
        (fun c i => P i (Fin.castSucc c)) (fun c i => f i c) (c • u) := by
      simp only [ht, _root_.GlobalTheory.SnMass.VolN.projF, smul_sub, Finset.smul_sum, smul_smul,
        _root_.GlobalTheory.SnMass.VolN.form_smul_left']
    rw [hsm]
    refine _root_.GlobalTheory.SnMass.VolN.projF_mem _ J hσ hΛ
      (fun c => _root_.GlobalTheory.SgGlob.dInv E (r - c.val)) (fun c => _root_.GlobalTheory.SnMass.FrameDual.dInv_ne_zero _)
      (fun c => _root_.GlobalTheory.SnMass.FrameDual.stab_dInv hσ _) _ _ he hg ?_
    rw [hu, ← Matrix.mulVec_smul]
    exact hinvΛ _ (hg a c hc)
  · set τ := w.embedding with hτdef
    have hAJ : (A w)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * A w = J.map τ := hModel w
    have hAdet : IsUnit (A w).det := by
      refine isUnit_iff_ne_zero.mpr fun h0 => hJdet ?_
      have h := congrArg Matrix.det hAJ
      rw [Matrix.det_mul, h0, mul_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_comm,
        map_eq_zero] at h
      exact h
    have hγτ : (γ.map τ)ᴴ * J.map τ * γ.map τ = J.map τ := by
      have hc : (γ.map τ)ᴴ = (_root_.GlobalTheory.SgAlg.cT (σ : E →+* E) γ).map τ := by
        ext i j
        simp [_root_.GlobalTheory.SgAlg.cT, Matrix.conjTranspose_apply, hτ]
      rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, hγiso]
    have hτu : γ.map τ *ᵥ (fun i => τ (u i)) = fun i => τ (f i a) := by
      ext i
      have h := RingHom.map_mulVec τ γ u i
      rw [hγu] at h
      exact h.symm
    have hsa : ((s a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hs a).ne'
    have h1 := fun c => (hAd w c).1
    have h2 := fun c => (hAd w c).2
    simp only [← hτdef] at h1 h2
    have hz1 : ∀ c, _root_.Formalism.QuantumDeterminants.Hpk k r (_root_.Formalism.QuantumDeterminants.eI k r c) (_root_.Formalism.QuantumDeterminants.wI k r l) = 0 := by
      intro c
      simp only [_root_.Formalism.QuantumDeterminants.Hpk, _root_.Formalism.QuantumDeterminants.eI, _root_.Formalism.QuantumDeterminants.wI, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    have hz2 : ∀ c, _root_.Formalism.QuantumDeterminants.Hpk k r (_root_.Formalism.QuantumDeterminants.esI k r c) (_root_.Formalism.QuantumDeterminants.wI k r l) = 0 := by
      intro c
      simp only [_root_.Formalism.QuantumDeterminants.Hpk, _root_.Formalism.QuantumDeterminants.esI, _root_.Formalism.QuantumDeterminants.wI, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    have hvec : (fun i => τ (t i)) = (fun i => τ (u i))
        - ∑ c, τ (_root_.GlobalTheory.SgAlg.form (σ : E →+* E) J u (fun i => f i c)) •
            (fun i => τ (P i (Fin.castSucc c)))
        - ∑ c, τ (_root_.GlobalTheory.SgAlg.form (σ : E →+* E) J u (fun i => P i (Fin.castSucc c))) •
            (fun i => τ (f i c)) := by
      ext i
      simp [ht, _root_.GlobalTheory.SnMass.VolN.projF, Finset.sum_apply, map_sum]
    have hproj : _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.wI k r l)) (A w *ᵥ fun i => τ (u i)) =
        _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.wI k r l)) (A w *ᵥ fun i => τ (t i)) := by
      rw [hvec, Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_sum, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, h1, h2]
      simp [_root_.Formalism.QuantumDeterminants.herm, _root_.Formalism.QuantumDeterminants.bvec, star_sub, sub_dotProduct, star_sum, sum_dotProduct, star_smul,
        smul_dotProduct, Matrix.mulVec_single_one, hz1, hz2]
    calc _root_.GlobalTheory.SnMass.VolN.gM A γ w (_root_.Formalism.QuantumDeterminants.eI k r a) (_root_.Formalism.QuantumDeterminants.wI k r l)
        = ((A w * γ.map τ * (A w)⁻¹) *ᵥ _root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.wI k r l)) (_root_.Formalism.QuantumDeterminants.eI k r a) := by
          simp [_root_.GlobalTheory.SnMass.VolN.gM, _root_.Formalism.QuantumDeterminants.bvec, Matrix.mulVec_single_one, τ]
      _ = _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) ((A w * γ.map τ * (A w)⁻¹) *ᵥ _root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.wI k r l))
            (_root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.esI k r a)) := by
          exact (_root_.GlobalTheory.SnMass.VolN.mulVec_esI k r a _).trans
            (_root_.GlobalTheory.SnMass.VolN.herm_bvec_right _ _ _).symm
      _ = _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (A w *ᵥ (γ.map τ *ᵥ ((A w)⁻¹ *ᵥ _root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.wI k r l))))
            (((s a : ℝ) : ℂ) • (A w *ᵥ fun i => τ (f i a))) := by
          rw [h2, smul_smul, mul_inv_cancel₀ hsa, one_smul, Matrix.mulVec_mulVec,
            Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = ((s a : ℝ) : ℂ) * _root_.Formalism.QuantumDeterminants.herm (J.map τ) (γ.map τ *ᵥ ((A w)⁻¹ *ᵥ _root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.wI k r l)))
            (fun i => τ (f i a)) := by
          rw [_root_.GlobalTheory.SnMass.VolN.herm_smul_right', _root_.GlobalTheory.SnMass.VolN.herm_model hAJ,
            Complex.star_def, Complex.conj_ofReal]
      _ = ((s a : ℝ) : ℂ) * _root_.Formalism.QuantumDeterminants.herm (J.map τ) ((A w)⁻¹ *ᵥ _root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.wI k r l))
            (fun i => τ (u i)) := by
          rw [← hτu, _root_.GlobalTheory.SnMass.VolN.herm_model hγτ]
      _ = ((s a : ℝ) : ℂ) * _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.wI k r l))
            (A w *ᵥ fun i => τ (u i)) := by
          rw [← hAJ, ← _root_.GlobalTheory.SnMass.VolN.herm_model (H := _root_.Formalism.QuantumDeterminants.Hpk k r) (B := A w) rfl,
            Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hAdet, Matrix.one_mulVec]
      _ = ((s a : ℝ) : ℂ) * _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.wI k r l))
            (A w *ᵥ fun i => τ (t i)) := by
          rw [hproj]

end GlobalTheory.SnMass.VolN
