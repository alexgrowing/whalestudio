import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvIInfScaleMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFrameModelEvaluation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementUnitaryMatrixIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.WittSupport

open GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in
private theorem form_eq (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (u v : Fin n → E) :
    form σ J u v = ∑ k, ∑ l, u k * J k l * σ (v l) := by
  simp only [form, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

omit [NumberField F] [NumberField E] in
private theorem form_swap {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (u v : Fin n → E) : form σ J u v = σ (form σ J v u) := by
  simp only [form_eq, map_sum, map_mul, hσ, hJ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [NumberField F] [NumberField E] in
private theorem witt_entry {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n q : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (U V : Matrix (Fin n) (Fin q) E) (i j : Fin q) :
    form σ J (fun k => U k i) (fun k => V k j) = σ ((Formalism.UG.cT (σ : E →+* E) U * ((1 : E) • J.map σ) * V) i j) := by
  simp only [form_eq, one_smul, Formalism.UG.cT, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, RingHom.coe_coe,
    Finset.sum_mul, map_sum, map_mul, hσ]
  exact Finset.sum_comm

omit [NumberField F] [NumberField E] in
private theorem isFrameU_of_isWittFrame {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n q : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {U V : Matrix (Fin n) (Fin q) E} (h : GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • J.map σ) U V) :
    IsFrameU σ J (fun i k => U k i) (fun i k => V k i) := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · rw [witt_entry hσ, h.xx]; simp
  · rw [witt_entry hσ, h.yy]; simp
  · rw [witt_entry hσ, h.xy, Matrix.one_apply]; split_ifs <;> simp

private theorem mat_eq_of_isTorusU {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n q : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) {x y : Fin q → Fin n → E} (hF : IsFrameU σ J x y) {t : Fin q → ℝ} {a a' : UA σ J}
    (ha : IsTorusU x y t a) (ha' : IsTorusU x y t a') : mat a = mat a' := by
  have hD : ∀ v, (mat a - mat a') *ᵥ v = (mat a - 1) *ᵥ v - (mat a' - 1) *ᵥ v := fun v => by
    rw [← Matrix.sub_mulVec, sub_sub_sub_cancel_right]
  have hyx : ∀ i j, form σ J (y i) (x j) = if i = j then 1 else 0 := fun i j => by
    rw [form_swap hσ hJ, hF.2.2]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hall : ∀ z : Fin n → E, (mat a - mat a') *ᵥ incV F z = 0 := fun z => by
    set z0 : Fin n → E := z - ∑ i, form σ J z (y i) • x i - ∑ i, form σ J z (x i) • y i with hz0
    have hf : ∀ w, form σ J z0 w = form σ J z w - ∑ i, form σ J z (y i) * form σ J (x i) w -
        ∑ i, form σ J z (x i) * form σ J (y i) w := fun w => by
      rw [hz0]
      simp only [form.eq_1 σ J _ w, sub_dotProduct, sum_dotProduct, smul_dotProduct, smul_eq_mul]
    have hx0 : ∀ j, form σ J z0 (x j) = 0 := fun j => by simp [hf, hF.1, hyx]
    have hy0 : ∀ j, form σ J z0 (y j) = 0 := fun j => by simp [hf, hF.2.1, hF.2.2]
    have hdec : incV F z = incV F z0 + ∑ i, inclR (F := F) (AF F) (form σ J z (y i)) • incV F (x i) +
        ∑ i, inclR (F := F) (AF F) (form σ J z (x i)) • incV F (y i) := by
      funext k
      simp only [hz0, incV, Pi.add_apply, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_sum,
        map_mul]
      ring
    rw [hdec]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul]
    simp only [hD, ha.1, ha'.1, ha.2.1, ha'.2.1, ha.2.2 z0 hx0 hy0, ha'.2.2 z0 hx0 hy0, sub_self, smul_zero,
      Finset.sum_const_zero, add_zero]
  refine sub_eq_zero.1 (Matrix.ext fun i j => ?_)
  have h1 : incV F (Pi.single j (1 : E) : Fin n → E) = Pi.single j 1 := by
    funext k
    by_cases h : k = j
    · subst h; simp [incV]
    · simp [incV, h]
  have := congrFun (hall (Pi.single j 1)) i
  rw [h1, Matrix.mulVec_single_one] at this
  exact this

private theorem tAd_eq (s : ℝ) : tAd F s = GlobalTheory.TorusTheta.infScale F s := by
  unfold tAd realAd GlobalTheory.TorusTheta.infScale
  refine Prod.ext ?_ ?_
  · show 1 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ (s - 1)) = _
    rw [map_sub, map_sub, map_one, map_one]
    exact add_sub_cancel _ _
  · exact add_zero _

private theorem infScale_one : GlobalTheory.TorusTheta.infScale F 1 = 1 := by
  unfold GlobalTheory.TorusTheta.infScale
  rw [map_one, map_one]
  rfl

private theorem blkScale_eq {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : κ → Option (Fin q)) (s : Fin q → ℝ)
    (z : κ → AF F) (j : κ) :
    blkScale (fun i => Finset.univ.filter (fun j => blk j = some i)) s z j =
      GlobalTheory.TorusTheta.infScale F ((blk j).elim 1 s) * z j := by
  unfold blkScale
  congr 1
  rcases h : blk j with _ | i₀
  · simp [h, infScale_one]
  · simp [h, tAd_eq]

end GlobalTheory.WittSupport

theorem _root_.GlobalTheory.T.darboux_witt_frame_pair : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
    ∀ (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d))
      (blk : Fin n × Fin d → Option (Fin r₀)),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      (∀ i : Fin r₀, (Finset.univ.filter (fun j => blk j = some i)).card = 2 * d) →
      (∀ t : Fin r₀ → ℝ, (∀ i, 0 < t i) → ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a →
        ∀ a' : UA σ X.J, (a' : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) a →
        ∀ z : Matrix (Fin n) (Fin d) (AE F E), co.e (mat a' * z) =
          (fun j => GlobalTheory.TorusTheta.infScale F (((blk j).elim 1 t)⁻¹) * (co.e z).1 j,
           fun j => GlobalTheory.TorusTheta.infScale F ((blk j).elim 1 t) * (co.e z).2 j)) →
    ∀ (M₁ : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d), M₁.co = co → M₁.IsGood B.ψ → IsEv B M M₁ 1 1 ∅ e →
    ∀ Φ ∈ schA F (Fin n × Fin d), Φ ∈ M.So B.ψ B.τ₁ → ∀ (g : UA σ X.J) (h : UA σ W.J) (ξ : Fin n × Fin d → F),
      (∃ i : Fin r₀, ∀ j, blk j = some i → ξ j = 0) → e (om (g, h) Φ) (fun j => algebraMap F (AF F) (ξ j)) = 0 := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hW co blk _ _ hact M₁ e hco hG hev Φ _ hΦ g h ξ hξ
  have hcm := hP.base.cm
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  have hJ' : IsHermND σ ((1 : E) • X.J.map σ) := by
    rw [one_smul]; exact GlobalTheory.UnitaryVol.isHermND_map hσ hP.herm
  have hF := GlobalTheory.WittSupport.isFrameU_of_isWittFrame hσ hW
  refine GlobalTheory.ThKTorus.vanish_of_block_zero hKP F E σ B n d X W M χX χW om r s r' s' hP r₀ _ _ hF M₁
    (fun i => Finset.univ.filter (fun j => blk j = some i)) e hG ⟨fun i j hij => ?_, fun t a ht ha z => ?_⟩ hev Φ hΦ g h ξ ?_
  · refine Finset.disjoint_left.2 fun k hi hj => hij ?_
    exact Option.some_injective _ ((Finset.mem_filter.1 hi).2.symm.trans (Finset.mem_filter.1 hj).2)
  · obtain ⟨a₀, ha₀⟩ := GlobalTheory.SiegelSet.exists_isTorusElt hcm hJ' hW (t := t) fun i => (ht i).ne'
    let φ : UA σ X.J ≃* GAd σ ((1 : E) • X.J.map σ) :=
      MulEquiv.subgroupCongr (GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := X.J) hσ (one_ne_zero : (1 : E) ≠ 0))
    have he : ((φ.symm a₀ : UA σ X.J) : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) a₀ := rfl
    have ha' := GlobalTheory.TorusTranslate.isTorusU_of_isTorusElt F E σ hcm n X.J hP.herm.herm r₀ Xf Yf t a₀ ha₀ _ he
    rw [GlobalTheory.WittSupport.mat_eq_of_isTorusU hσ hP.herm.herm hF ha ha', hco, hact t ht a₀ ha₀ _ he, hact t ht a₀ ha₀ _ he,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    refine ⟨Prod.ext (funext fun j => ?_) (funext fun j => mul_zero _),
      Prod.ext (funext fun j => mul_zero _) (funext fun j => (GlobalTheory.WittSupport.blkScale_eq blk t z j).symm)⟩
    refine Eq.trans ?_ (GlobalTheory.WittSupport.blkScale_eq blk (fun i => (t i)⁻¹) z j).symm
    show GlobalTheory.TorusTheta.infScale F ((blk j).elim 1 t)⁻¹ * z j = _
    rcases blk j with _ | i₀ <;> simp
  · obtain ⟨i, hi⟩ := hξ
    exact ⟨i, fun j hj => hi j (Finset.mem_filter.1 hj).2⟩
