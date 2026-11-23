import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneUnipotentDecompositionStatement
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.FlagLeviProj

open GlobalTheory.ThK.SquareIntegrability

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (σ) in

def leftInv {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (J₁ : Matrix (Fin n₁) (Fin n₁) E) (ι : Matrix (Fin n) (Fin n₁) E) :
    Matrix (Fin n₁) (Fin n) E :=
  (J₁ᵀ)⁻¹ * (ι.map σ)ᵀ * Jᵀ

theorem leftInv_mul {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E}
    {ι : Matrix (Fin n) (Fin n₁) E} (hg : ιᵀ * J * ι.map σ = J₁) (hd : J₁.det ≠ 0) : leftInv σ J J₁ ι * ι = 1 := by
  have e : (ι.map σ)ᵀ * (Jᵀ * ι) = J₁ᵀ := by
    rw [← hg]; simp [Matrix.transpose_mul, Matrix.mul_assoc]
  simp only [leftInv, Matrix.mul_assoc]
  rw [e]
  exact Matrix.nonsing_inv_mul _ (by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.2 hd)

theorem leftInv_mulVec {n n₁ : ℕ} (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (J₁ : Matrix (Fin n₁) (Fin n₁) E) {ι : Matrix (Fin n) (Fin n₁) E} {v : Fin n → E}
    (hv : ∀ u, form σ J (ι *ᵥ u) v = 0) : leftInv σ J J₁ ι *ᵥ v = 0 := by
  have e : (ι.map σ)ᵀ *ᵥ (Jᵀ *ᵥ v) = 0 := funext fun j => by
    have h := hv (Pi.single j 1)
    rw [GlobalTheory.LeviPlaneSection.form_skew hσ hJ, neg_eq_zero, map_eq_zero] at h
    refine Eq.trans ?_ h
    simp only [form, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply, Pi.zero_apply,
      Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  simp only [leftInv, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_zero]

theorem key {n n₁ : ℕ} {P : Matrix (Fin n₁) (Fin n) (AE F E)} {ι : Matrix (Fin n) (Fin n₁) (AE F E)} {x : Fin n → AE F E}
    (hPι : P * ι = 1) (hPx : P *ᵥ x = 0) {A : Matrix (Fin n) (Fin n) (AE F E)} {Q : Matrix (Fin n₁) (Fin n₁) (AE F E)}
    (hA : ∀ z, ∃ a : AE F E, A *ᵥ (ι *ᵥ z) = ι *ᵥ (Q *ᵥ z) + a • x) : P * A * ι = Q := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  obtain ⟨a, ha⟩ := hA (Pi.single j 1)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, Matrix.mulVec_smul, hPx, smul_zero, add_zero,
    Matrix.mulVec_mulVec, hPι, Matrix.one_mulVec]

theorem mat_mul' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (a b : UA σ J) : mat (a * b) = mat a * mat b := rfl

theorem mat_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (a : UA σ J) : mat a⁻¹ * mat a = 1 :=
  Units.inv_mul a.1

theorem mat_mul_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (a : UA σ J) : mat a * mat a⁻¹ = 1 :=
  Units.mul_inv a.1

theorem unip_act {n n₁ : ℕ} {W : Spc F E n} {H : Plane E n n₁} {v : UA σ W.J} (hv : v ∈ unip σ W H) :
    mat v *ᵥ incV F H.x = incV F H.x ∧
      ∀ z, ∃ a : AE F E, mat v *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x := by
  induction hv using Subgroup.closure_induction with
  | mem g hg => exact hg
  | one => exact ⟨Matrix.one_mulVec _, fun z => ⟨0, by rw [zero_smul, add_zero]; exact Matrix.one_mulVec _⟩⟩
  | mul a b _ _ ha hb =>
    refine ⟨by rw [mat_mul', ← Matrix.mulVec_mulVec, hb.1, ha.1], fun z => ?_⟩
    obtain ⟨c, hc⟩ := hb.2 z
    obtain ⟨d, hd⟩ := ha.2 z
    refine ⟨d + c, ?_⟩
    rw [mat_mul', ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_add, Matrix.mulVec_smul, hd, ha.1, add_smul, add_assoc]
  | inv a _ ha =>
    have hx : mat a⁻¹ *ᵥ incV F H.x = incV F H.x := by
      conv_lhs => rw [← ha.1]
      rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]
    refine ⟨hx, fun z => ?_⟩
    obtain ⟨c, hc⟩ := ha.2 z
    refine ⟨-c, ?_⟩
    have e : mat a⁻¹ *ᵥ (mat a *ᵥ (incM F H.ι *ᵥ z)) = mat a⁻¹ *ᵥ (incM F H.ι *ᵥ z + c • incV F H.x) := by rw [hc]
    rw [Matrix.mulVec_mulVec (incM F H.ι *ᵥ z) (mat a⁻¹) (mat a), mat_inv_mul, Matrix.one_mulVec, Matrix.mulVec_add,
      Matrix.mulVec_smul, hx] at e
    rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq]
    exact e.symm

end GlobalTheory.FlagLeviProj

open GlobalTheory.ThK.SquareIntegrability GlobalTheory.FlagLeviProj in

theorem GlobalTheory.FlagLeviProj.levi_proj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, Continuous M → (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      (∀ γ ∈ ratU σ W₁.J, M γ ∈ ratU σ W.J) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
      ∀ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) → (∀ k, Y' k 0 = c₀⁻¹ * H.y k) →
      (∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i) → ∀ S' : Finset (Fin r),
      ∃ p : GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' (insert 0 (S'.map (Fin.succEmb r))) → GlobalTheory.StdPar.unip σ (c₀ • W₁.J.map σ) Xf S', Continuous p ∧
        (∀ (x : GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' (insert 0 (S'.map (Fin.succEmb r)))) (v : UA σ W.J), v ∈ unip σ W H → ∀ u ∈ GlobalTheory.StdPar.unip σ (c₀ • W₁.J.map σ) Xf S',
          (x : GAd σ (c₀ • W.J.map σ)) = GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ v * GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ (M ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀).symm u)) → ((p x : GlobalTheory.StdPar.unip σ (c₀ • W₁.J.map σ) Xf S') : GAd σ (c₀ • W₁.J.map σ)) = u) ∧
        ∀ x : GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' (insert 0 (S'.map (Fin.succEmb r))), (x : GAd σ (c₀ • W.J.map σ)) ∈ ratPts σ (c₀ • W.J.map σ) → ((p x : GlobalTheory.StdPar.unip σ (c₀ • W₁.J.map σ) Xf S') : GAd σ (c₀ • W₁.J.map σ)) ∈ ratPts σ (c₀ • W₁.J.map σ) := by
  intro F E _ _ _ _ _ σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hJ₁ hJ M hMc hL hMr r Xf Yf hWf X' Y'
    hW' hX0 hY0 hXs S'
  have hdec := GlobalTheory.T.skew_plane_unipotent_decomposition F E σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hJ₁ hJ M hMc hL hMr r Xf Yf hWf
    X' Y' hW' hX0 hY0 hXs S'
  obtain ⟨_, _⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  have hd₁ : W₁.J.det ≠ 0 := fun h0 => hJ₁.2 (by
    have e : (W₁.J.map σ).det = (σ : E →+* E) W₁.J.det := by rw [RingHom.map_det]; rfl
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero])
  set P₀ := leftInv σ W.J W₁.J H.ι with hP₀
  have hPι : incM F P₀ * incM F H.ι = 1 := by
    rw [incM, incM, ← Matrix.map_mul, leftInv_mul hgram hd₁, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPx : incM F P₀ *ᵥ incV F H.x = 0 := funext fun i => by
    refine (RingHom.map_mulVec (inclR (F := F) (AF F)) _ H.x i).symm.trans ?_
    rw [leftInv_mulVec hσ hsk W₁.J fun u => (horth u).1]
    exact map_zero _
  have hlevi : ∀ h₁ : UA σ W₁.J, (∀ z, mat (M h₁) *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat h₁ *ᵥ z)) ∧
      mat (M h₁) *ᵥ incV F H.x = incV F H.x ∧
      (∀ z, mat (M h₁)⁻¹ *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat h₁⁻¹ *ᵥ z)) ∧
      mat (M h₁)⁻¹ *ᵥ incV F H.x = incV F H.x := fun h₁ => by
    obtain ⟨l1, -, l3⟩ := hL h₁
    have hx : mat (M h₁) *ᵥ incV F H.x = incV F H.x := by rw [l1]; simp
    have hι : ∀ z, mat (M h₁) *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat h₁ *ᵥ z) := fun z => by
      rw [Matrix.mulVec_mulVec, l3, ← Matrix.mulVec_mulVec]
    refine ⟨hι, hx, fun z => ?_, ?_⟩
    · have e := hι (mat h₁⁻¹ *ᵥ z)
      rw [Matrix.mulVec_mulVec z (mat h₁) (mat h₁⁻¹), mat_mul_inv, Matrix.one_mulVec] at e
      rw [← e, Matrix.mulVec_mulVec _ (mat (M h₁)⁻¹) (mat (M h₁)), mat_inv_mul, Matrix.one_mulVec]
    · conv_lhs => rw [← hx]
      rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]
  have hform : ∀ (g : GAd σ (c₀ • W.J.map σ)) (v : UA σ W.J), v ∈ unip σ W H → ∀ h₁ : UA σ W₁.J,
      g = toGAd hσ W.J hc₀ v * toGAd hσ W.J hc₀ (M h₁) →
      incM F P₀ * (matHom _ σ _ g).1 * incM F H.ι = mat h₁ ∧
        incM F P₀ * (matHom _ σ _ g⁻¹).1 * incM F H.ι = mat h₁⁻¹ := by
    rintro g v hv h₁ rfl
    obtain ⟨lι, lx, liι, lix⟩ := hlevi h₁
    constructor
    · refine key hPι hPx fun z => ?_
      obtain ⟨a, ha⟩ := (unip_act hv).2 (mat h₁ *ᵥ z)
      refine ⟨a, ?_⟩
      change (mat v * mat (M h₁)) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, lι, ha]
    · refine key hPι hPx fun z => ?_
      obtain ⟨a, ha⟩ := (unip_act (inv_mem hv)).2 z
      refine ⟨a, ?_⟩
      change (mat (M h₁)⁻¹ * mat v⁻¹) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, Matrix.mulVec_smul, liι, lix]
  have hex : ∀ g : GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' (insert 0 (S'.map (Fin.succEmb r))),
      ∃ u : GlobalTheory.StdPar.unip σ (c₀ • W₁.J.map σ) Xf S', ∃ v ∈ unip σ W H,
        (g : GAd σ (c₀ • W.J.map σ)) =
          toGAd hσ W.J hc₀ v * toGAd hσ W.J hc₀ (M ((toGAd hσ W₁.J hc₀).symm u)) := fun g => by
    obtain ⟨v, hv, u, hu, e⟩ := (hdec g).1 g.2
    exact ⟨⟨u, hu⟩, v, hv, e⟩
  choose p hp using hex
  have hpm : ∀ g, (matHom _ σ _ (p g : GAd σ (c₀ • W₁.J.map σ))).1 =
        incM F P₀ * (matHom _ σ _ (g : GAd σ (c₀ • W.J.map σ))).1 * incM F H.ι ∧
      (matHom _ σ _ (p g : GAd σ (c₀ • W₁.J.map σ))⁻¹).1 =
        incM F P₀ * (matHom _ σ _ (g : GAd σ (c₀ • W.J.map σ))⁻¹).1 * incM F H.ι := fun g => by
    obtain ⟨v, hv, e⟩ := hp g
    obtain ⟨h1, h2⟩ := hform _ v hv _ e
    rw [h1, h2]
    constructor
    · conv_lhs => rw [← (toGAd hσ W₁.J hc₀).apply_symm_apply (p g : GAd σ (c₀ • W₁.J.map σ))]
      rfl
    · conv_lhs => rw [← (toGAd hσ W₁.J hc₀).apply_symm_apply (p g : GAd σ (c₀ • W₁.J.map σ))]
      rfl
  have inj : Function.Injective (matHom (AF F) σ (c₀ • W₁.J.map σ)) := Subgroup.subtype_injective _
  refine ⟨p, ?_, ?_, ?_⟩
  · have hc : Continuous fun g => matHom _ σ (c₀ • W₁.J.map σ) (p g : GAd σ (c₀ • W₁.J.map σ)) := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · refine Continuous.congr (f := fun g : GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' (insert 0 (S'.map (Fin.succEmb r))) =>
          incM F P₀ * (matHom _ σ _ (g : GAd σ (c₀ • W.J.map σ))).1 * incM F H.ι) ?_ fun g => (hpm g).1.symm
        exact (continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.comp continuous_subtype_val)).matrix_mul
          continuous_const
      · refine Continuous.congr (f := fun g : GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' (insert 0 (S'.map (Fin.succEmb r))) =>
          incM F P₀ * (matHom _ σ _ (g : GAd σ (c₀ • W.J.map σ))⁻¹).1 * incM F H.ι) ?_ fun g => ?_
        · exact (continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.comp continuous_subtype_val.inv)).matrix_mul
            continuous_const
        · rw [← map_inv]
          exact (hpm g).2.symm
    exact continuous_induced_rng.2 (continuous_induced_rng.2 hc)
  · intro g v hv u hu e
    refine inj (Units.ext ?_)
    obtain ⟨h1, -⟩ := hform _ v hv _ e
    rw [(hpm g).1, h1]
    conv_rhs => rw [← (toGAd hσ W₁.J hc₀).apply_symm_apply u]
    rfl
  · intro g hg
    obtain ⟨γ, hγ, hγe⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hg)
    have e1 : (matHom _ σ _ (g : GAd σ (c₀ • W.J.map σ))).1 = γ.1.map (inclR (F := F) (AF F)) :=
      (congrArg Units.val hγe).symm
    have e2 : (matHom _ σ _ (g : GAd σ (c₀ • W.J.map σ))⁻¹).1 = (γ⁻¹).1.map (inclR (F := F) (AF F)) := by
      rw [map_inv]
      exact (congrArg (fun u : GL (Fin n) (AF F ⊗[F] E) => (u⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1) hγe).symm
    have eq1 : (matHom _ σ _ (p g : GAd σ (c₀ • W₁.J.map σ))).1 = (P₀ * γ.1 * H.ι).map (inclR (F := F) (AF F)) := by
      rw [(hpm g).1, e1, Matrix.map_mul, Matrix.map_mul]; rfl
    have eq2 : (matHom _ σ _ (p g : GAd σ (c₀ • W₁.J.map σ))⁻¹).1 =
        (P₀ * (γ⁻¹).1 * H.ι).map (inclR (F := F) (AF F)) := by
      rw [(hpm g).2, e2, Matrix.map_mul, Matrix.map_mul]; rfl
    have one : (1 : Matrix (Fin n₁) (Fin n₁) (AE F E)) = (1 : Matrix (Fin n₁) (Fin n₁) E).map (inclR (F := F) (AF F)) :=
      (Matrix.map_one _ (map_zero _) (map_one _)).symm
    have h12 : (P₀ * γ.1 * H.ι) * (P₀ * (γ⁻¹).1 * H.ι) = 1 := Matrix.map_injective GlobalTheory.AutFunCompare.inclA_injective (by
      beta_reduce
      rw [Matrix.map_mul, ← eq1, ← eq2, map_inv, Units.mul_inv, ← one])
    have h21 : (P₀ * (γ⁻¹).1 * H.ι) * (P₀ * γ.1 * H.ι) = 1 := Matrix.map_injective GlobalTheory.AutFunCompare.inclA_injective (by
      beta_reduce
      rw [Matrix.map_mul, ← eq1, ← eq2, map_inv, Units.inv_mul, ← one])
    let γ₁ : GL (Fin n₁) E := ⟨P₀ * γ.1 * H.ι, P₀ * (γ⁻¹).1 * H.ι, h12, h21⟩
    have hU : γ₁ ∈ Formalism.UG.UJ (σ : E →+* E) (c₀ • W₁.J.map σ) := by
      have h2 := (p g : GAd σ (c₀ • W₁.J.map σ)).2
      change Formalism.UG.cT _ (matHom _ σ _ (p g : GAd σ (c₀ • W₁.J.map σ))).1 * Matrix.map _ (inclR (F := F) (AF F)) *
        (matHom _ σ _ (p g : GAd σ (c₀ • W₁.J.map σ))).1 = Matrix.map _ (inclR (F := F) (AF F)) at h2
      rw [eq1, GlobalTheory.AutFunCounterexample.cT_map_gen, ← Matrix.map_mul, ← Matrix.map_mul] at h2
      exact Matrix.map_injective GlobalTheory.AutFunCompare.inclA_injective h2
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ₁, hU, Units.ext eq1.symm⟩)
