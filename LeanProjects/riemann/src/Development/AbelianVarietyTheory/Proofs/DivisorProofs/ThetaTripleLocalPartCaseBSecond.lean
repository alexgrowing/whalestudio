import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOpInfMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionMapsSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalEigenTripleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFixingVectorPreserves
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TmulSumEqZeroOfPureTensorFunctionZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionUnitaryCompact

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.InfBUnip

theorem rho_add_of_form {R : Type} [CommRing R] [Invertible (2 : R)] {V : Type} [AddCommGroup V] [Module R V]
    {Bf : V → V → R} {κ : Type} [Fintype κ] (d : Darboux Bf κ) (ψ : AddChar R ℂ) {u v : V} (h0 : Bf u v = 0)
    (φ : (κ → R) → ℂ) : d.rho ψ (u + v) φ = d.rho ψ u (d.rho ψ v φ) := by
  have h := (d.form u v).symm.trans h0
  funext x
  simp only [Darboux.rho, schr, map_add, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (-(⅟(2 : R))) * h + ((d.e u).1 ⬝ᵥ (d.e v).2) * h2

theorem hTens_line {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type} [Fintype α]
    [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (w : β → A) (hw : ∑ j, ∑ l, w j * JB j l * c (w l) = 0)
    (p p' : α → A) : hTens c JA JB (Matrix.vecMulVec p w) (Matrix.vecMulVec p' w) = 0 := by
  unfold hTens
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  have := congrArg (fun t => p i * JA i k * c (p' k) * t) hw
  simp only [Finset.mul_sum, mul_zero] at this
  rw [← this]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [Matrix.vecMulVec_apply, map_mul]
  ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem iso_adelic {d : ℕ} {J : Matrix (Fin d) (Fin d) E} {w : Fin d → E} (hw : form σ J w w = 0) :
    ∑ j, ∑ l, incV F w j * incM F J j l * cA σ (incV F w l) = 0 := by
  have := congrArg (inclR (F := F) (AF F)) hw
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, map_zero, Finset.mul_sum] at this
  rw [← this]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [incV, incM, Matrix.map_apply, GlobalTheory.UnipLine.cA_inclR, mul_assoc]

theorem partInf_vecMulVec {n d : ℕ} (p : Fin n → AE F E) (w : Fin d → AE F E) :
    partInf F (Matrix.vecMulVec p w) = Matrix.vecMulVec (realAd F 1 • p) w := by
  ext i j
  simp only [partInf, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_mul_assoc]

theorem locOpInf_rho_add {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {ψ : AddChar (AF F) ℂ}
    (hψ : IsStd ψ) {w : Fin d → E} (hw : form σ W.J w w = 0) (p p' : Fin n → AE F E) (f : SInf F (Fin n × Fin d)) :
    locOpInf (M.co.rho ψ (partInf F (Matrix.vecMulVec (p + p') (incV F w)))) f =
      locOpInf (M.co.rho ψ (partInf F (Matrix.vecMulVec p (incV F w))))
        (locOpInf (M.co.rho ψ (partInf F (Matrix.vecMulVec p' (incV F w)))) f) := by
  obtain ⟨r, h0, hr⟩ := exists_rest_inf F (Fin n × Fin d)
  refine DFunLike.coe_injective (eq_of_tens_inf h0 (hr f).1 ?_)
  rw [← (locOpInf_rho M.co hψ _ _).1 r (hr _), ← (locOpInf_rho M.co hψ _ _).1 r (hr _),
    ← (locOpInf_rho M.co hψ _ _).1 r (hr _), ← rho_add_of_form]
  · rw [Matrix.add_vecMulVec, partInf, smul_add]
    rfl
  · rw [partInf_vecMulVec, partInf_vecMulVec, symp, hTens_line _ _ _ _ (iso_adelic hw), mul_zero, map_zero]

theorem locOpInf_om_rho {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ}
    (hψ : IsStd ψ) {χX χW : Chr F E} {om : Rep σ X W} (hW : M.IsWeil ψ χX χW om) {g : UA σ X.J}
    (hex : ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (g, 1)) f f₁)
    (u : Matrix (Fin n) (Fin d) (AE F E)) (f : SInf F (Fin n × Fin d)) :
    locOpInf (M.co.rho ψ (partInf F (mat g * u))) (locOpInf (om (g, 1)) f) =
      locOpInf (om (g, 1)) (locOpInf (M.co.rho ψ (partInf F u)) f) := by
  have hS := IsUWeilPair.isUSplitting hW
  have hact : actAB (cA σ) ((g, 1) : UA σ X.J × UA σ W.J) (partInf F u) = partInf F (mat g * u) := by
    change mat g * (partInf F u) * (mat (1 : UA σ W.J))ᵀ = _
    have h1 : mat (1 : UA σ W.J) = 1 := rfl
    rw [h1, Matrix.transpose_one, Matrix.mul_one, partInf, partInf, Matrix.mul_smul]
  obtain ⟨r, h0, hr⟩ := exists_rest_inf F (Fin n × Fin d)
  refine DFunLike.coe_injective (eq_of_tens_inf h0 (hr f).1 ?_)
  have h2 := hS.impl (g, 1) (partInf F u) _ (hr f).2
  rw [hact, (locOpInf_rho M.co hψ u f).1 r (hr _), acts_locOpInf (hex _) r (hr _), acts_locOpInf (hex _) r (hr _),
    (locOpInf_rho M.co hψ _ _).1 r (hr _)] at h2
  exact h2.symm

theorem rest_vac {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ)
    (f : SInf F (Fin n × Fin d)) :
    Rest (evI F) (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
      (fun x => ∏ᶠ v, M.vac v fun i => evFin F v (x i)) := by
  refine ⟨fun x z hz => ?_, GlobalTheory.TensUniq.pure_mem_schA f M.vac (fun v => (hM.vac v).1) hM.std⟩
  have hz0 : ∀ v i, evFin F v (z i) = 0 := by
    intro v i
    set u : AF F := (0, 1) with hu
    have h1 := congrFun (hz u GlobalTheory.ArchLocality.evI_fin) i
    have h2 : evFin F v u = 1 := map_one (evFin F v)
    have h3 := congrArg (evFin F v) h1
    simp only [Pi.zero_apply, map_zero] at h3
    change evFin F v (u * z i) = 0 at h3
    rw [map_mul, h2, one_mul] at h3
    exact h3
  simp only [Pi.add_apply, map_add, hz0, add_zero]

theorem eq_of_pure_vac {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ}
    (hM : M.IsGood ψ) {A C : SInf F (Fin n × Fin d)} (h : pure A M.vac = pure C M.vac) : A = C := by
  refine DFunLike.ext _ _ fun x => ?_
  have key := GlobalTheory.ThK.PureTensIndep.sum_local_eq_zero M.vac (fun v => (hM.vac v).2.1) hM.std ∅ ![A - C] ![M.vac]
    (fun i v _ => by fin_cases i; rfl) ?_ x (fun _ _ => 0)
  · simpa [sub_eq_zero] using key
  · simp only [Fin.sum_univ_one, Matrix.cons_val_zero]
    funext y
    have e := congrFun h y
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure] at e
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.zero_apply, SchwartzMap.sub_apply]
    rw [sub_mul, e, sub_self]

theorem locPart_rho {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E}
    {M : Model σ X W} {M₁ : Model σ X₁ W₁} (hψ : IsStd B.ψ) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ)
    {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E} {I : Set (Matrix (Fin n) (Fin d) (AE F E))}
    {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} (he : IsEv B M M₁ ι ι' I e)
    {ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁)}
    {ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ}
    (hL : IsLocPart M M₁ e ei ev) {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : partInf F u ∈ I)
    (f : SInf F (Fin n × Fin d)) : ei (locOpInf (M.co.rho B.ψ (partInf F u)) f) = ei f := by
  obtain ⟨-, hvac, hpure⟩ := hL
  have hE : ∀ f, e (pure f M.vac) = pure (ei f) M₁.vac := by
    intro f
    rw [hpure f M.vac (fun v => (hM.vac v).1) (Eventually.of_forall fun _ => rfl)]
    congr 1
    funext v
    exact (hvac v).1
  have hA : M.co.rho B.ψ (partInf F u) (pure f M.vac) = pure (locOpInf (M.co.rho B.ψ (partInf F u)) f) M.vac :=
    (locOpInf_rho M.co hψ u f).1 _ (rest_vac hM f)
  have hS : pure f M.vac ∈ schA F (Fin n × Fin d) := (rest_vac hM f).2
  apply eq_of_pure_vac hM₁
  rw [← hE, ← hE, ← hA, he.inv _ hu _ hS]

theorem unip_fix {n n₁ : ℕ} {X : Spc F E n} {H : Plane E n n₁} {g : UA σ X.J} (hg : g ∈ unip σ X H) :
    mat g *ᵥ incV F H.x = incV F H.x := by
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact hg.1
  | one => rw [GlobalTheory.UnipLine.mat_one, Matrix.one_mulVec]
  | mul g h _ _ hg hh => rw [GlobalTheory.UnipLine.mulVec_mul, hh, hg]
  | inv g _ hg => exact GlobalTheory.UnipLine.inv_mulVec_of_mulVec hg

theorem unip_cone_law : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ n ∈ unip σ G.V' H, n ∈ UAt σ G.V' (evI F) →
    ∀ (s : (AE F E)ˣ) (f : SInf F (Fin (b + 2) × Fin (a + (b + 2)))),
      ei' (locOpInf (G.M'.co.rho B.ψ (partInf F (shiftB σ H H' s))) (locOpInf (om' (n, 1)) f)) =
        ei' (locOpInf (G.M'.co.rho B.ψ (partInf F (shiftB σ H H' s))) f) := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he ei' ev' hL X om om' om₁ om₁' hT hT₁ n hn hni s f
  have hex := GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ _ _ _ _ G.M' B.ψ _ _ om' hT.base.cm hT.base.std hT.weil' n hni
  obtain ⟨c, z₀, hy⟩ := GlobalTheory.UnipLine.mulVec_y hC.hH hT.geo.hV' n⁻¹ (unip_fix (inv_mem hn))
  have hsh : shiftB σ H H' s = Matrix.vecMulVec (cA σ s.1 • incV F H.y) (incV F H'.x) := by
    rw [shiftB, Matrix.smul_vecMulVec]
  have hu : mat n⁻¹ * shiftB σ H H' s = Matrix.vecMulVec ((cA σ s.1 * c) • incV F H.x +
      (incM F H.ι *ᵥ (cA σ s.1 • z₀) + cA σ s.1 • incV F H.y)) (incV F H'.x) := by
    rw [hsh, Matrix.mul_vecMulVec, Matrix.mulVec_smul, hy, Matrix.mulVec_smul, mul_smul, smul_add, smul_add]
    congr 1
    abel
  have hback : mat n * (mat n⁻¹ * shiftB σ H H' s) = shiftB σ H H' s := by
    rw [← Matrix.mul_assoc, ← GlobalTheory.UnipLine.mat_mul, mul_inv_cancel, GlobalTheory.UnipLine.mat_one, Matrix.one_mul]
  have h1 := locOpInf_om_rho hT.base.std hT.weil' hex (mat n⁻¹ * shiftB σ H H' s) f
  rw [hback] at h1
  rw [h1, (GlobalTheory.T.config_b_local_eigen_triple hP F E σ B a b G G₁ H H' hC e' he ei' ev' hL X om om' om₁ om₁' hT hT₁).1 n hn hni, hu,
    locOpInf_rho_add G.M' hT.base.std hC.hH'.xx, locPart_rho hT.base.std hT.geo.hM' hT₁.geo.hM' he hL,
    locOpInf_rho_add G.M' hT.base.std hC.hH'.xx, locPart_rho hT.base.std hT.geo.hM' hT₁.geo.hM' he hL, hsh]
  · refine Or.inr ⟨realAd F 1 • (cA σ s.1 • z₀), ?_⟩
    rw [partInf_vecMulVec, Matrix.mulVec_smul _ (realAd F 1)]
  · refine Or.inl ⟨realAd F 1 • ((cA σ s.1 * c) • incV F H'.x), ?_⟩
    ext i j
    simp only [partInf, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mul_smul_comm]
    congr 1
    ring

end GlobalTheory.ThK.InfBUnip

end
