import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero

noncomputable section

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open scoped GlobalTheory.VacAny

namespace GlobalTheory.VacShift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_invol {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]

theorem form_swap {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (a b : Fin n → E) : form σ J a b = -σ (form σ J b a) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem form_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (t : E) (a b : Fin n → E) :
    form σ J (t • a) b = t * form σ J a b := by
  simp only [form, smul_dotProduct, smul_eq_mul]

theorem form_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (t : E) (a b : Fin n → E) :
    form σ J a (t • b) = σ t * form σ J a b := by
  have : (fun i => σ ((t • b) i)) = σ t • fun i => σ (b i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_add_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J a (b + c) = form σ J a b + form σ J a c := by
  have : (fun i => σ ((b + c) i)) = (fun i => σ (b i)) + fun i => σ (c i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_add, dotProduct_add]

theorem mem_conjI (σ : E →ₐ[F] E) {𝔠 : FractionalIdeal (𝓞 E)⁰ E} {s : E} (hs : s ∈ 𝔠) :
    σ s ∈ conjI σ 𝔠 := by
  rw [conjI, FractionalIdeal.mem_extended_iff]
  apply Submodule.subset_span
  refine ⟨s, hs, ?_⟩
  have h : (IsLocalization.map E (conjO σ) (conjO_le σ) : E →+* E) = (σ : E →+* E) :=
    IsLocalization.ringHom_ext (𝓞 E)⁰ (RingHom.ext fun x => by
      simp [IsLocalization.map_eq, conjO, RingOfIntegers.mapRingHom_apply])
  exact congrFun (congrArg DFunLike.coe h) s

end GlobalTheory.VacShift

namespace GlobalTheory.VacShift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem smul_y_mem {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {B : Base F E} {d d₁ : ℕ} {W : Spc F E d}
    {W₁ : Spc F E d₁} {H' : Plane E d d₁} {i₀ i₁ r s : ℕ} (hW : W.IsSkew σ B r s)
    (hH : H'.IsAdapted σ B W W₁ i₀ i₁) {t : E} (ht : t ∈ (conjI σ H'.𝔟)⁻¹ * (diffE E)⁻¹) : t • H'.y ∈ W.L := by
  by_cases h0 : conjI σ H'.𝔟 = 0
  · rw [h0, inv_zero, zero_mul, FractionalIdeal.mem_zero_iff] at ht
    rw [ht, zero_smul]
    exact W.L.zero_mem
  refine (hW.dual _).2 fun x hx o => ?_
  obtain ⟨s, t', u, hs, -, -, rfl⟩ := hH.split x hx
  have hs' : s ∈ H'.𝔟 := (hH.ideal s).2 hs
  have hyx : form σ W.J H'.y H'.x = -1 := by rw [form_swap hσ _ hW.skew, hH.xy, map_one]
  have hyι : form σ W.J H'.y (H'.ι *ᵥ u) = 0 := by
    rw [form_swap hσ _ hW.skew, (hH.orth u).2, map_zero, neg_zero]
  have e : form σ W.J (t • H'.y) (s • H'.x + H'.ι *ᵥ u + t' • H'.y) = -(t * σ s) := by
    rw [form_smul_left, form_add_right, form_add_right, form_smul_right, form_smul_right, hyx, hyι, hH.yy]
    ring
  have hmem : (o : E) * (t * σ s) ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    have h1 : (o : E) ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := (FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩
    have h2 := FractionalIdeal.mul_mem_mul h1 (FractionalIdeal.mul_mem_mul ht (mem_conjI σ hs'))
    rwa [one_mul, mul_right_comm, inv_mul_cancel₀ h0, one_mul, diffE, coeIdeal_differentIdeal ℤ ℚ, inv_inv] at h2
  obtain ⟨k, hk⟩ := (FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))).1 hmem 1 ((FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩)
  rw [Algebra.traceForm_apply, mul_one] at hk
  rw [e, mul_neg, map_neg, ← hk]
  exact isIntegral_algebraMap.neg

theorem liftV_one_mul (v : Pl F) (x : AF F) :
    GlobalTheory.LatVac.liftV v (1 : Fv F v) * x = GlobalTheory.LatVac.liftV v (evFin F v x) := by
  have h := GlobalTheory.LatVac.at_liftV v (1 : Fv F v) (x - GlobalTheory.LatVac.liftV v (evFin F v x))
    (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, sub_self])
  have h2 := GlobalTheory.LatVac.at_liftV v (evFin F v x) (1 - GlobalTheory.LatVac.liftV v 1)
    (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [smul_eq_mul] at h h2
  linear_combination h - h2

theorem liftV_one_smul_eq (v : Pl F) (a : AE F E) :
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • a = (GlobalTheory.LatVac.liftV v).rTensor E (compFin F E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, liftV_one_mul]
    rfl
  | add a b ha hb => rw [smul_add, ha, hb, map_add, map_add]

end GlobalTheory.VacShift

namespace GlobalTheory.VacShift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem lift_smul_mem (hσ : ∀ x, σ (σ x) = x) {B : Base F E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d}
    {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {H : Plane E n n₁} {H' : Plane E d d₁} {i₀ i₁ j₀ j₁ r s : ℕ}
    (hW : W.IsSkew σ B r s) (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hH' : H'.IsAdapted σ B W W₁ i₀ i₁) (v : Pl F)
    {z : Fv F v ⊗[F] E} (hz : z ∈ GlobalTheory.SnMass.locId v (idA σ H.𝔟 H'.𝔟)) :
    ((GlobalTheory.LatVac.liftV v).rTensor E z) • Matrix.vecMulVec (incV F H.x) (incV F H'.y) ∈ latAtV X W v := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, x, hx, rfl⟩ := hy
    rw [LinearMap.rTensor_tmul]
    rw [idA, mul_assoc] at hx
    refine FractionalIdeal.mul_induction_on hx (fun p hp q hq => ?_) (fun p q hp hq => ?_)
    · have e : (GlobalTheory.LatVac.liftV v c ⊗ₜ[F] (p * q)) • Matrix.vecMulVec (incV F H.x) (incV F H'.y) =
          GlobalTheory.LatVac.liftV v c • incM F (Matrix.vecMulVec (p • H.x) (q • H'.y)) := by
        ext i j
        simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, incV, incM, Matrix.map_apply, inclR,
          Pi.smul_apply, smul_eq_mul, RingHom.coe_coe, AlgHom.toRingHom_eq_coe,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul',
          mul_one]
        congr 1
        ring
      rw [e]
      exact AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.at_liftV v c, by rw [GlobalTheory.LatVac.evFin_liftV]; exact hc,
        _, (hH.ideal p).1 hp, _, smul_y_mem hσ hW hH' hq, rfl⟩
    · rw [TensorProduct.tmul_add, add_smul]
      exact add_mem hp hq
  | zero => rw [map_zero, zero_smul]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, add_smul]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, neg_smul]; exact neg_mem hx

theorem hTens_vecMulVec_gen {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
    {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (x x' : α → A) (y y' : β → A) :
    GlobalTheory.WeilM.hTens c JA JB (Matrix.vecMulVec x y) (Matrix.vecMulVec x' y') =
      (∑ i : α, ∑ k : α, x i * JA i k * c (x' k)) * (∑ j : β, ∑ l : β, y j * JB j l * c (y' l)) := by
  unfold GlobalTheory.WeilM.hTens
  simp_rw [Finset.sum_mul_sum]
  simp only [Matrix.vecMulVec_apply, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

variable (σ) in

theorem symp_shift_zero {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E) {y : Fin d → E}
    (hy : form σ JB y y = 0) (ξ c : AE F E) (x : Fin n → E) :
    symp (R := AF F) (cA σ) ξ (incM F JA) (incM F JB) (c • Matrix.vecMulVec (incV F x) (incV F y))
      (c • Matrix.vecMulVec (incV F x) (incV F y)) = 0 := by
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  have h0 : (∑ j, ∑ l, incV F y j * incM F JB j l * cA σ (incV F y l)) = 0 := by
    have e : (∑ j, ∑ l, incV F y j * incM F JB j l * cA σ (incV F y l)) = inclR (F := F) (AF F) (form σ JB y y) := by
      simp only [form, dotProduct, Matrix.mulVec, incV, incM, Matrix.map_apply, hc, map_sum, map_mul, Finset.mul_sum,
        mul_assoc]
    rw [e, hy, map_zero]
  have hs : c • Matrix.vecMulVec (incV F x) (incV F y) = Matrix.vecMulVec (c • incV F x) (incV F y) := by
    ext i j
    simp [Matrix.vecMulVec_apply, mul_assoc]
  rw [hs, symp, hTens_vecMulVec_gen, h0, mul_zero, mul_zero, map_zero]

theorem vac_fixed : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) {b a' : ℕ}
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')) (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → CfgA B G G₁ H H' →
    ∀ (v : Pl F) (l : (AE F E)ˣ), l ∈ idelesAt E (evFin F v) → (unitFin F E v l : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v (idA σ H.𝔟 H'.𝔟) →
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (shiftA H H' l)) (G.M.vac v) = G.M.vac v := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' hX hC v l hl hloc
  have hσ := sigma_invol hX.base.cm
  set u := shiftA H H' l with hu
  have hpart : partFin v u = ((GlobalTheory.LatVac.liftV v).rTensor E (compFin F E v l.1)) •
      Matrix.vecMulVec (incV F H.x) (incV F H'.y) := by
    rw [partFin, hu, smul_shiftA, liftV_one_smul_eq]
  have hγ : partFin v u ∈ latAtV G.V G.W v := by
    rw [hpart]
    exact lift_smul_mem hσ hX.geo.hW hC.hH hC.hH' v hloc
  obtain ⟨hSB, -, θ, -, hvac⟩ := hX.geo.hM.vac v
  have h1 := hvac _ hγ
  have hz : symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) (partFin v u)
      (partFin v u) = 0 := by
    rw [hpart]
    exact symp_shift_zero σ _ _ hC.hH'.yy _ _ _
  rw [hz, mul_zero, AddChar.map_zero_eq_one, one_smul] at h1
  have h2 := GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v _ (at_partFin v u) (G.M.vac v)
  have e : GlobalTheory.LatVac.locCo G.M.co v (partFin v u) = GlobalTheory.LatVac.locCo G.M.co v u := by
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
      simp [GlobalTheory.LatVac.locCo, partFin, GlobalTheory.LatVac.evFin_liftV]
  rw [e] at h2
  exact GlobalTheory.TensUniq.eq_of_tens_eq v (G.M.vac v) _ _ hSB fun r hr => (h2 r hr).symm.trans (h1 r hr)

end GlobalTheory.VacShift
