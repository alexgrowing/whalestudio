import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneHermitianIdealCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSkewIdealCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchroedingerEigenvectorCompactCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEigenContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalUnitLevi
open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler GlobalTheory.LocIdeal
open GlobalTheory.Doubling (absE)
open Formalism.L2.Host (aboveF)
open scoped Classical
open scoped GlobalTheory.VacAny
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

noncomputable section

namespace GlobalTheory.VacShiftB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_swap_herm {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (a b : Fin n → E) : form σ J a b = σ (form σ J b a) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hJ j i]
  ring

theorem smul_y_mem {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {B : Base F E} {n n₁ : ℕ} {V : Spc F E n}
    {V₁ : Spc F E n₁} {H : Plane E n n₁} {i₀ i₁ r s : ℕ} (hV : V.IsHerm σ B r s)
    (hH : H.IsAdapted σ B V V₁ i₀ i₁) {p : E} (hp : p ∈ H.𝔟⁻¹) : σ p • H.y ∈ V.L := by
  by_cases h0 : H.𝔟 = 0
  · rw [h0, inv_zero, FractionalIdeal.mem_zero_iff] at hp
    rw [hp, map_zero, zero_smul]
    exact V.L.zero_mem
  refine (hV.dual _).2 fun x hx => ?_
  obtain ⟨s, t, u, hs, -, -, rfl⟩ := hH.split x hx
  have hs' : s ∈ H.𝔟 := (hH.ideal s).2 hs
  have hyx : form σ V.J H.y H.x = 1 := by rw [form_swap_herm hσ _ hV.herm, hH.xy, map_one]
  have hyι : form σ V.J H.y (H.ι *ᵥ u) = 0 := by
    rw [form_swap_herm hσ _ hV.herm, (hH.orth u).2, map_zero]
  have e : form σ V.J (σ p • H.y) (s • H.x + H.ι *ᵥ u + t • H.y) = σ (p * s) := by
    rw [GlobalTheory.VacShift.form_smul_left, GlobalTheory.VacShift.form_add_right, GlobalTheory.VacShift.form_add_right,
      GlobalTheory.VacShift.form_smul_right, GlobalTheory.VacShift.form_smul_right, hyx, hyι, hH.yy, map_mul]
    ring
  have hmem : p * s ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    have h2 := FractionalIdeal.mul_mem_mul hp hs'
    rwa [inv_mul_cancel₀ h0] at h2
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hmem
  rw [e, ← ho]
  exact (o.isIntegral_coe).map (σ : E →+* E).toIntAlgHom

theorem mem_conjI_iff_span (σ : E →ₐ[F] E) (𝔠 : FractionalIdeal (𝓞 E)⁰ E) (q : E) :
    q ∈ conjI σ 𝔠 ↔ q ∈ Submodule.span (𝓞 E) (σ '' (𝔠 : Set E)) := by
  rw [conjI, FractionalIdeal.mem_extended_iff]
  have h : (IsLocalization.map E (conjO σ) (conjO_le σ) : E →+* E) = (σ : E →+* E) :=
    IsLocalization.ringHom_ext (𝓞 E)⁰ (RingHom.ext fun x => by
      simp [IsLocalization.map_eq, conjO, RingOfIntegers.mapRingHom_apply])
  have h' : (IsLocalization.map E (conjO σ) (conjO_le σ) : E → E) = σ := congrArg DFunLike.coe h
  rw [h']

theorem compFin_cA (σ : E →ₐ[F] E) (v : Pl F) (x : AE F E) :
    compFin F E v (cA σ x) = TensorProduct.map LinearMap.id σ.toLinearMap (compFin F E v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

variable {σ : E →ₐ[F] E}

theorem incM_add {n d : ℕ} (A C : Matrix (Fin n) (Fin d) E) : incM F (A + C) = incM F A + incM F C := by
  ext i j
  simp [incM]

theorem incM_zero {n d : ℕ} : incM F (0 : Matrix (Fin n) (Fin d) E) = 0 := by
  ext i j
  simp [incM]

theorem lift_smul_mem (hσ : ∀ x, σ (σ x) = x) {B : Base F E} {n d n₁ d₁ : ℕ} {V : Spc F E n} {W : Spc F E d}
    {V₁ : Spc F E n₁} {W₁ : Spc F E d₁} {H : Plane E n n₁} {H' : Plane E d d₁} {i₀ i₁ j₀ j₁ r s : ℕ}
    (hV : V.IsHerm σ B r s) (hH : H.IsAdapted σ B V V₁ j₀ j₁) (hH' : H'.IsAdapted σ B W W₁ i₀ i₁) (v : Pl F)
    {z : Fv F v ⊗[F] E} (hz : z ∈ locId v (H.𝔟⁻¹ * conjI σ H'.𝔟)) :
    ((GlobalTheory.LatVac.liftV v).rTensor E (TensorProduct.map LinearMap.id σ.toLinearMap z)) •
      Matrix.vecMulVec (incV F H.y) (incV F H'.x) ∈ latAtV V W v := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, x, hx, rfl⟩ := hy
    rw [TensorProduct.map_tmul, LinearMap.rTensor_tmul]
    have claim : ∀ q ∈ Submodule.span (𝓞 E) (σ '' (H'.𝔟 : Set E)), ∀ p ∈ H.𝔟⁻¹,
        GlobalTheory.LatVac.liftV v c • incM F (Matrix.vecMulVec (σ (p * q) • H.y) H'.x) ∈ latAtV V W v := by
      intro q hq
      induction hq using Submodule.span_induction with
      | mem q hq =>
        obtain ⟨c', hc', rfl⟩ := hq
        intro p hp
        have e : Matrix.vecMulVec (σ (p * σ c') • H.y) H'.x = Matrix.vecMulVec (σ p • H.y) (c' • H'.x) := by
          ext i j
          simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, map_mul, hσ]
          ring
        rw [e]
        exact AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.at_liftV v c, by rw [GlobalTheory.LatVac.evFin_liftV]; exact hc,
          _, smul_y_mem hσ hV hH hp, _, (hH'.ideal c').1 hc', rfl⟩
      | zero =>
        intro p _
        rw [mul_zero, map_zero, zero_smul, Matrix.zero_vecMulVec, incM_zero, smul_zero]
        exact zero_mem _
      | add x y _ _ hx hy =>
        intro p hp
        rw [mul_add, map_add, add_smul, Matrix.add_vecMulVec, incM_add, smul_add]
        exact add_mem (hx p hp) (hy p hp)
      | smul o x _ hx =>
        intro p hp
        have e : p * (o • x) = (o • p) * x := by rw [mul_smul_comm, smul_mul_assoc]
        rw [e]
        exact hx _ (Submodule.smul_mem ((H.𝔟⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) o hp)
    have key : ∀ x ∈ H.𝔟⁻¹ * conjI σ H'.𝔟,
        GlobalTheory.LatVac.liftV v c • incM F (Matrix.vecMulVec (σ x • H.y) H'.x) ∈ latAtV V W v := by
      intro x hx
      refine FractionalIdeal.mul_induction_on hx (fun p hp q hq => ?_) (fun p q hp hq => ?_)
      · rw [mul_comm]
        rw [mem_conjI_iff_span] at hq
        rw [mul_comm]
        exact claim q hq p hp
      · rw [map_add, add_smul, Matrix.add_vecMulVec, incM_add, smul_add]
        exact add_mem hp hq
    have e : (GlobalTheory.LatVac.liftV v c ⊗ₜ[F] σ x) • Matrix.vecMulVec (incV F H.y) (incV F H'.x) =
        GlobalTheory.LatVac.liftV v c • incM F (Matrix.vecMulVec (σ x • H.y) H'.x) := by
      ext i j
      simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, incV, incM, Matrix.map_apply, inclR,
        Pi.smul_apply, smul_eq_mul, RingHom.coe_coe, AlgHom.toRingHom_eq_coe,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul',
        mul_one]
      congr 1
      ring
    rw [LinearMap.id_apply, AlgHom.toLinearMap_apply, e]
    exact key x hx
  | zero => rw [map_zero, map_zero, zero_smul]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, map_add, add_smul]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, map_neg, neg_smul]; exact neg_mem hx

theorem vac_fixed : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {a b : ℕ} (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), B.IsGood σ → G.IsGood B → CfgB B G G₁ H H' →
    ∀ (v : Pl F) (l : (AE F E)ˣ), l ∈ idelesAt E (evFin F v) →
      compFin F E v (l : AE F E) ∈ locId v (H.𝔟⁻¹ * conjI σ H'.𝔟) →
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (shiftB σ H H' l)) (G.M'.vac v) = G.M'.vac v := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hB hG hC v l hl hloc
  have hσ := GlobalTheory.VacShift.sigma_invol hB.cm
  set u := shiftB σ H H' l with hu
  have hpart : partFin v u = ((GlobalTheory.LatVac.liftV v).rTensor E
      (TensorProduct.map LinearMap.id σ.toLinearMap (compFin F E v l.1))) •
      Matrix.vecMulVec (incV F H.y) (incV F H'.x) := by
    rw [partFin, hu, smul_shiftB, map_smul, GlobalTheory.VacShift.liftV_one_smul_eq, compFin_cA]
  have hγ : partFin v u ∈ latAtV G.V' G.W v := by
    rw [hpart]
    exact lift_smul_mem hσ hG.hV' hC.hH hC.hH' v hloc
  obtain ⟨hSB, -, θ, -, hvac⟩ := hG.hM'.vac v
  have h1 := hvac _ hγ
  have hz : symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) (partFin v u)
      (partFin v u) = 0 := by
    rw [hpart]
    exact GlobalTheory.VacShift.symp_shift_zero σ _ _ hC.hH'.xx _ _ _
  rw [hz, mul_zero, AddChar.map_zero_eq_one, one_smul] at h1
  have h2 := GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v _ (at_partFin v u) (G.M'.vac v)
  have e : GlobalTheory.LatVac.locCo G.M'.co v (partFin v u) = GlobalTheory.LatVac.locCo G.M'.co v u := by
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
      simp [GlobalTheory.LatVac.locCo, partFin, GlobalTheory.LatVac.evFin_liftV]
  rw [e] at h2
  exact GlobalTheory.TensUniq.eq_of_tens_eq v (G.M'.vac v) _ _ hSB fun r hr => (h2 r hr).symm.trans (h1 r hr)

end GlobalTheory.VacShiftB
