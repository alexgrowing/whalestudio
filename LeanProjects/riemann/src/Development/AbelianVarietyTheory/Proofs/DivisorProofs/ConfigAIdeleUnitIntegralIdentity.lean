import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneFormMemInverseDifferentStatement

noncomputable section

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open scoped GlobalTheory.VacAny

namespace GlobalTheory.SuppOut

section General
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α β : Type} [Fintype α] [Fintype β]

theorem hTens_vecMulVec (JA : Matrix α α A) (JB : Matrix β β A) (x : Matrix α β A) (p : α → A) (q : β → A) :
    hTens c JA JB x (Matrix.vecMulVec p q) =
      ∑ i, ∑ k, JA i k * c (p k) * (x *ᵥ (JB *ᵥ fun l => c (q l))) i := by
  unfold hTens
  simp only [Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem symp_proj (σ : E →ₐ[F] E) {n d : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (w w' : Fin d → E) (hw : form σ JW w w' = 1) (ξ a : AE F E) (p : Fin n → AE F E)
    (γ : Matrix (Fin n) (Fin d) (AE F E)) :
    symp (R := AF F) (cA σ) ξ (incM F JX) (incM F JW) (γ * incM F (Matrix.vecMulVec (JW *ᵥ fun i => σ (w' i)) w))
        (a • Matrix.vecMulVec p (incV F w')) =
      symp (R := AF F) (cA σ) ξ (incM F JX) (incM F JW) γ (a • Matrix.vecMulVec p (incV F w')) := by
  have hU : (incM F JW *ᵥ fun l => cA σ (incV F w' l)) = incV F (JW *ᵥ fun i => σ (w' i)) := by
    ext i
    simp only [incV, incM, Matrix.mulVec, dotProduct, Matrix.map_apply, cA_inclR, map_sum, map_mul]
  have hQ : incM F (Matrix.vecMulVec (JW *ᵥ fun i => σ (w' i)) w) *ᵥ incV F (JW *ᵥ fun i => σ (w' i)) =
      incV F (JW *ᵥ fun i => σ (w' i)) := by
    ext i
    have h1 : (∑ j, inclR (F := F) (AF F) (w j) * inclR (F := F) (AF F) ((JW *ᵥ fun i => σ (w' i)) j)) = 1 := by
      have h := congrArg (inclR (F := F) (AF F)) hw
      rw [map_one] at h
      rw [← h, form, dotProduct, map_sum]; simp only [map_mul]
    generalize (JW *ᵥ fun i => σ (w' i)) = u at h1 ⊢
    simp only [incV, incM, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.vecMulVec_apply, map_mul]
    simp_rw [mul_assoc, ← Finset.mul_sum, h1, mul_one]
  have hs : a • Matrix.vecMulVec p (incV F w') = Matrix.vecMulVec (a • p) (incV F w') := by
    ext i j; simp [Matrix.vecMulVec_apply, smul_eq_mul, mul_assoc]
  rw [hs]
  unfold symp
  rw [hTens_vecMulVec, hTens_vecMulVec, hU, ← Matrix.mulVec_mulVec, hQ]

theorem symp_antisymm [NumberField E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n d : ℕ} (JX : Matrix (Fin n) (Fin n) E)
    (JW : Matrix (Fin d) (Fin d) E) (hX : ∀ i j, σ (JX j i) = JX i j) (hW : ∀ i j, σ (JW j i) = -JW i j)
    (x y : Matrix (Fin n) (Fin d) (AE F E)) :
    symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW) x y =
      -symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW) y x := by
  have hc : ∀ z, cA σ (cA σ z) = z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [cA, hσ]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hA : ∀ i j, cA σ (incM F JX j i) = incM F JX i j := fun i j => by
    simp only [incM, Matrix.map_apply, cA_inclR, hX]
  have hB : ∀ i j, cA σ (incM F JW j i) = -incM F JW i j := fun i j => by
    simp only [incM, Matrix.map_apply, cA_inclR, hW, map_neg]
  unfold symp
  rw [neg_one_mul, neg_one_mul, map_neg, map_neg, neg_neg,
    ← GlobalTheory.VacCocycle.trace_conj (cA σ) hc (hTens (cA σ) (incM F JX) (incM F JW) y x),
    GlobalTheory.VacCocycle.conj_hTens (cA σ) hc hA hB, map_neg]

end GlobalTheory.SuppOut

namespace GlobalTheory.SuppOut

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem form_split_y (σ : E →ₐ[F] E) (B : Base F E) {n n₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    {i₀ i₁ : ℕ} (hH : Plane.IsAdapted σ B H Y Y₁ i₀ i₁) (s t : E) (u : Fin n₁ → E) :
    form σ Y.J (s • H.x + H.ι *ᵥ u + t • H.y) H.y = s := by
  have hadd : ∀ a b : Fin n → E, form σ Y.J (a + b) H.y = form σ Y.J a H.y + form σ Y.J b H.y := fun a b => by
    simp only [form, add_dotProduct]
  have hsm : ∀ (c : E) (a : Fin n → E), form σ Y.J (c • a) H.y = c * form σ Y.J a H.y := fun c a => by
    simp only [form, smul_dotProduct, smul_eq_mul]
  rw [hadd, hadd, hsm, hsm, hH.xy, (hH.orth u).2, hH.yy]
  ring

theorem form_mem_ideal (σ : E →ₐ[F] E) (B : Base F E) {n n₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    {i₀ i₁ : ℕ} (hH : Plane.IsAdapted σ B H Y Y₁ i₀ i₁) {z : Fin n → E} (hz : z ∈ Y.L) :
    form σ Y.J z H.y • H.x ∈ Y.L ∧ form σ Y.J z H.y ∈ H.𝔟 := by
  obtain ⟨s, t, u, hs, -, -, rfl⟩ := hH.split z hz
  rw [form_split_y σ B hH]
  exact ⟨hs, (hH.ideal s).2 hs⟩

theorem proj_mem [NumberField E] (σ : E →ₐ[F] E) (B : Base F E) {n d d₁ : ℕ} (X : Spc F E n) (W : Spc F E d)
    (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (hH' : Plane.IsAdapted σ B H' W W₁ i₀ i₁) (v : Pl F)
    (γ : Matrix (Fin n) (Fin d) (AE F E)) (hγ : γ ∈ latAtV X W v) :
    γ * incM F (Matrix.vecMulVec (W.J *ᵥ fun i => σ (H'.y i)) H'.x) ∈ latAtV X W v := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hav, x, hx, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hav, x, hx, form σ W.J y H'.y • H'.x, (form_mem_ideal σ B hH' hy).1, ?_⟩
    rw [Matrix.smul_mul, incM, incM, incM, ← Matrix.map_mul]
    congr 2
    ext i j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, form, dotProduct]
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  | zero => rw [Matrix.zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.neg_mul]; exact neg_mem hx

end GlobalTheory.SuppOut

namespace GlobalTheory.SuppOut

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem coef_mem [NumberField E] (σ : E →ₐ[F] E) (B : Base F E) {n n₁ d : ℕ} (X : Spc F E n) (X₁ : Spc F E n₁)
    (W : Spc F E d) (H : Plane E n n₁) (w : Fin d → E) (i₀ i₁ : ℕ) (hH : Plane.IsAdapted σ B H X X₁ i₀ i₁)
    (I : FractionalIdeal (𝓞 E)⁰ E) (hI : ∀ y ∈ W.L, form σ W.J y w ∈ I) (v : Pl F)
    (z : Matrix (Fin n) (Fin d) (AE F E)) (hz : z ∈ latAtV X W v) :
    compFin F E v (∑ i, ∑ j, z i j * incV F (X.J *ᵥ fun k => σ (H.y k)) i * incV F (W.J *ᵥ fun k => σ (w k)) j) ∈
      GlobalTheory.SnMass.locId v (H.𝔟 * I) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hav, x, hx, y, hy, rfl⟩ := hz
    have hform : ∀ {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (x y : Fin m → E),
        inclR (F := F) (AF F) (form σ J x y) = ∑ i, incV F x i * incV F (J *ᵥ fun k => σ (y k)) i := by
      intro m J x y
      simp only [form, dotProduct, map_sum, map_mul, incV]
    have he : (∑ i, ∑ j, (a • incM F (Matrix.vecMulVec x y)) i j * incV F (X.J *ᵥ fun k => σ (H.y k)) i *
        incV F (W.J *ᵥ fun k => σ (w k)) j) =
        a ⊗ₜ[F] (form σ X.J x H.y * form σ W.J y w) := by
      have h1 : a ⊗ₜ[F] (form σ X.J x H.y * form σ W.J y w) =
          a • (inclR (F := F) (AF F) (form σ X.J x H.y) * inclR (F := F) (AF F) (form σ W.J y w)) := by
        rw [← map_mul]
        change a ⊗ₜ[F] _ = a • ((1 : AF F) ⊗ₜ[F] _)
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1, hform, hform, Finset.sum_mul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [incM, incV, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, map_mul, smul_mul_assoc,
        Algebra.smul_def]
      ring
    rw [he]
    change Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) (a ⊗ₜ[F] _) ∈ _
    rw [Algebra.TensorProduct.map_tmul]
    exact AddSubgroup.subset_closure ⟨_, hav, _, FractionalIdeal.mul_mem_mul (form_mem_ideal σ B hH hx).2 (hI y hy), rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add]
    exact add_mem hx hy
  | neg x _ hx =>
    simp only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, map_neg]
    exact neg_mem hx

end GlobalTheory.SuppOut

namespace GlobalTheory.SuppOut

theorem exists_lat_pair_ne_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) {b a' : ℕ}
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')) (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → CfgA B G G₁ H H' →
    ∀ (v : Pl F) (l : (AE F E)ˣ), l ∈ idelesAt E (evFin F v) →
      (unitFin F E v l : Fv F v ⊗[F] E) ∉ GlobalTheory.SnMass.locId v (idA σ H.𝔟 H'.𝔟) →
      ∃ γ : Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E), At (evFin F v) γ ∧ γ ∈ iso0 (F := F) (b + 2) H' ∧
        γ ∈ latAtV G.V G.W v ∧
        GlobalTheory.LatVac.psiAt B.ψ v (evFin F v (symp (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) γ (shiftA H H' l))) ≠ 1 := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' hT hC v l _hl hnot
  by_contra hall
  push_neg at hall
  have hB := hT.base
  have hσ : ∀ x : E, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  set s := shiftA H H' l with hs
  set e : AF F := GlobalTheory.LatVac.liftV v 1 with he
  have heat : At (evFin F v) e := GlobalTheory.LatVac.at_liftV v 1
  have hev : evFin F v e = 1 := GlobalTheory.LatVac.evFin_liftV v 1
  have hsat : At (evFin F v) (e • s) := fun u hu => by
    rw [smul_smul, ← smul_eq_mul u e, heat u hu, zero_smul]
  have hsv : e • s ∈ latAtV G.V G.W v := by
    rw [GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B _ _ G.V G.W _ _ _ _ hB hT.geo.hV hT.geo.hW v _ hsat]
    intro γ hγ
    set γ' := γ * incM F (Matrix.vecMulVec (G.W.J *ᵥ fun i => σ (H'.y i)) H'.x) with hγ'
    have hγ'L : γ' ∈ latAtV G.V G.W v := proj_mem σ B G.V G.W G₁.W H' 0 (b + 1) hC.hH' v γ hγ
    have hγ'at : At (evFin F v) γ' := (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).1 γ' hγ'L
    have hγ'iso : γ' ∈ iso0 (F := F) (b + 2) H' := by
      have key : ∀ u w : Fin (b + 2 + a') → E,
          γ * incM F (Matrix.vecMulVec u w) = Matrix.vecMulVec (γ *ᵥ incV F u) (incV F w) := by
        intro u w
        ext i j
        simp only [incM, incV, Matrix.mul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Matrix.mulVec,
          dotProduct, Finset.sum_mul, map_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      exact ⟨_, key _ _⟩
    have h1 := hall γ' hγ'at hγ'iso hγ'L
    have h2 : symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) (e • s) γ =
        -(e * symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) γ' s) := by
      have := GlobalTheory.LatVac.symp_smul_smul σ (incM F G.V.J) (incM F G.W.J) (-1) e 1 s γ
      rw [one_smul, mul_one] at this
      rw [this, symp_antisymm σ hσ G.V.J G.W.J hT.geo.hV.herm hT.geo.hW.skew s γ, hs, shiftA,
        symp_proj σ G.V.J G.W.J H'.x H'.y hC.hH'.xy]
      ring
    have hat2 : At (evFin F v) (e * symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) γ' s) :=
      fun u hu => by
        rw [smul_eq_mul, ← mul_assoc, ← smul_eq_mul u e, heat u hu, zero_mul]
    rw [h2, AddChar.map_neg_eq_inv, GlobalTheory.VacIndic.psi_of_at _ hat2, map_mul, hev, one_mul]
    rw [← GlobalTheory.LatVac.psiAt_apply, h1, inv_one]
  have hc := coef_mem σ B G.V G₁.V G.W H H'.x 0 (b + 1) hC.hH _ (GlobalTheory.T.adapted_plane_form_mem_inverse_different σ B G.W G₁.W H' hC.hH' hT.geo.hW) v _ hsv
  have hid : idA σ H.𝔟 H'.𝔟 = H.𝔟 * ((conjI σ H'.𝔟)⁻¹ * (diffE E)⁻¹) := by
    rw [idA, mul_assoc]
  rw [hid] at hnot

  have hf1 : form σ G.V.J H.x H.y = 1 := hC.hH.xy
  have hf2 : form σ G.W.J H'.y H'.x = -1 := by
    have h := hC.hH'.xy
    have hsk := hT.geo.hW.skew
    have : σ (form σ G.W.J H'.x H'.y) = -form σ G.W.J H'.y H'.x := by
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hsk]; ring
    rw [h, map_one] at this
    linear_combination this
  have hΦ : (∑ i, ∑ j, (e • s) i j * incV F (G.V.J *ᵥ fun k => σ (H.y k)) i *
      incV F (G.W.J *ᵥ fun k => σ (H'.x k)) j) = e • (l : AE F E) * inclR (F := F) (AF F) (form σ G.V.J H.x H.y) *
        inclR (F := F) (AF F) (form σ G.W.J H'.y H'.x) := by
    have hform : ∀ {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (x y : Fin m → E),
        inclR (F := F) (AF F) (form σ J x y) = ∑ i, incV F x i * incV F (J *ᵥ fun k => σ (y k)) i := by
      intro m J x y
      simp only [form, dotProduct, map_sum, map_mul, incV]
    rw [hform, hform, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hs, shiftA, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, Algebra.smul_def]
    ring
  rw [hΦ, hf1, hf2, map_one, map_neg, map_one, mul_one, mul_neg_one, map_neg] at hc
  have hce : compFin F E v (e • (l : AE F E)) = (unitFin F E v l : Fv F v ⊗[F] E) := by
    rw [Algebra.smul_def, map_mul]
    have : compFin F E v (algebraMap (AF F) (AE F E) e) = 1 := by
      change Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) (e ⊗ₜ[F] (1 : E)) = 1
      rw [Algebra.TensorProduct.map_tmul, hev]; rfl
    rw [this, one_mul]; rfl
  rw [hce] at hc
  exact hnot (by simpa using neg_mem hc)

end GlobalTheory.SuppOut
