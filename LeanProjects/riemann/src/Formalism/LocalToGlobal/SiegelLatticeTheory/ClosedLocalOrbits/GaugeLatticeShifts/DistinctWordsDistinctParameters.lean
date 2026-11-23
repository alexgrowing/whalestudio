import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdBlocks
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData

noncomputable section

open scoped InnerProductSpace ComplexConjugate

namespace Formalism.L2.SG.Pf.IdBlocks2.TensIrr

section Schur

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

theorem form_scalar [FiniteDimensional ℂ U] [Nontrivial U] (A : Set (U →ₗ[ℂ] U))
    (hiso : ∀ a ∈ A, ∀ p q, ⟪a p, a q⟫_ℂ = ⟪p, q⟫_ℂ) (hsurj : ∀ a ∈ A, Function.Surjective a)
    (hirr : ∀ S : Submodule ℂ U, (∀ a ∈ A, ∀ x ∈ S, a x ∈ S) → S = ⊥ ∨ S = ⊤)
    (M : U →ₗ[ℂ] U) (hM : ∀ a ∈ A, ∀ p q, ⟪a p, M (a q)⟫_ℂ = ⟪p, M q⟫_ℂ) :
    ∃ c : ℂ, ∀ x, M x = c • x := by
  have hcomm : ∀ a ∈ A, ∀ q, M (a q) = a (M q) := by
    intro a ha q
    apply ext_inner_left ℂ
    intro y
    obtain ⟨p, rfl⟩ := hsurj a ha y
    rw [hM a ha p q, hiso a ha p (M q)]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue M
  refine ⟨c, ?_⟩
  have hS : ∀ a ∈ A, ∀ x ∈ Module.End.eigenspace M c, a x ∈ Module.End.eigenspace M c := by
    intro a ha x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [hcomm a ha x, hx, map_smul]
  rcases hirr (Module.End.eigenspace M c) hS with h | h
  · exact absurd h (Module.End.hasEigenvalue_iff.mp hc)
  · intro x
    have hx : x ∈ Module.End.eigenspace M c := by rw [h]; exact Submodule.mem_top
    exact Module.End.mem_eigenspace_iff.mp hx

end Schur

section Tens

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℂ (V i)]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem eq_of_inner_tens (tens : (∀ i, V i) → W) (hspan : Submodule.span ℂ (Set.range tens) = ⊤)
    {a b : W} (h : ∀ z, ⟪tens z, a⟫_ℂ = ⟪tens z, b⟫_ℂ) : a = b := by
  have h0 : ∀ w ∈ Submodule.span ℂ (Set.range tens), ⟪w, a - b⟫_ℂ = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      rw [inner_sub_right, h z, sub_self]
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
  have h1 := h0 (a - b) (by rw [hspan]; exact Submodule.mem_top)
  rw [inner_self_eq_zero, sub_eq_zero] at h1
  exact h1

variable (tens : (∀ i, V i) → W) (hin : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
  (hspan : Submodule.span ℂ (Set.range tens) = ⊤)

include hin in

theorem inner_tens_update (z x : ∀ i, V i) (i : ι) (p : V i) :
    ⟪tens z, tens (Function.update x i p)⟫_ℂ =
      ⟪z i, p⟫_ℂ * ∏ j ∈ Finset.univ \ {i}, ⟪z j, x j⟫_ℂ := by
  rw [hin, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [Function.update_apply, hji]

include hin hspan in

theorem tens_update_add (x : ∀ i, V i) (i : ι) (p q : V i) :
    tens (Function.update x i (p + q)) = tens (Function.update x i p) + tens (Function.update x i q) := by
  apply eq_of_inner_tens tens hspan
  intro z
  rw [inner_add_right, inner_tens_update tens hin, inner_tens_update tens hin, inner_tens_update tens hin,
    inner_add_right, add_mul]

include hin hspan in

theorem tens_update_smul (x : ∀ i, V i) (i : ι) (c : ℂ) (p : V i) :
    tens (Function.update x i (c • p)) = c • tens (Function.update x i p) := by
  apply eq_of_inner_tens tens hspan
  intro z
  rw [inner_smul_right, inner_tens_update tens hin, inner_tens_update tens hin, inner_smul_right, mul_assoc]

def intersection_update_fsHerm_neg_one (x : ∀ i, V i) (i : ι) : V i →ₗ[ℂ] W where
  toFun p := tens (Function.update x i p)
  map_add' p q := tens_update_add tens hin hspan x i p q
  map_smul' c p := tens_update_smul tens hin hspan x i c p

def fill (e x : ∀ i, V i) (s : Finset ι) : ∀ i, V i := fun i => if i ∈ s then e i else x i

include hin hspan in

theorem commutant_scalar [FiniteDimensional ℂ W] [∀ i, FiniteDimensional ℂ (V i)] [∀ i, Nontrivial (V i)]
    {G : Type*} (H : Set G) (π : G → (W →ₗ[ℂ] W)) (hiso : ∀ s ∈ H, ∀ p q, ⟪π s p, π s q⟫_ℂ = ⟪p, q⟫_ℂ)
    (A : ∀ i, Set (V i →ₗ[ℂ] V i)) (hAiso : ∀ i, ∀ a ∈ A i, ∀ p q, ⟪a p, a q⟫_ℂ = ⟪p, q⟫_ℂ)
    (hAsurj : ∀ i, ∀ a ∈ A i, Function.Surjective a)
    (hAirr : ∀ i, ∀ S : Submodule ℂ (V i), (∀ a ∈ A i, ∀ x ∈ S, a x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hlift : ∀ i, ∀ a ∈ A i, ∃ s ∈ H, ∀ x, π s (tens x) = tens (Function.update x i (a (x i))))
    (T : W →ₗ[ℂ] W) (hT : ∀ s ∈ H, ∀ w, T (π s w) = π s (T w)) :
    ∃ c : ℂ, ∀ w, T w = c • w := by
  classical
  have hunit : ∀ i, ∃ e : V i, ⟪e, e⟫_ℂ = 1 := by
    intro i
    obtain ⟨e, he⟩ := exists_norm_eq (V i) (zero_le_one : (0 : ℝ) ≤ 1)
    exact ⟨e, by rw [inner_self_eq_norm_sq_to_K, he]; simp⟩
  choose e he using hunit
  have hinvar : ∀ i, ∀ a ∈ A i, ∀ z x : ∀ i, V i,
      ⟪tens (Function.update z i (a (z i))), T (tens (Function.update x i (a (x i))))⟫_ℂ =
        ⟪tens z, T (tens x)⟫_ℂ := by
    intro i a ha z x
    obtain ⟨s, hs, hsx⟩ := hlift i a ha
    rw [← hsx z, ← hsx x, hT s hs, hiso s hs]
  have hstep : ∀ (i : ι) (z x : ∀ i, V i),
      ⟪tens z, T (tens x)⟫_ℂ = ⟪z i, x i⟫_ℂ *
        ⟪tens (Function.update z i (e i)), T (tens (Function.update x i (e i)))⟫_ℂ := by
    intro i z x
    have hMinner : ∀ p q, ⟪p, (LinearMap.adjoint (intersection_update_fsHerm_neg_one tens hin hspan z i) ∘ₗ T ∘ₗ intersection_update_fsHerm_neg_one tens hin hspan x i) q⟫_ℂ =
        ⟪tens (Function.update z i p), T (tens (Function.update x i q))⟫_ℂ := by
      intro p q
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
      rfl
    obtain ⟨κ, hκ⟩ := form_scalar (A i) (hAiso i) (hAsurj i) (hAirr i)
      (LinearMap.adjoint (intersection_update_fsHerm_neg_one tens hin hspan z i) ∘ₗ T ∘ₗ intersection_update_fsHerm_neg_one tens hin hspan x i) (by
        intro a ha p q
        rw [hMinner, hMinner]
        have h1 := hinvar i a ha (Function.update z i p) (Function.update x i q)
        simpa using h1)
    have hκ' : ∀ p q, ⟪tens (Function.update z i p), T (tens (Function.update x i q))⟫_ℂ = κ * ⟪p, q⟫_ℂ := by
      intro p q
      rw [← hMinner, hκ, inner_smul_right]
    have h1 := hκ' (z i) (x i)
    simp only [Function.update_eq_self] at h1
    rw [h1, hκ' (e i) (e i), he i, mul_one, mul_comm]
  have hfill : ∀ s : Finset ι, ∀ z x : ∀ i, V i,
      ⟪tens z, T (tens x)⟫_ℂ = (∏ j ∈ s, ⟪z j, x j⟫_ℂ) * ⟪tens (fill e z s), T (tens (fill e x s))⟫_ℂ := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro z x
      have hz : fill e z ∅ = z := funext fun i => by simp [fill]
      have hx : fill e x ∅ = x := funext fun i => by simp [fill]
      rw [hz, hx, Finset.prod_empty, one_mul]
    · intro j t hj ih z x
      rw [ih z x, hstep j (fill e z t) (fill e x t), Finset.prod_insert hj]
      have hz : Function.update (fill e z t) j (e j) = fill e z (insert j t) := by
        funext k
        by_cases hk : k = j
        · subst hk; simp [fill]
        · simp [fill, Function.update_apply, hk]
      have hx : Function.update (fill e x t) j (e j) = fill e x (insert j t) := by
        funext k
        by_cases hk : k = j
        · subst hk; simp [fill]
        · simp [fill, Function.update_apply, hk]
      have hzj : fill e z t j = z j := by simp [fill, hj]
      have hxj : fill e x t j = x j := by simp [fill, hj]
      rw [hz, hx, hzj, hxj]
      ring
  refine ⟨⟪tens e, T (tens e)⟫_ℂ, fun w => ?_⟩
  have hT' : T = (⟪tens e, T (tens e)⟫_ℂ) • LinearMap.id := by
    apply LinearMap.ext_on_range hspan
    intro x
    apply eq_of_inner_tens tens hspan
    intro z
    have hu : fill e z Finset.univ = e := funext fun i => by simp [fill]
    have hu' : fill e x Finset.univ = e := funext fun i => by simp [fill]
    rw [hfill Finset.univ z x, hu, hu', LinearMap.smul_apply, LinearMap.id_apply, inner_smul_right, hin]
    ring
  have h2 := LinearMap.congr_fun hT' w
  rw [LinearMap.smul_apply, LinearMap.id_apply] at h2
  exact h2

include hin hspan in

theorem tens_irr [FiniteDimensional ℂ W] [∀ i, FiniteDimensional ℂ (V i)] [∀ i, Nontrivial (V i)]
    {G : Type*} (H : Set G) (π : G → (W →ₗ[ℂ] W)) (hiso : ∀ s ∈ H, ∀ p q, ⟪π s p, π s q⟫_ℂ = ⟪p, q⟫_ℂ)
    (hinv : ∀ s ∈ H, ∃ s' ∈ H, ∀ w, π s' (π s w) = w)
    (A : ∀ i, Set (V i →ₗ[ℂ] V i)) (hAiso : ∀ i, ∀ a ∈ A i, ∀ p q, ⟪a p, a q⟫_ℂ = ⟪p, q⟫_ℂ)
    (hAsurj : ∀ i, ∀ a ∈ A i, Function.Surjective a)
    (hAirr : ∀ i, ∀ S : Submodule ℂ (V i), (∀ a ∈ A i, ∀ x ∈ S, a x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hlift : ∀ i, ∀ a ∈ A i, ∃ s ∈ H, ∀ x, π s (tens x) = tens (Function.update x i (a (x i))))
    (S : Submodule ℂ W) (hS : ∀ s ∈ H, ∀ x ∈ S, π s x ∈ S) : S = ⊥ ∨ S = ⊤ := by
  classical
  set P : W →ₗ[ℂ] W := S.subtype ∘ₗ LinearMap.adjoint S.subtype with hPdef
  have hPin : ∀ t ∈ S, ∀ x, ⟪t, P x⟫_ℂ = ⟪t, x⟫_ℂ := by
    intro t ht x
    have h := LinearMap.adjoint_inner_right S.subtype (⟨t, ht⟩ : S) x
    rw [hPdef, LinearMap.comp_apply, Submodule.subtype_apply]
    simpa [Submodule.coe_inner] using h
  have hPmem : ∀ x, P x ∈ S := by
    intro x
    rw [hPdef, LinearMap.comp_apply, Submodule.subtype_apply]
    exact Submodule.coe_mem _
  have hchar : ∀ x a, a ∈ S → (∀ t ∈ S, ⟪t, x⟫_ℂ = ⟪t, a⟫_ℂ) → P x = a := by
    intro x a ha h
    have hd : P x - a ∈ S := S.sub_mem (hPmem x) ha
    have h0 : ⟪P x - a, P x - a⟫_ℂ = 0 := by
      rw [inner_sub_right, hPin _ hd, h _ hd, sub_self]
    rw [inner_self_eq_zero, sub_eq_zero] at h0
    exact h0
  have hP : ∀ s ∈ H, ∀ w, P (π s w) = π s (P w) := by
    intro s hs w
    obtain ⟨s', hs', hinv'⟩ := hinv s hs
    apply hchar _ _ (hS s hs _ (hPmem w))
    intro t ht
    rw [← hiso s' hs' t (π s w), hinv', ← hiso s' hs' t (π s (P w)), hinv', hPin _ (hS s' hs' t ht)]
  obtain ⟨c, hc⟩ := commutant_scalar tens hin hspan H π hiso A hAiso hAsurj hAirr hlift P hP
  by_cases hc0 : c = 0
  · left
    rw [Submodule.eq_bot_iff]
    intro t ht
    have h1 := hPin t ht t
    rw [hc, hc0, zero_smul, inner_zero_right] at h1
    exact inner_self_eq_zero.mp h1.symm
  · right
    rw [Submodule.eq_top_iff']
    intro x
    have hx : x = c⁻¹ • P x := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [hx]
    exact S.smul_mem _ (hPmem x)

end Tens

end Formalism.L2.SG.Pf.IdBlocks2.TensIrr

open Matrix

namespace Formalism.L2.SG.Pf.IdBlocks2.UkEmb

variable {n k : ℕ}

def Wm (wf : Fin k → Fin n → ℂ) : Matrix (Fin n) (Fin k) ℂ := Matrix.of fun i a => wf a i

def smat (J : Matrix (Fin n) (Fin n) ℂ) (wf : Fin k → Fin n → ℂ) (G : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  1 + Wm wf * (G - 1) * (Wm wf)ᴴ * J

theorem entry (wf : Fin k → Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (a b : Fin k) :
    ((Wm wf)ᴴ * M * Wm wf) a b = star (wf a) ⬝ᵥ (M *ᵥ wf b) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Wm, Matrix.of_apply, dotProduct, Matrix.mulVec,
    Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hswap (J : Matrix (Fin n) (Fin n) ℂ) (hJh : Jᴴ = J) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (J *ᵥ y) = star (star y ⬝ᵥ (J *ᵥ x)) := by
  have hJ : ∀ i j, star (J i j) = J j i := fun i j => by
    have h := congrFun (congrFun hJh j) i
    simpa [Matrix.conjTranspose_apply] using h
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable (J : Matrix (Fin n) (Fin n) ℂ) (wf : Fin k → Fin n → ℂ)
  (hon : ∀ a b, star (wf a) ⬝ᵥ (J *ᵥ wf b) = if a = b then 1 else 0)

include hon in
theorem ortho : (Wm wf)ᴴ * J * Wm wf = 1 := by
  ext a b
  rw [entry, hon, Matrix.one_apply]

include hon in
theorem smat_unitary (hJh : Jᴴ = J) (G : Matrix (Fin k) (Fin k) ℂ) (hG : Gᴴ * G = 1) :
    (smat J wf G)ᴴ * J * smat J wf G = J := by
  have hO : ∀ R : Matrix (Fin k) (Fin n) ℂ, (Wm wf)ᴴ * (J * (Wm wf * R)) = R := by
    intro R
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ortho J wf hon, Matrix.one_mul]
  have hsh : (smat J wf G)ᴴ = 1 + J * (Wm wf * ((Gᴴ - 1) * (Wm wf)ᴴ)) := by
    simp only [smat, Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, hJh, Matrix.mul_assoc]
  have hsq : (G - 1) + (Gᴴ - 1) + (Gᴴ - 1) * (G - 1) = 0 := by
    have e : (G - 1) + (Gᴴ - 1) + (Gᴴ - 1) * (G - 1) = Gᴴ * G - 1 := by noncomm_ring
    rw [e, hG, sub_self]
  calc (smat J wf G)ᴴ * J * smat J wf G
      = J + J * (Wm wf * (((G - 1) + (Gᴴ - 1) + (Gᴴ - 1) * (G - 1)) * ((Wm wf)ᴴ * J))) := by
        rw [hsh]
        simp only [smat, Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, hO]
        abel
    _ = J := by rw [hsq]; simp

include hon in
theorem smat_fix (G : Matrix (Fin k) (Fin k) ℂ) (x : Fin n → ℂ) (hx : ∀ a, star (wf a) ⬝ᵥ (J *ᵥ x) = 0) :
    smat J wf G *ᵥ x = x := by
  have h0 : (Wm wf)ᴴ *ᵥ (J *ᵥ x) = 0 := by
    funext a
    simp only [Pi.zero_apply]
    rw [← hx a]
    simp [Matrix.mulVec, dotProduct, Wm, Matrix.conjTranspose_apply]
  simp only [smat, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero, add_zero]

include hon in
theorem smat_mat (G : Matrix (Fin k) (Fin k) ℂ) (a b : Fin k) :
    star (wf a) ⬝ᵥ (J *ᵥ (smat J wf G *ᵥ wf b)) = G a b := by
  have hO1 : (Wm wf)ᴴ * (J * Wm wf) = 1 := by rw [← Matrix.mul_assoc, ortho J wf hon]
  have hO2 : ∀ R : Matrix (Fin k) (Fin k) ℂ, (Wm wf)ᴴ * (J * (Wm wf * R)) = R := by
    intro R
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ortho J wf hon, Matrix.one_mul]
  have e := entry wf (J * smat J wf G) a b
  rw [← Matrix.mulVec_mulVec] at e
  rw [← e]
  have h2 : (Wm wf)ᴴ * (J * smat J wf G) * Wm wf = G := by
    simp only [smat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, hO1, hO2]
    abel
  rw [h2]

include hon in
theorem one_mat (a b : Fin k) : star (wf a) ⬝ᵥ (J *ᵥ ((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ wf b)) =
    (1 : Matrix (Fin k) (Fin k) ℂ) a b := by
  rw [Matrix.one_mulVec, hon, Matrix.one_apply]

theorem smat_inv (hJ2 : J * J = 1) (hJh : Jᴴ = J) (G : Matrix (Fin k) (Fin k) ℂ) (hG : Gᴴ * G = 1)
    (hon : ∀ a b, star (wf a) ⬝ᵥ (J *ᵥ wf b) = if a = b then 1 else 0) :
    (J * (smat J wf G)ᴴ * J) * smat J wf G = 1 := by
  have h := smat_unitary J wf hon hJh G hG
  calc (J * (smat J wf G)ᴴ * J) * smat J wf G = J * ((smat J wf G)ᴴ * J * smat J wf G) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, hJ2]

end Formalism.L2.SG.Pf.IdBlocks2.UkEmb

open scoped InnerProductSpace ComplexConjugate
open Matrix Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.IdBlocks2.HW

section CDom

theorem cdom_antisymm {k : ℕ} {μ Λ : Fin k → ℝ} (h1 : CDom (allPos k) μ Λ) (h2 : CDom (allPos k) Λ μ) : μ = Λ := by
  obtain ⟨c, hc, hΛ⟩ := h1
  obtain ⟨c', hc', hμ⟩ := h2
  have hfS : ∀ d : Fin k → Fin k → ℕ,
      (∑ i : Fin k, ((i : ℕ) : ℝ) * (∑ a, ∑ b, (d a b : ℝ) • Formalism.REAL.root a b) i) =
        ∑ a, ∑ b, (d a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) := by
    intro d
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Formalism.REAL.root, Pi.sub_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Pi.single_apply, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hneg : ∀ d : Fin k → Fin k → ℕ, (∀ a b, d a b ≠ 0 → a < b ∧ allPos k a = allPos k b) →
      ∀ a b, (d a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ 0 := by
    intro d hd a b
    by_cases h0 : d a b = 0
    · simp [h0]
    · have hab := (hd a b h0).1
      have hlt : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
  have e1 := hfS c
  have e2 := hfS c'
  rw [← hΛ] at e1
  rw [← hμ] at e2
  have hsum : (∑ i : Fin k, ((i : ℕ) : ℝ) * (Λ - μ) i) = -(∑ i : Fin k, ((i : ℕ) : ℝ) * (μ - Λ) i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply]
    ring
  have hS1 : ∑ a, ∑ b, (c a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ 0 :=
    Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => hneg c hc a b
  have hS2 : ∑ a, ∑ b, (c' a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ 0 :=
    Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => hneg c' hc' a b
  have hzero : ∑ a, ∑ b, (c a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) = 0 := by linarith
  have hc0 : ∀ a b, c a b = 0 := by
    intro a b
    by_contra h0
    have hab := (hc a b h0).1
    have hlt : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
    have hpos : (0 : ℝ) < c a b := by exact_mod_cast Nat.pos_of_ne_zero h0
    have hinner := (Finset.sum_eq_zero_iff_of_nonpos
      (fun a _ => Finset.sum_nonpos fun b _ => hneg c hc a b)).mp hzero a (Finset.mem_univ a)
    have hterm := (Finset.sum_eq_zero_iff_of_nonpos (fun b _ => hneg c hc a b)).mp hinner b (Finset.mem_univ b)
    have hlt2 : (c a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) < 0 := mul_neg_of_pos_of_neg hpos (by linarith)
    linarith
  have h3 : Λ - μ = 0 := by
    rw [hΛ]
    simp [hc0]
  exact (sub_eq_zero.mp h3).symm

end CDom

section Rep

variable {k : ℕ} {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V']

theorem jm_allPos' : Formalism.REAL.Jm (allPos k) = 1 := by
  ext a b
  simp [Formalism.REAL.Jm, allPos, Matrix.diagonal_apply, Matrix.one_apply]

theorem kset_uj {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ Formalism.REAL.Kset (allPos k)) : g ∈ UJset (allPos k) := by
  show Formalism.REAL.inUJ (allPos k) g
  unfold Formalism.REAL.inUJ
  rw [jm_allPos', Matrix.mul_one]
  have h := Matrix.mem_unitaryGroup_iff'.mp hg.1
  rwa [Matrix.star_eq_conjTranspose] at h

theorem kset_star {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ Formalism.REAL.Kset (allPos k)) :
    gᴴ ∈ Formalism.REAL.Kset (allPos k) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    have h := Matrix.mem_unitaryGroup_iff'.mp hg.1
    rwa [Matrix.star_eq_conjTranspose] at h
  · rw [jm_allPos', Matrix.mul_one, Matrix.one_mul]

theorem kset_mul_star {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ Formalism.REAL.Kset (allPos k)) : g * gᴴ = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp hg.1
  rwa [Matrix.star_eq_conjTranspose] at h

theorem kset_star_mul {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ Formalism.REAL.Kset (allPos k)) : gᴴ * g = 1 := by
  have h := Matrix.mem_unitaryGroup_iff'.mp hg.1
  rwa [Matrix.star_eq_conjTranspose] at h

theorem hc_inner {u : Fin k → ℝ} {σ : Matrix (Fin k) (Fin k) ℂ → (V →L[ℂ] V)} (hσ : IsHCTypeU k u σ)
    {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ Formalism.REAL.Kset (allPos k)) (p q : V) :
    ⟪σ g p, σ g q⟫_ℂ = ⟪p, q⟫_ℂ := by
  have hn := hσ.2.2.1.2.1
  let f : V →ₗᵢ[ℂ] V := ⟨(σ g : V →ₗ[ℂ] V), fun x => hn g (kset_uj hg) x⟩
  exact f.inner_map_map p q

theorem hc_inv {u : Fin k → ℝ} {σ : Matrix (Fin k) (Fin k) ℂ → (V →L[ℂ] V)} (hσ : IsHCTypeU k u σ)
    {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ Formalism.REAL.Kset (allPos k)) (p : V) : σ gᴴ (σ g p) = p := by
  have h0 := hσ.2.2.1.1.2 gᴴ (kset_uj (kset_star hg)) g (kset_uj hg)
  rw [kset_star_mul hg, hσ.2.2.1.1.1] at h0
  have h2 := congrArg (fun T => T p) h0
  simpa using h2.symm

theorem hc_mul {u : Fin k → ℝ} {σ : Matrix (Fin k) (Fin k) ℂ → (V →L[ℂ] V)} (hσ : IsHCTypeU k u σ)
    {g h : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ Formalism.REAL.Kset (allPos k)) (hh : h ∈ Formalism.REAL.Kset (allPos k))
    (p : V) : σ (g * h) p = σ g (σ h p) := by
  rw [hσ.2.2.1.1.2 g (kset_uj hg) h (kset_uj hh)]
  rfl

theorem cdom_of_intertwiner {u u' : Fin k → ℝ} {σ : Matrix (Fin k) (Fin k) ℂ → (V →L[ℂ] V)}
    {σ' : Matrix (Fin k) (Fin k) ℂ → (V' →L[ℂ] V')} (hσ : IsHCTypeU k u σ) (hσ' : IsHCTypeU k u' σ')
    (N : V' →ₗ[ℂ] V) (hN : ∀ g ∈ Formalism.REAL.Kset (allPos k), ∀ x, N (σ' g x) = σ g (N x)) (hN0 : N ≠ 0) :
    CDom (allPos k) (Formalism.QuantumDeterminants.lowK (allPos k) u') (Formalism.QuantumDeterminants.lowK (allPos k) u) := by
  obtain ⟨_, _, _, _, _, hirr', ⟨v', _, hv'0, hv'w⟩, _⟩ := hσ'
  obtain ⟨_, _, _, _, _, _, _, hdom⟩ := hσ
  have hstab : IsKStableOn (allPos k) σ' (LinearMap.ker N) := by
    intro g hg v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hN g hg v, hv, map_zero]
  have hker : LinearMap.ker N = ⊥ := by
    rcases hirr' (LinearMap.ker N) le_top hstab with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.mp h) hN0
  have hNv : N v' ≠ 0 := by
    intro h0
    apply hv'0
    have hm : v' ∈ LinearMap.ker N := LinearMap.mem_ker.mpr h0
    rw [hker] at hm
    exact (Submodule.mem_bot ℂ).mp hm
  refine hdom _ (N v') Submodule.mem_top hNv ?_
  intro θ hθ
  rw [← hN _ hθ v', hv'w θ hθ, map_smul]

theorem hcType_inequiv {u u' : Fin k → ℝ} {σ : Matrix (Fin k) (Fin k) ℂ → (V →L[ℂ] V)}
    {σ' : Matrix (Fin k) (Fin k) ℂ → (V' →L[ℂ] V')} (hσ : IsHCTypeU k u σ) (hσ' : IsHCTypeU k u' σ')
    (huu : u ≠ u') (N : V' →ₗ[ℂ] V) (hN : ∀ g ∈ Formalism.REAL.Kset (allPos k), ∀ x, N (σ' g x) = σ g (N x)) :
    N = 0 := by
  by_contra hN0
  have h1 := cdom_of_intertwiner hσ hσ' N hN hN0
  haveI : FiniteDimensional ℂ V := hσ.2.1
  haveI : FiniteDimensional ℂ V' := hσ'.2.1
  have hN'int : ∀ g ∈ Formalism.REAL.Kset (allPos k), ∀ x, LinearMap.adjoint N (σ g x) = σ' g (LinearMap.adjoint N x) := by
    intro g hg x
    apply ext_inner_left ℂ
    intro y
    obtain ⟨y₀, rfl⟩ : ∃ y₀, y = σ' g y₀ := ⟨σ' gᴴ y, by
      have h := hc_inv hσ' (kset_star hg) y
      rw [Matrix.conjTranspose_conjTranspose] at h
      exact h.symm⟩
    rw [LinearMap.adjoint_inner_right, hN g hg y₀, hc_inner hσ hg, hc_inner hσ' hg, LinearMap.adjoint_inner_right]
  have hN'0 : LinearMap.adjoint N ≠ 0 := by
    intro h
    apply hN0
    rw [← LinearMap.adjoint_adjoint N, h, map_zero]
  have h2 := cdom_of_intertwiner hσ' hσ (LinearMap.adjoint N) hN'int hN'0
  have heq := cdom_antisymm h1 h2
  simp only [Formalism.QuantumDeterminants.lowK] at heq
  exact huu (add_left_inj _ |>.mp (sub_left_inj.mp heq)).symm

end Rep

section Tens

open Formalism.L2.SG.Pf.IdBlocks2.TensIrr

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
  {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℂ (V i)]
  {V' : ι → Type*} [∀ i, NormedAddCommGroup (V' i)] [∀ i, InnerProductSpace ℂ (V' i)]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {W' : Type*} [NormedAddCommGroup W'] [InnerProductSpace ℂ W']

theorem tens_inequiv [FiniteDimensional ℂ W] [FiniteDimensional ℂ W'] [∀ i, FiniteDimensional ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V' i)]
    (tens : (∀ i, V i) → W) (hin : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (hspan : Submodule.span ℂ (Set.range tens) = ⊤)
    (tens' : (∀ i, V' i) → W') (hin' : ∀ x y, ⟪tens' x, tens' y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (hspan' : Submodule.span ℂ (Set.range tens') = ⊤)
    {G : Type*} (H : Set G) (π : G → (W →ₗ[ℂ] W)) (π' : G → (W' →ₗ[ℂ] W'))
    (hiso : ∀ s ∈ H, ∀ p q, ⟪π s p, π s q⟫_ℂ = ⟪p, q⟫_ℂ)
    (i₀ : ι) {u u' : Fin k → ℝ} (σ : Matrix (Fin k) (Fin k) ℂ → (V i₀ →L[ℂ] V i₀))
    (σ' : Matrix (Fin k) (Fin k) ℂ → (V' i₀ →L[ℂ] V' i₀)) (hσ : IsHCTypeU k u σ) (hσ' : IsHCTypeU k u' σ')
    (huu : u ≠ u') (A : Matrix (Fin k) (Fin k) ℂ) (hA : A ∈ Formalism.REAL.Kset (allPos k))
    (hlift : ∀ g ∈ Formalism.REAL.Kset (allPos k), ∃ s ∈ H,
      (∀ x, π s (tens x) = tens (Function.update x i₀ (σ g (x i₀)))) ∧
      ∀ x, π' s (tens' x) = tens' (Function.update x i₀ (σ' (Aᴴ * g * A) (x i₀))))
    (T : W' →ₗ[ℂ] W) (hT : ∀ s ∈ H, ∀ w, T (π' s w) = π s (T w)) : T = 0 := by
  have hmemK : ∀ a ∈ Formalism.REAL.Kset (allPos k), ∀ b ∈ Formalism.REAL.Kset (allPos k),
      a * b ∈ Formalism.REAL.Kset (allPos k) := by
    intro a ha b hb
    refine ⟨Submonoid.mul_mem _ ha.1 hb.1, ?_⟩
    rw [jm_allPos', Matrix.mul_one, Matrix.one_mul]
  have hAs : Aᴴ ∈ Formalism.REAL.Kset (allPos k) := kset_star hA
  have hKg : ∀ g ∈ Formalism.REAL.Kset (allPos k), Aᴴ * g * A ∈ Formalism.REAL.Kset (allPos k) :=
    fun g hg => hmemK _ (hmemK _ hAs _ hg) _ hA
  suffices hc : ∀ z x, ⟪tens z, T (tens' x)⟫_ℂ = 0 by
    apply LinearMap.ext_on_range hspan'
    intro x
    rw [LinearMap.zero_apply]
    apply eq_of_inner_tens tens hspan
    intro z
    rw [hc z x, inner_zero_right]
  intro z x
  set M : V' i₀ →ₗ[ℂ] V i₀ :=
    LinearMap.adjoint (intersection_update_fsHerm_neg_one tens hin hspan z i₀) ∘ₗ T ∘ₗ intersection_update_fsHerm_neg_one tens' hin' hspan' x i₀ with hMdef
  have hMinner : ∀ p q, ⟪p, M q⟫_ℂ =
      ⟪tens (Function.update z i₀ p), T (tens' (Function.update x i₀ q))⟫_ℂ := by
    intro p q
    rw [hMdef, LinearMap.comp_apply, LinearMap.adjoint_inner_right]
    rfl
  have hstar : ∀ g ∈ Formalism.REAL.Kset (allPos k), ∀ p q,
      ⟪σ g p, M (σ' (Aᴴ * g * A) q)⟫_ℂ = ⟪p, M q⟫_ℂ := by
    intro g hg p q
    obtain ⟨s, hs, h1, h2⟩ := hlift g hg
    rw [hMinner, hMinner]
    have e1 := h1 (Function.update z i₀ p)
    have e2 := h2 (Function.update x i₀ q)
    simp at e1 e2
    rw [← e1, ← e2, hT s hs, hiso s hs]
  have hMint : ∀ g ∈ Formalism.REAL.Kset (allPos k), ∀ q, M (σ' (Aᴴ * g * A) q) = σ g (M q) := by
    intro g hg q
    apply ext_inner_left ℂ
    intro y
    obtain ⟨p, rfl⟩ : ∃ p, y = σ g p := ⟨σ gᴴ y, by
      have h := hc_inv hσ (kset_star hg) y
      rw [Matrix.conjTranspose_conjTranspose] at h
      exact h.symm⟩
    rw [hstar g hg p q, hc_inner hσ hg]
  have hN : ∀ g ∈ Formalism.REAL.Kset (allPos k), ∀ q,
      (M ∘ₗ (σ' Aᴴ : V' i₀ →ₗ[ℂ] V' i₀)) (σ' g q) = σ g ((M ∘ₗ (σ' Aᴴ : V' i₀ →ₗ[ℂ] V' i₀)) q) := by
    intro g hg q
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [← hMint g hg]
    congr 1
    rw [← hc_mul hσ' hAs hg q, ← hc_mul hσ' (hKg g hg) hAs q, Matrix.mul_assoc (Aᴴ * g),
      kset_mul_star hA, Matrix.mul_one]
  have hN0 := hcType_inequiv hσ hσ' huu (M ∘ₗ (σ' Aᴴ : V' i₀ →ₗ[ℂ] V' i₀)) hN
  have hM0 : ∀ q, M q = 0 := by
    intro q
    have h := LinearMap.congr_fun hN0 (σ' A q)
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearMap.zero_apply] at h
    rwa [hc_inv hσ' hA q] at h
  have hfin := hMinner (z i₀) (x i₀)
  rw [hM0, inner_zero_right] at hfin
  simpa using hfin.symm

end Tens

end Formalism.L2.SG.Pf.IdBlocks2.HW

open scoped Classical ComplexConjugate InnerProductSpace
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.IdBlocks2.Geo

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.Pf.IdBlocks2.UkEmb Formalism.L2.SG.Pf.IdBlocks2.TensIrr

theorem jm_allPos (k : ℕ) : Formalism.REAL.Jm (allPos k) = 1 := by
  ext a b
  simp [Formalism.REAL.Jm, allPos, Matrix.diagonal_apply, Matrix.one_apply]

theorem kset_unitary {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ Formalism.REAL.Kset (allPos k)) :
    gᴴ * g = 1 ∧ g * gᴴ = 1 := by
  refine ⟨?_, ?_⟩
  · have h := Matrix.mem_unitaryGroup_iff'.mp hg.1
    rwa [Matrix.star_eq_conjTranspose] at h
  · have h := Matrix.mem_unitaryGroup_iff.mp hg.1
    rwa [Matrix.star_eq_conjTranspose] at h

theorem uj_of_unitary {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : gᴴ * g = 1) : g ∈ UJset (allPos k) := by
  show Formalism.REAL.inUJ (allPos k) g
  unfold Formalism.REAL.inUJ
  rw [jm_allPos, Matrix.mul_one]
  exact hg

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def sU (v : InfinitePlace X.B.I.F) (g : Matrix (Fin D.R.k) (Fin D.R.k) ℂ) (hg : gᴴ * g = 1) :
    Formalism.REAL.UJ (X.B.I.ε v) :=
  ⟨⟨smat (Formalism.REAL.Jm (X.B.I.ε v)) (X.wfr u v) g,
    Formalism.REAL.Jm (X.B.I.ε v) * (smat (Formalism.REAL.Jm (X.B.I.ε v)) (X.wfr u v) g)ᴴ * Formalism.REAL.Jm (X.B.I.ε v),
    mul_eq_one_comm.1 (smat_inv _ _ (Formalism.REAL.Jm_mul_self _) (Formalism.REAL.Jm_conjTranspose _) g hg
      (fun a b => X.wfr_on u v a b)),
    smat_inv _ _ (Formalism.REAL.Jm_mul_self _) (Formalism.REAL.Jm_conjTranspose _) g hg (fun a b => X.wfr_on u v a b)⟩,
    smat_unitary _ _ (fun a b => X.wfr_on u v a b) (Formalism.REAL.Jm_conjTranspose _) g hg⟩

def sAt (v : InfinitePlace X.B.I.F) (g : Matrix (Fin D.R.k) (Fin D.R.k) ℂ) (hg : gᴴ * g = 1) : X.B.I.Ginf :=
  Function.update (1 : X.B.I.Ginf) v (sU X u v g hg)

theorem sAt_mem (v : InfinitePlace X.B.I.F) (g : Matrix (Fin D.R.k) (Fin D.R.k) ℂ) (hg : gᴴ * g = 1) :
    sAt X u v g hg ∈ Hinf X u := by
  intro w x hx
  by_cases hw : w = v
  · subst hw
    have hU : uMat (sAt X u w g hg w) = smat (Formalism.REAL.Jm (X.B.I.ε w)) (X.wfr u w) g := by
      unfold sAt
      rw [Function.update_self]
      rfl
    rw [hU]
    refine smat_fix _ _ (fun a b => X.wfr_on u w a b) g _ fun a => ?_
    rw [hswap _ (Formalism.REAL.Jm_conjTranspose _)]
    have h0 : hJ (X.B.I.ε w) (rv X.B.I w x) (X.wfr u w a) = 0 := by
      rcases hx with (⟨c, rfl⟩ | ⟨c, rfl⟩) | hx
      · exact ((X.wfr_perp u w a).1 c).1
      · exact ((X.wfr_perp u w a).1 c).2
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact (X.wfr_perp u w a).2
    have h0' : star (rv X.B.I w x) ⬝ᵥ (Formalism.REAL.Jm (X.B.I.ε w) *ᵥ X.wfr u w a) = 0 := h0
    rw [h0', star_zero]
  · have : sAt X u v g hg w = 1 := by
      unfold sAt
      rw [Function.update_of_ne hw]
      rfl
    rw [this]
    simp [uMat]

theorem matW_sAt_self (v : InfinitePlace X.B.I.F) (g : Matrix (Fin D.R.k) (Fin D.R.k) ℂ) (hg : gᴴ * g = 1) :
    matW X.B.I (X.wfr u v) v (sAt X u v g hg) = g := by
  ext a b
  have hv : sAt X u v g hg v = sU X u v g hg := by simp [sAt]
  simp only [matW]
  rw [hv]
  exact smat_mat _ _ (fun a b => X.wfr_on u v a b) g a b

theorem matW_sAt_ne (v w : InfinitePlace X.B.I.F) (hw : w ≠ v) (g : Matrix (Fin D.R.k) (Fin D.R.k) ℂ)
    (hg : gᴴ * g = 1) : matW X.B.I (X.wfr u w) w (sAt X u v g hg) = 1 := by
  ext a b
  have hw' : sAt X u v g hg w = 1 := by simp [sAt, Function.update_apply, hw]
  simp only [matW]
  rw [hw']
  exact one_mat _ _ (fun a b => X.wfr_on u w a b) a b

theorem piIrr : Formalism.L2.SG.TermOp.IdBlocks.PiIrr X u := by
  have : ∀ v, Nontrivial (X.Vloc u v) := fun v => (X.piLoc_type u v).1
  intro S hS
  have hrep := X.piU_rep u
  refine tens_irr (X.tensU u) (X.tensU_inner u) (X.tensU_span u) ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf)
    (fun s => (X.piU u s : X.Vpi u →ₗ[ℂ] X.Vpi u)) ?_ ?_
    (fun v => {a | ∃ g ∈ Formalism.REAL.Kset (allPos D.R.k), a = (X.piLoc u v g : X.Vloc u v →ₗ[ℂ] X.Vloc u v)})
    ?_ ?_ ?_ ?_ S hS
  · intro s hs p q
    exact hrep.2.2.1 s (hinf_le_sinf X u s hs) p q
  · intro s hs
    refine ⟨s⁻¹, (Hinf X u).inv_mem hs, fun w => ?_⟩
    show X.piU u s⁻¹ (X.piU u s w) = w
    rw [← ContinuousLinearMap.mul_apply, ← hrep.2.1 _ (hinf_le_sinf X u _ ((Hinf X u).inv_mem hs)) _
      (hinf_le_sinf X u s hs), inv_mul_cancel, hrep.1]
    rfl
  · rintro v a ⟨g, hg, rfl⟩ p q
    have hn := (X.piLoc_type u v).2.2.1.2.1 g (uj_of_unitary (kset_unitary hg).1)
    let L : X.Vloc u v →ₗᵢ[ℂ] X.Vloc u v := ⟨(X.piLoc u v g : X.Vloc u v →ₗ[ℂ] X.Vloc u v), hn⟩
    exact L.inner_map_map p q
  · rintro v a ⟨g, hg, rfl⟩ y
    have hu := kset_unitary hg
    refine ⟨X.piLoc u v gᴴ y, ?_⟩
    have hmul := (X.piLoc_type u v).2.2.1.1.2 g (uj_of_unitary hu.1) gᴴ
      (uj_of_unitary (by rw [Matrix.conjTranspose_conjTranspose]; exact hu.2))
    show X.piLoc u v g (X.piLoc u v gᴴ y) = y
    rw [← ContinuousLinearMap.comp_apply, ← hmul, hu.2, (X.piLoc_type u v).2.2.1.1.1]
    rfl
  · intro v S' hS'
    have := (X.piLoc_type u v).2.2.2.2.2.1 S' le_top (fun g hg x hx => hS' _ ⟨g, hg, rfl⟩ x hx)
    exact this
  · rintro v a ⟨g, hg, rfl⟩
    have hu := kset_unitary hg
    refine ⟨sAt X u v g hu.1, sAt_mem X u v g hu.1, fun x => ?_⟩
    show X.piU u (sAt X u v g hu.1) (X.tensU u x) = _
    rw [X.tensU_equiv u _ (sAt_mem X u v g hu.1) x]
    congr 1
    funext w
    by_cases hw : w = v
    · subst hw
      rw [matW_sAt_self, Function.update_self]
      rfl
    · rw [matW_sAt_ne X u v w hw, Function.update_of_ne hw, (X.piLoc_type u w).2.2.1.1.1]
      rfl

end Formalism.L2.SG.Pf.IdBlocks2.Geo

open scoped Classical ComplexConjugate InnerProductSpace
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.Pf.IdBlocks2.Geo

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem uS_ne {D : D7} {u u' : D.what₂.Word} (hu : u ≠ u') (τ : D.what₂.Tau) : uS D u τ ≠ uS D u' τ := by
  obtain ⟨l, hl⟩ : ∃ l, D.s.letter u l ≠ D.s.letter u' l := by
    by_contra h
    push_neg at h
    exact hu (D.s.letter_inj (funext h))
  intro heq
  have h1 := D.s.u_letter u τ l.1 l.2
  have h2 := D.s.u_letter u' τ l.1 l.2
  have hv : (D.hcW u τ).v = (D.hcW u' τ).v := (D.hcW_v u τ).trans (D.hcW_v u' τ).symm
  have he := congrFun heq ⟨l.1 + 1, by omega⟩
  have he' : (D.hcW u τ).u ⟨l.1 + 1, by omega⟩ = (D.hcW u' τ).u ⟨l.1 + 1, by omega⟩ := by
    simp only [uS] at he
    exact_mod_cast he
  rw [h1, h2, hv] at he'
  have hD := D.s.Del_pos
  have hl' : D.s.letter u ⟨l.1, l.2⟩ ≠ D.s.letter u' ⟨l.1, l.2⟩ := hl
  by_cases ha : D.s.letter u ⟨l.1, l.2⟩ = true <;> by_cases hb : D.s.letter u' ⟨l.1, l.2⟩ = true <;>
    simp only [ha, hb, ite_true, ite_false, Bool.false_eq_true] at he' hl' <;> first | exact hl' rfl | linarith |
      (simp only [Bool.not_eq_true] at ha hb; exact hl' (ha.trans hb.symm))

theorem ro_of (hN : Formalism.L2.SG.TermOp.Vanish.NLamNinf) {D : D7} (X : HidaSetting D) {u u' : D.what₂.Word} {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (t : GTerm X u u' (X.Fu u) (X.Fu u') what₂ rows') :
    (ROinf t).Countable ∧ (∀ a ∈ ROinf t, ∀ b ∈ ROinf t, a * b ∈ ROinf t) ∧ (∀ a ∈ ROinf t, a⁻¹ ∈ ROinf t) ∧
      ROinf t ⊆ X.NinfU u := by
  refine ⟨Vanish.ROset_countable X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin,
    fun a ha b hb => (Vanish.ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin).mul_mem ha hb,
    fun a ha => (Vanish.ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin).inv_mem ha, ?_⟩
  rintro _ ⟨x, n, hx, rfl, hn, -⟩
  exact hN D X u t.lam x n hx hn

end Formalism.L2.SG.Pf.IdBlocks2.Geo

open scoped Classical ComplexConjugate InnerProductSpace
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.Pf.IdBlocks2.Geo

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.Pf.IdBlocks2.Geo

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem piU_sAt (v : InfinitePlace X.B.I.F) (g : Matrix (Fin D.R.k) (Fin D.R.k) ℂ) (hg : gᴴ * g = 1)
    (x : ∀ w, X.Vloc u w) :
    X.piU u (sAt X u v g hg) (X.tensU u x) = X.tensU u (Function.update x v (X.piLoc u v g (x v))) := by
  rw [X.tensU_equiv u _ (sAt_mem X u v g hg) x]
  congr 1
  funext w
  by_cases hw : w = v
  · subst hw
    rw [matW_sAt_self, Function.update_self]
  · rw [matW_sAt_ne X u v w hw, Function.update_of_ne hw, (X.piLoc_type u w).2.2.1.1.1]
    rfl

theorem sAt_ne (v w : InfinitePlace X.B.I.F) (hw : w ≠ v) (g : Matrix (Fin D.R.k) (Fin D.R.k) ℂ)
    (hg : gᴴ * g = 1) : sAt X u v g hg w = 1 := by
  simp [sAt, Function.update_apply, hw]

end Formalism.L2.SG.Pf.IdBlocks2.Geo

namespace Formalism.L2.SG.Pf.IdBlocks2.Geo

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.Pf.IdBlocks2.Geo

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (F0 F0' what₂ rows') in

def IdOffLift : Prop :=
  u ≠ u' → ∀ t : GTerm X u u' F0 F0' what₂ rows', t.isId → ∀ v : InfinitePlace X.B.I.F,
    ∃ A ∈ Formalism.REAL.Kset (allPos D.R.k), ∀ h ∈ ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf),
      (∀ w, w ≠ v → h w = 1) → ∀ x : ∀ w, X.Vloc u' w,
        X.piU u' (t.pt.1⁻¹ * h * t.pt.1) (X.tensU u' x) =
          X.tensU u' (Function.update x v (X.piLoc u' v (Aᴴ * matW X.B.I (X.wfr u v) v h * A) (x v)))

theorem idOffIneq_of_lift (hL : IdOffLift F0 F0' what₂ rows' (X := X)) :
    Formalism.L2.SG.TermOp.IdBlocks.IdOffIneq F0 F0' what₂ rows' (X := X) := by
  intro hu t ht T hT
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  obtain ⟨A, hA, hAl⟩ := hL hu t ht v
  have hne : (fun i => ((D.hcW u (X.pl v)).u i : ℝ)) ≠ (fun i => ((D.hcW u' (X.pl v)).u i : ℝ)) :=
    Formalism.L2.SG.Pf.IdBlocks2.Geo.uS_ne hu (X.pl v)
  have hrep := X.piU_rep u
  refine Formalism.L2.SG.Pf.IdBlocks2.HW.tens_inequiv (X.tensU u) (X.tensU_inner u) (X.tensU_span u)
    (X.tensU u') (X.tensU_inner u') (X.tensU_span u') ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf)
    (fun s => (X.piU u s : X.Vpi u →ₗ[ℂ] X.Vpi u))
    (fun s => (X.piU u' (t.pt.1⁻¹ * s * t.pt.1) : X.Vpi u' →ₗ[ℂ] X.Vpi u'))
    (fun s hs p q => hrep.2.2.1 s (hinf_le_sinf X u s hs) p q) v (X.piLoc u v) (X.piLoc u' v)
    (X.piLoc_type u v) (X.piLoc_type u' v) hne A hA ?_ T hT
  intro g hg
  have hgu := Formalism.L2.SG.Pf.IdBlocks2.HW.kset_star_mul hg
  refine ⟨sAt X u v g hgu, sAt_mem X u v g hgu, fun x => piU_sAt X u v g hgu x, fun x => ?_⟩
  have := hAl (sAt X u v g hgu) (sAt_mem X u v g hgu) (fun w hw => sAt_ne X u v w hw g hgu) x
  rw [matW_sAt_self] at this
  exact this

end Formalism.L2.SG.Pf.IdBlocks2.Geo

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut

theorem piIrrC_holds : PiIrrC := by
  intro D X u
  exact Formalism.L2.SG.Pf.IdBlocks2.Geo.piIrr X u

theorem distinct_words_distinct_parameters (D : D7) (u u' : D.what₂.Word) (hu : u ≠ u') (τ : D.what₂.Tau) : uS D u τ ≠ uS D u' τ := by
  exact Formalism.L2.SG.Pf.IdBlocks2.Geo.uS_ne hu τ

theorem idMeetRO_of (hN : Formalism.L2.SG.TermOp.Vanish.NLamNinf) (D : D7) (X : HidaSetting D) (Y : Full X)
    (u : D.what₂.Word) : IdMeetRO (X.Fu u) (Y.cs u) := by
  intro _ t _ _
  exact Formalism.L2.SG.Pf.IdBlocks2.Geo.ro_of hN X t

theorem idOffRO_of (hN : Formalism.L2.SG.TermOp.Vanish.NLamNinf) (D : D7) (X : HidaSetting D) (Y : Full X)
    (u u' : D.what₂.Word) : IdOffRO (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X) := by
  intro _ t _
  exact Formalism.L2.SG.Pf.IdBlocks2.Geo.ro_of hN X t

def IdOffConjC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    IdOffConj (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X)

def IdOffLiftC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    Formalism.L2.SG.Pf.IdBlocks2.Geo.IdOffLift (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X)

def IdMeetOneC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), NeatKu X u Y.hK →
    FundExists X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) → IdMeetOne (X.Fu u) (Y.cs u)

def IdMeetPhaseC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), NeatKu X u Y.hK →
    FundExists X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) → IdMeetPhase (X.Fu u) (Y.cs u)

def IdMeetVolC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), NeatKu X u Y.hK →
    FundExists X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) → IdMeetVol (X.Fu u) (Y.cs u) (Y.FN u)

theorem idOffC_of_conjLift (hN : Formalism.L2.SG.TermOp.Vanish.NLamNinf) (hC : IdOffConjC) (hL : IdOffLiftC) : IdOffC := by
  intro D X Y u u' _
  exact ⟨hC D X Y u u', Formalism.L2.SG.Pf.IdBlocks2.Geo.idOffIneq_of_lift (hL D X Y u u'), idOffRO_of hN D X Y u u'⟩

theorem idCellOffC_of_conjLift (hN : Formalism.L2.SG.TermOp.Vanish.NLamNinf) (hV : VolPosC) (hC : IdOffConjC)
    (hL : IdOffLiftC) : IdCellOffC := by
  exact idCellOffC_of_steps hV (idOffC_of_conjLift hN hC hL)

theorem idMeetC_of_steps3 (hL : Formalism.L2.SG.TermOp.Vanish.NLamNinf) (h1 : IdMeetOneC) (h2 : IdMeetPhaseC)
    (h3 : IdMeetVolC) : IdMeetC := by
  intro D X Y u hC hFE
  exact ⟨h1 D X Y u hC hFE, h2 D X Y u hC hFE, idMeetRO_of hL D X Y u, h3 D X Y u hC hFE⟩

theorem idCellDiagNeatC_of_steps3 (hL : Formalism.L2.SG.TermOp.Vanish.NLamNinf) (hV : VolPosC) (h1 : IdMeetOneC)
    (h2 : IdMeetPhaseC) (h3 : IdMeetVolC) : IdCellDiagNeatC := by
  exact idCellDiagNeatC_of hV piIrrC_holds (idMeetC_of_steps3 hL h1 h2 h3)

theorem idCellDiagC_of_steps3 (hL : Formalism.L2.SG.TermOp.Vanish.NLamNinf) (hV : VolPosC) (h1 : IdMeetOneC)
    (h2 : IdMeetPhaseC) (h3 : IdMeetVolC) (hN : NeatC) : IdCellDiagC := by
  exact idCellDiagC_of_steps hV piIrrC_holds (idMeetC_of_steps3 hL h1 h2 h3) hN

end Formalism.L2.SG.Pf
