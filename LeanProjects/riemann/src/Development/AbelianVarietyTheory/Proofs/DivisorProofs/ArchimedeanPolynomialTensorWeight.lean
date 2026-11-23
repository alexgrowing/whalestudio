import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixPartEqBotOfLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemDegLE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFinitePiTensorSumOfFactorOperators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.RealLift Formalism.BasicNotions.TH
open scoped Classical

noncomputable section
namespace GlobalTheory.FockKStab
open GlobalTheory.ExpAct
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem mem_of_exp {V : Type} [AddCommGroup V] [Module ℂ V] (L : Module.End ℂ V) (hL : LocFin L) (N : Submodule ℂ V)
    (T : V) (h : ∀ s : ℝ, ∃ U : Module.End ℂ V, IsExp ((s : ℂ) • L) U ∧ U T ∈ N) : L T ∈ N := by
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l'
  set l : V →ₗ[ℂ] ℂ := l' ∘ₗ N.mkQ with hldef
  have hl : ∀ v ∈ N, l v = 0 := fun v hv => by simp [hldef, (Submodule.Quotient.mk_eq_zero N).2 hv]
  show l (L T) = 0
  obtain ⟨N0, hfin, hT, hN0⟩ := hL T
  set A := mat L N0 hN0
  set x := crd N0 ⟨T, hT⟩
  set φ := l ∘ₗ emb N0
  have hpow : ∀ n : ℕ, φ ((A ^ n) *ᵥ x) = l ((L ^ n) T) := fun n => by
    simp only [φ, LinearMap.comp_apply, A, emb_pow_mulVec, x, emb_crd]
  have hg : ∀ s : ℝ, φ (NormedSpace.exp (s • A) *ᵥ x) = 0 := by
    intro s
    obtain ⟨U, hU, hUN⟩ := h s
    have h1 := hU T l
    have h2 := hasSum_exp_mulVec (s • A) φ x
    have e : ∀ n : ℕ, ((n.factorial : ℂ))⁻¹ * φ (((s • A) ^ n) *ᵥ x) =
        ((n.factorial : ℂ))⁻¹ * l ((((s : ℂ) • L) ^ n) T) := fun n => by
      rw [smul_pow, smul_pow, Matrix.smul_mulVec, LinearMap.map_smul_of_tower, hpow, LinearMap.smul_apply,
        map_smul]
      simp [Complex.real_smul]
    simp only [e] at h2
    rw [h2.unique h1, hl _ hUN]
  let ψ : Matrix (Fin (Module.finrank ℂ N0)) (Fin (Module.finrank ℂ N0)) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => φ (M *ᵥ x)
      map_add' := fun M M' => by simp [Matrix.add_mulVec]
      map_smul' := fun r M => by
        rw [Matrix.smul_mulVec, LinearMap.map_smul_of_tower]; rfl }
  have hd : HasDerivAt (fun u : ℝ => ψ.toContinuousLinearMap (NormedSpace.exp (u • A)))
      (ψ.toContinuousLinearMap (A * NormedSpace.exp ((0 : ℝ) • A))) 0 :=
    (ψ.toContinuousLinearMap).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_smul_const' A (0 : ℝ))
  have hz : (fun u : ℝ => ψ.toContinuousLinearMap (NormedSpace.exp (u • A))) = fun _ => 0 := by
    funext u; exact hg u
  rw [hz] at hd
  have := hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  simp only [zero_smul, NormedSpace.exp_zero, mul_one] at this
  have e2 : ψ.toContinuousLinearMap A = l (L T) := by
    show φ (A *ᵥ x) = _
    simp only [φ, LinearMap.comp_apply, A, emb_mulVec, x, emb_crd]
  rw [← e2]; exact this

end GlobalTheory.FockKStab
end

noncomputable section
namespace GlobalTheory.FockKStab
open Matrix

theorem jm_mul_jm (R S : ℕ) : Formalism.BasicNotions.TH.Jm R S * Formalism.BasicNotions.TH.Jm R S = 1 := by
  simp [Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem commute_jm {R S : ℕ} {X : Mat R S} (hX : IsKC X) : Commute X (Formalism.BasicNotions.TH.Jm R S) := by
  show X * _ = _ * X
  have h1 : ∀ i j, X (Sum.inl i) (Sum.inr j) = 0 := fun i j => hX _ _ (by simp [sameBlock])
  have h2 : ∀ i j, X (Sum.inr i) (Sum.inl j) = 0 := fun i j => hX _ _ (by simp [sameBlock])
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Matrix.mul_apply, Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.one_apply, h1, h2]

theorem isKC_smul {R S : ℕ} {X : Mat R S} (hX : IsKC X) (c : ℂ) : IsKC (c • X) := fun a b h => by
  simp [hX a b h]

theorem isKC_zero (R S : ℕ) : IsKC (0 : Mat R S) := fun a b _ => rfl

theorem isKC_add {R S : ℕ} {X X' : Mat R S} (hX : IsKC X) (hX' : IsKC X') : IsKC (X + X') := fun a b h => by
  simp [hX a b h, hX' a b h]

theorem isKC_conjTranspose {R S : ℕ} {X : Mat R S} (hX : IsKC X) : IsKC Xᴴ := fun a b h => by
  have h' : ¬ sameBlock b a := by
    intro h2; apply h; rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]
  simp [Matrix.conjTranspose_apply, hX b a h']

theorem mem_upq {R S : ℕ} {X : Mat R S} (hX : IsKC X) (hs : Xᴴ = -X) : X ∈ upq R S := by
  show Xᴴ * _ + _ * X = 0
  rw [hs, ← (commute_jm hX).eq]; simp

theorem frame_inv {α : Type} [Fintype α] [DecidableEq α] {R S : ℕ} {M : Matrix α α ℂ} {C : Matrix α (Ix R S) ℂ}
    {A' : Matrix (Ix R S) α ℂ} (h : IsFrame M C) (hA : C * A' = 1) : A' * C = 1 := by
  set K := M * C.map star * Formalism.BasicNotions.TH.Jm R S
  have h1 : Cᵀ * K = 1 := by
    simp only [K, ← Matrix.mul_assoc, h.1, jm_mul_jm]
  have h2 : Kᵀ * C = 1 := by
    have := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have h3 : A' = Kᵀ := by
    calc A' = (Kᵀ * C) * A' := by rw [h2, Matrix.one_mul]
      _ = Kᵀ := by rw [Matrix.mul_assoc, hA, Matrix.mul_one]
  rw [h3, h2]

theorem commute_of_frame {α : Type} [Fintype α] [DecidableEq α] {R S : ℕ} {C : Matrix α (Ix R S) ℂ}
    {A' : Matrix (Ix R S) α ℂ} (hCA : C * A' = 1) (hAC : A' * C = 1) {G θ : Matrix α α ℂ} {E : Mat R S}
    (hG : G * C = C * E) (hθ : θ * C = C * Formalism.BasicNotions.TH.Jm R S) (hE : Commute E (Formalism.BasicNotions.TH.Jm R S)) : Commute G θ := by
  have hG' : G = C * E * A' := by rw [← hG, Matrix.mul_assoc, hCA, Matrix.mul_one]
  have hθ' : A' * θ = Formalism.BasicNotions.TH.Jm R S * A' := by
    calc A' * θ = A' * θ * (C * A') := by rw [hCA, Matrix.mul_one]
      _ = A' * (θ * C) * A' := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hθ]; simp only [← Matrix.mul_assoc, hAC, Matrix.one_mul]
  show G * θ = θ * G
  rw [hG']
  calc C * E * A' * θ = C * E * (A' * θ) := by rw [Matrix.mul_assoc]
    _ = C * (E * Formalism.BasicNotions.TH.Jm R S) * A' := by rw [hθ']; simp only [Matrix.mul_assoc]
    _ = (θ * C) * E * A' := by rw [hE.eq, hθ]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

end GlobalTheory.FockKStab
end

noncomputable section
namespace GlobalTheory.FockKStab
open Matrix

section Tensor
variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem atPl_eq' (w : ι) (L : Module.End ℂ (V w)) :
    atPl w L = PiTensorProduct.mapMultilinear ℂ V V (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w L) := rfl

theorem atPl_add' (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L + L') = atPl w L + atPl w L' := by
  simp only [atPl_eq', MultilinearMap.map_update_add]

theorem atPl_smul' (w : ι) (c : ℂ) (L : Module.End ℂ (V w)) : atPl w (c • L) = c • atPl w L := by
  simp only [atPl_eq', MultilinearMap.map_update_smul]

theorem atPl_zero' (w : ι) : atPl w (0 : Module.End ℂ (V w)) = 0 := by
  simp only [atPl_eq', MultilinearMap.map_update_zero]

theorem atPl_one' (w : ι) : atPl w (1 : Module.End ℂ (V w)) = 1 := by
  rw [atPl_eq', show Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w 1 = fun i => LinearMap.id by
    funext i; by_cases h : i = w
    · subst h; simp; rfl
    · simp [Function.update_of_ne h]]
  exact PiTensorProduct.map_id

end Tensor

theorem locFin_fock2' (P Q R S : ℕ) (Y : Mat R S) (hY : IsKC Y) (c : ℂ) :
    LocFin (fockAct2 P Q R S Y + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs Y hY y hy) (W.smul_mem c hy)⟩

set_option maxHeartbeats 1000000 in

theorem kstab_skew : GlobalTheory.RealLift.ActsLaws → GlobalTheory.RealLift.LineEx → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d P Q R S : ℕ) (X : Spc F E n) (W : Spc F E d) (om : Rep σ X W)
    (C : InfinitePlace F → Matrix (Fin d) (Formalism.BasicNotions.TH.Ix R S) ℂ) (Φ : GlobalTheory.RealLift.Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d))
    (c : InfinitePlace F → ℂ), IsCMExt F E σ →
    (∀ w, GlobalTheory.RealLift.IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w)) →
    (∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm R S) → Function.Injective Φ →
    GlobalTheory.RealLift.ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (Formalism.BasicNotions.TH.fockAct2 P Q R S) c →
    (∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d)) →
    ∀ N : Submodule ℂ (GlobalTheory.RealLift.Tens F P Q R S),
      (∀ k ∈ KInf σ W B.emb, ∀ T ∈ N, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) (Φ T) f₁ → f₁ ∈ N.map Φ) →
      ∀ w (Y : Formalism.BasicNotions.TH.Mat R S), Formalism.BasicNotions.TH.IsKC Y → Yᴴ = -Y → ∀ T ∈ N,
        GlobalTheory.RealLift.atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (Formalism.BasicNotions.TH.fockAct2 P Q R S Y) T ∈ N := by
  intro hAL hLE F E _ _ _ _ _ σ B n d P Q R S X W om C Φ c hcm hC hθ hinj hact hadm N hN w
  intro Y hY hYs T hT
  set L0 : Module.End ℂ (Tens F P Q R S) :=
    atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct2 P Q R S Y + (c w * Y.trace) • 1) with hL0
  set Ys : ℝ → InfinitePlace F → Mat R S := fun s w' => if w' = w then (s : ℂ) • Y else 0 with hYsdef
  have hYsKC : ∀ s w', IsKC (Ys s w') := by
    intro s w'; by_cases h : w' = w
    · simp only [hYsdef, if_pos h]; exact isKC_smul hY _
    · simp only [hYsdef, if_neg h]; exact isKC_zero R S
  have hYsU : ∀ s w', Ys s w' ∈ upq R S := by
    intro s w'; apply mem_upq (hYsKC s w'); by_cases h : w' = w
    · simp [hYsdef, h, Matrix.conjTranspose_smul, hYs]
    · simp [hYsdef, h]
  have hsum : ∀ s : ℝ, sumPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S)
      (fun w' => fockAct2 P Q R S (Ys s w') + (c w' * (Ys s w').trace) • 1) = (s : ℂ) • L0 := by
    intro s
    unfold sumPl
    rw [Finset.sum_eq_single w]
    · rw [hL0, ← atPl_smul']
      congr 1
      simp only [hYsdef, if_pos rfl, map_smul, Matrix.trace_smul, smul_add, smul_smul, smul_eq_mul]
      congr 2; ring
    · intro w' _ hw'; simp [hYsdef, hw', atPl_zero']
    · simp
  have hloc : ∀ s : ℝ, LocFin (sumPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S)
      (fun w' => fockAct2 P Q R S (Ys s w') + (c w' * (Ys s w').trace) • 1)) := fun s =>
    GlobalTheory.RealLift.locFin_sumPl _ _ _ (fun w' => locFin_fock2' P Q R S _ (hYsKC s w') _)
  have hexp : ∀ s : ℝ, ∃ U : Module.End ℂ (Tens F P Q R S), IsExp ((s : ℂ) • L0) U ∧ U T ∈ N := by
    intro s
    obtain ⟨γ, hγ, hgen⟩ := hLE F E σ (Fin d) R S B.emb (incM F W.J) Complex.I C hcm hC (Ys s) (hYsU s)
    obtain ⟨U, hU, hSA⟩ := GlobalTheory.ExpAct.expAct_fock F (Fin n × Fin d) _ Φ _
      ((om.comp (MonoidHom.inr _ _)).comp γ) (hloc s) (fun t l hl => hadm _ l hl) (fun T => hact γ hγ (Ys s) hgen T)
    refine ⟨U, hsum s ▸ hU, ?_⟩
    have h1 := (hAL F _ (Φ T) (Φ (U T)) (Φ (U T))).2.1 _ (map_zero _) (hSA T)
    have hk : γ (Multiplicative.ofAdd 1) ∈ KInf σ W B.emb := by
      refine ⟨hγ.2 _, fun w' => ?_⟩
      obtain ⟨A', hA'⟩ := (hC w').2
      exact commute_of_frame hA' (frame_inv (hC w') hA') (hgen 1 w') (hθ w')
        (Commute.exp_left (Commute.smul_left (commute_jm (hYsKC s w')) _))
    have h2 := hN _ hk T hT _ h1
    obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 h2
    exact hinj e ▸ hy
  have hL0loc : LocFin L0 := by
    have := hloc 1
    rwa [hsum 1, Complex.ofReal_one, one_smul] at this
  have hmem := mem_of_exp L0 hL0loc N T hexp
  have e : L0 T = atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct2 P Q R S Y) T +
      (c w * Y.trace) • T := by
    simp [hL0, atPl_add', atPl_smul', atPl_one']
  rw [e] at hmem
  simpa using N.sub_mem hmem (N.smul_mem (c w * Y.trace) hT)

set_option maxHeartbeats 1000000 in

theorem kstab : GlobalTheory.RealLift.ActsLaws → GlobalTheory.RealLift.LineEx →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d P Q R S : ℕ) (X : Spc F E n) (W : Spc F E d) (om : Rep σ X W)
    (C : InfinitePlace F → Matrix (Fin d) (Formalism.BasicNotions.TH.Ix R S) ℂ) (Φ : GlobalTheory.RealLift.Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d))
    (c : InfinitePlace F → ℂ), IsCMExt F E σ →
    (∀ w, GlobalTheory.RealLift.IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w)) →
    (∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm R S) → Function.Injective Φ →
    GlobalTheory.RealLift.ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (Formalism.BasicNotions.TH.fockAct2 P Q R S) c →
    (∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d)) →
    ∀ N : Submodule ℂ (GlobalTheory.RealLift.Tens F P Q R S),
      (∀ k ∈ KInf σ W B.emb, ∀ T ∈ N, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) (Φ T) f₁ → f₁ ∈ N.map Φ) →
      ∀ w (Z : Formalism.BasicNotions.TH.Mat R S), Formalism.BasicNotions.TH.IsKC Z → ∀ T ∈ N,
        GlobalTheory.RealLift.atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (Formalism.BasicNotions.TH.fockAct2 P Q R S Z) T ∈ N := by
  intro hAL hLE F E _ _ _ _ _ σ B n d P Q R S X W om C Φ c hcm hC hθ hinj hact hadm N hN w Z hZ T hT
  have key := kstab_skew hAL hLE F E σ B n d P Q R S X W om C Φ c hcm hC hθ hinj hact hadm N hN w
  obtain ⟨Y1, hY1⟩ : ∃ Y1 : Mat R S, Y1 = (1 / 2 : ℂ) • (Z - Zᴴ) := ⟨_, rfl⟩
  obtain ⟨Y2, hY2⟩ : ∃ Y2 : Mat R S, Y2 = (1 / (2 * Complex.I)) • (Z + Zᴴ) := ⟨_, rfl⟩
  have hZ' : Z = Y1 + Complex.I • Y2 := by
    rw [hY1, hY2, smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add]
    rw [show Z - Zᴴ + (Z + Zᴴ) = (2 : ℂ) • Z by rw [two_smul]; abel, smul_smul]; norm_num
  have hZh : IsKC Zᴴ := isKC_conjTranspose hZ
  have k1 : IsKC Y1 := hY1 ▸ isKC_smul (by rw [sub_eq_add_neg]; exact isKC_add hZ (by simpa using isKC_smul hZh (-1))) _
  have k2 : IsKC Y2 := hY2 ▸ isKC_smul (isKC_add hZ hZh) _
  have s1 : Y1ᴴ = -Y1 := by
    rw [hY1, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
    rw [show star (1 / 2 : ℂ) = 1 / 2 by simp, ← smul_neg, neg_sub]
  have s2 : Y2ᴴ = -Y2 := by
    rw [hY2, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
    rw [show star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) by simp, neg_smul, add_comm]
  rw [hZ', map_add, map_smul, atPl_add', atPl_smul', LinearMap.add_apply, LinearMap.smul_apply]
  exact N.add_mem (key Y1 k1 s1 T hT) (N.smul_mem _ (key Y2 k2 s2 T hT))

end GlobalTheory.FockKStab
end
