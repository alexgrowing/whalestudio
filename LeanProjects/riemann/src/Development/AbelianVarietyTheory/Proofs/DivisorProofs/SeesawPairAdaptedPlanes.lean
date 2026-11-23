import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairDescendsAlongAdaptedPlane

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedLagrXW

theorem hTens_sandwich {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
    {α β γ δ γ' δ' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [Fintype δ]
    [Fintype γ'] [Fintype δ'] (JA : Matrix α α E) (JB : Matrix β β E)
    (P : Matrix α γ E) (Z : Matrix γ δ E) (Q : Matrix β δ E) (P' : Matrix α γ' E) (Z' : Matrix γ' δ' E) (Q' : Matrix β δ' E) :
    hTens c JA JB (P * Z * Qᵀ) (P' * Z' * Q'ᵀ) =
      Matrix.trace (Zᵀ * (Pᵀ * JA * P'.map c) * Z'.map c * (Qᵀ * JB * Q'.map c)ᵀ) := by
  rw [GlobalTheory.MixedLagrGram.hTens_eq_trace]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.transpose_map, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm Q]
  simp only [Matrix.mul_assoc]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem span_decomp {B : Base F E} {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {i₀ i₁ : ℕ}
    (hlat : Y.L.IsLattice E) (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (z : Fin n → E) :
    ∃ (s t : E) (u : Fin n₁ → E), z = s • H.x + H.ι *ᵥ u + t • H.y := by
  have hm : z ∈ Submodule.span E (Y.L : Set (Fin n → E)) := by
    rw [Submodule.IsLattice.span_eq_top (self := hlat)]; trivial
  induction hm using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨s, t, u, -, -, -, h⟩ := hH.split z hz
    exact ⟨s, t, u, h⟩
  | zero => exact ⟨0, 0, 0, by simp⟩
  | add z z' _ _ h h' =>
    obtain ⟨s, t, u, rfl⟩ := h
    obtain ⟨s', t', u', rfl⟩ := h'
    exact ⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩
  | smul c z _ h =>
    obtain ⟨s, t, u, rfl⟩ := h
    exact ⟨c * s, c * t, c • u, by rw [Matrix.mulVec_smul]; module⟩

theorem indep {B : Base F E} {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {i₀ i₁ : ℕ}
    (hlat : Y.L.IsLattice E) (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (s t : E) (u : Fin n₁ → E)
    (h : s • H.x + H.ι *ᵥ u + t • H.y = 0) : s = 0 ∧ u = 0 ∧ t = 0 := by
  let b : Fin n₁ ⊕ Fin 2 → (Fin n → E) := Sum.elim (fun k i => H.ι i k) ![H.x, H.y]
  have hsum : ∀ g : Fin n₁ ⊕ Fin 2 → E, ∑ i, g i • b i = g (Sum.inr 0) • H.x + H.ι *ᵥ (g ∘ Sum.inl) + g (Sum.inr 1) • H.y := by
    intro g
    rw [Fintype.sum_sum_type, Fin.sum_univ_two]
    funext i
    simp [b, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    ring
  have hli : LinearIndependent E b := by
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ ?_
    · intro z _
      obtain ⟨s, t, u, rfl⟩ := span_decomp hlat hH z
      have : s • H.x + H.ι *ᵥ u + t • H.y = ∑ i, (Sum.elim u ![s, t]) i • b i := by
        rw [hsum]; rfl
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · simp [hH.rank]
  have h0 := Fintype.linearIndependent_iff.1 hli (Sum.elim u ![s, t]) (by rw [hsum]; exact h)
  exact ⟨h0 (Sum.inr 0), funext fun k => h0 (Sum.inl k), h0 (Sum.inr 1)⟩

section Orth

variable {B : Base F E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
  {H : Plane E n n₁} {H' : Plane E d d₁} {j₀ j₁ i₀ i₁ : ℕ}

open GlobalTheory.MixedLagrX in
theorem replicateCol_transpose_mul_J_mul_map_eq_zero_of_isAdapted {k k₁ : ℕ} {Y : Spc F E k} {Y₁ : Spc F E k₁} {G : Plane E k k₁} {a b : ℕ} (hG : G.IsAdapted σ B Y Y₁ a b) :
    (Matrix.replicateCol Unit G.x)ᵀ * Y.J * (Matrix.replicateCol Unit G.x).map σ = 0 := by
  ext i j
  rw [gram_apply]
  exact hG.xx

open GlobalTheory.MixedLagrX in
theorem gram_ιx {k k₁ : ℕ} {Y : Spc F E k} {Y₁ : Spc F E k₁} {G : Plane E k k₁} {a b : ℕ} (hG : G.IsAdapted σ B Y Y₁ a b) :
    G.ιᵀ * Y.J * (Matrix.replicateCol Unit G.x).map σ = 0 := by
  ext i j
  rw [gram_apply]
  have := (hG.orth (Pi.single i 1)).1
  rw [Matrix.mulVec_single_one] at this
  exact this

theorem incM_one' {m : ℕ} : incM F (1 : Matrix (Fin m) (Fin m) E) = 1 := by
  simp only [incM]; exact Matrix.map_one _ (map_zero _) (map_one _)

theorem repA (y : Fin n → AE F E) (w : Fin d → E) :
    Matrix.vecMulVec y (incV F w) =
      incM F (1 : Matrix (Fin n) (Fin n) E) * Matrix.replicateCol Unit y * (incM F (Matrix.replicateCol Unit w))ᵀ := by
  rw [incM_one', Matrix.one_mul]
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.mul_apply, incM, incV]

theorem repB (x : Fin n → E) (ι' : Matrix (Fin d) (Fin d₁) E) (z₂ : Fin d₁ → AE F E) :
    Matrix.vecMulVec (incV F x) (incM F ι' *ᵥ z₂) =
      incM F (Matrix.replicateCol Unit x) * Matrix.replicateRow Unit z₂ * (incM F ι')ᵀ := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.mul_apply, incM, incV, Matrix.mulVec, dotProduct, Finset.mul_sum,
    Matrix.replicateCol_apply, Matrix.replicateRow_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.univ_unique,
    Finset.sum_singleton]
  exact Finset.sum_congr rfl fun k _ => by ring

variable (σ) in

abbrev sy (X : Spc F E n) (W : Spc F E d) := symp (cA σ) (-1 : AE F E) (incM F X.J) (incM F W.J)

open GlobalTheory.MixedLagrX in
theorem sAA (hH' : H'.IsAdapted σ B W W₁ i₀ i₁) (y y' : Fin n → AE F E) :
    sy σ X W (Matrix.vecMulVec y (incV F H'.x)) (Matrix.vecMulVec y' (incV F H'.x)) = 0 := by
  rw [sy, symp, repA, repA, hTens_sandwich, incM_gram, incM_gram, replicateCol_transpose_mul_J_mul_map_eq_zero_of_isAdapted hH', incM_zero]
  simp

open GlobalTheory.MixedLagrX in
theorem sBA (hH' : H'.IsAdapted σ B W W₁ i₀ i₁) (z₂ : Fin d₁ → AE F E) (y' : Fin n → AE F E) :
    sy σ X W (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z₂)) (Matrix.vecMulVec y' (incV F H'.x)) = 0 := by
  rw [sy, symp, repB, repA, hTens_sandwich, incM_gram, incM_gram, gram_ιx hH', incM_zero]
  simp

open GlobalTheory.MixedLagrX in
theorem sCA (hH' : H'.IsAdapted σ B W W₁ i₀ i₁) (z : Matrix (Fin n₁) (Fin d₁) (AE F E)) (y' : Fin n → AE F E) :
    sy σ X W (incM F H.ι * z * (incM F H'.ι)ᵀ) (Matrix.vecMulVec y' (incV F H'.x)) = 0 := by
  rw [sy, symp, repA, hTens_sandwich, incM_gram, incM_gram, gram_ιx hH', incM_zero]
  simp

open GlobalTheory.MixedLagrX in
theorem sBB (hH : H.IsAdapted σ B X X₁ j₀ j₁) (z₂ z₂' : Fin d₁ → AE F E) :
    sy σ X W (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z₂)) (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z₂')) = 0 := by
  rw [sy, symp, repB, repB, hTens_sandwich, incM_gram, incM_gram, replicateCol_transpose_mul_J_mul_map_eq_zero_of_isAdapted hH, incM_zero]
  simp

open GlobalTheory.MixedLagrX in
theorem sCB (hH : H.IsAdapted σ B X X₁ j₀ j₁) (z : Matrix (Fin n₁) (Fin d₁) (AE F E)) (z₂' : Fin d₁ → AE F E) :
    sy σ X W (incM F H.ι * z * (incM F H'.ι)ᵀ) (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z₂')) = 0 := by
  rw [sy, symp, repB, hTens_sandwich, incM_gram, incM_gram, gram_ιx hH, incM_zero]
  simp

open GlobalTheory.MixedLagrX in
theorem sCC (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hH' : H'.IsAdapted σ B W W₁ i₀ i₁) (z z' : Matrix (Fin n₁) (Fin d₁) (AE F E)) :
    sy σ X W (incM F H.ι * z * (incM F H'.ι)ᵀ) (incM F H.ι * z' * (incM F H'.ι)ᵀ) = sy σ X₁ W₁ z z' := by
  rw [sy, sy, symp, symp, hTens_sandwich, incM_gram, incM_gram, hH.gram, hH'.gram, GlobalTheory.MixedLagrGram.hTens_eq_trace]

end Orth

section Inj
variable {B : Base F E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
  {H : Plane E n n₁} {H' : Plane E d d₁} {j₀ j₁ i₀ i₁ : ℕ}

theorem row_eq (y : Fin n → E) (z₂ : Fin d₁ → E) (z : Matrix (Fin n₁) (Fin d₁) E) (i : Fin n) :
    (Matrix.vecMulVec y H'.x + Matrix.vecMulVec H.x (H'.ι *ᵥ z₂) + H.ι * z * H'.ιᵀ) i =
      y i • H'.x + H'.ι *ᵥ (H.x i • z₂ + (H.ι * z) i) + (0 : E) • H'.y := by
  funext j
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, add_zero,
    Matrix.mulVec, dotProduct, Matrix.mul_apply (M := H.ι * z), Matrix.transpose_apply, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  rw [add_assoc]
  congr 1
  congr 1 <;> exact Finset.sum_congr rfl fun k _ => by ring

theorem mixed_injective (hX : X.L.IsLattice E) (hW : W.L.IsLattice E) (hH : H.IsAdapted σ B X X₁ j₀ j₁)
    (hH' : H'.IsAdapted σ B W W₁ i₀ i₁) (y : Fin n → E) (z₂ : Fin d₁ → E) (z : Matrix (Fin n₁) (Fin d₁) E)
    (h : Matrix.vecMulVec y H'.x + Matrix.vecMulVec H.x (H'.ι *ᵥ z₂) + H.ι * z * H'.ιᵀ = 0) :
    y = 0 ∧ z₂ = 0 ∧ z = 0 := by
  have hr : ∀ i, y i = 0 ∧ H.x i • z₂ + (H.ι * z) i = 0 := by
    intro i
    have := congrFun h i
    rw [row_eq] at this
    obtain ⟨a, b, -⟩ := indep hW hH' _ _ _ this
    exact ⟨a, b⟩
  have hc : ∀ j, z₂ j = 0 ∧ (fun k => z k j) = 0 := by
    intro j
    have e : z₂ j • H.x + H.ι *ᵥ (fun k => z k j) + (0 : E) • H.y = 0 := by
      funext i
      have := congrFun (hr i).2 j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Pi.zero_apply] at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, add_zero, Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← this, mul_comm]
    obtain ⟨a, b, -⟩ := indep hX hH _ _ _ e
    exact ⟨a, b⟩
  refine ⟨funext fun i => (hr i).1, funext fun j => (hc j).1, ?_⟩
  ext k j
  exact congrFun (hc j).2 k

end Inj

section Main
variable {B : Base F E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
  {H : Plane E n n₁} {H' : Plane E d d₁} {j₀ j₁ i₀ i₁ : ℕ}

theorem orth_pieces (M : Model σ X W) (M₁ : Model σ X₁ W₁) (hH : H.IsAdapted σ B X X₁ j₀ j₁)
    (hH' : H'.IsAdapted σ B W W₁ i₀ i₁) (y y' : Fin n → AE F E) (z₂ z₂' : Fin d₁ → AE F E)
    (z z' : Matrix (Fin n₁) (Fin d₁) (AE F E)) :
    (M.co.e (Matrix.vecMulVec y (incV F H'.x))).1 ⬝ᵥ
        (M.co.e (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z₂) + incM F H.ι * z * (incM F H'.ι)ᵀ)).2 -
      (M.co.e (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z₂) + incM F H.ι * z * (incM F H'.ι)ᵀ)).1 ⬝ᵥ
        (M.co.e (Matrix.vecMulVec y (incV F H'.x))).2 = 0 ∧
    (M.co.e (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z₂))).1 ⬝ᵥ (M.co.e (incM F H.ι * z * (incM F H'.ι)ᵀ)).2 -
      (M.co.e (incM F H.ι * z * (incM F H'.ι)ᵀ)).1 ⬝ᵥ (M.co.e (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z₂))).2 = 0 ∧
    ((M₁.co.e z).1 = 0 → (M₁.co.e z').1 = 0 →
      (M.co.e (Matrix.vecMulVec y (incV F H'.x) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z₂) +
          incM F H.ι * z * (incM F H'.ι)ᵀ)).1 ⬝ᵥ
        (M.co.e (Matrix.vecMulVec y' (incV F H'.x) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z₂') +
          incM F H.ι * z' * (incM F H'.ι)ᵀ)).2 =
      (M.co.e (Matrix.vecMulVec y' (incV F H'.x) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z₂') +
          incM F H.ι * z' * (incM F H'.ι)ᵀ)).1 ⬝ᵥ
        (M.co.e (Matrix.vecMulVec y (incV F H'.x) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z₂) +
          incM F H.ι * z * (incM F H'.ι)ᵀ)).2) := by
  have hD : ∀ p q, sy σ X W p q = (M.co.e p).1 ⬝ᵥ (M.co.e q).2 - (M.co.e q).1 ⬝ᵥ (M.co.e p).2 := M.co.form
  have ba := sBA (X := X) (H := H) hH' z₂ y
  have ca := sCA (X := X) (H := H) hH' z y
  have cb := sCB (W := W) (H' := H') hH z z₂
  rw [hD] at ba ca cb
  refine ⟨?_, ?_, fun hz hz' => ?_⟩
  · simp only [map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
    linear_combination -ba - ca
  · linear_combination -cb
  · have aa := sAA (X := X) hH' y y'
    have ba' := sBA (X := X) (H := H) hH' z₂' y
    have ca' := sCA (X := X) (H := H) hH' z' y
    have ba₂ := sBA (X := X) (H := H) hH' z₂ y'
    have bb := sBB (W := W) (H' := H') hH z₂ z₂'
    have cb' := sCB (W := W) (H' := H') hH z' z₂
    have ca₂ := sCA (X := X) (H := H) hH' z y'
    have cb₂ := sCB (W := W) (H' := H') hH z z₂'
    have cc := sCC hH hH' z z'
    have cc' : sy σ X₁ W₁ z z' = 0 := by
      rw [sy, M₁.co.form, hz, hz', zero_dotProduct, zero_dotProduct, sub_zero]
    rw [cc'] at cc
    rw [hD] at aa ba' ca' ba₂ bb cb' ca₂ cb₂ cc
    simp only [map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
    linear_combination aa - ba' - ca' + ba₂ + bb - cb' + ca₂ + cb₂ + cc

end Main

theorem exists_ratLagr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ : ℕ) (M₁ : Model σ X₁ W₁),
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∃ L : Submodule F ((Fin n × Fin d → F) × (Fin n × Fin d → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
      Module.finrank F L = Fintype.card (Fin n × Fin d) ∧
      ∀ (t : AF F), ∀ w ∈ L, ∃ (y : Fin n → AE F E) (z₂ : Fin d₁ → AE F E) (z : Matrix (Fin n₁) (Fin d₁) (AE F E)),
        (M₁.co.e z).1 = 0 ∧ ∀ φ : (Fin n × Fin d → AF F) → ℂ,
          schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ =
            M.co.rho B.ψ (Matrix.vecMulVec y (incV F H'.x))
              (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z₂))
                (M.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) φ)) := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M χX χW om r s r' s' hP H H' j₀ j₁ i₀ i₁ M₁ hH hH' hM₁
  obtain ⟨f, hf, hfe⟩ := GlobalTheory.MixedLagrX.exists_ratMap M hP.good.rat
  obtain ⟨f₁, hf₁, hfe₁⟩ := GlobalTheory.MixedLagrX.exists_ratMap M₁ hM₁.rat
  have h2 : Module.finrank F E = 2 := hP.base.cm.2.2.1
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  obtain ⟨K, hK, hKz⟩ := GlobalTheory.MixedLagr.rat_first_zero_dim F E σ n₁ d₁ X₁ W₁ M₁ h2 f₁ hf₁ hfe₁
  let Φ : (Fin n → E) × (Fin d₁ → E) × K →ₗ[F] Matrix (Fin n) (Fin d) E :=
    { toFun := fun p => Matrix.vecMulVec p.1 H'.x + Matrix.vecMulVec H.x (H'.ι *ᵥ p.2.1) +
        H.ι * (p.2.2 : Matrix (Fin n₁) (Fin d₁) E) * H'.ιᵀ
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Matrix.add_vecMulVec, Matrix.mulVec_add,
          Matrix.vecMulVec_add, Matrix.mul_add, Matrix.add_mul]
        abel
      map_smul' := fun c p => by
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, Matrix.smul_vecMulVec, Matrix.mulVec_smul,
          Matrix.vecMulVec_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_add] }
  have hΦ : ∀ p, Φ p = Matrix.vecMulVec p.1 H'.x + Matrix.vecMulVec H.x (H'.ι *ᵥ p.2.1) +
      H.ι * (p.2.2 : Matrix (Fin n₁) (Fin d₁) E) * H'.ιᵀ := fun _ => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    obtain ⟨h1, h2, h3⟩ := mixed_injective hP.herm.lat hP.skew.lat hH hH' _ _ _ hp
    exact Prod.ext h1 (Prod.ext h2 (Subtype.ext h3))
  have hhat : ∀ p, GlobalTheory.MixedLagr.hat (f (Φ p)) = M.co.e (Matrix.vecMulVec (incV F p.1) (incV F H'.x) +
      Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ incV F p.2.1) +
      incM F H.ι * incM F (p.2.2 : Matrix (Fin n₁) (Fin d₁) E) * (incM F H'.ι)ᵀ) := by
    intro p
    rw [hfe, hΦ]
    congr 1
    ext i j
    simp [incM, incV, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine ⟨LinearMap.range (f ∘ₗ Φ), ?_, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    have h := (orth_pieces M M₁ hH hH' (incV F p.1) (incV F q.1) (incV F p.2.1) (incV F q.2.1)
      (incM F (p.2.2 : Matrix (Fin n₁) (Fin d₁) E)) (incM F (q.2.2 : Matrix (Fin n₁) (Fin d₁) E))).2.2
      (hKz _ p.2.2.2) (hKz _ q.2.2.2)
    rw [← hhat, ← hhat] at h
    apply AdeleRing.algebraMap_injective (𝓞 F) F
    rw [RingHom.map_dotProduct, RingHom.map_dotProduct]
    exact h
  · rw [LinearMap.finrank_range_of_inj (f := f ∘ₗ Φ) (hf.comp hinj), Module.finrank_prod, Module.finrank_prod,
      Module.finrank_pi_fintype, Module.finrank_pi_fintype, hK]
    simp [h2, hH.rank, hH'.rank]
    ring
  · rintro t _ ⟨p, rfl⟩
    have hz : (M₁.co.e (t • incM F (p.2.2 : Matrix (Fin n₁) (Fin d₁) E))).1 = 0 := by
      rw [LinearEquiv.map_smul, Prod.smul_fst, hKz _ p.2.2.2, smul_zero]
    refine ⟨t • incV F p.1, t • incV F p.2.1, t • incM F (p.2.2 : Matrix (Fin n₁) (Fin d₁) E), hz, fun φ => ?_⟩
    have he : t • GlobalTheory.MixedLagr.hat (f (Φ p)) = M.co.e (Matrix.vecMulVec (t • incV F p.1) (incV F H'.x) +
        Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ (t • incV F p.2.1)) +
        incM F H.ι * (t • incM F (p.2.2 : Matrix (Fin n₁) (Fin d₁) E)) * (incM F H'.ι)ᵀ) := by
      rw [hhat, ← LinearEquiv.map_smul]
      congr 1
      rw [Matrix.smul_vecMulVec, Matrix.mulVec_smul, Matrix.vecMulVec_smul, Matrix.mul_smul, Matrix.smul_mul, smul_add,
        smul_add]
    obtain ⟨o1, o2, -⟩ := orth_pieces M M₁ hH hH' (t • incV F p.1) (t • incV F p.1) (t • incV F p.2.1) (t • incV F p.2.1)
      (t • incM F (p.2.2 : Matrix (Fin n₁) (Fin d₁) E)) (t • incM F (p.2.2 : Matrix (Fin n₁) (Fin d₁) E))
    show schr B.ψ (t • GlobalTheory.MixedLagr.hat (f (Φ p))) φ = _
    rw [he]
    simp only [Darboux.rho]
    set Am := Matrix.vecMulVec (t • incV F p.1) (incV F H'.x)
    set Bm := Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ (t • incV F p.2.1))
    set Cm := incM F H.ι * (t • incM F (p.2.2 : Matrix (Fin n₁) (Fin d₁) E)) * (incM F H'.ι)ᵀ
    have k1 := GlobalTheory.MixedLagr.schr_comp B.ψ (M.co.e Bm) (M.co.e Cm) φ
    rw [o2, mul_zero, AddChar.map_zero_eq_one, one_smul, ← map_add] at k1
    have k2 := GlobalTheory.MixedLagr.schr_comp B.ψ (M.co.e Am) (M.co.e (Bm + Cm)) φ
    rw [o1, mul_zero, AddChar.map_zero_eq_one, one_smul, ← map_add, ← add_assoc] at k2
    rw [k1, k2]

end GlobalTheory.MixedLagrXW
