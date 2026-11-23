import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteCompactLeviLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.KInfLevi

open Matrix

section Ring

variable {R : Type} [CommRing R] {d d₁ : ℕ}

theorem of_mul_eq {a b : Fin d → R} {K : Matrix (Fin d) (Fin d) R} (h : b ᵥ* K = b) :
    Matrix.of (fun i j => a i * b j) * K = Matrix.of (fun i j => a i * b j) := by
  ext i j
  have := congrFun h j
  simp only [vecMul, dotProduct] at this
  simp only [Matrix.mul_apply, Matrix.of_apply, mul_assoc, ← Finset.mul_sum, this]

theorem vecMul_fix (c : R →+* R) {J K : Matrix (Fin d) (Fin d) R} (hK : Kᵀ * J * K.map c = J)
    {y : Fin d → R} (hy : K *ᵥ y = y) : (J *ᵥ fun i => c (y i)) ᵥ* K = J *ᵥ fun i => c (y i) := by
  have hcy : (fun i => c (y i)) = K.map c *ᵥ fun i => c (y i) := by
    funext i
    conv_lhs => rw [← hy]
    exact RingHom.map_mulVec c K y i
  rw [← mulVec_transpose]
  conv_lhs => rw [hcy]
  rw [mulVec_mulVec, mulVec_mulVec, hK]

theorem mul_eq_of_fix {K : Matrix (Fin d) (Fin d) R} {ι : Matrix (Fin d) (Fin d₁) R} {π : Matrix (Fin d₁) (Fin d) R}
    {x y r r' : Fin d → R}
    (hQ : Matrix.of (fun i j => x i * r j) + ι * π - Matrix.of (fun i j => y i * r' j) = 1)
    (hπι : π * ι = 1) (hr : r ᵥ* K = r) (hr' : r' ᵥ* K = r') : K * ι = ι * (π * K * ι) := by
  set X := Matrix.of (fun i j => x i * r j) with hXd
  set Y := Matrix.of (fun i j => y i * r' j) with hYd
  have hX : X * K = X := of_mul_eq hr
  have hY : Y * K = Y := of_mul_eq hr'
  have h1 : ι = X * ι + ι - Y * ι := by
    conv_lhs => rw [← Matrix.one_mul ι, ← hQ]
    rw [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc ι, hπι, Matrix.mul_one]
  have h2 : X * ι - Y * ι = 0 := by
    have h3 : X * ι - Y * ι = (X * ι + ι - Y * ι) - ι := by abel
    rw [h3, ← h1, sub_self]
  calc K * ι = 1 * (K * ι) := (Matrix.one_mul _).symm
    _ = (X + ι * π - Y) * (K * ι) := by rw [hQ]
    _ = (X * ι - Y * ι) + ι * (π * K * ι) := by
      rw [Matrix.sub_mul, Matrix.add_mul, ← Matrix.mul_assoc X, hX, ← Matrix.mul_assoc Y, hY]
      simp only [Matrix.mul_assoc]
      abel
    _ = _ := by rw [h2, zero_add]

theorem unitary_of_mul (c : R →+* R) {J K : Matrix (Fin d) (Fin d) R} {J₁ K₁ : Matrix (Fin d₁) (Fin d₁) R}
    {ι : Matrix (Fin d) (Fin d₁) R} (hK : Kᵀ * J * K.map c = J) (hg : ιᵀ * J * ι.map c = J₁) (h : K * ι = ι * K₁) :
    K₁ᵀ * J₁ * K₁.map c = J₁ := by
  rw [← hg]
  calc K₁ᵀ * (ιᵀ * J * ι.map c) * K₁.map c = (ι * K₁)ᵀ * J * (ι * K₁).map c := by
        rw [transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
    _ = (K * ι)ᵀ * J * (K * ι).map c := by rw [h]
    _ = ιᵀ * (Kᵀ * J * K.map c) * ι.map c := by rw [transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hK]

theorem comm_of {S : Type} [CommRing S] {θ Kw : Matrix (Fin d) (Fin d) S} {θ₁ : Matrix (Fin d₁) (Fin d₁) S}
    {ι : Matrix (Fin d) (Fin d₁) S} {π : Matrix (Fin d₁) (Fin d) S} (hθι : θ * ι = ι * θ₁) (hπθ : π * θ = θ₁ * π)
    (hK : Commute Kw θ) : Commute (π * Kw * ι) θ₁ := by
  show π * Kw * ι * θ₁ = θ₁ * (π * Kw * ι)
  rw [Matrix.mul_assoc, ← hθι, ← Matrix.mul_assoc, Matrix.mul_assoc π, hK.eq, ← Matrix.mul_assoc, hπθ]
  simp only [Matrix.mul_assoc]

end Ring

theorem exists_kInf_isLevi_of_fix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ i₀ i₁ r s r₁ s₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁), B.IsGood σ → W.IsSkew σ B r s →
    W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (Rn Sn : ℕ) (r₀ : Fin Rn) (s₀ : Fin Sn) (C : InfinitePlace F → Matrix (Fin d) (Formalism.BasicNotions.TH.Ix Rn Sn) ℂ),
    (∀ w, GlobalTheory.RealLift.IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w)) →
    (∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm Rn Sn) → GlobalTheory.FockBridge.IsAdaptedFrame B H' C r₀ s₀ →
    ∀ k ∈ KInf σ W B.emb, (∀ w, (∀ i, ((mat k).map (piInf (B.emb w)) * C w) i (.inl r₀) = C w i (.inl r₀)) ∧
        ∀ i, ((mat k).map (piInf (B.emb w)) * C w) i (.inr s₀) = C w i (.inr s₀)) →
      ∃ k₁ ∈ KInf σ W₁ B.emb, IsLevi H' 1 k₁ k := by
  intro F E _ _ _ _ _ σ B d d₁ i₀ i₁ r s r₁ s₁ W W₁ H' hB hW hW₁ hA Rn Sn r₀ s₀ C _hFr _hθC hAd k hk hcol
  have hσ : ∀ z, σ (σ z) = z := GlobalTheory.LeviTorus.sigma_invol hB.cm
  obtain ⟨π, p1, p2, p3, p4, p5⟩ := GlobalTheory.LeviUnitary.exists_proj hB hW hW₁ hA
  have hid := GlobalTheory.LeviKInf.frame_id hσ hW hA π p1 p4 p5
  have q1 : incM F π * incM F H'.ι = 1 := by
    rw [← GlobalTheory.LeviUnitary.incM_mul, p1]; exact Matrix.map_one _ (map_zero _) (map_one _)

  have hfixv : ∀ z : Fin d → E, (∀ w, (mat k).map (piInf (B.emb w)) *ᵥ (fun i => (B.emb w).1 (z i)) =
      fun i => (B.emb w).1 (z i)) → mat k *ᵥ incV F z = incV F z := by
    intro z hz
    funext i
    rw [← sub_eq_zero]
    have e : (mat k *ᵥ incV F z) i - incV F z i = ((mat k - 1) *ᵥ incV F z) i := by
      rw [sub_mulVec, one_mulVec]; rfl
    rw [e]
    apply GlobalTheory.RealLift.KLineProof.eq_zero_of_piInf hB.cm B.emb
    · intro u hu
      have h0 : u • (mat k - 1) = 0 := hk.1 u hu
      have : u • ((mat k - 1) *ᵥ incV F z) i = ((u • (mat k - 1)) *ᵥ incV F z) i := by
        simp [mulVec, dotProduct, Finset.smul_sum, smul_mul_assoc]
      rw [this, h0, zero_mulVec]; rfl
    · intro w
      have h1 := RingHom.map_mulVec (piInf (B.emb w)) (mat k - 1) (incV F z) i
      rw [h1, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
      have h2 : (piInf (B.emb w)) ∘ incV F z = fun i => (B.emb w).1 (z i) := by
        funext j; exact GlobalTheory.IwaAdelicIso.piInf_inclR _ _
      rw [h2, sub_mulVec, one_mulVec, hz w]; simp
  have ecol : ∀ w (M : Matrix (Fin d) (Fin d) ℂ) (a b : ℂ) i,
      (M *ᵥ fun j => a * C w j (.inl r₀) + b * C w j (.inr s₀)) i =
        a * (M * C w) i (.inl r₀) + b * (M * C w) i (.inr s₀) := by
    intro w M a b i
    simp only [mulVec, dotProduct, Matrix.mul_apply, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun j _ => by ring
  have hKx : mat k *ᵥ incV F H'.x = incV F H'.x := by
    apply hfixv
    intro w
    obtain ⟨⟨c, -, hc⟩, -, -⟩ := hAd w
    obtain ⟨h1, h2⟩ := hcol w
    have hxw : (fun i => (B.emb w).1 (H'.x i)) = fun j => c * C w j (.inl r₀) + c * C w j (.inr s₀) := by
      funext j; rw [hc j, mul_add]
    rw [hxw]; funext i; rw [ecol, h1 i, h2 i]
  have hKy : mat k *ᵥ incV F H'.y = incV F H'.y := by
    apply hfixv
    intro w
    obtain ⟨-, ⟨c₁, c₂, hc⟩, -⟩ := hAd w
    obtain ⟨h1, h2⟩ := hcol w
    have hyw : (fun i => (B.emb w).1 (H'.y i)) = fun j => c₁ * C w j (.inl r₀) + c₂ * C w j (.inr s₀) := by
      funext j; rw [hc j]
    rw [hyw]; funext i; rw [ecol, h1 i, h2 i]

  have hrr : ∀ z : Fin d → E, incV F (W.J *ᵥ fun k => σ (z k)) = incM F W.J *ᵥ fun i => cA σ (incV F z i) := by
    intro z
    have e : (fun i => cA σ (incV F z i)) = incV F (fun k => σ (z k)) := by
      funext i; exact GlobalTheory.LeviTorus.cA_incl σ (z i)
    rw [e, GlobalTheory.LeviUnitary.incM_mulVec]
  have hidA : Matrix.of (fun i j => incV F H'.x i * incV F (W.J *ᵥ fun k => σ (H'.y k)) j) +
      incM F H'.ι * incM F π - Matrix.of (fun i j => incV F H'.y i * incV F (W.J *ᵥ fun k => σ (H'.x k)) j) = 1 := by
    have h := congrArg (fun A => A.map (inclR (F := F) (AF F))) hid
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _), Matrix.map_mul,
      Matrix.map_one _ (map_zero _) (map_one _)] at h
    rw [← h]
    congr 1
    · congr 1
      ext i j; simp [incV, map_mul]
    · ext i j; simp [incV, map_mul]
  have hKu : (mat k)ᵀ * incM F W.J * (mat k).map (cA σ).toRingHom = incM F W.J := k.2
  have hrx : incV F (W.J *ᵥ fun k => σ (H'.y k)) ᵥ* mat k = incV F (W.J *ᵥ fun k => σ (H'.y k)) := by
    rw [hrr]; exact vecMul_fix (cA σ).toRingHom hKu hKy
  have hry : incV F (W.J *ᵥ fun k => σ (H'.x k)) ᵥ* mat k = incV F (W.J *ᵥ fun k => σ (H'.x k)) := by
    rw [hrr]; exact vecMul_fix (cA σ).toRingHom hKu hKx
  have hKK' : mat k * (k.1⁻¹).1 = 1 := by rw [mat, Units.mul_inv]
  have hK'K : (k.1⁻¹).1 * mat k = 1 := by rw [mat, Units.inv_mul]
  have hKι : mat k * incM F H'.ι = incM F H'.ι * (incM F π * mat k * incM F H'.ι) :=
    mul_eq_of_fix hidA q1 hrx hry
  have hK'ι : (k.1⁻¹).1 * incM F H'.ι = incM F H'.ι * (incM F π * (k.1⁻¹).1 * incM F H'.ι) := by
    refine mul_eq_of_fix hidA q1 ?_ ?_
    · conv_lhs => rw [← hrx]
      rw [vecMul_vecMul, hKK', vecMul_one]
    · conv_lhs => rw [← hry]
      rw [vecMul_vecMul, hKK', vecMul_one]
  have hg : (incM F H'.ι)ᵀ * incM F W.J * (incM F H'.ι).map (cA σ).toRingHom = incM F W₁.J := by
    rw [GlobalTheory.LeviUnitary.incM_conj, ← hA.gram, GlobalTheory.LeviUnitary.incM_mul, GlobalTheory.LeviUnitary.incM_mul]; rfl
  refine ⟨⟨⟨incM F π * mat k * incM F H'.ι, incM F π * (k.1⁻¹).1 * incM F H'.ι, ?_, ?_⟩, ?_⟩, ⟨?_, fun w => ?_⟩,
    ?_, ?_, ?_⟩
  · calc incM F π * mat k * incM F H'.ι * (incM F π * (k.1⁻¹).1 * incM F H'.ι)
        = incM F π * mat k * (incM F H'.ι * (incM F π * (k.1⁻¹).1 * incM F H'.ι)) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [← hK'ι, Matrix.mul_assoc (incM F π), ← Matrix.mul_assoc (mat k), hKK', Matrix.one_mul, q1]
  · calc incM F π * (k.1⁻¹).1 * incM F H'.ι * (incM F π * mat k * incM F H'.ι)
        = incM F π * (k.1⁻¹).1 * (incM F H'.ι * (incM F π * mat k * incM F H'.ι)) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [← hKι, Matrix.mul_assoc (incM F π), ← Matrix.mul_assoc ((k.1⁻¹).1), hK'K, Matrix.one_mul, q1]
  · exact unitary_of_mul (cA σ).toRingHom hKu hg hKι
  · show At (evI F) (incM F π * mat k * incM F H'.ι - 1)
    have e : incM F π * mat k * incM F H'.ι - 1 = incM F π * (mat k - 1) * incM F H'.ι := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, q1]
    rw [e]
    intro u hu
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hk.1 u hu, Matrix.mul_zero, Matrix.zero_mul]
  · set τ : E →+* ℂ := (B.emb w).1 with hτ
    show Commute ((incM F π * mat k * incM F H'.ι).map (piInf (B.emb w))) (W₁.θ w)
    rw [Matrix.map_mul, Matrix.map_mul, GlobalTheory.LeviKInf.incM_map_piInf, GlobalTheory.LeviKInf.incM_map_piInf]
    obtain ⟨hθι, c, hc, hy⟩ := hA.cartan w
    have hidw : Matrix.of (fun i j => τ (H'.x i) * τ ((W.J *ᵥ fun k => σ (H'.y k)) j)) + H'.ι.map τ * π.map τ -
        Matrix.of (fun i j => τ (H'.y i) * τ ((W.J *ᵥ fun k => σ (H'.x k)) j)) = 1 := by
      rw [← Matrix.map_one τ (map_zero τ) (map_one τ), ← hid]
      ext i j
      simp [Matrix.mul_apply, map_sum, map_mul]
    have hπι : π.map τ * H'.ι.map τ = 1 := by
      rw [← Matrix.map_mul, p1, Matrix.map_one _ (map_zero τ) (map_one τ)]
    have hπθ := GlobalTheory.LeviKInf.proj_comm (W.θ w) (W₁.θ w) (H'.ι.map τ) (π.map τ) _ _ _ _ c hidw (hW.cartan w).1 hθι hc hy
      hπι (GlobalTheory.LeviKInf.map_mulVec_zero τ π _ p4) (GlobalTheory.LeviKInf.map_mulVec_zero τ π _ p5)
    have hKθ : Commute ((mat k).map (piInf (B.emb w))) (W.θ w) := hk.2 w
    exact comm_of hθι hπθ hKθ
  · rw [Units.val_one, one_smul]; exact hKx
  · rw [inv_one, Units.val_one, map_one, one_smul]; exact hKy
  · exact hKι

end GlobalTheory.KInfLevi

end
