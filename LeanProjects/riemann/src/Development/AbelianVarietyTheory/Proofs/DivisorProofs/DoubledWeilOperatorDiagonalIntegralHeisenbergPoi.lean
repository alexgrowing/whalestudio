import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormEqZeroOfLagrangianAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneSeesaw
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.InertLagChar

theorem at_mul_left' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    {a b c : Type} [Fintype b] (P : Matrix a b (AE F E)) {z : Matrix b c (AE F E)} (hz : At (evFin F v) z) :
    At (evFin F v) (P * z) := fun u hu => by rw [← Matrix.mul_smul, hz u hu, Matrix.mul_zero]

theorem at_mul_right' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    {a b c : Type} [Fintype b] {z : Matrix a b (AE F E)} (hz : At (evFin F v) z) (P : Matrix b c (AE F E)) :
    At (evFin F v) (z * P) := fun u hu => by rw [← Matrix.smul_mul, hz u hu, Matrix.zero_mul]

theorem at_fromCols_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    {a b c : Type} {u : Matrix a b (AE F E)} (hu : At (evFin F v) u) :
    At (evFin F v) (Matrix.fromCols uᵀ (0 : Matrix b c (AE F E))) := fun t ht => by
  ext i j
  rcases j with j | j
  · have := congrArg (fun M => M j i) (hu t ht)
    simpa using this
  · simp

theorem fromCols_add_fromCols {R : Type} [Add R] {a b c : Type} (x z : Matrix a b R) (y w : Matrix a c R) :
    Matrix.fromCols x y + Matrix.fromCols z w = Matrix.fromCols (x + z) (y + w) := by
  ext i j; rcases j with j | j <;> rfl

theorem fromCols_mul_transpose_split {R : Type} [CommRing R] {a b : Type} [Fintype a] (u : Matrix a b R)
    (P : Matrix (a ⊕ a) (a ⊕ a) R) :
    Matrix.fromCols uᵀ (0 : Matrix b a R) * Pᵀ =
      Matrix.fromCols (P.toBlocks₂₁ * u)ᵀ (P.toBlocks₂₁ * u)ᵀ + Matrix.fromCols ((P.toBlocks₁₁ - P.toBlocks₂₁) * u)ᵀ 0 := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks P, Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks]
  rw [fromCols_add_fromCols]
  simp only [Matrix.zero_mul, add_zero, Matrix.transpose_mul, Matrix.transpose_sub, Matrix.mul_sub]
  congr 1
  abel

theorem diagW_omd_point : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W)
    (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ (v : Pl F) (m : ℕ) (C : Matrix (Fin d) (Fin m) (AE F E)), IsLagrAt σ W v C →
    ∀ d' : Darboux (symp (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d),
    (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
    ∀ dd : Darboux (symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
    IsDblCoord (cA σ) (-1) (incM F W.J) (incM F X.J) d' dd →
    ∀ omd : UG (cA σ) (dbl (incM F X.J)) →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ),
    IsSplitting (adeleClass F) ψ dd (actB (cA σ)) omd →
    ∀ l : (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] ℂ,
    (∀ z : Matrix (Fin d) (Fin n) (AE F E), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
      l (dd.rho ψ (z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) Φ) = l Φ) →
    ∀ r₀ : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ,
    (∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), Rest (evFin F v) φ r₀) →
    ∀ c₀ : ℂ, c₀ ≠ 0 → ∀ μ : @Measure (Fin n × Fin d → Fv F v) (borel _),
    (∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), l (tens (evFin F v) φ r₀) = c₀ * ∫ x, φ (Sum.elim x x) ∂μ) →
    ∀ (p : UG (cA σ) (dbl (incM F X.J))) (ρ₀ : ℂ),
    (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), l (omd p Φ) = ρ₀ * l Φ) →
    ∀ Φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), ∀ Φ₁ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v),
    Acts (evFin F v) (omd p) Φ Φ₁ → ∀ z : Matrix (Fin n) (Fin m) (AE F E), At (evFin F v) z →
      diagW (psiAt ψ v) μ Φ₁ (locCo M.co v (z * Cᵀ)) = ρ₀ * diagW (psiAt ψ v) μ Φ (locCo M.co v
        (((((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).toBlocks₁₁ - ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).toBlocks₂₁) * z) * Cᵀ)) := by
  intro F E _ _ _ _ _ σ n d X W M ψ hψ v m C hL d' hd' dd hdd omd hsp l hlinv r₀ hr₀ c₀ hc₀ μ hlint p ρ₀ hρ Φ hΦ Φ₁ hΦ₁ hacts z hz

  have hstep : ∀ γ, At (evFin F v) γ → ∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v),
      dd.rho ψ γ (tens (evFin F v) φ r₀) = tens (evFin F v) (schr (psiAt ψ v) (locCo dd v γ) φ) r₀ :=
    fun γ hγ φ hφ => GlobalTheory.VacBridge.rho_acts_locCo dd ψ v γ hγ φ r₀ (hr₀ φ hφ)
  have hmem : ∀ γ, At (evFin F v) γ → ∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v),
      dd.rho ψ γ (tens (evFin F v) φ r₀) ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)) := fun γ hγ φ hφ => by
    rw [hstep γ hγ φ hφ]
    exact (hr₀ _ (GlobalTheory.SchrSB.schr_mem_SB ψ hψ v _ φ hφ)).2
  have hW : ∀ u : Matrix (Fin n) (Fin d) (AE F E), locCo dd v (Matrix.fromCols uᵀ 0) =
      (Sum.elim (locCo M.co v u).1 0, Sum.elim (locCo M.co v u).2 0) := fun u => by
    ext k <;> rcases k with k | k <;> simp [locCo, hdd uᵀ 0, hd' u]
  have hkey : ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) u →
      ∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v),
      c₀ * diagW (psiAt ψ v) μ φ (locCo M.co v u) = l (dd.rho ψ (Matrix.fromCols uᵀ 0) (tens (evFin F v) φ r₀)) :=
    fun u hu φ hφ => by
      rw [hstep _ (at_fromCols_zero hu) φ hφ, hlint _ (GlobalTheory.SchrSB.schr_mem_SB ψ hψ v _ φ hφ), hW, diagW]

  set P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) := ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) with hP
  set u : Matrix (Fin n) (Fin d) (AE F E) := z * Cᵀ with hu
  set u' : Matrix (Fin n) (Fin d) (AE F E) := ((P.toBlocks₁₁ - P.toBlocks₂₁) * z) * Cᵀ with hu'
  have hzat : At (evFin F v) u := at_mul_right' hz _
  have hu'at : At (evFin F v) u' := at_mul_right' (at_mul_left' _ hz) _
  set xm : Matrix (Fin d) (Fin n) (AE F E) := (P.toBlocks₂₁ * u)ᵀ with hxm
  set δ : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) :=
    xm * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ with hδ
  have hδc : δ = Matrix.fromCols xm xm := by
    rw [hδ, diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]
  set Ψ := tens (evFin F v) Φ r₀ with hΨ
  have hΨm : Ψ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)) := (hr₀ Φ hΦ).2
  have h1 : tens (evFin F v) Φ₁ r₀ = omd p Ψ := (hacts r₀ (hr₀ Φ hΦ)).symm
  set γ := actB (cA σ) p⁻¹ (Matrix.fromCols uᵀ (0 : Matrix (Fin d) (Fin n) (AE F E))) with hγ
  have hγat : At (evFin F v) γ := at_mul_right' (at_fromCols_zero hzat) _
  have hinv : dd.rho ψ (Matrix.fromCols uᵀ 0) (omd p Ψ) = omd p (dd.rho ψ γ Ψ) := by
    have h := hsp.impl p⁻¹ (Matrix.fromCols uᵀ 0) (omd p Ψ) (hsp.pres p Ψ hΨm)
    have e1 : ∀ Y, omd p⁻¹ (omd p Y) = Y := fun Y => by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have e2 : ∀ Y, omd p (omd p⁻¹ Y) = Y := fun Y => by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [e1] at h
    rw [← h, e2]
  have hdec : γ = δ + Matrix.fromCols u'ᵀ 0 := by
    have e : u' = (P.toBlocks₁₁ - P.toBlocks₂₁) * u := by rw [hu', hu, Matrix.mul_assoc]
    rw [e, hδc, hxm]
    exact fromCols_mul_transpose_split u P
  have hsum : ∀ Y, dd.rho ψ γ Y = dd.rho ψ δ (dd.rho ψ (Matrix.fromCols u'ᵀ 0) Y) := fun Y => by
    rw [hdec]
    unfold Darboux.rho
    rw [map_add]
    apply GlobalTheory.MixXEvUniq.schr_add
    rw [hδc, hdd xm xm, hdd u'ᵀ 0, hd' u', map_zero, hxm, hd' (P.toBlocks₂₁ * u)]
    simp only [Prod.fst_zero, Prod.snd_zero, neg_zero, sumElim_dotProduct_sumElim, dotProduct_zero,
      zero_dotProduct, add_zero]
    have hform := M.co.form (P.toBlocks₂₁ * u) u'
    have h0 := GlobalTheory.InertVacIso.symp_eq_zero_of_lagAt σ X.J W v C hL (-1) (P.toBlocks₂₁ * u) u'
      ⟨at_mul_left' _ hzat, P.toBlocks₂₁ * z, by rw [hu, Matrix.mul_assoc]⟩ ⟨hu'at, (P.toBlocks₁₁ - P.toBlocks₂₁) * z, rfl⟩
    rw [h0] at hform
    exact (sub_eq_zero.mp hform.symm)
  have hW'm : dd.rho ψ (Matrix.fromCols u'ᵀ 0) Ψ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)) :=
    hmem _ (at_fromCols_zero hu'at) Φ hΦ
  have hγm : dd.rho ψ γ Ψ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)) := hmem γ hγat Φ hΦ
  apply mul_left_cancel₀ hc₀
  rw [hkey u hzat Φ₁ hΦ₁, h1, hinv, hρ _ hγm, hsum, hδ, hlinv xm _ hW'm, ← hkey u' hu'at Φ hΦ]
  ring

end GlobalTheory.InertLagChar
end
