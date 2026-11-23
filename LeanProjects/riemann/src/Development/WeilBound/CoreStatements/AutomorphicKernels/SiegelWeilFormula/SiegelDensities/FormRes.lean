import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.MassOneCounts.ZOfSurj
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.SiegelWeilFormula.Gunr PositivityTheory.SiegelWeilFormula.MOne
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem zOf_repr {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (w : Fin 1 × Fin d → v.adicCompletionIntegers F) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (zOf b v w) k = (w (0, k) : Fv F v) := by
  simp [zOf, map_sum, Finsupp.single_apply]

theorem zOf_mem' {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (w : Fin 1 × Fin d → v.adicCompletionIntegers F) : zOf b v w ∈ Rv b v := by
  intro k
  rw [zOf_repr]
  exact (w (0, k)).2

theorem form_res (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (J : Matrix (Fin 1) (Fin 1) E) (hJ : IsHermND σ J) (d : ℕ)
    (b : Module.Basis (Fin d) F E) (B : Matrix (Fin 1 × Fin d) (Fin 1 × Fin d) F)
    (hBt : ∀ (R : Type) [CommRing R] [Algebra F R] (x y : Fin 1 → R ⊗[F] E),
      Algebra.trace R (R ⊗[F] E) (hR R σ J x y) =
        (fun p : Fin 1 × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ
          (B.map (algebraMap F R) *ᵥ fun p : Fin 1 × Fin d => (Algebra.TensorProduct.basis R b).repr (y p.1) p.2))
    (v : HeightOneSpectrum (𝓞 F))
    (hfix : ∀ x : Fv F v ⊗[F] E, sigR (Fv F v) σ x = x → ∃ c : Fv F v, x = algebraMap (Fv F v) (Fv F v ⊗[F] E) c)
    (htr : ∀ a : Fv F v ⊗[F] E,
      (∀ y ∈ Rv b v, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a * y) ∈ v.adicCompletionIntegers F) ↔ a ∈ Rv b v)
    (hR1 : (1 : Fv F v ⊗[F] E) ∈ Rv b v)
    (hRmul : ∀ x ∈ Rv b v, ∀ y ∈ Rv b v, x * y ∈ Rv b v)
    (hRsig : ∀ x ∈ Rv b v, sigR (Fv F v) σ x ∈ Rv b v)
    (h2 : Valued.v (2 : Fv F v) = 1) (hj : inclR (Fv F v) (J 0 0) ∈ Rv b v)
    (ϖ : v.adicCompletionIntegers F) (hϖ0 : (ϖ : Fv F v) ≠ 0) (hϖ1 : ‖(ϖ : Fv F v)‖ < 1)
    (hϖd : ∀ x : v.adicCompletionIntegers F, ‖(x : Fv F v)‖ < 1 → ϖ ∣ x)
    (w : Fin 1 × Fin d → v.adicCompletionIntegers F) (s : v.adicCompletionIntegers F) :
    Valued.v ((2 : Fv F v)⁻¹ * ((fun p => (w p : Fv F v)) ⬝ᵥ
        (B.map (algebraMap F (Fv F v)) *ᵥ fun p => (w p : Fv F v))) - s) < 1 ↔
      ∃ y ∈ Rv b v, sigR (Fv F v) σ (zOf b v w) * inclR (Fv F v) (J 0 0) * zOf b v w -
        algebraMap (Fv F v) (Fv F v ⊗[F] E) s = algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ * y := by
  classical
  have hσσ : ∀ x, σ (σ x) = x := GlobalTheory.CompanionTheory.SW.SWIsom.sigma_sigma σ hCM
  have hj0 : σ (J 0 0) = J 0 0 := hJ.1 0 0
  have h20 : (2 : Fv F v) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h2
    exact zero_ne_one h2
  have hd : d = 2 := by
    rw [← hCM.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]

  have htrc : ∀ c : Fv F v, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (algebraMap (Fv F v) _ c) = 2 * c := by
    intro c
    rw [Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis (Fv F v) b), Fintype.card_fin, hd,
      nsmul_eq_mul]
    norm_num

  have hint : ∀ c : Fv F v, algebraMap (Fv F v) (Fv F v ⊗[F] E) c ∈ Rv b v → c ∈ v.adicCompletionIntegers F := by
    intro c hc
    have h1 := (htr _).2 hc 1 hR1
    rw [mul_one, htrc] at h1
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 ⊢
    rwa [map_mul, h2, one_mul] at h1

  have hsc : ∀ u : Fv F v, u ∈ v.adicCompletionIntegers F → algebraMap (Fv F v) (Fv F v ⊗[F] E) u ∈ Rv b v := by
    intro u hu k
    rw [Algebra.algebraMap_eq_smul_one, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact Subring.mul_mem _ hu (hR1 k)
  set z := zOf b v w with hz
  have hzR : z ∈ Rv b v := zOf_mem' b v w
  have hsig2 : ∀ x, sigR (Fv F v) σ (sigR (Fv F v) σ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [sigR, hσσ]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hsj : sigR (Fv F v) σ (inclR (Fv F v) (J 0 0)) = inclR (Fv F v) (J 0 0) := by
    simp [sigR, inclR, hj0]
  set Q := sigR (Fv F v) σ z * inclR (Fv F v) (J 0 0) * z with hQ
  have hQfix : sigR (Fv F v) σ Q = Q := by
    rw [hQ, map_mul, map_mul, hsig2, hsj]
    ring
  obtain ⟨c, hc⟩ := hfix Q hQfix
  have hQR : Q ∈ Rv b v := hRmul _ (hRmul _ (hRsig _ hzR) _ hj) _ hzR
  have hcO : c ∈ v.adicCompletionIntegers F := hint c (hc ▸ hQR)

  have hform : (fun p => (w p : Fv F v)) ⬝ᵥ (B.map (algebraMap F (Fv F v)) *ᵥ fun p => (w p : Fv F v)) = 2 * c := by
    have e1 := hBt (Fv F v) (fun _ => z) (fun _ => z)
    have e2 : hR (Fv F v) σ J (fun _ => z) (fun _ => z) = Q := by
      simp [hR, hform, JR, Matrix.map_apply, hQ]
    have e3 : (fun p : Fin 1 × Fin d => (Algebra.TensorProduct.basis (Fv F v) b).repr ((fun _ => z) p.1) p.2) =
        fun p => (w p : Fv F v) := by
      funext p
      obtain ⟨i, k⟩ := p
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact zOf_repr b v w k
    rw [e2, e3, hc, htrc] at e1
    exact e1.symm
  rw [hform, ← mul_assoc, inv_mul_cancel₀ h20, one_mul, hc]
  constructor
  · intro hlt
    have hcs : c - s ∈ v.adicCompletionIntegers F :=
      Subring.sub_mem _ hcO s.2
    obtain ⟨u, hu⟩ := hϖd ⟨c - s, hcs⟩ (by rwa [Valued.toNormedField.norm_lt_one_iff])
    refine ⟨algebraMap (Fv F v) _ (u : Fv F v), hsc _ u.2, ?_⟩
    have hu' : c - (s : Fv F v) = (ϖ : Fv F v) * u := congrArg Subtype.val hu
    rw [← map_sub, hu', map_mul]
  · rintro ⟨y, hy, he⟩
    set u := (ϖ : Fv F v)⁻¹ * (c - s) with hu
    have hyu : y = algebraMap (Fv F v) _ u := by
      have := congrArg (fun q => algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ : Fv F v)⁻¹ * q) he
      rw [← map_sub, ← map_mul, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hϖ0, map_one, one_mul] at this
      rw [hu, this]
    have huO : u ∈ v.adicCompletionIntegers F := hint u (hyu ▸ hy)
    have hcs : c - (s : Fv F v) = (ϖ : Fv F v) * u := by
      rw [hu, ← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]
    rw [hcs, map_mul]
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at huO
    have hϖv : Valued.v (ϖ : Fv F v) < 1 := by rwa [← Valued.toNormedField.norm_lt_one_iff]
    calc Valued.v (ϖ : Fv F v) * Valued.v u ≤ Valued.v (ϖ : Fv F v) := by
          first
          | exact mul_le_of_le_one_right' huO
          | exact mul_le_of_le_one_right zero_le' huO
      _ < 1 := hϖv

end PositivityTheory.SiegelWeilFormula.Densx

end
