import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinResidueLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsModerateFormAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchGlue

noncomputable section

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.EisResLineModel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem exists_reps (x : Matrix (Fin n) (Fin 1) E) : ∃ T : Set (ratPts σ J), ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧
    ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J (γ * t⁻¹ : ratPts σ J).1).1 * adMat F x = l.1 • adMat F x := by
  let P : Subgroup (ratPts σ J) :=
    { carrier := {p | ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p.1).1 * adMat F x = l.1 • adMat F x}
      one_mem' := ⟨1, by simp⟩
      mul_mem' := by
        rintro p q ⟨l, hp⟩ ⟨m, hq⟩
        refine ⟨l * m, ?_⟩
        rw [Subgroup.coe_mul, map_mul, Units.val_mul, Matrix.mul_assoc, hq, Matrix.mul_smul, hp, smul_smul,
          Units.val_mul, mul_comm]
      inv_mem' := by
        rintro p ⟨l, hp⟩
        refine ⟨l⁻¹, ?_⟩
        have := congrArg (fun z => l⁻¹.1 • ((matHom _ σ J p.1⁻¹).1 * z)) hp
        simp only [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
          Matrix.one_mul, Matrix.mul_smul, smul_smul] at this
        simpa using this.symm }
  refine ⟨Set.range (fun q : Quotient (QuotientGroup.rightRel P) => q.out), fun γ => ?_⟩
  refine ⟨(Quotient.mk (QuotientGroup.rightRel P) γ).out, ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
  · exact QuotientGroup.rightRel_apply.1 (Quotient.mk_out (s := QuotientGroup.rightRel P) γ)
  · rintro _ ⟨⟨q, rfl⟩, hq⟩
    have : Quotient.mk (QuotientGroup.rightRel P) q.out = Quotient.mk _ γ :=
      Quotient.sound (QuotientGroup.rightRel_apply.2 hq)
    rw [← this, Quotient.out_eq]

theorem hyps_inhabited : ∃ (F E : Type) (_ : Field F) (_ : NumberField F) (_ : Field E) (_ : NumberField E) (_ : Algebra F E)
    (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (X Y : Matrix (Fin 2) (Fin (0 + 1)) E) (x : Matrix (Fin 2) (Fin 1) E)
    (L : Submodule (𝓞 E) (Fin 2 → E)) (a : GL (Fin 2) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) (T : Set (ratPts σ J)),
    IsCMExt F E σ ∧ Algebra.Unramified (𝓞 F) (𝓞 E) ∧ IsHermND σ J ∧ IsWittFrame σ J X Y ∧
      x = X.submatrix id (fun _ => 0) ∧ IsAdapted σ J X Y L a ∧
      (∀ g, ∃ p, ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x ∧
          ∃ k ∈ levelAll σ J L a, g = p * k) ∧
      (∀ p, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x →
          ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l) ∧
      ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ l : (AF F ⊗[F] E)ˣ,
            (matHom _ σ J (γ * t⁻¹ : ratPts σ J).1).1 * adMat F x = l.1 • adMat F x := by
  obtain ⟨F, E, _, _, _, _, _, σ, J, X, Y, L, a, hc, hu, hJ, hW, hA⟩ := GlobalTheory.EisLineModel.data_inhabited
  obtain ⟨h1, h, h2⟩ := GlobalTheory.IwLine.iwasawa_line F E σ hc hu 2 J hJ 0 X Y hW _ rfl L a hA
  obtain ⟨T, hT⟩ := exists_reps (σ := σ) (J := J) (X.submatrix id (fun _ : Fin 1 => 0))
  exact ⟨F, E, _, _, _, _, _, σ, J, X, Y, _, L, a, h, T, hc, hu, hJ, hW, rfl, hA, h1, h2, hT⟩

theorem neBot (n : ℕ) : (𝓝[{s : ℂ | ((n : ℝ) - 1) / 2 < s.re}] (((n : ℂ) - 1) / 2)).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Complex.closure_setOf_lt_re]
  have : ((n : ℂ) - 1) / 2 = ((((n : ℝ) - 1) / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [this]; simp only [Set.mem_setOf_eq, Complex.ofReal_re, le_refl]

theorem infinite_of_concl {ι : Type} (n : ℕ) (c : ι → ℝ) (hc : ∀ i, 0 < c i) {R : ℂ} (hR : R ≠ 0)
    (h : Tendsto (fun s : ℂ => (s - ((n : ℂ) - 1) / 2) * ∑' t : ι, (c t : ℂ) ^ (s + ((n : ℂ) - 1) / 2))
      (𝓝[{s : ℂ | ((n : ℝ) - 1) / 2 < s.re}] (((n : ℂ) - 1) / 2)) (𝓝 R)) : Infinite ι := by
  by_contra hi
  haveI : Finite ι := not_infinite_iff_finite.1 hi
  haveI := Fintype.ofFinite ι
  haveI := neBot n
  have hcont : Continuous fun s : ℂ => (s - ((n : ℂ) - 1) / 2) * ∑' t : ι, (c t : ℂ) ^ (s + ((n : ℂ) - 1) / 2) := by
    simp only [tsum_fintype]
    refine (continuous_id.sub continuous_const).mul (continuous_finset_sum _ fun t _ => ?_)
    exact (continuous_id.add continuous_const).const_cpow (Or.inl (by exact_mod_cast (hc t).ne'))
  have h2 := (hcont.tendsto (((n : ℂ) - 1) / 2)).mono_left
    (nhdsWithin_le_nhds (s := {s : ℂ | ((n : ℝ) - 1) / 2 < s.re}))
  have := tendsto_nhds_unique h h2
  simp at this
  exact hR this

theorem eisensteinIsotropicLine_of_isWittFrame (hP : GlobalTheory.Published.EisensteinResidueLine) : ∃ (F E : Type) (_ : Field F) (_ : NumberField F) (_ : Field E)
    (_ : NumberField E) (_ : Algebra F E) (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (x : Matrix (Fin 2) (Fin 1) E)
    (T : Set (ratPts σ J)), (∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ l : (AF F ⊗[F] E)ˣ,
      (matHom _ σ J (γ * t⁻¹ : ratPts σ J).1).1 * adMat F x = l.1 • adMat F x) ∧ Infinite T := by
  obtain ⟨F, E, _, _, _, _, _, σ, J, X, Y, x, L, a, h, T, hc, hu, hJ, hW, hx, hA, h1, h2, hT⟩ := hyps_inhabited
  obtain ⟨R, hR, hl⟩ := hP F E σ hc hu 2 J hJ 0 X Y hW x hx L a hA h h1 h2 T hT
  exact ⟨F, E, _, _, _, inferInstance, _, σ, J, x, T, hT,
    infinite_of_concl 2 (fun t : T => h (t.1.1 * 1)) (fun _ => (GlobalTheory.EisLineModel.pos h1 h2).1 _) hR (hl 1)⟩

end GlobalTheory.EisResLineModel

end
