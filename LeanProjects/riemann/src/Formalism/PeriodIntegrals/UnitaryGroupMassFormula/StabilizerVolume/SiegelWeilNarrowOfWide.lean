import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcWeil

noncomputable section

namespace Formalism.L2.SG.Pf.NcWeil

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.UnusedSlot34 Formalism.L2.SG.Volumes NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

def IsSmoothCc (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] {n M : ℕ}
    (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) : Prop :=
  HasCompactSupport Φinf ∧
    ∀ (N : ℕ) (e : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φinf ∘ e.symm)

section Ext

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def StabilizerFirstChernCompatibility : Prop :=
  ∀ (n : ℕ), 2 * n < M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b),
    T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ),
    Continuous Φinf → RapidDecay b Φinf → IsSmoothCc F E Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
    AllSome (IsHaarH F E σ M J) fun μ => AllSome (IsFDH F E σ M J μ) fun 𝓕 =>
    AllSome (IsCharAF F) fun ψ =>
    AllSome (SdW F E σ M J (Ainf F) (psiInf F ψ) n) fun μinf =>
    AllSome (SdHerm F E σ (Ainf F) (psiInf F ψ) n) fun νinf =>
    AllSome (fun μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E) =>
      ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (μv v)) fun μv =>
    AllSome (fun νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ n) =>
      ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) n (νv v)) fun νv =>
    ∃ (ginf : HermR (Ainf F) σ n → ℂ) (gv : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → ℂ),
      IsContDensityOn μinf (gramR (Ainf F) σ J) Subtype.val νinf
        {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} Φinf ginf ∧
      (∀ v, IsContDensityOn (μv v) (gramR (Fv F v) σ J) Subtype.val (νv v)
        {S | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} (Φv v) (gv v)) ∧
      Multipliable (fun v => gv v (hermOf (Fv F v) σ T hT)) ∧
      meanC μ 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = T}) =
        ginf (hermOf (Ainf F) σ T hT) * ∏' v, gv v (hermOf (Fv F v) σ T hT)

end Ext

section Class

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n M : ℕ}

theorem isSmoothCc_const (c : ℂ)
    (hc : HasCompactSupport (fun _ : Fin n → Fin M → Ainf F ⊗[F] E => c)) :
    IsSmoothCc F E (fun _ : Fin n → Fin M → Ainf F ⊗[F] E => c) :=
  ⟨hc, fun _ _ _ _ => contDiff_const⟩

theorem isSmoothCc_zero : IsSmoothCc F E (fun _ : Fin n → Fin M → Ainf F ⊗[F] E => (0 : ℂ)) :=
  isSmoothCc_const 0 HasCompactSupport.zero

theorem isSmoothCc_empty (Φinf : (Fin 0 → Fin M → Ainf F ⊗[F] E) → ℂ) : IsSmoothCc F E Φinf := by
  have e : Φinf = fun _ => Φinf default := funext fun X => congrArg Φinf (Subsingleton.elim X default)
  rw [e]
  exact isSmoothCc_const _ (HasCompactSupport.intro' isCompact_univ isClosed_univ fun x hx => absurd (Set.mem_univ x) hx)

theorem isSmoothCc_of_coord (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (hs : HasCompactSupport Φinf)
    {N : ℕ} (e0 : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ)) (he0 : Continuous e0)
    (h0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φinf ∘ e0.symm)) : IsSmoothCc F E Φinf := by
  refine ⟨hs, fun N' e _ he' => ?_⟩
  let L : (Fin N' → ℝ) →+ (Fin N → ℝ) := (e.symm.trans e0).toAddMonoidHom
  have hL : Continuous L := he0.comp he'
  have key : Φinf ∘ e.symm = (Φinf ∘ e0.symm) ∘ (L.toRealLinearMap hL) := by
    funext x
    simp [L]
  rw [key]
  exact h0.comp (L.toRealLinearMap hL).contDiff

end Class

end Formalism.L2.SG.Pf.NcWeil
