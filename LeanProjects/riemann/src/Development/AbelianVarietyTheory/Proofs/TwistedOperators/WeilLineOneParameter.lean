import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionUnitaryCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleFiniteFactorArchimedeanSchwartzStatement

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical

namespace GlobalTheory.ArchFamily

theorem exists_family : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om → ∀ γ ∈ Lines σ W,
    ∃ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
      (∀ t (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) ∧
      (∀ s t (f : SInf F (Fin n × Fin d)), T (s + t) f = T s (T t f)) ∧ ∀ f : SInf F (Fin n × Fin d), T 0 f = f := by
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hcm hstd hW γ hγ
  obtain ⟨r₀, hR, hinj⟩ := GlobalTheory.T.exists_admissible_finiteFactor_archimedeanSchwartz (F := F) (Fin n × Fin d)
  have hex : ∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑f₁ :=
    fun t f => GlobalTheory.T.weil_action_unitary_compact hP M ψ χX χW om hcm hstd hW _ (hγ.2 _) f
  choose S hS using hex
  have key : ∀ t (f : SInf F (Fin n × Fin d)),
      om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f r₀) = tens (evI F) ⇑(S t f) r₀ :=
    fun t f => hS t f r₀ (hR f)
  have tadd : ∀ f g : SInf F (Fin n × Fin d),
      tens (evI F) ⇑(f + g) r₀ = tens (evI F) ⇑f r₀ + tens (evI F) ⇑g r₀ := by
    intro f g; funext x; simp [tens, add_mul]
  have tsmul : ∀ (c : ℂ) (f : SInf F (Fin n × Fin d)),
      tens (evI F) ⇑(c • f) r₀ = c • tens (evI F) ⇑f r₀ := by
    intro c f; funext x; simp [tens, mul_assoc]
  let T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) := fun t =>
    { toFun := S t
      map_add' := fun f g => hinj _ _ (by rw [← key, tadd, map_add, key, key, tadd])
      map_smul' := fun c f => hinj _ _ (by rw [← key, tsmul, map_smul, key, RingHom.id_apply, tsmul]) }
  refine ⟨T, fun t f => hS t f, fun s t f => hinj _ _ ?_, fun f => hinj _ _ ?_⟩
  · show tens (evI F) ⇑(S (s + t) f) r₀ = tens (evI F) ⇑(S s (S t f)) r₀
    have hmul : ((1 : UA σ X.J), γ (Multiplicative.ofAdd (s + t))) =
        ((1 : UA σ X.J), γ (Multiplicative.ofAdd s)) * ((1 : UA σ X.J), γ (Multiplicative.ofAdd t)) := by
      rw [ofAdd_add, map_mul, Prod.mk_mul_mk, one_mul]
    rw [← key, hmul, map_mul, Module.End.mul_apply, key, key]
  · show tens (evI F) ⇑(S 0 f) r₀ = tens (evI F) ⇑f r₀
    have h1 : ((1 : UA σ X.J), γ (Multiplicative.ofAdd (0 : ℝ))) = 1 := by
      rw [ofAdd_zero, map_one]; rfl
    rw [← key, h1, map_one, Module.End.one_apply]

end GlobalTheory.ArchFamily
