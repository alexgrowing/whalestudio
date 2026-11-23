import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAddCharPlaceIdempotentDivPrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticValTauCompat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SplitDegOneChar

theorem absNorm_under {E F : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Algebra (𝓞 F) (𝓞 E)] [Algebra.IsIntegral (𝓞 F) (𝓞 E)]
    (PP : HeightOneSpectrum (𝓞 E)) (p : ℕ) (hp : p.Prime) (hPP : Ideal.absNorm PP.asIdeal = p) :
    Ideal.absNorm (PP.under (𝓞 F)).asIdeal = p := by
  set v := PP.under (𝓞 F) with hvdef
  have hle : v.asIdeal ≤ PP.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) := le_rfl
  haveI := v.isMaximal
  haveI := PP.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  letI : Algebra (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ PP.asIdeal) := Ideal.Quotient.algebraQuotientOfLEComap hle
  have hE : Nat.card (𝓞 E ⧸ PP.asIdeal) = p := by rw [← hPP, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ PP.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hE]; exact hp.ne_zero)
  haveI : Module.Finite (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ PP.asIdeal) := Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := 𝓞 F ⧸ v.asIdeal) (V := 𝓞 E ⧸ PP.asIdeal)
  rw [hE] at h
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact ((hp.pow_eq_iff).1 h.symm).1

theorem natCast_not_mem_under_sq {E F : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra (𝓞 F) (𝓞 E)] [Algebra.IsIntegral (𝓞 F) (𝓞 E)]
    (PP : HeightOneSpectrum (𝓞 E)) (p : ℕ) (hsq : (p : 𝓞 E) ∉ PP.asIdeal ^ 2) :
    (p : 𝓞 F) ∉ (PP.under (𝓞 F)).asIdeal ^ 2 := by
  intro h
  apply hsq
  have h1 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) h
  rw [Ideal.map_pow, map_natCast] at h1
  exact Ideal.pow_right_mono (Ideal.map_comap_le) 2 h1

end GlobalTheory.SplitDegOneChar

namespace GlobalTheory.SplitDegOneChar

theorem psiE_sec_pr_eq_exp : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E) (p : ℕ), p.Prime → Ideal.absNorm PP.asIdeal = p → ((p : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2 → q.v = PP.under (𝓞 D.host.F) → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt PP x) → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (x : D.host.E) (b : ℤ), Formalism.L2.Col.IntAt PP (x - (b : D.host.E) / (p : D.host.E)) → psiE ψ (q.sec ((ofSplit q).pr x)) = Complex.exp (2 * Real.pi * Complex.I * b / (p : ℂ)) := by
  intro D k _ _ _ _ q PP p hp hPP hsq hv hint ψ hψ x b hx
  have hpr : ∀ y : D.host.E, (ofSplit q).pr y = q.pr (incA D y) := fun _ => rfl
  set c : D.host.F := (b : D.host.F) / (p : D.host.F) with hcdef
  have hc : algebraMap D.host.F D.host.E c = (b : D.host.E) / (p : D.host.E) := by
    rw [hcdef, map_div₀, map_intCast, map_natCast]
  have hxs : x = (x - (b : D.host.E) / (p : D.host.E)) + algebraMap D.host.F D.host.E c := by
    rw [hc]; ring
  have hadd : ∀ u w : AE D, psiE ψ (u + w) = psiE ψ u * psiE ψ w := by
    intro u w; simp only [GlobalTheory.MixPer.psiE, map_add, AddChar.map_add_eq_mul]
  rw [hxs, hpr, map_add, map_add, map_add, hadd]

  have hy : q.pr (incA D (x - (b : D.host.E) / (p : D.host.E))) ∈ 𝒪[k] := by
    rw [← hpr]; exact (hint _).2 hx
  have h1 : psiE ψ (q.sec (q.pr (incA D (x - (b : D.host.E) / (p : D.host.E))))) = 1 := by
    rw [GlobalTheory.MixPer.psiE, GlobalTheory.SplitCharCond.trace_sec q, GlobalTheory.SplitCharCond.snd_trace,
      GlobalTheory.SplitCharCond.char_int hψ (GlobalTheory.SplitCharCond.trace_int ((q.int_iff _).1 hy))]
  rw [h1, one_mul]

  obtain ⟨ε, hε, he⟩ := q.above
  have htr : Algebra.trace (AF D.host.F) (AE D) q.e = ε := by
    refine Algebra.TensorProduct.includeLeft_injective (S := AF D.host.F) (algebraMap D.host.F D.host.E).injective ?_
    change algebraMap (AF D.host.F) (AE D) _ = algebraMap (AF D.host.F) (AE D) _
    rw [GlobalTheory.FockCompare.SymplVal.trace_AE, he]
  have hinc : incA D (algebraMap D.host.F D.host.E c) =
      algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) c) := GlobalTheory.SplitCharCond.one_tmul_eq c
  rw [q.sec_pr, hinc, mul_comm, ← Algebra.smul_def, GlobalTheory.MixPer.psiE, map_smul, smul_eq_mul, htr, mul_comm]
  have hnorm : Ideal.absNorm q.v.asIdeal = p := by rw [hv]; exact absNorm_under PP p hp hPP
  have hsqv : (p : 𝓞 D.host.F) ∉ q.v.asIdeal ^ 2 := by rw [hv]; exact natCast_not_mem_under_sq PP p hsq
  have key := GlobalTheory.StdCharDegOne.stdChar_placeIdem_div D ψ hψ p hp q.v hnorm hsqv ε hε (b : 𝓞 D.host.F) b
    (by rw [sub_self]; exact zero_mem _)
  rw [← key, hcdef]
  push_cast
  rfl

end GlobalTheory.SplitDegOneChar
