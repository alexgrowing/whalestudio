import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SqrtInUnramifiedCompletion
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimeOfLiesOver
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HostFieldPadicEmbeddingMemMaxUnramified

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

open GlobalTheory.InertCompare GlobalTheory.Proof.IdempotentLatticeSequence

theorem exists_aut_of_algHoms {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [CharZero K]
    (f g : E →ₐ[ℚ] K) : ∃ u : E ≃ₐ[ℚ] E, ∀ x, g x = f (u x) := by
  have hmem : ∀ x, ∃ y, f y = g x := fun x => by
    have hs := Normal.splits (inferInstance : Normal ℚ E) x
    have hi : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    have hr : (((minpoly ℚ x).map (algebraMap ℚ E)).map (f : E →+* K)).IsRoot (g x) := by
      rw [Polynomial.map_map, AlgHom.comp_algebraMap_of_tower, Polynomial.IsRoot, Polynomial.eval_map_algebraMap,
        Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    exact hs.mem_range_of_isRoot (Polynomial.map_ne_zero (minpoly.ne_zero hi)) hr
  choose v hv using hmem
  have hf : Function.Injective f := f.toRingHom.injective
  let w : E →ₐ[ℚ] E :=
    { toFun := v
      map_one' := hf (by rw [hv, map_one, map_one])
      map_mul' := fun a b => hf (by rw [hv, map_mul, map_mul, hv, hv])
      map_zero' := hf (by rw [hv, map_zero, map_zero])
      map_add' := fun a b => hf (by rw [hv, map_add, map_add, hv, hv])
      commutes' := fun r => hf (by
        rw [hv, AlgHom.commutes, AlgHom.commutes]) }
  exact ⟨AlgEquiv.ofBijective w (AlgHom.normal_bijective ℚ E E w), fun x => (hv x).symm⟩

theorem exists_aut_of_embeddings {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [CharZero K]
    (f g : E →+* K) : ∃ u : E ≃ₐ[ℚ] E, ∀ x, g x = f (u x) :=
  exists_aut_of_algHoms f.toRatAlgHom g.toRatAlgHom

theorem padic_mem_Kur (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) : algebraMap ℚ_[p] ℂ_[p] x ∈ MaximalUnramifiedExtension p := by
  have hc : Continuous (algebraMap ℚ_[p] ℂ_[p]) := (algebraMap_isometry ℚ_[p] ℂ_[p]).continuous
  refine (Padic.denseRange_ratCast p).induction_on (p := fun x => algebraMap ℚ_[p] ℂ_[p] x ∈ MaximalUnramifiedExtension p) x ?_ ?_
  · exact Formalism.L2.Th1.D.GaussNormEstimates.isClosed_Kur.preimage hc
  · intro q
    simp

theorem coe_mem_Kur (p : ℕ) [Fact p.Prime] {x : PadicAlgCl p} (hx : x ∈ Formalism.BasicNotions.Loc.MaximalUnramifiedExtension p) :
    algebraMap (PadicAlgCl p) ℂ_[p] x ∈ MaximalUnramifiedExtension p := by
  unfold Formalism.BasicNotions.Loc.MaximalUnramifiedExtension at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, hm, hpm, h1⟩ := hx
    exact Formalism.L2.Th1.D.GaussNormEstimates.mu_mem_Kur hm hpm (by rw [← map_pow, h1, map_one])
  | algebraMap x =>
    rw [← IsScalarTower.algebraMap_apply]
    exact padic_mem_Kur p x
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem host_image_mem_Kur_complex {R : Ranks} (H : Host R) (p : ℕ) [Fact p.Prime] (h2 : p ∉ H.small) (hq : p ≠ H.q)
    (hd : p ≠ H.d) (ρ : H.E →+* ℂ_[p]) (x : H.E) : ρ x ∈ MaximalUnramifiedExtension p := by
  have : IsGalois ℚ H.E := H.hostE_isGalois
  let c : H.E →+* PadicAlgCl p := (IsAlgClosed.lift : H.E →ₐ[ℚ] PadicAlgCl p)
  obtain ⟨u, hu⟩ := exists_aut_of_embeddings ((algebraMap (PadicAlgCl p) ℂ_[p]).comp c) ρ
  rw [hu, RingHom.comp_apply]
  exact coe_mem_Kur p (GlobalTheory.HostKur.host_image_mem_Kur H p h2 hq hd c _)

theorem exists_kur_frob_tauEmb_posPl : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (z : Bool × HH D) (y : D.host.E), ∃ a : MaximalUnramifiedExtension p, (a : ℂ_[p]) = tauEmb D lam (tauPl D z) y ∧ ((σ a : MaximalUnramifiedExtension p) : ℂ_[p]) = tauEmb D lam (tauPl D (posPl D p z 1)) (D.host.conj y) := by
  intro D p _ lam σ hσ h z y
  obtain ⟨h2, hq, hd⟩ := ne_of_inert D p h
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = rhoH D lam (tauPl D z) := ⟨_, rfl⟩
  have hK : ∀ x, ρ x ∈ MaximalUnramifiedExtension p := host_image_mem_Kur_complex D.host p h2 hq hd ρ
  let ρ' : D.host.E →+* MaximalUnramifiedExtension p := ρ.codRestrict (MaximalUnramifiedExtension p) hK
  have hρ' : ∀ x, ((ρ' x : MaximalUnramifiedExtension p) : ℂ_[p]) = ρ x := fun _ => rfl
  let ρ2 : D.host.E →+* ℂ_[p] := (MaximalUnramifiedExtension p).subtype.comp (σ.comp ρ')
  obtain ⟨g, hg⟩ := exists_aut_of_embeddings ρ ρ2
  have := primeOf_isPrime ρ
  have hL := primeOf_liesOver ρ
  have hc : Nat.card (ℤ ⧸ Ideal.under ℤ (primeOf ρ)) = p := by
    rw [← hL.over, Int.card_ideal_quot]
  have hgF : IsArithFrobAt ℤ g (primeOf ρ) := by
    intro x
    rw [hc, mem_primeOf]
    have hx : ‖ρ' (x : D.host.E)‖ ≤ 1 := norm_int_le ρ x
    have h3 := hσ.2.2.2.2 _ hx
    have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    refine lt_of_le_of_lt ?_ hp1
    refine le_of_eq_of_le ?_ h3
    have e1 : ρ (algebraMap (𝓞 D.host.E) D.host.E ((MulSemiringAction.toAlgHom ℤ (𝓞 D.host.E) g) x - x ^ p)) =
        ((σ (ρ' (x : D.host.E)) - ρ' (x : D.host.E) ^ p : MaximalUnramifiedExtension p) : ℂ_[p]) := by
      have e0 : algebraMap (𝓞 D.host.E) D.host.E ((MulSemiringAction.toAlgHom ℤ (𝓞 D.host.E) g) x) = g (x : D.host.E) := rfl
      rw [map_sub, map_sub, e0, ← hg, map_pow, map_pow]
      rfl
    rw [e1]
    rfl
  obtain ⟨φ, hφ, -⟩ := exists_frob_step D p h (primeOf ρ)
  have hgφ : g = φ := by
    have hI := hgF.mul_inv_mem_inertia hφ
    have h1 := ((D.host.der.frob p (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd) (primeOf ρ)).2.2.2 (g * φ⁻¹)).1 (fun x => hI x)
    exact mul_inv_eq_one.1 h1
  have hcc : D.host.conj (D.host.conj y) = y := D.host.φ₀.injective (by
    rw [D.host.conjE_apply, D.host.conjE_apply, Complex.conj_conj])
  refine ⟨ρ' y, ?_, ?_⟩
  · rw [hρ', hρ, ← coe_rhoH]
  · have h4 := rhoH_posPl_one D p lam h (primeOf ρ) φ hφ z (D.host.conj y)
    rw [hcc] at h4
    rw [← coe_rhoH, h4, ← hρ, ← hgφ, ← hg]
    rfl

end GlobalTheory.KerStd
