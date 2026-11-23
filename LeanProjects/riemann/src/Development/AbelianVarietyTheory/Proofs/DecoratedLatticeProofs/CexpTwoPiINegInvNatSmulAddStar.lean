import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.I0M
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedFiniteCharacterInverseExpTrace
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Core.TieSign
variable {D : D7}

def hN (n : GA D (D.sp.Y 0)) (p q : Fin (D.sp.Y 0).rank → D.host.E) : AE D :=
  ∑ i, ∑ j, incA D (star (p i) * (D.sp.Y 0).gram i j) * (mt (D.sp.Y 0) n *ᵥ ratV q) j
end GlobalTheory.Core.TieSign
end

noncomputable section
namespace GlobalTheory.Core.TieSign
open Formalism.L2.SG.AdBridge Formalism.L2.SG.InstExistsPf

section Generic

variable (I : Formalism.MainNotions.S.AutInst)

theorem phi_star (v : InfinitePlace I.F) (x : I.E) : I.φ v (star x) = star (I.φ v x) :=
  I.cm.cmUnram.2.1 (I.φ v) x

theorem hJ_frame (v : InfinitePlace I.F) (x y : Fin I.n → ℂ) (N : Matrix (Fin I.n) (Fin I.n) ℂ) :
    hJ (I.ε v) ((I.P v)⁻¹ *ᵥ x) (((I.P v)⁻¹ * N * I.P v) *ᵥ ((I.P v)⁻¹ *ᵥ y)) =
      star x ⬝ᵥ (I.J.map (I.φ v) *ᵥ (N *ᵥ y)) := by
  have hd : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have h1 : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h2 : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have h3 : ((I.P v)⁻¹)ᴴ * (Formalism.REAL.Jm (I.ε v) * ((I.P v)⁻¹ * N * I.P v * (I.P v)⁻¹)) = I.J.map (I.φ v) * N := by
    rw [← I.P_spec v, Matrix.mul_assoc _ (I.P v) (I.P v)⁻¹, h1, Matrix.mul_one, Matrix.mul_assoc _ (I.P v),
      ← Matrix.mul_assoc (I.P v), h1, Matrix.one_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [hJ, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← h3]
  simp only [Matrix.mul_assoc]

theorem theta_form (v : InfinitePlace I.F) (M : Matrix (Fin I.n) (Fin I.n) (AF I.F ⊗[I.F] I.E)) (p q : Fin I.n → I.E) :
    thetaV I v (∑ i, ∑ j, inclR (AF I.F) (star (p i) * I.J i j) * (M *ᵥ fun k => inclR (AF I.F) (q k)) j) =
      hJ (I.ε v) (rv I v p) (((I.P v)⁻¹ * M.map (thetaV I v) * I.P v) *ᵥ rv I v q) := by
  rw [rv, rv, hJ_frame]
  simp only [map_sum, map_mul, thetaV_inclR, phi_star, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.star_apply,
    Finset.mul_sum, mul_assoc]

theorem sig_inclE (x : I.E) : Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F) (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) =
    Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (star x) := by
  simp only [Formalism.UG.sigR, Formalism.UG.inclE, Algebra.TensorProduct.includeLeftRingHom_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rfl

theorem tau_form (M : Matrix (Fin I.n) (Fin I.n) (AF I.F ⊗[I.F] I.E)) (p q : Fin I.n → I.E) :
    tauF I (∑ i, ∑ j, inclR (AF I.F) (star (p i) * I.J i j) * (M *ᵥ fun k => inclR (AF I.F) (q k)) j) =
      hA I (incl I p) (M.map (tauF I) *ᵥ incl I q) := by
  simp only [map_sum, map_mul, tauF_inclR, Matrix.mulVec, dotProduct, Matrix.map_apply, hA, Formalism.UG.hform, incl, sig_inclE]

theorem trace_tmul' (a : AF I.F) (x : I.E) :
    Algebra.trace (AF I.F) (AF I.F ⊗[I.F] I.E) (a ⊗ₜ[I.F] x) = a * algebraMap I.F (AF I.F) (Algebra.trace I.F I.E x) := by
  have e : a ⊗ₜ[I.F] x = a • ((1 : AF I.F) ⊗ₜ[I.F] x) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [e, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange,
    smul_eq_mul]

theorem evV_trace (v : InfinitePlace I.F) (y : AF I.F ⊗[I.F] I.E) :
    evV I v (Algebra.trace (AF I.F) (AF I.F ⊗[I.F] I.E) y) = thetaV I v y + star (thetaV I v y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have h1 := thetaV_sigR I v (a ⊗ₜ[I.F] x)
    have hs : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF I.F) I.cm.sig (a ⊗ₜ[I.F] x) = a ⊗ₜ[I.F] (star x) := by
      simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
      rfl
    rw [hs] at h1
    rw [trace_tmul', map_mul, evV_algebraMap, ← I.φ_over, GlobalTheory.St.G.trace_cm_eq_add_star I.cm, map_add, mul_add,
      ← thetaV_tmul, ← thetaV_tmul, h1]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, star_add]; ring

theorem tmul_mem_int {x : I.E} (hx : IsIntegral ℤ x) {b : Formalism.MainNotions.S.Af I.F} (hb : b ∈ Formalism.UG.intAd I.F) :
    x ⊗ₜ[I.F] b ∈ IntAf I.F I.E := by
  have e : x ⊗ₜ[I.F] b = (x ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F)) * ((1 : I.E) ⊗ₜ[I.F] b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [e]
  exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨x, ⟨⟨x, hx⟩, rfl⟩⟩, rfl⟩))
    (Subring.subset_closure (Or.inr ⟨⟨b, hb⟩, rfl⟩))

theorem fin_char (ψ : AddChar (AF I.F) ℂ)
    (hψr : ∀ x : I.F, ψ (pairA I.F 0 (algebraMap I.F (Formalism.MainNotions.S.Af I.F) x)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ I.F x : ℚ) : ℂ)))
    (hψi : ∀ β ∈ Formalism.UG.intAd I.F, ψ (pairA I.F 0 β) = 1)
    (psiEf : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F → ℂ)
    (hadd : ∀ x y, psiEf (x + y) = psiEf x * psiEf y)
    (hint : ∀ x ∈ IntAf I.F I.E, psiEf x = 1)
    (hrat : ∀ x : I.E, psiEf (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) * psiEinf I x = 1)
    (y : AF I.F ⊗[I.F] I.E) :
    ψ (pairA I.F 0 (Algebra.trace (AF I.F) (AF I.F ⊗[I.F] I.E) y).2) = psiEf (tauF I (-y)) := by
  have padd : ∀ α β : Formalism.MainNotions.S.Af I.F, ψ (pairA I.F 0 (α + β)) = ψ (pairA I.F 0 α) * ψ (pairA I.F 0 β) := by
    intro α β
    rw [← AddChar.map_add_eq_mul]
    congr 1
    exact Prod.ext (add_zero _).symm rfl
  induction y using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, neg_zero, map_zero, hint 0 (zero_mem _)]
    exact hψi 0 (zero_mem _)
  | add x y hx hy =>
    rw [map_add, neg_add, map_add, hadd, ← hx, ← hy, ← padd]
    rfl
  | tmul a x =>
    obtain ⟨N, s, hN0, hs⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ I.E).2
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)).exists_nsmul_eq (𝓞 I.E)
    have hN : IsIntegral ℤ (N • x) := by rw [hs]; exact s.2
    obtain ⟨a0, β, hβ, hab⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat I.F N (Nat.pos_of_ne_zero hN0)).1 a.2
    have hβ' : β ∈ Formalism.UG.intAd I.F := hβ
    have e1 : (Algebra.trace (AF I.F) (AF I.F ⊗[I.F] I.E) (a ⊗ₜ[I.F] x)).2 =
        algebraMap I.F (Formalism.MainNotions.S.Af I.F) (Algebra.trace I.F I.E (a0 • x)) +
          β * algebraMap I.F (Formalism.MainNotions.S.Af I.F) (Algebra.trace I.F I.E (N • x)) := by
      rw [trace_tmul']
      show a.2 * algebraMap I.F (Formalism.MainNotions.S.Af I.F) (Algebra.trace I.F I.E x) = _
      rw [hab, map_smul, map_nsmul, map_nsmul, smul_eq_mul, map_mul, add_mul, smul_mul_assoc, mul_smul_comm]
    have e2 : tauF I (-(a ⊗ₜ[I.F] x)) =
        Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (-(a0 • x)) + -((N • x) ⊗ₜ[I.F] β) := by
      rw [map_neg, tauF_tmul, hab, TensorProduct.tmul_add, neg_add, map_neg]
      congr 2
      · rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
        rfl
      · rw [← Nat.cast_smul_eq_nsmul I.F, ← Nat.cast_smul_eq_nsmul I.F, TensorProduct.smul_tmul]
    have hti : algebraMap I.F (Formalism.MainNotions.S.Af I.F) (Algebra.trace I.F I.E (N • x)) ∈ Formalism.UG.intAd I.F := by
      have h := Algebra.isIntegral_trace (L := I.F) hN
      intro v
      exact IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := I.F) v (⟨_, h⟩ : 𝓞 I.F)
    rw [e1, e2, padd, hadd, hψi _ (mul_mem hβ' hti), hint _ (neg_mem (tmul_mem_int I hN hβ')), hψr, Algebra.trace_trace,
      eq_inv_of_mul_eq_one_left (hrat _), GlobalTheory.St.G.psiEinf_eq_exp_trace, ← Complex.exp_neg, map_neg]
    congr 2
    push_cast
    ring

end Generic
end GlobalTheory.Core.TieSign
end

noncomputable section
namespace GlobalTheory.Core.TieSign
open Formalism.L2.SG.AdBridge Formalism.L2.SG.InstExistsPf

theorem hN_smul {D : D7} (n : GA D (D.sp.Y 0)) (a b : D.host.E) (p q : Fin (D.sp.Y 0).rank → D.host.E) :
    hN n (a • p) (b • q) = incA D (star a * b) * hN n p q := by
  simp only [hN, Matrix.mulVec, dotProduct, ratV, Pi.smul_apply, smul_eq_mul, star_mul', map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem pX_mulVec {D : D7} {V₀ : HSp D} {ρ : ℕ} (d : HypDec (D.sp.Y 0) V₀ ρ) (n : GA D (D.sp.Y 0))
    (q : Fin (D.sp.Y 0).rank → D.host.E) (a : Fin ρ) :
    (d.pX *ᵥ (mt (D.sp.Y 0) n *ᵥ ratV q)) a = hN n (fun k => d.e' k a) q := by
  rw [hN, Finset.sum_comm, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul, ← map_sum (incA D)]
  rfl

theorem blockX_eq {D : D7} {V₀ : HSp D} {ρ : ℕ} (d : HypDec (D.sp.Y 0) V₀ ρ) (n : GA D (D.sp.Y 0)) (a b : Fin ρ) :
    blockX d n a b = hN n (fun k => d.e' k a) (fun k => d.e k b) := by
  rw [← pX_mulVec]
  rfl

theorem coefX_eq {D : D7} {V₀ : HSp D} {ρ : ℕ} (d : HypDec (D.sp.Y 0) V₀ ρ) (z : Fin V₀.rank → D.host.E)
    (n : GA D (D.sp.Y 0)) (a : Fin ρ) : coefX d z n a = hN n (fun k => d.e' k a) (d.i₀ *ᵥ z) := by
  rw [← pX_mulVec, ratV_mulVec, coefX, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rfl

theorem bridge_comp (D : D7) (g : GA D (D.sp.Y 0)) :
    (∀ v, uMat ((Formalism.IndefR.RationalEmbedding.iota D g).1 v) = ofHAInf (instOf D) g v) ∧
      (instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 = ofHAFin (instOf D) g := by
  have hb := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D g)
  have key : (Formalism.IndefR.RationalEmbedding.iota D).symm (Formalism.IndefR.RationalEmbedding.iota D g) = g :=
    (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply g
  exact ⟨fun v => (hb.1 v).trans (congrArg (fun q => ofHAInf (instOf D) q v) key),
    hb.2.trans (congrArg (fun q => ofHAFin (instOf D) q) key)⟩

theorem simpleSum_eq (D : D7) {V₀ : HSp D} {ρ : ℕ} (d : HypDec (D.sp.Y 0) V₀ ρ)
    (E F : Fin ρ → Fin (D.sp.Y 0).rank → D.host.E) (Z : Fin (D.sp.Y 0).rank → D.host.E)
    (z : Fin V₀.rank → D.host.E) (t lam : D.host.E) (ht : t ≠ 0) (hl : lam ≠ 0)
    (he : d.e = Matrix.of fun k (a : Fin ρ) => t * lam ^ (ρ - (a : ℕ)) * E a k)
    (he' : d.e' = Matrix.of fun k (a : Fin ρ) => (star (t * lam ^ (ρ - (a : ℕ))))⁻¹ * F a k)
    (hz : d.i₀ *ᵥ z = t • Z) (n : GA D (D.sp.Y 0)) :
    simpleSum d z n = incA D lam⁻¹ * ∑ a, hN n (F a) (nxt E Z a) := by
  have hF : ∀ a : Fin ρ, (fun k => d.e' k a) = (star (t * lam ^ (ρ - (a : ℕ))))⁻¹ • F a := fun a => by rw [he']; rfl
  have hE : ∀ a : Fin ρ, (fun k => d.e k a) = (t * lam ^ (ρ - (a : ℕ))) • E a := fun a => by rw [he]; rfl
  rw [simpleSum, upSum, dotProduct, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have ha := a.2
  by_cases h1 : a.1 + 1 < ρ
  · have h2 : ¬ (a.1 + 1 = ρ) := by omega
    rw [Finset.sum_eq_single (⟨a.1 + 1, h1⟩ : Fin ρ) (fun b _ hb => if_neg fun e => hb (Fin.ext e))
      (fun h => absurd (Finset.mem_univ _) h), if_pos rfl, ell, if_neg h2, zero_mul, add_zero, blockX_eq, hF, hE, hN_smul,
      nxt, dif_pos h1]
    congr 2
    have e : ρ - (a : ℕ) = (ρ - (a.1 + 1)) + 1 := by omega
    rw [star_inv₀, star_star, e, pow_succ]
    field_simp
  · have h2 : a.1 + 1 = ρ := by omega
    rw [Finset.sum_eq_zero (fun b _ => if_neg (by have := b.2; omega)), zero_add, ell, if_pos h2, one_mul, coefX_eq, hF, hz,
      hN_smul, nxt, dif_neg h1]
    congr 2
    have e : ρ - (a : ℕ) = 1 := by omega
    rw [star_inv₀, star_star, e, pow_one]
    field_simp

theorem thetaV_hN (D : D7) (n : GA D (D.sp.Y 0)) (v : InfinitePlace (instOf D).F)
    (p q : Fin (D.sp.Y 0).rank → D.host.E) :
    thetaV (instOf D) v (hN n p q) =
      hJ ((instOf D).ε v) (rv (instOf D) v p) (uMat ((Formalism.IndefR.RationalEmbedding.iota D n).1 v) *ᵥ rv (instOf D) v q) := by
  rw [(bridge_comp D n).1 v]
  exact theta_form (instOf D) v (hmat (instOf D) n) p q

theorem tauF_hN (D : D7) (n : GA D (D.sp.Y 0)) (p q : Fin (D.sp.Y 0).rank → D.host.E) :
    tauF (instOf D) (hN n p q) =
      hA (instOf D) (incl (instOf D) p) ((instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D n).2 *ᵥ incl (instOf D) q) := by
  rw [(bridge_comp D n).2]
  exact tau_form (instOf D) (hmat (instOf D) n) p q

theorem psi_inf_trace (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (y : AE D) :
    ψ (pairA D.host.F (Algebra.trace (AF D.host.F) (AE D) y).1 0) =
      ∏ v, Complex.exp (2 * Real.pi * Complex.I *
        -(thetaV (instOf D) v y + star (thetaV (instOf D) v y))) := by
  have h := hψ.2.2 _ (Formalism.IndefR.Eqv.isInfFam_thetaC D) (Algebra.trace (AF D.host.F) (AE D) y).1
  have hs : ∑ ρ, Formalism.IndefR.Eqv.thetaC D ρ ((Algebra.trace (AF D.host.F) (AE D) y).1 ⊗ₜ[D.host.F] (1 : D.host.E)) =
      ∑ v : InfinitePlace (instOf D).F, (thetaV (instOf D) v y + star (thetaV (instOf D) v y)) := by
    refine Fintype.sum_equiv (Formalism.L2.Host.tauPl D) _ _ fun ρ => ?_
    rw [Formalism.IndefR.Eqv.thetaC_tmul, map_one, mul_one]
    exact evV_trace (instOf D) (Formalism.L2.Host.tauPl D ρ) y
  refine h.trans ?_
  rw [hs, ← Complex.exp_sum, ← Finset.mul_sum, Finset.sum_neg_distrib]
  congr 1
  push_cast
  ring

theorem psi_fin_trace (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (psiEf : (instOf D).E ⊗[(instOf D).F] Formalism.MainNotions.S.Af (instOf D).F → ℂ)
    (hadd : ∀ x y, psiEf (x + y) = psiEf x * psiEf y)
    (hint : ∀ x ∈ IntAf (instOf D).F (instOf D).E, psiEf x = 1)
    (hrat : ∀ x : (instOf D).E, psiEf (Formalism.UG.inclE (F := (instOf D).F) (Formalism.MainNotions.S.Af (instOf D).F) x) * psiEinf (instOf D) x = 1)
    (y : AE D) :
    ψ (pairA D.host.F 0 (Algebra.trace (AF D.host.F) (AE D) y).2) = psiEf (tauF (instOf D) (-y)) :=
  fin_char (instOf D) ψ (GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ) (fun _ hβ => GlobalTheory.SplitCharCond.char_int hψ hβ)
    psiEf hadd hint hrat y

end GlobalTheory.Core.TieSign
end

noncomputable section
namespace GlobalTheory.Core.TieSign
open Formalism.L2.SG.AdBridge Formalism.L2.SG.InstExistsPf

theorem thetaV_incA' (D : D7) (v : InfinitePlace (instOf D).F) (y : D.host.E) :
    thetaV (instOf D) v (incA D y) = (instOf D).φ v y := by
  have := thetaV_tmul (instOf D) v 1 y
  rw [map_one, one_mul] at this
  exact this

theorem tauF_incA' (D : D7) (y : D.host.E) :
    tauF (instOf D) (incA D y) = Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) y :=
  tauF_tmul (instOf D) 1 y

theorem thetaV_mulAE (D : D7) (v : InfinitePlace (instOf D).F) (a b : AE D) :
    thetaV (instOf D) v (a * b) = thetaV (instOf D) v a * thetaV (instOf D) v b := map_mul _ a b

theorem thetaV_negAE (D : D7) (v : InfinitePlace (instOf D).F) (a : AE D) :
    thetaV (instOf D) v (-a) = -thetaV (instOf D) v a := map_neg _ a

theorem thetaV_sumAE (D : D7) (v : InfinitePlace (instOf D).F) {ρ : ℕ} (x : Fin ρ → AE D) :
    thetaV (instOf D) v (∑ a, x a) = ∑ a, thetaV (instOf D) v (x a) := map_sum _ x _

theorem tauF_mulAE (D : D7) (a b : AE D) :
    tauF (instOf D) (a * b) = tauF (instOf D) a * tauF (instOf D) b := map_mul _ a b

theorem tauF_sumAE (D : D7) {ρ : ℕ} (x : Fin ρ → AE D) :
    tauF (instOf D) (∑ a, x a) = ∑ a, tauF (instOf D) (x a) := map_sum _ x _

theorem star_psi_eq {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (a : AF F) :
    star (ψ a) = ψ (-a) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ.2.1 a]
  simp

theorem psi_split {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (a : AF F) :
    ψ a = ψ (pairA F a.1 0) * ψ (pairA F 0 a.2) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  exact Prod.ext (add_zero _).symm (zero_add _).symm

theorem cexp_two_pi_I_neg_inv_nat_smul_add_star {g : ℕ} (c x : ℂ) (hc : c = ((g : ℂ))⁻¹) :
    Complex.exp (2 * Real.pi * Complex.I * -(-(c * x) + star (-(c * x)))) =
      Complex.exp (2 * Real.pi * Complex.I * ((x + star x) / (g : ℂ))) := by
  subst hc
  congr 1
  simp only [star_neg, star_mul', star_inv₀, star_natCast]
  ring

theorem star_psiE_div (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (psiEf : (instOf D).E ⊗[(instOf D).F] Formalism.MainNotions.S.Af (instOf D).F → ℂ)
    (hadd : ∀ x y, psiEf (x + y) = psiEf x * psiEf y)
    (hint : ∀ x ∈ IntAf (instOf D).F (instOf D).E, psiEf x = 1)
    (hrat : ∀ x : (instOf D).E, psiEf (Formalism.UG.inclE (F := (instOf D).F) (Formalism.MainNotions.S.Af (instOf D).F) x) * psiEinf (instOf D) x = 1)
    (g : ℕ) (hg : g ≠ 0) (S : AE D) :
    star (psiE ψ (incA D ((g : D.host.E)⁻¹) * S)) =
      (∏ v, Complex.exp (2 * Real.pi * Complex.I *
        ((thetaV (instOf D) v S + star (thetaV (instOf D) v S)) / (g : ℂ)))) *
        psiEf (divN (instOf D) g (tauF (instOf D) S)) := by
  have key : ∀ v : InfinitePlace (instOf D).F, (instOf D).φ v ((g : D.host.E)⁻¹) = ((g : ℂ))⁻¹ := by
    intro v
    show (instOf D).φ v ((g : (instOf D).E)⁻¹) = _
    rw [map_inv₀, map_natCast]
  have h1 : ∀ v : InfinitePlace (instOf D).F, Complex.exp (2 * Real.pi * Complex.I *
      -(thetaV (instOf D) v (-(incA D ((g : D.host.E)⁻¹) * S)) + star (thetaV (instOf D) v (-(incA D ((g : D.host.E)⁻¹) * S))))) =
      Complex.exp (2 * Real.pi * Complex.I * ((thetaV (instOf D) v S + star (thetaV (instOf D) v S)) / (g : ℂ))) := by
    intro v
    rw [thetaV_negAE, thetaV_mulAE, thetaV_incA']
    exact cexp_two_pi_I_neg_inv_nat_smul_add_star _ _ (key v)
  have h2 : tauF (instOf D) (incA D ((g : D.host.E)⁻¹) * S) = divN (instOf D) g (tauF (instOf D) S) := by
    rw [tauF_mulAE, tauF_incA', divN]
    congr 1
  rw [psiE, star_psi_eq ψ hψ.1, ← map_neg, psi_split, psi_inf_trace D ψ hψ, psi_fin_trace D ψ hψ psiEf hadd hint hrat, neg_neg]
  congr 1
  · exact Finset.prod_congr rfl fun v _ => h1 v
  · exact congrArg psiEf h2

theorem sum_add_star_eq_of_eq_fin_sum {ρ : ℕ} (s : ℂ) (c : Fin ρ → ℂ) (h : s = ∑ a, c a) :
    s + star s = ∑ a, (c a + star (c a)) := by
  rw [h, star_sum, ← Finset.sum_add_distrib]

theorem rv_nxt (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) {ρ : ℕ} (e : Fin ρ → Fin I.n → I.E) (z : Fin I.n → I.E)
    (a : Fin ρ) : rv I v (nxt e z a) = nxt (fun b => rv I v (e b)) (rv I v z) a := by
  unfold nxt
  split_ifs <;> rfl

theorem castGA_self' {I : Formalism.MainNotions.S.AutInst} (e : I = I) (x : I.GA) : castGA e x = x := rfl

theorem core (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (I : Formalism.MainNotions.S.AutInst)
    (hI : I = instOf D) (ιE : I.E ≃+* D.host.E) (hId : ∀ y, HEq (ιE y) y) (hr : (D.sp.Y 0).rank = I.n)
    (psiEf : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F → ℂ)
    (hadd : ∀ x y, psiEf (x + y) = psiEf x * psiEf y)
    (hint : ∀ x ∈ IntAf I.F I.E, psiEf x = 1)
    (hrat : ∀ x : I.E, psiEf (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) * psiEinf I x = 1)
    (g : ℕ) (hg : g ≠ 0) {ρ : ℕ} (e f : Fin ρ → Fin I.n → I.E) (z : Fin I.n → I.E) (n : GA D (D.sp.Y 0)) :
    star (psiE ψ (incA D ((g : D.host.E)⁻¹) * ∑ a, hN n (fun k => ιE (f a (Fin.cast hr k)))
      (nxt (fun b k => ιE (e b (Fin.cast hr k))) (fun k => ιE (z (Fin.cast hr k))) a))) =
    psiInf I g e f z (castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D n)).1 *
      psiFin I psiEf g e f z (castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D n)).2 := by
  subst hI
  have hid : ∀ y, ιE y = y := fun y => eq_of_heq (hId y)
  simp only [castGA_self']
  have hs : ∀ v, thetaV (instOf D) v (∑ a, hN n (fun k => ιE (f a (Fin.cast hr k)))
      (nxt (fun b k => ιE (e b (Fin.cast hr k))) (fun k => ιE (z (Fin.cast hr k))) a)) =
      ∑ a, hJ ((instOf D).ε v) (rv (instOf D) v (f a))
        (uMat ((Formalism.IndefR.RationalEmbedding.iota D n).1 v) *ᵥ nxt (fun b => rv (instOf D) v (e b)) (rv (instOf D) v z) a) := by
    intro v
    rw [thetaV_sumAE]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [thetaV_hN]
    simp only [hid]
    exact congrArg (fun w => hJ ((instOf D).ε v) (rv (instOf D) v (f a))
      (uMat ((Formalism.IndefR.RationalEmbedding.iota D n).1 v) *ᵥ w)) (rv_nxt (instOf D) v e z a)
  have ht : tauF (instOf D) (∑ a, hN n (fun k => ιE (f a (Fin.cast hr k)))
      (nxt (fun b k => ιE (e b (Fin.cast hr k))) (fun k => ιE (z (Fin.cast hr k))) a)) =
      ∑ a, hA (instOf D) (incl (instOf D) (f a))
        ((instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D n).2 *ᵥ incl (instOf D) (nxt e z a)) := by
    rw [tauF_sumAE]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [tauF_hN]
    simp only [hid]
    rfl
  rw [star_psiE_div D ψ hψ psiEf hadd hint hrat g hg]
  congr 1
  · unfold Formalism.L2.SG.HidaSetting.psiInf
    refine Finset.prod_congr rfl fun v _ => ?_
    unfold psiR rootCoord
    exact congrArg (fun w => Complex.exp (2 * Real.pi * Complex.I * (w / (g : ℂ)))) (sum_add_star_eq_of_eq_fin_sum _ _ (hs v))
  · unfold psiFin
    exact congrArg (fun w => psiEf (divN (instOf D) g w)) ht

end GlobalTheory.Core.TieSign
end

open GlobalTheory.Core.TieSign GlobalTheory.Core.SBesEx in

theorem GlobalTheory.Core.Mi.tiepsi_sign : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ), IdE X → IsStdChar D ψ (-1) → ∃ lam : D.host.E, (lam = (X.B.g : D.host.E) ∨ lam = -(X.B.g : D.host.E)) ∧ ∀ t : D.host.E, t ≠ 0 → ∀ (V₀ L : HSp D) (d : HypDec (D.sp.Y 0) V₀ D.R.rS) (o : OrthDec V₀ (D.sp.X 0) L) (ζ : Fin L.rank → D.host.E), d.e = GlobalTheory.Core.SBesEx.eM X h t lam → d.e' = GlobalTheory.Core.SBesEx.e'M X h t lam → d.i₀ *ᵥ vecB o ζ = t • GlobalTheory.Core.SBesEx.cY X h (X.zu u) → ∀ n ∈ flagN d, star (psiBes ψ d 1 (vecB o ζ) n) = X.psiInfU u (iotaX X h n).1 * X.psiFinU u (iotaX X h n).2 := by
  intro D X h u ψ hE hψ
  have hg : X.B.g ≠ 0 := Formalism.L2.SG.Pf.modulus_g_ne_zero X
  have hg' : ((X.B.g : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hg
  refine ⟨(X.B.g : D.host.E), Or.inl rfl, ?_⟩
  intro t ht V₀ L d o ζ hde hde' hz n _hn
  have hA := simpleSum_eq D d (fun a => cY X h (X.eX a)) (fun a => cY X h (X.fY a)) (cY X h (X.zu u)) (vecB o ζ) t
    (X.B.g : D.host.E) ht hg' (by rw [hde]; rfl) (by rw [hde']; rfl) hz n
  rw [psiBes, map_one, one_mul, hA]
  exact core D ψ hψ X.B.I h X.ιE hE (rank_eq X h) X.psiEf X.psiEf_add X.psiEf_int X.psiEf_rat X.B.g hg X.eR X.fR (X.zR u) n
