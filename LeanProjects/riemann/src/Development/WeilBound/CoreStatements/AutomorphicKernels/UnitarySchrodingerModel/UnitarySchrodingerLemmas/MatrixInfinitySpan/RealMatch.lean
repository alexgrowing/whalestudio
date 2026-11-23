import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.PsiPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussMulUnitary
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ExistsUnitaryDiag

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwSpanR

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS.SwMatch GlobalTheory.CompanionTheory.SiegelND

def lz {m k : ℕ} (fr : Matrix (Fin m) (Fin m) ℂ) (q : Fin m × Fin k × Bool) : PositivityTheory.Rg.Sw.PX m k :=
  if q.2.2 then ∑ b, MvPolynomial.C (star (fr q.1 b)) * MvPolynomial.X (b, q.2.1, true)
  else ∑ b, MvPolynomial.C (fr q.1 b) * MvPolynomial.X (b, q.2.1, false)

theorem evX_lz {m k : ℕ} (fr : Matrix (Fin m) (Fin m) ℂ) (y : Matrix (Fin m) (Fin k) ℂ) (q : Fin m × Fin k × Bool) :
    PositivityTheory.Rg.Sw.evX (lz fr q) y = if q.2.2 then star ((fr * y) q.1 q.2.1) else (fr * y) q.1 q.2.1 := by
  obtain ⟨a, i, b⟩ := q
  cases b <;> simp [lz, PositivityTheory.Rg.Sw.evX, Matrix.mul_apply, star_sum]

theorem trace_ct_mul_self {m k : ℕ} (Y : Matrix (Fin m) (Fin k) ℂ) :
    Matrix.trace (Yᴴ * Y) = ((∑ a, ∑ i, ‖Y a i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, ← starRingEnd_apply,
    Complex.conj_mul']
  push_cast
  exact Finset.sum_comm

theorem trace_frame {m k : ℕ} (fr fri G : Matrix (Fin m) (Fin m) ℂ) (Z : Matrix (Fin m) (Fin k) ℂ)
    (h1 : fr * fri = 1) (h2 : frᴴ * G * fr = 1) :
    Matrix.trace (Zᴴ * G * Z) = Matrix.trace ((fri * Z)ᴴ * (fri * Z)) := by
  have hz : Z = fr * (fri * Z) := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  calc Matrix.trace (Zᴴ * G * Z) = Matrix.trace ((fri * Z)ᴴ * (frᴴ * G * fr) * (fri * Z)) := by
        conv_lhs => rw [hz]
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h2, Matrix.mul_one]

theorem realMatch : RealMatch := by
  classical
  intro D n V ψ θ l s hθ _hψ hs e c a
  have hfr : ∀ τ, ∃ ε fr, PositivityTheory.Rg.Sw.Glob.IsTauFrame V τ s ε fr := fun τ =>
    PositivityTheory.Rg.Sw.Glob.sFrame D V τ s (hs τ)
  choose εG frM hfrM using hfr
  obtain ⟨frG, hfrG⟩ : ∃ frG : D.what₂.Tau → GL (Fin V.rank) ℂ, ∀ τ, (frG τ).1 = frM τ :=
    ⟨fun τ => Matrix.nonsingInvUnit (frM τ) (hfrM τ).1, fun τ => rfl⟩
  obtain ⟨τ0⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  obtain ⟨PG, hPG⟩ : ∃ PG : D.what₂.Tau → PositivityTheory.Rg.Sw.PX V.rank n, ∀ τ,
      PG τ = MvPolynomial.C (if τ = τ0 then c else 1) *
        ∏ k ∈ e.support, (if k.1 = τ then lz (frM τ) k.2 else 1) ^ (e k) := ⟨_, fun τ => rfl⟩
  refine ⟨εG, frG, PG, ?_, ?_⟩
  · intro τ
    rw [hfrG τ]
    convert (hfrM τ).2.1 using 3
    ext i j
    exact (hθ τ).1 _
  · intro x
    have hinv : ∀ τ, frM τ * ((frG τ)⁻¹).1 = 1 := fun τ => by
      rw [← hfrG τ]
      exact Units.mul_inv (frG τ)
    have hY : ∀ τ, PositivityTheory.SiegelWeilFormula.Gen.crd (θ τ) (frG τ) (aTau θ a τ) (HeckeCharacterZeroLocus.SiegelWeilU.projInf (tupInv x)) =
        ((frG τ)⁻¹).1 * compAt θ τ (HMul.hMul x a.1 : Mx D V.rank n) := fun τ => by
      rw [GlobalTheory.VacKInf.LeviFix.compAt_mul', ← Matrix.mul_assoc]
      rfl
    have hZ : ∀ τ, frM τ * (((frG τ)⁻¹).1 * compAt θ τ (HMul.hMul x a.1 : Mx D V.rank n)) =
        compAt θ τ (HMul.hMul x a.1 : Mx D V.rank n) := fun τ => by
      rw [← Matrix.mul_assoc, hinv τ, Matrix.one_mul]

    have hG : gauss V l s (fun τ => compAt θ τ (HMul.hMul x a.1 : Mx D V.rank n)) =
        ∏ τ, PositivityTheory.Rg.Sw.gs (2 * Real.pi * |l τ|) (((frG τ)⁻¹).1 * compAt θ τ (HMul.hMul x a.1 : Mx D V.rank n)) := by
      unfold gauss PositivityTheory.Rg.Sw.gs
      rw [← Complex.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [trace_frame (frM τ) ((frG τ)⁻¹).1 _ _ (hinv τ) (hfrM τ).2.2, trace_ct_mul_self]
      push_cast
      ring

    have hP : evalPoly (MvPolynomial.monomial e c) (fun τ => compAt θ τ (HMul.hMul x a.1 : Mx D V.rank n)) =
        ∏ τ, PositivityTheory.Rg.Sw.evX (PG τ) (((frG τ)⁻¹).1 * compAt θ τ (HMul.hMul x a.1 : Mx D V.rank n)) := by
      set f : D.what₂.Tau × Fin V.rank × Fin n × Bool → ℂ := fun k =>
        if k.2.2.2 then (starRingEnd ℂ) (compAt θ k.1 (HMul.hMul x a.1 : Mx D V.rank n) k.2.1 k.2.2.1)
        else compAt θ k.1 (HMul.hMul x a.1 : Mx D V.rank n) k.2.1 k.2.2.1 with hf
      have hτ : ∀ τ, PositivityTheory.Rg.Sw.evX (PG τ) (((frG τ)⁻¹).1 * compAt θ τ (HMul.hMul x a.1 : Mx D V.rank n)) =
          (if τ = τ0 then c else 1) * ∏ k ∈ e.support, (if k.1 = τ then f k else 1) ^ (e k) := fun τ => by
        rw [hPG τ]
        simp only [PositivityTheory.Rg.Sw.evX, map_mul, MvPolynomial.eval_C, map_prod, map_pow]
        congr 1
        refine Finset.prod_congr rfl fun k _ => ?_
        by_cases h : k.1 = τ
        · subst h
          rw [if_pos rfl, if_pos rfl]
          have := evX_lz (frM k.1) (((frG k.1)⁻¹).1 * compAt θ k.1 (HMul.hMul x a.1 : Mx D V.rank n)) k.2
          unfold PositivityTheory.Rg.Sw.evX at this
          rw [this, hZ k.1, hf]
          simp only [starRingEnd_apply]
        · rw [if_neg h, if_neg h, map_one]
      simp only [hτ]
      rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ τ0, if_pos (Finset.mem_univ _), Finset.prod_comm]
      unfold evalPoly
      rw [MvPolynomial.eval_monomial]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      simp only [ite_pow, one_pow]
      rw [Finset.prod_ite_eq Finset.univ k.1, if_pos (Finset.mem_univ _)]
      simp only [hf, ite_pow]
    unfold PositivityTheory.SiegelWeilFormula.Gen.phiInf
    simp only [hY]
    rw [hP, hG, ← Finset.prod_mul_distrib]

end PositivityTheory.PfSWUS.SwSpanR
