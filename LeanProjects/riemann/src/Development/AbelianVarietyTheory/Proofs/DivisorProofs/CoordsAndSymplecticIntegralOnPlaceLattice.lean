import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddConjEqOneOfFormallyUnramified
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.AdelicU GlobalTheory.WeilM

noncomputable section

namespace GlobalTheory.LatticeAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def Gd (v : HeightOneSpectrum (𝓞 F)) (x : AF F) : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) x ∧ evFin F v x ∈ v.adicCompletionIntegers F

theorem gd_zero (v : HeightOneSpectrum (𝓞 F)) : Gd v (0 : AF F) :=
  ⟨fun u _ => smul_zero u, by rw [map_zero]; exact zero_mem _⟩

theorem gd_add {v : HeightOneSpectrum (𝓞 F)} {x y : AF F} (hx : Gd v x) (hy : Gd v y) : Gd v (x + y) :=
  ⟨fun u hu => by rw [smul_add, hx.1 u hu, hy.1 u hu, add_zero], by rw [map_add]; exact add_mem hx.2 hy.2⟩

theorem gd_neg {v : HeightOneSpectrum (𝓞 F)} {x : AF F} (hx : Gd v x) : Gd v (-x) :=
  ⟨fun u hu => by rw [smul_neg, hx.1 u hu, neg_zero], by rw [map_neg]; exact neg_mem hx.2⟩

theorem gd_mul {v : HeightOneSpectrum (𝓞 F)} {x y : AF F} (hx : Gd v x)
    (hy : evFin F v y ∈ v.adicCompletionIntegers F) : Gd v (x * y) :=
  ⟨fun u hu => by rw [← smul_mul_assoc, hx.1 u hu, zero_mul], by rw [map_mul]; exact mul_mem hx.2 hy⟩

theorem ev_alg (v : HeightOneSpectrum (𝓞 F)) (y : F) :
    evFin F v (algebraMap F (AF F) y) = algebraMap F (Fv F v) y := AlgHom.commutes _ y

def bil (σ : E →ₐ[F] E) {n d : ℕ} (ξ : E) (JX : Matrix (Fin n) (Fin n) E) (JY : Matrix (Fin d) (Fin d) E) :
    LinearMap.BilinForm (AF F) (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) :=
  LinearMap.mk₂ (AF F) (symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) ξ)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JX) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JY))
    (fun x x' y => by
      simp only [symp, hTens, Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add, map_add])
    (fun a x y => by
      simp only [symp, hTens, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, mul_smul_comm, map_smul])
    (fun x y y' => by
      simp only [symp, hTens, Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add, map_add])
    (fun a x y => by
      simp only [symp, hTens, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, mul_smul_comm, map_smul])

theorem symp_incM (σ : E →ₐ[F] E) {n d : ℕ} (ξ : E) (JX : Matrix (Fin n) (Fin n) E)
    (JY : Matrix (Fin d) (Fin d) E) (x y : Matrix (Fin n) (Fin d) E) :
    symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) ξ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JX) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JY)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F y) = algebraMap F (AF F) (symp σ ξ JX JY x y) := by
  have ht : ∀ e : E, Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) (inclR (F := F) (AF F) e) =
      algebraMap F (AF F) (Algebra.trace F E e) := fun e => by
    show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
    rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
  have hc : ∀ e : E, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  rw [symp, symp, ← ht]
  simp only [hTens, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, hc, map_mul, map_sum]

end GlobalTheory.LatticeAtPlace

namespace GlobalTheory.LatticeAtPlace

theorem coords_symp_integral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}
    (JX : Matrix (Fin n) (Fin n) E) (JY : Matrix (Fin d) (Fin d) E) (ξ : E) (v : HeightOneSpectrum (𝓞 F))
    (co : (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) →ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F))
    (T₀ : Set (Matrix (Fin n) (Fin d) E)) (yf zf : Matrix (Fin n) (Fin d) E → Fin n × Fin d → F),
    (∀ x, co (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (yf x k), fun k => algebraMap F (AF F) (zf x k))) →
    (∀ t ∈ T₀, ∀ k, algebraMap F (Fv F v) (yf t k) ∈ v.adicCompletionIntegers F ∧
      algebraMap F (Fv F v) (zf t k) ∈ v.adicCompletionIntegers F) →
    (∀ t ∈ T₀, ∀ t' ∈ T₀, algebraMap F (Fv F v) (GlobalTheory.WeilM.symp σ ξ JX JY t t') ∈ v.adicCompletionIntegers F) →
    ∀ γ ∈ AddSubgroup.closure {z | ∃ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧
        ∃ t ∈ T₀, z = a • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F t},
      (∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co γ).1 k) ∧ evFin F v ((co γ).1 k) ∈ v.adicCompletionIntegers F ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co γ).2 k) ∧ evFin F v ((co γ).2 k) ∈ v.adicCompletionIntegers F) ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) ξ)
                   (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JX) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JY) γ γ) ∧
        evFin F v (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) ξ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JX)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JY) γ γ) ∈ v.adicCompletionIntegers F) := by
  intro F E _ _ _ _ _ σ n d JX JY ξ v co T₀ yf zf hco hyz hs γ hγ
  set S : Set (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) := {z | ∃ a : AF F,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧
      ∃ t ∈ T₀, z = a • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F t} with hS
  have hcoord : ∀ z ∈ AddSubgroup.closure S, ∀ k, Gd v ((co z).1 k) ∧ Gd v ((co z).2 k) := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha1, ha2, t, ht, rfl⟩ := hz
      intro k
      rw [map_smul, hco]
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      exact ⟨gd_mul ⟨ha1, ha2⟩ (by rw [ev_alg]; exact (hyz t ht k).1),
        gd_mul ⟨ha1, ha2⟩ (by rw [ev_alg]; exact (hyz t ht k).2)⟩
    | zero =>
      intro k
      simp only [map_zero, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]
      exact ⟨gd_zero v, gd_zero v⟩
    | add x y _ _ hx hy =>
      intro k
      simp only [map_add, Prod.fst_add, Prod.snd_add, Pi.add_apply]
      exact ⟨gd_add (hx k).1 (hy k).1, gd_add (hx k).2 (hy k).2⟩
    | neg x _ hx =>
      intro k
      simp only [map_neg, Prod.fst_neg, Prod.snd_neg, Pi.neg_apply]
      exact ⟨gd_neg (hx k).1, gd_neg (hx k).2⟩
  have hgen : ∀ x ∈ S, ∀ y ∈ S, Gd v (bil σ ξ JX JY x y) := by
    rintro _ ⟨a, ha1, ha2, t, ht, rfl⟩ _ ⟨b, -, hb2, t', ht', rfl⟩
    rw [LinearMap.map_smul₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul]
    have e : bil σ ξ JX JY (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F t) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F t') =
        algebraMap F (AF F) (symp σ ξ JX JY t t') := symp_incM σ ξ JX JY t t'
    rw [e]
    refine gd_mul ⟨ha1, ha2⟩ ?_
    rw [map_mul, ev_alg]
    exact mul_mem hb2 (hs t ht t' ht')
  have hpair : ∀ x ∈ AddSubgroup.closure S, ∀ y ∈ AddSubgroup.closure S, Gd v (bil σ ξ JX JY x y) := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      intro y hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy => exact hgen x hx y hy
      | zero => rw [map_zero]; exact gd_zero v
      | add y y' _ _ h h' => rw [map_add]; exact gd_add h h'
      | neg y _ h => rw [map_neg]; exact gd_neg h
    | zero => intro y _; rw [map_zero, LinearMap.zero_apply]; exact gd_zero v
    | add x x' _ _ h h' => intro y hy; rw [map_add, LinearMap.add_apply]; exact gd_add (h y hy) (h' y hy)
    | neg x _ h => intro y hy; rw [map_neg, LinearMap.neg_apply]; exact gd_neg (h y hy)
  have hp := hpair γ hγ γ hγ
  exact ⟨fun k => ⟨(hcoord γ hγ k).1.1, (hcoord γ hγ k).1.2, (hcoord γ hγ k).2.1, (hcoord γ hγ k).2.2⟩, hp.1, hp.2⟩

end GlobalTheory.LatticeAtPlace
