import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SquareComm

variable {D : D7} {M X V : HSp D} (ω : WRep M X) (j : GA D V → GA D X) (G : GA D V → ℂ)
  (ν : Measure (GA D M)) (𝓕 : Set (GA D M)) (μ : Measure (GA D V)) (𝓔 : Set (GA D V))

def innerInt (Φ : WO M X → ℂ) (w : GA D M) : ℂ := ∫ g in 𝓔, thetaKO ω w (j g) Φ * G g ∂μ

def iterInt (Φ : WO M X → ℂ) : ℂ := ∫ w in 𝓕, innerInt ω j G μ 𝓔 Φ w ∂ν

def iterConv : Submodule ℂ (WO M X → ℂ) where
  carrier := {Φ | (∀ w, IntegrableOn (fun g => thetaKO ω w (j g) Φ * G g) 𝓔 μ) ∧ IntegrableOn (innerInt ω j G μ 𝓔 Φ) 𝓕 ν}
  zero_mem' := ⟨fun w => by simp [thetaKO], by
    have : innerInt ω j G μ 𝓔 0 = 0 := by funext w; simp [innerInt, thetaKO]
    rw [this]; exact integrable_zero _ _ _⟩
  add_mem' := fun {Φ Ψ} h h' => ⟨fun w => ((h.1 w).add (h'.1 w)).congr (.of_forall fun g => by simp [thetaKO, add_mul]), by
    have : innerInt ω j G μ 𝓔 (Φ + Ψ) = innerInt ω j G μ 𝓔 Φ + innerInt ω j G μ 𝓔 Ψ := by
      funext w
      have := integral_add (h.1 w) (h'.1 w)
      simpa [innerInt, thetaKO, add_mul] using this
    rw [this]; exact h.2.add h'.2⟩
  smul_mem' := fun c Φ h => ⟨fun w => ((h.1 w).const_mul c).congr (.of_forall fun g => by simp [thetaKO, mul_assoc]), by
    have : innerInt ω j G μ 𝓔 (c • Φ) = fun w => c * innerInt ω j G μ 𝓔 Φ w := by
      funext w
      simp [innerInt, thetaKO, mul_assoc, integral_const_mul]
    rw [this]; exact h.2.const_mul c⟩

variable {ω j G ν 𝓕 μ 𝓔}

theorem ofSgn_symm_mem_GQ (ε : Bool) {γ : GA D M} (hγ : γ ∈ GQ M) : (ofSgn ε M).symm γ ∈ GQ (sgn ε M) := by
  have hγ' : γ.1 ∈ HFin (AF D.host.F) D.sp.cm.sig M.gram := hγ
  cases ε
  · exact hγ'
  · have hm : γ.1 ∈ HFin (AF D.host.F) D.sp.cm.sig (-M.gram) := by
      unfold HFin at hγ' ⊢
      rw [UJ_neg]
      exact hγ'
    rw [← neg_gram] at hm
    exact hm

theorem integral_rightTranslate (h : IsHaarFD M ν 𝓕) {f : GA D M → ℂ} (hf : ∀ γ ∈ GQ M, ∀ w, f (γ * w) = f w) (u : GA D M) :
    (IntegrableOn (fun w => f (w * u)) 𝓕 ν ↔ IntegrableOn f 𝓕 ν) ∧ ∫ w in 𝓕, f (w * u) ∂ν = ∫ w in 𝓕, f w ∂ν := by
  obtain ⟨hH, hFD⟩ := h
  obtain ⟨_, _, _, hB, hTG, _, hC⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D M
  have : ν.IsMulRightInvariant :=
    (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D M ν hH).1
  have hpres : MeasurePreserving (fun w => w * u) ν ν := measurePreserving_mul_right ν u
  have hemb : MeasurableEmbedding (fun w : GA D M => w * u) := (MeasurableEquiv.mulRight u).measurableEmbedding
  set S : Set (GA D M) := (fun w => w * u⁻¹) ⁻¹' 𝓕 with hSdef
  have hS : IsFundamentalDomain (GQ M) S ν :=
    hFD.preimage_of_equiv (measurePreserving_mul_right ν u⁻¹).quasiMeasurePreserving Function.bijective_id
      (fun g x => by simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc])
  have hset : (fun w => w * u) ⁻¹' S = 𝓕 := by
    ext w
    simp [hSdef]
  have hinv : ∀ (g : GQ M) (x : GA D M), f (g • x) = f x := fun g x => hf g g.2 x
  refine ⟨?_, ?_⟩
  · have h1 := hpres.integrableOn_comp_preimage hemb (f := f) (s := S)
    rw [hset] at h1
    exact h1.trans (hS.integrableOn_iff hFD hinv)
  · have h2 := hpres.setIntegral_preimage_emb hemb f S
    rw [hset] at h2
    exact h2.trans (hS.setIntegral_eq hFD hinv)

end GlobalTheory.SquareComm

end
