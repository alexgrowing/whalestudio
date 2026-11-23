import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.GraphHeightLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceNonsplitPlace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open Formalism.UG (GLint)

noncomputable section
namespace GlobalTheory.InertIwasawaGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_trace_one_loc {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : HeightOneSpectrum (𝓞 F)}
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) :
    ∃ τ ∈ intLoc F E v, τ + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ τ = 1 := by
  have hu := (GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl
  obtain ⟨x, hx⟩ := GlobalTheory.LFun.InertChart.exists_conj_sub_unit h hw
  have hσ := GlobalTheory.LFun.InertChart.conj_conj h
  have h0 : σ (x : E) - x ≠ 0 := by
    intro e; rw [e, map_zero] at hx; exact zero_ne_one hx
  set t : E := σ x / (σ x - x) with ht
  have hsum : t + σ t = 1 := by
    rw [ht, map_div₀, map_sub, hσ, ← neg_sub (σ (x : E)) x, div_neg, ← sub_eq_add_neg, ← sub_div, div_self h0]
  refine ⟨(1 : Fv F v) ⊗ₜ[F] t, ?_, ?_⟩
  · rw [GlobalTheory.LFun.InertChart.mem_intLoc_iff hw hu, GlobalTheory.LFun.toCompl_tmul, map_one, one_mul]
    have hval : ∀ a : E, Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a := fun a =>
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    change Valued.v (algebraMap E (w.adicCompletion E) t) ≤ 1
    rw [hval, ht, map_div₀, hx, div_one]
    exact w.valuation_le_one (RingOfIntegers.mapRingHom (σ : E →+* E) x)
  · change (1 : Fv F v) ⊗ₜ[F] t + 1 ⊗ₜ[F] σ t = 1
    rw [← TensorProduct.tmul_add, hsum]; rfl

open GlobalTheory.LFun GlobalTheory.InertIwasawa in

theorem hasIwasawa_of_inertAt {σ : E →ₐ[F] E} (hC : IsCMExt F E σ) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (hQ : Q = dblGram finSumFinEquiv J) {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsLattice E L]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (hL : IsSelfDualAt σ J L v) : HasIwasawa σ Q (KFin σ Q L v) := fun g => by
  have h := (InertChart.under_eq_iff hw w).2 rfl
  obtain ⟨τ, hτO, hτ⟩ := exists_trace_one_loc hC hw
  obtain ⟨a, ha⟩ := Frames.exists_isLatticeFrame (F := F) L
  have eQ : JR (F := F) (Fv F v) Q = dblGram finSumFinEquiv (JR (Fv F v) J) := hQ ▸ JR_dblGram _ J
  obtain ⟨k, h1, h2, h3⟩ := exists_stab finSumFinEquiv (intLoc F E v)
    (hasFrames_of_equiv _ (w.adicCompletionIntegers E) (InertChart.complEquiv hw h) (InertChart.mem_intLoc_iff hw h))
    (σ := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) (fun _ => sigR_mem_intLoc σ) (sigR_invol (InertChart.conj_conj hC))
    hτO hτ
    (J := JR (Fv F v) J) (by ext i j; exact congrArg (fun x => (1 : Fv F v) ⊗ₜ[F] x) (hJ.1 i j))
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_det_JR hJ.2)) (Λ := latLoc F L v)
    (fun y => Submodule.ext_iff.1 hL y) (ha v) (g := matHom _ σ Q g) (eQ ▸ g.2)
  let κ : GLoc σ Q v := ⟨k, (eQ ▸ h1 : k ∈ Formalism.UG.UJ _ (JR (Fv F v) Q))⟩
  have hκ : κ ∈ KFin σ Q L v := by
    change k ∈ Formalism.UG.stabGL _
    rwa [latLoc_sumLat]
  exact ⟨⟨g * κ, h3⟩, κ⁻¹, inv_mem hκ, (mul_inv_cancel_right g κ).symm⟩

theorem ioH_mem_siegel_mul_KFin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)),
    IsSelfDualAt σ J L v → ∀ P : HeightOneSpectrum (𝓞 E), IsInertUnder v P → ∀ g : GLoc σ J v,
      ∃ p : siegelH (Fv F v) σ (dblGram finSumFinEquiv J), ∃ k ∈ KFin σ (dblGram finSumFinEquiv J) L v,
        ioH (Fv F v) σ rfl (g, 1) = (p : GLoc σ (dblGram finSumFinEquiv J) v) * k := by
  intro F E _ _ _ _ _ σ h n J hJ L _ v hL P hP g
  exact hasIwasawa_of_inertAt h hJ rfl (w := P) hP hL _

end GlobalTheory.InertIwasawaGen
