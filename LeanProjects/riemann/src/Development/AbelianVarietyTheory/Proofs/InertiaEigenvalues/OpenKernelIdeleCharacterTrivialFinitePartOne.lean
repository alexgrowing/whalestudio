import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatMMemOfLeHalf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArchAdeleTensorEquivComplexCmType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueInfEmb
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.UnivCover

namespace GlobalTheory.UnivCover.OpenKerChar

set_option maxHeartbeats 400000 in

theorem map_eq_one_of_finPart_eq_one : ∀ (D : D7) {A : Type} [Group A] (χ : (AE D)ˣ →* A),
    IsOpen (χ.ker : Set (AE D)ˣ) → ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → χ x = 1 := by
  intro D A _ χ hχ x hx
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hfam : GlobalTheory.Mem.Vol.IsCMFam (fun w : InfinitePlace D.host.E => w.embedding) := by
    unfold GlobalTheory.Mem.Vol.IsCMFam
    simp only [InfinitePlace.mk_embedding]
    exact Function.bijective_id
  choose θ hθ using fun w : InfinitePlace D.host.E =>
    (GlobalTheory.Mem.VolEmb.existsUnique_infEmb D.host.F D.host.E D.sp.cm.sig hcm w.embedding).exists
  obtain ⟨e2, -, hc2, hc2', -⟩ :=
    GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv D.host.F D.host.E D.sp.cm.sig (InfinitePlace D.host.E) _ θ hcm hfam hθ
  obtain ⟨e1, he1, hc1, hc1'⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have h2 : (e1 (x : AE D)).2 = 1 := (he1 _).2.trans hx
  set c : InfinitePlace D.host.E → ℂ := e2 (e1 (x : AE D)).1 with hcdef
  have hcu : IsUnit c := by
    have hu : IsUnit (e1 (x : AE D)) := x.isUnit.map e1
    exact (Prod.isUnit_iff.1 hu).1.map e2
  have hc0 : ∀ w, c w ≠ 0 := fun w => (Pi.isUnit_iff.1 hcu w).ne_zero
  let p : ℝ → (InfinitePlace D.host.E → ℂ) := fun t w => Complex.exp (t * Complex.log (c w))
  let γ : ℝ → AE D := fun t => e1.symm (e2.symm (p t), 1)
  have hpc : Continuous p := continuous_pi fun w =>
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hγc : Continuous γ := hc1'.comp ((hc2'.comp hpc).prodMk continuous_const)
  have hpmul : ∀ s t, p s * p t = p (s + t) := fun s t => by
    funext w
    simp only [p, Pi.mul_apply, ← Complex.exp_add, Complex.ofReal_add, add_mul]
  have hγmul : ∀ s t, γ s * γ t = γ (s + t) := fun s t => by
    simp only [γ, ← map_mul, Prod.mk_mul_mk, mul_one, hpmul]
  have hp0 : p 0 = 1 := by funext w; simp [p]
  have hγ0 : γ 0 = 1 := by simp only [γ, hp0, map_one, Prod.mk_one_one]
  have hp1 : p 1 = c := by funext w; simp [p, Complex.exp_log (hc0 w)]
  have hγ1 : γ 1 = x := by
    simp only [γ, hp1, hcdef, RingEquiv.symm_apply_apply]
    rw [← h2, Prod.mk.eta, RingEquiv.symm_apply_apply]
  have hr : ∀ t, γ t * γ (-t) = 1 := fun t =>
    (hγmul t (-t)).trans ((congrArg γ (add_neg_cancel t)).trans hγ0)
  have hl : ∀ t, γ (-t) * γ t = 1 := fun t =>
    (hγmul (-t) t).trans ((congrArg γ (neg_add_cancel t)).trans hγ0)
  let f : ℝ → (AE D)ˣ := fun t => Units.mk (γ t) (γ (-t)) (hr t) (hl t)
  have hf : Continuous f := Units.continuous_iff.2 ⟨hγc, hγc.comp continuous_neg⟩
  have hcl : IsClosed (χ.ker : Set (AE D)ˣ) := Subgroup.isClosed_of_isOpen _ hχ
  have hS : IsClopen (f ⁻¹' (χ.ker : Set (AE D)ˣ)) := ⟨hcl.preimage hf, hχ.preimage hf⟩
  have h0 : (0 : ℝ) ∈ f ⁻¹' (χ.ker : Set (AE D)ˣ) := by
    have : f 0 = 1 := Units.ext hγ0
    simp [this]
  rcases isClopen_iff.1 hS with h | h
  · rw [h] at h0; exact absurd h0 (Set.notMem_empty _)
  · have h1 : (1 : ℝ) ∈ f ⁻¹' (χ.ker : Set (AE D)ˣ) := h ▸ Set.mem_univ _
    have hf1 : f 1 = x := Units.ext hγ1
    rw [Set.mem_preimage, hf1] at h1
    exact h1

end GlobalTheory.UnivCover.OpenKerChar
