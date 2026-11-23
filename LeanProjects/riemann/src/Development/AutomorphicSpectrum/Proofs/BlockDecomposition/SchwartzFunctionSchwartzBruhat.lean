import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.SchGlue

open GlobalTheory.Published.SiegelOneVector

variable {D : D7}

theorem exists_homeomorph_of_sections {A Y Z : Type} [TopologicalSpace A] [TopologicalSpace Y] [TopologicalSpace Z]
    (p : A → Y) (s : Y → A) (c : Y → Z) (σ : Z → A) (hp : Continuous p) (hs : Continuous s)
    (hc : Continuous fun a => c (p a)) (hσ : Continuous σ) (h1 : ∀ y, p (s y) = y)
    (h2 : ∀ z, c (p (σ z)) = z) (h3 : ∀ y, p (σ (c y)) = y) :
    ∃ P : Y ≃ₜ Z, ∀ y, P y = c y := by
  have hcc : Continuous c := by
    have : c = (fun a => c (p a)) ∘ s := funext fun y => by simp only [Function.comp, h1]
    rw [this]
    exact hc.comp hs
  exact ⟨{ toFun := c, invFun := fun z => p (σ z), left_inv := h3, right_inv := h2,
           continuous_toFun := hcc, continuous_invFun := hp.comp hσ }, fun _ => rfl⟩

set_option maxHeartbeats 1600000 in

theorem exists_infHomeo {θ : InfFam D} (hθ : IsInfFam θ) :
    ∃ P : (Ainf D.host.F ⊗[D.host.F] D.host.E) ≃ₜ (D.what₂.Tau → ℂ), ∀ y τ, P y τ = θ τ y := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, he, hec, hec'⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hinf : ∀ y, infPart D (e.symm (y, 0)) = y := fun y => by
    have := (he (e.symm (y, 0))).1
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  have hfin : ∀ y, finPart D (e.symm (y, 0)) = 0 := fun y => by
    have := (he (e.symm (y, 0))).2
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  have hci : Continuous (infPart D) := by
    have : (infPart D : AE D → _) = fun z => (e z).1 := funext fun z => ((he z).1).symm
    rw [this]
    exact continuous_fst.comp hec
  have hs : Continuous fun y : Ainf D.host.F ⊗[D.host.F] D.host.E => e.symm (y, 0) :=
    hec'.comp (continuous_id.prodMk continuous_const)
  have hback : ∀ a : AE D, finPart D a = 0 → a = σ fun τ => θ τ (infPart D a) := fun a ha => by
    refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
    · rw [(finPart D).map_sub, ha, hσ.fin, sub_zero]
    · rw [(infPart D).map_sub, (θ τ).map_sub, hσ.comp, sub_self]
  obtain ⟨P, hP⟩ := exists_homeomorph_of_sections (infPart D : AE D → _) (fun y => e.symm (y, 0))
    (fun (y : Ainf D.host.F ⊗[D.host.F] D.host.E) (τ : D.what₂.Tau) => θ τ y) σ hci hs
    (continuous_pi fun τ => GlobalTheory.FockCompare.continuous_comp hθ τ) hσ.cont hinf
    (fun z => funext fun τ => hσ.comp z τ)
    (fun y => by
      obtain ⟨a, ha⟩ : ∃ a : AE D, a = e.symm (y, 0) := ⟨_, rfl⟩
      have h1 : infPart D a = y := ha ▸ hinf y
      have h2 : finPart D a = 0 := ha ▸ hfin y
      subst h1
      exact congrArg (infPart D) (hback a h2).symm)
  exact ⟨P, fun y τ => congrFun (hP y) τ⟩

theorem isSchwartzArch_comp {θ : InfFam D} (hθ : IsInfFam θ) {m r : ℕ}
    (f : SchwartzMap (D.what₂.Tau → Fin m → Fin r → ℂ) ℂ) :
    IsSchwartzArch (F := D.host.F) (E := D.host.E) (M := m) (n := r)
      fun Y => f fun τ i j => θ τ (Y j i) := by
  obtain ⟨P, hP⟩ := exists_infHomeo hθ
  let Q : (Fin r → Fin m → Ainf D.host.F ⊗[D.host.F] D.host.E) ≃ₜ (D.what₂.Tau → Fin m → Fin r → ℂ) :=
    { toFun := fun Y τ i j => P (Y j i) τ
      invFun := fun c j i => P.symm fun τ => c τ i j
      left_inv := fun Y => by simp
      right_inv := fun c => by simp
      continuous_toFun := continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply τ).comp (P.continuous.comp ((continuous_apply i).comp (continuous_apply j)))
      continuous_invFun := continuous_pi fun j => continuous_pi fun i => P.symm.continuous.comp
        (continuous_pi fun τ => (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply τ))) }
  have hQ : ∀ Y τ i j, Q Y τ i j = θ τ (Y j i) := fun Y τ i j => hP _ _
  have hadd : ∀ X Y, Q (X + Y) = Q X + Q Y := fun X Y => by
    funext τ i j
    simp only [hQ, Pi.add_apply, map_add]
  let B : (D.what₂.Tau → Fin m → Fin r → ℂ) ≃L[ℝ]
      (Fin (Module.finrank ℝ (D.what₂.Tau → Fin m → Fin r → ℂ)) → ℝ) :=
    (Module.finBasis ℝ (D.what₂.Tau → Fin m → Fin r → ℂ)).equivFun.toContinuousLinearEquiv
  refine ⟨_, (AddEquiv.mk' Q.toEquiv hadd).trans B.toLinearEquiv.toAddEquiv,
    B.continuous.comp Q.continuous, Q.symm.continuous.comp B.symm.continuous,
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ B.symm f, fun Y => ?_⟩
  show _ = f (B.symm (B (Q Y)))
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact congrArg f (funext fun τ => funext fun i => funext fun j => (hQ Y τ i j).symm)

theorem isSB_swap {m r : ℕ} {g : (Fin m → Fin r → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin m → Fin r → Af D.host.F ⊗[D.host.F] D.host.E)) :
    IsSB fun Y : Fin r → Fin m → Af D.host.F ⊗[D.host.F] D.host.E => g fun i j => Y j i := by
  let S : (Fin r → Fin m → Af D.host.F ⊗[D.host.F] D.host.E) ≃ₜ
      (Fin m → Fin r → Af D.host.F ⊗[D.host.F] D.host.E) :=
    { toFun := fun Y i j => Y j i
      invFun := fun Y j i => Y i j
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply i).comp (continuous_apply j)
      continuous_invFun := continuous_pi fun j => continuous_pi fun i =>
        (continuous_apply j).comp (continuous_apply i) }
  exact ⟨hg.1.comp_continuous S.continuous, hg.2.comp_homeomorph S⟩

theorem isSchwartzArch_smul {M n : ℕ} (c : ℂ) {Φ : (Fin n → Fin M → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℂ}
    (h : IsSchwartzArch (F := D.host.F) (E := D.host.E) Φ) :
    IsSchwartzArch (F := D.host.F) (E := D.host.E) fun X => c * Φ X := by
  obtain ⟨N, e, h1, h2, f, hf⟩ := h
  exact ⟨N, e, h1, h2, c • f, fun X => by simp [hf]⟩

theorem sb_zero {M n : ℕ} :
    IsSchwartzBruhat (F := D.host.F) (E := D.host.E) (0 : (Fin n → Fin M → AE D) → ℂ) :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun _ => by simp⟩

theorem sb_add {M n : ℕ} {Φ Ψ : (Fin n → Fin M → AE D) → ℂ}
    (hΦ : IsSchwartzBruhat (F := D.host.F) (E := D.host.E) Φ)
    (hΨ : IsSchwartzBruhat (F := D.host.F) (E := D.host.E) Ψ) :
    IsSchwartzBruhat (F := D.host.F) (E := D.host.E) (Φ + Ψ) := by
  obtain ⟨k, a, b, ha, hb, hs⟩ := hΦ
  obtain ⟨k', a', b', ha', hb', hs'⟩ := hΨ
  refine ⟨k + k', Fin.append a a', Fin.append b b', fun i => ?_, fun i => ?_, fun X => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact ha i
    · rw [Fin.append_right]; exact ha' i
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact hb i
    · rw [Fin.append_right]; exact hb' i
  · rw [Fin.sum_univ_add, Pi.add_apply, hs, hs']
    simp only [Fin.append_left, Fin.append_right]

theorem sb_smul {M n : ℕ} (c : ℂ) {Φ : (Fin n → Fin M → AE D) → ℂ}
    (hΦ : IsSchwartzBruhat (F := D.host.F) (E := D.host.E) Φ) :
    IsSchwartzBruhat (F := D.host.F) (E := D.host.E) (c • Φ) := by
  obtain ⟨k, a, b, ha, hb, hs⟩ := hΦ
  refine ⟨k, fun i X => c * a i X, b, fun i => isSchwartzArch_smul c (ha i), hb, fun X => ?_⟩
  rw [Pi.smul_apply, hs, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.CompanionTheory.SiegelND.SchGlue

namespace GlobalTheory.CompanionTheory.SiegelND

open GlobalTheory.CompanionTheory.SiegelND.SchGlue

theorem isSchwartzBruhat_tupOf_of_mem_schwartzA : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m r : ℕ) (φ : Mx D m r → ℂ), φ ∈ schwartzA θ m r →
  GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (F := D.host.F) (E := D.host.E) (fun X : Fin r → Fin m → AE D => φ (tupOf X)) := by
  intro D θ hθ m r φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine ⟨1, fun _ Y => f fun τ i j => θ τ (Y j i), fun _ Y => g fun i j => Y j i,
      fun _ => isSchwartzArch_comp hθ f, fun _ => isSB_swap hg, fun X => ?_⟩
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rfl
  | zero => exact sb_zero
  | add a b _ _ ha hb => exact sb_add ha hb
  | smul c a _ ha => exact sb_smul c ha

end GlobalTheory.CompanionTheory.SiegelND
