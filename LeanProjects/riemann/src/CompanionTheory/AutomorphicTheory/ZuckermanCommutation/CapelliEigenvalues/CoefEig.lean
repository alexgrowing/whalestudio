import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.FunAct
import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.ZuckDualTOfZuckDual

open Matrix PI.UpqRep Formalism.FourierDecayAlt
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.CapEig

theorem capC_vec (hI : PI.DSInfCharCap.DSInfCharCap) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {lam : Fin (2 * r + k + 1) → ℝ} {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Hs →L[ℂ] Hs)}
    (hlam : IsHCParam lam) (hσ : IsDSHpk k r ε lam σ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : Hs →L[ℂ] E) {v : Hs} (hv : v ∈ smoothVecs (k := k) (r := r) σ)
    {F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E} (hF : ∀ x ∈ UH (Hpk k r), F x = L (σ x v))
    (Y : ℂ) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    PI.CapelliEig.capC (k := k) (r := r) Y F g = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • F g := by
  obtain ⟨P₀, hP₀, hds⟩ := hσ
  have hdet : IsUnit P₀.det := (Matrix.isUnit_iff_isUnit_det _).mp hP₀.1.1
  have hPQ : P₀ * P₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hQP : P₀⁻¹ * P₀ = 1 := Matrix.nonsing_inv_mul _ hdet
  have hH : Formalism.QuantumDeterminants.Hpk k r = P₀ᴴ * Formalism.REAL.Jm ε * P₀ := hP₀.1.2.symm
  have hv' : Formalism.REAL.SmoothOnGV ε (fun x => σ (P₀⁻¹ * x * P₀) v) :=
    Formalism.QuantumDeterminants.ioh_smooth ε _ P₀ P₀⁻¹ (fun x => σ x v) hPQ hH hv
  have hg' : Formalism.REAL.inUJ ε (P₀ * g * P₀⁻¹) := Formalism.QuantumDeterminants.ioh_inUJ ε _ P₀ P₀⁻¹ g hPQ hH hg
  have hsm : Formalism.REAL.SmoothOnGV ε (fun x => L (σ (P₀⁻¹ * x * P₀) v)) :=
    (Formalism.REAL.rdVPair _ ε Hs E L _ 0 1 hv' (by simp [Formalism.REAL.inG]) inUJ_one).1
  have hm : ∀ a b, Formalism.REAL.inUJ ε a → Formalism.REAL.inUJ ε b →
      σ (P₀⁻¹ * (a * b) * P₀) = (σ (P₀⁻¹ * a * P₀)).comp (σ (P₀⁻¹ * b * P₀)) :=
    fun a b ha hb => hds.2.2.1.1.2 a ha b hb
  have hu : (Y + ((2 * r + k : ℕ) : ℂ) / 2) = Y + (((2 * r + k + 1 : ℕ) : ℂ) - 1) / 2 := by
    push_cast; ring
  unfold PI.CapelliEig.capC
  rw [capelli_localization _ ε _ _ P₀ P₀⁻¹ F (fun x => L (σ x v)) _ g hQP hPQ hH hF hg,
    capelli_transport _ ε _ _ P₀ P₀⁻¹ _ _ g hQP hPQ hH hsm hg, ← capelli_clm L hv' _ hg',
    capelli_vec (σ := fun x => σ (P₀⁻¹ * x * P₀)) hm hv' _ hg', hu, hI _ ε lam Hs _ hlam hds v hv' Y,
    Formalism.QuantumDeterminants.ioh_QP P₀ P₀⁻¹ g hQP, hF g hg, map_smul, map_smul]

theorem qminorOp_cast {n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)) (h : m = n)
    (a : Fin m → Fin n) (ha : ∀ j, (a j).val = j.val) (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Formalism.QuantumDeterminants.qminorOp Eop a a u f = Formalism.QuantumDeterminants.qminorOp Eop id id u f := by
  subst h
  have : a = id := funext fun j => Fin.ext (ha j)
  rw [this]

theorem capelli_eigenvalue_transfer : CompanionTheory.LimBd.Main.CVBridge := by
  intro k r E _ _ Y F
  unfold Q.CV Q.capL PI.CapelliEig.capC Formalism.QuantumDeterminants.capelliH Formalism.QuantumDeterminants.qdetOp
  have hm : Q.mdim k r 0 = 2 * r + k + 1 := by simp [Q.mdim]
  have hu : Q.uC k r 0 Y = Y + ((2 * r + k : ℕ) : ℂ) / 2 := by
    unfold Q.uC; rw [hm]; push_cast; ring
  rw [hu]
  exact qminorOp_cast _ hm _ (fun j => by simp [Q.posL]) _ _

theorem coefEig_of (hI : PI.DSInfCharCap.DSInfCharCap) (hK : PI.KFinSmooth) : CompanionTheory.LimBd.Main.CoefEig := by
  intro k r ε μ φ Wp Wq _ _ _ _ _ _ T hφ Y g hg
  obtain ⟨H, _, _, _, σ, v, w, hμ, hσ, hv, -, he⟩ := hφ
  rw [capelli_eigenvalue_transfer]
  exact capC_vec hI hμ hσ ((innerSL ℂ w).smulRight T) (hK k r ε μ H σ hμ hσ v hv)
    (F := fun x => φ x • T) (fun x hx => by simp [he x hx]) Y hg

end CompanionTheory.CapEig

end
