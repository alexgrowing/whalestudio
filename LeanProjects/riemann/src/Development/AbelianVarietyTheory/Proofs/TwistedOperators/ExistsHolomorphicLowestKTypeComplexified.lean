import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KTypeExtendsHolomorphicComplexifiedK

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet.LowTau

theorem exp_conj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (NormedSpace.exp A).map star = NormedSpace.exp (A.map star) := by
  have hc : ∀ B : Matrix (Fin n) (Fin n) ℂ, B.map star = Bᴴᵀ := fun B => by ext i j; simp
  rw [hc, hc, ← Matrix.exp_conjTranspose, ← Matrix.exp_transpose]

theorem inG_conj {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (h : inG ε X) :
    inG ε (X.map star) := by
  unfold inG at h ⊢
  have hJ : (Jm ε)ᵀ = Jm ε := by unfold Jm; simp
  have e1 : (X.map star)ᴴ = Xᵀ := by ext i j; simp
  have e2 : Xᴴᵀ = X.map star := by ext i j; simp
  have h2 := congrArg Matrix.transpose h
  rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, hJ, e2, Matrix.transpose_zero] at h2
  rw [e1, add_comm]
  exact h2

theorem exists_tau : ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : Fin n → Fin n → Module.End ℂ V) (ι : V →ₗᵢ[ℂ] H) (u : V), IsURepOn (UJset ε) σ → DerTie ε σ E ι → ‖u‖ = 1 → IsKTypeOf ε σ Λ ((kSpan ε E u).map ι.toLinearMap) → IsWtOn (Kset ε) σ Λ (ι u) → ∃ (W : Type) (_ : NormedAddCommGroup W) (_ : InnerProductSpace ℂ W) (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W) (j : W →ₗᵢ[ℂ] V), IsTau ε Λ τ w ∧ j w = u ∧ LinearMap.range j.toLinearMap = kSpan ε E u ∧ TauTie ε E j τ := by
  intro n ε Λ H V _ _ _ _ σ E ι u hσ hD hu hK hW
  set S : Submodule ℂ H := (Formalism.REAL.kSpan ε E u).map ι.toLinearMap with hS
  have huk : u ∈ Formalism.REAL.kSpan ε E u := by
    unfold Formalism.REAL.kSpan
    exact Submodule.mem_sInf.2 fun _ h => h.1
  have huS : ι u ∈ S := Submodule.mem_map_of_mem huk
  have hKU : Formalism.REAL.Kset ε ⊆ UJset ε := by
    intro g hg
    obtain ⟨hgu, hgc⟩ := hg
    have h1 : gᴴ * g = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff'.1 hgu
    show gᴴ * Jm ε * g = Jm ε
    rw [Matrix.mul_assoc, ← hgc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hexpK : ∀ Z : Matrix (Fin n) (Fin n) ℂ, inK ε Z → NormedSpace.exp Z ∈ Formalism.REAL.Kset ε := by
    intro Z hZ
    obtain ⟨hg, hc⟩ := hZ
    unfold inG at hg
    have hZH : Zᴴ = -Z := by
      have h1 : Zᴴ * Jm ε = -(Z * Jm ε) := by
        rw [hc]; exact eq_neg_of_add_eq_zero_left hg
      calc Zᴴ = Zᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]
        _ = -Z := by rw [h1, Matrix.neg_mul, Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]
    refine ⟨?_, (Commute.exp_left (show Commute Z (Jm ε) from hc)).eq⟩
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hZH,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl Z).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  have hσK : IsURepOn (Formalism.REAL.Kset ε) σ := by
    obtain ⟨⟨h1, hm⟩, hn, hc⟩ := hσ
    exact ⟨⟨h1, fun a ha b hb => hm a (hKU ha) b (hKU hb)⟩, fun g hg => hn g (hKU hg),
      fun v => (hc v).mono hKU⟩
  have hwS : ‖(⟨ι u, huS⟩ : S)‖ = 1 := by
    show ‖(ι u : H)‖ = 1
    simp [hu]
  obtain ⟨τ, hτ, hτσ⟩ := GlobalTheory.Dec.TauExt.tauExists n ε Λ H σ S ⟨ι u, huS⟩ hσK hK hwS hW
  let e := Submodule.equivMapOfInjective ι.toLinearMap ι.injective (Formalism.REAL.kSpan ε E u)
  have heι : ∀ x : S, ι (e.symm x : V) = (x : H) := by
    intro x
    have h0 : ((e (e.symm x) : S) : H) = ι (e.symm x : V) := rfl
    rw [LinearEquiv.apply_symm_apply] at h0
    exact h0.symm
  let j : S →ₗᵢ[ℂ] V :=
    { toLinearMap := (Formalism.REAL.kSpan ε E u).subtype ∘ₗ e.symm.toLinearMap
      norm_map' := fun x => by
        show ‖(e.symm x : V)‖ = ‖x‖
        rw [← ι.norm_map, heι, Submodule.coe_norm] }
  have hjι : ∀ x : S, ι (j x) = (x : H) := heι
  refine ⟨S, inferInstance, inferInstance, τ, ⟨ι u, huS⟩, j, hτ, ι.injective (hjι _), ?_, ?_⟩
  · show LinearMap.range ((Formalism.REAL.kSpan ε E u).subtype ∘ₗ e.symm.toLinearMap) = _
    rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), Submodule.range_subtype]
  · intro Y hY v v' hv'
    have hX : inG ε (Y.map star) := inG_conj hY.1
    have hsm : ∀ t : ℝ, inK ε ((t : ℂ) • Y) := by
      intro t
      obtain ⟨hg, hc⟩ := hY
      unfold inG at hg
      refine ⟨?_, ?_⟩
      · unfold inG
        rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
          Matrix.mul_smul, ← smul_add, hg, smul_zero]
      · rw [Matrix.smul_mul, Matrix.mul_smul, hc]
    have hpt : ∀ t : ℝ, ((τ (NormedSpace.exp ((t : ℂ) • Y)) v : S) : H) =
        σ (NormedSpace.exp ((t : ℂ) • Y.map star)) v := by
      intro t
      rw [hτσ _ (hexpK _ (hsm t)), exp_conj]
      congr 3
      ext a b
      simp
    have hd := hD (Y.map star) hX (j v)
    rw [hjι, ← hv', hjι] at hd
    rw [hasDerivAt_iff_isLittleO] at hd ⊢
    refine Asymptotics.isLittleO_norm_left.mp ?_
    refine (Asymptotics.isLittleO_norm_left.mpr hd).congr_left fun t => ?_
    rw [Submodule.coe_norm]
    simp only [Submodule.coe_sub, Submodule.coe_smul_of_tower, hpt]

end GlobalTheory.SphJet.LowTau
