import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AtPlaceIffEqAtTau

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdTh.RealCoord

section Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def perL (X : Data E r) (x : Frame X.Ψ r) : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ × Fin r → ℂ) where
  toFun := perC X x
  map_add' u v := by
    funext p
    simp only [perC, Pi.add_apply]
    split_ifs
    · simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
    · rw [Matrix.mulVec_add, Pi.add_apply]
  map_smul' c u := by
    funext p
    simp only [perC, Pi.smul_apply, RingHom.id_apply]
    split_ifs
    · simp only [hermC, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    · rw [Matrix.mulVec_smul, Pi.smul_apply]

theorem hermC_col_mulVec (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) (a : Fin r)
    (c : Fin r → ℂ) : hermC τ G (FD.col x a) (x *ᵥ c) = ∑ b, FD.gram τ G x a b * conj (c b) := by
  simp only [hermC, FD.gram, FD.col, Matrix.of_apply, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum,
    Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem perL_injective (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) : Function.Injective (perL X x) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  funext τ
  have hd : (mat x τ).det ≠ 0 := (hx τ).1
  have hA : (X.gramPos x τ).det ≠ 0 := by
    have h := (hx τ).2 ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
    intro h0
    have e : dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ = (X.gramPos x τ).det := rfl
    rw [e, h0] at h
    simp at h
  set c : Fin r → ℂ := (mat x τ)⁻¹ *ᵥ u τ with hc
  have hu' : u τ = mat x τ *ᵥ c := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd), Matrix.one_mulVec]
  have h2 : ∀ a : Fin r, ¬ (a : ℕ) < X.p0 → c a = 0 := fun a ha => by
    have := congrFun hu (τ, a)
    change perC X x u (τ, a) = 0 at this
    simpa only [perC, if_neg ha] using this
  have h1 : X.gramPos x τ *ᵥ (fun b => conj (c (Fin.castLE X.p0_le b))) = 0 := by
    funext a
    have ha : ((Fin.castLE X.p0_le a : Fin r) : ℕ) < X.p0 := a.2
    have := congrFun hu (τ, Fin.castLE X.p0_le a)
    change perC X x u (τ, Fin.castLE X.p0_le a) = 0 at this
    simp only [perC, if_pos ha] at this
    rw [hu', hermC_col_mulVec] at this
    rw [Pi.zero_apply, ← this]
    simp only [Matrix.mulVec, dotProduct, Data.gramPos, Matrix.submatrix_apply]
    refine Fintype.sum_of_injective (Fin.castLE X.p0_le) (Fin.castLE_injective _) _ _ (fun b hb => ?_) fun _ => rfl
    rw [h2 b fun h => hb ⟨⟨b, h⟩, rfl⟩, map_zero, mul_zero]
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero hA h1
  have h4 : c = 0 := by
    funext a
    by_cases ha : (a : ℕ) < X.p0
    · have := congrFun h3 ⟨a, ha⟩
      simpa using this
    · exact h2 a ha
  rw [hu', h4, Matrix.mulVec_zero]
  rfl

theorem perL_bijective (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) : Function.Bijective (perL X x) := by
  refine ⟨perL_injective X hx, ?_⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 (perL_injective X hx)
  simp [Module.finrank_pi_fintype, mul_assoc]

end Lin

variable {D : D7}

theorem realM_tauE (θ : InfFam D) {m n : ℕ} (w : Mx D m n) (ρ : D.what₂.Tau) :
    realM θ w (tauE D ρ) = compAt θ ρ w := by
  have h : ∃ ρ', tauE D ρ = tauE D ρ' := ⟨ρ, rfl⟩
  rw [realM, dif_pos h, ← GlobalTheory.PointAtPlace.tauE_injective h.choose_spec]

theorem realM_add (θ : InfFam D) {m n : ℕ} (v w : Mx D m n) (τ : D.host.E →+* ℂ) :
    realM θ (v + w) τ = realM θ v τ + realM θ w τ := by
  unfold realM
  split_ifs with h
  · funext i j
    show θ _ (infPart D (v i j + w i j)) = θ _ (infPart D (v i j)) + θ _ (infPart D (w i j))
    rw [RingHom.map_add, RingHom.map_add]
  · rw [add_zero]

theorem continuous_realM {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.host.E →+* ℂ) (i : Fin m) (j : Fin n) :
    Continuous fun w : Mx D m n => realM θ w τ i j := by
  unfold realM
  split_ifs with h
  · exact (GlobalTheory.FockCompare.continuous_comp hθ _).comp ((continuous_apply j).comp (continuous_apply i))
  · exact continuous_const

theorem realM_lineAt {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (ρ : D.what₂.Tau) (u : Matrix (Fin m) (Fin n) ℂ)
    (t : ℝ) (τ : D.host.E →+* ℂ) : realM θ (lineAt θ ρ u t) τ = t • realM θ (lineAt θ ρ u 1) τ := by
  have hL : IsLineAt θ ρ u (lineAt θ ρ u) :=
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n ρ u)
  unfold realM
  split_ifs with h
  · rw [hL.2.2, hL.2.2]
    split_ifs
    · funext i j
      simp
    · rw [smul_zero]
  · rw [smul_zero]

theorem zOf_coordinates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r), (∀ (γ : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (v : WO V W), v.map (infPart D) = (ratW W V γ).map (infPart D) → zOf θ V W hr X idx x v = fun b => pv X idx x (colsR hr γ b)) ∧ (∀ v w : WO V W, zOf θ V W hr X idx x (v + w) = zOf θ V W hr X idx x v + zOf θ V W hr X idx x w) ∧ (∀ (τ : D.what₂.Tau) (u : Matrix (Fin W.rank) (Fin V.rank) ℂ) (t : ℝ), zOf θ V W hr X idx x (lineAt θ τ u t) = (t : ℂ) • zOf θ V W hr X idx x (lineAt θ τ u 1)) ∧ Continuous (zOf θ V W hr X idx x ) ∧ (x ∈ X.dom → ∃ p : (Fin V.rank → Fin g → ℂ) →+ WO V W, Continuous p ∧ (∀ z, (p z).map (finPart D) = 0 ∧ zOf θ V W hr X idx x (p z) = z) ∧ ∀ w : WO V W, w.map (finPart D) = 0 → p (zOf θ V W hr X idx x w) = w) := by
  intro D ψ θ V W r g hr X bas idx _ hθ _ _ hM _ x
  have hz : ∀ w b j, zOf θ V W hr X idx x w b j =
      perL X x (fun τ a => realM θ w τ.1 (Fin.cast hr.symm a) b) (idx j) := fun _ _ _ => rfl
  refine ⟨fun γ v hv => ?_, fun v w => ?_, fun ρ u t => ?_, ?_, fun hx => ?_⟩
  · funext b j
    show perC X x _ (idx j) = per X x _ (idx j)
    rw [← perC_emb]
    congr 1
    funext τ a
    obtain ⟨ρ, hρ⟩ := (hM.psi τ.1).1 τ.2
    have e : infPart D (v (Fin.cast hr.symm a) b) = infPart D (incA D (γ (Fin.cast hr.symm a) b)) :=
      congrFun (congrFun hv _) _
    show realM θ v τ.1 _ _ = τ.1 (γ (Fin.cast hr.symm a) b)
    rw [hρ, realM_tauE, ← GlobalTheory.FockCompare.comp_incA hθ, ← e]
    rfl
  · funext b j
    rw [Pi.add_apply, Pi.add_apply, hz, hz, hz, ← Pi.add_apply (perL X x _), ← map_add]
    refine congrFun (congrArg (perL X x) ?_) _
    funext τ a
    rw [realM_add]
    rfl
  · funext b j
    rw [Pi.smul_apply, Pi.smul_apply, hz, hz, Complex.coe_smul, ← Pi.smul_apply t (perL X x _), ← map_smul]
    refine congrFun (congrArg (perL X x) ?_) _
    funext τ a
    rw [realM_lineAt hθ]
    rfl
  · refine continuous_pi fun b => continuous_pi fun j => ?_
    simp only [hz]
    exact (continuous_apply (idx j)).comp ((perL X x).continuous_of_finiteDimensional.comp
      (continuous_pi fun τ => continuous_pi fun a => continuous_realM hθ τ.1 _ b))
  · obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
    let L := LinearEquiv.ofBijective (perL X x) (perL_bijective X hx)
    have hL : ∀ u, L u = perL X x u := fun _ => rfl
    let pl : D.what₂.Tau → X.Ψ := fun ρ => ⟨tauE D ρ, (hM.psi _).2 ⟨ρ, rfl⟩⟩
    let p : (Fin V.rank → Fin g → ℂ) →+ WO V W :=
      { toFun := fun z => Matrix.of fun i b => σ fun ρ => L.symm (fun q => z b (idx.symm q)) (pl ρ) (Fin.cast hr i)
        map_zero' := by
          funext i b
          have : (fun q => (0 : Fin V.rank → Fin g → ℂ) b (idx.symm q)) = 0 := rfl
          rw [Matrix.of_apply, this, map_zero]
          exact σ.map_zero
        map_add' := fun z z' => by
          funext i b
          have : (fun q => (z + z') b (idx.symm q)) = (fun q => z b (idx.symm q)) + fun q => z' b (idx.symm q) := rfl
          rw [Matrix.of_apply, this, map_add]
          exact σ.map_add _ _ }
    have hp : ∀ z i b, p z i b = σ fun ρ => L.symm (fun q => z b (idx.symm q)) (pl ρ) (Fin.cast hr i) :=
      fun _ _ _ => rfl
    refine ⟨p, ?_, fun z => ⟨?_, ?_⟩, fun w hw => ?_⟩
    · refine continuous_pi fun i => continuous_pi fun b => hσ.cont.comp (continuous_pi fun ρ => ?_)
      exact (continuous_apply (Fin.cast hr i)).comp ((continuous_apply (pl ρ)).comp
        (L.symm.toLinearMap.continuous_of_finiteDimensional.comp
          (continuous_pi fun q => (continuous_apply (idx.symm q)).comp (continuous_apply b))))
    · funext i b
      exact hσ.fin _
    · funext b j
      have e : (fun (τ : X.Ψ) a => realM θ (p z) τ.1 (Fin.cast hr.symm a) b) =
          L.symm (fun q => z b (idx.symm q)) := by
        funext τ a
        obtain ⟨ρ, hρ⟩ := (hM.psi τ.1).1 τ.2
        obtain rfl : τ = pl ρ := Subtype.ext hρ
        show realM θ (p z) (tauE D ρ) _ _ = _
        rw [realM_tauE]
        exact hσ.comp _ ρ
      rw [hz, e, ← hL, LinearEquiv.apply_symm_apply, Equiv.symm_apply_apply]
    · funext i b
      have e : (fun q => zOf θ V W hr X idx x w b (idx.symm q)) =
          L (fun τ a => realM θ w τ.1 (Fin.cast hr.symm a) b) := by
        funext q
        rw [hz, Equiv.apply_symm_apply, hL]
      rw [hp, e, LinearEquiv.symm_apply_apply]
      refine sub_eq_zero.1 (hσ.ext _ ?_ fun ρ => ?_)
      · have e1 : finPart D (w i b) = 0 := congrFun (congrFun hw i) b
        rw [RingHom.map_sub, hσ.fin, e1, sub_zero]
      · rw [RingHom.map_sub, RingHom.map_sub, hσ.comp, sub_eq_zero]
        show realM θ w (tauE D ρ) i b = _
        rw [realM_tauE]
        rfl

end GlobalTheory.AdTh.RealCoord

end
