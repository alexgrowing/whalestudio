import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReflectionTransposeEntriesMem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SignedCoordinateEqSignSmul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurableOfContinuousOnZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

section Inv

variable {A T : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype T]

theorem aeval_mem' (𝒜 : StarSubalgebra ℂ A) {x : A} (hx : x ∈ 𝒜) (p : Polynomial ℂ) :
    Polynomial.aeval x p ∈ 𝒜 := by
  refine Polynomial.induction_on p (fun a => ?_) (fun p q hp hq => ?_) (fun n a _ => ?_)
  · rw [Polynomial.aeval_C]; exact 𝒜.algebraMap_mem a
  · rw [map_add]; exact 𝒜.add_mem hp hq
  · rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    exact 𝒜.mul_mem (𝒜.algebraMap_mem a) (𝒜.pow_mem hx _)

theorem inv_mem_of_kappa (κ : (T → ℂ) →ₐ[ℂ] A) (𝒜 : StarSubalgebra ℂ A) (f : T → ℂ) (hf : κ f ∈ 𝒜) :
    κ (fun ρ => (f ρ)⁻¹) ∈ 𝒜 := by
  classical
  set N : Finset ℂ := Finset.univ.image f
  set p : Polynomial ℂ := Lagrange.interpolate N id (fun v => v⁻¹)
  have hp : ∀ ρ, p.eval (f ρ) = (f ρ)⁻¹ := by
    intro ρ
    have hmem : f ρ ∈ N := Finset.mem_image_of_mem _ (Finset.mem_univ ρ)
    have h := Lagrange.eval_interpolate_at_node (fun v : ℂ => v⁻¹) (Set.injOn_id _) hmem
    simpa only [id] using h
  have he : (fun ρ => (f ρ)⁻¹) = Polynomial.aeval f p := by
    funext ρ
    rw [← hp ρ]
    have := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℂ (fun _ : T => ℂ) ρ) f p
    rw [Pi.evalAlgHom_apply, Polynomial.coe_aeval_eq_eval] at this
    rw [this]
    rfl
  rw [he, ← Polynomial.aeval_algHom_apply]
  exact aeval_mem' 𝒜 hf p

variable {r : ℕ}

theorem x_eq_of_start (L : LevelData A r) (st : Start A) (hst : IsLevelStart L st) (Y : ℂ) :
    st.x Y = L.GGi * st.QQ Y 1 1 := by
  rw [hst.tau, ← mul_assoc, L.GGi_GG, one_mul]

theorem gens_of (𝒜 : StarSubalgebra ℂ A) (L : LevelData A r) (st : Start A) (hst : IsLevelStart L st)
    (κ : (T → ℂ) →ₐ[ℂ] A) (x0 : T → ℂ → ℂ) (hx : ∀ Y, st.x Y = κ fun ρ => x0 ρ Y)
    (hxi : ∀ Y ∈ st.inv, st.xi Y = κ fun ρ => (x0 ρ Y)⁻¹)
    (hz : ∀ g ∈ zfns L, g ∈ 𝒜) (hQ : ∀ Y : ℂ, star Y = Y → ∀ i j, st.QQ Y i j ∈ 𝒜) : Gens 𝒜 L st := by
  have hxm : ∀ Y : ℂ, star Y = Y → st.x Y ∈ 𝒜 := fun Y hY => by
    rw [x_eq_of_start L st hst Y]
    exact 𝒜.mul_mem (hz _ (by simp [zfns])) (hQ Y hY 1 1)
  refine ⟨hz, hQ, hxm, fun Y hYs hY => ?_⟩
  rw [hxi Y hYs]
  exact inv_mem_of_kappa κ 𝒜 (fun ρ => x0 ρ Y) (by rw [← hx Y]; exact hxm Y hY)

end Inv

section Fn

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem fnVal_conj (j : Fin 6) (g : Mx k r) : conj (fnVal k r z z' (fnConj j) g) = fnVal k r z z' j g := by
  fin_cases j <;> simp [fnVal, fnConj, map_inv₀]

theorem fn_adj (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) (U : Submodule ℂ (RadSp k r z z' π π'))
    (hU : IntOn μ U) (hfn : ∀ j, ∀ Φ ∈ U, X.fn j Φ ∈ U) (j : Fin 6) :
    mkP (X.fn j) (X.fn (fnConj j)) ∈ adjAlg μ U hU := by
  refine ⟨fun Φ hΦ => hfn j Φ hΦ, fun Φ hΦ => hfn _ Φ hΦ, fun c _ Φ _ Ψ _ => ?_⟩
  show pairAt μ (X.fn j Φ) Ψ c = pairAt μ Φ (X.fn (fnConj j) Ψ) c
  unfold pairAt
  congr 1
  funext g
  by_cases hx : (c, Matrix.of g) ∈ DomR k r z z'
  · have e1 := X.fn_apply j Φ (c, Matrix.of g) hx
    have e2 := X.fn_apply (fnConj j) Ψ (c, Matrix.of g) hx
    simp only at e1 e2
    rw [e1, e2, hsInner_smul_left', hsInner_smul_right', fnVal_conj]
  · have h0 : (Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g) = 0 := radSp_zero_off Φ hx
    have h1 : (X.fn j Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g) = 0 := radSp_zero_off (X.fn j Φ) hx
    rw [h0, h1, hsInner_zero_left, hsInner_zero_left]

end Fn

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem adjTop_of_tAdj (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0)
    (U : Submodule ℂ (RadSp P.k P.r z z' π π')) (hU : IntOn μ U) (hK : K (Fin.last P.r) ≤ U)
    (hfn : ∀ j, ∀ Φ ∈ U, X.fn j Φ ∈ U)
    (hT : ∀ Y : ℂ, star Y = Y → ∀ a b, X.QQ Y a b ∈ adjAlg μ U hU) :
    AdjTop (S := S) P z z' π π' μ L st K l0 := by
  have hD' := hD
  obtain ⟨κ, hx, hxi, -⟩ :=
    xKappaOfNF Formalism.FourierDecayAlt.P.normal_form_actual kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD
  obtain ⟨-, -, hAL, hQQ, -, -, -, hst⟩ := hD
  obtain ⟨-, -, -, -, -, -, hζ, hζi, hζb, hζbi, hGG, hGGi, -⟩ := hAL
  have hz : ∀ g ∈ zfns L, g ∈ adjAlg μ U hU := by
    intro g hg
    simp only [zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hζ]; exact fn_adj X μ U hU hfn 0
    · rw [hζi]; exact fn_adj X μ U hU hfn 1
    · rw [hζb]; exact fn_adj X μ U hU hfn 2
    · rw [hζbi]; exact fn_adj X μ U hU hfn 3
    · rw [hGG]; exact fn_adj X μ U hU hfn 4
    · rw [hGGi]; exact fn_adj X μ U hU hfn 5
  have hQ : ∀ Y : ℂ, star Y = Y → ∀ i j, st.QQ Y i j ∈ adjAlg μ U hU := by
    intro Y hY i j
    rw [hQQ Y, Matrix.smul_apply]
    exact (adjAlg μ U hU).smul_mem (hT Y hY i j) _
  exact adjTop_of_gens P z z' π π' X μ L st K l0 hD' U hU hK
    (gens_of _ L st hst κ _ hx hxi hz hQ)

end Top

end Formalism.FourierDecayAlt.P5.HerA
