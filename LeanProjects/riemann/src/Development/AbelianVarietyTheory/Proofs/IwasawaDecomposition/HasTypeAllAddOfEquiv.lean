import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.IsTypeAtCentral
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.BlattnerShiftsSignedParameters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeTransport

noncomputable section

namespace GlobalTheory.TypeSum

section Model

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace Topology

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx n → (H →L[ℂ] H)}

def IsExpnAll (Lie Gs : Set (Mx n)) (σ : Mx n → (H →L[ℂ] H)) (S : List (List (Mx n))) (v : ℕ → H)
    (ℓ : ℕ → (H →ₗ[ℂ] ℂ)) (C : ℕ → ℝ) (f : Mx n → ℂ) : Prop :=
  IsExpn Lie Gs σ S v ℓ C f ∧ ∀ S', Words Lie S' → Summable (fun i => C i * sobNorm σ S' (v i))

def HasTypeAll (Lie Gs : Set (Mx n)) (σ : Mx n → (H →L[ℂ] H)) (f : Mx n → ℂ) : Prop :=
  ∃ S, Words Lie S ∧ Ctrl Lie Gs σ S ∧ ∃ v ℓ C, IsExpnAll Lie Gs σ S v ℓ C f

theorem hasTypeAll_iff {Lie Gs : Set (Mx n)} {f : Mx n → ℂ} : HasTypeAll Lie Gs σ f ↔
    ∃ v : ℕ → H, (∀ i, SmoothVec Lie σ (v i)) ∧ ∃ ℓ : ℕ → (H →ₗ[ℂ] ℂ), (∀ i, Sobolev₂ Lie σ (ℓ i)) ∧
      (∃ (S : List (List (Mx n))) (C : ℕ → ℝ), (∀ l ∈ S, ∀ X ∈ l, X ∈ Lie) ∧
        (∀ i w, SmoothVec Lie σ w → ‖ℓ i w‖ ≤ C i * (S.map fun l => ‖l.foldr (dRep σ) w‖).sum) ∧
        (∀ S' : List (List (Mx n)), (∀ l ∈ S', ∀ X ∈ l, X ∈ Lie) →
          Summable (fun i => C i * (S'.map fun l => ‖l.foldr (dRep σ) (v i)‖).sum)) ∧
        (∃ B : Mx n → ℝ, Continuous B ∧ ∀ g ∈ Gs, ∀ w, SmoothVec Lie σ w →
          (S.map fun l => ‖l.foldr (dRep σ) (σ g w)‖).sum ≤ B g * (S.map fun l => ‖l.foldr (dRep σ) w‖).sum)) ∧
      ∀ g ∈ Gs, HasSum (fun i => ℓ i (σ g (v i))) (f g) := by
  constructor
  · rintro ⟨S, hS, hc, v, ℓ, C, e, eS⟩
    exact ⟨v, e.1, ℓ, e.sobCont hS, ⟨S, C, hS, e.2.2.1, eS, hc⟩, e.2.2.2.2⟩
  · rintro ⟨v, h1, ℓ, -, ⟨S, C, hS, h2, h3, hc⟩, h4⟩
    have hab : ∀ S', Words Lie S' → Summable (fun i => |C i| * sobNorm σ S' (v i)) := fun S' hS' =>
      (h3 S' hS').abs.congr fun i => by
        rw [abs_mul]
        exact congrArg _ (abs_of_nonneg (sobNorm_nonneg σ S' (v i)))
    refine ⟨S, hS, hc, v, ℓ, fun i => |C i|, ⟨h1, fun _ => abs_nonneg _, fun i w hw => (h2 i w hw).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (sobNorm_nonneg σ S w)), hab S hS, h4⟩, hab⟩

theorem HasTypeAll.add {Lie Gs : Set (Mx n)} {f f' : Mx n → ℂ} (h : HasTypeAll Lie Gs σ f)
    (h' : HasTypeAll Lie Gs σ f') : HasTypeAll Lie Gs σ fun g => f g + f' g := by
  obtain ⟨S₀, hS₀, ⟨B₀, hB₀, hc₀⟩, v, ℓ, C, ⟨a1, a2, a3, -, a5⟩, a6⟩ := h
  obtain ⟨S₁, hS₁, ⟨B₁, hB₁, hc₁⟩, v', ℓ', C', ⟨b1, b2, b3, -, b5⟩, b6⟩ := h'
  have e1 : ∀ k : ℕ, 2 * k / 2 = k := fun k => by omega
  have e2 : ∀ k : ℕ, (2 * k + 1) / 2 = k := fun k => by omega
  have e3 : ∀ k : ℕ, 2 * k % 2 = 0 := fun k => by omega
  have e4 : ∀ k : ℕ, ¬ (2 * k + 1) % 2 = 0 := fun k => by omega
  have hS := words_append hS₀ hS₁
  have sumAll : ∀ S', Words Lie S' → Summable (fun i => (if i % 2 = 0 then C (i / 2) else C' (i / 2)) *
      sobNorm σ S' (if i % 2 = 0 then v (i / 2) else v' (i / 2))) := fun S' hS' => by
    refine Summable.even_add_odd ?_ ?_
    · simpa only [e1, e3, if_true] using a6 S' hS'
    · simpa only [e2, e4, if_false] using b6 S' hS'
  refine ⟨S₀ ++ S₁, hS, ⟨fun g => |B₀ g| + |B₁ g|, (continuous_abs.comp hB₀).add (continuous_abs.comp hB₁),
    fun g hg w hw => ?_⟩, fun i => if i % 2 = 0 then v (i / 2) else v' (i / 2),
    fun i => if i % 2 = 0 then ℓ (i / 2) else ℓ' (i / 2), fun i => if i % 2 = 0 then C (i / 2) else C' (i / 2),
    ⟨fun i => ?_, fun i => ?_, fun i w hw => ?_, sumAll _ hS, fun g hg => ?_⟩, sumAll⟩
  · rw [sobNorm_append, sobNorm_append]
    have p0 := sobNorm_nonneg σ S₀ w
    have p1 := sobNorm_nonneg σ S₁ w
    have q0 := hc₀ g hg w hw
    have q1 := hc₁ g hg w hw
    have r0 : B₀ g * sobNorm σ S₀ w ≤ |B₀ g| * sobNorm σ S₀ w := mul_le_mul_of_nonneg_right (le_abs_self _) p0
    have r1 : B₁ g * sobNorm σ S₁ w ≤ |B₁ g| * sobNorm σ S₁ w := mul_le_mul_of_nonneg_right (le_abs_self _) p1
    have s0 := abs_nonneg (B₀ g)
    have s1 := abs_nonneg (B₁ g)
    nlinarith [mul_nonneg s0 p1, mul_nonneg s1 p0]
  · beta_reduce; split_ifs
    exacts [a1 _, b1 _]
  · beta_reduce; split_ifs
    exacts [a2 _, b2 _]
  · beta_reduce
    rw [sobNorm_append]
    have p0 := sobNorm_nonneg σ S₀ w
    have p1 := sobNorm_nonneg σ S₁ w
    split_ifs
    · exact (a3 _ w hw).trans (mul_le_mul_of_nonneg_left (by linarith) (a2 _))
    · exact (b3 _ w hw).trans (mul_le_mul_of_nonneg_left (by linarith) (b2 _))
  · refine HasSum.even_add_odd ?_ ?_
    · simpa only [e1, e3, if_true] using a5 g hg
    · simpa only [e2, e4, if_false] using b5 g hg

open GlobalTheory.TypeSum.Transport in

theorem hasTypeAll_transport : ∀ (n : ℕ) (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ₁ : Mx n → (H →L[ℂ] H)) (σ₂ : Mx n → (H' →L[ℂ] H')) (G₁ G₂ Q : Mx n), IsUnit G₁ → IsUnit Q → Qᴴ * G₂ * Q = G₁ → ∀ U : H ≃ₗᵢ[ℂ] H', (∀ g ∈ Formalism.QuantumDeterminants.UH G₁, ∀ v, U (σ₁ g v) = σ₂ (Q * g * Q⁻¹) (U v)) → ∀ f : Mx n → ℂ, HasTypeAll (lieOf G₁) (Formalism.QuantumDeterminants.UH G₁) σ₁ f → HasTypeAll (lieOf G₂) (Formalism.QuantumDeterminants.UH G₂) σ₂ (fun y => f (Q⁻¹ * y * Q)) := by
  intro n H H' _ _ _ _ σ₁ σ₂ G₁ G₂ Q hG hQ hGG U hU f hf
  have h1 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hQ)
  have h2 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hQ)
  have hGG' : (Q⁻¹)ᴴ * G₁ * Q⁻¹ = G₂ := by
    rw [← hGG]
    calc (Q⁻¹)ᴴ * (Qᴴ * G₂ * Q) * Q⁻¹ = (Q * Q⁻¹)ᴴ * G₂ * (Q * Q⁻¹) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h2]; simp
  have cd : ∀ Y : Mx n, Q * (Q⁻¹ * Y * Q) * Q⁻¹ = Y := fun Y => by
    calc Q * (Q⁻¹ * Y * Q) * Q⁻¹ = (Q * Q⁻¹) * Y * (Q * Q⁻¹) := by simp only [Matrix.mul_assoc]
      _ = Y := by rw [h2]; simp
  let Ur : H ≃L[ℝ] H' :=
    { U.toLinearEquiv.restrictScalars ℝ with
      continuous_toFun := U.continuous
      continuous_invFun := U.symm.continuous }
  have hUr : ∀ x, Ur x = U x := fun _ => rfl
  have key : ∀ (k : ℕ) (Xs : Fin k → Mx n), (∀ i, Xs i ∈ lieOf G₁) → ∀ w : H,
      (fun t : Fin k → ℝ => σ₂ (List.ofFn fun i => NormedSpace.exp (t i • (Q * Xs i * Q⁻¹))).prod (U w)) =
        Ur ∘ fun t : Fin k → ℝ => σ₁ (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod w := by
    intro k Xs hX w
    funext t
    have hm : (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ Formalism.QuantumDeterminants.UH G₁ :=
      GlobalTheory.GardingVec.list_prod_mem _ (by
        intro g hg
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
        exact GlobalTheory.GardingVec.exp_mem hG (hX i) _)
    rw [Function.comp_apply, hUr, hU _ hm, ← prod_conj h1 h2, List.map_ofFn]
    simp only [exp_smul_conj hQ, Function.comp_def]
  have smF : ∀ w, SmoothVec (lieOf G₁) σ₁ w → SmoothVec (lieOf G₂) σ₂ (U w) := by
    intro w hw k Ys hY
    have hX : ∀ i, Q⁻¹ * Ys i * Q ∈ lieOf G₁ := fun i => conj_lie h2 hGG (hY i)
    have := key k _ hX w
    simp only [cd] at this
    rw [this]
    exact Ur.contDiff.comp (hw k _ hX)
  have smB : ∀ w, SmoothVec (lieOf G₂) σ₂ (U w) → SmoothVec (lieOf G₁) σ₁ w := by
    intro w hw k Xs hX
    have := hw k _ fun i => conj_lie h1 hGG' (hX i)
    rw [key k Xs hX w] at this
    exact Ur.comp_contDiff_iff.1 this
  have hd : ∀ X ∈ lieOf G₁, ∀ w, dRep σ₂ (Q * X * Q⁻¹) (U w) = U (dRep σ₁ X w) := by
    intro X hX w
    have e : (fun t : ℝ => σ₂ (NormedSpace.exp (t • (Q * X * Q⁻¹))) (U w)) =
        Ur ∘ fun t : ℝ => σ₁ (NormedSpace.exp (t • X)) w := by
      funext t
      rw [Function.comp_apply, hUr, hU _ (GlobalTheory.GardingVec.exp_mem hG hX t), exp_smul_conj hQ]
    unfold dRep
    rw [e, deriv, deriv, Ur.comp_fderiv]
    rfl
  have hw : ∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieOf G₁) → ∀ w,
      (l.map fun X => Q * X * Q⁻¹).foldr (dRep σ₂) (U w) = U (l.foldr (dRep σ₁) w) := by
    intro l hl w
    induction l with
    | nil => rfl
    | cons X l ih =>
      rw [List.map_cons, List.foldr_cons, List.foldr_cons, ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY),
        hd X (hl X List.mem_cons_self)]
  have hsT : ∀ T : List (List (Mx n)), Words (lieOf G₁) T → ∀ w,
      sobNorm σ₂ (T.map fun l => l.map fun X => Q * X * Q⁻¹) (U w) = sobNorm σ₁ T w := by
    intro T hT w
    unfold sobNorm
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun l hl => ?_
    simp only [Function.comp_apply]
    rw [hw l (hT l hl), U.norm_map]
  obtain ⟨S, hS, ⟨B, hB, hBc⟩, v, ℓ, C, ⟨e1, e2, e3, e4, e5⟩, e6⟩ := hf
  have hs := hsT S hS
  have hσ : ∀ g ∈ Formalism.QuantumDeterminants.UH G₂, ∀ w, σ₂ g (U w) = U (σ₁ (Q⁻¹ * g * Q) w) := fun g hg w => by
    rw [hU _ (conj_UH h2 hGG hg), cd]
  refine ⟨S.map fun l => l.map fun X => Q * X * Q⁻¹, ?_, ⟨fun y => B (Q⁻¹ * y * Q), hB.comp (by fun_prop), ?_⟩,
    fun i => U (v i), fun i => ℓ i ∘ₗ (U.symm.toLinearEquiv : H' →ₗ[ℂ] H), C, ⟨fun i => smF _ (e1 i), e2, ?_, ?_, ?_⟩,
    ?_⟩
  · intro l hl X hX
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact conj_lie h1 hGG' (hS l' hl' Y hY)
  · intro g hg w hw'
    obtain ⟨w, rfl⟩ := U.surjective w
    rw [hσ g hg, hs, hs]
    exact hBc _ (conj_UH h2 hGG hg) w (smB w hw')
  · intro i w hw'
    obtain ⟨w, rfl⟩ := U.surjective w
    rw [hs]
    simpa using e3 i w (smB w hw')
  · simpa only [hs] using e4
  · intro g hg
    simpa [hσ g hg] using e5 _ (conj_UH h2 hGG hg)
  · intro S' hS'
    have hT : Words (lieOf G₁) (S'.map fun l => l.map fun X => Q⁻¹ * X * Q) := by
      intro l hl X hX
      obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      exact conj_lie h2 hGG (hS' l' hl' Y hY)
    have eS : ((S'.map fun l => l.map fun X => Q⁻¹ * X * Q).map fun l => l.map fun X => Q * X * Q⁻¹) = S' := by
      simp [List.map_map, Function.comp_def, cd]
    have := e6 _ hT
    refine this.congr fun i => ?_
    rw [← hsT _ hT, eS]

def opEquiv {ε : Fin n → Bool} (hσ : IsURepOn (UJset ε) σ) {g : Mx n} (hg : g ∈ UJset ε) : H ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective ⟨(σ g : H →ₗ[ℂ] H), hσ.2.1 g hg⟩ fun w => ⟨σ g⁻¹ w, by
    show σ g (σ g⁻¹ w) = w
    rw [← sigma_mul hσ hg (inv_mem_UJ hg), mul_inv_UJ hg, sigma_one hσ]⟩

theorem hasTypeAll_add_of_equiv {H' : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    {σ' : Mx n → (H' →L[ℂ] H')} {ε : Fin n → Bool} (hσ : IsURepOn (UJset ε) σ)
    (U : H' ≃ₗᵢ[ℂ] H) (hU : ∀ g ∈ UJset ε, ∀ v, U (σ' g v) = σ g (U v)) {P P' G : Mx n} (hP : IsUnit P)
    (hP' : IsUnit P') (hG : Pᴴ * Jm ε * P = G) (hG' : P'ᴴ * Jm ε * P' = G) {f f' : Mx n → ℂ}
    (h : HasTypeAll (lieOf G) (Formalism.QuantumDeterminants.UH G) (fun g => σ (P * g * P⁻¹)) f)
    (h' : HasTypeAll (lieOf G) (Formalism.QuantumDeterminants.UH G) (fun g => σ' (P' * g * P'⁻¹)) f') :
    HasTypeAll (lieOf G) (Formalism.QuantumDeterminants.UH G) (fun g => σ (P * g * P⁻¹)) fun g => f g + f' g := by
  have hGu := isUnit_gram hP hG
  have hd := (isUnit_iff_isUnit_det _).1 hP
  have hd' := (isUnit_iff_isUnit_det _).1 hP'
  have a1 := Matrix.mul_nonsing_inv _ hd
  have a2 := Matrix.nonsing_inv_mul _ hd
  have a3 := Matrix.mul_nonsing_inv _ hd'
  have a4 := Matrix.nonsing_inv_mul _ hd'
  have hm : P * P'⁻¹ ∈ UJset ε := by
    show (P * P'⁻¹)ᴴ * Jm ε * (P * P'⁻¹) = Jm ε
    calc _ = (P'⁻¹)ᴴ * (Pᴴ * Jm ε * P) * P'⁻¹ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (P' * P'⁻¹)ᴴ * Jm ε * (P' * P'⁻¹) := by
          rw [hG, ← hG']; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [a3]; simp
  have t1 := hasTypeAll_transport n H H _ σ G (Jm ε) P hGu hP hG (LinearIsometryEquiv.refl ℂ H) (fun _ _ _ => rfl) f h
  have t2 := hasTypeAll_transport n H' H _ σ G (Jm ε) P hGu hP hG (U.trans (opEquiv hσ hm)) (fun g hg v => by
    have m1 := GlobalTheory.GardingVec.conj_mem hP hG hg
    have m2 := GlobalTheory.GardingVec.conj_mem hP' hG' hg
    show σ (P * P'⁻¹) (U (σ' (P' * g * P'⁻¹) v)) = σ (P * g * P⁻¹) (σ (P * P'⁻¹) (U v))
    rw [hU _ m2, ← sigma_mul hσ hm m2, ← sigma_mul hσ m1 hm]
    congr 2
    calc P * P'⁻¹ * (P' * g * P'⁻¹) = P * (P'⁻¹ * P') * g * P'⁻¹ := by simp only [Matrix.mul_assoc]
      _ = P * g * (P⁻¹ * P) * P'⁻¹ := by rw [a2, a4, mul_one, mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]) f' h'
  have s := t1.add t2
  have hi : P⁻¹⁻¹ = P := Matrix.nonsing_inv_nonsing_inv _ hd
  have t3 := hasTypeAll_transport n H H σ (fun g => σ (P * g * P⁻¹)) (Jm ε) G P⁻¹ (isUnit_Jm ε)
    (IsUnit.of_mul_eq_one _ a2) (by
      rw [← hG]
      calc _ = (P * P⁻¹)ᴴ * Jm ε * (P * P⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [a1]; simp) (LinearIsometryEquiv.refl ℂ H) (fun g _ v => by
      rw [hi, conj_conj hP]; rfl) _ s
  have e : ∀ g : Mx n, P⁻¹ * (P⁻¹⁻¹ * g * P⁻¹) * P = g := fun g => by
    rw [hi]
    calc _ = (P⁻¹ * P) * g * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [a2, one_mul, mul_one]
  simpa only [e] using t3

end Model

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.TypeSum

end
