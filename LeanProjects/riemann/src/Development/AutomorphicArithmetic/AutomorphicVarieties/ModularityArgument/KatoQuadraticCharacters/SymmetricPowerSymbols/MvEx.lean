import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.KumLagr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.KumUn
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ComapLtOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.DifB

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

private theorem isKum_one_of_vanish_on_inD {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}
    (X : Tower Ω ε) (m : ℕ) (hm : 0 < m) (φ : RingAut (Kb X) → ZMod m)
    (hφ : ∀ h, InD X h → φ h = 0) : IsKum X m φ 1 := by
  refine ⟨1, by simp, fun h hh => ?_⟩
  rw [hφ h hh]
  show lg X m (h 1) 1 = 0
  rw [map_one]
  exact (lgB Ω ε X m hm).2.2.1 1 1 0 one_ne_zero (by simp)

private theorem pt_mv_mul_eq_mv_mv_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} {X : Tower Ω ε} {m : ℕ}
    (σ ρ : RingAut (Kb X)) (χ : ZMod m) (P : Pt X m) :
    Pt.mv (σ * ρ) χ P = Pt.mv σ χ (Pt.mv ρ 1 P) := by
  simp only [Pt.mv, one_pow, one_mul, Pt.mk.injEq]
  refine ⟨rfl, rfl, ?_⟩
  funext h
  simp only [mul_inv_rev, mul_assoc]

theorem UpperTheory.V.Z.Kato.Sym.mvEx :
    UpperTheory.V.Z.Kato.Sym.MvEx := by
  intro Ω _ _ _ ε X m hm τ s hadm u v P hP
  obtain ⟨-, -, hrefl, -, -, -, hlift, -⟩ := admB Ω ε X
  have hD := difB Ω ε X m hm
  have hK := kum Ω ε X m hm
  have hKU := kumUn Ω ε X m hm
  have hMv := mvPt Ω ε X m hm
  have hcyc1 : cyc m (1 : Gal(Ω/ℚ)) = 1 := ((lgB Ω ε X m hm).2.2.2.2.2.2 1 1).2.1
  have hInv : ∀ (g : RingAut (Kb X)) (x : Kb X), g⁻¹ (g x) = x := by
    intro g x
    show (g⁻¹ * g) x = x
    rw [inv_mul_cancel]
    rfl
  obtain ⟨σ, hσ⟩ := hlift τ
  have hP' : IsPt X m (τ u) (τ v) (Pt.mv σ (cyc m s) P) := hMv τ s hadm σ hσ u v P hP
  have hInD1 : InD X 1 := fun f => rfl
  have hLift1 : Lifts X 1 (RingEquiv.refl X.K) := fun f => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨hadd, hlc, hunr, -⟩ := hD (τ u) (τ v) _ Q hP' hQ
    obtain ⟨f, hf⟩ := hK.1 _ hadd hlc
    exact ⟨f, hKU _ f hf hunr, σ, hσ, hf⟩
  · refine ⟨_, hP', σ, hσ, isKum_one_of_vanish_on_inD X m hm _ ?_⟩
    intro h hh
    exact (hD (τ u) (τ v) _ _ hP' hP').2.2.2.2.1 h hh
  · refine ⟨1, hLift1, isKum_one_of_vanish_on_inD X m hm _ ?_⟩
    intro h hh
    rw [hcyc1]
    exact (hD u v _ _ hP hP).2.2.2.2.2.1 1 hInD1 h hh
  · intro Q hQ f f' hf
    obtain ⟨σ₀, hσ₀, hf₀⟩ := hf
    constructor
    · rintro ⟨σ₁, hσ₁, hf₁⟩
      refine (hK.2 _ _ f f' hf₀ ?_).mp hf₁
      intro h hh
      have hρ : InD X (σ₀⁻¹ * σ₁) := fun f => by
        show σ₀⁻¹ (σ₁ (io X f)) = io X f
        rw [hσ₁ f, ← hσ₀ f, hInv]
      have hP1 : IsPt X m u v (Pt.mv (σ₀⁻¹ * σ₁) 1 P) := by
        have := hMv (RingEquiv.refl X.K) 1 hrefl (σ₀⁻¹ * σ₁) (fun f => hρ f) u v P hP
        rw [hcyc1] at this
        exact this
      have hconj : InD X (σ₀⁻¹ * h * σ₀) := fun f => by
        show σ₀⁻¹ (h (σ₀ (io X f))) = io X f
        rw [hσ₀ f, hh (τ f), ← hσ₀ f, hInv]
      have hA : IsPt X m (τ u) (τ v) (Pt.mv σ₁ (cyc m s) P) := hMv τ s hadm σ₁ hσ₁ u v P hP
      have hB : IsPt X m (τ u) (τ v) (Pt.mv σ₀ (cyc m s) P) := hMv τ s hadm σ₀ hσ₀ u v P hP
      have hsplit := (hD (τ u) (τ v) _ _ hA hB).2.2.2.1 Q hQ h hh
      have hzero : dif X (Pt.mv σ₁ (cyc m s) P) (Pt.mv σ₀ (cyc m s) P) h = 0 := by
        rw [show σ₁ = σ₀ * (σ₀⁻¹ * σ₁) from (mul_inv_cancel_left σ₀ σ₁).symm, pt_mv_mul_eq_mv_mv_one]
        rw [(hD u v _ P hP1 hP).2.2.2.2.2.2 τ s hadm σ₀ hσ₀ h hh,
          (hD u v P P hP hP).2.2.2.2.2.1 _ hρ _ hconj, mul_zero]
      rw [hsplit, hzero, zero_add]
    · intro hc
      exact ⟨σ₀, hσ₀, (hK.2 _ _ f f' hf₀ (fun _ _ => rfl)).mpr hc⟩
