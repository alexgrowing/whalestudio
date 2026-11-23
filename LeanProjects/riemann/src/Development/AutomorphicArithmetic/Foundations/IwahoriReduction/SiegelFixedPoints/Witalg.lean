import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueGalBEquivariant
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem gal_mul' {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (s t : Ω ≃ₐ[ℚ] Ω) (f : X.K) :
    X.gal (s * t) f = X.gal s (X.gal t f) := by
  apply X.exp.toRingHom.injective
  show X.exp _ = X.exp _
  ext r
  simp [X.gal_exp]

private theorem kmap_comp' {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (φ ψ χ : X.K ≃+* X.K) (h : ∀ f, χ f = φ (ψ f)) (a : X.Khat l) : X.kmap l χ a = X.kmap l φ (X.kmap l ψ a) := by
  unfold Tower.kmap
  have e : (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map χ.toMonoidHom))) =
      (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom))) ∘ₗ
        (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map ψ.toMonoidHom))) := by
    ext u
    exact h _
  show AdicCompletion.map (idl l) _ a = AdicCompletion.map (idl l) _ (AdicCompletion.map (idl l) _ a)
  rw [AdicCompletion.map_comp_apply, ← LinearMap.baseChange_comp, e]

theorem UpperTheory.Kd.L.witalg :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N n : ℕ), 1 ≤ N → (∀ (b b' : X.Fn l) (f f' : X.Kˣ), IsWit X N l n b f → IsWit X N l n b' f' → IsWit X N l n (b + b') (f * f')) ∧ IsWit X N l n 0 1 ∧ (∀ (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) (f : X.Kˣ), IsWit X N l n b f → IsWit X N l n (X.galB l s b) (Units.map (X.gal s).toMonoidHom f)) ∧ ∀ s t : Ω ≃ₐ[ℚ] Ω, ∀ b : X.Fn l, X.galB l (s * t) b = X.galB l s (X.galB l t b) := by
  intro Ω _ _ _ _ ε X l _ N n _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl : 0 < l := (Fact.out : l.Prime).pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro b b' f f' ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
    refine ⟨fun γ hγ => ?_, ?_, fun δ a c => ?_⟩
    · rw [Units.val_mul, map_mul, h1 γ hγ, k1 γ hγ]
    · rw [Pi.add_apply, map_add, h2, k2]
      unfold Tower.cls
      rw [← Submodule.Quotient.mk_add, ← TensorProduct.tmul_add, ofMul_mul]
    · obtain ⟨g, hg, e⟩ := h3 δ a c
      obtain ⟨g', hg', e'⟩ := k3 δ a c
      refine ⟨g * g', fun γ hγ => by rw [map_mul, hg γ hγ, hg' γ hγ], ?_⟩
      rw [Units.val_mul, map_mul, mul_pow, ← e, ← e']
      ring
  · refine ⟨fun γ _ => by simp, ?_, fun δ _ _ => ⟨1, fun γ _ => by simp, by simp⟩⟩
    simp [Tower.cls]
  · rintro s b f ⟨hfI, hcls, hδ⟩
    have hf : ((Units.map (X.gal s).toMonoidHom f : X.Kˣ) : X.K) = X.gal s f := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hf]; exact GlobalTheory.ThGal.inv_gal X s _ _ hfI
    · have hu : (![(![1, 0] : Fin 2 → ℤ_[l]) 0,
          (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (![1, 0] : Fin 2 → ℤ_[l]) 1] : Fin 2 → ℤ_[l]) = ![1, 0] := by
        funext i; fin_cases i <;> simp
      have hg : X.galB l s b ![1, 0] = X.kmap l (X.gal s) (b ![(![1, 0] : Fin 2 → ℤ_[l]) 0,
          (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (![1, 0] : Fin 2 → ℤ_[l]) 1]) := rfl
      rw [hu] at hg
      rw [AdicCompletion.eval_apply] at hcls
      rw [hg, AdicCompletion.eval_apply, Tower.kmap]
      erw [AdicCompletion.map_val_apply]
      rw [hcls]
      simp [Tower.cls, LinearMap.reduceModIdeal_apply]
    · intro δ hδ1 hδ2
      obtain ⟨δ', h1, h2, hrec⟩ := GlobalTheory.ThGal.exists_twist X s N l n hl f hfI δ hδ1 hδ2
      obtain ⟨g, hg, hfg⟩ := hδ δ' h1 h2
      refine ⟨X.gal s g, GlobalTheory.ThGal.inv_gal X s _ _ hg, ?_⟩
      rw [hf, ← hrec, ← map_mul, hfg, map_pow]
  · intro s t b
    funext u
    show X.kmap l (X.gal (s * t)) (b ![u 0, (cyclotomicCharacter Ω l (s * t).toRingEquiv : ℤ_[l]) * u 1]) =
      X.kmap l (X.gal s) (X.kmap l (X.gal t) (b ![u 0, (cyclotomicCharacter Ω l t.toRingEquiv : ℤ_[l]) *
        ((cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * u 1)]))
    have hm : (s * t).toRingEquiv = s.toRingEquiv * t.toRingEquiv := rfl
    rw [kmap_comp' X l _ _ _ (gal_mul' X s t), hm, map_mul, Units.val_mul, mul_left_comm, mul_assoc]
