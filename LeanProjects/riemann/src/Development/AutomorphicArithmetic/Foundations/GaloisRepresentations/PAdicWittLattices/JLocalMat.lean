import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CoverLowOfCov

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

private theorem isMatF_of_isMat {k : Type} [Field k] {l : ℕ} [Fact l.Prime] (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω]
    (θ : H.Γ → Formalism.ConjugateSelfDual.Qbar l) {d : ℕ} (ρ₁ : (Ω ≃ₐ[k] Ω) →* Matrix.GeneralLinearGroup (Fin d) (Formalism.ConjugateSelfDual.Qbar l))
    (h : UpperTheory.Gal.Int.Geo.IsMat l H Ω (Formalism.ConjugateSelfDual.Qbar l) θ ρ₁)
    (f : (Ω ≃ₐ[k] Ω) → Matrix (Fin d) (Fin d) (Formalism.ConjugateSelfDual.Qbar l)) (hf : ∀ σ, (ρ₁ σ).val = f σ) :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.IsMatF H Ω θ f := by
  obtain ⟨b, hb⟩ := h
  refine ⟨b, fun σ j => ?_⟩
  rw [hb σ j, hf σ]

theorem UpperTheory.Gal.G3.jLocalMat :
    UpperTheory.Gal.Seam.NiceBc → UpperTheory.Gal.Seam.HopEx → UpperTheory.Gal.Seam.LocTower → PositivityTheory.AutomorphicGaloisHodgeTate.G8.LocalMat := by
  intro hNice hHop hLoc E Ω _ _ _ _ _ l _ H θ hN Gw O _ _ _ Bw τK hτ
  refine ⟨fun g => ⟨_, hHop l _ _ (UpperTheory.Gal.Int.Geo.bcAlong H τK) (hNice _ _ τK H hN) g⟩, ?_⟩
  intro d ρ hρ
  obtain ⟨ρ₁, hρ₁, hc⟩ := hLoc l E _ Ω (Formalism.ConjugateSelfDual.Qbar l) τK Bw.j (fun x => (hτ x).symm) H hN
    (Formalism.ConjugateSelfDual.Qbar l) θ d ρ hρ
  refine isMatF_of_isMat (UpperTheory.Gal.Int.Geo.bcAlong H τK) (Formalism.ConjugateSelfDual.Qbar l) θ ρ₁ hρ₁ _
    (fun σ => congrArg Units.val (hc _ σ (fun x => ?_)))
  rw [← Bw.e_comm]
  erw [MulEquiv.apply_symm_apply]
  rfl
