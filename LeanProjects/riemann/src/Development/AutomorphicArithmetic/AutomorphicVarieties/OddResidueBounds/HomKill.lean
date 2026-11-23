import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ClKill
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.FixField

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.homKill :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), IsCycAct Ω N ρ → 2 < N → ∀ a : ℕ, Odd a → a.Coprime N → ∀ (R X : Type) [CommRing R] [AddCommGroup X] [Module R X] (N' : ℕ), ∀ φ ∈ XDual N' (fixMu E Ω N) R X, ∀ σ : (ZMod N)ˣ → Ω ≃+* Ω, (∀ b, CycLift N b (σ b)) → ∀ (u : fixMu E Ω N) (w : (ZMod N)ˣ → fixMu E Ω N), (∀ b y, u.1 (σ b y) = σ b ((w b).1 y)) → ∑ b : (ZMod N)ˣ, Eone N a b • φ (w b) = 0 := by
  intro E Ω _ _ _ _ _ N _ ρ hρ hN2 a ha hcop R X _ _ _ N' φ hφ σ hσ u w huw
  obtain ⟨K, hKnf, hKcyc, hKgal, hKlift⟩ := fixField E Ω N ρ hρ
  have hU : fixMu E Ω N ≤ galOf E K Ω := le_of_eq hKgal.symm
  have hφ1 : φ ∈ XDual 1 (fixMu E Ω N) R X := by
    obtain ⟨h1, h2, h3, -⟩ := hφ
    refine ⟨h1, h2, h3, ?_⟩
    intro A hA
    simp at hA
  have hTC : IsTotallyComplex K := IsCyclotomicExtension.Rat.isTotallyComplex K hN2
  rw [← pullOnto E Ω K (fixMu E Ω N) hU 1 R X one_ne_zero (le_of_eq hKgal) (Or.inl hTC)] at hφ1
  obtain ⟨ψ, hψ, rfl⟩ := hφ1
  have hart : ∀ b, Additive.ofMul (artU K hU (w b)) =
      Stick.clRep K ((Stick.sg N K) b)⁻¹ (Additive.ofMul (artU K hU u)) := by
    intro b
    have hl := hKlift b (σ b) (hσ b)
    have hg : toGal K hU (w b) = conjGal hl (toGal K hU u) := by
      ext x
      rw [conjGal_apply]
      show (w b).1 x = (σ b).symm (u.1 (σ b x))
      rw [huw b x, RingEquiv.symm_apply_apply]
    have hc := artConj K Ω _ (σ b) hl (toGal K hU u)
    rw [← hg] at hc
    show _ = Stick.clRep K ((Stick.sg N K) b)⁻¹ (Additive.ofMul (artCl K Ω (toGal K hU u)))
    rw [hc]
    show _ = Stick.clRep K ((Stick.sg N K) b)⁻¹ (Stick.clRep K ((Stick.sg N K) b) (Additive.ofMul (artCl K Ω (toGal K hU (w b)))))
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rfl
  let ψ' : Additive (ClassGroup (𝓞 K)) →+ X :=
    AddMonoidHom.mk' (fun c => ψ (Additive.toMul c)) (fun c d => hψ.1 _ _)
  have hsum := clKill N K a ha hcop (Additive.ofMul (artU K hU u))
  have key : ∀ b, (clPull K hU R X ψ) (w b) = ψ' (Stick.clRep K ((Stick.sg N K) b)⁻¹ (Additive.ofMul (artU K hU u))) := by
    intro b
    rw [← hart b]
    rfl
  calc _ = ∑ b : (ZMod N)ˣ, Eone N a ↑b • ψ' (Stick.clRep K ((Stick.sg N K) b)⁻¹ (Additive.ofMul (artU K hU u))) :=
        Finset.sum_congr rfl (fun b _ => by rw [key b])
    _ = 0 := by
      simp_rw [← map_zsmul ψ']
      rw [← map_sum, hsum, map_zero]
