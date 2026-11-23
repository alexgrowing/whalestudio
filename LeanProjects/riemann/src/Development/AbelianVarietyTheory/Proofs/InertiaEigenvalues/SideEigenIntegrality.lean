import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BuiltEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenWeightStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenConductorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenCharacterStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.CoefDuty.ExtBuilt

theorem extOf_built : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ big₀ L₀, Built A M C tp.tup big₀ L₀ → ∃ big₁, ∀ L₁, Built A M C tp.tup big₁ L₁ → ∀ i₁, ∃ i₀, ExtOf L₀ L₁ i₀ i₁ := by
  intro hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hst hex hsp hCh big₀ L₀ hB₀
  obtain ⟨big₁, hR⟩ := GlobalTheory.T.side_eigen_level hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hst hex hsp hCh big₀ L₀ hB₀
  refine ⟨big₁, fun L₁ hB₁ i₁ => ?_⟩
  obtain ⟨i₀, hw, hj, e, he⟩ := GlobalTheory.T.side_eigen_weight hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hst hex hsp hCh big₀ big₁ L₀ L₁ hB₀ hB₁ i₁
  obtain ⟨φ, hφ, hφa⟩ := hR L₁ hB₁ i₀ i₁ hw
  have hZ := GlobalTheory.T.side_eigen_conductor hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hst hex hsp hCh big₀ big₁ L₀ L₁ hB₀ hB₁ i₀ i₁ hw hj e he
  have hchi := GlobalTheory.T.side_eigen_character hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hst hex hsp hCh big₀ big₁ L₀ L₁ hB₀ hB₁ i₀ i₁ hw hj φ hφ hφa
  have hl : L₀.lay.fixZ.nd.l i₀ = L₁.lay.fixZ.nd.l i₁ := by
    rw [← L₀.lay.fixZ.nd.w_l, ← L₁.lay.fixZ.nd.w_l, hw]
  have hQ : L₀.lay.fixZ.nd.Q i₀ = L₁.lay.fixZ.nd.Q i₁ := by
    obtain ⟨Sp₀, -, -⟩ := hB₀
    obtain ⟨Sp₁, -, -⟩ := hB₁
    have h0 := Sp₀.Q_eq _ _ i₀ ((L₀.X.locs_mem _ _ i₀).2 ⟨rfl, rfl⟩)
    have h1 := Sp₁.Q_eq _ _ i₁ ((L₁.X.locs_mem _ _ i₁).2 ⟨rfl, rfl⟩)
    rw [Sp₀.Qc_eq] at h0
    rw [Sp₁.Qc_eq] at h1
    exact h0.trans ((congrArg C.Q hw).trans h1.symm)
  have hS : ∀ v, v ∈ L₀.lay.fixZ.nd.S i₀ ↔ v ∈ L₁.lay.fixZ.nd.S i₁ := by
    intro v
    rw [L₀.lay.fixZ.nd.S_def, L₁.lay.fixZ.nd.S_def, hl]
  have hout : ∀ v, SplitOut L₁.lay.fixZ.nd i₁ v ↔ SplitOut L₀.lay.fixZ.nd i₀ v := by
    intro v
    unfold SplitOut
    rw [hl, hQ, hS v]
  have hinj : Function.Injective (iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁) := by
    unfold iotaO
    exact (RingEquiv.injective _).comp ((RingHom.injective _).comp (IsFractionRing.injective _ _))
  have hcyc : ∀ (l l' : ℕ) (_ : l = l') [Fact l.Prime] [Fact l'.Prime] (σ : GE L₁.lay.fixZ.nd),
      HEq (cycZ (F := D.host.E) (Ω := L₀.lay.fixZ.nd.Om) l σ) (cycZ (F := D.host.E) (Ω := L₁.lay.fixZ.nd.Om) l' σ) := by
    intro l l' h _ _ σ
    subst h
    rfl
  refine ⟨i₀, hw, ⟨LocExt.mk hl φ hφ hφa e hout ?_ hZ (MulEquiv.refl _) continuous_id continuous_id
    (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun σ => hcyc _ _ hl σ) hchi⟩⟩
  intro v k x hv hk1 hk2
  apply hinj
  rw [hφ]
  exact he v k x hv hk1 hk2

end GlobalTheory.CoefDuty.ExtBuilt

end
