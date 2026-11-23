import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OnePerPlace

noncomputable section

namespace HcInf

open NumberField IsDedekindDomain HcS.BasicNotions HcS.MainNotions HcS.MainNotions.StandardLattice HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes HcS.L2.Fam.SG.Tau
  HcS.L2.Fam.SG.Tau.InfCmpCut Matrix MeasureTheory Filter
open scoped TensorProduct Topology ENNReal NNReal

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (T : Type) [Fintype T] (emb : T → (E →+* ℂ)) (cd : CDHaar)

def Rel {W : HSpace E} {P Q : ℕ} (θ : T → (Ainf F ⊗[F] E →+* ℂ))
    (A : T → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ) (b : HA (Ainf F) hc.sig W.gram) (ρ : T)
    (x : UpqT P Q) : Prop :=
  UpqT.mat x * A ρ = A ρ * (Units.val (HA.mat (Ainf F) hc.sig W.gram b)).map (θ ρ)

def CdFin : Prop := ∀ P Q : ℕ, SigmaFinite (cd.cd P Q)

def ArchSplit : Prop :=
  OnePerPlace (F := F) emb → ∀ (W : HSpace E) (P Q : ℕ), P + Q = W.rank →
  ∀ θ : T → (Ainf F ⊗[F] E →+* ℂ), (∀ ρ, IsInfEmb (emb ρ) (θ ρ)) →
  ∀ A : T → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ,
    (∀ ρ, (A ρ).conjTranspose * HcS.UG.Jpq P Q * A ρ = W.gram.map (emb ρ)) →
  ∃ Φ : HA (Ainf F) hc.sig W.gram ≃ᵐ (T → UpqT P Q),
    (∀ b c, Φ (b * c) = Φ b * Φ c) ∧ Continuous Φ ∧ Continuous Φ.symm ∧
    ∀ b ρ x, (Rel F E hc T θ A b ρ x ↔ x = Φ b ρ)

def LocTamExists : Prop :=
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ W : HSpace E,
    ∃ μ : Measure (HA (Ainf F) hc.sig W.gram), LocTam (Ainf F) hc.sig W.gram (psiInf F ψ) μ

def HaarUnique : Prop :=
  ∀ (W : HSpace E) (P Q : ℕ) (Φ : HA (Ainf F) hc.sig W.gram ≃ᵐ (T → UpqT P Q)),
    (∀ b c, Φ (b * c) = Φ b * Φ c) → Continuous Φ → Continuous Φ.symm →
    ∀ μ : Measure (HA (Ainf F) hc.sig W.gram), μ.IsHaarMeasure →
      ∃ k : ℝ≥0∞, μ.map Φ = k • Measure.pi (fun _ : T => cd.cd P Q)

def DensityConst : Prop :=
  OnePerPlace (F := F) emb → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∃ a : ℕ → ℝ, (∀ M, 0 < a M) ∧
  ∀ (W : HSpace E) (P Q : ℕ), P + Q = W.rank →
  ∀ θ : T → (Ainf F ⊗[F] E →+* ℂ), (∀ ρ, IsInfEmb (emb ρ) (θ ρ)) →
  ∀ A : T → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ,
    (∀ ρ, (A ρ).conjTranspose * HcS.UG.Jpq P Q * A ρ = W.gram.map (emb ρ)) →
  ∀ Φ : HA (Ainf F) hc.sig W.gram ≃ᵐ (T → UpqT P Q),
    (∀ b c, Φ (b * c) = Φ b * Φ c) → Continuous Φ → Continuous Φ.symm →
    (∀ b ρ x, (Rel F E hc T θ A b ρ x ↔ x = Φ b ρ)) →
  ∀ (μ : Measure (HA (Ainf F) hc.sig W.gram)) (k : ℝ≥0∞),
    LocTam (Ainf F) hc.sig W.gram (psiInf F ψ) μ →
    μ.map Φ = k • Measure.pi (fun _ : T => cd.cd P Q) → k = ENNReal.ofReal (a W.rank)

variable {F E hc T emb cd}

end HcInf
