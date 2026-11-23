import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.MeasLie

noncomputable section

namespace HcS.L2.Fam.SG.Tau.InfCmpCut

open NumberField IsDedekindDomain HcS.BasicNotions HcS.MainNotions HcS.MainNotions.StandardLattice HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes HcS.L2.Fam.SG.Tau Matrix
  MeasureTheory Filter
open scoped TensorProduct Topology ENNReal NNReal

def OnePerPlace {F E : Type} [Field F] [Field E] [Algebra F E] {T : Type} (emb : T → (E →+* ℂ)) : Prop :=
  Function.Bijective fun ρ : T => (emb ρ).comp (algebraMap F E)

def InfCmpG (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (T : Type) [Fintype T] (emb : T → (E →+* ℂ)) (cd : CDHaar) : Prop :=
  OnePerPlace (F := F) emb →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∃ a : ℕ → ℝ, (∀ M, 0 < a M) ∧
  ∀ (W : HSpace E) (P Q : ℕ), P + Q = W.rank →
  ∀ θ : T → (Ainf F ⊗[F] E →+* ℂ), (∀ ρ, IsInfEmb (emb ρ) (θ ρ)) →
  ∀ A : T → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ,
    (∀ ρ, (A ρ).conjTranspose * HcS.UG.Jpq P Q * A ρ = W.gram.map (emb ρ)) →
  ∃ μ : Measure (HA (Ainf F) hc.sig W.gram), LocTam (Ainf F) hc.sig W.gram (psiInf F ψ) μ ∧
  ∀ B : T → Set (UpqT P Q), (∀ ρ, MeasurableSet (B ρ)) →
    let S : Set (HA (Ainf F) hc.sig W.gram) := {b | ∀ ρ, ∃ x ∈ B ρ, UpqT.mat x * A ρ = A ρ *
      (Units.val (HA.mat (Ainf F) hc.sig W.gram b)).map (θ ρ)}
    MeasurableSet S ∧ μ S = ENNReal.ofReal (a W.rank) * ∏ ρ, cd.cd P Q (B ρ)

end HcS.L2.Fam.SG.Tau.InfCmpCut
