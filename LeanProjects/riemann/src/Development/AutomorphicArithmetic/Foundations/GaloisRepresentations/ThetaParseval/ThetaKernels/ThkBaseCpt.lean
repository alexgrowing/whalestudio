import Development.WeilBound.ThetaLifts.LatticeBasics.FdEqZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkEstStmt

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
def CptAll_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → min r s = 0 → Cpt σ Y.J
theorem cptAll_of_k (h1 : PositivityTheory.ThKEst.GrpTop) (h2 : _root_.PositivityTheory.ThKEst.EpsOf_k) (h3 : PositivityTheory.ThKEst.SiegelAll) (h4 : PositivityTheory.ThKEst.FinVolU)
    (h5 : PositivityTheory.ThKF.Unimod) : _root_.GlobalTheory.ThK.Dbl.CptAll_k := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY h0
  obtain ⟨e, -, hr⟩ := h2 F E σ B hB n Y r s hY
  obtain ⟨a1, a2, a3, a4, -, -, -, a5⟩ := h1 F E σ hB.cm n Y.J e
  obtain ⟨fr, g, -, ⟨Ω, hΩ, hc⟩, -⟩ := h3 F E σ hB.cm n Y.J e
  have r0 : fr.r = 0 := by have := hr fr g; omega
  have a0 : ∀ t, fr.a t = 1 := fun t => by
    have : t + t = t := funext fun i => absurd i.2 (by omega)
    have e := g.add t t
    rw [this] at e
    exact left_eq_mul.1 e
  have cov : ∀ x, ∃ γ ∈ ratU σ Y.J, γ * x ∈ Ω := fun x => by
    obtain ⟨γ, hγ, t, -, κ, hκ, e⟩ := hc x
    exact ⟨γ, hγ, by rwa [e, a0, one_mul]⟩
  obtain ⟨C, hC⟩ := a5 Ω hΩ
  obtain ⟨-, u1, u2⟩ : Countable (ratU σ Y.J) ∧ _ ∧ _ := e.1.elim
    (fun h => h5 F E σ hB.cm n Y.J 1 (fun i j => by simp [h]) e.2) fun h => h5 F E σ hB.cm n Y.J (-1) (fun i j => by simp [h]) e.2
  refine ⟨a1, a2, a3, a4, ⟨Ω, hΩ, cov⟩, ⟨C, fun x => ?_⟩, u1, h4 F E σ hB.cm n Y.J e, u2⟩
  obtain ⟨γ, hγ, hx⟩ := cov x
  exact (ciInf_le (OrderBot.bddBelow _) (⟨γ, hγ⟩ : ratU σ Y.J)).trans (hC _ hx)
section Gen
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [μ.IsHaarMeasure] {Γ : Subgroup G} [Countable Γ] {D : Set G}
end Gen
variable {J : Matrix (Fin n) (Fin n) E}
end GlobalTheory.ThK.Dbl
end
end
