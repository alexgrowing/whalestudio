import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunModel
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfSabMap
import Development.AbelianVarietyTheory.Counterexamples.ThetaValuation.UniformMultiplier
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.LatticeAndConstantUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev uAt {D : D7} {J : CoreJ D} {G : Type} (r : TwoRuns J G) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (i : Fin D.R.m) :=
  (r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀

end GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Build

theorem mem_localLattice_iff_mulVec {r : ℕ} (D : D7) {Λ Λ' : Submodule (𝓞 D.host.E) (Fin r → D.host.E)}
    (A : Matrix (Fin r) (Fin r) D.host.E) (h : ∀ w, w ∈ Λ ↔ A.mulVec w ∈ Λ') (w : Fin r → D.host.E) :
    w ∈ lattice₂ D Λ ↔ A.mulVec w ∈ lattice₂ D Λ' := by
  simp only [mem_latP]
  refine forall₂_congr fun a _ => ?_
  rw [h, Matrix.mulVec_smul]

theorem chi_one_of_toData {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Xd : DataX E r) (X : Data E r)
    (e : Xd.toData = X) (h : ∀ la, ∀ γ ∈ X.Γ, X.χ la γ = 1) : ∀ la, ∀ γ ∈ Xd.Γ, Xd.χ la γ = 1 := by
  subst e
  exact h

theorem nonempty_place (D : D7) : Nonempty (HeightOneSpectrum (𝓞 D.what₂.LL)) := by
  obtain ⟨I, hb, ht⟩ := (Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top).1 (NumberField.RingOfIntegers.not_isField D.what₂.LL)
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I ht.ne
  exact ⟨⟨P, hP.isPrime, fun e => hb.ne' (le_bot_iff.1 (e ▸ hIP))⟩⟩

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem exists_dataX_latP (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (i : Fin D.R.m)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (k : (uAt r v i).Comp) :
    ∃ Xx : DataX D.host.E D.R.r, Xx.toData = (uAt r v i).X k ∧ Xx.L' = lattice₂ D ((uAt r v i).X k).Λ := by
  obtain ⟨X, ⟨h1, -, h3⟩, -⟩ := GlobalTheory.ModelLatticeCheck.holds_by_value D (r.used v).full.toCore (h.laws v).p.toLawsCore
    ((i : ℕ) + 1) ⟨Nat.le_add_left _ _, i.2⟩ (r.used v).full.σ₀ (r.used v).full.toCore.good_σ₀ k
  refine ⟨X, h1, ?_⟩
  rw [GlobalTheory.ModelLatExamples.eq_latP D X.Λ X.L' h3]
  show lattice₂ D X.toData.Λ = _
  rw [h1]

end Build

end GlobalTheory.ShareOn

end
