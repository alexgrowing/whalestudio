import Mathlib
import Formalism.SharpRestriction.ElevenLe
import Formalism.LocalRingCardinality.DataParamsT
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Definitions.Divisors.GridTestLatticeLargestSlopeBound
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def SizeRows (large₂ : SizeData₂ D) : Prop :=
  (∃ (Pm : ParameterChoice' D large₂) (_ : ParamsT D large₂ Pm), Pm.CnW = 10) ∧ Formalism.MainNotions.SizesAt large₂ ∧
  D.R.m ^ 4 ≤ D.R.f ∧ 44 ≤ D.R.m ∧
  large₂.sc.x ^ 2 * (D.R.m : ℝ) ^ 3 * large₂.sc.L * Real.log D.host.rdE ≤ D.R.k ∧
  (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d ≤ large₂.sc.b ∧
  D.R.f * D.R.m ≤ (D.R.r + 1) ^ 3 ∧
  (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) ∧
  Real.log (q0 D) ≤ large₂.sc.L ∧
  Real.log D.host.rdE ≤ Real.log (LevelStarExponents.condE D) ∧ Real.log (LevelStarExponents.condE D) ≤ large₂.sc.L / 100 ∧
  large₂.Sc + ((D.R.m : ℝ) + 1) * gap D 1 + 1 / 2 ≤ large₂.sc.b ∧
  (∀ τ l, 0 < (D.hc τ).b l ∧ (((D.hc τ).e l : ℚ) : ℝ) ≤ 4 * large₂.sc.b) ∧
  D.host.ccK = ⊤

section Columns

variable {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (θ : InfFam D)

theorem posDef_dual (τ : D.what₂.Tau) : (((Xp G).gram.map (tauE D τ))⁻¹).transpose.PosDef := by
  exact ((posDef_Xp G (tauE D τ)).inv).transpose

def coefPlus : CoefA (G.V (.top 0)) :=
  GlobalTheory.CoefModel.coefOf (LaP G) (posDef_dual G) (invTrK.comp (GlobalTheory.CoefModel.realGL θ (Xp G)))

def levPlus : Subgroup (Bridge.Gf (G.V (.top 0))) := (Lev.toAfE _ G.Kplus).comap (finHom (G.V (.top 0))).range.subtype

def Cols : Submodule ℂ (Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W) :=
  Bridge.AdForms (Bridge.ratF (G.V (.top 0))) (coefPlus G θ).coef.ρ (levPlus G) 1

theorem mem_cols (Ψ : Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W) : Ψ ∈ Cols G θ ↔
    ∀ (γ : GQ (G.V (.top 0))) g (k : levPlus G), Ψ (Bridge.ratF (G.V (.top 0)) γ * g * k) = (coefPlus G θ).ρ γ (Ψ g) := by
  unfold Cols Bridge.AdForms
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq,
    MonoidHom.one_apply, Units.val_one, one_smul]
  rfl

end Columns

section Main

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {sc : Consts}
  {G : GridData R.toLevCh sc} (W : G.Weil) (M : Vol G)

def rowForm (w : SmT (R.MY 0)) (t : Mult.MMap (R.MY 0)) : GA D (Yc D 0) → ℂ := PiTensorProduct.lift t w

def Separates (w : SmT (R.MY 0)) (ρ : G.RealVec) (ξ : Module.Dual ℂ (coefPlus G W.θ).W) : Prop :=
  ∀ t ∈ R.EEat R.triv, t ≠ 0 → ∃ Ψ ∈ Cols G W.θ, ∃ Φ : G.Datum,
    FConv W M ρ ξ Ψ Φ (rowForm R w t) ∧ fPsiPhi W M ρ ξ Ψ Φ (rowForm R w t) ≠ 0

def SeparatesSpan (w : SmT (R.MY 0)) (ρ : G.RealVec) (ξ : Module.Dual ℂ (coefPlus G W.θ).W) : Prop :=
  ∀ t ∈ R.EEat R.triv, t ≠ 0 → ∃ Ψ ∈ Cols G W.θ, ∃ c : G.Datum →₀ ℂ,
    (∀ Φ ∈ c.support, FConv W M ρ ξ Ψ Φ (rowForm R w t)) ∧ (c.sum fun Φ a => a * fPsiPhi W M ρ ξ Ψ Φ (rowForm R w t)) ≠ 0

example (w : SmT (R.MY 0)) (ρ : G.RealVec) (h : Separates R W M w ρ 0) : R.EEat R.triv = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun t ht => by_contra fun h0 => ?_
  obtain ⟨Ψ, -, Φ, -, h2⟩ := h t ht h0
  refine h2 ?_
  have e : pairVec (coefPlus G W.θ) 0 Ψ = (0 : ℂ) • pairVec (coefPlus G W.θ) 0 Ψ := by
    funext x; simp [pairVec_apply]
  rw [fPsiPhi, e, ← one_smul ℂ (thetaChi W M ρ Φ _), Bplus_smul, zero_mul, zero_mul]

end Main

def FunctionalsSeparate : Prop :=
  ∀ ε CF : ℝ, 6510 ≤ CF → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → SizeRows large₂ →
    GlobalTheory.GLq.ESerTie D →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
      R.toLevCh.Is A.μ0 → R.grp_record →
      ∀ (G : GridData R.toLevCh ⟨1, CF, large₂.sc.b⟩) (W : G.Weil), W.Over R → ∀ M : Vol G, M.IsRow →
        ∀ w : SmT (R.MY 0), w ≠ 0 →
          ∃ (ρ : G.RealVec) (ξ : Module.Dual ℂ (coefPlus G W.θ).W), Separates R W M w ρ ξ

end GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup

end
