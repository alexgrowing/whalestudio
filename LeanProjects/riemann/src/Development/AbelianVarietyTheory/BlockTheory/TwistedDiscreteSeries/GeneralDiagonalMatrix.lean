import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lattice

variable {D : D7}

def StabLat (V : HSp D) (κ : GA D V) : Prop :=
  κ ∈ GfC V ∧ gLat V κ = (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E))

def LevAgrees (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (M : ℕ) (Mh : Ideal (𝓞 D.host.E)) (κ : GA D V)
    (lev : La →ₗ[𝓞 D.host.E] La) : Prop :=
  ∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
    finVec V (ι (lev a)) - (finHom V κ).1.mulVec (finVec V (ι a)) = M • w

theorem stabLat_one (V : HSp D) : StabLat V 1 := by
  refine ⟨Subgroup.one_mem _, ?_⟩
  unfold gLat
  rw [map_one]
  ext z
  simp

end Lattice

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def genDiag (Dw : Datum H) {S : Type} [CommRing S] (a : Sˣ) : Ix Dw → Sˣ
  | none => a
  | some _ => 1

def FrScal {S : Type} [CommRing S] [Algebra c.F S] (a : Sˣ) (y z : FrPt Xo c S) : Prop :=
  (∀ τ i, z.u τ i = y.u τ i) ∧ FrBor (genDiag Dw a) y z

end Frames

section Statement

variable {D : D7} (T : CoreJ D) (hT : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ)

include hT hj hσ in

theorem dict_mem_dom (h : GA D (T.V j σ)) : (T.dict j σ h).2 ∈ ((T.U j σ).X (T.dict j σ h).1).dom := by
  obtain ⟨_, _, _, hd⟩ := hT.dictU j hj σ hσ
  exact hd.2.2.2.1 h

include hT hj hσ in

theorem rank_eq : (T.V j σ).rank = D.R.r := (hT.modelW j hj σ hσ).choose

def ptOf (h : GA D (T.V j σ)) : FrPt (T.Q.Xo j) T.Q.c (CAt σ) :=
  (T.U j σ).un (T.dict j σ h).1 ⟨(T.dict j σ h).2, dict_mem_dom T hT j hj σ hσ h⟩

def iotaV : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (T.V j σ).rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_eq T hT j hj σ hσ)) ∘ₗ T.iota j

def halfM : Ideal (𝓞 D.host.E) := T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)

def MovesBy (κ : GA D (T.V j σ)) (lev : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) (h : GA D (T.V j σ))
    (a : (CAt σ)ˣ) : Prop :=
  ∃ y' : FrPt (T.Q.Xo j) T.Q.c (CAt σ),
    levR (lev, LinearMap.id) (ptOf T hT j hj σ hσ h) y' ∧ FrScal a y' (ptOf T hT j hj σ hσ (h * κ))

def DictLevelMoveAt : Prop :=
  ∀ κ, StabLat (T.V j σ) κ → ∃ c₂ : (T.U j σ).Comp → ℂ, CUnit c₂ ∧
    ∀ lev : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La,
      LevAgrees (T.V j σ) (iotaV T hT j hj σ hσ) T.Q.l.M (halfM T) κ lev →
      ∀ h, ∃ a : (CAt σ)ˣ, MovesBy T hT j hj σ hσ κ lev h a ∧ toC (a : CAt σ) ^ 2 = c₂ (T.dict j σ h).1

def DictLevelMoveSignedAt : Prop :=
  ∀ κ, StabLat (T.V j σ) κ → ∃ c₁ : (T.U j σ).Comp → ℂ, CUnit c₁ ∧
    ∀ lev : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La,
      LevAgrees (T.V j σ) (iotaV T hT j hj σ hσ) T.Q.l.M (halfM T) κ lev →
      ∀ h, ∃ a : (CAt σ)ˣ, MovesBy T hT j hj σ hσ κ lev h a ∧ toC (a : CAt σ) = c₁ (T.dict j σ h).1

end Statement

def DictLevelMove : Prop :=
  ∀ (D : D7) (T : CoreJ D) (hT : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ),
    DictLevelMoveAt T hT j hj σ hσ

end GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix
