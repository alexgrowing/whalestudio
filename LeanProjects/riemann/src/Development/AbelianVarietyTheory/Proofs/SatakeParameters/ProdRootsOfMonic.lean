import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowLeSpan

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne

namespace GlobalTheory.RowTie

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

def WDOfTie (T : WDTie N A) : Prop :=
  ∀ (i : N.Loc) (a : ℕ) (r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) (w : PlE H)
    (hl : ((N.l i : ℕ) : 𝓞 H.E) ∉ w.asIdeal),
    Continuous (fun g => ((r g : GL (Fin a) (Qbar (N.l i))) :
      Matrix (Fin a) (Fin a) (Qbar (N.l i)))) →
    T.e w (A.wdOf i r w) = wdOf (N.plOm.2 w) hl (A.iotaQC i) r

theorem prod_roots_of_monic {p : ℂ[X]} (hp : p.Monic) : (p.roots.map fun α => X - C α).prod = p :=
  ((IsAlgClosed.splits p).eq_prod_roots_of_monic hp).symm

theorem eigAway_of_wdOfTie : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂)
    (A : NAut N) (T : WDTie N A), WDOfTie T → GlobalTheory.LocalInv.EigAway N A T.eig := by
  intro R H what₂ N A T hT i a ρ hρ w hw σ hσ
  have hW : σ ∈ Weil (N.plOm.2 w) := mem_Weil_of_isFrob _ hσ
  have hr : Continuous (fun g => ((mapRep (iotaOQ N A i) ρ g : GL (Fin a) (Qbar (N.l i))) :
      Matrix (Fin a) (Fin a) (Qbar (N.l i)))) :=
    Continuous.matrix_map hρ (GlobalTheory.CoeffEmbedding.continuous_iotaOQ R H what₂ N A i)
  have hcomp : iotaO N A i = (A.iotaQC i).toRingHom.comp (iotaOQ N A i) := rfl
  rw [WDTie.eig, GlobalTheory.LocalInv.wd, hT i a _ w hw hr, WD.inePol_of_mem _ hW,
    prod_roots_of_monic (WD.charPol_monic _ _), charPol_wdOf hw (A.iotaQC i) hr ⟨σ, hW⟩, hcomp,
    ← Polynomial.map_map, ← Matrix.charpoly_map]
  rfl

end GlobalTheory.RowTie
