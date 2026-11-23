import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.jumpSeed_of :
    CoverIn → SSBlock → SubLoc → LocConj → JumpCard → JumpCondition := by
  intro h1 h2 h3 h4 h5 E Ω _ _ _ _ _ _ l _ ι a dd U r ρ hss hcov w hcrys hocc P AI hT A hA O _ _ _ Bw hj
  have hc := hcrys P AI hT A hA O Bw hj
  have hdr := ((h4 l P AI hT E Ω A O Bw a (r.comp (Dec (F := E) A).subtype) (r.comp (Dec (F := E) A).subtype)).1 hc).1
  refine ⟨hc, hdr, ?_⟩
  intro τ LL' τ' hτ lam J hw hJ
  obtain ⟨Jr, hJr, hcard⟩ := h5 l P AI hT E Ω A O Bw a _ hdr τ LL' τ' hτ
  obtain ⟨J', hJ', hsub⟩ := hocc P AI hT A hA O Bw hj τ LL' τ' hτ lam J hw hJ
  obtain ⟨m, n, e, hin⟩ := h1 _ _ a dd r ρ hcov
  have hR := h2 _ _ a m n e r hss
  have hcomp : (blockRep (a := fun _ : Fin m => a) e fun _ => r).comp (Dec (F := E) A).subtype =
      blockRep (a := fun _ : Fin m => a) e fun _ => r.comp (Dec (F := E) A).subtype := by
    ext g i j
    rfl
  have hjR : IsJumpsAt P Bw ((blockRep (a := fun _ : Fin m => a) e fun _ => r).comp (Dec (F := E) A).subtype) τ
      (∑ _ : Fin m, Jr) := by
    rw [hcomp]
    exact GlobalTheory.BlockSum.isJumpsAt_blockRep P Bw e hτ fun _ => hJr
  have hle : J' ≤ ∑ _ : Fin m, Jr :=
    (h3 E Ω l dd n ρ _ hR hin ι w P AI hT A hA O Bw hj).2 τ _ _ hjR hJ'
  have hJeq : J = (wtJumps lam).val :=
    Multiset.map_injective Int.cast_injective (hJ.trans (wtJumps_val lam).symm)
  have hnd : J.Nodup := hJeq ▸ (wtJumps lam).nodup
  have hJc : J.card = a := by rw [hJeq]; exact card_wtJumps lam
  have hss' : J ⊆ Jr := fun j hjJ => by
    obtain ⟨_, -, hj'⟩ := Multiset.mem_sum.1 (Multiset.mem_of_le hle (hsub j hjJ))
    exact hj'
  have hJJ : J = Jr :=
    Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset hnd).2 hss') (by rw [hcard, hJc])
  rw [hJJ]
  exact hJr
