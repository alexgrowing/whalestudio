import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DenseSplitFrobInvAway
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.frobId_holds :
    DenseId → CpFacts → FrobId := by
  intro hDI hCp E Ω _ _ _ _ _ _ l _ ι d t r r' a a' hr hr' ha ha' hev
  have hS := Filter.eventually_cofinite.1 hev
  refine hDI (G E Ω) l d d t t r r' a a' hr hr' ha ha' _
    (GlobalTheory.SplitAttUniq.dense_splitFrobInv_away E Ω l (Fact.out) _ hS) ?_
  rintro g ⟨w, hw, hsp, hl, A, hA, hF⟩
  obtain ⟨S₀, c, c', h1, h2, h3, h4⟩ := (not_not.1 hw) hsp
  have lin_map : ∀ (b : Fin t → G E Ω →* (Qbar l)ˣ) (e : Fin t → ℂ),
      (∀ i, FrobEig ι (rk1 (b i)) w {e i}) →
      (lin b g).map ι.toRingHom = ∏ i, (X - C (e i)) := by
    intro b e hb
    rw [lin, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    have h := ((hb i) A hA).2 g⁻¹ hF
    rw [inv_inv] at h
    have h' : cp (rk1 (b i)) g = X - C (b i g : Qbar l) := (hCp (G E Ω) (Qbar l) 0 0).2.1 (b i) g
    rw [← h']
    simpa using h
  have cp_map : ∀ (s : G E Ω →* GL (Fin d) (Qbar l)) (e : Fin t → ℂ),
      FrobEig ι s w (S₀ + Finset.univ.val.map e) →
      (cp s g).map ι.toRingHom = (S₀.map fun z => X - C z).prod * ∏ i, (X - C (e i)) := by
    intro s e hs
    have h := (hs A hA).2 g⁻¹ hF
    rw [inv_inv] at h
    rw [cp, h, Multiset.map_add, Multiset.prod_add, Multiset.map_map]
    rfl
  apply Polynomial.map_injective ι.toRingHom ι.injective
  rw [Polynomial.map_mul, Polynomial.map_mul, cp_map r c h1, cp_map r' c' h2, lin_map a' c' h4,
    lin_map a c h3]
  ring
