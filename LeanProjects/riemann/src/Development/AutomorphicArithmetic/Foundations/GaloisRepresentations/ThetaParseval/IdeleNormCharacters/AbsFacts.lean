import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.AbsFactsAlt
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TwistSatHolds
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr

private theorem symm_eq_mk {E : Type} [Field E] [NumberField E] [IsCMField E]
    (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w)
    (w : InfinitePlace (maximalRealSubfield E)) :
    (IsCMField.equivInfinitePlace E).symm w = InfinitePlace.mk (emb w).1 := by
  rw [Equiv.symm_apply_eq, IsCMField.equivInfinitePlace_apply, InfinitePlace.comap_mk, (emb w).2,
    InfinitePlace.mk_embedding]

private theorem logNorm_diag {E : Type} [Field E] [NumberField E] [IsCMField E] (k : Eˣ) :
    GlobalTheory.Mem.Chr.CharModel.logNorm E (infDiag k) = ∑ v : InfinitePlace E, 2 * Real.log (v (k : E)) := by
  have hp : ∀ v : InfinitePlace E, v (k : E) ≠ 0 := fun v => by simp
  have h := InfinitePlace.prod_eq_abs_norm (k : E)
  change GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.infDiag k) = _
  rw [GlobalTheory.Mem.Chr.CharModel.logNorm, (GlobalTheory.Mem.Chr.CharModel.infDiag_parts k).1,
    (GlobalTheory.Mem.Chr.CharModel.infDiag_parts k).2, GlobalTheory.Mem.Chr.CharModel.logFin_one, sub_zero,
    GlobalTheory.Mem.Chr.CharModel.logInf_principal, ← h, Real.log_prod (fun v _ => pow_ne_zero _ (hp v))]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Real.log_pow, InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex v))]
  norm_num

theorem UpperTheory.Gal.TP.Chr.absFacts :
    UpperTheory.Gal.TP.Chr.AbsFacts := by
  intro E _ _ _ emb z
  refine ⟨fun w => ⟨DiscreteGroups.T1.G.absC_unrAt z w, DiscreteGroups.T1.G.absC_val z w⟩, fun k => ?_⟩
  change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E (infDiag k)) = _
  rw [logNorm_diag, ← (IsCMField.equivInfinitePlace E).symm.sum_comp, Complex.ofReal_sum, Finset.mul_sum,
    Complex.exp_sum]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h0 : 0 < ‖(emb w).1 (k : E)‖ := norm_pos_iff.2 ((map_ne_zero _).2 k.ne_zero)
  rw [symm_eq_mk emb w, InfinitePlace.apply, Complex.cpow_def_of_ne_zero (by exact_mod_cast h0.ne'),
    ← Complex.ofReal_log h0.le]
  congr 1
  push_cast
  ring
