import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharpolySmulMap
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem cp_pv (v w : H.P ℚ) :
    H.cp v ((pv w : (A ℚ)ˣ) : A ℚ) = if w = v then ((atFin v (unif v) : (H.Kv v)ˣ) : H.Kv v) else 1 := by
  obtain ⟨-, -, h3, h4, -, -, -, h8, -⟩ := UpperTheory.ConvolutionTheory.R2.H.sgLaws ℚ w
  rw [pv, h4, map_add, map_one]
  split_ifs with h
  · subst h
    rw [h3, add_sub_cancel]
  · have : H.cp v (H.sg w (((atFin w (unif w) : (H.Kv w)ˣ) : H.Kv w) - 1)) = 0 := (h8 _).2 v (Ne.symm h)
    rw [this, add_zero]

private theorem fin_supp {n : ℕ} : (Function.mulSupport fun v : H.P ℚ => pv v ^ n.factorization (normV v)).Finite := by
  refine (n.factorization.support.finite_toSet.preimage GlobalTheory.TwAtt.normV_injective.injOn).subset fun v hv => ?_
  exact Finsupp.mem_support_iff.2 fun (h : n.factorization (normV v) = 0) => hv (by simp only [h, pow_zero])

private theorem cp_pin (n : ℕ) (v : H.P ℚ) :
    H.cp v ((pin n : (A ℚ)ˣ) : A ℚ) = ((atFin v (unif v) : (H.Kv v)ˣ) : H.Kv v) ^ n.factorization (normV v) := by
  have h := ((H.cp v).toMonoidHom.comp (Units.coeHom (A ℚ))).map_finprod (fin_supp (n := n))
  refine h.trans ((finprod_eq_single _ v fun w hw => ?_).trans ?_)
  · rw [map_pow]
    change H.cp v ((pv w : (A ℚ)ˣ) : A ℚ) ^ _ = 1
    rw [cp_pv, if_neg hw, one_pow]
  · rw [map_pow]
    change H.cp v ((pv v : (A ℚ)ˣ) : A ℚ) ^ _ = _
    rw [cp_pv, if_pos rfl]

private theorem val_nat (v : H.P ℚ) (n : ℕ) : Valued.v (n : H.Kv v) = v.intValuation (n : 𝓞 ℚ) := by
  have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (n : 𝓞 ℚ)
  rw [HeightOneSpectrum.valuation_of_algebraMap] at h1
  simpa using h1

private theorem val_normV (v : H.P ℚ) : Valued.v ((normV v : ℕ) : H.Kv v) = WithZero.exp (-1 : ℤ) := by
  rw [val_nat]
  refine HeightOneSpectrum.intValuation_singleton _ (by exact_mod_cast (GlobalTheory.TwAtt.normV_prime v).ne_zero) ?_
  refine le_antisymm (fun x hx => ?_) ((Ideal.span_singleton_le_iff_mem _).2 ((GlobalTheory.TwAtt.mem_iff v _).2 dvd_rfl))
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, (m : 𝓞 ℚ) = x := ⟨Rat.ringOfIntegersEquiv x, by
    apply Rat.ringOfIntegersEquiv.injective; simp⟩
  have h1 : ((m.natAbs : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    rcases Int.natAbs_eq m with e | e
    · rwa [e, Int.cast_natCast] at hx
    · rwa [e, Int.cast_neg, Int.cast_natCast, neg_mem_iff] at hx
  obtain ⟨c, hc⟩ := Int.natCast_dvd.2 ((GlobalTheory.TwAtt.mem_iff v _).1 h1)
  rw [hc, Int.cast_mul, Int.cast_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

private theorem fst_pin (n : ℕ) : ((pin n : (A ℚ)ˣ) : A ℚ).1 = 1 := by
  have h := ((RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom.comp
    (Units.coeHom (A ℚ))).map_finprod (fin_supp (n := n))
  refine h.trans (finprod_eq_one_of_forall_eq_one fun w => ?_)
  rw [map_pow]
  exact one_pow _

theorem UpperTheory.finiteNatIdele_arch_valuation_support :
    ∀ n : ℕ, 0 < n → ((pin n : (A ℚ)ˣ) : A ℚ).1 = 1 ∧ (∀ v : H.P ℚ, Valued.v (H.cp v ((pin n : (A ℚ)ˣ) : A ℚ)) = Valued.v (n : H.Kv v)) ∧ ∀ v : H.P ℚ, ¬ Bad n v → H.cp v ((pin n : (A ℚ)ˣ) : A ℚ) = 1 := by
  intro n hn
  refine ⟨fst_pin n, fun v => ?_, fun v hv => ?_⟩
  · have hp := GlobalTheory.TwAtt.normV_prime v
    rw [cp_pin, map_pow, unif_spec v]
    conv_rhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n (normV v), Nat.cast_mul, Nat.cast_pow, map_mul, map_pow, val_normV,
      val_nat v (ordCompl[normV v] n), HeightOneSpectrum.intValuation_eq_one_iff.2
        fun h => Nat.not_dvd_ordCompl hp hn.ne' ((GlobalTheory.TwAtt.mem_iff v _).1 h), mul_one]
  · rw [cp_pin, Nat.factorization_eq_zero_of_not_dvd fun h => hv ((GlobalTheory.TwAtt.mem_iff v _).2 h), pow_zero]
