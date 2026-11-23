import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

namespace GlobalTheory.LeviHC

theorem monicFactorFinite : MonicFactorFinite := by
  intro N _ _ p q hp hq hpp hqq hpq v hfin
  rcases subsingleton_or_nontrivial N with hN | hN
  · infer_instance
  obtain ⟨d, c₀, hcd, hpc₀⟩ := hp
  obtain ⟨e, b₀, hbe, hqb₀⟩ := hq
  set T := Algebra.adjoin ℂ (Set.range fun u => p u * q u) with hT
  set Wsp := Submodule.span ℂ {y | ∃ a ∈ T, y = a v} with hWsp
  let s : Set (Module.End ℂ N) := Set.range p ∪ Set.range q
  have hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a := by
    rintro a (⟨u, rfl⟩ | ⟨u, rfl⟩) b (⟨u', rfl⟩ | ⟨u', rfl⟩)
    · exact hpp u u'
    · exact hpq u u'
    · exact (hpq u' u).symm
    · exact hqq u u'
  let S := Algebra.adjoin ℂ s
  letI : CommRing S := Algebra.adjoinCommRingOfComm ℂ hcomm

  let c : ℕ → Module.End ℂ N := fun i => if i < d + 1 then c₀ i else 0
  let b : ℕ → Module.End ℂ N := fun i => if i < e + 1 then b₀ i else 0
  have hpc : ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • c i := fun u => by
    rw [hpc₀ u]; exact Finset.sum_congr rfl fun i hi => by
      show _ = u ^ i • (if i < d + 1 then c₀ i else 0); rw [if_pos (Finset.mem_range.1 hi)]
  have hqb : ∀ u, q u = ∑ i ∈ Finset.range (e + 1), u ^ i • b i := fun u => by
    rw [hqb₀ u]; exact Finset.sum_congr rfl fun i hi => by
      show _ = u ^ i • (if i < e + 1 then b₀ i else 0); rw [if_pos (Finset.mem_range.1 hi)]
  have hpS : Submodule.span ℂ (Set.range p) ≤ Subalgebra.toSubmodule S :=
    Submodule.span_le.2 fun x hx => Algebra.subset_adjoin (Or.inl hx)
  have hqS : Submodule.span ℂ (Set.range q) ≤ Subalgebra.toSubmodule S :=
    Submodule.span_le.2 fun x hx => Algebra.subset_adjoin (Or.inr hx)
  have hcS : ∀ i, c i ∈ S := fun i => by
    by_cases h : i < d + 1
    · show (if i < d + 1 then c₀ i else 0) ∈ S
      rw [if_pos h]; exact hpS (coeff_mem_span hpc₀ h)
    · show (if i < d + 1 then c₀ i else 0) ∈ S
      rw [if_neg h]; exact S.zero_mem
  have hbS : ∀ i, b i ∈ S := fun i => by
    by_cases h : i < e + 1
    · show (if i < e + 1 then b₀ i else 0) ∈ S
      rw [if_pos h]; exact hqS (coeff_mem_span hqb₀ h)
    · show (if i < e + 1 then b₀ i else 0) ∈ S
      rw [if_neg h]; exact S.zero_mem
  let c' : ℕ → S := fun i => ⟨c i, hcS i⟩
  let b' : ℕ → S := fun i => ⟨b i, hbS i⟩
  let P : Polynomial S := ∑ i ∈ Finset.range (d + 1), Polynomial.monomial i (c' i)
  let Q : Polynomial S := ∑ i ∈ Finset.range (e + 1), Polynomial.monomial i (b' i)
  have hPe : ∀ u, ((P.eval (algebraMap ℂ S u) : S) : Module.End ℂ N) = p u := fun u => by
    rw [hpc u]
    simp only [P, Polynomial.eval_finset_sum, Polynomial.eval_monomial]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.commutes, map_pow]
  have hQe : ∀ u, ((Q.eval (algebraMap ℂ S u) : S) : Module.End ℂ N) = q u := fun u => by
    rw [hqb u]
    simp only [Q, Polynomial.eval_finset_sum, Polynomial.eval_monomial]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.commutes, map_pow]
  have hPc : ∀ i, i < d + 1 → P.coeff i = c' i := fun i hi => by
    simp [P, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, hi]
  have hPm : P.Monic := by
    refine Polynomial.monic_of_degree_le d ?_ ?_
    · refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le fun i hi => ?_)
      exact (Polynomial.degree_monomial_le _ _).trans (by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    · rw [hPc d (Nat.lt_succ_self d)]
      exact Subtype.ext (by simp [c', c, hcd])
  have hQm : Q.Monic := by
    refine Polynomial.monic_of_degree_le e ?_ ?_
    · refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le fun i hi => ?_)
      exact (Polynomial.degree_monomial_le _ _).trans (by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    · simp only [Q, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
      rw [Finset.sum_ite_eq' (Finset.range (e + 1)) e b', if_pos (Finset.mem_range.2 (Nat.lt_succ_self e))]
      exact Subtype.ext (by simp [b', b, hbe])

  let R : Subalgebra ℂ S :=
    Algebra.adjoin ℂ (Set.range fun u => P.eval (algebraMap ℂ S u) * Q.eval (algebraMap ℂ S u))
  have hRT : ∀ r ∈ R, ((r : S) : Module.End ℂ N) ∈ T := by
    intro r hr
    have hle : R ≤ Subalgebra.comap S.val T := Algebra.adjoin_le (by
      rintro _ ⟨u, rfl⟩
      show ((P.eval (algebraMap ℂ S u) * Q.eval (algebraMap ℂ S u) : S) : Module.End ℂ N) ∈ T
      rw [Subalgebra.coe_mul, hPe, hQe]
      exact Algebra.subset_adjoin ⟨u, rfl⟩)
    exact hle hr

  have hPQR : ∀ k, (P * Q).coeff k ∈ R := by
    intro k
    by_cases hk : k < (P * Q).natDegree + 1
    · have hf : ∀ u, (P * Q).eval (algebraMap ℂ S u) =
          ∑ i ∈ Finset.range ((P * Q).natDegree + 1), u ^ i • (P * Q).coeff i := fun u => by
        rw [Polynomial.eval_eq_sum_range]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def, map_pow, mul_comm]
      have h1 := coeff_mem_span hf hk
      have h2 : Submodule.span ℂ (Set.range fun u => (P * Q).eval (algebraMap ℂ S u)) ≤ Subalgebra.toSubmodule R := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨u, rfl⟩
        show Polynomial.eval (algebraMap ℂ S u) (P * Q) ∈ R
        rw [Polynomial.eval_mul]
        exact Algebra.subset_adjoin ⟨u, rfl⟩
      exact h2 h1
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      exact R.zero_mem
  have hlift : P * Q ∈ Polynomial.lifts (algebraMap R S) :=
    (Polynomial.lifts_iff_coeff_lifts _).2 fun k => ⟨⟨_, hPQR k⟩, rfl⟩
  obtain ⟨F, hF, -, hFm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (hPm.mul hQm)

  let C : Set S := c' '' (Finset.range (d + 1) : Set ℕ)
  have hCf : C.Finite := (Finset.range (d + 1)).finite_toSet.image c'
  have hCi : ∀ x ∈ C, IsIntegral R x := by
    rintro _ ⟨i, hi, rfl⟩
    have := Polynomial.isIntegral_coeff_of_dvd F P hFm hPm (by rw [hF]; exact dvd_mul_right P Q) i
    rwa [hPc i (Finset.mem_range.1 hi)] at this
  obtain ⟨G, hG⟩ := fg_adjoin_of_finite hCf hCi

  let B : Subalgebra ℂ S := (Algebra.adjoin R C).restrictScalars ℂ
  have hpB : Algebra.adjoin ℂ (Set.range fun u => P.eval (algebraMap ℂ S u)) ≤ B := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨u, rfl⟩
    simp only [P, Polynomial.eval_finset_sum, Polynomial.eval_monomial]
    refine B.sum_mem fun i hi => B.mul_mem ?_ (B.pow_mem (B.algebraMap_mem u) _)
    exact (Subalgebra.mem_restrictScalars _).2 (Algebra.subset_adjoin ⟨i, hi, rfl⟩)
  have hmap : Algebra.adjoin ℂ (Set.range p) =
      (Algebra.adjoin ℂ (Set.range fun u => P.eval (algebraMap ℂ S u))).map S.val := by
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    exact congrArg (fun f => Algebra.adjoin ℂ (Set.range f)) (funext fun u => (hPe u).symm)

  let Xs : Submodule ℂ N := ⨆ g : (G : Set S), (Wsp.map ((g : S) : Module.End ℂ N) : Submodule ℂ N)
  haveI : FiniteDimensional ℂ Wsp := hfin
  have key : ∀ x ∈ Submodule.span R (G : Set S), ∀ t ∈ T, ((x : S) : Module.End ℂ N) (t v) ∈ Xs := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      intro t ht
      have h1 : t v ∈ Wsp := Submodule.subset_span ⟨t, ht, rfl⟩
      exact (le_iSup (fun g : (G : Set S) => (Wsp.map ((g : S) : Module.End ℂ N) : Submodule ℂ N)) ⟨g, hg⟩)
        (Submodule.mem_map_of_mem h1)
    | zero => intro t _; simp [Xs]
    | add x y _ _ ihx ihy =>
      intro t ht
      rw [Subalgebra.coe_add, LinearMap.add_apply]
      exact Xs.add_mem (ihx t ht) (ihy t ht)
    | smul a x _ ih =>
      intro t ht
      have e1 : (a • x : S) = x * (a : S) := by rw [Algebra.smul_def, mul_comm]; rfl
      rw [e1, Subalgebra.coe_mul, Module.End.mul_apply]
      have := ih _ (T.mul_mem (hRT a a.2) ht)
      rwa [Module.End.mul_apply] at this
  refine Submodule.finiteDimensional_of_le (S₂ := Xs) (Submodule.span_le.2 ?_)
  rintro _ ⟨a, ha, rfl⟩
  rw [hmap] at ha
  obtain ⟨x, hx, rfl⟩ := Subalgebra.mem_map.1 ha
  have hx' : x ∈ Submodule.span R (G : Set S) := by
    rw [hG]; exact (Subalgebra.mem_restrictScalars _).1 (hpB hx)
  have := key x hx' 1 T.one_mem
  simpa using this

end GlobalTheory.LeviHC
