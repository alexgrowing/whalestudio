import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem b_mem (hd : d.AxH 𝒜) (h : d.S1) (la : HeightOneSpectrum (𝓞 K)) (k : Fin d.del) (c : ι)
    (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (hw : w ∈ d.PlOver la c) :
    0 ≤ w (d.bvecG hd.sel hd.a4.choose k c) +
      ((d.ord c (d.Wres c w) d.wF (hd.a4.choose c) : ℤ) : WithTop ℤ) := by
  classical
  obtain ⟨he, -, -⟩ := hd.a4.choose_spec
  obtain ⟨heF, he0⟩ := he c
  have hadm := (d.admissible_over_prime hd h la c w hw).1
  have hthpF : d.thp (hd.sel k) c ∈ 𝒜 c d.wF := hd.thp_mem _ c
  obtain ⟨a, ha⟩ : ∃ a : Ω c, d.thp (hd.sel k) c = a • hd.a4.choose c := by
    have he0' : (⟨hd.a4.choose c, heF⟩ : 𝒜 c d.wF) ≠ 0 := by
      intro h0; exact he0 (congrArg Subtype.val h0)
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ he0').mp (hd.finrank_one c d.wF)
      ⟨_, hthpF⟩
    exact ⟨a, (congrArg Subtype.val ha).symm⟩
  have hb : d.bvecG hd.sel hd.a4.choose k c = algebraMap (Ω c) (OmS (Ω c) d.D d.N) a := by
    simp only [bvecG]
    rw [ValuationResidueLemmas.ratio_eq he0 ha]
  rw [hb]
  change 0 ≤ d.Wres c w a + _
  by_cases ha0 : a = 0
  · rw [ha0, AddValuation.map_zero, top_add]
    exact le_top
  have hth0 : d.thp (hd.sel k) c ≠ 0 := by
    rw [ha]; exact smul_ne_zero ha0 he0
  rw [← hd.ord_smul c _ hadm a heF he0 ha0, ← ha]
  have hmem : d.thp (hd.sel k) ∈ d.Thp := by
    rw [hd.Thp_span]; exact Submodule.subset_span ⟨_, rfl⟩
  exact_mod_cast hd.ord_nonneg_Thp c _ hadm _ hmem hth0

theorem b_linIndep (hd : d.AxH 𝒜) (h : d.S1) :
    letI : ∀ c, Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS h c).toAlgebra
    LinearIndependent (KTf K d.D d.N) (d.bvecG hd.sel hd.a4.choose) := by
  letI : ∀ c, Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS h c).toAlgebra
  classical
  obtain ⟨-, hind, -⟩ := hd.a4.choose_spec
  rw [Fintype.linearIndependent_iff]
  intro q hq
  obtain ⟨⟨s, hs⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples (nonZeroDivisors (KTp K d.D d.N)) Finset.univ q
  choose p hp using fun k => hint k (Finset.mem_univ k)
  have hsH : ∀ c (x : KTp K d.D d.N),
      d.sH c x = d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) x) := by
    intro c x
    rw [Data.KTtoS, IsFractionRing.lift_algebraMap]
    rfl
  have hzero : ∀ k, p k = 0 := hind p (fun c => by
    have hc := congrFun hq c
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at hc
    simp only [Algebra.smul_def] at hc
    calc ∑ k, d.sH c (p k) * algebraMap (Ω c) (OmS (Ω c) d.D d.N)
            (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c))
        = d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) s) *
            ∑ k, algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N) (q k) *
              d.bvecG hd.sel hd.a4.choose k c := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hsH, hp k, Algebra.smul_def, map_mul, mul_assoc]
          rfl
      _ = 0 := by rw [hc, mul_zero])
  intro k
  have hk := hp k
  rw [hzero k, map_zero, Algebra.smul_def] at hk
  exact (mul_eq_zero.mp hk.symm).resolve_left
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs)

theorem del_eq (hd : d.AxH 𝒜) (h : d.S1) :
    letI : ∀ c, Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS h c).toAlgebra
    d.del = ∑ c, Module.finrank (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
  Finset.sum_congr rfl fun c _ => (d.omS_finite hd h c).2.symm

end Data

end ReciprocityTheory.ChartRestriction.G.T0
