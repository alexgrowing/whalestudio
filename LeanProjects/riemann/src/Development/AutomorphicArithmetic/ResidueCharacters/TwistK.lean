import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightGoodReductionAtPrime
import Development.AutomorphicArithmetic.ResidueCharacters.TwistDef

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct GlobalTheory.TwistTors

namespace UpperTheory.N.TwistK

section

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

theorem tbe_of (PD : PeriodData G Qp K₀ K B BdR) (I : Subgroup G) [TopologicalSpace Qp] [CompactSpace G] [IsTopologicalGroup G]
    [IsTopologicalRing LL] (hO : GoodO (Qp := Qp) LL O)
    (hfin : ∀ n : ℕ, Finite (O ⧸ Ideal.span {((PD.p : ℕ) : O) ^ n}))
    (hp : ((PD.p : ℕ) : O) ≠ 0)
    (h5 : TateFilteredInvariants PD) (h7 : fontCore PD) (hbk : bkADim PD)
    (heul : ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Finite M] (a : G → M →+ M), (∀ m, a 1 m = m) →
      (∀ g h m, a (g * h) m = a g (a h m)) → (∀ m : M, PD.p ^ r • m = 0) →
      (∀ m, IsLocallyConstant fun g => a g m) →
      {c : G → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.Finite ∧
      {c : G → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.ncard ≤
        Nat.card M ^ (Module.finrank Qp K + 2))
    (hchi : ∀ e : ℕ, 0 < e → ∃ g : G, (PD.χ g : Qp) ^ e ≠ 1)
    (φ : G) (hφ : (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤)
    (δ : G → LL) (hδ : δ ∈ finiteCocycles PD (1 : Representation LL G LL))
    (hδI : ∀ g ∈ I, δ g = 0) (hδ0 : δ ≠ 0) : TBe PD LL O I := by
  intro e Ve h1 hχ
  obtain ⟨hDR, hFil⟩ := GlobalTheory.isDR_and_DdR_le_Fil_zero_of_twist PD Ve.ρ e hχ
  have hpos : 0 < e → HfD PD Ve.L = BD Ve.L ∧ BD Ve.L ≠ ⊥ := by
    intro he
    obtain ⟨g, hg1⟩ := hchi e he
    have hu : ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e ≠ 1 := by
      rw [inv_pow, Ne, inv_eq_one, ← map_pow, map_eq_one_iff _ (algebraMap Qp LL).injective]
      exact hg1
    exact ⟨HfD_eq_BD PD Ve (GlobalTheory.HfZero.z1f_le_b1 PD h5 h7 hO (toG Ve) hDR hFil
      (fixed_points_trivial_of_scalar_action_ne_one Ve _ _ hu (hχ _))), BD_ne_bot hO Ve h1 _ _ hu (hχ _)⟩
  have hzero : e = 0 → HfD PD Ve.L ≠ ⊥ ∧ ∀ c : G → Ve.V ⧸ Ve.L.T, c ∈ HfD PD Ve.L ↔
      (c ∈ divisibleCocycles Ve.L ∧ ∃ x, ∀ g ∈ I, c g = actD Ve.L g x - x) := by
    rintro rfl
    simp only [pow_zero, one_smul] at hχ
    have htop : H0V Ve.ρ = ⊤ := by
      rw [eq_top_iff]
      intro x _
      refine (Submodule.mem_iInf _).2 fun g => ?_
      rw [LinearMap.mem_ker, LinearMap.sub_apply, hχ, LinearMap.id_apply, sub_self]
    have hdim : ((Module.finrank LL (FiniteCohomology PD Ve.ρ) : ℕ) : ℤ) =
        Module.finrank LL ↥(H0V Ve.ρ) + ((Module.finrank LL ↥(DdR PD Ve.ρ) : ℤ) -
          Module.finrank LL ↥(DdR PD Ve.ρ ⊓ FilV PD (LL := LL) (V := Ve.V) 0)) :=
      hbk _ _ hO (toG Ve) hDR
    rw [inf_eq_left.2 hFil, sub_self, add_zero, htop, finrank_top, h1] at hdim
    exact GlobalTheory.UnramifiedClasses.HfD_eq_unramified PD hO Ve h1 hχ (by exact_mod_cast hdim) I φ hφ δ hδ hδI hδ0
  refine ⟨fun n => ?_, fun he => (hpos he).1, fun he => (hzero he).2⟩
  have hne : HfD PD Ve.L ≠ ⊥ := by
    rcases Nat.eq_zero_or_pos e with he | he
    · exact (hzero he).1
    · rw [(hpos he).1]; exact (hpos he).2
  haveI := hfin n
  haveI : IsDomain O := hO.1.1
  have key := len_part PD hO Ve h1 PD.p n (Module.finrank Qp K) (pow_ne_zero n hp)
    (heul n) hne
  have hord : Module.length O (O ⧸ Ideal.span {((PD.p : ℕ) : O) ^ n}) =
      n • Module.length O (O ⧸ Ideal.span {((PD.p : ℕ) : O)}) :=
    Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hp) n
  unfold lenOl
  rw [Nat.cast_mul, mul_assoc, ← nsmul_eq_mul n, ← hord]
  exact key

end

theorem tbe_all (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (hA : admitted D HW F) (hB : Conclusion5 D)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) : TBe ((D.loc l).PD K) ↥LL.1 ↥(OL LL) (IK K) := by
  obtain ⟨-, hA2, -, hA4, hA5, -, hA7, -, -⟩ := hA
  obtain ⟨hO, hfin⟩ := GlobalTheory.LocalIntegers.good_integers l LL
  haveI := K.2
  haveI hc : CompactSpace ↥(GK K) :=
    isCompact_iff_compactSpace.1 (IntermediateField.fixingSubgroup_isClosed K.1).isCompact
  obtain ⟨φ, hφ⟩ := GlobalTheory.exists_topologicalClosure_zpowers_sup_inertia l K
  obtain ⟨δ, hδ, hδI, hδ0⟩ := exists_unr D l K LL
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  haveI : IsTopologicalRing ↥LL.1 := hO.2.2.2.1
  refine tbe_of _ _ hO ?_ ?_ (hA5 l K) (hA7 l K) (hB l K).2.1 ?_ ?_ φ hφ δ hδ hδI hδ0
  · rw [hp]; exact hfin
  · rw [hp]; exact hl0
  · rw [hp]; exact GlobalTheory.CocycleCount.cocycles_finite_ncard_le hA2 hA4 l K
  · intro e he
    obtain ⟨g, hg, hg1⟩ := GlobalTheory.Cyc.exists_mem_GK_chi_pow_ne_one l (D.loc l).χQ (D.loc l).χQ_cyc K e he
    refine ⟨⟨g, hg⟩, ?_⟩
    rw [(D.loc l).PD_χ K ⟨g, hg⟩]
    exact hg1

end UpperTheory.N.TwistK

end
