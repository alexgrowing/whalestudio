import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSysFFMemFinitePerpProj
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMulIsIntegralChart
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIntegrallyClosedStalkOfRingOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAffineOpenRingOnEqAdjoinInv

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem finite_over_subfield_of_le {Ω : Type} [Field Ω] {K L : Subfield Ω} (h : K ≤ L)
    (hK : Module.Finite K Ω) : Module.Finite L Ω := by
  letI : Algebra K L := (Subfield.inclusion h).toAlgebra
  haveI : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite K L Ω

theorem exists_normal_proj_hasDiv_family (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (J : Type) [Fintype J] (t : J → Ω) (ht : ∃ i, t i ≠ 0)
    (hfin : Module.Finite
      (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i})) Ω)
    (B : Type) [Finite B] (JJ : B → Type) [∀ b, Finite (JJ b)] (tt : ∀ b, JJ b → Ω)
    (htt : ∀ b, ∃ k, tt b k ≠ 0) :
    ∃ M : RatModel o Ω, IsNormalScheme M.Z ∧ IsProjOver M.s ∧ M.HasDiv t ∧ ∀ b, M.HasDiv (tt b) := by
  haveI := ArithBase.ded (o := o) (Ω := Ω)
  haveI := ArithBase.char (o := o) (Ω := Ω)
  letI : Fintype B := Fintype.ofFinite B
  letI : Fintype (∀ b, JJ b) := Fintype.ofFinite _
  choose q₀ hq₀ using htt
  have hP : (∏ b, tt b (q₀ b)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => hq₀ b
  obtain ⟨i₀, hi₀⟩ := ht
  obtain ⟨M, hM, hp⟩ := GlobalTheory.ZH.exists_isNm_isProjOver o Ω (ArithBase.inj (o := o) (Ω := Ω))
    (J × ∀ b, JJ b) (fun q => t q.1 * ∏ b, tt b (q.2 b)) ⟨(i₀, q₀), mul_ne_zero hi₀ hP⟩
    (finite_over_subfield_of_le (Subfield.closure_mono (Set.union_subset_union_right _ (by
      rintro _ ⟨i, j, rfl⟩
      exact ⟨(i, q₀), (j, q₀), (mul_div_mul_right _ _ hP).symm⟩))) hfin)
  have h := GlobalTheory.ZH.isNm_normal_and_div_prod o Ω M J t
  have h2 : M.HasDiv t ∧ M.HasDiv (fun q : ∀ b, JJ b => ∏ b, tt b (q b)) := by
    refine ⟨fun z => ?_, fun z => ?_⟩
    · obtain ⟨⟨i, q⟩, hi⟩ := hM.1 z
      exact ⟨i, ((h.2.1 _ (fun q : ∀ b, JJ b => ∏ b, tt b (q b)) i q z).1 hi).1⟩
    · obtain ⟨⟨i, q⟩, hi⟩ := hM.1 z
      exact ⟨q, ((h.2.1 _ (fun q : ∀ b, JJ b => ∏ b, tt b (q b)) i q z).1 hi).2⟩
  exact ⟨M, (GlobalTheory.ZH.isNm_normal_and_div_prod o Ω M _ _).1 hM, hp, h2.1, (h.2.2 B JJ tt).1 h2.2⟩

theorem exists_admissible_affine_model_dividing_tuple : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (J₀ : Type) [Fintype J₀] (t₀ : J₀ → Ω), (∃ i, t₀ i ≠ 0) → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j : S.Gam × J₀, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)})) Ω → ∃ (M : RatModel o Ω) (U₀ : M.Z.Opens), S.admitted M U₀ ∧ IsAffineOpen U₀ ∧ M.HasDiv t₀ := by
  intro o Ω _ _ _ _ S J₀ _ t₀ ht₀ hfin
  have hN : S.N ≠ 0 := by have := S.N_ge; omega
  have hr : S.r ≠ 0 := by have := S.r_pos; omega
  haveI : NeZero S.N := ⟨hN⟩
  haveI : NeZero (S.r * S.N) := ⟨mul_ne_zero hr hN⟩
  haveI : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (mul_ne_zero hr hN)⟩
  haveI : Finite (AddSubgroup S.Gam) := Finite.of_injective _ SetLike.coe_injective
  haveI : ∀ T : AddSubgroup S.Gam, Finite (T →+ ZMod S.N) := fun T =>
    Finite.of_injective _ DFunLike.coe_injective
  obtain ⟨x₀, hx₀⟩ := S.th_ne
  obtain ⟨i₀, hi₀⟩ := ht₀
  obtain ⟨M, hn, hp, hd, hF⟩ := exists_normal_proj_hasDiv_family o Ω (S.Gam × J₀)
    (fun q => S.th q.1 * t₀ q.2) ⟨(x₀, i₀), mul_ne_zero hx₀ hi₀⟩ hfin
    {b : Σ T : AddSubgroup S.Gam, T →+ ZMod S.N // S.FF b.1 b.2 ≠ 0}
    (fun b => S.J × (b.1.1 → ZMod ((S.r * S.N) ^ 2))) (fun b => S.FF b.1.1 b.1.2)
    (fun b => Function.ne_iff.1 b.2)
  have h := GlobalTheory.ZH.isNm_normal_and_div_prod o Ω M _ S.th
  have hth : M.HasDiv S.th := fun z => by
    obtain ⟨⟨x, i⟩, hi⟩ := hd z
    exact ⟨x, ((h.2.1 _ t₀ x i z).1 hi).1⟩
  have ht : M.HasDiv t₀ := fun z => by
    obtain ⟨⟨x, i⟩, hi⟩ := hd z
    exact ⟨i, ((h.2.1 _ t₀ x i z).1 hi).2⟩
  have hA : ((fun x : Ω => x⁻¹) '' (Set.range S.th ∪ {x : Ω | ∃ T c k, x = S.FF T c k})).Finite :=
    ((Set.finite_range _).union (GlobalTheory.thetaSys_FF_mem_finite_perp_proj o Ω S).2.1).image _
  obtain ⟨U₀, a, -, hne, haff, -, -, hR, hsub⟩ := GlobalTheory.ZH.exists_affineOpen_ringOn_eq_adjoin_inv o Ω M S.R _
    S.fg S.frac hA ⊤ ⟨genericPoint M.Z, trivial⟩
  refine ⟨M, U₀, ⟨⟨hn, hp, hth, hne, fun x hx => ?_, fun x _ => hsub ⟨_, Or.inl ⟨x, rfl⟩, rfl⟩,
    fun T c k _ _ => hsub ⟨_, Or.inr ⟨T, c, k, rfl⟩, rfl⟩⟩, fun T c _ h0 => hF ⟨⟨T, c⟩, h0⟩⟩, haff, ht⟩
  rw [hR]
  exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)

end GlobalTheory.ZH
