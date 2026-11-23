import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineCyclotomicLevelOfFinrankInvariants

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

namespace GlobalTheory.NL.FiniteRestrictionH1f

theorem coboundary_of_finiteIndex {G M k : Type} [Group G] [Field k] [CharZero k] [AddCommGroup M]
    [Module k M] (a : G → M →ₗ[k] M) (ha : ∀ g h x, a (g * h) x = a g (a h x))
    (H : Subgroup G) [H.FiniteIndex] (c : G → M) (hc : ∀ g h, c (g * h) = c g + a g (c h))
    (b : M) (hb : ∀ h ∈ H, c h = a h b - b) : ∃ x : M, ∀ g, c g = a g x - x := by
  classical
  let d : G → M := fun g => c g - (a g b - b)
  have hd : ∀ g h, d (g * h) = d g + a g (d h) := by
    intro g h
    simp only [d, hc, ha, map_sub]
    abel
  have hd0 : ∀ h ∈ H, d h = 0 := fun h hh => by simp only [d, hb h hh, sub_self]
  have hdH : ∀ g g' : G, (QuotientGroup.leftRel H) g g' → d g = d g' := by
    intro g g' hgg
    rw [QuotientGroup.leftRel_apply] at hgg
    have : g' = g * (g⁻¹ * g') := by group
    rw [this, hd, hd0 _ hgg, map_zero, add_zero]
  let D : G ⧸ H → M := fun q => Quotient.liftOn' q d hdH
  have hD : ∀ (g : G) (q : G ⧸ H), D (g • q) = d g + a g (D q) := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H x => exact hd g x
  let _inst : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hn : ((Fintype.card (G ⧸ H) : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hsum : ∀ g : G, ∑ q, D q = ((Fintype.card (G ⧸ H) : ℕ) : k) • d g + a g (∑ q, D q) := by
    intro g
    rw [← Equiv.sum_comp (MulAction.toPerm g) D]
    conv_rhs => rw [Equiv.sum_comp (MulAction.toPerm g) D]
    simp only [MulAction.toPerm_apply, hD, Finset.sum_add_distrib, map_sum, Finset.sum_const,
      Finset.card_univ, Nat.cast_smul_eq_nsmul]
  refine ⟨b - (((Fintype.card (G ⧸ H) : ℕ) : k))⁻¹ • ∑ q, D q, fun g => ?_⟩
  have h1 : d g = (((Fintype.card (G ⧸ H) : ℕ) : k))⁻¹ • (∑ q, D q - a g (∑ q, D q)) := by
    rw [← eq_sub_iff_add_eq.2 (hsum g).symm, smul_smul, inv_mul_cancel₀ hn, one_smul]
  have h2 : c g = d g + (a g b - b) := by simp only [d]; abel
  rw [h2, h1, map_sub, map_smul, smul_sub]
  abel

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem actVB_tmul (g : G) (x : V) (b : B) :
    actVB PD ρ g (x ⊗ₜ[Qp] b) = ρ g x ⊗ₜ[Qp] PD.actB g b := rfl

theorem actVB_mul (g h : G) (x : V ⊗[Qp] B) :
    actVB PD ρ (g * h) x = actVB PD ρ g (actVB PD ρ h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp only [actVB_tmul, map_mul]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem crisCob_of_finiteIndex [CharZero LL] (H : Subgroup G) [H.FiniteIndex] (c : G → V)
    (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (b : V ⊗[Qp] B)
    (hb : ∀ h ∈ H, c h ⊗ₜ[Qp] (1 : B) = actVB PD ρ h b - b) :
    ∃ x : V ⊗[Qp] B, ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x :=
  coboundary_of_finiteIndex (actVB PD ρ) (actVB_mul PD ρ) H (fun g => c g ⊗ₜ[Qp] (1 : B))
    (fun g h => by simp only [hc, add_tmul, actVB_tmul, map_one]) b hb

end Generic

section Classes

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O]
    [Algebra O LL] [TopologicalSpace LL] (T : LocLat G Qp LL O)

theorem mem_H1fT_iff_res [CharZero LL] (H : Subgroup G) [H.FiniteIndex] (κ : LatticeCohomology T.L) :
    κ ∈ latticeFiniteCohomology PD T.L ↔ ∃ c : ↥(latticeCocycles (resLat T H)),
      (∃ x : T.V ⊗[Qp] B, ∀ h : ↥H,
        (c : ↥H → T.V) h ⊗ₜ[Qp] (1 : B) = actVB PD T.ρ (h : G) x - x) ∧
      Submodule.Quotient.mk c = resH1 T H κ := by
  constructor
  · rintro ⟨z, ⟨-, -, x, hx⟩, rfl⟩
    exact ⟨⟨resFun T H z, resFun_Z1T T H z z.2⟩, ⟨x, fun h => hx (h : G)⟩, rfl⟩
  · rintro ⟨c, ⟨x, hx⟩, hc⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
    have hc' : (Submodule.Quotient.mk c : LatticeCohomology (resLat T H)) =
        Submodule.Quotient.mk ⟨resFun T H z, resFun_Z1T T H z z.2⟩ := hc
    obtain ⟨y, -, hy⟩ := (Submodule.Quotient.eq _).1 hc'
    refine ⟨z, ⟨z.2, z.2.1, ?_⟩, rfl⟩
    refine crisCob_of_finiteIndex PD T.ρ H z z.2.1.2 (x - y ⊗ₜ[Qp] (1 : B)) fun h hh => ?_
    have h1 : T.ρ h y - y = (c : ↥H → T.V) ⟨h, hh⟩ - (z : G → T.V) h := congrFun hy ⟨h, hh⟩
    have h2 : (z : G → T.V) h = (c : ↥H → T.V) ⟨h, hh⟩ - (T.ρ h y - y) := by rw [h1]; abel
    rw [h2, sub_tmul, sub_tmul, hx ⟨h, hh⟩, map_sub, actVB_tmul, map_one]
    abel

end Classes

theorem GKs_finiteIndex {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (n : ℕ)
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) : W.GKs.FiniteIndex := by
  have h1 : W.GKs = (GlobalTheory.Cyc.Gj K W.s).subgroupOf (GK K) := by
    ext x
    rw [GlobalTheory.Cyc.mem_GKs_iff_mem_Gj, Subgroup.mem_subgroupOf]
  have h2 : (GlobalTheory.Cyc.Gj K W.s).FiniteIndex := by
    have hlp : l.Prime := Fact.out
    constructor
    rw [GlobalTheory.Cyc.Gj, ← IntermediateField.finrank_eq_fixingSubgroup_index,
      GlobalTheory.Cyc.finrank_Ks K W.s W.s_pos]
    have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    have : FiniteDimensional ℚ_[l] ↥(K0 K) :=
      FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
        (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
    exact (Nat.mul_pos Module.finrank_pos
      (Nat.mul_pos (Nat.sub_pos_of_lt hlp.one_lt) (pow_pos hlp.pos _))).ne'
  rw [h1]
  infer_instance

end GlobalTheory.NL.FiniteRestrictionH1f
