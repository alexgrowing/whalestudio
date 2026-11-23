import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.IsDualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ZhatFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.DecZhat
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoboundaryCriterion
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RootEquality

noncomputable section

namespace UpperTheory.V.Pa

section Abstract

variable {R G M : Type} [CommRing R] [Group G] [AddCommGroup M] [Module R M] (ρ : Representation R G M)

private theorem degree_inverse {l n : ℕ} (hn : n.Coprime l) (hl : ∀ m : M, l • m = 0) :
    ∃ a : ℤ, ∀ m : M, a • (n • m) = m := by
  refine ⟨Nat.gcdA n l, fun m => ?_⟩
  have e : (1 : ℤ) = n * Nat.gcdA n l + l * Nat.gcdB n l := by
    have := Nat.gcd_eq_gcd_ab n l
    rwa [hn.gcd_eq_one, Nat.cast_one] at this
  have h0 : (l : ℤ) • m = 0 := by rw [natCast_zsmul, hl]
  calc Nat.gcdA n l • (n • m) = ((n : ℤ) * Nat.gcdA n l) • m + ((l : ℤ) * Nat.gcdB n l) • m := by
        rw [mul_comm (l : ℤ), mul_smul (Nat.gcdB n l), h0, smul_zero, add_zero, mul_comm, mul_smul, natCast_zsmul]
    _ = m := by rw [← add_smul, ← e, one_smul]

private theorem isCoboundary_of_coprime {l : ℕ} {H C : Type} [Group H] [Group C] [Finite C] (i : H →* G) (f : H →* C)
    (hC : (Nat.card C).Coprime l) (hl : ∀ m : M, l • m = 0) (z : G → M)
    (hz : ∀ g h, z (g * h) = z g + ρ g (z h)) (h0 : ∀ u, f u = 1 → z (i u) = 0) :
    ∃ b, ∀ u, z (i u) = ρ (i u) b - b :=
  _root_.UpperTheory.Reformulated.B.CoboundaryCriterion.isCoboundary_of_coprime _ i f hC hl z hz h0

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [Finite M]

private theorem degree_eval (I : Subgroup G) [hI : I.Normal] (φ : G) (hρ : LC ρ)
    (hd : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hc : ∀ n : ℕ, 0 < n → ∃ d : G →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1) :
    Nat.card {z // z ∈ Zl ρ ∧ ∀ u ∈ I, z u = 0} = Nat.card {m // ∀ u ∈ I, ρ u m = m} := by
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  haveI : ContinuousConstSMul R M := ⟨fun _ => continuous_of_discreteTopology⟩
  have key := AlgebraTools.zhatFin R G M ρ I φ
    (continuous_prod_of_discrete_right.2 fun m => (hρ m).continuous)
    (by rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, hd, Subgroup.coe_top])
    (fun k hk => by
      obtain ⟨d, d1, d2, d3⟩ := hc k hk
      exact ⟨d, d1.isOpen_fiber 1, d2, d3⟩)
  have val : ∀ z, z ∈ Zl ρ → (∀ u ∈ I, z u = 0) → ∀ u ∈ I, ρ u (z φ) = z φ := fun z hz h0 u hu => by
    have e1 := hz.2 u φ
    have e2 := hz.2 φ (φ⁻¹ * u * φ)
    rw [h0 _ (hI.conj_mem' u hu φ), map_zero, add_zero, show φ * (φ⁻¹ * u * φ) = u * φ by group, e1, h0 u hu,
      zero_add] at e2
    exact e2
  refine Nat.card_eq_of_bijective (fun z => ⟨z.1 φ, val z.1 z.2.1 z.2.2⟩) ⟨fun x y e => ?_, fun m => ?_⟩
  · have e' : x.1 φ = y.1 φ := congrArg Subtype.val e
    have := (key _ (val x.1 x.2.1 x.2.2)).unique
      (y₁ := ⟨x.1, x.2.1.1.continuous, x.2.1.2⟩) (y₂ := ⟨y.1, y.2.1.1.continuous, y.2.1.2⟩)
      ⟨x.2.2, rfl⟩ ⟨y.2.2, e'.symm⟩
    exact Subtype.ext (Subtype.mk.inj this)
  · obtain ⟨z, ⟨z1, z2⟩, -⟩ := key m.1 m.2
    exact ⟨⟨z.1, ⟨(IsLocallyConstant.iff_continuous _).2 z.2.1, z.2.2⟩, z1⟩, Subtype.ext z2⟩

end Abstract

private theorem degree_count₂ (l : ℕ) {G C : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [Group C] [Finite C] (χ : G →* C) (hC : (Nat.card C).Coprime l) (I : Subgroup G) [I.Normal] (φ : G)
    (hd : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hc : ∀ n : ℕ, 0 < n → ∃ d : G →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1) :
    UnrCount l G (I ⊓ χ.ker) := by
  intro R M _ _ _ _ ρ hρ hl hJ
  let Z : AddSubgroup (G → M) :=
    { carrier := {z | z ∈ Zl ρ ∧ ∀ g ∈ I ⊓ χ.ker, z g = 0}
      add_mem' := fun x y => ⟨add_mem x.1 y.1, fun g hg => by rw [Pi.add_apply, x.2 g hg, y.2 g hg, add_zero]⟩
      zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩
      neg_mem' := fun x => ⟨neg_mem x.1, fun g hg => by rw [Pi.neg_apply, x.2 g hg, neg_zero]⟩ }
  let res : Z →+ (I → M) := AddMonoidHom.mk' (fun z u => z.1 u) fun _ _ => rfl
  let δ : M →+ (I → M) := AddMonoidHom.mk' (fun b u => ρ u b - b) fun x y => funext fun u => by
    simp only [map_add, Pi.add_apply]; abel
  have rng : res.range = δ.range := by
    ext w
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨b, hb⟩ := isCoboundary_of_coprime ρ I.subtype (χ.comp I.subtype) hC hl z.1 z.2.1.2
        fun u hu => z.2.2 u ⟨u.2, hu⟩
      exact ⟨b, funext fun u => (hb u).symm⟩
    · rintro ⟨b, rfl⟩
      refine ⟨⟨fun g => ρ g b - b, ⟨(hρ b).comp (· - b), fun g h => ?_⟩, fun g hg => ?_⟩, rfl⟩
      · simp only [map_mul, Module.End.mul_apply, map_sub]; abel
      · simp only [hJ g hg, Module.End.one_apply, sub_self]
  have k1 : Nat.card res.ker = Nat.card {z // z ∈ Zl ρ ∧ ∀ u ∈ I, z u = 0} :=
    Nat.card_congr
      { toFun := fun z => ⟨z.1.1, z.1.2.1, fun u hu => congrFun z.2 ⟨u, hu⟩⟩
        invFun := fun z => ⟨⟨z.1, z.2.1, fun g hg => z.2.2 g hg.1⟩, funext fun u => z.2.2 u u.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have k2 : Nat.card δ.ker = Nat.card {m // ∀ u ∈ I, ρ u m = m} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun m =>
      ⟨fun h u hu => sub_eq_zero.1 (congrFun h ⟨u, hu⟩), fun h => funext fun u => sub_eq_zero.2 (h u u.2)⟩)
  have tot : Nat.card Z = Nat.card M := by
    rw [← res.ker.card_mul_index, ← δ.ker.card_mul_index, AddSubgroup.index_ker, AddSubgroup.index_ker, rng, k1, k2,
      degree_eval ρ I φ hρ hd hc]
  have fin : Finite Z := Nat.finite_of_card_ne_zero (tot ▸ (Nat.card_pos (α := M)).ne')
  exact ⟨Set.toFinite (Z : Set (G → M)), tot⟩

theorem unrBare : ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (C : Type) [CommGroup C] [Finite C] (χ : ReciprocityTheory.Gal.Dec (F := F) A →* C), Formalism.ConjugateSelfDual.IsPlaceOver A v →
    IsOpen (χ.ker : Set (ReciprocityTheory.Gal.Dec (F := F) A)) → (Nat.card C).Coprime l →
    UnrCount l (ReciprocityTheory.Gal.Dec (F := F) A) ((ReciprocityTheory.Gal.Ine A).subgroupOf (ReciprocityTheory.Gal.Dec A) ⊓ χ.ker) :=
  _root_.UpperTheory.Reformulated.B.RootEquality.unrBare

end UpperTheory.V.Pa
