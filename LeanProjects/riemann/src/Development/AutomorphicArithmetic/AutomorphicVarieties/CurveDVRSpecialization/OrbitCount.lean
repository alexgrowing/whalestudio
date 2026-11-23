import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V
open scoped Pointwise

private theorem orbit_count {G X V : Type} [Group G] [MulAction G X] [Fintype V] (U : Subgroup G) [U.Normal]
    (hU : U.index ≠ 0) (b : X) (p : V → X) (h1 : ∀ v, ∃ γ : G, p v = γ • b)
    (h2 : ∀ g : G, ∃! v, ∃ u ∈ U, g • b = u • p v) :
    ∑ v, U.relIndex (MulAction.stabilizer G (p v)) = U.index := by
  classical
  have hN : U.Normal := inferInstance
  have conj_eq : ∀ γ : G, U.map (MulAut.conj γ).toMonoidHom = U := by
    intro γ
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hN.conj_mem y hy γ
    · intro hx
      refine ⟨γ⁻¹ * x * γ, ?_, ?_⟩
      · simpa using hN.conj_mem x hx γ⁻¹
      · simp [mul_assoc]
  have hrel : ∀ v, U.relIndex (MulAction.stabilizer G (p v)) =
      U.relIndex (U ⊔ MulAction.stabilizer G b) := by
    intro v
    obtain ⟨γ, hγ⟩ := h1 v
    rw [hγ, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    have e := Subgroup.relIndex_map_map (MulAut.conj γ).toMonoidHom U (MulAction.stabilizer G b)
    rw [conj_eq γ] at e
    have hker : (MulAut.conj γ).toMonoidHom.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff _).mpr (MulEquiv.injective _)
    rw [e, hker, sup_bot_eq, sup_bot_eq, Subgroup.relIndex_sup_left]
  choose γ hγ using h1
  let F : V → G ⧸ (U ⊔ MulAction.stabilizer G b) := fun v => QuotientGroup.mk (γ v)
  have inj : Function.Injective F := by
    intro v w hvw
    have hm : (γ v)⁻¹ * γ w ∈ U ⊔ MulAction.stabilizer G b := QuotientGroup.eq.mp hvw
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at hm
    obtain ⟨a, ha, c, hc, hac⟩ := hm
    have hac' : a * c = (γ v)⁻¹ * γ w := hac
    have hw : γ w = γ v * a * c := by
      rw [mul_assoc, hac', mul_inv_cancel_left]
    have h₁ : γ w • b = (γ v * a * (γ v)⁻¹) • p v := by
      rw [hw, hγ v, mul_smul, MulAction.mem_stabilizer_iff.mp hc, ← mul_smul, inv_mul_cancel_right]
    have h₂ : γ w • b = (1 : G) • p w := by rw [one_smul, hγ w]
    have hu : γ v * a * (γ v)⁻¹ ∈ U := hN.conj_mem a ha (γ v)
    exact (h2 (γ w)).unique ⟨_, hu, h₁⟩ ⟨1, U.one_mem, h₂⟩
  have surj : Function.Surjective F := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨v, ⟨u, hu, e⟩, -⟩ := h2 g
      refine ⟨v, QuotientGroup.eq.mpr ?_⟩
      have hsplit : (γ v)⁻¹ * g = ((γ v)⁻¹ * u * γ v) * ((γ v)⁻¹ * u⁻¹ * g) := by group
      rw [hsplit]
      refine Subgroup.mul_mem_sup ?_ ?_
      · simpa using hN.conj_mem u hu (γ v)⁻¹
      · rw [MulAction.mem_stabilizer_iff]
        rw [hγ v] at e
        simp only [mul_smul, e, inv_smul_smul]
  have hcard : Fintype.card V = (U ⊔ MulAction.stabilizer G b).index := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_eq_of_bijective F ⟨inj, surj⟩
  rw [Finset.sum_congr rfl (fun v _ => hrel v), Finset.sum_const, Finset.card_univ, smul_eq_mul,
    hcard, mul_comm, Subgroup.relIndex_mul_index le_sup_left]

private theorem upl_normal (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (L : Type) [Field L] [NumberField L]
    [Algebra L Ω] [IsAbelianGalois ℚ L] : (upl Ω L).Normal := by
  unfold upl
  constructor
  intro n hn g x hx
  obtain ⟨y, hy, hy'⟩ : ∃ y ∈ maximalRealSubfield L, g⁻¹ (algebraMap L Ω x) = algebraMap L Ω y := by
    refine ⟨((g⁻¹ : Ω ≃ₐ[ℚ] Ω).toAlgHom.restrictNormal L) x, ?_, ?_⟩
    · intro φ
      exact hx (φ.comp ((g⁻¹ : Ω ≃ₐ[ℚ] Ω).toAlgHom.restrictNormal L).toRingHom)
    · exact (AlgHom.restrictNormal_commutes (g⁻¹ : Ω ≃ₐ[ℚ] Ω).toAlgHom L x).symm
  have hn' := hn y hy
  show (g * n * g⁻¹) (algebraMap L Ω x) = algebraMap L Ω x
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hy', hn', ← hy', ← AlgEquiv.mul_apply, mul_inv_cancel,
    AlgEquiv.one_apply]

private theorem cycMod_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ l) {s : G ℚ Ω} (hs : s ζ = ζ) : cycMod ℚ Ω l 1 s = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  unfold cycMod cycZ
  ext
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_one]
  change PadicInt.toZModPow 1 ((cyclotomicCharacter Ω l) ((MulSemiringAction.toRingAut (G ℚ Ω) Ω) s)).val = 1
  rw [cyclotomicCharacter.toZModPow]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have hl1 : l ^ 1 ≠ 1 := by rw [pow_one]; exact hl.out.one_lt.ne'
  rw [ZMod.val_one'' hl1, pow_one]
  rw [pow_one] at ht
  obtain ⟨i, -, e⟩ := (hζ.isUnit_unit hl.out.ne_zero).eq_pow_of_mem_rootsOfUnity ht
  rw [← e]
  simp [hs]

private theorem val_smul {Ω : Type} [Field Ω] [CharZero Ω] (g : G ℚ Ω) (B : ValuationSubring Ω) (n : ℕ)
    (h : B.valuation (n : Ω) < 1) : (g • B).valuation (n : Ω) < 1 := by
  have key : ∀ (A : ValuationSubring Ω) (x : Ω), x ≠ 0 → (A.valuation x < 1 ↔ x⁻¹ ∉ A) := by
    intro A x hx
    rw [← A.valuation_le_one_iff, not_le, Valuation.one_lt_val_iff _ (inv_ne_zero hx), inv_inv]
  by_cases hn : (n : Ω) = 0
  · rw [hn]
    generalize g • B = C
    haveI : Nontrivial C.ValueGroup := ValuationRing.instNontrivialValueGroup C Ω
    rw [map_zero]
    exact zero_lt_one
  rw [key _ _ hn] at h ⊢
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, map_inv₀, map_natCast]
  exact h

set_option maxHeartbeats 400000 in
theorem UpperTheory.V.Pr.degEq :
    UpperTheory.V.Pr.DegEq := by
  unfold UpperTheory.V.Pr.DegEq
  intro Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M hL L _ _ _ _ _ Φ k a
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAbelianGalois ℚ L := k.ab
  haveI : (upl Ω L).Normal := upl_normal Ω L
  refine ⟨?_, ?_⟩
  · have hgal : galOf ℚ (W.Lp L) Ω = upl Ω L := by
      ext s
      unfold galOf upl
      constructor
      · intro h x hx
        exact h ⟨x, hx⟩
      · intro h x
        exact h x.1 x.2
    have hidx : (upl Ω L).index = Module.finrank ℚ (W.Lp L) := by
      rw [← hgal]
      exact (galEmbTop ℚ (W.Lp L) Ω).2.2
    rw [← hidx]
    unfold Fr.Frame.d
    rw [Finset.sum_congr rfl (fun v _ => k.dv v)]
    refine orbit_count (upl Ω L) (by rw [hidx]; exact Module.finrank_pos.ne') B k.pl ?_ ?_
    · intro v
      obtain ⟨γ, -, h⟩ := k.pl_conj v
      exact ⟨γ, h⟩
    · intro g
      exact k.pl_all (g • B) (val_smul g B l hL.atl)
  · rintro ⟨ζ, hζ⟩
    obtain ⟨g, hg⟩ := k.mu a
    apply hg
    have hsD : ((k.j a g : upl Ω L) : G ℚ Ω) ∈ Dec (k.pl a) := (k.j_range a _).mp ⟨g, rfl⟩
    obtain ⟨γ, -, hγ⟩ := k.pl_conj a
    have hM : B.valuation (M : Ω) < 1 := by
      obtain ⟨t, ht⟩ := hL.dvd
      have h1 : B.valuation ((N * t : ℕ) : Ω) ≤ 1 := (B.valuation_le_one_iff _).mpr (natCast_mem B _)
      rw [ht, mul_assoc, Nat.cast_mul, map_mul]
      calc B.valuation (l : Ω) * B.valuation ((N * t : ℕ) : Ω) ≤ B.valuation (l : Ω) :=
            mul_le_of_le_one_right' h1
        _ < 1 := hL.atl
    have hM' : (k.pl a).valuation (M : Ω) < 1 := by
      rw [hγ]
      exact val_smul γ B M hM
    have hker : ((k.j a g : upl Ω L) : G ℚ Ω) ∈ η.ker :=
      k.split (k.pl a) hM' (Subgroup.mem_inf.mpr ⟨hsD, (k.j a g).2⟩)
    have hfix : ((k.j a g : upl Ω L) : G ℚ Ω) ∈ galOf ℚ L Ω := by
      rw [k.gal]
      exact Subgroup.mem_inf.mpr ⟨(k.j a g).2, hker⟩
    unfold galOf at hfix
    exact cycMod_one l (hζ.map_of_injective (algebraMap L Ω).injective) (hfix ζ)
