import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private def SJ {R D M : Type} [CommRing R] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module R M]
    (ρ : Representation R D M) (J : Subgroup D) : Submodule R (D → M) where
  carrier := {z | z ∈ Zl ρ ∧ ∀ g ∈ J, z g = 0}
  add_mem' a b := ⟨add_mem a.1 b.1, fun g hg => by rw [Pi.add_apply, a.2 g hg, b.2 g hg, add_zero]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩
  smul_mem' c x a := ⟨Submodule.smul_mem _ c a.1, fun g hg => by rw [Pi.smul_apply, a.2 g hg, smul_zero]⟩

private theorem card_step {R A B C : Type} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup C] [Module R C]
    [Finite B] [Finite C] (f : A →ₗ[R] C) (i : LinearMap.ker f → B) (hi : Function.Injective i) :
    Finite A ∧ Nat.card A ≤ Nat.card B * Nat.card C := by
  haveI : Finite (LinearMap.ker f) := Finite.of_injective i hi
  have h : Nat.card A = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
    rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f), Nat.card_congr f.quotKerEquivRange.toEquiv]
  refine ⟨Nat.finite_of_card_ne_zero (h ▸ mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'), ?_⟩
  rw [h]
  exact Nat.mul_le_mul (Nat.card_le_card_of_injective i hi) (Nat.card_le_card_of_injective _ Subtype.val_injective)

theorem UpperTheory.V.Th.unrDev :
    ∀ (l : ℕ) [Fact l.Prime] (D : Type) [Group D] [TopologicalSpace D] (J : Subgroup D), UnrCount l D J → UnrCnt l D J := by
  intro l _ D _ _ J hU k R
  induction k with
  | zero =>
    intro M _ _ _ _ ρ _ hk _
    have : {z | z ∈ Zl ρ ∧ ∀ g ∈ J, z g = 0} ⊆ {0} := fun z _ => funext fun g => by simpa using hk (z g)
    refine ⟨(Set.finite_singleton _).subset this, (Set.ncard_le_ncard this).trans ?_⟩
    rw [Set.ncard_singleton]
    exact Nat.card_pos
  | succ k ih =>
    intro M _ _ _ _ ρ hLC hk hJ
    let μ : M →ₗ[R] M := l • LinearMap.id
    have hμ : ∀ m, μ m = l • m := fun m => rfl
    have hN : ∀ g, LinearMap.ker μ ≤ (LinearMap.ker μ).comap (ρ g) := fun g m hm => by
      have h1 : l • m = 0 := hm
      show l • ρ g m = 0
      rw [← map_nsmul, h1, map_zero]
    have hQ : ∀ g, LinearMap.range μ ≤ (LinearMap.range μ).comap (ρ g) := by
      rintro g _ ⟨m, rfl⟩
      exact ⟨ρ g m, (map_nsmul (ρ g) l m).symm⟩
    let σ := ρ.subrepresentation _ hN
    let τ := ρ.subrepresentation _ hQ
    obtain ⟨f1, c1⟩ := hU R _ σ (fun m => IsLocallyConstant.desc _ Subtype.val (hLC m.1) Subtype.val_injective)
      (fun m => Subtype.ext m.2) fun g hg => LinearMap.ext fun m => Subtype.ext (by
        show ρ g m = m
        rw [hJ g hg]; rfl)
    obtain ⟨f2, c2⟩ := ih _ τ (fun m => IsLocallyConstant.desc _ Subtype.val (hLC m.1) Subtype.val_injective)
      (by
        rintro ⟨_, m, rfl⟩
        refine Subtype.ext ?_
        show l ^ k • l • m = 0
        rw [← mul_smul, ← pow_succ, hk]) fun g hg => LinearMap.ext fun m => Subtype.ext (by
        show ρ g m = m
        rw [hJ g hg]; rfl)
    haveI : Finite (SJ σ J) := f1
    haveI : Finite (SJ τ J) := f2
    let f : SJ ρ J →ₗ[R] SJ τ J :=
      { toFun := fun z => ⟨fun g => ⟨μ (z.1 g), z.1 g, rfl⟩,
          ⟨IsLocallyConstant.desc _ Subtype.val (z.2.1.1.comp μ) Subtype.val_injective, fun g h => Subtype.ext (by
            show μ (z.1 (g * h)) = μ (z.1 g) + ρ g (μ (z.1 h))
            rw [z.2.1.2, map_add, hμ (ρ g _), hμ (z.1 h), map_nsmul])⟩,
          fun g hg => Subtype.ext (by
            show μ (z.1 g) = 0
            rw [z.2.2 g hg, map_zero])⟩
        map_add' := fun a b => Subtype.ext (funext fun g => Subtype.ext (map_add μ _ _))
        map_smul' := fun c a => Subtype.ext (funext fun g => Subtype.ext (map_smul μ _ _)) }
    have hm : ∀ (z : LinearMap.ker f) g, z.1.1 g ∈ LinearMap.ker μ := fun z g =>
      congrArg Subtype.val (congrFun (congrArg Subtype.val z.2) g)
    let i : LinearMap.ker f → SJ σ J := fun z => ⟨fun g => ⟨z.1.1 g, hm z g⟩,
      ⟨IsLocallyConstant.desc _ Subtype.val z.1.2.1.1 Subtype.val_injective, fun g h => Subtype.ext (z.1.2.1.2 g h)⟩,
      fun g hg => Subtype.ext (z.1.2.2 g hg)⟩
    obtain ⟨f3, c3⟩ := card_step f i fun a b h =>
      Subtype.ext (Subtype.ext (funext fun g => congrArg Subtype.val (congrFun (congrArg Subtype.val h) g)))
    refine ⟨f3, ?_⟩
    have h : Nat.card M = Nat.card (LinearMap.ker μ) * Nat.card (LinearMap.range μ) := by
      rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker μ), Nat.card_congr μ.quotKerEquivRange.toEquiv]
    rw [h, ← Nat.card_coe_set_eq]
    rw [← Nat.card_coe_set_eq] at c1 c2
    exact c3.trans (Nat.mul_le_mul c1.le c2)
