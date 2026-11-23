import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CardTors
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.IneCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.AmbHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullMem

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.amb :
    ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (ζ : F), IsPrimitiveRoot ζ l → ∃ B : ℕ, ∀ (n : ℕ) (K : Type) [Field K] [NumberField K] [Algebra F K] [IsCyclotomicExtension {l ^ n} F K] (τ : Gal(K/F)), IsTotallyComplex K → (∀ σ : Gal(K/F), σ ∈ Subgroup.zpowers τ) → (powR (Cl K) l ⊔ difR (clMap τ.toRingEquiv)).index ≤ B := by
  intro F _ _ l _ ζ hζ
  obtain ⟨Ω, _, _, hΩ⟩ : ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra F Ω), IsAlgClosure F Ω :=
    ⟨AlgebraicClosure F, inferInstance, inferInstance, inferInstance⟩
  haveI : IsAlgClosed Ω := hΩ.isAlgClosed
  haveI : Algebra.IsAlgebraic F Ω := hΩ.isAlgebraic
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  refine ⟨{φ : G F Ω → ZMod l | IsLocallyConstant φ ∧ (∀ a b : G F Ω, φ (a * b) = φ a + φ b) ∧
      ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine A, φ g = 0}.ncard,
    fun n K _ _ _ _ τ hK hτ => ?_⟩
  haveI hgal : IsGalois F K := IsCyclotomicExtension.isGalois (S := {l ^ n}) (K := F) (L := K)
  let e : K →ₐ[F] Ω := IsAlgClosed.lift
  letI : Algebra K Ω := e.toRingHom.toAlgebra
  haveI : IsScalarTower F K Ω := IsScalarTower.of_algebraMap_eq (fun x => (e.commutes x).symm)
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := F) K
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  let ρ : Representation (ZMod l) (G F Ω) (ZMod l) := scalRep (ZMod l) 1
  have hcyc : IsCyclic Gal(K/F) := ⟨⟨τ, hτ⟩⟩
  have hpe := (pullEq F Ω K (galOf F K Ω) le_rfl 1 (ZMod l) (ZMod l) ρ one_ne_zero le_rfl (Or.inl hK)).1
  have hinj := (pullMem F Ω K (galOf F K Ω) le_rfl 1 (ZMod l) (ZMod l) one_ne_zero).2 le_rfl
  haveI hCfin : Finite (ClEq K 1 ρ) := Subtype.finite
  have hcardEq : Nat.card (EqHom 1 (galOf F K Ω) ρ) = Nat.card (ClEq K 1 ρ) := by
    rw [← hpe]
    exact Nat.card_congr (Submodule.equivMapOfInjective _ hinj _).toEquiv.symm
  have hEfin : Finite (EqHom 1 (galOf F K Ω) ρ) := by
    rw [← hpe]
    exact Finite.of_equiv _ (Submodule.equivMapOfInjective _ hinj _).toEquiv
  have hamb := ambHom F Ω K l ζ hζ hcyc (ineCyc F Ω K l n) hEfin
  set H := powR (Cl K) l ⊔ difR (clMap τ.toRingEquiv) with hH
  have hfix : ∀ c : Cl K, (QuotientGroup.mk (clMap τ.toRingEquiv c) : Cl K ⧸ H) = QuotientGroup.mk c := by
    intro c
    rw [QuotientGroup.eq]
    have h1 : c / clMap τ.toRingEquiv c ∈ H := le_sup_right (a := powR (Cl K) l) ⟨c, rfl⟩
    have h2 : (clMap τ.toRingEquiv c)⁻¹ * c = c / clMap τ.toRingEquiv c := by
      rw [div_eq_mul_inv, mul_comm]
    rw [h2]
    exact h1
  have hmulc : ∀ (a b : Gal(K/F)) (c : Cl K),
      clMap (a * b).toRingEquiv c = clMap a.toRingEquiv (clMap b.toRingEquiv c) :=
    fun a b c => clMap_trans b.toRingEquiv a.toRingEquiv c
  have hone1 : ∀ c : Cl K, clMap (1 : Gal(K/F)).toRingEquiv c = c := fun c => clMap_refl K c
  have hinv : ∀ d : Cl K, (QuotientGroup.mk (clMap τ⁻¹.toRingEquiv d) : Cl K ⧸ H) = QuotientGroup.mk d := by
    intro d
    have h3 : clMap τ.toRingEquiv (clMap τ⁻¹.toRingEquiv d) = d := by
      rw [← hmulc, mul_inv_cancel, hone1]
    conv_rhs => rw [← h3]
    rw [hfix]
  have hall : ∀ α : Gal(K/F), ∀ c : Cl K,
      (QuotientGroup.mk (clMap α.toRingEquiv c) : Cl K ⧸ H) = QuotientGroup.mk c := by
    intro α
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hτ α)
    induction k using Int.induction_on with
    | zero =>
      intro c
      rw [zpow_zero, hone1]
    | succ k ih =>
      intro c
      rw [zpow_add_one, hmulc, ih, hfix]
    | pred k ih =>
      intro c
      rw [zpow_sub_one, hmulc, ih, hinv]
  have hlift : ∀ (g : G F Ω) (τ' : K ≃+* K), IsLift τ' g.toRingEquiv → ∀ c : Cl K,
      (QuotientGroup.mk (clMap τ' c) : Cl K ⧸ H) = QuotientGroup.mk c := by
    intro g τ' hl c
    unfold IsLift at hl
    have hF : ∀ x : F, τ' (algebraMap F K x) = algebraMap F K x := by
      intro x
      apply (algebraMap K Ω).injective
      rw [← hl]
      show g (algebraMap K Ω (algebraMap F K x)) = algebraMap K Ω (algebraMap F K x)
      rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]
    let α : Gal(K/F) := AlgEquiv.ofRingEquiv (f := τ') hF
    have hα : α.toRingEquiv = τ' := RingEquiv.ext fun x => rfl
    rw [← hα]
    exact hall α c
  have hpowQ : powR (Cl K ⧸ H) l = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    unfold powR at hy
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
    rw [Subgroup.mem_bot]
    show (QuotientGroup.mk c : Cl K ⧸ H) ^ l = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact le_sup_left (b := difR (clMap τ.toRingEquiv)) ⟨c, rfl⟩
  have hcardQ : H.index = Nat.card (Cl K ⧸ H →* Multiplicative (ZMod l)) := by
    rw [(cardTors (Cl K ⧸ H)).2 l, hpowQ, Subgroup.index_bot]
    rfl
  let Φ : (Cl K ⧸ H →* Multiplicative (ZMod l)) → ClEq K 1 ρ := fun ψ =>
    ⟨fun c => Multiplicative.toAdd (ψ (QuotientGroup.mk c)), by
      unfold ClEq
      rw [Submodule.mem_inf, Submodule.mem_iInf]
      refine ⟨?_, fun g => ?_⟩
      · unfold ClDual
        refine ⟨fun a b => ?_, fun v hv => ?_⟩
        · beta_reduce
          rw [QuotientGroup.mk_mul, map_mul, toAdd_mul]
        · exfalso
          unfold Above at hv
          exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using hv))
      · unfold clCond
        intro τ' hl c
        beta_reduce
        rw [hlift g τ' hl c]
        simp [ρ, scalRep]⟩
  have hΦ : Function.Injective Φ := by
    intro ψ1 ψ2 h
    apply MonoidHom.ext
    intro x
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
    have h4 := congrFun (congrArg Subtype.val h) c
    exact Multiplicative.toAdd.injective h4
  calc H.index = Nat.card (Cl K ⧸ H →* Multiplicative (ZMod l)) := hcardQ
    _ ≤ Nat.card (ClEq K 1 ρ) := Nat.card_le_card_of_injective Φ hΦ
    _ = Nat.card (EqHom 1 (galOf F K Ω) ρ) := hcardEq.symm
    _ ≤ _ := hamb
