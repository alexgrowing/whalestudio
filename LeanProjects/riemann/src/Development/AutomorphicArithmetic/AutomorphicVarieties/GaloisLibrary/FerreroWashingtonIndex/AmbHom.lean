import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.HomCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FinChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem aH_lc {H M : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup M]
    (φ : H → M) (h : ∀ a b, φ (a * b) = φ a + φ b) (N : Set H) (hN : IsOpen N) (h1 : (1 : H) ∈ N)
    (h0 : ∀ u ∈ N, φ u = 0) : IsLocallyConstant φ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have ho : IsOpen ((fun y => x⁻¹ * y) ⁻¹' N) := hN.preimage (by fun_prop)
  filter_upwards [ho.mem_nhds (show x ∈ (fun y => x⁻¹ * y) ⁻¹' N by simpa using h1)] with y hy
  have := h x (x⁻¹ * y)
  rw [h0 _ hy, add_zero, mul_inv_cancel_left] at this
  exact this

private theorem aH_one {H M : Type} [Group H] [AddCommGroup M]
    (φ : H → M) (h : ∀ a b, φ (a * b) = φ a + φ b) : φ 1 = 0 := by
  have := h 1 1
  rw [mul_one] at this
  exact left_eq_add.1 this

private theorem aH_inv {H M : Type} [Group H] [AddCommGroup M]
    (φ : H → M) (h : ∀ a b, φ (a * b) = φ a + φ b) (a : H) : φ a⁻¹ = -φ a := by
  have := h a⁻¹ a
  rw [inv_mul_cancel, aH_one φ h] at this
  exact eq_neg_of_add_eq_zero_left this.symm

private theorem aH_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ)
    (U : Subgroup (G F Ω)) [hU : U.Normal] (φ : U → ZMod l) :
    φ ∈ EqHom 1 U (Formalism.GaloisCohomology.scalRep (ZMod l) (1 : G F Ω →* (ZMod l)ˣ)) ↔
      IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧
        (∀ (A : ValuationSubring Ω) (u : U), u.1 ∈ Ine (F := F) A → φ u = 0) ∧
        ∀ (g : G F Ω) (u : U), φ ⟨g * u * g⁻¹, hU.conj_mem _ u.2 g⟩ = φ u := by
  rw [EqHom, Submodule.mem_inf, Submodule.mem_iInf]
  constructor
  · rintro ⟨⟨h1, h2, h3, -⟩, h4⟩
    refine ⟨h1, h2, h3, fun g u => ?_⟩
    have := h4 g u ⟨g * u * g⁻¹, hU.conj_mem _ u.2 g⟩ (fun x => by
      show g (u.1 (g.symm (g x))) = g (u.1 x)
      rw [AlgEquiv.symm_apply_apply])
    rw [this, scalRep_apply]
    simp
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1, h2, h3, fun A hA => ?_⟩, fun g u u' h => ?_⟩
    · simp at hA
    · rw [scalRep_apply, ← h4 g u]
      have : u' = ⟨g * u * g⁻¹, hU.conj_mem _ u.2 g⟩ := Subtype.ext (AlgEquiv.ext fun x => by
        have := h (g.symm x)
        rw [show g.toRingEquiv (g.symm x) = x from g.apply_symm_apply x] at this
        exact this)
      rw [this]
      simp

theorem UpperTheory.V.FW.ambHom :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] [IsGalois F K] (l : ℕ) [Fact l.Prime] (ζ : F), IsPrimitiveRoot ζ l → IsCyclic Gal(K/F) → (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → Ine (F := F) A ≤ galOf F K Ω) → Finite (EqHom 1 (galOf F K Ω) (Formalism.GaloisCohomology.scalRep (ZMod l) (1 : G F Ω →* (ZMod l)ˣ))) → Nat.card (EqHom 1 (galOf F K Ω) (Formalism.GaloisCohomology.scalRep (ZMod l) (1 : G F Ω →* (ZMod l)ˣ))) ≤ Set.ncard {φ : G F Ω → ZMod l | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := F) A, φ g = 0} := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ _ l hl ζ hζ hc hI hfin
  haveI : IsGalois F Ω := {}
  have hUo : IsOpen (galOf F K Ω : Set (G F Ω)) := (galEmbTop F K Ω).2.1
  have hcyc : IsCyclic (G F Ω ⧸ galOf F K Ω) := by
    obtain ⟨q1, q2, -⟩ := galQuot F K Ω
    have e := (QuotientGroup.quotientMulEquivOfEq q2.symm).trans (QuotientGroup.quotientKerEquivOfSurjective _ q1)
    exact isCyclic_of_surjective e.symm e.symm.surjective
  have hn : (galOf F K Ω).Normal := inferInstance
  set U := galOf F K Ω with hUdef
  have hm := aH_mem l U
  set E := EqHom 1 U (Formalism.GaloisCohomology.scalRep (ZMod l) (1 : G F Ω →* (ZMod l)ˣ)) with hE
  let N : Subgroup (G F Ω) :=
    { carrier := {g | ∃ h : g ∈ U, ∀ φ : E, φ.1 ⟨g, h⟩ = 0}
      one_mem' := ⟨U.one_mem, fun φ => aH_one φ.1 ((hm _).1 φ.2).2.1⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨U.mul_mem ha hb, fun φ => ?_⟩
        have := ((hm _).1 φ.2).2.1 ⟨a, ha⟩ ⟨b, hb⟩
        rw [ha', hb', add_zero] at this
        exact this
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨U.inv_mem ha, fun φ => ?_⟩
        have := aH_inv φ.1 ((hm _).1 φ.2).2.1 ⟨a, ha⟩
        rw [ha', neg_zero] at this
        exact this }
  have hN : ∀ g, g ∈ N ↔ ∃ h : g ∈ U, ∀ φ : E, φ.1 ⟨g, h⟩ = 0 := fun _ => Iff.rfl
  haveI : N.Normal := ⟨fun u ⟨hu, hu'⟩ g => ⟨hn.conj_mem u hu g, fun φ =>
    (((hm _).1 φ.2).2.2.2 g ⟨u, hu⟩).trans (hu' φ)⟩⟩
  have hNo : IsOpen (N : Set (G F Ω)) := by
    have : (N : Set (G F Ω)) = Subtype.val '' (⋂ φ : E, φ.1 ⁻¹' {0}) := by
      ext g
      simp only [SetLike.mem_coe, hN, Set.mem_image, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun ⟨h, h'⟩ => ⟨⟨g, h⟩, h', rfl⟩, fun ⟨u, h, e⟩ => e ▸ ⟨u.2, h⟩⟩
    rw [this]
    exact hUo.isOpenMap_subtype_val _ (isOpen_iInter_of_finite fun φ => ((hm _).1 φ.2).1 _)
  haveI : Finite (G F Ω ⧸ N) := N.quotient_finite_of_isOpen hNo
  haveI : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hcomm : ∀ g, ∀ u ∈ U, g * u * g⁻¹ * u⁻¹ ∈ N := fun g u hu => by
    refine ⟨U.mul_mem (hn.conj_mem u hu g) (U.inv_mem hu), fun φ => ?_⟩
    obtain ⟨-, h2, -, h4⟩ := (hm _).1 φ.2
    have := h2 ⟨g * u * g⁻¹, hn.conj_mem u hu g⟩ (⟨u, hu⟩ : U)⁻¹
    rw [aH_inv φ.1 h2, h4 g ⟨u, hu⟩, add_neg_cancel] at this
    exact this
  have hIN : ∀ (A : ValuationSubring Ω) (u : U), u.1 ∈ Ine (F := F) A → u.1 ∈ N := fun A u hu =>
    ⟨u.2, fun φ => ((hm _).1 φ.2).2.2.1 A u hu⟩
  have key := homCyc l (G F Ω) U N (fun g h => h.1) hcyc hcomm
  have e1 : Nat.card E = Nat.card {φ : U → ZMod l // (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u : U, u.1 ∈ N → φ u = 0} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun φ => ⟨fun h => ⟨((hm _).1 h).2.1, fun u hu => hu.2 ⟨φ, h⟩⟩, ?_⟩)
    rintro ⟨h2, h0⟩
    refine (hm _).2 ⟨aH_lc φ h2 (Subtype.val ⁻¹' N) (hNo.preimage continuous_subtype_val) N.one_mem h0, h2,
      fun A u hu => h0 u (hIN A u hu), fun g u => ?_⟩
    have := h2 ⟨g * u * g⁻¹, hn.conj_mem u u.2 g⟩ u⁻¹
    rw [aH_inv φ h2, h0 _ (hcomm g u u.2)] at this
    exact add_neg_eq_zero.1 this.symm
  have hf := finChar F Ω l l ζ hl.out.ne_zero hl.out.ne_zero hζ
  rw [e1]
  refine key.trans ?_
  rw [← Nat.card_coe_set_eq]
  haveI := hf.to_subtype
  refine Nat.card_le_card_of_injective (fun φ => ⟨φ.1, aH_lc φ.1 φ.2.1 N hNo N.one_mem φ.2.2, φ.2.1,
    fun A hA g hg => φ.2.2 g (hIN A ⟨g, hI A hA hg⟩ hg)⟩) fun a b h => Subtype.ext (Subtype.mk.inj h)
