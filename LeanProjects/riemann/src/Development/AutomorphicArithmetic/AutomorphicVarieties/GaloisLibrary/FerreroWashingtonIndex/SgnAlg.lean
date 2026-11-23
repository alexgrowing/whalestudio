import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.NilCard

open UpperTheory.V.FW

private theorem gen2 {G Q W : Type} [Group G] [Finite Q] [AddCommGroup W] (h2 : ∀ w : W, 2 • w = 0)
    (ψ : MonoidAlgebra ℤ G →+ W) (hψ : Function.Surjective ψ) (p : G → Q) (v : Q → W)
    (hv : ∀ g, ψ (MonoidAlgebra.single g 1) = v (p g)) :
    Finite W ∧ Nat.card W ≤ 2 ^ Nat.card Q := by
  classical
  letI : Fintype Q := Fintype.ofFinite Q
  letI : Module (ZMod 2) W := AddCommGroup.zmodModule h2
  let φ : (Q → ZMod 2) →ₗ[ZMod 2] W := Fintype.linearCombination (ZMod 2) v
  have hs : Function.Surjective φ := by
    intro w
    obtain ⟨x, rfl⟩ := hψ w
    change ψ x ∈ (LinearMap.range φ).toAddSubgroup
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
    | single g n =>
      have : (MonoidAlgebra.single g n : MonoidAlgebra ℤ G) = n • MonoidAlgebra.single g 1 := by simp
      rw [this, map_zsmul]
      refine zsmul_mem ?_ _
      rw [hv]
      exact ⟨Pi.single (p g) 1, by simp [φ]⟩
  refine ⟨Finite.of_surjective φ hs, ?_⟩
  have := Nat.card_le_card_of_surjective φ hs
  simpa [Nat.card_fun] using this

private noncomputable def kap {G : Type} [CommGroup G] (J : G) : MonoidAlgebra ℤ G →+ (G → ZMod 2) where
  toFun x := fun g => (((x * (1 + MonoidAlgebra.of ℤ G J)).coeff g : ℤ) : ZMod 2)
  map_zero' := by ext g; simp
  map_add' a b := by ext g; simp [add_mul]

private theorem kap_apply {G : Type} [CommGroup G] {J : G} (hJ : J * J = 1) (x : MonoidAlgebra ℤ G) (g : G) :
    kap J x g = (x.coeff g : ZMod 2) + (x.coeff (J * g) : ZMod 2) := by
  have : J⁻¹ = J := inv_eq_of_mul_eq_one_right hJ
  simp [kap, mul_add, this, mul_comm J g]

private theorem kap_single_mul {G : Type} [CommGroup G] {J : G} (hJ : J * J = 1) (x : MonoidAlgebra ℤ G) (g : G) :
    kap J (MonoidAlgebra.single g 1 * x) = fun h => kap J x (g⁻¹ * h) := by
  ext h
  simp [kap_apply hJ, mul_left_comm]

private theorem kap_range {G : Type} [CommGroup G] [Finite G] {J : G} (hJ : J * J = 1) (hJ1 : J ≠ 1) :
    (kap J).range = evenF J := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩ g
    rw [kap_apply hJ, kap_apply hJ, ← mul_assoc, hJ, one_mul, add_comm]
  · intro f hf
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin G
    refine ⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun g => if e g < e (J * g) then ((f g).val : ℤ) else 0), ?_⟩
    ext g
    have hne : e g ≠ e (J * g) := fun h => hJ1 (by simpa using e.injective h)
    have hfg : f (J * g) = f g := hf g
    rw [kap_apply hJ]
    simp only [MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm, ← mul_assoc, hJ, one_mul]
    rcases lt_or_gt_of_ne hne with h | h
    · simp [h, h.le]
    · simp [h, h.le, hfg]

theorem UpperTheory.V.FW.sgnAlg :
    ∀ (G : Type) [CommGroup G] [Finite G] (J γ : G) (θ : MonoidAlgebra ℤ G) (N : ℕ) (S : AddSubgroup (G → ZMod 2)), J * J = 1 → J ≠ 1 → (∀ f ∈ S, ∀ g, (fun x => f (g * x)) ∈ S) → (fun g => (((θ * (1 + MonoidAlgebra.of ℤ G J)).coeff g : ℤ) : ZMod 2)) ∈ S → (MonoidAlgebra.of ℤ G γ - 1) ^ N ∈ Ideal.span {θ, 1 + MonoidAlgebra.of ℤ G J, ((2 : ℕ) : MonoidAlgebra ℤ G)} → S.relIndex (evenF J) ≤ (2 ^ (Subgroup.zpowers γ).index) ^ N := by
  intro G _ _ J γ θ N S hJ hJ1 hS hθ hN
  have hdbl : ∀ y, kap J (y + y) ∈ S := fun y => by
    have : kap J (y + y) = 0 := by
      rw [map_add]; ext g; simp [CharTwo.add_self_eq_zero]
    rw [this]; exact zero_mem _
  let I : Ideal (MonoidAlgebra ℤ G) :=
    { (S.comap (kap J)).toAddSubmonoid with
      smul_mem' := fun r x hx => by
        change kap J (r * x) ∈ S
        induction r using MonoidAlgebra.induction_linear with
        | zero => simp
        | add a b ha hb => rw [add_mul, map_add]; exact add_mem ha hb
        | single g n =>
          have : (MonoidAlgebra.single g n : MonoidAlgebra ℤ G) = n • MonoidAlgebra.single g 1 := by simp
          rw [this, smul_mul_assoc, map_zsmul, kap_single_mul hJ]
          exact zsmul_mem (hS _ hx _) _ }
  have hI : ∀ x, x ∈ I ↔ kap J x ∈ S := fun x => Iff.rfl
  have hNI : (MonoidAlgebra.of ℤ G γ - 1) ^ N ∈ I := by
    refine Ideal.span_le.2 ?_ hN
    rintro x (rfl | rfl | rfl)
    · exact hθ
    · change kap J _ ∈ S
      have : kap J (1 + MonoidAlgebra.of ℤ G J) = kap J (1 + 1) := by
        ext g
        have h1 : MonoidAlgebra.of ℤ G J * MonoidAlgebra.of ℤ G J = 1 := by rw [← map_mul, hJ, map_one]
        have : (1 + MonoidAlgebra.of ℤ G J) * (1 + MonoidAlgebra.of ℤ G J) = (1 + 1) * (1 + MonoidAlgebra.of ℤ G J) := by
          linear_combination h1
        simp only [kap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, this]
      rw [this]; exact hdbl 1
    · change kap J _ ∈ S
      have : ((2 : ℕ) : MonoidAlgebra ℤ G) = 1 + 1 := by norm_num
      rw [this]; exact hdbl 1
  have hidx : S.relIndex (evenF J) = Nat.card (MonoidAlgebra ℤ G ⧸ I) := by
    rw [← kap_range hJ hJ1, ← AddSubgroup.index_comap]
    rfl
  have h2 : ∀ w : MonoidAlgebra ℤ G ⧸ I, 2 • w = 0 := fun w => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective w
    rw [two_nsmul, ← map_add, Ideal.Quotient.eq_zero_iff_mem]
    exact hdbl x
  haveI hfin : Finite (MonoidAlgebra ℤ G ⧸ I) :=
    (gen2 h2 (Ideal.Quotient.mk I).toAddMonoidHom Ideal.Quotient.mk_surjective id
      (fun g => Ideal.Quotient.mk I (MonoidAlgebra.single g 1)) fun _ => rfl).1
  set t : MonoidAlgebra ℤ G ⧸ I := Ideal.Quotient.mk I (MonoidAlgebra.of ℤ G γ - 1) with ht
  let T : AddMonoid.End (MonoidAlgebra ℤ G ⧸ I) := Module.toAddMonoidEnd (MonoidAlgebra ℤ G ⧸ I) (MonoidAlgebra ℤ G ⧸ I) t
  have hT : T ^ N = 0 := by
    have : t ^ N = 0 := by rw [ht, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hNI
    rw [← map_pow, this, map_zero]
  rw [hidx]
  refine (nilCard _ T N hT).trans (Nat.pow_le_pow_left ?_ N)
  let ψ : MonoidAlgebra ℤ G →+ (MonoidAlgebra ℤ G ⧸ I) ⧸ AddMonoidHom.range T :=
    (QuotientAddGroup.mk' _).comp (Ideal.Quotient.mk I).toAddMonoidHom
  have hstep : ∀ g, ψ (MonoidAlgebra.single (γ * g) 1) = ψ (MonoidAlgebra.single g 1) := fun g => by
    rw [← sub_eq_zero, ← map_sub]
    refine (QuotientAddGroup.eq_zero_iff _).2 ⟨Ideal.Quotient.mk I (MonoidAlgebra.single g 1), ?_⟩
    change t * _ = Ideal.Quotient.mk I _
    rw [ht, ← map_mul, sub_mul]
    simp [MonoidAlgebra.single_mul_single]
  have hpow : ∀ (n : ℕ) g, ψ (MonoidAlgebra.single (γ ^ n * g) 1) = ψ (MonoidAlgebra.single g 1) := fun n g => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_assoc, hstep, ih]
  refine (gen2 (Q := G ⧸ Subgroup.zpowers γ) ?_ ψ ?_ QuotientGroup.mk
    (fun q => ψ (MonoidAlgebra.single q.out 1)) ?_).2
  · intro w
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ w
    rw [← map_nsmul, h2, map_zero]
  · exact (QuotientAddGroup.mk'_surjective _).comp Ideal.Quotient.mk_surjective
  · intro g
    obtain ⟨⟨h, hh⟩, e⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.zpowers γ) g
    obtain ⟨n, rfl⟩ := (mem_powers_iff_mem_zpowers.2 hh)
    simp only at e ⊢
    rw [e, mul_comm, hpow]
