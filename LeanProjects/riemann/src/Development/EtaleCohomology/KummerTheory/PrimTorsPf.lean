import Development.EtaleCohomology.KummerTheory.TwSecPf

noncomputable section
open Polynomial IsLocalRing GlobalTheory.EtC

namespace LateralTheory.KummerTheory.PrimitiveRootTorsion

theorem aeval_cyc {S : Type} [CommRing S] (q : ℕ) (x : S) :
    aeval x (cyclotomic q ℤ) = eval x (cyclotomic q S) := by
  rw [aeval_def, eval₂_eq_eval_map, algebraMap_int_eq, map_cyclotomic_int]

theorem prim_pow {q : ℕ} {B : Type} [CommRing B] (ζ : Prim q B) : ζ.1 ^ q = 1 := by
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (aeval ζ.1) hg
  rw [map_mul, ζ.2.2, zero_mul] at h
  simpa [sub_eq_zero] using h

theorem pow_mod_q {q : ℕ} {B : Type} [CommRing B] {x : B} (h : x ^ q = 1) (n : ℕ) : x ^ n = x ^ (n % q) := by
  conv_lhs => rw [← Nat.div_add_mod n q, pow_add, pow_mul, h, one_pow, one_mul]

variable {q : ℕ} [NeZero q] {B : Type} [CommRing B] [IsLocalRing B]

theorem neZero_res (hq : IsUnit (q : B)) : NeZero (q : ResidueField B) :=
  ⟨by simpa using (hq.map (residue B)).ne_zero⟩

theorem uniq (hq : IsUnit (q : B)) {u v : B} (hu : u ^ q = 1) (hv : v ^ q = 1)
    (h : residue B u = residue B v) : u = v := by
  have hq' := neZero_res hq
  have hS : IsUnit (∑ i ∈ Finset.range q, u ^ i * v ^ (q - 1 - i)) := by
    apply isUnit_of_map_unit (residue B)
    rw [map_sum]
    simp only [map_mul, map_pow, h]
    rw [geom_sum₂_self]
    have hv' : residue B v ^ q = 1 := by rw [← map_pow, hv, map_one]
    have hu1 : IsUnit (residue B v) := IsUnit.of_pow_eq_one hv' (NeZero.ne q)
    exact (isUnit_iff_ne_zero.2 (NeZero.ne _)).mul (hu1.pow _)
  have e := geom_sum₂_mul u v q
  rw [hu, hv, sub_self] at e
  exact sub_eq_zero.1 ((hS.mul_right_eq_zero).1 e)

theorem prim_res (hq : IsUnit (q : B)) (ζ : Prim q B) : IsPrimitiveRoot (residue B ζ.1) q := by
  have := neZero_res hq
  rw [← isRoot_cyclotomic_iff, IsRoot, ← aeval_cyc]
  have e := Polynomial.aeval_algHom_apply (residue B).toIntAlgHom ζ.1 (cyclotomic q ℤ)
  rw [ζ.2.2, map_zero] at e
  exact e

theorem exists_idx (hq : IsUnit (q : B)) (ζ ξ : Prim q B) :
    ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val := by
  have hζ := prim_res hq ζ
  have hξ := prim_res hq ξ
  obtain ⟨i, hi, he⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
  have hc : i.Coprime q := (hζ.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (he ▸ hξ)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  have hval : ((ZMod.unitOfCoprime i hc : (ZMod q)ˣ) : ZMod q).val = i := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  rw [hval]
  refine uniq hq (prim_pow ξ) (by rw [← pow_mul, mul_comm, pow_mul, prim_pow ζ, one_pow]) ?_
  rw [map_pow, he]

theorem idx_unique (hq : IsUnit (q : B)) (ζ : Prim q B) {a b : (ZMod q)ˣ}
    (h : ζ.1 ^ (a : ZMod q).val = ζ.1 ^ (b : ZMod q).val) : a = b := by
  have h' := congrArg (residue B) h
  rw [map_pow, map_pow] at h'
  exact Units.ext (ZMod.val_injective q ((prim_res hq ζ).pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h'))

theorem idx_mul {ζ0 ζ ξ : Prim q B} {a b : (ZMod q)ˣ} (hb : ζ.1 = ζ0.1 ^ (b : ZMod q).val)
    (ha : ξ.1 = ζ.1 ^ (a : ZMod q).val) : ξ.1 = ζ0.1 ^ ((a * b : (ZMod q)ˣ) : ZMod q).val := by
  rw [Units.val_mul, ZMod.val_mul, ← pow_mod_q (prim_pow ζ0), ha, hb, ← pow_mul, mul_comm]

end LateralTheory.KummerTheory.PrimitiveRootTorsion

namespace LateralTheory.KummerTheory.PrimitiveRootTorsion

theorem exists_prim {q : ℕ} [NeZero q] {B : Type} [CommRing B] [HenselianLocalRing B]
    [IsSepClosed (ResidueField B)] (hq : IsUnit (q : B)) : Nonempty (Prim q B) := by
  have := neZero_res hq
  obtain ⟨μ, hμ⟩ := IsSepClosed.exists_root (cyclotomic q (ResidueField B))
    (degree_cyclotomic_pos q _ (Nat.pos_of_ne_zero (NeZero.ne q))).ne' (separable_cyclotomic q _)
  obtain ⟨a0, rfl⟩ := residue_surjective μ
  have hev : residue B (eval a0 (cyclotomic q B)) = eval (residue B a0) (cyclotomic q (ResidueField B)) := by
    rw [← Polynomial.eval₂_hom, ← Polynomial.eval_map, map_cyclotomic]
  have hder : residue B (eval a0 (derivative (cyclotomic q B))) =
      eval (residue B a0) (derivative (cyclotomic q (ResidueField B))) := by
    rw [← Polynomial.eval₂_hom, ← Polynomial.eval_map, ← Polynomial.derivative_map, map_cyclotomic]
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (cyclotomic q B) (cyclotomic.monic q B) a0
    (by rw [← residue_eq_zero_iff, hev]; exact hμ)
    (by
      apply isUnit_of_map_unit (residue B)
      rw [hder, isUnit_iff_ne_zero]
      have h := (separable_cyclotomic q (ResidueField B)).aeval_derivative_ne_zero
        (x := residue B a0) (by rw [Polynomial.coe_aeval_eq_eval]; exact hμ)
      rwa [Polynomial.coe_aeval_eq_eval] at h)
  exact ⟨⟨a, hq, by rw [aeval_cyc]; exact ha⟩⟩

end LateralTheory.KummerTheory.PrimitiveRootTorsion

namespace LateralTheory.KummerTheory
open LateralTheory.KummerTheory.PrimitiveRootTorsion

theorem PrimTors_of : PrimTors := by
  intro q _ B _ hSH hq
  obtain ⟨_, _⟩ := hSH
  refine ⟨exists_prim hq, fun i ζ => ?_⟩
  classical
  have hex : ∀ ξ : Prim q B, ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val := fun ξ => exists_idx hq ζ ξ
  let ind : Prim q B → (ZMod q)ˣ := fun ξ => (hex ξ).choose
  have hind : ∀ ξ, ξ.1 = ζ.1 ^ (ind ξ : ZMod q).val := fun ξ => (hex ξ).choose_spec
  let v : Prim q B → ULift.{1} (ZMod q) := fun ξ => ULift.up (((ind ξ) ^ i : (ZMod q)ˣ) : ZMod q)
  let φ := Finsupp.linearCombination (ULift.{1} (ZMod q)) v
  have hker : twRel q i B ≤ LinearMap.ker φ := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ', ξ, a, h, rfl⟩
    have hi : ind ξ = a * ind ζ' := idx_unique hq ζ (by rw [← hind ξ]; exact idx_mul (hind ζ') h)
    change φ _ = 0
    rw [map_sub, Finsupp.linearCombination_single, Finsupp.linearCombination_single, sub_eq_zero]
    apply ULift.ext
    simp [v, hi, mul_zpow]
  let ψ := (twRel q i B).liftQ φ hker
  constructor
  · intro t t' h
    have h2 := congrArg ψ h
    simp only [LinearMap.map_smul, ψ, Submodule.liftQ_apply, φ, Finsupp.linearCombination_single,
      one_smul] at h2
    have h3 := congrArg ULift.down h2
    change t * (((ind ζ) ^ i : (ZMod q)ˣ) : ZMod q) = t' * (((ind ζ) ^ i : (ZMod q)ˣ) : ZMod q) at h3
    exact (Units.mul_left_inj _).1 h3
  · intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    induction x using Finsupp.induction_linear with
    | zero => exact ⟨0, by simp⟩
    | add f g hf hg =>
      obtain ⟨a, ha⟩ := hf
      obtain ⟨b, hb⟩ := hg
      refine ⟨a + b, ?_⟩
      simp only at ha hb ⊢
      rw [Submodule.Quotient.mk_add, ← ha, ← hb, ← add_smul]
      rfl
    | single ξ c =>
      have hmem : Finsupp.single ξ 1 - Finsupp.single ζ (ULift.up (((ind ξ) ^ i : (ZMod q)ˣ) : ZMod q)) ∈
          twRel q i B := Submodule.subset_span ⟨ζ, ξ, ind ξ, hind ξ, rfl⟩
      have he : (Submodule.Quotient.mk (Finsupp.single ξ 1) : _ ⧸ twRel q i B) =
          Submodule.Quotient.mk (Finsupp.single ζ (ULift.up (((ind ξ) ^ i : (ZMod q)ˣ) : ZMod q))) :=
        (Submodule.Quotient.eq _).2 hmem
      refine ⟨(c * ULift.up (((ind ξ) ^ i : (ZMod q)ˣ) : ZMod q)).down, ?_⟩
      have hs : Finsupp.single ζ (ULift.up (((ind ξ) ^ i : (ZMod q)ˣ) : ZMod q)) =
          (ULift.up (((ind ξ) ^ i : (ZMod q)ˣ) : ZMod q)) • Finsupp.single ζ (1 : ULift.{1} (ZMod q)) := by
        rw [Finsupp.smul_single_one]
      simp only [ULift.up_down]
      rw [← Finsupp.smul_single_one ξ c, Submodule.Quotient.mk_smul, he, hs, Submodule.Quotient.mk_smul, smul_smul]

end LateralTheory.KummerTheory
