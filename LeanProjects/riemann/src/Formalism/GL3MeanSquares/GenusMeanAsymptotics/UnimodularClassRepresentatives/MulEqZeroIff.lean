import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NkCountLocF
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoMeanAlphaN

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinAA

open HermitianSublattices LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans localValuationFiltration

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

def rd (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) (k j : ℕ) :
    (𝓞 K ⧸ extP K 𝔭 ^ k) →+* (𝓞 K ⧸ extP K 𝔭 ^ (k - j)) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.sub_le k j))

theorem rd_mk (𝔭 : Ideal (𝓞 F)) (k j : ℕ) (a : 𝓞 K) :
    rd K 𝔭 k j (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := rfl

theorem rd_surjective (𝔭 : Ideal (𝓞 F)) (k j : ℕ) : Function.Surjective (rd K 𝔭 k j) :=
  Ideal.Quotient.factor_surjective _

theorem rd_star [Fact (IsFixF K F)] (𝔭 : Ideal (𝓞 F)) (k j : ℕ) (a : 𝓞 K ⧸ extP K 𝔭 ^ k) :
    rd K 𝔭 k j (star a) = star (rd K 𝔭 k j a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  show rd K 𝔭 k j (NormLifting.conjQ _ _ (Ideal.Quotient.mk _ a)) =
    NormLifting.conjQ _ _ (rd K 𝔭 k j (Ideal.Quotient.mk _ a))
  rw [rd_mk, NormLifting.conjQ_mk, NormLifting.conjQ_mk, rd_mk]

private theorem iota_mul_mem_extP_pow_iff_mem_pow_sub_vF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0)
    {k : ℕ} (hk : vF 𝔭 c ≤ k) (x : 𝓞 K) :
    ι c * x ∈ extP K 𝔭 ^ k ↔ x ∈ extP K 𝔭 ^ (k - vF 𝔭 c) := by
  constructor
  · intro h
    obtain ⟨J, hJ⟩ : 𝔭 ^ vF 𝔭 c ∣ Ideal.span {c} :=
      Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr (localValuationFiltration.mem_pow_vF h𝔭 hc))
    have hJp : ¬ J ≤ 𝔭 := by
      intro hle
      apply localValuationFiltration.notMem_pow_vF h𝔭 hc
      have hle' : Ideal.span {c} ≤ 𝔭 ^ (vF 𝔭 c + 1) := by
        rw [hJ, pow_succ]; exact Ideal.mul_mono_right hle
      exact hle' (Ideal.mem_span_singleton_self c)
    have hcop : IsCoprime 𝔭 J := by
      rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      exact hJp (le_sup_right.trans (h𝔭.eq_of_le hne le_sup_left).symm.le)
    have hcopK : IsCoprime (extP K 𝔭) (J.map ι) := by
      rw [Ideal.isCoprime_iff_sup_eq] at hcop ⊢
      show 𝔭.map ι ⊔ J.map ι = ⊤
      rw [← Ideal.map_sup, hcop, Ideal.map_top]
    have hinj : Function.Injective ι := FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)
    have h𝔭0 : 𝔭 ≠ ⊥ := by
      intro h0
      have := reductionMapsOfForms.absNorm_pos h𝔭
      rw [h0, Ideal.absNorm_bot] at this
      exact lt_irrefl _ this
    have hP0 : extP K 𝔭 ≠ ⊥ := by
      show 𝔭.map ι ≠ ⊥
      rwa [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
    have hsc : Ideal.span {ι c} = (Ideal.span {c}).map ι := by
      rw [Ideal.map_span, Set.image_singleton]
    have hspan : Ideal.span {ι c * x} =
        extP K 𝔭 ^ vF 𝔭 c * (J.map ι * Ideal.span {x}) := by
      rw [← Ideal.span_singleton_mul_span_singleton, hsc, hJ, Ideal.map_mul, Ideal.map_pow,
        mul_assoc]
      rfl
    have hle : extP K 𝔭 ^ k ∣ Ideal.span {ι c * x} :=
      Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr h)
    rw [hspan, show k = vF 𝔭 c + (k - vF 𝔭 c) by omega, pow_add] at hle
    have h2 := (mul_dvd_mul_iff_left (pow_ne_zero _ hP0)).mp hle
    have h3 := (hcopK.pow_left (m := k - vF 𝔭 c)).dvd_of_dvd_mul_left h2
    exact (Ideal.span_singleton_le_iff_mem _).mp (Ideal.dvd_iff_le.mp h3)
  · intro h
    have h' := Ideal.mul_mem_mul (localizedQuotients.ι_mem_pow (K := K) (localValuationFiltration.mem_pow_vF h𝔭 hc)) h
    rwa [← pow_add, show vF 𝔭 c + (k - vF 𝔭 c) = k by omega] at h'

theorem mul_eq_zero_iff {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) {k : ℕ}
    (hk : vF 𝔭 c ≤ k) (z : 𝓞 K ⧸ extP K 𝔭 ^ k) :
    Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι c) * z = 0 ↔ rd K 𝔭 k (vF 𝔭 c) z = 0 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [← map_mul, rd_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem]
  exact iota_mul_mem_extP_pow_iff_mem_pow_sub_vF h𝔭 hc hk x

theorem mul_eq_mul_iff {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) {k : ℕ}
    (hk : vF 𝔭 c ≤ k) (x y : 𝓞 K ⧸ extP K 𝔭 ^ k) :
    Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι c) * x = Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι c) * y ↔
      rd K 𝔭 k (vF 𝔭 c) x = rd K 𝔭 k (vF 𝔭 c) y := by
  rw [← sub_eq_zero, ← mul_sub, mul_eq_zero_iff h𝔭 hc hk, map_sub, sub_eq_zero]

theorem card_ker_rd (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k j : ℕ} (hjk : j ≤ k) :
    Nat.card (RingHom.ker (rd K 𝔭 k j)) = Ideal.absNorm 𝔭 ^ (2 * j) := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (RingHom.ker (rd K 𝔭 k j))
  rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective (rd_surjective 𝔭 k j)).toEquiv,
    idealPowerSpanBounds.absNorm_extP_pow hK hF h𝔭, idealPowerSpanBounds.absNorm_extP_pow hK hF h𝔭] at h1
  have hpos : 0 < Ideal.absNorm 𝔭 ^ (2 * (k - j)) := pow_pos (reductionMapsOfForms.absNorm_pos h𝔭) _
  have h2 : Ideal.absNorm 𝔭 ^ (2 * k) = Ideal.absNorm 𝔭 ^ (2 * j) * Ideal.absNorm 𝔭 ^ (2 * (k - j)) := by
    rw [← pow_add]; congr 1; omega
  rw [h2] at h1
  exact (Nat.eq_of_mul_eq_mul_right hpos (by rw [← h1])).symm

variable {κ : Type} [Fintype κ] [DecidableEq κ] [Fact (IsFixF K F)]

theorem map_smul_mk (𝔭 : Ideal (𝓞 F)) (k : ℕ) (c : 𝓞 F) (H : Matrix κ κ (𝓞 K)) :
    (ι c • H).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) =
      Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι c) • H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by
  ext i j
  show Ideal.Quotient.mk _ (ι c * H i j) =
    Ideal.Quotient.mk _ (ι c) * Ideal.Quotient.mk _ (H i j)
  exact map_mul _ _ _

private theorem card_subtype_comp_eq_card_mul_card_ker_of_surjective {A B : Type} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hf : Function.Surjective f) (T : B → Prop) :
    Nat.card {a : A // T (f a)} = Nat.card {b : B // T b} * Nat.card (AddMonoidHom.ker f) := by
  have hs : ∀ b, f (Function.surjInv hf b) = b := Function.surjInv_eq hf
  rw [← Nat.card_prod]
  apply Nat.card_congr
  exact
    { toFun := fun a => (⟨f a.1, a.2⟩, ⟨a.1 - Function.surjInv hf (f a.1), by
        rw [AddMonoidHom.mem_ker, map_sub, hs, sub_self]⟩)
      invFun := fun p => ⟨Function.surjInv hf p.1.1 + p.2.1, by
        rw [map_add, hs, AddMonoidHom.mem_ker.mp p.2.2, add_zero]; exact p.1.2⟩
      left_inv := fun a => Subtype.ext (by
        show Function.surjInv hf (f a.1) + (a.1 - Function.surjInv hf (f a.1)) = a.1
        abel)
      right_inv := fun p => by
        have e : f (Function.surjInv hf p.1.1 + p.2.1) = p.1.1 := by
          rw [map_add, hs, AddMonoidHom.mem_ker.mp p.2.2, add_zero]
        refine Prod.ext (Subtype.ext e) (Subtype.ext ?_)
        show Function.surjInv hf p.1.1 + p.2.1 - Function.surjInv hf (f (Function.surjInv hf p.1.1 + p.2.1)) = p.2.1
        rw [e]; abel }

private theorem card_ker_mapMatrix_eq_card_ker_pow_sq {A B : Type} [Ring A] [Ring B] (R : A →+* B) :
    Nat.card (AddMonoidHom.ker (R.toAddMonoidHom.mapMatrix : Matrix κ κ A →+ Matrix κ κ B)) =
      Nat.card (RingHom.ker R) ^ (Fintype.card κ ^ 2) := by
  have e : AddMonoidHom.ker (R.toAddMonoidHom.mapMatrix : Matrix κ κ A →+ Matrix κ κ B) ≃
      (κ → κ → RingHom.ker R) :=
    { toFun := fun X i j => ⟨X.1 i j, by
        have h := congrFun (congrFun (AddMonoidHom.mem_ker.mp X.2) i) j
        exact (RingHom.mem_ker).mpr h⟩
      invFun := fun g => ⟨Matrix.of fun i j => (g i j).1, by
        rw [AddMonoidHom.mem_ker]
        ext i j
        exact (RingHom.mem_ker).mp (g i j).2⟩
      left_inv := fun X => rfl
      right_inv := fun g => rfl }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := κ), ← pow_mul, sq]

private theorem card_ker_compLeft_eq_card_ker_pow {A B : Type} [Ring A] [Ring B] (R : A →+* B) :
    Nat.card (AddMonoidHom.ker (AddMonoidHom.compLeft R.toAddMonoidHom κ)) =
      Nat.card (RingHom.ker R) ^ Fintype.card κ := by
  have e : AddMonoidHom.ker (AddMonoidHom.compLeft R.toAddMonoidHom κ) ≃ (κ → RingHom.ker R) :=
    { toFun := fun x i => ⟨x.1 i, by
        have h := congrFun (AddMonoidHom.mem_ker.mp x.2) i
        exact (RingHom.mem_ker).mpr h⟩
      invFun := fun g => ⟨fun i => (g i).1, by
        rw [AddMonoidHom.mem_ker]
        funext i
        exact (RingHom.mem_ker).mp (g i).2⟩
      left_inv := fun x => rfl
      right_inv := fun g => rfl }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := κ)]

theorem akM_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F}
    (hc : c ≠ 0) {k : ℕ} (hk : vF 𝔭 c ≤ k) (H : Matrix κ κ (𝓞 K)) :
    Nat.card {X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k) //
        Xᴴ * (ι c • H).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) * X =
          (ι c • H).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))} =
      Ideal.absNorm 𝔭 ^ (2 * vF 𝔭 c * Fintype.card κ ^ 2) *
        Nat.card {X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (k - vF 𝔭 c)) //
          Xᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) * X =
            H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c)))} := by
  have hHR : (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))).map (rd K 𝔭 k (vF 𝔭 c)) =
      H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) := by
    rw [Matrix.map_map]; rfl
  have key : ∀ X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k),
      (Xᴴ * (ι c • H).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) * X =
          (ι c • H).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) ↔
        (X.map (rd K 𝔭 k (vF 𝔭 c)))ᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) *
            X.map (rd K 𝔭 k (vF 𝔭 c)) =
          H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) := by
    intro X
    have hR : (X.map (rd K 𝔭 k (vF 𝔭 c)))ᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) *
        X.map (rd K 𝔭 k (vF 𝔭 c)) =
        (Xᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) * X).map (rd K 𝔭 k (vF 𝔭 c)) := by
      rw [Matrix.map_mul, Matrix.map_mul, ← hHR,
        Matrix.conjTranspose_map _ (fun a => rd_star 𝔭 k (vF 𝔭 c) a)]
    rw [map_smul_mk, Matrix.mul_smul, Matrix.smul_mul, hR, ← hHR, ← Matrix.ext_iff,
      ← Matrix.ext_iff]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
    exact mul_eq_mul_iff h𝔭 hc hk _ _
  have hsurj : Function.Surjective
      ((rd K 𝔭 k (vF 𝔭 c)).toAddMonoidHom.mapMatrix :
        Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k) →+ Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (k - vF 𝔭 c))) := by
    intro Y
    refine ⟨Y.map (Function.surjInv (rd_surjective 𝔭 k (vF 𝔭 c))), ?_⟩
    ext i j
    exact Function.surjInv_eq (rd_surjective 𝔭 k (vF 𝔭 c)) (Y i j)
  rw [Nat.card_congr (Equiv.subtypeEquivRight key)]
  refine (card_subtype_comp_eq_card_mul_card_ker_of_surjective _ hsurj (fun Y => Yᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) * Y =
      H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))))).trans ?_
  rw [card_ker_mapMatrix_eq_card_ker_pow_sq, card_ker_rd hK Fact.out h𝔭 hk, ← pow_mul, mul_comm]

theorem nkM_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F}
    (hc : c ≠ 0) (n : 𝓞 F) {k : ℕ} (hk : vF 𝔭 c ≤ k) (H : Matrix κ κ (𝓞 K)) :
    Nat.card {x : κ → 𝓞 K ⧸ extP K 𝔭 ^ k //
        star x ⬝ᵥ ((ι c • H).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *ᵥ x) =
          Ideal.Quotient.mk _ (ι (c * n))} =
      Ideal.absNorm 𝔭 ^ (2 * vF 𝔭 c * Fintype.card κ) *
        Nat.card {x : κ → 𝓞 K ⧸ extP K 𝔭 ^ (k - vF 𝔭 c) //
          star x ⬝ᵥ (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) *ᵥ x) =
            Ideal.Quotient.mk _ (ι n)} := by
  have key : ∀ x : κ → 𝓞 K ⧸ extP K 𝔭 ^ k,
      (star x ⬝ᵥ ((ι c • H).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *ᵥ x) =
          Ideal.Quotient.mk _ (ι (c * n))) ↔
        star (fun i => rd K 𝔭 k (vF 𝔭 c) (x i)) ⬝ᵥ
            (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) *ᵥ
              fun i => rd K 𝔭 k (vF 𝔭 c) (x i)) =
          Ideal.Quotient.mk _ (ι n) := by
    intro x
    have e : rd K 𝔭 k (vF 𝔭 c) (star x ⬝ᵥ (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *ᵥ x)) =
        star (fun i => rd K 𝔭 k (vF 𝔭 c) (x i)) ⬝ᵥ
            (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) *ᵥ
              fun i => rd K 𝔭 k (vF 𝔭 c) (x i)) := by
      simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Pi.star_apply, rd_star,
        Matrix.map_apply, rd_mk]
    rw [map_smul_mk, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, map_mul, map_mul,
      mul_eq_mul_iff h𝔭 hc hk, e, rd_mk]
  have hsurj : Function.Surjective
      (AddMonoidHom.compLeft (rd K 𝔭 k (vF 𝔭 c)).toAddMonoidHom κ) := by
    intro y
    refine ⟨fun i => Function.surjInv (rd_surjective 𝔭 k (vF 𝔭 c)) (y i), ?_⟩
    funext i
    exact Function.surjInv_eq (rd_surjective 𝔭 k (vF 𝔭 c)) (y i)
  rw [Nat.card_congr (Equiv.subtypeEquivRight key)]
  refine (card_subtype_comp_eq_card_mul_card_ker_of_surjective _ hsurj (fun y => star y ⬝ᵥ
      (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) *ᵥ y) = Ideal.Quotient.mk _ (ι n))).trans ?_
  rw [card_ker_compLeft_eq_card_ker_pow, card_ker_rd hK Fact.out h𝔭 hk, ← pow_mul, mul_comm]

end Formalism.HermitianLattices.Ext.L3.PinAA
