import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TateBasisMatrix
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormCardQuotientSpan

namespace GlobalTheory
namespace TorsionMatrix

section
open Matrix

theorem norm_card_quot_span (l : ℕ) [Fact l.Prime] {a : ℤ_[l]} (ha : a ≠ 0) :
    ‖((Nat.card (ℤ_[l] ⧸ Ideal.span {a}) : ℕ) : ℚ_[l])‖ = ‖a‖ := by
  have h1 : Ideal.span {a} = RingHom.ker (PadicInt.toZModPow (p := l) a.valuation) := by
    rw [PadicInt.ker_toZModPow]
    conv_lhs => rw [PadicInt.unitCoeff_spec ha]
    exact Ideal.span_singleton_mul_left_unit (PadicInt.unitCoeff ha).isUnit _
  have h2 : Nat.card (ℤ_[l] ⧸ Ideal.span {a}) = l ^ a.valuation := by
    rw [h1, Nat.card_congr (RingHom.quotientKerEquivOfSurjective
      (ZMod.ringHom_surjective (PadicInt.toZModPow (p := l) a.valuation))).toEquiv, Nat.card_zmod]
  rw [h2, PadicInt.norm_eq_zpow_neg_valuation ha]
  push_cast
  rw [Padic.norm_p_pow]

theorem norm_index_range (l : ℕ) [Fact l.Prime] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ ℤ_[l]) (hM : M.det ≠ 0) :
    ‖M.det‖ = ‖(((LinearMap.range M.mulVecLin).toAddSubgroup.index : ℕ) : ℚ_[l])‖ := by
  first
  | exact @_root_.GlobalTheory.NormDetIndex.norm_det_eq_norm_index
  | exact _root_.GlobalTheory.NormDetIndex.norm_det_eq_norm_index
  | (apply _root_.GlobalTheory.NormDetIndex.norm_det_eq_norm_index <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormDetIndex.norm_det_eq_norm_index <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormDetIndex.norm_det_eq_norm_index <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormDetIndex.norm_det_eq_norm_index ..)

theorem norm_card_eq_torsion (l : ℕ) [hl : Fact l.Prime] (K : Type) [AddCommGroup K] [Finite K]
    (N : ℕ) (hN : Nat.card K ≤ N) :
    ‖((Nat.card K : ℕ) : ℚ_[l])‖ = ‖((Nat.card {x : K // l ^ N • x = 0} : ℕ) : ℚ_[l])‖ := by
  let T : AddSubgroup K := (nsmulAddMonoidHom (α := K) (l ^ N)).ker
  have hT : ∀ x, x ∈ T ↔ l ^ N • x = 0 := fun x => Iff.rfl
  have h1 : Nat.card K = Nat.card (K ⧸ T) * Nat.card {x : K // l ^ N • x = 0} :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup T
  have h2 : ¬ l ∣ Nat.card (K ⧸ T) := by
    intro hd
    obtain ⟨y, hy⟩ := exists_prime_addOrderOf_dvd_card' l hd
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    have h3 : l • x ∈ T := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul,
        ← addOrderOf_dvd_iff_nsmul_eq_zero, hy]
    rw [hT, smul_smul, ← pow_succ, ← addOrderOf_dvd_iff_nsmul_eq_zero,
      Nat.dvd_prime_pow hl.out] at h3
    obtain ⟨k, -, hk⟩ := h3
    have h4 : k ≤ N := by
      have := addOrderOf_le_card (x := x)
      have := Nat.lt_pow_self (n := k) hl.out.one_lt
      omega
    have h5 : x ∈ T := by
      rw [hT, ← addOrderOf_dvd_iff_nsmul_eq_zero, hk]
      exact pow_dvd_pow _ h4
    rw [(QuotientAddGroup.eq_zero_iff x).2 h5, addOrderOf_zero] at hy
    exact hl.out.one_lt.ne hy
  rw [h1, Nat.cast_mul, norm_mul, Padic.norm_natCast_eq_one_iff.2
    ((Nat.Prime.coprime_iff_not_dvd hl.out).2 h2), one_mul]

theorem exists_zmod_basis (l : ℕ) [hl : Fact l.Prime] (m : ℕ) (V : Type) [AddCommGroup V]
    [Module (ZMod l) V] (hc1 : Nat.card V = l ^ m) :
    ∃ b : Fin m → V, ∀ x : V, ∃! t : Fin m → ZMod l, x = ∑ j, (t j).val • b j := by
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hc1]; exact pow_ne_zero _ hl.out.ne_zero)
  have hr : Module.finrank (ZMod l) V = m := by
    have := Module.natCard_eq_pow_finrank (K := ZMod l) (V := V)
    rw [hc1, Nat.card_zmod] at this
    exact (Nat.pow_right_injective hl.out.two_le this).symm
  let b := Module.finBasisOfFinrankEq (ZMod l) V hr
  have hs : ∀ t : Fin m → ZMod l, ∑ j, (t j).val • b j = b.equivFun.symm t := by
    intro t
    rw [b.equivFun_symm_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Nat.cast_smul_eq_nsmul (ZMod l), ZMod.natCast_zmod_val]
  refine ⟨b, fun x => ⟨b.equivFun x, ?_, fun t ht => ?_⟩⟩
  · simp only [hs, LinearEquiv.symm_apply_apply]
  · simp only [hs] at ht
    rw [ht, LinearEquiv.apply_symm_apply]

theorem exists_tower (l : ℕ) [hl : Fact l.Prime] (m : ℕ) (Q : Type) [AddCommGroup Q]
    (h : ∀ j : ℕ, Nat.card {x : Q // l ^ j • x = 0} = l ^ (m * j)) :
    ∃ τ : Fin m → ℕ → Q, (∀ i n, (l ^ (n + 1)) • τ i n = 0) ∧ (∀ i n, τ i n = l • τ i (n + 1)) ∧
      (∀ x : Q, l • x = 0 → ∃! t : Fin m → ZMod l, x = ∑ j, (t j).val • τ j 0) := by
  let T : ℕ → AddSubgroup Q := fun k => (nsmulAddMonoidHom (α := Q) k).ker
  have hT : ∀ k x, x ∈ T k ↔ k • x = 0 := fun k x => Iff.rfl
  have hc : ∀ j, Nat.card (T (l ^ j)) = l ^ (m * j) := h
  have hc1 : Nat.card (T l) = l ^ m := by simpa using hc 1
  have hfin : ∀ j, Finite (T (l ^ j)) := fun j =>
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hl.out.ne_zero)
  have hsurj : ∀ j (x : Q), l ^ j • x = 0 → ∃ y : Q, l ^ (j + 1) • y = 0 ∧ x = l • y := by
    intro j x hx
    have := hfin j
    have := hfin (j + 1)
    let φ : T (l ^ (j + 1)) →+ T (l ^ j) :=
      ((nsmulAddMonoidHom (α := Q) l).comp (T (l ^ (j + 1))).subtype).codRestrict _ fun y => by
        have := (hT _ _).1 y.2
        change l ^ j • l • (y : Q) = 0
        rw [smul_smul, ← pow_succ]
        exact this
    have hφ : ∀ y, (φ y : Q) = l • (y : Q) := fun y => rfl
    have hk : Nat.card φ.ker = l ^ m := by
      rw [← hc1]
      refine Nat.card_congr ⟨fun y => ⟨y.1.1, ?_⟩, fun y => ⟨⟨y.1, ?_⟩, ?_⟩, fun _ => rfl, fun _ => rfl⟩
      · exact congrArg Subtype.val y.2
      · rw [hT, pow_succ, mul_smul, (hT _ _).1 y.2, smul_zero]
      · exact Subtype.ext y.2
    have h1 := AddSubgroup.card_mul_index φ.ker
    rw [AddSubgroup.index_ker, hk, hc, mul_add, mul_one, pow_add l (m * j), mul_comm] at h1
    have h2 : Nat.card φ.range = Nat.card (T (l ^ j)) := by
      rw [hc]
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hl.out.pos m) h1
    have h3 : φ.range = ⊤ := AddSubgroup.eq_top_of_card_eq _ h2
    obtain ⟨y, hy⟩ := AddMonoidHom.range_eq_top.1 h3 ⟨x, hx⟩
    exact ⟨y, y.2, (congrArg Subtype.val hy).symm⟩
  choose! g hg1 hg2 using hsurj
  obtain ⟨b, hb⟩ := @exists_zmod_basis l hl m (T l) _
    (AddCommGroup.zmodModule fun x => Subtype.ext x.2) hc1
  let τ : Fin m → ℕ → Q := fun i n => Nat.rec (b i : Q) (fun k x => g (k + 1) x) n
  have h1 : ∀ i n, (l ^ (n + 1)) • τ i n = 0 := by
    intro i n
    induction n with
    | zero => rw [zero_add, pow_one]; exact (b i).2
    | succ n ih => exact hg1 _ _ ih
  have hs : ∀ t : Fin m → ZMod l,
      ((∑ j, (t j).val • b j : T l) : Q) = ∑ j, (t j).val • τ j 0 := by
    intro t
    rw [AddSubgroup.val_finset_sum]
    rfl
  refine ⟨τ, h1, fun i n => hg2 _ _ (h1 i n), fun x hx => ?_⟩
  simpa only [Subtype.ext_iff, hs] using hb ⟨x, hx⟩

theorem card_ker_eq_index (l : ℕ) [hl : Fact l.Prime] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M A : Matrix κ κ ℤ_[l]) (N : ℕ) (h1 : M * A = ((l : ℤ_[l]) ^ N) • 1)
    (h2 : A * M = ((l : ℤ_[l]) ^ N) • 1) :
    Nat.card {t : κ → ZMod (l ^ N) // (M.map (PadicInt.toZModPow N)) *ᵥ t = 0} =
      (LinearMap.range M.mulVecLin).toAddSubgroup.index := by
  set π := PadicInt.toZModPow (p := l) N with hπ
  have hl0 : ((l : ℤ_[l]) ^ N) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)
  have hz : ∀ y : κ → ℤ_[l], π ∘ y = 0 ↔ ∃ z : κ → ℤ_[l], y = ((l : ℤ_[l]) ^ N) • z := by
    intro y
    have : ∀ a : ℤ_[l], π a = 0 ↔ ∃ z, a = ((l : ℤ_[l]) ^ N) * z := by
      intro a
      rw [← RingHom.mem_ker, hπ, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]; rfl
    constructor
    · intro h
      choose z hz using fun i => (this (y i)).1 (congrFun h i)
      exact ⟨z, funext hz⟩
    · rintro ⟨z, rfl⟩
      exact funext fun i => (this _).2 ⟨z i, rfl⟩
  have hc : ∀ (P R : Matrix κ κ ℤ_[l]), R * P = ((l : ℤ_[l]) ^ N) • 1 →
      ∀ y z : κ → ℤ_[l], P *ᵥ y = P *ᵥ z → y = z := by
    intro P R h y z hyz
    have := congrArg (R *ᵥ ·) hyz
    simp only [mulVec_mulVec, h, smul_mulVec, one_mulVec] at this
    exact smul_right_injective _ hl0 this
  have hmap : ∀ y : κ → ℤ_[l], (M.map π) *ᵥ (π ∘ y) = π ∘ (M *ᵥ y) := fun y =>
    funext fun i => (RingHom.map_mulVec π M y i).symm
  let φ : (κ → ℤ_[l]) →+ (κ → ZMod (l ^ N)) :=
    (π.toAddMonoidHom.compLeft κ).comp A.mulVecLin.toAddMonoidHom
  have hφ : ∀ y, φ y = π ∘ (A *ᵥ y) := fun y => rfl
  have hk : φ.ker = (LinearMap.range M.mulVecLin).toAddSubgroup := by
    ext y
    rw [AddMonoidHom.mem_ker, hφ, hz]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z, hc A M h1 _ _ ?_⟩
      rw [mulVecLin_apply, mulVec_mulVec, h2, hz, smul_mulVec, one_mulVec]
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [mulVecLin_apply, mulVec_mulVec, h2, smul_mulVec, one_mulVec]⟩
  rw [← hk, AddSubgroup.index_ker]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun t => ?_)
  constructor
  · intro ht
    choose y hy using fun i => ZMod.ringHom_surjective π (t i)
    obtain rfl : π ∘ y = t := funext hy
    rw [hmap, hz] at ht
    obtain ⟨z, hz⟩ := ht
    refine ⟨z, ?_⟩
    rw [hφ, hc M A h2 (A *ᵥ z) y]
    rw [mulVec_mulVec, h1, hz, smul_mulVec, one_mulVec]
  · rintro ⟨z, rfl⟩
    rw [hφ, hmap, hz]
    exact ⟨z, by rw [mulVec_mulVec, h1, smul_mulVec, one_mulVec]⟩

section ev
variable {Q κ : Type} [AddCommGroup Q] [Fintype κ] {N : ℕ} [NeZero N]

theorem val_add_smul {x : Q} (hx : N • x = 0) (a b : ZMod N) :
    (a + b).val • x = a.val • x + b.val • x := by
  rw [ZMod.val_add, ← nsmul_eq_mod_nsmul _ hx, add_smul]

theorem val_mul_smul {x : Q} (hx : N • x = 0) (a b : ZMod N) :
    (a * b).val • x = b.val • a.val • x := by
  rw [ZMod.val_mul, ← nsmul_eq_mod_nsmul _ hx, mul_comm, mul_smul]

def ev (pt : κ → Q) (h : ∀ i, N • pt i = 0) : (κ → ZMod N) →+ Q :=
  AddMonoidHom.mk' (fun t => ∑ i, (t i).val • pt i) fun a b => by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => val_add_smul (h i) _ _

theorem ev_apply (pt : κ → Q) (h : ∀ i, N • pt i = 0) (t : κ → ZMod N) :
    ev pt h t = ∑ i, (t i).val • pt i := rfl

theorem nsmul_ev (pt : κ → Q) (h : ∀ i, N • pt i = 0) (t : κ → ZMod N) : N • ev pt h t = 0 := by
  rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod N), ZMod.natCast_self, zero_smul, map_zero]

theorem map_ev (g : Q →+ Q) {pt pt' : κ → Q} (h : ∀ i, N • pt i = 0) (h' : ∀ i, N • pt' i = 0)
    (M : Matrix κ κ (ZMod N)) (hM : ∀ j, g (pt j) = ∑ i, (M i j).val • pt' i) (t : κ → ZMod N) :
    g (ev pt h t) = ev pt' h' (M *ᵥ t) := by
  have : M *ᵥ t = ∑ j, fun i => M i j * t j := by
    funext i
    simp [mulVec, dotProduct, Finset.sum_apply]
  rw [this, map_sum, ev_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_nsmul, hM, ev_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => (val_mul_smul (h' i) _ _).symm

theorem ev_injective {pt : κ → Q} (h : ∀ i, N • pt i = 0)
    (hb : ∀ y : Q, N • y = 0 → ∃! c : κ → ZMod N, ∑ i, (c i).val • pt i = y) :
    Function.Injective (ev pt h) := fun a b hab =>
  (hb _ (nsmul_ev pt h b)).unique hab rfl

theorem det_eq_det [DecidableEq κ] (g : Q →+ Q) {pt pt' : κ → Q} (h : ∀ i, N • pt i = 0)
    (h' : ∀ i, N • pt' i = 0)
    (hb : ∀ y : Q, N • y = 0 → ∃! c : κ → ZMod N, ∑ i, (c i).val • pt i = y)
    (hb' : ∀ y : Q, N • y = 0 → ∃! c : κ → ZMod N, ∑ i, (c i).val • pt' i = y)
    (M M' : Matrix κ κ (ZMod N)) (hM : ∀ j, g (pt j) = ∑ i, (M i j).val • pt i)
    (hM' : ∀ j, g (pt' j) = ∑ i, (M' i j).val • pt' i) : M.det = M'.det := by
  choose P hP using fun j => (hb' _ (h j)).exists
  choose P' hP' using fun j => (hb _ (h' j)).exists
  have e1 := map_ev (AddMonoidHom.id Q) h h' (Matrix.of P)ᵀ fun j => (hP j).symm
  have e2 := map_ev (AddMonoidHom.id Q) h' h (Matrix.of P')ᵀ fun j => (hP' j).symm
  simp only [AddMonoidHom.id_apply] at e1 e2
  have f1 : (Matrix.of P)ᵀ * (Matrix.of P')ᵀ = 1 := by
    refine Matrix.mulVec_injective (funext fun t => ev_injective h' hb' ?_)
    rw [← mulVec_mulVec, ← e1, ← e2, one_mulVec]
  have f2 : (Matrix.of P)ᵀ * M = M' * (Matrix.of P)ᵀ := by
    refine Matrix.mulVec_injective (funext fun t => ev_injective h' hb' ?_)
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← e1, ← map_ev g h' h' M' hM', ← e1,
      ← map_ev g h h M hM]
  have hu := Matrix.isUnit_det_of_right_inverse f1
  have := congrArg Matrix.det f2
  rw [det_mul, det_mul, mul_comm] at this
  exact hu.mul_right_cancel this

end ev

theorem norm_det_eq (l : ℕ) [hl : Fact l.Prime] {κ Q : Type} [Fintype κ] [DecidableEq κ]
    [AddCommGroup Q] (τ : κ → ℕ → Q) (h1 : ∀ i n, (l ^ (n + 1)) • τ i n = 0)
    (hb : ∀ n (x : Q), (l ^ (n + 1)) • x = 0 →
      ∃! t : κ → ZMod (l ^ (n + 1)), ∑ j, (t j).val • τ j n = x)
    (f : Q →+ Q) (M : Matrix κ κ ℤ_[l])
    (hM : ∀ j n, f (τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (M k j)).val • τ k n)
    [Finite f.ker] : ‖M.det‖ = ‖((Nat.card f.ker : ℕ) : ℚ_[l])‖ := by
  have hev : ∀ n t, f (ev (fun i => τ i n) (fun i => h1 i n) t) =
      ev (fun i => τ i n) (fun i => h1 i n) ((M.map (PadicInt.toZModPow (n + 1))) *ᵥ t) :=
    fun n => map_ev f _ _ _ fun j => hM j n
  have hinj : ∀ n, Function.Injective (ev (fun i => τ i n) (fun i => h1 i n)) :=
    fun n => ev_injective _ (hb n)
  have hc0 : Nat.card f.ker ≠ 0 := Nat.card_pos.ne'
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv0
    funext i
    have key : ∀ n, PadicInt.toZModPow (n + 1) (Nat.card f.ker • v i) = 0 := by
      intro n
      have hk : ev (fun i => τ i n) (fun i => h1 i n) (PadicInt.toZModPow (n + 1) ∘ v) ∈ f.ker := by
        rw [AddMonoidHom.mem_ker, hev]
        have : (M.map (PadicInt.toZModPow (n + 1))) *ᵥ (PadicInt.toZModPow (n + 1) ∘ v) = 0 := by
          funext k
          rw [← RingHom.map_mulVec, hv]
          simp
        rw [this, map_zero]
      have h2 := congrArg Subtype.val (card_nsmul_eq_zero' (x := (⟨_, hk⟩ : f.ker)))
      rw [AddSubgroup.coe_nsmul, ← map_nsmul, ZeroMemClass.coe_zero,
        map_eq_zero_iff _ (hinj n)] at h2
      rw [map_nsmul]
      exact congrFun h2 i
    have : Nat.card f.ker • v i = 0 := by
      rw [← PadicInt.ext_of_toZModPow]
      intro n
      rw [map_zero]
      cases n with
      | zero =>
        have : Subsingleton (ZMod (l ^ 0)) := ZMod.subsingleton_iff.2 (pow_zero l)
        exact Subsingleton.elim _ _
      | succ n => exact key n
    rw [nsmul_eq_mul, mul_eq_zero] at this
    exact this.resolve_left (Nat.cast_ne_zero.2 hc0)
  set n := M.det.valuation + Nat.card f.ker with hn
  obtain ⟨c, hc⟩ : M.det ∣ (l : ℤ_[l]) ^ (n + 1) := by
    rw [PadicInt.unitCoeff_spec hdet, Units.mul_left_dvd]
    exact pow_dvd_pow _ (by omega)
  have a1 : M * (c • M.adjugate) = ((l : ℤ_[l]) ^ (n + 1)) • 1 := by
    rw [Matrix.mul_smul, mul_adjugate, smul_smul, hc, mul_comm]
  have a2 : (c • M.adjugate) * M = ((l : ℤ_[l]) ^ (n + 1)) • 1 := by
    rw [Matrix.smul_mul, adjugate_mul, smul_smul, hc, mul_comm]
  rw [norm_index_range l M hdet, ← card_ker_eq_index l M _ _ a1 a2,
    norm_card_eq_torsion l f.ker (n + 1) (by omega)]
  congr 2
  refine Nat.card_eq_of_bijective (fun t => ⟨⟨ev (fun i => τ i n) (fun i => h1 i n) t.1, ?_⟩,
    Subtype.ext (nsmul_ev _ _ _)⟩) ⟨fun a b hab => ?_, fun x => ?_⟩
  · rw [AddMonoidHom.mem_ker, hev, t.2, map_zero]
  · exact Subtype.ext (hinj n (congrArg (fun z => z.1.1) hab))
  · obtain ⟨t, ht, -⟩ := hb n x.1.1 (congrArg Subtype.val x.2)
    refine ⟨⟨t, hinj n ?_⟩, Subtype.ext (Subtype.ext ht)⟩
    rw [← hev, ev_apply, ht, map_zero]
    exact x.1.2

end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem exists_padic_matrix : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (Q : Type) [AddCommGroup Q] (s : Module.End ℤ Q), (∀ j : ℕ, Nat.card {x : Q // l ^ j • x = 0} = l ^ (m * j)) → ∃ U : Matrix (Fin m) (Fin m) ℤ_[l], (∀ F : Polynomial ℤ, Finite {x : Q // Polynomial.aeval s F x = 0} → ‖(Polynomial.aeval U F).det‖ = ‖((Nat.card {x : Q // Polynomial.aeval s F x = 0} : ℕ) : ℚ_[l])‖) ∧ (∀ F : Polynomial ℤ, Polynomial.aeval U F = 0 → ∀ (j : ℕ) (x : Q), l ^ j • x = 0 → Polynomial.aeval s F x = 0) ∧ ∀ (j : ℕ) (pt : Fin m → Q) (Mat : Matrix (Fin m) (Fin m) (ZMod (l ^ j))), (∀ i, l ^ j • pt i = 0) → (∀ y : Q, l ^ j • y = 0 → ∃! c : Fin m → ZMod (l ^ j), ∑ i, (c i).val • pt i = y) → (∀ i, s (pt i) = ∑ i', (Mat i' i).val • pt i') → PadicInt.toZModPow j U.det = Mat.det := by
  intro l hl m Q _ s h
  obtain ⟨τ, h1, h2, h3⟩ := exists_tower l m Q h
  obtain ⟨hb0, ρ0, hρ0⟩ := GlobalTheory.tate_basis_matrix l (Fin m) Q τ h1 h2 h3
  have hb : ∀ n (x : Q), (l ^ (n + 1)) • x = 0 →
      ∃! t : Fin m → ZMod (l ^ (n + 1)), ∑ j, (t j).val • τ j n = x := by
    intro n x hx
    simpa only [eq_comm] using hb0 n x hx
  let ρ : Module.End ℤ Q →+* Matrix (Fin m) (Fin m) ℤ_[l] :=
    ρ0.comp (addMonoidEndRingEquivInt Q).symm.toRingHom
  have hρ : ∀ (f : Module.End ℤ Q) j n,
      f (τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (ρ f k j)).val • τ k n :=
    fun f j n => hρ0 ((addMonoidEndRingEquivInt Q).symm f) j n
  have hF : ∀ F : Polynomial ℤ, Polynomial.aeval (ρ s) F = ρ (Polynomial.aeval s F) :=
    fun F => Polynomial.aeval_algHom_apply ρ.toIntAlgHom s F
  refine ⟨ρ s, fun F hfin => ?_, fun F h0 j x hx => ?_, fun j pt Mat hpt hbp hs => ?_⟩
  · rw [hF]
    have : Finite (Polynomial.aeval s F).toAddMonoidHom.ker := hfin
    exact norm_det_eq l τ h1 hb (Polynomial.aeval s F).toAddMonoidHom _ (hρ _)
  · obtain ⟨t, ht, -⟩ := hb j x (by rw [pow_succ', mul_smul, hx, smul_zero])
    rw [← ht, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_nsmul, hρ, ← hF, h0]
    simp
  · cases j with
    | zero =>
      have : Subsingleton (ZMod (l ^ 0)) := ZMod.subsingleton_iff.2 (pow_zero l)
      exact Subsingleton.elim _ _
    | succ n =>
      rw [RingHom.map_det]
      exact det_eq_det s.toAddMonoidHom (fun i => h1 i n) hpt (hb n) hbp _ _
        (fun j => hρ s j n) hs

end TorsionMatrix
end GlobalTheory
