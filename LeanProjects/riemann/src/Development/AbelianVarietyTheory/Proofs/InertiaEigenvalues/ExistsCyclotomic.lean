import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfAssembleMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsPrimitiveRootSubIsUnitOfDvdSubOne

noncomputable section
namespace GlobalTheory.CycRing
open scoped LaurentSeries PowerSeries
open PowerSeries GlobalTheory.PhiGam GlobalTheory.PhiGam.Inh GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters GlobalTheory.PsiLemmaCompare GlobalTheory.PsiShiftProof

section General
variable {k : Type} [Field k]

theorem const_hom (σ : k⟦X⟧ →ₐ[k] k⟦X⟧) (h : X ∣ σ X) (a : k⟦X⟧) : constantCoeff (σ a) = constantCoeff a := by
  obtain ⟨c, hc⟩ := h
  have hC : σ (C (constantCoeff a)) = C (constantCoeff a) := σ.commutes _
  conv_lhs => rw [eq_X_mul_shift_add_const a, map_add, map_mul, hc, hC]
  simp

theorem dvd_hom_sub (σ : k⟦X⟧ →ₐ[k] k⟦X⟧) (n : ℕ) (h : X ^ n ∣ σ X - X) (a : k⟦X⟧) : X ^ n ∣ σ a - a := by
  have key : ∀ m ≤ n, ∀ a : k⟦X⟧, X ^ m ∣ σ a - a := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro hm a
      have hC : σ (C (constantCoeff a)) = C (constantCoeff a) := σ.commutes _
      set s : k⟦X⟧ := mk fun p => coeff (p + 1) a
      have ha : a = X * s + C (constantCoeff a) := eq_X_mul_shift_add_const a
      have : σ a - a = (σ X - X) * σ s + X * (σ s - s) := by
        conv_lhs => rw [ha, map_add, map_mul, hC]
        ring
      rw [this]
      refine dvd_add (((pow_dvd_pow _ hm).trans h).mul_right _) ?_
      rw [pow_succ']
      exact mul_dvd_mul_left _ (ih (by omega) s)
  exact key n le_rfl a

theorem mem_range_of_step (σ : k⟦X⟧ →ₐ[k] k⟦X⟧) (h : X ∣ σ X) (S : k⟦X⟧ → Prop)
    (hS : ∀ b, S b → ∃ (c : k) (b' : k⟦X⟧), S b' ∧ b = C c + σ X * b') (b : k⟦X⟧) (hb : S b) :
    ∃ a, σ a = b := by
  choose c T hT hb' using hS
  let T' : {b // S b} → {b // S b} := fun b => ⟨T b.1 b.2, hT b.1 b.2⟩
  let A : {b // S b} → k⟦X⟧ := fun b => mk fun n => c (T'^[n] b).1 (T'^[n] b).2
  have hA : ∀ b, A b = X * A (T' b) + C (c b.1 b.2) := fun b => by
    ext n
    cases n with
    | zero => simp [A]
    | succ n => simp [A, coeff_succ_X_mul, coeff_C]
  have key : ∀ (N : ℕ) (b : {b // S b}), X ^ N ∣ σ (A b) - b.1 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      intro b
      have hC : σ (C (c b.1 b.2)) = C (c b.1 b.2) := σ.commutes _
      have : σ (A b) - b.1 = σ X * (σ (A (T' b)) - (T' b).1) := by
        have e1 := congrArg σ (hA b)
        have e2 : b.1 = C (c b.1 b.2) + σ X * (T' b).1 := hb' b.1 b.2
        rw [map_add, map_mul, hC] at e1
        linear_combination e1 - e2
      rw [this, pow_succ']
      exact mul_dvd_mul h (ih _)
  refine ⟨A ⟨b, hb⟩, ?_⟩
  rw [← sub_eq_zero]
  ext n
  exact X_pow_dvd_iff.1 (key (n + 1) ⟨b, hb⟩) n (by omega)

def sb (f : k⟦X⟧) (h : X ∣ f) : k⟦X⟧ →ₐ[k] k⟦X⟧ :=
  substAlgHom (HasSubst.of_constantCoeff_zero' (X_dvd_iff.1 h))

theorem sb_apply (f : k⟦X⟧) (h : X ∣ f) (a : k⟦X⟧) : sb f h a = a.subst f := by
  rw [sb, coe_substAlgHom]

theorem sb_X (f : k⟦X⟧) (h : X ∣ f) : sb f h X = f := substAlgHom_X _

theorem sb_sb {f g f' g' : k⟦X⟧} {hf : X ∣ f} {hg : X ∣ g} {hf' : X ∣ f'} {hg' : X ∣ g'}
    (h : sb g hg f = sb g' hg' f') (a : k⟦X⟧) : sb g hg (sb f hf a) = sb g' hg' (sb f' hf' a) := by
  have s := fun {f : k⟦X⟧} (h : X ∣ f) => HasSubst.of_constantCoeff_zero' (X_dvd_iff.1 h)
  simp only [sb_apply] at h ⊢
  rw [subst_comp_subst_apply (s hf) (s hg), subst_comp_subst_apply (s hf') (s hg'), h]

end General

section Roots
variable (l : ℕ) [hl : Fact l.Prime]

def mu : Finset ℤ_[l] := Polynomial.nthRootsFinset (l - 1) 1

variable {l}

theorem pred_pos : 0 < l - 1 := by have := hl.out.two_le; omega

theorem mem_mu {z : ℤ_[l]} : z ∈ mu l ↔ z ^ (l - 1) = 1 := Polynomial.mem_nthRootsFinset pred_pos _

theorem exists_root : ∃ ω : ℤ_[l], IsPrimitiveRoot ω (l - 1) ∧
    ∀ i j : ℕ, i < l - 1 → j < l - 1 → i ≠ j → IsUnit (ω ^ i - ω ^ j) :=
  exists_isPrimitiveRoot_sub_isUnit_of_dvd_sub_one hl.out PadicInt.irreducible_p.not_isUnit _ dvd_rfl

theorem image_mu : (mu l).image PadicInt.zmodRepr = (Finset.range l).erase 0 ∧
    Set.InjOn PadicInt.zmodRepr (mu l : Set ℤ_[l]) := by
  obtain ⟨ω, hω, hu⟩ := exists_root (l := l)
  haveI : NeZero (l - 1) := ⟨pred_pos.ne'⟩
  have inj : Set.InjOn PadicInt.zmodRepr (mu l : Set ℤ_[l]) := by
    intro x hx y hy e
    obtain ⟨i, hi, rfl⟩ := hω.eq_pow_of_pow_eq_one (mem_mu.1 hx)
    obtain ⟨j, hj, rfl⟩ := hω.eq_pow_of_pow_eq_one (mem_mu.1 hy)
    by_contra hne
    have h1 := sub_mem (PadicInt.sub_zmodRepr_mem (ω ^ i)) (PadicInt.sub_zmodRepr_mem (ω ^ j))
    rw [e, sub_sub_sub_cancel_right] at h1
    exact h1 (hu i j hi hj fun h => hne (by rw [h]))
  refine ⟨Finset.eq_of_subset_of_card_le (fun a ha => ?_) ?_, inj⟩
  · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 ha
    refine Finset.mem_erase.2 ⟨fun h0 => ?_, Finset.mem_range.2 z.zmodRepr_lt_p⟩
    have h1 := PadicInt.sub_zmodRepr_mem z
    rw [h0, Nat.cast_zero, sub_zero] at h1
    exact h1 (IsUnit.of_pow_eq_one (mem_mu.1 hz) pred_pos.ne')
  · rw [Finset.card_image_of_injOn inj, mu, hω.card_nthRootsFinset,
      Finset.card_erase_of_mem (Finset.mem_range.2 hl.out.pos), Finset.card_range]

theorem sum_mu_mul {M : Type} [AddCommMonoid M] (f : ℤ_[l] → M) {t : ℤ_[l]} (ht : t ^ (l - 1) = 1) :
    ∑ z ∈ mu l, f (t * z) = ∑ z ∈ mu l, f z := by
  have h1 : t * t ^ (l - 1 - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel pred_pos, ht]
  refine Finset.sum_nbij' (fun z => t * z) (fun z => t ^ (l - 1 - 1) * z) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro z hz
    rw [mem_mu] at hz ⊢
    rw [mul_pow, ht, hz, one_mul]
  · intro z hz
    rw [mem_mu] at hz ⊢
    rw [mul_pow, pow_right_comm, ht, hz, one_pow, one_mul]
  · intro z _
    simp only [← mul_assoc, mul_comm _ t, h1, one_mul]
  · intro z _
    simp only [← mul_assoc, h1, one_mul]

end Roots

section Cyc
variable {k : Type} [Field k] {l : ℕ} [hl : Fact l.Prime] [CharP k l]

instance charP_powerSeries : CharP k⟦X⟧ l := charP_of_injective_algebraMap (algebraMap k k⟦X⟧).injective l

theorem hom_opp' (σ : k⟦X⟧ →ₐ[k] k⟦X⟧) (t : ℤ_[l]) (h : σ X = onePlusPow k l t - 1) (z : ℤ_[l]) :
    σ (onePlusPow k l z) = onePlusPow k l (t * z) := by
  have hX : X ∣ σ X := h ▸ opp_dvd t
  have h' : σ (1 + X) = onePlusPow k l t := by rw [map_add, map_one, h]; ring
  have key : ∀ N : ℕ, X ^ N ∣ σ (onePlusPow k l z) - onePlusPow k l (t * z) := by
    intro N
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec N z)
    have hz : z = (z.appr N : ℕ) + ((l ^ N : ℕ) : ℤ_[l]) * w := by push_cast; linear_combination hw
    have hz' : t * z = (z.appr N : ℕ) * t + ((l ^ N : ℕ) : ℤ_[l]) * (t * w) := by
      push_cast; linear_combination t * hw
    have h1 : X ∣ σ (onePlusPow k l w) - onePlusPow k l (t * w) := by
      obtain ⟨c, hc⟩ := opp_dvd (k := k) w
      have h2 : X ∣ σ (onePlusPow k l w) - 1 := by
        rw [← map_one σ, ← map_sub, hc, map_mul]; exact hX.mul_right _
      simpa using dvd_sub h2 (opp_dvd (t * w))
    rw [hz', hz, opp_add, opp_add, opp_nat, opp_mul, opp_mul, opp_mul, map_mul, map_pow, map_pow, h', ← hz,
      ← mul_sub, ← sub_pow_char_pow]
    exact ((pow_dvd_pow _ (Nat.lt_pow_self hl.out.one_lt).le).trans (pow_dvd_pow_of_dvd h1 _)).mul_left _
  rw [← sub_eq_zero]
  ext n
  exact X_pow_dvd_iff.1 (key (n + 1)) n (by omega)

variable (k l) in

def trace (m : ℤ_[l]) : k⟦X⟧ := 1 + ∑ z ∈ mu l, onePlusPow k l (m * z)

theorem hom_trace (σ : k⟦X⟧ →ₐ[k] k⟦X⟧) (t : ℤ_[l]) (h : σ X = onePlusPow k l t - 1) (m : ℤ_[l]) :
    σ (trace k l m) = trace k l (t * m) := by
  simp only [trace, map_add, map_one, map_sum, hom_opp' σ t h, mul_assoc]

theorem trace_mul {t : ℤ_[l]} (ht : t ^ (l - 1) = 1) (m : ℤ_[l]) : trace k l (t * m) = trace k l m := by
  have := sum_mu_mul (fun z => onePlusPow k l (m * z)) ht
  simp only [trace, ← this, mul_comm t m, mul_assoc]

theorem trace_l : trace k l (l * 1) = trace k l 1 ^ l := by
  simp only [trace, add_pow_char, sum_pow_char, one_pow, mul_one, one_mul, opp_mul]

theorem trace_one : ∃ c : k⟦X⟧, trace k l 1 = X ^ (l - 1) * (1 + X * c) := by
  have h1 : ∀ z : ℤ_[l], X ^ l ∣ onePlusPow k l (1 * z) - (1 + X) ^ z.zmodRepr := by
    intro z
    have h := PadicInt.sub_zmodRepr_mem z
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
    obtain ⟨w, hw⟩ := h
    have hz : z = (z.zmodRepr : ℕ) + (l : ℤ_[l]) * w := by linear_combination hw
    conv_rhs => rw [one_mul, hz, opp_add, opp_nat, opp_mul, ← hz, ← mul_sub_one, ← one_pow l, ← sub_pow_char]
    exact (pow_dvd_pow_of_dvd (opp_dvd w) _).mul_left _
  have h2 : 1 + ∑ z ∈ mu l, (1 + X : k⟦X⟧) ^ z.zmodRepr = X ^ (l - 1) := by
    rw [← Finset.sum_image (f := fun a => (1 + X : k⟦X⟧) ^ a) image_mu.2, image_mu.1]
    have h3 := Finset.add_sum_erase (Finset.range l) (fun a => (1 + X : k⟦X⟧) ^ a) (Finset.mem_range.2 hl.out.pos)
    rw [pow_zero] at h3
    rw [h3]
    apply mul_right_cancel₀ (X_ne_zero (R := k))
    have h4 := geom_sum_mul (1 + X : k⟦X⟧) l
    rw [add_sub_cancel_left, frob_eq] at h4
    rw [h4, ← pow_succ, Nat.sub_add_cancel hl.out.pos]
  obtain ⟨c, hc⟩ := Finset.dvd_sum (s := mu l) fun z _ => h1 z
  refine ⟨c, ?_⟩
  have h5 : (X : k⟦X⟧) ^ l = X ^ (l - 1) * X := by rw [← pow_succ, Nat.sub_add_cancel hl.out.pos]
  rw [Finset.sum_sub_distrib, h5] at hc
  rw [trace]
  linear_combination hc + h2

variable (k) in

def act (t : ℤ_[l]) : k⟦X⟧ →ₐ[k] k⟦X⟧ := sb (onePlusPow k l t - 1) (opp_dvd t)

theorem act_X (t : ℤ_[l]) : act k t X = onePlusPow k l t - 1 := sb_X _ _

theorem act_eq (t : ℤ_[l]) (b : k⟦X⟧) : deltaPi k l t b = act k t b := (sb_apply _ _ b).symm

theorem act_X_eq (t : ℤ_[l]) : ∃ e : k⟦X⟧, act k t X = X * e ∧ constantCoeff e = FrobeniusBinomialReduction.red k l t := by
  obtain ⟨e, he⟩ := opp_dvd (k := k) t
  refine ⟨e, (act_X t).trans he, ?_⟩
  have := congrArg (coeff (0 + 1)) he
  rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, map_sub, onePlusPow, coeff_map,
    binomialSeries_coeff] at this
  rw [← this]
  simp [coeff_one, FrobeniusBinomialReduction.red]

variable (l) in

def Inv (b : k⟦X⟧) : Prop := ∀ z : ℤ_[l], z ^ (l - 1) = 1 → act k z b = b

theorem inv_trace (m : ℤ_[l]) : Inv l (trace k l m) := fun z hz => by
  rw [hom_trace _ z (act_X z), trace_mul hz]

theorem trace_ne : trace k l 1 ≠ 0 := by
  obtain ⟨c, hc⟩ := trace_one (k := k) (l := l)
  rw [hc]
  refine mul_ne_zero (pow_ne_zero _ X_ne_zero) fun h => ?_
  simpa using congrArg constantCoeff h

theorem X_dvd_trace : X ∣ trace k l 1 := by
  obtain ⟨c, hc⟩ := trace_one (k := k) (l := l)
  rw [hc]
  exact (dvd_pow_self _ pred_pos.ne').mul_right _

theorem Inv.of_mul {b : k⟦X⟧} (h : Inv l (trace k l 1 * b)) : Inv l b := fun z hz => by
  have := h z hz
  rw [map_mul, inv_trace 1 z hz] at this
  exact mul_left_cancel₀ trace_ne this

theorem Inv.pow_dvd {b : k⟦X⟧} (h : Inv l b) (hX : X ∣ b) : X ^ (l - 1) ∣ b := by
  obtain ⟨ω, hω, hu⟩ := exists_root (l := l)
  obtain ⟨e, he, he0⟩ := act_X_eq (k := k) ω
  have key : ∀ m, m + 1 ≤ l - 1 → X ^ (m + 1) ∣ b := by
    intro m
    induction m with
    | zero => simpa using fun _ => hX
    | succ m ih =>
      intro hm
      obtain ⟨u, rfl⟩ := ih (by omega)
      have h1 := h ω hω.pow_eq_one
      rw [map_mul, map_pow, he, mul_pow, mul_assoc] at h1
      have h2 := congrArg constantCoeff (mul_left_cancel₀ (pow_ne_zero _ X_ne_zero) h1)
      rw [map_mul, map_pow, he0, const_hom _ ⟨e, he⟩] at h2
      have h3 := ((hu (m + 1) 0 (by omega) pred_pos (by omega)).map (FrobeniusBinomialReduction.red k l)).ne_zero
      rw [map_sub, map_pow, pow_zero, map_one] at h3
      rw [pow_succ _ (m + 1)]
      refine mul_dvd_mul_left _ (X_dvd_iff.2 ((mul_eq_zero.1 ?_).resolve_left h3))
      linear_combination h2
  have := key (l - 1 - 1) (Nat.sub_add_cancel pred_pos).le
  rwa [Nat.sub_add_cancel pred_pos] at this

variable (k l) in

def emb : k⟦X⟧ →ₐ[k] k⟦X⟧ := sb (trace k l 1) X_dvd_trace

theorem emb_X : emb k l X = trace k l 1 := sb_X _ _

theorem X_dvd_emb : X ∣ emb k l X := emb_X (k := k) (l := l) ▸ X_dvd_trace

theorem emb_X_ne : emb k l X ≠ 0 := emb_X (k := k) (l := l) ▸ trace_ne

theorem inv_iff (b : k⟦X⟧) : Inv l b ↔ ∃ a, emb k l a = b := by
  constructor
  · refine mem_range_of_step _ X_dvd_emb (Inv l) (fun b hb => ?_) b
    have h1 : Inv l (b - C (constantCoeff b)) := fun z hz => by
      have hC : act k z (C (constantCoeff b)) = C (constantCoeff b) := (act k z).commutes _
      rw [map_sub, hb z hz, hC]
    obtain ⟨c, hc⟩ := trace_one (k := k) (l := l)
    have hu : IsUnit (1 + X * c) := by rw [isUnit_iff_constantCoeff]; simp
    have h2 := h1.pow_dvd (X_dvd_iff.2 (by simp))
    rw [← hu.mul_right_dvd, ← hc] at h2
    obtain ⟨b', hb'⟩ := h2
    refine ⟨constantCoeff b, b', Inv.of_mul (hb' ▸ h1), ?_⟩
    rw [emb_X]
    linear_combination hb'
  · rintro ⟨a, rfl⟩ z hz
    have s := fun {f : k⟦X⟧} (h : X ∣ f) => HasSubst.of_constantCoeff_zero' (X_dvd_iff.1 h)
    have := inv_trace (k := k) 1 z hz
    simp only [act, emb, sb_apply] at this ⊢
    rw [subst_comp_subst_apply (s X_dvd_trace) (s (opp_dvd z)), this]

variable (k l) in

def fr : k⟦X⟧ →ₐ[k] k⟦X⟧ := sb (X ^ l) (dvd_pow_self _ hl.out.ne_zero)

variable (k l) in

def ga : k⟦X⟧ →ₐ[k] k⟦X⟧ := sb ((1 + X) ^ (1 + l) - 1) (X_dvd_iff.2 gam_const)

theorem fr_X : fr k l X = onePlusPow k l l - 1 := by rw [opp_nat, frob_eq]; exact sb_X _ _

theorem ga_X : ga k l X = onePlusPow k l (1 + l : ℕ) - 1 := by rw [opp_nat]; exact sb_X _ _

theorem emb_fr (a : k⟦X⟧) : emb k l (fr k l a) = fr k l (emb k l a) := by
  refine sb_sb ?_ a
  change emb k l _ = fr k l _
  rw [hom_trace _ _ fr_X, trace_l, map_pow, emb_X]

theorem fr_ga (a : k⟦X⟧) : fr k l (ga k l a) = ga k l (fr k l a) := by
  refine sb_sb ?_ a
  change fr k l _ = ga k l _
  rw [← frob_eq, ← opp_nat, ← opp_nat, map_sub, map_sub, hom_opp' _ _ fr_X, hom_opp' _ _ ga_X, map_one, map_one,
    mul_comm]

theorem ga_trace : ∃ κ : k⟦X⟧, constantCoeff κ = 1 ∧
    ga k l (trace k l 1) = emb k l (X * (1 - κ * X)) := by
  obtain ⟨c, hc⟩ := trace_one (k := k) (l := l)
  have h5 : (X : k⟦X⟧) ^ l = X ^ (l - 1) * X := by rw [← pow_succ, Nat.sub_add_cancel hl.out.pos]
  set e : k⟦X⟧ := 1 + X ^ (l - 1) * (1 + X) with he
  have hX : ga k l X = X * e := by
    rw [ga, sb_X, pow_add, pow_one, add_pow_char, one_pow, h5, he]; ring
  obtain ⟨s, hs⟩ := dvd_hom_sub (ga k l) l ⟨1 + X, by rw [hX, he, h5]; ring⟩ (1 + X * c)
  obtain ⟨u, hu⟩ : IsUnit (1 + X * c) := by rw [isUnit_iff_constantCoeff]; simp
  have hS := geom_sum_mul e (l - 1)
  set S := ∑ i ∈ Finset.range (l - 1), e ^ i with hSd
  have hS0 : constantCoeff S = -1 := by
    simp [hSd, he, pred_pos.ne', Nat.cast_pred hl.out.pos]
  have hui : (1 + X * c) * ((u⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 1 := by rw [← hu]; simp
  generalize ((u⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = ui at hui
  have hui0 : constantCoeff ui = 1 := by simpa using congrArg constantCoeff hui
  set κ' := -(S * (1 + X) * (1 + X * c + X ^ (l - 1) * X * s) + X * s) * ui ^ 2 with hκ'
  have key : ga k l (trace k l 1) = trace k l 1 * (1 - trace k l 1 * κ') := by
    rw [h5, sub_eq_iff_eq_add'] at hs
    rw [hc, map_mul, map_pow, hX, mul_pow, hs, hκ']
    have hS' : e ^ (l - 1) = 1 + S * (X ^ (l - 1) * (1 + X)) := by rw [he] at hS ⊢; linear_combination -hS
    rw [hS']
    linear_combination (-(X ^ (l - 1)) ^ 2 * (S * (1 + X) * (1 + X * c + X ^ (l - 1) * X * s) + X * s) *
      ((1 + X * c) * ui + 1)) * hui
  have hinv : Inv l κ' := by
    have h1 : Inv l (trace k l 1 * (1 - trace k l 1 * κ')) := by
      rw [← key, hom_trace _ _ ga_X]; exact inv_trace _
    refine Inv.of_mul fun z hz => ?_
    have := h1.of_mul z hz
    rw [map_sub, map_one] at this
    exact sub_right_injective this
  obtain ⟨κ, hκ⟩ := (inv_iff κ').1 hinv
  refine ⟨κ, ?_, ?_⟩
  · rw [← const_hom _ X_dvd_emb, hκ, hκ']
    simp [hS0, hui0]
  · rw [key, map_mul, map_sub, map_mul, map_one, hκ, emb_X, mul_comm κ']

end Cyc

theorem exists_cyclotomic : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l], 5 ≤ l →
    ∃ (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι ∧
      ι (vv k) = ((1 + ∑ᶠ z : {z : ℤ_[l] // z ^ (l - 1) = 1}, GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow k l z.1 : k⟦X⟧) :
        k⸨X⸩) := by
  intro l hl k _ _ _
  obtain ⟨κ, hκ0, hκ⟩ := ga_trace (k := k) (l := l)
  obtain ⟨c, hc⟩ := trace_one (k := k) (l := l)
  let ι := extend (emb k l) emb_X_ne
  have hι : ∀ a : k⟦X⟧, ι (a : k⸨X⸩) = ((emb k l a : k⟦X⟧) : k⸨X⸩) := extend_coe _ _
  have inj : Function.Injective (emb k l) := fun a b h =>
    HahnSeries.ofPowerSeries_injective (ι.toRingHom.injective ((hι a).trans (h ▸ (hι b).symm)))
  let g : k⟦X⟧ →ₐ[k] k⟦X⟧ := sb (X * (1 - κ * X)) (dvd_mul_right _ _)
  have gX : g X = X * (1 - κ * X) := sb_X _ _
  have gne : g X ≠ 0 := by
    rw [gX]
    refine mul_ne_zero X_ne_zero fun h => ?_
    simpa using congrArg constantCoeff h
  have fX : fr k l X = X ^ l := sb_X _ _
  have fne : fr k l X ≠ 0 := fX ▸ pow_ne_zero _ X_ne_zero
  have hg : ∀ a, emb k l (g a) = ga k l (emb k l a) := sb_sb hκ.symm
  have hv : ι (vv k) = ((trace k l 1 : k⟦X⟧) : k⸨X⸩) := by rw [vv_eq_coe_X, hι, emb_X]
  refine ⟨⟨extend (fr k l) fne, extend g gne, fun a => ⟨_, extend_coe _ _ a⟩, fun a => ⟨_, extend_coe _ _ a⟩,
    ⟨1, ?_⟩, ⟨κ, hκ0, ?_⟩, fun x => ?_⟩, ι, ⟨?_, fun a => ⟨_, hι a⟩, fun b => ?_, fun x => ?_,
    fun a b hab => ?_⟩, ?_⟩
  · rw [vv_eq_coe_X, extend_coe, fX]; simp
  · rw [vv_eq_coe_X, extend_coe, gX]; simp
  · refine Inh.algHom_ext (f := (extend (fr k l) fne).comp (extend g gne))
      (g := (extend g gne).comp (extend (fr k l) fne)) (fun a => ?_) x
    simp only [AlgHom.comp_apply, extend_coe]
    congr 1
    apply inj
    rw [emb_fr, hg, hg, emb_fr, fr_ga]
  · obtain ⟨u, hu⟩ : IsUnit (1 + X * c) := by rw [isUnit_iff_constantCoeff]; simp
    exact ⟨u, by rw [hv, hc, hu, map_mul, map_pow, ← vv_eq_coe_X, mul_comm]⟩
  · simp only [act_eq, hι]
    exact (inv_iff b).trans (exists_congr fun a => HahnSeries.ofPowerSeries_injective.eq_iff.symm)
  · have : ι.toRingHom.comp (extend (fr k l) fne).toRingHom = (phiPi k l).comp ι.toRingHom := by
      refine hom_ext fun a => ?_
      change ι (extend (fr k l) fne a) = phiPi k l (ι a)
      rw [extend_coe, hι, hι, phi_eq_subst, substHom_coe, frob_eq, emb_fr, fr, sb_apply]
    exact RingHom.congr_fun this x
  · rw [hι] at hab
    change ι (extend g gne a) = _
    rw [extend_coe, hι, hg, HahnSeries.ofPowerSeries_injective hab, ga, sb_apply, gammaPi]
  · rw [hv, trace, finsum_subtype_eq_finsum_cond (f := fun z => onePlusPow k l z) (fun z => z ^ (l - 1) = 1),
      finsum_cond_eq_sum_of_cond_iff _ (t := mu l) fun _ => mem_mu.symm]
    simp only [one_mul]

end GlobalTheory.CycRing
