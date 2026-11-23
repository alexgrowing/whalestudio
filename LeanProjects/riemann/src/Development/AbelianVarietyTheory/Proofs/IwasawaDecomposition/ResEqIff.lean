import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMemWpNormSubLtOne
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ClosedBallValuationSubringToSubring

noncomputable section
namespace GlobalTheory.MemLoc.FrobLaws
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc Polynomial

theorem endo_root {k : Type} [CommRing k] [IsDomain k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    (φ : k →+* k) {a : k} {m : ℕ} (hm : 0 < m) (hpm : ¬ p ∣ m) (ha : a ^ m = 1) :
    ∃ n : ℕ, φ a = a ^ (p ^ n) := by
  have hf : 0 < m.totient := Nat.totient_pos.2 hm
  have hcop : p.Coprime m := (Nat.Prime.coprime_iff_not_dvd hp.out).2 hpm
  let F : Subring k := RingHom.eqLocus (iterateFrobenius k p m.totient) (RingHom.id k)
  have hF : ∀ y : k, y ∈ F ↔ y ^ (p ^ m.totient) = y := fun y => Iff.rfl
  have haF : a ∈ F := by
    rw [hF]
    have h1 := Nat.ModEq.pow_totient hcop
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.out.pos)).1 h1.symm
    have : p ^ m.totient = m * c + 1 := by
      have := Nat.one_le_pow m.totient p hp.out.pos
      omega
    rw [this, pow_succ, pow_mul, ha, one_pow, one_mul]
  have hfin : (F : Set k).Finite := by
    have hne : (X ^ (p ^ m.totient) - X : k[X]) ≠ 0 :=
      (monic_X_pow_sub (by
        rw [degree_X]
        exact_mod_cast Nat.one_lt_pow hf.ne' hp.out.one_lt)).ne_zero
    refine (Polynomial.rootSet_finite (X ^ (p ^ m.totient) - X : k[X]) k).subset fun y hy => ?_
    rw [Polynomial.mem_rootSet]
    refine ⟨hne, ?_⟩
    have := (hF y).1 hy
    simp [this]
  haveI : Finite F := hfin
  letI : Field F := (Finite.isField_of_domain F).toField
  haveI : CharP F p := CharP.subring k p F
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  let ψ : F →+* F := (φ.comp F.subtype).codRestrict F fun y => by
    rw [hF]
    show φ y ^ _ = φ y
    rw [← map_pow, (hF y).1 y.2]
  let ψ' : F →ₐ[ZMod p] F :=
    { ψ with commutes' := fun r =>
        RingHom.congr_fun (RingHom.ext_zmod (ψ.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) F)) r }
  obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) F).2 ψ'
  refine ⟨j, ?_⟩
  have h1 : ψ' ⟨a, haF⟩ = (⟨a, haF⟩ : F) ^ (p ^ (j : ℕ)) := by
    rw [← hj]
    simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]
  exact congrArg Subtype.val h1

variable {l : ℕ} [hl : Fact l.Prime]

theorem norm_gal (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ := (spectralNorm_eq_of_equiv g x).symm

def OO (l : ℕ) [Fact l.Prime] : Subring (Om l) := GlobalTheory.ClosedBallValuationSubring.closedBallSubring (Om l)

def MM (l : ℕ) [Fact l.Prime] : Ideal (OO l) := GlobalTheory.ClosedBallValuationSubring.openBallIdeal (Om l)

theorem mem_MM (x : OO l) : x ∈ MM l ↔ ‖(x : Om l)‖ < 1 := Iff.rfl

instance MM_prime : (MM l).IsPrime where
  ne_top' := by
    rw [Ideal.ne_top_iff_one, mem_MM]; simp
  mem_or_mem' := fun {a b} h => by
    rw [mem_MM] at h
    by_contra hc
    rw [not_or, mem_MM, mem_MM, not_lt, not_lt] at hc
    have : ‖(a : Om l) * b‖ < 1 := h
    rw [norm_mul] at this
    exact absurd this (not_lt.2 (one_le_mul_of_one_le_of_one_le hc.1 hc.2))

abbrev kk (l : ℕ) [Fact l.Prime] : Type := OO l ⧸ MM l

abbrev res : OO l →+* kk l := Ideal.Quotient.mk (MM l)

theorem res_eq_iff (a b : OO l) : res a = res b ↔ ‖(a : Om l) - b‖ < 1 := Ideal.Quotient.eq

instance kk_char : CharP (kk l) l := by
  refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
  rw [← map_natCast (res (l := l)), Ideal.Quotient.eq_zero_iff_mem, mem_MM]
  have h : ‖((l : ℚ_[l]) : Om l)‖ < 1 := by
    rw [PadicAlgCl.norm_extends]; exact Padic.norm_p_lt_one
  simpa using h

def galO (g : GQ l) : OO l →+* OO l :=
  ((g : Om l →+* Om l).comp (OO l).subtype).codRestrict (OO l) fun x => by
    show ‖g x‖ ≤ 1
    rw [norm_gal]; exact x.2

def galK (g : GQ l) : kk l →+* kk l :=
  Ideal.quotientMap (MM l) (galO g) fun x hx => by
    show ‖g x‖ < 1
    rw [norm_gal]; exact hx

theorem galK_res (g : GQ l) (x : OO l) : galK g (res x) = res (galO g x) := rfl

theorem norm_root {ζ : Om l} {m : ℕ} (hm : 0 < m) (h : ζ ^ m = 1) : ‖ζ‖ = 1 := by
  have := congrArg norm h
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 this

theorem res_inj {a b : OO l} {m : ℕ} (hm : 0 < m) (hlm : ¬ l ∣ m) (ha : a ^ m = 1) (hb : b ^ m = 1)
    (h : res a = res b) : a = b := by
  by_contra hne
  have h1 := (Commute.all a b).geom_sum₂_mul m
  rw [ha, hb, sub_self] at h1
  have h2 := (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 hne)
  have h3 := congrArg res h2
  simp only [map_sum, map_mul, map_pow, map_zero, ← h] at h3
  rw [geom_sum₂_self] at h3
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact hlm ((CharP.cast_eq_zero_iff (kk l) l m).1 h4)
  · have h5 : res a ^ m = 1 := by rw [← map_pow, ha, map_one]
    have h6 : res a = 0 := eq_zero_of_pow_eq_zero h4
    rw [h6, zero_pow hm.ne'] at h5
    exact zero_ne_one h5

theorem gal_root (h : GQ l) {m : ℕ} (hm : 0 < m) (hlm : ¬ l ∣ m) :
    ∃ n : ℕ, ∀ ζ : Om l, ζ ^ m = 1 → h ζ = ζ ^ (l ^ n) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) m
  let a : OO l := ⟨ξ, (norm_root hm hξ.pow_eq_one).le⟩
  have ha : a ^ m = 1 := Subtype.ext hξ.pow_eq_one
  obtain ⟨n, hn⟩ := endo_root l (galK h) (a := res a) hm hlm (by rw [← map_pow, ha, map_one])
  rw [galK_res, ← map_pow] at hn
  have h1 := res_inj hm hlm (by rw [← map_pow, ha, map_one])
    (by rw [← pow_mul, mul_comm, pow_mul, ha, one_pow]) hn
  have h2 : h ξ = ξ ^ (l ^ n) := congrArg Subtype.val h1
  refine ⟨n, fun ζ hζ => ?_⟩
  obtain ⟨i, -, rfl⟩ := hξ.eq_pow_of_pow_eq_one hζ
  rw [map_pow, h2, ← pow_mul, ← pow_mul, mul_comm]

theorem exists_root (x : Om l) (hx : ‖x‖ = 1) :
    ∃ (ζ : Om l) (m : ℕ), 0 < m ∧ ¬ l ∣ m ∧ ζ ^ m = 1 ∧ ‖x - ζ‖ < 1 := by
  obtain ⟨n, hn, h⟩ := GlobalTheory.ResidueRoot.exists_pow_alg x hx
  obtain ⟨e, m, hlm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' l hl.out.ne_one
  have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hlm)
  let a : OO l := ⟨x, hx.le⟩
  have h1 : res a ^ (l ^ e * m) = 1 := by
    rw [← map_pow, ← map_one (res (l := l)), res_eq_iff]; exact h
  rw [ExpChar.pow_prime_pow_mul_eq_one_iff] at h1
  have h2 : ‖x ^ m - 1‖ < 1 := by
    rw [← map_pow, ← map_one (res (l := l)), res_eq_iff] at h1; exact h1
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) m
  have e := congrArg (eval x) (X_pow_sub_one_eq_prod hm hξ)
  simp only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at e
  rw [e, norm_prod] at h2
  by_contra hc
  push Not at hc
  refine absurd h2 (not_lt.2 ?_)
  exact Finset.prod_induction _ (fun r : ℝ => 1 ≤ r)
    (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb)
    le_rfl fun ζ hζ => hc ζ m hm hlm ((mem_nthRootsFinset hm _).1 hζ)

theorem exists_level {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) :
    ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧
      ∀ h h' : GQ l, (∀ ζ : Om l, ζ ^ m = 1 → h ζ = h' ζ) → h x = h' x := by
  have key : ∀ {a b : Om l}, (∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧
      ∀ h h' : GQ l, (∀ ζ : Om l, ζ ^ m = 1 → h ζ = h' ζ) → h a = h' a) →
      (∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧
      ∀ h h' : GQ l, (∀ ζ : Om l, ζ ^ m = 1 → h ζ = h' ζ) → h b = h' b) →
      ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧
      ∀ h h' : GQ l, (∀ ζ : Om l, ζ ^ m = 1 → h ζ = h' ζ) → h a = h' a ∧ h b = h' b := by
    rintro a b ⟨m, hm, hlm, ha⟩ ⟨n, hn, hln, hb⟩
    refine ⟨m * n, Nat.mul_pos hm hn, fun hd => ((hl.out.dvd_mul).1 hd).elim hlm hln,
      fun h h' H => ⟨ha h h' fun ζ hζ => H ζ ?_, hb h h' fun ζ hζ => H ζ ?_⟩⟩
    · rw [pow_mul, hζ, one_pow]
    · rw [mul_comm, pow_mul, hζ, one_pow]
  unfold MaximalUnramifiedExtension at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, hm, hlm, hx⟩ := hx
    exact ⟨m, hm, hlm, fun h h' H => H x hx⟩
  | algebraMap c =>
    exact ⟨1, one_pos, hl.out.not_dvd_one, fun h h' _ => by rw [h.commutes, h'.commutes]⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, hm, hlm, H⟩ := key ha hb
    exact ⟨m, hm, hlm, fun h h' H' => by rw [map_add, map_add, (H h h' H').1, (H h h' H').2]⟩
  | inv a _ ha =>
    obtain ⟨m, hm, hlm, H⟩ := ha
    exact ⟨m, hm, hlm, fun h h' H' => by rw [map_inv₀, map_inv₀, H h h' H']⟩
  | mul a b _ _ ha hb =>
    obtain ⟨m, hm, hlm, H⟩ := key ha hb
    exact ⟨m, hm, hlm, fun h h' H' => by rw [map_mul, map_mul, (H h h' H').1, (H h h' H').2]⟩

theorem exists_ext (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l)) :
    ∃ g : GQ l, ∀ x : ↥(MaximalUnramifiedExtension l), g x = (σ x : Om l) := by
  let f : Om l →ₐ[ℚ_[l]] Om l := σ.liftNormal (Om l)
  refine ⟨AlgEquiv.ofBijective f (Algebra.IsAlgebraic.algHom_bijective f), fun x => ?_⟩
  exact σ.liftNormal_commutes (Om l) x

end GlobalTheory.MemLoc.FrobLaws

namespace GlobalTheory.MemLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc FrobLaws

theorem frob_laws (l : ℕ) [hl : Fact l.Prime] (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l))
    (hσ : ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → σ c = c ^ l) :
    (∀ x : ↥(MaximalUnramifiedExtension l), ‖(x : Om l)‖ ≤ 1 → ‖((σ x : ↥(MaximalUnramifiedExtension l)) : Om l) - (x : Om l) ^ l‖ < 1) ∧
    (∀ (K : FinExt l) (x : ↥(MaximalUnramifiedExtension l)), (x : Om l) ∈ K.1 → ((σ x : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) ∧
    (∀ x : ↥(MaximalUnramifiedExtension l), σ x = x → ∃ c : ℚ_[l], algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c = x) := by
  obtain ⟨g, hg⟩ := exists_ext σ
  have hroot : ∀ (ζ : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → ζ ^ m = 1 → g ζ = ζ ^ l := by
    intro ζ m hm hlm hζ
    let c : ↥(MaximalUnramifiedExtension l) := ⟨ζ, IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, hζ⟩⟩
    have := hσ c m hm hlm (Subtype.ext hζ)
    rw [show ζ = (c : Om l) from rfl, hg, this]; rfl
  refine ⟨fun x hx => ?_, fun K x hx => ?_, fun x hx => ?_⟩
  · rw [← hg]
    let a : OO l := ⟨x, hx⟩
    refine (res_eq_iff (galO g a) (a ^ l)).1 ?_
    rw [← galK_res, map_pow]
    rcases hx.lt_or_eq with h | h
    · have : res a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 ((mem_MM a).2 h)
      rw [this, map_zero, zero_pow hl.out.ne_zero]
    · obtain ⟨ζ, m, hm, hlm, hζ, hn⟩ := FrobLaws.exists_root (l := l) (x : Om l) h
      let b : OO l := ⟨ζ, (norm_root hm hζ).le⟩
      have : res a = res b := (res_eq_iff a b).2 hn
      rw [this, galK_res, ← map_pow]
      have e : galO g b = b ^ l := Subtype.ext (hroot ζ m hm hlm hζ)
      rw [e]
  · rw [← hg, ← InfiniteGalois.fixedField_fixingSubgroup K.1, IntermediateField.mem_fixedField_iff]
    intro h hh
    obtain ⟨m, hm, hlm, H⟩ := exists_level x.2
    have h1 := H (h * g) (g * h) fun ζ hζ => by
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hroot ζ m hm hlm hζ, map_pow,
        hroot (h ζ) m hm hlm (by rw [← map_pow, hζ, map_one])]
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at h1
    rw [h1, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh x hx]
  · have hgx : g x = x := by rw [hg, hx]
    have hpow : ∀ n : ℕ, (g ^ n) x = x := fun n => by
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, hgx, ih]
    obtain ⟨m, hm, hlm, H⟩ := exists_level x.2
    have hr : ∀ (n : ℕ) (ζ : Om l), ζ ^ m = 1 → (g ^ n) ζ = ζ ^ (l ^ n) := fun n ζ hζ => by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hroot ζ m hm hlm hζ, ← pow_mul, pow_succ']
    obtain ⟨c, hc⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ_[l]) (x : Om l)).2
      fun h => by
        obtain ⟨n, hn⟩ := gal_root h hm hlm
        rw [H h (g ^ n) fun ζ hζ => by rw [hn ζ hζ, hr n ζ hζ], hpow]
    exact ⟨c, Subtype.ext hc⟩

end GlobalTheory.MemLoc
