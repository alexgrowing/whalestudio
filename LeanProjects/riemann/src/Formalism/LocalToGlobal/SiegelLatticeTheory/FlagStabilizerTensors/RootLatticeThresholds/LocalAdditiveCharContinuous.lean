import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.EFSymmCont
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMoreMore

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.LocCP

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel

variable {D : D7} (p : PlF D)

def th : (D.s.atP p).Ep := (D.s.atP p).ιE (D.host.sqq)

theorem cj_th : (D.s.atP p).cj (th p) = -th p := by
  rw [th, (D.s.atP p).cj_ιE, D.conjF_eq, Examples₂.conj_aE, map_neg]

theorem q_ne : (D.host.q : ℕ) ≠ 0 := by
  obtain ⟨k, hk⟩ := Examples₂.q_mod_four D.host
  omega

theorem th_sq : th p * th p = -((D.host.q : ℕ) : (D.s.atP p).Ep) := by
  rw [th, ← map_mul, ← pow_two, Examples₂.aE_sq, map_neg, map_natCast]

theorem aE_ne : D.host.sqq ≠ 0 := by
  intro h
  have := Examples₂.aE_sq D.host
  rw [h, zero_pow two_ne_zero, eq_comm, neg_eq_zero, Nat.cast_eq_zero] at this
  exact q_ne this

theorem mem_span_aE (x : D.host.E) :
    x ∈ Submodule.span D.host.F ({1, D.host.sqq} : Set D.host.E) := by
  have hli : LinearIndependent D.host.F ![(1 : D.host.E), D.host.sqq] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_contra hne
    have ht : t ≠ 0 := by
      intro ht; subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact hne ⟨hst, rfl⟩
    have hmem : D.host.sqq ∈ D.host.F := by
      have : D.host.sqq = algebraMap D.host.F D.host.E (-(s / t)) := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        rw [map_neg, map_div₀]
        field_simp [(map_ne_zero (algebraMap D.host.F D.host.E)).2 ht]
        linear_combination hst
      rw [this]; exact (-(s / t)).2
    have h1 := (Examples₂.conj_eq_self_iff D.host _).2 hmem
    rw [Examples₂.conj_aE] at h1
    exact aE_ne (D := D) (by linear_combination -h1 / 2)
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by simp [Examples₂.finrank_FE D.host])
  have : x ∈ Submodule.span D.host.F (Set.range ![(1 : D.host.E), D.host.sqq]) := by
    rw [hsp]; trivial
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union] at this
  exact this

theorem span_th : Submodule.span (D.s.atP p).Fp ({1, th p} : Set (D.s.atP p).Ep) = ⊤ := by
  rw [eq_top_iff, ← (D.s.atP p).span, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 (mem_span_aE x)
  rw [← hab, map_add, Algebra.smul_def, Algebra.smul_def, mul_one, map_mul, (D.s.atP p).compat,
    (D.s.atP p).compat]
  refine Submodule.mem_span_pair.2 ⟨(D.s.atP p).ιF a, (D.s.atP p).ιF b, ?_⟩
  rw [Algebra.smul_def, Algebra.smul_def, mul_one, th]

instance finEp : Module.Finite (D.s.atP p).Fp (D.s.atP p).Ep :=
  Module.finite_of_finrank_pos (by rw [(D.s.atP p).rank]; norm_num)

theorem indep_th : LinearIndependent (D.s.atP p).Fp ![(1 : (D.s.atP p).Ep), th p] := by
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp [(D.s.atP p).rank])
  rw [← span_th p]
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union, le_refl]

theorem repr_th (y : (D.s.atP p).Ep) : ∃ a b : (D.s.atP p).Fp,
    y = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep a + algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b * th p := by
  have : y ∈ Submodule.span (D.s.atP p).Fp ({1, th p} : Set (D.s.atP p).Ep) := by rw [span_th]; trivial
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 this
  exact ⟨a, b, by rw [← hab, Algebra.smul_def, Algebra.smul_def, mul_one]⟩

theorem eq_zero_th (a b : (D.s.atP p).Fp)
    (h : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep a + algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b * th p = 0) :
    a = 0 ∧ b = 0 := by
  have := (LinearIndependent.pair_iff.1 (indep_th p)) a b
  apply this
  rw [Algebra.smul_def, Algebra.smul_def, mul_one]; exact h

theorem cj_alg' (z : (D.s.atP p).Fp) :
    (D.s.atP p).cj (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep z) = algebraMap _ _ z :=
  (D.s.atP p).cj.commutes z

theorem cj_cj (y : (D.s.atP p).Ep) : (D.s.atP p).cj ((D.s.atP p).cj y) = y := by
  obtain ⟨a, b, rfl⟩ := repr_th p y
  simp only [map_add, map_mul, map_neg, cj_alg', cj_th, mul_neg, neg_neg]

theorem cj_fix (y : (D.s.atP p).Ep) :
    (D.s.atP p).cj y = y ↔ ∃ a : (D.s.atP p).Fp, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep a = y := by
  constructor
  · intro h
    obtain ⟨a, b, rfl⟩ := repr_th p y
    simp only [map_add, map_mul, cj_alg', cj_th] at h
    have h2 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep 0 +
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (2 * b) * th p = 0 := by
      rw [map_zero, zero_add, map_mul, map_ofNat]; linear_combination -h
    have hb := (eq_zero_th p 0 (2 * b) h2).2
    have hb' : b = 0 := by
      have := (D.s.atP p).char0
      rcases mul_eq_zero.1 hb with h | h
      · exact absurd h two_ne_zero
      · exact h
    exact ⟨a, by rw [hb', map_zero, zero_mul, add_zero]⟩
  · rintro ⟨a, rfl⟩; exact cj_alg' p a

theorem sq_eq_zero (y : (D.s.atP p).Ep) (h : y * y = 0) : y = 0 := by
  have := (D.s.atP p).char0
  obtain ⟨a, b, rfl⟩ := repr_th p y
  have hq : ((D.host.q : ℕ) : (D.s.atP p).Fp) ≠ 0 := Nat.cast_ne_zero.2 (q_ne (D := D))
  have e : (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep a + algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b * th p) *
      (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep a + algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b * th p) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (a * a - (D.host.q : ℕ) * (b * b)) +
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (2 * a * b) * th p := by
    have := th_sq p
    simp only [map_sub, map_mul, map_natCast, map_ofNat]
    linear_combination (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b) ^ 2 * this
  rw [e] at h
  obtain ⟨h1, h2⟩ := eq_zero_th p _ _ h
  have hab : a = 0 ∨ b = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h two_ne_zero
      · exact Or.inl h
    · exact Or.inr h
  rcases hab with ha | hb
  · subst ha
    have h3 : ((D.host.q : ℕ) : (D.s.atP p).Fp) * (b * b) = 0 := by linear_combination -h1
    have : b * b = 0 := (mul_eq_zero.1 h3).resolve_left hq
    have hb : b = 0 := mul_self_eq_zero.1 this
    subst hb; simp
  · subst hb
    have : a * a = 0 := by simpa using h1
    have ha : a = 0 := mul_self_eq_zero.1 this
    subst ha; simp

theorem reduced : IsReduced (D.s.atP p).Ep := by
  refine ⟨fun y ⟨n, hn⟩ => ?_⟩
  have key : ∀ k : ℕ, y ^ (2 ^ k) = 0 → y = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      apply ih
      apply sq_eq_zero
      rw [← pow_two, ← pow_mul, ← pow_succ]; exact hk
  apply key n
  have : n ≤ 2 ^ n := Nat.lt_two_pow_self.le
  rw [← Nat.sub_add_cancel this, pow_add, hn, mul_zero]

end Formalism.L2.SG.Pf.LocCP

namespace Formalism.L2.SG.Pf.LocCP

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel MeasureTheory

theorem factRes {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : Fact (Loc.resChar v).Prime :=
  ⟨Formalism.BasicNotions.Examples₂.resChar_prime v⟩

attribute [local instance] factRes

variable {D : D7} (p : PlF D)

def trQ (y : (D.s.atP p).Ep) : ℚ_[Loc.resChar p] :=
  letI := ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).comp
    (algebraMap ℚ_[Loc.resChar p] (D.s.atP p).Fp)).toAlgebra
  Algebra.trace ℚ_[Loc.resChar p] (D.s.atP p).Ep y

theorem trQ_sub (y z : (D.s.atP p).Ep) : trQ p (y - z) = trQ p y - trQ p z := by
  unfold trQ; exact map_sub _ _ _

theorem trQ_cj (y : (D.s.atP p).Ep) : trQ p ((D.s.atP p).cj y) = trQ p y := by
  unfold trQ
  letI := ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).comp
    (algebraMap ℚ_[Loc.resChar p] (D.s.atP p).Fp)).toAlgebra
  haveI : IsScalarTower ℚ_[Loc.resChar p] (D.s.atP p).Fp (D.s.atP p).Ep :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact Algebra.trace_eq_of_algEquiv ((D.s.atP p).cj.restrictScalars ℚ_[Loc.resChar p]) y

theorem den_one_of (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (a : ℚ) (n : ℕ) (hden : a.den = ℓ ^ n)
    (ha : ‖(a : ℚ_[ℓ])‖ ≤ 1) : a.den = 1 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hden, hn, pow_zero]
  exfalso
  have hdvd : ℓ ∣ a.den := by rw [hden]; exact dvd_pow_self ℓ hn.ne'
  have hnum : ¬ (ℓ : ℤ) ∣ a.num := by
    intro h
    have h1 : ℓ ∣ a.num.natAbs := Int.natCast_dvd.1 h
    have hg : ℓ ∣ Nat.gcd a.num.natAbs a.den := Nat.dvd_gcd h1 hdvd
    rw [Nat.Coprime.gcd_eq_one a.reduced] at hg
    exact hℓ.out.one_lt.ne' (Nat.dvd_one.1 hg)
  have hn1 : ‖(a.num : ℚ_[ℓ])‖ = 1 :=
    le_antisymm (Padic.norm_int_le_one _) (not_lt.1 fun h => hnum (Padic.norm_intCast_lt_one_iff.1 h))
  have hd : ‖(a.den : ℚ_[ℓ])‖ = (ℓ : ℝ)⁻¹ ^ n := by
    rw [hden, Nat.cast_pow, norm_pow, Padic.norm_p]
  have e : ‖(a : ℚ_[ℓ])‖ = (ℓ : ℝ) ^ n := by
    rw [Rat.cast_def, norm_div, hn1, hd, inv_pow, one_div, inv_inv]
  rw [e] at ha
  have hl : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.out.one_lt
  exact absurd ha (not_le.2 (one_lt_pow₀ hl hn.ne'))

theorem psiE_tr_zero (z : (D.s.atP p).Ep) (hz : trQ p z = 0) : (D.s.atP p).psiE z = 1 := by
  obtain ⟨a, ⟨n, hden⟩, hle, heq⟩ := (D.s.atP p).psiE_def z
  change ‖trQ p z - (a : ℚ_[Loc.resChar p])‖ ≤ 1 at hle
  rw [hz, zero_sub, norm_neg] at hle
  have h1 := den_one_of (Loc.resChar p) a n hden hle
  have ha : ((a.num : ℚ) : ℂ) = (a : ℂ) := by rw [Rat.coe_int_num_of_den_eq_one h1]
  rw [heq, ← ha, Rat.cast_intCast, mul_comm]
  exact Complex.exp_int_mul_two_pi_mul_I a.num

theorem psiE_cj (y : (D.s.atP p).Ep) : (D.s.atP p).psiE ((D.s.atP p).cj y) = (D.s.atP p).psiE y := by
  have h : (D.s.atP p).psiE ((D.s.atP p).cj y - y) = 1 :=
    psiE_tr_zero p _ (by rw [trQ_sub, trQ_cj, sub_self])
  calc (D.s.atP p).psiE ((D.s.atP p).cj y) = (D.s.atP p).psiE (((D.s.atP p).cj y - y) + y) := by rw [sub_add_cancel]
    _ = _ := by rw [AddChar.map_add_eq_mul, h, one_mul]

end Formalism.L2.SG.Pf.LocCP

namespace Formalism.L2.SG.Pf.LocCP

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel MeasureTheory

attribute [local instance] factRes

variable {D : D7}

variable (D) in

def LocTied : Prop := ∀ p : PlF D, Nonempty (Formalism.L2.S.LocIso (D.s.atP p) (Formalism.L2.S.locC D p))

def DualAt (p : PlF D) (δ : (D.s.atP p).Fp) : Prop :=
  ∀ x : (D.s.atP p).Ep, (∀ y ∈ (D.s.atP p).O,
    (D.s.atP p).psiE (-(x * y * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep δ⁻¹)) = 1) ↔ x ∈ (D.s.atP p).O

def PinAt (p : PlF D) (δ : (D.s.atP p).Fp) : Prop :=
  ∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal →
    δ = (D.s.atP p).ιF (((D.host.g 0 : ℕ) : D.host.F) * ((D.host.g 1 : ℕ) : D.host.F) / ((D.host.g i : ℕ) : D.host.F))

def UnramAt (p : PlF D) : Prop :=
  ∀ ϖ : 𝒪[(D.s.atP p).Fp], Irreducible ϖ → ∀ x ∈ (D.s.atP p).O,
    x * x ∈ Submodule.span (D.s.atP p).O {algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (ϖ : (D.s.atP p).Fp)} →
      x ∈ Submodule.span (D.s.atP p).O {algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (ϖ : (D.s.atP p).Fp)}

def ordR {p : PlF D} (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p)) :
    Subring (D.s.atP p).Ep :=
  let S : Subring (𝒪[(D.s.atP p).Fp] × 𝒪[(D.s.atP p).Fp]) :=
    RingHom.eqLocus ((Ideal.Quotient.mk (Ideal.span {sg.q})).comp (RingHom.fst _ _))
      ((Ideal.Quotient.mk (Ideal.span {sg.q})).comp (RingHom.snd _ _))
  (S.map ((𝒪[(D.s.atP p).Fp]).subtype.prodMap (𝒪[(D.s.atP p).Fp]).subtype)).comap sg.e.toRingEquiv.toRingHom

def RR (p : PlF D) : Set (D.s.atP p).Ep :=
  match (D.s.atP p).split with
  | none => ((D.s.atP p).O : Set (D.s.atP p).Ep)
  | some sg => (ordR sg : Set (D.s.atP p).Ep)

def HaarAt (p : PlF D) : Prop :=
  ∃ μ : Measure (D.s.atP p).Ep, μ.IsAddHaarMeasure ∧ SigmaFinite μ ∧ μ (RR p) = 1

def LocDualC : Prop :=
  ∀ D : D7, LocTied D → ∀ p : PlF D, ∃ δ : (D.s.atP p).Fp, δ ≠ 0 ∧ DualAt p δ ∧ PinAt p δ

def LocUnramC : Prop := ∀ D : D7, LocTied D → ∀ p : PlF D, UnramAt p

def LocPsiContC : Prop := ∀ D : D7, LocTied D → ∀ p : PlF D, Continuous (D.s.atP p).psiE

def LocHaarC : Prop := ∀ D : D7, LocTied D → ∀ p : PlF D, HaarAt p

section Build

variable (p : PlF D) (δ : (D.s.atP p).Fp)

def psi0 : AddChar (D.s.atP p).Ep ℂ :=
  (D.s.atP p).psiE.compAddMonoidHom (AddMonoidHom.mulRight (-(algebraMap (D.s.atP p).Fp (D.s.atP p).Ep δ⁻¹)))

theorem local_additive_char_apply (y : (D.s.atP p).Ep) :
    psi0 p δ y = (D.s.atP p).psiE (-(y * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep δ⁻¹)) := by
  simp [psi0, mul_neg]

theorem local_additive_char_conj (y : (D.s.atP p).Ep) : psi0 p δ ((D.s.atP p).cj y) = psi0 p δ y := by
  rw [local_additive_char_apply, local_additive_char_apply, ← psiE_cj p (-(y * _))]
  congr 1
  rw [map_neg, map_mul, cj_alg']

theorem local_additive_char_continuous (hc : Continuous (D.s.atP p).psiE) : Continuous (psi0 p δ) := by
  haveI := (D.s.atP p).top
  haveI := (D.s.atP p).lf
  haveI := IsModuleTopology.toContinuousAdd (D.s.atP p).Fp (D.s.atP p).Ep
  haveI := IsModuleTopology.toContinuousSMul (D.s.atP p).Fp (D.s.atP p).Ep
  have hl : Continuous (LinearMap.mulRight (D.s.atP p).Fp (-(algebraMap (D.s.atP p).Fp (D.s.atP p).Ep δ⁻¹))) :=
    IsModuleTopology.continuous_of_linearMap _
  exact hc.comp hl

def mkLocE (hc : Continuous (D.s.atP p).psiE) (hd : DualAt p δ) (hu : UnramAt p) :
    Loc.LocE (D.s.atP p).Fp (D.s.atP p).Ep where
  cj := (D.s.atP p).cj
  cj_cj := cj_cj p
  cj_fix := cj_fix p
  free := (D.s.atP p).free
  rank := (D.s.atP p).rank
  reduced := reduced p
  top := (D.s.atP p).top
  O := (D.s.atP p).O
  O_def := (D.s.atP p).O_def
  unram := hu
  psi0 := psi0 p δ
  local_additive_char_continuous := local_additive_char_continuous p δ hc
  local_additive_char_conj := local_additive_char_conj p δ
  additive_character_dual_ring x := by
    simp only [local_additive_char_apply, mul_assoc] at *
    have := hd x
    simp only [mul_assoc] at this
    exact this

end Build

end Formalism.L2.SG.Pf.LocCP

namespace Formalism.L2.SG.Pf.LocCP

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel MeasureTheory

attribute [local instance] factRes

variable {D : D7}

section Split

variable {p : PlF D} (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p))

theorem e_symm_cj (a b : (D.s.atP p).Fp) : (D.s.atP p).cj (sg.e.symm (a, b)) = sg.e.symm (b, a) := by
  apply sg.e.injective
  rw [sg.e_cj, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]; rfl

theorem inl_eq (y : (D.s.atP p).Fp) :
    sg.e.symm (y, 0) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep y * sg.e.symm (1, 0) := by
  apply sg.e.injective
  rw [map_mul, AlgEquiv.commutes, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  ext <;> simp

theorem mem_O_inl (y : (D.s.atP p).Fp) (hy : y ∈ 𝒪[(D.s.atP p).Fp]) : sg.e.symm (y, 0) ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def, inl_eq]
  refine IsIntegral.mul ?_ ?_
  · have : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep y =
        algebraMap 𝒪[(D.s.atP p).Fp] (D.s.atP p).Ep ⟨y, hy⟩ := rfl
    rw [this]; exact isIntegral_algebraMap
  · refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num), ?_⟩
    have h : sg.e.symm (1, 0) * sg.e.symm (1, 0) = sg.e.symm ((1 : (D.s.atP p).Fp), (0 : (D.s.atP p).Fp)) := by
      rw [← map_mul]; congr 1; ext <;> simp
    simp [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, pow_two, h]

theorem comp_mem (z : (D.s.atP p).Ep) (hz : z ∈ (D.s.atP p).O) :
    (sg.e z).1 ∈ 𝒪[(D.s.atP p).Fp] ∧ (sg.e z).2 ∈ 𝒪[(D.s.atP p).Fp] := by
  rw [(D.s.atP p).O_def] at hz
  have f1 := ((AlgHom.fst (D.s.atP p).Fp (D.s.atP p).Fp (D.s.atP p).Fp).comp sg.e.toAlgHom).restrictScalars
    𝒪[(D.s.atP p).Fp]
  have f2 := ((AlgHom.snd (D.s.atP p).Fp (D.s.atP p).Fp (D.s.atP p).Fp).comp sg.e.toAlgHom).restrictScalars
    𝒪[(D.s.atP p).Fp]
  have h1 : IsIntegral 𝒪[(D.s.atP p).Fp] (sg.e z).1 :=
    hz.map (((AlgHom.fst (D.s.atP p).Fp (D.s.atP p).Fp (D.s.atP p).Fp).comp sg.e.toAlgHom).restrictScalars
      𝒪[(D.s.atP p).Fp])
  have h2 : IsIntegral 𝒪[(D.s.atP p).Fp] (sg.e z).2 :=
    hz.map (((AlgHom.snd (D.s.atP p).Fp (D.s.atP p).Fp (D.s.atP p).Fp).comp sg.e.toAlgHom).restrictScalars
      𝒪[(D.s.atP p).Fp])
  exact ⟨(Valuation.integer.integers _).mem_of_integral h1, (Valuation.integer.integers _).mem_of_integral h2⟩

end Split

end Formalism.L2.SG.Pf.LocCP

namespace Formalism.L2.SG.Pf.LocCP

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel MeasureTheory

attribute [local instance] factRes

variable {D : D7}

section Model

variable (p : PlF D) (δ : (D.s.atP p).Fp)

theorem local_additive_char_integers (hd : DualAt p δ) (z : (D.s.atP p).Ep) (hz : z ∈ (D.s.atP p).O) : psi0 p δ z = 1 := by
  rw [local_additive_char_apply]
  have := (hd 1).2 (D.s.atP p).O.one_mem z hz
  simpa using this

variable (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p))

def psiFof : AddChar (D.s.atP p).Fp ℂ :=
  (psi0 p δ).compAddMonoidHom (sg.e.symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _))

theorem psiFof_apply (y : (D.s.atP p).Fp) : psiFof p δ sg y = psi0 p δ (sg.e.symm (y, 0)) := rfl

theorem psiFof_cont (hc : Continuous (D.s.atP p).psiE) : Continuous (psiFof p δ sg) := by
  haveI := (D.s.atP p).top
  haveI := (D.s.atP p).lf
  haveI := IsModuleTopology.toContinuousAdd (D.s.atP p).Fp (D.s.atP p).Ep
  haveI := IsModuleTopology.toContinuousSMul (D.s.atP p).Fp (D.s.atP p).Ep
  have h1 : Continuous (sg.e.symm.toLinearMap.comp (LinearMap.inl (D.s.atP p).Fp (D.s.atP p).Fp (D.s.atP p).Fp)) :=
    IsModuleTopology.continuous_of_linearMap _
  exact (local_additive_char_continuous p δ hc).comp h1

theorem psiFof_o (hd : DualAt p δ) (y : (D.s.atP p).Fp) (hy : y ∈ 𝒪[(D.s.atP p).Fp]) : psiFof p δ sg y = 1 := by
  rw [psiFof_apply]; exact local_additive_char_integers p δ hd _ (mem_O_inl sg y hy)

theorem local_additive_char_eq_trace (x : (D.s.atP p).Ep) : psi0 p δ x = psiFof p δ sg ((sg.e x).1 + (sg.e x).2) := by
  rw [psiFof_apply]
  have hx : x = sg.e.symm ((sg.e x).1, 0) + (D.s.atP p).cj (sg.e.symm ((sg.e x).2, 0)) := by
    rw [e_symm_cj, ← map_add]
    apply sg.e.injective; rw [AlgEquiv.apply_symm_apply]; ext <;> simp
  have hs : sg.e.symm ((sg.e x).1 + (sg.e x).2, 0) = sg.e.symm ((sg.e x).1, 0) + sg.e.symm ((sg.e x).2, 0) := by
    rw [← map_add]; congr 1; ext <;> simp
  have e1 : psi0 p δ x = psi0 p δ (sg.e.symm ((sg.e x).1, 0)) * psi0 p δ (sg.e.symm ((sg.e x).2, 0)) := by
    conv_lhs => rw [hx]
    rw [AddChar.map_add_eq_mul, local_additive_char_conj]
  rw [e1, hs, AddChar.map_add_eq_mul]

theorem psiFof_cond (hd : DualAt p δ) :
    ∃ y : 𝒪[(D.s.atP p).Fp], psiFof p δ sg ((y : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) ≠ 1 := by
  by_contra h
  push_neg at h
  have hq0 : ((sg.q : (D.s.atP p).Fp)) ≠ 0 := fun h0 => sg.q_irr.ne_zero (Subtype.ext h0)
  set x := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp))⁻¹ with hx
  have hall : ∀ z ∈ (D.s.atP p).O,
      (D.s.atP p).psiE (-(x * z * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep δ⁻¹)) = 1 := by
    intro z hz
    obtain ⟨h1, h2⟩ := comp_mem sg z hz
    rw [← local_additive_char_apply, local_additive_char_eq_trace]
    have e1 : (sg.e (x * z)).1 + (sg.e (x * z)).2 =
        (((sg.e z).1 + (sg.e z).2 : (D.s.atP p).Fp)) / (sg.q : (D.s.atP p).Fp) := by
      rw [hx, map_mul, AlgEquiv.commutes]
      simp [Prod.algebraMap_apply, div_eq_inv_mul, mul_add]
    rw [e1]
    exact h ⟨(sg.e z).1 + (sg.e z).2, add_mem h1 h2⟩
  have hxO : x ∈ (D.s.atP p).O := (hd x).1 hall
  have h1 := (comp_mem sg x hxO).1
  rw [hx, AlgEquiv.commutes] at h1
  exact sg.q_irr.not_isUnit ⟨⟨sg.q, ⟨_, h1⟩, Subtype.ext (mul_inv_cancel₀ hq0), Subtype.ext (inv_mul_cancel₀ hq0)⟩, rfl⟩

def mkSplit (hc : Continuous (D.s.atP p).psiE) (hd : DualAt p δ) (hu : UnramAt p) :
    Loc.SplitG (mkLocE p δ hc hd hu) where
  e := sg.e
  e_cj := sg.e_cj
  q := sg.q
  q_irr := sg.q_irr
  psiF := psiFof p δ sg
  psiF_cont := psiFof_cont p δ sg hc
  psiF_o := psiFof_o p δ sg hd
  psiF_cond := psiFof_cond p δ sg hd
  fractionFieldToGenericStalk_algebraMap_eq := local_additive_char_eq_trace p δ sg

end Model

def mkModel (p : PlF D) (δ : (D.s.atP p).Fp) (hc : Continuous (D.s.atP p).psiE) (hd : DualAt p δ)
    (hu : UnramAt p) (μ : Measure (D.s.atP p).Ep) : Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep where
  L := mkLocE p δ hc hd hu
  split := (D.s.atP p).split.map (fun sg => mkSplit p δ sg hc hd hu)
  mu := μ

theorem mkModel_R (p : PlF D) (δ : (D.s.atP p).Fp) (hc : Continuous (D.s.atP p).psiE) (hd : DualAt p δ)
    (hu : UnramAt p) (μ : Measure (D.s.atP p).Ep) :
    ((mkModel p δ hc hd hu μ).R : Set (D.s.atP p).Ep) = RR p := by
  unfold Loc.Model.R RR mkModel
  rcases h : (D.s.atP p).split with _ | sg
  · simp only [Option.map_none]; rfl
  · simp only [Option.map_some]; rfl

theorem agree_mk (δf : ∀ q : PlF D, (D.s.atP q).Fp) (hcf : ∀ q : PlF D, Continuous (D.s.atP q).psiE)
    (hdf : ∀ q : PlF D, DualAt q (δf q)) (huf : ∀ q : PlF D, UnramAt q) (μf : ∀ q : PlF D, Measure (D.s.atP q).Ep)
    (p : PlF D) (hμ : (μf p).IsAddHaarMeasure) (hσ : SigmaFinite (μf p)) (h1 : μf p (RR p) = 1) (hδ : δf p ≠ 0) :
    Agree δf (fun q => mkModel q (δf q) (hcf q) (hdf q) (huf q) (μf q)) p := by
  refine ⟨⟨(D.s.atP p).lf, (D.s.atP p).char0, (D.s.atP p).borel, ⟨hμ, hσ, ?_⟩⟩, hδ, rfl, rfl,
    fun y => local_additive_char_apply p (δf p) y, ?_⟩
  · show (μf p) ((mkModel p (δf p) (hcf p) (hdf p) (huf p) (μf p)).R : Set (D.s.atP p).Ep) = 1
    rw [mkModel_R]; exact h1
  · simp only [mkModel]
    split
    · trivial
    · rename_i g sg hg hs
      rw [hs] at hg
      simp only [Option.map_some, Option.some.injEq] at hg
      subst hg; exact ⟨rfl, rfl⟩
    · rcases hs : (D.s.atP p).split with _ | sg <;> simp_all

theorem locBody_of (D : D7) (hT : LocTied D) (h1 : LocDualC) (h2 : LocUnramC) (h3 : LocPsiContC) (h4 : LocHaarC) :
    ∃ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
      (∀ p, Agree δ M p) ∧ ∀ p, PinAt p (δ p) := by
  choose δ hδ hd hpin using h1 D hT
  choose μ hμ hσ hR using h4 D hT
  exact ⟨δ, fun p => mkModel p (δ p) (h3 D hT p) (hd p) (h2 D hT p) (μ p),
    fun p => agree_mk δ (h3 D hT) hd (h2 D hT) μ p (hμ p) (hσ p) (hR p) (hδ p), hpin⟩

end Formalism.L2.SG.Pf.LocCP

namespace Formalism.L2.SG.Pf.LocCP

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel MeasureTheory

attribute [local instance] factRes

def LocDualGenC : Prop :=
  ∀ D : D7, LocTied D → ∀ p : PlF D,
    (IsReduced (D.s.atP p).Ep → UnramAt p → ∃ δ : (D.s.atP p).Fp, δ ≠ 0 ∧ DualAt p δ) ∧
    (∀ (δ : (D.s.atP p).Fp) (u : 𝒪[(D.s.atP p).Fp]), IsUnit u → DualAt p δ → DualAt p (δ * (u : (D.s.atP p).Fp))) ∧
    (IsReduced (D.s.atP p).Ep → UnramAt p → Irreducible ((Loc.resChar p : ℕ) : 𝒪[(D.s.atP p).Fp]) → DualAt p 1)

def PinHostC : Prop :=
  ∀ D : D7, LocTied D → ∀ (p : PlF D) (i : Fin 2), ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal →
    Irreducible ((Loc.resChar p : ℕ) : 𝒪[(D.s.atP p).Fp]) ∧
      ∃ u : 𝒪[(D.s.atP p).Fp], IsUnit u ∧ (u : (D.s.atP p).Fp) =
        (D.s.atP p).ιF (((D.host.g 0 : ℕ) : D.host.F) * ((D.host.g 1 : ℕ) : D.host.F) / ((D.host.g i : ℕ) : D.host.F))

theorem not_both (D : D7) (p : PlF D) (h0 : ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal)
    (h1 : ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) : False := by
  first | exact UpperTheory.Reformulated.B.Qf52.not_both .. | (apply UpperTheory.Reformulated.B.Qf52.not_both <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qf52.not_both <;> assumption) | (apply @UpperTheory.Reformulated.B.Qf52.not_both <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qf52.not_both <;> assumption) | (apply @UpperTheory.Reformulated.B.Qf52.not_both <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qf52.not_both D p h0 h1 | exact @UpperTheory.Reformulated.B.Qf52.not_both D p h0 | exact @UpperTheory.Reformulated.B.Qf52.not_both D p | exact @UpperTheory.Reformulated.B.Qf52.not_both D

theorem locDualC_of (hG : LocDualGenC) (hU : LocUnramC) (hP : PinHostC) : LocDualC := by
  intro D hT p
  have hred := reduced p
  have hun := hU D hT p
  obtain ⟨g1, g2, g3⟩ := hG D hT p
  by_cases hty : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal
  · obtain ⟨i, hi⟩ := hty
    obtain ⟨hirr, u, hu, hval⟩ := hP D hT p i hi
    have hd1 := g3 hred hun hirr
    have hdu := g2 1 u hu hd1
    rw [one_mul] at hdu
    refine ⟨(u : (D.s.atP p).Fp), fun h0 => ?_, hdu, ?_⟩
    · exact hu.ne_zero (Subtype.ext h0)
    · intro j hj
      have hji : j = i := by
        by_contra hne
        fin_cases i <;> fin_cases j
        · exact hne rfl
        · exact not_both D p hi hj
        · exact not_both D p hj hi
        · exact hne rfl
      subst hji; exact hval
  · push_neg at hty
    obtain ⟨δ, hδ, hd⟩ := g1 hred hun
    exact ⟨δ, hδ, hd, fun i hi => absurd hi (hty i)⟩

end Formalism.L2.SG.Pf.LocCP

namespace Formalism.L2.SG.Pf.LocCP

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel MeasureTheory Topology

attribute [local instance] factRes

variable {D : D7} (p : PlF D)

theorem psiE_of_norm (z : (D.s.atP p).Ep) (hz : ‖trQ p z‖ ≤ 1) : (D.s.atP p).psiE z = 1 := by
  obtain ⟨a, ⟨n, hden⟩, hle, heq⟩ := (D.s.atP p).psiE_def z
  change ‖trQ p z - (a : ℚ_[Loc.resChar p])‖ ≤ 1 at hle
  have ha : ‖(a : ℚ_[Loc.resChar p])‖ ≤ 1 := by
    have h := Padic.nonarchimedean (trQ p z) (-(trQ p z - (a : ℚ_[Loc.resChar p])))
    rw [norm_neg, ← sub_eq_add_neg, sub_sub_cancel] at h
    exact h.trans (max_le hz hle)
  have h1 := den_one_of (Loc.resChar p) a n hden ha
  have ha' : ((a.num : ℚ) : ℂ) = (a : ℂ) := by rw [Rat.coe_int_num_of_den_eq_one h1]
  rw [heq, ← ha', Rat.cast_intCast, mul_comm]
  exact Complex.exp_int_mul_two_pi_mul_I a.num

theorem t2Fp : T2Space (D.s.atP p).Fp := by
  haveI := (D.s.atP p).lf
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx => ?_
  have hv : ValuativeRel.valuation (D.s.atP p).Fp x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  refine ⟨{z | ValuativeRel.valuation (D.s.atP p).Fp z < ValuativeRel.valuation (D.s.atP p).Fp x},
    (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨Units.mk0 _ hv, fun z hz => by simpa using hz⟩,
    by intro h; simp only [Set.mem_setOf_eq] at h; exact lt_irrefl _ h⟩

theorem trQ_cont : Continuous (trQ p) := by
  haveI := (D.s.atP p).lf
  haveI := t2Fp p
  haveI := (D.s.atP p).top
  haveI := (D.s.atP p).free
  haveI := (D.s.atP p).qlFin
  haveI := IsModuleTopology.toContinuousAdd (D.s.atP p).Fp (D.s.atP p).Ep
  letI := ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).comp
    (algebraMap ℚ_[Loc.resChar p] (D.s.atP p).Fp)).toAlgebra
  haveI : IsScalarTower ℚ_[Loc.resChar p] (D.s.atP p).Fp (D.s.atP p).Ep :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : ContinuousSMul ℚ_[Loc.resChar p] (D.s.atP p).Fp := by
    refine ⟨?_⟩
    have : (fun x : ℚ_[Loc.resChar p] × (D.s.atP p).Fp => x.1 • x.2) =
        fun x => algebraMap ℚ_[Loc.resChar p] (D.s.atP p).Fp x.1 * x.2 := by
      funext x; exact Algebra.smul_def _ _
    rw [this]
    exact ((D.s.atP p).qlCont.comp continuous_fst).mul continuous_snd
  have e : trQ p = fun y => Algebra.trace ℚ_[Loc.resChar p] (D.s.atP p).Fp
      (Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep y) := by
    funext y; unfold trQ; exact (Algebra.trace_trace (S := (D.s.atP p).Fp) y).symm
  rw [e]
  have h1 : Continuous (Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep) :=
    IsModuleTopology.continuous_of_linearMap _
  have h2 : Continuous (Algebra.trace ℚ_[Loc.resChar p] (D.s.atP p).Fp) :=
    LinearMap.continuous_of_finiteDimensional _
  exact h2.comp h1

theorem psiE_cont : Continuous (D.s.atP p).psiE := by
  haveI := (D.s.atP p).top
  haveI := (D.s.atP p).lf
  haveI := IsModuleTopology.toContinuousAdd (D.s.atP p).Fp (D.s.atP p).Ep
  haveI : IsTopologicalAddGroup (D.s.atP p).Ep := IsModuleTopology.topologicalAddGroup (D.s.atP p).Fp (D.s.atP p).Ep
  have hU : IsOpen {y : (D.s.atP p).Ep | ‖trQ p y‖ ≤ 1} := by
    have := (IsUltrametricDist.isOpen_closedBall (0 : ℚ_[Loc.resChar p]) (one_ne_zero)).preimage (trQ_cont p)
    simpa [Metric.closedBall, dist_zero_right] using this
  rw [continuous_iff_continuousAt]
  intro y
  have hmem : {w : (D.s.atP p).Ep | ‖trQ p (w - y)‖ ≤ 1} ∈ 𝓝 y := by
    have hc : Continuous fun w : (D.s.atP p).Ep => w - y := continuous_id.sub continuous_const
    exact (hU.preimage hc).mem_nhds (by simp [sub_self, trQ_sub])
  refine (continuousAt_const (y := (D.s.atP p).psiE y)).congr ?_
  filter_upwards [hmem] with w hw
  have hw' : (D.s.atP p).psiE (w - y) = 1 := psiE_of_norm p _ hw
  calc (D.s.atP p).psiE y = (D.s.atP p).psiE (w - y) * (D.s.atP p).psiE y := by rw [hw', one_mul]
    _ = (D.s.atP p).psiE w := by rw [← AddChar.map_add_eq_mul, sub_add_cancel]

theorem locPsiContC : LocPsiContC := fun _ _ p => psiE_cont p

end Formalism.L2.SG.Pf.LocCP
