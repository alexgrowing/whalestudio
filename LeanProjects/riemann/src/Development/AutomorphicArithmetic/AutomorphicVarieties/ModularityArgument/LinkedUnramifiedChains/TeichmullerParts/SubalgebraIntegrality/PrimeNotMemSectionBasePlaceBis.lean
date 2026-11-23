import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConjAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.J.D

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.J.D.AuxBlock5

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
  [IsAlgClosure L Ω] {n : ℕ}

private theorem cmp_of {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) :
    cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dif_pos h]
  rfl

private theorem cmp_over_l {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (x : Ga l L n) : cmp n w x = 1 := by
  unfold CaseU.cmp
  rw [dif_neg (not_not.2 h)]
  rfl

private theorem ext_cmp {x y : Ga l L n} (h : ∀ w, cmp n w x = cmp n w y) : x = y := by
  obtain ⟨x, rfl⟩ := (away l L n).rangeRestrict_surjective x
  obtain ⟨y, rfl⟩ := (away l L n).rangeRestrict_surjective y
  refine Subtype.ext (funext fun w => ?_)
  have e := h w.1
  rwa [cmp_of w.2, cmp_of w.2] at e

private theorem comm_of {a b : Ga l L n} (h : ∀ w, cmp n w a = 1 ∨ cmp n w b = 1) : Commute a b := by
  refine ext_cmp fun w => ?_
  rw [map_mul, map_mul]
  rcases h w with h | h <;> rw [h] <;> simp

private theorem l_under {u : Plc L} :
    ((l : ℕ) : 𝓞 L) ∈ u.asIdeal ↔ ((l : ℕ) : 𝓞 (Lp L)) ∈ (u.under (𝓞 (Lp L))).asIdeal := by
  change _ ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ u.asIdeal
  rw [map_natCast]

private theorem cLoc_over {w u : Plc L} (hw : IsSplitAt w) (x : UA L n) (h1 : cLoc w x = 1)
    (hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) : cLoc u x = 1 := by
  have hw1 : ∀ v, v = w → cLoc v x = 1 := by
    rintro v rfl
    exact h1
  rcases (GlobalTheory.SplitPts.over_split hw).2.2 u hu with rfl | rfl
  · exact h1
  · have hce := GlobalTheory.SplitPts.comp_eq x (conjSrc (GlobalTheory.SplitPts.conjE L) w)
    rw [hw1 _ (GlobalTheory.SplitPts.conjSrc_conjSrc_cm w), Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.transpose_one, Matrix.one_mul] at hce
    exact Units.ext hce

private theorem cmp_over {w u : Plc L} (hw : IsSplitAt w) (x : Ga l L n) (h1 : cmp n w x = 1)
    (hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) : cmp n u x = 1 := by
  by_cases hl : ((l : ℕ) : 𝓞 L) ∈ u.asIdeal
  · exact cmp_over_l hl x
  have hl' : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal := fun h => hl (l_under.2 (hu ▸ l_under.1 h))
  obtain ⟨x, rfl⟩ := (away l L n).rangeRestrict_surjective x
  rw [cmp_of hl'] at h1
  rw [cmp_of hl]
  exact cLoc_over hw x h1 hu

private theorem loc_one {w u : Plc L} {x : UA L n} (hx : x ∈ locU n w)
    (hu : u.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) : cLoc u x = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u) hu)

variable (s : HidaSetting l L Ω)

private theorem under_w (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

private theorem split_of {v : Plc (Lp L)} (h : v ∈ s.St ∨ v = s.v0) : IsSplitAt (s.w v) :=
  UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA v) (s.split v (Or.inr h)) _ (under_w s v)

private theorem SectionSplitPlaces : ((l : ℕ) : 𝓞 (Lp L)) ∉ s.v0.asIdeal := by
  intro h
  have hp := s.p_prime
  have hcard : Nat.card (𝓞 (Lp L) ⧸ s.v0.asIdeal) = s.p := s.norm_v0_eq_one
  have hl0 : ((l : ℕ) : 𝓞 (Lp L) ⧸ s.v0.asIdeal) = 0 := by
    exact (Ideal.Quotient.eq_zero_iff_mem.2 h : _) |> fun e => by simpa using e
  have hp0 : ((s.p : ℕ) : 𝓞 (Lp L) ⧸ s.v0.asIdeal) = 0 := by
    have := card_nsmul_eq_zero' (G := 𝓞 (Lp L) ⧸ s.v0.asIdeal) (x := 1)
    rw [hcard] at this
    simpa using this
  have hco : Nat.Coprime l s.p := (Nat.coprime_primes (Fact.out : l.Prime) hp).2 (Ne.symm s.p_ne)
  have h1 : (1 : 𝓞 (Lp L) ⧸ s.v0.asIdeal) = 0 := by
    have := Nat.Coprime.isCoprime hco
    obtain ⟨a, b, e⟩ := this
    have e' := congrArg (Int.cast : ℤ → 𝓞 (Lp L) ⧸ s.v0.asIdeal) e
    push_cast at e'
    rw [hl0, hp0] at e'
    simpa using e'.symm
  have hsub : Subsingleton (𝓞 (Lp L) ⧸ s.v0.asIdeal) := subsingleton_of_zero_eq_one h1.symm
  rw [Nat.card_of_subsingleton (0 : 𝓞 (Lp L) ⧸ s.v0.asIdeal)] at hcard
  exact hp.one_lt.ne hcard

private theorem away_of {v : Plc (Lp L)} (h : v ∈ s.St ∨ v = s.v0) : ((l : ℕ) : 𝓞 L) ∉ (s.w v).asIdeal := by
  intro e
  have e' := l_under.1 e
  rw [under_w] at e'
  rcases h with h | rfl
  · exact s.St_l _ h e'
  · exact SectionSplitPlaces s e'

private theorem mem_GaS {x : Ga l L n} : x ∈ GaS n s ↔
    ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ s.St ∧ w.under (𝓞 (Lp L)) ≠ s.v0 → cmp n w x = 1 := by
  simp only [GaS, Subgroup.mem_iInf, MonoidHom.mem_ker]

private theorem toGS_one {x : Ga l L n} (h : toGS n s x = 1) {w : Plc L}
    (hw : w.under (𝓞 (Lp L)) ∈ s.St ∨ w.under (𝓞 (Lp L)) = s.v0) : cmp n w x = 1 := by
  rcases hw with hw | hw
  · have e : cmp n (s.w (w.under (𝓞 (Lp L)))) x = 1 := congrFun (congrArg Prod.fst h) ⟨_, hw⟩
    exact cmp_over (split_of s (Or.inl hw)) x e (under_w s _).symm
  · have e : cmp n (s.w s.v0) x = 1 := congrArg Prod.snd h
    exact cmp_over (split_of s (Or.inr rfl)) x e (by rw [under_w, hw])

private theorem build (hn : 1 ≤ n) (T : Finset (Plc (Lp L))) (hT : ∀ v ∈ T, IsSplitAt (s.w v))
    (f : ∀ v, GLw n (s.w v)) :
    ∃ x : UA L n, (∀ v ∈ T, cLoc (s.w v) x = f v) ∧ ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ T → cLoc w x = 1 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, by simp, fun w _ => map_one _⟩
  | insert a T ha ih =>
    obtain ⟨x, hx, hx'⟩ := ih fun v hv => hT v (Finset.mem_insert_of_mem hv)
    obtain ⟨⟨j, hj, hj', -, -⟩, -⟩ := secU l L Ω s n hn (s.w a) (hT a (Finset.mem_insert_self _ _))
    have hloc : ∀ g (u : Plc L), u.under (𝓞 (Lp L)) ≠ a → cLoc u (j g) = 1 := fun g u hu =>
      loc_one (hj g) (by rwa [under_w])
    refine ⟨x * j (f a), fun v hv => ?_, fun w hw => ?_⟩
    · rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [map_mul, hj', hx' _ (by rwa [under_w]), one_mul]
      · rw [map_mul, hx v hv, hloc _ _ (by rw [under_w]; exact fun e => ha (e ▸ hv)), mul_one]
    · rw [map_mul, hx' w fun h => hw (Finset.mem_insert_of_mem h),
        hloc _ w fun h => hw (h ▸ Finset.mem_insert_self _ _), one_mul]

private theorem bij (hn : 1 ≤ n) : Function.Bijective ((toGS n s).comp (GaS n s).subtype) := by
  classical
  refine ⟨(injective_iff_map_eq_one _).2 ?_, fun g => ?_⟩
  · rintro ⟨x, hx⟩ h1
    refine Subtype.ext (ext_cmp fun w => ?_)
    rw [show ((1 : GaS n s) : Ga l L n) = 1 from rfl, map_one]
    by_cases hw : w.under (𝓞 (Lp L)) ∈ s.St ∨ w.under (𝓞 (Lp L)) = s.v0
    · exact toGS_one s h1 hw
    · exact (mem_GaS s).1 hx w (not_or.1 hw)
  · obtain ⟨x, hx, hx'⟩ := build s hn s.St (fun v hv => split_of s (Or.inl hv))
      fun v => if h : v ∈ s.St then g.1 ⟨v, h⟩ else 1
    obtain ⟨⟨j, hj, hj', -, -⟩, -⟩ := secU l L Ω s n hn (s.w s.v0) (split_of s (Or.inr rfl))
    have hloc : ∀ (u : Plc L), u.under (𝓞 (Lp L)) ≠ s.v0 → cLoc u (j g.2) = 1 := fun u hu =>
      loc_one (hj _) (by rwa [under_w])
    have hS : (away l L n).rangeRestrict (x * j g.2) ∈ GaS n s := by
      refine (mem_GaS s).2 fun w hw => ?_
      by_cases hl : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal
      · exact cmp_over_l hl _
      · rw [cmp_of hl, map_mul, hx' w hw.1, hloc w hw.2, one_mul]
    refine ⟨⟨_, hS⟩, Prod.ext (funext fun u => ?_) ?_⟩
    · change cmp n (s.w u) ((away l L n).rangeRestrict (x * j g.2)) = g.1 u
      rw [cmp_of (away_of s (Or.inl u.2)), map_mul, hx _ u.2, dif_pos u.2,
        hloc _ (by rw [under_w]; exact fun e => s.v0_St (e ▸ u.2)), mul_one]
    · change cmp n (s.w s.v0) ((away l L n).rangeRestrict (x * j g.2)) = g.2
      rw [cmp_of (away_of s (Or.inr rfl)), map_mul, hx' _ (by rw [under_w]; exact s.v0_St), hj', one_mul]

private theorem secS_spec (h : Function.Bijective ((toGS n s).comp (GaS n s).subtype)) (g : GS n s) :
    toGS n s (secS n s g) = g ∧ secS n s g ∈ GaS n s := by
  unfold secS
  rw [dif_pos h]
  exact ⟨(MulEquiv.ofBijective _ h).apply_symm_apply g, ((MulEquiv.ofBijective _ h).symm g).2⟩

private theorem mem_KS {k : Ga l L n} : k ∈ KS n s ↔ toGS n s k = 1 ∧
    ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ s.S → cmp n w k ∈ KO (w.adicCompletion L) (Fin n) := by
  simp only [KS, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker, Subgroup.mem_comap]

private theorem notS {w : Plc L} (h : w.under (𝓞 (Lp L)) ∉ s.S) :
    w.under (𝓞 (Lp L)) ∉ s.St ∧ w.under (𝓞 (Lp L)) ≠ s.v0 :=
  ⟨fun e => h (Or.inr (Or.inl e)), fun e => h (Or.inr (Or.inr e))⟩

private theorem mem_Ub {x : Ga l L n} : x ∈ Ub n s ↔
    (∀ u : s.St, cmp n (s.w u) x ∈ KO ((s.w u).adicCompletion L) (Fin n)) ∧ cmp n (s.w s.v0) x ∈ Kc _ n 1 := by
  simp only [Ub, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap]

variable {s}

private theorem mem_UQ {V : s.Lev} (Q : QData V) (hV : V.S' = s.S) {x : Ub n s} : x ∈ UQ n Q ↔
    ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ s.S → cmp n w (x : Ga l L n) ∈ KO (w.adicCompletion L) (Fin n) := by
  have hq : ∀ q : Q.Q, False := fun q => Q.notS q (by
    have h : (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := by
      rw [Q.range]
      exact Or.inr ⟨q, rfl⟩
    rwa [hV] at h)
  simp only [UQ, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker, Subgroup.mem_comap, hV]
  exact ⟨fun h => h.1, fun h => ⟨h, fun q => (hq q).elim⟩⟩

end UpperTheory.V.Z.J.D.AuxBlock5

open UpperTheory.V.Z.J.D.AuxBlock5 in
theorem UpperTheory.V.Z.J.D.secSp :
    SecS := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V hV
  have hb := bij s hn
  refine ⟨hb, fun g k hk => comm_of fun w => ?_, fun Q g => ⟨?_, ?_⟩⟩
  · by_cases hw : w.under (𝓞 (Lp L)) ∈ s.St ∨ w.under (𝓞 (Lp L)) = s.v0
    · exact Or.inr (toGS_one s ((mem_KS s).1 hk).1 hw)
    · exact Or.inl ((mem_GaS s).1 (secS_spec s hb g).2 w (not_or.1 hw))
  · rintro ⟨x, hx, rfl⟩
    have hU := (mem_Ub s).1 x.2
    have hs := secS_spec s hb (toGS n s (x : Ga l L n))
    refine ⟨(secS n s (toGS n s (x : Ga l L n)))⁻¹ * x, (mem_KS s).2 ⟨?_, fun w hw => ?_⟩,
      toGS n s (x : Ga l L n), Subgroup.mem_prod.2 ⟨fun u _ => hU.1 u, hU.2⟩, (mul_inv_cancel_left _ _).symm⟩
    · rw [map_mul, map_inv, hs.1, inv_mul_cancel]
    · rw [map_mul, map_inv, (mem_GaS s).1 hs.2 w (notS s hw), inv_one, one_mul]
      exact (mem_UQ Q hV).1 hx w hw
  · rintro ⟨k, hk, p, hp, rfl⟩
    obtain ⟨hk1, hk2⟩ := (mem_KS s).1 hk
    have hs := secS_spec s hb p
    have hU : secS n s p * k ∈ Ub n s := by
      refine (mem_Ub s).2 ⟨fun u => ?_, ?_⟩
      · have e : cmp n (s.w u) (secS n s p) = p.1 u := congrFun (congrArg Prod.fst hs.1) u
        rw [map_mul, e, toGS_one s hk1 (Or.inl (by rw [UpperTheory.V.Z.J.D.AuxBlock5.under_w]; exact u.2)), mul_one]
        exact (Subgroup.mem_prod.1 hp).1 u (Set.mem_univ _)
      · have e : cmp n (s.w s.v0) (secS n s p) = p.2 := congrArg Prod.snd hs.1
        rw [map_mul, e, toGS_one s hk1 (Or.inr (by rw [UpperTheory.V.Z.J.D.AuxBlock5.under_w])), mul_one]
        exact (Subgroup.mem_prod.1 hp).2
    refine ⟨⟨_, hU⟩, (mem_UQ Q hV).2 fun w hw => ?_, rfl⟩
    change cmp n w (secS n s p * k) ∈ _
    rw [map_mul, (mem_GaS s).1 hs.2 w (notS s hw), one_mul]
    exact hk2 w hw
