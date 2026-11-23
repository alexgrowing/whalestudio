import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.SupportG
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SupportLoc
import Formalism.LocalToGlobal.UnitaryNorms.CharRat
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices

noncomputable section

namespace Formalism.L2.SG.Pf

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel Formalism.L2.SG.SupportG
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section AbsSums

theorem posSemidef_of_hasSum {ι J : Type*} [Fintype ι] (f : J → ι → ℂ) (b : J → ℝ) (hb : ∀ j, 0 ≤ b j)
    (K : Matrix ι ι ℂ) (hK : ∀ x y, HasSum (fun j => (b j : ℂ) * f j x * star (f j y)) (K x y)) : K.PosSemidef := by
  have hherm : K.IsHermitian := by
    ext x y
    have h1 := (hK y x).star
    have h2 := hK x y
    simp only [Matrix.conjTranspose_apply]
    refine h1.unique ?_
    convert h2 using 1
    funext j
    simp only [star_mul', star_star, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    ring
  refine ⟨hherm, fun v => ?_⟩
  simp only [Finsupp.sum]
  have hs : HasSum (fun j => ∑ x ∈ v.support, ∑ y ∈ v.support, star (v x) * ((b j : ℂ) * f j x * star (f j y)) * v y)
      (∑ x ∈ v.support, ∑ y ∈ v.support, star (v x) * K x y * v y) :=
    hasSum_sum fun x _ => hasSum_sum fun y _ => ((hK x y).mul_left (star (v x))).mul_right (v y)
  refine hs.nonneg fun j => ?_
  have e2 : (∑ x ∈ v.support, ∑ y ∈ v.support, star (v x) * ((b j : ℂ) * f j x * star (f j y)) * v y) =
      (b j : ℂ) * ((∑ x ∈ v.support, star (v x) * f j x) * star (∑ x ∈ v.support, star (v x) * f j x)) := by
    simp only [star_sum, star_mul', star_star, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  rw [e2, Complex.star_def, Complex.mul_conj, ← Complex.ofReal_mul]
  exact Complex.zero_le_real.mpr (mul_nonneg (hb j) (Complex.normSq_nonneg _))

variable {P : Type*} {C : P → Type*}

def OffS (θ0 : ∀ p, C p) (S : Finset P) : Type _ := {θ : ∀ p, C p // ∀ p ∉ S, θ p = θ0 p}

set_option maxHeartbeats 800000 in

theorem hasSum_prod_offS [DecidableEq P] (θ0 : ∀ p, C p) (f : ∀ p, C p → ℂ) (a : P → ℂ) (S : Finset P)
    (hf : ∀ p ∈ S, HasSum (f p) (a p)) (hn : ∀ p ∈ S, Summable fun c => ‖f p c‖) :
    HasSum (fun θ : OffS θ0 S => ∏ p ∈ S, f p (θ.1 p)) (∏ p ∈ S, a p) ∧
      Summable (fun θ : OffS θ0 S => ‖∏ p ∈ S, f p (θ.1 p)‖) := by
  revert hf hn
  refine Finset.induction_on S ?_ ?_
  · intro _ _
    haveI : Unique (OffS θ0 (∅ : Finset P)) :=
      { default := ⟨θ0, fun _ _ => rfl⟩
        uniq := fun θ => Subtype.ext (funext fun p => θ.2 p (Finset.notMem_empty p)) }
    simp only [Finset.prod_empty, norm_one]
    exact ⟨by simpa using hasSum_fintype (fun _ : OffS θ0 (∅ : Finset P) => (1 : ℂ)),
      (hasSum_fintype _).summable⟩
  · intro q S hq ih hf hn
    obtain ⟨ihs, ihn⟩ := ih (fun p hp => hf p (Finset.mem_insert_of_mem hp))
      (fun p hp => hn p (Finset.mem_insert_of_mem hp))
    have hqS : q ∈ insert q S := Finset.mem_insert_self q S
    let e : C q × OffS θ0 S ≃ OffS θ0 (insert q S) :=
      { toFun := fun x => ⟨Function.update x.2.1 q x.1, fun p hp => by
          have hpq : p ≠ q := fun h => hp (h ▸ hqS)
          rw [Function.update_of_ne hpq]
          exact x.2.2 p (fun h => hp (Finset.mem_insert_of_mem h))⟩
        invFun := fun θ => (θ.1 q, ⟨Function.update θ.1 q (θ0 q), fun p hp => by
          by_cases hpq : p = q
          · subst hpq
            rw [Function.update_self]
          · rw [Function.update_of_ne hpq]
            exact θ.2 p (by simp [hpq, hp])⟩)
        left_inv := fun x => by
          refine Prod.ext (Function.update_self _ _ _) (Subtype.ext (funext fun p => ?_))
          by_cases hpq : p = q
          · subst hpq
            simp only [Function.update_self]
            exact (x.2.2 p hq).symm
          · simp only [Function.update_of_ne hpq]
        right_inv := fun θ => Subtype.ext (funext fun p => by
          by_cases hpq : p = q
          · subst hpq
            simp only [Function.update_self]
          · simp only [Function.update_of_ne hpq]) }
    have key : ∀ x : C q × OffS θ0 S,
        (∏ p ∈ insert q S, f p ((e x).1 p)) = f q x.1 * ∏ p ∈ S, f p (x.2.1 p) := by
      intro x
      rw [Finset.prod_insert hq]
      have h1 : (e x).1 q = x.1 := Function.update_self _ _ _
      have h2 : ∀ p ∈ S, (e x).1 p = x.2.1 p := fun p hp =>
        Function.update_of_ne (fun h : p = q => hq (h ▸ hp)) _ _
      rw [h1, Finset.prod_congr rfl (fun p hp => by rw [h2 p hp])]
    have hsm : Summable fun x : C q × OffS θ0 S => ‖f q x.1 * ∏ p ∈ S, f p (x.2.1 p)‖ :=
      Summable.mul_norm (f := f q) (g := fun θ : OffS θ0 S => ∏ p ∈ S, f p (θ.1 p)) (hn q hqS) ihn
    have hm := HasSum.mul (f := f q) (g := fun θ : OffS θ0 S => ∏ p ∈ S, f p (θ.1 p)) (hf q hqS) ihs
      hsm.of_norm
    rw [Finset.prod_insert hq]
    constructor
    · exact e.hasSum_iff.mp (by simpa only [Function.comp_def, key] using hm)
    · exact e.summable_iff.mp (by simpa only [Function.comp_def, key] using hsm)

end AbsSums

section Top

variable {D : Formalism.BasicNotions.D7}

def autP (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)
    (o : Option ((M p).Cls D.R.rS)) : ℂ :=
  match o with
  | some c => (((M p).nAut c : ℕ) : ℂ)
  | none => 1

def autPR (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)
    (o : Option ((M p).Cls D.R.rS)) : ℝ :=
  match o with
  | some c => (((M p).nAut c : ℕ) : ℝ)
  | none => 1

def autR (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (th : ∀ p, Option ((M p).Cls D.R.rS)) : ℝ :=
  ∏ᶠ p, autPR M p (th p)

def locF (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D)
    (w w' : Point D.host.E (D.R.rS + 1)) (o : Option ((M p).Cls D.R.rS)) : ℂ :=
  BBtop M δ T T' p w o * starRingEnd ℂ (BBtop M δ T T' p w' o) / autP M p o

def BBsq (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D)
    (w : Point D.host.E (D.R.rS + 1)) : Prop :=
  Summable fun o : Option ((M p).Cls D.R.rS) => ‖BBtop M δ T T' p w o‖ ^ 2 / ‖autP M p o‖

def UnramOff (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ)
    (θ0 : ∀ p, Option ((M p).Cls D.R.rS)) (S : Finset (PlF D)) (w : Point D.host.E (D.R.rS + 1)) : Prop :=
  ∀ p ∉ S, autP M p (θ0 p) = 1 ∧ ∀ o, BBtop M δ T T' p w o = if o = θ0 p then 1 else 0

def Restricted {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (θ0 θ : ∀ p, Option ((M p).Cls D.R.rS)) :
    Prop :=
  {p | θ p ≠ θ0 p}.Finite

variable {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {δ : ∀ p, (D.s.atP p).Fp} {T T' : ℕ}

theorem autG_eq_prod (th : ∀ p, Option ((M p).Cls D.R.rS)) : autG M th = ∏ᶠ p, autP M p (th p) := rfl

theorem autP_ofReal (p : PlF D) (o : Option ((M p).Cls D.R.rS)) : ((autPR M p o : ℝ) : ℂ) = autP M p o := by
  cases o <;> simp [autP, autPR]

theorem autG_eq_ofReal (th : ∀ p, Option ((M p).Cls D.R.rS)) : autG M th = ((autR M th : ℝ) : ℂ) := by
  rw [autG_eq_prod, autR]
  have e := MonoidHom.map_finprod_of_injective (Complex.ofRealHom : ℝ →+* ℂ).toMonoidHom
    Complex.ofReal_injective (fun p => autPR M p (th p))
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Complex.ofRealHom_eq_coe] at e
  rw [e]
  simp only [autP_ofReal]

theorem autR_nonneg (th : ∀ p, Option ((M p).Cls D.R.rS)) : 0 ≤ autR M th := by
  unfold autR
  exact finprod_nonneg fun p => by unfold autPR; split <;> positivity

theorem bbtop_none (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) : BBtop M δ T T' p w none = 0 := by
  unfold BBtop
  cases modPt δ T T' p w <;> rfl

theorem topTerm_eq_tsum (p : PlF D) (w w' : Point D.host.E (D.R.rS + 1)) :
    KtopP M δ T T' p w w' = ∑' c : (M p).Cls D.R.rS, locF M δ T T' p w w' (some c) := by
  unfold KtopP locF
  unfold locK BBtop
  rcases ha : modPt δ T T' p w with _ | a <;> rcases hb : modPt δ T T' p w' with _ | b
  · simp
  · simp
  · simp
  · simp only [Loc.Model.Kk, autP]
    rw [show dfac M δ T T' p w * (∑' c : (M p).Cls D.R.rS, (M p).BB a c * starRingEnd ℂ ((M p).BB b c) /
        (((M p).nAut c : ℕ) : ℂ)) * starRingEnd ℂ (dfac M δ T T' p w') =
        (dfac M δ T T' p w * starRingEnd ℂ (dfac M δ T T' p w')) * (∑' c : (M p).Cls D.R.rS,
        (M p).BB a c * starRingEnd ℂ ((M p).BB b c) / (((M p).nAut c : ℕ) : ℂ)) by ring, ← tsum_mul_left]
    congr 1
    funext c
    simp only [map_mul]
    ring

theorem hasSum_locF {p : PlF D} {w w' : Point D.host.E (D.R.rS + 1)} (hs : Summable (locF M δ T T' p w w')) :
    HasSum (locF M δ T T' p w w') (KtopP M δ T T' p w w') := by
  have h0 : ∀ x ∉ Set.range (@some ((M p).Cls D.R.rS)), locF M δ T T' p w w' x = 0 := by
    intro x hx
    cases x with
    | none => simp [locF, bbtop_none]
    | some c => exact absurd ⟨c, rfl⟩ hx
  rw [← (Option.some_injective _).hasSum_iff h0, topTerm_eq_tsum]
  exact (hs.comp_injective (Option.some_injective _)).hasSum

theorem locF_summable {p : PlF D} {w w' : Point D.host.E (D.R.rS + 1)} (h : BBsq M δ T T' p w)
    (h' : BBsq M δ T T' p w') : Summable fun o => ‖locF M δ T T' p w w' o‖ := by
  unfold BBsq at h h'
  refine Summable.of_nonneg_of_le (fun o => norm_nonneg _) (fun o => ?_) ((h.add h').div_const 2)
  simp only [locF, norm_div, norm_mul, RCLike.norm_conj]
  have hab : ‖BBtop M δ T T' p w o‖ * ‖BBtop M δ T T' p w' o‖ ≤
      (‖BBtop M δ T T' p w o‖ ^ 2 + ‖BBtop M δ T T' p w' o‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖BBtop M δ T T' p w o‖ - ‖BBtop M δ T T' p w' o‖)]
  calc ‖BBtop M δ T T' p w o‖ * ‖BBtop M δ T T' p w' o‖ / ‖autP M p o‖
      ≤ ((‖BBtop M δ T T' p w o‖ ^ 2 + ‖BBtop M δ T T' p w' o‖ ^ 2) / 2) / ‖autP M p o‖ := by gcongr
    _ = (‖BBtop M δ T T' p w o‖ ^ 2 / ‖autP M p o‖ + ‖BBtop M δ T T' p w' o‖ ^ 2 / ‖autP M p o‖) / 2 := by ring

theorem topTerm_off {θ0 : ∀ p, Option ((M p).Cls D.R.rS)} {S : Finset (PlF D)} {w w' : Point D.host.E (D.R.rS + 1)}
    (hu : UnramOff M δ T T' θ0 S w) (hu' : UnramOff M δ T T' θ0 S w') {p : PlF D} (hp : p ∉ S) :
    KtopP M δ T T' p w w' = 1 := by
  obtain ⟨ha, hb⟩ := hu p hp
  obtain ⟨-, hb'⟩ := hu' p hp
  rw [topTerm_eq_tsum]
  cases h0 : θ0 p with
  | none =>
    have e := hb none
    rw [h0, bbtop_none] at e
    simp at e
  | some c0 =>
    rw [h0] at ha hb hb'
    rw [tsum_eq_single c0]
    · simp [locF, hb, hb', ha]
    · intro c hc
      simp [locF, hb, hb', hc]

theorem bbG_eq_prod {θ0 : ∀ p, Option ((M p).Cls D.R.rS)} {S : Finset (PlF D)} {w : Point D.host.E (D.R.rS + 1)}
    (hu : UnramOff M δ T T' θ0 S w) {θ : ∀ p, Option ((M p).Cls D.R.rS)} (hθ : ∀ p ∉ S, θ p = θ0 p)
    {κ : Option D.host.E} (hk : kind w = κ) : BBG M δ T T' w κ θ = ∏ p ∈ S, BBtop M δ T T' p w (θ p) := by
  unfold BBG
  rw [if_pos hk]
  refine finprod_eq_prod_of_mulSupport_subset _ fun p hp => ?_
  by_contra hpS
  apply hp
  show BBtop M δ T T' p w (θ p) = 1
  rw [hθ p hpS, (hu p hpS).2]
  simp

theorem autG_eq_prodS {θ0 : ∀ p, Option ((M p).Cls D.R.rS)} {S : Finset (PlF D)} {w : Point D.host.E (D.R.rS + 1)}
    (hu : UnramOff M δ T T' θ0 S w) {θ : ∀ p, Option ((M p).Cls D.R.rS)} (hθ : ∀ p ∉ S, θ p = θ0 p) :
    autG M θ = ∏ p ∈ S, autP M p (θ p) := by
  rw [autG_eq_prod]
  refine finprod_eq_prod_of_mulSupport_subset _ fun p hp => ?_
  by_contra hpS
  exact hp (by show autP M p (θ p) = 1; rw [hθ p hpS]; exact (hu p hpS).1)

theorem bbtop_mulSupport_finite {θ0 : ∀ p, Option ((M p).Cls D.R.rS)} {S : Finset (PlF D)}
    {w : Point D.host.E (D.R.rS + 1)} (hu : UnramOff M δ T T' θ0 S w) {θ : ∀ p, Option ((M p).Cls D.R.rS)}
    (hr : Restricted θ0 θ) : (Function.mulSupport fun p => BBtop M δ T T' p w (θ p)).Finite := by
  refine ((S.finite_toSet).union (show {p | θ p ≠ θ0 p}.Finite from hr)).subset fun p hp => ?_
  by_contra h
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at h
  exact hp (by show BBtop M δ T T' p w (θ p) = 1; rw [h.2, (hu p h.1).2]; simp)

theorem bbG_zero {θ0 : ∀ p, Option ((M p).Cls D.R.rS)} {S : Finset (PlF D)} {w : Point D.host.E (D.R.rS + 1)}
    (hu : UnramOff M δ T T' θ0 S w) {θ : ∀ p, Option ((M p).Cls D.R.rS)} (hr : Restricted θ0 θ) {p : PlF D}
    (hp : p ∉ S) (hne : θ p ≠ θ0 p) (κ : Option D.host.E) : BBG M δ T T' w κ θ = 0 := by
  unfold BBG
  split_ifs
  · exact finprod_eq_zero _ p (by show BBtop M δ T T' p w (θ p) = 0; rw [(hu p hp).2]; simp [hne])
      (bbtop_mulSupport_finite hu hr)
  · rfl

theorem ktopG_hasSum {θ0 : ∀ p, Option ((M p).Cls D.R.rS)} {S : Finset (PlF D)} {w w' : Point D.host.E (D.R.rS + 1)}
    (hk : kind w = kind w') (hu : UnramOff M δ T T' θ0 S w) (hu' : UnramOff M δ T T' θ0 S w')
    (hs : ∀ p ∈ S, BBsq M δ T T' p w) (hs' : ∀ p ∈ S, BBsq M δ T T' p w') :
    HasSum (fun θ : {θ : ∀ p, Option ((M p).Cls D.R.rS) // Restricted θ0 θ} =>
      BBG M δ T T' w (kind w) θ.1 * starRingEnd ℂ (BBG M δ T T' w' (kind w) θ.1) / autG M θ.1)
      (KtopG M δ T T' w w') := by
  have hN : ∀ p ∈ S, Summable fun o => ‖locF M δ T T' p w w' o‖ :=
    fun p hp => locF_summable (hs p hp) (hs' p hp)
  have hS : ∀ p ∈ S, HasSum (locF M δ T T' p w w') (KtopP M δ T T' p w w') :=
    fun p hp => hasSum_locF (hN p hp).of_norm
  obtain ⟨hsum, -⟩ := hasSum_prod_offS θ0 (fun p => locF M δ T T' p w w')
    (fun p => KtopP M δ T T' p w w') S hS hN
  have hK : KtopG M δ T T' w w' = ∏ p ∈ S, KtopP M δ T T' p w w' := by
    unfold KtopG
    rw [if_pos hk]
    exact finprod_eq_prod_of_mulSupport_subset _ (fun p hp => by
      by_contra hpS
      exact hp (topTerm_off hu hu' hpS))
  rw [hK]
  let g : OffS θ0 S → {θ : ∀ p, Option ((M p).Cls D.R.rS) // Restricted θ0 θ} := fun θ =>
    ⟨θ.1, S.finite_toSet.subset (fun p hp => by
      by_contra h
      exact hp (θ.2 p h))⟩
  have hg : Function.Injective g := fun a b h =>
    Subtype.ext (congrArg (fun x : {θ : ∀ p, Option ((M p).Cls D.R.rS) // Restricted θ0 θ} => x.1) h)
  have hz : ∀ θ, θ ∉ Set.range g →
      BBG M δ T T' w (kind w) θ.1 * starRingEnd ℂ (BBG M δ T T' w' (kind w) θ.1) / autG M θ.1 = 0 := by
    intro θ hθ
    by_contra hne
    apply hθ
    have hoff : ∀ p ∉ S, θ.1 p = θ0 p := fun p hp => by
      by_contra hpe
      apply hne
      rw [bbG_zero hu θ.2 hp hpe, zero_mul, zero_div]
    exact ⟨⟨θ.1, hoff⟩, rfl⟩
  rw [← hg.hasSum_iff hz]
  convert hsum using 1
  funext θ
  simp only [Function.comp_apply, g]
  rw [bbG_eq_prod hu θ.2 rfl, bbG_eq_prod hu' θ.2 hk.symm, autG_eq_prodS hu θ.2, map_prod,
    ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  rfl

end Top

section Pos

variable {D : Formalism.BasicNotions.D7}

theorem emb_conjF (τ : D.what₂.Tau) (x : D.host.E) :
    D.host.emb (D.eTau τ : D.R.GG) (D.conjF x) =
      starRingEnd ℂ (D.host.emb (D.eTau τ : D.R.GG) x) := by
  letI := Formalism.MainNotions.LocalModelPeriodLattices.cmE D
  rw [Formalism.MainNotions.LocalModelPeriodLattices.conjF_eq_complexConj]
  exact NumberField.IsCMField.complexEmbedding_complexConj _ _ _

theorem re_emb_G (τ : D.what₂.Tau) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) :
    (D.host.emb (D.eTau τ : D.R.GG) (Gpt T T' w)).re =
      Complex.normSq (D.host.emb (D.eTau τ : D.R.GG) (Dmin w (D.R.rS + 1))) -
        (T : ℝ) * T' * Complex.normSq (D.host.emb (D.eTau τ : D.R.GG) (Dmin w D.R.rS)) := by
  simp only [Gpt, map_sub, map_mul, map_natCast, emb_conjF, Complex.mul_conj, Complex.sub_re, Complex.mul_re,
    Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem dmin_top_eq_zeta (w : Point D.host.E (D.R.rS + 1)) (h0 : Dmin w D.R.rS ≠ 0) :
    Dmin w (D.R.rS + 1) = zetaOf w * Dmin w D.R.rS := by
  simp only [zetaOf]
  exact (div_mul_cancel₀ _ h0).symm

theorem totPos_of_kind {T T' : ℕ} {w w' : Point D.host.E (D.R.rS + 1)} (hk : kind w = kind w')
    (h' : TotPos (Gpt T T' w')) : TotPos (Gpt (D := D) T T' w) := by
  intro τ
  have hd := Formalism.MainNotions.BridgeLemma.Dmin_top_ne w
  have h'τ := h' τ
  rw [re_emb_G] at h'τ ⊢
  by_cases h0 : Dmin w D.R.rS = 0
  · rw [h0, map_zero, Complex.normSq_zero, mul_zero, sub_zero]
    exact Complex.normSq_pos.mpr ((map_ne_zero _).mpr hd)
  · have h0' : Dmin w' D.R.rS ≠ 0 := by
      intro h
      simp [kind, h0, h] at hk
    have hz : zetaOf w = zetaOf w' := by simpa [kind, h0, h0'] using hk
    rw [dmin_top_eq_zeta w h0]
    rw [dmin_top_eq_zeta w' h0'] at h'τ
    rw [hz]
    simp only [map_mul, Complex.normSq_mul] at h'τ ⊢
    have hp : 0 < Complex.normSq (D.host.emb (D.eTau τ : D.R.GG) (Dmin w D.R.rS)) :=
      Complex.normSq_pos.mpr ((map_ne_zero _).mpr h0)
    have hp' : 0 < Complex.normSq (D.host.emb (D.eTau τ : D.R.GG) (Dmin w' D.R.rS)) :=
      Complex.normSq_pos.mpr ((map_ne_zero _).mpr h0')
    have hq : 0 < Complex.normSq (D.host.emb (D.eTau τ : D.R.GG) (zetaOf w')) - (T : ℝ) * T' := by
      by_contra hc
      push_neg at hc
      nlinarith
    nlinarith [mul_pos hq hp]

end Pos

section Vec

section LocCls

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem det_assoc_cls (Mo : Loc.Model F E) {m : ℕ} (a b : Loc.Pt E (m + 1)) (c : Mo.Cls m) (hc1 : Mo.BB a c ≠ 0)
    (hc2 : Mo.BB b c ≠ 0) : IsUnit a.mat.det ∧ ∃ u : (Mo.R)ˣ, b.mat.det = a.mat.det * ((u : Mo.R) : E) := by
  obtain ⟨Z1, hZ1, i1⟩ := bb_ne Mo a c hc1
  obtain ⟨Z2, hZ2, i2⟩ := bb_ne Mo b c hc2
  have hreg : ∀ x, Z1.Z.det * x = 0 → x = 0 := by
    intro x hx
    have e := congrArg Mo.R.subtype hx
    rw [map_mul, RingHom.map_det, map_zero] at e
    have e2 := (Z1.unit.mul_right_eq_zero).1 e
    exact Subtype.val_injective (e2.trans (map_zero Mo.R.subtype).symm)
  obtain ⟨u, hu⟩ := det_assoc_of_cok Z1.Z Z2.Z ((Classical.choice i1).1.trans (Classical.choice i2).1.symm) hreg
  refine ⟨hZ1 ▸ Z1.unit, u, ?_⟩
  have e := congrArg Mo.R.subtype hu
  rw [map_mul, RingHom.map_det, RingHom.map_det] at e
  rw [← hZ1, ← hZ2]
  exact e

end LocCls

variable {D : Formalism.BasicNotions.D7}

theorem modK_eq_of_assoc (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (T T' : ℕ) (p : PlF D) {w w' : Point D.host.E (D.R.rS + 1)} (hk : kind w = kind w')
    (a b : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (ha : modPt δ T T' p w = some a) (hb : modPt δ T T' p w' = some b)
    (hab : IsUnit a.mat.det ∧ ∃ u : ((M p).R)ˣ, b.mat.det = a.mat.det * ((u : (M p).R) : (D.s.atP p).Ep)) :
    (M p).modK ((D.s.atP p).ιE (Dmin w (D.R.rS + 1))) = (M p).modK ((D.s.atP p).ιE (Dmin w' (D.R.rS + 1))) ∧
    (M p).modK ((D.s.atP p).ιE (Dmin w D.R.rS)) = (M p).modK ((D.s.atP p).ιE (Dmin w' D.R.rS)) := by
  obtain ⟨haU, u, hdet⟩ := hab
  have ea := det_amat δ T T' p w a ha
  have eb := det_amat δ T T' p w' b hb
  by_cases h0 : Dmin w D.R.rS = 0
  · have h0' : Dmin w' D.R.rS = 0 := by
      unfold kind at hk
      rw [if_pos h0] at hk
      by_contra hne
      rw [if_neg hne] at hk
      exact absurd hk (by simp)
    rw [h0, map_zero, mul_zero, mul_zero, add_zero] at ea
    rw [h0', map_zero, mul_zero, mul_zero, add_zero] at eb
    have hL : IsUnit ((∏ x : Fin (D.R.rS + 1), rho δ p x) ^ 2 * kap p ^ (D.R.rS + 1)) :=
      isUnit_of_mul_isUnit_left (ea ▸ haU)
    have hX : (D.s.atP p).ιE (Dmin w' (D.R.rS + 1)) =
        (D.s.atP p).ιE (Dmin w (D.R.rS + 1)) * (((u : (M p).R)) : (D.s.atP p).Ep) := by
      apply hL.mul_left_cancel
      rw [← eb, hdet, ea]
      ring
    refine ⟨?_, by rw [h0, h0']⟩
    rw [hX, modK_mul_unit]
  · have h0' : Dmin w' D.R.rS ≠ 0 := by
      unfold kind at hk
      rw [if_neg h0] at hk
      intro hne
      rw [if_pos hne] at hk
      exact absurd hk (by simp)
    have hz : zetaOf w = zetaOf w' := by
      unfold kind at hk
      rw [if_neg h0, if_neg h0'] at hk
      exact Option.some.inj hk
    obtain ⟨l0, t, hb0, hs0⟩ := last_one w h0
    obtain ⟨l0', t', hb0', hs0'⟩ := last_one w' h0'
    have htt : t' = t := by
      rw [← zeta_snoc w h0 l0 t hb0 hs0, ← zeta_snoc w' h0' l0' t' hb0' hs0', hz]
    subst htt
    have hL1 : (∏ x : Fin (D.R.rS + 1), rho δ p x) ^ 2 * kap p ^ (D.R.rS + 1) =
        ((∏ x : Fin D.R.rS, rho δ p x) ^ 2 * kap p ^ D.R.rS) * (rho δ p D.R.rS * rho δ p D.R.rS * kap p) := by
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      ring
    rw [amat_last δ T T' p w a ha l0 t' hb0 hs0, ptMat_last w l0 t' hb0 hs0, dmin_snoc w l0 t' hb0 hs0, hL1,
      map_mul] at ea
    rw [amat_last δ T T' p w' b hb l0' t' hb0' hs0', ptMat_last w' l0' t' hb0' hs0', dmin_snoc w' l0' t' hb0' hs0',
      hL1, map_mul] at eb
    have ea' : a.mat.det = (((∏ x : Fin D.R.rS, rho δ p x) ^ 2 * kap p ^ D.R.rS) * blkTop δ T T' p (D.R.rS + 1) 1 t') *
        (D.s.atP p).ιE (Dmin w D.R.rS) := by rw [ea]; ring
    have eb' : b.mat.det = (((∏ x : Fin D.R.rS, rho δ p x) ^ 2 * kap p ^ D.R.rS) * blkTop δ T T' p (D.R.rS + 1) 1 t') *
        (D.s.atP p).ιE (Dmin w' D.R.rS) := by rw [eb]; ring
    have hL : IsUnit (((∏ x : Fin D.R.rS, rho δ p x) ^ 2 * kap p ^ D.R.rS) * blkTop δ T T' p (D.R.rS + 1) 1 t') :=
      isUnit_of_mul_isUnit_left (ea' ▸ haU)
    have hY : (D.s.atP p).ιE (Dmin w' D.R.rS) =
        (D.s.atP p).ιE (Dmin w D.R.rS) * (((u : (M p).R)) : (D.s.atP p).Ep) := by
      apply hL.mul_left_cancel
      rw [← eb', hdet, ea']
      ring
    refine ⟨?_, by rw [hY, modK_mul_unit]⟩
    rw [dmin_snoc w l0 t' hb0 hs0, dmin_snoc w' l0' t' hb0' hs0', map_mul, map_mul, hY]
    rw [show (D.s.atP p).ιE (Dmin w D.R.rS) * (((u : (M p).R)) : (D.s.atP p).Ep) * (D.s.atP p).ιE t' =
      (D.s.atP p).ιE (Dmin w D.R.rS) * (D.s.atP p).ιE t' * (((u : (M p).R)) : (D.s.atP p).Ep) by ring,
      modK_mul_unit]

theorem normG_eq_of_loc (hN : NormProd D) {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) (T T' : ℕ)
    {w w' : Point D.host.E (D.R.rS + 1)} (hk : kind w = kind w')
    (loc : ∀ p, (M p).modK ((D.s.atP p).ιE (Dmin w (D.R.rS + 1))) = (M p).modK ((D.s.atP p).ιE (Dmin w' (D.R.rS + 1))) ∧
      (M p).modK ((D.s.atP p).ιE (Dmin w D.R.rS)) = (M p).modK ((D.s.atP p).ιE (Dmin w' D.R.rS))) :
    normG T T' w = normG T T' w' := by
  unfold normG
  by_cases h0 : Dmin w D.R.rS = 0
  · have h0' : Dmin w' D.R.rS = 0 := by
      by_contra h
      simp [kind, h0, h] at hk
    have e1 := absNorm_eq_of_prod hN hA (Formalism.MainNotions.BridgeLemma.Dmin_top_ne w) (Formalism.MainNotions.BridgeLemma.Dmin_top_ne w')
      (fun p => (loc p).1)
    simp only [Gpt, h0, h0', map_zero, mul_zero, sub_zero, map_mul, norm_conjF, abs_mul, e1]
  · have h0' : Dmin w' D.R.rS ≠ 0 := by
      intro h
      simp [kind, h0, h] at hk
    have hz : zetaOf w = zetaOf w' := by simpa [kind, h0, h0'] using hk
    have e2 := absNorm_eq_of_prod hN hA h0 h0' (fun p => (loc p).2)
    have hG : ∀ v : Point D.host.E (D.R.rS + 1), Dmin v D.R.rS ≠ 0 → Gpt T T' v =
        (Dmin v D.R.rS * D.conjF (Dmin v D.R.rS)) * (zetaOf v * D.conjF (zetaOf v) - (T : D.host.E) * T') := by
      intro v hv
      simp only [Gpt]
      rw [dmin_top_eq_zeta v hv, map_mul]
      ring
    rw [hG w h0, hG w' h0', hz]
    simp only [map_mul, norm_conjF, abs_mul, e2]

theorem supportVec_of_normProd (hN : NormProd D) : SupportVec D := by
  intro δ M hA T T' w w' κ th hf hf' h1 h2
  unfold BBG at h1 h2
  have hk1 : kind w = κ := by
    by_contra h
    exact h1 (if_neg h)
  have hk2 : kind w' = κ := by
    by_contra h
    exact h2 (if_neg h)
  rw [if_pos hk1] at h1
  rw [if_pos hk2] at h2
  have hk : kind w = kind w' := hk1.trans hk2.symm
  refine normG_eq_of_loc hN hA T T' hk fun p => ?_
  have e1 : BBtop M δ T T' p w (th p) ≠ 0 := fun h => h1 (finprod_eq_zero _ p h hf)
  have e2 : BBtop M δ T T' p w' (th p) ≠ 0 := fun h => h2 (finprod_eq_zero _ p h hf')
  unfold BBtop at e1 e2
  rcases ha : modPt δ T T' p w with _ | a <;> rcases hb : modPt δ T T' p w' with _ | b <;>
    rcases hc : th p with _ | c <;> simp only [ha, hb, hc, ne_eq, not_true_eq_false] at e1 e2
  exact modK_eq_of_assoc δ M T T' p hk a b ha hb
    (det_assoc_cls (M p) a b c (right_ne_zero_of_mul e1) (right_ne_zero_of_mul e2))

end Vec

section PropSix

variable {D : Formalism.BasicNotions.D7}

def TopLocal {Y : TermTie D} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {u u' : D.what₂.Word} (X : TermLoc D Y δ M u u') : Prop :=
  ∃ θ0 : ∀ p, Option ((M p).Cls D.R.rS),
    (∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
      (∃ S : Finset (PlF D), UnramOff M δ (D.mem u).A.T (D.mem u').A.T θ0 S w) ∧
        ∀ p, BBsq M δ (D.mem u).A.T (D.mem u').A.T p w) ∧
    ∀ γ : D.s.Term u u', D.s.generic γ → Gpt (D.mem u).A.T (D.mem u').A.T (D.s.ptOf γ) ≠ 0 →
      Restricted θ0 (thCls X γ)

theorem n0_pos {c : ℝ} (hc : 0 < c) {T T' : ℕ} {w : Point D.host.E (D.R.rS + 1)} (hG : Gpt T T' w ≠ 0) :
    0 < n0 c T T' w := by
  unfold n0
  exact mul_pos hc (pow_pos (Real.sqrt_pos.mpr (abs_pos.mpr (Rat.cast_ne_zero.mpr
    ((Algebra.norm_ne_zero_iff).mpr (div_ne_zero hG (pow_ne_zero _
      (Nat.cast_ne_zero.mpr (Formalism.MainNotions.LocalModelPeriodLattices.gS_pos D).ne'))))))) _)

theorem unramOff_mono {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {δ : ∀ p, (D.s.atP p).Fp}
    {T T' : ℕ} {θ0 : ∀ p, Option ((M p).Cls D.R.rS)} {S S' : Finset (PlF D)} {w : Point D.host.E (D.R.rS + 1)}
    (hu : UnramOff M δ T T' θ0 S w) (hS : S ⊆ S') : UnramOff M δ T T' θ0 S' w := by
  intro p hp
  exact hu p (fun h => hp (hS h))

theorem ktop_sub_posSemidef {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {δ : ∀ p, (D.s.atP p).Fp}
    {T T' : ℕ} {ι : Type*} [Fintype ι] (w : ι → Point D.host.E (D.R.rS + 1)) (θ0 : ∀ p, Option ((M p).Cls D.R.rS))
    (Sx : ι → Finset (PlF D)) (hU : ∀ x, UnramOff M δ T T' θ0 (Sx x) (w x)) (hB : ∀ x p, BBsq M δ T T' p (w x))
    (Θs : Finset (Option D.host.E × (∀ p, Option ((M p).Cls D.R.rS))))
    (hΘ : ∀ j ∈ Θs, (∃ x, j.1 = kind (w x)) ∧ Restricted θ0 j.2) :
    (Matrix.of fun x y => KtopG M δ T T' (w x) (w y) - ∑ j ∈ Θs, (((autR M j.2)⁻¹ : ℝ) : ℂ) *
      BBG M δ T T' (w x) j.1 j.2 * star (BBG M δ T T' (w y) j.1 j.2)).PosSemidef := by
  apply posSemidef_of_hasSum (J := Option D.host.E × {θ : ∀ p, Option ((M p).Cls D.R.rS) // Restricted θ0 θ})
    (fun j x => BBG M δ T T' (w x) j.1 j.2.1)
    (fun j => if (j.1, j.2.1) ∈ Θs then 0 else (autR M j.2.1)⁻¹)
    (fun j => by
      split_ifs
      · exact le_refl 0
      · exact inv_nonneg.mpr (autR_nonneg _))
  intro x y
  simp only [Matrix.of_apply]
  have hA : HasSum (fun j : Option D.host.E × {θ : ∀ p, Option ((M p).Cls D.R.rS) // Restricted θ0 θ} =>
      (((autR M j.2.1)⁻¹ : ℝ) : ℂ) * BBG M δ T T' (w x) j.1 j.2.1 * star (BBG M δ T T' (w y) j.1 j.2.1))
      (KtopG M δ T T' (w x) (w y)) := by
    by_cases hk : kind (w x) = kind (w y)
    · have h1 := ktopG_hasSum hk (unramOff_mono (hU x) Finset.subset_union_left)
        (unramOff_mono (hU y) Finset.subset_union_right) (fun p _ => hB x p) (fun p _ => hB y p)
      let g : {θ : ∀ p, Option ((M p).Cls D.R.rS) // Restricted θ0 θ} → Option D.host.E × {θ : ∀ p, Option ((M p).Cls D.R.rS) // Restricted θ0 θ} := fun θ => (kind (w x), θ)
      have hg : Function.Injective g := fun a b h => (Prod.ext_iff.mp h).2
      rw [← hg.hasSum_iff]
      · convert h1 using 1
        funext θ
        simp only [Function.comp_apply, g, autG_eq_ofReal, Complex.ofReal_inv, starRingEnd_apply]
        rw [div_eq_inv_mul]
        ring
      · intro j hj
        have hne : kind (w x) ≠ j.1 := fun h => hj ⟨j.2, Prod.ext h rfl⟩
        simp [BBG, hne]
    · have hK0 : KtopG M δ T T' (w x) (w y) = 0 := by
        unfold KtopG
        rw [if_neg hk]
      rw [hK0]
      convert hasSum_zero using 1
      funext j
      by_cases h1 : kind (w x) = j.1
      · have h2 : kind (w y) ≠ j.1 := fun h => hk (h1.trans h.symm)
        simp [BBG, h2]
      · simp [BBG, h1]
  let e : Θs → Option D.host.E × {θ : ∀ p, Option ((M p).Cls D.R.rS) // Restricted θ0 θ} := fun i => (i.1.1, ⟨i.1.2, (hΘ i.1 i.2).2⟩)
  have he : Function.Injective e := fun a b h =>
    Subtype.ext (Prod.ext (congrArg (fun z : Option D.host.E × {θ : ∀ p, Option ((M p).Cls D.R.rS) // Restricted θ0 θ} => z.1) h) (congrArg (fun z : Option D.host.E × {θ : ∀ p, Option ((M p).Cls D.R.rS) // Restricted θ0 θ} => z.2.1) h))
  have hB' : HasSum (fun j : Option D.host.E × {θ : ∀ p, Option ((M p).Cls D.R.rS) // Restricted θ0 θ} => if (j.1, j.2.1) ∈ Θs then
      (((autR M j.2.1)⁻¹ : ℝ) : ℂ) * BBG M δ T T' (w x) j.1 j.2.1 * star (BBG M δ T T' (w y) j.1 j.2.1) else 0)
      (∑ i ∈ Θs, (((autR M i.2)⁻¹ : ℝ) : ℂ) * BBG M δ T T' (w x) i.1 i.2 * star (BBG M δ T T' (w y) i.1 i.2)) := by
    rw [← he.hasSum_iff]
    · convert hasSum_fintype _ using 1
      rw [← Finset.sum_coe_sort Θs]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [Function.comp_apply, e, Prod.mk.eta, if_pos i.2]
    · intro j hj
      rw [if_neg]
      intro hmem
      exact hj ⟨⟨(j.1, j.2.1), hmem⟩, rfl⟩
  convert hA.sub hB' using 1
  all_goals first
    | rfl
    | (funext j
       split_ifs <;> simp)

end PropSix

end Formalism.L2.SG.Pf
