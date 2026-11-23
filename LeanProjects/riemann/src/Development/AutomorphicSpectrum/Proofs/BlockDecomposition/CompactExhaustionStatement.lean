import Mathlib
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

noncomputable section

open Finset MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.WordFam

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgDs.K

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

theorem eword_smooth (hP : IsPsiFor ε lam T Ψ) (v : T.V) :
    ∀ w : List (Fin n × Fin n), IsSmoothL2 ε (Formalism.REAL.Eword ε w (jfun Ψ T.w v))
  | [] => datumFunction_isSmoothL2 hP T.w v
  | p :: w => (eword_smooth hP v w).Eab p.1 p.2

def cD (hP : IsPsiFor ε lam T Ψ) (w : List (Fin n × Fin n)) (v : T.V) : smD ε (rreg ε) :=
  ⟨toL2 ε (Formalism.REAL.Eword ε w (jfun Ψ T.w v)), toL2_mem_smD_of_isSmoothL2 (eword_smooth hP v w)⟩

theorem cD_cons (hP : IsPsiFor ε lam T Ψ) (p : Fin n × Fin n) (w : List (Fin n × Fin n)) (v : T.V) :
    cD hP (p :: w) v = smE ε (rreg ε) p.1 p.2 (cD hP w v) :=
  Subtype.ext (rightDerivative_toL2 (eword_smooth hP v w) p.1 p.2).symm

theorem cD_add (hP : IsPsiFor ε lam T Ψ) (u v : T.V) :
    ∀ w : List (Fin n × Fin n), cD hP w (u + v) = cD hP w u + cD hP w v
  | [] => Subtype.ext (datumEmbedding_add hP T.w u v)
  | p :: w => by rw [cD_cons, cD_cons, cD_cons, cD_add hP u v w, map_add]

theorem cD_smul (hP : IsPsiFor ε lam T Ψ) (c : ℂ) (v : T.V) :
    ∀ w : List (Fin n × Fin n), cD hP w (c • v) = c • cD hP w v
  | [] => Subtype.ext (datumEmbedding_smul hP T.w c v)
  | p :: w => by rw [cD_cons, cD_cons, cD_smul hP c v w, map_smul]

theorem cD_zero (hP : IsPsiFor ε lam T Ψ) (w : List (Fin n × Fin n)) : cD hP w (0 : T.V) = 0 := by
  simpa using cD_smul hP (0 : ℂ) (0 : T.V) w

theorem actL_eq (hP : IsPsiFor ε lam T Ψ) {m : ℕ} (a : AS T m) :
    actL T Ψ a = ∑ x, (cD hP (ofW x) (a x) : L2 ε) := by
  have h := toL2_finset_sum_of_memLp (ε := ε) univ
    (fun x : Wd n m => Formalism.REAL.Eword ε (ofW x) (jfun Ψ T.w (a x)))
    (fun x => (eword_smooth hP (a x) (ofW x)).2 [])
  have e : actF T Ψ a = fun g => ∑ x : Wd n m, Formalism.REAL.Eword ε (ofW x) (jfun Ψ T.w (a x)) g := by
    funext g
    exact Finset.sum_apply _ _ _
  unfold actL
  rw [e]
  exact h

theorem ofW_inj {m : ℕ} {x y : Wd n m} (h : ofW x = ofW y) : x = y := by
  obtain ⟨⟨l, hl⟩, w⟩ := x
  obtain ⟨⟨l', hl'⟩, w'⟩ := y
  have hlen : l = l' := by simpa [ofW] using congrArg List.length h
  subst hlen
  have : w = w' := List.ofFn_injective h
  subst this
  rfl

open Classical in

def sgl (m : ℕ) (w : List (Fin n × Fin n)) (v : T.V) : AS T m := fun y => if ofW y = w then v else 0

theorem actL_sgl (hP : IsPsiFor ε lam T Ψ) {m : ℕ} {w : List (Fin n × Fin n)} (h : w.length ≤ m) (v : T.V) :
    actL T Ψ (sgl m w v) = (cD hP w v : L2 ε) := by
  have hx0 : ofW (⟨⟨w.length, Nat.lt_succ_of_le h⟩, w.get⟩ : Wd n m) = w := List.ofFn_get w
  rw [actL_eq hP, Finset.sum_eq_single (⟨⟨w.length, Nat.lt_succ_of_le h⟩, w.get⟩ : Wd n m)]
  · simp only [sgl, hx0, if_true]
  · intro y _ hy
    have hne : ofW y ≠ w := fun e => hy (ofW_inj (e.trans hx0.symm))
    simp only [sgl, if_neg hne, cD_zero]
    rfl
  · intro hn
    exact absurd (Finset.mem_univ _) hn

def actLin (hP : IsPsiFor ε lam T Ψ) (m : ℕ) : AS T m →ₗ[ℂ] L2 ε where
  toFun := actL T Ψ
  map_add' a b := by
    simp only [actL_eq hP, Pi.add_apply, cD_add, Submodule.coe_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [actL_eq hP, Pi.smul_apply, cD_smul, Submodule.coe_smul, Finset.smul_sum, RingHom.id_apply]

theorem actLin_apply (hP : IsPsiFor ε lam T Ψ) {m : ℕ} (a : AS T m) : actLin hP m a = actL T Ψ a := rfl

theorem pad (hP : IsPsiFor ε lam T Ψ) {m m' : ℕ} (h : m ≤ m') (a : AS T m) :
    ∃ a' : AS T m', actL T Ψ a' = actL T Ψ a := by
  refine ⟨∑ x : Wd n m, sgl m' (ofW x) (a x), ?_⟩
  rw [← actLin_apply hP, map_sum, actL_eq hP a]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [actLin_apply, actL_sgl hP]
  have : (ofW x).length = x.1 := by simp [ofW]
  have h2 := x.1.2
  omega

def exS (hP : IsPsiFor ε lam T Ψ) : Submodule ℂ (smD ε (rreg ε)) where
  carrier := {x | ∃ (m : ℕ) (a : AS T m), (x : L2 ε) = actL T Ψ a}
  add_mem' := by
    rintro x y ⟨m, a, ha⟩ ⟨m', b, hb⟩
    obtain ⟨a', ea⟩ := pad hP (le_max_left m m') a
    obtain ⟨b', eb⟩ := pad hP (le_max_right m m') b
    refine ⟨_, a' + b', ?_⟩
    rw [Submodule.coe_add, ha, hb, ← ea, ← eb]
    exact ((actLin hP _).map_add a' b').symm
  zero_mem' := ⟨0, 0, ((actLin hP 0).map_zero).symm⟩
  smul_mem' := by
    rintro c x ⟨m, a, ha⟩
    refine ⟨m, c • a, ?_⟩
    rw [Submodule.coe_smul, ha]
    exact ((actLin hP m).map_smul c a).symm

theorem cD_mem_exS (hP : IsPsiFor ε lam T Ψ) (w : List (Fin n × Fin n)) (v : T.V) : cD hP w v ∈ exS hP :=
  ⟨w.length, sgl _ w v, (actL_sgl hP le_rfl v).symm⟩

theorem eq_sum (hP : IsPsiFor ε lam T Ψ) {x : smD ε (rreg ε)} {m : ℕ} {a : AS T m}
    (h : (x : L2 ε) = actL T Ψ a) : x = ∑ y, cD hP (ofW y) (a y) :=
  Subtype.ext (by rw [h, actL_eq hP, Submodule.coe_sum])

theorem genSub_le_exS (hP : IsPsiFor ε lam T Ψ) :
    genSub (smE ε (rreg ε)) (datumV ε Ψ T.w) ≤ exS hP := by
  refine sInf_le ⟨fun x hx => ?_, fun a b x hx => ?_⟩
  · obtain ⟨v, hv⟩ := (mem_datumV_iff hP T.w x).1 hx
    have : x = cD hP [] v := Subtype.ext hv
    rw [this]
    exact cD_mem_exS hP [] v
  · obtain ⟨m, f, hf⟩ := hx
    rw [eq_sum hP hf, map_sum]
    refine Submodule.sum_mem _ fun y _ => ?_
    have := cD_cons hP (a, b) (ofW y) (f y)
    simp only at this
    rw [← this]
    exact cD_mem_exS hP _ _

theorem cD_mem_genSub (hP : IsPsiFor ε lam T Ψ) (v : T.V) (w : List (Fin n × Fin n)) :
    cD hP w v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w) := by
  refine (Submodule.mem_sInf).2 fun N hN => ?_
  induction w with
  | nil => exact hN.1 ((mem_datumV_iff hP T.w _).2 ⟨v, rfl⟩)
  | cons p w ih =>
    rw [cD_cons]
    exact hN.2 _ _ _ ih

theorem exhaust : Exhaust := by
  intro n ε lam T Ψ hP
  refine ⟨fun x hx => genSub_le_exS hP hx, fun m m' h a => pad hP h a, fun m a => ?_⟩
  refine ⟨∑ x, cD hP (ofW x) (a x),
    Submodule.sum_mem _ fun x _ => cD_mem_genSub hP _ _, ?_⟩
  rw [actL_eq hP]
  simp only [Submodule.subtype_apply, Submodule.coe_sum]

end GlobalTheory.CompanionTheory.WordFam
