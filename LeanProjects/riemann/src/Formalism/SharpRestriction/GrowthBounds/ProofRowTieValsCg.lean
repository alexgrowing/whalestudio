import Formalism.SharpRestriction.GrowthBounds.ProofRowTieValsDef

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VS

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {σ τ : Type} [Finite σ]

def UImg (V : VF C) (A : σ → MvPowerSeries τ C) (Φ : MvPowerSeries τ C) : Prop :=
  ∃ U : MvPowerSeries σ C, IsIU V U ∧ MvPowerSeries.subst A U = Φ

def GImg (V : VF C) (A : σ → MvPowerSeries τ C) (a : Fin dd → MvPowerSeries τ C) : Prop :=
  ∃ P : Fin dd → MvPowerSeries σ C, VP.GoodPt V P ∧ ∀ i, MvPowerSeries.subst A (P i) = a i

def Cg (V : VF C) (A : σ → MvPowerSeries τ C) (f g : MvPowerSeries τ C) : Prop :=
  MvPowerSeries.constantCoeff f = 0 ∧ MvPowerSeries.constantCoeff g = 0 ∧ UImg V A (mvExp (f - g))

variable {A : σ → MvPowerSeries τ C} (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0)

include hA

theorem UImg.one : UImg V A 1 := ⟨1, IsIU.one, VP.subst_one hA⟩

theorem UImg.mul {Φ Ψ : MvPowerSeries τ C} (h : UImg V A Φ) (h' : UImg V A Ψ) : UImg V A (Φ * Ψ) := by
  obtain ⟨U, hU, rfl⟩ := h
  obtain ⟨U', hU', rfl⟩ := h'
  exact ⟨U * U', hU.mul hU', VP.subst_mul hA _ _⟩

theorem UImg.pow {Φ : MvPowerSeries τ C} (h : UImg V A Φ) (k : ℕ) : UImg V A (Φ ^ k) := by
  obtain ⟨U, hU, rfl⟩ := h
  exact ⟨U ^ k, ⟨hU.1.pow k, by rw [map_pow, V.v.map_pow, hU.2, smul_zero]⟩, VP.subst_pow' hA _ _⟩

theorem UImg.exp_neg {f : MvPowerSeries τ C} (hf : MvPowerSeries.constantCoeff f = 0) (h : UImg V A (mvExp f)) :
    UImg V A (mvExp (-f)) := by
  obtain ⟨U, hU, e⟩ := h
  obtain ⟨U', hU'i, hUU⟩ := VP.intInv hU.1 hU.2
  have hU'0 : V.v (MvPowerSeries.constantCoeff U') = 0 := by
    have h1 := congrArg (fun x => V.v (MvPowerSeries.constantCoeff x)) hUU
    simp only [map_mul, map_one, V.v.map_mul, V.v.map_one, hU.2, add_zero] at h1
    exact h1
  refine ⟨U', ⟨hU'i, hU'0⟩, ?_⟩
  have h2 : MvPowerSeries.subst A U' * mvExp f = 1 := by
    rw [← e, ← VP.subst_mul hA, hUU, VP.subst_one hA]
  have h3 : mvExp (-f) * mvExp f = 1 := by
    rw [← VP.exp_add (by rw [map_neg, hf, neg_zero]) hf, neg_add_cancel, rtj_mvExp_zero]
  calc MvPowerSeries.subst A U' = MvPowerSeries.subst A U' * (mvExp (-f) * mvExp f) := by rw [h3, mul_one]
    _ = (MvPowerSeries.subst A U' * mvExp f) * mvExp (-f) := by ring
    _ = mvExp (-f) := by rw [h2, one_mul]

theorem Cg.refl {f : MvPowerSeries τ C} (hf : MvPowerSeries.constantCoeff f = 0) : Cg V A f f :=
  ⟨hf, hf, by rw [sub_self, rtj_mvExp_zero]; exact UImg.one hA⟩

theorem Cg.symm {f g : MvPowerSeries τ C} (h : Cg V A f g) : Cg V A g f :=
  ⟨h.2.1, h.1, by
    have := UImg.exp_neg hA (by rw [map_sub, h.1, h.2.1, sub_zero]) h.2.2
    rwa [neg_sub] at this⟩

theorem Cg.trans {f g k : MvPowerSeries τ C} (h : Cg V A f g) (h' : Cg V A g k) : Cg V A f k :=
  ⟨h.1, h'.2.1, by
    have := UImg.mul hA h.2.2 h'.2.2
    rw [← VP.exp_add (by rw [map_sub, h.1, h.2.1, sub_zero]) (by rw [map_sub, h'.1, h'.2.1, sub_zero])] at this
    rwa [sub_add_sub_cancel] at this⟩

theorem Cg.add {f g f' g' : MvPowerSeries τ C} (h : Cg V A f g) (h' : Cg V A f' g') : Cg V A (f + f') (g + g') :=
  ⟨by rw [map_add, h.1, h'.1, add_zero], by rw [map_add, h.2.1, h'.2.1, add_zero], by
    have := UImg.mul hA h.2.2 h'.2.2
    rw [← VP.exp_add (by rw [map_sub, h.1, h.2.1, sub_zero]) (by rw [map_sub, h'.1, h'.2.1, sub_zero])] at this
    rwa [show f - g + (f' - g') = f + f' - (g + g') by ring] at this⟩

theorem Cg.sum {ι : Type} (s : Finset ι) {f g : ι → MvPowerSeries τ C} (h : ∀ i ∈ s, Cg V A (f i) (g i)) :
    Cg V A (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (Cg.refl hA (map_zero _) : Cg V A (0 : MvPowerSeries τ C) 0)
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact Cg.add hA (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Cg.nsmul {f g : MvPowerSeries τ C} (h : Cg V A f g) (k : ℕ) : Cg V A ((k : C) • f) ((k : C) • g) :=
  ⟨VP.cc_smul _ h.1, VP.cc_smul _ h.2.1, by
    rw [← smul_sub, VP.exp_nsmul (by rw [map_sub, h.1, h.2.1, sub_zero])]
    exact UImg.pow hA h.2.2 k⟩

theorem Cg.unit {f g : MvPowerSeries τ C} (h : Cg V A f g) :
    ∃ U : MvPowerSeries σ C, IsIU V U ∧ mvExp f = MvPowerSeries.subst A U * mvExp g := by
  obtain ⟨U, hU, e⟩ := h.2.2
  refine ⟨U, hU, ?_⟩
  rw [e, ← VP.exp_add (by rw [map_sub, h.1, h.2.1, sub_zero]) h.2.1, sub_add_cancel]

theorem cg_of {F G : MvPowerSeries σ C} (hF : MvPowerSeries.constantCoeff F = 0)
    (hG : MvPowerSeries.constantCoeff G = 0) (hi : IntS V (mvExp (F - G))) :
    Cg V A (MvPowerSeries.subst A F) (MvPowerSeries.subst A G) :=
  ⟨VP.cc_subst hA hF, VP.cc_subst hA hG, mvExp (F - G), VP.isIU_of_exp hi rfl, by
    rw [VP.subst_exp hA (by rw [map_sub, hF, hG, sub_zero]), VP.subst_sub' hA]⟩

theorem GImg.cc {a : Fin dd → MvPowerSeries τ C} (h : GImg V A a) (i : Fin dd) :
    MvPowerSeries.constantCoeff (a i) = 0 := by
  obtain ⟨P, hP, e⟩ := h
  rw [← e i]
  exact VP.cc_subst hA (hP.1 i)

theorem GImg.zero : GImg V A (fun _ : Fin dd => (0 : MvPowerSeries τ C)) :=
  ⟨fun _ => 0, VP.GoodPt.zero, fun _ => VP.subst_zero' hA⟩

variable (Y : FBChart C V O dd)

theorem GImg.add {a b : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) (hb : GImg V A b) :
    GImg V A (VP.addAt Y a b) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain ⟨Q, hQ, e'⟩ := hb
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  obtain rfl : (fun i => MvPowerSeries.subst A (Q i)) = b := funext e'
  exact ⟨VP.addAt Y P Q, hP.add Y hQ, fun i => VP.addAt_subst Y hA hP.1 hQ.1 i⟩

theorem GImg.act (x : O) {a : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) : GImg V A (VP.actAt Y x a) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  exact ⟨VP.actAt Y x P, hP.act Y x, fun i => VP.actAt_subst Y hA hP.1 x i⟩

omit Y in
theorem GImg.map {Y : FBChart C V O dd} {φ : Pt C 1 dd} (hφ : IsEndo Y φ) {a : Fin dd → MvPowerSeries τ C}
    (ha : GImg V A a) : GImg V A (VP.mapAt φ a) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  exact ⟨VP.mapAt φ P, ⟨VP.cc_mapAt hφ.cc hP.1, fun i =>
    IntS.subst (a := fun q : Fin 1 × Fin dd => P q.2) (fun q => hP.1 q.2) (fun q => hP.2 q.2) (hφ.int i)⟩,
    fun i => VP.mapAt_subst hA φ hP.1 i⟩

theorem gauge_congr_additive_left {a b c : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) (hb : GImg V A b) (hc : GImg V A c) :
    Cg V A (VP.hAt Y (VP.addAt Y a b) c) (VP.hAt Y a c + VP.hAt Y b c) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain ⟨Q, hQ, e'⟩ := hb
  obtain ⟨R, hR, e''⟩ := hc
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  obtain rfl : (fun i => MvPowerSeries.subst A (Q i)) = b := funext e'
  obtain rfl : (fun i => MvPowerSeries.subst A (R i)) = c := funext e''
  have c1 := VP.cc_hAt Y hP.1 hR.1
  have c2 := VP.cc_hAt Y hQ.1 hR.1
  have c3 := VP.cc_hAt Y (VP.cc_addAt Y hP.1 hQ.1) hR.1
  have h := cg_of (V := V) hA (F := VP.hAt Y P R + VP.hAt Y Q R) (G := VP.hAt Y (VP.addAt Y P Q) R)
    (by rw [map_add, c1, c2, add_zero]) c3 (by
      rw [← VP.first_partial_law_at_points Y hP.1 hQ.1 hR.1]
      exact IntS.subst (VP.constantCoeff_triple_substitution hP.1 hQ.1 hR.1) (VP.integral_triple_substitution hP.2 hQ.2 hR.2) Y.intPh1)
  rw [VP.subst_add' hA, VP.hAt_subst Y hA hP.1 hR.1, VP.hAt_subst Y hA hQ.1 hR.1,
    VP.hAt_subst Y hA (VP.cc_addAt Y hP.1 hQ.1) hR.1, funext (VP.addAt_subst Y hA hP.1 hQ.1)] at h
  exact Cg.symm hA h

theorem gauge_congr_additive_right {a b c : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) (hb : GImg V A b) (hc : GImg V A c) :
    Cg V A (VP.hAt Y a (VP.addAt Y b c)) (VP.hAt Y a b + VP.hAt Y a c) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain ⟨Q, hQ, e'⟩ := hb
  obtain ⟨R, hR, e''⟩ := hc
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  obtain rfl : (fun i => MvPowerSeries.subst A (Q i)) = b := funext e'
  obtain rfl : (fun i => MvPowerSeries.subst A (R i)) = c := funext e''
  have c1 := VP.cc_hAt Y hP.1 hQ.1
  have c2 := VP.cc_hAt Y hP.1 hR.1
  have c3 := VP.cc_hAt Y hP.1 (VP.cc_addAt Y hQ.1 hR.1)
  have h := cg_of (V := V) hA (F := VP.hAt Y P Q + VP.hAt Y P R) (G := VP.hAt Y P (VP.addAt Y Q R))
    (by rw [map_add, c1, c2, add_zero]) c3 (by
      rw [← VP.second_partial_law_at_points Y hP.1 hQ.1 hR.1]
      exact IntS.subst (VP.constantCoeff_triple_substitution hP.1 hQ.1 hR.1) (VP.integral_triple_substitution hP.2 hQ.2 hR.2) Y.intPh2)
  rw [VP.subst_add' hA, VP.hAt_subst Y hA hP.1 hQ.1, VP.hAt_subst Y hA hP.1 hR.1,
    VP.hAt_subst Y hA hP.1 (VP.cc_addAt Y hQ.1 hR.1), funext (VP.addAt_subst Y hA hQ.1 hR.1)] at h
  exact Cg.symm hA h

theorem cg_sy {a b : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) (hb : GImg V A b) :
    Cg V A (VP.hAt Y b a) (VP.hAt Y a b) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain ⟨Q, hQ, e'⟩ := hb
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  obtain rfl : (fun i => MvPowerSeries.subst A (Q i)) = b := funext e'
  have h := cg_of (V := V) hA (F := VP.hAt Y Q P) (G := VP.hAt Y P Q) (VP.cc_hAt Y hQ.1 hP.1) (VP.cc_hAt Y hP.1 hQ.1) (by
      rw [← VP.sy_at Y hP.1 hQ.1]
      exact IntS.subst (VP.constantCoeff_pair_substitution hP.1 hQ.1) (VP.integral_pair_substitution hP.2 hQ.2) Y.intSy)
  rwa [VP.hAt_subst Y hA hQ.1 hP.1, VP.hAt_subst Y hA hP.1 hQ.1] at h

theorem cg_ad (x : O) {a b : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) (hb : GImg V A b) :
    Cg V A (VP.hAt Y (VP.actAt Y x a) b) (VP.hAt Y a (VP.actAt Y (star x) b)) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain ⟨Q, hQ, e'⟩ := hb
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  obtain rfl : (fun i => MvPowerSeries.subst A (Q i)) = b := funext e'
  have h := cg_of (V := V) hA (F := VP.hAt Y (VP.actAt Y x P) Q) (G := VP.hAt Y P (VP.actAt Y (star x) Q))
    (VP.cc_hAt Y (VP.cc_actAt Y x hP.1) hQ.1) (VP.cc_hAt Y hP.1 (VP.cc_actAt Y _ hQ.1)) (by
      rw [← VP.ad_at Y hP.1 hQ.1]
      exact IntS.subst (VP.constantCoeff_pair_substitution hP.1 hQ.1) (VP.integral_pair_substitution hP.2 hQ.2) (Y.intAd x))
  rwa [VP.hAt_subst Y hA (VP.cc_actAt Y x hP.1) hQ.1, VP.hAt_subst Y hA hP.1 (VP.cc_actAt Y _ hQ.1),
    funext (VP.actAt_subst Y hA hP.1 x), funext (VP.actAt_subst Y hA hQ.1 (star x))] at h

theorem cg_adj {φ φ' : Pt C 1 dd} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφ' : ∀ i, MvPowerSeries.constantCoeff (φ' i) = 0)
    (hadj : IntS V (FB.expS C (ev (n := 2) ![comp1 φ (pt C dd 0), pt C dd 1] Y.h -
      ev (n := 2) ![pt C dd 0, comp1 φ' (pt C dd 1)] Y.h)))
    {a b : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) (hb : GImg V A b) :
    Cg V A (VP.hAt Y (VP.mapAt φ a) b) (VP.hAt Y a (VP.mapAt φ' b)) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain ⟨Q, hQ, e'⟩ := hb
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  obtain rfl : (fun i => MvPowerSeries.subst A (Q i)) = b := funext e'
  have h := cg_of (V := V) hA (F := VP.hAt Y (VP.mapAt φ P) Q) (G := VP.hAt Y P (VP.mapAt φ' Q))
    (VP.cc_hAt Y (VP.cc_mapAt hφ hP.1) hQ.1) (VP.cc_hAt Y hP.1 (VP.cc_mapAt hφ' hQ.1)) (by
      rw [← VP.cmp_at Y hφ hφ' hP.1 hQ.1]
      exact IntS.subst (VP.constantCoeff_pair_substitution hP.1 hQ.1) (VP.integral_pair_substitution hP.2 hQ.2) hadj)
  rwa [VP.hAt_subst Y hA (VP.cc_mapAt hφ hP.1) hQ.1, VP.hAt_subst Y hA hP.1 (VP.cc_mapAt hφ' hQ.1),
    funext (VP.mapAt_subst hA φ hP.1), funext (VP.mapAt_subst hA φ' hQ.1)] at h

end VS

end Formalism.L2.FormalSeriesBounds
