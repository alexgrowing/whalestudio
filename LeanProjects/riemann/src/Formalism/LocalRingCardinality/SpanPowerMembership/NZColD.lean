import Formalism.LocalRingCardinality.Lemmas
import Formalism.LocalRingCardinality.SpanPowerMembership.NZColB

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.MainNotions.G Classical

section Gen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]

def locS (w : HeightOneSpectrum (𝓞 K)) (B : Submodule (𝓞 K) V) : Submodule (𝓞 K) V where
  carrier := {x | InLoc w B x}
  add_mem' := by
    rintro a b ⟨s, hs, h1⟩ ⟨t, ht, h2⟩
    refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, ?_⟩
    rw [smul_add]
    refine B.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact B.smul_mem _ h1
    · rw [mul_smul]; exact B.smul_mem _ h2
  zero_mem' := ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  smul_mem' := by
    rintro r a ⟨s, hs, h1⟩
    exact ⟨s, hs, by rw [smul_comm]; exact B.smul_mem r h1⟩

theorem mem_locS (w : HeightOneSpectrum (𝓞 K)) (B : Submodule (𝓞 K) V) (x : V) : x ∈ locS w B ↔ InLoc w B x := Iff.rfl

theorem locS_sat (w : HeightOneSpectrum (𝓞 K)) (B : Submodule (𝓞 K) V) (s : 𝓞 K) (hs : s ∉ w.asIdeal) (x : V)
    (h : s • x ∈ locS w B) : x ∈ locS w B := by
  obtain ⟨t, ht, h1⟩ := h
  exact ⟨t * s, fun h => (w.isPrime.mem_or_mem h).elim ht hs, by rwa [mul_smul]⟩

theorem exists_pow_val (v : HeightOneSpectrum (𝓞 K)) (b : 𝓞 K) (hb : b ≠ 0) :
    ∃ m : ℕ, ∀ a ∈ v.asIdeal ^ m, v.valuation K (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) ≤ 1 := by
  refine ⟨(Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {b} : Ideal (𝓞 K))).factors, fun a ha => ?_⟩
  rw [map_div₀, v.valuation_of_algebraMap, v.valuation_of_algebraMap]
  have h0 : 0 < v.intValuation b := by
    rw [v.intValuation_if_neg hb]; exact WithZero.exp_pos
  rw [div_le_one₀ h0, v.intValuation_if_neg hb]
  exact (v.intValuation_le_pow_iff_mem a _).mpr ha

theorem finite_over (t : 𝓞 K) (ht : t ≠ 0) : {v : HeightOneSpectrum (𝓞 K) | t ∈ v.asIdeal}.Finite := by
  have h : Ideal.span {t} ≠ 0 := by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ht
  exact (Ideal.finite_factors h).subset fun v hv => Ideal.dvd_span_singleton.mpr hv

variable [Module K V] [IsScalarTower (𝓞 K) K V]

theorem smul_eq_div (a b : 𝓞 K) (hb : b ≠ 0) (x : V) :
    a • x = (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) • (b • x) := by
  have hbK : algebraMap (𝓞 K) K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hb
  rw [← algebraMap_smul K b, smul_smul, div_mul_cancel₀ _ hbK, algebraMap_smul]

end Gen

variable {D : D7} (c : LatCmp D)

structure NuData (c : LatCmp D) where
  S : ℕ → Prop
  S_fin : {p | S p}.Finite
  NPf : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    Submodule (D.gat u w hg).O (D.gat u w hg).Fn

  exists_residueChar_pow_smul_mem : ∀ u w hg, ∃ N : ℕ, ∀ y ∈ DV.MramL D u,
    ((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^ N • c.cmpN u w hg y ∈ NPf u w hg

  T_abs : ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T → ∀ x : (D.div.Nu u).V,
    ∃ m : ℕ, ∀ a ∈ (D.plEq w).asIdeal ^ m, D.nuIn u (a • x) ∈ LT.Nlam D u w

variable {c} (N : NuData c)

theorem int_mem_intW (w : D.what₂.places.Pl) (r : 𝓞 D.what₂.LL) : (r : D.what₂.LL) ∈ intW D.what₂.places w :=
  (D.val_nonneg_iff w _).2 ((D.plEq w).valuation_le_one r)

def atT (u : D.what₂.Word) (w : D.what₂.places.Pl) : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V where
  carrier := {x | D.nuIn u x ∈ LT.Nlam D u w}
  add_mem' := by
    intro a b ha hb
    show D.nuIn u (a + b) ∈ LT.Nlam D u w
    rw [map_add]; exact Submodule.add_mem _ ha hb
  zero_mem' := by
    show D.nuIn u 0 ∈ LT.Nlam D u w
    rw [map_zero]; exact Submodule.zero_mem _
  smul_mem' := by
    intro r a ha
    show D.nuIn u (r • a) ∈ LT.Nlam D u w
    rw [← algebraMap_smul D.what₂.LL r a, map_smul]
    exact (LT.Nlam D u w).smul_mem (⟨_, int_mem_intW w r⟩ : intW D.what₂.places w) ha

include N in

def srv (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V where
  carrier := {x | c.cmpN u w hg x ∈ N.NPf u w hg}
  add_mem' := by
    intro a b ha hb
    show c.cmpN u w hg (a + b) ∈ N.NPf u w hg
    rw [map_add]; exact Submodule.add_mem _ ha hb
  zero_mem' := by
    show c.cmpN u w hg 0 ∈ N.NPf u w hg
    rw [map_zero]; exact Submodule.zero_mem _
  smul_mem' := by
    intro r a ha
    show c.cmpN u w hg (r • a) ∈ N.NPf u w hg
    obtain ⟨o, ho⟩ := (c.embW_val u w hg _).1 ((D.plEq w).valuation_le_one r)
    rw [← algebraMap_smul D.what₂.LL r a, c.cmpN_smul, ← ho, algebraMap_smul]
    exact Submodule.smul_mem _ o ha

def cond (u : D.what₂.Word) (w : D.what₂.places.Pl) : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V :=
  if D.what₂.places.resChar w = (D.mem u).A.T then atT u w
  else if h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) ∧ N.S (D.what₂.places.resChar w) then srv N u w h.1
  else locS (D.plEq w) (DV.MramL D u)

def nuLat (u : D.what₂.Word) : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V :=
  glue fun v => cond N u (D.plEq.symm v)

theorem inv_mem_intW (w : D.what₂.places.Pl) (s : 𝓞 D.what₂.LL) (hs : s ∉ (D.plEq w).asIdeal) :
    (algebraMap (𝓞 D.what₂.LL) D.what₂.LL s)⁻¹ ∈ intW D.what₂.places w ∧ algebraMap (𝓞 D.what₂.LL) D.what₂.LL s ≠ 0 := by
  have hv : (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL s) = 1 :=
    ((D.plEq w).valuation_eq_one_iff_notMem).2 hs
  have hs0 : algebraMap (𝓞 D.what₂.LL) D.what₂.LL s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  exact ⟨(D.val_nonneg_iff w _).2 (by rw [map_inv₀, hv, inv_one]), hs0⟩

theorem cond_sat (u : D.what₂.Word) (w : D.what₂.places.Pl) (s : 𝓞 D.what₂.LL) (hs : s ∉ (D.plEq w).asIdeal)
    (x : (D.div.Nu u).V) (h : s • x ∈ cond N u w) : x ∈ cond N u w := by
  obtain ⟨hinv, hs0⟩ := inv_mem_intW w s hs
  have hx : x = (algebraMap (𝓞 D.what₂.LL) D.what₂.LL s)⁻¹ • (s • x) := by
    rw [← algebraMap_smul D.what₂.LL s, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  unfold cond at h ⊢
  split_ifs at h ⊢ with h1 h2
  · show D.nuIn u x ∈ LT.Nlam D u w
    rw [hx, map_smul]
    exact (LT.Nlam D u w).smul_mem (⟨_, hinv⟩ : intW D.what₂.places w) h
  · show c.cmpN u w h2.1 x ∈ N.NPf u w h2.1
    obtain ⟨o, ho⟩ := (c.embW_val u w h2.1 _).1 ((D.val_nonneg_iff w _).1 hinv)
    rw [hx, c.cmpN_smul, ← ho, algebraMap_smul]
    exact Submodule.smul_mem _ o h
  · exact locS_sat _ _ s hs x h

theorem resChar_mem (w : D.what₂.places.Pl) : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  rw [← (D.plEq w).valuation_lt_one_iff_mem (K := D.what₂.LL), D.val_resChar' w, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  have := D.what₂.places.ramIdx_pos w
  omega

variable (hspan : ∀ u, Submodule.span D.what₂.LL (DV.MramL D u : Set (D.div.Nu u).V) = ⊤)

theorem locLe_zero_iff {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) : DV.LocLe w 0 A B ↔ ∀ x ∈ A, InLoc w B x := by
  unfold DV.LocLe InLoc
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]

theorem inLoc_of_mem {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (A : Submodule (𝓞 K) V) {x : V} (h : x ∈ A) : InLoc w A x :=
  ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by rwa [one_smul]⟩

end Formalism.BasicNotions.Examples₂.NZ
