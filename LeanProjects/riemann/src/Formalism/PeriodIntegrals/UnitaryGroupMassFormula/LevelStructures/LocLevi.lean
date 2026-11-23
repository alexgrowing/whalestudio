import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.ConjugateLevelLeMaximalCompact

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem relIndex_eq_of_le_of_dec {G : Type*} [Group G] (U A B : Subgroup G) (hBA : B ≤ A)
    (hdec : ∀ a ∈ A, ∃ u ∈ U, ∃ b ∈ B, a = u * b) : U.relIndex A = U.relIndex B := by
  unfold Subgroup.relIndex
  rw [Subgroup.index, Subgroup.index]
  symm
  refine Nat.card_congr (Equiv.ofBijective (Quotient.map' (Subgroup.inclusion hBA) ?_) ⟨?_, ?_⟩)
  · intro x y h
    rw [QuotientGroup.leftRel_apply] at h ⊢
    simpa [Subgroup.mem_subgroupOf] using h
  · intro p q h
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have h' : (QuotientGroup.mk (Subgroup.inclusion hBA x) : A ⧸ U.subgroupOf A) =
        QuotientGroup.mk (Subgroup.inclusion hBA y) := h
    rw [QuotientGroup.eq] at h' ⊢
    simpa [Subgroup.mem_subgroupOf] using h'
  · intro p
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨u, hu, b, hb, hab⟩ := hdec (a : G)⁻¹ (A.inv_mem a.2)
    refine ⟨QuotientGroup.mk ⟨b⁻¹, B.inv_mem hb⟩, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion hBA ⟨b⁻¹, B.inv_mem hb⟩) : A ⧸ U.subgroupOf A) = QuotientGroup.mk a
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have ha : (a : G) = b⁻¹ * u⁻¹ := by rw [← mul_inv_rev, ← hab, inv_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, inv_inv]
    rw [ha, ← mul_assoc, mul_inv_cancel, one_mul]
    exact U.inv_mem hu

theorem closure_val_preimage_eq_subgroupOf {G : Type*} [Group G] (S V : Subgroup G) :
    Subgroup.closure (Subtype.val ⁻¹' (V : Set G) : Set S) = V.subgroupOf S := by
  rw [show (Subtype.val ⁻¹' (V : Set G) : Set S) = (V.subgroupOf S : Set S) from
    (Subgroup.coe_subgroupOf V S).symm, Subgroup.closure_eq]

theorem relIndex_traces {G : Type*} [Group G] (S U K : Subgroup G) :
    (Subgroup.closure (Subtype.val ⁻¹' (U : Set G) : Set S)).relIndex
      (Subgroup.closure (Subtype.val ⁻¹' (K : Set G) : Set S)) = U.relIndex (K ⊓ S) := by
  rw [closure_val_preimage_eq_subgroupOf, closure_val_preimage_eq_subgroupOf, ← Subgroup.inf_subgroupOf_right K S,
    Subgroup.relIndex_subgroupOf inf_le_right]

theorem Hsub_le_Ssub {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (P : Frame E n r) :
    Hsub R σ J P ≤ Ssub R σ J P := by
  intro g hg
  rw [Hsub, mem_stabT] at hg
  show UniC R σ J (F0 P) g
  intro b
  have h := hg (Fin.castAdd r b)
  simp only [tupH, Fin.append_left] at h
  rw [h, sub_self]
  exact Submodule.zero_mem _

variable {D : D7}

def KvSubT (X : HidaSetting D) (p : TypX X) : Subgroup (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) where
  carrier := Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1
  one_mem' := (Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).one_mem
  mul_mem' := fun ha hb => (Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).mul_mem ha hb
  inv_mem' := fun ha => (Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).inv_mem ha

theorem finiteAdelic_map_mul (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (x y : X.B.I.Gf) :
    finHA X hb (x * y) = finHA X hb x * finHA X hb y := by
  unfold finHA
  rw [show ((1 : _), x * y) = ((1, x) * (1, y) : X.B.I.GA) from by simp, map_mul, map_mul, Prod.snd_mul]

theorem finiteAdelic_map_inv (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (x : X.B.I.Gf) :
    finHA X hb x⁻¹ = (finHA X hb x)⁻¹ := by
  unfold finHA
  rw [show ((1 : _), x⁻¹) = ((1, x)⁻¹ : X.B.I.GA) from by simp, map_inv, map_inv, Prod.snd_inv]

theorem finiteAdelic_map_one (X : HidaSetting D) (hb : AdBridgeIso X.B.I) : finHA X hb 1 = 1 := by
  unfold finHA
  rw [show ((1 : _), (1 : X.B.I.Gf)) = (1 : X.B.I.GA) from rfl, map_one, map_one, Prod.snd_one]

theorem mem_local_component_iff (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (w : D.what₂.Word) (p : TypX X)
    (z : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) :
    z ∈ compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 ↔
      ∃ k ∈ X.K2, haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1)
        (finHA X hb (X.xu w) * finHA X hb k * (finHA X hb (X.xu w))⁻¹) = z := by
  simp only [compSet, K2u, levelUnitary, Set.mem_image]
  constructor
  · rintro ⟨y, ⟨y', ⟨k, hk, rfl⟩, rfl⟩, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨_, ⟨k, hk, rfl⟩, rfl⟩, rfl⟩

def conjugateLevelLocalSubgroup (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (w : D.what₂.Word) (p : TypX X) :
    Subgroup (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) where
  carrier := compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1
  one_mem' := by
    refine (mem_local_component_iff X hb w p _).2 ⟨1, hK.1, ?_⟩
    rw [finiteAdelic_map_one, mul_one, mul_inv_cancel, map_one]
  mul_mem' := by
    intro a b ha hb'
    obtain ⟨k1, hk1, e1⟩ := (mem_local_component_iff X hb w p _).1 ha
    obtain ⟨k2, hk2, e2⟩ := (mem_local_component_iff X hb w p _).1 hb'
    refine (mem_local_component_iff X hb w p _).2 ⟨k1 * k2, hK.2.1 _ hk1 _ hk2, ?_⟩
    rw [← e1, ← e2, ← map_mul, finiteAdelic_map_mul]
    congr 1
    group
  inv_mem' := by
    intro a ha
    obtain ⟨k1, hk1, e1⟩ := (mem_local_component_iff X hb w p _).1 ha
    refine (mem_local_component_iff X hb w p _).2 ⟨k1⁻¹, hK.2.2.1 _ hk1, ?_⟩
    rw [← e1, ← map_inv, finiteAdelic_map_inv]
    congr 1
    group

def LeviRat : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word) (p : TypX X) (s : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J),
    s ∈ Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) →
    ∃ n h, n ∈ Nsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) ∧
      h ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) ∧ s = n * h

def LeviIntH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word) (p : TypX X) (n h : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J),
    n ∈ Nsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) →
    h ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) →
    n * h ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 →
    h ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1

def UnipotentIntegralInLevel : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb → X.LevelSubgroupNormalized →
    ∀ (w : D.what₂.Word) (p : TypX X) (n : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J),
      n ∈ Nsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) →
      n ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 →
      n ∈ compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1

theorem locLevi_of (ha : LeviRat) (hbI : LeviIntH) (hc : UnipotentIntegralInLevel) : LocLevi := by
  intro D X hb hK hM hL w p
  have e1 : idxS X hb w p = (conjugateLevelLocalSubgroup X hb hK w p).relIndex
      (KvSubT X p ⊓ Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) := by
    unfold idxS
    exact relIndex_traces _ (conjugateLevelLocalSubgroup X hb hK w p) (KvSubT X p)
  have e2 : idxHp X hb w p = (conjugateLevelLocalSubgroup X hb hK w p).relIndex
      (KvSubT X p ⊓ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) := by
    unfold idxHp
    exact relIndex_traces _ (conjugateLevelLocalSubgroup X hb hK w p) (KvSubT X p)
  rw [e1, e2]
  apply relIndex_eq_of_le_of_dec
  · exact inf_le_inf_left _ (Hsub_le_Ssub _ _ _ _)
  · rintro a ⟨haK, haS⟩
    obtain ⟨n, h, hn, hh, rfl⟩ := ha X w p a haS
    have hhK := hbI X w p n h hn hh haK
    have hnK : n ∈ KvSubT X p := by
      have e : n = (n * h) * h⁻¹ := by group
      rw [e]
      exact (KvSubT X p).mul_mem haK ((KvSubT X p).inv_mem hhK)
    exact ⟨n, hc X hb hK hM hL w p n hn hnK, h, ⟨hhK, hh⟩, rfl⟩

end MassDataLevelSSteps
