import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.ConjugateLevelLeMaximalCompact

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem index_pi_dep {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, Group (β i)]
    (C : ∀ i, Subgroup (β i)) : (Subgroup.pi Set.univ C).index = ∏ i, (C i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

theorem index_comap_pi {A : Type*} [Group A] {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, Group (β i)]
    (φ : A →* ((i : ι) → β i)) (hφ : Function.Surjective φ) (C : ∀ i, Subgroup (β i)) :
    ((Subgroup.pi Set.univ C).comap φ).index = ∏ i, (C i).index := by
  rw [Subgroup.index_comap_of_surjective _ hφ, index_pi_dep]

theorem closure_val_preimage {G : Type*} [Group G] (H T : Subgroup G) :
    Subgroup.closure (Subtype.val ⁻¹' (T : Set G) : Set H) = T.subgroupOf H :=
  Subgroup.closure_eq (T.subgroupOf H)

def CompH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.F))
    (h : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J), h ∈ Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w) →
    haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h ∈ Hsub (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (frameOf X w)

def CompK : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.F))
    (h : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J),
    h ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) →
    haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h ∈
      Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v

def ConjugateLevelIsSubgroup : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → ∀ w : D.what₂.Word,
    (1 : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ K2u X hb w ∧
    (∀ x ∈ K2u X hb w, ∀ y ∈ K2u X hb w, x * y ∈ K2u X hb w) ∧ (∀ x ∈ K2u X hb w, x⁻¹ ∈ K2u X hb w)

def SurjKH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word)
    (t : ∀ p : TypX X, HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J),
    (∀ p, t p ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) →
    (∀ p, t p ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1) →
    ∃ h ∈ Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w),
      h ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ∧
      ∀ p, haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) h = t p

def ConjugateLevelLocalCongruence : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.LevelSubgroupNormalized → ∀ (w : D.what₂.Word)
    (h : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J), h ∈ Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w) →
    h ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) →
    (∀ p : TypX X, haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) h ∈
      compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1) → h ∈ K2u X hb w

section Der

variable {D : D7} (X : HidaSetting D)

def KvS (v : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.F)) : Subgroup (HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) where
  carrier := Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v
  one_mem' := Subgroup.one_mem (Kloc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))
  mul_mem' := fun {_ _} ha hb => Subgroup.mul_mem (Kloc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) ha hb
  inv_mem' := fun {_} ha => Subgroup.inv_mem (Kloc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) ha

def concreteLevelAdelicSubset (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (hg : ConjugateLevelIsSubgroup) (w : D.what₂.Word) :
    Subgroup (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) where
  carrier := K2u X hb w
  one_mem' := (hg X hb hK w).1
  mul_mem' := fun {a b} ha hb' => (hg X hb hK w).2.1 a ha b hb'
  inv_mem' := fun {a} ha => (hg X hb hK w).2.2 a ha

def compHom (ha : CompH) (hk : CompK) (w : D.what₂.Word) :
    ↥((Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).subgroupOf
        (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) →*
      ((p : TypX X) → ↥((KvS X p.1).subgroupOf (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)))) where
  toFun x := fun p => ⟨⟨haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) x.1.1, ha X w p.1 x.1.1 x.1.2⟩,
    hk X p.1 x.1.1 (Subgroup.mem_subgroupOf.1 x.2)⟩
  map_one' := by
    funext p
    apply Subtype.ext; apply Subtype.ext
    exact map_one _
  map_mul' := by
    intro x y
    funext p
    apply Subtype.ext; apply Subtype.ext
    exact map_mul _ _ _

end Der

theorem globProd_of (ha : CompH) (hk : CompK) (hg : ConjugateLevelIsSubgroup) (hs : SurjKH) (hp : ConjugateLevelLocalCongruence) : GlobProd := by
  intro D X hb hK hT hL w
  classical
  have e1 : idxH X hb w = (((concreteLevelAdelicSubset X hb hK hg w).subgroupOf (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))).subgroupOf
      ((Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).subgroupOf
        (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)))).index := by
    unfold idxH
    rw [show (Subtype.val ⁻¹' K2u X hb w : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      Subtype.val ⁻¹' ((concreteLevelAdelicSubset X hb hK hg w : Subgroup _) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) from rfl,
      closure_val_preimage, closure_val_preimage]
    rfl
  have e2 : ∀ p : TypX X, idxHp X hb w p =
      ((((concreteLevelAdelicSubset X hb hK hg w).map (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1))).subgroupOf
        (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))).subgroupOf
        ((KvS X p.1).subgroupOf (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)))).index := by
    intro p
    unfold idxHp
    rw [show (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 :
        Set ↥(Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      Subtype.val ⁻¹' ((((concreteLevelAdelicSubset X hb hK hg w).map (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1))) :
        Subgroup _) : Set (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J)) from by
          rw [Subgroup.coe_map]; rfl,
      show (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 :
        Set ↥(Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      Subtype.val ⁻¹' ((KvS X p.1 : Subgroup _) : Set (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J)) from rfl,
      closure_val_preimage, closure_val_preimage]
    rfl
  rw [e1, Finset.prod_congr rfl (fun p _ => e2 p), ← index_comap_pi (compHom X ha hk w)]
  · congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hx p
      exact ⟨x.1.1, hx, rfl⟩
    · intro hx
      exact hp X hb hK hL w x.1.1 x.1.2 (Subgroup.mem_subgroupOf.1 x.2) (fun p => hx p)
  · intro y
    obtain ⟨h, hH, hKf, hh⟩ := hs X w (fun p => (y p).1.1) (fun p => (y p).1.2) (fun p => (y p).2)
    refine ⟨⟨⟨h, hH⟩, Subgroup.mem_subgroupOf.2 hKf⟩, ?_⟩
    funext p
    apply Subtype.ext; apply Subtype.ext
    exact hh p

end MassDataLevelSSteps
