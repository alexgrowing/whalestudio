import Formalism.LocalToGlobal.NumberFieldFamilies.NPartCNdTie
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Module Module.End Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace Formalism.L2.Fam.NPC

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

section Gen

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂)

def HeckeStd0 : Prop := ∀ j w, 1 ≤ j → j ≤ R.m →
  (∀ v k v' k', GenAt0 H (what₂.places.resChar w) (B.Qw w) v k → GenAt0 H (what₂.places.resChar w) (B.Qw w) v' k' →
    Commute (B.hK j w v k) (B.hK j w v' k')) ∧
  (∀ v k, GenAt0 H (what₂.places.resChar w) (B.Qw w) v k → ∀ μ, (B.hK j w v k).maxGenEigenspace μ ≠ ⊥ →
    μ ∈ (algebraMap (B.Oc j w) (FractionRing (B.Oc j w))).range)

def FinDimV : Prop := ∀ j w, FiniteDimensional (FractionRing (B.Oc j w)) (B.V j w)

variable {B}

theorem std_comm (hs : HeckeStd0 B) {j : ℕ} {w : what₂.places.Pl} (h1 : 1 ≤ j) (h2 : j ≤ R.m) :
    ∀ a ∈ {f | ∃ v k, GenAt0 H (what₂.places.resChar w) (B.Qw w) v k ∧ f = B.hK j w v k},
      ∀ b ∈ {f | ∃ v k, GenAt0 H (what₂.places.resChar w) (B.Qw w) v k ∧ f = B.hK j w v k}, Commute a b := by
  rintro a ⟨v, k, hvk, rfl⟩ b ⟨v', k', hvk', rfl⟩
  exact (hs j w h1 h2).1 v k v' k' hvk hvk'

theorem std_split {j : ℕ} {w : what₂.places.Pl} :
    ∀ a ∈ {f | ∃ v k, GenAt0 H (what₂.places.resChar w) (B.Qw w) v k ∧ f = B.hK j w v k}, ⨆ μ, a.maxGenEigenspace μ = ⊤ := by
  rintro a ⟨v, k, hvk, rfl⟩
  exact B.split j w v k hvk

theorem std_int (hs : HeckeStd0 B) {j : ℕ} {w : what₂.places.Pl} (h1 : 1 ≤ j) (h2 : j ≤ R.m) :
    ∀ a ∈ {f | ∃ v k, GenAt0 H (what₂.places.resChar w) (B.Qw w) v k ∧ f = B.hK j w v k}, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ →
      μ ∈ (algebraMap (B.Oc j w) (FractionRing (B.Oc j w))).range := by
  rintro a ⟨v, k, hvk, rfl⟩
  exact (hs j w h1 h2).2 v k hvk

theorem partCompl_of (hs : HeckeStd0 B) (hd : FinDimV B) : PartCompl B := fun i => by
  have := hd (jOf B i) (wOf B i)
  exact NCov.isCompl_part_off (IsFractionRing.injective _ _) (std_comm (w := wOf B i) hs i.2.2.2.1 i.2.2.2.2.1) std_split
    (std_int hs i.2.2.2.1 i.2.2.2.2.1) _

theorem xNe_of (hs : HeckeStd0 B) (hd : FinDimV B) (i : LocT B) : Nonempty (XOf B i) := by
  have := hd (jOf B i) (wOf B i)
  obtain ⟨ψ, hW, hc⟩ := NCov.exists_pt_of_isMaximal (IsFractionRing.injective _ _) (std_comm (w := wOf B i) hs i.2.2.2.1 i.2.2.2.2.1)
    (std_split (j := jOf B i) (w := wOf B i)) (std_int (w := wOf B i) hs i.2.2.2.1 i.2.2.2.2.1) i.2.1 i.2.2.1
  exact ⟨⟨ψ, hc, hW⟩⟩

theorem xFin_of (hs : HeckeStd0 B) (hd : FinDimV B) (i : LocT B) : Finite (XOf B i) := by
  have := hd (jOf B i) (wOf B i)
  obtain ⟨F, hF, -⟩ := NCov.exists_finset_pts (IsFractionRing.injective _ _) (std_comm (w := wOf B i) hs i.2.2.2.1 i.2.2.2.2.1)
    (std_split (j := jOf B i) (w := wOf B i)) (std_int (w := wOf B i) hs i.2.2.2.1 i.2.2.2.2.1)
  exact Finite.of_injective (fun x : XOf B i => (⟨x.1, hF _ x.2.2⟩ : F)) (by
    intro x y hxy
    have e := congrArg Subtype.val hxy
    exact Subtype.ext e)

theorem mxC_injOn (j : ℕ) (w : what₂.places.Pl) : Set.InjOn (mxC B j w) {i : LocT B | jOf B i = j ∧ wOf B i = w} := by
  rintro ⟨⟨j1, w1⟩, I1⟩ h1 ⟨⟨j2, w2⟩, I2⟩ h2 he
  have h1' : j1 = j ∧ w1 = w := h1
  have h2' : j2 = j ∧ w2 = w := h2
  obtain ⟨rfl, rfl⟩ := h1'
  obtain ⟨rfl, rfl⟩ := h2'
  have e1 := mxC_self B ⟨(_, _), I1⟩
  have e2 := mxC_self B ⟨(_, _), I2⟩
  simp only [jOf, wOf] at e1 e2 he
  rw [e1, e2] at he
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext he))

theorem locsFin_of (hs : HeckeStd0 B) (hd : FinDimV B) : LocsFin B := by
  intro j w
  by_cases hne : ({i : LocT B | jOf B i = j ∧ wOf B i = w}).Nonempty
  · obtain ⟨i0, hj, hw⟩ := hne
    subst hj; subst hw
    have := hd (jOf B i0) (wOf B i0)
    have hmax := NCov.finite_maximal (IsFractionRing.injective _ _) (std_comm (w := wOf B i0) hs i0.2.2.2.1 i0.2.2.2.2.1)
      (std_split (j := jOf B i0) (w := wOf B i0)) (std_int (w := wOf B i0) hs i0.2.2.2.1 i0.2.2.2.2.1)
    refine Set.Finite.of_finite_image (hmax.subset ?_) (mxC_injOn _ _)
    rintro _ ⟨⟨⟨j1, w1⟩, I1⟩, hi, rfl⟩
    have hi' : j1 = jOf B i0 ∧ w1 = wOf B i0 := hi
    obtain ⟨hj, hw⟩ := hi'
    subst hj; subst hw
    have e1 := mxC_self B ⟨(_, _), I1⟩
    simp only [jOf, wOf] at e1
    show (mxC B _ _ _).IsMaximal
    rw [e1]
    exact I1.2.1
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    exact Set.finite_empty

theorem tSep (i : LocT B) (x y : XOf B i) (hxy : x ≠ y) :
    ∃ f ∈ TOf B i, (f : XOf B i → OOf B i) x ≠ (f : XOf B i → OOf B i) y := by
  by_contra hcon
  push_neg at hcon
  apply hxy
  apply Subtype.ext
  refine AlgHom.ext_of_adjoin_eq_top Algebra.adjoin_adjoin_coe_preimage ?_
  intro z hz
  obtain ⟨v, k, hvk, hzv⟩ := hz
  have hz' : z = ⟨B.hK (jOf B i) (wOf B i) v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ := Subtype.ext hzv
  have := hcon (hTfun B i v k) (Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩)
  rw [hz']
  simpa [hTfun, dif_pos hvk] using this

end Gen

end Formalism.L2.Fam.NPC
