import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.GlOperatorsFormRepresentation
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.SaturatedLowerSetSpanOfLowerSetTypesSpan
import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightConditionFromIntegralForm

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.Joints Formalism.MainNotions.LemmaBAlt

theorem span_inter_eq_span_image {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] (hinj : Function.Injective (algebraMap O Kf))
    {σ X : Type} (bO : X → MvPolynomial σ O) (bK : X → MvPolynomial σ Kf)
    (hmap : ∀ x, MvPolynomial.map (algebraMap O Kf) (bO x) = bK x) (hLI : LinearIndependent Kf bK)
    (Y : Submodule Kf (MvPolynomial σ Kf)) (A : Set X)
    (hY : Submodule.span Kf (Set.range bK) ⊓ Y = Submodule.span Kf (bK '' A)) :
    {f | f ∈ Submodule.span O (Set.range bO) ∧ MvPolynomial.map (algebraMap O Kf) f ∈ Y} =
      (Submodule.span O (bO '' A) : Set _) := by
  classical
  have hmaplc : ∀ c : X →₀ O, MvPolynomial.map (algebraMap O Kf) (Finsupp.linearCombination O bO c) =
      Finsupp.linearCombination Kf bK (c.mapRange (algebraMap O Kf) (map_zero _)) := by
    intro c
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (by intro i; exact zero_smul _ _), Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, hmap, ← MvPolynomial.smul_eq_C_mul]
  ext G
  constructor
  · rintro ⟨hG, hGY⟩
    obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hG
    change (c.sum fun x a => a • bO x) ∈ Submodule.span O (bO '' A)
    refine Submodule.sum_mem _ fun x hx => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, ?_, rfl⟩)
    have h1 : MvPolynomial.map (algebraMap O Kf) (Finsupp.linearCombination O bO c) ∈
        Submodule.span Kf (bK '' A) := by
      rw [← hY]
      refine ⟨?_, hGY⟩
      rw [hmaplc]
      exact Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨_, rfl⟩
    obtain ⟨l, hl, hle⟩ := (Finsupp.mem_span_image_iff_linearCombination Kf).1 h1
    rw [hmaplc] at hle
    have hlc := hLI hle
    have hxl : x ∈ l.support := by
      rw [hlc, Finsupp.mem_support_iff, Finsupp.mapRange_apply]
      intro h0
      exact (Finsupp.mem_support_iff.1 hx) (hinj (by rw [h0, map_zero]))
    exact (Finsupp.mem_supported Kf l).1 hl hxl
  · intro hG
    change G ∈ Submodule.span O (bO '' A) at hG
    induction hG using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      refine ⟨Submodule.subset_span ⟨x, rfl⟩, ?_⟩
      rw [hmap]
      have : bK x ∈ Submodule.span Kf (Set.range bK) ⊓ Y := by
        rw [hY]
        exact Submodule.subset_span ⟨x, hx, rfl⟩
      exact this.2
    | zero => exact ⟨Submodule.zero_mem _, by rw [map_zero]; exact Submodule.zero_mem _⟩
    | add x y _ _ hx hy =>
      exact ⟨Submodule.add_mem _ hx.1 hy.1, by rw [map_add]; exact Submodule.add_mem _ hx.2 hy.2⟩
    | smul a x _ hx =>
      exact ⟨Submodule.smul_mem _ _ hx.1, by
        rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
        exact Submodule.smul_mem _ _ hx.2⟩

abbrev GLWeightLabels (N r K : ℕ) : Fin (N + 1) ⊕ Fin (N + 1) → Type
  | .inl _ => Fin r → ℤ
  | .inr _ => Fin K → ℤ

structure ExternalProductHyps : Prop where
  p16 : ExternalProductBasis
  e1 : GlOperatorsFormRepresentation
  e2 : IsotypicZeroOfNonDominant
  e3 : ProjectorsPreserveMultidegree
  e5a : ProjectorsCommuteNested
  e5b : ProjectorsCommuteDisjoint
  lowPl : RestLowPl
  lowTan : RestLowTan
  sum : RestJointSum

section

variable (D : Formalism.BasicNotions.D7) (H : ExternalProductHyps) {F : Type} [Field F] [CharZero F] {N : ℕ} (r K : ℕ) (LL : Letters (Fin N))
  (B : Fin N → ℕ)

include D H in
theorem exists_decSys_isoSub_glOpsE_of_injective {m k : ℕ} (S : Set (Fin N)) (e : Fin m → Fin k) (he : Function.Injective e) :
    ∃ pr : (Fin m → ℤ) → Module.End F (MvPolynomial (Fin N × Fin k) F), DecSys (isoSub (glOpsE F LL S e)) pr :=
  isoDecomp (glOpsE F LL S e) D (weight_condition_from_integral_form D) (H.e1 F N m k LL S e he)

abbrev EPl (F : Type) [Field F] {N : ℕ} (r K : ℕ) (LL : Letters (Fin N)) (i : Fin (N + 1)) :
    GLOps r F (MvPolynomial (Fin N × Fin (r + K)) F) := glOpsE F LL {j | j.val < i.val} (Fin.castAdd K)

abbrev ETan (F : Type) [Field F] {N : ℕ} (r K : ℕ) (LL : Letters (Fin N)) (i : Fin (N + 1)) :
    GLOps K F (MvPolynomial (Fin N × Fin (r + K)) F) := glOpsE F LL {j | j.val < i.val} (Fin.natAdd r)

def prPl (i : Fin (N + 1)) : (Fin r → ℤ) → Module.End F (MvPolynomial (Fin N × Fin (r + K)) F) :=
  Classical.choose (exists_decSys_isoSub_glOpsE_of_injective (F := F) D H LL {j | j.val < i.val} (Fin.castAdd K) (Fin.castAdd_injective r K))

def prTan (i : Fin (N + 1)) : (Fin K → ℤ) → Module.End F (MvPolynomial (Fin N × Fin (r + K)) F) :=
  Classical.choose (exists_decSys_isoSub_glOpsE_of_injective (F := F) D H LL {j | j.val < i.val} (Fin.natAdd r) (Fin.natAdd_injective K r))

theorem prPl_sys (i : Fin (N + 1)) : DecSys (isoSub (EPl F r K LL i)) (prPl D H r K LL i) :=
  Classical.choose_spec (exists_decSys_isoSub_glOpsE_of_injective (F := F) D H LL {j | j.val < i.val} (Fin.castAdd K) (Fin.castAdd_injective r K))

theorem prTan_sys (i : Fin (N + 1)) : DecSys (isoSub (ETan F r K LL i)) (prTan D H r K LL i) :=
  Classical.choose_spec (exists_decSys_isoSub_glOpsE_of_injective (F := F) D H LL {j | j.val < i.val} (Fin.natAdd r) (Fin.natAdd_injective K r))

theorem initialSegments_nested (i j : Fin (N + 1)) :
    ({l : Fin N | l.val < i.val} ⊆ {l : Fin N | l.val < j.val}) ∨
      ({l : Fin N | l.val < j.val} ⊆ {l : Fin N | l.val < i.val}) := by
  rcases le_total i j with h | h
  · exact Or.inl fun l (hl : l.val < i.val) => lt_of_lt_of_le hl h
  · exact Or.inr fun l (hl : l.val < j.val) => lt_of_lt_of_le hl h

theorem fin_castAdd_ne_natAdd (a : Fin r) (b : Fin K) : Fin.castAdd K a ≠ Fin.natAdd r b := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

def externalProductJointData : JointData F (MvPolynomial (Fin N × Fin (r + K)) F) (Fin (N + 1) ⊕ Fin (N + 1)) (GLWeightLabels N r K)
    (PIdx r K LL B) where
  le := fun s => match s with
    | .inl _ => DomLE
    | .inr _ => DomLE
  dom := fun s => match s with
    | .inl _ => Dominant
    | .inr _ => Dominant
  le_refl := fun s => match s with
    | .inl _ => fun a => dominance_refl a
    | .inr _ => fun a => dominance_refl a
  le_trans := fun s => match s with
    | .inl _ => fun _ _ _ h1 h2 => dominance_trans h1 h2
    | .inr _ => fun _ _ _ h1 h2 => dominance_trans h1 h2
  le_antisymm := fun s => match s with
    | .inl _ => fun _ _ h1 h2 => dominance_antisymm h1 h2
    | .inr _ => fun _ _ h1 h2 => dominance_antisymm h1 h2
  W := fun s => match s with
    | .inl i => isoSub (EPl F r K LL i)
    | .inr i => isoSub (ETan F r K LL i)
  e := fun s => match s with
    | .inl i => prPl D H r K LL i
    | .inr i => prTan D H r K LL i
  sys := fun s => match s with
    | .inl i => prPl_sys D H r K LL i
    | .inr i => prTan_sys D H r K LL i
  comm := fun s t => match s, t with
    | .inl i, .inl j => fun a b => H.e5a F N r (r + K) LL _ _ _ (Fin.castAdd_injective r K) (initialSegments_nested i j) _ _
        (prPl_sys D H r K LL i) (prPl_sys D H r K LL j) a b
    | .inr i, .inr j => fun a b => H.e5a F N K (r + K) LL _ _ _ (Fin.natAdd_injective K r) (initialSegments_nested i j) _ _
        (prTan_sys D H r K LL i) (prTan_sys D H r K LL j) a b
    | .inl i, .inr j => fun a b => H.e5b F N r K (r + K) LL _ _ _ _ (Fin.castAdd_injective r K)
        (Fin.natAdd_injective K r) (fin_castAdd_ne_natAdd r K) _ _ (prPl_sys D H r K LL i) (prTan_sys D H r K LL j) a b
    | .inr i, .inl j => fun a b => (H.e5b F N r K (r + K) LL _ _ _ _ (Fin.castAdd_injective r K)
        (Fin.natAdd_injective K r) (fin_castAdd_ne_natAdd r K) _ _ (prPl_sys D H r K LL j) (prTan_sys D H r K LL i) b a).symm
  bot := fun s => match s with
    | .inl i => fun a h => H.e2 F N r (r + K) LL _ _ (Fin.castAdd_injective r K) a h
    | .inr i => fun a h => H.e2 F N K (r + K) LL _ _ (Fin.natAdd_injective K r) a h
  Pl := Pol F (r + K) B
  stab := fun s => match s with
    | .inl i => fun a x hx => H.e3 F N r (r + K) LL _ _ (Fin.castAdd_injective r K) _ (prPl_sys D H r K LL i) B a x hx
    | .inr i => fun a x hx => H.e3 F N K (r + K) LL _ _ (Fin.natAdd_injective K r) _ (prTan_sys D H r K LL i) B a x hx
  b := pvec F r K LL B
  P := fun x s => match s with
    | .inl i => x.1.1.1 i
    | .inr i => x.1.2.1 i
  Pdom := fun x s => match s with
    | .inl i => by
        obtain ⟨_, _, _, ⟨P1, h1⟩, _⟩ := x.2.1
        exact h1 ▸ P1.dom i
    | .inr i => by
        obtain ⟨_, _, _, _, ⟨P2, h2⟩⟩ := x.2.1
        exact h2 ▸ P2.dom i
  li := (H.p16 F N r K LL B).1
  span := (H.p16 F N r K LL B).2
  low := fun s => match s with
    | .inl i => fun pi h1 h2 => H.lowPl F N r K LL B i pi ⟨h1, h2⟩
    | .inr i => fun pi h1 h2 => H.lowTan F N r K LL B i pi ⟨h1, h2⟩

end

end Formalism.MainNotions.G.ColumnFamilies
