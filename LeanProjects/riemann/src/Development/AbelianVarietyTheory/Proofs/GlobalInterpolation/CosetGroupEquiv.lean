import Mathlib
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.CosetGroupMembership
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ClassesDoubleCosets

noncomputable section

namespace GlobalTheory.Proof.CosetGroupEquiv

open NumberField IsDedekindDomain Formalism.UG Formalism.BasicNotions Formalism.L2.Herm
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke

section Abstract

variable {G : Type} [Group G]

def cosetGrpEquiv (Γ K : Subgroup G) (y : G) : CosetGroupMembership.cosetGrp Γ K y ≃ stabAt Γ K y where
  toFun x := ⟨⟨x.1, ((CosetGroupMembership.mem_cosetGrp Γ K y x.1).1 x.2).1⟩, ((CosetGroupMembership.mem_cosetGrp Γ K y x.1).1 x.2).2⟩
  invFun x := ⟨x.1.1, (CosetGroupMembership.mem_cosetGrp Γ K y x.1.1).2 ⟨x.1.2, x.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_cosetGrp (Γ K : Subgroup G) (y : G) :
    Nat.card (CosetGroupMembership.cosetGrp Γ K y) = Nat.card (stabAt Γ K y) :=
  Nat.card_congr (cosetGrpEquiv Γ K y)

theorem sum_clause_iff (Γ K : Subgroup G) (m : ℝ) :
    (∀ (ι : Type) [Fintype ι] (y : ι → G),
      Function.Bijective (fun i => (DoubleCoset.mk Γ K (y i) : ClassSet Γ K)) →
      ∑ i, ((Nat.card (CosetGroupMembership.cosetGrp Γ K (y i)) : ℕ) : ℝ)⁻¹ = m) ↔
    (∀ [Fintype (ClassSet Γ K)] (s : ClassSet Γ K → G), (∀ c, DoubleCoset.mk Γ K (s c) = c) →
      ∑ c, ((Nat.card (stabAt Γ K (s c)) : ℕ) : ℝ)⁻¹ = m) := by
  constructor
  · intro h _ s hs
    have hb : Function.Bijective (fun c => (DoubleCoset.mk Γ K (s c) : ClassSet Γ K)) := by
      have : (fun c => (DoubleCoset.mk Γ K (s c) : ClassSet Γ K)) = id := funext hs
      rw [this]
      exact Function.bijective_id
    rw [← h _ s hb]
    simp only [card_cosetGrp]
  · intro h ι _ y hy
    let e : ι ≃ ClassSet Γ K := Equiv.ofBijective _ hy
    letI : Fintype (ClassSet Γ K) := Fintype.ofEquiv ι e
    have hs : ∀ c : ClassSet Γ K, DoubleCoset.mk Γ K (y (e.symm c)) = c := fun c => e.apply_symm_apply c
    rw [← h (fun c => y (e.symm c)) hs, ← e.symm.sum_comp]
    simp only [card_cosetGrp]

theorem cosetSum_iff (Γ K : Subgroup G) (m : ℝ) : CosetGroupMembership.CosetSum Γ K m ↔ ClassesDoubleCosets.CosetMass Γ K m :=
  and_congr Iff.rfl (and_congr (forall_congr' fun y => (cosetGrpEquiv Γ K y).finite_iff)
    (sum_clause_iff Γ K m))

end Abstract

section Obj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem stabHat_eq (hc : CMData F E) (S : HSpace E) (N : Submodule (𝓞 E) S.V) :
    CosetGroupMembership.stabHat hc S N = ClassesDoubleCosets.stabHat hc S N := rfl

theorem stabHat0_eq {R : Ranks} (sp : Spaces R F E) (N : Submodule (𝓞 E) (sp.X 0).V) :
    CosetGroupMembership.stabHat0 sp N = (levelAfL sp.cm.sig sp.gram0 (sp.crdLat0 N)).subgroupOf
      (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)) := by
  ext x
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

def InCoords (hc : CMData F E) {k : ℕ} (J : Matrix (Fin k) (Fin k) E) (Λ : Submodule (𝓞 E) (Fin k → E))
    (m : ℝ) : Prop :=
  CosetGroupMembership.CosetSum ((ratPts hc.sig J (Af F)).subgroupOf (UPts hc.sig J (Af F)))
    ((stabGL (hatL (F := F) Λ)).subgroupOf (UPts hc.sig J (Af F))) m

theorem inCoords_cast (hc : CMData F E) (S : HSpace E) {k : ℕ} (h : S.rank = k) (N : Submodule (𝓞 E) S.V)
    (m : ℝ) :
    InCoords hc S.gram (crdLat S N) m ↔
    InCoords hc (S.gram.reindex (finCongr h) (finCongr h))
      (N.map (((S.frame.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr h).symm) :
        S.V ≃ₗ[E] (Fin k → E)) : S.V →ₗ[E] (Fin k → E)).restrictScalars (𝓞 E))) m := by
  subst h
  rfl

theorem general_clause_iff {R : Ranks} (sp : Spaces R F E) (N : Submodule (𝓞 E) (sp.X 0).V) (m : ℝ) :
    CosetGroupMembership.CosetSum (UFin sp.cm (sp.X 0)) (CosetGroupMembership.stabHat sp.cm (sp.X 0) N) m ↔
    CosetGroupMembership.CosetSum (CosetGroupMembership.rat0 sp) (CosetGroupMembership.stabHat0 sp N) m :=
  inCoords_cast sp.cm (sp.X 0) sp.rank0 N m

end Obj

theorem general_iff : CosetGroupMembership.GeneralForm ↔ ClassesDoubleCosets.General := by
  unfold CosetGroupMembership.GeneralForm ClassesDoubleCosets.General
  simp only [cosetSum_iff, stabHat_eq]

theorem column_iff (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    CosetGroupMembership.ColumnForm D ↔ ClassesDoubleCosets.DefiniteSpaceClassStatement D Lv u := by
  letI := D.host.cmStar
  unfold CosetGroupMembership.ColumnForm ClassesDoubleCosets.DefiniteSpaceClassStatement
  refine forall_congr' fun N => forall_congr' fun _ => forall_congr' fun _ => ?_
  rw [cosetSum_iff, stabHat0_eq]
  rfl

theorem column_of_general (h : CosetGroupMembership.GeneralForm) (D : D7) : CosetGroupMembership.ColumnForm D := by
  letI := D.host.cmStar
  intro N hN hU
  exact (general_clause_iff D.sp N _).1
    (h D.host.F D.host.E D.sp.cm (D.sp.X 0) (D.sp.X_sig 0) (baseSpace_posDef D.R D.host.F D.sp) N hN hU)

theorem massAsCosetSum_iff : CosetGroupMembership.MassAsCosetSum ↔ ClassesDoubleCosets.ClassesAsDoubleCosets :=
  ⟨fun h => ⟨general_iff.1 h.1, fun D Lv u => (column_iff D Lv u).1 (h.2 D)⟩,
    fun h => ⟨general_iff.2 h.1, column_of_general (general_iff.2 h.1)⟩⟩

end GlobalTheory.Proof.CosetGroupEquiv

end
