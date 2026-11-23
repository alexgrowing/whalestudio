import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

namespace GlobalTheory.GenFibreDim

section

attribute [local instance low] specializationOrder

theorem le_height_of_specializingMap {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    [T0Space X] [T0Space Z] {f : X → Z} (hf : SpecializingMap f) (n : ℕ) :
    ∀ y : X, (n : ℕ∞) ≤ Order.height (f y) → (n : ℕ∞) ≤ Order.height y := by
  induction n with
  | zero => intro y _; simp
  | succ n ih =>
    intro y hy
    have hex : ∃ b < f y, (n : ℕ∞) ≤ Order.height b := by
      by_contra hne
      push_neg at hne
      have h1 : Order.height (f y) ≤ n := by
        rw [Order.height_eq_iSup_lt_height]
        exact iSup₂_le fun b hb => Order.add_one_le_of_lt (hne b hb)
      have h2 : ((n + 1 : ℕ) : ℕ∞) ≤ n := hy.trans h1
      have h3 : n + 1 ≤ n := by exact_mod_cast h2
      omega
    obtain ⟨b, hb, hnb⟩ := hex
    obtain ⟨y', hyy', rfl⟩ := hf hb.le
    have hlt : y' < y := lt_of_le_of_ne hyy' (fun h => hb.ne (by rw [h]))
    have h4 := Order.height_add_one_le hlt
    have h5 := ih y' hnb
    calc ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; rfl
      _ ≤ Order.height y' + 1 := by gcongr
      _ ≤ Order.height y := h4

theorem topologicalKrullDim_genericFibre_le : ∀ (B Y : Scheme.{0}) [IsIntegral B] (d e : ℕ),
    topologicalKrullDim B = (d : ℕ) → topologicalKrullDim Y ≤ (d + e : ℕ) →
    ∀ (f : Y ⟶ B) [UniversallyClosed f] (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField),
    IsPullback j s f (B.fromSpecStalk (genericPoint B)) → topologicalKrullDim G ≤ (e : ℕ) := by
  intro B Y _ d e hB hY f _ G j s h
  have hpre : IsPreimmersion j :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) h.flip inferInstance
  have hinj : Function.Injective j := (IsPreimmersion.isEmbedding j).injective
  have hm : StrictMono (j : G → Y) := fun a b hab =>
    lt_of_le_of_ne (Specializes.map hab.le j.continuous) (hinj.ne hab.ne)
  have hfj : ∀ x : G, f (j x) = genericPoint B := by
    intro x
    have e1 : f (j x) = (B.fromSpecStalk (genericPoint B)) (s x) := by
      rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
    have e2 : (B.fromSpecStalk (genericPoint B)) (s x) ⤳ genericPoint B := by
      have : (B.fromSpecStalk (genericPoint B)) (s x) ∈
          Set.range (B.fromSpecStalk (genericPoint B)) := ⟨_, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    rw [e1]
    exact (e2.antisymm (genericPoint_specializes _)).eq
  have eB : Order.krullDim B = (d : WithBot ℕ∞) := by
    rw [← hB]; exact (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := B))).symm
  have eY : topologicalKrullDim Y = Order.krullDim Y :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))
  have eG : topologicalKrullDim G = Order.krullDim G :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := G))

  have hη : (d : ℕ∞) ≤ Order.height (genericPoint B) := by
    rw [Order.krullDim_eq_iSup_height_of_nonempty] at eB
    have : (⨆ b : B, Order.height b) = (d : ℕ∞) := by exact_mod_cast eB
    rw [← this]
    exact iSup_le fun b => Order.height_mono (genericPoint_specializes b)
  have hsp : SpecializingMap f := f.isClosedMap.specializingMap
  rw [eG]
  rcases isEmpty_or_nonempty G with _ | _
  · simp [Order.krullDim_eq_bot]
  haveI : Nonempty Y := Nonempty.map j inferInstance
  rw [eY, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty] at hY
  have hY' : (⨆ y : Y, Order.height y + Order.coheight y) ≤ ((d + e : ℕ) : ℕ∞) := by
    exact_mod_cast hY
  rw [Order.krullDim_eq_iSup_coheight_of_nonempty]
  have : (⨆ x : G, Order.coheight x) ≤ (e : ℕ∞) := by
    refine iSup_le fun x => ?_
    have h1 : (d : ℕ∞) ≤ Order.height (j x) :=
      le_height_of_specializingMap hsp d (j x) (by rw [hfj x]; exact hη)
    have h2 := Order.coheight_le_coheight_apply_of_strictMono _ hm x
    have h3 : Order.height (j x) + Order.coheight (j x) ≤ ((d + e : ℕ) : ℕ∞) :=
      (le_iSup (fun y : Y => Order.height y + Order.coheight y) (j x)).trans hY'
    have h4 : (d : ℕ∞) + Order.coheight x ≤ (d : ℕ∞) + (e : ℕ∞) := by
      push_cast at h3
      exact (add_le_add h1 h2).trans h3
    exact (WithTop.add_le_add_iff_left (ENat.coe_ne_top d)).1 h4
  exact_mod_cast this

end

end GlobalTheory.GenFibreDim
