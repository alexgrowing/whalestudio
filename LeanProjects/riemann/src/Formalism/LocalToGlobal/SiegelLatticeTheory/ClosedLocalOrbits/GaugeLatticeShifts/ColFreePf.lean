import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AdmNPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormCorePsiNatEquiv
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHNeat

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.NormCut

section ColFreeBij

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X) {u : D.what₂.Word}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂)

def colD (h h' : Hfin X u) : X.B.I.Gf := ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)

def LeviOnto : Prop :=
  ∀ (q : {Λ // Λ ∈ what₂}) (s : Iof TR), ∃ h : Hfin X u,
    colD (cs.h (cs.base q.1)) h ∈ X.B.I.Kset ∧ colD h (cs.h (cs.base q.1)) ∈ X.B.I.Kset ∧
      levi TR (colD (cs.h (cs.base q.1)) h) = s

def ColLatRep (hK : X.LevelSubgroupCharacter) : Prop :=
  ∀ (q : {Λ // Λ ∈ what₂}) (h : Hfin X u) (ρ : cs.Cl) (γ : Gam X u) (κ : Ku X u hK),
    colD (cs.h (cs.base q.1)) h ∈ X.B.I.Kset → h = iotaF X u γ * cs.h ρ * (κ : Hfin X u) → cs.lamOf ρ = q.1

theorem UG_mul {x y : Iof TR} (hx : x ∈ UG TR) (hy : y ∈ UG TR) : x * y ∈ UG TR := fun v =>
  Formalism.L2.SG.NormCut.PsiNatEquivPf.isUni_mul (hx v) (hy v)

theorem UG_inv {x : Iof TR} (hx : x ∈ UG TR) : x⁻¹ ∈ UG TR := fun v =>
  Formalism.L2.SG.NormCut.PsiNatEquivPf.isUni_inv (hx v)

theorem colD_mul (h h' h'' : Hfin X u) : colD h h' * colD h' h'' = colD h h'' := by
  unfold colD; group

theorem colD_inv (h h' : Hfin X u) : (colD h h')⁻¹ = colD h' h := by
  unfold colD; group

theorem good_colD {h h' : Hfin X u} (hk : colD h h' ∈ X.B.I.Kset) : Good X (colD h h') :=
  colGood X u h h' hk (by have := K_inv X.B.I hk; rw [colD_inv] at this; exact this)

theorem scOf_eq (ρ : cs.Cl) : scOf TR cs ρ = levi TR (colD (cs.h (cs.base (cs.lamOf ρ))) (cs.h ρ)) := rfl

theorem colD_conj (γ h h' : Hfin X u) : colD h (γ * h) * colD h h' = colD h (γ * h') := by
  unfold colD; simp only [Subgroup.coe_mul]; group

theorem colD_ku (hK : X.LevelSubgroupCharacter) {h h' : Hfin X u} (hm : colD h h' ∈ X.K2) : h⁻¹ * h' ∈ Ku X u hK := by
  show (X.xu u)⁻¹ * ((h⁻¹ * h' : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.K2
  have e : (X.xu u)⁻¹ * ((h⁻¹ * h' : Hfin X u) : X.B.I.Gf) * X.xu u = colD h h' := by
    unfold colD; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  rw [e]; exact hm

theorem colFreeBij_of (hK : X.LevelSubgroupCharacter) (hR : ColReps hK cs) (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u hK) (hL : ColLatK cs)
    (hO : LeviOnto TR cs) (hRep : ColLatRep cs hK) (q : {Λ // Λ ∈ what₂}) :
    Function.Bijective (fun x : Aset TR cs q × {ρ : cs.Cl // lamQ cs ρ = q} × UG TR =>
      (x.1 : Iof TR) * scOf TR cs x.2.1.1 * (x.2.2 : Iof TR)) := by
  set hb : Hfin X u := cs.h (cs.base q.1) with hhb
  have hbl : cs.lamOf (cs.base q.1) = q.1 := cs.base_lam _ q.2
  have lamρ : ∀ ρ : {ρ : cs.Cl // lamQ cs ρ = q}, cs.lamOf ρ.1 = q.1 := fun ρ => congrArg Subtype.val ρ.2
  have kK : ∀ ρ : cs.Cl, cs.lamOf ρ = q.1 → colD hb (cs.h ρ) ∈ X.B.I.Kset := fun ρ hρ =>
    hL (cs.base q.1) ρ (hbl.trans hρ.symm)
  have kKi : ∀ ρ : cs.Cl, cs.lamOf ρ = q.1 → colD (cs.h ρ) hb ∈ X.B.I.Kset := fun ρ hρ =>
    hL ρ (cs.base q.1) (hρ.trans hbl.symm)
  have scρ : ∀ ρ : {ρ : cs.Cl // lamQ cs ρ = q}, scOf TR cs ρ.1 = levi TR (colD hb (cs.h ρ.1)) := fun ρ => by
    rw [scOf_eq, lamρ ρ]
  have aK : ∀ γ : Gam X u, ((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u)⁻¹ * (iotaF X u γ : X.B.I.Gf) *
      ((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u) = colD hb (iotaF X u γ * hb) := fun γ => by
    unfold colD; rw [hhb, Subgroup.coe_mul]; group
  constructor
  · rintro ⟨⟨a1, ha1⟩, ρ1, w1⟩ ⟨⟨a2, ha2⟩, ρ2, w2⟩ heq
    obtain ⟨γ1, hγ1K, ha1e⟩ := ha1
    obtain ⟨γ2, hγ2K, ha2e⟩ := ha2
    simp only at heq
    rw [aK] at hγ1K hγ2K ha1e ha2e
    rw [ha1e, ha2e, scρ, scρ] at heq
    rw [← levi_mul TR (good_colD hγ1K) (good_colD (kK _ (lamρ ρ1))),
      ← levi_mul TR (good_colD hγ2K) (good_colD (kK _ (lamρ ρ2))), colD_conj, colD_conj] at heq
    have hP1 : colD hb (iotaF X u γ1 * cs.h ρ1.1) ∈ X.B.I.Kset := by
      rw [← colD_conj]; exact K_mul X.B.I hγ1K (kK _ (lamρ ρ1))
    have hP2 : colD hb (iotaF X u γ2 * cs.h ρ2.1) ∈ X.B.I.Kset := by
      rw [← colD_conj]; exact K_mul X.B.I hγ2K (kK _ (lamρ ρ2))
    have hmK : colD (iotaF X u γ1 * cs.h ρ1.1) (iotaF X u γ2 * cs.h ρ2.1) ∈ X.B.I.Kset := by
      rw [← colD_mul _ hb, ← colD_inv]; exact K_mul X.B.I (K_inv X.B.I hP1) hP2
    have hlm : levi TR (colD (iotaF X u γ1 * cs.h ρ1.1) (iotaF X u γ2 * cs.h ρ2.1)) =
        (w1 : Iof TR) * (w2 : Iof TR)⁻¹ := by
      rw [← colD_mul _ hb, ← colD_inv, levi_mul TR (good_inv X (good_colD hP1)) (good_colD hP2),
        levi_inv TR (good_colD hP1)]
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, heq, mul_assoc, mul_inv_cancel, mul_one]
    have hmU : ∀ v, Formalism.L2.SG.GGMirabolic.IsUni D.R.k
        (levi TR (colD (iotaF X u γ1 * cs.h ρ1.1) (iotaF X u γ2 * cs.h ρ2.1)) v) := by
      rw [hlm]; exact UG_mul TR w1.2 (UG_inv TR w2.2)
    have hm2 := mem_level_of_unitriangular TR (good_colD hmK) (ncong_colDiff u _ _ hmK) hmU
    have hku := colD_ku hK hm2

    have hρ : ρ1.1 = ρ2.1 := by
      have hu := hR (cs.h ρ2.1)
      refine hu.unique ?_ ⟨1, 1, by simp⟩
      refine ⟨γ2⁻¹ * γ1, ⟨_, hku⟩, ?_⟩
      simp only [map_mul, map_inv]
      group
    have hρ' : ρ1 = ρ2 := Subtype.ext hρ
    subst hρ'

    have hγ : γ1 = γ2 := by
      have h0 : γ1⁻¹ * γ2 = 1 := by
        refine hN (cs.h ρ1.1) (γ1⁻¹ * γ2) ?_
        have e : (cs.h ρ1.1)⁻¹ * iotaF X u (γ1⁻¹ * γ2) * cs.h ρ1.1 =
            (iotaF X u γ1 * cs.h ρ1.1)⁻¹ * (iotaF X u γ2 * cs.h ρ1.1) := by
          simp only [map_mul, map_inv]; group
        rw [e]; exact hku
      rw [inv_mul_eq_one] at h0; exact h0
    subst hγ
    have ha : a1 = a2 := ha1e.trans ha2e.symm
    subst ha
    have hw : (w1 : Iof TR) = w2 := mul_left_cancel heq
    have : w1 = w2 := Subtype.ext hw
    subst this
    rfl
  · intro s
    obtain ⟨h, hk, hki, hs⟩ := hO q s
    obtain ⟨ρ, ⟨γ, κ, hh⟩, -⟩ := hR h
    have hlam : cs.lamOf ρ = q.1 := hRep q h ρ γ κ hk hh
    have hκ2 : colD 1 (κ : Hfin X u) ∈ X.K2 := by
      have := κ.2
      have e : colD 1 (κ : Hfin X u) = (X.xu u)⁻¹ * ((κ : Hfin X u) : X.B.I.Gf) * X.xu u := by
        unfold colD; simp only [Subgroup.coe_one, one_mul]; group
      rw [e]; exact this
    have hκK : colD 1 (κ : Hfin X u) ∈ X.B.I.Kset := hκ2.1
    have haE : colD hb (iotaF X u γ * hb) = colD hb h * (colD 1 (κ : Hfin X u))⁻¹ * colD (cs.h ρ) hb := by
      rw [hh]; unfold colD; simp only [Subgroup.coe_mul, Subgroup.coe_one, one_mul]; group
    have haK : colD hb (iotaF X u γ * hb) ∈ X.B.I.Kset := by
      rw [haE]; exact K_mul X.B.I (K_mul X.B.I hk (K_inv X.B.I hκK)) (kKi ρ hlam)
    have ga := good_colD haK
    have gr := good_colD (kK ρ hlam)
    have gk := good_colD hκK
    refine ⟨⟨⟨levi TR (colD hb (iotaF X u γ * hb)), γ, by rw [aK]; exact haK, by rw [aK]⟩,
      ⟨ρ, Subtype.ext hlam⟩, ⟨levi TR (colD 1 (κ : Hfin X u)), fun v => unitriangular_reduction_of_mem_level TR gk hκ2 v⟩⟩, ?_⟩
    simp only
    rw [show scOf TR cs ρ = levi TR (colD hb (cs.h ρ)) by rw [scOf_eq, hlam], ← levi_mul TR ga gr,
      ← levi_mul TR (good_mul X ga gr) gk, colD_conj]
    have e2 : colD hb (iotaF X u γ * cs.h ρ) * colD 1 (κ : Hfin X u) = colD hb h := by
      rw [hh]; unfold colD; simp only [Subgroup.coe_mul, Subgroup.coe_one, one_mul]; group
    rw [e2, hs]

end ColFreeBij

end Formalism.L2.SG.NormCut
