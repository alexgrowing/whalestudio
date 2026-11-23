import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeToLevelOfDvdTrueDGam

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC

namespace GlobalTheory.Mem.R3.GamDvd

attribute [local instance] starE

section Stab

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (Λ : LevFam X.E X.K n SG)

def stabRat (d : DecoSet X.E n ST SG) : MulAction.stabilizer (FormG Λ) d →* autO d.1.N where
  toFun g := ⟨(g.1.1 : Sp X.E n ≃ₗ[X.E] Sp X.E n), g.1.1.2,
    congrArg (fun e : DecoSet X.E n ST SG => e.1.N) ((MulAction.mem_stabilizer_iff).1 g.2)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem stabRat_injective (d : DecoSet X.E n ST SG) : Function.Injective (stabRat Λ d) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hγ : (g.1.1 : Sp X.E n ≃ₗ[X.E] Sp X.E n) = 1 := congrArg Subtype.val hg
  have hbe := congrArg (fun e : DecoSet X.E n ST SG => e.1.be) ((MulAction.mem_stabilizer_iff).1 g.2)
  have hM : ∀ w : SG, ((g.1.2 : GLG X.E n SG) w : Matrix (Fin n) (Fin n) (𝓞 X.E ⧸ w.1.asIdeal)) = 1 := by
    intro w
    refine Matrix.ext_of_mulVec_single fun i => ?_
    obtain ⟨x, -, hx⟩ := d.2.be_surj w (Pi.single i 1)
    have e := congrFun (congrFun hbe w) x
    change ((g.1.2 : GLG X.E n SG) w : Matrix (Fin n) (Fin n) _).mulVec
      (d.1.be w ((g.1.1 : Sp X.E n ≃ₗ[X.E] Sp X.E n).symm x)) = d.1.be w x at e
    rw [hγ] at e
    change ((g.1.2 : GLG X.E n SG) w : Matrix (Fin n) (Fin n) _).mulVec (d.1.be w x) = d.1.be w x at e
    rw [hx] at e
    rw [e, Matrix.one_mulVec]
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext hγ
  · exact Subtype.ext (funext fun w => Units.ext (hM w))

theorem card_stab_dvd (d : DecoSet X.E n ST SG) :
    Nat.card (MulAction.stabilizer (FormG Λ) d) ∣ Nat.card (autO d.1.N) :=
  Subgroup.card_dvd_of_injective (stabRat Λ d) (stabRat_injective Λ d)

end Stab

section Fam

variable {B : Base} {px : PreX B.toPre} (I : TC B px) (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B px → B.LL))
  (tr : TrI B px)

theorem gamDvd_DGam :
    (∀ (t : TupU I U) (c : ((famC I hX U Xg tr).A.fam.R t).S.Cl),
      Fintype.card (((famC I hX U Xg tr).A.fam.R t).S.Gam c) ∣ DGam B.fields.E B.R) ∧
    ∀ (j : Fin B.R.m) (t : TupU I U) (c : ((famC I hX U Xg tr).A.fam.L j t).S.Cl),
      Fintype.card (((famC I hX U Xg tr).A.fam.L j t).S.Gam c) ∣ DGam B.fields.E B.R := by
  refine ⟨fun t c => ?_, fun j t c => ?_⟩
  · rw [Fintype.card_eq_nat_card]
    exact (card_stab_dvd _ (Quotient.out c)).trans
      (dvd_DGam (posStar_of_ok hX) B.R (pred_mem_gamRanks B.R) (Quotient.out c).2.lat (Quotient.out c).2.uni)
  · rw [Fintype.card_eq_nat_card]
    exact (card_stab_dvd _ (Quotient.out c)).trans
      (dvd_DGam (posStar_of_ok hX) B.R (nV_mem_gamRanks B.R) (Quotient.out c).2.lat (Quotient.out c).2.uni)

theorem gamDvd (l : I.Laws) (Z : Later B (I.cols l)) :
    (∀ (t : TupU I U) (c : ((famC I hX U Xg tr).A.fam.R t).S.Cl),
      Fintype.card (((famC I hX U Xg tr).A.fam.R t).S.Gam c) ∣ ((I.rec7 l Z).mem (I.rec7 l Z).u₀).C.DGam) ∧
    ∀ (j : Fin B.R.m) (t : TupU I U) (c : ((famC I hX U Xg tr).A.fam.L j t).S.Cl),
      Fintype.card (((famC I hX U Xg tr).A.fam.L j t).S.Gam c) ∣ ((I.rec7 l Z).mem (I.rec7 l Z).u₀).C.DGam :=
  gamDvd_DGam I hX U Xg tr

theorem gamDvd_stages (Y : Stages) {px : PreX Y.B.toPre} (I : TC Y.B px) (l : I.Laws) (hC : Y.C = I.cols l) (hX : Y.B.fields.Ok)
    (U : Set I.ι) (Xg : Finset (Gc Y.B px → Y.B.LL)) (tr : TrI Y.B px) :
    (∀ (t : TupU I U) (c : ((famC I hX U Xg tr).A.fam.R t).S.Cl),
      Fintype.card (((famC I hX U Xg tr).A.fam.R t).S.Gam c) ∣ (Y.toD7.mem Y.toD7.u₀).C.DGam) ∧
    ∀ (j : Fin Y.B.R.m) (t : TupU I U) (c : ((famC I hX U Xg tr).A.fam.L j t).S.Cl),
      Fintype.card (((famC I hX U Xg tr).A.fam.L j t).S.Gam c) ∣ (Y.toD7.mem Y.toD7.u₀).C.DGam := by
  have e : (Y.toD7.mem Y.toD7.u₀).C.DGam = DGam Y.B.fields.E Y.B.R := by
    have e1 : ∀ u, (Y.toD7.mem u).C.DGam = (Y.C.mem u).C.DGam := fun _ => rfl
    rw [e1, hC]
    rfl
  rw [e]
  exact gamDvd_DGam I hX U Xg tr

end Fam

end GlobalTheory.Mem.R3.GamDvd
