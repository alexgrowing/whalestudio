import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPdivGroupForPoint

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.KernelNoTorsion GlobalTheory.RaynaudPDiv
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj

namespace GlobalTheory.RaynaudTower

theorem exists_pDivGroup_raynaud_tower : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), ∃ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] P.tateGt) (l : LieG P.Gt ≃ G.Lie) (c : P.T →ₗ[ℤ_[p]] G.dual.Tate) (ζ : (PDivGroup.mu p O).Tate) (tw : G.TorsionTower P.Gt), Function.Bijective (fun a : ℤ_[p] => a • ζ) ∧ (∀ s t, pairing G O s (c t) = pairT P.A P.eps (e s : P.T) t • ζ) ∧ (∀ x t, l x (dlog (G := G) (c t)) = (P.al₀ t).1 x) ∧ (∀ (s : G.Tate) (n : ℕ), (e s : P.T).lev n = (P.toA (GlobalTheory.DeRham.spOver (s.pt n) ≫ tw.y n))) ∧ ∀ n : ℕ, algebraMap O C (muRoot ζ n) = (P.eps.1.lev n : C) := by
  intro p hp C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P
  have hi := P.integers.hom_inj
  haveI : IsDomain O := hi.isDomain (algebraMap O C)
  have hA := isSemiAbelian_of_isGt _ _ P.Gt ⟨P.D⟩
  haveI := hA.smooth
  obtain ⟨G, ⟨t⟩⟩ := exists_tower p O (fun h => hp.out.ne_zero ((Nat.cast_eq_zero (R := C)).1 (by
    rw [← map_natCast (algebraMap O C), h, map_zero]))) P.Gt hA P.finite_flat
  obtain ⟨e, he⟩ := exists_tateEquiv p O P.Gt G t
  obtain ⟨l, hl⟩ := exists_lieEquiv p O P.Gt G t
  obtain ⟨ζ, hζ, hζ'⟩ := exists_generator P.integers P.eps
  choose c hc using fun s : P.T => exists_dual_tate p O P.Gt G t (P.weilChar s)
  have hu : ∀ s n, charElem (c s) n = (unitOf (torsionLift (t.y n) (t.y_pow n) ≫ (P.weilChar s).χ n) : G.A n) :=
    fun s n => hc s n _ (AlgHom.id O _) _ (by rw [torsionLift_ι, spOver_id, Category.id_comp])
  have hx : ∀ {a b : G.dual.Tate}, (∀ n, charElem a n = charElem b n) → a = b := fun h =>
    (charHom G).injective (hom_mu_ext fun n => by rw [charHom_app_muT, charHom_app_muT, h])
  have hadd : ∀ s s', c (s + s') = c s + c s' := fun s s' => hx fun n => by
    rw [charElem_add, hu, hu, hu, P.weilChar_add, MonObj.comp_mul, GmPoints.unitOf_mul, Units.val_mul]
  have hpow : ∀ (R : Type) [CommRing R] [Algebra O R] (w : specO O R ⟶ Gm (Sp O)) (k : ℕ),
      unitOf (w ^ k) = unitOf w ^ k := fun R _ _ w k => map_pow (MonoidHom.mk' unitOf GmPoints.unitOf_mul) w k
  have hsm : ∀ (a : ℤ_[p]) s, c (a • s) = a • c s := fun a s => hx fun n => by
    have h : (P.weilChar (a • s)).χ n = (P.weilChar s).χ n ^ digit n a := P.char_ext fun w => by
      rw [P.isWeilChar_weilChar, MonObj.comp_pow, hpow, Units.val_pow_eq_pow_val, map_pow,
        P.isWeilChar_weilChar, Tate.lev_smul, weil_pow_right (one_le_ppow p n) (s.lev_pow n) (P.toA_pow w),
        Units.val_pow_eq_pow_val]
    rw [charElem_smul, hu, hu, h, MonObj.comp_pow, hpow, Units.val_pow_eq_pow_val]
  refine ⟨G, e.trans (LinearEquiv.ofInjective _ (Tate.map_injective P.toA_injective)), l,
    ⟨⟨c, hadd⟩, hsm⟩, ζ, t, hζ, fun s s' => muRoot_ext fun n => hi ?_,
    fun x s => lie_dlog p O P.Gt G t _ _ (hc s) x _ (hl x), fun s n => ?_, hζ'⟩
  · have hw := torsionLift_ι _ ((t.exists_iff n _).1 ⟨s.pt n, rfl⟩)
    rw [muRoot_pairing, muRoot_smul, map_pow, hζ', ← Units.val_pow_eq_pow_val, pow_pairT]
    refine (congrArg (algebraMap O C) (hc s' n O _ _ hw)).trans ((P.isWeilChar_weilChar s' n _).trans ?_)
    rw [hw, ← he]
    rfl
  · rw [← he]
    rfl

end GlobalTheory.RaynaudTower
