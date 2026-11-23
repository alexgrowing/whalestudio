import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.RedMk
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatThickeningQuotientStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.LsQ

open CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb.LsG

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O]
  {F : B.Fn O} {ρ : O →+* k} {n : ℕ} (hn : n ≠ 0)

def qG : (fl l F ρ (n + 1)).FullSubcategory ⥤ (fl l F ρ n).FullSubcategory :=
  (fl l F ρ n).lift ((fl l F ρ (n + 1)).ι ⋙ qF hn) fun T => GlobalTheory.T.flat_thickening_quotient l k O F ρ n hn T.obj T.property

def mq : QMor (sW l F ρ n) (sW l F ρ (n + 1)) (IdF.span _ ((l : WittVector l k) ^ n)) where
  G := qG hn
  ρ T := { toFun := fun x => (show T.obj.B ⧸ lI n T.obj from x)
           map_one' := rfl
           map_mul' := fun _ _ => rfl
           map_zero' := rfl
           map_add' := fun _ _ => rfl
           commutes' := fun _ => rfl }
  inj _ _ _ h := h
  nat {T T'} φ x y h := by
    have h' : x = Ideal.Quotient.mk (lI n T.obj) y := h
    subst h'
    rfl
  dp T e x y hx hy h := by
    have h' : x = Ideal.Quotient.mk (lI n T.obj) y := h
    subst h'
    exact DividedPowers.Quotient.dpow_apply T.obj.δ (subPd hn T.obj) hy

def qα (T : Thick (Wc.L l F ρ (n + 1))) : T ⟶ (Wc.redM l F ρ n).functor.obj (qT hn T) where
  φ := Ideal.Quotient.mk (lI n T)
  u j := j.elim
  comm r := (qi_red T r).symm
  dp := DividedPowers.Quotient.isDPMorphism T.δ (subPd hn T)
  hle := Ideal.le_comap_map
  pt := by
    refine Subtype.ext (Prod.ext ?_ rfl)
    refine Ideal.Quotient.ringHom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun w => ?_))
    have h := T.w (Ideal.Quotient.mk _ w)
    change Ideal.quotientMap (T.J.map (Ideal.Quotient.mk (lI n T))) (Ideal.Quotient.mk (lI n T)) Ideal.le_comap_map
        ((Wc.L l F ρ (n + 1)).str T.y _) =
      qy T (Ideal.quotientMap (Wc.Im l k n) (Wc.red l k n) (Ideal.map_le_iff_le_comap.1 (Wc.dp_red l k n).1)
        (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ w)))
    rw [h, Ideal.quotientMap_mk, Ideal.quotientMap_mk, red_mk']
    rfl
  hx j := j.elim
  hs := by
    have h := T.hs
    change ∏ j : Empty, T.x j = (T.s : T.B) * T.i 1 at h
    rw [Finset.univ_eq_empty, Finset.prod_empty, map_one, mul_one] at h
    have : IsEmpty (Wc.L l F ρ (n + 1)).ι := inferInstanceAs (IsEmpty Empty)
    have : IsEmpty (Wc.L l F ρ n).ι := inferInstanceAs (IsEmpty Empty)
    ext
    simp [Wc.redM, B.crMor, Mor.functor, Mor.obj, qT, ← h]
  hv j := j.elim

theorem qα_nat {T T' : Thick (Wc.L l F ρ (n + 1))} (f : T ⟶ T') :
    qα hn T ≫ (Wc.redM l F ρ n).functor.map ((qF hn).map f) = f ≫ qα hn T' :=
  Thick.Hom.ext (RingHom.ext fun _ => rfl) (funext fun j => j.elim)

end CrystallineSemistableComparison.Pb.LsQ

end
