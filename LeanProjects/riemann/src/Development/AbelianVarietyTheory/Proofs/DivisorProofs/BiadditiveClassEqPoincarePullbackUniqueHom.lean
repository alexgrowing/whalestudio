import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.FamHom

theorem main : ∀ (K : Type) [Field K] (A A' T : AbVar K) (P : LB (A.X ⊗ A'.X).left) (hP : AbDual.IsDual A.X A'.X P)
    (β : Pic (A.X ⊗ T.X).left), (∀ (Y : Over (Sp K)) (a a' : Y ⟶ A.X) (t : Y ⟶ T.X),
      CechPic.pull (lift (a * a') t).left β = CechPic.pull (lift a t).left β + CechPic.pull (lift a' t).left β) →
    CechPic.pull (lift (𝟙 A.X) (1 : A.X ⟶ T.X)).left β = 0 →
    ∃! ψ : T ⟶ A', β = AbDual.evc hP.isLB (fst A.X T.X) (snd A.X T.X ≫ ψ.hom) := by
  intro K _ A A' T P hP β hadd h0
  obtain ⟨M, hM, rfl⟩ := cls_surj β
  have hMa : AbDual.IsAdditive M := (AbDual.isAdditive_iff hM).2 fun Y a a' t => hadd Y a a' t
  obtain ⟨x, hx, hu⟩ := hP.univ T.X M hM hMa
  have hE : (AbDual.ev P (fst A.X T.X) (snd A.X T.X ≫ x)).IsLB := pull_isLB hP.isLB _
  have c : cls M hM = AbDual.evc hP.isLB (fst A.X T.X) (snd A.X T.X ≫ x) := (cls_eq_iff hM hE).2 hx
  have Kx : ∀ (Y : Over (Sp K)) (a : Y ⟶ A.X) (t : Y ⟶ T.X),
      AbDual.evc hP.isLB a (t ≫ x) = AbDual.evc hM a t := by
    intro Y a t
    have k := AbDual.evc_ev hP.isLB (fst A.X T.X) (snd A.X T.X ≫ x) hE a t
    rw [lift_fst, lift_snd_assoc] at k
    rw [← k]
    unfold AbDual.evc
    rw [c]
    rfl
  have h1 := (AbDual.triv_ev_iff hM (𝟙 A.X) (1 : A.X ⟶ T.X)).2 h0
  have u : snd A.X (𝟙_ (Over (Sp K))) ≫ (η[T.X] : 𝟙_ (Over (Sp K)) ⟶ T.X) = 1 := by
    show _ = toUnit _ ≫ η
    rw [toUnit_unique (snd A.X (𝟙_ (Over (Sp K)))) (toUnit _)]
  have e1 : η[T.X] ≫ x = 1 := by
    apply hP.eq_one
    rw [AbDual.triv_ev_iff hP.isLB, ← Category.assoc, Kx, u, AbDual.evc_one_right hM h1]
  have hpt : η[T.X] ≫ x = η[A'.X] := by
    rw [e1]
    show toUnit _ ≫ η = η
    rw [toUnit_unique (toUnit (𝟙_ (Over (Sp K)))) (𝟙 _), Category.id_comp]
  have hmon : IsMonHom x := rigidity_holds (Sp K) T.X A'.X T.ab A'.ab x hpt
  refine ⟨Hom.mk x, c, fun ψ hψ => ?_⟩
  have hE' : (AbDual.ev P (fst A.X T.X) (snd A.X T.X ≫ ψ.hom)).IsLB := pull_isLB hP.isLB _
  have hψ' : LBIso M (AbDual.ev P (fst A.X T.X) (snd A.X T.X ≫ ψ.hom)) := (cls_eq_iff hM hE').1 hψ
  exact hom_ext (hu ψ.hom hψ')

end GlobalTheory.AV.FamHom
