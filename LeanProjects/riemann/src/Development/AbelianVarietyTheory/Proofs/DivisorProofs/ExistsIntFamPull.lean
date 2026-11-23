import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamOfIsPullDeg

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem PullB.vanMod {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} {hD : IsPullDeg φ D D'} {k : ℕ} {x : D'.X} {b : D.SecB k (hD.xe x)}
    {b' : D'.SecB k x} (H : PullB hD x b b') {I : Ideal R} {I' : Ideal R'} (hI : I ≤ I'.comap φ) {e : ℕ}
    (hb : VanMod I b e) : VanMod I' b' e := by
  have hle : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ :=
    (Ideal.pow_right_mono hI _).trans (Ideal.le_comap_pow φ _)
  have hw : (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ D.P.A.hom = D'.P.A.hom ≫ specOf φ :=
    (pull_grp hD).1.w
  have hc := ExpGTrans.famφB_pull hD x
  unfold PullB at H
  have ht : thick R' I' e ≫ specOf φ =
      spMap (Ideal.quotientMap (I' ^ (e + 1)) φ hle) ≫ thick R I e := by
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  obtain ⟨h, hh⟩ : ∃ h : pullback D'.P.A.hom (thick R' I' e) ⟶ pullback D.P.A.hom (thick R I e),
      h ≫ pullback.fst D.P.A.hom (thick R I e) = pullback.fst D'.P.A.hom (thick R' I' e) ≫
        hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) :=
    ⟨pullback.lift _ (pullback.snd D'.P.A.hom (thick R' I' e) ≫ spMap (Ideal.quotientMap (I' ^ (e + 1)) φ hle)) (by
      rw [Category.assoc, hw, ← Category.assoc, pullback.condition, Category.assoc, ht, Category.assoc]),
      pullback.lift_fst _ _ _⟩
  intro q
  refine fn_ext fun y hy => ?_
  choose p hp using fun κ => exists_chart D.P.isLB ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))
    (D'.famφB x κ (pullback.fst D'.P.A.hom (thick R' I' e) y)))
  have e₁ := H _ (pullback.fst D'.P.A.hom (thick R' I' e)) y p q hp (Set.mem_iInter.1 hy)
  have hm : pullback.fst D.P.A.hom (thick R I e) (h y) ∈ LB.wchart D.P.L (D.famφB (hD.xe x)) p :=
    Set.mem_iInter.2 fun κ => by
      have a : h ≫ pullback.fst D.P.A.hom (thick R I e) ≫ D.famφB (hD.xe x) κ =
          pullback.fst D'.P.A.hom (thick R' I' e) ≫ D'.famφB x κ ≫
            hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) := by
        rw [← Category.assoc, hh, Category.assoc, ← hc κ]
      exact (congrArg (fun m => m y ∈ D.P.L.U (p κ)) a).mpr (hp κ)
  have z₀ : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens), f y ∈ U → gs f y U 0 = 0 := fun f y U h => by
    rw [gs_eq f y U h, map_zero, map_zero]
  rw [← hh] at e₁
  have e₂ := (Units.mul_right_eq_zero _).1 (e₁.symm.trans ((gs_pull h _ y _ hm _).symm.trans
    ((congrArg (gs h y _) (hb p)).trans (z₀ h y _ hm))))
  exact ((gs_pull (𝟙 _) _ y _ hy _).trans ((congrArg (fun m => gs m y _ _) (Category.id_comp _)).trans e₂)).trans
    (z₀ _ y _ hy).symm

theorem exists_intFam_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W) (D' : DegData W (maximalIdeal W)) (hD : IsPullDeg φ D.toPre D'.toPre), Function.Injective φ → IsLocalHom φ → ∀ (k : ℕ) (F : IntFam (maximalIdeal R) D.toPre k), ∃ F' : IntFam (maximalIdeal W) D'.toPre k, ∀ x, PullB hD x (F.f (hD.xe x)) (F'.f x) := by
  intro R _ _ _ _ D W _ _ _ φ D' hD _ hl k F
  choose f' hf' using fun x => (SecPull.existsUnique_secPull _ _ _ _ _ _ _ D.toPre.P.isLB D'.toPre.P.isLB hD.w
    hD.w_gen (Fin 4) (D'.toPre.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k) _ (ExpGTrans.famφB_pull hD x)
    (F.f (hD.xe x))).exists
  have s₁ : scal (DegPre.BF D.toPre (FractionRing R)).hom 1 = 1 := by rw [scal, map_one, map_one]
  have s₂ : scal (DegPre.BF D'.toPre (FractionRing W)).hom 1 = 1 := by rw [scal, map_one, map_one]
  obtain ⟨E, hE⟩ := exists_fam_of_isPullDeg GlobalTheory.allSixLaws.1.globalFns R W φ D.toPre D'.toPre hD k F.F F.f f'
    (fun α => s₁ ▸ F.ext α) hf'
  have hI : maximalIdeal R ≤ (maximalIdeal W).comap φ := fun a ha => map_nonunit φ a ha
  refine ⟨{ F := E, f := f', ext := fun α => s₂.symm ▸ hE α, small := fun e => ?_ }, hf'⟩
  exact ((F.small e).preimage hD.xe.injective.injOn).subset fun x hx hv => hx (PullB.vanMod (hf' x) hI hv)

end GlobalTheory.Mum
