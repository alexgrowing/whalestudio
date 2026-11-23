import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqZeroOfThickeningsOfSection
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfSumMulCoord
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkMapInjectiveOfFlat

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.WeightTwo

theorem exists_sec_finsum {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {I : Type} (s : Finset I) (d : I → LB.Sec (LB.LinComb L φ ε)) :
    ∃ t : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval t r z J = ∑ i ∈ s, sval (d i) r z J := by
  refine ⟨⟨fun j => ∑ i ∈ s, (d i).f j, fun j j' => ?_⟩, fun Z r z J hJ => ?_⟩
  · rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (d i).compat j j'
  · exact DVR.gs_fsum r z _ (hJ.mem φ r) _ _

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem formEq_cancel (k l : ℕ) (α β : D.X) :
    FormEq (Sum.elim (fun a => (D.P.A ◁ g.pG).left ≫ Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB α i)
        (fun i => (snd D.P.A D.P.A).left ≫ D.famφB β i) a)
        (fun a => (snd D.P.A ((Over.map (thick R I e)).obj (thickObj R I e G))).left ≫ D.Oφ g.pG β a))
      (Sum.elim (Sum.elim (DegPre.famε k) (DegPre.famε l)) Oinvε)
      (Sum.elim (fun i => (fst D.P.A ((Over.map (thick R I e)).obj (thickObj R I e G))).left ≫ D.famφB α i)
        (fun _ : Unit => (snd D.P.A _ ≫ g.pG).left))
      (Sum.elim (DegPre.famε k) (fun _ => (l : ℤ))) := by
  intro U _ h
  have e₁ : (D.P.A ◁ g.pG).left ≫ (fst D.P.A D.P.A).left = (fst D.P.A _).left := by
    rw [← Over.comp_left, whiskerLeft_fst]
  have e₂ : (D.P.A ◁ g.pG).left ≫ (snd D.P.A D.P.A).left = (snd D.P.A _).left ≫ g.pG.left := by
    rw [← Over.comp_left, whiskerLeft_snd, Over.comp_left]
  have f₀ : g.pG.left ≫ D.famφB β 0 = g.pG.left := Category.comp_id _
  have f₁ : g.pG.left ≫ D.famφB β 1 = D.Oφ g.pG β 0 := by
    change (g.pG ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c β)).left = (padd D.P.A g.pG (toUnit _ ≫ D.c β)).left
    congr 1
    simp only [padd, comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
  have f₂ : g.pG.left ≫ D.famφB β 2 = D.Oφ g.pG β 1 := by
    change (g.pG ≫ toUnit _ ≫ D.c β).left = (toUnit _ ≫ D.c β).left
    rw [comp_toUnit_assoc]
  have f₃ : g.pG.left ≫ D.famφB β 3 = D.Oφ g.pG β 3 := by
    change (g.pG ≫ toUnit _ ≫ η[D.P.A]).left = (toUnit _ ≫ η[D.P.A]).left
    rw [comp_toUnit_assoc]
  have f₄ : D.Oφ g.pG β 2 = g.pG.left := rfl
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, reassoc_of% e₁, reassoc_of% e₂,
    Finset.univ_unique, Finset.prod_singleton]
  rw [_root_.mul_assoc]
  congr 1
  rw [Fin.prod_univ_four, Fin.prod_univ_four, f₀, f₁, f₂, f₃, f₄, Over.comp_left _ _ _ (snd D.P.A _) g.pG]
  generalize h (_ ≫ g.pG.left) = a
  generalize h (_ ≫ D.Oφ g.pG β 0) = b
  generalize h (_ ≫ D.Oφ g.pG β 1) = c
  generalize h (_ ≫ D.Oφ g.pG β 3) = d
  change a ^ ((l : ℤ) - 1) * b ^ (1 : ℤ) * c ^ (-1 : ℤ) * d ^ (1 : ℤ) *
    (b ^ (-1 : ℤ) * c ^ (1 : ℤ) * a ^ (1 : ℤ) * d ^ (-1 : ℤ)) = a ^ (l : ℤ)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

theorem level (k l : ℕ) (d : ∀ p : D.X × D.X, LB.Sec (LB.LinComb D.P.L (K := Fin 4 ⊕ Fin 4)
      (Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB p.1 i) (fun i => (snd D.P.A D.P.A).left ≫ D.famφB p.2 i))
      (Sum.elim (DegPre.famε k) (DegPre.famε l)))) (s : Finset D.X)
    (H : ∀ (T : Over (Spec (CommRingCat.of R))) (x y : T ⟶ D.P.A) (xe ye : T.left ⟶ (thickObj R I e G).left),
      xe ≫ g.pG.left = x.left → ye ≫ g.pG.left = y.left →
      xe ≫ (thickObj R I e G).hom = ye ≫ (thickObj R I e G).hom → ∀ (z : T.left) (J), Good D.P.L z J →
      ∑ α ∈ s, ∑ β ∈ s, sval (d (α, β)) (lift x y).left z J *
        ((val (g.t α) xe z J).val * (val (g.t β) ye z J).val) = 0)
    (α : D.X) (hα : α ∈ s) (β : D.X) (hβ : β ∈ s) (Z : Scheme.{0}) (r : Z ⟶ (D.P.A ⊗ D.P.A).left)
    (hr : ∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ (D.P.A ⊗ D.P.A).hom)
    (z : Z) (J) (hJ : Good D.P.L z J) : sval (d (α, β)) r z J = 0 := by
  let Ge := (Over.map (thick R I e)).obj (thickObj R I e G)
  have hcl : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have ex : ∀ α : D.X, ∃ t : LB.Sec (LB.LinComb D.P.L
      (Sum.elim (fun i => (fst D.P.A Ge).left ≫ D.famφB α i) (fun _ : Unit => (snd D.P.A Ge ≫ g.pG).left))
      (Sum.elim (DegPre.famε k) (fun _ => (l : ℤ)))), ∀ (Z : Scheme.{0}) (r : Z ⟶ (D.P.A ⊗ Ge).left) (z : Z) (J),
      Good D.P.L z J → sval t r z J = ∑ β ∈ s, sval (d (α, β)) (r ≫ (D.P.A ◁ g.pG).left) z J *
        (val (g.t β) (r ≫ (snd D.P.A Ge).left) z J).val := by
    intro α
    choose u hu using fun β : D.X => exists_sec D.P.isLB (formEq_cancel g k l α β)
      (pullMulSec (d (α, β)) (D.P.A ◁ g.pG).left (LB.pullGen D.P.L _ _ (g.t β) (snd D.P.A Ge).left)
        (DVR.pullGen_isGen D.P.L _ _ _ (g.t_gen β) _))
    obtain ⟨t, ht⟩ := exists_sec_finsum s u
    refine ⟨t, fun Z r z J hJ => (ht Z r z J hJ).trans (Finset.sum_congr rfl fun β _ => ?_)⟩
    rw [hu β Z r z J hJ, sval_pullMulSec _ _ _ _ r z hJ, val_pull hJ]
  choose t ht using ex
  have h₁ := sval_eq_zero_of_sum_mul_coord R I D e G g (D.P.A ⊗ Ge) (fst _ _) _ _ _ t s (by
    intro Z x r hx z J hJ
    let r' : Over.mk (r ≫ (D.P.A ⊗ Ge).hom) ⟶ D.P.A ⊗ Ge := Over.homMk r rfl
    have E := H _ (r' ≫ fst _ _) (r' ≫ snd _ _ ≫ g.pG) x (r ≫ (snd D.P.A Ge).left) hx.symm
      (Category.assoc _ _ _) (by
        rw [← cancel_mono (thick R I e), Category.assoc, Category.assoc, Category.assoc]
        have w₁ : g.pG.left ≫ D.P.A.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w g.pG
        have w₂ : (snd D.P.A Ge).left ≫ (thickObj R I e G).hom ≫ thick R I e = (D.P.A ⊗ Ge).hom :=
          Over.w (snd D.P.A Ge)
        rw [w₂, ← w₁, ← Category.assoc, ← hx, Category.assoc, Over.w]) z J hJ
    have e₁ : lift (r' ≫ fst _ _) (r' ≫ snd _ _ ≫ g.pG) = r' ≫ D.P.A ◁ g.pG := by
      ext1 <;> simp
    rw [e₁] at E
    refine Eq.trans (Finset.sum_congr rfl fun α _ => ?_) E
    rw [ht α Z r z J hJ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [_root_.mul_assoc, mul_comm (val (g.t β) _ z J).val]
    rfl) α hα
  have h₂ := LiftTest.main R I D e G g (D.P.A ⊗ Ge) (fst _ _) _ D.P.L D.P.isLB _ _ _ (t α) h₁
  have h₃ := sval_eq_zero_of_sum_mul_coord R I D e G g (D.P.A ⊗ D.P.A) (snd _ _) _
    (fun β => Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB α i)
      (fun i => (snd D.P.A D.P.A).left ≫ D.famφB β i)) _ (fun β => d (α, β)) s (by
    intro Z y r hy z J hJ
    let r' : Over.mk (r ≫ (D.P.A ⊗ D.P.A).hom) ⟶ D.P.A ⊗ D.P.A := Over.homMk r rfl
    let y' : Over.mk (r ≫ (D.P.A ⊗ D.P.A).hom) ⟶ Ge := Over.homMk y (by
      change y ≫ Ge.hom = r ≫ (D.P.A ⊗ D.P.A).hom
      rw [← Over.w g.pG, ← Category.assoc, ← hy, Category.assoc, Over.w])
    have hy' : r' ≫ snd _ _ = y' ≫ g.pG := Over.OverMorphism.ext hy
    have e₁ : lift (r' ≫ fst _ _) y' ≫ D.P.A ◁ g.pG = r' := by
      ext1
      · simp
      · rw [hy', Category.assoc, whiskerLeft_snd, lift_snd_assoc]
    have e₂ : (lift (r' ≫ fst _ _) y').left ≫ (D.P.A ◁ g.pG).left = r := congrArg CommaMorphism.left e₁
    have e₃ : (lift (r' ≫ fst _ _) y').left ≫ (snd D.P.A Ge).left = y :=
      congrArg CommaMorphism.left (lift_snd (r' ≫ fst _ _) y')
    have E := h₂ Z (lift (r' ≫ fst _ _) y').left ⟨y ≫ (thickObj R I e G).hom, by
      rw [Over.w, Category.assoc]
      exact Over.w y'⟩ z J hJ
    rw [ht α _ _ z J hJ, e₂, e₃] at E
    exact E) β hβ
  exact LiftTest.main R I D e G g (D.P.A ⊗ D.P.A) (snd _ _) _ D.P.L D.P.isLB _ _ _ (d (α, β)) h₃ Z r hr z J hJ

theorem main : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (k l : ℕ) (d : ∀ p : D.X × D.X, LB.Sec (LB.LinComb D.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB p.1 i) (fun i => (snd D.P.A D.P.A).left ≫ D.famφB p.2 i)) (Sum.elim (DegPre.famε k) (DegPre.famε l)))), (∀ e : ℕ, ∃ s₀ : Finset D.X, ∀ s : Finset D.X, s₀ ⊆ s → ∀ (T : Over (Spec (CommRingCat.of V))) (x y : T ⟶ D.P.A) (xe ye : T.left ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (U.gt e).pG.left = x.left → ye ≫ (U.gt e).pG.left = y.left → xe ≫ (thickObj V (IsLocalRing.maximalIdeal V) e G).hom = ye ≫ (thickObj V (IsLocalRing.maximalIdeal V) e G).hom → ∀ (z : T.left) (J), Good D.P.L z J → ∑ α ∈ s, ∑ β ∈ s, sval (d (α, β)) (lift x y).left z J * ((val ((U.gt e).t α) xe z J).val * (val ((U.gt e).t β) ye z J).val) = 0) → ∀ p j, (d p).f j = 0) := by
  classical
  intro V _ _ _ hV D A G _ _ U k l d H p j
  have := hV.1
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : Smooth (D.P.A ⊗ D.P.A).hom := inferInstanceAs (Smooth (pullback.fst D.P.A.hom D.P.A.hom ≫ D.P.A.hom))
  have : GeometricallyConnected (D.P.A ⊗ D.P.A).hom := by
    change GeometricallyConnected (pullback.fst D.P.A.hom D.P.A.hom ≫ D.P.A.hom)
    exact GeometricallyConnected.comp _ _
  refine sec_eq_zero_of_thickenings_of_section V (IsLocalRing.maximalIdeal V)
    (IsLocalRing.maximalIdeal_le_jacobson _) (D.P.A ⊗ D.P.A) (lift η[D.P.A] η[D.P.A]) _
    (DVR.linComb_isLB D.P.L D.P.isLB _ _) (d p) (fun e j => app_sec_eq_zero_of_sval D.P.isLB (d p) _ ?_ j) j
  obtain ⟨s₀, hs⟩ := H e
  exact level (U.gt e) k l d (insert p.1 (insert p.2 s₀))
    (hs _ ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _))) p.1 (Finset.mem_insert_self _ _) p.2
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) _ _
    ⟨pullback.snd _ _, pullback.condition.symm⟩

end GlobalTheory.WeightTwo
