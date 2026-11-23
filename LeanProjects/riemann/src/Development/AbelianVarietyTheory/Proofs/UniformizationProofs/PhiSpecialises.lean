import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdNeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PhiRelTransport

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace PhiSpec

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

section Base

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T : Over (Spec (CommRingCat.of R))}

def trT (m : T ⟶ D.P.A) : T ⊗ D.P.A ⟶ T ⊗ D.P.A :=
  lift (fst _ _) (padd D.P.A (snd _ _) (fst _ _ ≫ m))

theorem trT_fst (m : T ⟶ D.P.A) : trT D m ≫ fst _ _ = fst _ _ := lift_fst _ _

theorem trT_snd (m : T ⟶ D.P.A) : trT D m ≫ snd _ _ = snd _ _ * (fst _ _ ≫ m) := lift_snd _ _

def lineT (m : T ⟶ D.P.A) : Fin 2 → (T.left ⟶ D.P.A.left) := ![(1 : T ⟶ D.P.A).left, m.left]

def uT (k : ℕ) (α : D.X) (m : T ⟶ D.P.A) {T₁ : Over (Spec (CommRingCat.of R))} (ρ : T₁ ⟶ T ⊗ D.P.A)
    (z : T₁.left) (J : (T₁.left ⟶ D.P.A.left) → D.P.L.ι) : (T₁.left.presheaf.stalk z)ˣ :=
  cubN (th D z J) k (cP D T₁ α) (ρ ≫ fst _ _ ≫ m) (ρ ≫ snd _ _) *
    (th D z J (cP D T₁ α) (ρ ≫ snd _ _) (ρ ≫ fst _ _ ≫ m))⁻¹

theorem gen_uT (k : ℕ) (α α' : D.X) (m : T ⟶ D.P.A)
    (hα : cP D _ α' = cP D _ α * m ^ k) {K : Type} [Fintype K]
    {φ : K → (T.left ⟶ D.P.A.left)} {ε : K → ℤ}
    (vO : LB.Gen (LB.LinComb D.P.L φ ε)) (hvO : vO.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U), ∏ i, h (φ i) ^ ε i =
      (h (cP D _ α * m).left)⁻¹ * h (cP D _ α).left * h m.left * (h (1 : T ⟶ D.P.A).left)⁻¹ *
        (h m.left ^ k)⁻¹ * h (1 : T ⟶ D.P.A).left ^ k) :
    ∃ u : LB.Gen (LB.LinComb D.P.L (Sum.elim (fun i => (snd T D.P.A).left ≫ D.famφB α' i)
        (fun i => (trT D m ≫ snd _ _).left ≫ D.famφB α i)) (DegPre.deltaε k)), u.IsGen ∧
      ∀ (T₁ : Over (Spec (CommRingCat.of R))) (ρ : T₁ ⟶ T ⊗ D.P.A) (z : T₁.left) (J), Good D.P.L z J →
        val u ρ.left z J = uT D k α m ρ z J * val vO (ρ ≫ fst _ _).left z J := by
  let a : T ⊗ D.P.A ⟶ D.P.A := cP D _ α
  let mm : T ⊗ D.P.A ⟶ D.P.A := fst _ _ ≫ m
  let x : T ⊗ D.P.A ⟶ D.P.A := snd _ _
  have hα' : cP D (T ⊗ D.P.A) α' = a * mm ^ k := by
    rw [← comp_cP D (fst T D.P.A), hα]
    exact (map_mul (preHom (fst T D.P.A)) _ _).trans
      (congrArg₂ (· * ·) (comp_cP D _ α) (map_pow (preHom (fst T D.P.A)) _ _))
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub a mm x k
  obtain ⟨u₀, hu₀, vu₀⟩ := exists_gen D.P.isLB (φ' := Sum.elim (fun i => (snd T D.P.A).left ≫ D.famφB α' i)
      (fun i => (trT D m ≫ snd _ _).left ≫ D.famφB α i)) (ε' := DegPre.deltaε k) (fun U _ h => by
      have p₁ := prod_cub a x mm h
      have p₂ := hF U (fun q => h ((fst T D.P.A).left ≫ q))
      have p₃ := SectionScalarValuation.prod_famB D (snd T D.P.A) α' k h
      have p₄ := SectionScalarValuation.prod_famB D (trT D m ≫ snd _ _) α k h
      have q₁ : (fst T D.P.A).left ≫ (cP D _ α * m).left = (a * mm).left :=
        congrArg (fun q : T ⊗ D.P.A ⟶ D.P.A => q.left)
          ((MonObj.comp_mul (fst T D.P.A) (cP D _ α) m).trans
            (congrArg (· * mm) (comp_cP D (fst T D.P.A) α)))
      have q₂ : (fst T D.P.A).left ≫ (cP D _ α).left = a.left :=
        congrArg (fun q : T ⊗ D.P.A ⟶ D.P.A => q.left) (comp_cP D (fst T D.P.A) α)
      have q₃ : (fst T D.P.A).left ≫ (1 : T ⟶ D.P.A).left = (1 : T ⊗ D.P.A ⟶ D.P.A).left :=
        congrArg (fun q : T ⊗ D.P.A ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (fst T D.P.A))
      have q₄ : (fst T D.P.A).left ≫ m.left = mm.left := rfl
      rw [q₁, q₂, q₃, q₄] at p₂
      have c₁ : SectionScalarValuation.cQ D (T ⊗ D.P.A) α' = a * mm ^ k := hα'
      have c₂ : SectionScalarValuation.cQ D (T ⊗ D.P.A) α = a := rfl
      rw [c₁] at p₃
      rw [c₂] at p₄
      conv at p₄ => rhs; rw [trT_snd]
      refine Eq.trans (prod_sum₂ (K := Fin 8 ⊕ thK) (K' := K) (U := U) _
        (prod_sum₂ (K := Fin 8) (K' := thK) (U := U) _ rfl (prod_neg _ _ p₁)) p₂)
        (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)).symm)
      have r1 : x * (a * mm ^ k) = a * mm ^ k * x := mul_comm _ _
      have r2 : x * mm * a = a * x * mm := by rw [mul_comm, ← _root_.mul_assoc]
      have r3 : mm * x = x * mm := mul_comm _ _
      rw [r1, r2, r3]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, a, mm, x]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (LB.invGen D.P.L _ _
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift x mm)).left)))
      (LB.pullGen D.P.L _ _ vO (fst T D.P.A).left))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN (invGen_isGen _ _ _ _
      (pullGen_isGen _ _ _ _ D.cub.isGen _))) (pullGen_isGen _ _ _ _ hvO _))
  refine ⟨u₀, hu₀, fun T₁ ρ z J hJ => ?_⟩
  refine (vu₀ _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    ((congrArg₂ (· * ·) (vN T₁ ρ z J hJ) ((val_inv _ _).trans
      (congrArg (·⁻¹) (val_cub D.cub ρ hJ _ _ _)))).trans ?_)) (val_pull hJ _ _ _)))
  rw [uT, ← comp_cP D ρ α]

abbrev SecT (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (α : D.X) : Type :=
  LB.Sec (LB.LinComb D.P.L (fun i => (snd T D.P.A).left ≫ D.famφB α i) (DegPre.famε k))

variable {D}

def PhiT {k : ℕ} (y : D.X) (gp : GtPt D T) (w : LB.Gen (LB.LinComb D.P.L (lineT D gp.b) (DegPre.lineε k)))
    (g g₂ : ∀ α, SecT D T k α) : Prop :=
  ∀ (α β : D.X), α + y = β → ∀ (T₁ : Over (Spec (CommRingCat.of R))) (ρ : T₁ ⟶ T ⊗ D.P.A) (z : T₁.left) (J),
    Good D.P.L z J → sval (g₂ β) ρ.left z J = sval (g α) (ρ ≫ trT D gp.b).left z J *
      (uT D k α gp.b ρ z J * (val (gp.s α) (ρ ≫ fst _ _).left z J * val w (ρ ≫ fst _ _).left z J)).val

theorem exists_phiT {k : ℕ} (y : D.X) (gp : GtPt D T) (hy : cP D T y = gp.b ^ k)
    (w : LB.Gen (LB.LinComb D.P.L (lineT D gp.b) (DegPre.lineε k))) (hw : w.IsGen) (g : ∀ α, SecT D T k α) :
    ∃ g₂ : ∀ α, SecT D T k α, PhiT y gp w g g₂ := by
  have ex : ∀ β, ∃ t : SecT D T k β, ∀ α, α + y = β →
      ∀ (T₁ : Over (Spec (CommRingCat.of R))) (ρ : T₁ ⟶ T ⊗ D.P.A) (z : T₁.left) (J),
      Good D.P.L z J → sval t ρ.left z J = sval (g α) (ρ ≫ trT D gp.b).left z J *
        (uT D k α gp.b ρ z J * (val (gp.s α) (ρ ≫ fst _ _).left z J * val w (ρ ≫ fst _ _).left z J)).val := by
    intro β
    obtain ⟨α₀, rfl⟩ : ∃ α₀, α₀ + y = β := ⟨β - y, sub_add_cancel _ _⟩
    obtain ⟨u, hu, hv⟩ := gen_uT D k α₀ (α₀ + y) gp.b (by rw [cPoint_add, hy]) _
      (mulGen_isGen _ _ _ _ _ _ _ (gp.isGen α₀) hw) (fun U _ h => by
        refine (Fintype.prod_sum_type _).trans ?_
        rw [Fin.prod_univ_four, Fin.prod_univ_two]
        show h (cP D _ α₀ * gp.b).left ^ (-1 : ℤ) * h (cP D _ α₀).left ^ (1 : ℤ) * h gp.b.left ^ (1 : ℤ) *
          h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) *
          (h (1 : T ⟶ D.P.A).left ^ (k : ℤ) * h gp.b.left ^ (-(k : ℤ))) = _
        simp only [zpow_neg, zpow_one, zpow_natCast]
        ac_rfl)
    obtain ⟨t, ht⟩ := exists_sec D.P.isLB (φ' := fun i => (snd T D.P.A).left ≫ D.famφB (α₀ + y) i)
      (ε' := DegPre.famε k) (fun U _ h => by
        refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _
          (c := ∏ i, h ((trT D gp.b ≫ snd _ _).left ≫ D.famφB α₀ i) ^ DegPre.famε k i)
          (Finset.prod_congr rfl fun i _ => congrArg (fun q => h q ^ DegPre.famε k i) (Category.assoc _ _ _).symm)
          (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
            (c := ∏ i, h ((snd T D.P.A).left ≫ D.famφB (α₀ + y) i) ^ DegPre.famε k i) rfl (prod_neg _ _ rfl))) ?_
        exact (mul_comm _ _).trans (inv_mul_cancel_right _ _)) (pullMulSec (g α₀) (trT D gp.b).left u hu)
    refine ⟨t, fun α hα T₁ ρ z J hJ => ?_⟩
    obtain rfl : α = α₀ := add_right_cancel hα
    exact (ht _ _ z J hJ).trans ((sval_pullMulSec _ _ _ _ _ z hJ).trans
      (congrArg₂ (· * ·) rfl (congrArg Units.val ((hv T₁ ρ z J hJ).trans
        (congrArg₂ (· * ·) rfl (val_mul hJ _ _ _))))))
  choose t ht using ex
  exact ⟨t, fun α β h => ht β α h⟩

variable {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem generic_fibre {k : ℕ} (gp : GtPt D T) (ρ : TF (R := R) F ⟶ T) (p : QkPt D F k)
    (hp : GtPt.IsPullF F ρ.left gp p.g)
    (w : LB.Gen (LB.LinComb D.P.L (lineT D gp.b) (DegPre.lineε k)))
    (ν : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)))
    (hν : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) (J), Good D.P.L z J →
      val ν r z J = val w (r ≫ ρ.left) z J)
    (s s₂ : Fam D F k) (g g₂ : ∀ α, SecT D T k α) (H : PhiVal p ν s.s s₂.s) (HT : PhiT p.y gp w g g₂)
    (hs : ∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (s.s α)
      (fun i => (snd T D.P.A).left ≫ D.famφB α i) (DegPre.famε k) (g α) (ρ ▷ D.P.A).left 1) (β : D.X) :
    GeneratorPullback.SecScal D.P.L (DegPre.famφ D F β) (DegPre.famε k) (s₂.s β)
      (fun i => (snd T D.P.A).left ≫ D.famφB β i) (DegPre.famε k) (g₂ β) (ρ ▷ D.P.A).left 1 := by
  refine SectionScalarValuation.secScal_of_sval D.P.isLB fun y J hJ => ?_
  have hb : ρ ≫ gp.b = p.g.b := Over.OverMorphism.ext hp.1.symm
  have e₁ := H (β - p.y) β (sub_add_cancel _ _) _ (𝟙 _) y J hJ
  have e₂ := HT (β - p.y) β (sub_add_cancel _ _) _ (ρ ▷ D.P.A) y J hJ
  have e₃ := SectionScalarValuation.secScal_sval (hs (β - p.y)) (DegPre.trPt D F p.g.b).left y hJ
  have t : ρ ▷ D.P.A ≫ trT D gp.b = DegPre.trPt D F p.g.b ≫ ρ ▷ D.P.A := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, trT_fst, Category.assoc, whiskerRight_fst, ← Category.assoc, tr_fst]
    · rw [Category.assoc, trT_snd, MonObj.comp_mul, whiskerRight_snd, Category.assoc, whiskerRight_snd, tr_pr,
        ← Category.assoc, whiskerRight_fst, Category.assoc, hb]
  have u : uT D k (β - p.y) gp.b (ρ ▷ D.P.A) y J = uVal D F k (β - p.y) p.g.b (𝟙 _) y J := by
    rw [uVal_id, uT, ← Category.assoc, whiskerRight_fst, Category.assoc, hb, whiskerRight_snd]
  have v₁ := (val_corr hJ (hp.2 (β - p.y)) (fst (TF (R := R) F) D.P.A).left).trans (val_pull hJ _ _ _)
  have v₂ := hν _ (fst (TF (R := R) F) D.P.A).left y J hJ
  rw [t, u, whiskerRight_fst] at e₂
  rw [Category.id_comp, Category.id_comp, val_mul hJ, v₁, v₂, ← e₃] at e₁
  rw [Category.id_comp]
  exact e₂.trans e₁.symm

end Base

section Charts

variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {G : X' ⟶ X} {K : Type} [Fintype K]

theorem gs_of_charts {w : LB.Iso L' (L.pull G)} (hw : PGen w) {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {ε : K → ℤ}
    {h : Y' ⟶ Y} (hψ : ∀ k, φ' k ≫ G = h ≫ φ k) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L' φ' ε))
    (r : Z ⟶ Y') (z : Z) {p p' : K → L.ι} {q q' : K → L'.ι}
    (hp : ∀ k, G (φ' k (r z)) ∈ L.U (p k)) (hq : ∀ k, φ' k (r z) ∈ L'.U (q k))
    (hp' : ∀ k, G (φ' k (r z)) ∈ L.U (p' k)) (hq' : ∀ k, φ' k (r z) ∈ L'.U (q' k))
    (H : gs (r ≫ h) z (LB.wchart L φ p') (s.f p') =
      (∏ k, gw w (r ≫ φ' k) z (p' k) (q' k) ^ ε k).val * gs r z (LB.wchart L' φ' q') (s'.f q')) :
    gs (r ≫ h) z (LB.wchart L φ p) (s.f p) =
      (∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k).val * gs r z (LB.wchart L' φ' q) (s'.f q) := by
  have m : ∀ {p : K → L.ι}, (∀ k, G (φ' k (r z)) ∈ L.U (p k)) → (r ≫ h) z ∈ LB.wchart L φ p := fun hp =>
    Set.mem_iInter.2 fun k => by
      show φ k (h (r z)) ∈ L.U _
      rw [pt_eq hψ]; exact hp k
  have a := sec_trans s (r ≫ h) z (m hp) (m hp')
  have b := sec_trans s' r z (Set.mem_iInter.2 hq) (Set.mem_iInter.2 hq')
  have c := pw_trans hw φ' ε r z (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hp') (Set.mem_iInter.2 hq)
    (Set.mem_iInter.2 hq')
  have d : trF (fun k => φ' k ≫ G) ε r z p p' = trF φ ε (r ≫ h) z p p' :=
    Finset.prod_congr rfl fun k _ => by rw [Category.assoc, ← hψ k]
  rw [d] at c
  show _ = (pw w φ' ε r z p q).val * _
  rw [a, b, c, H]
  show _ * ((pw w φ' ε r z p' q').val * _) = _
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, mul_right_comm _ _ (trF φ' ε r z q q'),
    inv_mul_cancel_right]

end Charts

section Special

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} {T : Over (Spec (CommRingCat.of R))} {F : Type} [Field F] [Algebra (FractionRing R') F]
  (hD : IsPullDeg φ D D') {h : (TF (R := R') F).left ⟶ T.left} (hT : (TF (R := R') F).hom ≫ spMap φ = h ≫ T.hom)
  {Θ : (DegPre.BF D' F).left ⟶ (T ⊗ D.P.A).left}
  (hΘ₁ : Θ ≫ (fst T D.P.A).left = (fst (TF (R := R') F) D'.P.A).left ≫ h)
  (hΘ₂ : Θ ≫ (snd T D.P.A).left = (DegPre.prB D' F).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
  {T' : Over (Spec (CommRingCat.of R'))}

def liftB (ρ : T' ⟶ DegPre.BF D' F) : Over.mk (T'.hom ≫ spMap φ) ⟶ T ⊗ D.P.A :=
  Over.homMk (ρ.left ≫ Θ) (by
    show (ρ.left ≫ Θ) ≫ (T ⊗ D.P.A).hom = T'.hom ≫ spMap φ
    rw [← Over.w (fst T D.P.A), Category.assoc, ← Category.assoc Θ, hΘ₁, Category.assoc, ← hT, ← Over.w ρ,
      ← Over.w (fst (TF (R := R') F) D'.P.A)]
    simp only [Category.assoc])

theorem liftB_fst (ρ : T' ⟶ DegPre.BF D' F) :
    (liftB hT hΘ₁ ρ ≫ fst T D.P.A).left = (ρ ≫ fst (TF (R := R') F) D'.P.A).left ≫ h :=
  (Category.assoc _ _ _).trans ((congrArg (ρ.left ≫ ·) hΘ₁).trans (Category.assoc _ _ _).symm)

include hΘ₂ in
theorem liftB_pr (ρ : T' ⟶ DegPre.BF D' F) :
    liftB hT hΘ₁ ρ ≫ snd T D.P.A = pushHom (pull_grp hD) T' (ρ ≫ DegPre.prB D' F) :=
  Over.OverMorphism.ext ((Category.assoc _ _ _).trans ((congrArg (ρ.left ≫ ·) hΘ₂).trans (Category.assoc _ _ _).symm))

theorem liftB_pt (ρ : T' ⟶ DegPre.BF D' F) {b : T ⟶ D.P.A} {b' : TF (R := R') F ⟶ D'.P.A}
    (hb : b'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ b.left) :
    liftB hT hΘ₁ ρ ≫ fst T D.P.A ≫ b =
      pushHom (pull_grp hD) T' (ρ ≫ fst (TF (R := R') F) D'.P.A ≫ b') := by
  refine Over.OverMorphism.ext ?_
  show (liftB hT hΘ₁ ρ).left ≫ (fst T D.P.A).left ≫ b.left =
    (ρ.left ≫ (fst (TF (R := R') F) D'.P.A).left ≫ b'.left) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))
  rw [← Category.assoc, ← Over.comp_left, liftB_fst, Category.assoc, ← hb]
  simp only [Over.comp_left, Category.assoc]

include hΘ₂ in
theorem liftB_tr (ρ : T' ⟶ DegPre.BF D' F) {b : T ⟶ D.P.A} {b' : TF (R := R') F ⟶ D'.P.A}
    (hb : b'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ b.left) :
    liftB hT hΘ₁ ρ ≫ trT D b = liftB hT hΘ₁ (ρ ≫ DegPre.trPt D' F b') := by
  apply CartesianMonoidalCategory.hom_ext
  · refine Over.OverMorphism.ext ?_
    rw [Category.assoc, trT_fst, liftB_fst, liftB_fst, Category.assoc ρ, tr_fst]
  · refine Eq.trans ?_ (liftB_pr hD hT hΘ₁ hΘ₂ _).symm
    rw [Category.assoc, Category.assoc, trT_snd, tr_pr, MonObj.comp_mul, MonObj.comp_mul, map_mul,
      liftB_pr hD hT hΘ₁ hΘ₂, liftB_pt hD hT hΘ₁ ρ hb]

include hΘ₂ in
theorem liftB_fam (ρ : T' ⟶ DegPre.BF D' F) (x : D'.X) (κ : Fin 4) :
    (liftB hT hΘ₁ ρ).left ≫ (snd T D.P.A).left ≫ D.famφB (hD.xe x) κ =
      (ρ.left ≫ DegPre.famφ D' F x κ) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := by
  fin_cases κ
  · exact (congrArg ((liftB hT hΘ₁ ρ).left ≫ ·) (Category.comp_id _)).trans
      (congrArg (fun q => q.left) (liftB_pr hD hT hΘ₁ hΘ₂ ρ))
  · have e : liftB hT hΘ₁ ρ ≫ snd T D.P.A ≫ (𝟙 D.P.A * cP D _ (hD.xe x)) =
        pushHom (pull_grp hD) T' (ρ ≫ (DegPre.prB D' F * cP D' _ x)) := by
      rw [MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_mul, map_mul, comp_cP, comp_cP, comp_cP, PhiPull.push_cP,
        Category.comp_id, liftB_pr hD hT hΘ₁ hΘ₂]
    exact congrArg (fun q => q.left) e
  · have e : liftB hT hΘ₁ ρ ≫ snd T D.P.A ≫ cP D _ (hD.xe x) = pushHom (pull_grp hD) T' (ρ ≫ cP D' _ x) := by
      rw [comp_cP, comp_cP, comp_cP, PhiPull.push_cP]
    exact congrArg (fun q => q.left) e
  · have e : liftB hT hΘ₁ ρ ≫ snd T D.P.A ≫ (1 : D.P.A ⟶ D.P.A) =
        pushHom (pull_grp hD) T' (ρ ≫ (1 : DegPre.BF D' F ⟶ D'.P.A)) := by
      rw [MonObj.comp_one, MonObj.comp_one, MonObj.comp_one, map_one]
    exact congrArg (fun q => q.left) e

include hT hΘ₁ hΘ₂ in
theorem fam_comm (x : D'.X) (κ : Fin 4) : DegPre.famφ D' F x κ ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) =
    Θ ≫ (snd T D.P.A).left ≫ D.famφB (hD.xe x) κ := by
  have e := liftB_fam hD hT hΘ₁ hΘ₂ (𝟙 (DegPre.BF D' F)) x κ
  exact ((congrArg (· ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) (Category.id_comp _)).symm.trans e.symm).trans
    (congrArg (· ≫ (snd T D.P.A).left ≫ D.famφB (hD.xe x) κ) (Category.id_comp Θ))

variable (Θ) in

def SecMaps {k : ℕ} (x : D'.X) (s : SecT D T k (hD.xe x))
    (s' : LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' F x) (DegPre.famε k))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D' F).left) (z : Z) (p : Fin 4 → D.P.L.ι) (q : Fin 4 → D'.P.L.ι),
    (∀ κ, (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ((DegPre.famφ D' F x) κ (r z)) ∈ D.P.L.U (p κ)) →
    (∀ κ, (DegPre.famφ D' F x) κ (r z) ∈ D'.P.L.U (q κ)) →
    gs (r ≫ Θ) z (LB.wchart D.P.L (fun i => (snd T D.P.A).left ≫ D.famφB (hD.xe x) i) p) (s.f p) =
      (∏ κ, gw hD.w (r ≫ (DegPre.famφ D' F x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val *
        gs r z (LB.wchart D'.P.L (DegPre.famφ D' F x) q) (s'.f q)

include hΘ₂ in
theorem sval_rel {k : ℕ} (x : D'.X) (s : SecT D T k (hD.xe x))
    (s' : LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' F x) (DegPre.famε k))) (H : SecMaps hD Θ x s s')
    (ρ : T' ⟶ DegPre.BF D' F) {z : T'.left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J')
    (Ω : (T' ⟶ D'.P.A) → (T'.left.presheaf.stalk z)ˣ)
    (hΩ : Ω = fun x => gw hD.w x.left z (J (x.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (J' x.left)) :
    @Eq (T'.left.presheaf.stalk z) (sval s (liftB hT hΘ₁ ρ).left z J)
      ((Ω (ρ ≫ DegPre.prB D' F) ^ ((k : ℤ) - 1) * Ω (cP D' T' x * (ρ ≫ DegPre.prB D' F)) * (Ω (cP D' T' x))⁻¹ *
        Ω 1).val * sval s' ρ.left z J') := by
  subst hΩ
  have e := H _ ρ.left z (fun κ => J ((ρ.left ≫ DegPre.famφ D' F x κ) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))))
    (fun κ => J' (ρ.left ≫ DegPre.famφ D' F x κ)) (fun κ => hJ ((ρ.left ≫ DegPre.famφ D' F x κ) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))))
    (fun κ => hJ' (ρ.left ≫ DegPre.famφ D' F x κ))
  have p := prod_fam D' F ρ x k (fun q => gw hD.w q z (J (q ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (J' q))
  refine (sval_of s (liftB hT hΘ₁ ρ).left z J _ (fun κ => congrArg J (liftB_fam hD hT hΘ₁ hΘ₂ ρ x κ))).trans
    (e.trans ?_)
  exact congrArg₂ (· * ·) (congrArg Units.val p) rfl

include hΘ₂ in
theorem secMaps_of_sval {k : ℕ} (x : D'.X) (s : SecT D T k (hD.xe x))
    (s' : LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' F x) (DegPre.famε k)))
    (H : ∀ (T' : Over (Spec (CommRingCat.of R'))) (ρ : T' ⟶ DegPre.BF D' F) (z : T'.left) (J J'),
      Good D.P.L z J → Good D'.P.L z J' → ∀ (Ω : (T' ⟶ D'.P.A) → (T'.left.presheaf.stalk z)ˣ),
      (Ω = fun x => gw hD.w x.left z (J (x.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (J' x.left)) →
      @Eq (T'.left.presheaf.stalk z) (sval s (liftB hT hΘ₁ ρ).left z J)
      ((Ω (ρ ≫ DegPre.prB D' F) ^ ((k : ℤ) - 1) * Ω (cP D' T' x * (ρ ≫ DegPre.prB D' F)) * (Ω (cP D' T' x))⁻¹ *
        Ω 1).val * sval s' ρ.left z J')) : SecMaps hD Θ x s s' := by
  intro Z r z p q hp hq
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB z
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
  let ρ : Over.mk (r ≫ (DegPre.BF D' F).hom) ⟶ DegPre.BF D' F := Over.homMk r rfl
  have e := H _ ρ z J J' hJ hJ' _ rfl
  have pr := prod_fam D' F ρ x k (fun q => gw hD.w q z (J (q ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (J' q))
  refine gs_of_charts ((isGen_iff hD.w).1 hD.w_gen) (fam_comm hD hT hΘ₁ hΘ₂ x) s s' r z hp hq
    (p' := fun κ => J ((r ≫ DegPre.famφ D' F x κ) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (q' := fun κ => J' (r ≫ DegPre.famφ D' F x κ))
    (fun κ => hJ ((r ≫ DegPre.famφ D' F x κ) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (fun κ => hJ' (r ≫ DegPre.famφ D' F x κ)) ?_
  refine (sval_of s (liftB hT hΘ₁ ρ).left z J _
    (fun κ => congrArg J (liftB_fam hD hT hΘ₁ hΘ₂ ρ x κ))).symm.trans (e.trans ?_)
  exact congrArg₂ (· * ·) (congrArg Units.val pr.symm) rfl

include hT in
theorem gt_comm {b : T ⟶ D.P.A} {b' : TF (R := R') F ⟶ D'.P.A} (hb : b'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ b.left) (x : D'.X) (i : Fin 4) :
    DegPre.gtφ D' F b' x i ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ DegPre.gtφT D T b (hD.xe x) i := by
  let η₀ : Over.mk ((TF (R := R') F).hom ≫ spMap φ) ⟶ T := Over.homMk h hT.symm
  have eb : pushHom (pull_grp hD) _ b' = η₀ ≫ b := Over.OverMorphism.ext hb
  have ec : pushHom (pull_grp hD) _ (cP D' (TF (R := R') F) x) = η₀ ≫ cP D T (hD.xe x) := by
    rw [PhiPull.push_cP, comp_cP]
  fin_cases i
  · have e : pushHom (pull_grp hD) _ (cP D' (TF (R := R') F) x * b') = η₀ ≫ (cP D T (hD.xe x) * b) := by
      rw [map_mul, eb, ec, MonObj.comp_mul]
    exact congrArg (fun q => q.left) e
  · exact congrArg (fun q => q.left) ec
  · exact hb
  · have e : pushHom (pull_grp hD) _ (1 : TF (R := R') F ⟶ D'.P.A) = η₀ ≫ (1 : T ⟶ D.P.A) := by
      rw [map_one, MonObj.comp_one]
    exact congrArg (fun q => q.left) e

include hT in
theorem line_comm {b : T ⟶ D.P.A} {b' : TF (R := R') F ⟶ D'.P.A} (hb : b'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ b.left) (i : Fin 2) :
    DegPre.lineφ D' F b' i ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ lineT D b i := by
  fin_cases i
  · exact gt_comm hD hT hb 0 3
  · exact hb

set_option maxHeartbeats 1000000 in
include hT hΘ₁ hΘ₂ in
theorem special_fibre (hG : GlobalFnsSt) {k : ℕ} (y : D.X) (gp : GtPt D T) (p : QkPt D' F k)
    (hy : p.y = hD.xe.symm y) (hb : p.g.b.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ gp.b.left)
    (hg : ∀ χ, PMaps hD.w (DegPre.gtφ D' F p.g.b χ) (DegPre.gtφT D T gp.b (hD.xe χ)) DegPre.gtε (p.g.s χ)
      (gp.s (hD.xe χ)) h)
    (w : LB.Gen (LB.LinComb D.P.L (lineT D gp.b) (DegPre.lineε k)))
    (ν' : LB.Gen (LB.LinComb D'.P.L (DegPre.lineφ D' F p.g.b) (DegPre.lineε k)))
    (hν : PMaps hD.w (DegPre.lineφ D' F p.g.b) (lineT D gp.b) (DegPre.lineε k) ν' w h)
    (g g₂ : ∀ α, SecT D T k α) (s' s₂' : Fam D' F k)
    (H₁ : ∀ x, SecMaps hD Θ x (g (hD.xe x)) (s'.s x)) (HT : PhiT y gp w g g₂) (H : PhiVal p ν' s'.s s₂'.s)
    (β : D'.X) : SecMaps hD Θ β (g₂ (hD.xe β)) (s₂'.s β) := by
  obtain ⟨α, rfl⟩ : ∃ α, α + p.y = β := ⟨β - p.y, sub_add_cancel _ _⟩
  refine secMaps_of_sval hD hT hΘ₁ hΘ₂ _ _ _ fun T' ρ z J J' hJ hJ' Ω hΩ => ?_
  have e := HT (hD.xe α) (hD.xe (α + p.y)) (by rw [map_add, hy, AddEquiv.apply_symm_apply]) _ (liftB hT hΘ₁ ρ) z J hJ
  have e' := H α _ rfl T' ρ z J' hJ'
  have v₁ := sval_rel hD hT hΘ₁ hΘ₂ _ _ _ (H₁ α) (ρ ≫ DegPre.trPt D' F p.g.b) hJ hJ' Ω hΩ
  let σ : T' ⟶ TF (R := R') F := ρ ≫ fst _ _
  have m₁ : ρ ≫ fst (TF (R := R') F) D'.P.A ≫ p.g.b = σ ≫ p.g.b := (Category.assoc _ _ _).symm
  have cy : cP D' T' (α + p.y) = cP D' T' α * (σ ≫ p.g.b) ^ k := by
    rw [cPoint_add, ← comp_cP D' σ p.y, cPoint_y]
    exact congrArg _ (map_pow (preHom σ) _ _)
  have tp : (ρ ≫ DegPre.trPt D' F p.g.b) ≫ DegPre.prB D' F = (ρ ≫ DegPre.prB D' F) * (σ ≫ p.g.b) := by
    rw [Category.assoc, tr_pr, MonObj.comp_mul, m₁]
  rw [cy]
  rw [tp, ← liftB_tr hD hT hΘ₁ hΘ₂ ρ hb] at v₁
  have vu : @Eq (T'.left.presheaf.stalk z)ˣ (uT D k (hD.xe α) gp.b (liftB hT hΘ₁ ρ) z J)
      (cubN (th D (T := Over.mk (T'.hom ≫ spMap φ)) z J) k (pushHom (pull_grp hD) T' (cP D' T' α))
        (pushHom (pull_grp hD) T' (σ ≫ p.g.b)) (pushHom (pull_grp hD) T' (ρ ≫ DegPre.prB D' F)) *
      (th D (T := Over.mk (T'.hom ≫ spMap φ)) z J (pushHom (pull_grp hD) T' (cP D' T' α))
        (pushHom (pull_grp hD) T' (ρ ≫ DegPre.prB D' F)) (pushHom (pull_grp hD) T' (σ ≫ p.g.b)))⁻¹) := by
    rw [uT, liftB_pt hD hT hΘ₁ ρ hb, liftB_pr hD hT hΘ₁ hΘ₂, PhiPull.push_cP, m₁]
  have vg : @Eq (T'.left.presheaf.stalk z)ˣ (val (gp.s (hD.xe α)) (liftB hT hΘ₁ ρ ≫ fst _ _).left z J)
      ((Ω (cP D' T' α * (σ ≫ p.g.b)))⁻¹ * Ω (cP D' T' α) * Ω (σ ≫ p.g.b) * (Ω 1)⁻¹ *
        val (p.g.s α) σ.left z J') := by
    have c := DegPull.pmaps_val (gt_comm hD hT hb α) (hg α) σ.left z hJ hJ'
    have pr := prod_gt p.g.b α (fun q => gw hD.w (σ.left ≫ q) z (J ((σ.left ≫ q) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (J' (σ.left ≫ q)))
    rw [liftB_fst]
    refine c.trans (congrArg₂ (· * ·) (pr.trans ?_) rfl)
    rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul, comp_cP,
      MonObj.comp_one, hΩ]
  have vν : @Eq (T'.left.presheaf.stalk z)ˣ (val w (liftB hT hΘ₁ ρ ≫ fst _ _).left z J)
      (Ω 1 ^ (k : ℤ) * Ω (σ ≫ p.g.b) ^ (-(k : ℤ)) * val ν' σ.left z J') := by
    have c := DegPull.pmaps_val (line_comm hD hT hb) hν σ.left z hJ hJ'
    rw [liftB_fst]
    refine c.trans (congrArg₂ (· * ·) ((Fin.prod_univ_two _).trans ?_) rfl)
    have e₀ : σ.left ≫ DegPre.lineφ D' F p.g.b 0 = (1 : T' ⟶ D'.P.A).left :=
      congrArg (fun q : T' ⟶ D'.P.A => q.left) (MonObj.comp_one (M := D'.P.A) σ)
    have e₁ : σ.left ≫ DegPre.lineφ D' F p.g.b 1 = (σ ≫ p.g.b).left := rfl
    rw [e₀, e₁, hΩ]
    rfl
  have key := PhiPull.units_rel (pushHom (pull_grp hD) T') Ω (PhiPull.cub_rel hG hD hJ hJ' Ω hΩ) k (cP D' T' α)
    (σ ≫ p.g.b) (ρ ≫ DegPre.prB D' F) (val (p.g.s α) σ.left z J') (val ν' σ.left z J')
  have fin := e.trans (congrArg₂ (· * ·) v₁ (congrArg Units.val
    (congrArg₂ (· * ·) vu (congrArg₂ (· * ·) vg vν))))
  have alg : ∀ {S : Type} [CommRing S] (A₁ A₂ u u' : Sˣ) (a : S), A₁ * u = A₂ * u' →
      A₁.val * a * u.val = A₂.val * (a * u'.val) := by
    intro S _ A₁ A₂ u u' a h₁
    rw [mul_right_comm, ← Units.val_mul, h₁, Units.val_mul, _root_.mul_assoc, mul_comm a]
  rw [val_mul hJ', uVal, m₁] at e'
  refine fin.trans ((alg _ _ _ _ _ key).trans ?_)
  rw [e']

end Special

end PhiSpec

theorem phi_specialises : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre), ∀ (S : Type) [CommRing S] [IsDomain S] [ValuationRing S] (σ : R →+* S) (F : Type) [Field F] [Algebra (FractionRing R) F] (ιF : S →+* F), Function.Injective ιF → ∀ (ρ : TF (R := R) F ⟶ (Over.mk (specOf σ))), ρ.left = specOf ιF → ∀ (F' : Type) [Field F'] [Algebra (FractionRing R') F'] (π : S →+* F'), IsLocalHom π → (∀ r : R, π (σ r) = algebraMap (FractionRing R') F' (algebraMap R' (FractionRing R') (φ r))) → ∀ (Θ : (DegPre.BF D'.toPre F').left ⟶ ((Over.mk (specOf σ)) ⊗ D.toPre.P.A).left), Θ ≫ (fst (Over.mk (specOf σ)) D.toPre.P.A).left = (fst (TF (R := R') F') D'.toPre.P.A).left ≫ specOf π → Θ ≫ (snd (Over.mk (specOf σ)) D.toPre.P.A).left = (DegPre.prB D'.toPre F').left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) → ∀ (k : ℕ), 1 ≤ k → ∀ (gp : GtPt D.toPre (Over.mk (specOf σ))) (p₀ : QkPt D.toPre F k) (p₁ : QkPt D'.toPre F' k), GtPt.IsPullF F ρ.left gp p₀.g → p₁.y = hD.xe.symm p₀.y → p₁.g.b.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = specOf π ≫ gp.b.left → (∀ χ, Geo.Tor.PMaps hD.w (DegPre.gtφ D'.toPre F' p₁.g.b χ) (DegPre.gtφT D.toPre (Over.mk (specOf σ)) gp.b (hD.xe χ)) DegPre.gtε (p₁.g.s χ) (gp.s (hD.xe χ)) (specOf π)) → ∃ (ν : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₀.g.b) (DegPre.lineε k))) (ν' : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F' p₁.g.b) (DegPre.lineε k))), ν.IsGen ∧ ν'.IsGen ∧ ∀ (s : Fam D.toPre F k) (s' : Fam D'.toPre F' k) (g : ∀ α, LB.Sec (LB.LinComb D.toPre.P.L (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k))), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k) (g α) (ρ ▷ D.toPre.P.A).left 1) → (∀ (x : D'.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D'.toPre F').left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q : Fin 4 → D'.toPre.P.L.ι), (∀ κ, (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) ((DegPre.famφ D'.toPre F' x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (DegPre.famφ D'.toPre F' x) κ (r z) ∈ D'.toPre.P.L.U (q κ)) → Geo.Tor.gs (r ≫ Θ) z (LB.wchart D.toPre.P.L (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB (hD.xe x) i) p) ((g (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (DegPre.famφ D'.toPre F' x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.toPre.P.L (DegPre.famφ D'.toPre F' x) q) ((s'.s x).f q)) → ∃ (s₂ : Fam D.toPre F k) (s₂' : Fam D'.toPre F' k) (g₂ : ∀ α, LB.Sec (LB.LinComb D.toPre.P.L (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k))), PhiRel D.toPre F k p₀ ν s s₂ ∧ PhiRel D'.toPre F' k p₁ ν' s' s₂' ∧ (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s₂.s α) (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k) (g₂ α) (ρ ▷ D.toPre.P.A).left 1) ∧ (∀ (x : D'.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D'.toPre F').left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q : Fin 4 → D'.toPre.P.L.ι), (∀ κ, (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) ((DegPre.famφ D'.toPre F' x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (DegPre.famφ D'.toPre F' x) κ (r z) ∈ D'.toPre.P.L.U (q κ)) → Geo.Tor.gs (r ≫ Θ) z (LB.wchart D.toPre.P.L (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB (hD.xe x) i) p) ((g₂ (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (DegPre.famφ D'.toPre F' x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.toPre.P.L (DegPre.famφ D'.toPre F' x) q) ((s₂'.s x).f q)) := by
  intro hG R R' _ _ _ _ I I' φ D D' hD S _ _ _ σ F _ _ ιF hι ρ hρ F' _ _ π _ hπ Θ hΘ₁ hΘ₂ k _ gp p₀ p₁ hp hy hb hg
  have hT : (TF (R := R') F').hom ≫ Geo.Tor.spMap φ = specOf π ≫ (Over.mk (specOf σ)).hom :=
    (Category.assoc _ _ _).trans
      (((congrArg (jFK (R := R') F' ≫ ·) (Geo.Tor.spMap_comp φ _).symm).trans (Geo.Tor.spMap_comp _ _).symm).trans
        ((congrArg Geo.Tor.spMap (RingHom.ext fun r => (hπ r).symm)).trans (Geo.Tor.spMap_comp _ _)))
  have hb₀ : ρ ≫ gp.b = p₀.g.b := Over.OverMorphism.ext hp.1.symm
  have hk : DVR.cP D.toPre _ p₀.y = gp.b ^ k := by
    have : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
    have hd : IsDominant ρ.left := by
      rw [hρ]
      constructor
      exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical ιF).2
        (by rw [(RingHom.injective_iff_ker_eq_bot ιF).1 hι]; exact bot_le)
    have : IsReduced (Over.mk (specOf σ)).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of S)))
    have e : ρ ≫ DVR.cP D.toPre _ p₀.y = ρ ≫ gp.b ^ k := by
      rw [DVR.comp_cP, DVR.cPoint_y, ← hb₀]
      exact (map_pow (Geo.Tor.preHom ρ) _ _).symm
    exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated D.toPre.P.A.hom ((Over.w _).trans (Over.w _).symm)
      ρ.left (congrArg (fun q => q.left) e))
  obtain ⟨w, hw⟩ := DVR.exists_gen_of_local (V := S) D.toPre.P.L D.toPre.P.isLB (PhiSpec.lineT D.toPre gp.b)
    (DegPre.lineε k)
  obtain ⟨ν, hν, vν⟩ := Geo.Tor.exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F p₀.g.b)
    (ε' := DegPre.lineε k) (fun U _ h => Finset.prod_congr rfl fun i _ => congrArg (fun q => h q ^ DegPre.lineε k i) (by
      fin_cases i
      · exact congrArg (fun q : TF (R := R) F ⟶ D.toPre.P.A => q.left) (MonObj.comp_one (M := D.toPre.P.A) ρ)
      · exact hp.1.symm))
    (LB.pullGen D.toPre.P.L _ _ w ρ.left) (DVR.pullGen_isGen _ _ _ _ hw _)
  obtain ⟨ν', hν', pm⟩ := DegPull.exists_pmaps ((Geo.Tor.isGen_iff hD.w).1 hD.w_gen) D.toPre.P.isLB D'.toPre.P.isLB
    (specOf π) (PhiSpec.line_comm hD hT hb) w hw
  refine ⟨ν, ν', hν, hν', fun s s' g hs hs' => ?_⟩
  obtain ⟨s₂, H⟩ := DVR.exists_phi hG p₀ ν hν D.tau_bimult s
  obtain ⟨s₂', H'⟩ := DVR.exists_phi hG p₁ ν' hν' D'.tau_bimult s'
  obtain ⟨g₂, HT⟩ := PhiSpec.exists_phiT p₀.y gp hk w hw g
  exact ⟨s₂, s₂', g₂, (DVR.phiRel_iff hG p₀ ν hν _ _).2 H, (DVR.phiRel_iff hG p₁ ν' hν' _ _).2 H',
    PhiSpec.generic_fibre gp ρ p₀ hp w ν
      (fun Z r z J hJ => (vν Z r z J hJ).trans (Geo.Tor.val_pull hJ _ _ _)) s s₂ g g₂ H HT hs,
    PhiSpec.special_fibre hD hT hΘ₁ hΘ₂ hG p₀.y gp p₁ hy hb hg w ν' pm g g₂ s' s₂' hs' HT H'⟩

end GlobalTheory
