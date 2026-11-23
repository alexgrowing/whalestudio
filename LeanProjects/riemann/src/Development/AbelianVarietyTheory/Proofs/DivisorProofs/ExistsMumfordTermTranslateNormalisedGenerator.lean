import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.MumTerm

variable {X Y Z : Scheme.{0}}

theorem scal_spec {A B : Type} [CommRing A] [CommRing B] (q : Y ⟶ Sp B) (φ : A →+* B) (r : A) :
    scal q (φ r) = scal (q ≫ Spec.map (CommRingCat.ofHom φ)) r := by
  have e := congrArg (fun h => h.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [scal, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [e]

theorem gs_scal {A : Type} [CommRing A] (p : Z ⟶ Y) (q : Y ⟶ Sp A) (z : Z) (r : A) :
    gs p z ⊤ (scal q r) = gs (p ≫ q) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r) :=
  gs_pull p q z ⊤ trivial _

theorem exists_smul {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (a : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) : ∃ t : LB.Sec (LB.LinComb L φ ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval t r z J = gs r z ⊤ a * sval s r z J := by
  refine ⟨⟨fun i => (Y.presheaf.map (homOfLE le_top).op).hom a * s.f i, fun i j => ?_⟩, fun Z r z J hJ => ?_⟩
  · rw [map_mul, map_mul, s.compat i j, mul_left_comm]
    congr 2
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  · have hm := hJ.mem φ r
    exact (gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm a))

theorem exists_term : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X) (N : ℕ) (s₀ : SecT D.toPre a N (-1) 0) (ν : D.toPre.X) (u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a (shift h h' N (-1) ν)) (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c ν)).left ≫ tφ D.toPre a 0 k)) (dε N (-1)))), u₀.IsGen → ∀ ρ : R, (∀ u, IsFac D.toPre a h N (-1) ν 0 (shift h h' N (-1) ν) u → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → (val u x z J).val = gs x z ⊤ (scal ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left : (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) (algebraMap R (FractionRing R) ρ)) * (val u₀ (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J).val) → ∃ t : SecT D.toPre a N (-1) (shift h h' N (-1) ν), TRel h ν s₀ t ∧ ∀ e : ℕ, ρ ∈ maximalIdeal R ^ (e + 1) → Van (maximalIdeal R) t e := by
  intro R _ _ _ D a h h' N s₀ ν u₀ hu₀ ρ H
  obtain ⟨p, hp⟩ := exists_sec D.toPre.P.isLB (φ' := tφ D.toPre a (shift h h' N (-1) ν)) (ε' := tε N (-1))
    (fun U _ g => by
      simp only [Fintype.prod_sum_type, dε, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [mul_left_comm, mul_inv_cancel, _root_.mul_one])
    (pullMulSec s₀ (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c ν)).left u₀ hu₀)
  obtain ⟨t, ht⟩ := exists_smul (scal D.toPre.P.A.hom ρ) p
  refine ⟨t, fun u hu Z x z J hJ => ?_, fun e he Z x z J hJ => ?_⟩
  · have e₁ : (DegPre.prB D.toPre (FractionRing R)).left ≫ (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c ν)).left =
        (DegPre.trF D.toPre (FractionRing R) ν).left ≫ (DegPre.prB D.toPre (FractionRing R)).left := by
      rw [← Over.comp_left, ← Over.comp_left]
      congr 1
      simp only [DegPre.trF, padd, lift_snd]
      rw [← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit]
    have e₂ : (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom =
        ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left :
          (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) ≫ jK R := by
      have j : jFK (R := R) (FractionRing R) = 𝟙 _ := by
        simp [jFK]
      rw [Over.w]
      refine (Over.w (fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R))).symm.trans ?_
      congr 1
      show jFK (R := R) (FractionRing R) ≫ jK R = jK R
      rw [j, Category.id_comp]
    rw [ht _ _ z J hJ, hp _ _ z J hJ, sval_pullMulSec _ _ _ _ _ z hJ, H u hu Z x z J hJ, Category.assoc, e₁,
      scal_spec, gs_scal, gs_scal, Category.assoc, e₂, mul_left_comm]
  · rw [ht _ _ z J hJ, gs_scal, Category.assoc, pullback.condition, ← gs_scal, ← scal_spec,
      Ideal.Quotient.eq_zero_iff_mem.2 he]
    have : scal (pullback.snd D.toPre.P.A.hom (thick R (maximalIdeal R) e)) (0 : R ⧸ maximalIdeal R ^ (e + 1)) = 0 := by
      simp only [scal, map_zero]
    exact (congrArg (· * _) ((congrArg (gs x z ⊤) this).trans (DVR.gs_zero x z ⊤ trivial))).trans (zero_mul _)

end GlobalTheory.MumTerm
