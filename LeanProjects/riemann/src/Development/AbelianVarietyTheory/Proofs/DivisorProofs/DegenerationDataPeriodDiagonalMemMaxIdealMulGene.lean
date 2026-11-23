import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauDiagEqUnitMulPsiSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GsJKToOpenTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefiningDegenerationDataTauCoordinateUnit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DataPos

variable {V : Type} [CommRing V] [IsDomain V]

theorem lamPts_generic (D : DegPre V) (a b : D.X) (k : Fin 4) :
    lamPts (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b) k = jK V ≫ lamPts (D.c a) (D.c b) k := by
  have e : (toUnit (TK V)).left = jK V := GlobalTheory.Mum.UnitValuedLeadingSection.toUnit_TK_left V
  fin_cases k
  · show ((toUnit (TK V) ≫ D.c a) * (toUnit (TK V) ≫ D.c b)).left = jK V ≫ (D.c a * D.c b).left
    rw [← MonObj.comp_mul, Over.comp_left, e]
  · show (toUnit (TK V) ≫ D.c a).left = jK V ≫ (D.c a).left
    rw [Over.comp_left, e]
  · show (toUnit (TK V) ≫ D.c b).left = jK V ≫ (D.c b).left
    rw [Over.comp_left, e]
  · show (1 : TK V ⟶ D.P.A).left = jK V ≫ (1 : 𝟙_ _ ⟶ D.P.A).left
    rw [← e, ← Over.comp_left, MonObj.comp_one]

theorem lamPts_sec (D : DegPre V) (a b : D.X) (k : Fin 4) : lamPts (D.c a) (D.c b) k ≫ D.P.A.hom = 𝟙 _ := by
  fin_cases k <;> exact GlobalTheory.Mum.UnitValuedLeadingSection.left_comp_hom_unit _

theorem tau_diag_pos : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V))
    (y : D.toPre.X), y ≠ 0 → ∃ r ∈ maximalIdeal V, ∃ k : (FractionRing V)ˣ, (k : FractionRing V) = algebraMap V _ r ∧
      ∃ u : LB.Gen (LB.LinComb D.toPre.P.L (lamPts (D.toPre.c y) (D.toPre.c y)) negε),
        ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (TK V).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
          Good D.toPre.P.L z J → val (D.toPre.tau y y) ρ z J = gm ρ z ⊤ (unitOn k) * val u (ρ ≫ jK V) z J := by
  intro V _ _ _ D y hy
  obtain ⟨z₀⟩ : Nonempty (TK V).left := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J₀, hJ₀⟩ := GlobalTheory.Mum.UnitValuedLeadingSection.exists_topGood V D.toPre.P z₀
  obtain ⟨u₁, hu₁⟩ :=
    GlobalTheory.Mum.UnitValuedLeadingSection.tau_diag_eq_unit_mul_psi_sq V D.toPre D.tau_bimult D.psi_even z₀ J₀ hJ₀ y
  obtain ⟨r₀, hr₀, e₀⟩ :=
    (GlobalTheory.Mum.UnitValuedLeadingSection.psiIn_iff_val V D.toPre z₀ J₀ hJ₀ y (maximalIdeal V)).1 (D.psi_pos y hy)
  have hr : (u₁ : V) * r₀ ^ 2 ∈ maximalIdeal V :=
    Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hr₀ 2 two_pos)
  have eT : ((val (D.toPre.tau y y) (𝟙 _) z₀ J₀ : ((TK V).left.presheaf.stalk z₀)ˣ) : (TK V).left.presheaf.stalk z₀) =
      GlobalTheory.Mum.UnitValuedLeadingSection.thK V z₀ (algebraMap V _ ((u₁ : V) * r₀ ^ 2)) := by
    rw [hu₁, Units.val_mul, Units.val_pow_eq_pow_val, e₀, map_mul, map_mul, map_pow, map_pow]
    rfl
  have hr0 : algebraMap V (FractionRing V) ((u₁ : V) * r₀ ^ 2) ≠ 0 := by
    intro h
    have := (val (D.toPre.tau y y) (𝟙 _) z₀ J₀).ne_zero
    rw [eT, h, map_zero] at this
    exact this rfl
  refine ⟨_, hr, Units.mk0 _ hr0, rfl, ?_⟩

  set k : (FractionRing V)ˣ := Units.mk0 _ hr0 with hk
  set φV := lamPts (D.toPre.c y) (D.toPre.c y) with hφVdef
  set φK := lamPts (toUnit (TK V) ≫ D.toPre.c y) (toUnit (TK V) ≫ D.toPre.c y) with hφKdef
  have hφ : ∀ k, φK k = jK V ≫ φV k := lamPts_generic D.toPre y y
  let jst : Fin 4 → D.toPre.P.L.ι := fun k => J₀ (jK V ≫ φV k)
  have hint : ∀ k, φV k ⁻¹ᵁ D.toPre.P.L.U (jst k) = ⊤ := fun k => hJ₀.2 (φV k) (lamPts_sec D.toPre y y k)
  have htop : LB.wchart D.toPre.P.L φV jst = ⊤ := eq_top_iff.2 fun p _ => Set.mem_iInter.2 fun k => by
    have : p ∈ φV k ⁻¹ᵁ D.toPre.P.L.U (jst k) := by rw [hint k]; trivial
    exact this
  have htopK : LB.wchart D.toPre.P.L φK jst = ⊤ := eq_top_iff.2 fun p _ => Set.mem_iInter.2 fun k => by
    have : jK V p ∈ φV k ⁻¹ᵁ D.toPre.P.L.U (jst k) := by rw [hint k]; trivial
    show p ∈ (φK k).base ⁻¹' (D.toPre.P.L.U (jst k) : Set _)
    rw [hφ k]
    exact this
  have hle : ∀ j, LB.wchart D.toPre.P.L φV j ≤ LB.wchart D.toPre.P.L φV j ⊓ LB.wchart D.toPre.P.L φV jst :=
    fun j => le_inf le_rfl (by rw [htop]; exact le_top)
  let u : LB.Gen (LB.LinComb D.toPre.P.L φV negε) := ⟨fun j => res (hle j) ((LB.LinComb D.toPre.P.L φV negε).g j jst)⟩
  obtain ⟨t, htg, ht⟩ := GlobalTheory.PolDeg.Wit.exists_tau D.toPre y y

  have hkey : t.s jst = res le_top (unitOn k) := by
    refine unit_ext fun x hx => ?_
    obtain rfl : x = z₀ := Subsingleton.elim (α := PrimeSpectrum (FractionRing V)) x z₀
    refine Units.ext ?_
    rw [gm_res _ x _ hx]
    have e1 : gm (𝟙 _) x ((LB.LinComb D.toPre.P.L φK negε).U jst) (t.s jst) = val t (𝟙 _) x J₀ :=
      (val_of t (𝟙 _) x J₀ jst (fun k => by show J₀ (𝟙 _ ≫ φK k) = J₀ (jK V ≫ φV k); rw [Category.id_comp, hφ k])).symm
    rw [e1, ht _ _ x J₀ hJ₀.1, eT]
    have e2 := GlobalTheory.RefTauCoord.gm_unitOn (R := V) (RingHom.id (FractionRing V)) x k
    have e3 : spMap (RingHom.id (FractionRing V)) = 𝟙 _ := by
      show Spec.map (CommRingCat.ofHom (RingHom.id _)) = _
      rw [CommRingCat.ofHom_id, Spec.map_id]
    rw [e3] at e2
    exact e2.symm
  refine ⟨u, fun Z ρ z J hJ => ?_⟩
  have hmK : ρ z ∈ LB.wchart D.toPre.P.L φK jst := by rw [htopK]; trivial
  have hmV : (ρ ≫ jK V) z ∈ LB.wchart D.toPre.P.L φV jst := by rw [htop]; trivial
  have L1 : val (D.toPre.tau y y) ρ z J =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.trF φK negε ρ z (fun k => J (ρ ≫ φK k)) jst * gm ρ z ⊤ (unitOn k) := by
    rw [← ht Z ρ z J hJ]
    refine (gen_trans htg ρ z (hJ.mem φK ρ) hmK).trans ?_
    rw [hkey]
    exact congrArg (_ * ·) (gm_res _ z _ hmK _)
  have L2 : val u (ρ ≫ jK V) z J =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.trF φV negε (ρ ≫ jK V) z (fun k => J ((ρ ≫ jK V) ≫ φV k)) jst := by
    have hm := hJ.mem φV (ρ ≫ jK V)
    exact (gm_res _ z (hle _) hm _).trans (gm_linComb _ _ _ _ z _ _ hm hmV)
  have L3 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.trF φK negε ρ z (fun k => J (ρ ≫ φK k)) jst =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.trF φV negε (ρ ≫ jK V) z (fun k => J ((ρ ≫ jK V) ≫ φV k)) jst := by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.trF
    refine Finset.prod_congr rfl fun k _ => ?_
    have e : ρ ≫ φK k = (ρ ≫ jK V) ≫ φV k := by rw [hφ k, Category.assoc]
    have h : ∀ a b : Z ⟶ D.toPre.P.A.left, a = b →
        gm a z (D.toPre.P.L.U (J a) ⊓ D.toPre.P.L.U (jst k)) (D.toPre.P.L.g (J a) (jst k)) =
          gm b z (D.toPre.P.L.U (J b) ⊓ D.toPre.P.L.U (jst k)) (D.toPre.P.L.g (J b) (jst k)) := by
      rintro a b rfl; rfl
    exact congrArg (· ^ negε k) (h _ _ e)
  rw [L1, L2, L3, mul_comm]

end GlobalTheory.DataPos
