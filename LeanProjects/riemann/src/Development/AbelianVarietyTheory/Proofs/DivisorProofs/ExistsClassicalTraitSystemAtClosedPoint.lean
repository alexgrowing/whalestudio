import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTraitCharacterGroupFinrankLeGenusThreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupClassicalTraitPeriodsBoundedBelowMaxIdStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.PreSys

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem rank_le (hn : 3 ≤ n) (T : Trait F) : Module.finrank ℤ T.D.toPre.X ≤ g := GlobalTheory.T.siegelTrait_characterGroup_finrank_le_genus_of_three_le g n F hn T

theorem lam (hE : IsE8 W) (hT : ThetaInt F W i) (X₁ : Setup F W i) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z)
    (hz : IsClosed ({z₁} : Set X₁.M.Z)) : ∃ C : ℝ, ∀ (c : CTrait X₁ p z₁) (x : c.T.D.toPre.X), x ≠ 0 →
      ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), Real.exp (-(C * (c.sc * c.T.β x x))) ≤ ‖c.val h‖ :=
  GlobalTheory.T.thetaSetup_classicalTraitPeriods_bounded_below_maxIdeal _ n F W Z i X₁ X₁.one_le X₁.three_le X₁.odd X₁.imm hE hT X₁.projM p z₁ hz

variable {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

def evC (c : CTrait X₁ p z₁) : X₁.M.Z.presheaf.stalk z₁ →+* PadicAlgCl p :=
  (RatModel.valHomOf (gPt p ≫ c.y) z₁ (RatModel.gPt_specializes c.cen)).comp (X₁.M.stalkEquiv z₁).toRingHom

theorem evC_apply (c : CTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : evC c a = c.val a := rfl

theorem norm_evC_le (c : CTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : ‖evC c a‖ ≤ 1 :=
  RatModel.norm_val_le_one c.cen (X₁.M.stalkEquiv z₁ a).2

theorem norm_evC_lt (c : CTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) (ha : a ∈ maximalIdeal _) :
    ‖evC c a‖ < 1 := by
  have h1 : ¬ IsUnit (X₁.M.stalkEquiv z₁ a) := fun hu => ha ((isUnit_map_iff (X₁.M.stalkEquiv z₁) a).1 hu)
  exact (RatModel.norm_val_lt_one_iff c.cen (X₁.M.stalkEquiv z₁ a).2).2 h1

theorem sc_pos (c : CTrait X₁ p z₁) : 0 < c.sc := by
  have hϖ0 : algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 c.T.irr.ne_zero
  have h0 : c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ) ≠ 0 := (map_ne_zero _).2 hϖ0
  have hlt : ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)‖ < 1 := by
    by_contra hge
    push_neg at hge
    have hinv : ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hge
    obtain ⟨w, hw⟩ := (c.int _).1 hinv
    apply c.T.irr.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨w, IsFractionRing.injective c.T.V (FractionRing c.T.V) ?_⟩
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hϖ0]
  unfold CTrait.sc
  have := Real.log_neg (norm_pos_iff.2 h0) hlt
  linarith

theorem beta_pos (c : CTrait X₁ p z₁) (x : c.T.D.toPre.X) (hx : x ≠ 0) : 0 < c.T.β x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal c.T.V).ne_top c.T.mono hx
  fin_cases j
  simpa using hj

end GlobalTheory.Poinc.PreSys

namespace GlobalTheory.Poinc.PreSys

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

variable (X₁ p) in

abbrev Key : Type := (Sp (OO p) ⟶ X₁.M.Z) × (Σ k : ℕ, (Fin k → ℤ) → (Fin k → ℤ) → ℝ)

def Rep (c : CTrait X₁ p z₁) (q : Key X₁ p) : Prop :=
  c.y = q.1 ∧ ∃ e : (Fin q.2.1 → ℤ) ≃ₗ[ℤ] c.T.D.toPre.X, ∀ u v, q.2.2 u v = c.sc * c.T.β (e u) (e v)

def coord (c : CTrait X₁ p z₁) : (Fin (Module.finrank ℤ c.T.D.toPre.X) → ℤ) ≃ₗ[ℤ] c.T.D.toPre.X :=
  (Module.finBasis ℤ c.T.D.toPre.X).equivFun.symm

def keyOf (c : CTrait X₁ p z₁) : Key X₁ p :=
  (c.y, ⟨Module.finrank ℤ c.T.D.toPre.X, fun u v => c.sc * c.T.β (coord c u) (coord c v)⟩)

theorem rep_keyOf (c : CTrait X₁ p z₁) : Rep c (keyOf c) := ⟨rfl, coord c, fun _ _ => rfl⟩

variable (X₁ p z₁) in

def Pts : Type := {q : Key X₁ p // ∃ c : CTrait X₁ p z₁, Rep c q}

noncomputable def pick (y : Pts X₁ p z₁) : CTrait X₁ p z₁ := Classical.choose y.2

theorem pick_rep (y : Pts X₁ p z₁) : Rep (pick y) y.1 := Classical.choose_spec y.2

variable (X₁ p z₁) in

noncomputable def sys : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁) where
  Y := Pts X₁ p z₁
  ev y := evC (pick y)
  ev_le y h := norm_evC_le _ h
  ev_lt y h hh := norm_evC_lt _ h hh
  X y := (pick y).T.D.toPre.X
  rank_le y := rank_le X₁.three_le _
  β y := (pick y).T.β
  bal y := ⟨(pick y).T.symm, fun a u v => by simp⟩
  pos y x hx := beta_pos _ x hx
  sc y := (pick y).sc
  sc_pos y := sc_pos _

theorem sys_matches : (sys X₁ p z₁ (g := g)).Matches := by
  intro c
  refine ⟨⟨keyOf c, c, rep_keyOf c⟩, fun a => ?_, ?_⟩
  · obtain ⟨hy, -⟩ := pick_rep ⟨keyOf c, c, rep_keyOf c⟩
    show evC _ a = c.val a
    rw [evC_apply]
    unfold CTrait.val
    rw [hy]
    rfl
  · obtain ⟨-, e', he'⟩ := pick_rep ⟨keyOf c, c, rep_keyOf c⟩
    have key : ∀ a b : (pick ⟨keyOf c, c, rep_keyOf c⟩).T.D.toPre.X,
        (pick ⟨keyOf c, c, rep_keyOf c⟩).sc * (pick ⟨keyOf c, c, rep_keyOf c⟩).T.β a b =
          c.sc * c.T.β (coord c (e'.symm a)) (coord c (e'.symm b)) := by
      intro a b
      have h := he' (e'.symm a) (e'.symm b)
      rw [e'.apply_symm_apply, e'.apply_symm_apply] at h
      exact h.symm
    exact ⟨e'.symm.trans (coord c), key⟩

theorem sys_lam (hE : IsE8 W) (hT : ThetaInt F W i) (hz : IsClosed ({z₁} : Set X₁.M.Z)) :
    (sys X₁ p z₁ (g := g)).abelian₂ := by
  obtain ⟨C, hC⟩ := lam hE hT X₁ p z₁ hz
  exact ⟨C, fun y x hx => by
    obtain ⟨h, hm, hle⟩ := hC (pick y) x hx
    exact ⟨h, hm, hle⟩⟩

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z),
    IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) →
      ∃ Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁), Φ.Matches ∧ Φ.abelian₂ ∧
        (∀ y, ∃ c : CTrait X₁ p z₁, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X,
          ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) := by
  intro g n F W Z i hE hT X₁ p _ z₁ hz
  exact ⟨sys X₁ p z₁, sys_matches, sys_lam hE hT hz, fun y => ⟨pick y, fun a => rfl, LinearEquiv.refl ℤ _,
    fun a b => rfl⟩⟩

end GlobalTheory.Poinc.PreSys
