import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsUUOver
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsOfCubeBundleGenerator
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVariety

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.ThMove
open GlobalTheory.TranslMove

theorem gs_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens) (h : q (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ q) z U a = (r.stalkMap z).hom (gs q (r z) U a) := by
  rw [← gs_pull r q z U h, gs_stalkMap r z _ h, gs_pull (𝟙 Y) q (r z) U h, Category.id_comp]

theorem sval_all {S : Scheme.{0}} {A T : Over S} {L : LB A.left} {k : ℤ} {s : LB.Sec (LPow A L k T)}
    {q : T.left ⟶ (T ⊗ A).left} {p : T.left ⟶ A.left}
    {e : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => p) (fun _ => k))} {c : Γ(T.left, ⊤)}
    (H : ∀ z J, Good L z J → sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s q z J =
      gs (𝟙 _) z ⊤ c * (val e (𝟙 _) z J).val) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s (r ≫ q) z J = gs r z ⊤ c * (val e r z J).val := by
  have hJ₀ : Good L (r z) (fun χ : T.left ⟶ A.left => J (r ≫ χ)) := fun χ => hJ (r ≫ χ)
  have a := congrArg (r.stalkMap z).hom (H (r z) _ hJ₀)
  rw [map_mul, ← gs_stalkMap r z ⊤ trivial] at a
  refine Eq.trans ?_ (a.trans (congrArg _ ?_))
  · rw [sval_of s (r ≫ q) z J (fun _ => J (r ≫ q ≫ (snd T A).left)) (fun _ => by rw [Category.assoc])]
    exact gs_comp r q z _ (hJ₀.mem _ q) _
  · have m := hJ.mem (fun _ : Fin 1 => p) r
    exact (congrArg _ (gs_unit (𝟙 _) (r z) _ m _).symm).trans ((gs_stalkMap r z _ m _).symm.trans (gs_unit r z _ m _))

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {P : PolAV S} {P' : PolAV S'} {φ : P'.A.left ⟶ P.A.left}
  {w : LB.Iso P'.L (P.L.pull φ)} {T : Over S} {T' : Over S'} {h : T'.left ⟶ T.left}
  {Ψ : (T' ⊗ P'.A).left ⟶ (T ⊗ P.A).left}

theorem secRel_of_thru (h₁ : Ψ ≫ (fst T P.A).left = (fst T' P'.A).left ≫ h)
    (h₂ : Ψ ≫ (snd T P.A).left = (snd T' P'.A).left ≫ φ) {k : ℕ} {s : LB.Sec (LPow P.A P.L (k : ℤ) T)}
    {s' : LB.Sec (LPow P'.A P'.L (k : ℤ) T')} (H : Thru w k h s s') : SecRel w Ψ s s' := by
  intro Z r z J J' hJ hJ'
  rw [zpow_natCast, Units.val_pow_eq_pow_val]
  exact H Z r (r ≫ Ψ) (by rw [Category.assoc, h₁]) (by rw [Category.assoc, h₂]) z J J' hJ hJ'

theorem secRel_unique {k : ℤ} {s : LB.Sec (LPow P.A P.L k T)} {a b : LB.Sec (LPow P'.A P'.L k T')}
    (ha : SecRel w Ψ s a) (hb : SecRel w Ψ s b) : a = b :=
  FieldBaseChange.sec_ext' P'.isLB (fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good_pt P.isLB y
    exact (Units.mul_right_inj _).1 ((ha _ _ y J J' hJ hJ').symm.trans (hb _ _ y J J' hJ hJ')))

theorem val_rigT_move {ρ ρ'} (R : RigPull P'.A P.A f φ w ρ' ρ) (hh : h ≫ T.hom = T'.hom ≫ f) (k : ℤ) (y : T'.left)
    {J J'} (hJ : Good P.L y J) (hJ' : Good P'.L y J') :
    val (rigT P.A P.L ρ T k) h y J =
      wv w y J J' (1 : T' ⟶ P'.A).left ^ k * val (rigT P'.A P'.L ρ' T' k) (𝟙 _) y J' := by
  rw [FrameMove.val_rigT _ _ _ hJ, FrameMove.val_rigT _ _ _ hJ', hh, Category.id_comp, ← mul_zpow]
  refine congrArg (· ^ k) ?_
  exact (val_move (fun _ => PolBaseChange.eSec_comm R.1) R.2.2.2 T'.hom hJ hJ').trans
    (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _)))

end

theorem thC_move : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (gam : FractionRing R →+* FractionRing R') (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing R'))) (ψ : A'.A.left ⟶ A.A.left) (ω : LB.Iso A'.L (A.L.pull ψ)) ρ ρ', RigPull A'.A A.A (spMap gam) ψ ω ρ' ρ → ∀ (F F' : Type) [Field F] [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F'] (σ : F →+* F'), (∀ x, σ (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R') F' (gam x)) → ∀ (m : ℕ) (th : SecA A F 1) (th' : SecA A' F' 1) (x : TFK (R := R) F ⟶ A.A) (x' : TFK (R := R') F' ⟶ A'.A) (t : SecA A F (m ^ 2)) (t' : SecA A' F' (m ^ 2)) (c : F), x'.left ≫ ψ = spMap σ ≫ x.left → Thru ω 1 (T' := TFK (R := R') F') (T := TFK (R := R) F) (spMap σ) th th' → Thru ω (m ^ 2) (T' := TFK (R := R') F') (T := TFK (R := R) F) (spMap σ) t t' → ThC A ρ m th x t c → ThC A' ρ' m th' x' t' (σ c) := by
  intro R R' _ _ _ _ gam A A' ψ ω ρ ρ' hR F F' _ _ _ _ σ _ m th th' x x' t t' c hx hth ht H
  obtain ⟨α, s₁, θ, gα, nα, tw, sl, ac, hv⟩ := H
  have gp := hR.1
  have hw := hR.2.1
  have := A'.isAb.comm
  replace hx : (spMap σ : (TFK (R := R') F').left ⟶ (TFK (R := R) F).left) ≫ x.left = x'.left ≫ ψ := hx.symm
  have hh := base_comm (x := x') (x₀ := x) gp hx
  obtain ⟨Ψ, h₁, h₂⟩ : ∃ Ψ : (TFK (R := R') F' ⊗ A'.A).left ⟶ (TFK (R := R) F ⊗ A.A).left,
      Ψ ≫ (fst _ A.A).left = (fst _ A'.A).left ≫ spMap σ ∧ Ψ ≫ (snd _ A.A).left = (snd _ A'.A).left ≫ ψ :=
    ⟨pullback.lift ((fst _ A'.A).left ≫ spMap σ) ((snd _ A'.A).left ≫ ψ) (by
      rw [Category.assoc, Category.assoc, hh, gp.1.w, ← Category.assoc, ← Category.assoc, Over.w, Over.w]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have h0 := pt_pow (x := x') (x₀ := x) gp hx 0
  rw [pow_zero, pow_zero] at h0
  have s₂ : (ptSecT A'.A (1 : TFK (R := R') F' ⟶ A'.A)).left ≫ (snd _ A'.A).left = (1 : TFK (R := R') F' ⟶ A'.A).left := by
    rw [← Over.comp_left, ptSecT, lift_snd]
  have s₃ : (ptSecT A'.A (1 : TFK (R := R') F' ⟶ A'.A)).left ≫ (snd _ A'.A ^ m).left =
      (1 : TFK (R := R') F' ⟶ A'.A).left := by
    rw [← Over.comp_left, FrameMove.comp_pow, ptSecT, lift_snd, one_pow]
  have e₀ : (ptSecT A'.A (1 : TFK (R := R') F' ⟶ A'.A)).left ≫ Ψ =
      spMap σ ≫ (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left := by
    refine FrameMove.prod_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, h₁, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, ptSecT, ptSecT,
        lift_fst, lift_fst, Over.id_left, Over.id_left, Category.id_comp]
      exact (Category.comp_id _).symm
    · rw [Category.assoc, Category.assoc, h₂, ← Category.assoc, s₂, ← Over.comp_left, ptSecT, lift_snd, h0]
  obtain ⟨α', gα', vα⟩ := exists_genRel A.isLB A'.isLB hw Ψ h₂ (pt_pow gp h₂ m) α gα
  obtain ⟨s₁', tw'⟩ := VVRank.exists_isTwistPull A'.A (ψ := mulT A'.A _ m) (hm := lift_snd _ _) A'.isLB gα' th'
  have R₁ := secRel_twist (lift_comm h₁ (pt_pow gp h₂ m) h₂) vα tw tw' (secRel_of_thru h₁ h₂ hth)
  obtain ⟨θ', sl', a⟩ := exists_symLift gp A.isLB A'.isLB hw h₁ h₂
    (fun θ => pt_pow_eq_one (AbLaw.FromCube.kerPow AbLaw.CubeAssembly.cube_and_sections.1) A' (m ^ 2) rfl θ) hx sl
  obtain ⟨u, ac', R₂⟩ := a _ _ _ ac R₁
  obtain rfl : u = t' := secRel_unique R₂ (secRel_of_thru h₁ h₂ ht)
  refine ⟨α', s₁', θ', gα', corr_of_val A'.isLB fun y J' hJ' => ?_, tw', sl', ac', fun y J' hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_good_pt A.isLB y
    have a₁ := vα _ (ptSecT A'.A (1 : TFK (R := R') F' ⟶ A'.A)).left y J J' hJ hJ'
    have a₂ := (val_pull hJ α _ (spMap σ)).symm.trans ((val_corr hJ nα (spMap σ)).trans
      (val_rigT_move hR hh _ y hJ hJ'))
    rw [e₀, a₂, s₂, s₃, ← zpow_add] at a₁
    rw [val_pull hJ', Category.id_comp]
    exact (mul_left_cancel a₁).symm
  · obtain ⟨J, hJ⟩ := exists_good_pt A.isLB y
    have a₁ := R₂ _ (ptSecT A'.A (1 : TFK (R := R') F' ⟶ A'.A)).left y J J' hJ hJ'
    have a₂ := (sval_all hv (spMap σ) y hJ).trans
      (congrArg (fun v => _ * Units.val v) (val_rigT_move hR hh _ y hJ hJ'))
    rw [Units.val_mul, mul_left_comm] at a₂
    rw [e₀, s₂] at a₁
    exact ((Units.mul_right_inj _).1 (a₁.symm.trans a₂)).trans (congrArg (· * _) (FrameMove.gs_spMap σ y c))

end GlobalTheory.OneBasis.ThMove
end
