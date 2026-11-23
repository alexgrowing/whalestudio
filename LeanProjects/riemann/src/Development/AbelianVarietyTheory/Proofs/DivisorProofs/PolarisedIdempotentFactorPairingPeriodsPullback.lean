import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEndOfPadd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorPeriodsAtGeneratingPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCancelValuesMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCompValuesMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodsPulledDegenerationDataStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FactorTau

theorem lift_square {S S' : Scheme.{0}} {B C : Over S} {B₁ C₁ : Over S'} {β : B₁.left ⟶ B.left} {δ : C₁.left ⟶ C.left}
    {β₂ : (G2 B₁).left ⟶ (G2 B).left} {δ₂ : (G2 C₁).left ⟶ (G2 C).left} (hβ : IsSquare β β₂) (hδ : IsSquare δ δ₂)
    {u v : B ⟶ C} {u₁ v₁ : B₁ ⟶ C₁} (hu : u₁.left ≫ δ = β ≫ u.left) (hv : v₁.left ≫ δ = β ≫ v.left) :
    (lift (fst B₁ B₁ ≫ u₁) (snd B₁ B₁ ≫ v₁) : G2 B₁ ⟶ G2 C₁).left ≫ δ₂ =
      β₂ ≫ (lift (fst B B ≫ u) (snd B B ≫ v) : G2 B ⟶ G2 C).left := by
  apply pullback.hom_ext
  · show _ ≫ (fst C C).left = _ ≫ (fst C C).left
    rw [Category.assoc, hδ.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
      ← Over.comp_left, lift_fst, Over.comp_left, Over.comp_left, Category.assoc, hu, ← Category.assoc β₂,
      hβ.1, Category.assoc]
  · show _ ≫ (snd C C).left = _ ≫ (snd C C).left
    rw [Category.assoc, hδ.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
      ← Over.comp_left, lift_snd, Over.comp_left, Over.comp_left, Category.assoc, hv, ← Category.assoc β₂,
      hβ.2, Category.assoc]

theorem pair_square {S S' : Scheme.{0}} {f : S' ⟶ S} {B : Over S} {B₁ T : Over S'} {β : B₁.left ⟶ B.left}
    {β₂ : (G2 B₁).left ⟶ (G2 B).left} (hβ : IsSquare β β₂) {a b : 𝟙_ (Over S) ⟶ B} {a₁ b₁ : 𝟙_ (Over S') ⟶ B₁}
    (ha : a₁.left ≫ β = f ≫ a.left) (hb : b₁.left ≫ β = f ≫ b.left) :
    (lift (toUnit T ≫ a₁) (toUnit T ≫ b₁)).left ≫ β₂ = (T.hom ≫ f) ≫ (lift a b).left := by
  have hT : (toUnit T).left = T.hom := (Category.comp_id _).symm.trans (Over.w (toUnit T))
  apply pullback.hom_ext
  · show _ ≫ (fst B B).left = _ ≫ (fst B B).left
    rw [Category.assoc, hβ.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
      ← Over.comp_left, lift_fst, Over.comp_left, Category.assoc, ha, hT, Category.assoc]
  · show _ ≫ (snd B B).left = _ ≫ (snd B B).left
    rw [Category.assoc, hβ.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
      ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc, hb, hT, Category.assoc]

set_option maxHeartbeats 800000 in

theorem factor_tau_pull : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (D₀ : DegPre R) (F : PFactor Q D₀) (D₁ : DegPre V) (hD : IsPullDeg θ D₀ D₁) [Module F.O D₁.X] (o₁ : D₁.OAct F.O), (∀ (a : F.O) (y : D₁.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (o₁.onB.act a).left ≫ GlobalTheory.PsiEvenPull.proj hD = GlobalTheory.PsiEvenPull.proj hD ≫ (F.o.onB.act a).left) → ∀ (Q' : Data V) (ex : Q'.X ≃+ Q.X), PullData Q θ Q' ex → ∃ β : Q'.B.left ⟶ Q.B.left, IsGrpPullback Q'.B Q.B (spMap θ) β ∧ (∀ a, (Q'.c a).left ≫ β = spMap θ ≫ (Q.c (ex a)).left) ∧ ∀ (inc : Q'.B ⟶ D₁.P.A) (xi : Q'.X →+ D₁.X), inc.left ≫ GlobalTheory.PsiEvenPull.proj hD = β ≫ F.inc.left → (∀ y, hD.xe (xi y) = F.xi (ex y)) → (∀ y, D₁.c (xi y) = Q'.c y ≫ inc) → ∃ w : LB.Iso (abelian₂ Q'.B Q'.M.L) ((abelian₂ D₁.P.A D₁.P.L).pull (lift (fst Q'.B Q'.B ≫ inc) (snd Q'.B Q'.B ≫ inc ≫ o₁.onB.act F.f) : G2 Q'.B ⟶ G2 D₁.P.A).left), w.IsGen ∧ ∀ a b z J J', Good D₁.P.L z J → Good Q'.M.L z J' → val (Q'.tau a b) (𝟙 _) z J' = lamVal w (lift (toUnit (TK V) ≫ Q'.c a) (toUnit (TK V) ≫ Q'.c b)).left z J J' * val (D₁.tau (xi a) (F.f • xi b)) (𝟙 _) z J := by
  intro R V _ _ _ _ θ Q D₀ F D₁ hD _ o₁ hx ho Q' ex hQ
  obtain ⟨β, β₂, wP, gβ, sβ, hwP, hc, hτ⟩ := hQ
  refine ⟨β, gβ, hc, fun inc xi hi hxi hcx => ?_⟩
  letI := D₀.P.isAb.comm
  letI := D₁.P.isAb.comm
  obtain ⟨w₁₂, hw₁₂, v₁₂⟩ := GlobalTheory.T.mumfordBundleIso_comp_values_mul _ _ _ Q'.B Q.B D₀.P.A Q'.M.L Q.M.L D₀.P.L Q'.M.isLB Q.M.isLB D₀.P.isLB
    β₂ _ _ rfl F.w F.w_gen wP hwP
  obtain ⟨δ₂, w₀, sδ, hw₀, v₀⟩ := GlobalTheory.T.exists_periods_pulled_degeneration_data R V θ D₀ D₁ hD
  have hf : (inc ≫ o₁.onB.act F.f).left ≫ GlobalTheory.PsiEvenPull.proj hD = β ≫ (F.inc ≫ F.o.onB.act F.f).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ho, ← Category.assoc, hi, Category.assoc]
  obtain ⟨w, hw, vw⟩ := GlobalTheory.T.mumfordBundleIso_cancel_values_mul _ _ _ Q'.B D₁.P.A D₀.P.A Q'.M.L D₁.P.L D₀.P.L Q'.M.isLB D₁.P.isLB D₀.P.isLB
    _ δ₂ _ (lift_square sβ sδ hi hf) w₀ hw₀ w₁₂ hw₁₂
  refine ⟨w, hw, fun a b z J J' hJ hJ' => ?_⟩
  obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D₀.P.isLB z
  obtain ⟨JQ, hJQ⟩ := DegPull.exists_good' Q.M.isLB z
  obtain ⟨u, x, y, k, k', hu, hy, hk, hk', t₀, t₁⟩ := hτ a b
  have e₁ := t₁ z JQ J' hJQ hJ'
  have e₂ := GlobalTheory.T.idempotent_factor_periods_at_generating_point R V θ Q D₀ F hD.W hD.psiW hD.g hD.g_comm (ex a) (ex b) u x y k k' hu hy hk hk' t₀
    z J₀ JQ hJ₀ hJQ
  have e₃ := v₁₂ _ (lift (toUnit (TK V) ≫ Q'.c a) (toUnit (TK V) ≫ Q'.c b)).left z J' JQ J₀ hJ' hJQ hJ₀
  have e₄ := vw _ (lift (toUnit (TK V) ≫ Q'.c a) (toUnit (TK V) ≫ Q'.c b)).left z J' J J₀ hJ' hJ hJ₀
  have e₅ := v₀ (xi a) (F.f • xi b) z J₀ J hJ₀ hJ
  have hP := pair_square (T := TK V) sβ (hc a) (hc b)
  have hq : (lift (toUnit (TK V) ≫ Q'.c a) (toUnit (TK V) ≫ Q'.c b)).left ≫
      (lift (fst Q'.B Q'.B ≫ inc) (snd Q'.B Q'.B ≫ inc ≫ o₁.onB.act F.f) : G2 Q'.B ⟶ G2 D₁.P.A).left =
      (lift (toUnit (TK V) ≫ D₁.c (xi a)) (toUnit (TK V) ≫ D₁.c (F.f • xi b))).left := by
    rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, o₁.c_lin, hcx, hcx]
    simp only [Category.assoc]
  rw [hP] at e₃
  rw [hq] at e₄
  rw [hx, hxi, hxi] at e₅
  rw [e₁, e₅, mul_left_comm, ← _root_.mul_assoc (lamVal w _ z J J'), ← e₄, e₃, _root_.mul_assoc]
  exact congrArg _ e₂

end GlobalTheory.FactorTau

end
