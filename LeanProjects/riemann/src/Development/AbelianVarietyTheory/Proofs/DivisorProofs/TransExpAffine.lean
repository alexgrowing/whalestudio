import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConstMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTermsTorusTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFramesSectionValuesRatioRootOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootOfUnityFractionFieldMemberEqZetaPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedMemberDividingThetaConstantNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemberTermsIntegralUnitShiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusTorsionPointOfLabelOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberTorsionPointsAdditiveLabelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidificationMatchingFramesTorsionFramesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTranslateLiesOverProductTorsionFraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionPointTorusExtensionEqOfLiesOverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionTorusExtensionRespectCubicalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaFrameCubeConstantRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyTermsEqUpToNormalisingThetaConstStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section
namespace GlobalTheory.Poinc.Sep.TransAff
open GlobalTheory.UT.CoefBasic GlobalTheory.UT.TorsionValue GlobalTheory.Poinc.Sep.TermsExt GlobalTheory.Poinc.Tors

theorem ratio_pow {V : Type} [CommRing V] [IsDomain V] {A : PolAV (Sp (FractionRing V))}
    {ρA : LB.Gen (A.L.pull (eSec A.A))} {N : ℕ} {x : TFK (R := V) (FractionRing V) ⟶ A.A} {e e' : FrAt x}
    (H : IsTorsFrame A ρA N x e) (H' : IsTorsFrame A ρA N x e') {l : FractionRing V}
    (hl : ∀ z J, Good A.L z J → (val e' (𝟙 _) z J).val =
      @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cstH (R := V) z l) * (val e (𝟙 _) z J).val) :
    l ^ (N ^ 2) = 1 := by
  obtain ⟨-, he, α, hα, nα, cα⟩ := H
  obtain ⟨-, he', α', hα', nα', cα'⟩ := H'
  have hp : Function.Surjective A.A.hom.appTop.hom := (GlobalTheory.globalFns_holds _ _ A.isAb).2
  have hαα : ∀ (Z : Scheme.{0}) (r : Z ⟶ A.A.left) (z : Z) J, Good A.L z J → val α r z J = val α' r z J :=
    gen_unique A.isLB A.A.hom (eSec A.A) (Over.w η[A.A]) hp hα hα' (fun w I hI => by
      have a := val_corr hI nα (𝟙 _)
      have b := val_corr hI nα' (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a b
      exact a.trans b.symm)
  obtain ⟨z⟩ : Nonempty (TFK (R := V) (FractionRing V)).left := exists_pt (R := V) (F := FractionRing V)
  obtain ⟨J, hJ⟩ := exists_good' A.isLB z
  have q : val e (𝟙 _) z J ^ ((N : ℤ) ^ 2) = val e' (𝟙 _) z J ^ ((N : ℤ) ^ 2) := by
    have a := val_corr hJ cα (𝟙 _)
    have b := val_corr hJ cα' (𝟙 _)
    have p₁ : val (powFrame A.A A.L x e ((N : ℤ) ^ 2)) (𝟙 _) z J = val e (𝟙 _) z J ^ ((N : ℤ) ^ 2) := map_zpow _ _ _
    have p₂ : val (powFrame A.A A.L x e' ((N : ℤ) ^ 2)) (𝟙 _) z J = val e' (𝟙 _) z J ^ ((N : ℤ) ^ 2) := map_zpow _ _ _
    rw [val_mul hJ, val_pull hJ] at a b
    rw [← p₁, ← p₂, a, b, hαα _ _ z J hJ]
  have q' := congrArg Units.val q
  rw [show ((N : ℤ) ^ 2) = ((N ^ 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, hl z J hJ, mul_pow] at q'
  have hu : IsUnit ((val e (𝟙 _) z J).val ^ (N ^ 2)) := (Units.isUnit _).pow _
  refine cstH_inj (R := V) z ((map_pow _ _ _).trans (Eq.trans ?_ (map_one _).symm))
  exact hu.mul_left_inj.1 (q'.symm.trans (_root_.one_mul _).symm)

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}

attribute [local instance] GlobalTheory.TorusExt.gtGroup in

theorem shift (𝔪 : UMem X₁ z₁ act V ev X t δ) {x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)}
    {fr : ∀ a, FrAt (x a)} (hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left)
    {ρA : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))} (hρA : ρA.IsGen)
    (htors : ∀ a, IsTorsFrame 𝔪.A ρA (X₁.S.r * X₁.S.N) (x a) (fr a)) {w₀ : W0 𝔪.U.toUnifPre} (hw₀ : w₀.IsGen)
    {a τ : X₁.S.Gam} {χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ} (hχ : TorChar 𝔪 τ χ)
    {g₁ : GtPtF 𝔪.D.toPre (FractionRing V)} {w₁ : Frm 𝔪.D.toPre (FractionRing V) 1 g₁.b}
    (hc : (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₁ o ∧ o.IsZero) ∧ w₁.IsGen ∧ 𝔪.Over' w₀ g₁ w₁ (x a) (fr a)) :
    ∃ (u : FractionRing V) (g₂ : GtPtF 𝔪.D.toPre (FractionRing V)) (w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 g₂.b),
      u ^ ((X₁.S.r * X₁.S.N) ^ 2) = 1 ∧
      ((∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₂ o ∧ o.IsZero) ∧ w₂.IsGen ∧ 𝔪.Over' w₀ g₂ w₂ (x (a + τ)) (fr (a + τ))) ∧
      g₂.b = g₁.b ∧ (∀ z J, Good 𝔪.D.toPre.P.L z J → (val w₂ (𝟙 _) z J).val = cstH z u⁻¹ * (val w₁ (𝟙 _) z J).val) ∧
      ∀ (s : Fam 𝔪.D.toPre (FractionRing V) 1) (β : 𝔪.D.toPre.X), coef s g₂ w₂ β =
        u⁻¹ * ((χ (Multiplicative.ofAdd β) : (FractionRing V)ˣ) : FractionRing V) * coef s g₁ w₁ β := by
  obtain ⟨hχ, hyp⟩ := hχ
  have hg₀ : IsTor χ (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) :=
    (isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ)
  obtain ⟨p, xτ, hpy, hpg, hq, hxτ⟩ := hyp _ hg₀
  have hadd := (GlobalTheory.TorusExt.isAdd_iff_eq g₁ (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) _).2 rfl
  have hb := (GlobalTheory.UT.ThetaAverage.val_translate hg₀ hadd).1
  obtain ⟨w'', hw''g, hw''v⟩ : ∃ w'' : Frm 𝔪.D.toPre (FractionRing V) 1
      (g₁ + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b,
      w''.IsGen ∧ ∀ z J, val w'' (𝟙 _) z J = val w₁ (𝟙 _) z J := by
    revert hb
    generalize (g₁ + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b = b
    rintro rfl
    exact ⟨w₁, hc.2.1, fun _ _ => rfl⟩
  obtain ⟨e₂, he₂, hov⟩ := GlobalTheory.T.torusExtension_translate_liesOver_product_torsionFrame g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 w₀ hw₀ ρA hρA (x a) (fr a) (htors _)
    g₁ w₁ hc.1 hc.2.1 hc.2.2 χ hχ _ hg₀ p xτ hpy hpg hq _ hadd w'' (fun z J _ => hw''v z J)
    (x (a + τ)) (GlobalTheory.T.memberTorsionPoints_additive_label g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x hx a τ xτ hxτ)
  obtain ⟨u, hu, huv⟩ := exists_frAt_ratio he₂.2.1 (htors (a + τ)).2.1
  obtain ⟨w₃, hw₃, hw₃v⟩ := exists_frm_scale w'' hw''g (inv_ne_zero hu)
  have hv : ∀ z J, Good 𝔪.D.toPre.P.L z J → (val w₃ (𝟙 _) z J).val = cstH z u⁻¹ * (val w₁ (𝟙 _) z J).val :=
    fun z J hJ => by rw [hw₃v z J hJ, hw''v, cst_eq]
  refine ⟨u, _, w₃, ratio_pow he₂ (htors _) huv, ⟨⟨0, (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 ?_,
    (GlobalTheory.TorusExt.isZero_iff_eq _).2 rfl⟩, hw₃, over_scale 𝔪 hw''g hu huv hw₃v hov⟩, hb, hv,
    GlobalTheory.UT.ThetaAverage.coef_translate hg₀ hadd hc.2.1 hv⟩
  obtain ⟨o, ho, ho'⟩ := hc.1
  rw [smul_add, ← (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 ho, (GlobalTheory.TorusExt.isZero_iff_eq _).1 ho', ← map_nsmul,
    ← ofMul_pow, hχ, ofMul_one, map_zero, add_zero]

theorem cube_alg {S : Type} [CommRing S] {A C D B₀ B₁ B₂ B₃ B₁₂ B₁₃ B₂₃ B₁₂₃ : Sˣ} {k v₀ v₁ v₂ v₁₂ : S}
    (E : A * (B₁₂₃ * B₁ * B₂ * B₃) * C = D * (B₁₂ * B₁₃ * B₂₃ * B₀)) (K : D.val = k * A.val)
    (h₀ : B₃.val = v₀ * B₀.val) (h₁ : B₁₃.val = v₁ * B₁.val) (h₂ : B₂₃.val = v₂ * B₂.val)
    (h₁₂ : B₁₂₃.val = v₁₂ * B₁₂.val) : v₁₂ * v₀ * C.val = k * v₁ * v₂ := by
  have E' := congrArg Units.val E
  simp only [Units.val_mul, K, h₀, h₁, h₂, h₁₂] at E'
  refine (A * B₀ * B₁ * B₂ * B₁₂).mul_right_inj.1 ?_
  simp only [Units.val_mul]
  linear_combination E'

theorem cube_rel (𝔪 : UMem X₁ z₁ act V ev X t δ) {κ : X₁.S.Gam → X₁.S.Gam → X₁.S.Gam → X₁.S.R}
    {x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)}
    {fr : ∀ a, FrAt (x a)} (hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) (hfr : ∀ a, (fr a).IsGen)
    {ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))} {hρ : ρ.IsGen} (c : CubicalStr 𝔪.A.A ⟨𝔪.A.L, ρ, 𝔪.A.isLB, hρ⟩)
    (hκ : ∀ (a a' a'' : X₁.S.Gam) (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ 𝔪.A.A.left) → 𝔪.A.L.ι), Good 𝔪.A.L z JA → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x a) (x a') (x a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr 0) (𝟙 _) z JA))).val = GlobalTheory.UT.cst (FractionRing V) z (𝔪.yK (κ a a' a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a') (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a'') (𝟙 _) z JA)).val)
    {w₀ : W0 𝔪.U.toUnifPre} (hw₀ : w₀.IsGen) {H : AddSubgroup X₁.S.Gam} {τ : X₁.S.Gam}
    {g₁ g₂ : H → GtPtF 𝔪.D.toPre (FractionRing V)} {w₁ : ∀ b, Frm 𝔪.D.toPre (FractionRing V) 1 (g₁ b).b}
    {w₂ : ∀ b, Frm 𝔪.D.toPre (FractionRing V) 1 (g₂ b).b} {v : H → FractionRing V}
    (h₁ : ∀ b, (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g₁ b) o ∧ o.IsZero) ∧ (w₁ b).IsGen ∧
      𝔪.Over' w₀ (g₁ b) (w₁ b) (x b) (fr b))
    (h₂ : ∀ b, (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g₂ b) o ∧ o.IsZero) ∧ (w₂ b).IsGen ∧
      𝔪.Over' w₀ (g₂ b) (w₂ b) (x (b + τ)) (fr (b + τ)))
    (hb : ∀ b, (g₂ b).b = (g₁ b).b)
    (hv : ∀ b z J, Good 𝔪.D.toPre.P.L z J → (val (w₂ b) (𝟙 _) z J).val = cstH z (v b) * (val (w₁ b) (𝟙 _) z J).val)
    (a a' : H) (z : (TF (R := V) (FractionRing V)).left) {JB} (hJB : Good 𝔪.D.toPre.P.L z JB) :
    cstH z (v (a + a') * v 0) * (cubV 𝔪.D.toPre.cub z JB (g₁ a).b (g₁ a').b (g₁ 0).b).val =
      cstH z (𝔪.yK (κ a a' τ) * v a * v a') := by
  have hadd : ∀ b b', x (b + b') = x b * x b' := fun b b' =>
    GlobalTheory.T.memberTorsionPoints_additive_label g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x hx b b' (x b') (hx b')
  have hx0 : x 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  have hk : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)
  obtain ⟨JA, hJA⟩ := exists_good' 𝔪.A.isLB z
  let P : (X₁.S.Gam × Σ g' : GtPtF 𝔪.D.toPre (FractionRing V), Frm 𝔪.D.toPre (FractionRing V) 1 g'.b) → Prop := fun q =>
    (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) q.2.1 o ∧ o.IsZero) ∧ q.2.2.IsGen ∧ (fr q.1).IsGen ∧
      LiesOver 𝔪.U.toUnifPre w₀ q.2.1 q.2.2 (x q.1) (fr q.1)
  have p₁ : ∀ b : H, P ⟨b, g₁ b, w₁ b⟩ := fun b => ⟨(h₁ b).1, (h₁ b).2.1, hfr _, (h₁ b).2.2⟩
  have p₂ : ∀ b : H, P ⟨b + τ, g₂ b, w₂ b⟩ := fun b => ⟨(h₂ b).1, (h₂ b).2.1, hfr _, (h₂ b).2.2⟩
  have p₃ : P ⟨τ, g₂ 0, w₂ 0⟩ := by
    have := p₂ 0
    rwa [AddSubgroup.coe_zero, zero_add] at this
  obtain ⟨f, hP, f₀, f₁, f₂, f₃, f₄, f₅, f₆, f₇⟩ : ∃ f : Finset (Fin 3) →
      (X₁.S.Gam × Σ g' : GtPtF 𝔪.D.toPre (FractionRing V), Frm 𝔪.D.toPre (FractionRing V) 1 g'.b), (∀ S, P (f S)) ∧
      f ∅ = ⟨0, g₁ 0, w₁ 0⟩ ∧ f {0} = ⟨a, g₁ a, w₁ a⟩ ∧ f {1} = ⟨a', g₁ a', w₁ a'⟩ ∧ f {2} = ⟨τ, g₂ 0, w₂ 0⟩ ∧
      f {0, 1} = ⟨a + a', g₁ (a + a'), w₁ (a + a')⟩ ∧ f {0, 2} = ⟨a + τ, g₂ a, w₂ a⟩ ∧
      f {1, 2} = ⟨a' + τ, g₂ a', w₂ a'⟩ ∧ f {0, 1, 2} = ⟨a + a' + τ, g₂ (a + a'), w₂ (a + a')⟩ := by
    refine ⟨fun S => if 2 ∈ S then
        (if 0 ∈ S then (if 1 ∈ S then ⟨a + a' + τ, g₂ (a + a'), w₂ (a + a')⟩ else ⟨a + τ, g₂ a, w₂ a⟩)
          else if 1 ∈ S then ⟨a' + τ, g₂ a', w₂ a'⟩ else ⟨τ, g₂ 0, w₂ 0⟩)
      else (if 0 ∈ S then (if 1 ∈ S then ⟨a + a', g₁ (a + a'), w₁ (a + a')⟩ else ⟨a, g₁ a, w₁ a⟩)
          else if 1 ∈ S then ⟨a', g₁ a', w₁ a'⟩ else ⟨0, g₁ 0, w₁ 0⟩), fun S => ?_, ?_⟩
    · dsimp only
      split_ifs
      exacts [p₂ (a + a'), p₂ a, p₂ a', p₃, p₁ (a + a'), p₁ a, p₁ a', p₁ 0]
    · simp
  have E := GlobalTheory.T.framed_torsion_torus_extension_respect_cubical V 𝔪.cn 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀ _ hk ρ hρ c (fun S => (f S).2.1) (fun S => (f S).2.2)
    (fun S => x (f S).1) (fun S => fr (f S).1) (by simp only [f₀, hx0]) (by simp only [f₁, f₂, f₄, hadd])
    (by simp only [f₁, f₃, f₅, hadd]) (by simp only [f₂, f₃, f₆, hadd]) (by simp only [f₁, f₂, f₃, f₇, hadd]) hP
    z JA JB hJA hJB
  beta_reduce at E
  rw [f₀, f₁, f₂, f₃, f₄, f₅, f₆, f₇] at E
  dsimp only at E
  have := cube_alg E (hκ a a' τ z JA hJA) (hv 0 z JB hJB) (hv a z JB hJB) (hv a' z JB hJB) (hv (a + a') z JB hJB)
  rw [hb 0, cst_eq] at this
  rw [map_mul, map_mul, map_mul, this]

theorem one_member {κ : X₁.S.Gam → X₁.S.Gam → X₁.S.Gam → X₁.S.R} {x₀ : X₁.S.Gam} (hdiv : X₁.M.Div X₁.S.th x₀ z₁)
    (𝔪 : UMem X₁ z₁ act V ev X t δ)
    (hκ : ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) → (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) → ∀ (ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))) (hρ : ρ.IsGen) (c : CubicalStr 𝔪.A.A ⟨𝔪.A.L, ρ, 𝔪.A.isLB, hρ⟩) (a a' a'' : X₁.S.Gam) (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ 𝔪.A.A.left) → 𝔪.A.L.ι), Good 𝔪.A.L z JA → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x a) (x a') (x a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr 0) (𝟙 _) z JA))).val = GlobalTheory.UT.cst (FractionRing V) z (𝔪.yK (κ a a' a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a') (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a'') (𝟙 _) z JA)).val)
    {τ : X₁.S.Gam} (hτ : τ ∈ X₁.S.TT X₁.M z₁) :
    ∃ e : X₁.S.HH X₁.M z₁ → ℕ, (∀ a : X₁.S.HH X₁.M z₁, TransExp 𝔪 x₀ a τ (e a)) ∧ ∀ a a' : X₁.S.HH X₁.M z₁,
      𝔪.yK (κ a a' 0 * algebraMap X₁.o₁ X₁.S.R X₁.S.ζ ^ (e a + e a')) =
        𝔪.yK (κ a a' τ * algebraMap X₁.o₁ X₁.S.R X₁.S.ζ ^ (e (a + a') + e 0)) := by
  obtain ⟨T₁, hT₀, -, -⟩ :=
    GlobalTheory.T.exists_member_terms_integral_unit_shift g n F W Z i X₁ z₁ act x₀ hdiv V ev X m t δ 𝔪 (X₁.S.HH X₁.M z₁) Subtype.val Subtype.range_coe
  generalize (fun mu c => T₁ mu c * mono W t δ mu) = T₀ at hT₀
  have hT₀' := hT₀
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs, hc, hTc⟩ := hT₀'
  obtain ⟨ρA, hρA, htors⟩ := GlobalTheory.T.exists_rigidification_matchingFrames_torsionFrames g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x fr hx hfr
  obtain ⟨χ₀, hχ₀⟩ : ∃ χ, TorChar 𝔪 τ χ := GlobalTheory.T.exists_torusTorsionPoint_of_label_orthogonal g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 τ hτ
  choose u g₂ w₂ hu h₂ hb hv hco using fun b : X₁.S.HH X₁.M z₁ => shift 𝔪 hx hρA htors hw₀ hχ₀ (hc b)
  choose e he using fun b => GlobalTheory.T.rootOfUnity_fractionField_member_eq_zeta_pow g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 (u b) (hu b)
  have hk : 0 < X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)
  have hu0 : ∀ b, u b ≠ 0 := fun b h => by
    have := hu b
    rw [h, zero_pow (by positivity)] at this
    exact zero_ne_one this
  obtain ⟨z⟩ : Nonempty (TF (R := V) (FractionRing V)).left := exists_pt (R := V) (F := FractionRing V)
  obtain ⟨J, hJ⟩ := exists_good' 𝔪.D.toPre.P.isLB z
  refine ⟨e, fun a χ hχ C lab T hT c hl C' lab' T' hT' c' hl' mu => ?_, fun a a' => ?_⟩
  · obtain ⟨u', g₃, w₃, hu', h₃, -, hv', hco'⟩ := shift 𝔪 hx hρA htors hw₀ hχ (hc a)
    have huu : u' = u a := by
      have q := (GlobalTheory.T.framedTorsionPoint_torusExtension_eq_of_liesOver V 𝔪.cn 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀ _ hk g₃ (g₂ a) w₃ (w₂ a) _ _ h₃.1 (h₂ a).1 h₃.2.1
        (h₂ a).2.1 (hfr _).1 h₃.2.2 (h₂ a).2.2).2 z J hJ
      have q' := congrArg Units.val q
      rw [hv' z J hJ, hv a z J hJ] at q'
      exact inv_injective (cstH_inj z ((Units.mul_left_inj _).1 q'))
    subst huu
    haveI : IsIntegrallyClosed V := 𝔪.cn.2.1
    have hint : ∀ mu : Fin 8 → X, ∃ r : V, algebraMap V (FractionRing V) r =
        (u a)⁻¹ * ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) := fun mu => by
      refine IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.mul ?_ ?_)
      · refine IsIntegral.of_pow (n := (X₁.S.r * X₁.S.N) ^ 2) (by positivity) ?_
        rw [inv_pow, hu', inv_one]
        exact isIntegral_one
      · refine IsIntegral.of_pow hk ?_
        rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hχ.1, MonoidHom.one_apply, Units.val_one]
        exact isIntegral_one
    choose r hr using hint
    have hT₂ : 𝔪.Terms x₀ (fun _ : Unit => a.1 + τ) fun mu _ => r mu * T₀ mu a :=
      ⟨x, fr, th, w₀, s, fun _ => g₃, fun _ => w₃, hx, hfr, hth, hw₀, hs, fun _ => h₃, fun mu _ => by
        rw [hco', map_mul, hr, ← hTc, _root_.mul_assoc]⟩
    have θ := GlobalTheory.T.uniformisedMember_dividingThetaConstant_ne_zero g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hdiv
    have a₁ := mul_right_cancel₀ θ
      (GlobalTheory.T.thetaFamily_terms_eq_up_to_normalising_thetaConst g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ x₀ _ _ _ _ _ _ hT hT₀ c a hl mu)
    have a₂ := mul_right_cancel₀ θ
      (GlobalTheory.T.thetaFamily_terms_eq_up_to_normalising_thetaConst g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ x₀ _ _ _ _ _ _ hT' hT₂ c' () hl' mu)
    rw [a₁, a₂, ← he, map_mul, hr, ← _root_.mul_assoc, mul_inv_cancel_left₀ (hu0 a)]
  · obtain ⟨c⟩ := (GlobalTheory.firstFiveLaws.1.cube _ 𝔪.A ⟨𝔪.A.L, ρA, 𝔪.A.isLB, hρA⟩ rfl).1
    have K := hκ x fr hx hfr ρA hρA c
    have E₁ := cube_rel 𝔪 hx (fun b => (hfr b).1) c K hw₀ hc h₂ hb hv a a' z hJ
    have E₀ := cube_rel 𝔪 hx (fun b => (hfr b).1) c K hw₀ (τ := 0) (v := fun _ => 1) hc
      (fun b => by rw [add_zero]; exact hc b) (fun _ => rfl) (fun b z J _ => by rw [map_one, _root_.one_mul]) a a' z hJ
    simp only [_root_.mul_one, map_one, _root_.one_mul] at E₀
    rw [E₀, ← map_mul] at E₁
    have E := cstH_inj z E₁
    have he' : ∀ b, 𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ) ^ e b = u b := fun b => by rw [he, map_pow, map_pow]
    simp only [map_mul, pow_add, map_pow, he']
    have := hu0 a
    have := hu0 a'
    have := hu0 (a + a')
    have := hu0 0
    field_simp at E
    linear_combination E

theorem prim_ring : IsPrimitiveRoot (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ) ((X₁.S.r * X₁.S.N) ^ 2) := by
  refine X₁.S.prim.map_of_injective fun a b hab => X₁.ar.inj ?_
  simpa using congrArg (fun x : X₁.S.R => (x : X₁.Ω₁)) hab

theorem prim_member (𝔪 : UMem X₁ z₁ act V ev X t δ) :
    IsPrimitiveRoot (𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ)) ((X₁.S.r * X₁.S.N) ^ 2) := by
  haveI : CharZero V := 𝔪.cn.2.2.2
  haveI : CharZero (FractionRing V) := IsFractionRing.charZero V
  have hk : 0 < (X₁.S.r * X₁.S.N) ^ 2 := pow_pos (Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)) 2
  have h := ((prim_ring (X₁ := X₁)).isRoot_cyclotomic hk).map (f := 𝔪.yK)
  rw [Polynomial.map_cyclotomic] at h
  haveI : NeZero ((((X₁.S.r * X₁.S.N) ^ 2 : ℕ)) : FractionRing V) := ⟨by exact_mod_cast hk.ne'⟩
  exact Polynomial.isRoot_cyclotomic_iff.1 h

theorem exp_eq (𝔪 : UMem X₁ z₁ act V ev X t δ) {p q : ℕ}
    (h : 𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ ^ p) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ ^ q)) :
    (p : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = q := by
  have hk : 0 < (X₁.S.r * X₁.S.N) ^ 2 := pow_pos (Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)) 2
  have hp := prim_member 𝔪
  rw [map_pow, map_pow, (isOfFinOrder_iff_pow_eq_one.2 ⟨_, hk, hp.pow_eq_one⟩).pow_eq_pow_iff_modEq, ← hp.eq_orderOf] at h
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h

theorem transExp_affine : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (m2 : ℕ) (t2 : Fin m2 → V2) (δ2 : Fin m2 → LinearMap.BilinForm ℤ Y2) (𝔪2 : UMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ F1 F2 : X₁.S.Gam → ℕ, (∀ a ∈ X₁.S.HH X₁.M z₁, TransExp 𝔪1 x₀ a τ (F1 a)) ∧ (∀ a ∈ X₁.S.HH X₁.M z₁, TransExp 𝔪2 x₀ a τ (F2 a)) ∧ ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((F1 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((F2 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  intro g n F W Z i X₁ z₁ act x₀ hdiv V1 _ _ _ ev1 Y1 _ m1 t1 δ1 𝔪1 V2 _ _ _ ev2 Y2 _ m2 t2 δ2 𝔪2 τ hτ
  classical
  obtain ⟨κ, hκ1, hκ⟩ := GlobalTheory.T.exists_theta_frame_cube_constant_root_of_unity g n F W Z i X₁ z₁ act
  obtain ⟨e₁, h₁, c₁⟩ := one_member hdiv 𝔪1 (hκ V1 ev1 Y1 m1 t1 δ1 𝔪1) hτ
  obtain ⟨e₂, h₂, c₂⟩ := one_member hdiv 𝔪2 (hκ V2 ev2 Y2 m2 t2 δ2 𝔪2) hτ
  haveI : NeZero ((X₁.S.r * X₁.S.N) ^ 2) :=
    ⟨(pow_pos (Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)) 2).ne'⟩
  let d : X₁.S.HH X₁.M z₁ → ZMod ((X₁.S.r * X₁.S.N) ^ 2) := fun a => (e₁ a : ZMod _) - (e₂ a : ZMod _)
  have hd : ∀ a a', d (a + a') - d 0 = d a - d 0 + (d a' - d 0) := fun a a' => by
    obtain ⟨k, -, hk⟩ := (prim_ring (X₁ := X₁)).eq_pow_of_pow_eq_one (hκ1 a a' 0)
    obtain ⟨k', -, hk'⟩ := (prim_ring (X₁ := X₁)).eq_pow_of_pow_eq_one (hκ1 a a' τ)
    have a₁ := c₁ a a'
    have a₂ := c₂ a a'
    rw [← hk, ← hk', ← pow_add, ← pow_add] at a₁ a₂
    have b₁ := exp_eq 𝔪1 a₁
    have b₂ := exp_eq 𝔪2 a₂
    push_cast at b₁ b₂
    simp only [d]
    linear_combination b₂ - b₁
  refine ⟨fun a => if h : a ∈ X₁.S.HH X₁.M z₁ then e₁ ⟨a, h⟩ else 0,
    fun a => if h : a ∈ X₁.S.HH X₁.M z₁ then e₂ ⟨a, h⟩ else 0, fun a ha => ?_, fun a ha => ?_, d 0,
    AddMonoidHom.mk' (fun a => d a - d 0) hd, fun a ha => ?_⟩
  · beta_reduce
    rw [dif_pos ha]
    exact h₁ ⟨a, ha⟩
  · beta_reduce
    rw [dif_pos ha]
    exact h₂ ⟨a, ha⟩
  · beta_reduce
    rw [dif_pos ha, dif_pos ha, AddMonoidHom.mk'_apply, add_sub_cancel]

end GlobalTheory.Poinc.Sep.TransAff
