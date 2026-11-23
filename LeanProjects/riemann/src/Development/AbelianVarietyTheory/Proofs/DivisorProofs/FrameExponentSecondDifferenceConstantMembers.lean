import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFCompEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigTorsFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaFrameCubeConstantRootOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyTermsEqUpToNormalisingThetaConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionTorusExtensionRespectCubicalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

noncomputable section

namespace GlobalTheory.GSep.FrExpCube
open GlobalTheory.UT.TorsionValue GlobalTheory.Poinc.Tors GlobalTheory.Poinc.CubeConst

theorem frame_cube_const : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∃ κ : X₁.S.Gam → X₁.S.Gam → X₁.S.Gam → X₁.S.R, (∀ a a' a'', κ a a' a'' ^ ((X₁.S.r * X₁.S.N) ^ 2) = 1) ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) → (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) → ∀ (ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))) (hρ : ρ.IsGen) (c : CubicalStr 𝔪.A.A ⟨𝔪.A.L, ρ, 𝔪.A.isLB, hρ⟩) (a a' a'' : X₁.S.Gam) (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ 𝔪.A.A.left) → 𝔪.A.L.ι), Good 𝔪.A.L z JA → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x a) (x a') (x a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr 0) (𝟙 _) z JA))).val = GlobalTheory.UT.cst (FractionRing V) z (𝔪.yK (κ a a' a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a') (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a'') (𝟙 _) z JA)).val := by
  intro I X₁ z₁ act
  have := X₁.ar.ded
  have : IsNoetherianRing X₁.S.R := isNoetherianRing_of_fg X₁.S.fg
  have : IsLocallyNoetherian (Sp X₁.S.R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of X₁.S.R)))
  have := X₁.ρ.P.isAb.comm
  obtain ⟨c₀⟩ := (GlobalTheory.firstFiveLaws.1.cube (Sp X₁.S.R) X₁.ρ.P ⟨X₁.ρ.P.L, X₁.ρ.rig, X₁.ρ.P.isLB, X₁.ρ.rig_gen⟩ rfl).1
  choose k hk using exists_cube_const c₀ X₁.ρ.pt X₁.ρ.pt_add X₁.ρ.fr (fun a => (X₁.ρ.fr_tors a).2.1)
  refine ⟨fun a a' a'' => (Scheme.ΓSpecIso (CommRingCat.of X₁.S.R)).hom.hom (k a a' a''), fun a a' a'' => ?_, ?_⟩
  · rw [← map_pow]
    refine Eq.trans (congrArg _ (fn_ext (b := 1) fun y _ => ?_)) (map_one _)
    obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' X₁.ρ.P.isLB y
    have e := hk a a' a'' _ (𝟙 _) y J hJ
    rw [Category.id_comp, Category.id_comp, Category.id_comp] at e
    have e' := congrArg Units.val (cube_torsFrame_pow GlobalTheory.firstFiveLaws.1.globalFns X₁.ρ.P c₀ X₁.ρ.pt X₁.ρ.pt_add
      X₁.ρ.fr X₁.ρ.fr_tors a a' a'' y J hJ)
    have e'' := (congrArg (· ^ ((X₁.S.r * X₁.S.N) ^ 2)) e).symm.trans ((Units.val_pow_eq_pow_val _ _).symm.trans e')
    rw [gs_eq _ y ⊤ trivial, ← map_pow, ← map_pow] at e''
    rw [gs_eq _ y ⊤ trivial, gs_eq _ y ⊤ trivial, map_one, map_one]
    exact e''
  intro V _ _ _ ev X _ t δ 𝔪 x fr hx hfr ρ hρ c a a' a'' z JA hJA
  have := 𝔪.A.isAb.comm
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' X₁.ρ.P.isLB z
  let U : Over.mk ((TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) :=
    Over.homMk (spMap 𝔪.yK) (by
      show spMap 𝔪.yK ≫ 𝟙 _ = _
      rw [Category.comp_id]
      change _ = Spec.map (𝟙 _) ≫ _
      rw [Spec.map_id, Category.id_comp])
  have hp : ∀ b, pushHom 𝔪.cart (TFK (R := V) (FractionRing V)) (x b) = U ≫ X₁.ρ.pt b := fun b =>
    Over.OverMorphism.ext (hx b)
  have hadd : ∀ b b', x (b + b') = x b * x b' := fun b b' =>
    GlobalTheory.GSep.TwistTranslate.x_add 𝔪 x hx b b' (x b') (hx b')
  have h0 : x 0 = 1 := mul_eq_left.1 ((hadd 0 0).symm.trans (by rw [add_zero]))
  have e₁ := cubV_through GlobalTheory.firstFiveLaws.1.globalFns 𝔪.A.isAb 𝔪.cart c₀ c 𝔪.wl 𝔪.wl_gen
    (T := TFK (R := V) (FractionRing V)) z hJ hJA (x a) (x a') (x a'')
  rw [hp, hp, hp, ← hadd, ← hadd, ← hadd, ← hadd, ← h0] at e₁
  have e₂ := hk a a' a'' _ U z J hJ
  have e₃ : gs U.left z ⊤ (k a a' a'') = GlobalTheory.UT.cst (FractionRing V) z
      (𝔪.yK ((Scheme.ΓSpecIso (CommRingCat.of X₁.S.R)).hom.hom (k a a' a''))) := by
    refine Eq.trans ?_ (Geo.Tor.cst_comp (𝟙 _) 𝔪.yK z _)
    rw [Category.id_comp]
    exact congrArg (gs (spMap 𝔪.yK) z ⊤) ((Scheme.ΓSpecIso (CommRingCat.of X₁.S.R)).hom_inv_id_apply _).symm
  have alg : ∀ {R : Type} [CommRing R] {κ : R} {c c₀ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ g₁ g₂ g₃ g₄ g₅ g₆ g₇ g₈ : Rˣ},
      c₀ = w₁ * w₂⁻¹ * w₃⁻¹ * w₄⁻¹ * w₅ * w₆ * w₇ * w₈⁻¹ * c →
      (c₀ * ((g₂ * g₃ * g₄ * g₈) * (g₁ * g₅ * g₆ * g₇)⁻¹)).val = κ →
      w₁ * f₁ = g₁ → w₂ * f₂ = g₂ → w₃ * f₃ = g₃ → w₄ * f₄ = g₄ → w₅ * f₅ = g₅ → w₆ * f₆ = g₆ → w₇ * f₇ = g₇ →
      w₈ * f₈ = g₈ → (c * (f₂ * f₃ * f₄ * f₈)).val = κ * (f₁ * f₅ * f₆ * f₇).val := by
    rintro R _ κ c c₀ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ g₁ g₂ g₃ g₄ g₅ g₆ g₇ g₈ rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl
    rw [← Units.val_mul]
    refine congrArg Units.val (Additive.ofMul.injective ?_)
    simp only [ofMul_mul, ofMul_inv]
    abel
  exact alg e₁ (e₂.trans e₃) ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA)
    ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA)
    ((hfr _).2 z J JA hJ hJA)

variable {I : Type} {X₁ : GlobalTheory.GSep.GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}

theorem cube_alg {S : Type} [CommRing S] {A C D B₀ B₁ B₂ B₃ B₁₂ B₁₃ B₂₃ B₁₂₃ : Sˣ} {k v₀ v₁ v₂ v₁₂ : S}
    (E : A * (B₁₂₃ * B₁ * B₂ * B₃) * C = D * (B₁₂ * B₁₃ * B₂₃ * B₀)) (K : D.val = k * A.val)
    (h₀ : B₃.val = v₀ * B₀.val) (h₁ : B₁₃.val = v₁ * B₁.val) (h₂ : B₂₃.val = v₂ * B₂.val)
    (h₁₂ : B₁₂₃.val = v₁₂ * B₁₂.val) : v₁₂ * v₀ * C.val = k * v₁ * v₂ := by
  have E' := congrArg Units.val E
  simp only [Units.val_mul, K, h₀, h₁, h₂, h₁₂] at E'
  refine (A * B₀ * B₁ * B₂ * B₁₂).mul_right_inj.1 ?_
  simp only [Units.val_mul]
  linear_combination E'

theorem cube_rel (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) {κ : X₁.S.Gam → X₁.S.Gam → X₁.S.Gam → X₁.S.R}
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
    GlobalTheory.GSep.TwistTranslate.x_add 𝔪 x hx b b' (x b') (hx b')
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

theorem prim_ring : IsPrimitiveRoot (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ) ((X₁.S.r * X₁.S.N) ^ 2) := by
  refine X₁.S.prim.map_of_injective fun a b hab => X₁.ar.inj ?_
  simpa using congrArg (fun x : X₁.S.R => (x : X₁.Ω₁)) hab

theorem prim_member (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) :
    IsPrimitiveRoot (𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ)) ((X₁.S.r * X₁.S.N) ^ 2) := by
  haveI : CharZero V := 𝔪.cn.2.2.2
  haveI : CharZero (FractionRing V) := IsFractionRing.charZero V
  have hk : 0 < (X₁.S.r * X₁.S.N) ^ 2 := pow_pos (Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)) 2
  have h := ((prim_ring (X₁ := X₁)).isRoot_cyclotomic hk).map (f := 𝔪.yK)
  rw [Polynomial.map_cyclotomic] at h
  haveI : NeZero ((((X₁.S.r * X₁.S.N) ^ 2 : ℕ)) : FractionRing V) := ⟨by exact_mod_cast hk.ne'⟩
  exact Polynomial.isRoot_cyclotomic_iff.1 h

theorem exp_eq (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) {p q : ℕ}
    (h : 𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ ^ p) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ ^ q)) :
    (p : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = q := by
  have hk : 0 < (X₁.S.r * X₁.S.N) ^ 2 := pow_pos (Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)) 2
  have hp := prim_member 𝔪
  rw [map_pow, map_pow, (isOfFinOrder_iff_pow_eq_one.2 ⟨_, hk, hp.pow_eq_one⟩).pow_eq_pow_iff_modEq, ← hp.eq_orderOf] at h
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h

attribute [local instance] GlobalTheory.TorusExt.gtGroup in

theorem lifts_of_frExp (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ)
    {x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)} {fr : ∀ a, FrAt (x a)}
    (hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left)
    (hfr : ∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J)
    {w₀ : W0 𝔪.U.toUnifPre} (hw₀ : w₀.IsGen) {a τ : X₁.S.Gam} {e : ℕ} (H : GlobalTheory.GSep.TransTerms.FrExp 𝔪 a τ e) :
    ∃ (g₁ g₂ : GtPtF 𝔪.D.toPre (FractionRing V)) (w₁ : Frm 𝔪.D.toPre (FractionRing V) 1 g₁.b)
      (w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 g₂.b),
      ((∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₁ o ∧ o.IsZero) ∧ w₁.IsGen ∧ 𝔪.Over' w₀ g₁ w₁ (x a) (fr a)) ∧
      ((∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₂ o ∧ o.IsZero) ∧ w₂.IsGen ∧ 𝔪.Over' w₀ g₂ w₂ (x (a + τ)) (fr (a + τ))) ∧
      g₂.b = g₁.b ∧ ∀ z J, Good 𝔪.D.toPre.P.L z J → (val w₂ (𝟙 _) z J).val =
        cstH z (𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ) ^ e)⁻¹ * (val w₁ (𝟙 _) z J).val := by
  obtain ⟨⟨χ, hχ⟩, x', fr', th, w₀', s, g₁, w, hx', hfr', -, hw₀', -, htor, hw, hov, htr⟩ := H
  obtain rfl : x = x' := funext fun a => Over.OverMorphism.ext
    (𝔪.cart.1.hom_ext ((hx a).trans (hx' a).symm) ((Over.w (x a)).trans (Over.w (x' a)).symm))
  have hf : ∀ a z J, Good 𝔪.A.L z J → val (fr a) (𝟙 _) z J = val (fr' a) (𝟙 _) z J := fun a z J hJ => by
    obtain ⟨J₀, hJ₀⟩ := exists_good' X₁.ρ.P.isLB z
    exact mul_left_cancel (((hfr a).2 z J₀ J hJ₀ hJ).trans ((hfr' a).2 z J₀ J hJ₀ hJ).symm)
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.Poinc.Sep.TermsCompare.exists_expandsF_pow 𝔪.U.toUnifPre (FractionRing V) hw₀' hw₀
  have hk : 0 < (X₁.S.r * X₁.S.N) ^ 2 := pow_pos (Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)) 2
  have hu : 𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ) ^ e ≠ 0 := pow_ne_zero _ ((prim_member 𝔪).ne_zero hk.ne')
  have hg₀ : IsTor χ (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) :=
    (GlobalTheory.UT.isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ)
  have hadd := (GlobalTheory.TorusExt.isAdd_iff_eq g₁ (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) _).2 rfl
  have hb := (GlobalTheory.UT.ThetaAverage.val_translate hg₀ hadd).1
  obtain ⟨w', hw'g, hw'v⟩ : ∃ w' : Frm 𝔪.D.toPre (FractionRing V) 1
      (g₁ + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b,
      w'.IsGen ∧ ∀ z J, val w' (𝟙 _) z J = val w (𝟙 _) z J := by
    revert hb
    generalize (g₁ + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b = b
    rintro rfl
    exact ⟨w, hw, fun _ _ => rfl⟩
  obtain ⟨w'', hw''g, hw''v⟩ := exists_frm_scale w' hw'g (inv_ne_zero hu)
  have hov₂ := htr χ hχ _ hg₀ _ hadd w'' hw''g (fun z J hJ => by
    rw [hw''v z J hJ, hw'v, cst_eq, ← _root_.mul_assoc, ← map_mul, map_pow, map_pow, mul_inv_cancel₀ hu, map_one,
      _root_.one_mul])
  obtain ⟨w₁, hw₁, hv₁⟩ := exists_frm_scale w hw hd0
  obtain ⟨w₂, hw₂, hv₂⟩ := exists_frm_scale w'' hw''g hd0
  refine ⟨g₁, _, w₁, w₂, ⟨htor, hw₁, GlobalTheory.Poinc.Sep.TermsCompare.liesOver_change hd hw hv₁ (hf _) hov⟩,
    ⟨⟨0, (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 ?_, (GlobalTheory.TorusExt.isZero_iff_eq _).2 rfl⟩, hw₂,
      GlobalTheory.Poinc.Sep.TermsCompare.liesOver_change hd hw''g hv₂ (hf _) hov₂⟩, hb, fun z J hJ => ?_⟩
  · obtain ⟨o, ho, ho'⟩ := htor
    rw [smul_add, ← (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 ho, (GlobalTheory.TorusExt.isZero_iff_eq _).1 ho', ← map_nsmul,
      ← ofMul_pow, hχ.1, ofMul_one, map_zero, add_zero]
  · rw [hv₂ z J hJ, hw''v z J hJ, hw'v, hv₁ z J hJ, cst_eq, cst_eq]
    ring

theorem frExp_second_diff : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ c : X₁.S.Gam → X₁.S.Gam → ZMod ((X₁.S.r * X₁.S.N) ^ 2), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (E : X₁.S.Gam → ℕ), (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.FrExp 𝔪 a τ (E a)) → ∀ a ∈ X₁.S.HH X₁.M z₁, ∀ b ∈ X₁.S.HH X₁.M z₁, ((E (a + b) : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((E a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((E b : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) + ((E 0 : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = c a b := by
  intro I X₁ z₁ act x₀ _ τ _
  obtain ⟨κ, hκ1, hκ⟩ := frame_cube_const I X₁ z₁ act
  haveI : NeZero ((X₁.S.r * X₁.S.N) ^ 2) :=
    ⟨(pow_pos (Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)) 2).ne'⟩
  choose k hk' hk using fun a a' a'' => (prim_ring (X₁ := X₁)).eq_pow_of_pow_eq_one (hκ1 a a' a'')
  refine ⟨fun a b => (k a b 0 : ZMod _) - (k a b τ : ZMod _), ?_⟩
  intro V _ _ _ ev Y _ t δ 𝔪 E hE a ha a' ha'
  obtain ⟨-, x, fr, -, w₀, -, -, -, hx, hfr, -, hw₀, -⟩ := hE a ha
  choose g₁ g₂ w₁ w₂ h₁ h₂ hb hv using fun b : X₁.S.HH X₁.M z₁ => lifts_of_frExp 𝔪 hx hfr hw₀ (hE b b.2)
  obtain ⟨ρA, hρA, -⟩ := GlobalTheory.GSep.TwistTranslate.exists_rig_torsFrame 𝔪 x fr hx hfr
  obtain ⟨z⟩ : Nonempty (TF (R := V) (FractionRing V)).left := exists_pt (R := V) (F := FractionRing V)
  obtain ⟨J, hJ⟩ := exists_good' 𝔪.D.toPre.P.isLB z
  obtain ⟨c⟩ := (GlobalTheory.firstFiveLaws.1.cube _ 𝔪.A ⟨𝔪.A.L, ρA, 𝔪.A.isLB, hρA⟩ rfl).1
  have K := hκ V ev Y t δ 𝔪 x fr hx hfr ρA hρA c
  have E₁ := cube_rel 𝔪 hx (fun b => (hfr b).1) c K hw₀ h₁ h₂ hb hv ⟨a, ha⟩ ⟨a', ha'⟩ z hJ
  have E₀ := cube_rel 𝔪 hx (fun b => (hfr b).1) c K hw₀ (τ := 0) (v := fun _ => 1) h₁
    (fun b => by rw [add_zero]; exact h₁ b) (fun _ => rfl) (fun b z J _ => by rw [map_one, _root_.one_mul])
    ⟨a, ha⟩ ⟨a', ha'⟩ z hJ
  simp only [_root_.mul_one, map_one, _root_.one_mul] at E₀
  rw [E₀, ← map_mul] at E₁
  have E' := cstH_inj z E₁
  have hu : 𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ) ≠ 0 := (prim_member 𝔪).ne_zero (NeZero.ne _)
  rw [← hk, ← hk] at E'
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_zero, map_pow] at E'
  have q : 𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ ^ (k a a' 0 + E a + E a')) =
      𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ ^ (k a a' τ + E (a + a') + E 0)) := by
    simp only [map_mul, map_pow, pow_add]
    generalize 𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ) = y at hu E' ⊢
    have fin : ∀ p q r s k₀ k₁ : FractionRing V, p ≠ 0 → q ≠ 0 → r ≠ 0 → s ≠ 0 →
        r⁻¹ * s⁻¹ * k₀ = k₁ * p⁻¹ * q⁻¹ → k₀ * p * q = k₁ * r * s := fun p q r s k₀ k₁ hp hq hr hs h => by
      field_simp at h
      linear_combination h
    exact fin _ _ _ _ _ _ (pow_ne_zero _ hu) (pow_ne_zero _ hu) (pow_ne_zero _ hu) (pow_ne_zero _ hu) E'
  have b₁ := exp_eq 𝔪 q
  push_cast at b₁
  linear_combination -b₁

end GlobalTheory.GSep.FrExpCube
