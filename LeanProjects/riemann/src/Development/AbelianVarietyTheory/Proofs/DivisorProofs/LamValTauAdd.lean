import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifAfterFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8invTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoValueOneZeroFirstFactor
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteNormalising

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

section
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.LamRigid GlobalTheory.LamBiext

namespace GlobalTheory.MumfordE8Bimultiplicative

theorem lamVal_law₁ {S : Scheme.{0}} (B₀ B : Over S) [GrpObj B₀] [IsCommMonObj B₀] [GrpObj B] [IsCommMonObj B]
    (M₀ : RigLB B₀) (M : RigLB B) (c₀ : CubicalStr B₀ M₀) (c : CubicalStr B M) (hB₀ : IsAbelianScheme B₀)
    (a b : B₀ ⟶ B) [IsMonHom a] [IsMonHom b]
    (w : LB.Iso (abelian₂ B₀ M₀.L) ((abelian₂ B M.L).pull (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left))
    (hw : w.IsGen)
    (hn : ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ B.left) → M.L.ι) (J' : (T.left ⟶ B₀.left) → M₀.L.ι),
      Good M.L z J → Good M₀.L z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ B₀) (1 : T ⟶ B₀)).left z J J' = 1)
    (T : Over S) (x x' y : T ⟶ B₀) (z : T.left) (J : (T.left ⟶ B.left) → M.L.ι) (J' : (T.left ⟶ B₀.left) → M₀.L.ι)
    (hJ : Good M.L z J) (hJ' : Good M₀.L z J') :
    GlobalTheory.PolDeg.lamVal w (lift (x * x') y).left z J J' * cubV c₀ z J' x x' y =
      cubV c z J (x ≫ a) (x' ≫ a) (y ≫ b) * GlobalTheory.PolDeg.lamVal w (lift x y).left z J J' *
        GlobalTheory.PolDeg.lamVal w (lift x' y).left z J J' := by
  have hG := GlobalTheory.globalFns_holds
  have hL : (abelian₂ B M.L).IsLB := DVR.linComb_isLB _ M.isLB _ _
  have hL' : (abelian₂ B₀ M₀.L).IsLB := DVR.linComb_isLB _ M₀.isLB _ _
  let β₂ : (G2 B₀).left ⟶ (G2 B).left := (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left
  have Hlam : ∀ {T₀ : Over S} (p q : T₀ ⟶ B₀) {U : Type} [CommGroup U] (h : (T₀.left ⟶ B.left) → U),
      ∏ i, h (((lift p q).left ≫ β₂) ≫ lamφ B i) ^ lamε i =
        h ((p ≫ a) * (q ≫ b)).left * (h (p ≫ a).left)⁻¹ * (h (q ≫ b).left)⁻¹ *
          h (1 : T₀ ⟶ B).left := fun p q U _ h => by
    rw [GlobalTheory.MumRigidZero.lift_comp_left]; exact prod_lam (p ≫ a) (q ≫ b) h
  obtain ⟨l₁, l₂, hl₁, hl₂, cl₁, cl₂, vl⟩ := exists_laws M₀ c₀
  let φ3 := law1φ B₀ (x3 B₀ 0) (x3 B₀ 1) (x3 B₀ 2)
  let β₃ : (G3 B₀).left ⟶ (G3 B).left := (lift (x3 B₀ 0 ≫ a) (lift (x3 B₀ 1 ≫ a) (x3 B₀ 2 ≫ b))).left
  have fe3 : FormEq (fun I => β₃ ≫ thφ B (x3 B) I) thε (flatφ (lamφ B) (fun k => φ3 k ≫ β₂)) (flatε lamε lawε) :=
    fun U _ h => by
      have e₁ := prod_cub (x3 B₀ 0 ≫ a) (x3 B₀ 1 ≫ a) (x3 B₀ 2 ≫ b) h
      have e₂ := prod_law₁ (x3 B₀ 0) (x3 B₀ 1) (x3 B₀ 2) (fun χ => ∏ i, h ((χ ≫ β₂) ≫ lamφ B i) ^ lamε i)
      rw [id₃] at e₂
      simp only [Over.id_left, Category.id_comp, Hlam, MonObj.mul_comp] at e₂
      rw [e₁, prod_flat, e₂]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
  obtain ⟨g₃, hg₃, hv₃⟩ := exists_gen M.isLB fe3 (LB.pullGen M.L (thφ B (x3 B)) thε c.t β₃)
    (DVR.pullGen_isGen _ _ _ _ c.isGen β₃)
  have ht₃ := nest_isGen (L := M.L) (φ := lamφ B) (δ := lamε) hg₃
  have Ft3 : ∀ {T₀ : Over S} (p p' q : T₀ ⟶ B₀) (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.L.ι), Good M.L z₀ J₀ →
      val (L := abelian₂ B M.L) (nest M.L (lamφ B) lamε (fun k => φ3 k ≫ β₂) lawε g₃) (lift p (lift p' q)).left z₀ (ind B J₀) =
        cubV c z₀ J₀ (p ≫ a) (p' ≫ a) (q ≫ b) := by
    intro T₀ p p' q z₀ J₀ hJ₀
    show val (L := LB.LinComb M.L (lamφ B) lamε) (nest M.L (lamφ B) lamε (fun k => φ3 k ≫ β₂) lawε g₃) _ z₀ (ind B J₀) = _
    rw [val_nest hg₃ _ (good_ind hJ₀) hJ₀]
    simp only [adj_ind M.isLB hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
    rw [hv₃ _ _ z₀ J₀ hJ₀]
    refine (val_pull hJ₀ _ _ _).trans ?_
    refine congrArg (fun r => val (L := M.L) (φ := thφ B (x3 B)) (ε := thε) c.t r z₀ J₀) ?_
    show (lift p (lift p' q) ≫ lift (x3 B₀ 0 ≫ a) (lift (x3 B₀ 1 ≫ a) (x3 B₀ 2 ≫ b))).left =
      (lift (p ≫ a) (lift (p' ≫ a) (q ≫ b))).left
    simp only [comp_lift, ← Category.assoc, cartesian_lift_three_comp_projection]
    rfl
  have Fa3 : ∀ {T₀ : Over S} (p p' q : T₀ ⟶ B₀) (z₀ : T₀.left) (J₀' : (T₀.left ⟶ B₀.left) → M₀.L.ι),
      Good M₀.L z₀ J₀' → val (L := abelian₂ B₀ M₀.L) l₁ (lift p (lift p' q)).left z₀ (ind B₀ J₀') = cubV c₀ z₀ J₀' p p' q := by
    intro T₀ p p' q z₀ J₀' hJ₀'
    show val (L := lamLB M₀) l₁ _ z₀ (ind B₀ J₀') = _
    rw [(vl z₀ (ind B₀ J₀') (good_ind hJ₀') J₀' hJ₀').1 p p' q, adj_ind M₀.isLB hJ₀', adj_ind M₀.isLB hJ₀',
      adj_ind M₀.isLB hJ₀']
    simp
  have Fp3 : ∀ {T₀ : Over S} (p p' q : T₀ ⟶ B₀) (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.L.ι)
      (J₀' : (T₀.left ⟶ B₀.left) → M₀.L.ι),
      pw w φ3 lawε (lift p (lift p' q)).left z₀ (fun k => ind B J₀ ((lift p (lift p' q)).left ≫ φ3 k ≫ β₂))
        (fun k => ind B₀ J₀' ((lift p (lift p' q)).left ≫ φ3 k)) =
        lamVal w (lift (p * p') q).left z₀ J₀ J₀' * (lamVal w (lift p q).left z₀ J₀ J₀')⁻¹ *
          (lamVal w (lift p' q).left z₀ J₀ J₀')⁻¹ := by
    intro T₀ p p' q z₀ J₀ J₀'
    rw [pw_eq]; exact prod_law₁ p p' q (fun χ => lamVal w χ z₀ J₀ J₀')
  have sj3 : Function.Surjective ((snd B₀ (B₀ ⊗ B₀)).left ≫ (snd B₀ B₀).left ≫ B₀.hom).appTop.hom :=
    surj_comp (surj_snd hG hB₀ _) (surj_comp (surj_snd hG hB₀ _) (hG _ _ hB₀).2)
  have he3 : (lift (1 : 𝟙_ (Over S) ⟶ B₀) (lift 1 1)).left ≫ (snd B₀ (B₀ ⊗ B₀)).left ≫ (snd B₀ B₀).left ≫ B₀.hom =
      𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w (lift (1 : 𝟙_ (Over S) ⟶ B₀) (lift 1 1))
  have R3 := rigid_pw w hw hL hL' φ3 lawε hl₁ ht₃ _ _ he3 sj3 (fun y₀ => by
    obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt M.isLB y₀
    obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt M₀.isLB y₀
    refine ⟨ind B J₁, ind B₀ J₁', good_ind hJ₁, good_ind hJ₁', ?_⟩
    rw [Ft3 (T₀ := 𝟙_ (Over S)) 1 1 1 y₀ J₁ hJ₁, Fp3, Fa3 1 1 1 y₀ J₁' hJ₁', GlobalTheory.MumRigidZero.one_comp_hom a,
      _root_.mul_one, (isCub_cubV c hJ₁).face, (isCub_cubV c₀ hJ₁').face, hn (𝟙_ (Over S)) y₀ J₁ J₁' hJ₁ hJ₁']
    simp)
  have E3 := R3 T.left (lift x (lift x' y)).left z (ind B J) (ind B₀ J') (good_ind hJ) (good_ind hJ')
  rw [Ft3 x x' y z J hJ, Fp3, Fa3 x x' y z J' hJ'] at E3
  rw [E3]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.MumfordE8Bimultiplicative

end

open GlobalTheory.Mum GlobalTheory.Mum.E8Ring

namespace GlobalTheory.MumfordE8Bimultiplicative

end GlobalTheory.MumfordE8Bimultiplicative
