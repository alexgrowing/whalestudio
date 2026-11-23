import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsE8WeightedBundle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSharpBasisSharpBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ActionProductEqOne
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilIsOfLbIsoCubeLB
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.E8Fibration.PairVal

open GlobalTheory.PairingOfLam GlobalTheory.DescentPairing GlobalTheory.AdjointOfPairing

variable {S : Scheme.{0}}

theorem weilIs_of_lbIso {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {N : RigLB A}
    (cN : CubicalStr A N) (f g f' g' : B ⟶ A) [IsMonHom f] [IsMonHom g] [IsMonHom f'] [IsMonHom g']
    (H : LBIso (cubeLB A ![fst B B ≫ f, snd B B ≫ g] N.L) (cubeLB A ![fst B B ≫ f', snd B B ≫ g'] N.L))
    {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (n : ℕ) (y z : T ⟶ B) (hy : y ^ n = 1) (hz : z ^ n = 1)
    (e : Γ(T.left, ⊤)ˣ) (he : WeilIs A N.L n (y ≫ f') (z ≫ g') e) : WeilIs A N.L n (y ≫ f) (z ≫ g) e := by
  have hyf : (y ≫ f) ^ n = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have hyc : (y ≫ f') ^ n = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have hzg : (z ≫ g) ^ n = 1 := by rw [← MonObj.pow_comp, hz, MonObj.one_comp]
  obtain ⟨e', hr⟩ := WeilCube.exists_isRatio cN n _ _ hyf hzg
  have he' := (WeilCube.weilIs_iff cN hG hA hyf hzg hr e').2 rfl
  refine (WeilCube.weilIs_iff cN hG hA hyf hzg hr e).2 (unit_ext fun p _ => ?_)
  obtain ⟨t, ht, v⟩ := exists_gen_lam hG hA cN p₀ hT f' g' n y hyc
  obtain ⟨t', ht', v'⟩ := exists_gen_lam hG hA cN p₀ hT f g n y hyf
  choose J hJ using fun χ : T.left ⟶ A.left => exists_chart N.isLB (χ p)
  have r := val_ratio N.isLB N.isLB H _ t ht t' ht' (fst T B).left (WeilCube.surj_fst hG hB T)
    (lift (𝟙 T) z).left (lift (𝟙 T) (1 : T ⟶ B)).left
    (by rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, lift_fst_assoc, lift_fst_assoc,
      MonObj.comp_pow, MonObj.comp_pow, lift_snd, lift_snd, hz, one_pow])
    (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]) p hJ hJ
  rw [v z e hz he p J hJ, v' z e' hz he' p J hJ] at r
  apply Additive.ofMul.injective
  have r' := congrArg Additive.ofMul r
  simp only [ofMul_mul, ofMul_inv] at r'
  linear_combination (norm := abel) r'

theorem exists_hom {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj B] {pr : Fin 8 → (A ⟶ B)} (hP : IsProd pr)
    (s : Fin 8 → ℤ) : ∃ f : B ⟶ A, IsMonHom f ∧ ∀ (T : Over S) (x : T ⟶ B) (a : Fin 8), (x ≫ f) ≫ pr a = x ^ s a := by
  obtain ⟨f, hf, -⟩ := hP.2 B (fun a => 𝟙 B ^ s a)
  have h : ∀ (T : Over S) (x : T ⟶ B) (a : Fin 8), (x ≫ f) ≫ pr a = x ^ s a := fun T x a => by
    rw [Category.assoc, hf a]
    exact (map_zpow (PrimPic.preH (G := B) x) _ _).trans (congrArg (· ^ s a) (Category.comp_id x))
  refine ⟨f, isMonHom_of_mul f fun T x y => ?_, h⟩
  refine (hP.2 T fun a => ((x * y) ≫ f) ≫ pr a).unique (fun a => rfl) fun a => ?_
  haveI := hP.1 a
  rw [MonObj.mul_comp, h, h, h, mul_zpow]

theorem bil_zpow {B : Over S} [GrpObj B] [IsCommMonObj B] (M : RigLB B) (cub : CubicalStr B M) {T : Over S}
    (m : Matrix (Fin 8) (Fin 8) ℤ) (s t : Fin 8 → ℤ) (x y : T ⟶ B) :
    PrimPic.bil (GlobalTheory.CechPic.cls M.L M.isLB) m (fun a => x ^ s a) (fun b => y ^ t b) =
      dotProduct s (m.mulVec t) • PrimPic.lam (GlobalTheory.CechPic.cls M.L M.isLB) x y := by
  have hl : ∀ (k : ℤ) (u v : T ⟶ B), PrimPic.lam (GlobalTheory.CechPic.cls M.L M.isLB) (u ^ k) v =
      k • PrimPic.lam (GlobalTheory.CechPic.cls M.L M.isLB) u v := fun k u v =>
    map_zsmul (PrimPic.lamHom M cub v) k (Additive.ofMul u)
  have hr : ∀ (k : ℤ) (u v : T ⟶ B), PrimPic.lam (GlobalTheory.CechPic.cls M.L M.isLB) u (v ^ k) =
      k • PrimPic.lam (GlobalTheory.CechPic.cls M.L M.isLB) u v := fun k u v => by
    rw [PrimPic.lam_comm, hl, PrimPic.lam_comm]
  simp only [PrimPic.bil, hl, hr, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_smul, smul_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  ring

theorem weilIs_of_form_eq : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ) (K : Type) [Field K] [IsAlgClosed K] (P' : PolAV (Sp K))
  (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L → ∀ (N : ℕ), 0 < N → ∀ (s t s' t' : Fin 8 → ℤ),
  dotProduct s ((E8Fibration.e8 W).mulVec t) = dotProduct s' ((E8Fibration.e8 W).mulVec t') →
  ∀ (p q : Out.baseOver (Sp K) ⟶ B), p ^ N = 1 → q ^ N = 1 →
  ∀ (x y x' y' : Out.baseOver (Sp K) ⟶ P'.A), (∀ u, x ≫ pr u = p ^ s u) → (∀ u, y ≫ pr u = q ^ t u) →
    (∀ u, x' ≫ pr u = p ^ s' u) → (∀ u, y' ≫ pr u = q ^ t' u) →
    ∀ c, Out.WeilIs P'.A P'.L N x y c → Out.WeilIs P'.A P'.L N x' y' c := by
  intro W _ gQ K _ _ P' B _ _ M pr hF hP hE N _ s t s' t' hst p q hp hq x y x' y' hx hy hx' hy' c hc
  letI := P'.isAb.comm
  obtain ⟨cub⟩ := hF.2.2.1
  obtain ⟨r, hr, ⟨cL⟩⟩ := GlobalTheory.PolAV_exists_cubical GlobalTheory.abelianSchemeLaws_all.1.cube P'
  obtain ⟨f, hfm, hf⟩ := exists_hom hP s
  obtain ⟨g, hgm, hg⟩ := exists_hom hP t
  obtain ⟨f', hfm', hf'⟩ := exists_hom hP s'
  obtain ⟨g', hgm', hg'⟩ := exists_hom hP t'
  have ex : x = p ≫ f := (hP.2 _ fun u => p ^ s u).unique hx (hf _ p)
  have ey : y = q ≫ g := (hP.2 _ fun u => q ^ t u).unique hy (hg _ q)
  have ex' : x' = p ≫ f' := (hP.2 _ fun u => p ^ s' u).unique hx' (hf' _ p)
  have ey' : y' = q ≫ g' := (hP.2 _ fun u => q ^ t' u).unique hy' (hg' _ q)
  subst ex ey ex' ey'
  have hc₁ : (cubeLB P'.A ![fst B B ≫ f', snd B B ≫ g'] P'.L).IsLB := LB.isLB_linComb P'.isLB _ _
  have hc₂ : (cubeLB P'.A ![fst B B ≫ f, snd B B ≫ g] P'.L).IsLB := LB.isLB_linComb P'.isLB _ _
  have H : LBIso (cubeLB P'.A ![fst B B ≫ f', snd B B ≫ g'] P'.L) (cubeLB P'.A ![fst B B ≫ f, snd B B ≫ g] P'.L) := by
    refine (GlobalTheory.CechPic.cls_eq_iff hc₁ hc₂).1 ?_
    rw [PrimPic.cube_class_e8Bundle_eighth_power W pr hP.1 P'.L P'.isLB M cub hE, PrimPic.cube_class_e8Bundle_eighth_power W pr hP.1 P'.L P'.isLB M cub hE,
      funext (hf _ (fst B B)), funext (hg _ (snd B B)), funext (hf' _ (fst B B)), funext (hg' _ (snd B B)),
      bil_zpow M cub, bil_zpow M cub, hst]
  have : Subsingleton (Out.baseOver (Sp K)).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  exact weilIs_of_lbIso GlobalTheory.abelianSchemeLaws_all.1.globalFns P'.isAb hF.1 cL f' g' f g H
    (T := Out.baseOver (Sp K)) (default : PrimeSpectrum K) (fun _ => Subsingleton.elim _ _) N p q hp hq c hc

end GlobalTheory.Poinc.Sep.E8Fibration.PairVal

end
