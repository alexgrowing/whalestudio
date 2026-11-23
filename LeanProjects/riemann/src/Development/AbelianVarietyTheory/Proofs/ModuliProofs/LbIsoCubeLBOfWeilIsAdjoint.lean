import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenTranslEqPairing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIsGenOfInvariant
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGenRosati
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsMemNonzeroLocus

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.AdjointOfPairing

open ReciprocityTheory.ChartRestriction.G.Out CommutatorPairing DescentPairing

theorem lbIso_of_gen {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k)))) (ht : t.IsGen) :
    LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') := by
  have le : ∀ p : (K' → L.ι) × (K → L.ι), LB.wchart L φ' p.1 ⊓ LB.wchart L φ p.2 ≤
      LB.wchart L (Sum.elim φ' φ) (Sum.elim p.1 p.2) := fun p y hy => Set.mem_iInter.2 fun k => by
    rcases k with k | k
    exacts [Set.mem_iInter.1 hy.1 k, Set.mem_iInter.1 hy.2 k]
  refine gen_chartPull (A' := LB.div (LB.LinComb L φ' ε') (LB.LinComb L φ ε)) (h := 𝟙 Y)
    (A := LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k)))
    ⟨fun p => Sum.elim p.1 p.2, le, fun y p q hp hq => ?_⟩ t ht
  refine (gm_div (LB.LinComb L φ ε) (LB.LinComb L φ' ε') (𝟙 Y) y p q ⟨hp, hq⟩).trans
    (Eq.trans ?_ (gm_linComb L _ _ (𝟙 Y) y _ _ (le p hp) (le q hq)).symm)
  refine (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L φ' ε' (𝟙 Y) y _ _ hp.1 hq.1)
    (gm_linComb L φ ε (𝟙 Y) y _ _ hp.2 hq.2)).trans (Eq.trans ?_ (Fintype.prod_sum_type _).symm)
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rfl

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem exists_gen_pairing (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {L : RigLB A} (cb : CubicalStr A L)
    {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (n : ℕ) (x : T ⟶ A) (hx : x ^ n = 1) :
    ∃ u : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(mulT A T n ≫ translPt A x).left, (snd T A ^ n).left] ![1, -1]),
      u.IsGen ∧ ∀ (y : T ⟶ A) (c : Γ(T.left, ⊤)ˣ), y ^ n = 1 → WeilIs A L.L n x y c →
        ∀ (Z : Over S) (t : Z ⟶ T) (w : Z ⟶ A) (z : Z.left) (J), Good L.L z J →
          val u (lift t ((t ≫ y) * w)).left z J = val u (lift t w).left z J * gm t.left z ⊤ c := by
  obtain ⟨θx, rfl, -⟩ := exists_theta cb p₀ hT n x hx
  obtain ⟨u, hu, vu⟩ := exists_triv cb p₀ hT n θx
  refine ⟨u, hu, fun y c hy hc Z t w z J hJ => ?_⟩
  obtain ⟨θy, rfl, vy⟩ := exists_theta cb p₀ hT n y hy
  have hcm := (commIsOf_iff L.isLB θx θy c).1 ((GlobalLift.weilIs_iff_commIsOf hG hA L.isLB θx θy c).1 hc)
  obtain ⟨s, hs⟩ := vu _ t z J hJ
  obtain ⟨s', hs'⟩ := vy _ t z J hJ
  have k₁ := hcm _ t w z J hJ
  have k₂ := cubN_transl (isCub_cubV cb hJ) n (t ≫ θy.pt) w (t ≫ θx.pt)
    ((map_pow (preHom t) θy.pt n).symm.trans (by rw [hy]; exact map_one _))
  refine (hs _).trans (Eq.trans ?_ (congrArg₂ (· * ·) (hs _) k₁.symm).symm)
  have t₁ := hs' w
  have t₂ := hs' ((t ≫ θx.pt) * w)
  apply Additive.ofMul.injective
  have E := fun {p q : (Z.left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E t₁; have a₂ := E t₂; have a₃ := E k₂
  simp only [commVal, ofMul_mul, ofMul_inv] at a₁ a₂ a₃ ⊢
  linear_combination (norm := abel) a₃ + a₁ - a₂

omit [IsCommMonObj A] in

theorem prod_mulT {T Z : Over S} (n : ℕ) (x : T ⟶ A) (t : Z ⟶ T) (w : Z ⟶ A) {U : Type} [CommGroup U]
    (h : (Z.left ⟶ A.left) → U) :
    ∏ i : Fin 2, h ((lift t w).left ≫ ![(mulT A T n ≫ translPt A x).left, (snd T A ^ n).left] i) ^ ![(1 : ℤ), -1] i =
      h ((t ≫ x) * w ^ n).left * (h (w ^ n).left)⁻¹ := by
  rw [Fin.prod_univ_two]
  show h (lift t w ≫ mulT A T n ≫ translPt A x).left ^ (1 : ℤ) * h (lift t w ≫ snd T A ^ n).left ^ (-1 : ℤ) = _
  rw [mulT, comp_lift_assoc, lift_fst, lift_translPt, MonObj.comp_pow, lift_snd, zpow_one, zpow_neg_one]

theorem exists_gen_of_formEq_zero {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  obtain ⟨t, ht, -⟩ := exists_gen hL (φ' := φ) (ε' := ε) (fun U _ g => (Fintype.prod_empty _).trans (h U g).symm)
    (LB.oneGen L (Y := Y)) (fun i j => (map_one _).trans
      ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  exact ⟨t, ht⟩

theorem exists_gen_fibre (hl : Laws) {k : Type} [Field k] [IsAlgClosed k] (P : PolAV (Sp k)) (a a' : P.A ⟶ P.A)
    [IsMonHom a] [IsMonHom a'] (n : ℕ) (hn : (n : k) ≠ 0) (x : 𝟙_ (Over (Sp k)) ⟶ P.A) (hx : x ^ n = 1)
    (H : ∀ (y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ), y ^ n = 1 →
      WeilIs P.A P.L n (x ≫ a) y c → WeilIs P.A P.L n x (y ≫ a') c) :
    ∃ t : LB.Gen (LB.LinComb P.L
      (fun i => (lift (toUnit P.A ≫ x) (𝟙 P.A)).left ≫ rosatiφ P.A a a' i) rosatiε), t.IsGen := by
  have := P.isAb.comm
  obtain ⟨rig, hrig⟩ := P.rigid
  let L : RigLB P.A := ⟨P.L, rig, P.isLB, hrig⟩
  obtain ⟨⟨cb⟩, -⟩ := hl.cube _ P L rfl
  let p₀ : (𝟙_ (Over (Sp k))).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  have hT : ∀ p : (𝟙_ (Over (Sp k))).left, p = p₀ := fun p => Subsingleton.elim (α := PrimeSpectrum k) p p₀
  have hxa : (x ≫ a) ^ n = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  obtain ⟨u₁, hu₁, v₁⟩ := exists_gen_pairing hl.globalFns P.isAb cb p₀ hT n (x ≫ a) hxa
  obtain ⟨u₂, hu₂, v₂⟩ := exists_gen_pairing hl.globalFns P.isAb cb p₀ hT n x hx
  obtain ⟨σ, hσ⟩ := exists_frame P.isLB (K := Fin 2) ![(x ≫ a).left, x.left] ![-1, 1] p₀ hT
  obtain ⟨u, hu, vu⟩ := exists_gen P.isLB
    (φ' := fun i => (mulA P.A n).left ≫ (lift (toUnit P.A ≫ x) (𝟙 P.A)).left ≫ rosatiφ P.A a a' i) (ε' := rosatiε)
    (fun U _ h => by
      have e : ∀ i, (mulA P.A n).left ≫ (lift (toUnit P.A ≫ x) (𝟙 P.A)).left ≫ rosatiφ P.A a a' i =
          (lift (toUnit P.A ≫ x) (𝟙 P.A ^ n)).left ≫ rosatiφ P.A a a' i := fun i => by
        rw [← Category.assoc, ← Over.comp_left, comp_lift, comp_toUnit_assoc, Category.comp_id]
      have e' : (𝟙 P.A ^ n) ≫ a' = a' ^ n := by rw [MonObj.pow_comp, Category.id_comp]
      have f : ∏ i : Fin 2, h ((toUnit P.A).left ≫ ![(x ≫ a).left, x.left] i) ^ ![(-1 : ℤ), 1] i =
          (h (toUnit P.A ≫ x ≫ a).left)⁻¹ * h (toUnit P.A ≫ x).left := by
        rw [Fin.prod_univ_two]
        exact congrArg₂ (· * ·) (zpow_neg_one _) (zpow_one _)
      refine (DVR.prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := Fin 2) (U := U) _
        (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _ (prod_mulT n (x ≫ a) (toUnit P.A) (𝟙 P.A) h)
        (DVR.prod_neg _ _ (prod_mulT n x (toUnit P.A) a' h))) f).trans ?_
      simp only [e]
      rw [prod_ros, e', Category.assoc]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen P.L _ _ _ _ (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ u₁ (lift (toUnit P.A) (𝟙 P.A)).left)
      (LB.invGen P.L _ _ (LB.pullGen P.L _ _ u₂ (lift (toUnit P.A) a').left))) (LB.pullGen P.L _ _ σ (toUnit P.A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₁ _)
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₂ _))) (DVR.pullGen_isGen _ _ _ _ hσ _))
  have vw : ∀ (w : P.A ⟶ P.A) (z : P.A.left) (J), Good P.L z J → val u w.left z J =
      val u₁ (lift (toUnit P.A) w).left z J * (val u₂ (lift (toUnit P.A) (w ≫ a')).left z J)⁻¹ *
        val σ (toUnit P.A).left z J := fun w z J hJ => by
    refine (vu _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((val_pull hJ _ _ _).trans ?_) ((val_inv _ _).trans (congrArg (·⁻¹)
        ((val_pull hJ _ _ _).trans ?_))))) ((val_pull hJ _ _ _).trans ?_)))
    · rw [← Over.comp_left, comp_lift, comp_toUnit, Category.comp_id]
    · rw [← Over.comp_left, comp_lift, comp_toUnit]
    · rw [← Over.comp_left, comp_toUnit]
  refine exists_isGen_of_invariant P.isLB _ _ (mulA P.A n).left
    (I := {y : 𝟙_ (Over (Sp k)) ⟶ P.A // y ^ n = 1}) (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left)
    (fun y => by
      rw [← Over.comp_left, GoodPoint.comp_mulA, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one, _root_.one_mul])
    (fun U f hf => torsion_invariant_descends (fun S _ Q m hm =>
      ⟨(hl.mulN S Q m hm).1, (hl.mulN S Q m hm).2.1, (hl.mulN S Q m hm).2.2.1, (hl.mulN S Q m hm).2.2.2.1⟩)
      k P n hn U f fun y hy => hf ⟨y, hy⟩) _ (fun _ => rfl) u hu fun y z J hJ => ?_
  obtain ⟨c, hc, -⟩ := (hl.weil _ P n _).1 (x ≫ a) y.1 hxa y.2
  have hya : (y.1 ≫ a') ^ n = 1 := by rw [← MonObj.pow_comp, y.2, MonObj.one_comp]
  refine (vw _ z J hJ).trans (Eq.trans ?_ (vw (𝟙 P.A) z J hJ).symm)
  rw [v₁ y.1 c y.2 hc _ _ _ z J hJ, MonObj.mul_comp, Category.assoc, v₂ _ c hya (H y.1 c y.2 hc) _ _ _ z J hJ,
    mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.mul_one]

end GlobalTheory.AdjointOfPairing

namespace GlobalTheory

end GlobalTheory
