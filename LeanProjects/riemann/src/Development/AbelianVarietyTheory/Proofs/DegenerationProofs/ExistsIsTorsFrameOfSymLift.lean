import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
noncomputable section
namespace GlobalTheory.TorsFrame

open CommPairing GlobalLift ThetaCoord

theorem val_powGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n := map_pow _ _ _

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem exists_pow_two (hL : L.IsLB) {Y : Scheme.{0}} {f g : Y ⟶ A.left} {k : ℤ} (m : ℕ)
    {u : LB.Gen (LB.LinComb L (K := Fin 2) ![f, g] ![k, -k])} (hu : u.IsGen) :
    ∃ u' : LB.Gen (LB.LinComb L (K := Fin 2) ![f, g] ![m * k, -(m * k)]), u'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val u' r z J = val u r z J ^ m := by
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![f, g]) (ε' := ![m * k, -(m * k)])
    (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_neg])
    (GeneratorPullback.powGen L _ _ u m) (DVR.powGen_isGen _ _ _ _ hu _)
  exact ⟨t, ht, fun Z r z J hJ => (hv Z r z J hJ).trans (val_powGen _ _ _ _ _)⟩

theorem exists_symLift_pow (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {k : ℤ} {q : ℕ} {x : T ⟶ A}
    {θ : ThetaGrp A L k T} (H : SymLift A L k q x θ) (m : ℕ) :
    ∃ θ' : ThetaGrp A L (m * k) T, SymLift A L (m * k) q x θ' ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J → tval θ' r z J = tval θ r z J ^ m := by
  obtain ⟨ν, hν, -⟩ := H.sym
  obtain ⟨u, hu, vu⟩ := exists_pow_two hL m (u := θ.φ) θ.isGen
  obtain ⟨ν', hν', vν⟩ := exists_pow_two hL m (u := ν) hν
  have vu' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      tval (⟨θ.pt, u, hu⟩ : ThetaGrp A L (m * k) T) r z J = tval θ r z J ^ m := vu
  have vν' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      nval (k := m * k) ν' r z J = nval ν r z J ^ m := vν
  refine ⟨⟨θ.pt, u, hu⟩, symLift_of_tval hL H.pt_eq (ν := ν') hν' (fun T' π z J hJ p => ?_)
    (fun T' π z J hJ p => ?_), vu'⟩
  · rw [Finset.prod_congr rfl fun j _ => vu' _ _ z J hJ, Finset.prod_pow, prod_tval H π hJ p, one_pow]
  · rw [vu' _ _ z J hJ, vu' _ _ z J hJ, vν' _ _ z J hJ, vν' _ _ z J hJ, ← inv_pow, ← mul_pow, ← mul_pow, ← mul_pow,
      sym_tval hG hA hL H hν π hJ p, one_pow]

theorem eSec_hom : eSec A ≫ A.hom = 𝟙 S := Over.w η[A]

theorem eSec_mulA (n : ℕ) : eSec A ≫ (mulA A n).left = eSec A := by
  have e : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := by rw [Hom.one_def, toUnit_unit, Category.id_comp]
  rw [eSec, ← Over.comp_left, MonObj.comp_pow, Category.comp_id, e, one_pow]

theorem one_left : (1 : T ⟶ A).left = T.hom ≫ eSec A := rfl

theorem exists_norm (hL : L.IsLB) {rig : LB.Gen (L.pull (eSec A))} (hr : rig.IsGen) {n : ℕ}
    {α₀ : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1])} (h₀ : α₀.IsGen) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good L z J → val α (r ≫ eSec A) z J =
        val (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig r z J ^ (n ^ 2) *
          (val (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig r z J)⁻¹ := by
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![𝟙 A.left, (mulA A n).left]) (ε' := ![(n : ℤ) ^ 2, -1])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, eSec_mulA, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L _ _ _ _ α₀ (LB.pullGen L _ _ (LB.mulGen L _ _ _ _
      (LB.mulGen L _ _ _ _ (GeneratorPullback.powGen L (fun _ : PUnit => eSec A) (fun _ => 1) rig (n ^ 2))
        (LB.invGen L (fun _ : PUnit => eSec A) (fun _ => 1) rig))
      (LB.invGen L _ _ (LB.pullGen L _ _ α₀ (eSec A)))) A.hom))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ h₀ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ hr _) (DVR.invGen_isGen _ _ _ _ hr))
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ h₀ _))) _))
  refine ⟨t, ht, fun Z r z J hJ => ?_⟩
  have e : (r ≫ eSec A) ≫ A.hom = r := by rw [Category.assoc, eSec_hom, Category.comp_id]
  rw [hv _ _ z J hJ, val_mul hJ, val_pull hJ, e, val_mul hJ, val_mul hJ, val_inv, val_inv, val_pull hJ, val_powGen,
    mul_comm, inv_mul_cancel_right]

theorem val_rigT (rig : LB.Gen (L.pull (eSec A))) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J} (hJ : Good L z J) :
    val (rigT A L rig T 1) r z J =
      val (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig (r ≫ T.hom) z J := by
  rw [val_of (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig (r ≫ T.hom) z J
    (fun _ => J (r ≫ T.hom ≫ eSec A)) (fun _ => by rw [Category.assoc])]
  have hm := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  refine (map_zpow _ _ _).trans ((zpow_one _).trans ((gm_res r z _ hm _).trans ?_))
  exact gm_pull r T.hom z _ (show T.hom (r z) ∈ LB.wchart L (fun _ : PUnit => eSec A)
    (fun _ => J (r ≫ T.hom ≫ eSec A)) from Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hm 0) _

theorem tval_pow (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {ν : LB.Gen (negLB A L 1 T)}
    (hν : ν.IsGen) {n : ℕ} (hn : Odd n)
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1])} (hα : α.IsGen)
    {y : T ⟶ A} (hy : y ^ (n ^ 2) = 1) {θ : ThetaGrp A L (n ^ 2 : ℕ) T} (H : SymLift A L (n ^ 2 : ℕ) (n ^ 2) y θ)
    {z : T.left} {J} (hJ : Good L z J) :
    tval θ (lift (𝟙 T) (1 : T ⟶ A)).left z J ^ (n ^ 2) =
      val α (1 : T ⟶ A).left z J ^ (n ^ 2) * val α (1 : T ⟶ A).left z J *
        (val α y.left z J ^ (n ^ 2) * val α (y ^ n).left z J)⁻¹ := by
  have e₁ : ∀ p : T ⊗ A ⟶ A, p.left ≫ (mulA A n).left = (p ^ n).left := fun p => by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨β, hβ, vβ⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ (n ^ 2)).left])
    (ε' := ![((n ^ 2 : ℕ) : ℤ) * (n ^ 2 : ℕ), -1])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₁, Category.comp_id, ← pow_mul, ← sq]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L _ _ _ _ (GeneratorPullback.powGen L _ _ (LB.pullGen L _ _ α (snd T A).left) (n ^ 2))
      (LB.pullGen L _ _ α (snd T A ^ n).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _) _)
      (DVR.pullGen_isGen _ _ _ _ hα _))
  have vβ' : ∀ p : T ⟶ A, bval (b := 1) β (lift (𝟙 T) p).left z J =
      val α p.left z J ^ (n ^ 2) * val α (p ^ n).left z J := fun p => by
    refine (vβ _ _ z J hJ).trans ?_
    rw [val_mul hJ, val_powGen, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, MonObj.comp_pow, lift_snd]
  obtain ⟨o, ho, vo⟩ := exists_symLift_one hL hν 1
  obtain ⟨θ₁, H₁, v₁⟩ := exists_symLift_mulPull hA hL (one_dvd (n ^ 2)) (b := 1) hβ hy (hy.symm ▸ ho)
  obtain ⟨θ₂, H₂, v₂⟩ := exists_symLift_pow hG hA hL H (n ^ 2)
  have e : tval θ₂ (lift (𝟙 T) (1 : T ⟶ A)).left z J = tval θ₁ (lift (𝟙 T) (1 : T ⟶ A)).left z J :=
    val_corr hJ (SymLiftOdd.symLift_unique hG hA hL hn.pow θ₂ θ₁ H₂ H₁) _
  rw [v₂ _ _ z J hJ, v₁ _ _ z J hJ, vo _ _ z J hJ, vβ', vβ', one_pow, _root_.mul_one, _root_.mul_one,
    Category.id_comp] at e
  exact e

end GlobalTheory.TorsFrame

namespace GlobalTheory

open TorsFrame CommPairing in

theorem exists_isTorsFrame_of_symLift : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (n : ℕ), Odd n → ∀ (T : Over S) (y x : T ⟶ P.A), y ^ (n ^ 2) = 1 → y ^ n = x → ∀ θ : ThetaGrp P.A P.L (n ^ 2 : ℕ) T, SymLift P.A P.L (n ^ 2 : ℕ) (n ^ 2) y θ → ∃ τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1)), IsTorsFrame P rig n x τ := by
  intro hLaw S _ P rig hr n hn T y x hy hx θ H
  subst hx
  have hL := P.isLB
  obtain ⟨α₀, h₀⟩ := hLaw.mulPull S P n
  obtain ⟨α, hα, vα⟩ := exists_norm hL hr h₀
  obtain ⟨ν, hν⟩ := exists_gen_negLB hLaw.globalFns S P 1 T
  have e₁ : y.left ≫ (mulA P.A n).left = (y ^ n).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have e₂ : (lift (𝟙 T) (1 : T ⟶ P.A)).left ≫ (snd T P.A).left = T.hom ≫ eSec P.A := by
    rw [← Over.comp_left, lift_snd, one_left]
  have e₃ : (lift (𝟙 T) (1 : T ⟶ P.A)).left ≫ (translPt P.A θ.pt).left = y.left := by
    rw [← Over.comp_left, translPt, comp_lift_assoc, lift_fst_assoc, lift_snd, Category.id_comp, H.pt_eq]
    exact congrArg (·.left) (_root_.mul_one y)
  obtain ⟨τ, hτ, vτ⟩ := exists_gen hL (φ' := fun _ : Fin 1 => (y ^ n).left) (ε' := fun _ => 1)
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₁, e₂, e₃, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen P.L _ _ _ _ (GeneratorPullback.powGen P.L _ _
        (LB.pullGen P.L (fun _ : PUnit => eSec P.A) (fun _ => 1) rig T.hom) (n ^ 2))
      (LB.invGen P.L _ _ (LB.mulGen P.L _ _ _ _
        (LB.pullGen P.L ![(snd T P.A).left, (translPt P.A θ.pt).left] ![(n ^ 2 : ℕ), -(n ^ 2 : ℕ)] θ.φ
          (lift (𝟙 T) (1 : T ⟶ P.A)).left) (LB.pullGen P.L _ _ α y.left))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hr _) _)
      (DVR.invGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ θ.isGen _)
        (DVR.pullGen_isGen _ _ _ _ hα _))))
  refine ⟨τ, by rw [← pow_mul, ← sq, hy], hτ, α, hα, corr_of_val hL fun z J hJ => ?_,
    corr_of_val hL fun z J hJ => ?_⟩
  · refine (val_pull hJ _ _ _).trans ((vα _ _ z J hJ).trans (Eq.symm ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((map_zpow _ _ _).trans ?_) (val_inv _ _)))))
    rw [← Nat.cast_pow, zpow_natCast]; rfl
  · have a : val (powFrame P.A P.L (y ^ n) τ ((n : ℤ) ^ 2)) (𝟙 _) z J = val τ (𝟙 _) z J ^ (n ^ 2) :=
      (map_zpow _ _ _).trans (by rw [← Nat.cast_pow, zpow_natCast]; rfl)
    have b := tval_pow hLaw.globalFns P.isAb hL hν hn hα hy H hJ
    have c : val (LB.pullGen P.L ![(snd T P.A).left, (translPt P.A θ.pt).left] ![(n ^ 2 : ℕ), -(n ^ 2 : ℕ)] θ.φ
        (lift (𝟙 T) (1 : T ⟶ P.A)).left) (𝟙 T.left) z J = tval θ (lift (𝟙 T) (1 : T ⟶ P.A)).left z J :=
      (val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)
    rw [one_left, vα _ _ z J hJ] at b
    rw [a, vτ _ _ z J hJ, val_mul hJ, val_mul hJ, val_inv, val_mul hJ, c, val_powGen, val_pull hJ, val_pull hJ,
      val_pull hJ, val_rigT rig _ z hJ, Category.id_comp, Category.id_comp, Category.id_comp, mul_pow, inv_pow, mul_pow, b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module

end GlobalTheory
end
