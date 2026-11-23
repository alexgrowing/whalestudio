import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalTau
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UTau0

theorem uw_even_val : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) (f : D₀.P.A ⟶ D₀.P.A) [IsMonHom f]
    (uw : LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.UTau0.w0φ D₀ f) GlobalTheory.UTau0.w0ε)), uw.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (eSec D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ (T : Over (Sp R)) (x : T ⟶ D₀.P.A) (z : T.left) (J : (T.left ⟶ D₀.P.A.left) → D₀.P.L.ι), Good D₀.P.L z J →
      val uw x⁻¹.left z J * val D₀.sym x.left z J * cubV D₀.cub z J (x ≫ f) (x ≫ f)⁻¹ x⁻¹ =
        val uw x.left z J * cubV D₀.cub z J x x⁻¹ (x ≫ f) := by
  intro R _ _ D₀ f _ uw hu h₀ T x z J hJ
  let gL := LB.mulGen D₀.P.L _ _ _ _
      (LB.mulGen D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw ((𝟙 D₀.P.A)⁻¹).left) D₀.sym)
      (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (lift f (lift f⁻¹ (𝟙 D₀.P.A)⁻¹)).left)
  let gR := LB.mulGen D₀.P.L _ _ _ _ uw
      (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (lift (𝟙 D₀.P.A) (lift (𝟙 D₀.P.A)⁻¹ f)).left)
  have ev : ∀ {T' : Over (Sp R)} (σ : T' ⟶ D₀.P.A) {z : T'.left} {J}, Good D₀.P.L z J →
      val gL σ.left z J = val uw (σ ≫ (𝟙 D₀.P.A)⁻¹).left z J * val D₀.sym σ.left z J *
          cubV D₀.cub z J (σ ≫ f) (σ ≫ f⁻¹) (σ ≫ (𝟙 D₀.P.A)⁻¹) ∧
        val gR σ.left z J = val uw σ.left z J *
          cubV D₀.cub z J (σ ≫ 𝟙 D₀.P.A) (σ ≫ (𝟙 D₀.P.A)⁻¹) (σ ≫ f) := fun σ z J hJ =>
    ⟨(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        (val_pull hJ _ _ _) rfl)) (val_cub D₀.cub σ hJ _ _ _)),
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D₀.cub σ hJ _ _ _))⟩

  have pw : ∀ (V : Type) [CommGroup V] (k : (D₀.P.A.left ⟶ D₀.P.A.left) → V) (σ : D₀.P.A ⟶ D₀.P.A),
      ∏ i, k (σ.left ≫ w0φ D₀ f i) ^ w0ε i =
        k (σ * (σ ≫ f)).left * (k σ.left)⁻¹ * (k σ.left)⁻¹ * (k (σ ≫ f).left)⁻¹ *
          k (1 : D₀.P.A ⟶ D₀.P.A).left * k (1 : D₀.P.A ⟶ D₀.P.A).left := by
    intro V _ k σ
    have e₀ : σ.left ≫ (padd D₀.P.A (𝟙 _) f).left = (σ * (σ ≫ f)).left :=
      congrArg (fun q : D₀.P.A ⟶ D₀.P.A => q.left) ((MonObj.comp_mul _ _ _).trans (by rw [Category.comp_id]))
    have e₃ : σ.left ≫ (toUnit D₀.P.A ≫ η[D₀.P.A]).left = (1 : D₀.P.A ⟶ D₀.P.A).left := by
      rw [← Over.comp_left]; congr 1; simp [Hom.one_def]
    rw [Fin.prod_univ_four]
    show k (σ.left ≫ (padd D₀.P.A (𝟙 _) f).left) ^ (1 : ℤ) * k (σ.left ≫ 𝟙 _) ^ (-2 : ℤ) *
      k (σ.left ≫ f.left) ^ (-1 : ℤ) * k (σ.left ≫ (toUnit D₀.P.A ≫ η[D₀.P.A]).left) ^ (2 : ℤ) = _
    rw [e₀, e₃, Category.comp_id]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, Over.comp_left]
    abel
  have hL : val gL x.left z J = val gR x.left z J := by
    refine gen_unique' D₀.P.isLB (u := gL) (u' := gR) ?_ D₀.P.A.hom (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left
      (Over.w (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A)) (GlobalTheory.globalFns_holds _ _ D₀.P.isAb).2 ?_ ?_ ?_ T.left x.left z J hJ
    · intro V _ k
      have pw0 : ∏ i, k (w0φ D₀ f i) ^ w0ε i = _ :=
        (Finset.prod_congr rfl fun i _ => by rw [Over.id_left, Category.id_comp]).trans (pw V k (𝟙 D₀.P.A))
      have ps : ∏ i : Fin 2, k (![(ι[D₀.P.A]).left, 𝟙 D₀.P.A.left] i) ^ (![1, -1] : Fin 2 → ℤ) i =
          k (Over.Hom.left (𝟙 D₀.P.A)⁻¹) * (k (Over.Hom.left (𝟙 D₀.P.A)))⁻¹ := by
        have : (𝟙 D₀.P.A)⁻¹ = ι[D₀.P.A] := by simp [Hom.inv_def]
        rw [Fin.prod_univ_two, this]
        simp
      refine (DVR.prod_sum₂ (K := Fin 4) (K' := thK) (U := V) _ pw0 (prod_cub _ _ _ k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 2) (K' := thK) (U := V) _
          (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 2) (U := V) _ (pw V k _) ps) (prod_cub _ _ _ k)).symm)
      have a1 : 𝟙 D₀.P.A ≫ f = f := Category.id_comp f
      have a2 : (𝟙 D₀.P.A)⁻¹ ≫ f = f⁻¹ := by rw [GrpObj.inv_comp, Category.id_comp]
      have a3 : 𝟙 D₀.P.A * (𝟙 D₀.P.A)⁻¹ * f = f := by group
      have a4 : 𝟙 D₀.P.A * (𝟙 D₀.P.A)⁻¹ = 1 := by group
      have a5 : f * f⁻¹ * (𝟙 D₀.P.A)⁻¹ = (𝟙 D₀.P.A)⁻¹ := by group
      have a6 : f * f⁻¹ = 1 := by group
      have a7 : f * (𝟙 D₀.P.A)⁻¹ = (𝟙 D₀.P.A)⁻¹ * f := mul_comm _ _
      have a8 : f⁻¹ * (𝟙 D₀.P.A)⁻¹ = (𝟙 D₀.P.A)⁻¹ * f⁻¹ := mul_comm _ _
      rw [a1, a2, a3, a4, a5, a6, a7, a8]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · exact DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) D₀.sym_gen)
        (DVR.pullGen_isGen _ _ _ _ D₀.cub.isGen _)
    · exact DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.pullGen_isGen _ _ _ _ D₀.cub.isGen _)
    · intro y I hI
      have C : IsCub (cubV D₀.cub (T := 𝟙_ _) y I) := isCub_cubV D₀.cub hI
      have o : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left = eSec D₀.P.A := by simp [Hom.one_def, eSec]
      have u1 : val uw (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left y I = 1 := by
        have := val_corr hI h₀ (𝟙 _)
        rwa [val_pull hI, Category.id_comp, val_one, ← o] at this
      have s1 : val D₀.sym (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left y I = 1 := by
        have := val_corr hI D₀.sym_rig (𝟙 _)
        rwa [val_pull hI, Category.id_comp, val_one, ← o] at this
      have i1 : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) ≫ (𝟙 D₀.P.A)⁻¹ = 1 := by
        rw [GrpObj.comp_inv, Category.comp_id, inv_one]
      have f1 : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) ≫ f⁻¹ = 1 := by
        rw [GrpObj.comp_inv, MonObj.one_comp, inv_one]
      rw [(ev _ hI).1, (ev _ hI).2, i1, f1, MonObj.one_comp, Category.comp_id, u1, s1, C.face]; simp only [_root_.mul_one]
  have := (ev x hJ).1.symm.trans (hL.trans (ev x hJ).2)
  rwa [GrpObj.comp_inv, GrpObj.comp_inv, Category.comp_id] at this

end GlobalTheory.UTau0
