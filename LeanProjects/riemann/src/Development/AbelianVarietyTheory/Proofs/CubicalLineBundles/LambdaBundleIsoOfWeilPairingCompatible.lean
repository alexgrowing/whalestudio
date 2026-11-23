import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoCubeLBOfWeilIsAdjoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LamIsoOfPairings
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawTrivialityOnDenseFibresProductAbelianStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM.LamOfWeil

open ReciprocityTheory.ChartRestriction.G.Out CommutatorPairing DescentPairing IsoDescent

section

variable {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] [IsCommMonObj A]

abbrev sqφ (a b : T ⟶ A) : ULift.{0} (Finset (Fin 2)) → (T.left ⟶ A.left) := fun I => (psum A ![a, b] I.down).left

abbrev sqε : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)

theorem prod_sq (ρ : T' ⟶ T) (a b : T ⟶ A) {U : Type} [CommGroup U] (h : (T'.left ⟶ A.left) → U) :
    ∏ I, h (ρ.left ≫ sqφ a b I) ^ sqε I =
      h ((ρ ≫ a) * (ρ ≫ b)).left * (h (ρ ≫ a).left)⁻¹ * (h (ρ ≫ b).left)⁻¹ * h (1 : T' ⟶ A).left := by
  have p := NormRos.prod_square a b (fun q => h (ρ.left ≫ q))
  simp only [← Over.comp_left, MonObj.comp_mul, MonObj.comp_one] at p
  exact p

theorem exists_gen_axis {L : LB A.left} (hL : L.IsLB) (ρ : T' ⟶ T) (a b : T ⟶ A) (H : ρ ≫ a = 1 ∨ ρ ≫ b = 1) :
    ∃ t : LB.Gen (LB.LinComb L (fun I => ρ.left ≫ sqφ a b I) sqε), t.IsGen :=
  AdjointOfPairing.exists_gen_of_formEq_zero hL fun U _ h => by
    rw [prod_sq]
    rcases H with H | H
    · rw [H, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel
    · rw [H, _root_.mul_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel

end

theorem exists_gen_div {X X' Y Y' : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] (L : LB X) (L' : LB X')
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ) (f : Y' ⟶ Y)
    (H : LBIso (LB.LinComb L (fun k => f ≫ φ k) ε) (LB.LinComb L' (fun k => f ≫ φ' k) ε')) :
    ∃ t : LB.Gen ((LB.div (LB.LinComb L' φ' ε') (LB.LinComb L φ ε)).pull f), t.IsGen := by
  obtain ⟨w, hw⟩ := H.chartPull (chartPullOut L φ ε f _ fun _ => rfl) (chartPullOut L' φ' ε' f _ fun _ => rfl)
  exact gen_chartPull (IsoDescent.chartPullDiv _ _ f) w hw

variable {k : Type} [Field k] {X Y : Over (Sp k)} [GrpObj X] [GrpObj Y]

theorem exists_gen_fibre (hG : GlobalFnsSt) (hC : CubeSt) (P : PolAV (Sp k)) (f₁ : X ⟶ P.A) (f₂ : Y ⟶ P.A)
    [IsMonHom f₁] [IsMonHom f₂] (n : ℕ) (x : 𝟙_ (Over (Sp k)) ⟶ X) (hx : x ^ n = 1) :
    ∃ u : LB.Gen (LB.LinComb P.L (fun I => (mulA Y n).left ≫ (lift (toUnit Y ≫ x) (𝟙 Y)).left ≫
        sqφ (fst X Y ≫ f₁) (snd X Y ≫ f₂) I) sqε),
      u.IsGen ∧ ∀ (y : 𝟙_ (Over (Sp k)) ⟶ Y) (c : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ), y ^ n = 1 →
        WeilIs P.A P.L n (x ≫ f₁) (y ≫ f₂) c → ∀ (z : Y.left) (J), Good P.L z J →
          val u ((toUnit Y ≫ y) * 𝟙 Y).left z J = val u (𝟙 _) z J * gm (toUnit Y).left z ⊤ c := by
  have := P.isAb.comm
  obtain ⟨rig, hrig⟩ := P.rigid
  let L : RigLB P.A := ⟨P.L, rig, P.isLB, hrig⟩
  obtain ⟨⟨cb⟩, -⟩ := hC _ P L rfl
  let T := 𝟙_ (Over (Sp k))
  let p₀ : T.left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  have hT : ∀ p : T.left, p = p₀ := fun p => Subsingleton.elim (α := PrimeSpectrum k) p p₀
  have hx₁ : (x ≫ f₁) ^ n = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  obtain ⟨u₀, hu₀, v₀⟩ := PairingDetermines.exists_gen_transl hG P.isAb cb p₀ hT n (x ≫ f₁) hx₁
  obtain ⟨σ, hσ⟩ := exists_frame P.isLB (K := Fin 2) ![(x ≫ f₁).left, (1 : T ⟶ P.A).left] ![-1, 1] p₀ hT
  obtain ⟨u, hu, v⟩ := exists_gen P.isLB
    (φ' := fun I => (mulA Y n).left ≫ (lift (toUnit Y ≫ x) (𝟙 Y)).left ≫
      sqφ (fst X Y ≫ f₁) (snd X Y ≫ f₂) I) (ε' := sqε)
    (fun U _ h => by
      have e₀ : mulA Y n ≫ lift (toUnit Y ≫ x) (𝟙 Y) = lift (toUnit Y ≫ x) (𝟙 Y ^ n) := by
        rw [comp_lift, comp_toUnit_assoc, Category.comp_id]
      have e₁ : lift (toUnit Y) f₂ ≫ mulT P.A T n ≫ translPt P.A (x ≫ f₁) =
          (toUnit Y ≫ x ≫ f₁) * ((𝟙 Y ^ n) ≫ f₂) := by
        rw [← Category.assoc, mulT, comp_lift, lift_translPt, lift_fst, MonObj.comp_pow, lift_snd,
          MonObj.pow_comp, Category.id_comp]
      have e₂ : lift (toUnit Y) f₂ ≫ snd T P.A ^ n = (𝟙 Y ^ n) ≫ f₂ := by
        rw [MonObj.comp_pow, lift_snd, MonObj.pow_comp, Category.id_comp]
      have e₃ : toUnit Y ≫ (1 : T ⟶ P.A) = 1 := MonObj.comp_one _
      have e := prod_sq (lift (toUnit Y ≫ x) (𝟙 Y ^ n)) (fst X Y ≫ f₁) (snd X Y ≫ f₂) h
      rw [lift_fst_assoc, lift_snd_assoc, Category.assoc] at e
      refine Eq.trans ?_ (e.symm.trans (Finset.prod_congr rfl fun I _ => by
        rw [← e₀, Over.comp_left, Category.assoc]))
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, ← Over.comp_left, e₁, e₂, e₃, Category.assoc, zpow_neg, zpow_one, _root_.mul_one]
      ac_rfl)
    (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ u₀ (lift (toUnit Y) f₂).left) (LB.pullGen P.L _ _ σ (toUnit Y).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₀ _) (DVR.pullGen_isGen _ _ _ _ hσ _))
  refine ⟨u, hu, fun y c hy hc z J hJ => ?_⟩
  have hy₂ : (y ≫ f₂) ^ n = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have w : ∀ a : Y ⟶ Y, val u a.left z J =
      val u₀ (lift (toUnit Y) (a ≫ f₂)).left z J * val σ (toUnit Y).left z J := fun a => by
    rw [v _ _ z J hJ, val_mul hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_lift,
      comp_toUnit]
  have w₀ := v₀ (y ≫ f₂) c hy₂ hc Y (toUnit Y) (𝟙 Y ≫ f₂) z J hJ
  refine (w _).trans (Eq.trans ?_ (congrArg (· * _) (w (𝟙 Y))).symm)
  rw [MonObj.mul_comp, Category.assoc, mul_right_comm]
  exact congrArg (fun q => q * _) w₀

end GlobalTheory.CM.LamOfWeil

namespace GlobalTheory.CM

open LamOfWeil IsoDescent

theorem lamEq_of_weilEq : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (X Y A B : Out.PolAV (Sp k)) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A), IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ → WeilEq A.L f₁ f₂ B.L g₁ g₂ (𝟙 (Sp k)) → LamEq A.L f₁ f₂ B.L g₁ g₂ := by
  intro hL k _ _ _ X Y A B f₁ f₂ g₁ g₂ hf₁ hf₂ hg₁ hg₂ hW
  haveI : IsCommMonObj A.A := A.isAb.comm
  haveI : IsCommMonObj B.A := B.isAb.comm
  haveI : IsCommMonObj Y.A := Y.isAb.comm
  have axis : ∀ {Z : Over (Sp k)} (ρ : Z ⟶ X.A ⊗ Y.A), ρ ≫ fst _ _ = 1 ∨ ρ ≫ snd _ _ = 1 →
      ∃ t : LB.Gen ((LB.div (LB.LinComb B.L (sqφ (fst X.A Y.A ≫ g₁) (snd X.A Y.A ≫ g₂)) sqε)
        (LB.LinComb A.L (sqφ (fst X.A Y.A ≫ f₁) (snd X.A Y.A ≫ f₂)) sqε)).pull ρ.left), t.IsGen := by
    intro Z ρ H
    obtain ⟨u, hu⟩ := exists_gen_axis A.isLB ρ (fst X.A Y.A ≫ f₁) (snd X.A Y.A ≫ f₂)
      (H.imp (fun h => by rw [reassoc_of% h, MonObj.one_comp]) (fun h => by rw [reassoc_of% h, MonObj.one_comp]))
    obtain ⟨u', hu'⟩ := exists_gen_axis B.isLB ρ (fst X.A Y.A ≫ g₁) (snd X.A Y.A ≫ g₂)
      (H.imp (fun h => by rw [reassoc_of% h, MonObj.one_comp]) (fun h => by rw [reassoc_of% h, MonObj.one_comp]))
    exact exists_gen_div _ _ _ _ _ _ _ (lbIso_of_gens A.isLB B.isLB _ _ _ _ u hu u' hu')
  refine T.seesaw_triviality_on_dense_fibres_product_abelian hL.globalFns k X.A Y.A
    (LB.div (LB.LinComb B.L (sqφ (fst X.A Y.A ≫ g₁) (snd X.A Y.A ≫ g₂)) sqε)
      (LB.LinComb A.L (sqφ (fst X.A Y.A ≫ f₁) (snd X.A Y.A ≫ f₂)) sqε)) Y.L X.isAb Y.isAb Y.isLB Y.ample
    (LB.isLB_div (DVR.linComb_isLB _ B.isLB _ _) (DVR.linComb_isLB _ A.isLB _ _))
    (axis _ (Or.inl (lift_fst _ _))) ?_ (axis _ (Or.inr (lift_snd _ _)))
  refine (TorsionDense.dense_torsion X hL.irred hL.kerPow).mono (Set.biUnion_subset_biUnion_left ?_)
  rintro x ⟨n, hn, hx⟩
  obtain ⟨u, hu, v⟩ := exists_gen_fibre hL.globalFns hL.cube A f₁ f₂ n x hx
  obtain ⟨u', hu', v'⟩ := exists_gen_fibre hL.globalFns hL.cube B g₁ g₂ n x hx
  refine exists_gen_div _ _ _ _ _ _ _ ?_
  refine lbIso_of_invariant A.isLB B.isLB _ _ _ _ (Out.mulA Y.A n).left
    (I := {y : 𝟙_ (Over (Sp k)) ⟶ Y.A // y ^ n = 1}) (fun y => ((toUnit Y.A ≫ y.1) * 𝟙 Y.A).left) (fun y => ?_)
    (fun U f hf => torsion_invariant_descends (fun S _ P n hn => by
      obtain ⟨a, b, c, e, -⟩ := hL.mulN S P n hn
      exact ⟨a, b, c, e⟩) k Y n (Nat.cast_ne_zero.2 hn.ne') U f fun y hy => hf ⟨y, hy⟩) u hu u' hu'
    (fun y z J J' hJ hJ' => ?_)
  · rw [← Over.comp_left, Out.mulA, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, y.2,
      MonObj.comp_one, _root_.one_mul]
  · have hx₁ : (x ≫ f₁) ^ n = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
    have hy₂ : (y.1 ≫ f₂) ^ n = 1 := by rw [← MonObj.pow_comp, y.2, MonObj.one_comp]
    obtain ⟨c, hc, -⟩ := (hL.weil _ A n _).1 (x ≫ f₁) (y.1 ≫ f₂) hx₁ hy₂
    obtain ⟨c, rfl⟩ : ∃ c₀ : kˣ, unitOn c₀ = c :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom c,
        Units.ext ((Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id_apply c.val)⟩
    have h₁ := v y.1 (unitOn c) y.2 hc z J hJ
    have h₂ := v' y.1 (unitOn c) y.2 ((hW n x y.1 c hn hx y.2).1 hc) z J' hJ'
    refine (congrArg₂ (fun a b => a * b⁻¹) h₂ h₁).trans ?_
    exact mul_div_mul_right_eq_div _ _ _ |> fun h => by simpa only [div_eq_mul_inv] using h

end GlobalTheory.CM

end
