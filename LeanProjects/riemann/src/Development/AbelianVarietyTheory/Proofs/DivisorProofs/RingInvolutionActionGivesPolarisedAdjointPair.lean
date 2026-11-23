import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndDataOfAdj
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGenRosati
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.ActAdj

section Iso

variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}

theorem chart_le (j' : K' → L.ι) (j : K → L.ι) :
    LB.wchart L φ' j' ⊓ LB.wchart L φ j ≤ LB.wchart L (Sum.elim φ' φ) (Sum.elim j' j) := fun _ hy =>
  Set.mem_iInter.2 fun k => match k with
    | Sum.inl k => Set.mem_iInter.1 hy.1 k
    | Sum.inr k => Set.mem_iInter.1 hy.2 k

def genIso (t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k)))) :
    LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') :=
  ⟨fun p => res (chart_le p.1 p.2) (t.s (Sum.elim p.1 p.2))⟩

theorem gm_genIso (t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k)))) {Z : Scheme.{0}}
    (r : Z ⟶ Y) (z : Z) (p : (K' → L.ι) × (K → L.ι)) (hp : r z ∈ LB.wchart L φ' p.1 ⊓ LB.wchart L φ p.2) :
    gm r z _ ((genIso t).s p) = gm r z _ (t.s (Sum.elim p.1 p.2)) :=
  gm_res r z (chart_le p.1 p.2) hp _

theorem genIso_isGen {t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k)))} (ht : t.IsGen) :
    (genIso t).IsGen := by
  intro p q
  refine unit_ext fun y hy => ?_
  have hp := chart_le (φ := φ) (φ' := φ') p.1 p.2 hy.1
  have hq := chart_le (φ := φ) (φ' := φ') q.1 q.2 hy.2
  have e := gen_trans ht (𝟙 Y) y hp hq
  refine ((gm_res (𝟙 Y) y _ hy _).trans ((gm_genIso t (𝟙 Y) y p hy.1).trans e)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div (LB.LinComb L φ ε) (LB.LinComb L φ' ε') (𝟙 Y) y p q hy)
    ((gm_res (𝟙 Y) y _ hy _).trans (gm_genIso t (𝟙 Y) y q hy.2)))).trans ?_
  congr 1
  refine (congrArg₂ (· * ·) (gm_linComb L φ' ε' (𝟙 Y) y _ _ hy.1.1 hy.2.1)
    (congrArg (·⁻¹) (gm_linComb L φ ε (𝟙 Y) y _ _ hy.1.2 hy.2.2))).trans ?_
  simp only [trF, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rfl

end Iso

end GlobalTheory.MumFam.ActAdj

namespace GlobalTheory.MumFam

open ActAdj in

theorem adj_act : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O), Adj (pol D) (pol D) (o.onB.act a) (o.onB.act (Star.star a)) (DistribMulAction.toAddMonoidHom D.toPre.X a) (DistribMulAction.toAddMonoidHom D.toPre.X (Star.star a)) := by
  intro R _ _ I D O _ _ _ o a
  have hL := D.toPre.P.isLB
  let B := D.toPre.P.A
  let f := o.onB.act a
  let g := o.onB.act (star a)
  haveI hf : IsMonHom f := o.onB.hom a
  haveI hg : IsMonHom g := o.onB.hom (star a)
  let φ₀ : ULift.{0} (Finset (Fin 2)) → ((B ⊗ B).left ⟶ B.left) :=
    fun I => (psum B ![fst B B ≫ f, snd B B] I.down).left
  let φ₁ : ULift.{0} (Finset (Fin 2)) → ((B ⊗ B).left ⟶ B.left) :=
    fun I => (psum B ![fst B B, snd B B ≫ g] I.down).left
  let e₂ : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)
  obtain ⟨u, hu, h0⟩ := exists_ros GlobalTheory.globalFns_holds D.toPre.P.isAb hL f g (o.onB.rosati a)
  have hF : FormEq (rosatiφ B f g) (fun i => - rosatiε i) (Sum.elim φ₁ φ₀) (Sum.elim e₂ (fun k => - e₂ k)) := by
    intro U _ k
    have p := prod_ros f g (fst B B) (snd B B) k
    rw [lift_fst_snd] at p
    have p' : ∏ i, k (rosatiφ B f g i) ^ rosatiε i = _ :=
      (Finset.prod_congr rfl fun i _ => by erw [Over.id_left, Category.id_comp]).trans p
    have s1 : ∏ I, k (φ₁ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B) (snd B B ≫ g) k
    have s0 : ∏ I, k (φ₀ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B ≫ f) (snd B B) k
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
    rw [p', s1, s0]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨t, ht, htv⟩ := exists_gen hL hF (LB.invGen _ _ _ u) (DVR.invGen_isGen _ _ _ _ hu)
  let w : LB.Iso (cubeLB B ![fst B B ≫ f, snd B B] D.toPre.P.L) (cubeLB B ![fst B B, snd B B ≫ g] D.toPre.P.L) :=
    genIso t
  refine ⟨hf, hg, fun y => o.c_lin a y, fun y => o.c_lin (star a) y, w, genIso_isGen ht,
    fun y y' z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  let P := (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left
  have hp : ∀ b b' J, Good D.toPre.P.L z J → val ((pol D).tau b b') (𝟙 _) z J = val (D.toPre.tau b b') (𝟙 _) z J :=
    fun b b' J hJ => (Wit.exists_tau D.toPre b b').choose_spec.2 _ _ z J hJ
  have hK₁ : Good D.toPre.P.L z J₁ := hJ₁
  have hK₂ : Good D.toPre.P.L z J₂ := hJ₂

  have bal := val_corr hK₁ (o.tau_bal a u hu h0 y y') (𝟙 _)
  rw [val_mul hK₁, val_pull hK₁, Category.id_comp] at bal
  have hut : val t P z J₁ = (val u P z J₁)⁻¹ := (htv _ P z J₁ hK₁).trans (val_inv _ _)
  let h := DistribMulAction.toAddMonoidHom D.toPre.X a
  let h' := DistribMulAction.toAddMonoidHom D.toPre.X (star a)
  have single : val ((pol D).tau (h y) y') (𝟙 _) z J₁ =
      val t P z J₁ * val ((pol D).tau y (h' y')) (𝟙 _) z J₁ := by
    exact (hp _ _ _ hK₁).trans ((eq_inv_mul_of_mul_eq ((mul_comm _ _).trans bal)).trans
      (congrArg₂ (· * ·) hut.symm (hp _ _ _ hK₁).symm))

  let j₁ : ULift.{0} (Finset (Fin 2)) → D.toPre.P.L.ι := fun I => J₁ (P ≫ φ₁ I)
  let j₂ : ULift.{0} (Finset (Fin 2)) → D.toPre.P.L.ι := fun I => J₂ (P ≫ φ₀ I)
  let j₁' : ULift.{0} (Finset (Fin 2)) → D.toPre.P.L.ι := fun I => J₁ (P ≫ φ₀ I)
  have m₁ : P z ∈ LB.wchart D.toPre.P.L φ₁ j₁ := hK₁.mem φ₁ P
  have m₂ : P z ∈ LB.wchart D.toPre.P.L φ₀ j₂ := hK₂.mem φ₀ P
  have m₁' : P z ∈ LB.wchart D.toPre.P.L φ₀ j₁' := hK₁.mem φ₀ P
  have eA : adjVal w P z J₁ J₂ = gm P z _ (t.s (Sum.elim j₁ j₂)) := gm_genIso t P z (j₁, j₂) ⟨m₁, m₂⟩
  have eT : val t P z J₁ = gm P z _ (t.s (Sum.elim j₁ j₁')) := val_of t P z J₁ _ (by rintro (k | k) <;> rfl)
  have tr := gen_trans ht P z (chart_le j₁ j₂ ⟨m₁, m₂⟩) (chart_le j₁ j₁' ⟨m₁, m₁'⟩)
  have trτ := gen_trans ((pol D).tau_gen (h y) y') (𝟙 _) z (hK₂.mem _ (𝟙 _)) (hK₁.mem _ (𝟙 _))
  let H : ((TK R).left ⟶ B.left) → ((TK R).left.presheaf.stalk z)ˣ :=
    fun ψ => gm ψ z (D.toPre.P.L.U (J₂ ψ) ⊓ D.toPre.P.L.U (J₁ ψ)) (D.toPre.P.L.g (J₂ ψ) (J₁ ψ))
  have kt : trF (Sum.elim φ₁ φ₀) (Sum.elim e₂ fun k => -e₂ k) P z (Sum.elim j₁ j₂) (Sum.elim j₁ j₁') =
      (∏ I, H (P ≫ φ₀ I) ^ e₂ I)⁻¹ := by
    unfold trF
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [Finset.prod_eq_one (fun I _ => by erw [gm_self hL (P ≫ φ₁ I) z (hK₁ (P ≫ φ₁ I)), one_zpow]), _root_.one_mul]
    simp only [zpow_neg, Finset.prod_inv_distrib]
    rfl
  have cx : (toUnit (TK R) ≫ D.toPre.c y) ≫ f = toUnit (TK R) ≫ (pol D).c (h y) :=
    (Category.assoc _ _ _).trans (congrArg (toUnit (TK R) ≫ ·) (o.c_lin a y)).symm
  let X : TK R ⟶ B := toUnit (TK R) ≫ (pol D).c (h y)
  let Y : TK R ⟶ B := toUnit (TK R) ≫ (pol D).c y'
  have q1 : P ≫ ((fst B B ≫ f) * snd B B).left = (X * Y).left := by
    show (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left ≫ _ = _
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst_assoc, lift_snd, cx]
    rfl
  have q2 : P ≫ (fst B B ≫ f).left = X.left := by
    show (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left ≫ _ = _
    rw [← Over.comp_left, lift_fst_assoc, cx]
    rfl
  have q3 : P ≫ (snd B B).left = Y.left := by
    show (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left ≫ _ = _
    rw [← Over.comp_left, lift_snd]
    rfl
  have q4 : P ≫ (1 : B ⊗ B ⟶ B).left = (1 : TK R ⟶ B).left := by
    show (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left ≫ _ = _
    rw [← Over.comp_left, MonObj.comp_one]
  have s0 : ∏ I, H (P ≫ φ₀ I) ^ e₂ I = H (P ≫ ((fst B B ≫ f) * snd B B).left) * (H (P ≫ (fst B B ≫ f).left))⁻¹ *
      (H (P ≫ (snd B B).left))⁻¹ * H (P ≫ (1 : B ⊗ B ⟶ B).left) :=
    GlobalTheory.NormRos.prod_square (fst B B ≫ f) (snd B B) (fun ψ => H (P ≫ ψ))
  have l4 : ∀ X Y : TK R ⟶ B, ∏ k, H (𝟙 _ ≫ lamPts X Y k) ^ negε k =
      (H (X * Y).left)⁻¹ * H X.left * H Y.left * (H (1 : TK R ⟶ B).left)⁻¹ := fun X Y => by
    have e := Wit.prod_neg_lamPts X Y (fun ψ => (H ψ)⁻¹)
    simpa only [inv_inv] using e
  have kτ : ∏ k, H (𝟙 _ ≫ lamPts X Y k) ^ negε k = (∏ I, H (P ≫ φ₀ I) ^ e₂ I)⁻¹ := by
    rw [l4 X Y, s0, q1, q2, q3, q4]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  refine (trτ.trans (congrArg (_ * ·) single)).trans (Eq.trans ?_
    (congrArg (· * _) (eA.trans (tr.trans (congrArg (_ * ·) eT.symm)))).symm)
  rw [_root_.mul_assoc]
  congr 1
  exact kτ.trans kt.symm

end GlobalTheory.MumFam
