import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsFibreIso
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

noncomputable section

namespace GlobalTheory.FamPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PsiEvenPull (proj)
open GlobalTheory.ArcPull
open scoped CategoryTheory.Obj

theorem exists_up_gen {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull Φ)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (h : Y ⟶ Y') (hc : ∀ k, (h ≫ φ' k) ≫ Φ = φ k) (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', Good L z J → Good L' z J' →
      val t r z J = (∏ k, om w z J J' ((r ≫ h) ≫ φ' k) ^ ε k) * val a (r ≫ h) z J' := by
  obtain rfl : (fun k => (h ≫ φ' k) ≫ Φ) = φ := funext hc
  obtain ⟨t, ht, hv⟩ := exists_up hw hL hL' (LB.pullGen L' φ' ε a h) (pullGen_isGen _ _ _ _ ha _)
  refine ⟨t, ht, fun Z r z J J' hJ hJ' => (hv _ r z _ _ (hJ.mem _ _) (hJ'.mem _ _)).trans
    (congrArg₂ (· * ·) ?_ (val_pull hJ' a h r))⟩
  simp only [pw, om, Category.assoc]

theorem secScal_one_val {X Y Y₁ Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ₁ : K' → (Y₁ ⟶ X)} {ε₁ : K' → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {s : LB.Sec (LB.LinComb L φ ε)} {h : Y₁ ⟶ Y}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ ε s h 1) (r : Z ⟶ Y₁) (z : Z) {J} (hJ : Good L z J) :
    sval s (r ≫ h) z J = sval s₁ r z J := by
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ k) (fun k => J (r ≫ h ≫ φ k)) :=
    ⟨hJ.mem φ₁ _, hJ.mem (fun k => h ≫ φ k) _⟩
  have e := H (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ k)) (by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e)
  have a₂ : LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ k) (fun k => J (r ≫ h ≫ φ k)) ≤
      h ⁻¹ᵁ LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)) :=
    inf_le_right.trans (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)
  rw [resTop, map_one, _root_.one_mul] at e
  exact ((gs_res _ z a₂ hm _).trans (gs_pull _ h z _ (a₂ hm) _)).symm.trans ((congrArg (gs r z _) e).trans
    (gs_res _ z _ hm _))

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} {hD : IsPullDeg φ D D'} {F : Type} [Field F] [Algebra (FractionRing R) F]
  [Algebra (FractionRing R') F]

theorem prB_fam (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (α : D.X) (i : Fin 4) :
    (DegPre.prB D F).left ≫ D.famφB α i = DegPre.famφ D F α i := by
  fin_cases i
  · exact Category.comp_id _
  · refine congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left)
      (show DegPre.prB D F ≫ (𝟙 D.P.A * cP D _ α) = DegPre.prB D F * cP D _ α from ?_)
    rw [MonObj.comp_mul, comp_cP, Category.comp_id]
  · exact congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left) (comp_cP D (DegPre.prB D F) α)
  · exact congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (DegPre.prB D F))

theorem famMult_val (hF : Compat φ F) (k : ℕ) (mu α : D'.X) (y : Sp F) (J J') (hJ : Good D.P.L y J)
    (hJ' : Good D'.P.L y J') : vS (DegPre.famMult D F k (hD.xe mu) (hD.xe α)) y J =
      (om hD.w y J J' (cP D' _ α * cP D' (TF (R := R') F) mu).left)⁻¹ * om hD.w y J J' (cP D' (TF (R := R') F) α).left *
        om hD.w y J J' (cP D' (TF (R := R') F) mu).left * (om hD.w y J J' (1 : TF (R := R') F ⟶ D'.P.A).left)⁻¹ *
        (om hD.w y J J' (1 : TF (R := R') F ⟶ D'.P.A).left ^ k *
          (om hD.w y J J' (cP D' (TF (R := R') F) mu).left ^ k)⁻¹) * vS (DegPre.famMult D' F k mu α) y J' := by
  have sq : (𝟙 (Sp F) ≫ jFK (R := R') F) ≫ jK R' ≫ spMap φ = (𝟙 (Sp F) ≫ jFK (R := R) F) ≫ jK R := by
    rw [Category.id_comp, Category.id_comp]; exact hF.sq
  have a₁ : ∀ χ, (𝟙 (Sp F) ≫ jFK (R := R') F) ≫ D'.xK χ = (cP D' (TF (R := R') F) χ).left := fun χ =>
    (Category.assoc _ _ _).trans ((Category.id_comp _).trans (Category.assoc _ _ _).symm)
  have a₂ : (𝟙 (Sp F) ≫ jFK (R := R') F) ≫ (1 : TK R' ⟶ D'.P.A).left = (1 : TF (R := R') F ⟶ D'.P.A).left :=
    (Category.assoc _ _ _).trans ((Category.id_comp _).trans (Category.assoc _ _ _).symm)
  have b₁ := tau_val hD _ _ sq hJ hJ' mu α
  have b₂ := psi_val hD _ _ sq hJ hJ' mu
  have b₃ := rig_val hD _ _ sq hJ hJ'
  rw [a₁, a₁, a₁, a₂, cPoint_add, mul_comm (cP D' _ mu)] at b₁
  rw [a₁] at b₂
  rw [a₂] at b₃
  have c : vS (DegPre.famMult D F k (hD.xe mu) (hD.xe α)) y J =
      val (D.tau (hD.xe mu) (hD.xe α)) (𝟙 (Sp F) ≫ jFK (R := R) F) y J *
      (val (D.psi (hD.xe mu)) (𝟙 (Sp F) ≫ jFK (R := R) F) y J ^ k * val D.rigK (𝟙 (Sp F) ≫ jFK (R := R) F) y J ^ k) :=
    (val_famMult (𝟙 (TF (R := R) F)) hJ k _ _).trans (congrArg₂ (· * ·) rfl
      (congrArg₂ (· * ·) (map_pow _ _ _) (map_pow _ _ _)))
  have c' : vS (DegPre.famMult D' F k mu α) y J' = val (D'.tau mu α) (𝟙 (Sp F) ≫ jFK (R := R') F) y J' *
      (val (D'.psi mu) (𝟙 (Sp F) ≫ jFK (R := R') F) y J' ^ k * val D'.rigK (𝟙 (Sp F) ≫ jFK (R := R') F) y J' ^ k) :=
    (val_famMult (𝟙 (TF (R := R') F)) hJ' k _ _).trans (congrArg₂ (· * ·) rfl
      (congrArg₂ (· * ·) (map_pow _ _ _) (map_pow _ _ _)))
  rw [c, c', b₁, b₂, b₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  module

section Fibre

variable {κ : (DegPre.BF D' F).left ⟶ (DegPre.BF D F).left} {κ' : (DegPre.BF D F).left ⟶ (DegPre.BF D' F).left}
  (hκ : IsFibreIso hD κ κ')

include hκ

theorem exists_secDown {k : ℕ} (α : D'.X) (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F (hD.xe α)) (DegPre.famε k))) :
    ∃ s' : LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' F α) (DegPre.famε k)), SecUp hD κ s' s := by
  obtain ⟨a, ha, -⟩ := GlobalTheory.SecPull.existsUnique_secPull _ _ _ _ D.P.L D'.P.L (proj hD) D.P.isLB D'.P.isLB hD.w hD.w_gen
    (Fin 4) (DegPre.famφ D' F α) (DegPre.famφ D F (hD.xe α)) (DegPre.famε k) κ (hκ.fam α) s
  refine ⟨a, fun Z r z J J' hJ hJ' => ?_⟩
  rw [sval_of s (r ≫ κ) z J (fun i => J ((r ≫ DegPre.famφ D' F α i) ≫ proj hD))
    (fun i => by rw [Category.assoc, Category.assoc, hκ.fam])]
  exact ha Z r z _ _ (fun i => hJ ((r ≫ DegPre.famφ D' F α i) ≫ proj hD)) (fun i => hJ' (r ≫ DegPre.famφ D' F α i))

theorem secRel_down (hF : Compat φ F) {k : ℕ} {α α₁ : D'.X} {β β₁ : D.X} (e : hD.xe α = β) (e₁ : hD.xe α₁ = β₁)
    {m' : TF (R := R') F ⟶ D'.P.A} {m : TF (R := R) F ⟶ D.P.A} (hm : m'.left ≫ proj hD = m.left)
    {tr' : DegPre.BF D' F ⟶ DegPre.BF D' F} {tr : DegPre.BF D F ⟶ DegPre.BF D F} (ht' : tr' = DegPre.trPt D' F m')
    (ht : tr = DegPre.trPt D F m) {s' s t' t} (hs : SecUp hD κ (k := k) (α := α) (β := β) s' s)
    (ht₁ : SecUp hD κ (k := k) (α := α₁) (β := β₁) t' t) {K K' : Type} [Fintype K] [Fintype K']
    {ψ : K → ((TF (R := R) F).left ⟶ D.P.A.left)} {ε : K → ℤ} {ψ' : K' → ((TF (R := R') F).left ⟶ D'.P.A.left)}
    {ε' : K' → ℤ} {v : LB.Gen (LB.LinComb D.P.L ψ ε)} {v' : LB.Gen (LB.LinComb D'.P.L ψ' ε')}
    (hv : ∀ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' → vS v y J =
      (om hD.w y J J' (cP D' _ α * m').left)⁻¹ * om hD.w y J J' (cP D' (TF (R := R') F) α).left * om hD.w y J J' m'.left *
        (om hD.w y J J' (1 : TF (R := R') F ⟶ D'.P.A).left)⁻¹ *
        (om hD.w y J J' (1 : TF (R := R') F ⟶ D'.P.A).left ^ k * (om hD.w y J J' m'.left ^ k)⁻¹) * vS v' y J')
    (H : ∀ u : LB.Gen (LB.LinComb D.P.L (Sum.elim (DegPre.famφ D F β₁) (fun i => tr.left ≫ DegPre.famφ D F β i))
        (DegPre.deltaε k)), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) v →
      GeneratorPullback.SecRel D.P.L _ _ t _ _ s tr.left _ _ u)
    (u' : LB.Gen (LB.LinComb D'.P.L (Sum.elim (DegPre.famφ D' F α₁) (fun i => tr'.left ≫ DegPre.famφ D' F α i))
      (DegPre.deltaε k))) (hu' : u'.IsGen)
    (hc : LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ u' (DegPre.zF D' F).left) v') :
    GeneratorPullback.SecRel D'.P.L _ _ t' _ _ s' tr'.left _ _ u' := by
  subst e e₁ ht ht'
  obtain ⟨u, hu, vu₀⟩ := exists_up_gen ((isGen_iff _).1 hD.w_gen) D.P.isLB D'.P.isLB
    (Sum.elim (DegPre.famφ D' F α₁) (fun i => (DegPre.trPt D' F m').left ≫ DegPre.famφ D' F α i))
    (Sum.elim (DegPre.famφ D F (hD.xe α₁)) (fun i => (DegPre.trPt D F m).left ≫ DegPre.famφ D F (hD.xe α) i))
    (DegPre.deltaε k) κ' (by
      rintro (i | i)
      · show (κ' ≫ DegPre.famφ D' F α₁ i) ≫ _ = DegPre.famφ D F _ i
        rw [Category.assoc, hκ.fam, ← Category.assoc, hκ.inv_hom, Category.id_comp]
      · show (κ' ≫ (DegPre.trPt D' F m').left ≫ _) ≫ _ = (DegPre.trPt D F m).left ≫ _
        rw [Category.assoc, Category.assoc, hκ.fam, ← Category.assoc (DegPre.trPt D' F m').left, hκ.tr hm,
          ← Category.assoc, ← Category.assoc, hκ.inv_hom, Category.id_comp]) u' hu'
  have vu : ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D' F).left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val u (r ≫ κ) z J = (∏ i, om hD.w z J J' (r ≫ Sum.elim (DegPre.famφ D' F α₁)
        (fun i => (DegPre.trPt D' F m').left ≫ DegPre.famφ D' F α i) i) ^ DegPre.deltaε k i) * val u' r z J' := by
    intro Z r z J J' hJ hJ'
    have := vu₀ Z (r ≫ κ) z J J' hJ hJ'
    rwa [Category.assoc r κ κ', hκ.hom_inv, Category.comp_id] at this
  have R' := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (H u hu (corr_of_val D.P.isLB fun y J hJ => by
    obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB (Z := Sp F) y
    have a := vu _ (DegPre.zF D' F).left y J J' hJ hJ'
    rw [prod_delta_zero, hκ.zero hF] at a
    have b := (val_pull hJ' _ _ _).symm.trans (val_corr hJ' hc (𝟙 _))
    rw [val_pull hJ, Category.id_comp]
    exact a.trans ((congrArg _ ((congrArg (fun q => val u' q y J') (Category.id_comp _).symm).trans b)).trans
      (hv y J J' hJ hJ').symm)))
  refine (secRel_iff D'.P.isLB _ _ _ _ _ _ _ _ _ u').2 fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
  have a₁ := ht₁ _ (𝟙 _) y J J' hJ hJ'
  have a₂ := hs _ (𝟙 _ ≫ (DegPre.trPt D' F m').left) y J J' hJ hJ'
  have a₃ := (vu _ (𝟙 _) y J J' hJ hJ').trans (congrArg₂ (· * ·) (prod_sum₂ (K := Fin 4) (K' := Fin 4) _
    (c := ∏ i, om hD.w y J J' (𝟙 _ ≫ DegPre.famφ D' F α₁ i) ^ DegPre.famε k i) rfl
    (prod_neg (c := ∏ i, om hD.w y J J' ((𝟙 _ ≫ (DegPre.trPt D' F m').left) ≫ DegPre.famφ D' F α i) ^ DegPre.famε k i)
      _ _ (Finset.prod_congr rfl fun i _ => by rw [Category.assoc]; rfl))) rfl)
  rw [Category.assoc, hκ.tr hm, ← Category.assoc] at a₂
  have b := R' _ (𝟙 _ ≫ κ) y J hJ
  rw [a₁, a₂, a₃, Units.val_mul, Units.val_mul] at b
  have := Units.mul_inv (∏ i, om hD.w y J J' ((𝟙 _ ≫ (DegPre.trPt D' F m').left) ≫ DegPre.famφ D' F α i) ^ DegPre.famε k i)
  refine (Units.mul_right_inj (∏ i, om hD.w y J J' (𝟙 _ ≫ DegPre.famφ D' F α₁ i) ^ DegPre.famε k i)).1 ?_
  linear_combination b + ((∏ i, om hD.w y J J' (𝟙 _ ≫ DegPre.famφ D' F α₁ i) ^ DegPre.famε k i).val *
    sval s' (𝟙 _ ≫ (DegPre.trPt D' F m').left) y J' * (val u' (𝟙 _) y J').val) * this

theorem exists_famDown (hF : Compat φ F) {k : ℕ} (s : Fam D F k) :
    ∃ s' : Fam D' F k, ∀ α β, hD.xe α = β → SecUp hD κ (s'.s α) (s.s β) := by
  choose s' hs using fun α => exists_secDown hκ α (s.s (hD.xe α))
  have hs' : ∀ α β, hD.xe α = β → SecUp hD κ (s' α) (s.s β) := fun α β e => by
    subst e
    exact hs α
  refine ⟨⟨s', fun mu α => ?_⟩, hs'⟩
  have e₁ : hD.xe (α + k • mu) = hD.xe α + k • hD.xe mu := by rw [map_add, map_nsmul]
  exact secRel_down hκ hF rfl e₁ ((cPoint_proj hD (T := TF (R := R) F) (T' := TF (R := R') F) (𝟙 _)
    (hF.base.trans (Category.id_comp _).symm) mu).trans (Category.id_comp _)) (trF_eq D' F mu) (trF_eq D F _)
    (hs' _ _ rfl) (hs' _ _ e₁) (famMult_val hF k mu α) (s.fe (hD.xe mu) (hD.xe α))

theorem phiRel_down (hF : Compat φ F) {k : ℕ} {p : QkPt D F k} {p' : QkPt D' F k} (hy : p'.y = hD.xe.symm p.y)
    (hg : IsPullGtF φ hD F p.g p'.g) {w w'} (hw : ∀ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' → vS w y J =
        om hD.w y J J' (1 : TF (R := R') F ⟶ D'.P.A).left ^ k * (om hD.w y J J' p'.g.b.left ^ k)⁻¹ * vS w' y J')
    {s t : Fam D F k} {s' t' : Fam D' F k} (hs : ∀ α β, hD.xe α = β → SecUp hD κ (s'.s α) (s.s β))
    (ht : ∀ α β, hD.xe α = β → SecUp hD κ (t'.s α) (t.s β)) (H : PhiRel D F k p w s t) : PhiRel D' F k p' w' s' t' := by
  intro α
  have e₁ : hD.xe (α + p'.y) = hD.xe α + p.y := by rw [map_add, hy, AddEquiv.apply_symm_apply]
  refine secRel_down hκ hF rfl e₁ hg.1 rfl rfl (hs _ _ rfl) (ht _ _ e₁) (fun y J J' hJ hJ' => ?_) (H (hD.xe α))
  have b := pullGt_val hD hg α (𝟙 _) hJ hJ'
  simp only [Category.id_comp] at b
  have c : vS (LB.mulGen D.P.L _ _ _ _ (p.g.s (hD.xe α)) w) y J = val (p.g.s (hD.xe α)) (𝟙 (Sp F)) y J * vS w y J :=
    val_mul hJ _ _ _
  have c' : vS (LB.mulGen D'.P.L _ _ _ _ (p'.g.s α) w') y J' = val (p'.g.s α) (𝟙 (Sp F)) y J' * vS w' y J' :=
    val_mul hJ' _ _ _
  rw [c, c', b, hw y J J' hJ hJ']
  ac_rfl

omit hκ in
theorem fam_down_unique {k : ℕ} {s : Fam D F k} {s' t' : Fam D' F k}
    (hs : ∀ α β, hD.xe α = β → SecUp hD κ (s'.s α) (s.s β)) (ht : ∀ α β, hD.xe α = β → SecUp hD κ (t'.s α) (s.s β)) :
    s' = t' :=
  fam_ext fun α => sec_ext_val D'.P.isLB fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    exact (Units.mul_right_inj _).1 ((hs α _ rfl _ (𝟙 _) y J J' hJ hJ').symm.trans (ht α _ rfl _ (𝟙 _) y J J' hJ hJ'))

theorem fam_up_unique {k : ℕ} {s t : Fam D F k} {s' : Fam D' F k}
    (hs : ∀ α β, hD.xe α = β → SecUp hD κ (s'.s α) (s.s β)) (ht : ∀ α β, hD.xe α = β → SecUp hD κ (s'.s α) (t.s β)) :
    s = t :=
  fam_ext fun β => sec_ext_val D.P.isLB fun y J hJ => by
    obtain ⟨α, rfl⟩ := hD.xe.surjective β
    obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB y
    have := (hs α _ rfl _ κ' y J J' hJ hJ').trans (ht α _ rfl _ κ' y J J' hJ hJ').symm
    rwa [hκ.inv_hom] at this

omit hκ in
theorem up_add {k : ℕ} {s t : Fam D F k} {s' t' : Fam D' F k}
    (hs : ∀ α β, hD.xe α = β → SecUp hD κ (s'.s α) (s.s β)) (ht : ∀ α β, hD.xe α = β → SecUp hD κ (t'.s α) (t.s β)) :
    ∀ α β, hD.xe α = β → SecUp hD κ ((s' + t').s α) ((s + t).s β) := fun α β e Z r z J J' hJ hJ' => by
  rw [sval_add _ _ _ _ z hJ, sval_add _ _ _ _ z hJ', hs α β e Z r z J J' hJ hJ', ht α β e Z r z J J' hJ hJ', mul_add]

theorem up_smul {k : ℕ} (c : F) {s : Fam D F k} {s' : Fam D' F k}
    (hs : ∀ α β, hD.xe α = β → SecUp hD κ (s'.s α) (s.s β)) :
    ∀ α β, hD.xe α = β → SecUp hD κ ((c • s').s α) ((c • s).s β) := fun α β e Z r z J J' hJ hJ' => by
  rw [sval_smul _ _ _ _ z hJ, sval_smul _ _ _ _ z hJ', hs α β e Z r z J J' hJ hJ', Category.assoc, hκ.fst, mul_left_comm]

theorem secScal_down {k : ℕ} {x : D'.X} {s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F (hD.xe x)) (DegPre.famε k))}
    {s' : LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' F x) (DegPre.famε k))} (hs : SecUp hD κ s' s)
    {b : D.SecB k (hD.xe x)} {b' : D'.SecB k x} (hb : GlobalTheory.Mum.PullB hD x b b')
    (H : GeneratorPullback.SecScal D.P.L _ _ s _ _ b (DegPre.prB D F).left 1) :
    GeneratorPullback.SecScal D'.P.L _ _ s' _ _ b' (DegPre.prB D' F).left 1 := by
  refine (GlobalTheory.FieldBaseChange.secScal_iff_val D'.P.isLB _ _ _ _).2 fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
  rw [gs_eq _ y ⊤ trivial, map_one, map_one, _root_.one_mul]
  have a₁ := hs _ (𝟙 _) y J J' hJ hJ'
  have a₂ := secScal_one_val H (𝟙 _ ≫ κ) y hJ
  have a₃ := hb _ (𝟙 _ ≫ (DegPre.prB D' F).left) y
    (fun i => J (((𝟙 _ ≫ (DegPre.prB D' F).left) ≫ D'.famφB x i) ≫ proj hD))
    (fun i => J' ((𝟙 _ ≫ (DegPre.prB D' F).left) ≫ D'.famφB x i))
    (fun i => hJ (((𝟙 _ ≫ (DegPre.prB D' F).left) ≫ D'.famφB x i) ≫ proj hD))
    (fun i => hJ' ((𝟙 _ ≫ (DegPre.prB D' F).left) ≫ D'.famφB x i))
  have e : (𝟙 _ ≫ κ) ≫ (DegPre.prB D F).left = (𝟙 _ ≫ (DegPre.prB D' F).left) ≫ proj hD := by
    rw [Category.assoc, Category.assoc, hκ.snd]
  have a₄ : sval b ((𝟙 _ ≫ (DegPre.prB D' F).left) ≫ proj hD) y J =
      (∏ i, om hD.w y J J' ((𝟙 _ ≫ (DegPre.prB D' F).left) ≫ D'.famφB x i) ^ DegPre.famε k i).val *
        sval b' (𝟙 _ ≫ (DegPre.prB D' F).left) y J' :=
    (sval_of b _ y J _ (fun i => by
      rw [← e, Category.assoc, prB_fam, Category.assoc _ (DegPre.prB D' F).left, prB_fam, Category.assoc,
        Category.assoc, hκ.fam])).trans a₃
  simp only [Category.assoc _ (DegPre.prB D' F).left, prB_fam] at a₄
  rw [e] at a₂
  simp only [Category.assoc _ (DegPre.prB D' F).left] at a₂
  exact (Units.mul_right_inj _).1 (a₄.symm.trans (a₂.trans a₁))

end Fibre

section Frames

open GlobalTheory.UT GlobalTheory.UT.SymFrame

theorem grep_step (D : DegPre R) (n : ℕ) : ∃ v, GRep D.P.L D.P.A
    (fun _ _ h => h (𝟙 D.P.A ^ (n + 1)).left * (h (𝟙 D.P.A ^ n).left)⁻¹ * (h (𝟙 D.P.A :).left ^ (2 * n + 1))⁻¹ *
      h (1 : D.P.A ⟶ D.P.A).left ^ (2 * n + 1)) v ∧ ∀ y J, Good D.P.L y J → v (𝟙_ _) 1 y J = 1 := by
  refine ⟨_, ((grep_cubN (D := D) (𝟙 _) (𝟙 _) n).mul
    (((grep_cub (D := D) (𝟙 _) (𝟙 _)⁻¹ (𝟙 _)).mul (grep_sym (𝟙 _)).inv).pow n).inv).congr
    (fun U _ h => by
      simp only [mul_inv_cancel, inv_mul_cancel, _root_.one_mul, ← pow_succ]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow]
      module) (fun _ _ _ _ _ => rfl), fun y J hJ => ?_⟩
  have C : IsCub (cubV D.cub (T := 𝟙_ _) y J) := isCub_cubV D.cub hJ
  beta_reduce
  rw [Category.comp_id, C.N_one, C.face, normd_one (u := D.sym) ⟨D.sym_gen, D.sym_rig⟩ hJ]
  simp

theorem grep_mulq (D : DegPre R) (n : ℕ) : ∃ v, GRep D.P.L D.P.A
    (fun _ _ h => h (𝟙 D.P.A ^ n).left * (h (𝟙 D.P.A :).left ^ (n ^ 2))⁻¹ * h (1 : D.P.A ⟶ D.P.A).left ^ (n ^ 2) *
      (h (1 : D.P.A ⟶ D.P.A).left)⁻¹) v ∧ ∀ y J, Good D.P.L y J → v (𝟙_ _) 1 y J = 1 := by
  induction n with
  | zero => exact ⟨_, ((grep_sym (𝟙 _)).pow 0).congr (fun U _ h => by simp) (fun _ _ _ _ _ => rfl),
      fun _ _ _ => pow_zero _⟩
  | succ n ih =>
    obtain ⟨v, hv, h₁⟩ := ih
    obtain ⟨v', hv', h₂⟩ := grep_step D n
    refine ⟨_, (hv.mul hv').congr (fun U _ h => ?_) (fun _ _ _ _ _ => rfl), fun y J hJ => ?_⟩
    · apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow]
      module
    · beta_reduce
      rw [h₁ y J hJ, h₂ y J hJ, _root_.mul_one]

theorem exists_nu (D : DegPre R) (n : ℕ) : ∃ ν : LB.Gen (nuLB D n), Normd ν := by
  obtain ⟨v, hv, h₁⟩ := grep_step D n
  obtain ⟨s, hs, -⟩ := hv.normd
    ![(𝟙 D.P.A ^ (n + 1)).left, (𝟙 D.P.A ^ n).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left]
    ![1, -1, -(2 * (n : ℤ) + 1), 2 * (n : ℤ) + 1]
    (fun U _ h => by
      rw [Fin.prod_univ_four]
      apply Additive.ofMul.injective
      simp [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module) h₁
  exact ⟨s, hs⟩

theorem exists_kap (D : DegPre R) (n : ℕ) : ∃ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1), Normd κ := by
  obtain ⟨v, hv, h₁⟩ := grep_mulq D n
  obtain ⟨s, hs, -⟩ := hv.inv.normd
    ![𝟙 _, (𝟙 D.P.A ^ n).left, (1 : D.P.A ⟶ D.P.A).left]
    ![((n ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - ((n ^ 2 : ℕ) : ℤ)]
    (fun U _ h => by
      rw [Fin.prod_univ_three]
      apply Additive.ofMul.injective
      simp [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module) (fun y J hJ => by beta_reduce; rw [h₁ y J hJ, inv_one])
  exact ⟨s, hs⟩

theorem txFrame_iff (hG : GlobalFnsSt) {N : ℕ} {ν : LB.Gen (nuLB D N)} (hν : Normd ν)
    {κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1)} (hκ : Normd κ) (p : QkPt D F N) (w : Frm D F N p.g.b) :
    TXFrame N p w ↔ w.IsGen ∧ ∀ z J, Good D.P.L z J →
      val w (𝟙 _) z J ^ 2 = val (p.g.s p.y) (𝟙 _) z J * val ν p.g.b.left z J ∧
      val w (𝟙 _) z J ^ N * val κ p.g.b.left z J =
        @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi p.y) (jFK (R := R) F) z J) *
          rigV D (TF (R := R) F).hom z J :=
  ⟨fun h => ⟨h.1, fun z J hJ => ⟨h.2.1 ν hν z J hJ, h.2.2 κ hκ z J hJ⟩⟩, fun h => ⟨h.1,
    fun _ hν' z J hJ => (h.2 z J hJ).1.trans (congrArg _ (normd_unique hG hν hν' _ z J hJ)),
    fun _ hκ' z J hJ => (congrArg _ (normd_unique hG hκ' hκ _ z J hJ)).trans (h.2 z J hJ).2⟩⟩

variable (hD) in
theorem normd_down {K : Type} [Fintype K] {ψ : K → (D.P.A.left ⟶ D.P.A.left)} {ε : K → ℤ}
    (ψ' : K → (D'.P.A.left ⟶ D'.P.A.left)) (hψ : ∀ k, ψ' k ≫ proj hD = proj hD ≫ ψ k)
    (h₁ : ∀ (U : Type) [CommGroup U] (h : (Sp R' ⟶ D'.P.A.left) → U),
      ∏ k, h ((1 : 𝟙_ _ ⟶ D'.P.A).left ≫ ψ' k) ^ ε k = 1)
    {u : LB.Gen (LB.LinComb D.P.L ψ ε)} (hu : Normd u) : ∃ u' : LB.Gen (LB.LinComb D'.P.L ψ' ε), Normd u' ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
        val u (r ≫ proj hD) z J = (∏ k, om hD.w z J J' (r ≫ ψ' k) ^ ε k) * val u' r z J' := by
  obtain ⟨t, ht, vt⟩ := exists_down_om hD.w_gen D.P.isLB D'.P.isLB (proj hD) hψ u hu.1
  refine ⟨t, (normd_iff t).2 ⟨ht, fun y J' hJ' => ?_⟩, vt⟩
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
  have o₁ : (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A).left = eSec D'.P.A := Category.id_comp _
  have e := vt _ (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A).left y J J' hJ hJ'
  have e₀ := h₁ _ (om hD.w y J J')
  have e₁ := (val_pull hJ _ _ _).symm.trans ((val_corr hJ hu.2 (specOf φ)).trans (val_one _))
  have e₂ := (congrArg (fun q => val u q y J) ((congrArg (· ≫ proj hD) o₁).trans hD.he)).trans e₁
  exact (congrArg (fun q => val t q y J') o₁.symm).trans ((_root_.one_mul _).symm.trans
    ((congrArg (· * _) e₀.symm).trans (e.symm.trans e₂)))

variable (hD) in
theorem pow_proj (n : ℕ) : (𝟙 D'.P.A ^ n).left ≫ proj hD = proj hD ≫ (𝟙 D.P.A ^ n).left := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact one_proj hD (proj hD) (pull_grp hD).1.w.symm
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact mul_push (pull_grp hD) (proj hD) ih ((Category.id_comp _).trans (Category.comp_id _).symm)

theorem prod_nu {Y : Over (Sp R)} (x : Y ⟶ D.P.A) (n : ℕ) {U : Type} [CommGroup U] (h : (Y.left ⟶ D.P.A.left) → U) :
    ∏ k : Fin 4, h (x.left ≫ ![(𝟙 D.P.A ^ (n + 1)).left, (𝟙 D.P.A ^ n).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left] k) ^
      (![1, -1, -(2 * (n : ℤ) + 1), 2 * (n : ℤ) + 1] : Fin 4 → ℤ) k =
    h (x ^ n * x).left * (h (x ^ n).left)⁻¹ * h x.left ^ (-(2 * (n : ℤ) + 1)) *
      h (1 : Y ⟶ D.P.A).left ^ (2 * (n : ℤ) + 1) := by
  rw [Fin.prod_univ_four]
  show h (x.left ≫ (𝟙 D.P.A ^ (n + 1)).left) ^ (1 : ℤ) * h (x.left ≫ (𝟙 D.P.A ^ n).left) ^ (-1 : ℤ) *
    h (x.left ≫ 𝟙 _) ^ (-(2 * (n : ℤ) + 1)) * h (x.left ≫ (1 : D.P.A ⟶ D.P.A).left) ^ (2 * (n : ℤ) + 1) = _
  rw [Category.comp_id, left_pow, left_pow, left_one, zpow_neg_one, zpow_one, pow_succ]

theorem prod_kap {Y : Over (Sp R)} (x : Y ⟶ D.P.A) (n : ℕ) {U : Type} [CommGroup U] (h : (Y.left ⟶ D.P.A.left) → U) :
    ∏ k : Fin 3, h (x.left ≫ ![𝟙 _, (𝟙 D.P.A ^ n).left, (1 : D.P.A ⟶ D.P.A).left] k) ^
      (![((n ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - ((n ^ 2 : ℕ) : ℤ)] : Fin 3 → ℤ) k =
    h x.left ^ ((n : ℤ) ^ 2) * (h (x ^ n).left)⁻¹ * h (1 : Y ⟶ D.P.A).left ^ (1 - (n : ℤ) ^ 2) := by
  rw [Fin.prod_univ_three]
  show h (x.left ≫ 𝟙 _) ^ ((n ^ 2 : ℕ) : ℤ) * h (x.left ≫ (𝟙 D.P.A ^ n).left) ^ (-((1 : ℕ) : ℤ)) *
    h (x.left ≫ (1 : D.P.A ⟶ D.P.A).left) ^ (((1 : ℕ) : ℤ) - ((n ^ 2 : ℕ) : ℤ)) = _
  rw [Category.comp_id, left_pow, left_one, Nat.cast_pow, Nat.cast_one, zpow_neg_one]

theorem frame_alg {U : Type} [CommGroup U] (N : ℕ) {w w' s s' ν ν' κ κ' ψ ψ' ρ ρ' o b c d : U}
    (hw : w = o ^ N * (b ^ N)⁻¹ * w') (hs : s = d⁻¹ * c * b * o⁻¹ * s')
    (hν : ν = d * c⁻¹ * b ^ (-(2 * (N : ℤ) + 1)) * o ^ (2 * (N : ℤ) + 1) * ν')
    (hκ : κ = b ^ ((N : ℤ) ^ 2) * c⁻¹ * o ^ (1 - (N : ℤ) ^ 2) * κ') (hψ : ψ = c⁻¹ * ψ') (hρ : ρ = o * ρ') :
    (w ^ 2 = s * ν ∧ w ^ N * κ = ψ * ρ) ↔ (w' ^ 2 = s' * ν' ∧ w' ^ N * κ' = ψ' * ρ') := by
  have e₁ : w ^ 2 = (o ^ N * (b ^ N)⁻¹) ^ 2 * w' ^ 2 := by rw [hw, mul_pow]
  have e₂ : s * ν = (o ^ N * (b ^ N)⁻¹) ^ 2 * (s' * ν') := by
    rw [hs, hν]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
    module
  have e₃ : w ^ N * κ = c⁻¹ * o * (w' ^ N * κ') := by
    rw [hw, hκ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
    module
  have e₄ : ψ * ρ = c⁻¹ * o * (ψ' * ρ') := by rw [hψ, hρ]; ac_rfl
  rw [e₁, e₂, e₃, e₄, mul_right_inj, mul_right_inj]

theorem txFrame_pull (hF : Compat φ F) {N : ℕ} {p : QkPt D F N} {p' : QkPt D' F N} (hy : p'.y = hD.xe.symm p.y)
    (hg : IsPullGtF φ hD F p.g p'.g) {w : Frm D F N p.g.b} {w' : Frm D' F N p'.g.b} (hw : w.IsGen) (hw' : w'.IsGen)
    (vw : ∀ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' → vS w y J =
        om hD.w y J J' (1 : TF (R := R') F ⟶ D'.P.A).left ^ N * (om hD.w y J J' p'.g.b.left ^ N)⁻¹ * vS w' y J') :
    TXFrame N p w ↔ TXFrame N p' w' := by
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨ν, hν⟩ := exists_nu D N
  obtain ⟨κ, hκ⟩ := exists_kap D N
  have i₁ : 𝟙 D'.P.A.left ≫ proj hD = proj hD ≫ 𝟙 D.P.A.left := (Category.id_comp _).trans (Category.comp_id _).symm
  have i₂ : (1 : D'.P.A ⟶ D'.P.A).left ≫ proj hD = proj hD ≫ (1 : D.P.A ⟶ D.P.A).left :=
    one_proj hD (proj hD) (pull_grp hD).1.w.symm
  obtain ⟨ν', hν', vν⟩ := normd_down hD
    ![(𝟙 D'.P.A ^ (N + 1)).left, (𝟙 D'.P.A ^ N).left, 𝟙 _, (1 : D'.P.A ⟶ D'.P.A).left] (fun i => by
      fin_cases i
      exacts [pow_proj hD _, pow_proj hD _, i₁, i₂]) (fun U _ h => by
      refine (prod_nu (D := D') (1 : 𝟙_ _ ⟶ D'.P.A) N h).trans ?_
      rw [one_pow, _root_.mul_one, mul_inv_cancel, _root_.one_mul, zpow_neg, inv_mul_cancel]) hν
  obtain ⟨κ', hκ', vκ⟩ := normd_down hD
    ![𝟙 _, (𝟙 D'.P.A ^ N).left, (1 : D'.P.A ⟶ D'.P.A).left] (fun i => by
      fin_cases i
      exacts [i₁, pow_proj hD _, i₂]) (fun U _ h => by
      refine (prod_kap (D := D') (1 : 𝟙_ _ ⟶ D'.P.A) N h).trans ?_
      rw [one_pow]
      group) hκ
  have ey : hD.xe p'.y = p.y := by rw [hy, AddEquiv.apply_symm_apply]
  have cy : cP D' _ p'.y = p'.g.b ^ N := cPoint_y p'
  have key : ∀ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' →
      ((val w (𝟙 _) y J ^ 2 = val (p.g.s p.y) (𝟙 _) y J * val ν p.g.b.left y J ∧
      val w (𝟙 _) y J ^ N * val κ p.g.b.left y J =
        @id ((TF (R := R) F).left.presheaf.stalk y)ˣ (val (D.psi p.y) (jFK (R := R) F) y J) *
          rigV D (TF (R := R) F).hom y J) ↔
      (val w' (𝟙 _) y J' ^ 2 = val (p'.g.s p'.y) (𝟙 _) y J' * val ν' p'.g.b.left y J' ∧
      val w' (𝟙 _) y J' ^ N * val κ' p'.g.b.left y J' =
        @id ((TF (R := R') F).left.presheaf.stalk y)ˣ (val (D'.psi p'.y) (jFK (R := R') F) y J') *
          rigV D' (TF (R := R') F).hom y J')) := fun y J J' hJ hJ' => by
    have b₁ := pullGt_val hD hg p'.y (𝟙 _) hJ hJ'
    simp only [Category.id_comp] at b₁
    rw [ey, cy] at b₁
    have b₂ := ((congrArg (fun q => val ν q y J) hg.1.symm).trans (vν _ p'.g.b.left y J J' hJ hJ')).trans
      (congrArg (· * _) (prod_nu p'.g.b N (om hD.w y J J')))
    have b₃ := ((congrArg (fun q => val κ q y J) hg.1.symm).trans (vκ _ p'.g.b.left y J J' hJ hJ')).trans
      (congrArg (· * _) (prod_kap p'.g.b N (om hD.w y J J')))
    have b₄ := psi_val hD _ _ hF.sq hJ hJ' p'.y
    have b₅ := rig_val hD _ _ hF.sq hJ hJ'
    have a₁ : jFK (R := R') F ≫ D'.xK p'.y = (p'.g.b ^ N).left :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun q : TF (R := R') F ⟶ D'.P.A => q.left) cy)
    have a₂ : jFK (R := R') F ≫ (1 : TK R' ⟶ D'.P.A).left = (1 : TF (R := R') F ⟶ D'.P.A).left :=
      (Category.assoc _ _ _).symm
    rw [ey, a₁] at b₄
    rw [a₂] at b₅
    have b₆ := (val_pull hJ _ _ _).symm.trans (b₅.trans (congrArg _ (val_pull hJ' _ _ _)))
    exact frame_alg (U := ((Sp F).presheaf.stalk y)ˣ) N (vw y J J' hJ hJ') b₁ b₂ b₃ b₄ b₆
  rw [txFrame_iff hG hν hκ, txFrame_iff hG hν' hκ']
  refine ⟨fun h => ⟨hw', fun y J' hJ' => ?_⟩, fun h => ⟨hw, fun y J hJ => ?_⟩⟩
  · obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB (Z := Sp F) y
    exact (key y J J' hJ hJ').1 (h.2 y J hJ)
  · obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB (Z := Sp F) y
    exact (key y J J' hJ hJ').2 (h.2 y J' hJ')

variable (hD) in
theorem exists_lineDown (hF : Compat φ F) {k : ℕ} {b : TF (R := R) F ⟶ D.P.A} {b' : TF (R := R') F ⟶ D'.P.A}
    (hb : b'.left ≫ proj hD = b.left) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F b) (DegPre.lineε k)))
    (hw : w.IsGen) : ∃ w' : LB.Gen (LB.LinComb D'.P.L (DegPre.lineφ D' F b') (DegPre.lineε k)), w'.IsGen ∧
      ∀ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' → vS w y J =
        om hD.w y J J' (1 : TF (R := R') F ⟶ D'.P.A).left ^ k * (om hD.w y J J' b'.left ^ k)⁻¹ * vS w' y J' := by
  obtain ⟨w', hw', vw⟩ := exists_down_om (Y := Sp F) (Y' := Sp F) hD.w_gen D.P.isLB D'.P.isLB
    (φ' := DegPre.lineφ D' F b') (φ := DegPre.lineφ D F b) (𝟙 _) (fun i => by
      fin_cases i
      · exact one_proj hD (T := TF (R := R) F) (T' := TF (R := R') F) (𝟙 _)
          (hF.base.trans (Category.id_comp _).symm)
      · exact hb.trans (Category.id_comp _).symm) w hw
  refine ⟨w', hw', fun y J J' hJ hJ' => ((congrArg (fun q => val w q y J) (Category.id_comp (𝟙 (Sp F))).symm).trans
    (vw _ (𝟙 _) y J J' hJ hJ')).trans (congrArg₂ (· * ·) ?_ rfl)⟩
  rw [Fin.prod_univ_two, Category.id_comp, Category.id_comp]
  show om hD.w y J J' (1 : TF (R := R') F ⟶ D'.P.A).left ^ (k : ℤ) * om hD.w y J J' b'.left ^ (-(k : ℤ)) = _
  rw [zpow_neg, zpow_natCast, zpow_natCast]

end Frames

end GlobalTheory.FamPull

end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.FamPull

open GlobalTheory.ArcPull ReciprocityTheory.ChartRestriction.G.DVR in

theorem fam_transport : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W) (D' : DegData W (maximalIdeal W)) (hD : IsPullDeg φ D.toPre D'.toPre) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (φ r))) → ∀ k : ℕ, ∃ Φ : Fam D.toPre F k → Fam D'.toPre F k, Function.Bijective Φ ∧ (∀ s s' s'' : Fam D.toPre F k, (∀ α i, (s''.s α).f i = (s.s α).f i + (s'.s α).f i) → ∀ α i, ((Φ s'').s α).f i = ((Φ s).s α).f i + ((Φ s').s α).f i) ∧ (∀ (c : F) (s s' : Fam D.toPre F k), Fam.IsSmul D.toPre F c s s' → Fam.IsSmul D'.toPre F c (Φ s) (Φ s')) ∧ (∀ (s : Fam D.toPre F k) (F₀ : IntFam (maximalIdeal R) D.toPre k), F₀.Over s → ∀ f' : ∀ x, D'.toPre.SecB k x, (∀ x, PullB hD x (F₀.f (hD.xe x)) (f' x)) → ∀ x, GeneratorPullback.SecScal D'.toPre.P.L (DegPre.famφ D'.toPre F x) (DegPre.famε k) ((Φ s).s x) (D'.toPre.famφB x) (DegPre.famε k) (f' x) (DegPre.prB D'.toPre F).left 1) ∧ (∀ p : QkPt D.toPre F k, ∃ p' : QkPt D'.toPre F k, p'.y = hD.xe.symm p.y ∧ IsPullGtF φ hD F p.g p'.g) ∧ ∀ (p : QkPt D.toPre F k) (p' : QkPt D'.toPre F k), p'.y = hD.xe.symm p.y → IsPullGtF φ hD F p.g p'.g → ((∃ w', GlobalTheory.UT.TXFrame k p' w') → ∃ w, GlobalTheory.UT.TXFrame k p w) ∧ ∀ w, GlobalTheory.UT.TXFrame k p w → ∃ w', GlobalTheory.UT.TXFrame k p' w' ∧ ∀ s s' : Fam D.toPre F k, PhiRel D.toPre F k p w s s' → PhiRel D'.toPre F k p' w' (Φ s) (Φ s') := by
  intro R _ _ _ D W _ _ _ φ D' hD F _ _ _ hF k
  have hF : Compat φ F := hF
  obtain ⟨κ, κ', hκ⟩ := exists_isFibreIso hD hF
  choose Φ hΦ using exists_famDown hκ hF (k := k)
  refine ⟨Φ, ⟨fun s t e => fam_up_unique hκ (hΦ s) (e ▸ hΦ t), fun s' => ?_⟩, fun s s' s'' h α i => ?_,
    fun c s s' h => ?_, fun s F₀ h f' hf x => secScal_down hκ (hΦ s x _ rfl) (hf x) (h _), fun p => ?_,
    fun p p' hy hg => ⟨?_, fun w hw => ?_⟩⟩
  · obtain ⟨s, hs⟩ := exists_famUp hκ hF s'
    exact ⟨s, fam_down_unique (hΦ s) hs⟩
  · obtain rfl : s'' = s + s' := fam_ext h
    rw [fam_down_unique (hΦ (s + s')) (up_add (hΦ s) (hΦ s'))]
    rfl
  · obtain rfl := (isSmul_iff _ _ _).1 h
    exact (isSmul_iff _ _ _).2 (fam_down_unique (hΦ (c • s)) (up_smul hκ c (hΦ s)))
  · exact ⟨_, (eq_pullQk_iff hD GlobalTheory.globalFns_holds hF D.tau_bimult D'.tau_bimult p _).1 rfl⟩
  · rintro ⟨w', hw'⟩
    obtain ⟨w, hw, vw⟩ := exists_lineUp hD hF hg.1 w' hw'.1
    exact ⟨w, (txFrame_pull hF hy hg hw hw'.1 vw).2 hw'⟩
  · obtain ⟨w', hw', vw⟩ := exists_lineDown hD hF hg.1 w hw.1
    exact ⟨w', (txFrame_pull hF hy hg hw.1 hw' vw).1 hw, fun s s' => phiRel_down hκ hF hy hg vw (hΦ s) (hΦ s')⟩

end GlobalTheory.FamPull
