import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProductOfSectionsExpandsToConvolutionStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.SeriesProd

theorem hasSum_of_sumI {R F Ix : Type} [CommRing R] [NormedField F] (φ : R →+* F)
    (h1 : ∀ a, ‖φ a‖ ≤ 1) (I : Ideal R) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (ϖ : R) (hI : I = Ideal.span {ϖ})
    (hϖ : ‖φ ϖ‖ ≤ r) [Module R F] (hs : ∀ (a : R) (x : F), a • x = φ a * x) {x : Ix → F} {s : F}
    (h : GlobalTheory.UT.SumI I x s) : HasSum x s := by
  obtain ⟨N, hN, -, -, h⟩ := h
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ y ∈ N, ‖y‖ ≤ C := by
    obtain ⟨T, rfl⟩ := hN
    refine ⟨∑ t ∈ T, ‖t‖, fun y hy => ?_⟩
    obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 hy
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
    rw [hs, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (h1 _)
  have hb : ∀ (n : ℕ) y, y ∈ I ^ n • N → ‖y‖ ≤ r ^ n * C := by
    intro n y hy
    rw [hI, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [hs, norm_mul, map_pow, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hϖ n) (hC z hz) (norm_nonneg _) (pow_nonneg hr0 n)
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  have ht : Filter.Tendsto (fun n : ℕ => r ^ n * C) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).mul_const C
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  obtain ⟨S, hS⟩ := h n
  refine ⟨S, fun T hT => ?_⟩
  rw [dist_comm, dist_eq_norm]
  exact (hb n _ (hS T hT)).trans_lt hn

theorem hasSum_conv {F X : Type} [NormedField F] [IsUltrametricDist F] [AddCommGroup X] {a b c : X → F} {x y : F}
    (ha : HasSum a x) (hb : HasSum b y) (hc : ∀ α, HasSum (fun χ => a χ * b (α - χ)) (c α)) :
    HasSum c (x * y) := by
  have : NonarchimedeanRing F :=
    { is_nonarchimedean := (IsUltrametricDist.nonarchimedeanAddGroup (M := F)).is_nonarchimedean }
  let e : X × X ≃ X × X :=
    { toFun := fun q => (q.2, q.1 - q.2)
      invFun := fun q => (q.1 + q.2, q.1)
      left_inv := fun q => by simp
      right_inv := fun q => by simp }
  exact ((e.hasSum_iff.2 (ha.mul_of_nonarchimedean hb))).prod_fiberwise hc

open GlobalTheory.FieldBaseChange GlobalTheory.UT

theorem mul_back {Y Y' X₁ X₂ Z₁ : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} {m : Y' ⟶ Y} {k k' : ℕ} {g₁ : Z₁ ⟶ X₁} {h₁ : Y' ⟶ Z₁}
    (hL₂ : L₂.IsLB) (n : Z₁ ⟶ Y') (hn : n ≫ h₁ = 𝟙 _) {a a' a'' b b' b''}
    (h : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a (m ≫ f₂) (𝟙 _) b)
    (h' : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k' g₁ h₁ a' (m ≫ f₂) (𝟙 _) b')
    (h'' : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m (k + k') g₁ h₁ a'' (m ≫ f₂) (𝟙 _) b'')
    (hb : ∀ j, (show Γ(Y', LB.wchart L₂ (fun _ : Fin 1 => m ≫ f₂) j) from b''.f j) =
      (show Γ(Y', LB.wchart L₂ (fun _ : Fin 1 => m ≫ f₂) j) from b.f j) *
        (show Γ(Y', LB.wchart L₂ (fun _ : Fin 1 => m ≫ f₂) j) from b'.f j))
    (y : Z₁) (i : L₁.ι) (hi : g₁ y ∈ L₁.U i) :
    powVal a'' (𝟙 _) y i = powVal a (𝟙 _) y i * powVal a' (𝟙 _) y i := by
  have e₃ : g₁ = (n ≫ m) ≫ f₁ := by rw [Category.assoc, ← h.1, ← Category.assoc, hn, Category.id_comp]
  obtain ⟨i₂, a₂⟩ := exists_chart hL₂ (f₂ (m (n y)))
  have a₁ : f₁ (m (n y)) ∈ L₁.U i := by rw [e₃] at hi; exact hi
  have v := (isoRelM_iff w m k h₁ h.1 _ h.2.1 a b).1 h _ n y i₂ i a₂ a₁
  have v' := (isoRelM_iff w m k' h₁ h.1 _ h.2.1 a' b').1 h' _ n y i₂ i a₂ a₁
  have v'' := (isoRelM_iff w m (k + k') h₁ h.1 _ h.2.1 a'' b'').1 h'' _ n y i₂ i a₂ a₁
  have e : powVal b'' (n ≫ 𝟙 _) y i₂ = powVal b (n ≫ 𝟙 _) y i₂ * powVal b' (n ≫ 𝟙 _) y i₂ := by
    rw [Category.comp_id]
    exact (congrArg (gs n y _) (hb fun _ => i₂)).trans (gs_mul n y _ (mem_wchart.2 fun _ => a₂) _ _)
  rw [v, v', v'', hn, zpow_natCast, zpow_natCast, zpow_natCast, pow_add, _root_.mul_mul_mul_comm,
    ← Units.val_mul] at e
  exact (Units.mul_right_inj _).1 e

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_frm_mul {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k k' : ℕ}
    {b : TF (R := R) F ⟶ D.P.A} {w : Frm D F k b} {w' : Frm D F k' b} (hw : w.IsGen) (hw' : w'.IsGen) :
    ∃ w'' : Frm D F (k + k') b, w''.IsGen ∧
      ∀ z J, Good D.P.L z J → val w'' (𝟙 _) z J = val w (𝟙 _) z J * val w' (𝟙 _) z J := by
  obtain ⟨w'', h, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε (k + k'))
    (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [CoefBasic.prod_line, CoefBasic.prod_line, CoefBasic.prod_line, pow_add, pow_add, mul_inv,
        _root_.mul_mul_mul_comm])
    (LB.mulGen D.P.L _ _ _ _ w w') (DVR.mulGen_isGen _ _ _ _ _ _ _ hw hw')
  exact ⟨w'', h, fun z J hJ => (hv _ _ z J hJ).trans (val_mul hJ _ _ _)⟩

theorem exists_back {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
    (F : Type) [Field F] [Algebra (FractionRing R) F] {w : W0 U} (hw : w.IsGen) {k k' : ℕ}
    {σ : U.SecGF F k} {σ' : U.SecGF F k'} {σ'' : U.SecGF F (k + k')} {s s' s''}
    (h : U.ExpandsG F k σ s) (h' : U.ExpandsG F k' σ' s') (h'' : U.ExpandsG F (k + k') σ'' s'')
    (hb : ∀ j, (show Γ((UnifPre.GF (G := G) F).left, LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) j)
        from σ''.f j) =
      (show Γ((UnifPre.GF (G := G) F).left, LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) j) from σ.f j) *
      (show Γ((UnifPre.GF (G := G) F).left, LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) j) from σ'.f j)) :
    ∃ (t : SecA A F k) (t' : SecA A F k') (t'' : SecA A F (k + k')), U.ExpandsF F k w t s ∧ U.ExpandsF F k' w t' s' ∧
      U.ExpandsF F (k + k') w t'' s'' ∧
      ∀ z J, Good A.L z J → sA t'' (𝟙 _) z J = sA t (𝟙 _) z J * sA t' (𝟙 _) z J := by
  let n : TFK (R := R) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n ≫ U.genF F = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  have hn' : U.genF F ≫ n = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  have i₂ := fun k => (isoRelM_bijective (k := k) (m := (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left)
    (g₁ := (snd (TFK (R := R) F) A.A).left) (h₁ := (U.genF F).left) A.isLB U.LG.isLB hw
    (congrArg (fun q => q.left) (lift_snd _ _ : U.genF F ≫ snd _ _ = _)) n.left
    (congrArg (fun q => q.left) hn) (congrArg (fun q => q.left) hn')).2
  obtain ⟨t, ht⟩ := (i₂ k σ).exists
  obtain ⟨t', ht'⟩ := (i₂ k' σ').exists
  obtain ⟨t'', ht''⟩ := (i₂ (k + k') σ'').exists
  exact ⟨t, t', t'', ⟨σ, ht, h⟩, ⟨σ', ht', h'⟩, ⟨σ'', ht'', h''⟩, fun z J hJ =>
    mul_back U.LG.isLB n.left (congrArg (fun q => q.left) hn) ht ht' ht'' hb z _ (hJ (𝟙 _ ≫ _))⟩

theorem main : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k k' : ℕ) (g : GtPtF u.D.toPre (PadicAlgCl p)) (w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b) (w' : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k' g.b) (w'' : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) (k + k') g.b), 1 ≤ k → 1 ≤ k' → w.IsGen → w'.IsGen → w''.IsGen → ∃ κ : PadicAlgCl p, κ ≠ 0 ∧ ∀ (σ : u.U.toUnifPre.SecGF (PadicAlgCl p) k) (σ' : u.U.toUnifPre.SecGF (PadicAlgCl p) k') (σ'' : u.U.toUnifPre.SecGF (PadicAlgCl p) (k + k')) s s' s'', u.U.toUnifPre.ExpandsG (PadicAlgCl p) k σ s → u.U.toUnifPre.ExpandsG (PadicAlgCl p) k' σ' s' → u.U.toUnifPre.ExpandsG (PadicAlgCl p) (k + k') σ'' s'' → (∀ j, (show Γ((UnifPre.GF (G := u.G) (PadicAlgCl p)).left, (LB.LinComb u.U.LG.L (K := Fin 1) (fun _ => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (fun _ => ((k : ℕ) : ℤ))).U j) from σ''.f j) = σ.f j * (show Γ((UnifPre.GF (G := u.G) (PadicAlgCl p)).left, (LB.LinComb u.U.LG.L (K := Fin 1) (fun _ => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (fun _ => ((k : ℕ) : ℤ))).U j) from σ'.f j)) → ∀ x x', HasSum (fun χ => GlobalTheory.UT.coef s g w χ) x → HasSum (fun χ => GlobalTheory.UT.coef s' g w' χ) x' → HasSum (fun χ => GlobalTheory.UT.coef s'' g w'' χ) (κ * x * x') := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u l k k' g w w' w'' hk hk' hw hw' hw''
  obtain ⟨w₃, hw₃, hv⟩ := exists_frm_mul hw hw'
  obtain ⟨c, hc, -, hcoef⟩ :=
    ((CoefBasic.coef_basic _ u.D.toPre (PadicAlgCl p) (k + k') g).2.2 w₃ hw₃).2.2.1 w'' hw''
  refine ⟨c, hc, fun σ σ' σ'' s s' s'' h h' h'' hb x x' hx hx' => ?_⟩
  obtain ⟨w₀, hw₀⟩ := u.U.ext
  obtain ⟨t, t', t'', e, e', e'', hm⟩ := exists_back u.U.toUnifPre (PadicAlgCl p) hw₀ h h' h'' hb
  let φ : u.V →+* PadicAlgCl p :=
    (algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))
  have : CharZero u.V := φ.charZero
  have hadm : AdmBase u.V (IsLocalRing.maximalIdeal u.V) :=
    ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hS := GlobalTheory.T.product_of_sections_expands_to_convolution hL u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p) w₀ hw₀ k k' (k + k') hk hk' rfl
    t t' t'' s s' s'' e e' e'' hm g w w' w₃ hw hw' hw₃ hv
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  have h1 : ∀ a, ‖φ a‖ ≤ 1 := fun a => (u.norm_le _).2 ⟨a, rfl⟩
  have hlt : ‖φ ϖ‖ < 1 := lt_of_le_of_ne (h1 ϖ) fun e1 => by
    obtain ⟨z, hz⟩ := (u.norm_le (algebraMap u.V (FractionRing u.V) ϖ)⁻¹).1 (by
      rw [map_inv₀, norm_inv]
      exact (congrArg (·⁻¹) e1).le.trans inv_one.le)
    have h0 : algebraMap u.V (FractionRing u.V) ϖ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective u.V (FractionRing u.V))).2 hϖ.ne_zero
    refine hϖ.not_isUnit (IsUnit.of_mul_eq_one z (IsFractionRing.injective u.V (FractionRing u.V) ?_))
    rw [map_mul, hz, map_one, mul_inv_cancel₀ h0]
  have hsum := hasSum_conv hx hx' fun α =>
    letI : Module u.V (PadicAlgCl p) := Module.compHom _ (algebraMap u.V (FractionRing u.V))
    hasSum_of_sumI φ h1 _ (norm_nonneg _) hlt ϖ hϖ.maximalIdeal_eq le_rfl
      (fun a x => Algebra.smul_def (algebraMap u.V (FractionRing u.V) a) x) (hS α)
  simp only [hcoef, _root_.mul_assoc]
  exact hsum.mul_left c

end GlobalTheory.ZH.SeriesProd
