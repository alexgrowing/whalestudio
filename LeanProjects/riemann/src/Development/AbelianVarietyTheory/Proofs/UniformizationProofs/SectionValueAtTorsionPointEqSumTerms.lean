import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLeOnFinset
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SumVOfConvolution
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProductOfSectionsExpandsToConvolutionStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionPullbackSectionEndomorphismStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SumVRootOfConvolutionPow
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsActValue
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecNeZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CoefFe
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenVOfPow
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullMulValue
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenMulPullPowUnif
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.TorsionValue
open GlobalTheory.UT.CoefBasic

section Sums
variable {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)}

theorem sumV_unique {Ix : Type} {x : Ix → F} {s s' : F} (h : SumV v x s) (h' : SumV v x s') : s = s' := by
  classical
  by_contra hne
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 (sub_ne_zero.2 hne))
  obtain ⟨S, hS⟩ := h (r + 1)
  obtain ⟨S', hS'⟩ := h' (r + 1)
  have e := v.map_le_sub (hS (S ∪ S') Finset.subset_union_left) (hS' (S ∪ S') Finset.subset_union_right)
  rw [sub_sub_sub_cancel_right, ← hr, WithTop.coe_le_coe] at e
  linarith

theorem sumV_smul {Ix : Type} {x : Ix → F} {s : F} (c : F) (h : SumV v x s) :
    SumV v (fun i => c * x i) (c * s) := by
  intro q
  by_cases hc : c = 0
  · refine ⟨∅, fun T _ => ?_⟩
    simp [hc]
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hc)
  obtain ⟨S, hS⟩ := h (q - r)
  refine ⟨S, fun T hT => ?_⟩
  rw [← Finset.mul_sum, ← mul_sub]
  exact le_v_mul v hr.le (hS T hT) (by ring)

theorem sumV_comp {Ix Iy : Type} {f : Ix → Iy} (hf : Function.Injective f) {x : Iy → F} {s : F}
    (h0 : ∀ β, β ∉ Set.range f → x β = 0) (h : SumV v x s) : SumV v (fun i => x (f i)) s := by
  classical
  intro q
  obtain ⟨S, hS⟩ := h q
  refine ⟨S.preimage f hf.injOn, fun T hT => ?_⟩
  have e : ∑ i ∈ T, x (f i) = ∑ β ∈ T.image f ∪ S, x β := by
    rw [← Finset.sum_image (f := x) (g := f) fun a _ b _ e => hf e]
    refine Finset.sum_subset Finset.subset_union_left fun β hβ hn => h0 β ?_
    rintro ⟨i, rfl⟩
    rcases Finset.mem_union.1 hβ with h₁ | h₁
    · exact hn h₁
    · exact hn (Finset.mem_image_of_mem f (hT (Finset.mem_preimage.2 h₁)))
  rw [e]
  exact hS _ Finset.subset_union_right

theorem exists_degree_constant [IsAlgClosed F] {X : Type} [AddCommGroup X] (Rel : ℕ → (X → F) → F → Prop) (n : ℕ)
    (hn : 1 ≤ n) (hnull : ∀ k a c, 1 ≤ k → Rel k a c → NullV v a)
    (hmul : ∀ k k' a a' c c', 1 ≤ k → 1 ≤ k' → Rel k a c → Rel k' a' c' →
      ∃ a'', Rel (k + k') a'' (c * c') ∧ ∀ α, SumV v (fun χ => a χ * a' (α - χ)) (a'' α))
    (hex : ∀ k, 4 ≤ k → ∃ a c, Rel k a c ∧ c ≠ 0)
    (hlev : ∀ m, 1 ≤ m → ∃ κ : F, κ ≠ 0 ∧ ∀ a c, Rel (n * m) a c → SumV v a (κ * c)) :
    ∃ l : F, l ≠ 0 ∧ ∀ k a c, 1 ≤ k → Rel k a c → SumV v a (l ^ k * c) := by
  have hsum : ∀ k a c, 1 ≤ k → Rel k a c → c ≠ 0 → ∃ r, r ≠ 0 ∧ SumV v a r := by
    intro k a c hk ha hc
    have pos : ∀ j, 1 ≤ k * (j + 1) := fun j => Nat.mul_pos hk (Nat.succ_pos j)
    have step : ∀ (j : ℕ) (b : {b // Rel (k * (j + 1)) b (c ^ (j + 1))}),
        ∃ b' : {b // Rel (k * (j + 1 + 1)) b (c ^ (j + 1 + 1))},
          ∀ α, SumV v (fun χ => b.1 χ * a (α - χ)) (b'.1 α) := fun j b => by
      obtain ⟨b', h₁, h₂⟩ := hmul _ _ _ _ _ _ (pos j) hk b.2 ha
      exact ⟨⟨b', by rw [Nat.mul_succ k (j + 1), pow_succ c (j + 1)]; exact h₁⟩, h₂⟩
    choose f hf using step
    let g : ∀ j : ℕ, {b // Rel (k * (j + 1)) b (c ^ (j + 1))} := fun j =>
      Nat.rec (motive := fun j => {b // Rel (k * (j + 1)) b (c ^ (j + 1))}) ⟨a, by simpa using ha⟩ f j
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨κ, hκ, H⟩ := hlev k hk
    obtain ⟨r, hr, e⟩ := sumV_root_of_convolution_pow F v X a (fun j => (g j).1) rfl
      (fun j => hnull _ _ _ (pos j) (g j).2) (fun j => hf j (g j)) m _
      (H _ _ (by rw [Nat.mul_comm]; exact (g m).2))
    refine ⟨r, fun h0 => ?_, hr⟩
    rw [h0, zero_pow (Nat.succ_ne_zero m)] at e
    exact mul_ne_zero hκ (pow_ne_zero _ hc) e.symm
  have hmu : ∀ k, 1 ≤ k → ∃ mu : F, mu ≠ 0 ∧ ∀ a c, Rel k a c → SumV v a (mu * c) := by
    intro k hk
    obtain ⟨k', e, h4⟩ : ∃ k', n * (k + 4) = k + k' ∧ 4 ≤ k' := by
      have : k + 4 ≤ n * (k + 4) := Nat.le_mul_of_pos_left _ hn
      exact ⟨n * (k + 4) - k, by omega, by omega⟩
    obtain ⟨κ, hκ, H⟩ := hlev (k + 4) (by omega)
    rw [e] at H
    obtain ⟨a', c', h', hc'⟩ := hex k' h4
    obtain ⟨r, hr, hs⟩ := hsum k' a' c' (by omega) h' hc'
    refine ⟨κ * c' / r, div_ne_zero (mul_ne_zero hκ hc') hr, fun a c ha => ?_⟩
    obtain ⟨a'', h₁, h₂⟩ := hmul _ _ _ _ _ _ hk (by omega) ha h'
    have := sumV_of_convolution F v X a a' a'' (hnull _ _ _ hk ha) (hnull _ _ _ (by omega) h') h₂ _ _ hs (H _ _ h₁) hr
    rwa [show κ * (c * c') / r = κ * c' / r * c by ring] at this
  choose! mu hmu0 hmu using hmu
  have hq : ∀ k k', 1 ≤ k → 4 ≤ k' → ∀ a c, Rel k a c → SumV v a (mu (k + k') / mu k' * c) := by
    intro k k' hk hk' a c ha
    obtain ⟨a', c', h', hc'⟩ := hex k' hk'
    obtain ⟨a'', h₁, h₂⟩ := hmul _ _ _ _ _ _ hk (by omega) ha h'
    have h0 := hmu0 k' (by omega)
    have := sumV_of_convolution F v X a a' a'' (hnull _ _ _ hk ha) (hnull _ _ _ (by omega) h') h₂ _ _
      (hmu k' (by omega) _ _ h') (hmu _ (by omega) _ _ h₁) (mul_ne_zero h0 hc')
    rwa [show mu (k + k') * (c * c') / (mu k' * c') = mu (k + k') / mu k' * c by field_simp] at this
  have hm : ∀ k k', 4 ≤ k → 4 ≤ k' → mu (k + k') = mu k * mu k' := by
    intro k k' hk hk'
    obtain ⟨a, c, h, hc⟩ := hex k hk
    have e := mul_right_cancel₀ hc (sumV_unique (hq k k' (by omega) hk' a c h) (hmu k (by omega) a c h))
    exact (div_eq_iff (hmu0 k' (by omega))).1 e
  have h40 := hmu0 4 (by omega)
  have h50 := hmu0 5 (by omega)
  have h20 : mu 5 ^ 4 = mu 4 ^ 5 := by
    have a₁ : mu 8 = _ := hm 4 4 le_rfl le_rfl
    have a₂ : mu 16 = _ := hm 8 8 (by omega) (by omega)
    have a₃ : mu 20 = _ := hm 16 4 (by omega) le_rfl
    have b₁ : mu 10 = _ := hm 5 5 (by omega) (by omega)
    have b₂ : mu 20 = _ := hm 10 10 (by omega) (by omega)
    rw [b₁] at b₂
    rw [a₂, a₁, b₂] at a₃
    linear_combination a₃
  have hp : ∀ k, mu (k + 4) = (mu 5 / mu 4) ^ (k + 4) := by
    intro k
    induction k with
    | zero => rw [zero_add, div_pow, h20]; field_simp
    | succ k ih =>
      have a₁ : mu (k + 1 + 4 + 4) = _ := hm (k + 1 + 4) 4 (by omega) le_rfl
      have a₂ : mu (k + 1 + 4 + 4) = _ := hm (k + 4) 5 (by omega) (by omega)
      rw [show k + 1 + 4 = k + 4 + 1 from rfl, pow_succ, ← ih, mul_div_assoc', eq_div_iff h40]
      exact a₁.symm.trans a₂
  refine ⟨mu 5 / mu 4, div_ne_zero h50 h40, fun k a c hk ha => ?_⟩
  have := hq k 4 hk le_rfl a c ha
  have h4 : mu 4 = (mu 5 / mu 4) ^ 4 := hp 0
  rwa [hp k, pow_add, ← h4, mul_div_cancel_right₀ _ h40] at this

end Sums

section Frames
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem coef_scale {k : ℕ} {g : GtPtF D F} {w w' : Frm D F k g.b} (hw : w.IsGen) {c : F}
    (hv : ∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = cst F z c * (val w (𝟙 _) z J).val) (s : Fam D F k) (χ : D.X) :
    coef s g w' χ = c * coef s g w χ := by
  refine coef_eq fun z J hJ => ?_
  have a := isCoef_coef g hw χ s z J hJ
  rw [hv z J hJ]
  simp only [cst_eq, map_mul] at a ⊢
  linear_combination cstH z c * a

theorem exists_frm_pow {b : TF (R := R) F ⟶ D.P.A} (ω : Frm D F 1 b) (hω : ω.IsGen) (k : ℕ) :
    ∃ w : Frm D F k b, w.IsGen ∧ ∀ z J, Good D.P.L z J → val w (𝟙 _) z J = val ω (𝟙 _) z J ^ k := by
  obtain ⟨w, hw, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε k) (fun U _ h => by
      rw [prod_line, Fin.prod_univ_two]
      show h (1 : TF (R := R) F ⟶ D.P.A).left ^ ((k : ℤ) * ((1 : ℕ) : ℤ)) * h b.left ^ ((k : ℤ) * -((1 : ℕ) : ℤ)) = _
      simp)
    (GeneratorPullback.powGen D.P.L _ _ ω k) (powGen_isGen _ _ _ ω hω k)
  exact ⟨w, hw, fun z J hJ => (hv _ _ z J hJ).trans (map_pow _ _ _)⟩

theorem exists_frm_scale {k : ℕ} {b : TF (R := R) F ⟶ D.P.A} (ω : Frm D F k b) (hω : ω.IsGen) {c : F} (hc : c ≠ 0) :
    ∃ w : Frm D F k b, w.IsGen ∧ ∀ z J, Good D.P.L z J →
      (val w (𝟙 _) z J).val = cst F z c * (val ω (𝟙 _) z J).val := by
  let u : Γ((TF (R := R) F).left, ⊤)ˣ := ((Ne.isUnit hc).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom).unit
  refine ⟨scaleGen u ω, scaleGen_isGen u ω hω, fun z J hJ => ?_⟩
  have e : val (scaleGen u ω) (𝟙 _) z J = gm (𝟙 _) z ⊤ u * val ω (𝟙 _) z J :=
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res (𝟙 _) z le_top (hJ.mem _ (𝟙 _)) u) rfl)
  rw [e, Units.val_mul, ← gs_unit (𝟙 _) z ⊤ trivial u]
  rfl

theorem exists_frm_psi (k : ℕ) (y : D.X) {b : TF (R := R) F ⟶ D.P.A} (hb : b = DegPre.cF D F y) :
    ∃ w : Frm D F k b, w.IsGen ∧ ∀ z J, Good D.P.L z J → val w (𝟙 _) z J =
      (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi y) (jFK (R := R) F) z J) *
        rigV D (TF (R := R) F).hom z J) ^ k := by
  have a₁ : jFK (R := R) F ≫ ptK (D.c y) = (DegPre.cF D F y).left := (Category.assoc _ _ _).symm
  have a₂ : (TF (R := R) F).hom ≫ eSec D.P.A = (1 : TF (R := R) F ⟶ D.P.A).left := rfl
  obtain ⟨w, hw, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε k) (fun U _ h => by
      rw [prod_line, hb, ← a₁, ← a₂, Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique]
      rw [mul_comm]
      simp)
    (GeneratorPullback.powGen D.P.L _ _ (LB.mulGen D.P.L (Y := (TF (R := R) F).left) _ _ _ _
      (LB.pullGen D.P.L _ _ (D.psi y) (jFK (R := R) F))
      (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig (TF (R := R) F).hom)) k)
    (powGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ (D.psi_gen y) _)
      (pullGen_isGen _ _ _ _ D.rig_gen _)) k)
  refine ⟨w, hw, fun z J hJ => (hv _ _ z J hJ).trans ((map_pow _ _ _).trans (congrArg (· ^ k)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ?_ ?_))))⟩
  · exact (val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)
  · exact (val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)

theorem exists_frm_kap {k' k : ℕ} {b b' : TF (R := R) F ⟶ D.P.A} {a : D.P.A ⟶ D.P.A} (hb : b' = b ≫ a)
    (W : Frm D F k' b) (hW : W.IsGen) (κ : LB.Gen (kapLB D a k' k)) (hκ : κ.IsGen) :
    ∃ w : Frm D F k b', w.IsGen ∧ ∀ z J, Good D.P.L z J →
      val W (𝟙 _) z J * val κ b.left z J = val w (𝟙 _) z J := by
  have a₁ : b.left ≫ a.left = b'.left := by rw [hb, Over.comp_left]
  have a₂ : b.left ≫ (1 : D.P.A ⟶ D.P.A).left = (1 : TF (R := R) F ⟶ D.P.A).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  obtain ⟨w, hw, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b') (ε' := DegPre.lineε k) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      refine (congrArg₂ (· * ·) (prod_line k' b h) (Fin.prod_univ_three _)).trans ?_
      rw [prod_line]
      show _ * (h (b.left ≫ 𝟙 _) ^ (k' : ℤ) * h (b.left ≫ a.left) ^ (-(k : ℤ)) *
        h (b.left ≫ (1 : D.P.A ⟶ D.P.A).left) ^ ((k : ℤ) - k')) = _
      rw [Category.comp_id, a₁, a₂]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen D.P.L _ _ _ _ W (LB.pullGen D.P.L _ _ κ b.left))
    (mulGen_isGen _ _ _ _ _ _ _ hW (pullGen_isGen _ _ _ _ hκ _))
  refine ⟨w, hw, fun z J hJ => Eq.symm ((hv _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ?_)))⟩
  exact (val_pull hJ _ _ _).trans (by rw [Category.id_comp])

theorem exists_secA_mul {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {k k' : ℕ} (t : SecA A F k)
    (t' : SecA A F k') : ∃ t'' : SecA A F (k + k'), ∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (z : Z) (J),
      Good A.L z J → sA t'' r z J = sA t r z J * sA t' r z J := by
  obtain ⟨t'', h⟩ := exists_sec A.isLB (φ' := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left)
    (ε' := fun _ => ((k + k' : ℕ) : ℤ)) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Nat.cast_add, zpow_add])
    (H1.SectionArithmetic.mulSec (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (k : ℤ))
      (φ' := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε' := fun _ => (k' : ℤ)) t t')
  exact ⟨t'', fun Z r z J hJ => (h Z r z J hJ).trans (H1.SectionArithmetic.sval_mulSec _ _ r z hJ)⟩

end Frames

theorem frame_eq : LL → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (n : ℕ), 1 ≤ n → ∀ (p : QkPt D.toPre F n) (x : TFK (R := V) F ⟶ A.A) e, IsTorsFrame A ρ n x e → ∀ W : Frm D.toPre F (4 * n ^ 2) p.g.b, W.IsGen → (∀ (t : SecA A F (4 * n ^ 2)) s (c : F), U.ExpandsF F (4 * n ^ 2) w₀ t s → (∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J = @id ((TFK (R := V) F).left.presheaf.stalk z) (cst (R := V) F z c) * (val (powFrame A.A A.L x e ((4 * n ^ 2 : ℕ) : ℤ)) (𝟙 _) z J).val) → SumV v (coef s p.g W) c) → ∃ κ : LB.Gen (kapLB D.toPre (𝟙 D.toPre.P.A ^ n) (4 * n ^ 2) 4), κ.IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val W (𝟙 _) z J * val κ p.g.b.left z J = (@id ((TF (R := V) F).left.presheaf.stalk z)ˣ (val (D.toPre.psi p.y) (jFK (R := V) F) z J) * rigV D.toPre (TF (R := V) F).hom z J) ^ 4 := by
  intro hL V _ _ _ _ hcpl ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN n hn p x e he W hW H
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcpl⟩
  have hpos : 1 ≤ 4 * n ^ 2 := Nat.mul_pos (by norm_num) (Nat.pow_pos hn)
  obtain ⟨E, eG, eA, eB, eh, eAct⟩ := (GlobalTheory.IntEnd.exists_nsmul_and_neg hL V _ hA D A G hG U).1 n
  have hinj : Function.Injective E.h := fun a b h => by
    rw [eh, eh, ← natCast_zsmul, ← natCast_zsmul] at h
    exact smul_right_injective _ (by exact_mod_cast (by omega : n ≠ 0)) h
  obtain ⟨⟨κ, hκ⟩, hpull⟩ := GlobalTheory.T.expansion_pullback_section_endomorphism hL V _ hA D A G hG U F E hinj (4 * n ^ 2) 4 (by norm_num) hpos
    (by rw [eG]; exact exists_gen_mulPull_pow_unif V _ D A G U.toUnifPre n 4 _ rfl)
  rw [← eB]
  refine ⟨κ, hκ.1, ?_⟩
  obtain ⟨h, hns, hio⟩ := p.eq
  have hAct : E.Act p.g h := (eAct F _ _).2 hns
  have hbij := (expBijF_and_expandsF_lin hL V _ hA D A G hG U).1 F
  obtain ⟨σ, c, hc, hσ⟩ := NonVan.exists_sec_ne_zero hL V A F 4 le_rfl 1 (rigT A.A A.L ρ (TFK (R := V) F) 1)
    (EvalLevel.rigT_isGen hN.2.1 1)
  have e₀ : powFrame A.A A.L (1 : TFK (R := V) F ⟶ A.A) (rigT A.A A.L ρ (TFK (R := V) F) 1) ((4 : ℕ) : ℤ) =
      rigT A.A A.L ρ (TFK (R := V) F) ((4 : ℕ) : ℤ) :=
    congrArg LB.Gen.mk (funext fun j => congrArg (· ^ ((4 : ℕ) : ℤ)) (zpow_one _))
  rw [e₀] at hσ
  obtain ⟨α, hα, hα₀, Hα⟩ := PullMul.pull_mul_value V A F ρ hN.2.1 n 4 (4 * n ^ 2) rfl x e he
    (lift (fst _ _) (snd _ _ ≫ E.aA)) (snd _ _ ≫ E.aA) (lift_snd _ _) (lift_fst _ _) (by rw [eA])
  obtain ⟨t, ht, htv⟩ := Hα σ c hσ
  obtain ⟨s, hs, -⟩ := (hbij 4 (by norm_num) w₀ hN.1).1 σ
  obtain ⟨s', hs', -⟩ := (hbij _ hpos w₀ hN.1).1 t
  obtain ⟨w, hw, hwv⟩ := exists_frm_kap hAct.1 W hW κ hκ.1
  obtain ⟨h₁, h₂⟩ := hpull w₀ ρ hN _ _ (lift_snd _ _) (lift_fst _ _) rfl α hα hα₀ σ t s s' hs hs' ht κ hκ p.g h hAct
    W w hW hw hwv
  have S₁ : SumV v (coef s h w) c := by
    have := sumV_comp hinj h₂ (H t s' c hs' htv)
    simpa only [h₁] using this
  obtain ⟨u, hu, huv⟩ := exists_frm_psi (D := D.toPre) (F := F) 4 p.y hio.1
  obtain ⟨o, ho⟩ := exists_zero_gt (D := D.toPre) (F := F)
  obtain ⟨w₁, hw₁⟩ := (coef_basic V D.toPre F 4 o).2.1 ((isZero_iff o).1 ho).1
  have S₂ : SumV v (coef s h u) c := by
    have S₀ := (AdicValSum.main V ϖ hϖ F v hv _ _ _
      ((EvalZero.value_at_origin hL V _ hA D A G hG U F).2.2 w₀ ρ hN 4 σ s hs o w₁ ho hw₁ c hσ)).1
    have := sumV_comp (f := fun β => β + 4 • p.y) (add_left_injective _)
      (fun β hβ => absurd ⟨β - 4 • p.y, sub_add_cancel _ _⟩ hβ) S₀
    simpa only [CoefFE.coef_fe hL V D.toPre F 4 p.y h o hio ho u w₁ hu hw₁ huv s] using this
  obtain ⟨l, -, hl⟩ := exists_frame_ratio hw hu
  have l₁ : l = 1 := by
    have S₃ := sumV_smul l S₁
    simp only [← coef_scale hw hl] at S₃
    exact mul_right_cancel₀ hc ((sumV_unique S₃ S₂).trans (_root_.one_mul c).symm)
  intro z J hJ
  rw [hwv z J hJ, ← huv z J hJ]
  have := hl z J hJ
  rw [l₁, cst_eq, map_one, _root_.one_mul] at this
  exact Units.ext this.symm

attribute [local instance] TorusExt.gtGroup in

theorem value_at_torsion : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (n : ℕ), 1 ≤ n → ∀ (p : QkPt D.toPre F n) x, QkToAkU U.toUnifPre F n p x → ∀ e, IsTorsFrame A ρ n x e → ∃ w₁ : Frm D.toPre F 1 p.g.b, w₁.IsGen ∧ GenV hϖ hv w₁ ((Q p.y : ℚ) / (n : ℚ) ^ 2) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ w : Frm D.toPre F k p.g.b, (w.IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J = val w₁ (𝟙 _) z J ^ k) → ∀ (t : SecA A F k) s (c : F), U.ExpandsF F k w₀ t s → (∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J = @id ((TFK (R := V) F).left.presheaf.stalk z) (cst (R := V) F z c) * (val (powFrame A.A A.L x e k) (𝟙 _) z J).val) → SumV v (coef s p.g w) c := by
  intro hL hT hVR hTW hUU V _ _ _ _ hcpl ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN n hn p x hx e he
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcpl⟩
  have hbij := (expBijF_and_expandsF_lin hL V _ hA D A G hG U).1 F
  obtain ⟨ω, hω⟩ := (coef_basic V D.toPre F 1 p.g).1
  choose Ω hΩ hΩv using exists_frm_pow ω hω
  have pf : ∀ (k : ℤ) z J, val (powFrame A.A A.L x e k) (𝟙 _) z J = val e (𝟙 _) z J ^ k := fun k z J => map_zpow _ _ _
  obtain ⟨l, hl, H⟩ := exists_degree_constant (v := v) (fun k a c => ∃ (t : SecA A F k) (s : Fam D.toPre F k),
      U.ExpandsF F k w₀ t s ∧ (∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J = @id ((TFK (R := V) F).left.presheaf.stalk z) (cst (R := V) F z c) * (val (powFrame A.A A.L x e k) (𝟙 _) z J).val) ∧ a = coef s p.g (Ω k)) n hn
    (by
      rintro k _ c hk ⟨t, s, -, -, rfl⟩
      exact ((CoefVal.main hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv p.g).2.2.2.2.2.2 k hk _ s (hΩ k)).1)
    (by
      rintro k k' _ _ c c' hk hk' ⟨t, s, hs, ht, rfl⟩ ⟨t', s', hs', ht', rfl⟩
      obtain ⟨t'', h''⟩ := exists_secA_mul t t'
      obtain ⟨s'', hs'', -⟩ := (hbij (k + k') (by omega) w₀ hN.1).1 t''
      refine ⟨_, ⟨t'', s'', hs'', fun z J hJ => ?_, rfl⟩, fun α => (AdicValSum.main V ϖ hϖ F v hv _ _ _
        (GlobalTheory.T.product_of_sections_expands_to_convolution hL V _ hA D A G hG U F w₀ hN.1 k k' _ hk hk' rfl t t' t'' s s' s'' hs hs' hs''
          (fun z J hJ => h'' _ _ z J hJ) p.g _ _ _ (hΩ k) (hΩ k') (hΩ _)
          (fun z J hJ => by rw [hΩv _ z J hJ, hΩv _ z J hJ, hΩv _ z J hJ, pow_add]) α)).1⟩
      have cm : @id ((TFK (R := V) F).left.presheaf.stalk z) (cst (R := V) F z (c * c')) =
          @id ((TFK (R := V) F).left.presheaf.stalk z) (cst (R := V) F z c) *
            @id ((TFK (R := V) F).left.presheaf.stalk z) (cst (R := V) F z c') :=
        (cst_eq (R := V) z _).trans ((map_mul _ _ _).trans
          (congrArg₂ (· * ·) (cst_eq (R := V) z _).symm (cst_eq (R := V) z _).symm))
      rw [h'' _ _ z J hJ, ht z J hJ, ht' z J hJ, pf, pf, pf, cm, Nat.cast_add, zpow_add, Units.val_mul]
      ring)
    (fun k hk => by
      obtain ⟨t, c, hc, ht⟩ := NonVan.exists_sec_ne_zero hL V A F k hk x e he.2.1
      obtain ⟨s, hs, -⟩ := (hbij k (by omega) w₀ hN.1).1 t
      exact ⟨_, c, ⟨t, s, hs, ht, rfl⟩, hc⟩)
    (fun m hm => by
      let q : QkPt D.toPre F (n * m) := TorusExt.qkMk D.tau_bimult (m • p.y) p.g (by
        rw [mul_nsmul, TorusExt.qk_nsmul D.tau_bimult p, map_nsmul])
      have hq : QkToAkU U.toUnifPre F (n * m) q x :=
        ((GlobalTheory.LevelCompat.qkToAkU_level hL V _ hA D A G hG U F n m _ hn hm rfl p q x).1 rfl rfl).1 hx
      obtain ⟨κ, hκ, Hκ⟩ := EvalLevel.value_at_level hL V hcpl ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN (n * m)
        (Nat.mul_pos hn hm) q x hq e he.2.1 (Ω _) (hΩ _)
      refine ⟨κ, hκ, ?_⟩
      rintro _ c ⟨t, s, hs, ht, rfl⟩
      exact Hκ t s c hs ht)
  obtain ⟨w₁, hw₁, hv₁⟩ := exists_frm_scale ω hω (inv_ne_zero hl)
  have main : ∀ (k : ℕ), 1 ≤ k → ∀ w : Frm D.toPre F k p.g.b,
      (w.IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J = val w₁ (𝟙 _) z J ^ k) →
      ∀ (t : SecA A F k) s (c : F), U.ExpandsF F k w₀ t s → (∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J = @id ((TFK (R := V) F).left.presheaf.stalk z) (cst (R := V) F z c) * (val (powFrame A.A A.L x e k) (𝟙 _) z J).val) →
      SumV v (coef s p.g w) c := by
    intro k hk w hw t s c hs ht
    have S := sumV_smul (l⁻¹ ^ k) (H k _ c hk ⟨t, s, hs, ht, rfl⟩)
    have sc := coef_scale (w' := w) (hΩ k) (c := l⁻¹ ^ k) (fun z J hJ => by
      rw [hw.2 z J hJ, hΩv k z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hv₁ z J hJ, mul_pow,
        cst_eq, cst_eq, map_pow]) s
    rw [← _root_.mul_assoc, ← mul_pow, inv_mul_cancel₀ hl, one_pow, _root_.one_mul] at S
    simpa only [← sc] using S
  refine ⟨w₁, hw₁, ?_, main⟩
  obtain ⟨W, hW, hWv⟩ := exists_frm_pow w₁ hw₁ (4 * n ^ 2)
  obtain ⟨κ, hκ, hκv⟩ := frame_eq hL V hcpl ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN n hn p x e he W hW
    (main _ (Nat.mul_pos (by norm_num) (Nat.pow_pos hn)) W ⟨hW, hWv⟩)
  exact FrameVal.genV_of_pow V hcpl ϖ hϖ D Q hQ F v hv n hn p w₁ hw₁ κ hκ fun z J hJ => by
    rw [← hWv z J hJ]; exact hκv z J hJ

end GlobalTheory.UT.TorsionValue
end
