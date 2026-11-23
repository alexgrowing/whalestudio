import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodPointDimOne
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalTriplePullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsCubeLBPairingIsoBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilPairingEqOfIsomorphicCubePairings
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilEqIffHermFormEqComplex
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomFamilyOfPureTypeComplexTriple
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyPolAVGenericFibreWithLieBasisStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignature
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenySumOfCmHoms
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueHomExtensionSemiAbelian

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM GlobalTheory.EigenSplit

namespace GlobalTheory.GramAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem ex_smul (T : PAT H (Sp ℂ)) {s : 𝓞 E} {r : ℂ}
    (hdet : ∀ τ : 𝓞 E →+* ℂ, τ s ≠ r → LieMult T.t.act (𝟙 (Sp ℂ)) τ 0)
    (u : HolUnif T.pol.A T.pol.L T.pol.g) (h1 : ∀ v, IsTangent v → ∃! w, u.IsDiff w v)
    (h2 : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) (z : Fin T.pol.g → ℂ) :
    u.ex (r • z) = u.ex z ≫ T.t.act.act s := by
  classical
  have hid : IsGrpPullback T.t.G T.t.G (𝟙 _) (𝟙 T.t.G.left) :=
    @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl T.t.G) (inferInstanceAs (IsMonHom (𝟙 T.t.G)))
  have he₀ : PointUnif.IsExp (y := 𝟙 (Sp ℂ)) (G := T.t.G) u.ex :=
    PointUnif.isExp_push hid u h1 h2 (MulEquiv.refl _) fun x => (Category.comp_id _).symm
  obtain ⟨ρ, hρ⟩ := he₀.exists_rep T.t.act u.Λ u.discrete u.ker fun a => by
    obtain ⟨F, hF, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom T.t.G T.t.G T.ab T.ab _ _ _ _ u u h1 h2
      (T.t.act.act a) (T.t.act.hom a)
    exact ⟨F, hF⟩
  refine Eq.trans (congrArg u.ex ?_) (hρ s z)
  have hs := PointUnif.isSplitting_embeddings (E := E)
  rw [← sum_proj hs ρ z, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun φ _ => ?_
  have hm := proj_mem hs ρ φ z
  by_cases hφ : φ.comp (algebraMap (𝓞 E) E) s = r
  · rw [mem_eigenSub.1 hm, hφ]
  · have h0 := Submodule.finrank_eq_zero.1 (he₀.finrank_eigenSub _ ρ hρ (hdet _ hφ))
    rw [h0, Submodule.mem_bot] at hm
    rw [hm, map_zero, smul_zero]

theorem weilEq_one_complex (A A' B : PAT H (Sp ℂ)) {r : ℂ} (hr : r ^ 2 = -(H.d : ℂ))
    (hA : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ≠ r → LieMult A.t.act (𝟙 (Sp ℂ)) τ 0)
    (hA' : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ≠ -r → LieMult A'.t.act (𝟙 (Sp ℂ)) τ 0)
    {f : A.t.G ⟶ B.t.G} {f' : A'.t.G ⟶ B.t.G} (hf : Serre.IsLinearHom A.t.act B.t.act f)
    (hf' : Serre.IsLinearHom A'.t.act B.t.act f') :
    WeilEq B.t.PP.L f f' A.t.PP.L (𝟙 _) (1 : A'.t.G ⟶ A.t.G) (𝟙 (Sp ℂ)) := by
  have hT : ThetaUnifAV := thetaUnifAV_all
  have hL : Out.Laws := abelianSchemeLaws_all.1
  obtain ⟨u, HA, χA, -, hu, -⟩ := PureType.exists_isThetaUnif hT A.pol
  obtain ⟨u', HA', χA', -, hu', -⟩ := PureType.exists_isThetaUnif hT A'.pol
  obtain ⟨uB, HB, χB, -, hB, -⟩ := PureType.exists_isThetaUnif hT B.pol
  obtain ⟨-, -, -, -, hA1, hA2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT A.pol _ u HA χA hu
  obtain ⟨-, -, -, -, hA1', hA2', -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT A'.pol _ u' HA' χA' hu'
  obtain ⟨-, -, -, -, hB1, hB2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT B.pol _ uB HB χB hB
  obtain ⟨F, hF, -⟩ := HomLinear.exists_linear_of_isMonHom A.t.G B.t.G A.ab B.ab _ _ _ _ u uB hB1 hB2 f hf.isMonHom
  obtain ⟨F', hF', -⟩ := HomLinear.exists_linear_of_isMonHom A'.t.G B.t.G A'.ab B.ab _ _ _ _ u' uB hB1 hB2 f'
    hf'.isMonHom
  choose ρB hρB using fun s : 𝓞 E => (HomLinear.exists_linear_of_isMonHom B.t.G B.t.G B.ab B.ab _ _ _ _ uB uB hB1 hB2
    (B.t.act.act s) (B.t.act.hom s)).imp fun _ h => h.1
  have hadj : ∀ s z w, hermForm HB (ρB s z) w = hermForm HB z (ρB (H.bar s) w) := fun a =>
    (weilEq_iff_hermForm_eq hT hL B.pol B.pol B.pol B.pol uB uB uB uB HB HB χB χB hB hB (B.t.act.act a) (𝟙 _) (𝟙 _)
      (B.t.act.act (H.bar a)) (ρB a) LinearMap.id LinearMap.id (ρB (H.bar a)) (hρB a)
      (fun _ => (Category.comp_id _).symm) (fun _ => (Category.comp_id _).symm) (hρB _)).1
      (weilEq_of_lamEq hL ℂ B.pol B.pol B.pol B.pol _ _ _ _ (B.t.act.hom a) inferInstance inferInstance
        (B.t.act.hom _) (by
          unfold LamEq
          rw [Category.comp_id, Category.comp_id]
          exact B.t.adj a))
  have hu0 : ∀ {g : ℕ} (M N : (Fin g → ℂ) →ₗ[ℂ] (Fin B.pol.g → ℂ)), (∀ z, uB.ex (M z) = uB.ex (N z)) → M = N :=
    fun M N h => by
      refine sub_eq_zero.1 (PointUnif.linear_eq_zero_of_discrete uB.Λ uB.discrete _ fun z => (uB.ker _).1 ?_)
      have := uB.ex_add ((M - N) z) (N z)
      rw [LinearMap.sub_apply, sub_add_cancel, h] at this
      exact mul_eq_right.1 this.symm
  have e : ∀ z, ρB H.rt (F z) = r • F z := fun z => LinearMap.congr_fun (hu0 (ρB H.rt ∘ₗ F) (r • F) fun z => by
    rw [LinearMap.comp_apply, LinearMap.smul_apply, ← map_smul, hρB, hF, hF, ex_smul A hA u hA1 hA2,
      Category.assoc, Category.assoc]
    exact congrArg _ (hf.comm _).symm) z
  have hA'' : ∀ τ : 𝓞 E →+* ℂ, τ (H.bar H.rt) ≠ r → LieMult A'.t.act (𝟙 (Sp ℂ)) τ 0 := fun τ h =>
    hA' τ fun h' => h (by rw [EigDec.bar_rt, map_neg, h', neg_neg])
  have e' : ∀ z, ρB (H.bar H.rt) (F' z) = r • F' z := fun z =>
    LinearMap.congr_fun (hu0 (ρB (H.bar H.rt) ∘ₗ F') (r • F') fun z => by
      rw [LinearMap.comp_apply, LinearMap.smul_apply, ← map_smul, hρB, hF', hF', ex_smul A' hA'' u' hA1' hA2',
        Category.assoc, Category.assoc]
      exact congrArg _ (hf'.comm _).symm) z
  have hd : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
  have hr0 : r ≠ 0 := fun h0 => by
    rw [h0] at hr
    have := congrArg Complex.re hr
    simp at this
    exact H.d_prime.ne_zero this
  have hrc : star r = -r := by
    have h1 := congrArg Complex.re hr
    have h2 := congrArg Complex.im hr
    simp [pow_two] at h1 h2
    have h3 : r.re = 0 := by
      by_contra h
      have : r.im = 0 := by
        have : r.re * r.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left h
      rw [this] at h1
      nlinarith [mul_self_nonneg r.re]
    exact Complex.ext (by simp [h3]) (by simp)
  refine (weilEq_iff_hermForm_eq hT hL A.pol A'.pol B.pol A.pol u u' uB u HB HA χB χA hB hu f f' (𝟙 _) 1 F F'
    LinearMap.id 0 hF hF' (fun _ => (Category.comp_id _).symm) fun z => ?_).2 fun z w => ?_
  · rw [LinearMap.zero_apply, HermWeil.ex_zero]
    exact (MonObj.comp_one _).symm
  · have h := hadj H.rt (F z) (F' w)
    rw [e, e'] at h
    simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, hrc] at h
    have h' : hermForm HB (F z) (F' w) = 0 := by
      refine mul_left_cancel₀ (mul_ne_zero two_ne_zero hr0) ?_
      unfold hermForm
      linear_combination h
    rw [h']
    simp [hermForm]

variable {K : Type} [Field K] [NumberField K]

theorem lamEq_one {ρ : 𝓞 K} (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) (A A' B : PAT H (Sp (𝓞 K))) {m m' : ℕ}
    (hA : HasType H A.t.act ρ m 0) (hA' : HasType H A'.t.act ρ 0 m')
    {f : A.t.G ⟶ B.t.G} {f' : A'.t.G ⟶ B.t.G} (hf : Serre.IsLinearHom A.t.act B.t.act f)
    (hf' : Serre.IsLinearHom A'.t.act B.t.act f') :
    LamEq B.t.PP.L f f' A.t.PP.L (𝟙 _) (1 : A'.t.G ⟶ A.t.G) := by
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hβi : Function.Injective (σ.comp (algebraMap (𝓞 K) K)) := σ.injective.comp (IsFractionRing.injective (𝓞 K) K)
  generalize σ.comp (algebraMap (𝓞 K) K) = β at hβi
  obtain ⟨⟨A₁, m₁, -⟩, h₁⟩ := GlobalTheory.LamT.pat_pullback E H (𝓞 K) ℂ β A
  obtain ⟨⟨A₂, m₂, -⟩, -⟩ := GlobalTheory.LamT.pat_pullback E H (𝓞 K) ℂ β A'
  obtain ⟨⟨B₁, mB, -⟩, hB⟩ := GlobalTheory.LamT.pat_pullback E H (𝓞 K) ℂ β B
  obtain ⟨-, -, wA, hwA⟩ := h₁ A₁ m₁ inferInstance
  obtain ⟨-, -, wB, hwB⟩ := hB B₁ mB inferInstance
  haveI := hf.isMonHom
  haveI := hf'.isMonHom
  haveI := A.ab.comm
  haveI : IsMonHom (1 : A'.t.G ⟶ A.t.G) := LamF.IsogSum.isMonHom_of_points _ fun T a b => by
    simp only [MonObj.comp_one, _root_.mul_one]
  obtain ⟨f₁, hm₁, e₁⟩ := GlobalTheory.PairingFibre.exists_hom m₁.cart mB.cart f
  obtain ⟨f₂, hm₂, e₂⟩ := GlobalTheory.PairingFibre.exists_hom m₂.cart mB.cart f'
  have lin : ∀ {A : PAT H (Sp (𝓞 K))} {A₁ : PAT H (Sp ℂ)} (mA : SABMap A₁.t A.t (spMap β)) (f : A.t.G ⟶ B.t.G)
      (f' : A₁.t.G ⟶ B₁.t.G), Serre.IsLinearHom A.t.act B.t.act f → IsMonHom f' →
      f'.left ≫ mB.φ = mA.φ ≫ f.left → Serre.IsLinearHom A₁.t.act B₁.t.act f' := by
    intro A A₁ mA f f' hf hm e
    refine ⟨hm, fun c => ?_⟩
    apply Over.OverMorphism.ext
    apply mB.cart.1.hom_ext
    · have hc := congrArg CommaMorphism.left (hf.comm c)
      simp only [Over.comp_left] at hc ⊢
      rw [Category.assoc, e, ← Category.assoc, mA.act c, Category.assoc, hc, Category.assoc, mB.act c,
        ← Category.assoc, ← Category.assoc, e]
    · simp only [Over.comp_left, Category.assoc, Over.w]
  have hlie : ∀ {A : PAT H (Sp (𝓞 K))} {A₁ : PAT H (Sp ℂ)} (mA : SABMap A₁.t A.t (spMap β)) (τ : 𝓞 E →+* ℂ) (n : ℕ),
      LieMult A.t.act (spMap β) τ n → LieMult A₁.t.act (𝟙 (Sp ℂ)) τ n := fun {A A₁} mA τ n => by
    have := GlobalTheory.lieMult_iff_of_isGrpPullback mA.cart A₁.t.act A.t.act mA.act (𝟙 (Sp ℂ)) τ n
    rw [Category.id_comp] at this
    exact this.2
  have hβρ : β ρ ^ 2 = -(H.d : ℂ) := by rw [← map_pow, hρ]; simp
  have hτ : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ^ 2 = -(H.d : ℂ) := fun τ => by rw [← map_pow, H.rt_sq]; simp
  have h := weilEq_one_complex A₁ A₂ B₁ hβρ (fun τ h => hlie m₁ τ 0 ((hA ℂ β hβi τ).2 h))
    (fun τ h => hlie m₂ τ 0 ((hA' ℂ β hβi τ).1
      ((sq_eq_sq_iff_eq_or_eq_neg.1 ((hτ τ).trans hβρ.symm)).resolve_right h)))
    (lin m₁ f f₁ hf hm₁ e₁) (lin m₂ f' f₂ hf' hm₂ e₂)
  have e₄ : (1 : A₂.t.G ⟶ A₁.t.G).left ≫ m₁.φ = m₂.φ ≫ (1 : A'.t.G ⟶ A.t.G).left := by
    have a : Geo.Tor.pushPt m₁.cart.1.w (1 : A₂.t.G ⟶ A₁.t.G) = 1 := map_one (Geo.Tor.pushHom m₁.cart _)
    have b : Geo.Tor.pushPt m₂.cart.1.w (𝟙 A₂.t.G) ≫ (1 : A'.t.G ⟶ A.t.G) = 1 := MonObj.comp_one _
    exact (congrArg (·.left) (a.trans b.symm)).trans (congrArg (· ≫ _) (Category.id_comp _))
  have h' := (GlobalTheory.PairingFibre.weilEq_iff (g₁ := 𝟙 _) m₁.cart m₂.cart mB.cart m₁.cart B.t.PP.isLB A.t.PP.isLB
    B₁.t.PP.isLB A₁.t.PP.isLB ⟨wB, hwB.1⟩ ⟨wA, hwA.1⟩ e₁ e₂ (by simp) e₄ (𝟙 (Sp ℂ))).1 h
  rw [Category.id_comp] at h'
  exact (PairingFibre.lamEq_weilEq_over_ring abelianSchemeLaws_all.1 (𝓞 K) A.pol A'.pol B.pol A.pol _ _ _ _
    hf.isMonHom hf'.isMonHom inferInstance inferInstance ℂ β).2 inferInstance hβi h'

variable {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ₁ p q)

theorem dims : (∀ b, (X.A b).g = Module.finrank ℚ E / 2) ∧ X.B.g = Module.finrank ℚ E / 2 * (p + q) ∧
    0 < Module.finrank ℚ E / 2 := by
  have key : ∀ (T : PAT H (Sp (𝓞 K))) (m n : ℕ), HasType H T.t.act ρ m n → T.g = Module.finrank ℚ E / 2 * (m + n) :=
    fun T m n h => by
      obtain ⟨F⟩ := GlobalTheory.T.nonempty_polAVGenericFibreWithLieBasis abelianSchemeLaws_all.1.polBaseChange K T.pol
      exact (EigDec.eigen_decomposition E H K ρ T F m n X.split h X.ρ_sq).2.2.2.1
  refine ⟨fun b => ?_, key _ _ _ X.typeB, ?_⟩
  · cases b
    · simpa using key _ _ _ X.typeM
    · simpa using key _ _ _ X.typeP
  · have e := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at e
    have : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
    omega

theorem lamEq_of_isGram {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ) :
    (∀ a b, LamEq X.B.t.PP.L (phiP X a) (phiP X b) (X.A true).t.PP.L ((X.A true).t.act.act (gP a b)) (𝟙 _)) ∧
    ∀ a b, LamEq X.B.t.PP.L (phiQ X a) (phiQ X b) (X.A false).t.PP.L ((X.A false).t.act.act (gQ a b)) (𝟙 _) :=
  have hβ := σ₁.injective.comp (IsFractionRing.injective (𝓞 K) K)
  ⟨fun a b => (PairingFibre.lamEq_weilEq_over_ring abelianSchemeLaws_all.1 (𝓞 K) (X.A true).pol (X.A true).pol X.B.pol
      (X.A true).pol _ _ _ _ (X.lin (.inl a)).isMonHom (X.lin (.inl b)).isMonHom ((X.A true).t.act.hom _) inferInstance ℂ
      (σ₁.comp (algebraMap (𝓞 K) K))).2 inferInstance hβ (h.1 a b),
    fun a b => (PairingFibre.lamEq_weilEq_over_ring abelianSchemeLaws_all.1 (𝓞 K) (X.A false).pol (X.A false).pol X.B.pol
      (X.A false).pol _ _ _ _ (X.lin (.inr a)).isMonHom (X.lin (.inr b)).isMonHom ((X.A false).t.act.hom _) inferInstance ℂ
      (σ₁.comp (algebraMap (𝓞 K) K))).2 inferInstance hβ (h.2 a b)⟩

theorem exists_inverse : ∃ (N : ℕ) (ψ : Fin p → (X.B.pol.A ⟶ (X.A true).pol.A))
    (ψ' : Fin q → (X.B.pol.A ⟶ (X.A false).pol.A)), 0 < N ∧ (∀ i, IsMonHom (ψ i)) ∧ (∀ i, IsMonHom (ψ' i)) ∧
    (∀ (T : Over (Sp (𝓞 K))) (x : T ⟶ X.B.pol.A),
      (∏ i, x ≫ ψ i ≫ phiP X i) * (∏ i, x ≫ ψ' i ≫ phiQ X i) = x ^ N) ∧
    ∀ (T : Over (Sp (𝓞 K))) (a : Fin p → (T ⟶ (X.A true).pol.A)) (a' : Fin q → (T ⟶ (X.A false).pol.A)),
      (∀ i, ((∏ k, a k ≫ phiP X k) * ∏ k, a' k ≫ phiQ X k : T ⟶ X.B.pol.A) ≫ ψ i = a i ^ N) ∧
      ∀ i, ((∏ k, a k ≫ phiP X k) * ∏ k, a' k ≫ phiQ X k : T ⟶ X.B.pol.A) ≫ ψ' i = a' i ^ N := by
  haveI hP : ∀ i, IsMonHom (M := (X.A true).pol.A) (N := X.B.pol.A) (phiP X i) := fun i => (X.lin (.inl i)).isMonHom
  haveI hQ : ∀ i, IsMonHom (M := (X.A false).pol.A) (N := X.B.pol.A) (phiQ X i) := fun i => (X.lin (.inr i)).isMonHom
  obtain ⟨gA, gB, -⟩ := dims X
  obtain ⟨N, ψ, ψ', hN, h1, h2⟩ := LamF.exists_inverse_isogeny_of_sum thetaUnifAV_all abelianSchemeLaws_all.1
    (fun T K _ _ _ _ _ _ G G' _ _ hG hG' φ hφ => GlobalTheory.existsUnique_hom_extension_semiAbelian T K G G' hG hG' φ hφ)
    K σ₁ (X.A true).pol (X.A false).pol X.B.pol p q (phiP X) (phiQ X) hP hQ
    (by
      change X.B.g = p * (X.A true).g + q * (X.A false).g
      rw [gB, gA, gA]
      ring) fun y => by
      obtain ⟨x, hx⟩ := X.onto y
      refine ⟨fun i => x (Sum.inl i), fun i => x (Sum.inr i), hx.trans ?_⟩
      rw [List.ofFn_add, List.prod_append]
      congr 2
      · congr 1
        funext i
        exact congrArg (fun j => x j ≫ X.φ j) (finSumFinEquiv_symm_apply_castAdd i)
      · congr 1
        funext i
        exact congrArg (fun j => x j ≫ X.φ j) (finSumFinEquiv_symm_apply_natAdd i)
  have S := LamF.points_sums_eq_products.1 (Sp (𝓞 K))
  simp only [fun G T [GrpObj G] => (S G T).2.1, fun G T [GrpObj G] => (S G T).2.2.1,
    fun G T [GrpObj G] => (S G T).2.2.2, List.prod_ofFn] at h1 h2
  have hm : ∀ (T : Over (Sp (𝓞 K))) (x y : T ⟶ X.B.pol.A),
      ((∏ k, (x ≫ ψ k * y ≫ ψ k) ≫ phiP X k) * ∏ k, (x ≫ ψ' k * y ≫ ψ' k) ≫ phiQ X k : T ⟶ X.B.pol.A) =
        (∏ k, ((x * y) ≫ ψ k) ≫ phiP X k) * ∏ k, ((x * y) ≫ ψ' k) ≫ phiQ X k := fun T x y => by
    simp only [Category.assoc]
    rw [h1, mul_pow, ← h1, ← h1, _root_.mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    simp only [← Category.assoc]
    exact congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => MonObj.mul_comp _ _ _)
      (Finset.prod_congr rfl fun k _ => MonObj.mul_comp _ _ _)
  refine ⟨N * N, fun i => ψ i ^ N, fun i => ψ' i ^ N, Nat.mul_pos hN hN,
    fun i => LamF.IsogSum.isMonHom_of_points _ fun T x y => ?_,
    fun i => LamF.IsogSum.isMonHom_of_points _ fun T x y => ?_, fun T x => ?_, fun T a a' => ⟨fun i => ?_, fun i => ?_⟩⟩
  · simp only [MonObj.comp_pow]
    rw [← mul_pow, ← (h2 T (fun k => x ≫ ψ k * y ≫ ψ k) fun k => x ≫ ψ' k * y ≫ ψ' k).1 i, hm,
      (h2 T (fun k => (x * y) ≫ ψ k) fun k => (x * y) ≫ ψ' k).1 i]
  · simp only [MonObj.comp_pow]
    rw [← mul_pow, ← (h2 T (fun k => x ≫ ψ k * y ≫ ψ k) fun k => x ≫ ψ' k * y ≫ ψ' k).2 i, hm,
      (h2 T (fun k => (x * y) ≫ ψ k) fun k => (x * y) ≫ ψ' k).2 i]
  · rw [pow_mul, ← h1 T x, mul_pow, ← Finset.prod_pow, ← Finset.prod_pow]
    exact congrArg₂ (· * ·)
      (Finset.prod_congr rfl fun k _ => (congrArg _ (MonObj.pow_comp _ _ _)).trans (MonObj.comp_pow _ _ _))
      (Finset.prod_congr rfl fun k _ => (congrArg _ (MonObj.pow_comp _ _ _)).trans (MonObj.comp_pow _ _ _))
  · rw [MonObj.comp_pow, (h2 T a a').1, pow_mul]
  · rw [MonObj.comp_pow, (h2 T a a').2, pow_mul]

end GlobalTheory.GramAt
