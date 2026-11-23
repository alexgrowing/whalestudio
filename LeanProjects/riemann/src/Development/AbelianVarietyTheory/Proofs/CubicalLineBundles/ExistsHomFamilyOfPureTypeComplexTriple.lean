import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmCurveHomFamilyToFibreAtPeriod
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveLieCharacterOfAdjoinGenerator
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsCMPairingFamilyOfPolarisationDiagonalComplexStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilPairingEqOfIsomorphicCubePairings
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilEqIffHermFormEqComplex
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolFibreIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TwoMulEqOfIsTypeFn
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.PureTriple

open GlobalTheory.PointUnif GlobalTheory.PureType

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_datum_period (hT : ThetaUnifAV) (hL : Out.Laws) (T : PAT H (Sp ℂ)) {p q g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H p q ty)
    (hdet : ∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ p) ∧
      (τ H.rt ≠ H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ q))
    (u : HolUnif T.pol.A T.pol.L T.pol.g) {Hm : Matrix (Fin T.pol.g) (Fin T.pol.g) ℂ} {χ : u.Λ → ℂ}
    (hAH : u.IsAH Hm χ) :
    ∃ (D : Datum H) (Pe : D.La →+ (Fin g → ℂ)) (F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin T.pol.g → ℂ)), D.p = p ∧ D.q = q ∧
      IsPeriod D ty Pe ∧ (∀ z, F z ∈ u.Λ ↔ z ∈ Pe.range) ∧
      (∀ a b, (hermForm Hm (F (Pe a)) (F (Pe b))).im = D.EF a b) ∧
      ∀ (s : 𝓞 E) z, u.ex (F fun k => ty k (s : E) * z k) = u.ex (F z) ≫ T.t.act.act s := by
  obtain ⟨Ef, hE, hbij, -, h1, h2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT T.pol _ u Hm χ hAH
  have hid : IsGrpPullback T.t.G T.t.G (𝟙 _) (𝟙 T.t.G.left) :=
    @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl T.t.G) (inferInstanceAs (IsMonHom (𝟙 T.t.G)))
  have he₀ : PointUnif.IsExp (y := 𝟙 (Sp ℂ)) (G := T.t.G) u.ex :=
    isExp_push hid u h1 h2 (MulEquiv.refl _) fun x => (Category.comp_id _).symm
  obtain ⟨ρ, hρ⟩ := he₀.exists_rep T.t.act u.Λ u.discrete u.ker fun a => by
    obtain ⟨F, hF, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom T.t.G T.t.G T.ab T.ab _ _ _ _ u u h1 h2
      (T.t.act.act a) (T.t.act.hom a)
    exact ⟨F, hF⟩
  obtain ⟨h, hh⟩ := exists_equiv_of_finrank_eq (isSplitting_embeddings (E := E)) (diagRep ty) ρ fun φ => by
    rw [finrank_eigenSub_diagRep]
    by_cases hφ : φ (H.rt : E) = H.rt0
    · rw [(hty φ).1 hφ, he₀.finrank_eigenSub _ ρ hρ ((hdet _).1 hφ)]
    · rw [(hty φ).2 hφ, he₀.finrank_eigenSub _ ρ hρ ((hdet _).2 hφ)]
  have hst : ∀ a, ∀ x ∈ u.Λ, ρ a x ∈ u.Λ := fun a x hx => HermWeil.map_mem u u (hρ a) ⟨x, hx⟩
  have hadj : ∀ a z w, hermForm Hm (ρ a z) w = hermForm Hm z (ρ (H.bar a) w) := fun a =>
    (weilEq_iff_hermForm_eq hT hL T.pol T.pol T.pol T.pol u u u u Hm Hm χ χ hAH hAH (T.t.act.act a) (𝟙 _) (𝟙 _)
      (T.t.act.act (H.bar a)) (ρ a) LinearMap.id LinearMap.id (ρ (H.bar a)) (hρ a)
      (fun _ => (Category.comp_id _).symm) (fun _ => (Category.comp_id _).symm) (hρ _)).1
      (weilEq_of_lamEq hL ℂ T.pol T.pol T.pol T.pol _ _ _ _ (T.t.act.hom a) inferInstance inferInstance
        (T.t.act.hom _) (by
          unfold LamEq
          rw [Category.comp_id, Category.comp_id]
          exact T.t.adj a))
  letI : SMul (𝓞 E) u.Λ := ⟨fun a x => ⟨ρ a x, hst a x x.2⟩⟩
  have hsm : ∀ (a : 𝓞 E) (x : u.Λ), ((a • x : u.Λ) : _ → ℂ) = ρ a x := fun _ _ => rfl
  letI : Module (𝓞 E) u.Λ := Module.ofMinimalAxioms
    (fun a x y => Subtype.ext (by simp [hsm])) (fun a b x => Subtype.ext (by simp [hsm]))
    (fun a b x => Subtype.ext (by simp [hsm])) (fun x => Subtype.ext (by simp [hsm]))
  let P : u.Λ →+ (Fin g → ℂ) := h.symm.toLinearMap.toAddMonoidHom.comp u.Λ.subtype.toAddMonoidHom
  have hP : ∀ x, h (P x) = x := fun x => h.apply_symm_apply _
  have hrange : ∀ z, z ∈ P.range ↔ h z ∈ u.Λ := fun z =>
    ⟨by rintro ⟨x, rfl⟩; rw [hP]; exact x.2, fun hz => ⟨⟨_, hz⟩, h.symm_apply_apply z⟩⟩
  have hPs : ∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i := fun a x => congrFun (h.injective (by
    rw [hP, hsm, ← diagRep_apply, hh, hP]))
  have hPi : Function.Injective P := h.symm.injective.comp Subtype.val_injective
  have hPd : DiscreteTopology P.range := by
    have := u.discrete
    refine DiscreteTopology.of_continuous_injective (f := fun z : P.range => (⟨h z, (hrange _).1 z.2⟩ : u.Λ))
      ((h.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _) fun z w hzw => ?_
    exact Subtype.ext (h.injective (congrArg Subtype.val hzw))
  have hPf : Submodule.span ℝ (Set.range P) = ⊤ := by
    have e : Set.range P = (h.symm.toLinearMap.restrictScalars ℝ) '' u.Λ := by
      ext z
      exact ⟨by rintro ⟨x, rfl⟩; exact ⟨x, x.2, rfl⟩, by rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩⟩
    rw [e, ← Submodule.map_span, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact h.symm.surjective
  obtain ⟨Hm', hH', hH''⟩ := exists_hermForm_comp Hm hAH.1 h.toLinearMap
  have hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re := fun z hz => by
    rw [hH'']
    exact hAH.2.1 _ (h.map_ne_zero_iff.2 hz)
  have him : ∀ x x', (hermForm Hm' (P x) (P x')).im = Ef x x' := fun x x' => by
    rw [hH'', hE]
    exact congrArg₂ (fun a b => (hermForm Hm a b).im) (hP x) (hP x')
  obtain ⟨D, ε, hp, hq, hε⟩ := PeriodDatum.exists_datum E H u.Λ Ef p q g ty P Hm' hty hbij
    (fun a x y => by
      have : ((Ef (a • x) y : ℤ) : ℝ) = (Ef x (H.bar a • y) : ℤ) := by rw [hE, hE, hsm, hsm, hadj]
      exact_mod_cast this) hPs hPi hPd hPf hH' hpos him
  let P' : D.La →+ (Fin g → ℂ) := P.comp ε.toLinearMap.toAddMonoidHom
  have hr' : P'.range = P.range := by
    ext z
    exact ⟨by rintro ⟨x, rfl⟩; exact ⟨ε x, rfl⟩,
      by rintro ⟨x, rfl⟩; exact ⟨ε.symm x, congrArg P (ε.apply_symm_apply x)⟩⟩
  refine ⟨D, P', h, hp, hq, ⟨fun a x i => ?_, hPi.comp ε.injective, hr' ▸ hPd, ?_, Hm', hH', hpos, fun x x' => ?_⟩,
    fun z => by rw [hr', hrange], fun a b => ?_, fun s z => ?_⟩
  · exact (congrArg (fun x => P x i) (map_smul ε a x)).trans (hPs a _ i)
  · rw [← AddMonoidHom.coe_range, hr', AddMonoidHom.coe_range, hPf]
  · rw [hε]; exact him _ _
  · rw [hε, ← him, hH'']; rfl
  · rw [← diagRep_apply, hh]; exact hρ s _

theorem exists_isHomFamily (T : PAT H (Sp ℂ)) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (u : HolUnif T.pol.A T.pol.L T.pol.g) {Hm : Matrix (Fin T.pol.g) (Fin T.pol.g) ℂ} {χ : u.Λ → ℂ}
    (hAH : u.IsAH Hm χ) (hD : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v)
    (hθ : ∀ (k : ℕ) s, ∃! θ, u.IsThetaFn Hm χ k θ ∧ u.IsFnPow k s θ)
    {D : Datum H} {Pe : D.La →+ (Fin g → ℂ)} (F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin T.pol.g → ℂ)) (hP : IsPeriod D ty Pe)
    (hF : ∀ z, F z ∈ u.Λ ↔ z ∈ Pe.range) (hE : ∀ a b, (hermForm Hm (F (Pe a)) (F (Pe b))).im = D.EF a b)
    (hact : ∀ (s : 𝓞 E) z, u.ex (F fun k => ty k (s : E) * z k) = u.ex (F z) ≫ T.t.act.act s)
    {PC : Out.PolAV (Sp ℂ)} (u₀ : HolUnif PC.A PC.L PC.g) {c : ℂ}
    (hg : PC.g = 1) (hu : IsThetaUnif u₀) (hc : c ≠ 0) (hΛ : IsQuadLattice u₀.Λ H.d c) {ρ : ℂ}
    (hρ : ρ ^ 2 = -(H.d : ℂ)) (L : Submodule (𝓞 E) D.La) (hLρ : ∀ a : L, (a : D.La) ∈ lat hP ρ) :
    ∃ φ : L → (PC.A ⟶ T.t.G), (∀ v, IsTangent v → IsHomFamily T.t PC.A PC.L v L ρ Set.univ φ) ∧
      ∀ a z, (u₀.ex fun _ => c * z) ≫ φ a = u.ex (F (z • Pe a)) := by
  obtain ⟨Hm₀, χ₀, Ef, hAH₀, hD₀, -, hθ₀, hE₀, hb⟩ := hu
  let i₀ : Fin PC.g := ⟨0, by omega⟩
  let G : L → (Fin PC.g → ℂ) →ₗ[ℂ] (Fin T.pol.g → ℂ) := fun a =>
    F.toLinearMap ∘ₗ LinearMap.toSpanSingleton ℂ _ (Pe a) ∘ₗ (c⁻¹ • LinearMap.proj i₀)
  have hG : ∀ a z, G a (fun _ => c * z) = F (z • Pe a) := fun a z => by
    simp [G, inv_mul_cancel_left₀ hc]
  have hall : ∀ x : Fin PC.g → ℂ, ∃ z, x = fun _ => c * z := fun x =>
    ⟨c⁻¹ * x i₀, by rw [mul_inv_cancel_left₀ hc]; exact eq_const hg x i₀⟩
  have hline := fun a : L => hermForm_line hP F hAH.1 hAH.2.1 hE hρ ⟨a, hLρ a⟩
  have hGΛ : ∀ a, ∀ x ∈ u₀.Λ, G a x ∈ u.Λ := fun a x hx => by
    obtain ⟨p, q, rfl⟩ := (hΛ x).1 hx
    rw [hG, hF]
    exact (hline a).1 p q
  have hGH : ∀ a x y, hermForm Hm (G a x) (G a y) =
      ((D.EF (H.w0 • (a : D.La)) a).natAbs : ℂ) * hermForm Hm₀ x y := fun a x y => by
    obtain ⟨z, rfl⟩ := hall x
    obtain ⟨w, rfl⟩ := hall y
    rw [hG, hG, (hline a).2, hermForm_of_isQuadLattice hg H.d_prime.pos hc hΛ hAH₀.1 hAH₀.2.1 hE₀ hb.2]
  choose φ hφ hφe using fun a => exists_hom_of_linear_scaling_hermForm PC T.pol u₀ u Hm₀ χ₀ Hm χ hAH₀ hAH
    (fun k => (hθ₀ k).2) hθ (G a) _ (hGΛ a) (hGH a)
  have hφz : ∀ a z, (u₀.ex fun _ => c * z) ≫ φ a = u.ex (F (z • Pe a)) := fun a z => by rw [← hφe, hG]
  have ext : ∀ f f' : PC.A ⟶ T.pol.A, (∀ z, (u₀.ex fun _ => c * z) ≫ f = (u₀.ex fun _ => c * z) ≫ f') → f = f' := by
    intro f f' h
    have hs : Smooth PC.A.hom := PC.isAb.smooth
    have hp : IsProper T.pol.A.hom := T.pol.isAb.proper
    have hr : IsReduced PC.A.left := isReduced_of_smooth_complex _ PC.A.hom hs
    refine ComplexPoints.over_hom_ext_of_complexPoints fun x => ?_
    obtain ⟨x, rfl⟩ := u₀.ex_onto x
    obtain ⟨z, rfl⟩ := hall x
    exact h z
  have hlin : ∀ (s : 𝓞 E) a, φ (s • a) = φ a ≫ T.t.act.act s := fun s a => ext _ _ fun z => by
    rw [← Category.assoc, hφz, hφz, ← hact]
    congr 2
    funext k
    simp only [Submodule.coe_smul, Pi.smul_apply, hP.1, smul_eq_mul]
    ring
  refine ⟨φ, fun v hv => ⟨hφ, fun a b => ext _ _ fun z => ?_, hlin, fun a => ?_, fun a _ => ?_⟩, hφz⟩
  · rw [MonObj.comp_mul, hφz, hφz, hφz, ← u.ex_add, ← map_add, ← smul_add, ← map_add]
    rfl
  · obtain ⟨w, hw, -⟩ := hD₀ v hv
    have := hφ a
    have := hφ (H.rt • a)
    have h₁ := HomLinear.isDiff_comp u₀ u (φ a) (G a) (hφe a) hv hw
    have h₂ := HomLinear.isDiff_comp u₀ u (φ (H.rt • a)) (G _) (hφe _) hv hw
    have e : G (H.rt • a) w = ρ • G a w := by
      obtain ⟨z, rfl⟩ := hall w
      rw [hG, hG, ← map_smul F ρ, smul_comm ρ z, ← period_rt_smul hP (hLρ a)]
      rfl
    rw [e] at h₂
    refine ⟨![CMCurveTest.scaleVec ρ (v ≫ φ a)], fun j => by fin_cases j; rfl, ?_⟩
    rw [← hlin]
    simpa using (hD _).unique ⟨HomLinear.isTangent_comp _ hv, h₂⟩
      ⟨isTangent_scaleVec ρ (HomLinear.isTangent_comp _ hv), CMCurveTest.isDiff_scaleVec u h₁ ρ⟩
  · exact lbIso_pow_of_hermForm_pull_eq PC T.pol u₀ u Hm₀ χ₀ Hm χ hAH₀ hAH (fun k => (hθ₀ k).2) hθ
      (G a) _ (hGΛ a) (hGH a) (φ a) (hφe a)

theorem ontoAt_of_span {A B : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) {I : Type}
    (φ : I → (B ⟶ A)) (v : I → Fin g → ℂ) (hv : Submodule.span ℂ (Set.range v) = ⊤)
    (x : ℂ → (𝟙_ (Over (Sp ℂ)) ⟶ B)) (h : ∀ a z, x z ≫ φ a = u.ex (z • v a)) :
    OntoAt (B := fun _ => B) φ (𝟙 (Sp ℂ)) := by
  intro y
  obtain ⟨w, rfl⟩ := u.ex_onto y
  obtain ⟨n, f, t, rfl⟩ := Submodule.mem_span_set'.1 (hv ▸ Submodule.mem_top : w ∈ Submodule.span ℂ (Set.range v))
  choose i hi using fun m => (t m).2
  refine ⟨n, i, fun m => x (f m), ?_⟩
  have key : ∀ (m : ℕ) (w : Fin m → Fin g → ℂ), u.ex (∑ j, w j) = (List.ofFn fun j => u.ex (w j)).prod := by
    intro m
    induction m with
    | zero => intro w; simp [HermWeil.ex_zero]
    | succ m ih => intro w; rw [List.ofFn_succ, List.prod_cons, ← ih, Fin.sum_univ_succ, u.ex_add]
  refine (key _ _).trans ?_
  simp only [← hi, ← h]

end GlobalTheory.CM.PureTriple

namespace GlobalTheory.CM

open PureTriple PureType

theorem exists_isFam_of_pureType : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ω : ℂ) (C : Ell H ℂ ω) (T : PAT H (Sp ℂ)) (r : ℕ), C.IsPrincipalAt (RingHom.id ℂ) → HasType H T.t.act (2 * ω - 1) r 0 → ∃ (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (ψ : (⊤ : Submodule (𝓞 E) D.La) → (C.P.A ⟶ T.t.G)), D.p + D.q = r ∧ IsKForm D ε h ∧ (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) ∧ IsFam C T h ⊤ ψ ∧ OntoAt ψ (spMap (RingHom.id ℂ)) := by
  intro hT hL E _ _ _ H ω C T r hC hT₀
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := Spec.map_id _
  have hdet := hT₀ ℂ (RingHom.id ℂ) Function.injective_id
  rw [hid] at hdet ⊢
  obtain ⟨τ, hτ, -⟩ := LieChar.ell_char E H ℂ ω C
  have hρ : (2 * ω - 1) ^ 2 = -(H.d : ℂ) := hτ ▸ two_mul_sub_one_sq_of_ringHom τ
  have hsq : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ^ 2 = -(H.d : ℂ) := fun τ => by
    rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  have hd : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.pos.ne'
  obtain ⟨p, q, hpq, hdet', hpure⟩ : ∃ p q : ℕ, p + q = r ∧
      (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ p) ∧
        (τ H.rt ≠ H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ q)) ∧
      ∀ τ : E →+* ℂ, τ (H.rt : E) ≠ 2 * ω - 1 → (τ (H.rt : E) = H.rt0 → p = 0) ∧ (τ (H.rt : E) ≠ H.rt0 → q = 0) := by
    by_cases h0 : 2 * ω - 1 = H.rt0
    · exact ⟨r, 0, rfl, h0 ▸ hdet, fun τ h => ⟨fun h' => absurd (h'.trans h0.symm) h, fun _ => rfl⟩⟩
    · have h1 := (sq_eq_sq_iff_eq_or_eq_neg.1 (hρ.trans H.sqrt_neg_disc_sq.symm)).resolve_left h0
      have h2 : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ≠ H.rt0 → τ H.rt = 2 * ω - 1 := fun τ h =>
        ((sq_eq_sq_iff_eq_or_eq_neg.1 ((hsq τ).trans H.sqrt_neg_disc_sq.symm)).resolve_left h).trans h1.symm
      exact ⟨0, r, zero_add r, fun τ => ⟨fun h => (hdet τ).2 fun h' => h0 (h'.symm.trans h),
        fun h => (hdet τ).1 (h2 τ h)⟩,
        fun τ h => ⟨fun _ => rfl, fun h' => absurd (h2 (τ.comp (algebraMap (𝓞 E) E)) h') h⟩⟩
  obtain ⟨g, ty, hty⟩ := AllClasses.exists_isTypeFn H p q
  obtain ⟨u, Hm, χ, -, hAH, -, hD, hθ, -⟩ := exists_isThetaUnif hT T.pol
  obtain ⟨D, Pe, F, hp, hq, hP, hF, hE, hact⟩ := exists_datum_period hT hL T hty hdet' u hAH
  have hlat : ∀ a : D.La, a ∈ lat hP (2 * ω - 1) := fun a j hj => by
    exfalso
    have : Nonempty {i // ty i = ty j} := ⟨⟨j, rfl⟩⟩
    by_cases h : ty j (H.rt : E) = H.rt0
    · exact Nat.card_pos.ne' (((hty _).1 h).trans ((hpure _ hj).1 h))
    · exact Nat.card_pos.ne' (((hty _).2 h).trans ((hpure _ hj).2 h))
  obtain ⟨u₀, hu₀⟩ := exists_isThetaUnif hT C.P
  obtain ⟨c, hc, hΛ⟩ := hC C.P (𝟙 _) (polFibre_id_comp_cancel.1 ℂ C.P C.v).1 u₀
  obtain ⟨φ, hφ, hφe⟩ := exists_isHomFamily T u hAH hD (fun k => (hθ k).1) F hP hF hE hact u₀ C.dim hu₀ hc hΛ hρ ⊤
    fun a => hlat a
  obtain ⟨ε, hε⟩ : ∃ ε : ℤˣ, 0 < ((ε : ℤ) : ℝ) * ω.im := by
    have him : ω.im ≠ 0 := fun h => by
      have e := congrArg Complex.re hρ
      have hd : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
      simp [pow_two, h] at e
      nlinarith [mul_self_nonneg (2 * ω.re - 1)]
    rcases lt_or_gt_of_ne him with h | h
    · exact ⟨-1, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  have hpos : ∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x := fun x h0 => by
    obtain ⟨s, hs, e⟩ := exists_hermitianPairing_eq_im_mul_pureType hP (hlat x) h0
    have : (0 : ℝ) < ((ε : ℤ) : ℝ) * (D.EF (H.w0 • x) x : ℤ) := by
      rw [e, ← _root_.mul_assoc]
      exact mul_pos hε hs
    exact_mod_cast this
  let h : D.La → D.La → OK H := fun x y =>
    (((ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y) : ℤ) : OK H) + (((ε : ℤ) * D.EF x y : ℤ) : OK H) * wK H
  have hh : IsKForm D ε h := fun x y => by
    simp only [h, wK, Subalgebra.coe_add, Subalgebra.coe_mul, SubringClass.coe_intCast]
  refine ⟨D, ε, h, φ, by rw [hp, hq, hpq], hh, hpos,
    GlobalTheory.T.isCMPairingFamily_of_polarisationDiagonal_complex hT hL E H ω C D ε h T ⊤ φ hh (fun x _ => hpos x) (hφ _ (C.basis.1 0)), ?_⟩
  refine ontoAt_of_span u φ (fun a => F (Pe a)) ?_ (fun z => u₀.ex fun _ => c * z) fun a z => by rw [hφe, map_smul]
  have e : (Set.range fun a : (⊤ : Submodule (𝓞 E) D.La) => F (Pe a)) = F.toLinearMap '' Set.range Pe := by
    ext z
    exact ⟨by rintro ⟨a, rfl⟩; exact ⟨_, ⟨a, rfl⟩, rfl⟩, by rintro ⟨_, ⟨a, rfl⟩, rfl⟩; exact ⟨⟨a, trivial⟩, rfl⟩⟩
  have e' : Submodule.span ℂ (Set.range Pe) = ⊤ :=
    top_le_iff.1 fun z _ => Submodule.span_subset_span ℝ ℂ _ (hP.2.2.2.1 ▸ Submodule.mem_top : z ∈ Submodule.span ℝ _)
  rw [e, ← Submodule.map_span, e', Submodule.map_top, LinearEquiv.range]

end GlobalTheory.CM
end
