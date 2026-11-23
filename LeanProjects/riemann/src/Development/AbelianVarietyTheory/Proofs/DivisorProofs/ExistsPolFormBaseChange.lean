import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmEllipticCurveIsPureHodgeEndomorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormsCommensurable

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel.HalfLower

section Lin

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}

omit [NumberField E] [IsCMField E] in

theorem inK_injective [Module.Free O H] : Function.Injective (inK (O := O) K H) := by
  have h := (Module.Flat.rTensor_preserves_injective_linearMap (M := H) (Algebra.linearMap O K)
    (IsFractionRing.injective O K)).comp (TensorProduct.lid O H).symm.injective
  intro x y hxy
  apply h
  simpa [inK] using hxy

theorem bar_bar (σ : E →+* K) : bar (bar σ) = σ := by
  ext x; simp [bar]

omit [IsDomain O] [IsFractionRing O K] in

theorem baseChange_inK (B : LinearMap.BilinForm O H) (x y : H) :
    B.baseChange K (inK K H x) (inK K H y) = algebraMap O K (B x y) := by
  simp [inK, Algebra.smul_def]

omit [IsCMField E] [IsDomain O] [IsFractionRing O K] in

theorem form_act (ρ : orderC c →+* Module.End O H) (B : LinearMap.BilinForm O H) {σ : E →+* K} {f : H}
    (hf : f ∈ eigLat ρ σ) (a : orderC c) (x : H) : algebraMap O K (B x (ρ a f)) = σ a * algebraMap O K (B x f) := by
  have h : inK K H f ∈ eigK ρ σ := hf
  have h1 := Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 h a)
  have h2 : (ρ a).baseChange K (inK K H f) = inK K H (ρ a f) := by simp [inK]
  rw [← baseChange_inK, ← baseChange_inK, ← h2, h1, map_smul, smul_eq_mul]

theorem lower_eq [Module.Free O H] (ρ : orderC c →+* Module.End O H) (B : LinearMap.BilinForm O H) {D : O} (hD : D ≠ 0)
    {τ : E →+* K} {e f : H} (he : eigLat ρ τ = O ∙ e) (hf : f ∈ eigLat ρ (bar τ))
    (hsup : ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat ρ σ)
    (horth : ∀ σ σ' : E →+* K, σ' ≠ bar σ → ∀ x ∈ eigK ρ σ, ∀ y ∈ eigK ρ σ', B.baseChange K x y = 0)
    {N : Module.End K (K ⊗[O] H)} {M : Module.End O H} (hN : IsLower ρ τ e f N) (hM : IsScaledRestr D N M) (x : H) :
    B e f • M x = (D * B x f) • f := by
  have key : ∀ h ∈ ⨆ σ : E →+* K, eigLat ρ σ, B e f • M h = (D * B h f) • f := by
    intro h hh
    induction hh using Submodule.iSup_induction' with
    | mem σ h hh =>
      by_cases hσ : σ = τ
      · subst hσ
        rw [he] at hh
        obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hh
        have hMe : M e = D • f := inK_injective (K := K) (by rw [hM, hN.1, map_smul, algebraMap_smul])
        simp only [map_smul, hMe, LinearMap.smul_apply, smul_eq_mul, smul_smul]
        congr 1; ring
      · have h1 : M h = 0 := inK_injective (K := K) (by rw [hM, hN.2 σ hσ _ hh, smul_zero, map_zero])
        have h2 : B h f = 0 := IsFractionRing.injective O K (by
          rw [← baseChange_inK, map_zero]
          exact horth σ (bar τ) (fun h' ↦ hσ (by rw [← bar_bar σ, ← h', bar_bar])) _ hh _ hf)
        simp [h1, h2]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, LinearMap.add_apply, smul_add, mul_add, add_smul, hx, hy]
  have h := key _ (hsup x)
  apply smul_right_injective H hD
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h ⊢
  rw [smul_comm D, h, smul_smul]

theorem lower_eq_of_scale [CharZero O] [Module.Free O H] (ρ : orderC c →+* Module.End O H) (B B' : LinearMap.BilinForm O H)
    {D : O} (hD : D ≠ 0)
    {τ : E →+* K} {e f : H} (he : eigLat ρ τ = O ∙ e) (hf : f ∈ eigLat ρ (bar τ))
    (hsup : ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat ρ σ)
    (horth : ∀ σ σ' : E →+* K, σ' ≠ bar σ → ∀ x ∈ eigK ρ σ, ∀ y ∈ eigK ρ σ', B.baseChange K x y = 0)
    {N : Module.End K (K ⊗[O] H)} {M : Module.End O H} (hN : IsLower ρ τ e f N) (hM : IsScaledRestr D N M)
    {n : ℕ} (hn : n ≠ 0) (a : orderC c) (hB : ∀ x y, (n : O) * B' x y = 2 * B x (ρ a y)) (h0 : B' e f ≠ 0) (x : H) :
    B' e f • M x = (D * B' x f) • f := by
  have hn' : (n : O) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h1 : B e (ρ a f) * B x f = B x (ρ a f) * B e f := IsFractionRing.injective O K (by
    rw [map_mul, map_mul, form_act ρ B hf, form_act ρ B hf]; ring)
  have h2 : B' e f * B x f = B' x f * B e f :=
    mul_left_cancel₀ hn' (by linear_combination B x f * hB e f - B e f * hB x f + 2 * h1)
  have hβ : B e f ≠ 0 := fun hβ ↦ h0 (mul_left_cancel₀ hn' (by
    have : B e (ρ a f) = 0 := IsFractionRing.injective O K (by rw [form_act ρ B hf, hβ]; simp)
    rw [hB, this]; simp))
  apply smul_right_injective H hβ
  simp only
  rw [smul_comm, lower_eq ρ B hD he hf hsup horth hN hM, smul_smul, smul_smul]
  congr 1
  linear_combination D * h2

end Lin

theorem exists_polForm_baseChange {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R R' : Type} [CommRing R] [CommRing R']
    (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {p : X'.A.left ⟶ X.A.left}
    (hX : X'.IsPullBy X (spMap σ) p) (m : GrpMor (dp0 R) (𝟙 _) X.A (dp0 R') (𝟙 _) X'.A σ (spMap σ) p) (c : 𝔠.elt)
    {ψ : LinearMap.BilinForm R (HdR X.A)} (hψ : IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ) :
    ∃ ψ' : LinearMap.BilinForm R' (HdR X'.A), IsPolForm (dp0 R') (𝟙 _) X'.A (X'.diag c) ψ' ∧
      ∀ x x' y y', m.Corr x x' → m.Corr y y' → ψ' x' y' = σ (ψ x y) := by
  obtain ⟨ψ', ⟨n, a, b, hch, he⟩, h'⟩ :=
    IsPolForm.pull_comp m (X.isLB c) (π := (lift (𝟙 X.A) (𝟙 X.A)).left) (L := X.P c) hψ
  obtain ⟨φ₂, hsq, hiso⟩ := hX.pol
  have e : (lift (𝟙 X'.A) (𝟙 X'.A)).left ≫ φ₂ = p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left := by
    apply pullback.hom_ext
    · change _ ≫ (fst X.A X.A).left = _ ≫ (fst X.A X.A).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst]
      simp
    · change _ ≫ (snd X.A X.A).left = _ ≫ (snd X.A X.A).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd]
      simp
  have hI : LBIso (X'.diag c) ((X.P c).pull (p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso (hiso c) _ e.symm
  exact ⟨ψ', ⟨n, a, b, (isChern_existsUnique_and_iso _ _ _ _ _).2 _ _ (pull_isLB (X.isLB c) _)
    (pull_isLB (X'.isLB c) _) hI.symm _ hch, he⟩, h'⟩

theorem corr_lower (hDR : GlobalTheory.Published.AbelianDeRham) {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
    {𝔠 : FracId (FR E)} {R : Subring ℂ} {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    {X₀ : Obj (FR E) 𝔠 (Sp R)} {X : Obj (FR E) 𝔠 (Sp ℂ)} {p : X.A.left ⟶ X₀.A.left} (cm : OAct (orderC c) X₀.A)
    (hrm : ∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = X₀.rm.act a)
    {n : ℕ} (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) {c₀ c₁ : 𝔠.elt} {ψ₀ ψR : LinearMap.BilinForm R (HdR X₀.A)} (hc₀ : (c₀ : FR E) ≠ 0)
    (hψ₀ : IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) ((2 : R) • ψ₀)) (hψR : IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₁) ψR)
    {D : R} (hD : D ≠ 0) {τ : E →+* K} {e f : Fin n → R}
    (he : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) τ = R ∙ e)
    (hf : f ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar τ))
    (hsup : ∀ h : Fin n → R, D • h ∈ ⨆ σ : E →+* K, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) σ)
    (horth : ∀ σ σ' : E →+* K, σ' ≠ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ →
      ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) σ,
      ∀ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) σ',
      LinearMap.BilinForm.baseChange K (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) x y = 0)
    {N : Module.End K (K ⊗[R] (Fin n → R))} {M : Module.End R (Fin n → R)}
    (hN : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsLower (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) τ e f N)
    (hM : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsScaledRestr D N M)
    (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p)
    {ψ : LinearMap.BilinForm ℂ (HdR X.A)} (hψ : ∀ x x' y y', m.Corr x x' → m.Corr y y' → ψ x' y' = algebraMap R ℂ (ψR x y))
    {ev yv : HdR X.A} (hev : m.Corr (eH.symm e) ev) (hyv : m.Corr (eH.symm f) yv) (h0 : ψ ev yv ≠ 0)
    (x₀ : HdR X₀.A) (x : HdR X.A) (hx : m.Corr x₀ x) :
    m.Corr (eH.symm.conjRingEquiv M x₀) ((((D : ℂ) / ψ ev yv) • (ψ.flip yv).smulRight yv) x) := by
  obtain ⟨k, t, hk, ht⟩ := GlobalTheory.RealMult.PolScale.exists_nat_mul_polForm_eq hDR (FR E) 𝔠 R X₀ c₁ c₀ hc₀ ψR _ hψR hψ₀
  have hact : act (dp0 R) (𝟙 _) X₀.rm t = act (dp0 R) (𝟙 _) cm (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c t) := by
    haveI := X₀.rm.hom t
    haveI := cm.hom (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c t)
    rw [act_apply, act_apply]
    exact push_congr _ _ (hrm t).symm
  have hγ := hψ _ _ _ _ hev hyv
  have h1 := lower_eq_of_scale (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm))
    (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap) (ψR.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap) hD he hf hsup horth
    hN hM hk (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c t) (fun x y ↦ by
      have := ht (eH.symm x) (eH.symm y)
      rw [hact] at this
      simpa using this) (fun h ↦ h0 (by
      have h' : ψR (eH.symm e) (eH.symm f) = 0 := h
      rw [hγ, h', map_zero])) (eH x₀)
  have h2 : ψR (eH.symm e) (eH.symm f) • eH.symm (M (eH x₀)) = (D * ψR x₀ (eH.symm f)) • eH.symm f := by
    have := congrArg eH.symm h1
    simpa using this
  intro z
  have h3 := congrArg (algebraMap R ℂ) (LinearMap.congr_fun h2 z)
  simp only [LinearMap.smul_apply, smul_eq_mul, map_mul] at h3
  have h4 : eH.symm.conjRingEquiv M x₀ = eH.symm (M (eH x₀)) := rfl
  rw [h4]
  simp only [LinearMap.smul_apply, LinearMap.smulRight_apply, LinearMap.flip_apply, smul_eq_mul]
  have h5 : ψ.flip yv x = algebraMap R ℂ (ψR x₀ (eH.symm f)) := hψ _ _ _ _ hx hyv
  rw [hyv z, h5, div_mul_eq_mul_div, div_eq_iff h0, hγ]
  have h6 : algebraMap R ℂ D = (D : ℂ) := rfl
  rw [h6] at h3
  linear_combination -h3

theorem neg_le_val_inv {R : Subring ℂ} [IsDiscreteValuationRing R] (l : ℕ) (x : R) (q : ℚ) (hx : x ≠ 0)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) x) ≤ (q : WithTop ℚ)) :
    ((-q : ℚ) : WithTop ℚ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l ((algebraMap R (FractionRing R) x)⁻¹) := by
  have hx' : algebraMap R (FractionRing R) x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hx
  unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp at h ⊢
  rw [if_neg hx'] at h
  rw [if_neg (inv_ne_zero hx')]
  have ho : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R ((algebraMap R (FractionRing R) x)⁻¹) = - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (algebraMap R (FractionRing R) x) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw
    rw [map_inv₀, WithZero.log_inv, neg_neg]
  rw [ho]
  have h' := WithTop.coe_le_coe.1 h
  refine WithTop.coe_le_coe.2 ?_
  push_cast
  rw [neg_div]
  exact neg_le_neg h'

end GlobalTheory.LatModel.HalfLower
