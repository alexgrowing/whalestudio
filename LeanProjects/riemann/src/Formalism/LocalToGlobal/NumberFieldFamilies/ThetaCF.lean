import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB
import Formalism.SharpRestriction.InertJacobiLevels.ExtraTheta
import Formalism.LocalRingCardinality.SpanPowerMembership.BaseFormAnisotropicOrthogonalSingle

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gaps

variable (D : D7)

def AtTauU : Prop := ∀ (V : HSp D) (τ : D.what₂.Tau), ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∃! h, IsAtTau (th0 D) V τ g h

def SmAdd : Prop := ∀ (V : HSp D) (φ φ' : GA D V → ℂ), IsAutFunSm (th0 D) V φ → IsAutFunSm (th0 D) V φ' →
  IsAutFunSm (th0 D) V (φ + φ')

def SmRight : Prop := ∀ (V : HSp D) (k : GA D V), k ∈ GfC V ∨ k ∈ GinfC V → ∀ φ : GA D V → ℂ, IsAutFunSm (th0 D) V φ →
  IsAutFunSm (th0 D) V (rTr V k φ)

def SmConj : Prop := ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFunSm (th0 D) V φ → IsAutFunSm (th0 D) V (star φ)

def CuspInt : Prop := ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFun V φ →
  ∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C →
    ∀ (μ : Measure (NI V C)) (𝓕 : Set (NI V C)), μ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓕 μ →
      ∀ g, IntegrableOn (fun n : NI V C => φ ((n : GA D V) * g)) 𝓕 μ

def VolU : Prop := ∀ V : HSp D, V.SigOK → ∀ μ μ' : Measure (GA D V),
  IsVolMeasG D V (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) μ →
  IsVolMeasG D V (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) μ' → μ = μ'

def VolEx : Prop := ∀ V : HSp D, V.SigOK → ∃ μ 𝓕, IsVolPair D V μ 𝓕

def PetInt : Prop := ∀ (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure →
  IsFundamentalDomain (GQ V) 𝓕 μ → ∀ φ φ' : GA D V → ℂ, IsAutFunSm (th0 D) V φ → IsAutFunSm (th0 D) V φ' → IsCuspFun V φ' →
    IntegrableOn (fun h => star (φ h) * φ' h) 𝓕 μ

def TypZero : Prop := ∀ V : HSp D, V.SigOK → ∀ (τ : D.what₂.Tau) (S : SPar),
  GoodPar V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 S → IsTypeAt (th0 D) V τ S 0

def TypAdd : Prop := ∀ V : HSp D, V.SigOK → ∀ (τ : D.what₂.Tau) (S : SPar),
  GoodPar V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 S → ∀ φ φ' : GA D V → ℂ,
    φ ∈ Submodule.span ℂ {f | IsAutFunSm (th0 D) V f} → φ' ∈ Submodule.span ℂ {f | IsAutFunSm (th0 D) V f} →
    IsTypeAt (th0 D) V τ S φ → IsTypeAt (th0 D) V τ S φ' → IsTypeAt (th0 D) V τ S (φ + φ')

end Gaps

variable {D : D7}

theorem Rder_smul (θ : InfF D) (V : HSp D) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (c : ℂ)
    (φ : GA D V → ℂ) : Rder θ V τ X (c • φ) = c • Rder θ V τ X φ := by
  funext g
  simp only [Rder, Pi.smul_apply, smul_eq_mul]
  rw [deriv_const_mul_field']

theorem sm_smul (θ : InfF D) (V : HSp D) (c : ℂ) (φ : GA D V → ℂ) (h : IsAutFunSm θ V φ) : IsAutFunSm θ V (c • φ) where
  left := fun γ hγ g => by simp only [Pi.smul_apply, h.left γ hγ g]
  level := by
    obtain ⟨U, hU, hk⟩ := h.level
    exact ⟨U, hU, fun k a b g => by simp only [Pi.smul_apply, hk k a b g]⟩
  cont := h.cont.const_smul c
  smooth := fun k τs Xs hX g => (h.smooth k τs Xs hX g).const_smul c
  zfin := by
    obtain ⟨W, a, b, e⟩ := h.zfin
    exact ⟨W, a, W.smul_mem c b, e⟩
  growth := by
    obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl x
    have e : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ),
        l.foldr (fun p f => Rder θ V p.1 p.2 f) (c • φ) = c • l.foldr (fun p f => Rder θ V p.1 p.2 f) φ := by
      intro l
      induction l with
      | nil => rfl
      | cons p l ih => rw [List.foldr_cons, List.foldr_cons, ih, Rder_smul]
    refine ⟨‖c‖ * C, fun g hg => ?_⟩
    rw [e, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g hg) (norm_nonneg _)

variable (D) in

def afC (V : HSp D) : Submodule ℂ (GA D V → ℂ) := Submodule.span ℂ {φ | IsAutFunSm (th0 D) V φ}

theorem mem_afC (h : SmAdd D) {V : HSp D} {φ : GA D V → ℂ} : φ ∈ afC D V ↔ IsAutFunSm (th0 D) V φ := by
  refine ⟨fun hφ => ?_, fun hφ => Submodule.subset_span hφ⟩
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact isAutFunSm_const _ V 0
  | add x y _ _ hx hy => exact h V x y hx hy
  | smul c x _ hx => exact sm_smul _ V c x hx

def rTrL (V : HSp D) (k : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) := LinearMap.funLeft ℂ ℂ (fun g => g * k)

theorem rTrL_mem (h : SmRight D) {V : HSp D} {k : GA D V} (hk : k ∈ GfC V ∨ k ∈ GinfC V) :
    ∀ φ ∈ afC D V, rTrL V k φ ∈ afC D V := by
  intro φ hφ
  unfold afC at hφ ⊢
  induction hφ using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (h V k hk x hx)
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

def actC (h : SmRight D) (V : HSp D) (k : GA D V) (hk : k ∈ GfC V ∨ k ∈ GinfC V) : Module.End ℂ (afC D V) :=
  (rTrL V k).restrict (rTrL_mem h hk)

theorem actC_apply (h : SmRight D) (V : HSp D) (k : GA D V) (hk : k ∈ GfC V ∨ k ∈ GinfC V) (F : afC D V) (x : GA D V) :
    (actC h V k hk F).1 x = F.1 (x * k) := rfl

def actFC (h : SmRight D) (V : HSp D) : GfC V →* Module.End ℂ (afC D V) where
  toFun k := actC h V k (Or.inl k.2)
  map_one' := by
    ext F x
    rw [actC_apply]
    simp
  map_mul' a b := by
    ext F x
    rw [Module.End.mul_apply, actC_apply, actC_apply, actC_apply]
    simp [mul_assoc]

def actRC (h : SmRight D) (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Module.End ℂ (afC D V) :=
  actC h V (atTau (th0 D) V τ g) (Or.inr (atTau_mem _ V τ g))

theorem atTau_spec (hU : AtTauU D) {V : HSp D} {τ : D.what₂.Tau} {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : IsAtTau (th0 D) V τ g (atTau (th0 D) V τ g) := by
  have hex : ∃ x, IsAtTau (th0 D) V τ g x := (hU V τ g hg).exists
  unfold atTau
  rw [dif_pos hex]
  exact hex.choose_spec

theorem atTau_eq (hU : AtTauU D) {V : HSp D} {τ : D.what₂.Tau} {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {h : GA D V} (hh : IsAtTau (th0 D) V τ g h) : atTau (th0 D) V τ g = h := by
  exact (hU V τ g hg).unique (atTau_spec hU hg) hh

theorem uh_mul {n : ℕ} {J g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH J) (hh : h ∈ Formalism.QuantumDeterminants.UH J) :
    g * h ∈ Formalism.QuantumDeterminants.UH J := by
  have hg' : gᴴ * J * g = J := hg
  have hh' : hᴴ * J * h = J := hh
  show (g * h)ᴴ * J * (g * h) = J
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * J * (g * h) = hᴴ * (gᴴ * J * g) * h := by simp only [mul_assoc]
    _ = J := by rw [hg', hh']

theorem atTau_one (hU : AtTauU D) (V : HSp D) (τ : D.what₂.Tau) : atTau (th0 D) V τ 1 = 1 := by
  have h1 : (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
    show (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * gramAt D V τ * 1 = gramAt D V τ
    simp
  refine atTau_eq hU h1 ⟨one_mem _, ?_, fun τ' _ => ?_⟩
  · unfold infMat
    change (Matrix.map (Units.val (1 : GL (Fin V.rank) (AF ↥D.host.F ⊗[↥D.host.F] D.host.E))) _).map _ = _
    rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]
  · unfold infMat
    change (Matrix.map (Units.val (1 : GL (Fin V.rank) (AF ↥D.host.F ⊗[↥D.host.F] D.host.E))) _).map _ = _
    rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]

theorem atTau_mul (hU : AtTauU D) (V : HSp D) (τ : D.what₂.Tau) {g h : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hh : h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    atTau (th0 D) V τ (g * h) = atTau (th0 D) V τ g * atTau (th0 D) V τ h := by
  have hmul : ∀ (τ' : D.what₂.Tau) (a b : GA D V), infMat D.sp.cm.sig V.gram (th0 D τ') (a * b) =
      infMat D.sp.cm.sig V.gram (th0 D τ') a * infMat D.sp.cm.sig V.gram (th0 D τ') b := by
    intro τ' a b
    unfold infMat
    change ((Units.val (HA.mat _ _ _ a * HA.mat _ _ _ b)).map _).map _ = _
    rw [Units.val_mul]
    ext i j
    simp [Matrix.mul_apply, map_sum]
  have sg := atTau_spec hU hg
  have sh := atTau_spec hU hh
  refine atTau_eq hU (uh_mul hg hh) ⟨mul_mem sg.1 sh.1, ?_, fun τ' hτ' => ?_⟩
  · rw [hmul, sg.2.1, sh.2.1]
  · rw [hmul, sg.2.2 τ' hτ', sh.2.2 τ' hτ', one_mul]

theorem star_mem (h : SmConj D) (V : HSp D) : ∀ φ ∈ afC D V, star φ ∈ afC D V := by
  intro φ hφ
  unfold afC at hφ ⊢
  induction hφ using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (h V x hx)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [star_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [star_smul]
    exact Submodule.smul_mem _ _ hx

def conjC (h : SmConj D) (V : HSp D) (F : afC D V) : afC D V := ⟨star F.1, star_mem h V F.1 F.2⟩

variable (D) in

def cuspC (V : HSp D) : Submodule ℂ (afC D V) := Submodule.span ℂ {F | IsCuspFun V F.1}

theorem mem_cuspC (hA : SmAdd D) (hI : CuspInt D) {V : HSp D} {F : afC D V} : F ∈ cuspC D V ↔ IsCuspFun V F.1 := by
  refine ⟨fun hF => ?_, fun hF => Submodule.subset_span hF⟩
  induction hF using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => intro r C _ μ 𝓕 _ _ g; simp
  | add x y _ _ hx hy =>
    intro r C hC μ 𝓕 h1 h2 g
    have a := hI V x.1 ((mem_afC hA).1 x.2).toIsAutFun r C hC μ 𝓕 h1 h2 g
    have b := hI V y.1 ((mem_afC hA).1 y.2).toIsAutFun r C hC μ 𝓕 h1 h2 g
    have e := integral_add a b
    rw [hx r C hC μ 𝓕 h1 h2 g, hy r C hC μ 𝓕 h1 h2 g, add_zero] at e
    exact e
  | smul c x _ hx =>
    intro r C hC μ 𝓕 h1 h2 g
    have e := hx r C hC μ 𝓕 h1 h2 g
    show ∫ n in 𝓕, c * x.1 ((n : GA D V) * g) ∂μ = 0
    rw [integral_const_mul, e, mul_zero]

theorem actC_cusp (h : SmRight D) (V : HSp D) (k : GA D V) (hk : k ∈ GfC V ∨ k ∈ GinfC V) :
    ∀ F ∈ cuspC D V, actC h V k hk F ∈ cuspC D V := by
  intro F hF
  unfold cuspC at hF ⊢
  induction hF using Submodule.span_induction with
  | mem x hx =>
    apply Submodule.subset_span
    intro r C hC μ 𝓕 hμ h𝓕 g
    show ∫ n in 𝓕, x.1 ((n : GA D V) * g * k) ∂μ = 0
    simp only [mul_assoc]
    exact hx r C hC μ 𝓕 hμ h𝓕 (g * k)
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

theorem conjC_add (h : SmConj D) (V : HSp D) (F F' : afC D V) : conjC h V (F + F') = conjC h V F + conjC h V F' := by
  apply Subtype.ext
  exact star_add _ _

theorem conjC_smul (h : SmConj D) (V : HSp D) (c : ℂ) (F : afC D V) : conjC h V (c • F) = star c • conjC h V F := by
  apply Subtype.ext
  exact star_smul _ _

theorem conjC_cusp (h : SmConj D) (V : HSp D) : ∀ F ∈ cuspC D V, conjC h V F ∈ cuspC D V := by
  intro F hF
  unfold cuspC at hF ⊢
  induction hF using Submodule.span_induction with
  | mem x hx =>
    apply Submodule.subset_span
    intro r C hC μ 𝓕 hμ h𝓕 g
    show ∫ n in 𝓕, star (x.1 ((n : GA D V) * g)) ∂μ = 0
    simp only [Complex.star_def]
    rw [integral_conj, hx r C hC μ 𝓕 hμ h𝓕 g]
    simp
  | zero =>
    have : conjC h V 0 = 0 := by
      apply Subtype.ext
      exact star_zero _
    rw [this]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [conjC_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [conjC_smul]
    exact Submodule.smul_mem _ _ hx

theorem finMat_mul (V : HSp D) (g h : GA D V) :
    finMat D.sp.cm.sig V.gram (g * h) = finMat D.sp.cm.sig V.gram g * finMat D.sp.cm.sig V.gram h := by
  unfold finMat
  change (Units.val (HA.mat _ _ _ g * HA.mat _ _ _ h)).map _ = _
  rw [Units.val_mul]
  ext i j
  simp [Matrix.mul_apply, map_sum]

theorem finMat_one (V : HSp D) : finMat D.sp.cm.sig V.gram 1 = 1 := by
  unfold finMat
  change Matrix.map (Units.val (1 : GL (Fin V.rank) (AF ↥D.host.F ⊗[↥D.host.F] D.host.E))) _ = _
  rw [Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem map_inv_one {n : ℕ} {R S Φ : Type} [CommRing R] [CommRing S] [FunLike Φ R S] [RingHomClass Φ R S] (f : Φ)
    (A B : Matrix (Fin n) (Fin n) R) (h : A * B = 1) (hA : A.map f = 1) : B.map f = 1 := by
  have e : (A * B).map f = A.map f * B.map f := by
    ext i j
    simp [Matrix.mul_apply, map_sum, map_mul]
  rw [h, hA, one_mul] at e
  rw [← e]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

def ksphC (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Subgroup (GfC V) where
  carrier := {g | (g : GA D V) ∈ KsphC V S}
  one_mem' := ⟨one_mem _, fun y => by rw [OneMemClass.coe_one, finMat_one, Matrix.one_mulVec], fun v _ => by
    rw [OneMemClass.coe_one, finMat_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)⟩
  mul_mem' := fun {a b} ha hb => ⟨(a * b).2, fun y => by
      rw [Subgroup.coe_mul, finMat_mul, ← Matrix.mulVec_mulVec, ← ha.2.1, ← hb.2.1], fun v hv => by
      rw [Subgroup.coe_mul, finMat_mul, Matrix.map_mul, ha.2.2 v hv, hb.2.2 v hv, one_mul]⟩
  inv_mem' := fun {a} ha => ⟨(a⁻¹).2, fun y => by
      rw [ha.2.1 ((finMat D.sp.cm.sig V.gram ((a⁻¹ : GfC V) : GA D V)).mulVec y), Matrix.mulVec_mulVec, ← finMat_mul,
        ← Subgroup.coe_mul, mul_inv_cancel, OneMemClass.coe_one, finMat_one, Matrix.one_mulVec], fun v hv => by
      have e0 : finMat D.sp.cm.sig V.gram (a : GA D V) * finMat D.sp.cm.sig V.gram ((a⁻¹ : GfC V) : GA D V) = 1 := by
        rw [← finMat_mul, ← Subgroup.coe_mul, mul_inv_cancel, OneMemClass.coe_one, finMat_one]
      exact map_inv_one _ _ _ e0 (ha.2.2 v hv)⟩

variable (D) in

def typC (V : HSp D) (P : D.what₂.Tau → SPar) : Submodule ℂ (afC D V) :=
  Submodule.span ℂ {F | ∀ τ, IsTypeAt (th0 D) V τ (P τ) F.1}

theorem typ_smul (θ : InfF D) (V : HSp D) (τ : D.what₂.Tau) (S : SPar) (c : ℂ) (φ : GA D V → ℂ) (h : IsTypeAt θ V τ S φ) :
    IsTypeAt θ V τ S (c • φ) := by
  obtain ⟨H, i1, i2, σ, lam, ε, P, a1, a2, a3, a4, hx⟩ := h
  refine ⟨H, i1, i2, σ, lam, ε, P, a1, a2, a3, a4, fun x => ?_⟩
  obtain ⟨v, hv, ℓ, hl, ⟨S', C, hS, hb, hs, hB⟩, he⟩ := hx x
  refine ⟨v, hv, fun i => c • ℓ i, fun i => ?_, ⟨S', fun i => ‖c‖ * C i, hS, fun i w hw => ?_,
    fun S'' hS'' => ((hs S'' hS'').mul_left ‖c‖).congr fun i => by ring, hB⟩, fun g hg => ?_⟩
  · obtain ⟨S'', C', b1, b2⟩ := hl i
    refine ⟨S'', ‖c‖ * C', b1, fun w hw => ?_⟩
    rw [LinearMap.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (b2 w hw) (norm_nonneg _)
  · rw [LinearMap.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb i w hw) (norm_nonneg _)
  · exact (he g hg).mul_left c

theorem mem_typC (h0 : TypZero D) (hA : TypAdd D) {V : HSp D} (hV : V.SigOK) {P : D.what₂.Tau → SPar}
    (hP : ∀ τ, GoodPar V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 (P τ)) {F : afC D V} :
    F ∈ typC D V P ↔ ∀ τ, IsTypeAt (th0 D) V τ (P τ) F.1 := by
  refine ⟨fun hF => ?_, fun hF => Submodule.subset_span hF⟩
  induction hF using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact fun τ => h0 V hV τ _ (hP τ)
  | add x y _ _ hx hy => exact fun τ => hA V hV τ _ (hP τ) _ _ x.2 y.2 (hx τ) (hy τ)
  | smul c x _ hx => exact fun τ => typ_smul _ V τ _ c _ (hx τ)

theorem emb_star (τ : D.host.E →+* ℂ) (x : D.host.E) : τ (star x) = starRingEnd ℂ (τ x) := by
  exact @NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ _ D.host.isCMField_hostE _ τ x

theorem gram_herm (V : HSp D) (τ : D.host.E →+* ℂ) : Formalism.UG.IsHerm (starRingEnd ℂ) (V.gram.map τ) := by
  unfold Formalism.UG.IsHerm Formalism.UG.cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, HSpace.gram]
  rw [← emb_star]
  congr 1
  have := V.herm.eq (V.frame j) (V.frame i)
  rw [starRingEnd_apply] at this
  exact this

theorem sig_ex (V : HSp D) (τ : D.host.E →+* ℂ) : ∃ s : ℕ × ℕ, Formalism.UG.HasSignature (V.gram.map τ) s.1 s.2 := by
  obtain ⟨p, q, h⟩ := Formalism.UG.P.signature_exists _ (V.gram.map τ) (gram_herm V τ) (by
    have : (V.gram.map τ).det = τ V.gram.det := (τ.map_det V.gram).symm
    rw [this]
    exact ((map_ne_zero τ).2 (gram_det_ne V)).isUnit)
  exact ⟨(p, q), h⟩

open Classical in

def fixSig (V : HSp D) : HSp D := { V with sig := if V.SigOK then V.sig else fun τ => (sig_ex V τ).choose }

theorem fixSig_ok (V : HSp D) : (fixSig V).SigOK := by
  unfold HSpace.SigOK
  intro τ
  by_cases h : V.SigOK
  · simp only [fixSig, h, if_true]
    exact h τ
  · simp only [fixSig, h, if_false]
    exact (sig_ex V τ).choose_spec

def GoodPair (V : HSp D) (p : Measure (GA D V) × Set (GA D V)) : Prop :=
  p.1.IsHaarMeasure ∧ IsFundamentalDomain (GQ V) p.2 p.1 ∧ (V.SigOK → IsVolPair D V p.1 p.2)

theorem goodPair_iff (V : HSp D) (p : Measure (GA D V) × Set (GA D V)) :
    GoodPair V p ↔ GoodPairR D.sp.cm (tauE D) D.cd V p :=
  ⟨fun h => ⟨h.1, h.2.1, fun a => (h.2.2 a).1⟩, fun h => ⟨h.1, h.2.1, fun a => ⟨h.2.2 a, h.2.1⟩⟩⟩

theorem goodPair_ex (h : VolEx D) (V : HSp D) : ∃ p, GoodPair V p := by
  by_cases hV : V.SigOK
  · obtain ⟨μ, 𝓕, e⟩ := h V hV
    exact ⟨(μ, 𝓕), e.1.1, e.2, fun _ => e⟩
  · obtain ⟨μ, 𝓕, e⟩ := h (fixSig V) (fixSig_ok V)
    exact ⟨(μ, 𝓕), e.1.1, e.2, fun a => absurd a hV⟩

def pairC (V : HSp D) : Measure (GA D V) × Set (GA D V) := pairR D.sp.cm (tauE D) D.cd V

theorem pairC_spec (h : VolEx D) (V : HSp D) : GoodPair V (pairC V) := by
  have e : ∃ p, GoodPairR D.sp.cm (tauE D) D.cd V p := (goodPair_ex h V).imp fun p hp => (goodPair_iff V p).1 hp
  rw [goodPair_iff]
  unfold pairC pairR
  rw [dif_pos e]
  exact e.choose_spec

def intC (V : HSp D) (f : GA D V → ℂ) : ℂ := ∫ h in (pairC V).2, f h ∂(pairC V).1

theorem fd_int_eq {V : HSp D} {μ : Measure (GA D V)} (hμ : μ.IsHaarMeasure) {𝓕 𝓕' : Set (GA D V)}
    (h : IsFundamentalDomain (GQ V) 𝓕 μ) (h' : IsFundamentalDomain (GQ V) 𝓕' μ) (f : GA D V → ℂ)
    (hf : ∀ γ ∈ GQ V, ∀ x, f (γ * x) = f x) : ∫ x in 𝓕, f x ∂μ = ∫ x in 𝓕', f x ∂μ := by
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  exact h.setIntegral_eq h' fun γ x => hf γ γ.2 x

theorem intC_eq (hE : VolEx D) (hU : VolU D) {V : HSp D} (hV : V.SigOK) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}
    (h : IsVolPair D V μ 𝓕) (f : GA D V → ℂ) (hf : ∀ γ ∈ GQ V, ∀ x, f (γ * x) = f x) :
    intC V f = ∫ x in 𝓕, f x ∂μ := by
  have s := pairC_spec hE V
  have e : (pairC V).1 = μ := hU V hV _ _ (s.2.2 hV).1 h.1
  unfold intC
  have s2 := s.2.1
  rw [e] at s2 ⊢
  exact fd_int_eq h.1.1 s2 h.2 f hf

def volG (V : HSp D) : ℝ := ((pairC V).1 (pairC V).2).toReal

def VolFin (D : D7) : Prop := ∀ (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure →
  IsFundamentalDomain (GQ V) 𝓕 μ → μ 𝓕 ≠ ⊤

theorem petR_ex (p q : ℕ) : ∃ c : ℝ, 0 < c ∧ OmegaDensity (ENNReal.ofReal c • D.cd.cd p q) (minfDensity (p + q)) := by
  obtain ⟨c, h0, ht, ⟨lam, hl, hlim⟩, -⟩ := D.cd.trick p q
  have m0 : minfDensity (p + q) ≠ 0 := by unfold minfDensity; simp
  have mt : minfDensity (p + q) ≠ ⊤ := by unfold minfDensity; simp
  have d0 : minfDensity (p + q) / c ≠ 0 := ENNReal.div_ne_zero.2 ⟨m0, ht⟩
  have dt : minfDensity (p + q) / c ≠ ⊤ := ENNReal.div_ne_top mt h0
  refine ⟨(minfDensity (p + q) / c).toReal, ENNReal.toReal_pos d0 dt, lam, hl, ?_⟩
  rw [ENNReal.ofReal_toReal dt]
  have := ENNReal.Tendsto.const_mul (a := minfDensity (p + q) / c) hlim (Or.inr dt)
  rw [ENNReal.div_mul_cancel h0 ht] at this
  refine this.congr fun r => ?_
  rw [Measure.smul_apply, smul_eq_mul, mul_div_assoc]

variable (D) in

def petRC (p q : ℕ) : ℝ := if p = 0 ∨ q = 0 then 1 else (petR_ex (D := D) p q).choose

theorem petRC_pos (p q : ℕ) : 0 < petRC D p q := by
  unfold petRC
  split_ifs
  · norm_num
  · exact (petR_ex (D := D) p q).choose_spec.1

theorem petRC_minf (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    OmegaDensity (ENNReal.ofReal (petRC D p q) • D.cd.cd p q) (minfDensity (p + q)) := by
  unfold petRC
  rw [if_neg (by omega)]
  exact (petR_ex (D := D) p q).choose_spec.2

def petC (petF : HSp D → ℝ) (V : HSp D) (F : afC D V) (G : cuspC D V) : ℂ :=
  (petCOf D petF (petRC D) V : ℂ) * intC V fun h => star (F.1 h) * G.1.1 h

theorem pet_int (hE : VolEx D) (hA : SmAdd D) (hC : CuspInt D) (hI : PetInt D) (V : HSp D) (F : afC D V) (G : cuspC D V) :
    IntegrableOn (fun h => star (F.1 h) * G.1.1 h) (pairC V).2 (pairC V).1 :=
  hI V _ _ (pairC_spec hE V).1 (pairC_spec hE V).2.1 _ _ ((mem_afC hA).1 F.2) ((mem_afC hA).1 G.1.2)
    ((mem_cuspC hA hC).1 G.2)

theorem petC_pos (hE : VolEx D) (hA : SmAdd D) (hC : CuspInt D) (hI : PetInt D) (petF : HSp D → ℝ) (hp : ∀ V, 0 < petF V)
    (V : HSp D) (F : cuspC D V) (hF : F ≠ 0) : 0 < (petC petF V F.1 F).re := by
  have s := pairC_spec hE V
  have hs := (mem_afC hA).1 F.1.2
  have hint := pet_int hE hA hC hI V F.1 F
  have e : (fun h => star (F.1.1 h) * F.1.1 h) = fun h => ((‖F.1.1 h‖ ^ 2 : ℝ) : ℂ) := by
    funext h
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  have hc : 0 < petCOf D petF (petRC D) V := mul_pos (hp V) (Finset.prod_pos fun _ _ => petRC_pos _ _)
  unfold petC intC
  rw [e] at hint ⊢
  rw [integral_complex_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  refine mul_pos hc ?_
  have hint' : IntegrableOn (fun h => ‖F.1.1 h‖ ^ 2) (pairC V).2 (pairC V).1 := by
    exact hint.re.congr (Filter.Eventually.of_forall fun h => Complex.ofReal_re _)
  refine lt_of_le_of_ne (integral_nonneg fun h => by positivity) fun h0 => hF ?_
  have h1 := (integral_eq_zero_iff_of_nonneg (fun h => by positivity) hint').1 h0.symm
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  haveI := s.1
  have hU : IsOpen {h | F.1.1 h ≠ 0} := isOpen_ne_fun hs.cont continuous_const
  have h2 : (pairC V).1 ({h | F.1.1 h ≠ 0} ∩ (pairC V).2) = 0 := by
    rw [← Measure.restrict_apply hU.measurableSet]
    refine measure_mono_null (fun h hh => ?_) h1
    simpa using hh
  have h3 : (pairC V).1 {h | F.1.1 h ≠ 0} = 0 := by
    refine s.2.1.measure_zero_of_invariant _ (fun γ => ?_) h2
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    show F.1.1 (((γ⁻¹ : GQ V) : GA D V) * x) ≠ 0 ↔ F.1.1 x ≠ 0
    rw [hs.left _ (γ⁻¹).2]
  have h4 := (hU.measure_eq_zero_iff (pairC V).1).1 h3
  apply Subtype.ext
  apply Subtype.ext
  funext x
  by_contra hx
  exact (Set.eq_empty_iff_forall_notMem.1 h4 x) hx

end Formalism.L2.Fam.ThC

end
