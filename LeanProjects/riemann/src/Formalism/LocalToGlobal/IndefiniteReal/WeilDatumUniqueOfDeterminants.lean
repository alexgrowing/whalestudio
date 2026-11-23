import Formalism.LocalToGlobal.IndefiniteReal.InjectiveDecompositionAction

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis Formalism.IndefR.InjectiveDecompositionAction
  IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.flipTwoThree

def DeterminantInUnitaryOne : Prop :=
  ∀ (D : D7) (V : HSp D) (g : GA D V), (mt V g).det * cA D (mt V g).det = 1

def RatDetP : Prop :=
  ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ q : D.host.E, incA D q * cA D (incA D q) = 1 →
    ∃ γ ∈ GQ V, (mt V γ).det = incA D q

def SplitDetP : Prop :=
  ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ e, IsSplitIdem D e → ∀ x : (AE D)ˣ, (x : AE D) * cA D (x : AE D) = 1 →
    SuppAtU D e x → ∃ g : GA D V, SuppAt e V g ∧ (∃ x', IsDetAt e V g x') ∧ (mt V g).det = x

variable {D : D7}

theorem mt_mul' (V : HSp D) (g g' : GA D V) :
    L2.Theta.mt V (g * g') = L2.Theta.mt V g * L2.Theta.mt V g' := by
  simp [L2.Theta.mt, map_mul]

theorem mt_one' (V : HSp D) : L2.Theta.mt V 1 = 1 := by
  simp [L2.Theta.mt, map_one]

theorem cM_mul' {n : ℕ} (x y : Matrix (Fin n) (Fin n) (AE D)) : cM (x * y) = cM x * cM y := by
  simp [cM, Matrix.map_mul]

theorem actHom_mul' (V W : HSp D) (g g' : GA D V) (h h' : GA D W) (w : WA V W) :
    actHom V W g h (actHom V W g' h' w) = actHom V W (g * g') (h * h') w := by
  unfold actHom
  split_ifs with hr
  · rw [mt_mul', mt_mul', cM_mul', Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  · rw [mt_mul', mt_mul', cM_mul', Matrix.transpose_mul]; simp only [Matrix.mul_assoc]

theorem actHom_one' (V W : HSp D) (w : WA V W) : actHom V W 1 1 w = w := by
  unfold actHom
  split_ifs <;> simp [mt_one', cM]

section Scalar

variable (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χ χ' : (AE D)ˣ →* Circle)
    (ω ω' : GA D V × GA D W →* Module.End ℂ (Hth ψ V W))

theorem scalar_step (hS : SvNSchur ψ V W) (hω : IsWeilDatum ψ V W χ χ' ω)
    (hω' : IsWeilDatum ψ V W χ χ' ω') (p : GA D V × GA D W) : ∃ c : ℂ, ‖c‖ = 1 ∧ ω' p = c • ω p := by
  obtain ⟨c, hc, hT⟩ := hS (ω' p * ω p⁻¹) (by
      intro w₀ Φ Φ' hΦ
      have h1 := hω.om_heis p⁻¹.1 p⁻¹.2 w₀ Φ Φ' hΦ
      simp only [Prod.mk.eta] at h1
      have h2 := hω'.om_heis p.1 p.2 (actHom V W p⁻¹.1 p⁻¹.2 w₀) (ω p⁻¹ Φ) (ω p⁻¹ Φ') h1
      simp only [Prod.mk.eta, actHom_mul', Prod.fst_inv, Prod.snd_inv, mul_inv_cancel, actHom_one'] at h2
      simpa [Module.End.mul_apply] using h2)
    (by
      intro μ 𝓕 hμ h𝓕 Φ
      simp only [Module.End.mul_apply]
      rw [hω'.om_unit μ 𝓕 hμ h𝓕 p (ω p⁻¹ Φ), hω.om_unit μ 𝓕 hμ h𝓕 p⁻¹ Φ])
  refine ⟨c, hc, ?_⟩
  have e1 : ω' p = (ω' p * ω p⁻¹) * ω p := by
    rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  rw [e1]
  ext Φ : 1
  simp only [Module.End.mul_apply, LinearMap.smul_apply]
  exact hT (ω p Φ)

theorem omega_inv_apply (p : GA D V × GA D W) (Φ : Hth ψ V W) : ω p (ω p⁻¹ Φ) = Φ := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem scalar_unique (hΘ : ThetaNZ ψ V W) (p : GA D V × GA D W) (c c' : ℂ)
    (h : c • ω p = c' • ω p) : c = c' := by
  obtain ⟨Φ, hΦ⟩ := hΘ
  have := congrArg (fun T : Module.End ℂ (Hth ψ V W) => ((T (ω p⁻¹ Φ) : Hth ψ V W) : WA V W → ℂ) 0) h
  simp only [LinearMap.smul_apply, omega_inv_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hΦ this

theorem scalar_rat (hΘ : ThetaNZ ψ V W) (hω : IsWeilDatum ψ V W χ χ' ω)
    (hω' : IsWeilDatum ψ V W χ χ' ω') (γ : GA D V) (hγ : γ ∈ GQ V) (γ' : GA D W) (hγ' : γ' ∈ GQ W) (c : ℂ)
    (h : ω' (γ, γ') = c • ω (γ, γ')) : c = 1 := by
  obtain ⟨Φ, hΦ⟩ := hΘ
  have e := congrArg (fun T : Module.End ℂ (Hth ψ V W) => ((T Φ : Hth ψ V W) : WA V W → ℂ) 0) h
  simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at e
  rw [hω'.om_aut γ hγ γ' hγ' Φ, hω.om_aut γ hγ γ' hγ' Φ] at e
  have : c * (Φ : WA V W → ℂ) 0 = 1 * (Φ : WA V W → ℂ) 0 := by rw [← e, one_mul]
  exact mul_right_cancel₀ hΦ this

theorem scalar_cont (hΘ : ThetaNZ ψ V W) (hω : IsWeilDatum ψ V W χ χ' ω)
    (hω' : IsWeilDatum ψ V W χ χ' ω') (c : GA D V × GA D W → ℂ) (hc : ∀ p, ω' p = c p • ω p) :
    Continuous c := by
  obtain ⟨Φ₀, hΦ₀⟩ := hΘ
  rw [continuous_iff_continuousAt]
  intro p₀
  set Φ₁ := ω p₀⁻¹ Φ₀
  let f : GA D V × GA D W → ℂ := fun p => ((ω p Φ₁ : Hth ψ V W) : WA V W → ℂ) 0
  let g : GA D V × GA D W → ℂ := fun p => ((ω' p Φ₁ : Hth ψ V W) : WA V W → ℂ) 0
  have hf : Continuous f := hω.om_cont Φ₁ 0
  have hg : Continuous g := hω'.om_cont Φ₁ 0
  have hf0 : f p₀ ≠ 0 := by simp only [f, Φ₁, omega_inv_apply]; exact hΦ₀
  have hgf : ∀ p, g p = c p * f p := by
    intro p; simp only [g, f, hc p, LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  have hev : (fun p => g p / f p) =ᶠ[nhds p₀] c := by
    filter_upwards [hf.continuousAt.eventually_ne hf0] with p hp
    rw [hgf p]; field_simp
  exact (hg.continuousAt.div hf.continuousAt hf0).congr hev

theorem scalar_mul (hΘ : ThetaNZ ψ V W) (c : GA D V × GA D W → ℂ) (hc : ∀ p, ω' p = c p • ω p)
    (p q : GA D V × GA D W) : c (p * q) = c p * c q := by
  apply scalar_unique ψ V W ω hΘ (p * q)
  rw [← hc, map_mul, map_mul, hc p, hc q, smul_mul_smul_comm]

theorem scalar_split (hF : SplitFormsNZ ψ V W) (hω : IsWeilDatum ψ V W χ χ' ω) (hω' : IsWeilDatum ψ V W χ χ' ω')
    (e : AE D) (he : IsSplitIdem D e) (g : GA D V) (h : GA D W) (hg : SuppAt e V g) (hh : SuppAt e W h)
    (x y : (AE D)ˣ) (hx : IsDetAt e V g x) (hy : IsDetAt e W h y) (c : ℂ) (hc1 : ‖c‖ = 1)
    (hc : ω' (g, h) = c • ω (g, h)) : c = 1 := by
  obtain ⟨ℓ, hinv, Φ, hΦ⟩ := hF e he
  obtain ⟨r, hr, hr1⟩ := hω.om_split e he g h hg hh x y hx hy
  obtain ⟨r', hr', hr1'⟩ := hω'.om_split e he g h hg hh x y hx hy
  have a1 := hr1 ℓ hinv Φ
  have a2 := hr1' ℓ hinv Φ
  rw [hc, LinearMap.smul_apply, map_smul, smul_eq_mul, a1] at a2
  have hs : ((splitFac V W χ χ' x y : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have key : c * (r : ℂ) = (r' : ℂ) := by
    have hne : ((splitFac V W χ χ' x y : Circle) : ℂ) * ℓ Φ ≠ 0 := mul_ne_zero hs hΦ
    apply mul_right_cancel₀ hne
    linear_combination a2
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hc' : c = ((r' / r : ℝ) : ℂ) := by
    push_cast; rw [← key]; field_simp
  rw [hc'] at hc1 ⊢
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hr' hr)] at hc1
  rw [hc1]; simp

end Scalar

section Side

def toCircle {G : Type*} [Group G] (f : G → ℂ) (hf1 : ∀ g, ‖f g‖ = 1) (h1 : f 1 = 1)
    (hmul : ∀ g g', f (g * g') = f g * f g') : G →* Circle where
  toFun g := (⟨f g, by simp [Submonoid.unitSphere, hf1 g]⟩ : Submonoid.unitSphere ℂ)
  map_one' := Subtype.ext h1
  map_mul' g g' := Subtype.ext (hmul g g')

def detU (hD : DeterminantInUnitaryOne) (V : HSp D) (g : GA D V) : FirstPropositionFrame D :=
  ⟨Units.mkOfMulEqOne _ _ (hD D V g), hD D V g⟩

theorem side_trivial (hD : DeterminantInUnitaryOne) (hR : RatDetP) (hSp : SplitDetP) (V : HSp D) (hCV : CharDet V)
    (hU1 : SecondCharacterFact D) (f : GA D V → ℂ) (hf1 : ∀ g, ‖f g‖ = 1) (h1 : f 1 = 1)
    (hmul : ∀ g g', f (g * g') = f g * f g') (hcont : Continuous f) (hrat : ∀ γ ∈ GQ V, f γ = 1)
    (hsplit : ∀ e, IsSplitIdem D e → ∀ g, SuppAt e V g → (∃ x, IsDetAt e V g x) → f g = 1) (g : GA D V) :
    f g = 1 := by
  obtain ⟨lam, hlamc, hlam⟩ := hCV (toCircle f hf1 h1 hmul) (Continuous.subtype_mk hcont _)
  have key : ∀ (g : GA D V) (x : FirstPropositionFrame D), (((x : (AE D)ˣ)) : AE D) = (mt V g).det →
      f g = ((lam x : Circle) : ℂ) := by
    intro g x hx
    rw [← hlam g x hx]; rfl
  rcases Nat.eq_zero_or_pos V.rank with hn | hn
  · have hdet : (mt V g).det = 1 := by
      have : IsEmpty (Fin V.rank) := by rw [hn]; infer_instance
      exact Matrix.det_isEmpty
    rw [key g 1 (by rw [hdet]; rfl), map_one, Circle.coe_one]
  · have hlam1 : ∀ x, lam x = 1 := by
      refine hU1 lam hlamc ?_ ?_
      · intro x q hxq
        have hq : incA D q * cA D (incA D q) = 1 := by rw [← hxq]; exact x.2
        obtain ⟨γ, hγ, hdet⟩ := hR D V hn q hq
        have h2 := key γ x (by rw [hdet, hxq])
        rw [hrat γ hγ] at h2
        exact Circle.ext (by rw [Circle.coe_one]; exact h2.symm)
      · intro e he x hx
        obtain ⟨g, hgS, hgD, hdet⟩ := hSp D V hn e he (x : (AE D)ˣ) x.2 hx
        have h2 := key g x hdet.symm
        rw [hsplit e he g hgS hgD] at h2
        exact Circle.ext (by rw [Circle.coe_one]; exact h2.symm)
    rw [key g (detU hD V g) rfl, hlam1, Circle.coe_one]

end Side

theorem weil_datum_unique_of_determinants (hD : DeterminantInUnitaryOne) (hR : RatDetP) (hSp : SplitDetP) : ConsequenceOfAdmissibleConstants := by
  intro D ψ V W χ χ' ω ω' hS hΘ hF hCV hCW hU1 hω hω'
  choose c hc1 hc using scalar_step ψ V W χ χ' ω ω' hS hω hω'
  have cmul := scalar_mul ψ V W ω ω' hΘ c hc
  have ccont := scalar_cont ψ V W χ χ' ω ω' hΘ hω hω' c hc
  have crat : ∀ γ ∈ GQ V, ∀ γ' ∈ GQ W, c (γ, γ') = 1 := fun γ hγ γ' hγ' =>
    scalar_rat ψ V W χ χ' ω ω' hΘ hω hω' γ hγ γ' hγ' _ (hc _)
  have csplit : ∀ e, IsSplitIdem D e → ∀ g h, SuppAt e V g → SuppAt e W h → (∃ x, IsDetAt e V g x) →
      (∃ y, IsDetAt e W h y) → c (g, h) = 1 := by
    rintro e he g h hg hh ⟨x, hx⟩ ⟨y, hy⟩
    exact scalar_split ψ V W χ χ' ω ω' hF hω hω' e he g h hg hh x y hx hy _ (hc1 _) (hc _)
  have h11 : c (1, 1) = 1 := crat 1 (one_mem _) 1 (one_mem _)
  have supp1 : ∀ (U : HSp D) (e : AE D), SuppAt e U (1 : GA D U) := by
    intro U e i j; simp [mt_one']
  have det1 : ∀ (U : HSp D) (e : AE D), IsDetAt e U (1 : GA D U) 1 := by
    intro U e; simp only [IsDetAt, mt_one', Matrix.det_one, Units.val_one, mul_one]; ring
  have hV : ∀ g : GA D V, c (g, 1) = 1 := by
    refine side_trivial hD hR hSp V hCV hU1 (fun g => c (g, 1)) (fun g => hc1 _) h11 ?_ ?_ ?_ ?_
    · intro g g'
      rw [show ((g * g', (1 : GA D W)) : GA D V × GA D W) = (g, 1) * (g', 1) by simp, cmul]
    · exact ccont.comp (continuous_id.prodMk continuous_const)
    · intro γ hγ; exact crat γ hγ 1 (one_mem _)
    · intro e he g hg hx; exact csplit e he g 1 hg (supp1 W e) hx ⟨1, det1 W e⟩
  have hW : ∀ h : GA D W, c (1, h) = 1 := by
    refine side_trivial hD hR hSp W hCW hU1 (fun h => c (1, h)) (fun h => hc1 _) h11 ?_ ?_ ?_ ?_
    · intro h h'
      rw [show (((1 : GA D V), h * h') : GA D V × GA D W) = (1, h) * (1, h') by simp, cmul]
    · exact ccont.comp (continuous_const.prodMk continuous_id)
    · intro γ hγ; exact crat 1 (one_mem _) γ hγ
    · intro e he h hh hy; exact csplit e he 1 h (supp1 V e) hh ⟨1, det1 V e⟩ hy
  refine MonoidHom.ext fun p => ?_
  have hp : c p = 1 := by
    rw [show p = (p.1, 1) * (1, p.2) by ext <;> simp, cmul, hV, hW, one_mul]
  rw [hc p, hp, one_smul]

end Formalism.IndefR.flipTwoThree

end
