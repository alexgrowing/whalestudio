import Development.AutomorphicArithmetic.AdelicQuotients.RieszRepresentationSesquilinear
import Development.AutomorphicArithmetic.AdelicQuotients.MeasurableOfSeparatingFunctionals
import Development.AutomorphicArithmetic.AdelicQuotients.InnerProductIntegralFundamentalDomainOfCompact
import Development.AutomorphicArithmetic.AdelicQuotients.IrreducibleHermitianFormUnique
import Development.WeilBound.ThetaLifts.LatticeBasics.ThetaBox
import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.ArchHeisOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GalTPDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGDecomp

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
namespace UpperTheory.TP
private theorem assemble_pk {H A V : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsOpenPosMeasure] (Γ : Subgroup H) [Countable Γ] (𝓕 : Set H)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hfin : μ 𝓕 < ⊤) (Ω : Set H) (hΩ : IsCompact Ω) (hcov : ∀ g, ∃ γ ∈ Γ, γ * g ∈ Ω)
    [Group A] [MeasurableSpace A] [MeasurableMul A] (μA : Measure A) [IsFiniteMeasure μA] [μA.IsMulLeftInvariant]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] (π : A →* Module.End ℂ V)
    (hI : ∀ W : Submodule ℂ V, (∀ g, ∀ w ∈ W, π g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (ι : A →* H) (hι : Measurable ι)
    (f : V →ₗ[ℂ] (H → ℂ)) (hf0 : ∀ a, f a = 0 → a = 0) (hfc : ∀ a, Continuous (f a))
    (hfl : ∀ a, ∀ γ ∈ Γ, ∀ h, f a (γ * h) = f a h) (hfr : ∀ x a y, f (π x a) y = f a (y * ι x))
    (B₁ : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB₁ : ∀ g a b, B₁ (π g a) (π g b) = B₁ a b) (x₀ : V)
    (u : H → ℂ) (huc : Continuous u) (hul : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) :
    ∫ x, B₁ (π x x₀) x₀ * star (pet μ 𝓕 (fun y => u (y * ι x)) (f x₀)) ∂μA =
      ((μA.real Set.univ / (Module.finrank ℂ V : ℝ) : ℝ) : ℂ) * B₁ x₀ x₀ * star (pet μ 𝓕 u (f x₀)) := by
  have P := fun g₁ g₂ c₁ c₂ l₁ l₂ => UpperTheory.innerProduct_integral_fundamentalDomain_of_compact μ Γ 𝓕 h𝓕 hfin Ω hΩ hcov g₁ g₂ c₁ c₂ l₁ l₂
  have hpet : ∀ g₁ g₂ : H → ℂ, pet μ 𝓕 g₁ g₂ = ∫ h in 𝓕, g₁ h * starRingEnd ℂ (g₂ h) ∂μ := fun _ _ => rfl
  have addL : ∀ g₁ g₂ g₃ : H → ℂ, Continuous g₁ → Continuous g₂ → Continuous g₃ → (∀ γ ∈ Γ, ∀ h, g₁ (γ * h) = g₁ h) →
      (∀ γ ∈ Γ, ∀ h, g₂ (γ * h) = g₂ h) → (∀ γ ∈ Γ, ∀ h, g₃ (γ * h) = g₃ h) →
      pet μ 𝓕 (g₁ + g₂) g₃ = pet μ 𝓕 g₁ g₃ + pet μ 𝓕 g₂ g₃ := fun g₁ g₂ g₃ c₁ c₂ c₃ l₁ l₂ l₃ => by
    simp only [hpet, Pi.add_apply, add_mul]
    exact integral_add (P _ _ c₁ c₃ l₁ l₃).1 (P _ _ c₂ c₃ l₂ l₃).1
  have addR : ∀ g₁ g₂ g₃ : H → ℂ, Continuous g₁ → Continuous g₂ → Continuous g₃ → (∀ γ ∈ Γ, ∀ h, g₁ (γ * h) = g₁ h) →
      (∀ γ ∈ Γ, ∀ h, g₂ (γ * h) = g₂ h) → (∀ γ ∈ Γ, ∀ h, g₃ (γ * h) = g₃ h) →
      pet μ 𝓕 g₃ (g₁ + g₂) = pet μ 𝓕 g₃ g₁ + pet μ 𝓕 g₃ g₂ := fun g₁ g₂ g₃ c₁ c₂ c₃ l₁ l₂ l₃ => by
    simp only [hpet, Pi.add_apply, map_add, mul_add]
    exact integral_add (P _ _ c₃ c₁ l₃ l₁).1 (P _ _ c₃ c₂ l₃ l₂).1
  have smL : ∀ (c : ℂ) (g₁ g₂ : H → ℂ), pet μ 𝓕 (c • g₁) g₂ = c * pet μ 𝓕 g₁ g₂ := fun c g₁ g₂ => by
    simp only [hpet, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul _ _
  have smR : ∀ (c : ℂ) (g₁ g₂ : H → ℂ), pet μ 𝓕 g₁ (c • g₂) = starRingEnd ℂ c * pet μ 𝓕 g₁ g₂ := fun c g₁ g₂ => by
    simp only [hpet, Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm _ (starRingEnd ℂ c)]
    exact integral_const_mul _ _
  let B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun a b => pet μ 𝓕 (f a) (f b))
    (fun a b c => by
      rw [map_add]; exact addL _ _ _ (hfc a) (hfc b) (hfc c) (hfl a) (hfl b) (hfl c))
    (fun c a b => by rw [map_smul]; exact smL _ _ _)
    (fun a b c => by
      rw [map_add]; exact addR _ _ _ (hfc b) (hfc c) (hfc a) (hfl b) (hfl c) (hfl a))
    (fun c a b => by rw [map_smul]; exact smR _ _ _)
  have hB : ∀ a b, B a b = pet μ 𝓕 (f a) (f b) := fun _ _ => rfl
  have hh : ∀ a b, B b a = star (B a b) := fun a b => by
    simp only [hB, hpet]
    rw [show star (∫ h in 𝓕, f a h * starRingEnd ℂ (f b h) ∂μ) = starRingEnd ℂ (∫ h in 𝓕, f a h * starRingEnd ℂ (f b h) ∂μ) from rfl,
      ← integral_conj]
    congr 1
    funext h
    simp [mul_comm]
  have hp : ∀ a, a ≠ 0 → 0 < (B a a).re := fun a ha =>
    (P _ _ (hfc a) (hfc a) (hfl a) (hfl a)).2.2 fun h => ha (hf0 a h)
  have hinv : ∀ g a b, B (π g a) (π g b) = B a b := fun g a b => by
    simp only [hB, hpet, hfr]
    exact (P _ _ (hfc a) (hfc b) (hfl a) (hfl b)).2.1 (ι g)
  obtain ⟨c', hc'⟩ := UpperTheory.invariant_sesquilinearForm_eq_smul_of_irreducible π hI B hh hp hinv B₁ hB₁
  let L : V →ₗ⋆[ℂ] ℂ :=
    { toFun := fun b => pet μ 𝓕 u (f b)
      map_add' := fun a b => by rw [map_add]; exact addR _ _ _ (hfc a) (hfc b) huc (hfl a) (hfl b) hul
      map_smul' := fun c a => by rw [map_smul]; exact smR _ _ _ }
  obtain ⟨u₀, hu₀⟩ := UpperTheory.riesz_representation_sesquilinear B hh hp L
  have hL : ∀ b, pet μ 𝓕 u (f b) = B u₀ b := hu₀
  have key : ∀ x, pet μ 𝓕 (fun y => u (y * ι x)) (f x₀) = B (π x u₀) x₀ := fun x => by
    have e1 := (P (fun y => u (y * ι x)) (f x₀) (huc.comp (continuous_mul_right _)) (hfc x₀)
      (fun γ hγ h => by simp only [mul_assoc, hul γ hγ]) (hfl x₀)).2.1 (ι x⁻¹)
    have e2 : ∀ h, f x₀ (h * ι x⁻¹) = f (π x⁻¹ x₀) h := fun h => (hfr _ _ _).symm
    have e3 : ∀ h, u (h * ι x⁻¹ * ι x) = u h := fun h => by
      rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
    simp only [e2, e3] at e1
    rw [hpet, ← e1, ← hpet, hL, ← hinv x u₀]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hm : ∀ a b, Measurable fun g => B (π g a) b := fun a b => by
    let l : H → V →ₗ[ℂ] ℂ := fun y => (LinearMap.proj y).comp f
    let Lb : V →ₗ[ℂ] ℂ :=
      { toFun := fun a => B a b
        map_add' := fun a a' => by simp
        map_smul' := fun c a => by simp }
    refine UpperTheory.measurable_of_separating_functionals l (fun a h => hf0 a (funext h)) (fun g => π g a) (fun y => ?_) Lb
    show Measurable fun g => f (π g a) y
    simp only [hfr]
    exact (hfc a).measurable.comp (measurable_const_mul y |>.comp hι)
  have hO := UpperTheory.irreducible_hermitian_form_unique μA π hI B hh hp hinv hm x₀ x₀ u₀ x₀
  simp only [key, hc']
  simp only [mul_assoc]
  rw [integral_const_mul]
  simp only [← mul_assoc] at hO ⊢
  rw [hO, hL x₀, hh x₀ u₀, star_star]
  have : star (B x₀ x₀) = B x₀ x₀ := (hh x₀ x₀).symm
  rw [this]
  ring
end UpperTheory.TP
theorem UpperTheory.TP.schurStep_k : _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.SchurStep_k := by
  intro T E _ _ _ B n d X W M χX χW om P hn e e' he he' U hU f₀ hf₀ φ hφ hS ν hν φf hfin μA hμA
  obtain ⟨V, _, _, _, ρ, i, j, x₀, hirr, hi, hj, hjU, hA, hR⟩ := hS
  have C := T.cpt _ E (UpperTheory.TP.cj E) B n X n 0 P.base (Or.inl P.herm) (by simp)
  have D := _root_.UpperTheory.TP.decomp_k T _ E (UpperTheory.TP.cj E) B n X P.base P.herm ∅
  haveI := C.lc
  haveI := C.sc
  haveI := C.t2
  haveI := C.cnt
  haveI : BorelSpace (UA (UpperTheory.TP.cj E) X.J) := ⟨rfl⟩
  haveI hHaar : M.μ.IsHaarMeasure := P.good.haar
  haveI := C.right _ hHaar
  haveI : CompactSpace (UpperTheory.TP.gInf (UpperTheory.TP.cj E) X) := isCompact_iff_compactSpace.1 D.2.1
  haveI : IsFiniteMeasure μA := inferInstance
  have hx₀ : x₀ ≠ 0 := fun h => hφ (by rw [← hj, h, map_zero])
  haveI : Nontrivial V := ⟨x₀, 0, hx₀⟩
  have hsymm : ∀ x : UpperTheory.TP.gInf (UpperTheory.TP.cj E) X, e.symm x.1 ∈ GlobalTheory.UnitaryBC.infU E n :=
    fun x => (he.inf _).1 (by simpa using x.2)
  let p : UpperTheory.TP.gInf (UpperTheory.TP.cj E) X →* GlobalTheory.UnitaryBC.infU E n :=
    { toFun := fun x => ⟨e.symm x.1, hsymm x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have hpe : ∀ x, e (p x).1 = x.1 := fun x => e.apply_symm_apply _
  have hpsurj : ∀ k : GlobalTheory.UnitaryBC.infU E n, ∃ x, p x = k := fun k =>
    ⟨⟨e k.1, (he.inf _).2 k.2⟩, Subtype.ext (e.symm_apply_apply _)⟩
  let π : UpperTheory.TP.gInf (UpperTheory.TP.cj E) X →* Module.End ℂ V := ρ.comp p
  have hI : ∀ W' : Submodule ℂ V, (∀ g, ∀ w ∈ W', π g w ∈ W') → W' = ⊥ ∨ W' = ⊤ := fun W' h => by
    let S : Subrepresentation ρ := ⟨W', fun k v hv => by
      obtain ⟨x, rfl⟩ := hpsurj k
      exact h x v hv⟩
    rcases hirr.eq_bot_or_eq_top S with h1 | h1
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h1)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)
  have hj0 : ∀ a, j a = 0 → a = 0 := fun a ha => by
    have hk := hI (LinearMap.ker j) (fun g w hw => by
      have hw' : j w = 0 := hw
      show j (ρ (p g) w) = 0
      rw [hR, hw', map_zero])
    rcases hk with h1 | h1
    · have : a ∈ LinearMap.ker j := ha
      rwa [h1, Submodule.mem_bot] at this
    · have : x₀ ∈ LinearMap.ker j := by rw [h1]; trivial
      exact absurd ((LinearMap.mem_ker.1 this).symm.trans (by rw [hj]) |>.symm) hφ
  let f : V →ₗ[ℂ] (UA (UpperTheory.TP.cj E) X.J → ℂ) := (LinearMap.funLeft ℂ ℂ e.symm).comp j
  have hfa : ∀ a y, f a y = j a (e.symm y) := fun _ _ => rfl
  have hf0 : ∀ a, f a = 0 → a = 0 := fun a ha => hj0 a (funext fun y => by
    have := congrFun ha (e y)
    rwa [hfa, e.symm_apply_apply] at this)
  have hleft : ∀ a, ∀ γ ∈ ratU (UpperTheory.TP.cj E) X.J, ∀ h, j a (e.symm (γ * h)) = j a (e.symm h) := fun a γ hγ h => by
    rw [map_mul]
    exact (hU.aut _ (hjU a)).left _ ((he.rat _).1 (by simpa using hγ)) _
  have hfc : ∀ a, Continuous (f a) := fun a => (hU.aut _ (hjU a)).cont.comp e.symm.continuous
  have hfr : ∀ x a y, f (π x a) y = f a (y * (UpperTheory.TP.gInf (UpperTheory.TP.cj E) X).subtype x) := fun x a y => by
    show j (ρ (p x) a) (e.symm y) = j a (e.symm (y * x.1))
    rw [hR, map_mul]
    rfl
  have h2 : ∀ᶠ v in cofinite, φf v = Set.indicator {x | ∀ i, x i ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers _ v} 1 :=
    (hfin.2.and P.good.std).mono fun v h => h.1.trans h.2
  have hrest := fun s => PositivityTheory.ThKG.Loc.Bump.rest_pure s φf hfin.1 h2
  let Ψ : V →ₗ[ℂ] ((Fin n × Fin d → AF (maximalRealSubfield E)) → ℂ) :=
    { toFun := fun a => pure (i a) φf
      map_add' := fun a b => by
        funext x
        simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
      map_smul' := fun c a => by
        funext x
        simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc] }
  have hΨa : ∀ a, Ψ a = pure (i a) φf := fun _ => rfl
  have hΨ : ∀ a, Ψ a ∈ schA _ (Fin n × Fin d) := fun a => (hrest (i a)).2
  have hact : ∀ x a, om (x.1, 1) (Ψ a) = Ψ (π x a) := fun x a => by
    have h := hA (p x) a _ (hrest (i a))
    rw [hpe] at h
    exact h
  have hsp := IsUWeilPair.isUSplitting P.weil
  let B₁ : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun a b => lD _ (Fin n × Fin d) (boxFun (Ψ a) (star (Ψ b))))
    (fun a b c => by rw [map_add, GlobalTheory.SchwartzBox.boxFun_add_left, map_add])
    (fun c a b => by rw [map_smul, GlobalTheory.SchwartzBox.boxFun_smul_left, map_smul]; rfl)
    (fun a b c => by rw [map_add, star_add, GlobalTheory.SchwartzBox.boxFun_add_right, map_add])
    (fun c a b => by rw [map_smul, star_smul, GlobalTheory.SchwartzBox.boxFun_smul_right, map_smul]; rfl)
  have hB₁a : ∀ a b, B₁ a b = lD _ (Fin n × Fin d) (boxFun (Ψ a) (star (Ψ b))) := fun _ _ => rfl
  have hB₁ : ∀ g a b, B₁ (π g a) (π g b) = B₁ a b := fun g a b => by
    rw [hB₁a, hB₁a, ← hact, ← hact]
    exact lD_unit hsp.unit hsp.pres (g.1, 1) (hΨ a) (hΨ b)
  obtain ⟨c, c0, hc⟩ := lD_haar ν hν
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 c0.ne'
  have hΦ : pure f₀ φf = Ψ x₀ := by rw [hΨa, hi]
  have hco : ∀ x : UpperTheory.TP.gInf (UpperTheory.TP.cj E) X, coef om ν (pure f₀ φf) x.1 = (c : ℂ)⁻¹ * B₁ (π x x₀) x₀ := fun x => by
    rw [hB₁a, hc _ (hΨ _) _ (hΨ _), inv_mul_cancel_left₀ hc0, ← hact, hΦ]
    rfl
  have hco1 : coef om ν (pure f₀ φf) 1 = (c : ℂ)⁻¹ * B₁ x₀ x₀ := by
    have := hco 1
    rwa [map_one, Module.End.one_apply] at this
  have hφU : φ ∈ U := hj ▸ hjU x₀
  have hform := hU.aut φ hφU
  obtain ⟨Ω, hΩ, hcov⟩ := C.cov
  refine ⟨((μA.real Set.univ / (Module.finrank ℂ V : ℝ) : ℝ) : ℂ), ?_, fun cc _ => ?_⟩
  · have h1 : 0 < μA.real Set.univ :=
      ENNReal.toReal_pos (IsOpen.measure_pos μA isOpen_univ Set.univ_nonempty).ne' (measure_ne_top _ _)
    have h3 : (0 : ℝ) < Module.finrank ℂ V := by exact_mod_cast Module.finrank_pos
    exact Complex.ofReal_ne_zero.2 (div_pos h1 h3).ne'
  have hmain := UpperTheory.TP.assemble_pk M.μ (ratU (UpperTheory.TP.cj E) X.J) M.dom P.good.dom (C.fin _ _ hHaar P.good.dom) Ω hΩ hcov μA π hI
    (UpperTheory.TP.gInf (UpperTheory.TP.cj E) X).subtype measurable_subtype_coe f hf0 hfc hleft hfr B₁ hB₁ x₀
    (fun y => φ (e.symm (y * cc))) (hform.cont.comp (e.symm.continuous.comp (continuous_mul_right cc)))
    (fun γ hγ h => by
      show φ (e.symm (γ * h * cc)) = φ (e.symm (h * cc))
      rw [mul_assoc, map_mul]
      exact hform.left _ ((he.rat _).1 (by simpa using hγ)) _)
  have hfx : f x₀ = φ ∘ e.symm := funext fun y => by rw [hfa, hj]; rfl
  rw [hfx] at hmain
  have e1 : ∀ x : UpperTheory.TP.gInf (UpperTheory.TP.cj E) X, coef om ν (pure f₀ φf) x.1 * star (UpperTheory.TP.mc M (φ ∘ e.symm) (x.1 * cc)) =
      (c : ℂ)⁻¹ * (B₁ (π x x₀) x₀ * star (pet M.μ M.dom (fun y => φ (e.symm (y * (UpperTheory.TP.gInf (UpperTheory.TP.cj E) X).subtype x * cc))) (φ ∘ e.symm))) := fun x => by
    rw [hco, mul_assoc]
    simp only [UpperTheory.TP.mc, Function.comp_apply, mul_assoc, Subgroup.subtype_apply]
  simp_rw [e1]
  rw [integral_const_mul, hmain, hco1]
  have e2 : UpperTheory.TP.mc M (φ ∘ e.symm) cc = pet M.μ M.dom (fun y => φ (e.symm (y * cc))) (φ ∘ e.symm) := rfl
  rw [e2]
  ring
end
end
