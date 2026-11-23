import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCellStructureData
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectionToTwistedEigenfunctionSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFourierExpansion

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.LocO

open MeasureTheory GlobalTheory.CompanionTheory.TwistedAverage GlobalTheory.CompanionTheory.Rodier

theorem eq_zero_of_eig_of_mem_twKer {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {L : Subgroup G}
    (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) {x : V}
    (hx : x ∈ twKer ρ L θ) (he : ∀ l : L, ρ (l : G) x = (θ l : ℂ) • x) : x = 0 := by
  classical
  obtain ⟨M, hM, hs⟩ := exists_sum_eq_zero hρ hL θ hθ hx
  haveI : M.FiniteIndex := hM
  haveI : M.normalCore.FiniteIndex := inferInstance
  haveI : M.normalCore.Normal := Subgroup.normalCore_normal _
  haveI : Finite (L ⧸ M.normalCore) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (L ⧸ M.normalCore) := Fintype.ofFinite _
  have h0 := hs M.normalCore (Subgroup.normalCore_le M)
  have h1 : ∀ t : L, twOrbit ρ L θ x t = x := fun t => by
    rw [twOrbit, he t, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  simp only [h1, Finset.sum_const, Finset.card_univ] at h0
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact absurd h0 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  · exact h0

theorem isSmooth_cInd {G Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup Z] [Module ℂ Z] (H : Subgroup G) (σ : Representation ℂ H Z) : IsSmooth (cInd H σ) := by
  intro f
  have h : {g : G | cInd H σ g f = f} = {g : G | ind H σ g f.1.1 = f.1.1} := by
    ext g
    exact ⟨fun h => congrArg (fun x : cIndSpace H σ => x.1.1) h, fun h => Subtype.ext (Subtype.ext h)⟩
  rw [h]
  exact f.1.2

def evL {G Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup Z] [Module ℂ Z] (H : Subgroup G) (σ : Representation ℂ H Z) (x : G) : cIndSpace H σ →ₗ[ℂ] Z :=
  (LinearMap.proj x) ∘ₗ (indSpace H σ).subtype ∘ₗ (smoothPart (ind H σ)).subtype ∘ₗ (cIndSpace H σ).subtype

theorem avgVanish_of_fibre {G Z Γ A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup Z] [Module ℂ Z] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsAddHaarMeasure]
    (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (θ : U →* ℂˣ)
    (ρ₁ : Representation ℂ Γ Z) (hρ₁ : IsSmooth ρ₁)
    (C : Subgroup Γ) (hC : IsCompact (C : Set Γ)) (χ : C →* ℂˣ) (hχ : IsOpen (χ.ker : Set C))
    (c : C → H) (hc : ∀ (b : C) (w : Z), σ (c b) w = ρ₁ (b : Γ) w)
    (e : A → G) (he : ∀ a a', e (a + a') = e a * e a')
    (hce : ∀ (b : C) (a : A), ((c b : H) : G) * e a = e a * ((c b : H) : G))
    (y : G) (D : Set A) (hD0 : (0 : A) ∈ D) (hDs : ∀ a a', a ∈ D → a' ∈ D → a - a' ∈ D)
    (hDc : IsCompact D) (hDo : IsOpen D)
    (L : Subgroup G) (hLU : L ≤ U) (hLc : IsCompact (L : Set G))
    (hθ : IsOpen ((θ.comp (Subgroup.inclusion hLU)).ker : Set L))
    (hL1 : ∀ l : L, ∃ (b : C) (a : A), a ∈ D ∧ y * (l : G) * y⁻¹ = ((c b : H) : G) * e a ∧
      θ (Subgroup.inclusion hLU l) = χ b)
    (hL2 : ∀ b : C, ∃ l : L, y * (l : G) * y⁻¹ = ((c b : H) : G) ∧ θ (Subgroup.inclusion hLU l) = χ b)
    (hL3 : ∀ a ∈ D, ∃ l : L, y * (l : G) * y⁻¹ = e a ∧ θ (Subgroup.inclusion hLU l) = 1)
    (hU : ∀ u ∈ U, ∃ h ∈ H, ∃ a : A, y * u * y⁻¹ = h * e a)
    (hfib : ∀ f' : cIndSpace H σ, IsLocallyConstant (fun a => evL H σ (e a * y) f') ∧
      HasCompactSupport (fun a => evL H σ (e a * y) f'))
    (f : cIndSpace H σ) (hsupp : ∀ a, evL H σ (e a * y) f ≠ 0 → a ∈ D)
    (hz : smInt μ (fun a => evL H σ (e a * y) f) ∈ twKer ρ₁ C χ) :
    AvgVanish H σ U θ f y := by
  classical
  have hev : ∀ (x l : G) (f' : cIndSpace H σ), evL H σ x (cInd H σ l f') = evL H σ (x * l) f' := fun _ _ _ => rfl
  have hleft : ∀ (h : H) (x : G) (f' : cIndSpace H σ), evL H σ ((h : G) * x) f' = σ h (evL H σ x f') :=
    fun h x f' => f'.1.1.2 h x
  have he0 : e 0 = 1 := by
    have := he 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  set θL : L →* ℂˣ := θ.comp (Subgroup.inclusion hLU) with hθL
  obtain ⟨ι, _, r, c₀, h1, h2⟩ := GlobalTheory.CompanionTheory.TwAvgInd.exists_finite_average (cInd H σ) (isSmooth_cInd H σ) hLc θL hθ f
  obtain ⟨g, hg⟩ : ∃ g : cIndSpace H σ, g = c₀ • ∑ i, twOrbit (cInd H σ) L θL f (r i) := ⟨_, rfl⟩
  rw [← hg] at h1
  simp only [← hg] at h2

  let T : cIndSpace H σ →ₗ[ℂ] Z :=
    { toFun := fun f' => smInt μ (fun a => evL H σ (e a * y) f')
      map_add' := fun f₁ f₂ => by
        have := SmIntEl.smInt_add μ (hfib f₁).1 (hfib f₁).2 (hfib f₂).1 (hfib f₂).2
        rw [← this]
        congr 1
      map_smul' := fun s f' => by
        have := SmIntEl.smInt_linear μ (s • (LinearMap.id : Z →ₗ[ℂ] Z)) (hfib f').1 (hfib f').2
        simp only [LinearMap.smul_apply, LinearMap.id_apply, RingHom.id_apply] at this ⊢
        rw [← this]
        congr 1 }
  have hTdef : ∀ f', T f' = smInt μ (fun a => evL H σ (e a * y) f') := fun _ => rfl
  have hpoint : ∀ (l : G) (b : C) (a₁ a : A), y * l * y⁻¹ = ((c b : H) : G) * e a₁ →
      e a * y * l = ((c b : H) : G) * (e (a₁ + a) * y) := by
    intro l b a₁ a h
    have h' : y * l = ((c b : H) : G) * e a₁ * y := by rw [← h]; group
    have h2 : e (a₁ + a) = e a * e a₁ := by rw [add_comm, he]
    rw [mul_assoc, h', h2]
    simp only [← mul_assoc]
    rw [← hce b a]
  have hTl : ∀ (l : G) (b : C) (a₁ : A), y * l * y⁻¹ = ((c b : H) : G) * e a₁ → ∀ f',
      T (cInd H σ l f') = ρ₁ (b : Γ) (T f') := by
    intro l b a₁ hl f'
    set φ : A → Z := fun a => evL H σ (e a * y) f' with hφ
    have hfun : (fun a => evL H σ (e a * y) (cInd H σ l f')) = (ρ₁ (b : Γ)) ∘ (φ ∘ (fun a => a₁ + a)) := by
      funext a
      rw [hev, hpoint l b a₁ a hl, hleft, hc]
      rfl
    have hl₂ : IsLocallyConstant (φ ∘ fun a => a₁ + a) := (hfib f').1.comp_continuous (by fun_prop)
    have hc₂ : HasCompactSupport (φ ∘ fun a => a₁ + a) := (hfib f').2.comp_homeomorph (Homeomorph.addLeft a₁)
    rw [hTdef, hfun, SmIntEl.smInt_linear μ _ hl₂ hc₂,
      SmIntEl.smInt_comp_measurePreserving μ (measurePreserving_add_left μ a₁) (hfib f').1]
    rfl
  have hker : ∀ x ∈ twKer (cInd H σ) L θL, T x ∈ twKer ρ₁ C χ := by
    intro x hx
    have hle : twKer (cInd H σ) L θL ≤ (twKer ρ₁ C χ).comap T := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨l, v, rfl⟩
      obtain ⟨b, a, -, h3, h4⟩ := hL1 l
      show T (_ - _) ∈ twKer ρ₁ C χ
      rw [map_sub, map_smul, hTl _ b a h3]
      have : θL l = χ b := h4
      rw [this]
      exact Submodule.subset_span ⟨b, T v, rfl⟩
    exact hle hx
  have hTg : T g ∈ twKer ρ₁ C χ := by
    have : T g = T f - T (f - g) := by rw [map_sub]; abel
    rw [this]
    exact Submodule.sub_mem _ hz (hker _ h1)
  have heig : ∀ b : C, ρ₁ (b : Γ) (T g) = (χ b : ℂ) • T g := by
    intro b
    obtain ⟨l, h3, h4⟩ := hL2 b
    have h5 : y * (l : G) * y⁻¹ = ((c b : H) : G) * e 0 := by rw [he0, mul_one, h3]
    rw [← hTl _ b 0 h5 g, h2 l, map_smul]
    have : θL l = χ b := h4
    rw [this]
  have hTg0 : T g = 0 := eq_zero_of_eig_of_mem_twKer hρ₁ hC χ hχ hTg heig

  have hsg : ∀ a, evL H σ (e a * y) g ≠ 0 → a ∈ D := by
    intro a ha
    by_contra hn
    apply ha
    have hz0 : ∀ i, evL H σ (e a * y) (twOrbit (cInd H σ) L θL f (r i)) = 0 := by
      intro i
      obtain ⟨b, a₁, ha₁, h3, -⟩ := hL1 (r i)
      rw [twOrbit, map_smul, hev, hpoint _ b a₁ a h3, hleft]
      have : evL H σ (e (a₁ + a) * y) f = 0 := by
        by_contra h
        have h6 := hsupp _ h
        apply hn
        have := hDs _ _ h6 ha₁
        rwa [add_sub_cancel_left] at this
      rw [this, map_zero, smul_zero]
    rw [hg, map_smul, map_sum, Finset.sum_eq_zero fun i _ => hz0 i, smul_zero]

  have hper : ∀ a ∈ D, evL H σ (e a * y) g = evL H σ (e 0 * y) g := by
    intro a ha
    obtain ⟨l, h3, h4⟩ := hL3 a ha
    have h5 := congrArg (evL H σ (e 0 * y)) (h2 l)
    rw [hev, map_smul] at h5
    have h6 : e 0 * y * (l : G) = e a * y := by
      rw [he0, one_mul]
      have : y * (l : G) = e a * y := by rw [← h3]; group
      exact this
    rw [h6] at h5
    have h7 : θL l = 1 := h4
    rw [h5, h7]
    simp
  have hφ : (fun a => evL H σ (e a * y) g) = D.indicator fun _ => evL H σ (e 0 * y) g := by
    funext a
    by_cases ha : a ∈ D
    · rw [Set.indicator_of_mem ha, hper a ha]
    · rw [Set.indicator_of_notMem ha]
      by_contra h
      exact ha (hsg a h)
  have hv0 : evL H σ (e 0 * y) g = 0 := by
    have h3 : T g = (((μ D).toReal : ℝ) : ℂ) • evL H σ (e 0 * y) g := by
      rw [hTdef, hφ, SmIntEl.smInt_indicator]
    rw [hTg0] at h3
    have hpos : (μ D).toReal ≠ 0 :=
      (ENNReal.toReal_pos (hDo.measure_pos μ ⟨0, hD0⟩).ne' hDc.measure_lt_top.ne).ne'
    rcases smul_eq_zero.1 h3.symm with h4 | h4
    · exact absurd (Complex.ofReal_eq_zero.1 h4) hpos
    · exact h4
  refine ⟨L, hLU, hLc, g, h1, fun l => h2 l, fun u hu => ?_⟩
  obtain ⟨h, hh, a, hua⟩ := hU u hu
  have h3 : y * u = (h : G) * (e a * y) := by
    have : y * u = (y * u * y⁻¹) * y := by group
    rw [this, hua, mul_assoc]
  show evL H σ (y * u) g = 0
  rw [h3]
  have h4 : evL H σ ((h : G) * (e a * y)) g = σ ⟨h, hh⟩ (evL H σ (e a * y) g) := hleft ⟨h, hh⟩ _ g
  rw [h4]
  have h5 : evL H σ (e a * y) g = 0 := by
    rw [show evL H σ (e a * y) g = _ from congrFun hφ a, hv0]
    simp
  rw [h5, map_zero]

end GlobalTheory.CompanionTheory.BZPhiPG.LocO

end
