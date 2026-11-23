import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectionToTwistedEigenfunctionSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveIntertwinerQuotientEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveIntertwinerSubrepEquiv

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Glue

open GlobalTheory.CompanionTheory.TwistedAverage GlobalTheory.CompanionTheory.PRep.JacExact

section Eig

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] [TopologicalSpace G] [IsTopologicalGroup G]

theorem eq_zero_of_mem_twKer_of_eig (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) {L : Subgroup G}
    (hL : IsCompact (L : Set G)) (χ : L →* ℂˣ) (hχ : IsOpen (χ.ker : Set L)) (e : V)
    (he : e ∈ twKer ρ L χ) (hev : ∀ l : L, ρ (l : G) e = ((χ l : ℂˣ) : ℂ) • e) : e = 0 := by
  classical
  obtain ⟨s, t, hst⟩ := exists_finite_support ρ L χ e he
  haveI : CompactSpace L := isCompact_iff_compactSpace.1 hL
  obtain ⟨M, hMo, hMχ, -, hMt⟩ := exists_open_fixing ρ ρ hρ hρ L χ.ker hχ e t
  haveI : Finite (L ⧸ M) := Subgroup.quotient_finite_of_isOpen M hMo
  haveI : M.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let C : Subgroup L := M.normalCore
  haveI : C.Normal := Subgroup.normalCore_normal M
  haveI : C.FiniteIndex := inferInstance
  haveI : Finite (L ⧸ C) := inferInstance
  letI := Fintype.ofFinite (L ⧸ C)
  have hCM : C ≤ M := Subgroup.normalCore_le M
  let τ : Representation ℂ L V := ρ.comp L.subtype
  have h0 : avg τ χ C e = 0 := by
    have hle : Submodule.span ℂ {y | ∃ n ∈ s, ∃ w ∈ t, y = ρ (n : G) w - ((χ n : ℂˣ) : ℂ) • w} ≤
        LinearMap.ker (avg τ χ C) := by
      refine Submodule.span_le.2 ?_
      rintro y ⟨n, -, w, hw, rfl⟩
      show avg τ χ C (τ n w - ((χ n : ℂˣ) : ℂ) • w) = 0
      rw [map_sub, avg_translate τ χ C (hCM.trans hMχ) w (fun m hm => hMt w hw m (hCM hm)) n, map_smul,
        sub_self]
    exact hle hst
  have h1 : avg τ χ C e = ((Fintype.card (L ⧸ C) : ℕ) : ℂ) • e := by
    have h2 : ∀ q : L ⧸ C, (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • τ (Quotient.out q) e = e := by
      intro q
      show (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • ρ ((Quotient.out q : L) : G) e = e
      rw [hev, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    rw [avg_apply, Finset.sum_congr rfl fun q _ => h2 q]
    simp [Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hc : ((Fintype.card (L ⧸ C) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [h0] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_left hc

theorem twKer_mono (ρ : Representation ℂ G V) {U L₁ L₂ : Subgroup G} (θ : U →* ℂˣ) (h₁ : L₁ ≤ U) (h₂ : L₂ ≤ U)
    (h : L₁ ≤ L₂) :
    twKer ρ L₁ (θ.comp (Subgroup.inclusion h₁)) ≤ twKer ρ L₂ (θ.comp (Subgroup.inclusion h₂)) := by
  refine Submodule.span_mono ?_
  rintro _ ⟨n, v, rfl⟩
  exact ⟨⟨n, h n.2⟩, v, rfl⟩

theorem twKer_le (ρ : Representation ℂ G V) {U L : Subgroup G} (θ : U →* ℂˣ) (h : L ≤ U) :
    twKer ρ L (θ.comp (Subgroup.inclusion h)) ≤ twKer ρ U θ := by
  refine Submodule.span_mono ?_
  rintro _ ⟨n, v, rfl⟩
  exact ⟨⟨n, h n.2⟩, v, rfl⟩

theorem isOpen_ker_comp {U L : Subgroup G} (θ : U →* ℂˣ) (hθ : IsOpen (θ.ker : Set U)) (h : L ≤ U) :
    IsOpen ((θ.comp (Subgroup.inclusion h)).ker : Set L) := by
  have e : ((θ.comp (Subgroup.inclusion h)).ker : Set L) = Subgroup.inclusion h ⁻¹' (θ.ker : Set U) := by
    ext l
    simp [MonoidHom.mem_ker]
  rw [e]
  exact hθ.preimage (Continuous.subtype_mk continuous_subtype_val _)

end Eig

theorem exists_factor {Y V A : Type} [AddCommGroup Y] [Module ℂ Y] [AddCommGroup V] [Module ℂ V] [AddCommGroup A]
    [Module ℂ A] (j : V →ₗ[ℂ] A) (hj : Function.Injective j) (E : Y →ₗ[ℂ] A) (h : ∀ y, ∃ v, j v = E y) :
    ∃ Φ : Y →ₗ[ℂ] V, ∀ y, j (Φ y) = E y := by
  let E' : Y →ₗ[ℂ] LinearMap.range j := E.codRestrict _ fun y => by
    obtain ⟨v, hv⟩ := h y
    exact ⟨v, hv⟩
  refine ⟨(LinearEquiv.ofInjective j hj).symm.toLinearMap ∘ₗ E', fun y => ?_⟩
  have := (LinearEquiv.ofInjective j hj).apply_symm_apply (E' y)
  exact congrArg Subtype.val this

theorem extension_of_maps {M Y VC VO AC AO : Type} [Group M] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup VC] [Module ℂ VC]
    [AddCommGroup VO] [Module ℂ VO] [AddCommGroup AC] [Module ℂ AC] [AddCommGroup AO] [Module ℂ AO]
    (ρ : Representation ℂ M Y) (πC : Representation ℂ M VC) (πO : Representation ℂ M VO)
    (aC : Representation ℂ M AC) (aO : Representation ℂ M AO)
    (jC : VC →ₗ[ℂ] AC) (jO : VO →ₗ[ℂ] AO) (hjC : Function.Injective jC) (hjO : Function.Injective jO)
    (hjCe : ∀ m v, jC (πC m v) = aC m (jC v)) (hjOe : ∀ m v, jO (πO m v) = aO m (jO v))
    (EC : Y →ₗ[ℂ] AC) (EO : Y →ₗ[ℂ] AO)
    (ECi : ∀ m y, EC (ρ m y) = aC m (EC y)) (EOi : ∀ m y, EO (ρ m y) = aO m (EO y))
    (hCmem : ∀ y, ∃ v, jC v = EC y) (hConto : ∀ v, ∃ y, EC y = jC v)
    (h1 : ∀ y, EC y = 0 → ∃ v, jO v = EO y) (h2 : ∀ y, EC y = 0 → EO y = 0 → y = 0)
    (h3 : ∀ v, ∃ y, EC y = 0 ∧ EO y = jO v) :
    ∃ S : Subrepresentation ρ, Nonempty ((subQuot S ⊥).Equiv πO) ∧ Nonempty ((subQuot ⊤ S).Equiv πC) := by
  obtain ⟨ΦC, hΦC⟩ := exists_factor jC hjC EC hCmem
  let R : ρ.IntertwiningMap πC := ⟨ΦC, fun m => LinearMap.ext fun y => by
    apply hjC
    show jC (ΦC (ρ m y)) = jC (πC m (ΦC y))
    rw [hΦC, hjCe, hΦC, ECi]⟩
  have hRs : Function.Surjective R := fun v => by
    obtain ⟨y, hy⟩ := hConto v
    refine ⟨y, hjC ?_⟩
    show jC (ΦC y) = jC v
    rw [hΦC, hy]
  obtain ⟨S, hS, hq⟩ := GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv ρ πC R hRs
  have memS : ∀ y, y ∈ S.toSubmodule ↔ EC y = 0 := by
    intro y
    rw [hS, LinearMap.mem_ker]
    constructor
    · intro h
      have h' : ΦC y = 0 := h
      rw [← hΦC, h', map_zero]
    · intro h
      refine hjC ?_
      show jC (ΦC y) = jC 0
      rw [hΦC, h, map_zero]
  obtain ⟨Ψ, hΨ⟩ := exists_factor jO hjO (EO ∘ₗ S.toSubmodule.subtype)
    (fun y => h1 y.1 ((memS _).1 y.2))
  refine ⟨S, GlobalTheory.CompanionTheory.BZRes.subQuot_bot_equiv_of_bijective ρ πO S Ψ ⟨?_, ?_⟩ ?_, hq⟩
  · rw [injective_iff_map_eq_zero]
    rintro ⟨y, hy⟩ h0
    have hO : EO y = 0 := by
      have := hΨ ⟨y, hy⟩
      rw [h0, map_zero] at this
      exact this.symm
    exact Subtype.ext (h2 y ((memS _).1 hy) hO)
  · intro v
    obtain ⟨y, hy, he⟩ := h3 v
    refine ⟨⟨y, (memS _).2 hy⟩, hjO ?_⟩
    rw [hΨ]
    exact he
  · intro m v
    apply hjO
    rw [hΨ, hjOe, hΨ]
    exact EOi m v.1

section Glue

variable {G Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup Z] [Module ℂ Z]

def evC (H : Subgroup G) (σ : Representation ℂ H Z) (x : G) : cIndSpace H σ →ₗ[ℂ] Z :=
  GlobalTheory.CompanionTheory.TwAvgInd.evalAt H σ x ∘ₗ (cIndSpace H σ).subtype

theorem exists_avg (H : Subgroup G) (σ : Representation ℂ H Z) {L : Subgroup G} (hL : IsCompact (L : Set G))
    (χ : L →* ℂˣ) (hχ : IsOpen (χ.ker : Set L)) (f : cIndSpace H σ) :
    ∃ f' : cIndSpace H σ, f - f' ∈ twKer (cInd H σ) L χ ∧
      (∀ x, f'.1.1.1 x ≠ 0 → ∃ l ∈ L, f.1.1.1 (x * l) ≠ 0) ∧
      ∀ l : L, cInd H σ (l : G) f' = ((χ l : ℂˣ) : ℂ) • f' := by
  obtain ⟨ι, _, r, c, h1, h2⟩ :=
    GlobalTheory.CompanionTheory.TwAvgInd.exists_finite_average (cInd H σ) (GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd H σ) hL χ hχ f
  refine ⟨_, h1, ?_, h2⟩
  intro x hx
  by_contra hcon
  push_neg at hcon
  apply hx
  have hz : ∀ i, evC H σ x (twOrbit (cInd H σ) L χ f (r i)) = 0 := by
    intro i
    have : evC H σ x (cInd H σ ((r i : L) : G) f) = 0 := hcon _ (r i).2
    simp only [twOrbit, map_smul, this, smul_zero]
  have : evC H σ x (c • ∑ i, twOrbit (cInd H σ) L χ f (r i)) = 0 := by
    rw [map_smul, map_sum, Finset.sum_eq_zero fun i _ => hz i, smul_zero]
  exact this

def Good (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (θ : U →* ℂˣ) (f : cIndSpace H σ)
    (A : Set G) : Prop :=
  ∃ L : Subgroup G, L ≤ U ∧ IsCompact (L : Set G) ∧
    ∀ (L' : Subgroup G) (hL' : L' ≤ U), IsCompact (L' : Set G) → L ≤ L' →
      ∀ g : cIndSpace H σ, f - g ∈ twKer (cInd H σ) L' (θ.comp (Subgroup.inclusion hL')) →
        (∀ l : L', cInd H σ (l : G) g = ((θ (Subgroup.inclusion hL' l) : ℂˣ) : ℂ) • g) →
        ∀ x ∈ A, g.1.1.1 x = 0

theorem good_nhds (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (hUn : U.Normal) (θ : U →* ℂˣ)
    (hθ : IsOpen (θ.ker : Set U)) (f : cIndSpace H σ) (p : G) (hp : AvgVanish H σ U θ f p) :
    ∃ t ∈ 𝓝 p, Good H σ U θ f t := by
  obtain ⟨L, hL, hLc, gp, h1, -, h3⟩ := hp
  have hK : IsOpen {k : G | cInd H σ k gp = gp} := GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd H σ gp
  have hop : IsOpen ((fun x => p⁻¹ * x) ⁻¹' {k : G | cInd H σ k gp = gp}) :=
    hK.preimage (by fun_prop)
  refine ⟨_, hop.mem_nhds (by simp), L, hL, hLc, fun L' hL' hL'c hLL' g hg hge ω hω => ?_⟩
  by_contra hne
  obtain ⟨h', a1, a2, a3⟩ := exists_avg H σ hL'c (θ.comp (Subgroup.inclusion hL'))
    (isOpen_ker_comp θ hθ hL') gp
  have hgh : g - h' = 0 := by
    refine eq_zero_of_mem_twKer_of_eig (cInd H σ) (GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd H σ) hL'c _
      (isOpen_ker_comp θ hθ hL') _ ?_ ?_
    · have e : g - h' = (f - gp) + (gp - h') - (f - g) := by abel
      rw [e]
      exact Submodule.sub_mem _ (Submodule.add_mem _ (twKer_mono _ θ hL hL' hLL' h1) a1) hg
    · intro l
      rw [map_sub, hge l, a3 l, smul_sub]
      rfl
  obtain rfl : g = h' := sub_eq_zero.1 hgh
  obtain ⟨l, hl, hne'⟩ := a2 ω hne
  apply hne'
  set k : G := p⁻¹ * ω with hk
  have hkK : cInd H σ k gp = gp := hω
  have hu : k * l * k⁻¹ ∈ U := hUn.conj_mem l (hL' hl) k
  have e1 : ω * l = p * (k * l * k⁻¹) * k := by
    rw [hk]; group
  have e2 : gp.1.1.1 (p * (k * l * k⁻¹) * k) = (cInd H σ k gp).1.1.1 (p * (k * l * k⁻¹)) := rfl
  rw [e1, e2, hkK]
  exact h3 _ hu

theorem glue (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (hUn : U.Normal) (θ : U →* ℂˣ)
    (hθ : IsOpen (θ.ker : Set U))
    (hdir : ∀ L₁ L₂ : Subgroup G, L₁ ≤ U → L₂ ≤ U → IsCompact (L₁ : Set G) → IsCompact (L₂ : Set G) →
      ∃ L : Subgroup G, L ≤ U ∧ IsCompact (L : Set G) ∧ L₁ ≤ L ∧ L₂ ≤ L)
    (S : Set G) (hS : IsClosed S) (hHS : ∀ h ∈ H, ∀ x ∈ S, h * x ∈ S) (hSU : ∀ x ∈ S, ∀ u ∈ U, x * u ∈ S)
    (f : cIndSpace H σ) (hf : ∀ p ∈ S, AvgVanish H σ U θ f p) :
    ∃ g : cIndSpace H σ, f - g ∈ twKer (cInd H σ) U θ ∧ ∀ x ∈ S, g.1.1.1 x = 0 := by
  obtain ⟨Ω₀, hΩ₀, hsupp⟩ := f.2
  have hΩ : IsCompact (Ω₀ ∩ S) := hΩ₀.inter_right hS
  have hG : Good H σ U θ f (Ω₀ ∩ S) := by
    refine hΩ.induction_on (p := Good H σ U θ f) ?_ ?_ ?_ ?_
    · refine ⟨⊥, bot_le, ?_, fun _ _ _ _ _ _ _ x hx => hx.elim⟩
      rw [Subgroup.coe_bot]
      exact isCompact_singleton
    · rintro A B hAB ⟨L, hL, hLc, h⟩
      exact ⟨L, hL, hLc, fun L' hL' c hl g a b x hx => h L' hL' c hl g a b x (hAB hx)⟩
    · rintro A B ⟨L₁, h₁, c₁, a₁⟩ ⟨L₂, h₂, c₂, a₂⟩
      obtain ⟨L, hL, hLc, l₁, l₂⟩ := hdir L₁ L₂ h₁ h₂ c₁ c₂
      refine ⟨L, hL, hLc, fun L' hL' c hl g a b x hx => ?_⟩
      rcases hx with hx | hx
      · exact a₁ L' hL' c (l₁.trans hl) g a b x hx
      · exact a₂ L' hL' c (l₂.trans hl) g a b x hx
    · intro x hx
      obtain ⟨t, ht, hg⟩ := good_nhds H σ U hUn θ hθ f x (hf x hx.2)
      exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, hg⟩
  obtain ⟨L, hL, hLc, hgood⟩ := hG
  obtain ⟨g, h1, h2, h3⟩ := exists_avg H σ hLc (θ.comp (Subgroup.inclusion hL)) (isOpen_ker_comp θ hθ hL) f
  refine ⟨g, twKer_le _ θ hL h1, fun x hx => ?_⟩
  by_contra hne
  obtain ⟨l, hl, hfl⟩ := h2 x hne
  obtain ⟨h, hh, ω, hω, e⟩ := hsupp (x * l) hfl
  have hωS : ω ∈ S := by
    have : ω = h⁻¹ * (x * l) := by rw [e]; group
    rw [this]
    exact hHS _ (inv_mem hh) _ (hSU x hx l (hL hl))
  have hz : g.1.1.1 ω = 0 := hgood L hL hLc le_rfl g h1 h3 ω ⟨hω, hωS⟩
  have hxl : g.1.1.1 (x * l) = 0 := by
    have e4 : g.1.1.1 (((⟨h, hh⟩ : H) : G) * ω) = σ ⟨h, hh⟩ (g.1.1.1 ω) := g.1.1.2 ⟨h, hh⟩ ω
    rw [e]
    rw [show g.1.1.1 (h * ω) = _ from e4, hz, map_zero]
  have e5 : g.1.1.1 (x * l) = (cInd H σ ((⟨l, hl⟩ : L) : G) g).1.1.1 x := rfl
  rw [e5, h3 ⟨l, hl⟩] at hxl
  have e7 : ((θ.comp (Subgroup.inclusion hL) ⟨l, hl⟩ : ℂˣ) : ℂ) • g.1.1.1 x = 0 := hxl
  exact hne ((smul_eq_zero.1 e7).resolve_left (Units.ne_zero _))

end Glue

theorem extension {G M Z VC VO AC AO : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
    [AddCommGroup Z] [Module ℂ Z] [AddCommGroup VC] [Module ℂ VC] [AddCommGroup VO] [Module ℂ VO]
    [AddCommGroup AC] [Module ℂ AC] [AddCommGroup AO] [Module ℂ AO]
    (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (hUn : U.Normal) (θ : U →* ℂˣ)
    (hθ : IsOpen (θ.ker : Set U))
    (hdir : ∀ L₁ L₂ : Subgroup G, L₁ ≤ U → L₂ ≤ U → IsCompact (L₁ : Set G) → IsCompact (L₂ : Set G) →
      ∃ L : Subgroup G, L ≤ U ∧ IsCompact (L : Set G) ∧ L₁ ≤ L ∧ L₂ ≤ L)
    (s : M →* G) (c : M →* ℂˣ) (ρ : Representation ℂ M (TwJacquet (cInd H σ) U θ))
    (hρ : ∀ (m : M) (f : cIndSpace H σ), ρ m (Submodule.Quotient.mk f) =
      ((c m : ℂˣ) : ℂ) • Submodule.Quotient.mk (cInd H σ (s m) f))
    (C : Set G) (hCc : IsClosed C) (hHC : ∀ h ∈ H, ∀ x ∈ C, h * x ∈ C) (hCU : ∀ x ∈ C, ∀ u ∈ U, x * u ∈ C)
    (πC : Representation ℂ M VC) (πO : Representation ℂ M VO)
    (aC : Representation ℂ M AC) (aO : Representation ℂ M AO)
    (jC : VC →ₗ[ℂ] AC) (jO : VO →ₗ[ℂ] AO) (hjC : Function.Injective jC) (hjO : Function.Injective jO)
    (hjCe : ∀ m v, jC (πC m v) = aC m (jC v)) (hjOe : ∀ m v, jO (πO m v) = aO m (jO v))
    (eC : cIndSpace H σ →ₗ[ℂ] AC) (eO : cIndSpace H σ →ₗ[ℂ] AO)
    (hC1 : ∀ (u : U) f, eC (cInd H σ (u : G) f) = ((θ u : ℂˣ) : ℂ) • eC f)
    (hO1 : ∀ (u : U) f, eO (cInd H σ (u : G) f) = ((θ u : ℂˣ) : ℂ) • eO f)
    (hCs : ∀ m f, aC m (eC f) = ((c m : ℂˣ) : ℂ) • eC (cInd H σ (s m) f))
    (hOs : ∀ m f, aO m (eO f) = ((c m : ℂˣ) : ℂ) • eO (cInd H σ (s m) f))
    (hCmem : ∀ f, ∃ v, jC v = eC f)
    (hOmem : ∀ f : cIndSpace H σ, (∀ x ∈ C, (f : smoothPart (ind H σ)).1.1 x = 0) → ∃ v, jO v = eO f)
    (hConto : ∀ v, ∃ f, eC f = jC v)
    (hOonto : ∀ v, ∃ f : cIndSpace H σ, (∀ x ∈ C, (f : smoothPart (ind H σ)).1.1 x = 0) ∧ eO f = jO v)
    (hCoff : ∀ f : cIndSpace H σ, (∀ x ∈ C, (f : smoothPart (ind H σ)).1.1 x = 0) → eC f = 0)
    (hlocC : ∀ f, eC f = 0 → ∀ p ∈ C, AvgVanish H σ U θ f p)
    (hlocO : ∀ f, eO f = 0 → ∀ p, p ∉ C → AvgVanish H σ U θ f p) :
    ∃ S : Subrepresentation ρ, Nonempty ((subQuot S ⊥).Equiv πO) ∧ Nonempty ((subQuot ⊤ S).Equiv πC) := by
  have kC : twKer (cInd H σ) U θ ≤ LinearMap.ker eC := Submodule.span_le.2 (by
    rintro _ ⟨u, v, rfl⟩
    show eC _ = 0
    rw [map_sub, hC1, map_smul, sub_self])
  have kO : twKer (cInd H σ) U θ ≤ LinearMap.ker eO := Submodule.span_le.2 (by
    rintro _ ⟨u, v, rfl⟩
    show eO _ = 0
    rw [map_sub, hO1, map_smul, sub_self])
  have ECmk : ∀ f, (twKer (cInd H σ) U θ).liftQ eC kC (Submodule.Quotient.mk f) = eC f := fun f => rfl
  have EOmk : ∀ f, (twKer (cInd H σ) U θ).liftQ eO kO (Submodule.Quotient.mk f) = eO f := fun f => rfl
  refine Glue.extension_of_maps ρ πC πO aC aO jC jO hjC hjO hjCe hjOe
    ((twKer (cInd H σ) U θ).liftQ eC kC) ((twKer (cInd H σ) U θ).liftQ eO kO) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro m y
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [hρ, map_smul, ECmk, ECmk, hCs]
  · intro m y
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [hρ, map_smul, EOmk, EOmk, hOs]
  · intro y
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact hCmem f
  · intro v
    obtain ⟨f, hf⟩ := hConto v
    exact ⟨Submodule.Quotient.mk f, hf⟩
  · intro y hy
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨g, hg, hv⟩ := Glue.glue H σ U hUn θ hθ hdir C hCc hHC hCU f (hlocC f hy)
    have e : (Submodule.Quotient.mk f : TwJacquet (cInd H σ) U θ) = Submodule.Quotient.mk g :=
      (Submodule.Quotient.eq _).2 hg
    obtain ⟨v, hv'⟩ := hOmem g hv
    exact ⟨v, by rw [e, EOmk, hv']⟩
  · intro y hyC hyO
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨g, hg, hv⟩ := Glue.glue H σ U hUn θ hθ hdir Set.univ isClosed_univ (fun _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial) f (fun p _ => by
        by_cases hp : p ∈ C
        · exact hlocC f hyC p hp
        · exact hlocO f hyO p hp)
    have hg0 : g = 0 := Subtype.ext (Subtype.ext (Subtype.ext (funext fun x => hv x trivial)))
    rw [hg0, sub_zero] at hg
    exact (Submodule.Quotient.mk_eq_zero _).2 hg
  · intro v
    obtain ⟨f, hf, he⟩ := hOonto v
    exact ⟨Submodule.Quotient.mk f, hCoff f hf, he⟩

end GlobalTheory.CompanionTheory.BZPhiPG.Glue
