import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifRiem
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace SheetDecomposition.Univ.Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

def Tan (_ : RiemLat E g Λ) : Type := Fin g → ℂ

instance (R : RiemLat E g Λ) : AddCommGroup (Tan R) := inferInstanceAs (AddCommGroup (Fin g → ℂ))

instance (R : RiemLat E g Λ) : Module ℂ (Tan R) := inferInstanceAs (Module ℂ (Fin g → ℂ))

instance (R : RiemLat E g Λ) : FiniteDimensional ℂ (Tan R) := inferInstanceAs (FiniteDimensional ℂ (Fin g → ℂ))

theorem ip_conj' (R : RiemLat E g Λ) (x y : Fin g → ℂ) : starRingEnd ℂ (R.ip x y) = R.ip y x := by
  show star (y ⬝ᵥ R.Hm *ᵥ star x) = x ⬝ᵥ R.Hm *ᵥ star y
  rw [← star_dotProduct_star, star_mulVec, star_star, R.herm.eq, dotProduct_mulVec]

theorem ip_add_right' (R : RiemLat E g Λ) (x y y' : Fin g → ℂ) : R.ip x (y + y') = R.ip x y + R.ip x y' := by
  simp [RiemLat.ip, add_dotProduct]

theorem ip_smul_right' (R : RiemLat E g Λ) (c : ℂ) (x y : Fin g → ℂ) : R.ip x (c • y) = c * R.ip x y := by
  simp [RiemLat.ip, smul_dotProduct]

theorem ip_add_left' (R : RiemLat E g Λ) (x x' y : Fin g → ℂ) : R.ip (x + x') y = R.ip x y + R.ip x' y := by
  rw [← ip_conj' R y, ip_add_right', map_add, ip_conj', ip_conj']

theorem ip_smul_left' (R : RiemLat E g Λ) (c : ℂ) (x y : Fin g → ℂ) :
    R.ip (c • x) y = starRingEnd ℂ c * R.ip x y := by
  rw [← ip_conj' R y, ip_smul_right', map_mul, ip_conj']

theorem ip_self_nonneg' (R : RiemLat E g Λ) (x : Fin g → ℂ) : 0 ≤ (R.ip x x).re := by
  by_cases hx : x = 0
  · subst hx
    simp [RiemLat.ip]
  · exact (R.pos x hx).le

theorem ip_self_zero' (R : RiemLat E g Λ) {x : Fin g → ℂ} (h : R.ip x x = 0) : x = 0 := by
  by_contra hx
  have := R.pos x hx
  change 0 < (R.ip x x).re at this
  rw [h] at this
  simp at this

def core (R : RiemLat E g Λ) : InnerProductSpace.Core ℂ (Tan R) where
  inner x y := R.ip x y
  conj_inner_symm x y := ip_conj' R y x
  re_inner_nonneg x := ip_self_nonneg' R x
  add_left x y z := ip_add_left' R x y z
  smul_left x y r := ip_smul_left' R r x y
  definite x h := ip_self_zero' R h

theorem exists_orthoBasis (R : RiemLat E g Λ) (S : Submodule ℂ (Fin g → ℂ)) (m : ℕ)
    (h : Module.finrank ℂ S = m) :
    ∃ e : Fin m → Fin g → ℂ, (∀ c, e c ∈ S) ∧ (∀ a b, R.ip (e a) (e b) = if a = b then 1 else 0) ∧
      S ≤ Submodule.span ℂ (Set.range e) := by
  letI : NormedAddCommGroup (Tan R) := (core R).toNormedAddCommGroup
  letI : InnerProductSpace ℂ (Tan R) := InnerProductSpace.ofCore (core R).toCore
  let S' : Submodule ℂ (Tan R) := S
  have h' : Module.finrank ℂ S' = m := h
  let b := (stdOrthonormalBasis ℂ S').reindex (finCongr h')
  refine ⟨fun c => ((b c : S') : Tan R), fun c => (b c).2, fun x y => ?_, fun x hx => ?_⟩
  · exact orthonormal_iff_ite.1 b.orthonormal x y
  · have hb : Submodule.span ℂ (Set.range b) = ⊤ := by simpa using b.toBasis.span_eq
    have hm := congrArg (Submodule.map S'.subtype) hb
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at hm
    have hx' : x ∈ S' := hx
    rw [← hm] at hx'
    exact hx'

theorem linearIndependent_of_ortho (R : RiemLat E g Λ) {I : Type} [DecidableEq I] (c : I → Fin g → ℂ)
    (h : ∀ i i', R.ip (c i) (c i') = if i = i' then 1 else 0) : LinearIndependent ℂ c := by
  letI : NormedAddCommGroup (Tan R) := (core R).toNormedAddCommGroup
  letI : InnerProductSpace ℂ (Tan R) := InnerProductSpace.ofCore (core R).toCore
  let c' : I → Tan R := c
  have ho : Orthonormal ℂ c' := orthonormal_iff_ite.2 h
  exact ho.linearIndependent

variable {Ψ : Type} [Fintype Ψ]

theorem cm_ne {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) (τ τ' : Ψ) :
    σ τ ≠ (starRingEnd ℂ).comp (σ τ') := fun h =>
  ((hσ.2 (σ τ')).1 ⟨τ', rfl⟩) ⟨τ, h⟩

theorem conj_comp_conj (s : 𝓞 E →+* ℂ) : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s := by
  ext a
  simp

theorem cm_cover {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) (s : 𝓞 E →+* ℂ) :
    (∃ τ, σ τ = s) ∨ ∃ τ, (starRingEnd ℂ).comp (σ τ) = s := by
  by_cases h : ∃ τ, σ τ = s
  · exact Or.inl h
  · right
    have h2 : ∃ τ, σ τ = (starRingEnd ℂ).comp s := by
      by_contra h3
      exact h ((hσ.2 s).2 h3)
    obtain ⟨τ, hτ⟩ := h2
    exact ⟨τ, by rw [hτ, conj_comp_conj]⟩

theorem exists_ortho_frame {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (R₀ : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (hσ : IsCMFam σ) (hs : R₀.HasSig σ j j') :
    ∃ (e : Ix Ψ j j' ≃ Fin g) (c : Ix Ψ j j' → Fin g → ℂ), (∀ i, c i ∈ eigSp R₀.B (emb σ i)) ∧
      ∀ i i', R₀.ip (c i) (c i') = if i = i' then 1 else 0 := by
  obtain ⟨-, -, h3, h4, h5⟩ := SheetDecomposition.riemBasic E g Λ Ψ R₀
  choose f hf1 hf2 hf3 using fun τ => exists_orthoBasis R₀ _ j' (hs τ).1
  choose f' hf1' hf2' hf3' using fun τ => exists_orthoBasis R₀ _ j (hs τ).2
  let c : Ix Ψ j j' → Fin g → ℂ := fun i => Sum.elim (f i.2) (f' i.2) i.1
  have hmem : ∀ i, c i ∈ eigSp R₀.B (emb σ i) := by
    rintro ⟨a | a, τ⟩
    · exact hf1 τ a
    · exact hf1' τ a
  have hinj' : ∀ {τ τ' : Ψ}, τ ≠ τ' → (starRingEnd ℂ).comp (σ τ) ≠ (starRingEnd ℂ).comp (σ τ') := by
    intro τ τ' hne h
    apply hne
    apply hσ.1
    rw [← conj_comp_conj (σ τ), h, conj_comp_conj]
  have hort : ∀ i i', R₀.ip (c i) (c i') = if i = i' then 1 else 0 := by
    rintro ⟨a | a, τ⟩ ⟨b | b, τ'⟩
    · by_cases ht : τ = τ'
      · subst ht
        have := hf2 τ a b
        simpa [c] using this
      · have := h5 _ _ (fun h => ht (hσ.1 h)) _ (hf1 τ a) _ (hf1 τ' b)
        simpa [c, ht] using this
    · have := h5 _ _ (cm_ne hσ τ τ') _ (hf1 τ a) _ (hf1' τ' b)
      simpa [c] using this
    · have := h5 _ _ (cm_ne hσ τ' τ).symm _ (hf1' τ a) _ (hf1 τ' b)
      simpa [c] using this
    · by_cases ht : τ = τ'
      · subst ht
        have := hf2' τ a b
        simpa [c] using this
      · have := h5 _ _ (hinj' ht) _ (hf1' τ a) _ (hf1' τ' b)
        simpa [c, ht] using this
  have hli : LinearIndependent ℂ c := linearIndependent_of_ortho R₀ c hort
  have hsp1 : ∀ τ, eigSp R₀.B (σ τ) ≤ Submodule.span ℂ (Set.range c) := fun τ =>
    (hf3 τ).trans (Submodule.span_mono (by
      rintro _ ⟨a, rfl⟩
      exact ⟨(Sum.inl a, τ), rfl⟩))
  have hsp2 : ∀ τ, eigSp R₀.B ((starRingEnd ℂ).comp (σ τ)) ≤ Submodule.span ℂ (Set.range c) := fun τ =>
    (hf3' τ).trans (Submodule.span_mono (by
      rintro _ ⟨a, rfl⟩
      exact ⟨(Sum.inr a, τ), rfl⟩))
  have hsp : ∀ s : 𝓞 E →+* ℂ, eigSp R₀.B s ≤ Submodule.span ℂ (Set.range c) := by
    intro s
    rcases cm_cover hσ s with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
    · exact hsp1 τ
    · exact hsp2 τ
  have htop : ⊤ ≤ Submodule.span ℂ (Set.range c) := by
    intro x _
    rw [← h4 x]
    exact Submodule.sum_mem _ fun s _ => hsp _ ((h3 _).1 x)
  have hcard : Fintype.card (Ix Ψ j j') = g := by
    have := Module.finrank_eq_card_basis (Module.Basis.mk hli htop)
    simpa using this.symm
  exact ⟨Fintype.equivFinOfCardEq hcard, c, hmem, hort⟩

end SheetDecomposition.Univ.Frame
