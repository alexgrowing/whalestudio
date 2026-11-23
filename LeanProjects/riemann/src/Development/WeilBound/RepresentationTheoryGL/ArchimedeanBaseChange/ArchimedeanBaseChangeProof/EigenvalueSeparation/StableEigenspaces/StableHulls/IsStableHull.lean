import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.E.E3.asm

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem subset_hull {N : ℕ} (S : Set (Sm E N)) : S ⊆ (hull S : Set (Sm E N)) := fun _ hφ =>
  Submodule.mem_sInf.2 fun _ hU => hU.1 hφ

theorem hull_eq_bot {N : ℕ} {S : Set (Sm E N)} (h : ∀ φ ∈ S, φ = 0) : hull S = ⊥ := by
  refine le_bot_iff.1 (sInf_le ⟨fun φ hφ => ?_, ?_⟩)
  · rw [h φ hφ]; exact Submodule.zero_mem _
  · intro o φ hφ
    rw [(Submodule.mem_bot ℂ).1 hφ, map_zero]; exact Submodule.zero_mem _

theorem isStable_hull {N : ℕ} (S : Set (Sm E N)) : IsStable (hull S) := by
  intro o φ hφ
  rw [hull, Submodule.mem_sInf] at hφ ⊢
  exact fun U hU => hU.2 o φ (hφ U hU)

theorem type₁ {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : H E a b → ℂ}
    (hF : SpectralAccumulation.TypeH K₁ K₂ W₁ W₂ F) (y : GA E b) :
    (∀ u ∈ K₁, ∀ x, F (x * finGL E a u, y) = F (x, y)) ∧
      ∀ x, (fun k : Kinf E a => F (x * infGL E a (Unitary.toUnits k), y)) ∈ W₁ := by
  refine ⟨fun u hu x => ?_, fun x => ?_⟩
  · have h := hF.1 u hu 1 K₂.one_mem (x, y)
    simpa using h
  · let L : (Kinf E a × Kinf E b → ℂ) →ₗ[ℂ] (Kinf E a → ℂ) := LinearMap.funLeft ℂ ℂ fun k => (k, 1)
    have hle : Submodule.span ℂ {f | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k : Kinf E a × Kinf E b => w₁ k.1 * w₂ k.2} ≤
        W₁.comap L := by
      rw [Submodule.span_le]
      rintro _ ⟨w₁, hw₁, w₂, hw₂, rfl⟩
      have h : L (fun k : Kinf E a × Kinf E b => w₁ k.1 * w₂ k.2) = w₂ 1 • w₁ := by
        funext k; simp [L, LinearMap.funLeft_apply, mul_comm]
      show L _ ∈ W₁
      rw [h]; exact W₁.smul_mem _ hw₁
    have h := hle (hF.2 (x, y))
    rw [Submodule.mem_comap] at h
    convert h using 1
    funext k
    simp [L, LinearMap.funLeft_apply]

theorem type₂ {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : H E a b → ℂ}
    (hF : SpectralAccumulation.TypeH K₁ K₂ W₁ W₂ F) (y : GA E a) :
    (∀ u ∈ K₂, ∀ x, F (y, x * finGL E b u) = F (y, x)) ∧
      ∀ x, (fun k : Kinf E b => F (y, x * infGL E b (Unitary.toUnits k))) ∈ W₂ := by
  refine ⟨fun u hu x => ?_, fun x => ?_⟩
  · have h := hF.1 1 K₁.one_mem u hu (y, x)
    simpa using h
  · let L : (Kinf E a × Kinf E b → ℂ) →ₗ[ℂ] (Kinf E b → ℂ) := LinearMap.funLeft ℂ ℂ fun k => (1, k)
    have hle : Submodule.span ℂ {f | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k : Kinf E a × Kinf E b => w₁ k.1 * w₂ k.2} ≤
        W₂.comap L := by
      rw [Submodule.span_le]
      rintro _ ⟨w₁, hw₁, w₂, hw₂, rfl⟩
      have h : L (fun k : Kinf E a × Kinf E b => w₁ k.1 * w₂ k.2) = w₁ 1 • w₂ := by
        funext k; simp [L, LinearMap.funLeft_apply]
      show L _ ∈ W₂
      rw [h]; exact W₂.smul_mem _ hw₂
    have h := hle (hF.2 (y, x))
    rw [Submodule.mem_comap] at h
    convert h using 1
    funext k
    simp [L, LinearMap.funLeft_apply]

theorem fd_range₂ {ι : Type} (f : ι → H E a b → ℂ) (i : ι) (h₂ : ∀ i m₁, ∃ φ : Sm E b, φ.1 = fun x => f i (m₁, x))
    (hfd : FiniteDimensional ℂ (Submodule.span ℂ (slices₂ f))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun x y => f i (x, y))) := by
  have hle : Submodule.span ℂ (Set.range fun x y => f i (x, y)) ≤
      (Submodule.span ℂ (slices₂ f)).map (Sm E b).subtype := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    obtain ⟨φ, hφ⟩ := h₂ i x
    exact ⟨φ, Submodule.subset_span (show ∃ j m, φ.1 = fun y => f j (m, y) from ⟨i, x, hφ⟩), hφ⟩
  exact Submodule.finiteDimensional_of_le hle

theorem fd_range₁ {ι : Type} (f : ι → H E a b → ℂ) (i : ι) (h₁ : ∀ i m₂, ∃ φ : Sm E a, φ.1 = fun x => f i (x, m₂))
    (hfd : FiniteDimensional ℂ (Submodule.span ℂ (slices₁ f))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun y x => f i (x, y))) := by
  have hle : Submodule.span ℂ (Set.range fun y x => f i (x, y)) ≤
      (Submodule.span ℂ (slices₁ f)).map (Sm E a).subtype := by
    rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    obtain ⟨φ, hφ⟩ := h₁ i y
    exact ⟨φ, Submodule.subset_span (show ∃ j m, φ.1 = fun x => f j (x, m) from ⟨i, y, hφ⟩), hφ⟩
  exact Submodule.finiteDimensional_of_le hle

theorem centIm {N : ℕ} (hCE : CentEig) (hCR : CentRe) (S : Set (Sm E N)) (m : (E →+* ℂ) → Multiset ℂ)
    (hm : ∀ τ, HasInfCharGL (hull S) τ (m τ)) (hc : ∀ φ ∈ S, Continuous φ.1) (hl : ∀ φ ∈ S, Loc φ.1) :
    SpectralAccumulation.CentIm (hull S) := by
  obtain ⟨z, hz⟩ := hCE E N (hull S) m hm
  by_cases h0 : ∃ φ ∈ S, φ ≠ 0
  · obtain ⟨φ, hφ, hne⟩ := h0
    refine ⟨z, hCR E N φ.1 z (hc φ hφ) (fun h => hne (Subtype.ext h)) (hl φ hφ) (hz φ (subset_hull S hφ)), hz⟩
  · push Not at h0
    refine ⟨0, by simp, fun φ hφ t g => ?_⟩
    rw [hull_eq_bot h0, Submodule.mem_bot] at hφ
    subst hφ
    simp

end PositivityTheory.Rg.BcB.E.E3.asm

namespace PositivityTheory.Rg.BcB.E.E3

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E.E3.asm

theorem asm_holds : Asm := by
  intro hFin hLocSl hLNP hCE hCR hHA hHNP hPS E _ _ _ a b D ι _ M f K₁ K₂ W₁ W₂ m₁ m₂ hK₁ hK₂ hW₁ hW₂ hcont hinv
    hwl2 htype hs₁ hs₂ haut₁ haut₂ hinf₁ hinf₂
  have fd₁ : FiniteDimensional ℂ (Submodule.span ℂ (slices₁ f)) := by
    refine hFin E a K₁ W₁ m₁ (slices₁ f) hK₁ hW₁ (fun φ hφ => ?_) hinf₁
    obtain ⟨i, y, hφ'⟩ := hφ
    obtain ⟨hl, hk⟩ := type₁ (htype i) y
    refine ⟨haut₁ φ ⟨i, y, hφ'⟩, fun u hu x => ?_, fun x => ?_⟩
    · rw [hφ']; exact hl u hu x
    · rw [hφ']; exact hk x
  have fd₂ : FiniteDimensional ℂ (Submodule.span ℂ (slices₂ f)) := by
    refine hFin E b K₂ W₂ m₂ (slices₂ f) hK₂ hW₂ (fun φ hφ => ?_) hinf₂
    obtain ⟨i, y, hφ'⟩ := hφ
    obtain ⟨hl, hk⟩ := type₂ (htype i) y
    refine ⟨haut₂ φ ⟨i, y, hφ'⟩, fun u hu x => ?_, fun x => ?_⟩
    · rw [hφ']; exact hl u hu x
    · rw [hφ']; exact hk x
  have hloc := fun i => hLocSl E a b D M (f i) (hcont i) (fun _ γ x => hinv i γ x) (fun _ => hwl2 i)
  have loc₁ : ∀ φ ∈ slices₁ f, Loc φ.1 := by
    intro φ hφ
    obtain ⟨i, y, hφ'⟩ := hφ
    rw [hφ']; exact (hloc i).1 (fd_range₂ f i hs₂ fd₂) y
  have loc₂ : ∀ φ ∈ slices₂ f, Loc φ.1 := by
    intro φ hφ
    obtain ⟨i, y, hφ'⟩ := hφ
    rw [hφ']; exact (hloc i).2 (fd_range₁ f i hs₁ fd₁) y
  have cont₁ : ∀ φ ∈ slices₁ f, Continuous φ.1 := by
    intro φ hφ
    obtain ⟨i, y, hφ'⟩ := hφ
    rw [hφ']; have := hcont i; fun_prop
  have cont₂ : ∀ φ ∈ slices₂ f, Continuous φ.1 := by
    intro φ hφ
    obtain ⟨i, y, hφ'⟩ := hφ
    rw [hφ']; have := hcont i; fun_prop
  have ha₁ := hHA E a (slices₁ f) haut₁
  have ha₂ := hHA E b (slices₂ f) haut₂
  have inf₁ : ∀ τ, HasInfCharGL (hull (slices₁ f)) τ (m₁ τ) := fun τ => ha₁.2 τ (m₁ τ) (hinf₁ τ)
  have inf₂ : ∀ τ, HasInfCharGL (hull (slices₂ f)) τ (m₂ τ) := fun τ => ha₂.2 τ (m₂ τ) (hinf₂ τ)
  refine ⟨isStable_hull _, isStable_hull _, ha₁.1, ha₂.1,
    hHNP E a (slices₁ f) fun φ hφ => ⟨haut₁ φ hφ, hLNP E a φ (haut₁ φ hφ) (loc₁ φ hφ)⟩,
    hHNP E b (slices₂ f) fun φ hφ => ⟨haut₂ φ hφ, hLNP E b φ (haut₂ φ hφ) (loc₂ φ hφ)⟩,
    centIm hCE hCR _ m₁ inf₁ cont₁ loc₁, centIm hCE hCR _ m₂ inf₂ cont₂ loc₂, inf₁, inf₂, fun i => ?_⟩
  refine hPS E a b (f i) _ _ (fun y => ?_) (fun x => ?_) (fd_range₁ f i hs₁ fd₁)
  · obtain ⟨φ, hφ⟩ := hs₁ i y
    exact ⟨φ, subset_hull _ ⟨i, y, hφ⟩, hφ⟩
  · obtain ⟨ψ, hψ⟩ := hs₂ i x
    exact ⟨ψ, subset_hull _ ⟨i, x, hψ⟩, hψ⟩

end PositivityTheory.Rg.BcB.E.E3

end
