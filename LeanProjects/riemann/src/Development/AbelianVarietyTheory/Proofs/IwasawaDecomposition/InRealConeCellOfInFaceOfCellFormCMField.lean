import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyFanFaceCutByIntLinearFormIsCell
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullLinInjective

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark.FaceIn

section Lattice

variable {X : Type} [AddCommGroup X]

theorem inRCone_of_nsmul_eq {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {β : LinearMap.BilinForm ℤ X} {k : ℕ}
    {c : Fin m → ℕ} (hk : 0 < k) (h : k • β = ∑ i, c i • γ i) : InRCone γ β := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨fun i => (c i : ℝ) / k, fun i => by positivity, LinearMap.ext₂ fun a b => ?_⟩
  have h1 : (k : ℤ) * β a b = ∑ i, (c i : ℤ) * γ i a b := by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ h a b
  have h2 : (k : ℝ) * β a b = ∑ i, (c i : ℝ) * γ i a b := by exact_mod_cast h1
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [← mul_right_inj' hk', h2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by field_simp

theorem inRCone_face {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {s : Fin m' ↪ Fin m}
    {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (hcut : IsFaceCut γ s h) {β : LinearMap.BilinForm ℤ X} (hβ : InRCone γ β)
    (h0 : h β = 0) : InRCone (fun j => γ (s j)) β := by
  obtain ⟨c, hc, e⟩ := hβ
  have e1 := apply_eq_of_toReal_eq e h
  rw [h0, Int.cast_zero] at e1
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
    mul_nonneg (hc j) (show (0 : ℝ) ≤ h (γ j) by exact_mod_cast hcut.1 j)).1 e1.symm
  have hc0 : ∀ j, j ∉ Set.range s → c j = 0 := fun j hj => by
    have hne : (h (γ j) : ℝ) ≠ 0 := fun h0 => hj ((hcut.2 j).1 (by exact_mod_cast h0))
    exact (mul_eq_zero.1 (hz j (Finset.mem_univ _))).resolve_right hne
  refine ⟨fun i => c (s i), fun i => hc _, ?_⟩
  rw [e]
  classical
  rw [← Finset.sum_map Finset.univ s (fun j => c j • toReal (γ j))]
  refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
  rw [hc0 j fun ⟨i, hi⟩ => hj (by simp [← hi]), zero_smul]

theorem apply_eq_zero_of_genRank_le {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {s : Fin m' → Fin m}
    {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (h0 : ∀ j, h (γ (s j)) = 0) (hr : genRank γ ≤ genRank fun j => γ (s j))
    (j : Fin m) : h (γ j) = 0 := by
  unfold genRank at hr
  set B := Submodule.span ℤ (Set.range γ) with hB
  set A := Submodule.span ℤ (Set.range fun j => γ (s j)) with hA
  haveI : Module.Finite ℤ B := Module.Finite.span_of_finite ℤ (Set.finite_range γ)
  have hAB : A ≤ B := Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨s j, rfl⟩)
  have hAk : A ≤ LinearMap.ker h := Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact h0 j)
  set K : Submodule ℤ B := LinearMap.ker (h.domRestrict B) with hK
  have h1 : Module.finrank ℤ A ≤ Module.finrank ℤ K := by
    rw [← (Submodule.comapSubtypeEquivOfLe hAB).finrank_eq]
    exact Submodule.finrank_mono fun y hy => hAk hy
  have h2 := Submodule.finrank_quotient_add_finrank K
  have h3 : Module.finrank ℤ (B ⧸ K) = 0 := by omega
  obtain ⟨a, ha, e⟩ := Module.finrank_eq_zero_iff.1 h3
    (Submodule.Quotient.mk ⟨γ j, Submodule.subset_span ⟨j, rfl⟩⟩)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at e
  have e' : a * h (γ j) = 0 := by simpa [hK] using e
  exact (mul_eq_zero.1 e').resolve_left ha

end Lattice

theorem apply_eq_of_inRCone {O : Type} [CommRing O] {ψ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : ψ.LinearOn γ) {N : ℕ}
    {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (h1 : ∀ i, (ℓ (γ i) : ℝ) = N * ψ.evalZ (γ i)) {β : LinearMap.BilinForm ℤ X}
    (hβ : InRCone γ β) : (ℓ β : ℝ) = N * ψ.evalZ β := by
  obtain ⟨c, hc, e⟩ := hβ
  rw [apply_eq_of_toReal_eq e ℓ, ← evalR_toReal, e, (linearOn_iff ψ γ).1 hγ c hc, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [h1]; ring

theorem inRCone_of_add : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (ψ lab : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCarrierDim H.bar q ψ lab → ∀ (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q →
    Dominates H.bar X → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → ∀ β ∈ balForms H.bar X,
    (∀ y, 0 ≤ β y y) → InRCone v β → ∀ x ∈ balForms H.bar X, (∀ y, 0 ≤ x y y) →
    ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x → lab.evalZ (β + x) = lab.evalZ β → InRCone v x := by
  intro E _ _ _ H q ψ lab hψ hlab X _ _ _ _ hX hD m v hv β hβ hβp hvβ x hx hxp hadd hl
  classical
  have hs : β + x ∈ balForms H.bar X := Submodule.add_mem _ hβ hx
  have hsp : ∀ y, 0 ≤ (β + x) y y := fun y => add_nonneg (hβp y) (hxp y)
  have hne : {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ InRCone γ (β + x) ∧
      genRank γ = k}.Nonempty := by
    have hR : toReal (β + x) ∈ psdCone H.bar X := by
      simpa using GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 ![β + x] ![1] (by simp [hs])
        (by simpa using hsp) (by simp)
    obtain ⟨S, -, hcov⟩ := (hψ X hX).finite
    obtain ⟨e, mm, γ, c, hγ, -, hc, hsum⟩ := hcov _ hR
    refine ⟨_, mm, fun i => pull e.symm.toLinearMap (γ i), CarDim.isCell_pull_equiv hγ e.symm, ⟨c, hc, ?_⟩, rfl⟩
    exact LinearMap.ext₂ fun a b => by
      have := LinearMap.congr_fun₂ hsum (e.symm a) (e.symm b)
      simpa [LinearMap.sum_apply] using this
  obtain ⟨n, γ, hγ, hγs, hrk⟩ := Nat.sInf_mem hne
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  obtain ⟨N', ℓ', hN', h1', h2', h3'⟩ := hv.strict
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN'r : (0 : ℝ) < N' := by exact_mod_cast hN'
  have e0 := apply_eq_of_inRCone hγ.linear h1 hγs
  rw [map_add, Int.cast_add, hadd, mul_add] at e0
  have eβ : (N : ℝ) * ψ.evalZ β = ℓ β := by linarith [h2 β hβ hβp, h2 x hx hxp]
  have ex : (N : ℝ) * ψ.evalZ x = ℓ x := by linarith [h2 β hβ hβp, h2 x hx hxp]
  have hγβ : InRCone γ β := by
    obtain ⟨k, c, hk, hc⟩ := h3 β hβ hβp eβ
    exact inRCone_of_nsmul_eq hk hc
  obtain ⟨cx, -, hcx⟩ : InRCone γ x := by
    obtain ⟨k, c, hk, hc⟩ := h3 x hx hxp ex
    exact inRCone_of_nsmul_eq hk hc
  set h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := (N : ℤ) • ℓ' - (N' : ℤ) • ℓ with hh
  have happ : ∀ u, (h u : ℝ) = N * ℓ' u - N' * ℓ u := fun u => by simp [hh]
  let Z : Finset (Fin n) := Finset.univ.filter fun j => h (γ j) = 0
  let s : Fin Z.card ↪ Fin n := (Z.orderEmbOfFin rfl).toEmbedding
  have hcut : IsFaceCut γ s h := by
    refine ⟨fun j => ?_, fun j => ?_⟩
    · have : (0 : ℝ) ≤ h (γ j) := by
        rw [happ, h1]
        have := mul_le_mul_of_nonneg_left (h2' _ (hγ.mem j) (hγ.nonneg j)) hNr.le
        linarith
      exact_mod_cast this
    · have : Set.range s = Z := Z.range_orderEmbOfFin rfl
      rw [this]
      simp [Z]
  have hface := isCell_face_of_isFaceCut E H q ψ hψ X hX hD n γ hγ _ s h hcut
  have hβ0 : h β = 0 := by
    have : (h β : ℝ) = 0 := by
      rw [happ, apply_eq_of_inRCone hv.linear h1' hvβ, ← eβ]; ring
    exact_mod_cast this
  have hle : genRank γ ≤ genRank fun j => γ (s j) := by
    rw [hlab X hX _ hs hsp, hlab X hX _ hβ hβp, Nat.cast_inj] at hl
    rw [hrk, hl]
    exact Nat.sInf_le ⟨_, _, hface, inRCone_face hcut hγβ hβ0, rfl⟩
  have hall := apply_eq_zero_of_genRank_le (h := h) (fun j => (hcut.2 _).2 ⟨j, rfl⟩) hle
  have hx0 : (h x : ℝ) = 0 := by
    rw [apply_eq_of_toReal_eq hcx h]
    simp [hall]
  rw [happ, ← ex] at hx0
  have ex' : (N' : ℝ) * ψ.evalZ x = ℓ' x := by
    have : (N : ℝ) * (N' * ψ.evalZ x - ℓ' x) = 0 := by linarith
    linarith [(mul_eq_zero.1 this).resolve_left hNr.ne']
  obtain ⟨k, c, hk, hc⟩ := h3' x hx hxp ex'
  exact inRCone_of_nsmul_eq hk hc

end GlobalTheory.PolFan.Mark.FaceIn
