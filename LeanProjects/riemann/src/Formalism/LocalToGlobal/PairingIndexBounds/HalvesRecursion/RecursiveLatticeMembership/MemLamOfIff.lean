import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.Statement
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Principal
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Rec

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

theorem eisG_eq_G (Λ : AddSubgroup ℂ) (L : PeriodPair) (h : ∀ w : ℂ, w ∈ Λ ↔ w ∈ L.lattice) (k : ℕ)
    (hk : 0 < k) : eisG Λ k = L.G (2 * k) := by
  unfold eisG PeriodPair.G
  have h1 := tsum_subtype ({w : ℂ | w ∈ Λ ∧ w ≠ 0} : Set ℂ) (fun z : ℂ => 1 / z ^ (2 * k))
  have h2 := tsum_subtype ((L.lattice : Set ℂ)) (fun z : ℂ => (z ^ (2 * k))⁻¹)
  refine h1.trans (Eq.trans ?_ h2.symm)
  congr 1
  funext w
  by_cases hw : w = 0
  · subst hw
    have : (0 : ℂ) ^ (2 * k) = 0 := zero_pow (by omega)
    simp [Set.indicator, this]
  · have hiff : w ∈ ({w : ℂ | w ∈ Λ ∧ w ≠ 0} : Set ℂ) ↔ w ∈ (L.lattice : Set ℂ) :=
      ⟨fun hh => (h w).1 hh.1, fun hh => ⟨(h w).2 hh, hw⟩⟩
    by_cases hm : w ∈ (L.lattice : Set ℂ)
    · rw [Set.indicator_of_mem (hiff.2 hm), Set.indicator_of_mem hm, one_div]
    · rw [Set.indicator_of_notMem (fun hh => hm (hiff.1 hh)), Set.indicator_of_notMem hm]

variable (D : D7)

def psi : 𝓞 D.host.K →+ ℂ where
  toFun c := D.host.φ₀ (((c : D.host.K) : D.host.E))
  map_zero' := by simp
  map_add' a b := by simp

theorem mem_lamOf_iff (cc : Ideal (𝓞 D.host.K)) (w : ℂ) :
    w ∈ lamOf D cc 1 ↔ ∃ c ∈ cc, psi D c = w := by
  constructor
  · intro hw
    induction hw using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨c, hc, by simp [psi]⟩
    | zero => exact ⟨0, cc.zero_mem, by simp⟩
    | add x y _ _ h1 h2 =>
      obtain ⟨c1, hc1, rfl⟩ := h1
      obtain ⟨c2, hc2, rfl⟩ := h2
      exact ⟨c1 + c2, cc.add_mem hc1 hc2, by simp⟩
    | neg x _ h1 =>
      obtain ⟨c1, hc1, rfl⟩ := h1
      exact ⟨-c1, cc.neg_mem hc1, by simp⟩
  · rintro ⟨c, hc, rfl⟩
    exact AddSubgroup.subset_closure ⟨c, hc, by simp [psi]⟩

theorem exists_sqrt : ∃ β : 𝓞 D.host.K,
    D.host.φ₀ (((β : D.host.K) : D.host.E)) = Complex.I * (Real.sqrt D.host.d : ℂ) := by
  have hsq : D.host.sqd ^ 2 = -(D.host.d : D.host.E) :=
    Formalism.BasicNotions.Examples₂.bE_sq D.host
  have hmem : D.host.sqd ∈ D.host.K :=
    IntermediateField.mem_adjoin_simple_self ℚ _
  set s : D.host.K := ⟨_, hmem⟩ with hs_def
  have hs : s ^ 2 = -(D.host.d : D.host.K) := by apply Subtype.ext; push_cast; exact hsq
  have hint : IsIntegral ℤ s := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [hs]
    have := isIntegral_algebraMap (R := ℤ) (A := D.host.K) (x := -(D.host.d : ℤ))
    simpa using this
  refine ⟨⟨s, hint⟩, ?_⟩
  exact D.host.φ₀_mem

theorem finrank_K : Module.finrank ℚ D.host.K = 2 :=
  Formalism.FrobeniusOrbits.SplitK.finrank_K (L := D.host.E) (b := D.host.sqd)
    D.host.hyp.2.1.pos (Formalism.BasicNotions.Examples₂.bE_sq D.host)

theorem exists_basis (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) : Nonempty (Module.Basis (Fin 2) ℤ cc) := by
  have e := Ideal.selfBasis (RingOfIntegers.basis D.host.K) cc hcc
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.K)) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, finrank_K]
  exact ⟨e.reindex (Fintype.equivFinOfCardEq hcard)⟩

theorem exists_pp (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) :
    ∃ L : PeriodPair, ∀ w : ℂ, w ∈ lamOf D cc 1 ↔ w ∈ L.lattice := by
  obtain ⟨e⟩ := exists_basis D cc hcc
  set ω₁ := psi D (e 0 : 𝓞 D.host.K)
  set ω₂ := psi D (e 1 : 𝓞 D.host.K)

  have hcomb : ∀ c ∈ cc, ∃ m n : ℤ, (m : ℂ) * ω₁ + (n : ℂ) * ω₂ = psi D c := by
    intro c hc
    have hx := e.sum_repr ⟨c, hc⟩
    refine ⟨e.repr ⟨c, hc⟩ 0, e.repr ⟨c, hc⟩ 1, ?_⟩
    rw [Fin.sum_univ_two] at hx
    have hx' := congrArg (fun y : cc => psi D (y : 𝓞 D.host.K)) hx
    simp only [Submodule.coe_add, map_add] at hx'
    rw [← hx']
    rw [Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower, map_zsmul, map_zsmul, zsmul_eq_mul,
      zsmul_eq_mul]
  have hback : ∀ m n : ℤ, ∃ c ∈ cc, psi D c = (m : ℂ) * ω₁ + (n : ℂ) * ω₂ := by
    intro m n
    refine ⟨m • (e 0 : 𝓞 D.host.K) + n • (e 1 : 𝓞 D.host.K),
      cc.add_mem (Submodule.smul_of_tower_mem _ m (e 0).2) (Submodule.smul_of_tower_mem _ n (e 1).2), ?_⟩
    rw [map_add, map_zsmul, map_zsmul, zsmul_eq_mul, zsmul_eq_mul]

  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcc
  obtain ⟨β, hβ⟩ := exists_sqrt D
  have hψc : psi D c ≠ 0 := by
    intro h
    apply hc0
    have h' : D.host.φ₀ (((c : D.host.K) : D.host.E)) = 0 := h
    rw [map_eq_zero_iff _ D.host.φ₀.injective] at h'
    have : ((c : D.host.K) : D.host.E) = 0 := h'
    exact_mod_cast this
  have hψcβ : psi D (c * β) = psi D c * (Complex.I * (Real.sqrt D.host.d : ℂ)) := by
    show D.host.φ₀ _ = D.host.φ₀ _ * _
    rw [← hβ, ← map_mul]
    congr 1
  have hd : (0 : ℝ) < Real.sqrt D.host.d :=
    Real.sqrt_pos.mpr (by exact_mod_cast D.host.hyp.2.1.pos)
  have hmemR : ∀ x ∈ cc, psi D x ∈ Submodule.span ℝ (Set.range ![ω₁, ω₂]) := by
    intro x hx
    obtain ⟨m, n, hmn⟩ := hcomb x hx
    rw [← hmn]
    refine Submodule.add_mem _ ?_ ?_
    · have := Submodule.smul_mem (Submodule.span ℝ (Set.range ![ω₁, ω₂])) (m : ℝ)
        (Submodule.subset_span (⟨0, rfl⟩ : ω₁ ∈ Set.range ![ω₁, ω₂]))
      simpa [Complex.real_smul] using this
    · have := Submodule.smul_mem (Submodule.span ℝ (Set.range ![ω₁, ω₂])) (n : ℝ)
        (Submodule.subset_span (⟨1, rfl⟩ : ω₂ ∈ Set.range ![ω₁, ω₂]))
      simpa [Complex.real_smul] using this
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range ![ω₁, ω₂]) := by
    intro z _
    have h1 := hmemR c hc
    have h2 := hmemR (c * β) (cc.mul_mem_right β hc)
    have hz : z = (z / psi D c).re • psi D c + ((z / psi D c).im / Real.sqrt D.host.d) • psi D (c * β) := by
      rw [hψcβ, Complex.real_smul, Complex.real_smul]
      have hsd : (Real.sqrt D.host.d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      have key : z = psi D c * (((z / psi D c).re : ℂ) + ((z / psi D c).im : ℂ) * Complex.I) := by
        rw [Complex.re_add_im, mul_div_cancel₀ _ hψc]
      conv_lhs => rw [key]
      push_cast
      field_simp
    rw [hz]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)
  have hind : LinearIndependent ℝ ![ω₁, ω₂] :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by simp [Complex.finrank_real_complex])
  refine ⟨⟨ω₁, ω₂, hind⟩, fun w => ?_⟩
  rw [mem_lamOf_iff, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact hcomb c hc
  · rintro ⟨m, n, rfl⟩
    exact hback m n

theorem discrNZ : DiscrNZ D := by
  intro cc hcc
  obtain ⟨L, hL⟩ := exists_pp D cc hcc.1
  have h4 := eisG_eq_G _ L hL 2 (by norm_num)
  have h6 := eisG_eq_G _ L hL 3 (by norm_num)
  have := Formalism.L2.Th1.F.discNeZero L
  unfold Formalism.MainNotions.TaylorLogMetric.discr Formalism.MainNotions.TaylorLogMetric.g2 Formalism.MainNotions.TaylorLogMetric.g3
  rw [h4, h6]
  simpa [PeriodPair.g₂, PeriodPair.g₃] using this

end Formalism.L2.PairingIndexBounds.Rec
