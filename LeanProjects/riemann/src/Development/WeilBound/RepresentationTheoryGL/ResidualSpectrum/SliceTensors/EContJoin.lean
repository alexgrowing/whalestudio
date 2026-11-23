import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceA
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceB
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalOfL2CuspidalMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteTopologyRatN
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLeftInvariantOfIsAutForm

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace PositivityTheory.Rg.Rs.SliceClasses

theorem E_lift {X Y : Type*} (L : ℝ → (X → ℂ) →ₗ[ℂ] (X → ℂ)) (L' : ℝ → (Y → ℂ) →ₗ[ℂ] (Y → ℂ))
    (hL0 : ∀ f, L 0 f = f) (hLL : ∀ s t f, L s (L t f) = L (t + s) f) (f₀ : X → ℂ)
    [FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun t => L t f₀))] (B : (X → ℂ) → (Y → ℂ))
    (hadd : ∀ v ∈ Submodule.span ℂ (Set.range fun t => L t f₀), ∀ w ∈ Submodule.span ℂ (Set.range fun t => L t f₀),
      B (v + w) = B v + B w)
    (hsmul : ∀ (a : ℂ), ∀ w ∈ Submodule.span ℂ (Set.range fun t => L t f₀), B (a • w) = a • B w)
    (c d : ℂ) (hB : ∀ t : ℝ, ∀ w ∈ Submodule.span ℂ (Set.range fun t => L t f₀),
      B (L t w) = Complex.exp (d * t) • L' t (B w))
    (F' : Y → ℂ) (hF' : F' ∈ Submodule.span ℂ (Set.range fun t => L' t (B f₀))) (hne : F' ≠ 0)
    (heig : ∀ t : ℝ, L' t F' = Complex.exp (c * t) • F') :
    ∃ F ∈ Submodule.span ℂ (Set.range fun t => L t f₀), F ≠ 0 ∧
      ∀ t : ℝ, L t F = Complex.exp ((c + d) * t) • F := by
  set W := Submodule.span ℂ (Set.range fun t => L t f₀) with hWdef
  have hf₀ : f₀ ∈ W := by
    have h0 : L 0 f₀ ∈ W := Submodule.subset_span ⟨0, rfl⟩
    rwa [hL0] at h0
  have hW : ∀ t, ∀ w ∈ W, L t w ∈ W := by
    intro t w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      rw [hLL]
      exact Submodule.subset_span ⟨u + t, rfl⟩
    | zero => rw [map_zero]; exact W.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact W.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact W.smul_mem a hx
  have hL : ∀ s t, ∀ w ∈ W, L s (L t w) = L t (L s w) := fun s t w _ => by rw [hLL, hLL, add_comm]
  have hB0 : B 0 = 0 := by
    have := hsmul 0 0 W.zero_mem
    rwa [zero_smul, zero_smul] at this
  have key : ∀ x ∈ Submodule.span ℂ (Set.range fun t => L' t (B f₀)), ∃ w ∈ W, B w = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      refine ⟨Complex.exp (-(d * t)) • L t f₀, W.smul_mem _ (Submodule.subset_span ⟨t, rfl⟩), ?_⟩
      rw [hsmul _ _ (Submodule.subset_span ⟨t, rfl⟩), hB t f₀ hf₀, smul_smul, ← Complex.exp_add, neg_add_cancel,
        Complex.exp_zero, one_smul]
    | zero => exact ⟨0, W.zero_mem, hB0⟩
    | add x y _ _ hx hy =>
      obtain ⟨v, hv, rfl⟩ := hx
      obtain ⟨w, hw, rfl⟩ := hy
      exact ⟨v + w, W.add_mem hv hw, hadd v hv w hw⟩
    | smul a x _ hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      exact ⟨a • v, W.smul_mem a hv, hsmul a v hv⟩
  obtain ⟨w₀, hw₀, hBw₀⟩ := key F' hF'
  exact eig_lift W L hL hW L' B hadd hsmul c d hB w₀ hw₀ (hBw₀ ▸ hne) (hBw₀ ▸ heig)

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def E_vol (E : Type) [Field E] [NumberField E] (N r : ℕ) : ℂ :=
  (((unipMeasure E N r).real (unipFundamentalDomain E N r) : ℝ) : ℂ)

omit [IsTotallyComplex E] in
theorem E_vol_ne (N r : ℕ) : E_vol E N r ≠ 0 := by
  have := JDict.vol_pos E N r
  unfold E_vol
  exact_mod_cast this.ne'

omit [IsTotallyComplex E] in
theorem E_ctn_eq {N : ℕ} (r : ℕ) (u : GA E N → ℂ) (g : GA E N) :
    An.ctn r u g = (E_vol E N r)⁻¹ * constantTerm r u g := rfl

omit [IsTotallyComplex E] in
theorem E_ct_eq {N : ℕ} (r : ℕ) (u : GA E N → ℂ) (g : GA E N) :
    constantTerm r u g = E_vol E N r * An.ctn r u g := by
  rw [E_ctn_eq, ← mul_assoc, mul_inv_cancel₀ (E_vol_ne N r), one_mul]

theorem E_cont_ctn {N : ℕ} (r : ℕ) {u : GA E N → ℂ} (hc : Continuous u)
    (hl : ∀ γ g, u (ratGL E N γ * g) = u g) : Continuous (An.ctn r u) := by
  have : BorelSpace (BlockIx N r → Ad E) := ⟨JDict.pi_eq_borel E N r⟩
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.ConstNotCusp.exists_compact_ratN E N r
  have hfin : unipMeasure E N r (unipFundamentalDomain E N r) ≠ ⊤ := by
    obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := E) (n := N) (r := r)
    exact ((measure_mono hDC).trans_lt hC.measure_lt_top).ne
  have h := GlobalTheory.CompanionTheory.CuspL2.continuous_constTerm (unipMeasure E N r) hfin hK hcov hc hl
  refine continuous_const.mul ?_
  convert h using 2 with g
  simp only [constantTerm, GlobalTheory.CompanionTheory.CuspBridge.unipGL_eq_unip]

theorem E_cont_span {N : ℕ} (r : ℕ) {f : GA E N → ℂ} (hf : Continuous f) :
    ∀ w ∈ Submodule.span ℂ (Set.range fun t : ℝ => fun g => f (aT E N r t * g)), Continuous w := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    exact hf.comp (continuous_const.mul continuous_id)
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact continuous_const.smul hx

def E_B {N : ℕ} {Y ι : Type*} [Fintype ι] (P : (ι → Ad E) → GA E N) (Q : ℝ → Y → GA E N) (κ : ℂ) (τs : Finset ℝ)
    (a : ℝ → ℂ) (f : GA E N → ℂ) (m : Y) : ℂ :=
  κ * ∑ t ∈ τs, a t * ∫ b, f (P b * Q t m) ∂(Measure.pi fun _ : ι => boxMeasure E)

omit [IsTotallyComplex E] in
theorem E_B_add {N : ℕ} {Y ι : Type*} [Fintype ι] {P : (ι → Ad E) → GA E N} (hP : Continuous P) (Q : ℝ → Y → GA E N)
    (κ : ℂ) (τs : Finset ℝ) (a : ℝ → ℂ) {f g : GA E N → ℂ} (hf : Continuous f) (hg : Continuous g) :
    E_B P Q κ τs a (f + g) = E_B P Q κ τs a f + E_B P Q κ τs a g := by
  funext m
  simp only [E_B, Pi.add_apply]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have hi : ∀ u : GA E N → ℂ, Continuous u →
      Integrable (fun b => u (P b * Q t m)) (Measure.pi fun _ : ι => boxMeasure E) := fun u hu =>
    integrable_box (hu.comp (hP.mul continuous_const))
  rw [← mul_add, ← integral_add (hi f hf) (hi g hg)]

omit [IsTotallyComplex E] in
theorem E_B_smul {N : ℕ} {Y ι : Type*} [Fintype ι] (P : (ι → Ad E) → GA E N) (Q : ℝ → Y → GA E N)
    (κ : ℂ) (τs : Finset ℝ) (a : ℝ → ℂ) (c : ℂ) (f : GA E N → ℂ) :
    E_B P Q κ τs a (c • f) = c • E_B P Q κ τs a f := by
  funext m
  simp only [E_B, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_const_mul]
  ring

omit [IsTotallyComplex E] in
theorem E_cont_join {n : ℕ} {S : Finset ℕ} (q : ℕ) :
    Continuous fun b : {x : PPos n S // ¬ IsTop q x} → Ad E => (parGL (joinPos (r := q) 0 b) : GA E n) := by
  refine continuous_parGL.comp (continuous_pi fun x => ?_)
  by_cases hx : IsTop q x
  · simp only [joinPos, dif_pos hx]
    exact continuous_const
  · simp only [joinPos, dif_neg hx]
    exact continuous_apply _

theorem E_pos_top {N p q : ℕ} (hpq : p < q) (x : PPos N {p, q}) (hx : ¬ IsTop q x) :
    (x.1.1 : ℕ) < p ∧ p ≤ (x.1.2 : ℕ) ∧ (x.1.2 : ℕ) < q := by
  obtain ⟨s, hs, h1, h2⟩ := x.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  have hx' : ¬ ((x.1.1 : ℕ) < q ∧ q ≤ (x.1.2 : ℕ)) := hx
  rcases hs with rfl | rfl <;> omega

theorem E_pos_bot {N p q : ℕ} (hpq : p < q) (x : PPos N {p, q}) (hx : ¬ IsTop p x) :
    p ≤ (x.1.1 : ℕ) ∧ (x.1.1 : ℕ) < q ∧ q ≤ (x.1.2 : ℕ) := by
  obtain ⟨s, hs, h1, h2⟩ := x.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  have hx' : ¬ ((x.1.1 : ℕ) < p ∧ p ≤ (x.1.2 : ℕ)) := hx
  rcases hs with rfl | rfl <;> omega

theorem E_exp_iff (hD : Dict) {N r : ℕ} (φ : Sm E N) (hφ : IsAutForm φ) (h0 : 0 < r) (h1 : r < N) (c : ℂ) :
    c ∈ Exp r φ.1 ↔ ∃ F ∈ Submodule.span ℂ (Set.range fun t : ℝ => fun g => An.ctn r φ.1 (aT E N r t * g)),
      F ≠ 0 ∧ ∀ (t : ℝ) g, F (aT E N r t * g) = Complex.exp (c * t) * F g := by
  have hd := (hD E N).2.2.2 φ hφ r h0 h1
  constructor
  · rintro ⟨F₀, hct, F, hF, hne, heig⟩
    obtain ⟨κ, -, rfl⟩ := hd.2 F₀ hct
    refine ⟨F, Submodule.span_le.2 ?_ hF, hne, heig⟩
    rintro _ ⟨t, rfl⟩
    have e : (fun g => κ * An.ctn r φ.1 (aT E N r t * g)) = κ • fun g => An.ctn r φ.1 (aT E N r t * g) := rfl
    simp only [e]
    exact Submodule.smul_mem _ κ (Submodule.subset_span ⟨t, rfl⟩)
  · rintro ⟨F, hF, hne, heig⟩
    exact ⟨An.ctn r φ.1, hd.1, F, hF, hne, heig⟩

end PositivityTheory.Rg.Rs.SliceClasses

end
