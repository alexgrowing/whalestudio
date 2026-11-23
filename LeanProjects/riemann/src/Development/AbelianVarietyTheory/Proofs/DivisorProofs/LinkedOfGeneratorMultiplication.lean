import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularFrameDiagonalRatiosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalGeneratorsCohereNearPointStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LatChain

section LcAlg

variable {K : Type} [Field K] {R : Subring K} {σ τ : Type} [Fintype σ] [Fintype τ]

theorem Lc.comp_lc {f : σ → K} {g : τ → K} {a : K} (h : Lc R f a) (hf : ∀ s, Lc R g (f s)) : Lc R g a := by
  obtain ⟨α, hα, rfl⟩ := h
  choose β hβ e using hf
  refine ⟨fun t => ∑ s, α s * β s t, fun t => sum_mem fun s _ => mul_mem (hα s) (hβ s t), ?_⟩
  calc ∑ s, α s * f s = ∑ s, ∑ t, α s * β s t * g t := by simp_rw [e, Finset.mul_sum, mul_assoc]
    _ = _ := by rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]

theorem Lc.div_mem_of {f : σ → K} {a η : K} (h : Lc R f a) (hf : ∀ s, f s / η ∈ R) : a / η ∈ R := by
  obtain ⟨α, hα, rfl⟩ := h
  rw [Finset.sum_div]
  exact sum_mem fun s _ => by rw [mul_div_assoc]; exact mul_mem (hα s) (hf s)

end LcAlg

section LocPt

variable {X : Scheme.{0}} [IsIntegral X]

theorem Gen.eventually_nhds {x : X} {σ : Type} [Fintype σ] {f : σ → X.functionField} {η : X.functionField}
    (h : Gen (loc x) f η) : ∀ᶠ z in 𝓝 x, Gen (loc z) f η := by
  obtain ⟨h0, h1, α, hα, e⟩ := h
  have A : ∀ᶠ z in 𝓝 x, ∀ s, RegAt z (f s / η) := eventually_all.2 fun s => eventually_regAt (h1 s)
  have B : ∀ᶠ z in 𝓝 x, ∀ s, RegAt z (α s) := eventually_all.2 fun s => eventually_regAt (hα s)
  exact (A.and B).mono fun z hz => ⟨h0, hz.1, α, hz.2, e⟩

theorem unitAt_of_mem_loc {z : X} {f : X.functionField} (h0 : f ≠ 0) (h : f ∈ loc z) (h' : f⁻¹ ∈ loc z) :
    UnitAt z f :=
  (unitAt_iff h0).2 ⟨h, h'⟩

theorem unitAt_of_comb {z : X} {u ρ α β : X.functionField} (hu : RegAt z u) (hρ : RegAt z ρ) (hn : ¬ UnitAt z ρ)
    (hα : RegAt z α) (hβ : RegAt z β) (e : 1 = u * α + ρ * β) : UnitAt z u := by
  by_contra hu'
  have h1 : ZeroAt z u := zeroAt_iff.2 ⟨hu, hu'⟩
  have h2 : ZeroAt z ρ := zeroAt_iff.2 ⟨hρ, hn⟩
  have h3 := (h1.mul hα).add (h2.mul hβ)
  rw [← e] at h3
  exact (zeroAt_iff.1 h3).2 (unitAt_one z)

theorem ne_zero_of_unitAt_add_zeroAt {z : X} {v w f : X.functionField} (hv : UnitAt z v) (hw : ZeroAt z w)
    (e : f = v + w) : f ≠ 0 := by
  rintro rfl
  have hv' : v = w * (-1) := by linear_combination (-1 : X.functionField) * e
  have hm : RegAt z (-1 : X.functionField) := mem_loc.1 (neg_mem (mem_loc.2 (unitAt_one z).regAt))
  rw [hv'] at hv
  exact (zeroAt_iff.1 (hw.mul hm)).2 hv

end LocPt

theorem link_adapted_step : ∀ (X : Scheme.{0}) [IsIntegral X] (p k a N : ℕ) (M : X → Matrix (Fin N) (Fin N) X.functionField) (c : X → Fin N → X.functionFieldˣ) (j : Fin N) (γ : X.functionField), γ ≠ 0 → (∀ x, Ov p x → RegAt x γ ∧ RegAt x ((p : X.functionField) ^ a / γ)) → Coh p (k + 1 + a) M c → ∀ η : X → Fin (N + 1) → X.functionFieldˣ, (∀ x, Ov p x → ∀ i, Gen (loc x) (gens γ (fun l => (M x)⁻¹ l j) i) (η x i)) → Link p c fun x i => c x i * η x i.succ / η x i.castSucc := by
  intro X _ p k a N M c j γ hγ hreg hcoh η hgen
  have E := fun x (hx : Ov p x) => GlobalTheory.T.triangular_frame_diagonal_ratios X.functionField N (loc x) (M x) j γ (fun i => (η x i : X.functionField))
    (hcoh x hx).1 (hreg x hx).1 hγ (hgen x hx)
  have CG := GlobalTheory.T.local_generators_cohere_near_point X p k a N M c j γ hγ hreg hcoh
  have KEY : ∀ x, Ov p x → ∀ i : Fin N, ¬ UnitAt x ((η x i.succ : X.functionField) / η x i.castSucc) →
      UnitAt x ((M x)⁻¹ i j / η x i.castSucc) := by
    intro x hx i hn
    obtain ⟨-, -, -, -, hE⟩ := E x hx
    obtain ⟨hρ, α, hα, β, hβ, e⟩ := hE i
    have hy : (M x)⁻¹ i j / η x i.castSucc ∈ loc x := by
      have := (hgen x hx i.castSucc).2.1 (some i)
      simpa [gens] using this
    refine unitAt_of_comb hy hρ hn hα hβ ?_
    field_simp
    linear_combination e
  have hU : ∀ x, Ov p x → ∀ᶠ z in 𝓝 x, Ov p z → ∀ i, UnitAt z ((η x i : X.functionField) / η z i) := by
    intro x hx
    filter_upwards [CG x hx, eventually_all.2 fun i => Gen.eventually_nhds (hgen x hx i)] with z h1 h2 hz i
    obtain ⟨h3, -⟩ := h1 hz
    have g := hgen z hz i
    refine unitAt_of_mem_loc (div_ne_zero (η x i).ne_zero (η z i).ne_zero) ?_ ?_
    · exact ((h2 i).2.2.comp_lc fun s => (h3 i s).2).div_mem_of g.2.1
    · rw [inv_div]; exact (g.2.2.comp_lc fun s => (h3 i s).1).div_mem_of (h2 i).2.1
  refine ⟨η, Units.mk0 γ hγ, fun i x hx => ?_, fun x hx => ?_, fun i => ?_⟩
  · obtain ⟨-, -, -, h4, -⟩ := E x hx
    refine ⟨(h4 i).1, ⟨a, ?_⟩, (hU x hx).mono fun z hz hz' => hz hz' i⟩
    have : (p : X.functionField) ^ a / η x i = ((p : X.functionField) ^ a / γ) * (γ / η x i) := by
      field_simp
    rw [this]; exact (hreg x hx).2.mul (h4 i).2
  · obtain ⟨-, h1, h2, h4, h5⟩ := E x hx
    refine ⟨unitAt_of_mem_loc (η x 0).ne_zero (h4 0).1 h1, unitAt_of_mem_loc ?_ ?_ ?_, fun i => ⟨(h5 i).1, ?_⟩⟩
    · simp [hγ]
    · simpa using h2
    · simpa [inv_div] using (h4 (Fin.last N)).2
    · convert unitAt_one x using 1
      simp only [Units.val_div_eq_div_val, Units.val_mul]
      field_simp
  · refine ⟨fun x => if h : (M x)⁻¹ i j = 0 then 1 else Units.mk0 ((M x)⁻¹ i j / c x i) (div_ne_zero h (c x i).ne_zero),
      fun x hx => ⟨fun hn => ?_, ?_⟩⟩
    · have hu := KEY x hx i hn
      have hy : (M x)⁻¹ i j ≠ 0 := fun h0 => hu.ne_zero (by rw [h0, zero_div])
      dsimp only
      rw [dif_neg hy]
      convert hu using 1
      simp only [Units.val_mk0]
      field_simp
    · filter_upwards [CG x hx] with z hz hz' hn
      obtain ⟨-, hc⟩ := hz hz'
      obtain ⟨hd, hl⟩ := hc i
      have hu := hl.div_mem_of (hgen z hz' i.succ).2.1
      have hv := KEY z hz' i hn
      have hyz : (M z)⁻¹ i j ≠ 0 := fun h0 => hv.ne_zero (by rw [h0, zero_div])
      obtain ⟨-, -, -, -, h5⟩ := E z hz'
      have hρ : ZeroAt z ((η z i.succ : X.functionField) / η z i.castSucc) := zeroAt_iff.2 ⟨(h5 i).1, hn⟩
      have hyx' := ne_zero_of_unitAt_add_zeroAt (hd.mul hv) (hρ.mul (mem_loc.1 hu))
        (f := (M x)⁻¹ i j / (η z i.castSucc : X.functionField)) (by field_simp; try ring)
      have hyx : (M x)⁻¹ i j ≠ 0 := fun h0 => hyx' (by rw [h0, zero_div])
      try beta_reduce
      rw [dif_neg hyx, dif_neg hyz]
      simp only [Units.val_mk0]
      have key : ((M x)⁻¹ i j / (c x i : X.functionField) / ((M z)⁻¹ i j / (c z i : X.functionField)) - 1) / ((η z i.succ : X.functionField) / η z i.castSucc) =
          ((M x)⁻¹ i j - (c x i : X.functionField) / c z i * (M z)⁻¹ i j) / η z i.succ *
            ((c x i : X.functionField) / c z i * ((M z)⁻¹ i j / η z i.castSucc))⁻¹ := by
        field_simp
        try ring
      rw [key]
      exact (mem_loc.1 hu).mul (hd.mul hv).inv.regAt

end GlobalTheory.LatChain

end
