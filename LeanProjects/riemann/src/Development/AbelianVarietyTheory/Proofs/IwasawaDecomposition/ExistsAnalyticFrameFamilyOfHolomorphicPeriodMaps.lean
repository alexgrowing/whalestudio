import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtEqOfPtOfFrameEq
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnitHmD
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.PeriodFamFrame
open ReciprocityTheory.ChartRestriction.G.FD

theorem sep_types {E : Type} [Field E] [NumberField E] {La : Type} [AddCommGroup La] [Module (𝓞 E) La]
    {g : ℕ} (ty : Fin g → (E →+* ℂ)) (G : Fin g → La → ℂ) (τ : E →+* ℂ) (c : Fin g → ℂ) (F : La → ℂ)
    (hG : ∀ j (a : 𝓞 E) v, G j (a • v) = ty j (a : E) * G j v)
    (hF : ∀ (a : 𝓞 E) v, F (a • v) = τ (a : E) * F v)
    (hsum : ∀ v, F v = ∑ j, c j * G j v) :
    ∀ v, F v = ∑ j, (if ty j = τ then c j else 0) * G j v := by
  classical
  intro v
  set H : (E →+* ℂ) → La → ℂ := fun χ w => ∑ j ∈ Finset.univ.filter (fun j => ty j = χ), c j * G j w with hH
  have hHs : ∀ χ (b : 𝓞 E) w, H χ (b • w) = χ (b : E) * H χ w := by
    intro χ b w
    simp only [hH, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hG, (Finset.mem_filter.1 hj).2]; ring
  have hFH : ∀ w, F w = ∑ χ ∈ Finset.univ.image ty, H χ w := by
    intro w
    rw [hsum w]
    exact (Finset.sum_fiberwise_of_maps_to (fun j _ => Finset.mem_image_of_mem ty (Finset.mem_univ j)) _).symm
  have hres : ∀ χ χ' : E →+* ℂ, (∀ a : 𝓞 E, χ (a : E) = χ' (a : E)) → χ = χ' := fun χ χ' h =>
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)
  have hli : LinearIndependent ℂ (fun χ : E →+* ℂ => fun a : 𝓞 E => χ (a : E)) :=
    (linearIndependent_monoidHom (𝓞 E) ℂ).comp (fun χ : E →+* ℂ => (χ.comp (algebraMap (𝓞 E) E)).toMonoidHom)
      (fun χ χ' e => hres χ χ' fun a => by simpa using DFunLike.congr_fun e a)
  have hzero : ∀ χ ∈ Finset.univ.image ty, χ ≠ τ → H χ v = 0 := by
    intro χ hχ hne
    obtain ⟨a, ha⟩ : ∃ a : 𝓞 E, χ (a : E) ≠ τ (a : E) := by
      by_contra hc; push_neg at hc; exact hne (hres _ _ hc)
    have key : ∑ χ' ∈ Finset.univ.image ty, ((χ' (a : E) - τ (a : E)) * H χ' v) • (fun b : 𝓞 E => χ' (b : E)) = 0 := by
      funext b
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have e1 := hF a (b • v)
      rw [hFH, hFH, smul_smul] at e1
      simp only [hHs] at e1
      rw [Finset.mul_sum] at e1
      calc _ = ∑ χ' ∈ Finset.univ.image ty, (χ' ((a * b : 𝓞 E) : E) * H χ' v - τ (a : E) * (χ' (b : E) * H χ' v)) :=
            Finset.sum_congr rfl fun χ' _ => by push_cast; rw [map_mul]; ring
        _ = 0 := by rw [Finset.sum_sub_distrib, e1, sub_self]
    have := linearIndependent_iff'.1 hli _ _ key χ hχ
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ha)
  rw [hFH v, Finset.sum_eq_single τ]
  · simp only [hH]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  · intro χ hχ hne; exact hzero χ hχ hne
  · intro hτ
    simp only [hH]
    refine Finset.sum_eq_zero fun j hj => ?_
    exact absurd ((Finset.mem_filter.1 hj).2 ▸ Finset.mem_image_of_mem ty (Finset.mem_univ j)) hτ

theorem exists_fam {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (φ : La ≃ₗ[𝓞 E] X.Λ) :
    ∃ (n : ℕ) (a : Fin n → La), ∀ ρ : E →+* ℂ, ∃ L : (Fin n → ℂ) →ₗ[ℂ] (Fin r → ℂ),
      ∀ u : Fin r → ℂ, L (fun k => hermC ρ X.Gm u (Data.emb ρ (φ (a k) : Fin r → E))) = u := by
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 X.Λ_fg
  have hsm : ∀ k, s k ∈ X.Λ := fun k => hs ▸ Submodule.subset_span (Set.mem_range_self k)
  refine ⟨n, fun k => φ.symm ⟨s k, hsm k⟩, fun ρ => ?_⟩
  simp only [LinearEquiv.apply_symm_apply]
  let Φ : (Fin r → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun u k => hermC ρ X.Gm u (Data.emb ρ (s k))
      map_add' := fun u u' => funext fun k => hermC_add_left ρ X.Gm u u' _
      map_smul' := fun c u => funext fun k => hermC_smul_left ρ X.Gm c u _ }
  have hΦ : LinearMap.ker Φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    have h0 : ∀ k, hermC ρ X.Gm u (Data.emb ρ (s k)) = 0 := fun k => congrFun hu k
    have hE : ∀ w : Fin r → E, hermC ρ X.Gm u (Data.emb ρ w) = 0 := by
      intro w
      have hw : w ∈ Submodule.span E (Set.range s) := by
        have h1 : X.Λ ≤ (Submodule.span E (Set.range s)).restrictScalars (𝓞 E) := by
          rw [← hs]; exact Submodule.span_le_restrictScalars (𝓞 E) E (Set.range s)
        have h2 : Submodule.span E (X.Λ : Set (Fin r → E)) ≤ Submodule.span E (Set.range s) :=
          Submodule.span_le.2 h1
        rw [X.Λ_span] at h2
        exact h2 trivial
      induction hw using Submodule.span_induction with
      | mem x hx => obtain ⟨k, rfl⟩ := hx; exact h0 k
      | zero => simp [Data.emb, hermC]
      | add x y _ _ hx hy =>
        rw [show Data.emb ρ (x + y) = Data.emb ρ x + Data.emb ρ y from funext fun _ => by simp [Data.emb],
          hermC_add_right, hx, hy, add_zero]
      | smul c x _ hx =>
        rw [show Data.emb ρ (c • x) = ρ c • Data.emb ρ x from funext fun _ => by simp [Data.emb],
          hermC_smul_right, hx, mul_zero]
    have hdet : (X.Gm.map ρ).det ≠ 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; simpa using X.Gm_det
    apply Matrix.eq_zero_of_vecMul_eq_zero hdet
    funext b
    have := hE (Pi.single b 1)
    simp only [hermC, Data.emb] at this
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Pi.zero_apply]
    rw [← this]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'; simp [Pi.single_apply, hb']
    · simp
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective Φ hΦ
  exact ⟨L, fun u => LinearMap.congr_fun hL u⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem perFr_smul_int (X : Data E r) (x : Frame X.Ψ r) (a : E) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    Formalism.L2.PjFree.perFr X x (a • v) τ i = τ a * Formalism.L2.PjFree.perFr X x v τ i := by
  have hemb : ∀ ρ : E →+* ℂ, Data.emb ρ (a • v) = ρ a • Data.emb ρ v := fun ρ => by
    funext k; simp [Data.emb]
  unfold Formalism.L2.PjFree.perFr
  split_ifs
  · rw [hemb, Matrix.mulVec_smul]; rfl
  · simp
  · rw [hemb, hermC_smul_right]; simp [conjEmb]
  · simp
  · simp

theorem coe_smul_lat (X : Data E r) (a : 𝓞 E) (w : X.Λ) :
    ((a • w : X.Λ) : Fin r → E) = (a : E) • (w : Fin r → E) := by
  funext k; simp [Algebra.smul_def]

theorem hermC_mulVec_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ)
    (w e : Fin r → ℂ) : hermC τ G (M *ᵥ w) e = ∑ k, w k * hermC τ G (col M k) e := by
  simp only [hermC, Matrix.mulVec, dotProduct, col, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring

theorem sum_fin_ite (n : ℕ) (f : Fin r → ℂ) :
    ∑ k : Fin r, (if (k : ℕ) = n then f k else 0) = if h : n < r then f ⟨n, h⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨n, h⟩]
    · simp
    · intro b _ hb; rw [if_neg]; intro e; exact hb (Fin.ext e)
    · simp
  · refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg]; intro e; exact h (e ▸ k.2)

theorem perFr_conj_type (X : Data E r) (x : Frame X.Ψ r) (ρ : X.Ψ) (w : Fin r → E) (i : ℕ) :
    Formalism.L2.PjFree.perFr X x w (conjEmb ρ.1) i =
      ∑ k : Fin r, (if (k : ℕ) = X.p0 - 1 - i then hermC ρ.1 X.Gm (col (mat x ρ) k) (Data.emb ρ.1 w) else 0) := by
  rw [sum_fin_ite]
  unfold Formalism.L2.PjFree.perFr
  rw [dif_neg (ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.conjEmb_not_mem X ρ)]
  have h' : conjEmb (conjEmb ρ.1) ∈ X.Ψ := by rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.conjEmb_conjEmb]; exact ρ.2
  rw [dif_pos h']
  suffices ∀ τ' (h' : τ' ∈ X.Ψ), τ' = ρ.1 →
      (if hj : X.p0 - 1 - i < r then hermC τ' X.Gm (col (mat x ⟨τ', h'⟩) ⟨X.p0 - 1 - i, hj⟩) (Data.emb τ' w) else 0) =
      (if hj : X.p0 - 1 - i < r then hermC ρ.1 X.Gm (col (mat x ρ) ⟨X.p0 - 1 - i, hj⟩) (Data.emb ρ.1 w) else 0) from
    this _ h' (ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.conjEmb_conjEmb _)
  rintro τ' h' rfl
  rfl

theorem rep_fwd (X : Data E r) {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (φ : La ≃ₗ[𝓞 E] X.Λ) {g : ℕ}
    (ty : Fin g → (E →+* ℂ)) (idx : Fin g → ℕ) (hidx : ∀ j, ty j ∉ X.Ψ → idx j < X.p0) (x' : Frame X.Ψ r)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (Q : La → Fin g → ℂ)
    (hQ : ∀ (a : 𝓞 E) v j, Q (a • v) j = ty j (a : E) * Q v j)
    (hh : ∀ v, Q v = h (fun j => Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j) (idx j)))
    (ρ : X.Ψ) (j : Fin g) (hj : ty j = conjEmb ρ.1) :
    ∃ w : Fin r → ℂ, (∀ k : Fin r, X.p0 ≤ (k : ℕ) → w k = 0) ∧
      ∀ v, Q v j = hermC ρ.1 X.Gm (mat x' ρ *ᵥ w) (Data.emb ρ.1 (φ v : Fin r → E)) := by
  set c : Fin g → ℂ := fun j' => h (fun k => if j' = k then 1 else 0) j with hc
  have hsum : ∀ v, Q v j = ∑ j', c j' * Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j') (idx j') := by
    intro v
    rw [hh v, show (h : (Fin g → ℂ) → (Fin g → ℂ)) _ = h.toLinearMap _ from rfl, LinearMap.pi_apply_eq_sum_univ]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hc, LinearEquiv.coe_coe]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hG : ∀ j' (a : 𝓞 E) v, Formalism.L2.PjFree.perFr X x' (φ (a • v) : Fin r → E) (ty j') (idx j') =
      ty j' (a : E) * Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j') (idx j') := by
    intro j' a v
    rw [map_smul, coe_smul_lat, perFr_smul_int]
  have hsep := sep_types ty (fun j' v => Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j') (idx j'))
    (conjEmb ρ.1) c (fun v => Q v j) hG (fun a v => by rw [hQ, hj]) hsum
  refine ⟨fun k => ∑ j', if ty j' = conjEmb ρ.1 ∧ (k : ℕ) = X.p0 - 1 - idx j' then c j' else 0, ?_, ?_⟩
  · intro k hk
    refine Finset.sum_eq_zero fun j' _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    have := hidx j' (h1 ▸ ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.conjEmb_not_mem X ρ)
    omega
  · intro v
    rw [hsep v, hermC_mulVec_left]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    by_cases hj' : ty j' = conjEmb ρ.1
    · rw [if_pos hj', hj', perFr_conj_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [true_and]
      split_ifs <;> simp
    · rw [if_neg hj', zero_mul]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      rw [if_neg (fun hh => hj' hh.1), zero_mul]

theorem rep_bwd (X : Data E r) {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (φ : La ≃ₗ[𝓞 E] X.Λ) {g : ℕ}
    (ty : Fin g → (E →+* ℂ)) (idx : Fin g → ℕ) (x' : Frame X.Ψ r)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (Q : La → Fin g → ℂ)
    (hQ : ∀ (a : 𝓞 E) v j, Q (a • v) j = ty j (a : E) * Q v j)
    (hh : ∀ v, Q v = h (fun j => Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j) (idx j)))
    (ρ : X.Ψ) (j0 : Fin g) (hj0 : ty j0 = conjEmb ρ.1) :
    ∃ c : Fin g → ℂ, ∀ v, Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j0) (idx j0) =
      ∑ j, (if ty j = conjEmb ρ.1 then c j else 0) * Q v j := by
  set c : Fin g → ℂ := fun j => h.symm (fun k => if j = k then 1 else 0) j0 with hc
  have hsum : ∀ v, Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j0) (idx j0) = ∑ j, c j * Q v j := by
    intro v
    have e : (fun j => Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j) (idx j)) = h.symm (Q v) := by
      rw [hh v, LinearEquiv.symm_apply_apply]
    rw [show Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j0) (idx j0) = h.symm (Q v) j0 from congrFun e j0,
      show (h.symm : (Fin g → ℂ) → (Fin g → ℂ)) _ = h.symm.toLinearMap _ from rfl, LinearMap.pi_apply_eq_sum_univ]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hc, LinearEquiv.coe_coe]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  refine ⟨c, sep_types ty (fun j v => Q v j) (conjEmb ρ.1) c
    (fun v => Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j0) (idx j0)) (fun j a v => hQ a v j) ?_ hsum⟩
  intro a v
  show Formalism.L2.PjFree.perFr X x' (φ (a • v) : Fin r → E) (ty j0) (idx j0) = _
  rw [map_smul, coe_smul_lat, perFr_smul_int, hj0]

theorem lift_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (La : Type) [AddCommGroup La] [Module (𝓞 E) La] (φ : La ≃ₗ[𝓞 E] X.Λ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (idx : Fin g → ℕ) (d : ℕ) (B : Set (ReciprocityTheory.L2DbarEstimates.V d)) (P : ReciprocityTheory.L2DbarEstimates.V d → (La →+ (Fin g → ℂ))) (b₀ : ReciprocityTheory.L2DbarEstimates.V d), IsOpen B → b₀ ∈ B → (∀ b ∈ B, ∀ (a : 𝓞 E) (v : La) (j : Fin g), P b (a • v) j = ty j (a : E) * P b v j) → (∀ v, DifferentiableOn ℂ (fun b => P b v) B) → (∀ ρ ∈ X.Ψ, ∀ m < X.p0, ∃ j, ty j = conjEmb ρ ∧ idx j = m) → (∀ j j', ty j = ty j' → idx j = idx j' → j = j') → (∀ j, ty j ∉ X.Ψ → idx j < X.p0) → (∀ b ∈ B, ∃ x' ∈ X.dom, ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ v, P b v = h (fun j => Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j) (idx j))) → ∃ s : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, AnalyticAt ℂ s b₀ ∧ ∀ᶠ b in 𝓝 b₀, s b ∈ X.dom ∧ ∀ x' ∈ X.dom, (∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ v, P b v = h (fun j => Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j) (idx j))) → (∀ (τ : X.Ψ) (a b' : Fin r), X.p0 ≤ (a : ℕ) → (b' : ℕ) < X.p0 → ((ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ)⁻¹ * ReciprocityTheory.ChartRestriction.G.FD.mat x' τ) a b' = 0) ∧ (∀ (τ : X.Ψ) (a b' : Fin r), X.p0 ≤ (a : ℕ) → (b' : ℕ) < X.p0 → ((ReciprocityTheory.ChartRestriction.G.FD.mat x' τ)⁻¹ * ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ) a b' = 0) := by
  intro E _ _ _ r X La _ _ φ g ty idx d B P b₀ hBo hb₀ hsl hdiff hcov hinj hidx hper
  obtain ⟨n, a, hL⟩ := exists_fam X φ
  choose L hL using hL
  set yv : ReciprocityTheory.L2DbarEstimates.V d → X.Ψ → Fin g → Fin r → ℂ := fun b ρ j => L ρ.1 (fun k => P b (a k) j) with hyv
  have hrep : ∀ b ∈ B, ∀ x' : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, ∀ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ),
      (∀ v, P b v = h (fun j => Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j) (idx j))) →
      ∀ (ρ : X.Ψ) (j : Fin g), ty j = conjEmb ρ.1 → ∃ w : Fin r → ℂ,
        (∀ k : Fin r, X.p0 ≤ (k : ℕ) → w k = 0) ∧ yv b ρ j = ReciprocityTheory.ChartRestriction.G.FD.mat x' ρ *ᵥ w ∧
        ∀ v, P b v j = ReciprocityTheory.ChartRestriction.G.FD.hermC ρ.1 X.Gm (yv b ρ j)
          (ReciprocityTheory.ChartRestriction.G.FD.Data.emb ρ.1 (φ v : Fin r → E)) := by
    intro b hb x' h hh ρ j hj
    obtain ⟨w, hw, hv⟩ := rep_fwd X φ ty idx hidx x' h (fun v => P b v) (fun a v j => hsl b hb a v j) hh ρ j hj
    have hy : yv b ρ j = ReciprocityTheory.ChartRestriction.G.FD.mat x' ρ *ᵥ w := by
      rw [hyv]
      dsimp only
      rw [show (fun k => P b (a k) j) = fun k => ReciprocityTheory.ChartRestriction.G.FD.hermC ρ.1 X.Gm
          (ReciprocityTheory.ChartRestriction.G.FD.mat x' ρ *ᵥ w) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb ρ.1 (φ (a k) : Fin r → E)) from
        funext fun k => hv (a k)]
      exact hL ρ.1 _
    exact ⟨w, hw, hy, fun v => by rw [hy]; exact hv v⟩
  obtain ⟨x₀, hx₀, h₀, hh₀⟩ := hper b₀ hb₀
  have hcol : ∀ (ρ : X.Ψ) (m : Fin r), (m : ℕ) < X.p0 → ∃ c : Fin g → ℂ, (∀ j, ty j ≠ conjEmb ρ.1 → c j = 0) ∧
      ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat x₀ ρ) m = ∑ j, c j • yv b₀ ρ j := by
    intro ρ m hm
    obtain ⟨j0, hj0, hi0⟩ := hcov ρ.1 ρ.2 (X.p0 - 1 - m) (by omega)
    obtain ⟨c, hc⟩ := rep_bwd X φ ty idx x₀ h₀ (fun v => P b₀ v) (fun a v j => hsl b₀ hb₀ a v j) hh₀ ρ j0 hj0
    refine ⟨fun j => if ty j = conjEmb ρ.1 then c j else 0, fun j hj => if_neg hj, ?_⟩
    have key : ∀ v, ReciprocityTheory.ChartRestriction.G.FD.hermC ρ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat x₀ ρ) m)
        (ReciprocityTheory.ChartRestriction.G.FD.Data.emb ρ.1 (φ v : Fin r → E)) =
        ReciprocityTheory.ChartRestriction.G.FD.hermC ρ.1 X.Gm (∑ j, (if ty j = conjEmb ρ.1 then c j else 0) • yv b₀ ρ j)
          (ReciprocityTheory.ChartRestriction.G.FD.Data.emb ρ.1 (φ v : Fin r → E)) := by
      intro v
      have e1 := hc v
      rw [hj0, hi0, perFr_conj_type] at e1
      have e2 : (∑ k : Fin r, if (k : ℕ) = X.p0 - 1 - (X.p0 - 1 - (m : ℕ)) then
          ReciprocityTheory.ChartRestriction.G.FD.hermC ρ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat x₀ ρ) k)
            (ReciprocityTheory.ChartRestriction.G.FD.Data.emb ρ.1 (φ v : Fin r → E)) else 0) =
          ReciprocityTheory.ChartRestriction.G.FD.hermC ρ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat x₀ ρ) m)
            (ReciprocityTheory.ChartRestriction.G.FD.Data.emb ρ.1 (φ v : Fin r → E)) := by
        rw [Finset.sum_eq_single m]
        · rw [if_pos (by omega)]
        · intro k _ hk; rw [if_neg]; intro e; exact hk (Fin.ext (by omega))
        · simp
      rw [← e2, e1, ReciprocityTheory.ChartRestriction.G.FD.hermC_sum_left]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : ty j = conjEmb ρ.1
      · rw [if_pos hj, ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left]
        obtain ⟨w, -, -, hPv⟩ := hrep b₀ hb₀ x₀ h₀ hh₀ ρ j hj
        rw [hPv v]
      · rw [if_neg hj, zero_mul, zero_smul, ReciprocityTheory.ChartRestriction.G.FD.hermC_zero_left]
    have := congrArg (L ρ.1) (funext fun k => key (a k))
    simpa only [hL] using this
  choose! cc hcc0 hcc using hcol
  let s : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r := fun b ρ k m =>
    if (m : ℕ) < X.p0 then ∑ j, cc ρ m j * yv b ρ j k else x₀ ρ k m
  have hs0 : s b₀ = x₀ := by
    funext ρ k m
    simp only [s]
    split_ifs with hm
    · have := congrFun (hcc ρ m hm) k
      simp only [ReciprocityTheory.ChartRestriction.G.FD.col, ReciprocityTheory.ChartRestriction.G.FD.mat, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at this
      exact this.symm
    · rfl
  have hsd : DifferentiableOn ℂ s B := by
    have hv : ∀ (ρ : X.Ψ) j, DifferentiableOn ℂ (fun b => yv b ρ j) B := by
      intro ρ j
      have h1 : DifferentiableOn ℂ (fun b => fun k => P b (a k) j) B :=
        differentiableOn_pi.2 fun k => differentiableOn_pi.1 (hdiff (a k)) j
      exact (LinearMap.toContinuousLinearMap (L ρ.1)).differentiable.comp_differentiableOn h1
    refine differentiableOn_pi.2 fun ρ => differentiableOn_pi.2 fun k => differentiableOn_pi.2 fun m => ?_
    by_cases hm : (m : ℕ) < X.p0
    · simp only [s, if_pos hm]
      exact DifferentiableOn.fun_sum fun j _ => (differentiableOn_const _).mul (differentiableOn_pi.1 (hv ρ j) k)
    · simp only [s, if_neg hm]
      exact differentiableOn_const _
  refine ⟨s, GlobalTheory.SCV.analyticAt_of_differentiableOn hsd (hBo.mem_nhds hb₀), ?_⟩
  have hev : ∀ᶠ b in 𝓝 b₀, s b ∈ X.dom :=
    (hsd.continuousOn.continuousAt (hBo.mem_nhds hb₀)).preimage_mem_nhds
      ((ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom X).mem_nhds (hs0 ▸ hx₀))
  filter_upwards [hev, hBo.mem_nhds hb₀] with b hsb hb
  refine ⟨hsb, fun x' hx' hex => ?_⟩
  obtain ⟨h, hh⟩ := hex
  have R2 : ∀ (τ : X.Ψ) (a' b' : Fin r), X.p0 ≤ (a' : ℕ) → (b' : ℕ) < X.p0 →
      ((ReciprocityTheory.ChartRestriction.G.FD.mat x' τ)⁻¹ * ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ) a' b' = 0 := by
    intro τ a' b' ha hb'
    have hr : ∀ j, ty j = conjEmb τ.1 → ∃ w : Fin r → ℂ, (∀ k : Fin r, X.p0 ≤ (k : ℕ) → w k = 0) ∧
        yv b τ j = ReciprocityTheory.ChartRestriction.G.FD.mat x' τ *ᵥ w := fun j hj => by
      obtain ⟨w, hw, hy, -⟩ := hrep b hb x' h hh τ j hj
      exact ⟨w, hw, hy⟩
    choose! w hw hyw using hr
    set W : Fin r → ℂ := ∑ j, cc τ b' j • w j with hW
    have hcolW : ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ) b' = ReciprocityTheory.ChartRestriction.G.FD.mat x' τ *ᵥ W := by
      rw [hW, Matrix.mulVec_sum]
      funext k
      simp only [ReciprocityTheory.ChartRestriction.G.FD.col, ReciprocityTheory.ChartRestriction.G.FD.mat, Matrix.of_apply, s, if_pos hb', Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : ty j = conjEmb τ.1
      · have e := hyw j hj
        simp only [ReciprocityTheory.ChartRestriction.G.FD.mat] at e
        simp only [Matrix.mulVec_smul, ← e, Pi.smul_apply, smul_eq_mul]
      · rw [hcc0 τ b' hb' j hj]; simp
    have hdet : IsUnit (ReciprocityTheory.ChartRestriction.G.FD.mat x' τ).det := ((hx' τ).1).isUnit
    have e : ((ReciprocityTheory.ChartRestriction.G.FD.mat x' τ)⁻¹ * ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ) a' b' =
        ((ReciprocityTheory.ChartRestriction.G.FD.mat x' τ)⁻¹ *ᵥ ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ) b') a' := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, ReciprocityTheory.ChartRestriction.G.FD.col]
    rw [e, hcolW, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec, hW]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : ty j = conjEmb τ.1
    · rw [hw j hj a' ha, mul_zero]
    · rw [hcc0 τ b' hb' j hj, zero_mul]
  refine ⟨fun τ a' b' ha hb' => ?_, R2⟩
  set M := (ReciprocityTheory.ChartRestriction.G.FD.mat x' τ)⁻¹ * ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ with hM
  have hdx : IsUnit (ReciprocityTheory.ChartRestriction.G.FD.mat x' τ).det := ((hx' τ).1).isUnit
  have hds : IsUnit (ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ).det := ((hsb τ).1).isUnit
  have hdM : IsUnit M.det := by
    rw [hM, Matrix.det_mul]; exact (Matrix.isUnit_nonsing_inv_det _ hdx).mul hds
  letI := M.invertibleOfIsUnitDet hdM
  have hbt : M.BlockTriangular (fun i : Fin r => if (i : ℕ) < X.p0 then 0 else 1) := by
    intro i j hij
    dsimp only at hij
    by_cases hi : (i : ℕ) < X.p0
    · rw [if_pos hi] at hij; exact absurd hij (Nat.not_lt_zero _)
    · by_cases hj : (j : ℕ) < X.p0
      · exact R2 τ i j (by omega) hj
      · rw [if_neg hi, if_neg hj] at hij; exact absurd hij (lt_irrefl _)
  have hinv := Matrix.blockTriangular_inv_of_blockTriangular hbt
  have eM : M⁻¹ = (ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ)⁻¹ * ReciprocityTheory.ChartRestriction.G.FD.mat x' τ := by
    rw [hM, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hdx]
  rw [← eM]
  exact hinv (show (if (b' : ℕ) < X.p0 then 0 else 1) < (if (a' : ℕ) < X.p0 then 0 else 1) by
    rw [if_pos hb', if_neg (by omega)]; exact Nat.zero_lt_one)

end GlobalTheory.PeriodFamFrame
