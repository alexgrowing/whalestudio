import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection

namespace GlobalTheory.CompanionTheory.RgEisSide

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem inv_mulVec_smul_vec (m γ : GL ι 𝔸[k]) (x : 𝔸[k]) (i : ι) :
    ((m⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ (x • MG.vec γ i) = x • MG.vec (γ * m) i := by
  unfold MG.vec
  rw [Matrix.mulVec_smul, _root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]

omit [Fintype ι] [DecidableEq ι] in

theorem norm_lineZeta_le (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (s : ℂ) (v : ι → 𝔸[k]) :
    ‖lineZeta Ψ ω s v‖ ≤ ∫ t : IdeleGroup k, ‖Ψ ((t : 𝔸[k]) • v)‖ *
      (IdeleGroup.ideleModule k t : ℝ) ^ s.re ∂ideleMeasure k := by
  unfold lineZeta globalZeta
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  have hpos : (0 : ℝ) < (IdeleGroup.ideleModule k t : ℝ) := (IdeleGroup.ideleModule k t).2
  simp only [norm_mul, Circle.norm_coe, mul_one]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]

section Eis

variable {G : Type} [Group G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem avg_const_mul {K : Subgroup G} [MeasurableSpace K] (μ : Measure K) (ρ : K →* (W →L[ℂ] W)) (a : ℂ) (φ : K → ℂ) :
    avg μ ρ (fun κ => a * φ κ) = a • avg μ ρ φ := by
  unfold avg
  rw [← integral_smul]
  simp only [smul_smul]

theorem eis_smul (Γ K P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) (Λ : G → ℂ) (g : G) (a : ℂ) (w : W) :
    eis Γ K P c ρ Λ g (a • w) = a • eis Γ K P c ρ Λ g w := by
  unfold eis
  rw [← tsum_const_smul'']
  exact tsum_congr fun q => by rw [map_smul, smul_comm]

end Eis

theorem sideUnfold : EpConv → Unfold → Lines → Term → ZetaK → SideUnfold := by
  intro hE hU hL hT hZ G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hμ hP k _ _ ι _ _ π Γ P i ω d c η hS Ψ hΨ s hs g w
  have hcard : (1 : ℝ) < (Fintype.card ι : ℝ) := by
    have := hS.two
    exact_mod_cast (by omega : 1 < Fintype.card ι)
  have hs1 : 1 < s.re := hcard.trans hs
  obtain ⟨e, he⟩ := hL G K hK k ι π Γ P i ω d c η hS
  obtain ⟨hT1, hT2⟩ := hT G K hK k ι π Γ P i ω d c η hS
  obtain ⟨hTp, hTl, hTx⟩ := hT2 Ψ s
  obtain ⟨-, hZc, -⟩ := hZ G K hK k ι π Γ P i ω d c η hS Ψ hΨ
  set a : ℂ := (ω.toIdele (d i) : ℂ) * modPow (d i) s with ha
  let T : G → ℂ := fun y => lineZeta Ψ ω s (MG.vec (π y * dgl d) i)
  let φ : K → ℂ := fun κ => a * zt π d i Ψ ω s κ
  let Λ : G → ℂ := fun x => s * η x
  have key : ∀ (y : G) (q : Cos P Γ), lineZeta Ψ ω s
      (((π y * dgl d)⁻¹ : GL ι 𝔸[k]).1 *ᵥ ratV (e q).rep) = T (rep q * y) := by
    intro y q
    obtain ⟨x, hx⟩ := he q
    rw [hx, inv_mulVec_smul_vec, hTx]
    simp only [T, map_mul, mul_assoc]
  have hφc : Continuous φ := by
    have h1 : Continuous fun κ : K => zt π d i Ψ ω s κ := by
      have h2 : ContinuousOn (fun y : ℂ × K => zt π d i Ψ ω y.1 y.2) (Set.univ.image fun κ : K => (s, κ)) :=
        hZc.mono (by rintro _ ⟨κ, -, rfl⟩; exact ⟨hs1, Set.mem_univ _⟩)
      have h3 := h2.comp_continuous (f := fun κ : K => (s, κ)) (by fun_prop) (fun κ => ⟨κ, Set.mem_univ _, rfl⟩)
      exact h3
    exact continuous_const.mul h1
  have hφl : Law K P c φ := fun r κ hr => by
    have h : zt π d i Ψ ω s ((r * κ : K) : G) = c r * zt π d i Ψ ω s κ := hTl r κ hr
    simp only [φ]
    rw [h]
    ring
  have hΛ : ∀ x, ∀ κ ∈ K, Λ (x * κ) = Λ x := fun x κ hκ => by
    simp only [Λ, hS.ht.right x κ hκ]
  have hTP : ∀ p ∈ P, ∀ κ : K, T (p * κ) = c p * Complex.exp (Λ p) * φ κ := fun p hp κ =>
    hTp p hp κ κ.2
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hCc : IsCompact (Set.range fun κ : K => ((π (g * κ) * dgl d)⁻¹ : GL ι 𝔸[k])) := by
    refine isCompact_range ?_
    have hπ := hS.cont
    exact ((hπ.comp (continuous_const.mul continuous_subtype_val)).mul continuous_const).inv
  obtain ⟨u, hu, hub⟩ := (hE k ι Ψ hΨ).2 s.re _ (max_lt hs1 hs |>.trans_le le_rfl) hCc
  have hbound : ∀ (q : Cos P Γ) (κ : K), ‖T (rep q * (g * κ))‖ ≤ (u ∘ e) q := fun q κ => by
    rw [← key]
    exact (norm_lineZeta_le Ψ ω s _).trans (hub _ ⟨κ, rfl⟩ (e q))
  have hfun : (fun κ : K => epstein Ψ ω s (π (g * κ) * dgl d)) = fun κ : K => ∑' q : Cos P Γ, T (rep q * (g * κ)) := by
    funext κ
    unfold epstein
    rw [← e.tsum_eq]
    exact tsum_congr fun q => key _ q
  have hmain := hU G W K ρ hK hρ μ hμ hP Γ P c hS.par φ Λ T hφc hφl hΛ hTP g (u ∘ e) (e.summable_iff.2 hu) hbound w
  rw [hfun, hmain]
  simp only [φ]
  rw [avg_const_mul, _root_.smul_apply, eis_smul]

end GlobalTheory.CompanionTheory.RgEisSide
