import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace

noncomputable section

namespace GlobalTheory.InvBilinTest

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

open Classical in

def cosetInd (K : Subgroup G) (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) (g : G) :
    SB G :=
  ⟨fun x => if x * g⁻¹ ∈ K then 1 else 0, by
    constructor
    · have h1 : IsOpen {x : G | x * g⁻¹ ∈ K} := ho.preimage (continuous_id.mul continuous_const)
      have h2 : IsClosed {x : G | x * g⁻¹ ∈ K} :=
        (K.isClosed_of_isOpen ho).preimage (continuous_id.mul continuous_const)
      rw [IsLocallyConstant.iff_exists_open]
      intro y
      by_cases hy : y * g⁻¹ ∈ K
      · exact ⟨_, h1, hy, fun x hx => by rw [if_pos hy]; exact if_pos hx⟩
      · exact ⟨_, h2.isOpen_compl, hy, fun x hx => by rw [if_neg hy]; exact if_neg hx⟩
    · refine HasCompactSupport.intro (hK.image (continuous_id.mul (continuous_const (y := g))))
        fun x hx => if_neg fun h => hx ⟨_, h, by simp⟩⟩

open Classical in

theorem cosetInd_apply (K : Subgroup G) (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G))
    (g x : G) : (cosetInd K ho hK g).1 x = if x * g⁻¹ ∈ K then 1 else 0 := rfl

theorem isLocallyConstant_cosetInd (K : Subgroup G) (ho : IsOpen (K : Set G))
    (hK : IsCompact (K : Set G)) : IsLocallyConstant (cosetInd K ho hK) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨{h | g * h⁻¹ ∈ K}, ho.preimage (continuous_const.mul continuous_inv), by simp,
    fun h hh => Subtype.ext (funext fun x => ?_)⟩
  rw [cosetInd_apply, cosetInd_apply]
  have : x * h⁻¹ = x * g⁻¹ * (g * h⁻¹) := by group
  classical
  have hh' : g * h⁻¹ ∈ K := hh
  rw [this]
  exact if_congr (K.mul_mem_cancel_right hh') rfl rfl

variable [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
  {Y : Type} [AddCommGroup Y] [Module ℂ Y]

open MeasureTheory in
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] in
variable [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
  {Y : Type} [AddCommGroup Y] [Module ℂ Y] in
omit [T2Space G] in
open Classical in

theorem _root_.GlobalTheory.InvBilinTest.integral_ite (K : Subgroup G) (ho : IsOpen (K : Set G)) (c : ℂ) :
    ∫ g, (if g ∈ K then c else 0) ∂μ = (μ.real K : ℂ) * c := by
  have hm : MeasurableSet (K : Set G) := ho.measurableSet
  have h : (fun g : G => if g ∈ K then c else 0) = (K : Set G).indicator (fun _ => c) := by
    ext g
    simp [Set.indicator_apply]
  rw [h, integral_indicator_const c hm, Complex.real_smul]

theorem smoothOp_cosetInd (hπ : IsSmooth π) (K : Subgroup G) (ho : IsOpen (K : Set G))
    (hK : IsCompact (K : Set G)) {w : V} (hw : ∀ k ∈ K, π k w = w) :
    smoothOp π μ (cosetInd K ho hK 1).1 w = (μ.real K : ℂ) • w := by
  refine eq_of_forall_dual fun l => ?_
  rw [hπ.map_smoothOp (cosetInd K ho hK 1).2.1 (cosetInd K ho hK 1).2.2, map_smul, smul_eq_mul,
    ← integral_ite K ho]
  congr 1
  ext g
  rw [cosetInd_apply]
  by_cases hg : g ∈ K
  · simp [hg, hw g hg]
  · simp [hg]

theorem key [μ.IsMulRightInvariant] (hπ : IsSmooth π) (B : SB G →ₗ[ℂ] V →ₗ[ℂ] Y)
    (hB : ∀ (g : G) (φ ψ : SB G) (v : V), (∀ x, ψ.1 x = φ.1 (x * g)) → B ψ (π g v) = B φ v)
    (K : Subgroup G) (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G))
    (φ : SB G) (hφ : ∀ k ∈ K, ∀ g, φ.1 (k * g) = φ.1 g) (v : V) :
    B (cosetInd K ho hK 1) (smoothOp π μ φ.1 v) = (μ.real K : ℂ) • B φ v := by
  classical
  have hF : IsLocallyConstant fun g => φ.1 g • cosetInd K ho hK g :=
    φ.2.1.comp₂ (isLocallyConstant_cosetInd K ho hK) (· • ·)
  have hc : HasCompactSupport fun g => φ.1 g • cosetInd K ho hK g :=
    HasCompactSupport.intro φ.2.2 fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]
  have h1 : lcIntegral μ (fun g => φ.1 g • cosetInd K ho hK g) = (μ.real K : ℂ) • φ := by
    refine Subtype.ext (funext fun x => ?_)
    have := map_lcIntegral (μ := μ) hF hc (LinearMap.proj (R := ℂ) (φ := fun _ : G => ℂ) x ∘ₗ (SB G).subtype)
    refine this.trans ?_
    show ∫ g, φ.1 g * (cosetInd K ho hK g).1 x ∂μ = (μ.real K : ℂ) * φ.1 x
    rw [← integral_ite K ho, ← integral_mul_right_eq_self _ x]
    congr 1
    ext g
    rw [cosetInd_apply]
    by_cases hg : g ∈ K
    · simp [hg, hφ g hg]
    · simp [hg]
  refine eq_of_forall_dual fun l => ?_
  have h2 := map_lcIntegral (μ := μ) hF hc (l ∘ₗ B.flip v)
  have h3 := hπ.map_smoothOp (μ := μ) φ.2.1 φ.2.2 (l ∘ₗ B (cosetInd K ho hK 1)) v
  rw [h1] at h2
  simp only [LinearMap.comp_apply, map_smul, LinearMap.flip_apply] at h2 h3 ⊢
  rw [h2, h3]
  congr 1
  ext g
  rw [hB g (cosetInd K ho hK g) (cosetInd K ho hK 1) v fun x => by simp [cosetInd_apply]]

theorem exists_factor (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G,
      IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (hπ : IsSmooth π)
    (Y : Type) [AddCommGroup Y] [Module ℂ Y] (B : SB G →ₗ[ℂ] V →ₗ[ℂ] Y)
    (hB : ∀ (g : G) (φ ψ : SB G) (v : V), (∀ x, ψ.1 x = φ.1 (x * g)) → B ψ (π g v) = B φ v) :
    ∃ B₀ : V →ₗ[ℂ] Y, ∀ (φ : SB G) (v : V), B φ v = B₀ (smoothOp π μ φ.1 v) := by
  have hpos : ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) →
      (μ.real K : ℂ) ≠ 0 := fun K ho hK => by
    have h1 : μ K ≠ 0 := (ho.measure_pos μ ⟨1, K.one_mem⟩).ne'
    have h2 : μ.real K ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h1, hK.measure_ne_top⟩
    exact_mod_cast h2
  have hle : ∀ (K : Subgroup G) (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G))
      (L : Subgroup G) (ho' : IsOpen (L : Set G)) (hL : IsCompact (L : Set G)), L ≤ K →
      ∀ w, (∀ k ∈ K, π k w = w) →
      (μ.real K : ℂ)⁻¹ • B (cosetInd K ho hK 1) w = (μ.real L : ℂ)⁻¹ • B (cosetInd L ho' hL 1) w := by
    intro K ho hK L ho' hL hLK w hw
    have h := key (μ := μ) hπ B hB L ho' hL (cosetInd K ho hK 1) (fun k hk g => by
      classical
      rw [cosetInd_apply, cosetInd_apply, mul_assoc]
      exact if_congr (K.mul_mem_cancel_left (hLK hk)) rfl rfl) w
    rw [smoothOp_cosetInd hπ K ho hK hw, map_smul] at h
    rw [inv_smul_eq_iff₀ (hpos K ho hK), smul_comm, h, inv_smul_smul₀ (hpos L ho' hL)]
  have hex : ∀ w : V, ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧
      ∀ k ∈ K, π k w = w := fun w => by
    obtain ⟨K, ho, hK, h⟩ := hG _ ((hπ w).mem_nhds (show π 1 w = w by simp))
    exact ⟨K, ho, hK, fun k hk => h hk⟩
  choose K ho hK hw using hex
  have hinter : ∀ (L M : Subgroup G), IsCompact (L : Set G) → IsOpen (M : Set G) →
      IsCompact ((L ⊓ M : Subgroup G) : Set G) := fun L M hL hM =>
    hL.inter_right (M.isClosed_of_isOpen hM)
  let b : V → Y := fun w => (μ.real (K w) : ℂ)⁻¹ • B (cosetInd (K w) (ho w) (hK w) 1) w
  have hb : ∀ (L : Subgroup G) (ho' : IsOpen (L : Set G)) (hL : IsCompact (L : Set G)) (w : V),
      (∀ k ∈ L, π k w = w) → b w = (μ.real L : ℂ)⁻¹ • B (cosetInd L ho' hL 1) w := by
    intro L ho' hL w h
    have h1 : IsOpen ((L ⊓ K w : Subgroup G) : Set G) := ho'.inter (ho w)
    have h2 := hinter L (K w) hL (ho w)
    exact (hle _ _ _ _ h1 h2 inf_le_right w (hw w)).trans (hle _ _ _ _ h1 h2 inf_le_left w h).symm
  refine ⟨⟨⟨b, fun v w => ?_⟩, fun c v => ?_⟩, fun φ v => ?_⟩
  · have h1 : IsOpen ((K v ⊓ K w : Subgroup G) : Set G) := (ho v).inter (ho w)
    have h2 := hinter (K v) (K w) (hK v) (ho w)
    rw [hb _ h1 h2 v fun k hk => hw v k hk.1, hb _ h1 h2 w fun k hk => hw w k hk.2,
      hb _ h1 h2 (v + w) fun k hk => by rw [map_add, hw v k hk.1, hw w k hk.2], map_add, smul_add]
  · show b (c • v) = c • b v
    rw [hb _ (ho v) (hK v) (c • v) fun k hk => by rw [map_smul, hw v k hk], map_smul, smul_comm]
  · show _ = b _
    obtain ⟨L, ho', hL, h⟩ := hG _ ((isOpen_leftStabilizer φ.2.1 φ.2.2).mem_nhds (one_mem _))
    have hφ : ∀ k ∈ L, ∀ g, φ.1 (k * g) = φ.1 g := fun k hk => h hk
    rw [hb L ho' hL _ (mem_fixed.1 (hπ.smoothOp_mem_fixed φ.2.1 φ.2.2 hφ v)),
      key hπ B hB L ho' hL φ hφ, inv_smul_smul₀ (hpos L ho' hL)]

end GlobalTheory.InvBilinTest
