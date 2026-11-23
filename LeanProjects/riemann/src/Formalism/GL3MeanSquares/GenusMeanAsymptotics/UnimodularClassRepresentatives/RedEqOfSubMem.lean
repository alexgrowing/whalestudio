import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteRepSetOfOrtho

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinG

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

def red (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    ↥(locF 𝔭 (spanO b)) →ₗ[𝓞 K] (κ → 𝓞 K ⧸ extP K 𝔭 ^ k) :=
  (qE b (extP K 𝔭 ^ k)).toLinearMap ∘ₗ (quotLocF h𝔭 (spanO b) k).symm.toLinearMap ∘ₗ
    Submodule.mkQ _

theorem red_of_mem (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ)
    (w : ↥(locF 𝔭 (spanO b))) (hw : (w : V) ∈ spanO b) :
    red b h𝔭 k w = fun i => Ideal.Quotient.mk (extP K 𝔭 ^ k) (crd b ⟨w, hw⟩ i) := by
  have e : (quotLocF h𝔭 (spanO b) k).symm (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk ⟨(w : V), hw⟩ := by
    rw [LinearEquiv.symm_apply_eq, quotLocF_mk h𝔭 (spanO b) k ⟨(w : V), hw⟩ w.2]
  show qE b _ ((quotLocF h𝔭 (spanO b) k).symm (Submodule.Quotient.mk w)) = _
  rw [e, qE_mk]

theorem red_smul_one (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) {c : 𝓞 F}
    (hc : c - 1 ∈ 𝔭 ^ k) (w : ↥(locF 𝔭 (spanO b))) : red b h𝔭 k (ι c • w) = red b h𝔭 k w := by
  rw [map_smul]
  funext i
  rw [Pi.smul_apply, Algebra.smul_def]
  have : algebraMap (𝓞 K) (𝓞 K ⧸ extP K 𝔭 ^ k) (ι c) = 1 := by
    show Ideal.Quotient.mk _ (ι c) = 1
    rw [← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ k)), Ideal.Quotient.eq, ← map_one ι, ← map_sub]
    exact ι_mem_pow hc
  rw [this, one_mul]

theorem red_eq_of_sub_mem (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ)
    (w w' : ↥(locF 𝔭 (spanO b)))
    (hww : (w : V) - w' ∈ (extP K 𝔭 ^ k • locF 𝔭 (spanO b) : Submodule (𝓞 K) V)) :
    red b h𝔭 k w = red b h𝔭 k w' := by
  have e : (Submodule.Quotient.mk w : ↥(locF 𝔭 (spanO b)) ⧸
      ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 (spanO b)))) = Submodule.Quotient.mk w' := by
    rw [Submodule.Quotient.eq, Submodule.mem_smul_top_iff]
    exact hww
  show qE b _ ((quotLocF h𝔭 (spanO b) k).symm (Submodule.Quotient.mk w)) =
    qE b _ ((quotLocF h𝔭 (spanO b) k).symm (Submodule.Quotient.mk w'))
  rw [e]

def bM (b : Basis κ K V) (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (j : κ) : ↥(locF 𝔭 (spanO b)) :=
  ⟨b j, le_locF 𝔭 _ (Submodule.subset_span (Set.mem_range_self j))⟩

theorem red_bM (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) [𝔭.IsPrime] (k : ℕ) (j : κ) :
    red b h𝔭 k (bM b 𝔭 j) = Pi.single j 1 := by
  have e : (quotLocF h𝔭 (spanO b) k).symm (Submodule.Quotient.mk (bM b 𝔭 j)) =
      Submodule.Quotient.mk (bO b j) := by
    rw [LinearEquiv.symm_apply_eq, quotLocF_mk h𝔭 (spanO b) k (bO b j)
      (by rw [bO_apply]; exact (bM b 𝔭 j).2)]
    congr 1
    apply Subtype.ext
    exact (bO_apply b j).symm
  show qE b _ ((quotLocF h𝔭 (spanO b) k).symm (Submodule.Quotient.mk (bM b 𝔭 j))) = _
  rw [e, qE_bO]

variable [Fact (IsFixF K F)]

theorem red_form (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, algebraMap (𝓞 K) K (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (k : ℕ) (w w' : ↥(locF 𝔭 (spanO b))) {z : 𝓞 K} (hz : h (w : V) (w' : V) = algebraMap (𝓞 K) K z) :
    star (red b h𝔭 k w) ⬝ᵥ (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *ᵥ red b h𝔭 k w') =
      Ideal.Quotient.mk (extP K 𝔭 ^ k) z := by
  have hF : IsFixF K F := Fact.out
  obtain ⟨c, hc, hcw⟩ := exists_approx h𝔭 (spanO b) k w.2
  obtain ⟨c', hc', hcw'⟩ := exists_approx h𝔭 (spanO b) k w'.2
  rw [← red_smul_one b h𝔭 k hc w, ← red_smul_one b h𝔭 k hc' w',
    red_of_mem b h𝔭 k (ι c • w) hcw, red_of_mem b h𝔭 k (ι c' • w') hcw', ← mk_form]
  have e1 := form_eq h b hH ⟨_, hcw⟩ ⟨_, hcw'⟩
  have e2 : h (ι c • (w : V)) (ι c' • (w' : V)) = algebraMap (𝓞 K) K (ι (c * c') * z) := by
    rw [form_smul hF, hz, map_mul (algebraMap (𝓞 K) K)]
  have e3 := FaithfulSMul.algebraMap_injective (𝓞 K) K (e1.symm.trans e2)
  have e4 : Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι (c * c')) = 1 := by
    rw [← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ k)), Ideal.Quotient.eq, ← map_one ι, ← map_sub]
    apply ι_mem_pow
    have : c * c' - 1 = (c - 1) * c' + (c' - 1) := by ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ hc) hc'
  calc _ = Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι (c * c') * z) := congrArg _ e3
    _ = _ := by rw [map_mul, e4, one_mul]

omit [Fact (IsFixF K F)] in
theorem map_mem {h : V →ₗ⋆[K] V →ₗ[K] K} {M : Submodule (𝓞 K) V} {g : V ≃ₗ[K] V}
    (hg : g ∈ autSub h M) {x : V} (hx : x ∈ M) : g x ∈ M := by
  have h2 : Formalism.HermitianLatticesTheory.gmap g M = M := hg.2
  rw [← h2]
  exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

def gM {h : V →ₗ⋆[K] V →ₗ[K] K} {M : Submodule (𝓞 K) V} {g : V ≃ₗ[K] V} (hg : g ∈ autSub h M) :
    ↥M →ₗ[𝓞 K] ↥M :=
  ((g : V →ₗ[K] V).restrictScalars (𝓞 K)).restrict fun _ hx => map_mem hg hx

def gMat {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    [𝔭.IsPrime] (k : ℕ) {g : V ≃ₗ[K] V} (hg : g ∈ autSub h (locF 𝔭 (spanO b))) :
    Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  Matrix.of fun i j => red b h𝔭 k (gM hg (bM b 𝔭 j)) i

omit [Fact (IsFixF K F)] in
theorem red_gM {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    [𝔭.IsPrime] (k : ℕ) {g : V ≃ₗ[K] V} (hg : g ∈ autSub h (locF 𝔭 (spanO b)))
    (w : ↥(locF 𝔭 (spanO b))) : red b h𝔭 k (gM hg w) = gMat b h𝔭 k hg *ᵥ red b h𝔭 k w := by
  have key : (red b h𝔭 k ∘ₗ gM hg) ∘ₗ Submodule.inclusion (le_locF 𝔭 (spanO b)) =
      (((gMat b h𝔭 k hg).mulVecLin.restrictScalars (𝓞 K)) ∘ₗ red b h𝔭 k) ∘ₗ
        Submodule.inclusion (le_locF 𝔭 (spanO b)) := by
    apply (bO b).ext
    intro j
    have e : Submodule.inclusion (le_locF 𝔭 (spanO b)) (bO b j) = bM b 𝔭 j := by
      apply Subtype.ext
      exact bO_apply b j
    simp only [LinearMap.comp_apply, e, LinearMap.restrictScalars_apply, mulVecLin_apply]
    rw [red_bM, mulVec_single_one]
    rfl
  obtain ⟨c, hc, hcw⟩ := exists_approx h𝔭 (spanO b) k w.2
  have h1 := LinearMap.congr_fun key ⟨_, hcw⟩
  have e : Submodule.inclusion (le_locF 𝔭 (spanO b)) ⟨_, hcw⟩ = ι c • w := rfl
  simp only [LinearMap.comp_apply, e, LinearMap.restrictScalars_apply, mulVecLin_apply] at h1
  rw [map_smul, red_smul_one b h𝔭 k hc, red_smul_one b h𝔭 k hc] at h1
  exact h1

theorem exists_matrix (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, algebraMap (𝓞 K) K (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (k : ℕ) {g : V ≃ₗ[K] V} (hg : g ∈ autSub h (locF 𝔭 (spanO b))) :
    ∃ G G' : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k),
      Gᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) * G = H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) ∧
      G * G' = 1 ∧ ∀ w w' : ↥(locF 𝔭 (spanO b)), (w' : V) = g w →
        red b h𝔭 k w' = G *ᵥ red b h𝔭 k w := by
  have := h𝔭.isPrime
  have hg' : g⁻¹ ∈ autSub h (locF 𝔭 (spanO b)) := inv_mem hg
  refine ⟨gMat b h𝔭 k hg, gMat b h𝔭 k hg', ?_, ?_, ?_⟩
  · ext i j
    rw [← form_single (_ᴴ * _ * _) i j, ← form_mulVec, ← red_bM b h𝔭 k i, ← red_bM b h𝔭 k j,
      ← red_gM, ← red_gM, Matrix.map_apply]
    apply red_form h b hH h𝔭 k
    show h (g (b i)) (g (b j)) = _
    rw [hg.1 (b i) (b j), hH]
  · ext i j
    have h1 : (gMat b h𝔭 k hg * gMat b h𝔭 k hg') *ᵥ Pi.single j 1 = Pi.single j 1 := by
      rw [← mulVec_mulVec, ← red_bM b h𝔭 k j, ← red_gM, ← red_gM]
      congr 1
      apply Subtype.ext
      show g (g⁻¹ (b j)) = b j
      exact g.apply_symm_apply (b j)
    have h2 := congrFun h1 i
    rw [mulVec_single_one] at h2
    rw [Matrix.one_apply, ← Pi.single_apply]
    exact h2
  · intro w w' hww
    rw [← red_gM]
    congr 1
    apply Subtype.ext
    exact hww

end Formalism.HermitianLattices.Ext.L3.PinG
