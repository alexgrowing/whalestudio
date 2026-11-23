import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousLatticeVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartExponentialToroidalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicLatticeBasisPunctPolydiscCoverPStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelsIsHolomorphicLatticeFamilyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealIndependentBasisLatticeFamilyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelLatticeRiemannFormOffBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CubicalWeilPairingTorsionConstHolomorphicFamilyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsToricTorsionCubicalWeilOneComplexPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCountThroughExponentialLatticeKernelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDifferentiableOnTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisRealBasisOfHolomorphicFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChangeStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj

set_option autoImplicit false

noncomputable section

open GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix

namespace GlobalTheory.ShFam.BdArc.ArcLat

section Exp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem isExpAt_of_deriv {X : Scheme.{0}} (t : SAB H X) (y : Sp ℂ ⟶ X) {g : ℕ} (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G))
    (hadd : ∀ z w, e (z + w) = e z * e w)
    (h1 : ∀ w, ∃! v : ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsPt y ⟶ t.G, IsDerivAt0 (fun z => (e z).left) w v.left)
    (h2 : ∀ v : ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsPt y ⟶ t.G,
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) : IsExpAt t y e := by
  have h0 : e 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have hl : (e 0).left = (1 : Over.mk y ⟶ t.G).left := by rw [h0]
  refine ⟨hadd, fun w => ?_, fun v hv => ?_⟩
  · obtain ⟨v, hv, hu⟩ := h1 w
    refine ⟨v.left, ⟨⟨Over.w v, hv.1.trans hl⟩, hv⟩, fun v' hv' => ?_⟩
    have := hu (Over.homMk v' hv'.1.1) hv'.2
    rw [← this]
    rfl
  · exact h2 (Over.homMk v hv.1) (hv.2.trans hl.symm)

end Exp

theorem real_basis_of_int_basis {n g r : ℕ} {B : Set (Fin n → ℂ)} {K : (Fin n → ℂ) → Set (Fin g → ℂ)}
    (hK : IsLatFam B K) {b₀ : Fin n → ℂ} (hb₀ : b₀ ∈ B) (hsp : Submodule.span ℝ (K b₀) = ⊤)
    {lam : Fin r → Fin g → ℂ} (hli : LinearIndependent ℤ lam)
    (hiff : ∀ w, w ∈ K b₀ ↔ ∃ k : Fin r → ℤ, w = ∑ j, k j • lam j) :
    LinearIndependent ℝ lam ∧ Submodule.span ℝ (Set.range lam) = ⊤ :=
  GlobalTheory.T.latticeBasis_realBasis_of_holomorphic_family n g r B K b₀ lam hK hb₀ hsp hli hiff

section Exp2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem isExpAt_mulVec {X : Scheme.{0}} (t : SAB H X) (y : Sp ℂ ⟶ X) {g : ℕ} (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G))
    {M : Matrix (Fin g) (Fin g) ℂ} (hM : IsUnit M.det) (hh : IsHolTo Set.univ fun z => (e z).left)
    (he : IsExpAt t y e) : IsExpAt t y fun w => e (M *ᵥ w) :=
  GlobalTheory.T.isExponentialOfSemiAbelianFibre_linearChange E H X t y g e M hM hh he

end Exp2

theorem norm_mulVec_le {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℂ) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ i j, ‖M i j‖ ≤ D) : ‖M *ᵥ v‖ ≤ g * D * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  calc ‖∑ j, M i j * v j‖ ≤ ∑ j, ‖M i j * v j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin g, D * ‖v‖ := Finset.sum_le_sum fun j _ => by
        rw [norm_mul]
        exact mul_le_mul (hD i j) (norm_le_pi_norm v j) (norm_nonneg _) hD0
    _ = g * D * ‖v‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

section Main
set_option maxHeartbeats 1000000 in

theorem exists_continuous_latBasis_of_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (g' : ℕ) (ρ : ℝ) (e' : ∀ u, (Fin g' → ℂ) → (Over.mk (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G)), GoodEmb c σ → 1 ≤ Dw.p + Dw.q → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ∀ s, (spMap (ψ u) ≫ x) s ∉ genBd Z) → 0 < ρ → ρ ≤ r → IsHolTo (Metric.ball (0 : ℂ) ρ ×ˢ Set.univ) (fun q : ℂ × (Fin g' → ℂ) => (show Sp ℂ ⟶ Z.t.G.left from (e' q.1 q.2).left)) → (∀ u ∈ Metric.ball (0 : ℂ) ρ, (∀ z w, e' u (z + w) = e' u z * e' u w) ∧ Function.Surjective (e' u) ∧ IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ Z.t.G.left from (e' u z).left)) ∧ (∀ w, ∃! v : epsPt (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G, IsDerivAt0 (fun z => (e' u z).left) w v.left) ∧ (∀ v : epsPt (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' u 0).left → ∃! w, IsDerivAt0 (fun z => (e' u z).left) w v.left)) → ∃ (ρ₀ : ℝ) (m : ℕ) (lamE : ℂ → Fin m → Fin g' → ℂ), 0 < ρ₀ ∧ ρ₀ < ρ ∧ ContinuousOn lamE {s : ℂ | s.re < 0} ∧ (∀ s : ℂ, s.re < 0 → LinearIndependent ℝ (lamE s) ∧ Submodule.span ℝ (Set.range (lamE s)) = ⊤ ∧ ∀ z, e' ((ρ₀ : ℂ) * Complex.exp s) z = 1 ↔ ∃ n : Fin m → ℤ, z = ∑ j, n j • lamE s j) ∧ ∃ (C : ℝ) (k : ℕ), ∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ Real.pi → ‖lamE s‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ A _ φ x ψ r g' ρ e' hσ hpq harc hinner hρ hρr hhol hfive
  have hExp : ∀ u ∈ Metric.ball (0 : ℂ) ρ, IsExpAt Z.t (spMap (ψ u) ≫ x ≫ genι Z) (e' u) := fun u hu =>
    isExpAt_of_deriv Z.t _ (e' u) (hfive u hu).1 (hfive u hu).2.2.2.1 (hfive u hu).2.2.2.2
  have hnorm1 : ∀ b : Fin 1 → ℂ, ‖b 0‖ = ‖b‖ := fun b => by
    have hb : b = fun _ => b 0 := funext fun i => by rw [Subsingleton.elim i 0]
    conv_rhs => rw [hb]
    exact (pi_norm_const (b 0)).symm
  have hB1 : ∀ b ∈ Metric.ball (0 : Fin 1 → ℂ) ρ, b 0 ∈ Metric.ball (0 : ℂ) ρ := fun b hb => by
    rw [mem_ball_zero_iff] at hb ⊢
    rwa [hnorm1]
  have hd1 : Differentiable ℂ (fun q : (Fin 1 → ℂ) × (Fin g' → ℂ) => q.1 0) := by fun_prop
  have hdφ : DifferentiableOn ℂ (fun q : (Fin 1 → ℂ) × (Fin g' → ℂ) => (q.1 0, q.2)) Set.univ :=
    hd1.differentiableOn.prodMk differentiableOn_snd
  have hhol1 := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun q : (Fin 1 → ℂ) × (Fin g' → ℂ) => (q.1 0, q.2)) hhol
      (Metric.isOpen_ball.prod isOpen_univ) (hdφ.mono (Set.subset_univ _))
      fun q hq => Set.mk_mem_prod (hB1 _ hq.1) (Set.mem_univ _)
  dsimp only at hhol1
  have hLF1 : IsLatFam (Metric.ball (0 : Fin 1 → ℂ) ρ) (fun b => {w | e' (b 0) w = 1}) :=
    GlobalTheory.T.exponentialKernels_isHolomorphicLatticeFamily E H Z.X Z.t 1 g' (Metric.ball (0 : Fin 1 → ℂ) ρ) (fun b => spMap (ψ (b 0)) ≫ x ≫ genι Z) (fun b => e' (b 0))
      Metric.isOpen_ball hhol1 fun b hb => hExp _ (hB1 b hb)
  have h00 : (0 : Fin 1 → ℂ) ∈ Metric.ball (0 : Fin 1 → ℂ) ρ := Metric.mem_ball_self hρ
  have h0c : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball_self hρ
  obtain ⟨r₀, b, hb⟩ := GlobalTheory.T.exists_real_independent_basis_lattice_family 1 g' _ _ 0 hLF1 h00
  have hspan : Submodule.span ℂ {w | e' ((0 : Fin 1 → ℂ) 0) w = 1} = ⊤ :=
    span_of_isExpAt Z.t _ (e' 0) (hfive 0 h0c).2.1 (hfive 0 h0c).2.2.1 (hExp 0 h0c)
  obtain ⟨κ, hκ⟩ := exists_frame hb hspan
  obtain ⟨ρ₂, ζ, hρ₂, hle, hζ0, han, hz⟩ := GlobalTheory.ShFam.Hor.LogCh.exists_sections hρ hLF1 hb κ hκ
  have hle' : ρ₂ < ρ := by linarith
  have hsm : ∀ z : Fin 1 → ℂ, (ρ₂ • z) 0 = (ρ₂ : ℂ) * z 0 := fun z => by
    simp [Complex.real_smul]
  have hsc : ∀ z ∈ Metric.ball (0 : Fin 1 → ℂ) 1, ρ₂ • z ∈ Metric.ball (0 : Fin 1 → ℂ) (2 * ρ₂) := fun z hzb => by
    have h1 := smul_mem_ball hρ₂ hzb
    rw [_root_.one_mul] at h1
    exact Metric.ball_subset_ball (by linarith) h1
  have hdet : ∀ z ∈ Metric.ball (0 : Fin 1 → ℂ) (2 * ρ₂), IsUnit (colMat κ (ζ z)).det := fun z hz' => (hz z hz').2.2
  have hU : ∀ z ∈ Metric.ball (0 : Fin 1 → ℂ) 1, (ρ₂ : ℂ) * z 0 ∈ Metric.ball (0 : ℂ) ρ := fun z hzb => by
    rw [← hsm]
    exact hB1 _ (Metric.ball_subset_ball hle (hsc z hzb))
  let M : (Fin 1 → ℂ) → Matrix (Fin g') (Fin g') ℂ := fun z => colMat κ (ζ (ρ₂ • z))
  let exN : ∀ z : Fin 1 → ℂ, (Fin g' → ℂ) → (Over.mk (spMap (ψ ((ρ₂ : ℂ) * z 0)) ≫ x ≫ genι Z) ⟶ Z.t.G) :=
    fun z w => e' ((ρ₂ : ℂ) * z 0) (M z *ᵥ w)
  have hMdet : ∀ z ∈ Metric.ball (0 : Fin 1 → ℂ) 1, IsUnit (M z).det := fun z hzb => hdet _ (hsc z hzb)
  have hExpN : ∀ z ∈ Metric.ball (0 : Fin 1 → ℂ) 1, IsExpAt Z.t _ (exN z) := fun z hzb =>
    isExpAt_mulVec Z.t _ (e' _) (hMdet z hzb) (hfive _ (hU z hzb)).2.2.1 (hExp _ (hU z hzb))
  have hzeroN : ∀ z ∈ Metric.ball (0 : Fin 1 → ℂ) 1, exN z 0 = 1 := fun z hzb => by
    have h := (hExpN z hzb).1 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have hζd : DifferentiableOn ℂ (fun q : (Fin 1 → ℂ) × (Fin g' → ℂ) => ζ (ρ₂ • q.1)) (Metric.ball 0 1 ×ˢ Set.univ) :=
    han.differentiableOn.comp (by fun_prop : Differentiable ℂ fun q : (Fin 1 → ℂ) × (Fin g' → ℂ) => ρ₂ • q.1).differentiableOn
      fun q hq => hsc q.1 hq.1
  have hMv : DifferentiableOn ℂ (fun q : (Fin 1 → ℂ) × (Fin g' → ℂ) => M q.1 *ᵥ q.2) (Metric.ball 0 1 ×ˢ Set.univ) := by
    refine differentiableOn_pi.2 fun i => ?_
    simp only [M, colMat, Matrix.mulVec, dotProduct, Matrix.of_apply]
    refine DifferentiableOn.fun_sum fun j _ => DifferentiableOn.mul ?_ ?_
    · exact differentiableOn_pi.1 (differentiableOn_pi.1 hζd (κ j)) i
    · exact (by fun_prop : Differentiable ℂ fun q : (Fin 1 → ℂ) × (Fin g' → ℂ) => q.2 j).differentiableOn
  have hd2 : Differentiable ℂ (fun q : (Fin 1 → ℂ) × (Fin g' → ℂ) => (ρ₂ : ℂ) * q.1 0) := by fun_prop
  have hholN := GlobalTheory.HolPeriods.isHolTo_comp
    (φ := fun q : (Fin 1 → ℂ) × (Fin g' → ℂ) => ((ρ₂ : ℂ) * q.1 0, M q.1 *ᵥ q.2)) hhol
    (Metric.isOpen_ball.prod isOpen_univ) (hd2.differentiableOn.prodMk hMv)
    fun q hq => Set.mk_mem_prod (hU _ hq.1) (Set.mem_univ _)
  dsimp only at hholN
  have hLF := GlobalTheory.T.exponentialKernels_isHolomorphicLatticeFamily E H Z.X Z.t 1 g' (Metric.ball 0 1) (fun z => spMap (ψ ((ρ₂ : ℂ) * z 0)) ≫ x ≫ genι Z) exN
    Metric.isOpen_ball hholN hExpN
  have hsliceN : ∀ z ∈ Metric.ball (0 : Fin 1 → ℂ) 1, IsHolTo Set.univ (fun w => (exN z w).left) := fun z hzb => by
    have h := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun w : Fin g' → ℂ => M z *ᵥ w) (hfive _ (hU z hzb)).2.2.1 isOpen_univ
      (Matrix.mulVecLin (M z)).toContinuousLinearMap.differentiable.differentiableOn (Set.mapsTo_univ _ _)
    exact h
  have hmem0 : (0 : Fin 1 → ℂ) ∈ Metric.ball (0 : Fin 1 → ℂ) 1 := Metric.mem_ball_self one_pos
  let K : (Fin 1 → ℂ) → Set (Fin g' → ℂ) := fun z => {w | exN z w = 1}
  let ζ' := frameSec ρ₂ κ ζ
  let Pair : ℕ → (Fin 1 → ℂ) → (Fin g' → ℂ) → (Fin g' → ℂ) → ℂˣ → Prop := fun N z v w c =>
    GlobalTheory.UU.CubWeil Z.t.cub N (exN z ((N : ℂ)⁻¹ • v)) (exN z ((N : ℂ)⁻¹ • w)) (unitOn c)
  have hζan : AnalyticOnNhd ℂ ζ' (Metric.ball 0 1) :=
    (analyticOnNhd_frameSec hρ₂ κ han hdet).mono (Metric.ball_subset_ball (by norm_num))
  have hζli : ∀ z ∈ Metric.ball (0 : Fin 1 → ℂ) 1, LinearIndependent ℝ (ζ' z) := fun z hzb =>
    linearIndependent_inv_mulVec (hMdet z hzb) (hz _ (hsc z hzb)).2.1
  have hζK : ∀ z ∈ Metric.ball (0 : Fin 1 → ℂ) 1, ∀ i, ζ' z i ∈ K z := fun z hzb i => by
    show e' _ (M z *ᵥ ((colMat κ (ζ (ρ₂ • z)))⁻¹ *ᵥ ζ (ρ₂ • z) i)) = 1
    rw [mulVec_mulVec_inv (hMdet z hzb), ← hsm]
    exact (hz _ (hsc z hzb)).1 i
  have h0' : (ρ₂ : ℂ) * (0 : Fin 1 → ℂ) 0 = 0 := by simp
  have hB0 : IsLatBasis (K 0) (ζ' 0) := by
    have h1 : ζ' 0 = fun i => (colMat κ (ζ 0))⁻¹ *ᵥ ζ 0 i := by
      funext i
      simp [ζ', frameSec]
    rw [h1]
    refine IsLatBasis.inv_mulVec (hdet 0 (Metric.mem_ball_self (by linarith))) (hζ0 ▸ hb) fun w => ?_
    show e' _ (M 0 *ᵥ w) = 1 ↔ e' ((0 : Fin 1 → ℂ) 0) (colMat κ (ζ 0) *ᵥ w) = 1
    have hM0 : M 0 = colMat κ (ζ 0) := by simp [M]
    rw [hM0, h0']
    rfl
  have hζC : ∃ C : ℝ, ∀ z ∈ Metric.ball (0 : Fin 1 → ℂ) 1, ‖ζ' z‖ ≤ C := exists_bound_frameSec hρ₂ κ han hdet
  have hζstd : ∀ j : Fin g', ∃ i, ∀ z ∈ Metric.ball (0 : Fin 1 → ℂ) 1, ζ' z i = Pi.single j 1 := fun j =>
    ⟨κ j, fun z hzb => frameSec_single κ (hdet _ (hsc z hzb)) j⟩
  have hP1 : ∀ N z v w c c', Pair N z v w c → Pair N z v w c' → c = c' := fun N z v w c c' h h' =>
    unitOn_injective (h.unique h')
  have hP2 : ∀ (m N : ℕ) (B : Set (Fin m → ℂ)) (φ' : (Fin m → ℂ) → Fin 1 → ℂ) (v w : (Fin m → ℂ) → Fin g' → ℂ)
      (c : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → DifferentiableOn ℂ φ' B →
      Set.MapsTo φ' B (Metric.ball 0 1) → DifferentiableOn ℂ v B → DifferentiableOn ℂ w B →
      (∀ b ∈ B, v b ∈ K (φ' b) ∧ w b ∈ K (φ' b)) → b₀ ∈ B → b₁ ∈ B →
      Pair N (φ' b₀) (v b₀) (w b₀) c → Pair N (φ' b₁) (v b₁) (w b₁) c := by
    intro m N B φ' v w c b₀ b₁ hN hB hBc hφ hφm hv hw hK hb₀ hb₁ h
    have h1 := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun b => (φ' b, (N : ℂ)⁻¹ • v b)) hholN hB
      (hφ.prodMk ((differentiableOn_const ((N : ℂ)⁻¹)).smul hv)) fun b hb => Set.mk_mem_prod (hφm hb) (Set.mem_univ _)
    have h2 := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun b => (φ' b, (N : ℂ)⁻¹ • w b)) hholN hB
      (hφ.prodMk ((differentiableOn_const ((N : ℂ)⁻¹)).smul hw)) fun b hb => Set.mk_mem_prod (hφm hb) (Set.mem_univ _)
    dsimp only at h1 h2
    exact GlobalTheory.T.cubicalWeilPairing_torsion_const_holomorphic_family Z.X Z.t.G Z.t.PP Z.t.cub m N B (fun b => spMap (ψ ((ρ₂ : ℂ) * φ' b 0)) ≫ x ≫ genι Z)
      (fun b => exN (φ' b) ((N : ℂ)⁻¹ • v b)) (fun b => exN (φ' b) ((N : ℂ)⁻¹ • w b)) c b₀ b₁ hN hB hBc h1 h2
      (fun b hb => ⟨pow_eq_one_of_map _ (hExpN _ (hφm hb)).1 (hzeroN _ (hφm hb)) hN (hK b hb).1,
        pow_eq_one_of_map _ (hExpN _ (hφm hb)).1 (hzeroN _ (hφm hb)) hN (hK b hb).2⟩) hb₀ hb₁ h
  have hP3 : ∀ z ∈ Metric.ball (0 : Fin 1 → ℂ) 1, (∀ k : Fin 1, (k : ℕ) < 1 → z k ≠ 0) →
      ∃ Hm : Matrix (Fin g') (Fin g') ℂ, Hm.IsHermitian ∧ (∀ u : Fin g' → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧
        Submodule.span ℝ (K z) = ⊤ ∧ (∀ v ∈ K z, ∀ w ∈ K z, ∃ m : ℤ, (hermForm Hm v w).im = m) ∧
        ∀ (N : ℕ) (v w : Fin g' → ℂ), 0 < N → v ∈ K z → w ∈ K z →
          Pair N z v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N))
            (Complex.exp_ne_zero _)) := by
    intro z hzb hnz
    have hu0 : (ρ₂ : ℂ) * z 0 ≠ 0 := mul_ne_zero (by exact_mod_cast hρ₂.ne') (hnz 0 (by decide))
    have hur : (ρ₂ : ℂ) * z 0 ∈ Metric.ball (0 : ℂ) r := Metric.ball_subset_ball hρr (hU z hzb)
    have hpt : (spMap (ψ ((ρ₂ : ℂ) * z 0)) ≫ x) ≫ genStr Z = spMap σ := by
      rw [Category.assoc, harc.2.1, ← harc.2.2 _ hur]
      simp only [spMap, ← Spec.map_comp]
      rfl
    let xp : CxPts (genStr Z) σ := ⟨spMap (ψ ((ρ₂ : ℂ) * z 0)) ≫ x, hpt⟩
    have hin := hinner _ hur hu0 (IsLocalRing.closedPoint ℂ)
    obtain ⟨Hm, hH, hpos, hspan, hint, hw⟩ := GlobalTheory.T.exponentialKernel_lattice_riemannForm_off_boundary E H Dw l Xo c O β Z σ g' xp (exN z) hσ hpq hin
      (hExpN z hzb) (hsliceN z hzb)
    exact ⟨Hm, hH, hpos, hspan, fun v hv w hw' => hint v w hv hw', fun N v w hN hv hw' => hw N v w _ hN hv hw' rfl⟩
  have hP4 : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g') ∧
      ∀ a a' : Fin r₀ → ℤ, (fun j => (a j : ZMod N)) ∈ S → Pair N 0 (∑ j, a j • ζ' 0 j) (∑ j, a' j • ζ' 0 j) 1 := by
    intro N hN
    have hsurj : Function.Surjective (exN 0) := fun p => by
      obtain ⟨w, hw⟩ := (hfive _ (hU 0 hmem0)).2.1 p
      refine ⟨(M 0)⁻¹ *ᵥ w, ?_⟩
      show e' _ (M 0 *ᵥ ((M 0)⁻¹ *ᵥ w)) = p
      rw [mulVec_mulVec_inv (hMdet 0 hmem0)]
      exact hw
    obtain ⟨Tt, hT1, hT2, hTc⟩ := GlobalTheory.T.exists_toricTorsion_cubicalWeil_one_complexPoint E H Z.X Z.t _ g' N (exN 0) hN (hExpN 0 hmem0) hsurj (hsliceN 0 hmem0)
    obtain ⟨S, hSc, hS⟩ := GlobalTheory.T.torsion_count_through_exponential_lattice_kernel _ g' r₀ N (exN 0) (ζ' 0) Tt hN (hExpN 0 hmem0).1 hsurj hB0 hT1 hTc
    refine ⟨S, hSc, fun a a' ha => ?_⟩
    show GlobalTheory.UU.CubWeil Z.t.cub N (exN 0 ((N : ℂ)⁻¹ • ∑ j, a j • ζ' 0 j)) (exN 0 ((N : ℂ)⁻¹ • ∑ j, a' j • ζ' 0 j))
      (unitOn 1)
    rw [unitOn_one]
    exact hT2 _ (hS a ha) _ (pow_eq_one_of_map _ (hExpN 0 hmem0).1 (hzeroN 0 hmem0) hN ((hB0.2 _).2 ⟨a', rfl⟩))
  obtain ⟨m, lam, ρc, hc, hs, hg⟩ :=
    GlobalTheory.T.exists_holomorphic_latticeBasis_punctPolydiscCover_polyGrowth 1 1 g' r₀ K ζ' Pair hLF hζan hζli hζK hB0 hζC hζstd hP1 hP2 hP3 hP4
  let sv : ℂ → Fin 1 → ℂ := fun s _ => s
  have hsv : ∀ s : ℂ, ‖sv s‖ = ‖s‖ := fun s => pi_norm_const s
  have hdom : ∀ s : ℂ, s.re < 0 → sv s ∈ GlobalTheory.ShFam.Hor.logDom 1 1 := fun s hsr k => by
    show if (k : ℕ) < 1 then (sv s k).re < 0 else ‖sv s k‖ < 1
    rw [if_pos k.isLt]
    exact hsr
  have hlogExp : ∀ s : ℂ, GlobalTheory.ShFam.Hor.logExp 1 (sv s) = sv (Complex.exp s) := fun s => funext fun k => by
    show (if (k : ℕ) < 1 then Complex.exp (sv s k) else sv s k) = Complex.exp s
    rw [if_pos k.isLt]
  have hexpball : ∀ s : ℂ, s.re < 0 → sv (Complex.exp s) ∈ Metric.ball (0 : Fin 1 → ℂ) 1 := fun s hsr => by
    rw [mem_ball_zero_iff, hsv, Complex.norm_exp]
    exact Real.exp_lt_one_iff.mpr hsr
  let lamE : ℂ → Fin m → Fin g' → ℂ := fun s j => M (sv (Complex.exp s)) *ᵥ lam (sv s) j
  refine ⟨ρ₂, m, lamE, hρ₂, hle', ?_, fun s hsr => ?_, ?_⟩
  · have hlamc : ContinuousOn (fun s : ℂ => lam (sv s)) {s : ℂ | s.re < 0} :=
      hc.comp (continuous_pi fun _ => continuous_id).continuousOn fun s hs => hdom s hs
    have hcol : Continuous fun f : Fin r₀ → Fin g' → ℂ => colMat κ f :=
      continuous_pi fun i => continuous_pi fun j => (continuous_apply i).comp (continuous_apply (κ j))
    have hsmc : Continuous fun s : ℂ => ρ₂ • sv (Complex.exp s) :=
      (continuous_pi fun _ => Complex.continuous_exp).const_smul ρ₂
    have hMc : ContinuousOn (fun s : ℂ => M (sv (Complex.exp s))) {s : ℂ | s.re < 0} :=
      hcol.comp_continuousOn (han.continuousOn.comp hsmc.continuousOn fun s hs => hsc _ (hexpball s hs))
    refine continuousOn_pi.2 fun j => continuousOn_pi.2 fun i => ?_
    simp only [lamE, Matrix.mulVec, dotProduct]
    refine continuousOn_finset_sum _ fun k _ => ContinuousOn.mul ?_ ?_
    · exact continuousOn_pi.1 (continuousOn_pi.1 hMc i) k
    · exact continuousOn_pi.1 (continuousOn_pi.1 hlamc j) k
  · have hzb := hexpball s hsr
    obtain ⟨hli, hiff, -⟩ := hs (sv s) (hdom s hsr)
    rw [hlogExp] at hiff
    obtain ⟨-, -, -, hspanK, -, -⟩ := hP3 _ hzb fun k _ => Complex.exp_ne_zero s
    have rb := real_basis_of_int_basis hLF hzb hspanK hli hiff
    have hbas : IsLatBasis (K (sv (Complex.exp s))) (lam (sv s)) := ⟨rb.1, hiff⟩
    have hinv := hMdet _ hzb
    have hM' : IsUnit ((M (sv (Complex.exp s)))⁻¹).det := Matrix.isUnit_nonsing_inv_det _ hinv
    have hb2 := IsLatBasis.inv_mulVec (K' := {w | e' ((ρ₂ : ℂ) * Complex.exp s) w = 1}) hM' hbas fun w => by
      show e' _ w = 1 ↔ e' _ (M (sv (Complex.exp s)) *ᵥ ((M (sv (Complex.exp s)))⁻¹ *ᵥ w)) = 1
      rw [mulVec_mulVec_inv hinv]
    rw [Matrix.nonsing_inv_nonsing_inv _ hinv] at hb2
    refine ⟨hb2.1, ?_, fun z => hb2.2 z⟩
    let f : (Fin g' → ℂ) →ₗ[ℝ] (Fin g' → ℂ) := (Matrix.mulVecLin (M (sv (Complex.exp s)))).restrictScalars ℝ
    have hrange : Set.range (lamE s) = f '' Set.range (lam (sv s)) := by
      rw [← Set.range_comp]
      rfl
    have hf : Function.Surjective f := fun v => ⟨(M (sv (Complex.exp s)))⁻¹ *ᵥ v, mulVec_mulVec_inv hinv v⟩
    rw [hrange, Submodule.span_image, rb.2, Submodule.map_top, LinearMap.range_eq_top.2 hf]
  · obtain ⟨C, k, hCk⟩ := hg
    obtain ⟨D, hD⟩ := (isCompact_closedBall (0 : Fin 1 → ℂ) ρ₂).exists_bound_of_continuousOn
      (han.continuousOn.mono (Metric.closedBall_subset_ball (by linarith)))
    have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0 (Metric.mem_closedBall_self hρ₂.le))
    have hMb : ∀ z ∈ Metric.ball (0 : Fin 1 → ℂ) 1, ∀ i j, ‖M z i j‖ ≤ D := fun z hzb i j => by
      have hzc : ρ₂ • z ∈ Metric.closedBall (0 : Fin 1 → ℂ) ρ₂ := by
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hρ₂]
        have := (mem_ball_zero_iff.1 hzb).le
        nlinarith
      have h1 : ‖M z i j‖ ≤ ‖ζ (ρ₂ • z) (κ j)‖ := norm_le_pi_norm (ζ (ρ₂ • z) (κ j)) i
      exact h1.trans ((norm_le_pi_norm (ζ (ρ₂ • z)) (κ j)).trans (hD _ hzc))
    refine ⟨g' * D * C, k, fun s hsr hs2 him => ?_⟩
    have hzb := hexpball s hsr
    have hl := hCk (sv s) (hdom s hsr) (by rw [hlogExp, hsv]; exact hs2) fun _ _ => him
    rw [hsv] at hl
    have hpos : 0 ≤ (g' : ℝ) * D := by positivity
    rw [mul_assoc ((g' : ℝ) * D) C]
    refine (pi_norm_le_iff_of_nonneg ((mul_nonneg hpos ((norm_nonneg _).trans hl)))).2 fun j => ?_
    calc ‖lamE s j‖ ≤ g' * D * ‖lam (sv s) j‖ := norm_mulVec_le _ _ hD0 (hMb _ hzb)
      _ ≤ g' * D * ‖lam (sv s)‖ := mul_le_mul_of_nonneg_left (norm_le_pi_norm _ j) hpos
      _ ≤ g' * D * (C * (1 + ‖s‖) ^ k) := mul_le_mul_of_nonneg_left hl hpos
end Main

end GlobalTheory.ShFam.BdArc.ArcLat
