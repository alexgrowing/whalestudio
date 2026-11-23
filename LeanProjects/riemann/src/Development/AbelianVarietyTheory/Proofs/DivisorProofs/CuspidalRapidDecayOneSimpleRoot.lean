import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import GroundTheory.AutomorphicForms.ReductionSiegel
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjFiniteUnipotentMemOpenSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalNormLeOfAlternatingSumScaledUnipFDStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReproducingIdentityExtendsHarishChandraSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOneAddOfSqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormToLMapPInfLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightLeOfIsCompactStatement
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff

noncomputable section
namespace GlobalTheory.HCF.Decay

theorem meanIter : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ), 0 < r → r < a →
    ∀ φ : GA E a → ℂ, (∀ γ g, φ (ratGL E a γ * g) = φ g) → IsCuspidal φ → Continuous φ →
    ∀ M : ℕ, 0 < M → ∀ (x : GA E a) (m : ℕ) (B : ℝ),
      (∀ y : Fin m → BlockIx a r → Ad E, (∀ i, y i ∈ GroundTheory.Automorphic.scaledUnipFD E a r M) →
        ‖∑ ε : Fin m → Bool, (GroundTheory.Automorphic.altSign ε : ℂ) * φ (unip (GroundTheory.Automorphic.altPoint y ε) * x)‖ ≤ B) →
      ‖φ x‖ ≤ B := GlobalTheory.T.cuspidal_norm_le_of_alternatingSum_scaledUnipFD

theorem reproSpan : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
    (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ) (β : Lie E a → ℂ),
    ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ invSet E a →
    (∀ φ ∈ formsGL E a L W X N, ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g) →
    ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g := GlobalTheory.T.reproducingIdentity_extends_harishChandraSpan

theorem diffInt : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (β : Lie E a → ℂ), ContDiff ℝ ∞ β →
    HasCompactSupport β → tsupport β ⊆ invSet E a → ∀ (m : ℕ) (R : ℝ), ∃ (c : ℝ) (Q : Set (Lie E a)),
    0 ≤ c ∧ IsCompact Q ∧ Q ⊆ invSet E a ∧ ∀ f : Lie E a → ℂ, ContinuousOn f (invSet E a) →
    ∀ F : ℝ, 0 ≤ F → (∀ w ∈ Q, ‖f w‖ ≤ F) →
    ∀ Y : Fin m → Matrix (Fin a) (Fin a) (Cinf E), (∀ i j, Y i * Y j = 0) → (∀ i, ‖toL (Y i)‖ ≤ R) →
    ‖∑ ε : Fin m → Bool, (GroundTheory.Automorphic.altSign ε : ℂ) *
        ∫ w, f (toL ((1 + GroundTheory.Automorphic.altPoint Y ε) * Matrix.of w)) * β w‖ ≤ c * F * ∏ i, ‖toL (Y i)‖ := GlobalTheory.T.norm_signed_sum_integral_le

theorem normTransfer : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ c : ℝ, 0 ≤ c ∧
    ∀ M : Matrix (Fin a) (Fin a) (Ad E),
      ‖toL (M.map (pInf E))‖ ≤ c * ‖GroundTheory.Automorphic.CuspidalSpectrum.archMat E a M‖ := GlobalTheory.T.norm_toL_map_pInf_le'

theorem heightBound : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Q : Set (Lie E a)),
    IsCompact Q → Q ⊆ invSet E a →
    ∃ H : ℝ, ∀ y : GL (Fin a) (Cinf E), toL y.val ∈ Q → GlobalTheory.CuspRep.height y ≤ H := GlobalTheory.T.height_bounded_of_toL_mem_isCompact

section Span
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {L : Subgroup (GL (Fin a) (Af E))}
  {W : Submodule ℂ (Kinf E a → ℂ)} {X : Set (Module.End ℂ (Sm E a) → ℂ)} {N : ℕ}

theorem span_left {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) :
    ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hx.1.left
  | zero => intro γ g; rfl
  | add x y _ _ hx hy => intro γ g; simp [hx γ g, hy γ g]
  | smul c x _ hx => intro γ g; simp [hx γ g]

theorem span_fin {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) :
    ∀ l ∈ L, finRep E a l φ = φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hx.2.1
  | zero => intro l _; exact map_zero _
  | add x y _ _ hx hy => intro l hl; rw [map_add, hx l hl, hy l hl]
  | smul c x _ hx => intro l hl; rw [map_smul, hx l hl]

theorem span_right {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) {l : GL (Fin a) (Af E)} (hl : l ∈ L)
    (g : GA E a) : φ.1 (g * finGL E a l) = φ.1 g :=
  congrFun (congrArg Subtype.val (span_fin hφ l hl)) g

theorem span_cont (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) {φ : Sm E a}
    (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) : Continuous φ.1 := by
  refine GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E a φ ?_
  refine isOpen_iff_forall_mem_open.2 fun k hk => ⟨(fun l => k * l) '' (L : Set (GL (Fin a) (Af E))), ?_, ?_, ⟨1, L.one_mem, mul_one k⟩⟩
  · rintro _ ⟨l, hl, rfl⟩
    change finRep E a (k * l) φ = φ
    rw [map_mul, Module.End.mul_apply, span_fin hφ l hl]
    exact hk
  · exact (Homeomorph.mulLeft k).isOpenMap _ hL

end Span

section Conj
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem nilM_add' {R : Type} [CommRing R] {r : ℕ} (x y : BlockIx a r → R) : nilM (x + y) = nilM x + nilM y := by
  ext i j; simp only [nilM, Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp

theorem nilM_zero' {R : Type} [CommRing R] {r : ℕ} : nilM (0 : BlockIx a r → R) = 0 := by
  ext i j; simp only [nilM, Matrix.of_apply, Matrix.zero_apply]; split_ifs <;> rfl

theorem map_unip' {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {r : ℕ} (P : BlockIx a r → R) :
    Matrix.GeneralLinearGroup.map f (unip P) = unip (fun p => f (P p)) := by
  ext i j
  change f ((1 + nilM P : Matrix (Fin a) (Fin a) R) i j) = (1 + nilM (fun p => f (P p)) : Matrix (Fin a) (Fin a) S) i j
  simp only [nilM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, map_add]
  split_ifs <;> simp

variable (E) in

def conjY {r : ℕ} (x : GA E a) : (BlockIx a r → Ad E) →+ Matrix (Fin a) (Fin a) (Cinf E) where
  toFun P := (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) * nilM P * (x : Matrix (Fin a) (Fin a) (Ad E))).map (pInf E)
  map_zero' := by simp [nilM_zero']
  map_add' P Q := by
    simp only [nilM_add', Matrix.mul_add, Matrix.add_mul]
    exact Matrix.map_add _ (map_add (pInf E)) _ _

theorem conjY_apply {r : ℕ} (x : GA E a) (P : BlockIx a r → Ad E) :
    conjY E x P = (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) * nilM P * (x : Matrix (Fin a) (Fin a) (Ad E))).map (pInf E) := rfl

theorem conjY_mul {r : ℕ} (x : GA E a) (P Q : BlockIx a r → Ad E) : conjY E x P * conjY E x Q = 0 := by
  rw [conjY_apply, conjY_apply, ← Matrix.map_mul]
  have : ((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) * nilM P * (x : Matrix (Fin a) (Fin a) (Ad E)) *
      (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) * nilM Q * (x : Matrix (Fin a) (Fin a) (Ad E))) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (x : Matrix (Fin a) (Fin a) (Ad E)), Units.mul_inv, Matrix.one_mul,
      ← Matrix.mul_assoc (nilM P), nilM_mul, Matrix.zero_mul, Matrix.mul_zero]
  rw [this]; simp

theorem conjY_truncInf {r : ℕ} (x : GA E a) (P : BlockIx a r → Ad E) :
    conjY E x (GroundTheory.Automorphic.CuspidalSpectrum.truncInf P) = conjY E x P := by
  rw [conjY_apply, conjY_apply, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
  congr 2
  ext i j
  simp only [nilM, Matrix.map_apply, Matrix.of_apply]
  split_ifs
  · rfl
  · simp

theorem conj_unip_eq {r : ℕ} (x : GA E a) (P : BlockIx a r → Ad E) (hP : ∀ p, (P p).2 = 0) :
    x⁻¹ * unip P * x = infGL E a (Matrix.GeneralLinearGroup.map (pInf E) (x⁻¹ * unip P * x)) := by
  refine ga_ext (by simp) ?_
  rw [pFin_infGL, map_mul, map_mul, map_unip', map_inv]
  have : (fun p => pFin E (P p)) = 0 := funext hP
  rw [this, show unip (0 : BlockIx a r → Af E) = 1 from Units.ext (by change 1 + nilM 0 = 1; rw [nilM_zero', add_zero]),
    mul_one, inv_mul_cancel]

theorem val_map_conj_unip {r : ℕ} (x : GA E a) (P : BlockIx a r → Ad E) :
    ((Matrix.GeneralLinearGroup.map (pInf E) (x⁻¹ * unip P * x) : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) =
      1 + conjY E x P := by
  rw [conjY_apply]
  change (((x⁻¹ * unip P * x : GA E a)) : Matrix (Fin a) (Fin a) (Ad E)).map (pInf E) = _
  rw [Units.val_mul, Units.val_mul]
  change ((((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) * (1 + nilM P)) * (x : Matrix (Fin a) (Fin a) (Ad E))).map (pInf E) = _
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul, Matrix.map_add _ (map_add (pInf E)),
    Matrix.map_one _ (map_zero (pInf E)) (map_one (pInf E))]

end Conj

theorem oneRoot (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
    (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ))
    (N : ℕ) (β : Lie E a → ℂ) (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β) (hβu : tsupport β ⊆ invSet E a)
    (hrep : ∀ φ ∈ formsGL E a L W X N, ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g)
    (φ : Sm E a) (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) (hcusp : IsCuspidal φ.1)
    (Ω : Set (GA E a)) (hΩ : IsCompact Ω) (hΩB : Ω ⊆ ((adelicBorel : Subgroup (GA E a)) : Set (GA E a)))
    (t C₀ : ℝ) (N₀ : ℕ) (ht : 0 < t)
    (hgrow : ∀ b ∈ Ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), ∀ k ∈ (maxCompact : Subgroup (GA E a)),
      ∀ y : GL (Fin a) (Cinf E), ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k * infGL E a y)‖ ≤
        C₀ * (∑ i, (r i + (r i)⁻¹)) ^ N₀ * GlobalTheory.CuspRep.height y ^ N₀)
    (m s : ℕ) (hs : 0 < s) (hsa : s < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ Ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) →
      ∀ k ∈ (maxCompact : Subgroup (GA E a)),
      ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k)‖ ≤
        C * (r ⟨s, hsa⟩ / r ⟨s - 1, by omega⟩) ^ m * (∑ i, (r i + (r i)⁻¹)) ^ N₀ := by
  classical
  obtain ⟨M, hM, hfin⟩ := GlobalTheory.T.exists_conj_finiteUnipotent_mem_openSubgroup E a s L hL Ω hΩ
  obtain ⟨C₁, hC₁⟩ := GroundTheory.Automorphic.CuspidalSpectrum.exists_norm_archMat_conj_le hΩ hΩB ht hs hsa
    (GroundTheory.Automorphic.isCompact_scaledInfSet (K := E) M)
  obtain ⟨cT, hcT0, hcT⟩ := normTransfer E a
  set K₁ := cT * max C₁ 0 with hK₁
  have hK₁0 : 0 ≤ K₁ := mul_nonneg hcT0 (le_max_right _ _)
  obtain ⟨c, Q, hc0, hQ, hQinv, hdiff⟩ := diffInt E a β hβ hβc hβu m (K₁ * t⁻¹)
  obtain ⟨H, hH⟩ := heightBound E a Q hQ hQinv
  set H' := max H 1 with hH'
  set C₀' := max C₀ 0 with hC₀'
  have hH'0 : 0 ≤ H' := le_trans zero_le_one (le_max_right _ _)
  have hC₀'0 : 0 ≤ C₀' := le_max_right _ _
  refine ⟨c * C₀' * H' ^ N₀ * K₁ ^ m, by positivity, ?_⟩
  intro b hb r hr hsieg k hk
  set x := b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k with hx
  set Sr := ∑ i, (r i + (r i)⁻¹) with hSr
  have hSr0 : 0 ≤ Sr := Finset.sum_nonneg fun i _ => add_nonneg (hr i).le (inv_nonneg.2 (hr i).le)
  set gain := r ⟨s, hsa⟩ / r ⟨s - 1, by omega⟩ with hgaindef
  have hgain0 : 0 ≤ gain := div_nonneg (hr _).le (hr _).le
  have hgain : gain ≤ t⁻¹ := by
    have h1 := hsieg ⟨s - 1, by omega⟩ ⟨s, hsa⟩ (by simp; omega)
    rw [hgaindef, div_le_iff₀ (hr _), ← div_eq_inv_mul, le_div_iff₀ ht, mul_comm]
    exact h1
  set f := chart φ.1 x with hf
  have hfc : ContinuousOn f (invSet E a) := (φ.2 x).continuousOn
  set F := C₀' * Sr ^ N₀ * H' ^ N₀ with hF
  have hF0 : 0 ≤ F := by positivity
  have hfQ : ∀ w ∈ Q, ‖f w‖ ≤ F := by
    intro w hw
    obtain ⟨u, hu⟩ := hQinv hw
    have hw' : w = toL u.val := by rw [hu]; rfl
    rw [hw'] at hw ⊢
    rw [hf, chart_val]
    have h1 := hgrow b hb r hr k hk u
    have h2 : GlobalTheory.CuspRep.height u ^ N₀ ≤ H' ^ N₀ :=
      pow_le_pow_left₀ (le_trans zero_le_one (one_le_height u)) ((hH u hw).trans (le_max_left _ _)) _
    calc ‖φ.1 (x * infGL E a u)‖ ≤ C₀ * Sr ^ N₀ * GlobalTheory.CuspRep.height u ^ N₀ := h1
      _ ≤ C₀' * Sr ^ N₀ * GlobalTheory.CuspRep.height u ^ N₀ := by
          gcongr
          · exact pow_nonneg (le_trans zero_le_one (one_le_height u)) _
          · exact le_max_left _ _
      _ ≤ F := by rw [hF]; gcongr
  refine meanIter E a s hs hsa φ.1 (span_left hφ) hcusp (span_cont hL hφ) M hM x m _ ?_
  intro y hy
  set Yv : Fin m → Matrix (Fin a) (Fin a) (Cinf E) := fun i => conjY E x (y i) with hYv
  have hYY : ∀ i j, Yv i * Yv j = 0 := fun i j => conjY_mul x _ _
  have hYn : ∀ i, ‖toL (Yv i)‖ ≤ K₁ * gain := by
    intro i
    have h1 := hC₁ b hb r hr hsieg k hk (GroundTheory.Automorphic.CuspidalSpectrum.truncInf (y i)) (fun p => rfl)
      (fun p => GroundTheory.Automorphic.infinite_mem_scaledInfSet hM (hy i) p)
    have h2 := hcT (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
      nilM (GroundTheory.Automorphic.CuspidalSpectrum.truncInf (y i)) * (x : Matrix (Fin a) (Fin a) (Ad E)))
    have e : Yv i = (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
        nilM (GroundTheory.Automorphic.CuspidalSpectrum.truncInf (y i)) * (x : Matrix (Fin a) (Fin a) (Ad E))).map (pInf E) := by
      rw [hYv]; dsimp only; rw [← conjY_truncInf, conjY_apply]
    rw [e]
    refine h2.trans ?_
    calc cT * ‖GroundTheory.Automorphic.CuspidalSpectrum.archMat E a (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
          nilM (GroundTheory.Automorphic.CuspidalSpectrum.truncInf (y i)) * (x : Matrix (Fin a) (Fin a) (Ad E)))‖
        ≤ cT * (C₁ * gain) := mul_le_mul_of_nonneg_left h1 hcT0
      _ ≤ cT * (max C₁ 0 * gain) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_left _ _) hgain0) hcT0
      _ = K₁ * gain := by rw [hK₁]; ring
  have hYR : ∀ i, ‖toL (Yv i)‖ ≤ K₁ * t⁻¹ := fun i => (hYn i).trans (mul_le_mul_of_nonneg_left hgain hK₁0)
  have key : ∀ ε : Fin m → Bool, φ.1 (unip (GroundTheory.Automorphic.altPoint y ε) * x) =
      ∫ w, f (toL ((1 + GroundTheory.Automorphic.altPoint Yv ε) * Matrix.of w)) * β w := by
    intro ε
    set sε := GroundTheory.Automorphic.altPoint y ε with hsε
    have hsplit : unip sε * x = x * (x⁻¹ * unip (GroundTheory.Automorphic.CuspidalSpectrum.truncInf sε) * x) *
        (x⁻¹ * unip (GroundTheory.Automorphic.CuspidalSpectrum.truncFin sε) * x) := by
      conv_lhs => rw [← GroundTheory.Automorphic.CuspidalSpectrum.truncInf_add_truncFin sε, unip_add]
      group
    obtain ⟨l, hl, hle⟩ := hfin b hb r hr k hk (GroundTheory.Automorphic.CuspidalSpectrum.truncFin sε) (fun p => rfl)
      (fun p => GroundTheory.Automorphic.exists_finite_altPoint_eq_natCast_mul hM y hy ε p)
    rw [hsplit, hle, span_right hφ hl, conj_unip_eq x _ (fun p => rfl)]
    rw [← reproSpan E a L W X N β hβ hβc hβu hrep φ hφ, chart_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have hv := val_map_conj_unip x (GroundTheory.Automorphic.CuspidalSpectrum.truncInf sε)
    rw [conjY_truncInf, hsε, GroundTheory.Automorphic.CuspidalSpectrum.map_altPoint] at hv
    simp only [Function.comp_apply]
    congr 2
    change toL (((Matrix.GeneralLinearGroup.map (pInf E) _ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of w) = _
    rw [hv]
  have hsum : ∑ ε : Fin m → Bool, (GroundTheory.Automorphic.altSign ε : ℂ) * φ.1 (unip (GroundTheory.Automorphic.altPoint y ε) * x) =
      ∑ ε : Fin m → Bool, (GroundTheory.Automorphic.altSign ε : ℂ) *
        ∫ w, f (toL ((1 + GroundTheory.Automorphic.altPoint Yv ε) * Matrix.of w)) * β w :=
    Finset.sum_congr rfl fun ε _ => by rw [key ε]
  rw [hsum]
  refine (hdiff f hfc F hF0 hfQ Yv hYY hYR).trans ?_
  have hprod : ∏ i, ‖toL (Yv i)‖ ≤ (K₁ * gain) ^ m := by
    rw [← Fin.prod_const]
    exact Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hYn i
  calc c * F * ∏ i, ‖toL (Yv i)‖ ≤ c * F * (K₁ * gain) ^ m := mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = c * C₀' * H' ^ N₀ * K₁ ^ m * gain ^ m * Sr ^ N₀ := by rw [hF]; ring

theorem decay : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ) (β : Lie E a → ℂ), ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ invSet E a → (∀ φ ∈ formsGL E a L W X N, ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g) → ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), IsCuspidal φ.1 → ∀ Ω : Set (GA E a), IsCompact Ω → Ω ⊆ ((adelicBorel : Subgroup (GA E a)) : Set (GA E a)) → ∀ (t C₀ : ℝ) (N₀ : ℕ), 0 < t → (∀ b ∈ Ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), ∀ k ∈ (maxCompact : Subgroup (GA E a)), ∀ y : GL (Fin a) (Cinf E), ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k * infGL E a y)‖ ≤ C₀ * (∑ i, (r i + (r i)⁻¹)) ^ N₀ * height y ^ N₀) → ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ Ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∀ k ∈ (maxCompact : Subgroup (GA E a)), ∀ i j : Fin a, (j : ℕ) = i + 1 → ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k)‖ ≤ C * (r j / r i) ^ m * (∑ i, (r i + (r i)⁻¹)) ^ N₀ := by
  intro E _ _ _ a L hL W X N β hβ hβc hβu hrep φ hφ hcusp Ω hΩ hΩB t C₀ N₀ ht hgrow m
  have hex : ∀ (s : ℕ) (hs : 0 < s) (hsa : s < a), ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ Ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i),
      (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∀ k ∈ (maxCompact : Subgroup (GA E a)),
      ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k)‖ ≤
        C * (r ⟨s, hsa⟩ / r ⟨s - 1, by omega⟩) ^ m * (∑ i, (r i + (r i)⁻¹)) ^ N₀ := fun s hs hsa =>
    oneRoot E a L hL W X N β hβ hβc hβu hrep φ hφ hcusp Ω hΩ hΩB t C₀ N₀ ht hgrow m s hs hsa
  choose Cf hCf0 hCf using hex
  refine ⟨∑ s : Fin a, if h : 0 < (s : ℕ) then Cf s h s.2 else 0,
    Finset.sum_nonneg fun s _ => by split_ifs <;> simp [hCf0], ?_⟩
  intro b hb r hr hsieg k hk i j hij
  have hj0 : 0 < (j : ℕ) := by omega
  have h := hCf j hj0 j.2 b hb r hr hsieg k hk
  have e1 : (⟨(j : ℕ) - 1, by omega⟩ : Fin a) = i := Fin.ext (by simp; omega)
  rw [e1] at h
  have hle : Cf j hj0 j.2 ≤ ∑ s : Fin a, if h : 0 < (s : ℕ) then Cf s h s.2 else 0 := by
    have h1 := Finset.single_le_sum (f := fun s : Fin a => if h : 0 < (s : ℕ) then Cf s h s.2 else 0)
      (fun s _ => by split_ifs <;> simp [hCf0]) (Finset.mem_univ j)
    simpa [hj0] using h1
  refine h.trans ?_
  have hpos : 0 ≤ (r j / r i) ^ m * (∑ i, (r i + (r i)⁻¹)) ^ N₀ :=
    mul_nonneg (pow_nonneg (div_nonneg (hr _).le (hr _).le) _)
      (pow_nonneg (Finset.sum_nonneg fun i _ => add_nonneg (hr i).le (inv_nonneg.2 (hr i).le)) _)
  calc Cf j hj0 j.2 * (r j / r i) ^ m * (∑ i, (r i + (r i)⁻¹)) ^ N₀
      = Cf j hj0 j.2 * ((r j / r i) ^ m * (∑ i, (r i + (r i)⁻¹)) ^ N₀) := by ring
    _ ≤ (∑ s : Fin a, if h : 0 < (s : ℕ) then Cf s h s.2 else 0) * ((r j / r i) ^ m * (∑ i, (r i + (r i)⁻¹)) ^ N₀) :=
        mul_le_mul_of_nonneg_right hle hpos
    _ = _ := by ring

end GlobalTheory.HCF.Decay
end
