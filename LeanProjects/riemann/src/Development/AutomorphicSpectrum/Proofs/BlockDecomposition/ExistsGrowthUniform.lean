import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicGLHomeomorphInfiniteFinite
import GroundTheory.GlobalFields.TateThesis.GlobalZetaInfinite

open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing
open IsDedekindDomain Matrix Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BoxBound

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem norm_toL_mul_le (A B : Matrix (Fin a) (Fin a) (Cinf E)) :
    ‖toL (A * B)‖ ≤ a * (‖toL A‖ * ‖toL B‖) := by
  have hA : ∀ i k, ‖A i k‖ ≤ ‖toL A‖ := fun i k =>
    (norm_le_pi_norm (toL A i) k).trans (norm_le_pi_norm (toL A) i)
  have hB : ∀ i k, ‖B i k‖ ≤ ‖toL B‖ := fun i k =>
    (norm_le_pi_norm (toL B i) k).trans (norm_le_pi_norm (toL B) i)
  have h0 : 0 ≤ (a : ℝ) * (‖toL A‖ * ‖toL B‖) := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  change ‖(A * B) i j‖ ≤ _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (‖toL A‖ * ‖toL B‖) fun k _ => ?_).trans_eq (by simp)
  exact (norm_mul_le _ _).trans (mul_le_mul (hA i k) (hB k j) (norm_nonneg _) (norm_nonneg _))

theorem height_mul_le' (y z : GL (Fin a) (Cinf E)) :
    CuspRep.height (y * z) ≤ (1 + 2 * a) * (CuspRep.height y * CuspRep.height z) := by
  have h1 := norm_toL_mul_le (y.val) (z.val)
  have h2 := norm_toL_mul_le ((z⁻¹).val) ((y⁻¹).val)
  have e1 : (y * z).val = y.val * z.val := rfl
  have e2 : ((y * z)⁻¹).val = (z⁻¹).val * (y⁻¹).val := by rw [_root_.mul_inv_rev]; rfl
  have hy := one_le_height y
  have hz := one_le_height z
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL z.val)
  have n3 := norm_nonneg (toL (y⁻¹).val)
  have n4 := norm_nonneg (toL (z⁻¹).val)
  have m1 : ‖toL y.val‖ * ‖toL z.val‖ ≤ CuspRep.height y * CuspRep.height z :=
    mul_le_mul (by unfold CuspRep.height; linarith) (by unfold CuspRep.height; linarith) n2 (by linarith)
  have m2 : ‖toL (z⁻¹).val‖ * ‖toL (y⁻¹).val‖ ≤ CuspRep.height y * CuspRep.height z := by
    rw [mul_comm]
    exact mul_le_mul (by unfold CuspRep.height; linarith) (by unfold CuspRep.height; linarith) n4 (by linarith)
  have m3 : 1 ≤ CuspRep.height y * CuspRep.height z := one_le_mul_of_one_le_of_one_le hy hz
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have : CuspRep.height (y * z) = 1 + ‖toL (y * z).val‖ + ‖toL ((y * z)⁻¹).val‖ := rfl
  rw [this, e1, e2]
  nlinarith [mul_le_mul_of_nonneg_left m1 ha, mul_le_mul_of_nonneg_left m2 ha]

theorem continuous_height : Continuous (CuspRep.height : GL (Fin a) (Cinf E) → ℝ) := by
  have h1 : Continuous fun y : GL (Fin a) (Cinf E) => (y.val : Matrix (Fin a) (Fin a) (Cinf E)) :=
    Units.continuous_val
  have h2 : Continuous fun y : GL (Fin a) (Cinf E) => ((y⁻¹).val : Matrix (Fin a) (Fin a) (Cinf E)) :=
    Units.continuous_coe_inv
  have n1 : Continuous fun y : GL (Fin a) (Cinf E) => ‖toL y.val‖ := (continuous_norm (E := Lie E a)).comp h1
  have n2 : Continuous fun y : GL (Fin a) (Cinf E) => ‖toL (y⁻¹).val‖ := (continuous_norm (E := Lie E a)).comp h2
  unfold CuspRep.height
  exact (continuous_const.add n1).add n2

abbrev gInf (g : GA E a) : GL (Fin a) (Cinf E) := GeneralLinearGroup.map (pInf E) g

abbrev gFin (g : GA E a) : GL (Fin a) (Af E) := GeneralLinearGroup.map (pFin E) g

theorem continuous_gInf : Continuous (gInf : GA E a → GL (Fin a) (Cinf E)) :=
  GASplit.continuous_glMap a (pInf E) (GASplit.continuous_pInf E)

theorem continuous_gFin : Continuous (gFin : GA E a → GL (Fin a) (Af E)) :=
  GASplit.continuous_glMap a (pFin E) (GASplit.continuous_pFin E)

theorem exists_height_bound {S : Set (GA E a)} (hS : IsCompact S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g ∈ S, CuspRep.height (gInf g) ≤ B := by
  obtain ⟨B, hB⟩ := (hS.image (continuous_height.comp continuous_gInf)).bddAbove
  exact ⟨max B 0, le_max_right _ _, fun g hg => (hB ⟨g, hg, rfl⟩).trans (le_max_left _ _)⟩

theorem exists_growth_uniform {φ : Sm E a} (hφ : IsAutForm φ) {T : Set (GL (Fin a) (Af E))} (hT : IsCompact T) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ t ∈ T, ∀ y, ‖φ.1 (finGL E a t * infGL E a y)‖ ≤ C * CuspRep.height y ^ N := by
  choose Cf Nf hf using fun x : GL (Fin a) (Af E) => hφ.growth (finGL E a x)
  have hU : ∀ x ∈ T, {t | x⁻¹ * t ∈ {k | finRep E a k φ = φ}} ∈ 𝓝 x := fun x _ =>
    (hφ.level.preimage (continuous_const.mul continuous_id :
      Continuous fun t : GL (Fin a) (Af E) => x⁻¹ * t)).mem_nhds (by
        change finRep E a (x⁻¹ * x) φ = φ
        rw [inv_mul_cancel, map_one]; rfl)
  obtain ⟨s, -, hs⟩ := hT.elim_nhds_subcover _ hU
  refine ⟨∑ x ∈ s, |Cf x|, s.sup Nf, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun t ht y => ?_⟩
  obtain ⟨x, hx, hxt⟩ := Set.mem_iUnion₂.1 (hs ht)
  have hk : finRep E a (x⁻¹ * t) φ = φ := hxt
  have e : φ.1 (finGL E a t * infGL E a y) = φ.1 (finGL E a x * infGL E a y) := by
    have h1 : finGL E a t = finGL E a x * finGL E a (x⁻¹ * t) := by
      rw [← map_mul, mul_inv_cancel_left]
    have h2 := congrFun (congrArg Subtype.val hk) (finGL E a x * infGL E a y)
    refine Eq.trans ?_ h2
    change _ = φ.1 (finGL E a x * infGL E a y * finGL E a (x⁻¹ * t))
    rw [h1, mul_assoc, mul_assoc, infGL_comm]
  rw [e]
  have hy := one_le_height y
  refine (hf x y).trans ?_
  refine (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans ?_
  refine mul_le_mul (Finset.single_le_sum (f := fun x => |Cf x|) (fun _ _ => abs_nonneg _) hx)
    (pow_le_pow_right₀ hy (Finset.le_sup hx)) (by positivity) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem norm_pInf_apply (x : Ad E) (w : InfinitePlace E) : ‖pInf E x w‖ = ‖x.1 w‖ :=
  norm_isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w) (x.1 w)

abbrev dg (a : ℕ) (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i) : GA E a :=
  diagUnits a (fun i => posIdele (K := E) (ρ i) (hρ i))

theorem gFin_dg (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i) : gFin (dg (E := E) a ρ hρ) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change pFin E ((diagonal fun i => ((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E) : 𝔸[E])) i j) = (1 : Matrix (Fin a) (Fin a) (Af E)) i j
  rw [Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with h
  · subst h
    exact FiniteAdeleRing.ext _ fun v => posIdele_finite (K := E) (ρ i) (hρ i) v
  · exact map_zero _

theorem height_gInf_dg_le (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i) {L : ℝ} (hL1 : 1 ≤ L)
    (hL : ∀ i, ρ i ≤ L ∧ (ρ i)⁻¹ ≤ L) : CuspRep.height (gInf (dg (E := E) a ρ hρ)) ≤ 3 * L := by
  have hL0 : 0 ≤ L := by linarith
  have key : ∀ i w, ‖pInf E ((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E) : 𝔸[E]) w‖ = ρ i := fun i w => by
    rw [norm_pInf_apply]; exact norm_posIdele_infinite (K := E) (ρ i) (hρ i) w
  have key' : ∀ i w, ‖pInf E (((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E)⁻¹ : IdeleGroup E) : 𝔸[E]) w‖ = (ρ i)⁻¹ := fun i w => by
    have h1 : pInf E ((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E) : 𝔸[E]) w *
        pInf E (((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E)⁻¹ : IdeleGroup E) : 𝔸[E]) w = 1 := by
      rw [← Pi.mul_apply, ← map_mul, Units.mul_inv, map_one, Pi.one_apply]
    have h2 := congrArg norm h1
    rw [norm_mul, key, norm_one] at h2
    exact eq_inv_of_mul_eq_one_right h2
  have b1 : ‖toL (gInf (dg (E := E) a ρ hρ)).val‖ ≤ L := by
    refine (pi_norm_le_iff_of_nonneg hL0).2 fun i => (pi_norm_le_iff_of_nonneg hL0).2 fun j =>
      (pi_norm_le_iff_of_nonneg hL0).2 fun w => ?_
    change ‖pInf E ((diagonal fun i => ((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E) : 𝔸[E])) i j) w‖ ≤ L
    rw [Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rw [key]; exact (hL i).1
    · simpa using hL0
  have b2 : ‖toL ((gInf (dg (E := E) a ρ hρ))⁻¹).val‖ ≤ L := by
    rw [← map_inv]
    refine (pi_norm_le_iff_of_nonneg hL0).2 fun i => (pi_norm_le_iff_of_nonneg hL0).2 fun j =>
      (pi_norm_le_iff_of_nonneg hL0).2 fun w => ?_
    change ‖pInf E ((diagonal fun i => (((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E)⁻¹ : IdeleGroup E) : 𝔸[E])) i j) w‖ ≤ L
    rw [Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rw [key']; exact (hL i).2
    · simpa using hL0
  unfold CuspRep.height
  linarith

theorem gFin_infEmb (y : AutomorphicForm.archGroup E a) : gFin (AutomorphicForm.infEmb E a y : GA E a) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h := AutomorphicForm.prodEquiv_infEmb (K := E) (n := a) y
  have h2 := congrArg (fun p => (p.2 : GL (Fin a) (Af E)) i j) h
  exact h2

theorem finGL_mul_infGL (g : GA E a) : finGL E a (gFin g) * infGL E a (gInf g) = g := by
  rw [← infGL_comm]; exact infGL_mul_finGL g

theorem box_bound : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → (∀ ω : Set (AdelicGLn.AdelicGL E a), IsCompact ω → ∃ N : ℕ, ∀ Q : Set (AutomorphicForm.archGroup E a), IsCompact Q → ∃ C : ℝ,
    ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i), ∀ kk ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL E a)), ∀ y ∈ Q, ∀ L : ℝ, 1 ≤ L →
      (∀ i, ρ i ≤ L ∧ (ρ i)⁻¹ ≤ L) →
      ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (ρ i) (hρ i)) * kk * AutomorphicForm.infEmb E a y)‖ ≤ C * L ^ N) := by
  intro E _ _ _ a φ hφ ω hω
  have hK : IsCompact (maxCompact (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)) := isCompact_maxCompact
  have hT : IsCompact ((fun p : GA E a × GA E a => gFin p.1 * gFin p.2) '' (ω ×ˢ (maxCompact (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)))) :=
    (hω.prod hK).image ((continuous_gFin.comp continuous_fst).mul (continuous_gFin.comp continuous_snd))
  obtain ⟨C₀, N, hC₀, hgrow⟩ := exists_growth_uniform hφ hT
  refine ⟨N, fun Q hQ => ?_⟩
  obtain ⟨B₁, hB₁, h₁⟩ := exists_height_bound (E := E) (a := a) hω
  obtain ⟨B₂, hB₂, h₂⟩ := exists_height_bound (E := E) (a := a) hK
  obtain ⟨B₃, hB₃, h₃⟩ := exists_height_bound (E := E) (a := a)
    (hQ.image (AutomorphicForm.continuous_infEmb (K := E) (n := a)))
  set c : ℝ := 1 + 2 * a with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨C₀ * (c * (c * (c * (B₁ * 3)) * B₂) * B₃) ^ N, fun b hb ρ hρ kk hk y hy L hL1 hL => ?_⟩
  set D : GA E a := dg a ρ hρ with hD
  set Y : GA E a := AutomorphicForm.infEmb E a y with hY
  set x : GA E a := b * D * kk * Y with hx
  have hfin : gFin x = gFin b * gFin kk := by
    simp only [hx, map_mul, hD, gFin_dg, hY, gFin_infEmb, mul_one]
  have hinf : gInf x = gInf b * gInf D * gInf kk * gInf Y := by
    simp only [hx, map_mul]
  have hb' := h₁ b hb
  have hk' := h₂ kk hk
  have hy' := h₃ Y ⟨y, hy, rfl⟩
  have hd' : CuspRep.height (gInf D) ≤ 3 * L := height_gInf_dg_le ρ hρ hL1 hL
  have hH : CuspRep.height (gInf x) ≤ (c * (c * (c * (B₁ * 3)) * B₂) * B₃) * L := by
    have o1 := one_le_height (gInf b)
    have o2 := one_le_height (gInf D)
    have o3 := one_le_height (gInf kk)
    have o4 := one_le_height (gInf Y)
    have s1 : CuspRep.height (gInf b * gInf D) ≤ c * (B₁ * (3 * L)) :=
      (height_mul_le' _ _).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul hb' hd' (by linarith) hB₁) hc0)
    have s2 : CuspRep.height (gInf b * gInf D * gInf kk) ≤ c * ((c * (B₁ * (3 * L))) * B₂) :=
      (height_mul_le' _ _).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul s1 hk' (by linarith) (by positivity)) hc0)
    have s3 : CuspRep.height (gInf b * gInf D * gInf kk * gInf Y) ≤ c * ((c * ((c * (B₁ * (3 * L))) * B₂)) * B₃) :=
      (height_mul_le' _ _).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul s2 hy' (by linarith) (by positivity)) hc0)
    rw [hinf]
    exact s3.trans_eq (by ring)
  have hbound := hgrow (gFin x) ⟨(b, kk), ⟨hb, hk⟩, hfin.symm⟩ (gInf x)
  rw [finGL_mul_infGL] at hbound
  refine hbound.trans ?_
  rw [mul_assoc, ← mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ hC₀
  exact pow_le_pow_left₀ (by linarith [one_le_height (gInf x)]) hH N

end GlobalTheory.CompanionTheory.BoxBound

end
