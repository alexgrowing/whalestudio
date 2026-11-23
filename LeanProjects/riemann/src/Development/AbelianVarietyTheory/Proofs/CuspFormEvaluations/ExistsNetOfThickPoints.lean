import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormProdSignMulDetSubmatrixSubOneLe
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThickPointHyperbolic
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetTypesOfBoundedBases
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetMeetingFibres
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstRaisingMemEquivariant

open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Matrix hiding gram
open scoped ComplexConjugate

namespace GlobalTheory

namespace FiniteNet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem norm_hermC_le_of_ortho (X : Data E r) {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ)
    (u v : Fin r → ℂ) : ‖hermC τ.1 X.Gm u v‖ ≤ (X.maj x τ u + X.maj x τ v) / 2 := by
  have hd := Ne.isUnit (FrameNet.det_ne_zero_of_ortho X hx τ)
  have hsurj : ∀ u : Fin r → ℂ, ∃ c, u = mat x τ *ᵥ c := fun u =>
    ⟨(mat x τ)⁻¹ *ᵥ u, by rw [mulVec_mulVec, mul_nonsing_inv _ hd, one_mulVec]⟩
  obtain ⟨c, rfl⟩ := hsurj u
  obtain ⟨d, rfl⟩ := hsurj v
  rw [UnipMove.GraphH.maj_ortho X hx, UnipMove.GraphH.maj_ortho X hx]
  have hg : ∀ i b, hermC τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.col (mat x τ) i)
      (ReciprocityTheory.ChartRestriction.G.FD.col (mat x τ) b) =
      if i = b then ((sgn X.p0 (i : ℕ) : ℝ) : ℂ) else 0 := by
    intro i b
    have := congrFun (congrFun (hx τ) i) b
    simpa [gram, Matrix.diagonal_apply] using this
  have h1 : hermC τ.1 X.Gm (mat x τ *ᵥ c) (mat x τ *ᵥ d) =
      ∑ i, c i * (conj (d i) * ((sgn X.p0 (i : ℕ) : ℝ) : ℂ)) := by
    rw [Data.mulVec_eq_sum_col _ c, Data.mulVec_eq_sum_col _ d, hermC_sum_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hermC_smul_left, hermC_sum_right]
    simp_rw [hermC_smul_right, hg, mul_ite, mul_zero]
    simp
  rw [h1]
  change _ ≤ (∑ i, ‖c i‖ ^ 2 + ∑ i, ‖d i‖ ^ 2) / 2
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hs : ‖((sgn X.p0 (i : ℕ) : ℝ) : ℂ)‖ = 1 := by
    unfold sgn
    split_ifs <;> simp
  rw [norm_mul, norm_mul, hs, Complex.norm_conj]
  nlinarith [sq_nonneg (‖c i‖ - ‖d i‖)]

theorem norm_herm_le_of_ortho (X : Data E r) {x : Frame X.Ψ r} (hx : X.IsOrtho x) {B : ℝ}
    {u v : Fin r → E} (hu : ∑ τ, X.maj x τ (Data.emb τ.1 u) ≤ B)
    (hv : ∑ τ, X.maj x τ (Data.emb τ.1 v) ≤ B) (σ : E →+* ℂ) : ‖σ (herm X.Gm u v)‖ ≤ B := by
  have hxd : x ∈ X.dom := PIW.FdPA.orthonormal_domain r X x hx
  have key : ∀ τ : X.Ψ, ‖τ.1 (herm X.Gm u v)‖ ≤ B := by
    intro τ
    have h1 := norm_hermC_le_of_ortho X hx τ (Data.emb τ.1 u) (Data.emb τ.1 v)
    rw [hermC_emb] at h1
    have h2 : ∀ w : Fin r → E, X.maj x τ (Data.emb τ.1 w) ≤ ∑ τ, X.maj x τ (Data.emb τ.1 w) :=
      fun w => Finset.single_le_sum (f := fun τ : X.Ψ => X.maj x τ (Data.emb τ.1 w))
        (fun _ _ => MajorantOperators.maj_nonneg hxd _ _) (Finset.mem_univ τ)
    linarith [h2 u, h2 v]
  by_cases h : σ ∈ X.Ψ
  · exact key ⟨σ, h⟩
  · have h' : ComplexEmbedding.conjugate σ ∈ X.Ψ := by
      by_contra h'
      exact h ((X.cmType σ).2 h')
    have := key ⟨_, h'⟩
    simpa [ComplexEmbedding.conjugate_coe_eq] using this

theorem pnorm_lact_rmul (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    X.pnorm la P (lact γ (rmul x b)) = X.pnorm la P x := by
  have hxb : rmul x b ∈ X.dom := OrthogonalFrameDomain.rmul_mem_dom X hx hb
  rw [← FrameDegreeData.pnorm_rmul X la P hP.2.1 x hx b hb]
  have hχ : ‖X.χ la γ‖ = 1 := by
    obtain ⟨n, hn, h⟩ := X.χ_fin la
    have := congrArg norm (h γ hγ)
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  unfold Data.pnorm dmin
  simp only [MajInv.gram_lact X (X.Γ_stab γ hγ)]
  rw [hP.2.2 γ hγ _ hxb, norm_mul, hχ, one_mul]

theorem dom_nonempty (X : Data E r) : X.dom.Nonempty := by
  choose p _ hp using X.signature
  exact ⟨fun τ => p τ, PIW.FdPA.orthonormal_domain r X _ hp⟩

theorem epStar_pos {M f w k : ℝ} (hM : 0 < M) (hf : 0 ≤ f) (hw : 0 < w) (hk : 0 < k) :
    0 < epStar M f w k := by
  have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h3 := Real.pi_pos
  unfold epStar
  positivity

end FiniteNet

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open FiniteNet

theorem exists_net_of_thick_points {r : ℕ} (X : DataX E r) {ε B η : ℝ} (hε : 0 < ε) (hB : 1 ≤ B)
    (hεB : (2 * fdeg E * r : ℝ) ^ 4 * dE E ^ 2 / (4 * ε) ≤ B) (hη0 : 0 < η) (hη : η ≤ 1) :
    ∃ N : Finset (Frame X.Ψ r), (∀ y ∈ N, y ∈ X.dom) ∧
      (∀ x ∈ X.dom, (∀ v ∈ X.L', v ≠ 0 → ε ≤ ∑ τ, X.maj x τ (Data.emb τ.1 v)) →
        ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ A : Frame X.Ψ r, X.IsOrtho (lact γ (rmul x b)) ∧
          rmul (lact γ (rmul x b)) A ∈ N ∧ ∀ τ a c, ‖A τ a c - (if a = c then 1 else 0)‖ ≤ η) ∧
      (N.card : ℝ) ≤ ((1 + 2 * B) ^ (2 * fdeg E * r ^ 2) *
          ((X.NA : ℝ) * X.NC * r * B) ^ (2 * fdeg E * r ^ 2) * (X.g : ℝ) ^ (2 * fdeg E * r ^ 2)) *
        Real.exp (2 * (fdeg E : ℝ) * (r : ℝ) ^ 2 * Real.log (6 * (r : ℝ) ^ 2 / η) +
          2 * (fdeg E : ℝ) * (r : ℝ) ^ 3 * Real.log (r * B)) := by
  classical
  obtain ⟨V, hV₁, hV₂, hV₃, -⟩ := exists_finset_types_of_bounded_bases X hB
  have hnet := fun v : V => FrameNet.exists_frame_net X.toData v.1 (hV₁ v.1 v.2).2.1
    (fun i k => X.L'_int _ ((hV₁ v.1 v.2).1 i) _ ((hV₁ v.1 v.2).1 k)) hB hη0 hη
  choose N hN₁ hN₂ hN₃ _ using hnet
  refine ⟨Finset.univ.biUnion N, fun y hy => ?_, fun x hx hmin => ?_, ?_⟩
  · obtain ⟨v, -, hv⟩ := Finset.mem_biUnion.1 hy
    exact FrameNet.shortFrames_subset_dom X.toData _ B (hN₁ v hv)
  · obtain ⟨b, hb, ho⟩ := (orthonormalFlagTranslate_holds (E := E) r X.toData).1 x hx
    obtain ⟨v, hv₁, hv₂, hv₃⟩ := exists_short_basis_at X x hx ε hε hmin
    have hv₄ : ∀ i, ∑ τ, X.maj (rmul x b) τ (Data.emb τ.1 (v i)) ≤ B := fun i => by
      simp only [MajInv.maj_rmul X.toData hx hb]
      exact (hv₃ i).trans hεB
    obtain ⟨γ, hγ, w, hw, hvw⟩ := hV₂ v hv₁ hv₂ fun σ i k =>
      norm_herm_le_of_ortho X.toData ho (hv₄ i) (hv₄ k) σ
    have hγ' := X.Γ_stab _ (X.Γ.inv_mem hγ)
    have ho' : X.IsOrtho (lact γ⁻¹ (rmul x b)) := fun τ =>
      (MajInv.gram_lact X.toData hγ' _ τ).trans (ho τ)
    obtain ⟨A, hA₁, hA₂⟩ := hN₂ ⟨w, hw⟩ (lact γ⁻¹ (rmul x b)) ⟨ho', fun i => by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun τ _ => ?_)) (hv₄ i)
      rw [← MajInv.maj_lact X.toData hγ' (rmul x b) τ]
      congr 1
      have h1 : w i = ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v i := by
        rw [hvw i, mulVec_mulVec, Units.inv_mul, one_mulVec]
      change Data.emb τ.1 (w i) = _
      rw [h1]
      funext a
      exact RingHom.map_mulVec τ.1 _ (v i) a⟩
    exact ⟨γ⁻¹, X.Γ.inv_mem hγ, b, hb, A, ho',
      Finset.mem_biUnion.2 ⟨⟨w, hw⟩, Finset.mem_univ _, hA₁⟩, hA₂⟩
  · calc ((Finset.univ.biUnion N).card : ℝ) ≤ ∑ v, ((N v).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _v : V, _ := Finset.sum_le_sum fun v _ => hN₃ v
      _ = V.card * _ := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe]
      _ ≤ _ := mul_le_mul_of_nonneg_right hV₃ (Real.exp_pos _).le

theorem exists_finite_net {r : ℕ} (X : DataX E r) (la : Wt X.Ψ r) (M w : ℝ)
    (hM : 0 < M) (hw : (∑ τ, X.spread la τ) ≤ w) (hw0 : 0 < w)
    (hT : ∀ v ∈ X.L', herm X.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ X.Γ, X.χ la γ = 1 ∧ ∀ τ : X.Ψ,
        (γ : Matrix (Fin r) (Fin r) E).map τ.1 = X.flowMat v τ ((M : ℂ) * τ.1 b)) :
    let ε : ℝ := epStar M (fdeg E) w X.k0
    let B : ℝ := max 1 ((2 * fdeg E * r : ℝ) ^ 4 * dE E ^ 2 / (4 * ε))
    let η : ℝ := 1 / (1000 * (r : ℝ) ^ 2 * (1 + ∑ τ, ∑ i, |(la τ i : ℝ)|))
    ∃ N : Finset (Frame X.Ψ r), N.Nonempty ∧ (∀ y ∈ N, y ∈ X.dom) ∧
      (∀ P ∈ X.SS la, ∀ x ∈ X.dom, ∃ y ∈ N, X.pnorm la P x ≤ 4 * X.pnorm la P y) ∧
      Real.log N.card ≤
        2 * (fdeg E : ℝ) * (r : ℝ) ^ 2 *
          Real.log ((1 + 2 * B) * ((X.NA : ℝ) * X.NC * r * B) * X.g) +
        (2 * (fdeg E : ℝ) * (r : ℝ) ^ 2 * Real.log (6 * (r : ℝ) ^ 2 / η) +
          2 * (fdeg E : ℝ) * (r : ℝ) ^ 3 * Real.log (r * B)) ∧
      Real.log N.card ≤
        2 * (fdeg E : ℝ) * (r : ℝ) ^ 2 * Real.log (3 * (X.NA : ℝ) * X.NC * X.g * r * B ^ 2) +
        (2 * (fdeg E : ℝ) * (r : ℝ) ^ 2 * Real.log (6 * (r : ℝ) ^ 2 / η) +
          2 * (fdeg E : ℝ) * (r : ℝ) ^ 3 * Real.log (r * B)) := by
  classical
  intro ε B η
  obtain ⟨x₀, hx₀⟩ := dom_nonempty X.toData
  have hp0 : ∀ (P : Frame X.Ψ r → ℂ) y, 0 ≤ X.pnorm la P y := fun P y => by
    unfold Data.pnorm
    positivity
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨{x₀}, Finset.singleton_nonempty _, by simpa using hx₀, fun P _ x _ =>
      ⟨x₀, Finset.mem_singleton_self _, ?_⟩, by simp, by simp⟩
    rw [Subsingleton.elim x x₀]
    linarith [hp0 P x₀]
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hε : 0 < ε := epStar_pos hM (Nat.cast_nonneg _) hw0 X.minWeight_pos
  have hB : 1 ≤ B := le_max_left _ _
  have hL : (0 : ℝ) ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := by positivity
  have hη0 : 0 < η := by positivity
  have hη : η ≤ 1 := by
    refine (div_le_one (by positivity)).2 ?_
    have h1 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := one_le_pow₀ hr1
    nlinarith
  obtain ⟨N, hN₁, hN₂, hN₃⟩ := exists_net_of_thick_points X hε hB (le_max_right _ _) hη0 hη
  have hNA : (1 : ℝ) ≤ X.NA := by exact_mod_cast X.NA_pos
  have hNC : (1 : ℝ) ≤ X.NC := by exact_mod_cast X.NC_pos
  have hg : (1 : ℝ) ≤ X.g := by exact_mod_cast X.g_pos
  set T : ℝ := (1 + 2 * B) * ((X.NA : ℝ) * X.NC * r * B) * X.g with hTdef
  set G : ℝ := 2 * (fdeg E : ℝ) * (r : ℝ) ^ 2 * Real.log (6 * (r : ℝ) ^ 2 / η) +
    2 * (fdeg E : ℝ) * (r : ℝ) ^ 3 * Real.log (r * B) with hG
  have hT1 : 1 ≤ T := by
    have h1 : (1 : ℝ) ≤ 1 + 2 * B := by linarith
    rw [hTdef]
    bound
  have hG0 : 0 ≤ G := by
    have h1 : 0 ≤ Real.log (6 * (r : ℝ) ^ 2 / η) :=
      Real.log_nonneg (by rw [le_div_iff₀ hη0]; nlinarith)
    have h2 : 0 ≤ Real.log (r * B) := Real.log_nonneg (by nlinarith)
    positivity
  rw [← mul_pow, ← mul_pow, ← hTdef] at hN₃
  have hbound : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ T ^ (2 * fdeg E * r ^ 2) * Real.exp G →
      Real.log n ≤ 2 * (fdeg E : ℝ) * (r : ℝ) ^ 2 * Real.log T + G ∧
      Real.log n ≤ 2 * (fdeg E : ℝ) * (r : ℝ) ^ 2 *
        Real.log (3 * (X.NA : ℝ) * X.NC * X.g * r * B ^ 2) + G := by
    intro n hn h
    have h1 := Real.log_le_log (by exact_mod_cast hn) h
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, Real.log_pow] at h1
    push_cast at h1
    refine ⟨h1, h1.trans ?_⟩
    gcongr
    calc T ≤ (3 * B) * ((X.NA : ℝ) * X.NC * r * B) * X.g := by rw [hTdef]; gcongr; linarith
      _ = _ := by ring
  have hmain : ∀ P ∈ X.SS la, ∀ x ∈ X.dom, 0 < X.pnorm la P x →
      ∃ y ∈ N, X.pnorm la P x ≤ 4 * X.pnorm la P y := by
    intro P hP x hx hpos
    obtain ⟨C, hC⟩ := hP.1.2
    set S : Set ℝ := (fun y => X.pnorm la P y) '' X.dom with hS
    have hbdd : BddAbove S := ⟨C, by rintro _ ⟨y, hy, rfl⟩; exact hC y hy⟩
    have hle : ∀ y ∈ X.dom, X.pnorm la P y ≤ sSup S := fun y hy => le_csSup hbdd ⟨y, hy, rfl⟩
    have hx' := hle x hx
    have hne : S.Nonempty := ⟨_, x, hx, rfl⟩
    have hhalf : sSup S / 2 < sSup S := by linarith
    obtain ⟨_, ⟨z, hz, rfl⟩, hz'⟩ := exists_lt_of_lt_csSup hne hhalf
    replace hz' : sSup S / 2 < X.pnorm la P z := hz'
    have hmax := maxBound_holds r X la P M w hP hM hw hw0 hT z hz
      (fun y hy => by have := hle y hy; linarith) (by linarith)
    obtain ⟨γ, hγ, b, hb, A, ho, hA₁, hA₂⟩ := hN₂ z hz fun v hv hv0 => by
      obtain ⟨τ, hτ⟩ := hmax v hv hv0
      exact hτ.trans (Finset.single_le_sum (f := fun τ : X.Ψ => X.maj z τ (Data.emb τ.1 v))
        (fun _ _ => MajorantOperators.maj_nonneg hz _ _) (Finset.mem_univ τ))
    have h := (pnorm_near_half_max X.toData la P hP.1.1.1 (sSup S) hle _ ho
      (by rw [pnorm_lact_rmul X.toData hP.1.1 hγ hz hb]; exact hz'.le) A hA₂).2
    exact ⟨_, hA₁, by linarith⟩
  rcases N.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
  · refine ⟨{x₀}, Finset.singleton_nonempty _, by simpa using hx₀, fun P hP x hx =>
      ⟨x₀, Finset.mem_singleton_self _, ?_⟩, hbound _ (by simp) ?_⟩
    · by_contra h
      obtain ⟨y, hy, -⟩ := hmain P hP x hx (by linarith [hp0 P x₀, not_le.1 h])
      simp at hy
    · rw [Finset.card_singleton, Nat.cast_one]
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hT1) (Real.one_le_exp hG0)
  · refine ⟨N, ⟨y₀, hy₀⟩, hN₁, fun P hP x hx => ?_, hbound _ (Finset.card_pos.2 ⟨y₀, hy₀⟩) hN₃⟩
    rcases (hp0 P x).eq_or_lt with h | h
    · exact ⟨y₀, hy₀, by linarith [hp0 P y₀]⟩
    · exact hmain P hP x hx h

open ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries (E4) in

theorem exists_finite_net_rank_one : ∃ (X : DataX E4 1) (la : Wt X.Ψ 1) (P : Frame X.Ψ 1 → ℂ)
    (N : Finset (Frame X.Ψ 1)), P ∈ X.SS la ∧ la ≠ 0 ∧ (∃ x ∈ X.dom, P x ≠ 0) ∧ N.Nonempty ∧
    (∀ y ∈ N, y ∈ X.dom) ∧
    ∀ Q ∈ X.SS la, ∀ x ∈ X.dom, ∃ y ∈ N, X.pnorm la Q x ≤ 4 * X.pnorm la Q y := by
  obtain ⟨X, la, P, M, hP, hla, hx, hM, -, hT⟩ := exists_cuspData_rank_one
  obtain ⟨N, h1, h2, h3, -⟩ := exists_finite_net X la M (max 1 (∑ τ, X.spread la τ)) hM
    (le_max_right _ _) (lt_of_lt_of_le one_pos (le_max_left _ _)) hT
  exact ⟨X, la, P, N, hP, hla, hx, h1, h2, h3⟩

end GlobalTheory
