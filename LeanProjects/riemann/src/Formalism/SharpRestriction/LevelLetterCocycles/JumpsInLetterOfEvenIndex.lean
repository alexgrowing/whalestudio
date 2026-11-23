import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UniformizerUnitAndQFactor
import Formalism.SharpRestriction.LevelLetterCocycles.GCoordProp

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.DetA

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 Formalism.MainNotions.RamifiedCoefficientChains.S9.LD Formalism.MainNotions.RamifiedCoefficientChains.S9.DetD
  Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS TensorProduct

theorem det_const {O : Type} [CommRing O] {r : ℕ} (QQ P Zext : Matrix (Fin r) (Fin r) (PowerSeries O))
    (dd : Fin r → PowerSeries O) (zz : Fin r → O)
    (hid : QQ * Matrix.diagonal dd = P * Zext)
    (hZ : ∀ l k, PowerSeries.constantCoeff (Zext l k) = if l = k then zz k else 0) :
    (QQ.map PowerSeries.constantCoeff).det * ∏ k, PowerSeries.constantCoeff (dd k) =
      PowerSeries.constantCoeff P.det * ∏ k, zz k := by
  have h := congrArg (fun M => PowerSeries.constantCoeff (Matrix.det M)) hid
  simp only [Matrix.det_mul, map_mul, Matrix.det_diagonal, map_prod] at h
  have hZd : Zext.map PowerSeries.constantCoeff = Matrix.diagonal zz := by
    ext l k; simp only [Matrix.map_apply, hZ, Matrix.diagonal_apply]; split_ifs with h <;> simp [h]
  rw [RingHom.map_det PowerSeries.constantCoeff Zext] at h
  rw [RingHom.map_det PowerSeries.constantCoeff QQ] at h
  change (QQ.map PowerSeries.constantCoeff).det * _ = _ * (Zext.map PowerSeries.constantCoeff).det at h
  rw [hZd, Matrix.det_diagonal] at h
  exact h

section Num

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

theorem sum_mult_window (hK : Function.Bijective (algebraMap K₀ K)) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) (τ : K →ₐ[Qp] LL)
    (hτ : Formalism.MainNotions.LiftingTheory.Over W τ i) [FiniteDimensional LL ↥(DdRE PD T.ρ τ)] (lo hi : ℤ)
    (hwin : JumpsInV PD T.ρ τ (Set.Icc lo hi)) (hlohi : lo ≤ hi) :
    ∑ a ∈ Finset.Icc lo hi, multV PD T.ρ τ a = (finrank LL T.V : ℤ) := by
  obtain ⟨L, hL⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_lo PD T.ρ τ
  obtain ⟨H, hH⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_hi PD T.ρ τ
  have hsub : Finset.Icc lo hi ⊆ Finset.Ico (min L lo) (max H (hi + 1)) := by
    intro a ha
    simp only [Finset.mem_Icc, Finset.mem_Ico] at ha ⊢
    constructor <;> omega
  have h1 : ∑ a ∈ Finset.Icc lo hi, multV PD T.ρ τ a =
      ∑ a ∈ Finset.Ico (min L lo) (max H (hi + 1)), multV PD T.ρ τ a := by
    refine Finset.sum_subset hsub fun a _ ha => ?_
    refine Formalism.MainNotions.N.Pv.LocalLengthBound.rk_multV_of_not_jump PD T.ρ τ a fun hj => ha ?_
    exact Finset.mem_Icc.mpr (hwin a hj)
  rw [h1, Formalism.MainNotions.N.Pv.LocalLengthBound.rk_sum_multV PD T.ρ τ _ _ (by omega), hL _ (min_le_left _ _),
    hH _ (le_max_left _ _), finrank_bot, Nat.cast_zero, sub_zero]
  rw [← Formalism.MainNotions.N.Pv.LocalLengthBound.rk_DcrisL_map W hK hQ T hT τ,
    ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (Formalism.MainNotions.N.Pv.LocalLengthBound.rk_ιV_inj PD) _)]
  unfold Formalism.MainNotions.LiftingTheory.Over at hτ
  rw [hτ, Formalism.MainNotions.N.Pv.LocalLengthBound.rk_finrank_DcrisL W hK hQ T hT]

theorem deep_bound (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) (bi S η : ℕ) (hηb : η < bi)
    (hwin : JumpsInV PD T.ρ τ (Set.Icc (-((bi + S : ℕ) : ℤ)) (-(bi : ℤ)) ∪ Set.Icc (-(η : ℤ)) η))
    (hnn : ∀ a, 0 ≤ multV PD T.ρ τ a)
    (hsum : ∑ a ∈ Finset.Icc (-((bi + S : ℕ) : ℤ)) (η : ℤ), multV PD T.ρ τ a = (finrank LL T.V : ℤ)) :
    ((bi + S : ℕ) : ℤ) * finrank LL T.V + ∑ a ∈ Finset.Icc (-((bi + S : ℕ) : ℤ)) (η : ℤ), a * multV PD T.ρ τ a
      - Formalism.MainNotions.RamifiedCoefficientChains.S9.Cut.lowSum (PD := PD) T τ (bi + S) η ≤ (finrank LL T.V : ℤ) * S := by
  set h := ((bi + S : ℕ) : ℤ) with hh
  have hsplit : Finset.Icc (-h) (η : ℤ) = Finset.Icc (-h) (-(η : ℤ) - 1) ∪ Finset.Icc (-(η : ℤ)) η := by
    ext a; simp only [Finset.mem_union, Finset.mem_Icc]; push_cast [hh] at *; omega
  have hdisj : Disjoint (Finset.Icc (-h) (-(η : ℤ) - 1)) (Finset.Icc (-(η : ℤ)) η) := by
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_Icc] at ha hb; omega
  have e1 : h * finrank LL T.V + ∑ a ∈ Finset.Icc (-h) (η : ℤ), a * multV PD T.ρ τ a =
      ∑ a ∈ Finset.Icc (-h) (η : ℤ), multV PD T.ρ τ a * (h + a) := by
    rw [← hsum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => by ring
  rw [e1, hsplit, Finset.sum_union hdisj]
  unfold Formalism.MainNotions.RamifiedCoefficientChains.S9.Cut.lowSum
  rw [← hh, add_sub_cancel_right]
  have hle : ∀ a ∈ Finset.Icc (-h) (-(η : ℤ) - 1), multV PD T.ρ τ a * (h + a) ≤ (S : ℤ) * multV PD T.ρ τ a := by
    intro a ha
    simp only [Finset.mem_Icc] at ha
    by_cases hj : IsJumpV PD T.ρ τ a
    · have := hwin a hj
      simp only [Set.mem_union, Set.mem_Icc] at this
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : h + a ≤ S := by rw [hh]; push_cast; omega
        nlinarith [hnn a]
      · omega
    · rw [Formalism.MainNotions.N.Pv.LocalLengthBound.rk_multV_of_not_jump PD T.ρ τ a hj]; simp
  calc ∑ a ∈ Finset.Icc (-h) (-(η : ℤ) - 1), multV PD T.ρ τ a * (h + a)
      ≤ ∑ a ∈ Finset.Icc (-h) (-(η : ℤ) - 1), (S : ℤ) * multV PD T.ρ τ a := Finset.sum_le_sum hle
    _ = (S : ℤ) * ∑ a ∈ Finset.Icc (-h) (-(η : ℤ) - 1), multV PD T.ρ τ a := by rw [Finset.mul_sum]
    _ ≤ (S : ℤ) * ∑ a ∈ Finset.Icc (-h) (η : ℤ), multV PD T.ρ τ a := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        rw [hsplit, Finset.sum_union hdisj]
        have : 0 ≤ ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV PD T.ρ τ a := Finset.sum_nonneg fun a _ => hnn a
        linarith
    _ = (finrank LL T.V : ℤ) * S := by rw [hsum, mul_comm]

end Num

section Mem

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

def MiS (b : ZMod n → ℕ) (S η : ℕ) (i : ZMod n) : ZMod n → ℕ := fun j => if j = i then b i + S else b j + S + η
def hiS (b : ZMod n → ℕ) (S η : ℕ) (i : ZMod n) : ZMod n → ℕ := fun j => if j = i then η else b j + S + η

theorem jumps_in_letter_of_even_index (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) {d : ℕ} {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L}
    {b : ZMod n → ℕ} {S η m : ℕ} (hS : SetCS W d T₁ T₂ F b S η m) (i : ZMod n) (hie : (i.val + d) % 2 = 0) :
    Formalism.MainNotions.LiftingTheory.JumpsLet W T₂ (MiS b S η i) (hiS b S η i) := by
  intro j τ hτ a ha
  have hw := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumps₂ W hE hC hQ hS j τ hτ a ha
  simp only [MiS, hiS, Set.mem_Icc]
  by_cases hj : j = i
  · subst hj
    have hηb := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_eta_lt W hS j
    unfold JumpWinS at hw
    simp only [hie, if_true, Set.mem_union, Set.mem_Icc] at hw
    push_cast
    omega
  · simp only [hj, if_false]
    unfold JumpWinS at hw
    split_ifs at hw <;> (simp only [Set.mem_union, Set.mem_Icc] at hw; push_cast; omega)

theorem qpφ_mem (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    {d : ℕ} {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L}
    {b : ZMod n → ℕ} {S η m : ℕ} (hS : SetCS W d T₁ T₂ F b S η m) (i : ZMod n) (hie : (i.val + d) % 2 = 0)
    {r : ℕ} (e' : Fin r → W.DD T₂) (he' : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsBas W T₂ (i - 1) e') (k : Fin r) :
    Formalism.MainNotions.LiftingTheory.qp W ^ (b i + S) • W.φD T₂ (e' k) ∈ NDl W T₂ i := by
  have hT : IsCrys PD T₂.ρ := hS.2.2.2.2.2.1.2.1
  have hJL := jumps_in_letter_of_even_index W hE hC hQ hS i hie
  have h5T := h5 T₂ (MiS b S η i) (hiS b S η i) hT (fun τ j hτ => hJL j τ hτ)
  have hmem : e' k ∈ W.Nl T₂ (i - 1) := ⟨e' k, (he'.1 k).1, by simpa using (he'.1 k).2.1⟩
  have h1 := h5T.1 i (e' k) hmem
  simp only [MiS, if_true] at h1
  obtain ⟨-, -, w, hw⟩ := uniformizer_unit_and_q_factor W h9 hS.1 T₂ hT (by have := hS.2.1; omega)
  rw [Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.Q_eq_q W hS.1.2.1, hw, mul_pow, mul_smul] at h1
  have hN : Formalism.MainNotions.LiftingTheory.qp W ^ (b i + S) • W.φD T₂ (e' k) ∈ W.N T₂ := by
    have := (W.N T₂).smul_mem (((w⁻¹ : (LetA O n)ˣ) : LetA O n) ^ (b i + S)) h1
    rwa [smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul] at this
  refine ⟨hN, ?_, fun δ hδ => ?_⟩
  · rw [smul_comm, ← Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.φA_letE W i, ← Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.φD_smulA, (he'.1 k).2.1]
  · rw [Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.γD_smulA, map_pow, Formalism.MainNotions.RamifiedCoefficientChains.S9.LD.qp_mem W (uniformizer_mem_delta_invariants W) δ hδ,
      ← W.φγ_comm, (he'.1 k).2.2 δ hδ]

end Mem

section Main

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

theorem detAlg_of (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hB : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool W) (hDT : 11 ≤ PD.p → Formalism.MainNotions.RamifiedCoefficientChains.Sh.DetTool W)
    (hGC : Formalism.MainNotions.RamifiedCoefficientChains.S9.GCoord.GCoordProp W) : DetAlg W := by
  intro d T₁ T₂ F b S η m hS i hi e' m' u had σ Z hσ hZ0 hgN
  classical
  obtain ⟨hdom, hdvr, hfrac⟩ := hS.2.2.2.1
  have hA := hS.1
  have hT : IsCrys PD T₂.ρ := hS.2.2.2.2.2.1.2.1
  have hie : (i.val + d) % 2 = 0 := (Finset.mem_filter.mp hi).2
  have hp2 : 2 ≤ PD.p := PD.hp.two_le
  have hl0 : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h0'
    have h1' : ((PD.p : ℕ) : LL) = 0 := by rw [← map_natCast (algebraMap O LL), h0', map_zero]
    have h2 := W.v_l
    rw [h1', AddValuation.map_zero] at h2
    simp at h2
  obtain ⟨hz, hπu, -⟩ := uniformizer_unit_and_q_factor W h9 hA T₂ hT hp2
  have hqpu := qp_unit W hπu
  obtain ⟨he', hm'm, hmr, hu, -, hlow⟩ := had
  obtain ⟨⟨e, he⟩, -⟩ := hB hA T₂ hT i
  obtain ⟨red, hred, hredc⟩ := red_exists W T₂ i hz hπu e he
  have hy : ∀ k, Formalism.MainNotions.LiftingTheory.qp W ^ (b i + S) • W.φD T₂ (e' k) ∈ NDl W T₂ i :=
    qpφ_mem W hE hC hQ h5 h9 hS i hie e' he'
  have hPex : ∀ k, ∃ a : Fin (finrank LL T₂.V) → PowerSeries O,
      Formalism.MainNotions.LiftingTheory.qp W ^ (b i + S) • W.φD T₂ (e' k) = ∑ m₁, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (a m₁) • e m₁ :=
    fun k => (he.2 _ (hy k).1 (hy k).2).exists
  choose Pc hPc using hPex
  let P : Matrix (Fin (finrank LL T₂.V)) (Fin (finrank LL T₂.V)) (PowerSeries O) := fun m₁ k => Pc k m₁
  obtain ⟨τ, hτ⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_lift hA.1 (W.emb i)
  obtain ⟨u0, w0, hu0, hdetP, hw0⟩ := hDT hS.2.1 hA T₂ (MiS b S η i) (hiS b S η i) hT
    (jumps_in_letter_of_even_index W hE hC hQ hS i hie) i τ hτ _ e e' he he' (b i + S) P (fun k => hPc k)
  let kk : Fin m' → ℕ := fun j => (((b i + S : ℕ) : ℤ) + u j).toNat
  let g : Fin m' → W.DD T₂ := fun j => gE W T₂ (b i + S) (kk j) e' Z (Fin.castLE hmr j)
  have hgmem : ∀ j, g j ∈ NDl W T₂ i := fun j => hgN j hmr
  let cols : Fin (finrank LL T₂.V) → ↥(NDl W T₂ i) := fun k =>
    if hk : (k : ℕ) < m' then ⟨g ⟨k, hk⟩, hgmem _⟩ else ⟨_, hy k⟩
  have hcast : ∀ (k : Fin (finrank LL T₂.V)) (hk : (k : ℕ) < m'), Fin.castLE hmr (⟨k, hk⟩ : Fin m') = k :=
    fun k hk => Fin.ext rfl
  have hQex : ∀ k, ∃ a : Fin (finrank LL T₂.V) → PowerSeries O,
      ((cols k : ↥(NDl W T₂ i)) : W.DD T₂) = ∑ l, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (a l) • e l :=
    fun k => (he.2 _ (cols k).2.1 (cols k).2.2).exists
  choose QQc' hQQc using hQex
  let QQc : Matrix (Fin (finrank LL T₂.V)) (Fin (finrank LL T₂.V)) (PowerSeries O) := fun l k => QQc' k l

  have hhigh : ∀ k : Fin (finrank LL T₂.V), ¬ (k : ℕ) < m' → QQc' k = Pc k := by
    intro k hk
    have h1 := hQQc k
    simp only [cols, hk, dite_false] at h1
    exact (he.2 _ (hy k).1 (hy k).2).unique h1 (hPc k)

  have hlowc : ∀ (k : Fin (finrank LL T₂.V)) (hk : (k : ℕ) < m') (l : Fin (finrank LL T₂.V)),
      (PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) ^ kk ⟨k, hk⟩ * QQc' k l = (P * Z) l k := by
    intro k hk l
    have h1 := hQQc k
    simp only [cols, hk, dite_true] at h1
    have hg' := hgmem ⟨k, hk⟩
    simp only [g, hcast k hk] at hg' h1
    exact hGC T₂ i (b i + S) (kk ⟨k, hk⟩) e e' he P Z (fun k' => hPc k') hz hqpu k hg'.1 hg'.2 _ h1 l
  let dd : Fin (finrank LL T₂.V) → PowerSeries O := fun k =>
    if hk : (k : ℕ) < m' then (PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) ^ kk ⟨k, hk⟩ else 1
  let Zext : Matrix (Fin (finrank LL T₂.V)) (Fin (finrank LL T₂.V)) (PowerSeries O) := fun l k =>
    if (k : ℕ) < m' then Z l k else (if l = k then 1 else 0)
  have hid : QQc * Matrix.diagonal dd = P * Zext := by
    ext l k
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    by_cases hk : (k : ℕ) < m'
    · simp only [QQc, dd, Zext, dif_pos hk, if_pos hk]
      rw [mul_comm, hlowc k hk l, Matrix.mul_apply]
    · simp only [QQc, dd, Zext, dif_neg hk, if_neg hk, mul_one]
      rw [hhigh k hk]
      simp [P]
  let zz : Fin (finrank LL T₂.V) → O := fun k => if (k : ℕ) < m' then ((PD.p : ℕ) : O) ^ σ else 1
  have hZext : ∀ l k, PowerSeries.constantCoeff (Zext l k) = if l = k then zz k else 0 := by
    intro l k
    by_cases hk : (k : ℕ) < m'
    · simp only [Zext, zz, if_pos hk]
      exact hZ0 l k
    · simp only [Zext, zz, if_neg hk]
      split_ifs <;> simp
  have hconst := det_const QQc P Zext dd zz hid hZext

  let κ : ℕ → ℕ := fun k => if hk : k < m' then kk ⟨k, hk⟩ else 0
  have hsumκ : ∑ k : Fin (finrank LL T₂.V), κ k = ∑ j : Fin m', kk j := by
    rw [Fin.sum_univ_eq_sum_range κ, ← Finset.sum_subset (Finset.range_subset_range.mpr hmr)
      (fun k _ hk => by rw [Finset.mem_range] at hk; simp only [κ, dif_neg hk]), Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => by simp [κ, j.2]
  have hsumσ : ∑ k : Fin (finrank LL T₂.V), (if (k : ℕ) < m' then σ else 0) = σ * m' := by
    rw [Fin.sum_univ_eq_sum_range (fun k => if k < m' then σ else 0),
      ← Finset.sum_subset (Finset.range_subset_range.mpr hmr)
        (fun k _ hk => by rw [Finset.mem_range] at hk; simp only [if_neg hk]), Finset.sum_range]
    simp [Finset.sum_const, mul_comm]
  have hdd : ∏ k, PowerSeries.constantCoeff (dd k) = ((PD.p : ℕ) : O) ^ (∑ j : Fin m', kk j) := by
    rw [← hsumκ, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun k _ => ?_
    by_cases hk : (k : ℕ) < m'
    · simp only [dd, κ, dif_pos hk, map_pow, map_add, PowerSeries.constantCoeff_X,
        PowerSeries.constantCoeff_C, zero_add]
    · simp [dd, κ, dif_neg hk]
  have hzz : ∏ k, zz k = ((PD.p : ℕ) : O) ^ (σ * m') := by
    rw [← hsumσ, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun k _ => ?_
    by_cases hk : (k : ℕ) < m' <;> simp [zz, hk]
  have hPd : PowerSeries.constantCoeff P.det = PowerSeries.constantCoeff u0 * ((PD.p : ℕ) : O) ^ w0 := by
    rw [hdetP, map_mul, map_pow, map_add, PowerSeries.constantCoeff_X, zero_add, map_natCast]
  have hM0 : (Matrix.of fun l k => red (cols k) l) = QQc.map PowerSeries.constantCoeff := by
    ext l k
    simp only [Matrix.of_apply, hredc (cols k) (QQc' k) (hQQc k)]
    rfl
  rw [hdd, hzz, hPd, ← hM0, mul_assoc, ← pow_add] at hconst

  obtain ⟨hfd⟩ : Nonempty (FiniteDimensional LL ↥(DdRE PD T₂.ρ τ)) := ⟨Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.fd_DdRE W hQ hS i τ hτ⟩
  have hηb := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_eta_lt W hS i
  have hwin : JumpsInV PD T₂.ρ τ (Set.Icc (-((b i + S : ℕ) : ℤ)) (-((b i : ℕ) : ℤ)) ∪ Set.Icc (-(η : ℤ)) η) := by
    intro a ha
    have hw := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumps₂ W hE hC hQ hS i τ hτ a ha
    unfold JumpWinS at hw
    simpa [hie] using hw
  have hwin' : JumpsInV PD T₂.ρ τ (Set.Icc (-((b i + S : ℕ) : ℤ)) η) := by
    intro a ha
    have := hwin a ha
    simp only [Set.mem_union, Set.mem_Icc] at this ⊢
    omega
  have hsum := sum_mult_window W hA.1 hQ T₂ hT i τ hτ _ _ hwin' (by omega)
  have hdeep := deep_bound (PD := PD) T₂ τ (b i) S η hηb hwin
    (fun a => Formalism.MainNotions.N.Pv.LocalLengthBound.rk_multV_nonneg (O := O) T₂ τ a) hsum
  have hw0' : (w0 : ℤ) = ((b i + S : ℕ) : ℤ) * (finrank LL T₂.V) +
      ∑ a ∈ Finset.Icc (-((b i + S : ℕ) : ℤ)) (η : ℤ), a * multV PD T₂.ρ τ a := by
    rw [hw0]; simp [MiS, hiS]
  have hkk : ∑ j : Fin m', ((kk j : ℕ) : ℤ) = ∑ j : Fin m', (((b i + S : ℕ) : ℤ) + u j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [kk]
    rw [Int.toNat_of_nonneg (by have := (hu j).1; push_cast; omega)]
  have hlow' := hlow τ hτ
  refine ⟨finrank LL T₂.V, red, hred, m', hm'm, g, hgmem, cols, fun k => ?_, ?_⟩
  · by_cases hk : (k : ℕ) < m'
    · right; exact ⟨⟨k, hk⟩, by simp [cols, hk]⟩
    · left
      simp only [cols, hk, dite_false]
      refine ⟨W.φD T₂ (e' k), Submodule.subset_span ⟨1, W.AΔ.one_mem, e' k,
        ⟨(he'.1 k).1, (he'.1 k).2⟩, by simp⟩, by simp⟩
  · by_cases hAB : (∑ j : Fin m', kk j) ≤ w0 + σ * m'
    · refine ⟨w0 + σ * m' - ∑ j : Fin m', kk j, ?_, dvd_of_mul_pow _ _ _ hl0
        (hu0.map PowerSeries.constantCoeff) _ _ hAB hconst⟩
      have h1 : ((∑ j : Fin m', kk j : ℕ) : ℤ) ≥ Formalism.MainNotions.RamifiedCoefficientChains.S9.Cut.lowSum (PD := PD) T₂ τ (b i + S) η := by
        push_cast; rw [hkk]; exact hlow'
      have h2 : (σ : ℤ) * m' ≤ 2 * ⌊cD PD.p (hpar n b S + η)⌋₊ * m := by
        have := Nat.mul_le_mul hσ hm'm; exact_mod_cast this
      have h3 : ((w0 + σ * m' - ∑ j : Fin m', kk j : ℕ) : ℤ) =
          (w0 : ℤ) + σ * m' - ((∑ j : Fin m', kk j : ℕ) : ℤ) := by
        rw [Nat.cast_sub hAB]; push_cast; ring
      have e1 : (w0 : ℤ) - Formalism.MainNotions.RamifiedCoefficientChains.S9.Cut.lowSum (PD := PD) T₂ τ (b i + S) η ≤
          (finrank LL T₂.V : ℤ) * S := by
        rw [hw0']; push_cast at hdeep ⊢; linarith
      have : ((w0 + σ * m' - ∑ j : Fin m', kk j : ℕ) : ℤ) ≤
          ((finrank LL T₂.V * S + 2 * ⌊cD PD.p (hpar n b S + η)⌋₊ * m : ℕ) : ℤ) := by
        rw [h3]
        have h1' : ((∑ j : Fin m', kk j : ℕ) : ℤ) ≥ Formalism.MainNotions.RamifiedCoefficientChains.S9.Cut.lowSum (PD := PD) T₂ τ (b i + S) η := h1
        push_cast
        push_cast at h1' h2
        linarith
      exact_mod_cast this
    · refine ⟨0, Nat.zero_le _, ?_⟩
      push Not at hAB
      have hsplit : ((PD.p : ℕ) : O) ^ (∑ j : Fin m', kk j) =
          ((PD.p : ℕ) : O) ^ (∑ j : Fin m', kk j - (w0 + σ * m')) * ((PD.p : ℕ) : O) ^ (w0 + σ * m') := by
        rw [← pow_add, Nat.sub_add_cancel hAB.le]
      rw [hsplit, ← mul_assoc] at hconst
      have h4 := mul_right_cancel₀ (pow_ne_zero _ hl0) hconst
      have hunit : IsUnit (Matrix.of fun l k => red (cols k) l).det :=
        isUnit_of_mul_isUnit_left (h4 ▸ hu0.map PowerSeries.constantCoeff)
      rw [pow_zero]
      exact hunit.dvd

end Main

end Formalism.MainNotions.RamifiedCoefficientChains.S9.DetA
