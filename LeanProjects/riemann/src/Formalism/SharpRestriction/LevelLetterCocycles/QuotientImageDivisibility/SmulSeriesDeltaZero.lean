import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LengthBoundOfHypotheses
import Formalism.SharpRestriction.LevelLetterCocycles.SemisimpleLetterIffForallMem
import Formalism.SharpRestriction.LevelLetterCocycles.LatticeMembershipPolynomialGamma

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section H41

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem pullJ_Q {c : ZMod n} {Bn : ℕ} (hM : ∀ z ∈ W.Nl T (c - 1), W.Q ^ Bn • W.φD T z ∈ W.N T)
    {z : W.DD T} (hz : z ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (c - 1) 1) : W.Q ^ Bn • z ∈ W.N T := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, ⟨hyN, hyE, -⟩, rfl⟩ := hx
    simp only [pow_one]
    apply hM
    unfold Formalism.BasicNotions.LocWach.Nl
    rw [Submodule.mem_map]
    exact ⟨y, hyN, by simpa using hyE⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact (W.N T).add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact (W.N T).smul_mem a hx

theorem trunc_s_Δ [IsDomain O] {j M X σ y : ℕ} {r s : LetA O n} (hr : Formalism.MainNotions.CrystallineLiftingInputs.IsRem W j M X y r)
    (hrs : ((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y * s = ((PD.p : ℕ) : LetA O n) ^ σ * r)
    (δ : W.Gam) (hδ : δ ∈ W.DelF) : W.γA δ s = s := by
  have hDel : ∀ g h : W.Gam, g ∈ W.DelF → h ∈ W.DelF → g * h ∈ W.DelF := by
    intro g h hg hh
    rw [W.DelF_def] at hg hh ⊢
    obtain ⟨k, hk, hgk⟩ := hg
    obtain ⟨m, hm, hhm⟩ := hh
    refine ⟨k * m, Nat.mul_pos hk hm, ?_⟩
    rw [mul_pow, pow_mul, hgk, one_pow, mul_comm k m, pow_mul, hhm, one_pow, one_mul]
  have hInv : ∀ g : W.Gam, g ∈ W.DelF → g⁻¹ ∈ W.DelF := by
    intro g hg
    rw [W.DelF_def] at hg ⊢
    obtain ⟨k, hk, hgk⟩ := hg
    exact ⟨k, hk, by rw [inv_pow, hgk, inv_one]⟩
  have hπ₁ : W.γ₀ δ W.π₀₁ = W.π₀₁ := by
    unfold Formalism.BasicNotions.LocWach.π₀₁
    rw [map_add, map_sub, map_one, map_natCast, map_sum]
    congr 1
    refine Finset.sum_nbij' (δ * ·) (δ⁻¹ * ·) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      exact hDel _ _ hδ ha
    · intro a ha
      exact hDel _ _ (hInv _ hδ) ha
    · intro a _
      simp
    · intro a _
      simp
    · intro a _
      rw [map_mul, AlgHom.mul_apply]
  have hπ : W.γA δ W.π₀ = W.π₀ := by
    unfold Formalism.BasicNotions.LocWach.γA Formalism.BasicNotions.letγ Formalism.BasicNotions.LocWach.π₀
    funext i
    exact hπ₁
  have hr' : W.γA δ r = r := by
    obtain ⟨⟨a, rfl⟩, -⟩ := hr
    simp only [map_sum, map_mul, map_pow, AlgHom.commutes, hπ]
  have hp0 : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h
    have h1 := W.v_l
    have h2 : ((PD.p : ℕ) : LL) = 0 := by
      rw [← map_natCast (algebraMap O LL) PD.p, h, map_zero]
    rw [h2, AddValuation.map_zero] at h1
    simp at h1
  have hpX : ((PD.p : ℕ) : PowerSeries O) ≠ 0 := by
    intro h
    apply hp0
    have h3 := congrArg PowerSeries.constantCoeff h
    simpa using h3
  have hcan : ∀ (k : ℕ) (x x' : LetA O n), ((PD.p : ℕ) : LetA O n) ^ k * x =
      ((PD.p : ℕ) : LetA O n) ^ k * x' → x = x' := by
    intro k x x' hxx
    funext i
    have hi := congrFun hxx i
    exact mul_left_cancel₀ (pow_ne_zero k hpX) hi
  have h2 : ((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y * W.γA δ s =
      ((PD.p : ℕ) : LetA O n) ^ σ * r := by
    have h4 := congrArg (W.γA δ) hrs
    simpa only [map_mul, map_pow, map_natCast, hr'] using h4
  apply hcan (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y)
  rw [h2, hrs]

theorem trunc_DL [IsDomain O] {c : ZMod n} {M X σ : ℕ} {w z : W.DD T}
    (hz : Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T (c - 1) 1 M X σ w z) (hw : Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c - 1) w) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c z := by
  obtain ⟨cs, r, s, ⟨-, hcDL, -⟩, hrs, rfl⟩ := hz
  have hφ : ∀ x, Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c - 1) x → Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (((W.φD T) ^ 1) x) := by
    intro x hx
    rw [pow_one]
    exact (Formalism.MainNotions.WachCoordinates.Br.φl (W := W) T c ⟨x, hx⟩).2
  have hsub : ∀ x y, Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x → Formalism.MainNotions.CrystallineLiftingInputs.DL W T c y →
      Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (x - y) := by
    intro x y hx hy
    exact (Formalism.MainNotions.WachCoordinates.Br.DDl W T c).sub_mem hx hy
  have hosmul : ∀ (o : O) x, Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x → Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (o • x) := by
    rintro o x ⟨hx1, hx2⟩
    show _ ∧ _
    refine ⟨?_, fun δ hδ => ?_⟩
    · rw [smul_comm, hx1]
    · rw [map_smul, hx2 δ hδ]
  have hasmul : ∀ (a : LetA O n) x, (∀ δ ∈ W.DelF, W.γA δ a = a) →
      Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x → Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (a • x) := by
    rintro a x ha ⟨hx1, hx2⟩
    show _ ∧ _
    refine ⟨?_, fun δ hδ => ?_⟩
    · rw [smul_comm, hx1]
    · rw [Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA' W T δ a x, ha δ hδ, hx2 δ hδ]
  apply hsub
  · exact hosmul _ _ (hφ w hw)
  · exact (Formalism.MainNotions.WachCoordinates.Br.DDl W T c).sum_mem (fun y _ =>
      hasmul _ _ (fun δ hδ => trunc_s_Δ W (hrs y).1 (hrs y).2 δ hδ) (hφ _ (hcDL y).1))

end H41

section locP_coef_Lsh

variable (W : LocWach PD LL O v n)

def del0 {V : Type} [Zero V] (C : V) : ℤ → V := fun k => if k = 0 then C else 0

theorem smulSeries_delta_zero {V : Type} [AddCommGroup V] [Module LL V] (g : PowerSeries LL) (C : V) (r : ℕ) :
    smulS g (del0 C) (r : ℤ) = PowerSeries.coeff r g • C := by
  unfold smulS
  rw [finsum_eq_single _ r]
  · simp [del0]
  · intro j hj
    have hne : (r : ℤ) - (j : ℤ) ≠ 0 := by
      intro h
      apply hj
      exact_mod_cast (sub_eq_zero.mp h).symm
    simp [del0, hne]

theorem lowerBound_delta_zero {V : Type} [AddCommGroup V] (C : V) : LB 0 (del0 C) := by
  intro k hk
  simp [del0, hk.ne]

theorem LB_of_mul {V : Type} [AddCommGroup V] [Module LL V] {m : ℤ} {g : ℤ → V} (hg : LB m g)
    (u : PowerSeries LL) (hu0 : constantCoeff u ≠ 0) (Bn : ℕ)
    (h : LB (2 * Bn) (smulS ((X * u) ^ Bn) g)) : LB Bn g := by
  have hw : LB m (smulS (u ^ Bn) g) := LB_smulS hg _
  have hcu : constantCoeff (u ^ Bn) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ hu0
  have hwB : LB Bn (smulS (u ^ Bn) g) := by
    intro k hk
    have hk2 := h (k + Bn) (by omega)
    rw [mul_pow, smulS_mul hg, smulS_X_pow hw] at hk2
    simpa using hk2
  have hg' : g = smulS (u ^ Bn)⁻¹ (smulS (u ^ Bn) g) := by
    rw [← smulS_mul hg, PowerSeries.inv_mul_cancel _ hcu, smulS_one hg]
  rw [hg']
  exact LB_smulS hwB _

end locP_coef_Lsh

section L41b

variable (W : LocWach PD LL O v n)

theorem pullJ_LB (T : LocLat G Qp LL O) {c : ZMod n} {Bn : ℕ} (ζ : LL)
    (hM : ∀ z ∈ W.Nl T (c - 1), W.Q ^ Bn • W.φD T z ∈ W.N T)
    (hφN : ∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) (j : ℤ), j < k →
      W.levN T c ζ ⟨_, hk⟩ j = 0)
    {z : W.DD T} (hz : z ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (c - 1) 1) (hQz : W.Q ^ Bn • z ∈ W.N T) :
    LB Bn (W.levN T c ζ ⟨W.Q ^ Bn • z, hQz⟩) := by
  have key : ∀ z ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (c - 1) 1, ∀ h : W.Q ^ Bn • z ∈ W.N T,
      LB Bn (W.levN T c ζ ⟨W.Q ^ Bn • z, h⟩) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, ⟨hyN, -⟩, rfl⟩ := hx
      intro h
      have h' : W.Q ^ Bn • W.φD T y ∈ W.N T := by rwa [pow_one] at h
      have e : (⟨_, h⟩ : ↥(W.N T)) = ⟨_, h'⟩ := Subtype.ext (by simp only [pow_one])
      rw [e]
      exact hφN ⟨y, hyN⟩ Bn h'
    | zero =>
      intro h
      have e : (⟨_, h⟩ : ↥(W.N T)) = 0 := Subtype.ext (by simp)
      rw [e, map_zero]
      intro k _
      rfl
    | add x y hx hy ihx ihy =>
      intro h
      have hx' := pullJ_Q W T hM hx
      have hy' := pullJ_Q W T hM hy
      have e : (⟨_, h⟩ : ↥(W.N T)) = ⟨_, hx'⟩ + ⟨_, hy'⟩ :=
        Subtype.ext (by simp only [Submodule.coe_add]; exact smul_add _ _ _)
      rw [e, map_add]
      exact LB_add (ihx hx') (ihy hy')
    | smul a x hx ihx =>
      intro h
      have hx' := pullJ_Q W T hM hx
      have e : (⟨_, h⟩ : ↥(W.N T)) = a • ⟨_, hx'⟩ :=
        Subtype.ext (by simp only [Submodule.coe_smul]; exact smul_comm _ _ _)
      rw [e]
      have hs : W.levN T c ζ (a • ⟨_, hx'⟩) = smulS (W.lev c ζ a) (W.levN T c ζ ⟨_, hx'⟩) := by
        funext k
        rw [W.levN_smul]
        rfl
      rw [hs]
      exact LB_smulS (ihx hx') _
  exact key z hz hQz

theorem map_pullJ {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (hT₁ : IsCrys PD T₁.ρ)
    (hT₂ : IsCrys PD T₂.ρ) {i : ZMod n} {z : W.DD T₁} (hz : z ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T₁ i 1) :
    W.map F z ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T₂ i 1 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, ⟨hyN, hyE, hyΔ⟩, rfl⟩ := hx
    refine Submodule.subset_span ⟨W.map F y, ⟨W.map_N F hT₁ hT₂ _ hyN, ?_⟩, ?_⟩
    · show _ ∧ _
      refine ⟨?_, fun δ hδ => ?_⟩
      · rw [← LinearMap.map_smul_of_tower, hyE]
      · rw [← W.map_γ, hyΔ δ hδ]
    · simp only [pow_one]
      rw [W.map_φ]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ a hx

end L41b

section L41d

variable {LL' : Type} [Field LL'] {V : Type} [AddCommGroup V] [Module LL' V]

theorem vals_of_div {m : ℤ} {dd e : ℤ → V} (hdd : LB m dd) (u : PowerSeries LL')
    (hu0 : constantCoeff u ≠ 0) (K : ℕ) (he : smulS ((X * u) ^ K) dd = e) (Z : Submodule LL' V)
    (hZ : ∀ k, e k ∈ Z) : ∀ k, dd k ∈ Z := by
  have hw : LB m (smulS (u ^ K) dd) := LB_smulS hdd _
  have hcu : constantCoeff (u ^ K) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ hu0
  have hdd' : dd = smulS (u ^ K)⁻¹ (smulS (u ^ K) dd) := by
    rw [← smulS_mul hdd, PowerSeries.inv_mul_cancel _ hcu, smulS_one hdd]
  have hwZ : ∀ k, smulS (u ^ K) dd k ∈ Z := by
    intro k
    have hk := hZ (k + K)
    rw [← he, mul_pow, smulS_mul hdd, smulS_X_pow hw] at hk
    simpa using hk
  intro k
  have hN : k - m < (((k - m).toNat + 1 : ℕ) : ℤ) := by
    have := Int.self_le_toNat (k - m)
    push_cast
    omega
  rw [hdd', smulS_eq_sum hw _ k _ hN]
  exact Z.sum_mem (fun j _ => Z.smul_mem _ (hwZ _))

end L41d

section L41c

variable (W : LocWach PD LL O v n)

theorem contentBoundLevel_of [NeZero n] (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hLev : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W)
    (hφN : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (c : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
      ∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) (j : ℤ), j < k →
        W.levN T c ζ ⟨_, hk⟩ j = 0)
    (hT2 : Formalism.MainNotions.CrystallineLiftingInputs.TTool2 W) (hTH : Formalism.MainNotions.CrystallineLiftingInputs.THor W) (hG : Formalism.MainNotions.RamifiedCoefficientChains.S9.LemmaGs W)
    (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) : ContentBoundLevel W := by
  intro d T₁ T₂ F b S η m hset c hc
  have hset' := hset
  obtain ⟨hCA, hl, hn, ⟨hDom, hDVR, hFrac⟩, -, hSur, -, -, -, -⟩ := hset'
  haveI := hDom
  haveI := hDVR
  haveI := hFrac
  have hCA' := hCA
  obtain ⟨hbij, hs, hp2⟩ := hCA
  have hK1 : Module.finrank K₀ K = 1 := Formalism.MainNotions.UnusedSlot80.SatW.finrank_one_of_bij' hbij
  obtain ⟨-, -, h9₁⟩ := h9 T₁ hSur.1 hs hp2
  obtain ⟨hR, hmod₁⟩ := h9₁ hK1
  obtain ⟨-, -, h9₂⟩ := h9 T₂ hSur.2.1 hs hp2
  obtain ⟨-, hmod₂⟩ := h9₂ hK1
  have hT₁ := hSur.1
  have hT₂ := hSur.2.1
  have h5₁ := h5 T₁ (boxM d b S η) (boxH d b S η) hT₁ (rk_jumpsLet₁ W hset)
  have h5₂ := h5 T₂ (boxM d b S η) (boxH d b S η) hT₂ (rk_jumpsLet₂ W hE hC hQ hset)
  have hcD : (c.val + d) % 2 = 0 := (Finset.mem_filter.1 hc).2
  have hc1 : ((c - 1).val + d) % 2 = 1 := by
    have := Formalism.MainNotions.RamifiedCoefficientChains.S9.parity_succ hn d (c - 1)
    rw [sub_add_cancel] at this
    omega
  have hMc : boxM d b S η c = b c + S := if_pos hcD
  have hM₁ : ∀ z ∈ W.Nl T₁ (c - 1), W.Q ^ (b c + S) • W.φD T₁ z ∈ W.N T₁ := by
    rw [← hMc]; exact h5₁.1 c
  have hM₂ : ∀ z ∈ W.Nl T₂ (c - 1), W.Q ^ (b c + S) • W.φD T₂ z ∈ W.N T₂ := by
    rw [← hMc]; exact h5₂.1 c
  have hπU := Formalism.MainNotions.UnusedSlot35.DssRec.π₀_unit W h9 hCA' T₁ hT₁
  obtain ⟨U, hU⟩ := qp_eq_unit W hs hR
  have hp : (PD.p : LL) ≠ 0 := Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W

  obtain ⟨E, hE', hGx⟩ := hG d T₁ T₂ F b S η m hset (c - 1) hc1
  have e12 : c - 1 - 2 = c - 1 - 1 - 1 := by ring
  rw [e12] at hGx
  set gG : ℤ := ⌈(E : ℝ) + Formalism.MainNotions.CrystallineLiftingInputs.sig2 PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) +
    ((b (c - 1 - 1) + S : ℕ) : ℝ) - (b (c - 1) : ℝ)⌉ with hgG
  set σ₁ : ℕ := ⌈(((1 : ℕ) : ℝ) + ((b c + S : ℕ) : ℝ)) / ((PD.p : ℝ) - 1) + 1⌉₊ with hσ₁
  have hTC : Formalism.MainNotions.CrystallineLiftingInputs.TCase PD.p 1 1 (b c + S) σ₁ := Or.inl ⟨rfl, le_rfl, rfl⟩
  obtain ⟨hTT, hnat⟩ := hT2 hCA' hl 1 1 (b c + S) σ₁ hTC
  refine ⟨(σ₁ : ℤ) + gG, ?_, fun ell hellD hellC => ?_⟩
  · have hl1 : (0 : ℝ) < (PD.p : ℝ) - 1 := by
      have : (11 : ℝ) ≤ PD.p := by exact_mod_cast hl
      linarith
    have h1 := Nat.ceil_lt_add_one (a := (((1 : ℕ) : ℝ) + ((b c + S : ℕ) : ℝ)) / ((PD.p : ℝ) - 1) + 1)
      (by positivity)
    have h2 := Int.ceil_lt_add_one ((E : ℝ) + Formalism.MainNotions.CrystallineLiftingInputs.sig2 PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) +
      ((b (c - 1 - 1) + S : ℕ) : ℝ) - (b (c - 1) : ℝ))
    have hEle : (E : ℝ) ≤ Formalism.MainNotions.RamifiedCoefficientChains.S9.EG PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S) η S := by
      refine hE'.trans ?_
      rw [Formalism.MainNotions.RamifiedCoefficientChains.S9.EG]
      have : 3 * Formalism.MainNotions.RamifiedCoefficientChains.aR PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) ≤
          3 * (Formalism.MainNotions.RamifiedCoefficientChains.S9.aN PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) : ℝ) := by
        have := Nat.le_ceil (Formalism.MainNotions.RamifiedCoefficientChains.aR PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η))
        unfold Formalism.MainNotions.RamifiedCoefficientChains.S9.aN; linarith
      have := div_le_div_of_nonneg_right
        (a := 3 * Formalism.MainNotions.RamifiedCoefficientChains.aR PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) + S + 2 * η)
        (b := 3 * (Formalism.MainNotions.RamifiedCoefficientChains.S9.aN PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) : ℝ) + S + 2 * η)
        (by linarith) hl1.le
      linarith
    have hs2 : Formalism.MainNotions.CrystallineLiftingInputs.sig2 PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) =
        Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) := by
      simp only [Formalism.MainNotions.CrystallineLiftingInputs.sig2, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂]
    rw [hσ₁, hgG]
    push_cast at h1 h2 ⊢
    rw [hs2] at h2
    have hnum : (1 + ((b c : ℝ) + (S : ℝ))) / ((PD.p : ℝ) - 1) =
        ((b c : ℝ) + (S : ℝ) + 1) / ((PD.p : ℝ) - 1) := by ring
    rw [hs2] at ⊢
    linarith [hnum]
  · obtain ⟨n₁, hn₁N, hFN, hn₁D, hcmp⟩ := hGx ell hellD hellC
    set Bn : ℕ := b c + S with hBn
    have hn₁Δ : n₁ ∈ W.NΔ T₁ := ⟨hn₁N, hn₁D.2⟩
    obtain ⟨x', hx'Δ, hx'e⟩ := hmod₁.2 n₁ hn₁Δ
    have hn₁I : Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ (c - 1) n₁ :=
      ⟨hn₁D, ⟨0, 0, by simpa using hn₁N⟩, ⟨x', hx'Δ.1, hx'Δ.2, by rw [pow_one]; exact hx'e⟩⟩
    obtain ⟨z₁, hz₁⟩ := (hTT T₁ hT₁ (c - 1)).1 n₁ hn₁I
    obtain ⟨hz₁P, p₁, hp₁, hγz⟩ := (hTT T₁ hT₁ (c - 1)).2.1 n₁ z₁ hn₁I hz₁
    have hQz : W.Q ^ Bn • z₁ ∈ W.N T₁ := by
      have e : z₁ = (z₁ - ((PD.p : ℕ) : O) ^ σ₁ • ((W.φD T₁) ^ 1) n₁) +
          ((PD.p : ℕ) : O) ^ σ₁ • ((W.φD T₁) ^ 1) n₁ := by abel
      rw [e, smul_add, osmul_comm W T₁]
      refine (W.N T₁).add_mem (pullJ_Q W T₁ hM₁ hz₁P) ?_
      rw [← algebraMap_smul (LetA O n), pow_one]
      exact (W.N T₁).smul_mem _ (hM₁ n₁ (mem_Nl W T₁ hn₁N hn₁D.1))
    have hUQ : ∀ (T : LocLat G Qp LL O) (x : W.DD T), W.Q ^ Bn • x ∈ W.N T →
        Formalism.MainNotions.LiftingTheory.qp W ^ Bn • x ∈ W.N T := fun T x hx => by
      rw [hU, mul_pow, mul_smul]; exact (W.N T).smul_mem _ hx
    have hz₁D := trunc_DL W T₁ hz₁ hn₁D
    have hy'N : Formalism.MainNotions.LiftingTheory.qp W ^ Bn • p₁ ∈ W.N T₁ := hUQ T₁ _ (pullJ_Q W T₁ hM₁ hp₁)
    have hy'eq : W.π₀ • (Formalism.MainNotions.LiftingTheory.qp W ^ Bn • p₁) = W.γ T₁ z₁ - z₁ := by
      rw [hγz, Formalism.MainNotions.CrystallineLiftingInputs.fMX, pow_one, mul_smul]
    have hz₁I : Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c z₁ := by
      refine ⟨hz₁D, ⟨1, Bn, ?_⟩, ⟨Formalism.MainNotions.LiftingTheory.qp W ^ Bn • p₁, hy'N, fun δ hδ => ?_, ?_⟩⟩
      · simpa [Formalism.MainNotions.LiftingTheory.pk] using hUQ T₁ z₁ hQz
      · apply Formalism.MainNotions.UnusedSlot80.SatW.smul_cancel W T₁ hπU
        calc W.π₀ • W.γD T₁ δ (Formalism.MainNotions.LiftingTheory.qp W ^ Bn • p₁)
            = W.γD T₁ δ (W.π₀ • (Formalism.MainNotions.LiftingTheory.qp W ^ Bn • p₁)) := by
              rw [Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA' W T₁ δ W.π₀ (Formalism.MainNotions.LiftingTheory.qp W ^ Bn • p₁),
                Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W δ hδ]
          _ = W.γD T₁ δ (W.γ T₁ z₁ - z₁) := by rw [hy'eq]
          _ = W.γ T₁ z₁ - z₁ := by
              rw [map_sub]
              show W.γD T₁ δ (W.γD T₁ W.gam z₁) - W.γD T₁ δ z₁ = W.γD T₁ W.gam z₁ - z₁
              rw [← W.γD_mul, mul_comm, W.γD_mul, hz₁D.2 δ hδ]
          _ = W.π₀ • (Formalism.MainNotions.LiftingTheory.qp W ^ Bn • p₁) := hy'eq.symm
      · rw [pow_one, hy'eq]

    have hFD : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (c - 1) (W.map F n₁) :=
      ⟨by rw [← Formalism.MainNotions.UnusedSlot80.ArcC.map_smulA, hn₁D.1], fun δ hδ => by rw [← W.map_γ, hn₁D.2 δ hδ]⟩
    have hFI : Formalism.MainNotions.CrystallineLiftingInputs.InI W T₂ (c - 1) (W.map F n₁) := by
      refine ⟨hFD, ⟨0, 0, by simpa using hFN⟩, ⟨W.map F x', W.map_N F hT₁ hT₂ _ hx'Δ.1,
        fun δ hδ => by rw [← W.map_γ, hx'Δ.2 δ hδ], ?_⟩⟩
      rw [pow_one, ← Formalism.MainNotions.UnusedSlot80.ArcC.map_smulA, ← hx'e, map_sub]
      show W.γD T₂ W.gam (W.map F n₁) - W.map F n₁ = W.map F (W.γD T₁ W.gam n₁) - W.map F n₁
      rw [W.map_γ]
    have hFNl : W.map F n₁ ∈ W.Nl T₂ (c - 1) := mem_Nl W T₂ hFN hFD.1
    have hB : W.Q ^ Bn • W.map F z₁ ∈ W.N T₂ := by
      have hP := map_pullJ W F hT₁ hT₂ hz₁P
      rw [map_sub, Formalism.MainNotions.UnusedSlot80.ArcC.map_smulO, pow_one, W.map_φ] at hP
      have e : W.map F z₁ = (W.map F z₁ - ((PD.p : ℕ) : O) ^ σ₁ • W.φD T₂ (W.map F n₁)) +
          ((PD.p : ℕ) : O) ^ σ₁ • W.φD T₂ (W.map F n₁) := by abel
      rw [e, smul_add, osmul_comm W T₂]
      refine (W.N T₂).add_mem (pullJ_Q W T₂ hM₂ hP) ?_
      rw [← algebraMap_smul (LetA O n)]
      exact (W.N T₂).smul_mem _ (hM₂ _ hFNl)
    refine ⟨z₁, hz₁I, hB, fun ζ hζ u hu hu0 dd hddLB hdde => ?_⟩
    obtain ⟨z', hz'⟩ := (hTT T₂ hT₂ (c - 1)).1 _ hFI
    obtain ⟨hz'P, -⟩ := (hTT T₂ hT₂ (c - 1)).2.1 _ z' hFI hz'
    obtain ⟨p', hp', hnatE⟩ := hnat T₁ T₂ F hT₁ hT₂ (c - 1) n₁ z₁ z' hn₁I hz₁ hz'
    have hQz' : W.Q ^ Bn • z' ∈ W.N T₂ := by
      have e : z' = (z' - ((PD.p : ℕ) : O) ^ σ₁ • ((W.φD T₂) ^ 1) (W.map F n₁)) +
          ((PD.p : ℕ) : O) ^ σ₁ • ((W.φD T₂) ^ 1) (W.map F n₁) := by abel
      rw [e, smul_add, osmul_comm W T₂]
      refine (W.N T₂).add_mem (pullJ_Q W T₂ hM₂ hz'P) ?_
      rw [← algebraMap_smul (LetA O n), pow_one]
      exact (W.N T₂).smul_mem _ (hM₂ _ hFNl)
    have hk : (Formalism.MainNotions.LiftingTheory.qp W ^ Bn * 1) • z' ∈ W.N T₂ := by rw [mul_one]; exact hUQ T₂ _ hQz'
    obtain ⟨hTneg, hTpos⟩ := hTH hCA' hl 1 1 Bn σ₁ hTC T₂ hT₂ (c - 1) (W.map F n₁) z' hFN hFI hz' ζ
      (Bn + Bn) Bn 1 hk (Or.inl ⟨hζ, rfl⟩)
    have hlet : c - 1 + ((1 : ℕ) : ZMod n) = c := by push_cast; ring
    rw [hlet] at hTneg hTpos
    set C : T₂.V ⊗[Qp] BdR := (PD.p : LL) ^ σ₁ • ιV PD (LL := LL) (V := T₂.V)
      ((φVB PD (LL := LL) (V := T₂.V))^[1] (W.cmp T₂ ⟨W.map F n₁, hFN⟩)) with hCdef
    have hC : C = (PD.p : LL) ^ ((σ₁ : ℤ) + gG) • ιV PD (LL := LL) (V := T₂.V)
        (φVB PD (LL := LL) (V := T₂.V) ell) := by
      rw [hCdef, Function.iterate_one, ← hcmp, map_smul, map_smul, smul_smul, zpow_add₀ hp,
        zpow_natCast]

    set v : PowerSeries LL := W.lev c ζ (U : LetA O n) * u with hv
    have hv0 : constantCoeff v ≠ 0 := by
      rw [hv, map_mul]
      refine mul_ne_zero ?_ hu0
      exact (PowerSeries.isUnit_iff_constantCoeff.1 ((Units.isUnit U).map (W.lev c ζ))).ne_zero
    have hQq : W.Q = W.q := Q_eq_q W hs
    have hltqp : W.lev c ζ (Formalism.MainNotions.LiftingTheory.qp W) = X * v := by
      rw [hU, map_mul, hQq, hu, hv]; ring

    have hqFN : Formalism.MainNotions.LiftingTheory.qp W ^ Bn • W.map F z₁ ∈ W.N T₂ := hUQ T₂ _ hB
    obtain ⟨mdd, hmdd⟩ := hddLB
    have hE1 : W.levN T₂ c ζ ⟨_, hqFN⟩ = smulS ((X * v) ^ Bn) dd := by
      have e : (⟨Formalism.MainNotions.LiftingTheory.qp W ^ Bn • W.map F z₁, hqFN⟩ : ↥(W.N T₂)) =
          ((U : LetA O n) ^ Bn) • ⟨W.Q ^ Bn • W.map F z₁, hB⟩ :=
        Subtype.ext (by
          show Formalism.MainNotions.LiftingTheory.qp W ^ Bn • W.map F z₁ = ((U : LetA O n) ^ Bn) • (W.Q ^ Bn • W.map F z₁)
          rw [hU, mul_pow, mul_smul])
      rw [e]
      have this : W.levN T₂ c ζ (((U : LetA O n) ^ Bn) • (⟨W.Q ^ Bn • W.map F z₁, hB⟩ : ↥(W.N T₂))) =
          smulS (W.lev c ζ ((U : LetA O n) ^ Bn)) (W.levN T₂ c ζ ⟨W.Q ^ Bn • W.map F z₁, hB⟩) :=
        funext fun k => W.levN_smul T₂ c ζ ((U : LetA O n) ^ Bn) ⟨W.Q ^ Bn • W.map F z₁, hB⟩ k
      rw [this, hdde, ← smulS_mul hmdd, map_pow, ← mul_pow, hv]
      congr 2
      ring

    have hp'N : Formalism.MainNotions.LiftingTheory.qp W ^ Bn • p' ∈ W.N T₂ := hUQ T₂ _ (pullJ_Q W T₂ hM₂ hp')
    have hfp : Formalism.MainNotions.CrystallineLiftingInputs.fMX W 1 Bn • (Formalism.MainNotions.LiftingTheory.qp W ^ Bn • p') ∈ W.N T₂ :=
      (W.N T₂).smul_mem _ hp'N
    have hsplit : (⟨Formalism.MainNotions.LiftingTheory.qp W ^ Bn • W.map F z₁, hqFN⟩ : ↥(W.N T₂)) =
        ⟨_, hk⟩ + ⟨_, hfp⟩ := by
      apply Subtype.ext
      show Formalism.MainNotions.LiftingTheory.qp W ^ Bn • W.map F z₁ = (Formalism.MainNotions.LiftingTheory.qp W ^ Bn * 1) • z' +
        Formalism.MainNotions.CrystallineLiftingInputs.fMX W 1 Bn • (Formalism.MainNotions.LiftingTheory.qp W ^ Bn • p')
      have e2 : W.map F z₁ = z' + Formalism.MainNotions.CrystallineLiftingInputs.fMX W 1 Bn • p' := by rw [← hnatE]; abel
      rw [e2, smul_add, mul_one, smul_smul, smul_smul, mul_comm]

    have hLBp : LB Bn (W.levN T₂ c ζ ⟨_, pullJ_Q W T₂ hM₂ hp'⟩) :=
      pullJ_LB W T₂ ζ hM₂ (hφN T₂ hT₂ c ζ hζ) hp' _
    have hR2 : LB (2 * Bn) (W.levN T₂ c ζ ⟨_, hfp⟩) := by
      have e1 : (⟨Formalism.MainNotions.CrystallineLiftingInputs.fMX W 1 Bn • (Formalism.MainNotions.LiftingTheory.qp W ^ Bn • p'), hfp⟩ : ↥(W.N T₂)) =
          (Formalism.MainNotions.CrystallineLiftingInputs.fMX W 1 Bn * (U : LetA O n) ^ Bn) • ⟨_, pullJ_Q W T₂ hM₂ hp'⟩ :=
        Subtype.ext (by
          show Formalism.MainNotions.CrystallineLiftingInputs.fMX W 1 Bn • (Formalism.MainNotions.LiftingTheory.qp W ^ Bn • p') =
            (Formalism.MainNotions.CrystallineLiftingInputs.fMX W 1 Bn * (U : LetA O n) ^ Bn) • (W.Q ^ Bn • p')
          simp only [hU, mul_pow, mul_smul])
      rw [e1]
      have this : W.levN T₂ c ζ ((Formalism.MainNotions.CrystallineLiftingInputs.fMX W 1 Bn * (U : LetA O n) ^ Bn) •
          (⟨_, pullJ_Q W T₂ hM₂ hp'⟩ : ↥(W.N T₂))) =
          smulS (W.lev c ζ (Formalism.MainNotions.CrystallineLiftingInputs.fMX W 1 Bn * (U : LetA O n) ^ Bn))
            (W.levN T₂ c ζ ⟨_, pullJ_Q W T₂ hM₂ hp'⟩) :=
        funext fun k => W.levN_smul T₂ c ζ _ _ k
      rw [this]
      have hlf : W.lev c ζ (Formalism.MainNotions.CrystallineLiftingInputs.fMX W 1 Bn * (U : LetA O n) ^ Bn) =
          X ^ Bn * (W.lev c ζ W.π₀ * v ^ Bn * W.lev c ζ (U : LetA O n) ^ Bn) := by
        rw [Formalism.MainNotions.CrystallineLiftingInputs.fMX, map_mul, map_mul, map_pow, map_pow, hltqp, pow_one, map_pow]; ring
      rw [hlf, smulS_mul hLBp, smulS_X_pow (LB_smulS hLBp _)]
      intro k hk'
      exact LB_smulS hLBp _ (k - Bn) (by omega)

    have hR1 : LB (2 * Bn) (W.levN T₂ c ζ ⟨_, hk⟩ - smulS ((X * v) ^ Bn) (del0 C)) := by
      intro r hr
      simp only [Pi.sub_apply]
      by_cases hr0 : r < 0
      · rw [hTneg r hr0, LB_smulS (lowerBound_delta_zero C) _ r hr0, sub_self]
      · obtain ⟨r', rfl⟩ : ∃ r' : ℕ, r = r' := ⟨r.toNat, by omega⟩
        rw [hTpos r' (by omega), smulSeries_delta_zero, mul_one, map_pow, hltqp, sub_self]
    have hkey : LB (2 * Bn) (smulS ((X * v) ^ Bn) (dd - del0 C)) := by
      rw [smulS_sub (LB_mono hmdd (min_le_left mdd 0)) (LB_mono (lowerBound_delta_zero C) (min_le_right mdd 0)),
        ← hE1, hsplit, map_add]
      have := LB_add hR1 hR2
      convert this using 1
      abel
    have hdiff := LB_of_mul (LB_sub (LB_mono hmdd (min_le_left mdd 0))
      (LB_mono (lowerBound_delta_zero C) (min_le_right mdd 0))) v hv0 Bn hkey
    refine ⟨fun i hi hi0 => ?_, ?_, ?_⟩
    · have := hdiff i hi
      simp only [Pi.sub_apply, del0, hi0, if_false, sub_zero] at this
      exact this
    · have hηb := rk_eta_lt W hset c
      have hB1 : 1 ≤ Bn := by omega
      have := hdiff 0 (by omega)
      simp only [Pi.sub_apply, del0, if_true, sub_eq_zero] at this
      rw [this, hC]
    · have hζ' : IsPrimitiveRoot ζ (PD.p ^ (0 + 1)) := by rwa [zero_add, pow_one]
      have hLv := (hLev T₂ hT₂ c 0 ζ hζ').1
      refine vals_of_div hmdd u hu0 Bn hdde.symm (Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ c) fun k => ?_
      have h := hLv ⟨W.Q ^ Bn • W.map F z₁, hB⟩ k
      rw [Formalism.MainNotions.UnusedSlot80.LevR.filLev_zero] at h
      exact (Submodule.mem_inf.1 h).1

end L41c

end Formalism.MainNotions.N.Pv.LocalLengthBound
