import Formalism.SharpRestriction.LevelLetterCocycles.LemmaGsOfLemGAB
import Formalism.SharpRestriction.LevelLetterCocycles.RelayGeneralCaseOfAdmissible
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains

section LemGAla

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem lemGAla_φ_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  exact Formalism.MainNotions.LiftingTheory.wmap_φD_smul W T a x

theorem lemGAla_dl_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) {i : ZMod n} {a : LetA O n}
    (ha : a ∈ W.AΔ) {x : W.DD T} (hx : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x) : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i (a • x) := by
  refine ⟨?_, fun δ hδ => ?_⟩
  · rw [smul_smul, mul_comm, ← smul_smul, hx.1]
  · rw [Formalism.MainNotions.LiftingTheory.wmap_γD_smul, ha δ hδ, hx.2 δ hδ]

theorem lemGAla_dl_φpow (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) {i : ZMod n} {x : W.DD T}
    (hx : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x) (k : ℕ) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T (i + (k : ZMod n)) (((W.φD T) ^ k) x) := by
  have step : ∀ (j : ZMod n) (y : W.DD T), Formalism.MainNotions.CrystallineLiftingInputs.DL W T j y →
      Formalism.MainNotions.CrystallineLiftingInputs.DL W T (j + 1) (W.φD T y) := by
    intro j y hy
    refine ⟨?_, fun δ hδ => ?_⟩
    · have h := Formalism.MainNotions.LiftingTheory.wmap_φA_letE W (j + 1)
      rw [add_sub_cancel_right] at h
      rw [← h, ← Formalism.MainNotions.LiftingTheory.wmap_φD_smul, hy.1]
    · rw [← W.φγ_comm, hy.2 δ hδ]
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [Nat.cast_succ, ← add_assoc, pow_succ']
    exact step _ _ ih

theorem lemGAla_dl_trunc (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
    (hO : ∀ c : O, ((PD.p : ℕ) : O) * c = 0 → c = 0) (hπ : W.π₀ ∈ W.AΔ) {c : ZMod n}
    {j M X σ : ℕ} {w z : W.DD T} (hw : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c w)
    (hz : Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T c j M X σ w z) : Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c + (j : ZMod n)) z := by
  obtain ⟨cc, r, s, hser, hrem, rfl⟩ := hz
  have hzero : Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c + (j : ZMod n)) 0 := ⟨by simp, fun δ hδ => by simp⟩
  have hsub : ∀ a b : W.DD T, Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c + (j : ZMod n)) a →
      Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c + (j : ZMod n)) b → Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c + (j : ZMod n)) (a - b) :=
    fun a b ha hb => ⟨by rw [smul_sub, ha.1, hb.1], fun δ hδ => by rw [map_sub, ha.2 δ hδ, hb.2 δ hδ]⟩
  have hadd : ∀ a b : W.DD T, Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c + (j : ZMod n)) a →
      Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c + (j : ZMod n)) b → Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c + (j : ZMod n)) (a + b) :=
    fun a b ha hb => ⟨by rw [smul_add, ha.1, hb.1], fun δ hδ => by rw [map_add, ha.2 δ hδ, hb.2 δ hδ]⟩
  have hsmem : ∀ y, s y ∈ W.AΔ := by
    intro y
    obtain ⟨⟨⟨a, ha⟩, -⟩, hps⟩ := hrem y
    have hr : r y ∈ W.AΔ := by
      rw [ha]
      exact Subalgebra.sum_mem _ fun k _ =>
        Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.pow_mem _ hπ _)
    refine Formalism.MainNotions.UnusedSlot80.SatW.mem_AΔ_of_p_pow W hO (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) ?_
    rw [hps]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.natCast_mem _ _) _) hr
  have hw' : Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c + (j : ZMod n)) (((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) w) := by
    rw [← algebraMap_smul (LetA O n)]
    exact lemGAla_dl_smul W T (Subalgebra.algebraMap_mem _ _) (lemGAla_dl_φpow W T hw j)
  refine hsub _ _ hw' ?_
  exact Finset.sum_induction _ (Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c + (j : ZMod n))) hadd hzero
    (fun y _ => lemGAla_dl_smul W T (hsmem y) (lemGAla_dl_φpow W T (hser.2.1 y).1 j))

theorem pullback_level_two_to_one (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) (k : ℕ)
    (hπ : W.π₀ ∈ W.AΔ)
    (hgen : ∀ x, x ∈ W.N T → Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x →
      Formalism.MainNotions.LiftingTheory.qp W ^ k • W.φD T x ∈ W.N T) :
    ∀ p ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T c 2,
      Formalism.MainNotions.LiftingTheory.pk W 1 ^ k • p ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (c + 1) 1 := by
  intro p hp
  have hqΔ : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ := W.AΔ.add_mem hπ (Subalgebra.natCast_mem _ _)
  unfold Formalism.MainNotions.CrystallineLiftingInputs.pullJ at hp ⊢
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, ⟨hyN, hyD⟩, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨Formalism.MainNotions.LiftingTheory.qp W ^ k • W.φD T y, ⟨hgen y hyN hyD, ?_⟩, ?_⟩
    · exact lemGAla_dl_smul W T (pow_mem hqΔ k) (by simpa using lemGAla_dl_φpow W T hyD 1)
    · simp only [pow_one, Formalism.MainNotions.LiftingTheory.pk]
      rw [Formalism.MainNotions.LiftingTheory.wmap_φD_smul, map_pow, pow_two]
      rfl
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [smul_smul, mul_comm, ← smul_smul]
    exact Submodule.smul_mem _ a hx

theorem lemGAla_pull1N (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) (k : ℕ)
    (hgen : ∀ x, x ∈ W.N T → Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x →
      Formalism.MainNotions.LiftingTheory.qp W ^ k • W.φD T x ∈ W.N T) :
    ∀ p ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T c 1, Formalism.MainNotions.LiftingTheory.qp W ^ k • p ∈ W.N T := by
  intro p hp
  unfold Formalism.MainNotions.CrystallineLiftingInputs.pullJ at hp
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, ⟨hyN, hyD⟩, rfl⟩ := hx
    simpa using hgen y hyN hyD
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [smul_smul, mul_comm, ← smul_smul]
    exact (W.N T).smul_mem a hx

theorem q_pow_smul_frobenius_mem' (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W)
    (hs : W.s = 1) {M h : ZMod n → ℕ} (h5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h) (c : ZMod n) :
    ∀ x, x ∈ W.N T → Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x →
      Formalism.MainNotions.LiftingTheory.qp W ^ M (c + 1) • W.φD T x ∈ W.N T := by
  intro x hxN hxD
  have hxl : x ∈ W.Nl T c := by
    have h := Formalism.MainNotions.LiftingTheory.liftb_letE_mem W T c hxN
    rwa [hxD.1] at h
  have h := h5.1 (c + 1) x (by rwa [add_sub_cancel_right])
  exact (Formalism.MainNotions.LiftingTheory.lifta_Qq W hR hs T _ _).1 h

theorem lemGAla_parity {n : ℕ} [NeZero n] (hn : Even n) (d : ℕ) (i : ZMod n) (hi : (i.val + d) % 2 = 1) :
    ((i - 1).val + d) % 2 = 0 := by
  have h2 : 2 ∣ n := even_iff_two_dvd.1 hn
  have key : ∀ x : ZMod n, (((x.val : ℕ)) : ZMod 2) = ZMod.castHom h2 (ZMod 2) x := by
    intro x
    simp [ZMod.castHom_apply, ZMod.natCast_val]
  have h1 : (((i.val + d : ℕ)) : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod, hi]
    rfl
  rw [← Nat.dvd_iff_mod_eq_zero, ← CharP.cast_eq_zero_iff (ZMod 2) 2]
  push_cast at h1 ⊢
  rw [key (i - 1), map_sub, map_one, ← key i]
  linear_combination h1

theorem lemGA_la_of [NeZero n] (W : LocWach PD LL O v n) (hT2 : Formalism.MainNotions.CrystallineLiftingInputs.TTool2 W)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W)
    (hJ : ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
      SetCS W d T₁ T₂ F b S η m → Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T₂ (MiW d b S η) (hiW d b S η)) :
    LemGA_la W := by
  intro d T₁ T₂ F b S η m hset i hi y hyN hyD
  have hsetc := hset
  obtain ⟨hA, hp11, hn, ⟨hdom, -, -⟩, ⟨ζ, hζ⟩, hsur, -, -, hbig, -⟩ := hset
  haveI := hdom
  have hs : W.s = 1 := hA.2.1
  have hc2 : IsCrys PD T₂.ρ := hsur.2.1
  have hO : ∀ c : O, ((PD.p : ℕ) : O) * c = 0 → c = 0 := by
    intro c hc
    haveI : NeZero PD.p := ⟨by omega⟩
    have hpL : ((PD.p : ℕ) : LL) ≠ 0 := hζ.neZero'.out
    have hpO : ((PD.p : ℕ) : O) ≠ 0 := fun h =>
      hpL (by rw [← map_natCast (algebraMap O LL), h, map_zero])
    exact (mul_eq_zero.1 hc).resolve_left hpO
  have hfin : finrank K₀ K = 1 := by
    have e := LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hA.1
    rw [← e.finrank_eq, finrank_self]
  obtain ⟨-, -, h9f⟩ := h9 T₂ hc2 hs hA.2.2
  obtain ⟨-, hmod⟩ := h9f hfin
  obtain ⟨-, hγN⟩ := hmod
  have hyΔ : y ∈ W.NΔ T₂ := ⟨hyN, hyD.2⟩
  obtain ⟨y', hy'Δ, hy'⟩ := hγN y hyΔ
  have hInI : Formalism.MainNotions.CrystallineLiftingInputs.InI W T₂ (i - 2) y := by
    refine ⟨hyD, ⟨0, ?_⟩, ⟨y', hy'Δ.1, hy'Δ.2, by rw [pow_one]; exact hy'⟩⟩
    first
      | exact hyN
      | (simp only [LocWach.InvN]; simpa using hyN)
      | (unfold LocWach.InvN; simpa [Formalism.MainNotions.DeltaInvariantLattices.invN, Formalism.MainNotions.DeltaInvariantLattices.smulA] using hyN)
  have hqΔ : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ := W.AΔ.add_mem hR.πΔ (Subalgebra.natCast_mem _ _)
  set H := hpar n b S + η with hH
  obtain ⟨hex, hcl, -⟩ := (hT2 hA hp11 2 1 (2 * H) (lemG_sig PD.p H) (Or.inr ⟨rfl, rfl, rfl⟩)).1
    T₂ hc2 (i - 2)
  obtain ⟨la, hla⟩ := hex y hInI
  obtain ⟨hdiff, p0, hp0, hγla⟩ := hcl y la hInI hla
  have h5T := h5 T₂ _ _ hc2 (hJ d T₁ T₂ F b S η m hsetc)
  have hpar1 : ((i - 1).val + d) % 2 = 0 := lemGAla_parity hn d i hi
  have hM1 : MiW d b S η (i - 1) = b (i - 1) + S := by simp [MiW, hpar1]
  have hMi : MiW d b S η i = η := by simp [MiW, hi]
  have hgen1 : ∀ x, x ∈ W.N T₂ → Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 2) x →
      Formalism.MainNotions.LiftingTheory.qp W ^ (b (i - 1) + S) • W.φD T₂ x ∈ W.N T₂ := by
    intro x hx hxD
    have h := q_pow_smul_frobenius_mem' W T₂ hR hs h5T (i - 2) x hx hxD
    rwa [show i - 2 + 1 = i - 1 by ring, hM1] at h
  have hgen2 : ∀ x, x ∈ W.N T₂ → Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 1) x →
      Formalism.MainNotions.LiftingTheory.qp W ^ η • W.φD T₂ x ∈ W.N T₂ := by
    intro x hx hxD
    have h := q_pow_smul_frobenius_mem' W T₂ hR hs h5T (i - 1) x hx hxD
    rwa [sub_add_cancel, hMi] at h
  have hla_mem : la ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T₂ (i - 2) 2 := by
    have hgenp : ((PD.p : ℕ) : O) ^ lemG_sig PD.p H • ((W.φD T₂) ^ 2) y ∈
        Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T₂ (i - 2) 2 := by
      rw [← algebraMap_smul (LetA O n)]
      refine Submodule.smul_mem _ _ ?_
      unfold Formalism.MainNotions.CrystallineLiftingInputs.pullJ
      exact Submodule.subset_span ⟨y, ⟨hyN, hyD⟩, rfl⟩
    have h := Submodule.add_mem _ hdiff hgenp
    rwa [sub_add_cancel] at h
  have hpull : Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • la ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T₂ (i - 1) 1 := by
    have h := pullback_level_two_to_one W T₂ (i - 2) (b (i - 1) + S) hR.πΔ hgen1 la hla_mem
    rwa [show i - 2 + 1 = i - 1 by ring] at h
  have hDLi : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ i la := by
    have h := lemGAla_dl_trunc W T₂ hO hR.πΔ hyD hla
    simpa using h
  have hp0' : Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • p0 ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T₂ (i - 1) 1 := by
    have h := pullback_level_two_to_one W T₂ (i - 2) (b (i - 1) + S) hR.πΔ hgen1 p0 hp0
    rwa [show i - 2 + 1 = i - 1 by ring] at h
  have hN1 := lemGAla_pull1N W T₂ (i - 1) η hgen2 _ hp0'

  have hle : ⌈aR PD.p H⌉₊ + b i + η ≤ 2 * H := by
    have hbi : b i ≤ hpar n b S :=
      le_trans (Finset.le_sup (f := b) (Finset.mem_univ i)) (Nat.le_add_right _ _)
    have hb := hbig i
    rcases le_or_gt 0 (aR PD.p H) with h0 | h0
    · have hc := Nat.ceil_lt_add_one h0
      have hbi' : (b i : ℝ) ≤ (hpar n b S : ℝ) := by exact_mod_cast hbi
      have hreal : ((⌈aR PD.p H⌉₊ : ℕ) : ℝ) + (b i : ℝ) + (η : ℝ) ≤ 2 * ((hpar n b S : ℝ) + η) := by
        linarith
      rw [hH]
      exact_mod_cast hreal
    · have hc : ⌈aR PD.p H⌉₊ = 0 := Nat.ceil_eq_zero.2 h0.le
      rw [hc, hH]
      omega
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hle
  set a := W.π₀ * Formalism.MainNotions.LiftingTheory.qp W ^ (⌈aR PD.p H⌉₊ + b i) with ha_def
  have haΔ : a ∈ W.AΔ := W.AΔ.mul_mem hR.πΔ (W.AΔ.pow_mem hqΔ _)
  have hpkΔ : Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) ∈ W.AΔ :=
    W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.PhiPowers.φA_pow_mem_AΔ (W := W) hqΔ 1) _
  have hcancel : ∀ x x' : W.DD T₂, a • x = a • x' → x = x' := by
    intro x x' h
    rw [ha_def, mul_comm, ← smul_smul, ← smul_smul] at h
    have h1 := (Formalism.MainNotions.LiftingTheory.lifta_qpow_bij W hR T₂ _).1 h
    obtain ⟨u, hu⟩ := hR.πU
    exact Formalism.MainNotions.LiftingTheory.lifta_π₀_cancel W T₂ (↑u⁻¹ : W.EE) (by rw [← hu]; exact u.mul_inv) x x' h1
  set w := Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • (W.γ T₂ la - la) with hw_def
  have hγDL : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ i (W.γ T₂ la) := by
    refine ⟨?_, fun δ hδ => ?_⟩
    · conv_lhs => rw [← Formalism.MainNotions.WachCoordinates.Br.γA_letE W W.gam i]
      rw [← Formalism.MainNotions.LiftingTheory.liftb_γ_smul, hDLi.1]
    · show W.γD T₂ δ (W.γD T₂ W.gam la) = W.γD T₂ W.gam la
      rw [← W.γD_mul, mul_comm, W.γD_mul, hDLi.2 δ hδ]
  have hwDL : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ i w := by
    refine lemGAla_dl_smul W T₂ hpkΔ ⟨?_, fun δ hδ => ?_⟩
    · rw [smul_sub, hγDL.1, hDLi.1]
    · rw [map_sub, hγDL.2 δ hδ, hDLi.2 δ hδ]
  set z := Formalism.MainNotions.LiftingTheory.qp W ^ t • (Formalism.MainNotions.LiftingTheory.qp W ^ η • (Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • p0))
    with hz_def
  have hzN : z ∈ W.N T₂ := Submodule.smul_mem _ _ hN1
  have hz_eq : a • z = w := by
    rw [hw_def, hγla, hz_def, ha_def, Formalism.MainNotions.CrystallineLiftingInputs.fMX, ht]
    simp only [smul_smul]
    congr 1
    ring
  refine ⟨la, hla, hDLi, hpull, z, hzN, ⟨hcancel _ _ ?_, fun δ hδ => hcancel _ _ ?_⟩, ?_⟩
  · rw [smul_smul, mul_comm, ← smul_smul, hz_eq, hwDL.1]
  · calc a • W.γD T₂ δ z = W.γA δ a • W.γD T₂ δ z := by rw [haΔ δ hδ]
      _ = W.γD T₂ δ (a • z) := (Formalism.MainNotions.LiftingTheory.wmap_γD_smul W T₂ δ a z).symm
      _ = a • z := by rw [hz_eq, hwDL.2 δ hδ]
  · rw [← hw_def, ← hz_eq]

end LemGAla

end Formalism.MainNotions.RamifiedCoefficientChains.S9
