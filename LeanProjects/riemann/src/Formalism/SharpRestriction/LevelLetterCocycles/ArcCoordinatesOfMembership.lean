import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfFrame
import Formalism.SharpRestriction.LevelLetterCocycles.RelayGeneralCaseOfAdmissible

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.ArcF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.UnusedSlot80.PhiPowers TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem cmp_smul_letter (T : LocLat G Qp LL O) (i : ZMod n) (a : LetA O n) (w : W.DD T)
    (hw : w ∈ W.N T) (hwi : (letE i : LetA O n) • w = w) :
    W.cmp T ⟨a • w, (W.N T).smul_mem a hw⟩ =
      algebraMap O LL (PowerSeries.constantCoeff (a i)) • W.cmp T ⟨w, hw⟩ := by
  set c : O := PowerSeries.constantCoeff (a i) with hc
  set a' : LetA O n := fun j => PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (a j) with ha'
  have hA : a * letE i = algebraMap O (LetA O n) c * letE i + letπ * a' * letE i := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [Pi.mul_apply, Pi.add_apply, letE, Pi.single_eq_same, mul_one, letπ, ha']
      have : (algebraMap O (LetA O n) c) j = PowerSeries.C c := rfl
      rw [this, hc]
      exact (PowerSeries.eq_X_mul_shift_add_const (a j)).trans (add_comm _ _)
    · simp [letE, Pi.single_eq_of_ne hj]
  have hkey : a • w = c • w + (letπ : LetA O n) • (a' • w) := by
    calc a • w = a • ((letE i : LetA O n) • w) := by rw [hwi]
      _ = (a * letE i) • w := by rw [mul_smul]
      _ = (algebraMap O (LetA O n) c) • ((letE i : LetA O n) • w) +
            (letπ : LetA O n) • (a' • ((letE i : LetA O n) • w)) := by
          rw [hA, add_smul, mul_smul, mul_smul, mul_smul]
      _ = c • w + (letπ : LetA O n) • (a' • w) := by rw [hwi, algebraMap_smul]
  have e : (⟨a • w, (W.N T).smul_mem a hw⟩ : ↥(W.N T)) =
      c • (⟨w, hw⟩ : ↥(W.N T)) + (letπ : LetA O n) • (⟨a' • w, (W.N T).smul_mem a' hw⟩ : ↥(W.N T)) :=
    Subtype.ext (by simpa using hkey)
  rw [e, map_add, W.cmp_smul, W.cmp_π, add_zero]

theorem mem_Dcris_iff (T : LocLat G Qp LL O) (x : T.V ⊗[Qp] B) :
    x ∈ Dcris PD T.ρ ↔ ∀ g, actVB PD T.ρ g x = x := by
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]

theorem mem_DcrisL_iff (T : LocLat G Qp LL O) (τ : K₀ →ₐ[Qp] LL) (x : T.V ⊗[Qp] B) :
    x ∈ DcrisL PD T.ρ τ ↔ x ∈ Dcris PD T.ρ ∧
      ∀ c, mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) c x = τ c • x := by
  simp only [DcrisL, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem mulVB_of_mem (T : LocLat G Qp LL O) (τ : K₀ →ₐ[Qp] LL) {x : T.V ⊗[Qp] B}
    (hx : x ∈ DcrisL PD T.ρ τ) (c : K₀) :
    mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) c x = τ c • x :=
  ((mem_DcrisL_iff T τ x).1 hx).2 c

theorem dcrisL_sum_zero (T : LocLat G Qp LL O) :
    ∀ (s : Finset (ZMod n)) (d : ZMod n → T.V ⊗[Qp] B),
      (∀ i ∈ s, d i ∈ DcrisL PD T.ρ (W.emb i)) → ∑ i ∈ s, d i = 0 → ∀ i ∈ s, d i = 0 := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro d _ _ i hi; simp at hi
  | insert a s ha ih =>
    intro d hd hsum
    have hrest : ∀ i ∈ s, d i = 0 := by
      intro i hi
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      obtain ⟨c, hc⟩ : ∃ c : K₀, W.emb i c ≠ W.emb a c := by
        by_contra h
        push Not at h
        exact hia (W.emb_bij.1 (AlgHom.ext h))
      set f : T.V ⊗[Qp] B →ₗ[LL] T.V ⊗[Qp] B :=
        mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) c - W.emb a c • LinearMap.id with hf
      have hfj : ∀ j ∈ insert a s, f (d j) = (W.emb j c - W.emb a c) • d j := by
        intro j hj
        rw [hf, LinearMap.sub_apply, mulVB_of_mem T _ (hd j hj), LinearMap.smul_apply,
          LinearMap.id_apply, sub_smul]
      have h1 := congrArg f hsum
      rw [map_sum, map_zero, Finset.sum_congr rfl hfj, Finset.sum_insert ha, sub_self, zero_smul,
        zero_add] at h1
      have := ih (fun j => (W.emb j c - W.emb a c) • d j)
        (fun j hj => (DcrisL PD T.ρ (W.emb j)).smul_mem _ (hd j (Finset.mem_insert_of_mem hj))) h1 i hi
      rcases smul_eq_zero.1 this with h | h
      · exact absurd (sub_eq_zero.1 h) hc
      · exact h
    rw [Finset.sum_insert ha, Finset.sum_eq_zero hrest, add_zero] at hsum
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hsum
    · exact hrest i hi

theorem φVB_act (T : LocLat G Qp LL O) (g : G) (x : T.V ⊗[Qp] B) :
    actVB PD T.ρ g (φVB PD (LL := LL) (V := T.V) x) = φVB PD (LL := LL) (V := T.V) (actVB PD T.ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, φVB, PD.φ_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem φVB_mul (T : LocLat G Qp LL O) (c : K₀) (x : T.V ⊗[Qp] B) :
    mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) (PD.σ c) (φVB PD (LL := LL) (V := T.V) x) =
      φVB PD (LL := LL) (V := T.V) (mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) c x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [mulVB, φVB, PD.φ_K₀]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem φVB_letter (T : LocLat G Qp LL O) (i : ZMod n) {x : T.V ⊗[Qp] B}
    (hx : x ∈ DcrisL PD T.ρ (W.emb i)) :
    φVB PD (LL := LL) (V := T.V) x ∈ DcrisL PD T.ρ (W.emb (i + 1)) := by
  rw [mem_DcrisL_iff]
  obtain ⟨h1, h2⟩ := (mem_DcrisL_iff T _ x).1 hx
  refine ⟨(mem_Dcris_iff T _).2 fun g => ?_, fun c => ?_⟩
  · rw [φVB_act, (mem_Dcris_iff T x).1 h1 g]
  · obtain ⟨c', rfl⟩ := PD.σ_bij.2 c
    rw [φVB_mul, h2 c', map_smul]
    congr 1
    have := congrArg (fun f : K₀ →ₐ[Qp] LL => f c') (W.emb_σ i)
    simpa using this.symm

theorem φVB_pow_letter (T : LocLat G Qp LL O) (i : ZMod n) {x : T.V ⊗[Qp] B}
    (hx : x ∈ DcrisL PD T.ρ (W.emb i)) (e : ℕ) :
    ((φVB PD (LL := LL) (V := T.V)) ^ e) x ∈ DcrisL PD T.ρ (W.emb (i + (e : ZMod n))) := by
  induction e with
  | zero => simpa using hx
  | succ e ih =>
    rw [pow_succ', Module.End.mul_apply]
    have := φVB_letter W T _ ih
    rwa [show i + (e : ZMod n) + 1 = i + ((e + 1 : ℕ) : ZMod n) by push_cast; ring] at this

theorem φVB_inj (T : LocLat G Qp LL O) : Function.Injective (φVB PD (LL := LL) (V := T.V)) := by
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := T.V) PD.φ.toLinearMap PD.φ_inj
  have e : ∀ z, φVB PD (LL := LL) (V := T.V) z = (PD.φ.toLinearMap.lTensor T.V) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [φVB]
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x y hxy
  rw [e, e] at hxy
  exact h hxy

include W in
theorem p_ne_zero : (PD.p : LL) ≠ 0 := by
  intro h
  have := W.v_l
  rw [h, AddValuation.map_zero] at this
  exact absurd this (by simp)

include W in

theorem exists_pow_mul (hV : ValRing (LL := LL) O v) (x : LL) :
    ∃ (m : ℕ) (o : O), algebraMap O LL o = (PD.p : LL) ^ m * x := by
  by_cases hx : x = 0
  · exact ⟨0, 0, by simp [hx]⟩
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 ((v.ne_top_iff).2 hx)
  obtain ⟨o, ho⟩ := hV.2.1 ((PD.p : LL) ^ ⌈-q⌉₊ * x) (by
    rw [AddValuation.map_mul, AddValuation.map_pow, W.v_l, ← hq]
    have h1 : (-q : ℚ) ≤ (⌈-q⌉₊ : ℚ) := Nat.le_ceil _
    have e : ((⌈-q⌉₊ : ℕ) • (1 : WithTop ℚ) + (q : WithTop ℚ)) =
        (((⌈-q⌉₊ : ℚ) + q : ℚ) : WithTop ℚ) := by
      rw [nsmul_one]; norm_cast
    rw [e]
    exact WithTop.coe_le_coe.2 (by linarith))
  exact ⟨_, o, ho⟩

include W in

theorem linIndep_of_O (hV : ValRing (LL := LL) O v) {M : Type} [AddCommGroup M] [Module LL M] {d : ℕ}
    (u : Fin d → M) (hO : ∀ c : Fin d → O, ∑ k, algebraMap O LL (c k) • u k = 0 → ∀ k, c k = 0) :
    LinearIndependent LL u := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  choose m o ho using fun i => exists_pow_mul W hV (g i)
  set N : ℕ := ∑ i, m i with hN
  have hle : ∀ i, m i ≤ N := fun i => Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ i)
  set c : Fin d → O := fun i => ((PD.p : ℕ) : O) ^ (N - m i) * o i with hc
  have hc' : ∀ i, algebraMap O LL (c i) = (PD.p : LL) ^ N * g i := by
    intro i
    rw [hc, map_mul, map_pow, map_natCast, ho i, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (hle i)]
  have h0 := hO c (by
    simp_rw [hc', mul_smul]
    rw [← Finset.smul_sum, hg, smul_zero])
  have := hc' k
  rw [h0 k, map_zero] at this
  rcases mul_eq_zero.1 this.symm with h | h
  · exact absurd (pow_eq_zero_iff'.1 h).1 (p_ne_zero W)
  · exact h

theorem cmp_sum_letter (T : LocLat G Qp LL O) (i : ZMod n) {d : ℕ} (b : Fin d → W.DD T)
    (hbN : ∀ m, b m ∈ W.N T) (hbl : ∀ m, (letE i : LetA O n) • b m = b m) (β : Fin d → LetA O n)
    (h : ∑ m, β m • b m ∈ W.N T) :
    W.cmp T ⟨∑ m, β m • b m, h⟩ =
      ∑ m, algebraMap O LL (PowerSeries.constantCoeff (β m i)) • W.cmp T ⟨b m, hbN m⟩ := by
  have e : (⟨∑ m, β m • b m, h⟩ : ↥(W.N T)) =
      ∑ m, (⟨β m • b m, (W.N T).smul_mem _ (hbN m)⟩ : ↥(W.N T)) := Subtype.ext (by simp)
  rw [e, map_sum]
  exact Finset.sum_congr rfl fun m _ => cmp_smul_letter W T i (β m) (b m) (hbN m) (hbl m)

theorem cmpD_of_mem (T : LocLat G Qp LL O) {x : W.DD T} (hx : x ∈ W.N T) :
    Formalism.MainNotions.ArcLiftingSetup.cmpD W T x = W.cmp T ⟨x, hx⟩ := by
  unfold Formalism.MainNotions.ArcLiftingSetup.cmpD; rw [dif_pos hx]

theorem letter_of_Nl (T : LocLat G Qp LL O) (i : ZMod n) {x : W.DD T} (hx : x ∈ W.Nl T i) :
    (letE i : LetA O n) • x = x := by
  obtain ⟨z, -, rfl⟩ := hx
  simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, letE_mul_self]

theorem cmp_mem_letter (T : LocLat G Qp LL O) (i : ZMod n) {x : W.DD T} (hx : x ∈ W.N T)
    (hxi : (letE i : LetA O n) • x = x) : W.cmp T ⟨x, hx⟩ ∈ DcrisL PD T.ρ (W.emb i) := by
  have e : (⟨x, hx⟩ : ↥(W.N T)) = (letE i : LetA O n) • (⟨x, hx⟩ : ↥(W.N T)) :=
    Subtype.ext (by simp [hxi])
  rw [e]; exact W.cmp_letter T i _

theorem dcrisL_le_span [NeZero n] (T : LocLat G Qp LL O) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (i : ZMod n) :
    DcrisL PD T.ρ (W.emb i) ≤
      Submodule.span LL (Set.range fun x : ↥(W.N T) => W.cmp T ((letE i : LetA O n) • x)) := by
  intro d hd
  set S : ZMod n → Submodule LL (T.V ⊗[Qp] B) := fun j =>
    Submodule.span LL (Set.range fun x : ↥(W.N T) => W.cmp T ((letE j : LetA O n) • x)) with hS
  have hSle : ∀ j, S j ≤ DcrisL PD T.ρ (W.emb j) := fun j =>
    Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact W.cmp_letter T j x)
  have hcmp : ∀ x : ↥(W.N T), W.cmp T x = ∑ j : ZMod n, W.cmp T ((letE j : LetA O n) • x) := by
    intro x
    rw [← map_sum, ← Finset.sum_smul, sum_letE, one_smul]
  have hrange : Set.range (W.cmp T) ⊆ ((⨆ j, S j : Submodule LL (T.V ⊗[Qp] B)) : Set _) := by
    rintro _ ⟨x, rfl⟩
    rw [hcmp]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.mem_iSup_of_mem j (Submodule.subset_span ⟨x, rfl⟩)
  have hdS : d ∈ (⨆ j, S j : Submodule LL (T.V ⊗[Qp] B)) := by
    have h1 : d ∈ Dcris PD T.ρ := (Submodule.mem_inf.1 hd).1
    rw [← h3.2.1] at h1
    exact Submodule.span_le.2 hrange h1
  have key : ∀ y ∈ (⨆ j, S j : Submodule LL (T.V ⊗[Qp] B)),
      ∃ f : ZMod n → T.V ⊗[Qp] B, (∀ j, f j ∈ S j) ∧ ∑ j, f j = y := by
    intro y hy
    refine Submodule.iSup_induction S (motive := fun y =>
      ∃ f : ZMod n → T.V ⊗[Qp] B, (∀ j, f j ∈ S j) ∧ ∑ j, f j = y) hy ?_ ?_ ?_
    · intro j y hy
      refine ⟨Pi.single j y, fun j' => ?_, by simp⟩
      by_cases h : j' = j
      · subst h; simpa using hy
      · simp [Pi.single_eq_of_ne h]
    · exact ⟨0, fun j => (S j).zero_mem, by simp⟩
    · rintro y z ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
      exact ⟨f + g, fun j => (S j).add_mem (hf j) (hg j), by simp [Finset.sum_add_distrib]⟩
  obtain ⟨f, hf, hfd⟩ := key d hdS
  have h0 := dcrisL_sum_zero W T Finset.univ (fun j => f j - if j = i then d else 0)
    (fun j _ => by
      refine (DcrisL PD T.ρ (W.emb j)).sub_mem (hSle j (hf j)) ?_
      split_ifs with h
      · subst h; exact hd
      · exact (DcrisL PD T.ρ (W.emb j)).zero_mem)
    (by rw [Finset.sum_sub_distrib, hfd, Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ _),
      sub_self]) i (Finset.mem_univ _)
  rw [if_pos rfl, sub_eq_zero] at h0
  rw [← h0]; exact hf i

def ev (i : ZMod n) : LetA O n →+* O :=
  PowerSeries.constantCoeff.comp (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) i)

theorem ev_apply (i : ZMod n) (a : LetA O n) : ev i a = PowerSeries.constantCoeff (a i) := rfl

theorem ev_alg (i : ZMod n) (c : O) : ev i (algebraMap O (LetA O n) c) = c := by
  show PowerSeries.constantCoeff ((algebraMap O (LetA O n) c) i) = c
  have : (algebraMap O (LetA O n) c) i = PowerSeries.C c := rfl
  rw [this, PowerSeries.constantCoeff_C]

theorem ev_π (i : ZMod n) : ev i (letπ : LetA O n) = 0 := by
  show PowerSeries.constantCoeff PowerSeries.X = 0
  simp

theorem ev_letE (i : ZMod n) : ev i (letE i : LetA O n) = 1 := by
  show PowerSeries.constantCoeff ((Pi.single i 1 : LetA O n) i) = 1
  simp

theorem cmp_indepO (T : LocLat G Qp LL O) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    (c' : ZMod n) {d : ℕ} (b : Fin d → W.DD T) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b)
    (cc : Fin d → O) (h0 : ∑ k, algebraMap O LL (cc k) • Formalism.MainNotions.ArcLiftingSetup.cmpD W T (b k) = 0) :
    ∀ k, cc k = 0 := by
  have hbN : ∀ k, b k ∈ W.N T := fun k => (hb.1 k).1.1
  have hbl : ∀ k, (letE c' : LetA O n) • b k = b k := fun k => letter_of_Nl W T c' (hb.1 k).2
  set X : W.DD T := ∑ k, cc k • b k with hXdef
  have hXN : X ∈ W.N T := Submodule.sum_mem _ fun k _ => by
    rw [← algebraMap_smul (LetA O n) (cc k) (b k)]; exact (W.N T).smul_mem _ (hbN k)
  have hcX : W.cmp T ⟨X, hXN⟩ = 0 := by
    have e : (⟨X, hXN⟩ : ↥(W.N T)) = ∑ k, cc k • (⟨b k, hbN k⟩ : ↥(W.N T)) :=
      Subtype.ext (by simp [hXdef])
    rw [e, map_sum, ← h0]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [W.cmp_smul, cmpD_of_mem W T (hbN k)]
  obtain ⟨y, hyN, hyX⟩ := h3.1 ⟨X, hXN⟩ hcX
  have hyX' : (letπ : LetA O n) • y = X := hyX
  obtain ⟨⟨r, b', hb'Δ, hU, hΔc⟩, -⟩ := hmod
  choose α' hα' using fun k => hΔc (b k) (hb.1 k).1
  obtain ⟨ay, hay⟩ := (hU y hyN).exists
  have hX1 : X = ∑ j, (∑ k, algebraMap O (LetA O n) (cc k) * α' k j) • b' j := by
    simp only [Finset.sum_smul, mul_smul, algebraMap_smul]
    rw [Finset.sum_comm, hXdef]
    refine Finset.sum_congr rfl fun k _ => ?_
    conv_lhs => rw [(hα' k).2]
    rw [Finset.smul_sum]
  have hX2 : X = ∑ j, ((letπ : LetA O n) * ay j) • b' j := by
    rw [← hyX', hay, Finset.smul_sum]
    simp only [mul_smul]
  have hcoef := (hU X hXN).unique hX1 hX2
  have hev0 : ∀ j, ∑ k, cc k * ev c' (α' k j) = 0 := by
    intro j
    have := congrArg (ev c') (congrFun hcoef j)
    simpa [map_sum, map_mul, ev_alg, ev_π] using this
  choose α hα using fun j => (hb.2 ((letE c' : LetA O n) • b' j)
    ⟨smul_mem_NΔ W T (SatPW.letE_mem_AΔ W c') (hb'Δ j),
      ⟨b' j, (hb'Δ j).1, by rw [LinearMap.smul_apply, LinearMap.id_apply]⟩⟩).exists
  have hbk : ∀ k, b k = ∑ m, (∑ j, α' k j * α j m) • b m := by
    intro k
    calc b k = (letE c' : LetA O n) • b k := (hbl k).symm
      _ = ∑ j, α' k j • ((letE c' : LetA O n) • b' j) := by
          conv_lhs => rw [(hα' k).2]
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
      _ = ∑ j, α' k j • ∑ m, α j m • b m := Finset.sum_congr rfl fun j _ => by rw [(hα j).2]
      _ = ∑ m, (∑ j, α' k j * α j m) • b m := by
          simp only [Finset.smul_sum, Finset.sum_smul, mul_smul]
          exact Finset.sum_comm
  have hδ : ∀ k m, (∑ j, α' k j * α j m) = if m = k then (letE c' : LetA O n) else 0 := by
    intro k
    have hu := hb.2 (b k) (hb.1 k)
    refine congrFun (hu.unique ⟨fun m => ⟨?_, ?_⟩, hbk k⟩ ⟨fun m => ⟨?_, ?_⟩, ?_⟩)
    · exact W.AΔ.sum_mem fun j _ => W.AΔ.mul_mem ((hα' k).1 j) ((hα j).1 m).1
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [mul_left_comm, ((hα j).1 m).2]
    · split_ifs
      · exact SatPW.letE_mem_AΔ W c'
      · exact W.AΔ.zero_mem
    · split_ifs
      · exact letE_mul_self c'
      · exact mul_zero _
    · simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact (hbl k).symm
  have hevδ : ∀ k m, ∑ j, ev c' (α' k j) * ev c' (α j m) = if m = k then 1 else 0 := by
    intro k m
    have := congrArg (ev c') (hδ k m)
    rw [map_sum] at this
    simp only [map_mul] at this
    rw [this]
    split_ifs
    · exact ev_letE c'
    · exact map_zero _
  intro m
  calc cc m = ∑ k, cc k * (if m = k then 1 else 0) := by simp
    _ = ∑ k, cc k * ∑ j, ev c' (α' k j) * ev c' (α j m) := by simp_rw [hevδ]
    _ = ∑ j, (∑ k, cc k * ev c' (α' k j)) * ev c' (α j m) := by
        simp_rw [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
    _ = 0 := by simp [hev0]

theorem dcrisL_le_spanB [NeZero n] (T : LocLat G Qp LL O) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T)
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (c' : ZMod n) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) :
    DcrisL PD T.ρ (W.emb c') ≤
      Submodule.span LL (Set.range fun k => Formalism.MainNotions.ArcLiftingSetup.cmpD W T (b k)) := by
  have hbN : ∀ k, b k ∈ W.N T := fun k => (hb.1 k).1.1
  have hbl : ∀ k, (letE c' : LetA O n) • b k = b k := fun k => letter_of_Nl W T c' (hb.1 k).2
  refine (dcrisL_le_span W T h3 c').trans (Submodule.span_le.2 ?_)
  rintro _ ⟨x, rfl⟩
  obtain ⟨⟨r, b', hb'Δ, hU, -⟩, -⟩ := hmod
  obtain ⟨a, ha⟩ := (hU x x.2).exists
  choose α hα using fun j => (hb.2 ((letE c' : LetA O n) • b' j)
    ⟨smul_mem_NΔ W T (SatPW.letE_mem_AΔ W c') (hb'Δ j),
      ⟨b' j, (hb'Δ j).1, by rw [LinearMap.smul_apply, LinearMap.id_apply]⟩⟩).exists
  have hx : ((letE c' : LetA O n) • x : W.DD T) = ∑ m, (∑ j, a j * α j m) • b m := by
    rw [ha, Finset.smul_sum]
    calc ∑ j, (letE c' : LetA O n) • a j • b' j = ∑ j, a j • ∑ m, α j m • b m :=
          Finset.sum_congr rfl fun j _ => by rw [smul_comm, (hα j).2]
      _ = _ := by
          simp only [Finset.smul_sum, Finset.sum_smul, mul_smul]
          exact Finset.sum_comm
  have hmem : ∑ m, (∑ j, a j * α j m) • b m ∈ W.N T := hx ▸ ((letE c' : LetA O n) • x).2
  have e : ((letE c' : LetA O n) • x : ↥(W.N T)) = ⟨_, hmem⟩ := Subtype.ext hx
  show W.cmp T ((letE c' : LetA O n) • x) ∈ _
  rw [e, cmp_sum_letter W T c' b hbN hbl _ hmem]
  exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨m, cmpD_of_mem W T (hbN m)⟩)

theorem constantCoeff_q_zero_eq_p : PowerSeries.constantCoeff W.q₀ = (PD.p : O) := by
  have h := congrArg (PowerSeries.coeff (0 + 1)) W.q₀_def
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
  rw [h, map_sub, show (1 + PowerSeries.X : PowerSeries O) =
      ((Polynomial.X + 1 : Polynomial O) : PowerSeries O) by simp [add_comm],
    ← Polynomial.coe_pow, Polynomial.coeff_coe, Polynomial.coeff_X_add_one_pow]
  simp

theorem dcrisL_succ_le [NeZero n] (hs : W.s = 1) (T : LocLat G Qp LL O) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T)
    {M h : ZMod n → ℕ} (h5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h) (i : ZMod n) :
    DcrisL PD T.ρ (W.emb (i + 1)) ≤
      Submodule.span LL ((φVB PD (LL := LL) (V := T.V)) '' (DcrisL PD T.ρ (W.emb i) : Set _)) := by
  refine (dcrisL_le_span W T h3 (i + 1)).trans (Submodule.span_le.2 ?_)
  rintro _ ⟨x, rfl⟩
  set S : Submodule LL (T.V ⊗[Qp] B) :=
    Submodule.span LL ((φVB PD (LL := LL) (V := T.V)) '' (DcrisL PD T.ρ (W.emb i) : Set _)) with hSdef
  have hQ : W.Q = W.q := by simp [LocWach.Q, hs]
  set k : ℕ := M (i + 1) with hk
  have key : ∀ z ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (i + 1 - 1)),
      (letE (i + 1) : LetA O n) • z = z ∧ W.Q ^ k • z ∈ W.N T ∧
        ∀ hz : W.Q ^ k • z ∈ W.N T, W.cmp T ⟨_, hz⟩ ∈ S := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      have hwN : w ∈ W.N T := Formalism.MainNotions.UnusedSlot80.ArcC.Nl_le_N W T _ hw
      have hwl : (letE (i + 1 - 1) : LetA O n) • w = w := letter_of_Nl W T _ hw
      have hφl : (letE (i + 1) : LetA O n) • W.φD T w = W.φD T w := by
        have := φD_pow_letter W T (i + 1 - 1) w hwl 1
        simpa using this
      refine ⟨hφl, h5.1 (i + 1) w hw, fun hz => ?_⟩
      have e := h3.2.2 ⟨w, hwN⟩ k hz
      rw [e]
      refine S.smul_mem _ (Submodule.subset_span ⟨_, cmp_mem_letter W T i hwN ?_, rfl⟩)
      rwa [show i + 1 - 1 = i by ring] at hwl
    | zero =>
      refine ⟨smul_zero _, by rw [smul_zero]; exact (W.N T).zero_mem, fun hz => ?_⟩
      have e : (⟨W.Q ^ k • (0 : W.DD T), hz⟩ : ↥(W.N T)) = 0 := Subtype.ext (by simp)
      rw [e, map_zero]; exact S.zero_mem
    | add z₁ z₂ _ _ h₁ h₂ =>
      refine ⟨by rw [smul_add, h₁.1, h₂.1], by rw [smul_add]; exact (W.N T).add_mem h₁.2.1 h₂.2.1,
        fun hz => ?_⟩
      have e : (⟨W.Q ^ k • (z₁ + z₂), hz⟩ : ↥(W.N T)) = ⟨_, h₁.2.1⟩ + ⟨_, h₂.2.1⟩ :=
        Subtype.ext (by simp [smul_add])
      rw [e, map_add]; exact S.add_mem (h₁.2.2 _) (h₂.2.2 _)
    | smul a z _ h₁ =>
      have hl : (letE (i + 1) : LetA O n) • (W.Q ^ k • z) = W.Q ^ k • z := by rw [smul_comm, h₁.1]
      refine ⟨by rw [smul_comm, h₁.1], by rw [smul_comm]; exact (W.N T).smul_mem a h₁.2.1, fun hz => ?_⟩
      have e : (⟨W.Q ^ k • (a • z), hz⟩ : ↥(W.N T)) =
          ⟨a • (W.Q ^ k • z), (W.N T).smul_mem a h₁.2.1⟩ := Subtype.ext (smul_comm _ _ _)
      rw [e, cmp_smul_letter W T (i + 1) a _ h₁.2.1 hl]
      exact S.smul_mem _ (h₁.2.2 _)
  have hyN : (letE (i + 1) : LetA O n) • (x : W.DD T) ∈ W.N T := (W.N T).smul_mem _ x.2
  have hyl : (letE (i + 1) : LetA O n) • (x : W.DD T) ∈ W.Nl T (i + 1) :=
    ⟨x, x.2, by rw [LinearMap.smul_apply, LinearMap.id_apply]⟩
  have hyl' := letter_of_Nl W T _ hyl
  obtain ⟨-, hmem, hc⟩ := key _ (h5.2.1 (i + 1) _ hyl)
  have e : (⟨W.Q ^ k • (W.Q ^ (h (i + 1)) • ((letE (i + 1) : LetA O n) • (x : W.DD T))), hmem⟩ :
      ↥(W.N T)) = ⟨(W.Q ^ (k + h (i + 1))) • ((letE (i + 1) : LetA O n) • (x : W.DD T)),
        (W.N T).smul_mem _ hyN⟩ := Subtype.ext (by
          change _ • _ • _ = _ • _
          rw [pow_add, mul_smul])
  have hS := hc hmem
  rw [e, cmp_smul_letter W T (i + 1) _ _ hyN hyl'] at hS
  have hcc : PowerSeries.constantCoeff ((W.Q ^ (k + h (i + 1))) (i + 1)) =
      (PD.p : O) ^ (k + h (i + 1)) := by
    rw [hQ, Pi.pow_apply, map_pow]
    show PowerSeries.constantCoeff W.q₀ ^ _ = _
    rw [constantCoeff_q_zero_eq_p]
  rw [hcc, map_pow, map_natCast] at hS
  have h2 := S.smul_mem ((PD.p : LL) ^ (k + h (i + 1)))⁻¹ hS
  rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (p_ne_zero W)), one_smul] at h2
  show W.cmp T ((letE (i + 1) : LetA O n) • x) ∈ S
  exact h2

theorem dv_single (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (k : Fin d) :
    Formalism.MainNotions.ArcLiftingSetup.dv W T e b (Pi.single k 1) =
      ((φVB PD (LL := LL) (V := T.V)) ^ e) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T (b k)) := by
  unfold Formalism.MainNotions.ArcLiftingSetup.dv
  simp [Pi.single_apply]

theorem pow_inj (T : LocLat G Qp LL O) (e : ℕ) :
    Function.Injective ((φVB PD (LL := LL) (V := T.V)) ^ e) := by
  induction e with
  | zero => intro x y h; simpa using h
  | succ e ih =>
    intro x y h
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply] at h
    exact ih (φVB_inj T h)

theorem frame_basis [NeZero n] (hs : W.s = 1) (hV : ValRing (LL := LL) O v) (T : LocLat G Qp LL O)
    (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) {M h : ZMod n → ℕ} (h5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (c' : ZMod n) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) :
    LinearIndependent LL (fun k : Fin d => Formalism.MainNotions.ArcLiftingSetup.dv W T e b (Pi.single k 1)) ∧
      Submodule.span LL (Set.range fun k : Fin d => Formalism.MainNotions.ArcLiftingSetup.dv W T e b (Pi.single k 1)) =
        DcrisL PD T.ρ (W.emb (c' + (e : ZMod n))) := by
  have hbN : ∀ k, b k ∈ W.N T := fun k => (hb.1 k).1.1
  have hbl : ∀ k, (letE c' : LetA O n) • b k = b k := fun k => letter_of_Nl W T c' (hb.1 k).2
  simp only [dv_single W T e b]
  have hcl : ∀ k, Formalism.MainNotions.ArcLiftingSetup.cmpD W T (b k) ∈ DcrisL PD T.ρ (W.emb c') := fun k => by
    rw [cmpD_of_mem W T (hbN k)]; exact cmp_mem_letter W T c' (hbN k) (hbl k)
  have hind : LinearIndependent LL fun k => Formalism.MainNotions.ArcLiftingSetup.cmpD W T (b k) :=
    linIndep_of_O W hV _ fun cc h0 => cmp_indepO W T h3 hmod c' b hb cc h0
  refine ⟨hind.map' _ (LinearMap.ker_eq_bot.2 (pow_inj T e)), le_antisymm ?_ ?_⟩
  · exact Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact φVB_pow_letter W T c' (hcl k) e)
  · have step : ∀ e' : ℕ, DcrisL PD T.ρ (W.emb (c' + (e' : ZMod n))) ≤
        (Submodule.span LL (Set.range fun k => Formalism.MainNotions.ArcLiftingSetup.cmpD W T (b k))).map
          ((φVB PD (LL := LL) (V := T.V)) ^ e') := by
      intro e'
      induction e' with
      | zero =>
        intro z hz
        simp only [Nat.cast_zero, add_zero] at hz
        exact ⟨z, dcrisL_le_spanB W T h3 hmod c' b hb hz, by simp⟩
      | succ e' ih =>
        have h1 := dcrisL_succ_le W hs T h3 h5 (c' + (e' : ZMod n))
        rw [show c' + (e' : ZMod n) + 1 = c' + ((e' + 1 : ℕ) : ZMod n) by push_cast; ring] at h1
        refine h1.trans (Submodule.span_le.2 ?_)
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨w, hw, rfl⟩ := ih hz
        exact ⟨w, hw, by rw [pow_succ', Module.End.mul_apply]⟩
    intro z hz
    have := step e hz
    rw [Submodule.map_span, ← Set.range_comp] at this
    exact this

theorem arcHyp_frameBasis [NeZero n] (hV : ValRing (LL := LL) O v) (h3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hmod : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) :
    Formalism.MainNotions.UnusedSlot80.ArcC.ArcHyp W (Formalism.MainNotions.UnusedSlot80.ArcC.FrameBasis W) := by
  intro hCA _ A hA c _ e _ _ T hT d b sol hb
  exact frame_basis W hCA.2.1 hV T (h3 T hT.1) (h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT))
    (hmod T hT.1) _ e b hb.1

theorem phi_trunc (T : LocLat G Qp LL O) (e R : ℕ) {d : ℕ} (b : Fin d → W.DD T) (y : ℕ → Fin d → O) :
    ((W.φD T) ^ e) (∑ r ∈ Finset.range R, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (y r)) =
      ∑ m, (∑ r ∈ Finset.range R, ((W.φA ^ e) W.π₀) ^ r * algebraMap O (LetA O n) (y r m)) •
        ((W.φD T) ^ e) (b m) := by
  rw [map_sum]
  have h1 : ∀ r ∈ Finset.range R, ((W.φD T) ^ e) (W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (y r)) =
      ∑ m, (((W.φA ^ e) W.π₀) ^ r * algebraMap O (LetA O n) (y r m)) • ((W.φD T) ^ e) (b m) := by
    intro r _
    rw [Formalism.MainNotions.UnusedSlot80.Relay2.φpow_smul, map_pow, Formalism.MainNotions.LiftingTheory.vecB, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, ← algebraMap_smul (LetA O n) (y r m), smul_smul]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_smul]

theorem phiA_pow_comp (e j : ℕ) (hje : j ≤ e) (r : ℕ) :
    (W.φA ^ (e - j)) (((W.φA ^ j) W.π₀) ^ r) = ((W.φA ^ e) W.π₀) ^ r := by
  rw [map_pow, ← AlgHom.mul_apply, ← pow_add, Nat.sub_add_cancel hje]

theorem pOfSec [IsDomain O] (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hR : Formalism.MainNotions.LiftingTheory.UniformizerRingClause W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W) (hH : Formalism.MainNotions.LiftingTheory.coreH W)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5p : 5 ≤ PD.p) (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (hA : A.OK)
    (c' : ZMod n) (e : ℕ) (hje : A.j ≤ e) (T : LocLat G Qp LL O) (hTc : IsCrys PD T.ρ) (d : ℕ)
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : Formalism.MainNotions.ArcLiftingSetup.IsHor W T c' b sol) :
    Formalism.MainNotions.UnusedSlot80.ArcC.POfSec W A c' e T d b sol := by
  intro f hf
  have hl : 2 ≤ PD.p := PD.hp.two_le
  have hsgσ := Formalism.MainNotions.UnusedSlot80.Relay2.sig_le A PD.p
  choose u hu hfu using hf
  have hHc := hH hCA T hTc c'
  have hBd := (hHc.2.2.2.2 d b hb.1 sol hb.2).1
  have h4 := hHc.2.2.2.1
  choose g hg using fun k r m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hO2 r (h4 r) _ (hBd k r m)
  let yy : Fin d → ℕ → Fin d → O := fun k r m =>
    ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p (A.M PD.p) - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g k r m
  have hyyLL : ∀ k, ∀ r < A.M PD.p, ∀ m, algebraMap O LL (yy k r m) =
      (PD.p : LL) ^ Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p (A.M PD.p) * sol k r m := by
    intro k r hr m
    have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le
    simp only [yy, map_mul, map_pow, map_natCast, hg]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  choose ta hta tB htB htr using fun r =>
    Formalism.MainNotions.LiftingTheory.tr_trunc_int W hR hCA.2.2 A.j (2 * A.G₀) (A.M PD.p) r hA.2.1
  obtain ⟨uu, huu, hJJ⟩ := Formalism.MainNotions.UnusedSlot80.ArcC.arc_ring W (hTr hCA).2.1 hR.1 h5p A hA (c' + (e : ZMod n)) e hje

  have hterm : ∀ k r m, r < A.M PD.p →
      ((PD.p : ℕ) : LetA O n) ^ A.σ PD.p * (((W.φA ^ e) W.π₀) ^ r * algebraMap O (LetA O n) (yy k r m)) =
        ((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p (A.M PD.p) *
          (((PD.p : ℕ) : LetA O n) ^ (A.σ PD.p - Formalism.NOK.sigNOK PD.p (2 * A.G₀) (A.M PD.p) A.j) *
            algebraMap O (LetA O n) (g k r m) * (W.φA ^ (e - A.j)) (ta r)) +
        W.π₀ * Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e ^ 2 *
          (((PD.p : ℕ) : LetA O n) ^ (A.σ PD.p - Formalism.NOK.sigNOK PD.p (2 * A.G₀) (A.M PD.p) A.j) *
            algebraMap O (LetA O n) (yy k r m) * uu * (W.φA ^ (e - A.j)) (tB r)) := by
    intro k r m hr
    have H := congrArg (W.φA ^ (e - A.j)) (htr r)
    rw [map_mul, map_pow, map_natCast, phiA_pow_comp W e A.j hje, map_add, map_mul, map_mul, map_pow,
      map_natCast, hJJ] at H
    have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le
    have hEx : Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r = ⌈(r : ℝ) * PD.p / ((PD.p : ℝ) - 1)⌉₊ := rfl
    have hy' : algebraMap O (LetA O n) (yy k r m) =
        ((PD.p : ℕ) : LetA O n) ^ (Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p (A.M PD.p) - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) *
          algebraMap O (LetA O n) (g k r m) := by
      simp only [yy, map_mul, map_pow, map_natCast]
    have e1 : ((PD.p : ℕ) : LetA O n) ^ A.σ PD.p =
        ((PD.p : ℕ) : LetA O n) ^ (A.σ PD.p - Formalism.NOK.sigNOK PD.p (2 * A.G₀) (A.M PD.p) A.j) *
          ((PD.p : ℕ) : LetA O n) ^ Formalism.NOK.sigNOK PD.p (2 * A.G₀) (A.M PD.p) A.j := by
      rw [← pow_add, Nat.sub_add_cancel hsgσ]
    have e2 : ((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p (A.M PD.p) =
        ((PD.p : ℕ) : LetA O n) ^ (Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p (A.M PD.p) - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) *
          ((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [hEx] at hy' e2
    rw [e1, e2]
    linear_combination (((PD.p : ℕ) : LetA O n) ^ (A.σ PD.p - Formalism.NOK.sigNOK PD.p (2 * A.G₀) (A.M PD.p) A.j) *
        algebraMap O (LetA O n) (yy k r m)) * H +
      (((PD.p : ℕ) : LetA O n) ^ (A.σ PD.p - Formalism.NOK.sigNOK PD.p (2 * A.G₀) (A.M PD.p) A.j) *
        (W.φA ^ (e - A.j)) (ta r) * ((PD.p : ℕ) : LetA O n) ^ ⌈(r : ℝ) * PD.p / ((PD.p : ℝ) - 1)⌉₊) * hy'

  let E : Fin d → LetA O n := fun k => letE (c' + (e : ZMod n)) * 1 * u k
  let γ : Fin d → LetA O n := fun m => ∑ k, E k * ∑ r ∈ Finset.range (A.M PD.p),
    ((PD.p : ℕ) : LetA O n) ^ (A.σ PD.p - Formalism.NOK.sigNOK PD.p (2 * A.G₀) (A.M PD.p) A.j) *
      algebraMap O (LetA O n) (g k r m) * (W.φA ^ (e - A.j)) (ta r)
  let gg : Fin d → LetA O n := fun m => ∑ k, E k * ∑ r ∈ Finset.range (A.M PD.p),
    ((PD.p : ℕ) : LetA O n) ^ (A.σ PD.p - Formalism.NOK.sigNOK PD.p (2 * A.G₀) (A.M PD.p) A.j) *
      algebraMap O (LetA O n) (yy k r m) * uu * (W.φA ^ (e - A.j)) (tB r)
  have hE : ∀ k, E k ∈ W.AΔ := fun k =>
    W.AΔ.mul_mem (W.AΔ.mul_mem (SatPW.letE_mem_AΔ W _) W.AΔ.one_mem) (hu k)
  have hpA : ∀ t : ℕ, ((PD.p : ℕ) : LetA O n) ^ t ∈ W.AΔ := fun t => W.AΔ.pow_mem (W.AΔ.natCast_mem _) t
  have hγ : ∀ m, γ m ∈ W.AΔ := fun m => W.AΔ.sum_mem fun k _ => W.AΔ.mul_mem (hE k)
    (W.AΔ.sum_mem fun r _ => W.AΔ.mul_mem (W.AΔ.mul_mem (hpA _) (W.AΔ.algebraMap_mem _))
      (φA_pow_mem_AΔ W (hta r) _))
  have hgg : ∀ m, gg m ∈ W.AΔ := fun m => W.AΔ.sum_mem fun k _ => W.AΔ.mul_mem (hE k)
    (W.AΔ.sum_mem fun r _ => W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (hpA _)
      (W.AΔ.algebraMap_mem _)) huu) (φA_pow_mem_AΔ W (htB r) _))
  have hmain : ∀ m, ∑ k, (((PD.p : ℕ) : LetA O n) ^ A.σ PD.p * E k) *
      ∑ r ∈ Finset.range (A.M PD.p), ((W.φA ^ e) W.π₀) ^ r * algebraMap O (LetA O n) (yy k r m) =
      ((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p (A.M PD.p) * γ m +
        W.π₀ * Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e ^ 2 * gg m := by
    intro m
    simp only [γ, gg, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun r hr => ?_
    have := hterm k r m (Finset.mem_range.1 hr)
    linear_combination E k * this

  obtain ⟨h3, h6⟩ := SatW.ring_clauses W hR
  have hUPi : SatW.UPi PD.p (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e) :=
    SatW.UPi.prod _ _ fun s _ => (SatW.UPi_qpow W h3 h6 s).pow _
  obtain ⟨U, hU⟩ := SatW.isUnit_EE_of_UPi W hUPi
  let yv : W.DD T := ∑ m, γ m • ((W.φD T) ^ e) (b m)
  have hyv : yv ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c' e := AddSubgroup.sum_mem _ fun m _ =>
    Formalism.MainNotions.UnusedSlot80.Relay2.Pp_gen W T c' e (hγ m) (hb.1.1 m)
  let x : W.DD T := ((U⁻¹ : W.EEˣ) : W.EE) • yv
  have hΛx : Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e • x = yv := by
    rw [← algebraMap_smul W.EE (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e) x, ← hU]
    simp only [x, smul_smul, Units.mul_inv, one_smul]
  refine ⟨x, ⟨yv, hyv, by rw [hΛx, one_smul]⟩, Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p (A.M PD.p), 0,
    fun k => ∑ r ∈ Finset.range (A.M PD.p), W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r),
    fun k => ((PD.p : ℕ) : LetA O n) ^ A.σ PD.p * E k, fun k => ⟨yy k, hyyLL k, rfl⟩,
    fun k => ⟨W.AΔ.mul_mem (hpA _) (hE k), ?_⟩, ?_⟩
  · rw [map_mul, map_pow, map_natCast, ← hfu k]
    unfold Formalism.MainNotions.ArcLiftingSetup.lE
    ring
  · have hsum : ∑ k, (((PD.p : ℕ) : LetA O n) ^ A.σ PD.p * E k) •
        ((W.φD T) ^ e) (∑ r ∈ Finset.range (A.M PD.p), W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r)) =
        ∑ m, (((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p (A.M PD.p) * γ m +
          W.π₀ * Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e ^ 2 * gg m) • ((W.φD T) ^ e) (b m) := by
      simp only [phi_trunc, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← hmain m, Finset.sum_smul]
    have hfin : Formalism.MainNotions.ArcLiftingSetup.lA W ^ 0 • (Formalism.MainNotions.ArcLiftingSetup.lA W ^ Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p (A.M PD.p) •
        Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e • x -
        ∑ k, (((PD.p : ℕ) : LetA O n) ^ A.σ PD.p * E k) •
          ((W.φD T) ^ e) (∑ r ∈ Finset.range (A.M PD.p), W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r))) =
        (W.π₀ * Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e ^ 2) •
          ∑ m, (-gg m) • ((W.φD T) ^ e) (b m) := by
      rw [pow_zero, one_smul, hΛx, hsum]
      simp only [yv, Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← sub_smul]
      congr 1
      unfold Formalism.MainNotions.ArcLiftingSetup.lA
      ring
    rw [hfin]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_of_mem W T c' e _ (AddSubgroup.sum_mem _ fun m _ =>
      Formalism.MainNotions.UnusedSlot80.Relay2.Pp_gen W T c' e (W.AΔ.neg_mem (hgg m)) (hb.1.1 m))

theorem tr_mono [IsDomain O] (hR : Formalism.MainNotions.LiftingTheory.UniformizerRingClause W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5p : 5 ≤ PD.p) (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (hA : A.OK) (a : ZMod n)
    (e : ℕ) (hje : A.j ≤ e) (r : ℕ) :
    ∃ a₁ ∈ W.AΔ, ∃ a₂ ∈ W.AΔ, ((PD.p : ℕ) : LetA O n) ^ A.σ PD.p * ((W.φA ^ e) W.π₀) ^ r =
      ((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r * a₁ +
        W.π₀ * Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A a e ^ 2 * a₂ := by
  have hsgσ := Formalism.MainNotions.UnusedSlot80.Relay2.sig_le A PD.p
  obtain ⟨ta, hta, tB, htB, htr⟩ :=
    Formalism.MainNotions.LiftingTheory.tr_trunc_int W hR hCA.2.2 A.j (2 * A.G₀) (A.M PD.p) r hA.2.1
  obtain ⟨uu, huu, hJJ⟩ := Formalism.MainNotions.UnusedSlot80.ArcC.arc_ring W (hTr hCA).2.1 hR.1 h5p A hA a e hje
  have H := congrArg (W.φA ^ (e - A.j)) htr
  rw [map_mul, map_pow, map_natCast, phiA_pow_comp W e A.j hje, map_add, map_mul, map_mul, map_pow,
    map_natCast, hJJ] at H
  have hpA : ∀ t : ℕ, ((PD.p : ℕ) : LetA O n) ^ t ∈ W.AΔ := fun t => W.AΔ.pow_mem (W.AΔ.natCast_mem _) t
  refine ⟨((PD.p : ℕ) : LetA O n) ^ (A.σ PD.p - Formalism.NOK.sigNOK PD.p (2 * A.G₀) (A.M PD.p) A.j) *
      (W.φA ^ (e - A.j)) ta, W.AΔ.mul_mem (hpA _) (φA_pow_mem_AΔ W hta _),
    ((PD.p : ℕ) : LetA O n) ^ (A.σ PD.p - Formalism.NOK.sigNOK PD.p (2 * A.G₀) (A.M PD.p) A.j) * uu *
      (W.φA ^ (e - A.j)) tB, W.AΔ.mul_mem (W.AΔ.mul_mem (hpA _) huu) (φA_pow_mem_AΔ W htB _), ?_⟩
  have e1 : ((PD.p : ℕ) : LetA O n) ^ A.σ PD.p =
      ((PD.p : ℕ) : LetA O n) ^ (A.σ PD.p - Formalism.NOK.sigNOK PD.p (2 * A.G₀) (A.M PD.p) A.j) *
        ((PD.p : ℕ) : LetA O n) ^ Formalism.NOK.sigNOK PD.p (2 * A.G₀) (A.M PD.p) A.j := by
    rw [← pow_add, Nat.sub_add_cancel hsgσ]
  have hEx : Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r = ⌈(r : ℝ) * PD.p / ((PD.p : ℝ) - 1)⌉₊ := rfl
  rw [e1, hEx]
  linear_combination ((PD.p : ℕ) : LetA O n) ^ (A.σ PD.p - Formalism.NOK.sigNOK PD.p (2 * A.G₀) (A.M PD.p) A.j) * H

theorem yM_mem [IsDomain O] (hR : Formalism.MainNotions.LiftingTheory.UniformizerRingClause W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5p : 5 ≤ PD.p) (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (hA : A.OK) (a : ZMod n)
    (e : ℕ) (hje : A.j ≤ e) :
    ∃ ν ∈ W.AΔ, ((W.φA ^ e) W.π₀) ^ A.M PD.p = W.π₀ * Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A a e ^ 2 * ν := by
  have hl : 2 ≤ PD.p := PD.hp.two_le
  obtain ⟨B, hB, hv⟩ := Formalism.MainNotions.LiftingTheory.tr_vanish_int W hR A.j (2 * A.G₀) (A.M PD.p) (A.M PD.p) le_rfl
    (Formalism.MainNotions.UnusedSlot80.Relay2.arith_M PD.p A.G₀ A.h hl hA.2.2.2.2.2.1)
  obtain ⟨uu, huu, hJJ⟩ := Formalism.MainNotions.UnusedSlot80.ArcC.arc_ring W (hTr hCA).2.1 hR.1 h5p A hA a e hje
  have H := congrArg (W.φA ^ (e - A.j)) hv
  rw [phiA_pow_comp W e A.j hje, map_mul, hJJ] at H
  exact ⟨(W.φA ^ (e - A.j)) B * uu, W.AΔ.mul_mem (φA_pow_mem_AΔ W hB _) huu, by rw [H]; ring⟩

theorem Pp_repr (T : LocLat G Qp LL O) (c' : ZMod n) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) :
    ∀ y ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c' e, ∃ β : Fin d → LetA O n, (∀ m, β m ∈ W.AΔ) ∧
      y = ∑ m, β m • ((W.φD T) ^ e) (b m) := by
  refine Formalism.MainNotions.UnusedSlot80.Relay2.Pp_ind W T c' e _ ⟨0, fun _ => W.AΔ.zero_mem, by simp⟩ ?_ ?_ ?_
  · rintro x y ⟨β₁, h₁, rfl⟩ ⟨β₂, h₂, rfl⟩
    exact ⟨β₁ + β₂, fun m => W.AΔ.add_mem (h₁ m) (h₂ m), by
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
  · rintro x ⟨β, h, rfl⟩
    exact ⟨-β, fun m => W.AΔ.neg_mem (h m), by
      simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]⟩
  · intro a ha x hx
    obtain ⟨α, hα, hxα⟩ := (hb.2 x hx).exists
    refine ⟨fun m => a * (W.φA ^ e) (α m), fun m => W.AΔ.mul_mem ha (φA_pow_mem_AΔ W (hα m).1 e), ?_⟩
    rw [hxα, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Formalism.MainNotions.UnusedSlot80.Relay2.φpow_smul, smul_smul]

theorem frame_inv_poly (hinj : Function.Injective (algebraMap O LL)) {d : ℕ}
    (sol : Fin d → ℕ → Fin d → LL) (hsol0 : ∀ k, sol k 0 = Pi.single k 1) (M κ : ℕ)
    (yy : Fin d → ℕ → Fin d → O) (hyy : ∀ k, ∀ r < M, ∀ m, algebraMap O LL (yy k r m) = (PD.p : LL) ^ κ * sol k r m)
    (zz : ℕ → Fin d → Fin d → O)
    (hzz : ∀ r < M, ∀ k m, algebraMap O LL (zz r k m) = (PD.p : LL) ^ κ *
      PowerSeries.coeff r ((Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' :
        Matrix (Fin d) (Fin d) (PowerSeries LL))⁻¹ k m))
    {R : Type} [CommRing R] [Algebra O R] (Y : R) (m m' : Fin d) :
    ∃ ρ : Polynomial O, ∑ k, (∑ r ∈ Finset.range M, algebraMap O R (yy k r m) * Y ^ r) *
        (∑ r ∈ Finset.range M, algebraMap O R (zz r k m') * Y ^ r) =
      algebraMap O R (((PD.p : ℕ) : O) ^ (2 * κ) * if m = m' then 1 else 0) + Y ^ M * Polynomial.aeval Y ρ := by
  set Hps : Matrix (Fin d) (Fin d) (PowerSeries LL) :=
    Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' with hHps
  have hdet : IsUnit Hps.det := by
    rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
    have h1 : (PowerSeries.constantCoeff : PowerSeries LL →+* LL).mapMatrix Hps = 1 := by
      ext i k
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hHps, Matrix.of_apply,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_mk, hsol0,
        Matrix.one_apply, Pi.single_apply]
    rw [h1, Matrix.det_one]
    exact isUnit_one
  have hinv : Hps * Hps⁻¹ = 1 := Matrix.mul_nonsing_inv Hps hdet
  have hcoef : ∀ t, ∑ k, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal t, sol k x.1 m * PowerSeries.coeff x.2 (Hps⁻¹ k m') =
      if t = 0 ∧ m = m' then 1 else 0 := by
    intro t
    have h := congrArg (fun Q : Matrix (Fin d) (Fin d) (PowerSeries LL) => PowerSeries.coeff t (Q m m')) hinv
    simp only [Matrix.mul_apply, map_sum, PowerSeries.coeff_mul, hHps, Matrix.of_apply,
      PowerSeries.coeff_mk] at h
    rw [h, Matrix.one_apply]
    by_cases hm : m = m'
    · by_cases ht : t = 0
      · subst ht; simp [hm]
      · simp [hm, ht, PowerSeries.coeff_one]
    · simp [hm]
  let HP : Fin d → Polynomial O := fun k =>
    ∑ r ∈ Finset.range M, Polynomial.C (yy k r m) * Polynomial.X ^ r
  let GP : Fin d → Polynomial O := fun k =>
    ∑ r ∈ Finset.range M, Polynomial.C (zz r k m') * Polynomial.X ^ r
  have hHPc : ∀ k i, (HP k).coeff i = if i < M then yy k i m else 0 := by
    intro k i
    simp only [HP, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range]
  have hGPc : ∀ k i, (GP k).coeff i = if i < M then zz i k m' else 0 := by
    intro k i
    simp only [GP, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range]
  set cst : O := ((PD.p : ℕ) : O) ^ (2 * κ) * if m = m' then 1 else 0 with hcst
  set Q : Polynomial O := ∑ k, HP k * GP k - Polynomial.C cst with hQdef
  have hQ : ∀ t < M, Q.coeff t = 0 := by
    intro t ht
    apply hinj
    rw [map_zero, hQdef, Polynomial.coeff_sub, Polynomial.finset_sum_coeff, Polynomial.coeff_C, map_sub,
      map_sum]
    have hk : ∀ k, algebraMap O LL ((HP k * GP k).coeff t) = (PD.p : LL) ^ (2 * κ) *
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal t, sol k x.1 m * PowerSeries.coeff x.2 (Hps⁻¹ k m') := by
      intro k
      rw [Polynomial.coeff_mul, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      rw [hHPc, hGPc, if_pos (by omega), if_pos (by omega), map_mul, hyy k x.1 (by omega),
        hzz x.2 (by omega)]
      ring
    rw [Finset.sum_congr rfl fun k _ => hk k, ← Finset.mul_sum, hcoef t, hcst]
    by_cases ht0 : t = 0
    · subst ht0
      by_cases hm : m = m' <;> simp [hm]
    · simp [ht0]
  obtain ⟨ρ, hρ⟩ := (Polynomial.X_pow_dvd_iff).2 hQ
  refine ⟨ρ, ?_⟩
  have h := congrArg (Polynomial.aeval Y) hρ
  simp only [hQdef, map_sub, map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, HP, GP,
    Polynomial.aeval_X] at h
  rw [← h]
  ring

theorem aeval_mem_AΔ {Y : LetA O n} (hY : Y ∈ W.AΔ) (ρ : Polynomial O) : Polynomial.aeval Y ρ ∈ W.AΔ := by
  rw [Polynomial.aeval_eq_sum_range]
  exact W.AΔ.sum_mem fun i _ => W.AΔ.smul_mem (W.AΔ.pow_mem hY i) _

theorem secOfP [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hR : Formalism.MainNotions.LiftingTheory.UniformizerRingClause W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W) (hH : Formalism.MainNotions.LiftingTheory.coreH W)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5p : 5 ≤ PD.p) (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (hA : A.OK)
    (c' : ZMod n) (e : ℕ) (hje : A.j ≤ e) (T : LocLat G Qp LL O) (hTc : IsCrys PD T.ρ) (d : ℕ)
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : Formalism.MainNotions.ArcLiftingSetup.IsHor W T c' b sol) :
    Formalism.MainNotions.UnusedSlot80.ArcC.SecOfP W A c' e T d b sol := by
  intro x hx
  have hl : 2 ≤ PD.p := PD.hp.two_le
  obtain ⟨yP, hyP, hyx⟩ := hx
  rw [one_smul] at hyx
  obtain ⟨β₀, hβ₀, hyβ⟩ := Pp_repr W T c' e b hb.1 yP hyP
  have hbl : ∀ m, (letE c' : LetA O n) • b m = b m := fun m => letter_of_Nl W T c' (hb.1.1 m).2
  have hφl : ∀ m, (letE (c' + (e : ZMod n)) : LetA O n) • ((W.φD T) ^ e) (b m) = ((W.φD T) ^ e) (b m) :=
    fun m => φD_pow_letter W T c' (b m) (hbl m) e
  let β : Fin d → LetA O n := fun m => letE (c' + (e : ZMod n)) * β₀ m
  have hβ : ∀ m, β m ∈ W.AΔ := fun m => W.AΔ.mul_mem (SatPW.letE_mem_AΔ W _) (hβ₀ m)
  have hΛx : Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e • x = ∑ m, β m • ((W.φD T) ^ e) (b m) := by
    rw [hyx, hyβ]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [β, mul_smul]
    rw [smul_comm, hφl]

  have hHc := hH hCA T hTc c'
  have hH5 := hHc.2.2.2.2 d b hb.1 sol hb.2
  have h4 := hHc.2.2.2.1
  choose g hg using fun k r m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hO2 r (h4 r) _ (hH5.1 k r m)
  choose g' hg' using fun r k m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hO2 r (h4 r) _ (hH5.2 k m r)
  let κ : ℕ := Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p (A.M PD.p)
  let yy : Fin d → ℕ → Fin d → O := fun k r m =>
    ((PD.p : ℕ) : O) ^ (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g k r m
  let zz : ℕ → Fin d → Fin d → O := fun r k m =>
    ((PD.p : ℕ) : O) ^ (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g' r k m
  have hyy : ∀ k, ∀ r < A.M PD.p, ∀ m, algebraMap O LL (yy k r m) = (PD.p : LL) ^ κ * sol k r m := by
    intro k r hr m
    have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le
    simp only [yy, map_mul, map_pow, map_natCast, hg]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  have hzz : ∀ r < A.M PD.p, ∀ k m, algebraMap O LL (zz r k m) = (PD.p : LL) ^ κ *
      PowerSeries.coeff r ((Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' :
        Matrix (Fin d) (Fin d) (PowerSeries LL))⁻¹ k m) := by
    intro r hr k m
    have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le
    simp only [zz, map_mul, map_pow, map_natCast, hg']
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

  set Y : LetA O n := (W.φA ^ e) W.π₀ with hYdef
  have hY : Y ∈ W.AΔ := φA_pow_mem_AΔ W hR.1 e
  set D : LetA O n := W.π₀ * Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e ^ 2 with hDdef
  choose a₁ ha₁ a₂ ha₂ htm using fun r => tr_mono W hR hTr hCA h5p A hA (c' + (e : ZMod n)) e hje r
  obtain ⟨ν, hν, hYM⟩ := yM_mem W hR hTr hCA h5p A hA (c' + (e : ZMod n)) e hje
  choose ρ hρ using fun m m' => frame_inv_poly hinj sol (fun k => (hb.2 k).2) (A.M PD.p) κ yy hyy zz hzz Y m m'
  let HY : Fin d → Fin d → LetA O n := fun m k =>
    ∑ r ∈ Finset.range (A.M PD.p), algebraMap O (LetA O n) (yy k r m) * Y ^ r
  let GY : Fin d → Fin d → LetA O n := fun k m' =>
    ∑ r ∈ Finset.range (A.M PD.p), algebraMap O (LetA O n) (zz r k m') * Y ^ r
  let Γ : Fin d → Fin d → LetA O n := fun k m' =>
    ∑ r ∈ Finset.range (A.M PD.p), algebraMap O (LetA O n) (g' r k m') * a₁ r
  let Ξ : Fin d → Fin d → LetA O n := fun k m' =>
    ∑ r ∈ Finset.range (A.M PD.p), algebraMap O (LetA O n) (zz r k m') * a₂ r
  have hpA : ∀ t : ℕ, ((PD.p : ℕ) : LetA O n) ^ t ∈ W.AΔ := fun t => W.AΔ.pow_mem (W.AΔ.natCast_mem _) t
  have hHY : ∀ m k, HY m k ∈ W.AΔ := fun m k => W.AΔ.sum_mem fun r _ =>
    W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (W.AΔ.pow_mem hY r)
  have hΓ : ∀ k m', Γ k m' ∈ W.AΔ := fun k m' => W.AΔ.sum_mem fun r _ =>
    W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (ha₁ r)
  have hΞ : ∀ k m', Ξ k m' ∈ W.AΔ := fun k m' => W.AΔ.sum_mem fun r _ =>
    W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (ha₂ r)

  have hT1 : ∀ k m', ((PD.p : ℕ) : LetA O n) ^ A.σ PD.p * GY k m' =
      ((PD.p : ℕ) : LetA O n) ^ κ * Γ k m' + D * Ξ k m' := by
    intro k m'
    simp only [GY, Γ, Ξ, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl (Finset.mem_range.1 hr).le
    have hz : algebraMap O (LetA O n) (zz r k m') = ((PD.p : ℕ) : LetA O n) ^
        (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * algebraMap O (LetA O n) (g' r k m') := by
      simp only [zz, map_mul, map_pow, map_natCast]
    have e2 : ((PD.p : ℕ) : LetA O n) ^ κ = ((PD.p : ℕ) : LetA O n) ^
        (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * ((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [e2]
    linear_combination (algebraMap O (LetA O n) (zz r k m')) * htm r +
      (((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r * a₁ r) * hz

  let aa : Fin d → LetA O n := fun k => ∑ m', Γ k m' * β m'
  have haa : ∀ k, aa k ∈ W.AΔ := fun k => W.AΔ.sum_mem fun m' _ => W.AΔ.mul_mem (hΓ k m') (hβ m')
  have haal : ∀ k, letE (c' + (e : ZMod n)) * 1 * aa k = aa k := by
    intro k
    simp only [aa, mul_one, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    simp only [β]
    linear_combination (Γ k m' * β₀ m') * (letE_mul_self (O := O) (c' + (e : ZMod n)))
  obtain ⟨h3, h6⟩ := SatW.ring_clauses W hR
  have hUPi : SatW.UPi PD.p (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e) :=
    SatW.UPi.prod _ _ fun s _ => (SatW.UPi_qpow W h3 h6 s).pow _
  obtain ⟨U, hU⟩ := SatW.isUnit_EE_of_UPi W hUPi
  have hcoef : ∀ k, algebraMap (LetA O n) W.EE (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e) *
      (((U⁻¹ : W.EEˣ) : W.EE) * algebraMap (LetA O n) W.EE (aa k)) = algebraMap (LetA O n) W.EE (aa k) := by
    intro k
    rw [← hU, ← mul_assoc, Units.mul_inv, one_mul]

  let w : Fin d → LetA O n := fun m =>
    (∑ m', (∑ k, HY m k * Ξ k m') * β m') -
      ((PD.p : ℕ) : LetA O n) ^ A.σ PD.p * ν * ∑ m', Polynomial.aeval Y (ρ m m') * β m'
  have hw : ∀ m, w m ∈ W.AΔ := fun m => W.AΔ.sub_mem
    (W.AΔ.sum_mem fun m' _ => W.AΔ.mul_mem (W.AΔ.sum_mem fun k _ => W.AΔ.mul_mem (hHY m k) (hΞ k m'))
      (hβ m'))
    (W.AΔ.mul_mem (W.AΔ.mul_mem (hpA _) hν) (W.AΔ.sum_mem fun m' _ =>
      W.AΔ.mul_mem (aeval_mem_AΔ W hY _) (hβ m')))
  have hkey : ∀ m, ((PD.p : ℕ) : LetA O n) ^ κ * (((PD.p : ℕ) : LetA O n) ^ κ *
      ((PD.p : ℕ) : LetA O n) ^ A.σ PD.p * β m - ∑ k, aa k * HY m k) = D * w m := by
    intro m
    have A1 : ((PD.p : ℕ) : LetA O n) ^ κ * ∑ k, aa k * HY m k =
        (∑ m', ((PD.p : ℕ) : LetA O n) ^ A.σ PD.p * (∑ k, HY m k * GY k m') * β m') -
          D * ∑ m', (∑ k, HY m k * Ξ k m') * β m' := by
      have L : ((PD.p : ℕ) : LetA O n) ^ κ * ∑ k, aa k * HY m k =
          ∑ m', ∑ k, ((PD.p : ℕ) : LetA O n) ^ κ * Γ k m' * β m' * HY m k := by
        simp only [aa, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m' _ => Finset.sum_congr rfl fun k _ => by ring
      have R : (∑ m', ((PD.p : ℕ) : LetA O n) ^ A.σ PD.p * (∑ k, HY m k * GY k m') * β m') -
          D * ∑ m', (∑ k, HY m k * Ξ k m') * β m' =
          ∑ m', ∑ k, (((PD.p : ℕ) : LetA O n) ^ A.σ PD.p * (HY m k * GY k m') * β m' -
            D * (HY m k * Ξ k m') * β m') := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun m' _ => ?_
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [L, R]
      refine Finset.sum_congr rfl fun m' _ => Finset.sum_congr rfl fun k _ => ?_
      linear_combination (-(HY m k * β m')) * hT1 k m'
    have A2 : ∑ m', ((PD.p : ℕ) : LetA O n) ^ A.σ PD.p * (∑ k, HY m k * GY k m') * β m' =
        ((PD.p : ℕ) : LetA O n) ^ A.σ PD.p * ((PD.p : ℕ) : LetA O n) ^ (2 * κ) * β m +
          ((PD.p : ℕ) : LetA O n) ^ A.σ PD.p * Y ^ A.M PD.p *
            ∑ m', Polynomial.aeval Y (ρ m m') * β m' := by
      have h1 : ∀ m', ((PD.p : ℕ) : LetA O n) ^ A.σ PD.p * (∑ k, HY m k * GY k m') * β m' =
          ((PD.p : ℕ) : LetA O n) ^ A.σ PD.p * ((PD.p : ℕ) : LetA O n) ^ (2 * κ) *
            ((if m = m' then 1 else 0) * β m') +
          ((PD.p : ℕ) : LetA O n) ^ A.σ PD.p * Y ^ A.M PD.p * (Polynomial.aeval Y (ρ m m') * β m') := by
        intro m'
        have := hρ m m'
        simp only [HY, GY] at this ⊢
        rw [this, map_mul, map_pow, map_natCast, apply_ite (algebraMap O (LetA O n)), map_one, map_zero]
        split_ifs <;> ring
      rw [Finset.sum_congr rfl fun m' _ => h1 m', Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp only [w]
    linear_combination -A1 - A2 -
      (((PD.p : ℕ) : LetA O n) ^ A.σ PD.p * ∑ m', Polynomial.aeval Y (ρ m m') * β m') * hYM
  refine ⟨fun k => ((U⁻¹ : W.EEˣ) : W.EE) * algebraMap (LetA O n) W.EE (aa k),
    fun k => ⟨aa k, haa k, by rw [hcoef k, haal k]⟩, κ, κ,
    fun k => ∑ r ∈ Finset.range (A.M PD.p), W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r), aa,
    fun k => ⟨yy k, hyy k, rfl⟩, fun k => ⟨haa k, hcoef k⟩, ?_⟩
  have hsum : ∑ k, aa k • ((W.φD T) ^ e)
      (∑ r ∈ Finset.range (A.M PD.p), W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r)) =
      ∑ m, (∑ k, aa k * HY m k) • ((W.φD T) ^ e) (b m) := by
    simp only [phi_trunc, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp only [HY, ← hYdef]
    congr 1
    refine Finset.sum_congr rfl fun r _ => mul_comm _ _
  have hfin : Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ • (Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ • Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e •
      (Formalism.MainNotions.ArcLiftingSetup.lA W ^ A.σ PD.p • x) - ∑ k, aa k • ((W.φD T) ^ e)
        (∑ r ∈ Finset.range (A.M PD.p), W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r))) =
      D • ∑ m, w m • ((W.φD T) ^ e) (b m) := by
    rw [hsum, smul_comm (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e), hΛx]
    simp only [Finset.smul_sum]
    rw [← Finset.sum_sub_distrib]
    simp only [Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [smul_smul]
    rw [← sub_smul, smul_smul, ← hkey m]
    congr 1
    unfold Formalism.MainNotions.ArcLiftingSetup.lA
    ring
  rw [hfin]
  exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_of_mem W T c' e _ (AddSubgroup.sum_mem _ fun m _ =>
    Formalism.MainNotions.UnusedSlot80.Relay2.Pp_gen W T c' e (hw m) (hb.1.1 m))

theorem inFr_lE {a : ZMod n} {num den : LetA O n} {f : W.EE} (h : Formalism.MainNotions.ArcLiftingSetup.InFr W a num den f) (t : ℕ) :
    Formalism.MainNotions.ArcLiftingSetup.InFr W a num den (Formalism.MainNotions.ArcLiftingSetup.lE W t * f) := by
  obtain ⟨u, hu, hf⟩ := h
  refine ⟨((PD.p : ℕ) : LetA O n) ^ t * u, W.AΔ.mul_mem (W.AΔ.pow_mem (W.AΔ.natCast_mem _) t) hu, ?_⟩
  unfold Formalism.MainNotions.ArcLiftingSetup.lE
  rw [mul_left_comm, hf]
  simp only [map_mul, map_pow, map_natCast]
  ring

theorem secIn_lE {a : ZMod n} {e d : ℕ} {cond : (ℕ → ℤ) → (Fin d → O) → Prop} {F : Fin d → W.EE}
    (h : Formalism.MainNotions.ArcLiftingSetup.SecIn W a e cond F) (t : ℕ) :
    Formalism.MainNotions.ArcLiftingSetup.SecIn W a e cond fun k => Formalism.MainNotions.ArcLiftingSetup.lE W t * F k := by
  obtain ⟨I, g, c₀, α, hg, hF⟩ := h
  refine ⟨I, fun i => Formalism.MainNotions.ArcLiftingSetup.lE W t * g i, c₀, α, fun i => ⟨inFr_lE W (hg i).1 t, (hg i).2⟩,
    fun k => ?_⟩
  show Formalism.MainNotions.ArcLiftingSetup.lE W t * F k = _
  rw [hF k, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem arcHyp_secOfN [NeZero n] [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hR : Formalism.MainNotions.LiftingTheory.UniformizerRingClause W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W) (hH : Formalism.MainNotions.LiftingTheory.coreH W)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hmod : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    (hΔ : IsUnit ((W.DelF.card : ℕ) : O))
    (hSC : Formalism.MainNotions.UnusedSlot80.ArcC.ArcHyp W (Formalism.MainNotions.UnusedSlot80.ArcC.SecCrit W)) :
    Formalism.MainNotions.UnusedSlot80.ArcC.ArcHyp W (Formalism.MainNotions.UnusedSlot80.ArcC.SecOfN W) := by
  intro hCA h5p A hA c hc e hje hel T hT d b sol hb x hx
  have hc' : c - ((A.len c : ℕ) : ZMod n) ∈ A.cuts := ((hA.2.2.1 c hc).2.2).1
  have hΛx := Formalism.MainNotions.UnusedSlot80.ArcC.arc_down W hCA.2.1 hR T A hA
    (h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT)) (hmod T hT.1) hΔ _ hc' e x hx
  obtain ⟨f, hfr, hrep⟩ := secOfP W hinj hO2 hR hTr hH hCA h5p A hA _ e hje T hT.1 d b sol hb x hΛx
  exact ⟨f, ⟨hfr, (hSC hCA h5p A hA c hc e hje hel T hT d b sol hb x (A.σ PD.p) f hΛx hrep hfr).1 hx⟩,
    hrep⟩

theorem arcHyp_nOfSec [IsDomain O] (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hR : Formalism.MainNotions.LiftingTheory.UniformizerRingClause W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W) (hH : Formalism.MainNotions.LiftingTheory.coreH W)
    (hSC : Formalism.MainNotions.UnusedSlot80.ArcC.ArcHyp W (Formalism.MainNotions.UnusedSlot80.ArcC.SecCrit W)) :
    Formalism.MainNotions.UnusedSlot80.ArcC.ArcHyp W (Formalism.MainNotions.UnusedSlot80.ArcC.NOfSec W) := by
  intro hCA h5p A hA c hc e hje hel T hT d b sol hb f hf
  obtain ⟨hfr, κ, hsec⟩ := hf
  obtain ⟨x, hΛx, hrep⟩ := pOfSec W hO2 hR hTr hH hCA h5p A hA _ e hje T hT.1 d b sol hb f hfr
  refine ⟨x, ?_, hrep⟩
  have hrep0 : Formalism.MainNotions.ArcLiftingSetup.RepVV W T (c - ((A.len c : ℕ) : ZMod n)) e (A.M PD.p)
      (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e) b sol
      (Formalism.MainNotions.ArcLiftingSetup.lA W ^ 0 • x) fun k => Formalism.MainNotions.ArcLiftingSetup.lE W (A.σ PD.p) * f k := by
    rw [pow_zero, one_smul]; exact hrep
  refine (hSC hCA h5p A hA c hc e hje hel T hT d b sol hb x 0 _ hΛx hrep0
    (fun m => inFr_lE W (hfr m) _)).2 ⟨κ, ?_⟩
  have := secIn_lE W hsec (A.σ PD.p)
  convert this using 2 with k
  ring

end Formalism.MainNotions.UnusedSlot80.ArcF

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

theorem frameBasisL_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h : AdmArcA D HW F Cm) :
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL), CaseA K LL → 5 ≤ l →
      ArcC.ArcHyp ((HW l).W K 1 LL hG) (ArcC.FrameBasis ((HW l).W K 1 LL hG)) := by
  obtain ⟨h3, -, h5, h9, -, -, -, -⟩ := h
  intro l _ K LL hG hCA _
  have := neZero_finrank_max_unramified K
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [(D.loc l).PD_p]; exact hCA.2.1
  have hK := finrank_K0_eq_one_of_le_Kur hCA.1
  have hmod : ∀ T, IsCrys ((D.loc l).PD K) T.ρ → Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters ((HW l).W K 1 LL hG) T
      ((HW l).W K 1 LL hG).π₀ := fun T hT => ((h9 l K 1 LL hG T hT hs hp).2.2 hK).2
  exact ArcF.arcHyp_frameBasis _ (valRing_rec (D.loc l) LL) (h3 l K 1 LL hG) (h5 l K 1 LL hG) hmod

def SecCritL (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL), CaseA K LL → 5 ≤ l →
    ArcC.ArcHyp ((HW l).W K 1 LL hG) (ArcC.SecCrit ((HW l).W K 1 LL hG))

theorem ArcFrameL_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h : AdmArcA D HW F Cm) (hSC : SecCritL D HW) : ArcFrameL D HW := by
  have hFB := frameBasisL_of D HW F Cm h
  obtain ⟨-, -, h5, h9, hH, hTr, -, -⟩ := h
  intro l _ K LL hG hCA h5l
  have := neZero_finrank_max_unramified K
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [(D.loc l).PD_p]; exact hCA.2.1
  have hK := finrank_K0_eq_one_of_le_Kur hCA.1
  have hR := ring_condition_uniformizer_polynomial D HW F h9 l K LL hCA
  have hmod : ∀ T, IsCrys ((D.loc l).PD K) T.ρ → Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters ((HW l).W K 1 LL hG) T
      ((HW l).W K 1 LL hG).π₀ := fun T hT => ((h9 l K 1 LL hG T hT hs hp).2.2 hK).2
  have hc1 := Formalism.MainNotions.LiftingTheory.gen_one_crys ((HW l).W K 1 LL hG)
  have := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  have hΔ : IsUnit ((((HW l).W K 1 LL hG).DelF.card : ℕ) : ↥(OL LL)) :=
    cardΔ_of (W := (HW l).W K 1 LL hG) (not_isUnit_p ((HW l).W K 1 LL hG) (valRing_rec (D.loc l) LL))
      (card_DelF (W := (HW l).W K 1 LL hG) hs hp hK (h9 l K 1 LL hG _ hc1))
  have hV := valRing_rec (D.loc l) LL
  have hSCl := hSC l K LL hG hCA h5l
  refine ⟨hFB l K LL hG hCA h5l, ?_, ?_,
    ArcF.arcHyp_secOfN _ hV.1 hV.2.1 hR (hTr l K 1 LL hG) (hH l K 1 LL hG) (h5 l K 1 LL hG) hmod hΔ hSCl,
    ArcF.arcHyp_nOfSec _ hV.2.1 hR (hTr l K 1 LL hG) (hH l K 1 LL hG) hSCl, hSCl⟩
  · intro hCA' h5p A hA c _ e hje _ T hT d b sol hb
    exact ArcF.secOfP _ hV.1 hV.2.1 hR (hTr l K 1 LL hG) (hH l K 1 LL hG) hCA' h5p A hA _ e hje T hT.1
      d b sol hb
  · intro hCA' h5p A hA c _ e hje _ T hT d b sol hb
    exact ArcF.pOfSec _ hV.2.1 hR (hTr l K 1 LL hG) (hH l K 1 LL hG) hCA' h5p A hA _ e hje T hT.1
      d b sol hb

theorem arc_coordinates_of_membership (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hSC : SecCritL D HW) : ArcCoordinatesTheorem D HW F Cm := fun h =>
  arc_coordinates_of_frame D HW F Cm (ArcFrameL_of D HW F Cm h hSC) h

end Formalism.MainNotions.UnusedSlot80
