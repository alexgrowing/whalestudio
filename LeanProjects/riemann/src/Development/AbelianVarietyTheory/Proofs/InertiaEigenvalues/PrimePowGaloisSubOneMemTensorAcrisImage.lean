import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSectionTrivialisesInvertPrimeTensorStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalTaylor

section Lemmas

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem actB_smul {G : Type} [Group G] [TopologicalSpace G] (s : G →* GQ l)
    (T : LocLat G ℚ_[l] K O) (g : G) (β : OB l O) (v : TW (OB l O) T) :
    actB s T g (β • v) = galOB O (s g) β • actB s T g v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [actB, TWact, TensorProduct.smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
      smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

theorem taylor_iC (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) (f : ZMod a → S O K e)
    (r : ℕ) : ∃ M₀, ∀ M ≥ M₀, (l : OCr l O) ^ r ∣ galOCr O g (ϖ.iC t K f) -
      ∑ i ∈ Finset.range M, ϖ.muDiv a O g i *
        ϖ.iC t K (fun τ => ⟨descN K i (f τ), descN_mem_S e i (f τ).2⟩) := by
  choose N hN using fun τ => ϖ.taylor_S a O K g (f τ) r
  refine ⟨Finset.univ.sup N, fun M hM => ?_⟩
  choose z hz using fun τ => hN τ M ((Finset.le_sup (Finset.mem_univ τ)).trans hM)
  refine ⟨∑ τ, idem (constC t) τ * z τ, ?_⟩
  simp only [PiSys.iC, glue_apply, map_sum, map_mul, galOCr_idem, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [mul_left_comm, ← hz τ, mul_sub, Finset.mul_sum]
  simp only [mul_left_comm (idem (constC t) τ)]

theorem toBcris_of_mem (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (P : PhiMod O K l e a ι) {m : Vec K a ι}
    (h : m ∈ P.MM) (h' : m ∈ P.MMl) (k : ι) :
    toBcris t ϖ P ⟨m, h'⟩ k = toOB l O (toCris t ϖ P ⟨m, h⟩ k) := by
  rw [toBcris_apply, toCris_apply, ← ϖ.iB_of_mem t K]
  rfl

theorem descConn_xiExt (P : PhiMod O K l e a ι) (i : ℕ) (w : Vec K a ι) :
    Polynomial.aeval P.conn (descPochhammer K i) (P.xiExt w) =
      P.xiExt (fun τ j => descN K i (w τ j)) := by
  induction i generalizing w with
  | zero => simp [descN]
  | succ i ih =>
    rw [descPochhammer_succ_right, map_mul, Module.End.mul_apply, map_sub, Polynomial.aeval_X, map_natCast,
      LinearMap.sub_apply, Module.End.natCast_apply, PhiMod.conn_xiExt, ← map_nsmul, ← map_sub, ih]
    congr 1
    funext τ j
    simp only [descN, descPochhammer_succ_right, map_mul, Module.End.mul_apply, map_sub, Polynomial.aeval_X,
      map_natCast, LinearMap.sub_apply, Module.End.natCast_apply, Pi.sub_apply, Pi.smul_apply]
    rfl

theorem aeval_descPochhammer_mem {V R : Type} [AddCommGroup V] [Module K V] [CommRing R] [Module R V]
    (W : Submodule R V) (φ : Module.End K V) (hφ : ∀ m ∈ W, φ m ∈ W) (n : ℕ) :
    ∀ m ∈ W, Polynomial.aeval φ (descPochhammer K n) m ∈ W := by
  induction n with
  | zero => intro m hm; simpa using hm
  | succ n ih =>
    intro m hm
    rw [descPochhammer_succ_right, map_mul, Module.End.mul_apply, map_sub, Polynomial.aeval_X, map_natCast,
      LinearMap.sub_apply, Module.End.natCast_apply]
    exact ih _ (sub_mem (hφ m hm) (nsmul_mem hm n))

theorem descConn_mem (P : PhiMod O K l e a ι) (hP : ∀ m ∈ P.MM, P.conn m ∈ P.MM) {v : Vec K a ι} {c : ℕ}
    (hv : (l : K) ^ c • P.conn v ∈ P.MM) (i : ℕ) :
    (l : K) ^ c • Polynomial.aeval P.conn (descPochhammer K (i + 1)) v ∈ P.MM := by
  rw [descPochhammer_succ_left, mul_comm, map_mul, Module.End.mul_apply, Polynomial.aeval_X, ← LinearMap.map_smul,
    Polynomial.aeval_comp, map_sub, Polynomial.aeval_X, map_one]
  exact aeval_descPochhammer_mem P.MM (P.conn - 1) (fun m hm => sub_mem (hP m hm) hm) i _ hv

theorem pow_smul_mem_S {f : K⟦X⟧} (hf : f ∈ invL l (S O K e)) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : K) ^ n • f ∈ S O K e := by
  obtain ⟨m, hm⟩ := mem_away.1 hf
  refine ⟨m, fun n hn => ?_⟩
  have e1 : (l : K) ^ n • f = (l : K⟦X⟧) ^ (n - m) * ((l : K⟦X⟧) ^ m * f) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hn, smul_eq_C_mul, map_pow, map_natCast]
  rw [e1]
  exact mul_mem (pow_mem (natCast_mem _ l) _) (by simpa using hm)

theorem pow_smul_mem_S_fin {κ : Type} [Fintype κ] {f : κ → K⟦X⟧} (hf : ∀ p, f p ∈ invL l (S O K e)) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ p, (l : K) ^ n • f p ∈ S O K e := by
  choose N hN using fun p => pow_smul_mem_S (hf p)
  exact ⟨Finset.univ.sup N, fun n hn p => hN p n ((Finset.le_sup (Finset.mem_univ p)).trans hn)⟩

theorem exists_pow_smul_mem_MM (P : PhiMod O K l e a ι) {x : Vec K a ι} (hx : x ∈ P.MMl) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : K) ^ n • x ∈ P.MM := by
  obtain ⟨n₀, h⟩ := pow_smul_mem_S_fin (κ := ZMod a × ι) (f := fun p => (P.mxInv p.1 *ᵥ x p.1) p.2)
    (fun p => mem_vecs.1 (P.mem_extc_iff.1 (mem_tot.1 hx p.1)) p.2)
  refine ⟨n₀, fun n hn => mem_tot.2 fun τ => P.mem_extc_iff.2 (mem_vecs.2 fun j => ?_)⟩
  rw [Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply]
  exact h n hn (τ, j)

theorem exists_pow_smul_mem_Mext (P : PhiMod O K l e a ι) {w : Vec K a ι}
    (hw : w ∈ P.Mext (invL l (S O K e))) : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ τ j, (l : K) ^ n • w τ j ∈ S O K e := by
  obtain ⟨n₀, h⟩ := pow_smul_mem_S_fin (κ := ZMod a × ι) (f := fun p => w p.1 p.2)
    (fun p => mem_vecs.1 (mem_tot.1 hw p.1) p.2)
  exact ⟨n₀, fun n hn τ j => h n hn (τ, j)⟩

theorem toBcris_xiExt (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (P : PhiMod O K l e a ι) {W : Vec K a ι}
    (hW : ∀ τ j, W τ j ∈ S O K e) (h : P.xiExt W ∈ P.MMl)
    (hx : ∀ j, P.xi (fun _ => Pi.single j 1) ∈ P.MMl) (k : ι) :
    toBcris t ϖ P ⟨P.xiExt W, h⟩ k =
      ∑ j, toOB l O (ϖ.iC t K fun τ => ⟨W τ j, hW τ j⟩) * toBcris t ϖ P ⟨_, hx j⟩ k := by
  have hsum : (⟨P.xiExt W, h⟩ : P.MMl) = ∑ j, (⟨(fun τ => W τ j) • P.xi (fun _ => Pi.single j 1),
      P.smul_tot_mem_ext (fun τ => le_away _ _ (hW τ j)) (hx j)⟩ : P.MMl) := by
    apply Subtype.ext
    show P.xiExt W = _
    rw [Submodule.coe_sum]
    conv_lhs => rw [eq_sum_bas W, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show _ = (fun τ => W τ j) • P.xi (fun _ => Pi.single j 1)
    rw [PhiMod.xiExt_smul_tot, PhiMod.xi_apply, cst_single]
  rw [hsum, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toBcris_apply, toBcris_apply, ← ϖ.iB_of_mem t K, ← map_mul]
  congr 1
  funext τ
  apply Subtype.ext
  simp [coordL, Matrix.mulVec_smul]

end Lemmas

theorem lpow_galDiff_eq_jB_toOB : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (σ : D.MMl) (c : ℕ), (l : K) ^ c • D.conn σ.1 ∈ D.MM → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∃ z : ι → OCr l O, (l : O) ^ c • (actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ)) - R.jB (toBcris t ϖ D.toPhiMod σ)) = R.jB fun i => toOB l O (z i) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ _ ι _ _ η H D T R σ c hc g hg
  haveI : FiniteDimensional ℚ_[l] K := TameDescentExponentData.finite (K := K) (l := l) (e := e) (a := a)
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  let g' : ↥(GK (ϖ.field a)) := ⟨sQ l g, hg⟩
  have hxi := (GlobalTheory.T.breuilKisin_section_trivialises_invertPrime_tensor O K l e a ι D.toPhiMod).2
  have nsm : ∀ (n : ℕ) (v : Vec K a ι), (l : K) ^ n • v = (l ^ n) • v := fun n v => by
    rw [← Nat.cast_smul_eq_nsmul K, Nat.cast_pow]

  have hxj : ∀ j : ι, D.toPhiMod.xi (fun _ => Pi.single j 1) ∈ D.toPhiMod.MMl := fun j => by
    rw [PhiMod.xi_apply, cst_single, hxi]
    exact mem_tot.2 fun τ => mem_vecs.2 fun i => by
      simp only [bas, Pi.single_apply]
      split_ifs <;> simp
  let X : ι → ι → OB l O := fun j => toBcris t ϖ D.toPhiMod ⟨_, hxj j⟩
  have hv : ∀ j, actB (sQ l) T g (R.jB (X j)) = R.jB (X j) := fun j => R.horiz g hg _ (hxj j)

  obtain ⟨w, hw⟩ := D.toPhiMod.xiExt.surjective σ.1
  have hwM : w ∈ D.toPhiMod.Mext (invL l (S O K e)) := (hxi w).1 (hw ▸ σ.2)
  obtain ⟨n₁, hn₁⟩ := exists_pow_smul_mem_Mext D.toPhiMod hwM
  choose m₀ hm₀ using fun j => exists_pow_smul_mem_MM D.toPhiMod (hxj j)
  set n₂ := Finset.univ.sup m₀ with hn₂
  have hX2 : ∀ j, (l : K) ^ n₂ • D.toPhiMod.xi (fun _ => Pi.single j 1) ∈ D.toPhiMod.MM := fun j =>
    hm₀ j n₂ (Finset.le_sup (Finset.mem_univ j))
  set W : Vec K a ι := (l : K) ^ n₁ • w with hWdef
  have hWS : ∀ τ j, W τ j ∈ S O K e := hn₁ n₁ le_rfl
  have hWσ : D.toPhiMod.xiExt W = (l : K) ^ n₁ • σ.1 := by rw [hWdef, map_smul, hw]
  have hWM : D.toPhiMod.xiExt W ∈ D.toPhiMod.MMl := by rw [hWσ, nsm]; exact nsmul_mem σ.2 _

  let Wi : ℕ → Vec K a ι := fun i τ j => descN K (i + 1) (W τ j)
  have hWi : ∀ i τ j, Wi i τ j ∈ S O K e := fun i τ j => descN_mem_S e (i + 1) (hWS τ j)
  have hWiM : ∀ i, D.toPhiMod.xiExt (Wi i) ∈ D.toPhiMod.MMl := fun i =>
    (hxi _).2 (mem_tot.2 fun τ => mem_vecs.2 fun j => le_away _ _ (hWi i τ j))
  let Pi' : ℕ → Vec K a ι := fun i => Polynomial.aeval D.toPhiMod.conn (descPochhammer K (i + 1)) σ.1
  have hPi : ∀ i, (l : K) ^ c • Pi' i ∈ D.toPhiMod.MM := fun i =>
    descConn_mem D.toPhiMod (fun m hm => D.conn_mem_MM hm) hc i
  have hxiWi : ∀ i, D.toPhiMod.xiExt (Wi i) = (l : K) ^ n₁ • Pi' i := fun i => by
    rw [← descConn_xiExt, hWσ, map_smul]
  let y : ℕ → ι → OCr l O := fun i => toCris t ϖ D.toPhiMod ⟨_, hPi i⟩
  let u : ι → ι → OCr l O := fun j => toCris t ϖ D.toPhiMod ⟨_, hX2 j⟩
  let Y : ℕ → ι → OB l O := fun i => toBcris t ϖ D.toPhiMod ⟨_, hWiM i⟩
  have hF : ∀ i k, (l : OB l O) ^ c * Y i k = (l : OB l O) ^ n₁ * toOB l O (y i k) := fun i k => by
    have hsub : (l ^ c) • (⟨D.toPhiMod.xiExt (Wi i), hWiM i⟩ : D.toPhiMod.MMl) =
        (l ^ n₁) • (⟨(l : K) ^ c • Pi' i, D.toPhiMod.ext_mono (le_away _ _) (hPi i)⟩ : D.toPhiMod.MMl) := by
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_nsmul, hxiWi]
      rw [← nsm, ← nsm, smul_smul, smul_smul, mul_comm]
    have := congrArg (fun x => toBcris t ϖ D.toPhiMod x k) hsub
    simp only [map_nsmul, Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow] at this
    rw [this, toBcris_of_mem t ϖ D.toPhiMod (hPi i)]
  have hG : ∀ j k, (l : OB l O) ^ n₂ * X j k = toOB l O (u j k) := fun j k => by
    have hsub : (l ^ n₂) • (⟨_, hxj j⟩ : D.toPhiMod.MMl) =
        (⟨(l : K) ^ n₂ • D.toPhiMod.xi (fun _ => Pi.single j 1), D.toPhiMod.ext_mono (le_away _ _) (hX2 j)⟩ : D.toPhiMod.MMl) := by
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_nsmul]
      rw [← nsm]
    have := congrArg (fun x => toBcris t ϖ D.toPhiMod x k) hsub
    simp only [map_nsmul, Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow] at this
    rw [this, toBcris_of_mem t ϖ D.toPhiMod (hX2 j)]

  let β : ι → OCr l O := fun j => ϖ.iC t K fun τ => ⟨W τ j, hWS τ j⟩
  have hA : ∀ k, toBcris t ϖ D.toPhiMod σ k * (l : OB l O) ^ n₁ = ∑ j, toOB l O (β j) * X j k := fun k => by
    have hsub : (l ^ n₁) • σ = (⟨D.toPhiMod.xiExt W, hWM⟩ : D.toPhiMod.MMl) := by
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_nsmul, hWσ]
      rw [← nsm]
    have := congrArg (fun x => toBcris t ϖ D.toPhiMod x k) hsub
    simp only [map_nsmul, Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow] at this
    rw [mul_comm, this, toBcris_xiExt t ϖ D.toPhiMod hWS hWM hxj k]
  have hb : (l ^ n₁) • R.jB (toBcris t ϖ D.toPhiMod σ) = ∑ j, toOB l O (β j) • R.jB (X j) := by
    rw [← map_nsmul]
    simp only [← LinearEquiv.map_smul, ← map_sum]
    congr 1
    funext k
    simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow, Finset.sum_apply, smul_eq_mul]
    rw [mul_comm, hA k]
  have hgb : (l ^ n₁) • (actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ)) - R.jB (toBcris t ϖ D.toPhiMod σ)) =
      ∑ j, toOB l O (galOCr O (sQ l g) (β j) - β j) • R.jB (X j) := by
    rw [nsmul_sub, ← map_nsmul, hb, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [actB_smul, hv, galOB_toOB, map_sub, sub_smul]

  choose M₀ hM₀ using fun j => taylor_iC t ϖ g' (fun τ => ⟨W τ j, hWS τ j⟩) (n₁ + n₂)
  set M := Finset.univ.sup M₀ with hM
  have hε : ∀ j, ∃ ε : OCr l O, galOCr O (sQ l g) (β j) - β j = ∑ i ∈ Finset.range M,
      ϖ.muDiv a O g' (i + 1) * ϖ.iC t K (fun τ => ⟨Wi i τ j, hWi i τ j⟩) + (l : OCr l O) ^ (n₁ + n₂) * ε := by
    intro j
    obtain ⟨ε, hε⟩ := hM₀ j (M + 1) ((Finset.le_sup (Finset.mem_univ j)).trans (Nat.le_succ _))
    refine ⟨ε, ?_⟩
    rw [Finset.sum_range_succ'] at hε
    have h0 : ϖ.muDiv a O g' 0 * ϖ.iC t K (fun τ => ⟨descN K 0 (W τ j), descN_mem_S e 0 (hWS τ j)⟩) = β j := by
      have h1 : ϖ.muDiv a O g' 0 = 1 := by
        simp [PiSys.muDiv, dpow_zero, Algebra.TensorProduct.one_def]
      rw [h1, one_mul]
      congr 1
      funext τ
      exact Subtype.ext (by simp [descN])
    rw [h0] at hε
    linear_combination hε
  choose ε hε using hε
  let z : ι → OCr l O := fun k => ∑ i ∈ Finset.range M, ϖ.muDiv a O g' (i + 1) * y i k +
    (l : OCr l O) ^ c * ∑ j, ε j * u j k
  refine ⟨z, ?_⟩
  have cancel : ∀ (N : ℕ) (A B : TW (OB l O) T), (l ^ N) • A = (l ^ N) • B → A = B := by
    intro N A B h
    rw [← Nat.cast_smul_eq_nsmul (OB l O), ← Nat.cast_smul_eq_nsmul (OB l O), Nat.cast_pow] at h
    exact ((isUnit_l_OB (l := l) (O := O)).pow N).smul_left_cancel.1 h
  have key : ∀ k, (l : OB l O) ^ n₂ * (l : OB l O) ^ c *
      ∑ j, toOB l O (galOCr O (sQ l g) (β j) - β j) * X j k =
      (l : OB l O) ^ (n₁ + n₂) * toOB l O (z k) := fun k => by
    have hstar : ∑ j, toOB l O (galOCr O (sQ l g) (β j) - β j) * X j k =
        ∑ i ∈ Finset.range M, toOB l O (ϖ.muDiv a O g' (i + 1)) * Y i k +
          (l : OB l O) ^ (n₁ + n₂) * ∑ j, toOB l O (ε j) * X j k := by
      simp only [hε, map_add, map_sum, map_mul, map_pow, map_natCast, add_mul, Finset.sum_add_distrib,
        Finset.sum_mul]
      congr 1
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show Y i k = _ from toBcris_xiExt t ϖ D.toPhiMod (hWi i) (hWiM i) hxj k, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    have hF' : (∑ i ∈ Finset.range M, toOB l O (ϖ.muDiv a O g' (i + 1)) * Y i k) * (l : OB l O) ^ c =
        (l : OB l O) ^ n₁ * ∑ i ∈ Finset.range M, toOB l O (ϖ.muDiv a O g' (i + 1)) * toOB l O (y i k) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      linear_combination toOB l O (ϖ.muDiv a O g' (i + 1)) * hF i k
    have hG' : (∑ j, toOB l O (ε j) * X j k) * (l : OB l O) ^ n₂ =
        ∑ j, toOB l O (ε j) * toOB l O (u j k) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      linear_combination toOB l O (ε j) * hG j k
    have hz : toOB l O (z k) = ∑ i ∈ Finset.range M, toOB l O (ϖ.muDiv a O g' (i + 1)) * toOB l O (y i k) +
        (l : OB l O) ^ c * ∑ j, toOB l O (ε j) * toOB l O (u j k) := by
      simp only [z, map_add, map_sum, map_mul, map_pow, map_natCast]
    rw [hstar, hz]
    linear_combination (l : OB l O) ^ n₂ * hF' + (l : OB l O) ^ (n₁ + n₂) * (l : OB l O) ^ c * hG'
  apply cancel (n₁ + n₂)
  have e1 : (l : O) ^ c • (actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ)) - R.jB (toBcris t ϖ D.toPhiMod σ)) =
      (l ^ c) • (actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ)) - R.jB (toBcris t ϖ D.toPhiMod σ)) := by
    rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
  rw [e1, smul_smul, show l ^ (n₁ + n₂) * l ^ c = (l ^ n₂ * l ^ c) * l ^ n₁ by ring, ← smul_smul, hgb]
  have eL : (l ^ n₂ * l ^ c) • ∑ j, toOB l O (galOCr O (sQ l g) (β j) - β j) • R.jB (X j) =
      R.jB ((l ^ n₂ * l ^ c) • ∑ j, toOB l O (galOCr O (sQ l g) (β j) - β j) • X j) := by
    rw [map_nsmul, map_sum]
    simp only [LinearEquiv.map_smul]
  have eR : (l ^ (n₁ + n₂)) • R.jB (fun i => toOB l O (z i)) =
      R.jB ((l ^ (n₁ + n₂)) • fun i => toOB l O (z i)) := (map_nsmul _ _ _).symm
  rw [eL, eR]
  congr 1
  funext k
  simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow, Nat.cast_mul, Finset.sum_apply, smul_eq_mul]
  linear_combination key k

end GlobalTheory.GalTaylor
