import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
import Formalism.LocalToGlobal.Columns.ChainTwKer
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertAtLeCongN
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff

noncomputable section
namespace GlobalTheory.Mem.Col2.TC.TwModel
open NumberField IsDedekindDomain _root_.Formalism.BasicNotions _root_.Formalism.L2.Col _root_.Formalism.L2.DIV

section
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

theorem scal_scl {n : ℕ} (q : ℕ) (e : ℕ → ℤ) {u : E} (h0 : u ≠ 0) (hu : P.valuation E u = 1) :
    LinearEquiv.smulOfNeZero E (Sp E n) u h0 ∈ stabL E n (LocE.sclLat P q n e) := by
  intro x
  rw [ciMem_sclLat, ciMem_sclLat]
  refine forall_congr' fun l => ?_
  rw [qth_intAt_iff, qth_intAt_iff]
  show P.valuation E (_ * (u * x l)) ≤ 1 ↔ _
  simp [hu]

theorem scal_std {n : ℕ} {u : E} (h0 : u ≠ 0) (hu : P.valuation E u = 1) :
    LinearEquiv.smulOfNeZero E (Sp E n) u h0 ∈ stabL E n (stdAt E n P) := by
  intro x
  rw [ciMem_stdAt, ciMem_stdAt]
  refine forall_congr' fun l => ?_
  rw [qth_intAt_iff, qth_intAt_iff]
  show P.valuation E (u * x l) ≤ 1 ↔ _
  simp [hu]

theorem scal_prX {n c kj q : ℕ} (hc : c = 0) {u : E} (h0 : u ≠ 0) (hu : P.valuation E u = 1) :
    LinearEquiv.smulOfNeZero E (Sp E n) u h0 ∈ Loc.prX (Loc.Cbe (LocE.JQ P q kj n c) 1) := by
  subst hc
  refine ⟨LinearEquiv.smulOfNeZero E (Sp E (n + 0)) u h0, ⟨mem_R1_zero _, ?_⟩, fun x => ?_⟩
  · show (MulAut.conj (1 : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0))⁻¹) _ ∈ LocE.JQ P q kj n 0
    rw [inv_one, map_one]
    exact ⟨scal_std P h0 hu, scal_scl P q _ h0 hu⟩
  · show u • Loc.inX E n 0 x = Loc.inX E n 0 (u • x)
    rw [map_smul]

theorem vq_lt : P.valuation E (qOf P : E) < 1 := by
  have : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _
  have h := (P.valuation_lt_one_iff_mem (K := E) _).2 this
  simpa using h

theorem q_ne : (qOf P : E) ≠ 0 := by
  have : qOf P ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast this

theorem v_one_add : P.valuation E (1 + (qOf P : E)) = 1 := by
  rw [Valuation.map_one_add_of_lt _ (vq_lt P)]

theorem scal_not {n r c : ℕ} (hn : 0 < n) (hc : 1 < c) (h0 : (1 + (qOf P : E)) ≠ 0) :
    (⟨LinearEquiv.smulOfNeZero E (Sp E n) _ h0, scal_std P h0 (v_one_add P)⟩ : GLint E n P) ∉ twK1H P n r c := by
  rintro ⟨-, -, -, h⟩
  have hw : (Pi.single ⟨n - 1, by omega⟩ 1 : Sp E n) ∈ LocE.sclLat P (qOf P) n (twistedLevelExponent n c) := by
    rw [ciMem_sclLat]
    intro l
    rw [qth_intAt_iff]
    by_cases e : l = ⟨n - 1, by omega⟩
    · subst e
      have : n - 1 + 1 = n := by omega
      simp [twistedLevelExponent, this]
    · simp [Pi.single_eq_of_ne e]
  have h1 := (ciMem_sclLat P (qOf P) _ _).1 (h _ hw) ⟨n - 1, by omega⟩
  rw [qth_intAt_iff] at h1
  have e : ((LinearEquiv.smulOfNeZero E (Sp E n) _ h0) (Pi.single ⟨n - 1, by omega⟩ 1 : Sp E n) - (Pi.single ⟨n - 1, by omega⟩ 1 : Sp E n) : Sp E n) ⟨n - 1, by omega⟩ = (qOf P : E) := by
    show (1 + (qOf P : E)) * (Pi.single ⟨n - 1, by omega⟩ 1 : Sp E n) ⟨n - 1, by omega⟩ - (Pi.single ⟨n - 1, by omega⟩ 1 : Sp E n) ⟨n - 1, by omega⟩ = _
    simp
  change P.valuation E (_ * ((LinearEquiv.smulOfNeZero E (Sp E n) _ h0) (Pi.single ⟨n - 1, by omega⟩ 1 : Sp E n) - (Pi.single ⟨n - 1, by omega⟩ 1 : Sp E n) : Sp E n) ⟨n - 1, by omega⟩) ≤ 1 at h1
  rw [e, map_mul, map_inv₀, map_zpow₀, zpow_natCast] at h1
  have hv0 : 0 < P.valuation E (qOf P : E) := zero_lt_iff.2 ((map_ne_zero _).2 (q_ne P))
  rw [inv_mul_le_iff₀ (pow_pos hv0 _), mul_one] at h1
  have := pow_lt_pow_right_of_lt_one₀ hv0 (vq_lt P) hc
  rw [pow_one] at this
  exact absurd h1 (not_le.2 this)

def trv {n : ℕ} {a b : Fin n} (h : a ≠ b) : Sp E n ≃ₗ[E] Sp E n where
  toFun x := x + Pi.single a (x b)
  invFun x := x - Pi.single a (x b)
  map_add' x y := by simp only [Pi.add_apply, Pi.single_add]; abel
  map_smul' c x := by
    funext l
    by_cases hl : l = a
    · subst hl; simp [mul_add]
    · simp [Pi.single_eq_of_ne hl]
  left_inv x := by simp [Pi.single_eq_of_ne h.symm]
  right_inv x := by simp [Pi.single_eq_of_ne h.symm]

theorem trv_apply {n : ℕ} {a b : Fin n} (h : a ≠ b) (x : Sp E n) : trv h x = x + Pi.single a (x b) := rfl

theorem single_mem {n : ℕ} {a b : Fin n} (e : ℕ → ℤ) (he : e a ≤ e b) {x : Sp E n}
    (hx : x ∈ LocE.sclLat P (qOf P) n e) : (Pi.single a (x b) : Sp E n) ∈ LocE.sclLat P (qOf P) n e := by
  rw [ciMem_sclLat] at hx ⊢
  intro l
  rw [qth_intAt_iff]
  by_cases hl : l = a
  · subst hl
    have h1 := (qth_intAt_iff P _).1 (hx b)
    rw [Pi.single_eq_same]
    have hq := q_ne P
    have e1 : ((qOf P : E) ^ e l)⁻¹ * x b = (qOf P : E) ^ (e b - e l).toNat * (((qOf P : E) ^ e b)⁻¹ * x b) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_sub₀ hq]
      have := zpow_ne_zero (e b) hq
      field_simp
    rw [e1, map_mul, map_pow]
    exact mul_le_one' (pow_le_one' (vq_lt P).le _) h1
  · simp [Pi.single_eq_of_ne hl]

theorem trv_scl {n : ℕ} {a b : Fin n} (h : a ≠ b) (e : ℕ → ℤ) (he : e a ≤ e b) :
    trv h ∈ stabL E n (LocE.sclLat P (qOf P) n e) := by
  intro x
  refine ⟨fun hx => ?_, fun hx => add_mem hx (single_mem P e he hx)⟩
  have := sub_mem hx (single_mem P e he hx)
  simpa [trv_apply, Pi.single_eq_of_ne h.symm] using this

theorem trv_prX {n c k rS r t : ℕ} (hc : c = 0) {a b : Fin n} (h : a ≠ b) (ha : a.1 = 0) (hk : 0 < k) (hr : r = k + 2 * rS + 1)
    (hb : r ≤ b.1) : trv h ∈ Loc.prX (Loc.Cbe (LocE.JGsym P (qOf P) k rS r t n c) 1) := by
  subst hc
  have hS : ∀ s, (trv h : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)) ∈ stabL E (n + 0) (LocE.flagS P (qOf P) k rS n 0 s) := fun s => by
    refine trv_scl P h _ ?_
    have := a.2
    have := b.2
    simp only [LocE.scE, LocE.fPos, symIdx, ha]
    split_ifs <;> omega
  refine ⟨(trv h : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)), ⟨mem_R1_zero _, ?_⟩, fun x => ?_⟩
  · show (MulAut.conj (1 : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0))⁻¹) _ ∈ LocE.JGsym P (qOf P) k rS r t n 0
    rw [inv_one, map_one]
    refine ⟨trv_scl P h _ ?_, fun s _ => hS s, fun s hs => ⟨hS s, ?_⟩⟩
    · have := a.2
      have := b.2
      simp only [LocE.scE]
      split_ifs <;> omega
    · have : LocE.bvecS E (qOf P) k rS n 0 s b = 0 := by
        simp only [LocE.bvecS, LocE.bvecG, Pi.smul_apply, Loc.eN]
        rw [if_neg, smul_zero]
        simp only [LocE.fIdx, symIdxInv]
        split_ifs <;> omega
      show LocE.bvecS E (qOf P) k rS n 0 s + Pi.single a (LocE.bvecS E (qOf P) k rS n 0 s b) - _ ∈ _
      rw [this]
      simp
  · have : ∀ y : Sp E n, Loc.inX E n 0 y = y := fun y => by
      funext l
      simp [Loc.inX, show l.1 < n from l.2]
    rw [this, this]

theorem trv_red {n : ℕ} {a b : Fin n} (h : a ≠ b) {x : Sp E n} (hx : x ∈ stdAt E n P) :
    redV P (trv h x) = (Matrix.transvection a b (1 : 𝓞 E ⧸ P.asIdeal)).mulVec (redV P x) := by
  rw [ciMem_stdAt] at hx
  funext l
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  by_cases hl : l = a
  · subst hl
    simp [redV, trv_apply, reduction_add (hx l) (hx b)]
  · simp [redV, trv_apply, Pi.single_eq_of_ne hl, Function.update_of_ne hl]
end

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (G : ChGlob X R.m) (m2 : ℕ)

theorem not_ok_Q (Λt) {P} (hP : P ∈ QE sel (mu : Chr X.F X.E X.K)) (hG : P ∉ Pr.vGs) :
    ¬ (twIdxTop Ch sel mu cst m2 Λt (twTt sel mu)).Ok Ch sel mu cst G m2 := by
  intro h
  have hm := h.hm
  have h0 : (1 + (qOf P : X.E)) ≠ 0 := by
    intro e; have := v_one_add P; rw [e] at this; simp at this
  have key := h.grpQ R.m (ChIdx.top _ m2 _ _ (by omega)) ⟨P, hP⟩
  apply scal_not P (n := R.N R.m) (r := R.r) (c := twTopDepth R) (by have := N_m_succ R; omega) (by unfold twTopDepth; omega) h0
  change twK1H P _ _ _ = (prCat (Pr := Pr) cst.sharp R.m P 1).subgroupOf _ at key
  rw [key, Subgroup.mem_subgroupOf]
  unfold prCat Jat
  rw [if_neg hG]
  exact scal_prX P (by unfold cOf; omega) h0 (v_one_add P)

theorem not_ok_G (Θt) (hs : cst.sharp = true) {w} (hw : w ∈ Pr.vGs) :
    ¬ (twIdxTop Ch sel mu cst m2 (twLt Ch) Θt).Ok Ch sel mu cst G m2 := by
  intro h
  have hm := h.hm
  have hN : R.N R.m = R.r + R.m * R.t + 1 := by
    have := R.two_le_m
    unfold Ranks.N Ranks.r
    rw [mul_add]; omega
  have hk := R.m_add_three_le_k
  have hr := r_eq_sym R
  let a : Fin (R.N R.m) := ⟨0, by omega⟩
  let b : Fin (R.N R.m) := ⟨R.r + R.m * R.t, by omega⟩
  have hab : a ≠ b := fun e => by have := congrArg Fin.val e; simp only [a, b] at this; omega
  let M : GL (Fin (R.N R.m)) (𝓞 X.E ⧸ w.asIdeal) :=
    ⟨Matrix.transvection a b 1, Matrix.transvection a b (-1), by rw [Matrix.transvection_mul_transvection_same _ _ hab]; simp,
      by rw [Matrix.transvection_mul_transvection_same _ _ hab]; simp⟩
  have key := (h.grpG R.m (ChIdx.top _ m2 _ _ (by omega)) ⟨w, hw⟩ M).2 ⟨trv hab, by
    show trv hab ∈ prCat (Pr := Pr) cst.sharp R.m w 1
    unfold prCat Jat
    rw [if_pos hw, hs, if_pos rfl]
    exact trv_prX w (by unfold cOf; omega) hab rfl (by omega) hr (by simp [b]), fun x hx => trv_red w hab hx⟩
  change M ∈ (colLevSym Ch R.m ⟨w, hw⟩).H at key
  rw [colLevSym_top_H Ch le_rfl] at key
  have h2 := key.2 a b rfl
  haveI := Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top
  simp [M, Matrix.transvection, Matrix.one_apply_ne hab] at h2

theorem not_ok_of_idx_top {B : Base} {Y : PreX B.toPre} (I : TC B Y) {a : I.ι}
    (ht : I.idx a = twIdxTop I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 2) (twLt I.Ch) (twTt I.sel (I.tup a))) : ¬ I.Ok := by
  intro h
  have hP := (GlobalTheory.BasePrimes.primes_ok B Y).1
  have hc : 0 < ((B.primes Y).vG 0).card := by
    rw [hP.vG_card, B.fields_f]
    unfold Ranks.f Ranks.n
    positivity
  obtain ⟨w, hw⟩ := Finset.card_pos.1 hc
  have hw' : w ∈ (B.primes Y).vGs := by
    classical
    unfold Primes.vGs
    convert Finset.mem_union_left _ hw
  have h1 := h.idx_ok a
  rw [ht] at h1
  exact not_ok_G _ _ _ _ _ _ _ (h.sharp a) hw' h1

end GlobalTheory.Mem.Col2.TC.TwModel

section Inhab

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.TC.TwModel

attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem exists_deep : ∃ (B : Base) (X : PreX B.toPre) (I : TC B X), StagesInhab.HasLetters B.toPre ∧ I.Ok ∧ TC.Pins B X ∧
    I.Deep ∧ ∀ a, (I.cst a).A = B.R.m := by
  classical
  obtain ⟨P, X, f, hL, hX, hsp, hdu, p1, p2⟩ := TrueColsTest.exists_pre
  obtain ⟨M, hM, -, -, m1, m2, -⟩ := FrameVal.frame_values P.R P.host _ f fun j τ => (P.hc τ).e_int j
  obtain ⟨α, hα, gα⟩ := @DatHecke.exists_gen M hM
  choose r hr using fun q : ℕ => IsAlgClosed.exists_pow_nat_eq (q : ℂ) (n := 2) two_pos
  obtain ⟨Y, hY, gY⟩ := InEx.exists_holds (2 * P.R.m) ({1, f.del, f.del'} : Set (Formalism.L2.Host.HChar P.host.E))
  obtain ⟨B, rfl, -, -, h2⟩ := BaseExt.exists_base P ∅ ∅
    (insert α (Y ∪ Finset.univ.image fun k => r (P.host.g k))) (by simp) (by simp)
    (fun z hz => by
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hα
      rcases Finset.mem_union.1 hz with h | h
      · exact hY z h
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 h
        exact IsAlgebraic.of_pow two_pos (by rw [hr]; exact isAlgebraic_natCast _))
  have i1 := gα B.LL B.embLL (h2 _ (Finset.mem_insert_self _ _))
  have hf : ({1, f.del, f.del'} : Set (Formalism.L2.Host.HChar B.host.E)).Finite := Set.toFinite _
  have ht : ∀ ξ ∈ ({1, f.del, f.del'} : Set (Formalism.L2.Host.HChar B.host.E)), Chr.IsTwist B.host (InEx.avoid B.toPre) ξ :=
    fun ξ hξ => InEx.isTwist_of_mem_set B f (Top.TwDat.untw B ∅) ξ (.inl hξ)
  obtain ⟨sel, hsel⟩ := Formalism.L2.Col.exists_sel B.fields
  obtain ⟨J, hJ⟩ := exists_ambIn_ok B.host
  obtain ⟨I, a1, -, -, -, -, -, a7⟩ := InEx.exists_colIn B X f hX hsp hdu (InEx.avoid B.toPre)
    (fun u => ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Exists.intro u rfl))))), B.T_ne_pde u⟩)
    (fun i => ⟨Or.inr (Or.inl (Exists.intro i rfl)), (B.host.pde_ne_g i).1.symm, (B.host.pde_ne_g i).2.symm⟩)
    (fun _ hp h => InEx.mem_avoid_of_dvd _ hp h)
    _ hf (.inl rfl) (.inr (.inl rfl)) (.inr (.inr rfl)) ht
    (fun ξ hξ => gY hf B.LL B.embLL
      (fun z hz => h2 z (Finset.mem_insert_of_mem (Finset.mem_union_left _ hz))) ξ hξ (ht ξ hξ).1)
    (fun j => InEx.valuesIn_of (m1 j) _ i1) (InEx.valuesIn_of m2 _ i1) (fun i => by
      obtain ⟨s, hs⟩ := h2 _ (Finset.mem_insert_of_mem
        (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
      exact ⟨s, B.embLL.injective (by rw [map_pow, hs, hr, map_natCast])⟩) sel hsel J hJ
  exact ⟨B, X, I, hL, a1, ⟨p1, p2⟩, fun a P hP => ((a7 a).2.2.2 P hP).ge, fun a => (a7 a).2.1⟩

theorem Q_star_nonempty {B : Base} {X : PreX B.toPre} {I : TC B X} (h : I.Ok) : (I.Q I.muStar).Nonempty := by
  classical
  obtain ⟨w, hw, hw'⟩ := Ideal.exists_le_maximal (Ideal.span {(B.host.pde : 𝓞 B.host.E)}) (by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have h1 := hu.map (Algebra.norm ℤ)
    rw [← map_natCast (algebraMap ℤ (𝓞 B.host.E)), Algebra.norm_algebraMap, isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq] at h1
    exact B.host.pde_prime.ne_one (by simpa using h1))
  have hm : (B.host.pde : 𝓞 B.host.E) ∈ w := hw' (Ideal.mem_span_singleton_self _)
  have hb : w ≠ ⊥ := by
    rintro rfl
    exact B.host.pde_prime.ne_zero (by simpa using hm)
  have hP : ¬ (I.xi I.muStar).UnrAt ⟨w, hw.isPrime, hb⟩ := fun hu => by
    rw [h.xi_star] at hu
    have h3 := (I.C.isDel.ine ⟨w, hw.isPrime, hb⟩ hm 1).1 fun x hx => by rw [pow_one]; exact hu x hx
    omega
  have hf := GlobalTheory.OpenChrRam.qprime_finite B.fields.F B.fields.E B.fields.K (I.tup I.muStar : Chr B.fields.F B.fields.E B.fields.K)
    (I.tup I.muStar).2.1.1.1.1.2
  refine ⟨I.sel ((⟨w, hw.isPrime, hb⟩ : HeightOneSpectrum (𝓞 B.fields.E)).under (𝓞 B.fields.F)), ?_⟩
  show _ ∈ QE _ _
  rw [QE, dif_pos hf]
  exact Finset.mem_image_of_mem _ (hf.mem_toFinset.2 ((GlobalTheory.Mem.ReadTwist.mem_qprime_iff (h.xi_reads I.muStar) _).2 ⟨_, rfl, hP⟩))

theorem exists_isTw : ∃ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws), I.Ok ∧ I.IsTw ∧ TC.Pins B X ∧ I.Law0 l ∧
    (I.Q I.muStar).Nonempty ∧ Nonempty (TC.Later B (I.cols l)) := by
  obtain ⟨B, X, I, hL, h, hP, hD, -⟩ := exists_deep
  have hk := canon_ok h hD
  exact ⟨B, X, I.canon, TrueColsTest.laws hk, hk, I.canon_isTw, hP, TrueColsTest.law0 hk _, Q_star_nonempty hk,
    TrueColsTest.later _ hL⟩

theorem exists_ok_not_isTw : ∃ (B : Base) (X : PreX B.toPre) (I : TC B X), I.Ok ∧ I.Deep ∧ ¬ I.IsTw := by
  obtain ⟨B, X, I, -, h, -, hD, hA⟩ := exists_deep
  refine ⟨B, X, I, h, hD, fun ht => ?_⟩
  have e := hA I.mu0
  rw [ht.cst_eq] at e
  exact Nat.succ_ne_self _ e

theorem topDep_eq {B : Base} {X : PreX B.toPre} {I : TC B X} (ht : I.IsTw) (a : I.ι) :
    topDep B.R (I.cst a).M + 1 = twTopDepth B.R := by
  rw [ht.cst_eq, topDep_succ]
  show max _ (2 * B.R.m + 2 * B.R.m) = _
  unfold twTopDepth
  omega

theorem kerEquivC_of_isTw {B : Base} {X : PreX B.toPre} {I : TC B X} (ht : I.IsTw) (h : I.Ok)
    (W : Wts B.fields (B.primes X).Word B.R) (a : I.ι) (u : B.Word)
    (hOk : ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh W I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)))
    (b : (I.idx a).β (B.R.m - 2 + 1))
    (hY : YbHyp (R := B.R) I.sel (I.tup a) (I.cst a) (I.idx a) u (B.R.m - 2) b) :
    KerEquivC W I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u (B.R.m - 2) b hY (rPsymF I.Ch) := by
  have hD := ht.deep
  have e := isTw_iff_canon_eq.1 ht
  revert hOk b hY
  rw [ht.idx_eq a, ht.cst_eq a]
  intro hOk b hY
  exact kerEquivC_tw W I.Ch I.sel (I.tup a) I.A u (base_fields_primes_ok B X).1 (base_fields_primes_ok B X).2.1 h.ch_ok
    (qOf_mod_four B X) I.glob h.ch_tied h.weil (val_of_ok h) h.hm (Q_notMem_of_ok h a) (fun P _ => degOne_of_ok h a P)
    (root_of_ok h hD a) (fun P _ => sqrt_of_ok h a P) (fun P _ => (h.idx_ok a).xiUnitAtPrime P) h.sel_ok h.g_mem (h.T_mem u) hOk b hY

end GlobalTheory.Mem.Col2.TC.TwModel

end Inhab

end
