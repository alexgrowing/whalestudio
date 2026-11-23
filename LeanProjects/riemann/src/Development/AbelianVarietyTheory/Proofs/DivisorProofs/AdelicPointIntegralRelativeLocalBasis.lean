import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamGApply
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedStdLatticeLatticeComparisonRational
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocBasisInt

open Matrix

theorem norm_natCast_lt_one (l : ℕ) [Fact l.Prime] : ‖(l : PadicAlgCl l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem norm_natCast_eq_one (l : ℕ) [Fact l.Prime] {s : ℕ} (hs : ¬ l ∣ s) : ‖(s : PadicAlgCl l)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hs)

theorem norm_le_one_of_cols {C : Type} [NormedField C] [IsUltrametricDist C] {n : ℕ} (U : Matrix (Fin n) (Fin n) C) (p : C)
    (hp : ‖p‖ < 1) (h : ∀ b, ∃ T : Fin n → C, (∀ c, ‖T c‖ ≤ 1) ∧ ∀ a, ‖U a b - p * ∑ c, U a c * T c‖ ≤ 1) (a b : Fin n) :
    ‖U a b‖ ≤ 1 := by
  haveI : Nonempty (Fin n × Fin n) := ⟨(a, b)⟩
  obtain ⟨⟨a₀, b₀⟩, hmax⟩ := Finite.exists_max fun q : Fin n × Fin n => ‖U q.1 q.2‖
  refine (hmax (a, b)).trans ?_
  obtain ⟨T, hT, hU⟩ := h b₀
  by_contra hm
  have hm : 1 < ‖U a₀ b₀‖ := not_le.1 hm
  have h1 : ‖∑ c, U a₀ c * T c‖ ≤ ‖U a₀ b₀‖ :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun c _ => by
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hT c)).trans (hmax (a₀, c))
  have h2 : ‖p * ∑ c, U a₀ c * T c‖ < ‖U a₀ b₀‖ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans_lt (mul_lt_of_lt_one_left (one_pos.trans hm) hp)
  have h3 := IsUltrametricDist.norm_add_le_max (U a₀ b₀ - p * ∑ c, U a₀ c * T c) (p * ∑ c, U a₀ c * T c)
  rw [sub_add_cancel] at h3
  exact absurd h3 (not_le.2 (max_lt ((hU a₀).trans_lt hm) h2))

theorem exists_col {A E : Type} [CommRing A] [CommRing E] (j : E →+* A) (S : Subring A) {n : ℕ}
    (happ : ∀ M : ℕ, 0 < M → ∀ z : A, ∃ (e : E) (s : A), s ∈ S ∧ z = j e + (M : A) * s)
    (Y Yi : Matrix (Fin n) (Fin n) A) (hY : Yi * Y = 1) {N : ℕ} (hN : 0 < N) (hNm : ∀ a b, (N : A) * Yi a b ∈ S)
    {p : ℕ} (hp : 0 < p) (b : Fin n) :
    ∃ (x : Fin n → E) (t : Fin n → A), (∀ c, t c ∈ S) ∧ Yi *ᵥ (fun i => j (x i)) = Pi.single b 1 - (p : A) • t := by
  choose x s hs hx using fun i => happ (p * N) (Nat.mul_pos hp hN) (Y i b)
  refine ⟨x, ((N : A) • Yi) *ᵥ s, fun c => ?_, ?_⟩
  · rw [Matrix.mulVec, dotProduct]
    exact S.sum_mem fun k _ => S.mul_mem (hNm c k) (hs k)
  · have e : (fun i => j (x i)) = Y *ᵥ Pi.single b 1 - (p : A) • (N : A) • s := by
      funext i
      rw [Matrix.mulVec_single_one]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply]
      rw [hx i]
      push_cast
      ring
    rw [e, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hY, Matrix.one_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.smul_mulVec]

theorem read_col {A E C : Type} [CommRing A] [CommRing E] [CommRing C] (j : E →+* A) (ev : A →+* C) (inc : E →+* C)
    (hj : ∀ e, ev (j e) = inc e) {n : ℕ} (Y Yi : Matrix (Fin n) (Fin n) A) (hY : Y * Yi = 1) (Bi : Matrix (Fin n) (Fin n) E)
    {p : ℕ} {b : Fin n} {x : Fin n → E} {t : Fin n → A}
    (h : Yi *ᵥ (fun i => j (x i)) = Pi.single b 1 - (p : A) • t) (a : Fin n) :
    (Bi.map inc * Y.map ev) a b - (p : C) * ∑ c, (Bi.map inc * Y.map ev) a c * ev (t c) = inc ((Bi *ᵥ x) a) := by
  have h1 : Y *ᵥ (Pi.single b 1 - (p : A) • t) = fun i => j (x i) := by
    rw [← h, Matrix.mulVec_mulVec, hY, Matrix.one_mulVec]
  have h2 : (ev ∘ (Pi.single b 1 - (p : A) • t : Fin n → A)) = Pi.single b 1 - (p : C) • fun c => ev (t c) := by
    funext c
    simp only [Function.comp_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, map_natCast,
      Pi.single_apply, apply_ite ev, map_one, map_zero]
  have h3 : Y.map ev *ᵥ (Pi.single b 1 - (p : C) • fun c => ev (t c)) = inc ∘ x := by
    funext i
    rw [← h2, ← RingHom.map_mulVec, h1, hj]
    rfl
  rw [RingHom.map_mulVec, ← h3, Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_single_one]
  rfl

theorem stdLat_of {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (h : V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame)) :
    Seed.FrmC.StdLat V := by
  intro x
  show (∑ i, x i • V.frame i ∈ V.L0) ↔ _
  rw [h, V.frame.mem_span_iff_repr_mem (𝓞 D.host.E), V.frame.repr_sum_self]
  exact forall_congr' fun i => (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).symm

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem approx (M : ℕ) (hM : 0 < M) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    ∃ (e : E) (s : E ⊗[F] FiniteAdeleRing (𝓞 F) F), s ∈ Formalism.L2.Herm.intAf F E ∧
      z = e ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) + (M : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * s := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add x y hx hy =>
    obtain ⟨e₁, s₁, h₁, rfl⟩ := hx
    obtain ⟨e₂, s₂, h₂, rfl⟩ := hy
    refine ⟨e₁ + e₂, s₁ + s₂, add_mem h₁ h₂, ?_⟩
    rw [TensorProduct.add_tmul]
    ring
  | tmul b α =>
    obtain ⟨d, hd, ho⟩ := GlobalTheory.AdIdem.exists_nat_mul_integral E b
    obtain ⟨x, β, hβ, rfl⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F (M * d) (Nat.mul_pos hM hd) α
    refine ⟨x • b, ((d : E) * b) ⊗ₜ[F] β, GlobalTheory.PlaceDatum.tmul_mem_int ho (α := β) hβ, ?_⟩
    rw [TensorProduct.tmul_add, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, TensorProduct.tmul_smul,
      ← nsmul_eq_mul, ← nsmul_eq_mul, mul_smul]
    rfl

theorem norm_ev_le_one {l : ℕ} [Fact l.Prime] {inc : E →+* PadicAlgCl l}
    {ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l} (hev : EvOk inc ev) {r : E ⊗[F] FiniteAdeleRing (𝓞 F) F}
    (hr : r ∈ Formalism.L2.Herm.intAf F E) :
    ‖ev ((Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).symm r)‖ ≤ 1 := by
  induction hr using Subring.closure_induction with
  | mem r hr =>
    rcases hr with ⟨⟨_, o, rfl⟩, rfl⟩ | ⟨⟨β, hβ⟩, rfl⟩
    · refine (congrArg norm (hev.1 (algebraMap (𝓞 E) E o))).le.trans ?_
      exact GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int inc o.isIntegral_coe)
    · exact hev.2.1 β hβ
  | zero => simp
  | one => simp
  | add x y _ _ hx hy =>
    rw [map_add, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | neg x _ hx => rwa [map_neg, map_neg, norm_neg]
  | mul x y _ _ hx hy =>
    rw [map_mul, map_mul, norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy

end General

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem norm_le_one_of_isLocBasis : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (l : ℕ) [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l), EvOk inc ev → V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame) → ∀ (y : Bridge.Gf V) (B : GL (Fin V.rank) D.host.E), Formalism.L2.Forms.IsLocBasis l (Bridge.hLat V y : Set (Fin V.rank → D.host.E)) B → ∀ a b, ‖((Matrix.GeneralLinearGroup.map inc B)⁻¹ * Matrix.GeneralLinearGroup.map ev (y : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))).val a b‖ ≤ 1 := by
  intro D V l hl inc ev hev hL0 y B hB
  have hV := stdLat_of V hL0
  have hY := GlobalTheory.HLatStd.invM_mul y
  obtain ⟨N, hN, hNm⟩ := GlobalTheory.PlaceDatum.exists_den_matrix (GlobalTheory.StdFrameExist.SI D) GlobalTheory.PlaceDatum.exists_den_adele
    (GlobalTheory.HLatStd.invM y)
  let j : D.host.E →+* Lev.EAf D := Algebra.TensorProduct.includeLeftRingHom
  let ev' : Lev.EAf D →+* PadicAlgCl l := ev.comp (GlobalTheory.HeckeTrans.unswap D)
  have hU : ((Matrix.GeneralLinearGroup.map inc B)⁻¹ * Matrix.GeneralLinearGroup.map ev (y : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))).val =
      (B⁻¹).val.map inc * ((Units.val ((y : Bridge.Gf V) : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))).map (Lev.swapAE D)).map ev' := by
    rw [← map_inv, Units.val_mul]
    congr 1
    ext a b
    exact (congrArg ev (GlobalTheory.HeckeTrans.unswap_swap _)).symm
  rw [hU]
  refine norm_le_one_of_cols _ (l : PadicAlgCl l) (norm_natCast_lt_one l) fun b => ?_
  obtain ⟨x, t, ht, hx⟩ := exists_col j (GlobalTheory.StdFrameExist.SI D) (fun M hM z => approx M hM z) _ _
    (mul_eq_one_comm.1 hY) hN hNm hl.out.pos b
  refine ⟨fun c => ev' (t c), fun c => norm_ev_le_one hev (ht c), fun a => ?_⟩
  rw [read_col j ev' inc (fun e => hev.1 e) _ _ hY _ hx a]
  have hmem : x ∈ Bridge.hLat V y := by
    refine GlobalTheory.HLatStd.mem_hLat_of hV y fun i => ?_
    have hi : (GlobalTheory.HLatStd.invM y *ᵥ GlobalTheory.HLatStd.iv x) i = _ := congrFun hx i
    rw [hi, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    refine sub_mem ?_ (mul_mem (natCast_mem _ _) (ht i))
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨s, hs, hint⟩ := (hB x).1 ⟨1, hl.out.not_dvd_one, by rw [Nat.cast_one, one_smul]; exact hmem⟩
  obtain ⟨o, ho⟩ := hint a
  have h1 : ‖inc (algebraMap (𝓞 D.host.E) D.host.E o)‖ ≤ 1 :=
    GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int inc o.isIntegral_coe)
  rwa [ho, map_mul, map_natCast, norm_mul, norm_natCast_eq_one l hs, one_mul] at h1

end GlobalTheory.LocBasisInt
