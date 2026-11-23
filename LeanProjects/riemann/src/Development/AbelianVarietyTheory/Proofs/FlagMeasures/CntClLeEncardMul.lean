import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteLatticeDiscriminantModuleCardDetSq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardBiUnionLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdxNOneMulAbsNorm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeProdReal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardSublatticesBoundedDetLeSum
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountTermsGramClassOverSublatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPowLeCardFlagQuotientStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExponentBookkeepingDivisorSumLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassNumberRootDiscFactorLeHHZStatement
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe

namespace GlobalTheory.LoopC.GenericMean

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lead_eq {E : Type} [Field E] {n : ℕ} {Z Z₂ : Matrix (Fin n) (Fin n) E} (h : ZEquiv Z Z₂) (l : ℕ) :
    leadMinorE Z₂ l = leadMinorE Z l := by
  obtain ⟨A, B, hA0, hA1, hB0, hB1, rfl⟩ := h
  unfold leadMinorE
  split_ifs with hl
  · exact Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.leadingMinorInvariant E n l hl _ Z _ (fun i => by simp [hA1])
      (fun i j hij => by simp [hA0 i j hij]) (fun i => by simp [hB1]) (fun i j hij => by simp [hB0 i j hij])
  · rfl

open GlobalTheory.Mass GlobalTheory.LoopC.DetCard Formalism.HermitianLatticesTheory in

theorem det_index {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hK : IsCMUnram K) (hs : h.IsSymm) (M P : Submodule (𝓞 K) V) (hM : M.FG) (hI : IsIntegralLat h M) (hP : P ≤ M)
    (hU : Submodule.span K (P : Set V) = Submodule.span K (M : Set V))
    (hn : ∀ x ∈ Submodule.span K (M : Set V), (∀ y ∈ Submodule.span K (M : Set V), h y x = 0) → x = 0) :
    idxN M P ≠ 0 ∧ latDetH h P = latDetH h M * idxN M P := by
  have hIP : IsIntegralLat h P := fun x hx y hy => hI x (hP hx) y (hP hy)
  obtain ⟨-, m3⟩ := Partner.det_sq h hK hs M hM hI hn
  obtain ⟨-, p3⟩ := Partner.det_sq h hK hs P (hM.of_le hP) hIP (hU ▸ hn)
  set U := Submodule.span K (M : Set V) with hUd
  have hsU : (hRes h U).IsSymm := ⟨fun x y => hs.eq x y⟩
  have hnU : (hRes h U).Nondegenerate :=
    ⟨fun x hx => Subtype.ext (hn x x.2 fun y hy => RowPerp.swap_zero hs (hx ⟨y, hy⟩)),
      fun x hx => Subtype.ext (hn x x.2 fun y hy => hx ⟨y, hy⟩)⟩
  have m1 : IsIntLat (hRes h U) (latIn U M) :=
    ⟨isLattice_latIn_span hM rfl, fun x hx y hy => hI x hx y hy⟩
  have p1 : IsIntLat (hRes h U) (latIn U P) :=
    ⟨isLattice_latIn_span (hM.of_le hP) hU, fun x hx y hy => hIP x hx y hy⟩
  obtain ⟨q1, q2⟩ := (DiscOrder.main K U _ hK hsU hnU _ p1).2.2.1 _ m1 (Submodule.comap_mono hP)
  rw [← idxN_latIn (U := U) (fun x hx => Submodule.subset_span hx)
    (fun x hx => Submodule.subset_span (hP hx))] at q1 q2
  refine ⟨q1, ?_⟩
  rw [p3, m3, idxN_dualInH h hU, idxN_dualInH h hUd.symm, q2, Nat.cast_mul, Nat.cast_pow,
    Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]

theorem le_finrank_orth {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
    (F : FlagG S r T) (F' : FlagG S r T') :
    finrank E S.V ≤ finrank E (orth S (F.Xplus ⊔ F'.Xplus)) + 2 * (r + 1) := by
  let φ : S.V →ₗ[E] (Fin (r + 1) ⊕ Fin (r + 1) → E) := LinearMap.pi fun i => S.hT (Sum.elim F.fvec F'.fvec i)
  have h1 := φ.finrank_range_add_finrank_ker
  have h2 := Submodule.finrank_le (LinearMap.range φ)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at h2
  have h3 : LinearMap.ker φ ≤ orth S (F.Xplus ⊔ F'.Xplus) := fun v hv => by
    have hv' : ∀ i, S.hT (Sum.elim F.fvec F'.fvec i) v = 0 := fun i => congrFun (LinearMap.mem_ker.1 hv) i
    refine (Formalism.MainNotions.mem_orth_iff _ _).2 fun x hx => ?_
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, LinearMap.add_apply,
      Formalism.MainNotions.hT_zero_of_mem_Xplus F (fun a => by simpa [FlagG.fvec] using hv' (.inl a.castSucc))
        (by simpa [FlagG.fvec] using hv' (.inl (Fin.last r))) p hp,
      Formalism.MainNotions.hT_zero_of_mem_Xplus F' (fun a => by simpa [FlagG.fvec] using hv' (.inr a.castSucc))
        (by simpa [FlagG.fvec] using hv' (.inr (Fin.last r))) q hq, add_zero]
  have h4 := Submodule.finrank_mono h3
  omega

theorem orth_lattice (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D) (hs : Stand D u u')
    (hb : IsBase D u F0) (hΛ : IsRowLat D F0 Λ) (F' : FlagU D u') (hF' : IsTermF D Λ (lf D F0) F') :
    seen D (lf D F0) (Thp Λ (lf D F0) F') ≤ L0X D Λ (lf D F0) ∧
      rkW D (seen D (lf D F0) (Thp Λ (lf D F0) F')) = D.R.k - 1 ∧
      detW D (seen D (lf D F0) (Thp Λ (lf D F0) F')) ≤ G0 Λ (gS D) (lf D F0) F' := by
  obtain ⟨hW, -, hpd, b4, b5, -⟩ := Base.main D u u' F0 Λ hs hb hΛ
  obtain ⟨-, ⟨hL, hu, hl, -⟩, hX⟩ := id hΛ
  obtain ⟨⟨hl', had, hG⟩, hc', hX'⟩ := hF'
  have hF := Partner.frame_mem_of_XS (lf D F0) hl hX
  have hF' := Partner.frame_mem_of_XS F' hl' hX'
  have n1 := Partner.UUE_eq (lf D F0) F' hl hl' hF hF'
  have n2 : UUE Λ (lf D F0) F' ⊓ orth (hS D) (UUE Λ (lf D F0) F') = ⊥ := by
    rw [n1]; exact Partner.sup_inf_orth F0 F'.fl hG
  have n3 : finrank D.host.E (Hp Λ (lf D F0) F') = D.R.k - 1 := by
    have a1 := Partner.finrank_orth_le F0 F'.fl hG (Nat.cast_ne_zero.2 hs.2.1.ne_zero)
      (Nat.cast_ne_zero.2 hs.2.2.1.ne_zero)
    have a2 := le_finrank_orth F0 F'.fl
    have a3 := Formalism.MainNotions.finrank_hS D
    rw [Hp, n1]
    change finrank D.host.E (orth (VS D) (F0.Xplus ⊔ F'.fl.Xplus)) = _
    change finrank D.host.E (VS D).V = _ at a3
    omega
  have hXp : Xplus (lf D F0) ≤ UUE Λ (lf D F0) F' := n1 ▸ le_sup_left
  have hH : Hp Λ (lf D F0) F' ≤ orth (hS D) (Xplus (lf D F0)) := fun x hx =>
    (Formalism.MainNotions.mem_orth_iff _ _).2 fun y hy => (Formalism.MainNotions.mem_orth_iff _ _).1 hx y (hXp hy)
  have hle := Partner.UU_le (lf D F0) F' hl hl'
  have hsp : spanE (hS D) (BLat Λ (lf D F0) F') = UUE Λ (lf D F0) F' := GlobalTheory.Mass.DetAgree.span_inf_eq Λ hL _
  have d1 := Partner.det_seen_le (lf D F0) hL hu hW hpd ⟨b4, b5⟩ (BLat Λ (lf D F0) F') inf_le_left
    (hsp ▸ hXp) (hsp ▸ n2)
  rw [hsp] at d1
  obtain ⟨g1, g2⟩ := det_index (hS D).hT D.sp.cm.cmUnram (hS D).herm (BLat Λ (lf D F0) F') (UU Λ (lf D F0) F')
    (hL.fg.of_le inf_le_left)
    (fun x hx y hy => (Formalism.HermitianLatticesTheory.dualBasic_mem_dual _ _ _).1 (hu.ge hy.1) x hx.1)
    (fun x hx => ⟨hle hx, Submodule.subset_span hx⟩) hsp.symm (fun x hx H =>
      (Submodule.mem_bot _).1 (n2.le ⟨hsp.le hx, (Formalism.MainNotions.mem_orth_iff _ _).2 fun y hy => H y (hsp.ge hy)⟩))
  have hg : gS D ≠ 0 := mul_ne_zero hs.2.2.2.2.2.2.2.1.ne_zero hs.2.2.2.2.2.2.2.2.1.ne_zero
  have hB := GlobalTheory.T.norm_pow_le_card_flag_quotient _ (hS D) _ Λ (gS D) _ _ (lf D F0) F' hg hl hl' hF hF' hc' had hG
    (Nat.finite_of_card_ne_zero g1)
  refine ⟨Partner.seen_le_L0X _ _ hH, (Partner.rk_seen _ hL hW _ hH ?_).trans n3, d1.trans ?_⟩
  · rw [eq_bot_iff, ← n2, inf_comm]
    exact inf_le_inf (le_sup_left.trans hXp) le_rfl
  · have hN : 0 < NE (E := D.host.E) (gS D) ^ (D.R.rS + 1) := by
      unfold NE
      have : (0 : ℝ) < gS D := Nat.cast_pos.2 (Nat.pos_of_ne_zero hg)
      positivity
    rw [G0, le_div_iff₀ hN, NG, latDet, latDet, g2]
    exact mul_le_mul_of_nonneg_left hB (Real.sqrt_nonneg _)

theorem sub_count (D : D7) (L : LatW D) (hp : IsPosDef (D.sp.X 0).hT)
    (hk : finrank D.host.E (D.sp.X 0).V = D.R.k) (hL : L.FG) (hI : Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT L)
    (n : ℕ) (G : ℝ) :
    (Set.encard {P : LatW D | P ≤ L ∧ rkW D P = n ∧ detW D P ≤ G} : ℝ≥0∞) ≤
      ∑ de ∈ Finset.Icc 1 ⌊G⌋₊, (cntPrim (D.sp.X 0).hT L n de : ℝ≥0∞) *
        ENNReal.ofReal ((G / (de : ℝ)) ^ ((D.R.k : ℝ) + lg2f D.R.f + 1)) := by
  rcases le_or_gt 1 G with hG | hG
  · exact SubCount.main D L hp hk hL hI n G hG
  · have : {P : LatW D | P ≤ L ∧ rkW D P = n ∧ detW D P ≤ G} = ∅ := by
      refine Set.eq_empty_of_forall_notMem ?_
      rintro P ⟨h1, -, h2⟩
      obtain ⟨a, b, -⟩ := DetCard.main D P (hL.of_le h1) hp fun x hx y hy => hI x (h1 hx) y (h1 hy)
      have c : (1 : ℝ) ≤ detW D P ^ 2 := by rw [← b]; exact_mod_cast a
      have d : 0 ≤ detW D P := Real.sqrt_nonneg _
      nlinarith
    simp [this]

theorem cntCl_le_encard_mul {α ι : Type} {R : α → α → Prop} (hR : Equivalence R) (X : Set α) (I : Set ι)
    (Y : ι → Set α) (B : ℝ≥0∞) (hB0 : B ≠ 0) (h : ∀ a ∈ X, ∃ i ∈ I, a ∈ Y i)
    (hY : ∀ i ∈ I, (cntCl (Y i) R : ℝ≥0∞) ≤ B) : (cntCl X R : ℝ≥0∞) ≤ (I.encard : ℝ≥0∞) * B := by
  by_cases hI : I.Finite
  · have h1 := FrEqv.cntCl_le_sum hR hI.toFinset X Y fun a ha => by
      obtain ⟨i, hi, hi'⟩ := h a ha
      exact ⟨i, hI.mem_toFinset.2 hi, a, hi', hR.refl a⟩
    have h2 : (cntCl X R : ℝ≥0∞) ≤ ∑ i ∈ hI.toFinset, (cntCl (Y i) R : ℝ≥0∞) := by
      have := ENat.toENNReal_le.2 h1
      refine this.trans (le_of_eq ?_)
      exact map_sum ENat.toENNRealRingHom _ _
    refine h2.trans ((Finset.sum_le_card_nsmul _ _ B fun i hi => hY i (hI.mem_toFinset.1 hi)).trans ?_)
    rw [hI.encard_eq_coe_toFinset_card, nsmul_eq_mul]
    simp
  · rw [Set.Infinite.encard_eq hI, ENat.toENNReal_top, ENNReal.top_mul hB0]
    exact le_top

theorem prod_nV (D : D7) (u u' : D.what₂.Word) (Z : GramM D) (hg : gS D ≠ 0) :
    ∏ τ, nV D (Tu D u) (Tu D u') Z τ = (Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) *
      ((∏ τ, Gz D (Tu D u) (Tu D u') Z τ) / NE (E := D.host.E) (gS D) ^ (D.R.rS + 1) / NT D u) ^ D.R.k := by
  obtain ⟨hcard, hE, -, hm, -⟩ := GlobalTheory.real_places_facts D
  have hg' : (0 : ℝ) < gS D := Nat.cast_pos.2 (Nat.pos_of_ne_zero hg)
  have e : ∀ τ, nV D (Tu D u) (Tu D u') Z τ = ((Real.exp 1 * Real.pi / (D.R.k * D.host.v)) *
      (((gS D : ℝ) ^ D.R.m)⁻¹ * (Tu D u : ℝ)⁻¹) * Gz D (Tu D u) (Tu D u') Z τ) ^ D.R.k := fun τ => by
    rw [nV, Real.rpow_neg hg'.le, Real.rpow_natCast]
    congr 1
    ring
  simp only [e]
  rw [Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard, NE, hE, hm, NT,
    mul_comm D.R.k D.R.f, pow_mul, ← mul_pow]
  congr 1
  unfold Tu
  ring

theorem main : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → (Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ what₂ : Finset (LatV D), IsRowReps D F0 what₂ → ∀ de : ℕ, 1 ≤ de → ∀ HH : ℝ, (de : ℝ) ≤ HH → NT D u ≤ HH → MeanLe D F0 what₂ (fun Λ => cntPrim (D.sp.X 0).hT (L0X D Λ (lf D F0)) (D.R.k - 1) de) (((de : ℝ) / NT D u) ^ (D.R.k - 1) * (Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) * (((2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f * (classNumber D.host.E : ℝ) * 2 ^ D.R.f) * HH ^ (11 + 3 * Real.logb 2 D.R.f)))) → Formalism.MainNotions.S.UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C := by
  intro Cg cb Cu cT CT C0 A
  obtain ⟨C1, h1⟩ := GlobalTheory.T.count_terms_gramClass_over_sublattice Cg cb Cu cT CT C0 A
  obtain ⟨C3, h3⟩ := GlobalTheory.T.classNumber_rootDisc_factor_le_HHZ Cg cb Cu cT CT C0 A
  refine ⟨max (max C1 CT) (max C3 60), fun D large₂ u u' C' Cl hCl hP hH F0 he hz what₂ hrows Z hZ => ?_⟩
  set C := max (max C1 CT) (max C3 60) with hC
  have c1 : C ≥ C1 := (le_max_left _ _).trans (le_max_left _ _)
  have c2 : CT ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have c3 : C ≥ C3 := (le_max_left _ _).trans (le_max_right _ _)
  have c4 : 60 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hs : Stand D u u' := hH.2.1
  have hS0 := hH.1.1
  have hg : gS D ≠ 0 := mul_ne_zero hs.2.2.2.2.2.2.2.1.ne_zero hs.2.2.2.2.2.2.2.2.1.ne_zero
  have hf : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (lt_of_lt_of_le two_pos D.R.two_le_m)) hS0.2.2.1
  have hk : 1 ≤ D.R.k := hf.trans hS0.2.2.2.1
  have hlog : Real.log D.R.f ≤ Real.sqrt D.R.rS := hS0.2.2.2.2.1
  have hv : 1 ≤ D.host.v := hS0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTb := hS0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (Real.rpow_nonneg (zero_lt_one.trans large₂.sc.one_lt_alt).le _)
  obtain ⟨-, z1, z2⟩ : _ ∧ NT D u ≤ _ ∧ _ := Partner.sizes hb (by linarith : 2 ≤ C) c2 hs.1
    (Nat.one_le_cast.2 hs.2.1.one_le : (1 : ℝ) ≤ Tu D u) (Nat.one_le_cast.2 hs.2.2.1.one_le : (1 : ℝ) ≤ Tu D u')
    (hTb u).2 (hTb u').2 Z
  have z3 := h3 C c3 D large₂ u u' C' Cl hCl hH Z
  set H := HHZ D large₂.sc.b C Z with hHd
  set G := (∏ τ, Gz D (Tu D u) (Tu D u') Z τ) / NE (E := D.host.E) (gS D) ^ (D.R.rS + 1) with hGd
  have hN : 1 ≤ NT D u := one_le_pow₀ (Nat.one_le_cast.2 hs.2.1.one_le)
  have hH1 : 1 ≤ H := hN.trans z1
  have hNE : 1 ≤ NE (E := D.host.E) (gS D) ^ (D.R.rS + 1) :=
    one_le_pow₀ (one_le_pow₀ (Nat.one_le_cast.2 (Nat.pos_of_ne_zero hg)))
  have hGH : G ≤ H := by
    rw [hGd, div_le_iff₀ (one_pos.trans_le hNE)]
    exact z2.trans (le_mul_of_one_le_right (zero_le_one.trans hH1) hNE)
  set G' := max G 1 with hG'
  set B := NT D u ^ (2 * D.R.rS) * G' ^ D.R.rS * 9 ^ D.R.f * H ^ (9 + 9 * D.R.rS + 16 * D.R.rS ^ 2) with hB
  have hG'1 : 1 ≤ G' := le_max_right _ _
  have hB0 : 0 < B := by positivity
  have row : ∀ Λ ∈ what₂, (cntSW D ((Tu D u' : ℕ) : D.host.E) (lf D F0) Λ Z : ℝ≥0∞) ≤
      ∑ de ∈ Finset.Icc 1 ⌊G⌋₊, (cntPrim (D.sp.X 0).hT (L0X D Λ (lf D F0)) (D.R.k - 1) de : ℝ≥0∞) *
        ENNReal.ofReal ((G / de) ^ ((D.R.k : ℝ) + Real.logb 2 (2 * D.R.f) + 1) * B) := by
    intro Λ hΛr
    have hΛ := hrows.1 Λ hΛr
    obtain ⟨b1, b2, b3, b4, b5, -⟩ := Base.main D u u' F0 Λ hs ⟨he, hz⟩ hΛ
    have b6 : finrank D.host.E (D.sp.X 0).V = D.R.k := (LinearMap.finrank_range_of_inj b2).symm.trans b1.2.2
    have a1 := cntCl_le_encard_mul (FrEqv.TEqv_equivalence D Λ (lf D F0) (T' := ((Tu D u' : ℕ) : D.host.E)))
      {F' | IsTerm Λ (gS D) (lf D F0) F' ∧ FrameOK D Λ F' ∧ IsGeneric Λ (gS D) (lf D F0) F' ∧
        ZEquiv (ZhatL (lf D F0) F') Z}
      {P : LatW D | P ≤ L0X D Λ (lf D F0) ∧ rkW D P = D.R.k - 1 ∧ detW D P ≤ G}
      (fun P => FrSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P) (ENNReal.ofReal B)
      (ENNReal.ofReal_pos.2 hB0).ne'
      (by
        rintro F' ⟨t1, t2, t3, t4⟩
        obtain ⟨o1, o2, o3⟩ := orth_lattice D u u' F0 Λ hs ⟨he, hz⟩ hΛ F' ⟨t1, t2⟩
        refine ⟨_, ⟨o1, o2, o3.trans (le_of_eq ?_)⟩, ⟨t1, t2⟩, t4, le_rfl⟩
        rw [G0, FrameDet.main D large₂ u u' C' Cl Cg cb Cu cT CT C0 A hH F0 he hz Λ hΛ F' ⟨t1, t2⟩ t3, hGd]
        simp only [Gz, absDl, lead_eq t4])
      (by
        rintro P ⟨p1, p2, p3⟩
        have := h1 C c1 D large₂ u u' C' Cl hCl hH F0 he hz Λ hΛ Z hZ 1 le_rfl hk P p1 p2 G' H hG'1
          (p3.trans (le_max_left _ _)) le_rfl
          ((max_le hGH hH1).trans (le_self_pow₀ hH1 three_ne_zero))
        simpa only [mul_one, one_mul] using this)
    refine a1.trans ((mul_le_mul_left (sub_count D _ b3 b6 b4.fg b5 (D.R.k - 1) G) _).trans (le_of_eq ?_))
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun de _ => ?_
    rw [mul_assoc, ← ENNReal.ofReal_mul' hB0.le]
    rfl
  unfold MeanLe
  refine (Finset.sum_le_sum fun Λ hΛ => mul_le_mul_right (row Λ hΛ) _).trans ?_
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul]
  rcases lt_or_ge G 1 with hG1 | hG1
  · rw [Nat.floor_eq_zero.2 hG1]
    simp
  have hGG : G' = G := max_eq_left hG1
  have ha : 0 ≤ (Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) := by
    have := Real.pi_pos
    positivity
  have hrd : 0 ≤ D.host.rdE := zero_le_one.trans (GlobalTheory.real_places_facts D).2.2.2.2.1
  have key := GlobalTheory.T.exponent_divisor_sum_le D.R.k D.R.f D.R.rS G (NT D u) H _
    ((2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f * (classNumber D.host.E : ℝ) * 2 ^ D.R.f) C hk hs.1 hf
    hlog hG1 hN hGH z1 ha (by positivity) z3 c4
  refine (Finset.sum_le_sum fun de hde => mul_le_mul_left
    (hP hH F0 he hz what₂ hrows de (Finset.mem_Icc.1 hde).1 H
      (((Nat.le_floor_iff (zero_le_one.trans hG1)).1 (Finset.mem_Icc.1 hde).2).trans hGH) z1) _).trans ?_
  simp only [mul_assoc (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ))]
  rw [← Finset.mul_sum]
  refine mul_le_mul_right ?_ _
  rw [prod_nV D u u' Z hg]
  refine le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal key)
  rw [ENNReal.ofReal_sum_of_nonneg fun de _ => by positivity]
  refine Finset.sum_congr rfl fun de _ => ?_
  rw [← ENNReal.ofReal_mul (by positivity), hB, hGG]

end GlobalTheory.LoopC.GenericMean
