import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasureFundamentalDomainLtTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffRational
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ActEEqOfConjRelated
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffIntegrableContinuous
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousUnitaryRootExchangeMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemBesselExchangeGroupIffRootExchange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryRootExchangeMirrorIdentityStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnnihilatorSubsetCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueNormalizedHaarMeasureAdelicUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootExch.PosLinear

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

def exL (d : BesselDatum A B ι) (ε : AE D) (m : ∀ i, Measure (d.Ex ε i)) (l : List (Fin (d.ρ + 1)))
    (β : GA D B → ℂ) : GA D B → ℂ := l.foldr (fun i β' => exF d ε i (m i) β') β

def moveL (P : PosDatum A B ι) (l : List (Fin P.n)) (β : GA D B → ℂ) : GA D B → ℂ :=
  l.foldr (fun a β' => toPosF P.bes (P.ε a) (P.m a) (P.p a) β') β

theorem lvl_exL (d : BesselDatum A B ι) (ε : AE D) (m) (l) {β : GA D B → ℂ} (h : Lvl β) : Lvl (exL d ε m l β) := by
  obtain ⟨U, hU, hk⟩ := h
  refine ⟨U, hU, fun k k1 k2 => ?_⟩
  induction l with
  | nil => exact hk k k1 k2
  | cons i l ih =>
    intro g
    show ∫ u, exL d ε m l β ((u : GA D B) * (g * k)) ∂(m i) = ∫ u, exL d ε m l β ((u : GA D B) * g) ∂(m i)
    simp only [← mul_assoc, ih]

theorem eqv_exL (d : BesselDatum A B ι) (ψ) {ε ε' : AE D} (hε : (ε' + cA D ε') * (ε + cA D ε) = 0) (m) (l)
    {β : GA D B → ℂ} (h : Eqv d ψ ε' β) : Eqv d ψ ε' (exL d ε m l β) := by
  intro n hn hs
  induction l with
  | nil => exact h n hn hs
  | cons i l ih =>
    intro g
    show ∫ u, exL d ε m l β ((u : GA D B) * (n * g)) ∂(m i) = _ * ∫ u, exL d ε m l β ((u : GA D B) * g) ∂(m i)
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show exL d ε m l β ((u : GA D B) * (n * g)) = _ * exL d ε m l β ((u : GA D B) * g)
    rw [← mul_assoc, ← commute_of_apart hε hs (suppAt_of_mem_Ex u.2), mul_assoc, ih]

theorem exL_left (d : BesselDatum A B ι) (ψ) (ε : AE D) (m) {β : GA D B → ℂ} (h : Eqv d ψ ε β) (p : ℕ) (c : ℂ)
    (l : List (Fin (d.ρ + 1))) (hl : ∀ i ∈ l, p ≤ i.1) :
    ∀ n, (∀ b ∈ ExGe d ε p, b * n * b⁻¹ ∈ d.N ∧ SuppAt ε B (b * n * b⁻¹) ∧ d.psiN ψ (b * n * b⁻¹) = c) →
      ∀ g, exL d ε m l β (n * g) = c * exL d ε m l β g := by
  induction l with
  | nil =>
    intro n hn g
    have := hn 1 (one_mem _)
    simp only [one_mul, inv_one, mul_one] at this
    rw [← this.2.2]
    exact h n this.1 this.2.1 g
  | cons i l ih =>
    intro n hn g
    show ∫ u, exL d ε m l β ((u : GA D B) * (n * g)) ∂(m i) = _ * ∫ u, exL d ε m l β ((u : GA D B) * g) ∂(m i)
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show exL d ε m l β ((u : GA D B) * (n * g)) = _ * exL d ε m l β ((u : GA D B) * g)
    have hu : (u : GA D B) ∈ ExGe d ε p := Ex_le_ExGe d ε (hl i List.mem_cons_self) u.2
    have e : (u : GA D B) * (n * g) = (u * n * (u : GA D B)⁻¹) * (u * g) := by
      simp only [mul_assoc, inv_mul_cancel_left]
    rw [e]
    refine ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) _ (fun b hb => ?_) _
    have e2 : b * (u * n * (u : GA D B)⁻¹) * b⁻¹ = (b * u) * n * (b * u)⁻¹ := by
      simp only [mul_assoc, _root_.mul_inv_rev]
    rw [e2]
    exact hn _ (mul_mem hb hu)

theorem isK_unique {v y : Fin B.rank → AE D} {k k' : GA D B} (h : IsK B v y k) (h' : IsK B v y k') : k = k' :=
  mt_ext fun x => by rw [h x, h' x]

theorem isK_zero (v : Fin B.rank → AE D) : IsK B v 0 1 := fun x => by
  rw [GlobalTheory.BesselCompare.mt_one, Matrix.one_mulVec, hA_zero_right, zero_smul, smul_zero, add_zero, sub_zero]

theorem continuous_iA : Continuous (iA (A := A) (B := B) ι) := by
  haveI : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  unfold iA
  exact continuous_const.matrix_mulVec continuous_id

theorem exists_K (η : AE D) (hη : η * cA D η = 0) {v : B.V} (hv : ∀ x, B.hD v (ι x) = 0) :
    ∃ K : {t : Fin A.rank → AE D // η • t = t} → GA D B, Continuous K ∧ ∀ t, IsK B (vecA B v) (iA ι t.1) (K t) := by
  obtain ⟨K, hK, hk⟩ := GlobalTheory.RootUnip.exists_continuous_isK D B η hη (vecA B v)
  refine ⟨fun t => K ⟨iA ι t.1, by rw [← iA_smul, t.2], hA_vec_iA hv _⟩,
    hK.comp (Continuous.subtype_mk (continuous_iA.comp continuous_subtype_val) _), fun t => hk _⟩

theorem isLocallyConstant_of_lvl {β : GA D B → ℂ} (h : Lvl β) (H : Subgroup (GA D B)) (hH : H ≤ GfC B) (g : GA D B) :
    IsLocallyConstant fun u : H => β ((u : GA D B) * g) := by
  haveI : IsTopologicalGroup (GA D B) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B).2.2.2.2.1
  obtain ⟨U, hU, hk⟩ := h
  rw [IsLocallyConstant.iff_exists_open]
  intro u
  refine ⟨(fun u' : H => g⁻¹ * ((u : GA D B)⁻¹ * u') * g) ⁻¹' U, hU.preimage (by fun_prop), by simp, fun u' hu' => ?_⟩
  have hn : (GfC B).Normal := MonoidHom.normal_ker _
  have := hk _ hu' (hn.conj_mem' _ (hH (u⁻¹ * u').2) g) (u * g)
  rw [← this]
  simp only [mul_assoc, mul_inv_cancel_left]

theorem exch_finite (d : BesselDatum A B ι) {ψ} (hψ : IsStdChar D ψ (-1)) {ε : AE D} (hε : IsSplitIdem D ε) (m)
    {β : GA D B → ℂ} (h1 : Lvl β) (h2 : Eqv d ψ ε β) (i : Fin (d.ρ + 1)) (hi : 1 ≤ i.1)
    (l : List (Fin (d.ρ + 1))) (hl : ∀ j ∈ l, i.1 + 1 ≤ j.1) (g : GA D B) :
    IsLocallyConstant (fun u : d.Ex ε i => exL d ε m l β ((u : GA D B) * g)) ∧
      HasCompactSupport (fun u : d.Ex ε i => exL d ε m l β ((u : GA D B) * g)) := by
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  haveI : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  haveI : T2Space (AE D) := e0.isEmbedding.t2Space
  have hL := lvl_exL d ε m l h1
  refine ⟨isLocallyConstant_of_lvl hL _ (fun u hu => mem_GfC hε (suppAt_of_mem_Ex hu)) g, ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j : Fin d.ρ, i = j.succ := (Fin.eq_zero_or_eq_succ i).resolve_left (by rintro rfl; simp at hi)
  obtain ⟨U, hU, hk⟩ := hL
  obtain ⟨K, hK, hKk⟩ := exists_K (ι := ι) (cA D ε) (by rw [cA_cA, mul_comm, hε.2.1]) (d.eA j)
  obtain ⟨K₀, hK₀, hK₀k⟩ := exists_K (ι := ι) ε hε.2.1 (dual_perp d j.succ)
  have hmem : ∀ t, K₀ t ∈ d.Ex ε j.succ := fun t =>
    (GlobalTheory.RootExch.ExStruct.mem_Ex_iff D A B ι d ε hε _ _).2 ⟨t.1, t.2, hK₀k t⟩
  have hopen : IsOpen ((fun t => g⁻¹ * K t * g) ⁻¹' (U : Set (GA D B))) := hU.preimage (by fun_prop)
  obtain ⟨V, hV, hVe⟩ := isOpen_induced_iff.1 hopen
  have h0 : (0 : Fin A.rank → AE D) ∈ V := by
    have : (⟨0, smul_zero _⟩ : {t : Fin A.rank → AE D // cA D ε • t = t}) ∈ Subtype.val ⁻¹' V := by
      rw [hVe]
      have e : K ⟨0, smul_zero _⟩ = 1 := isK_unique (hKk _) (by
        have : iA (A := A) (B := B) ι 0 = 0 := Matrix.mulVec_zero _
        rw [this]; exact isK_zero _)
      simp [e]
    exact this
  obtain ⟨C, hC, hCm⟩ := GlobalTheory.PosLinVec.annihilator_subset_compact D ψ hψ ε hε A d.θ d.θ_ne V (hV.mem_nhds h0)
  have hcl : IsClosed {t : Fin A.rank → AE D | ε • t = t} := isClosed_eq (continuous_const_smul ε) continuous_id
  have hC' : IsCompact ((Subtype.val : {t : Fin A.rank → AE D // ε • t = t} → _) ⁻¹' C) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hC
  refine HasCompactSupport.intro (hC'.image (f := fun t => (⟨K₀ t, hmem t⟩ : d.Ex ε j.succ))
    (hK₀.subtype_mk _)) fun u hu => ?_
  by_contra hne
  obtain ⟨t₀, ht₀, hu₀⟩ := (GlobalTheory.RootExch.ExStruct.mem_Ex_iff D A B ι d ε hε _ _).1 u.2
  refine hu ⟨⟨t₀, ht₀⟩, hCm t₀ ht₀ fun t htV ht => ?_, Subtype.ext (isK_unique (hK₀k _) hu₀)⟩
  obtain ⟨k1, k2⟩ := GlobalTheory.T.unitaryRootExchange_mirror_identity D A B ι d ψ ε hε j t₀ t u (K ⟨t, ht⟩) ht₀ ht hu₀ (hKk _)
  have e1 := exL_left d ψ ε m h2 (j.1 + 2) _ l hl _ k2 (u * g)
  have hn : (GfC B).Normal := MonoidHom.normal_ker _
  have hU' : g⁻¹ * K ⟨t, ht⟩ * g ∈ U := by
    have : (⟨t, ht⟩ : {t : Fin A.rank → AE D // cA D ε • t = t}) ∈ Subtype.val ⁻¹' V := htV
    rw [hVe] at this
    exact this
  have e2 := hk _ hU' (hn.conj_mem' _ (mem_GfC hε k1) g) (u * g)
  have e3 : (u : GA D B) * g * (g⁻¹ * K ⟨t, ht⟩ * g) = u * K ⟨t, ht⟩ * (u : GA D B)⁻¹ * (u * g) := by
    simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left]
  rw [e3, e1] at e2
  exact mul_right_cancel₀ hne (e2.trans (one_mul _).symm)

theorem exL_smul (d : BesselDatum A B ι) (ε : AE D) (m) (l) (c : ℂ) (β : GA D B → ℂ) :
    exL d ε m l (c • β) = c • exL d ε m l β := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    funext g
    show ∫ u, exL d ε m l (c • β) ((u : GA D B) * g) ∂(m i) = c * ∫ u, exL d ε m l β ((u : GA D B) * g) ∂(m i)
    rw [ih, ← integral_const_mul]
    rfl

theorem exL_add (d : BesselDatum A B ι) {ψ} (hψ : IsStdChar D ψ (-1)) {ε : AE D} (hε : IsSplitIdem D ε) (m)
    (hm : ∀ i, (m i).IsHaarMeasure) {β β' : GA D B → ℂ} (h1 : Lvl β) (h2 : Eqv d ψ ε β) (h1' : Lvl β')
    (h2' : Eqv d ψ ε β') (l : List (Fin (d.ρ + 1))) (hl : ∀ j ∈ l, 1 ≤ j.1) (hs : l.Pairwise (· < ·)) :
    exL d ε m l (β + β') = exL d ε m l β + exL d ε m l β' := by
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  induction l with
  | nil => rfl
  | cons i l ih =>
    funext g
    show ∫ u, exL d ε m l (β + β') ((u : GA D B) * g) ∂(m i) =
      ∫ u, exL d ε m l β ((u : GA D B) * g) ∂(m i) + ∫ u, exL d ε m l β' ((u : GA D B) * g) ∂(m i)
    have hi := hl i List.mem_cons_self
    have hj : ∀ j ∈ l, i.1 + 1 ≤ j.1 := fun j hj => (List.pairwise_cons.1 hs).1 j hj
    obtain ⟨a1, a2⟩ := exch_finite d hψ hε m h1 h2 i hi l hj g
    obtain ⟨b1, b2⟩ := exch_finite d hψ hε m h1' h2' i hi l hj g
    haveI := hm i
    rw [ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) (List.pairwise_cons.1 hs).2,
      ← integral_add (a1.continuous.integrable_of_hasCompactSupport a2) (b1.continuous.integrable_of_hasCompactSupport b2)]
    rfl

theorem lvl_moveL (P : PosDatum A B ι) (l) {β : GA D B → ℂ} (h : Lvl β) : Lvl (moveL P l β) := by
  induction l with
  | nil => exact h
  | cons a l ih => exact lvl_exL P.bes (P.ε a) (P.m a) _ ih

theorem eqv_moveL (P : PosDatum A B ι) (ψ) {ε : AE D} (l : List (Fin P.n))
    (hl : ∀ a ∈ l, (ε + cA D ε) * (P.ε a + cA D (P.ε a)) = 0) {β : GA D B → ℂ} (h : Eqv P.bes ψ ε β) :
    Eqv P.bes ψ ε (moveL P l β) := by
  induction l with
  | nil => exact h
  | cons a l ih =>
    exact eqv_exL P.bes ψ (hl a List.mem_cons_self) (P.m a) _ (ih fun b hb => hl b (List.mem_cons_of_mem _ hb))

theorem moveL_smul (P : PosDatum A B ι) (l) (c : ℂ) (β : GA D B → ℂ) : moveL P l (c • β) = c • moveL P l β := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show toPosF P.bes (P.ε a) (P.m a) (P.p a) (moveL P l (c • β)) = c • toPosF P.bes (P.ε a) (P.m a) (P.p a) (moveL P l β)
    rw [ih]
    exact exL_smul P.bes (P.ε a) (P.m a) _ c _

theorem moveL_add (P : PosDatum A B ι) {ψ} (hψ : IsStdChar D ψ (-1)) {β β' : GA D B → ℂ} (h1 : Lvl β)
    (h2 : ∀ ε, Eqv P.bes ψ ε β) (h1' : Lvl β') (h2' : ∀ ε, Eqv P.bes ψ ε β') (l : List (Fin P.n)) (hl : l.Nodup) :
    moveL P l (β + β') = moveL P l β + moveL P l β' := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show toPosF P.bes (P.ε a) (P.m a) (P.p a) (moveL P l (β + β')) =
      toPosF P.bes (P.ε a) (P.m a) (P.p a) (moveL P l β) + toPosF P.bes (P.ε a) (P.m a) (P.p a) (moveL P l β')
    obtain ⟨ha, hl'⟩ := List.nodup_cons.1 hl
    have hap : ∀ b ∈ l, (P.ε a + cA D (P.ε a)) * (P.ε b + cA D (P.ε b)) = 0 := fun b hb =>
      P.apart a b fun e => ha (e ▸ hb)
    rw [ih hl']
    refine exL_add P.bes hψ (P.split a) (P.m a) (P.haar a) (lvl_moveL P l h1) (eqv_moveL P ψ l hap (h2 _))
      (lvl_moveL P l h1') (eqv_moveL P ψ l hap (h2' _)) _ (fun j hj => ?_) ((List.pairwise_lt_finRange _).filter _)
    exact (P.one_le a).trans (of_decide_eq_true (List.mem_filter.1 hj).2)

def perF (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (GA D A)) (𝓕 : Set (GA D A))
    (ν : Measure d.N) (𝓝 : Set d.N) (s : GA D A → GA D B) (φ : GA D A → ℂ) (F : GA D B → ℂ) : GA D B → ℂ :=
  fun g => d.period ψ μ 𝓕 ν 𝓝 s φ (rTr B g F)

theorem coeff_rTr (d : BesselDatum A B ι) (ψ ν 𝓝) (F : GA D B → ℂ) (g x : GA D B) :
    d.coeff ψ ν 𝓝 (rTr B g F) x = d.coeff ψ ν 𝓝 F (x * g) := by
  simp only [BesselDatum.coeff, rTr, mul_assoc]

theorem perF_apply (d : BesselDatum A B ι) (ψ μ 𝓕 ν 𝓝 s φ) (F : GA D B → ℂ) (g) :
    perF d ψ μ 𝓕 ν 𝓝 s φ F g = ∫ h in 𝓕, φ h * d.coeff ψ ν 𝓝 F (s h * g) ∂μ := by
  simp only [perF, BesselDatum.period, coeff_rTr]

theorem period_eq (P : PosDatum A B ι) (ψ μ 𝓕 ν 𝓝 s φ) (F : GA D B → ℂ) :
    (fun g => P.period ψ μ 𝓕 ν 𝓝 s φ (rTr B g F)) = moveL P (List.finRange P.n) (perF P.bes ψ μ 𝓕 ν 𝓝 s φ F) :=
  move_rTr P _ F

theorem period_eq' (P : PosDatum A B ι) (ψ μ 𝓕 ν 𝓝 s φ) (F : GA D B → ℂ) :
    P.period ψ μ 𝓕 ν 𝓝 s φ F = moveL P (List.finRange P.n) (perF P.bes ψ μ 𝓕 ν 𝓝 s φ F) 1 := by
  rw [← period_eq]
  simp only [rTr_one]

theorem lvl_perF (d : BesselDatum A B ι) (ψ μ 𝓕 ν 𝓝 s φ) {F : GA D B → ℂ} (hF : IsAutFun B F) :
    Lvl (perF d ψ μ 𝓕 ν 𝓝 s φ F) := by
  obtain ⟨U, hU, hk⟩ := hF.level
  refine ⟨U, hU, fun k k1 k2 g => ?_⟩
  have : rTr B (g * k) F = rTr B g F := funext fun x => by simp only [rTr, ← mul_assoc, hk k k1 k2]
  simp only [perF, this]

theorem eqv_perF (d : BesselDatum A B ι) {ψ} (hψ : IsStdChar D ψ (-1)) (μ 𝓕) {ν 𝓝} (hν : d.IsUnitPair ν 𝓝) {s}
    (hs : ∀ h, EmbRel B A ι (s h) h) (φ) {F : GA D B → ℂ} (hF : IsAutFun B F) (ε) :
    Eqv d ψ ε (perF d ψ μ 𝓕 ν 𝓝 s φ F) := by
  intro n hn _ g
  rw [perF_apply, perF_apply, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  show φ h * d.coeff ψ ν 𝓝 F (s h * (n * g)) = _ * (φ h * d.coeff ψ ν 𝓝 F (s h * g))
  have e : s h * (n * g) = (s h * n * (s h)⁻¹) * (s h * g) := by simp only [mul_assoc, inv_mul_cancel_left]
  have e2 := GlobalTheory.CoeffRational.psiN_conj d ψ (hs h) (s h * n * (s h)⁻¹)
  have e3 : (s h)⁻¹ * (s h * n * (s h)⁻¹) * s h = n := by group
  rw [e3] at e2
  rw [e, (GlobalTheory.Mem.BesselCoeffIndep.coeff_indep_and_equivariant D A B ι d ψ hψ F hF.left ν 𝓝 hν).2 _
    (GlobalTheory.BesselConvDefinite.conj_mem_N d (hs h) hn), ← e2]
  ring

theorem exchangeFinite (D : D7) : ExchangeFinite D := by
  intro A B ι P ψ hψ _ μ 𝓕 _ ν 𝓝 hν s hs φ F _ hF _ ε hε hap m _ i hi
  have e : (fun u : P.bes.Ex ε i => P.bes.toPos ε m (i.1 + 1) (P.period ψ μ 𝓕 ν 𝓝 s φ) (rTr B (u : GA D B) F)) =
      fun u : P.bes.Ex ε i => exL P.bes ε m ((List.finRange (P.bes.ρ + 1)).filter fun j => decide (i.1 + 1 ≤ j.1))
        (moveL P (List.finRange P.n) (perF P.bes ψ μ 𝓕 ν 𝓝 s φ F)) ((u : GA D B) * 1) := by
    funext u
    rw [mul_one, ← period_eq]
    exact congrFun (toPos_rTr P.bes ε m (i.1 + 1) _ F) u
  rw [e]
  exact exch_finite P.bes hψ hε m (lvl_moveL P _ (lvl_perF _ _ _ _ _ _ _ _ hF))
    (eqv_moveL P ψ _ (fun a _ => hap a) (eqv_perF _ hψ μ 𝓕 hν hs φ hF ε)) i hi _
    (fun j hj => of_decide_eq_true (List.mem_filter.1 hj).2) 1

theorem isAutFun_star {φ : GA D A → ℂ} (h : IsAutFun A φ) : IsAutFun A fun g => star (φ g) := by
  obtain ⟨U, hU, hk⟩ := h.level
  exact ⟨fun γ hγ g => by rw [h.left γ hγ], ⟨U, hU, fun k k1 k2 g => by rw [hk k k1 k2]⟩, h.cont.star⟩

theorem perF_indep (d : BesselDatum A B ι) {ψ} (hψ : IsStdChar D ψ (-1)) (hA : A.SigOK) {μ 𝓕 μ' 𝓕'}
    (hμ : IsVolPair D A μ 𝓕) (hμ' : IsVolPair D A μ' 𝓕') {ν 𝓝 ν' 𝓝'} (hν : d.IsUnitPair ν 𝓝)
    (hν' : d.IsUnitPair ν' 𝓝') {s s'} (hs : ∀ h, EmbRel B A ι (s h) h) (hs' : ∀ h, EmbRel B A ι (s' h) h)
    {φ F} (hφ : IsAutFun A φ) (hF : IsAutFun B F) :
    perF d ψ μ' 𝓕' ν' 𝓝' s' φ F = perF d ψ μ 𝓕 ν 𝓝 s φ F := by
  obtain ⟨s₀, -, hrel, hQ⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι d.isom
  obtain rfl : s = s₀ := funext fun h => (hrel h _).1 (hs h)
  obtain rfl : s' = s₀ := funext fun h => (hrel h _).1 (hs' h)
  obtain rfl : μ' = μ := (GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG D A hA).unique hμ'.1 hμ.1
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  have := hμ.1.1
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ A)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ A) μ'
  funext g
  rw [perF_apply, perF_apply,
    (GlobalTheory.Mem.BesselCoeffIndep.coeff_indep_and_equivariant D A B ι d ψ hψ F hF.left ν 𝓝 hν).1 ν' 𝓝' hν']
  refine hμ'.2.setIntegral_eq hμ.2 fun γ x => ?_
  show φ (γ.1 * x) * d.coeff ψ ν 𝓝 F (s₀ (γ.1 * x) * g) = _
  rw [hφ.left _ γ.2, map_mul, mul_assoc,
    GlobalTheory.CoeffRational.coeff_rational D A B ι d ψ hψ F hF.left ν 𝓝 hν _ _ (hs γ.1) (hQ _ γ.2)]

theorem perF_smul_left (d : BesselDatum A B ι) (ψ μ 𝓕 ν 𝓝 s) (c : ℂ) (φ : GA D A → ℂ) (F : GA D B → ℂ) :
    perF d ψ μ 𝓕 ν 𝓝 s (c • φ) F = c • perF d ψ μ 𝓕 ν 𝓝 s φ F := by
  funext g
  simp only [perF_apply, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem perF_smul_right (d : BesselDatum A B ι) (ψ μ 𝓕 ν 𝓝 s) (c : ℂ) (φ : GA D A → ℂ) (F : GA D B → ℂ) :
    perF d ψ μ 𝓕 ν 𝓝 s φ (c • F) = c • perF d ψ μ 𝓕 ν 𝓝 s φ F := by
  funext g
  have e : ∀ x, d.coeff ψ ν 𝓝 (c • F) x = c * d.coeff ψ ν 𝓝 F x := fun x => by
    simp only [BesselDatum.coeff, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  simp only [perF_apply, e, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]

theorem perF_add_left (d : BesselDatum A B ι) {ψ μ 𝓕 ν 𝓝 s} {φ φ' : GA D A → ℂ} {F : GA D B → ℂ}
    (h : d.Converges ψ μ 𝓕 ν 𝓝 s φ F) (h' : d.Converges ψ μ 𝓕 ν 𝓝 s φ' F) :
    perF d ψ μ 𝓕 ν 𝓝 s (φ + φ') F = perF d ψ μ 𝓕 ν 𝓝 s φ F + perF d ψ μ 𝓕 ν 𝓝 s φ' F := by
  funext g
  simp only [perF, BesselDatum.period, Pi.add_apply, add_mul]
  exact integral_add (h g) (h' g)

theorem perF_add_right (d : BesselDatum A B ι) {ψ} (hψ : IsCharAF D.host.F ψ) {μ 𝓕 ν 𝓝 s} (hν : d.IsUnitPair ν 𝓝)
    {φ : GA D A → ℂ} {F F' : GA D B → ℂ} (hF : IsAutFun B F) (hF' : IsAutFun B F')
    (h : d.Converges ψ μ 𝓕 ν 𝓝 s φ F) (h' : d.Converges ψ μ 𝓕 ν 𝓝 s φ F') :
    perF d ψ μ 𝓕 ν 𝓝 s φ (F + F') = perF d ψ μ 𝓕 ν 𝓝 s φ F + perF d ψ μ 𝓕 ν 𝓝 s φ F' := by
  funext g
  have e : ∀ x, d.coeff ψ ν 𝓝 (F + F') x = d.coeff ψ ν 𝓝 F x + d.coeff ψ ν 𝓝 F' x := fun x => by
    simp only [BesselDatum.coeff, Pi.add_apply, add_mul]
    exact integral_add
      ((GlobalTheory.RootExch.CoefInt.coeff_integrable_continuous D A B ι d ψ hψ ν 𝓝 hν F hF.cont hF.left).1 x)
      ((GlobalTheory.RootExch.CoefInt.coeff_integrable_continuous D A B ι d ψ hψ ν 𝓝 hν F' hF'.cont hF'.left).1 x)
  have k := h g
  have k' := h' g
  simp only [coeff_rTr] at k k'
  simp only [perF_apply, e, Pi.add_apply, mul_add]
  exact integral_add k k'

theorem posLin : ∀ D : D7, PosLin D := by
  intro D
  refine ⟨GlobalTheory.BesselConvDefinite.convergesDef D, exchangeFinite D, fun θ hθ ψ hψ A B ι P hA hd => ?_⟩
  by_cases hex : ∃ μ 𝓕 ν 𝓝, ∃ s : GA D A → GA D B, IsVolPair D A μ 𝓕 ∧ P.bes.IsUnitPair ν 𝓝 ∧ ∀ h, EmbRel B A ι (s h) h
  swap
  · exact ⟨0, fun μ 𝓕 hμ ν 𝓝 hν s hs => absurd ⟨μ, 𝓕, ν, 𝓝, s, hμ, hν, hs⟩ hex⟩
  obtain ⟨μ, 𝓕, ν, 𝓝, s, hμ, hν, hs⟩ := hex
  have a1 : ∀ φ : AFs θ A, IsAutFun A fun g => star (φ.1 g) := fun φ =>
    isAutFun_star ((GlobalTheory.Mem.AutSpace.mem_AFs_iff D θ hθ A φ.1).1 φ.2).toIsAutFun
  have a2 : ∀ F : CuspS θ B, IsAutFun B F.1 := fun F =>
    ((GlobalTheory.Mem.AutSpace.mem_AFs_iff D θ hθ B F.1).1 (CuspS_le θ B F.2)).toIsAutFun
  have cv : ∀ (φ : AFs θ A) (F : CuspS θ B), P.bes.Converges ψ μ 𝓕 ν 𝓝 s (fun g => star (φ.1 g)) F.1 := fun φ F =>
    GlobalTheory.BesselConvDefinite.convergesDef D A B ι P.bes ψ hψ.1 hA hd μ 𝓕 hμ ν 𝓝 hν s hs _ _ (a1 φ) (a2 F)
  have ad : ∀ φ φ' (F F' : CuspS θ B), moveL P (List.finRange P.n)
      (perF P.bes ψ μ 𝓕 ν 𝓝 s φ F.1 + perF P.bes ψ μ 𝓕 ν 𝓝 s φ' F'.1) =
      moveL P (List.finRange P.n) (perF P.bes ψ μ 𝓕 ν 𝓝 s φ F.1) +
        moveL P (List.finRange P.n) (perF P.bes ψ μ 𝓕 ν 𝓝 s φ' F'.1) := fun φ φ' F F' =>
    moveL_add P hψ (lvl_perF _ _ _ _ _ _ _ _ (a2 F)) (eqv_perF _ hψ μ 𝓕 hν hs φ (a2 F))
      (lvl_perF _ _ _ _ _ _ _ _ (a2 F')) (eqv_perF _ hψ μ 𝓕 hν hs φ' (a2 F')) _ (List.nodup_finRange _)
  refine ⟨LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun (φ : AFs θ A) (F : CuspS θ B) =>
      moveL P (List.finRange P.n) (perF P.bes ψ μ 𝓕 ν 𝓝 s (fun g => star (φ.1 g)) F.1) 1)
    (fun φ φ' F => ?_) (fun c φ F => ?_) (fun φ F F' => ?_) (fun c φ F => ?_),
    fun μ' 𝓕' hμ' ν' 𝓝' hν' s' hs' φ F => ?_⟩
  · have e : (fun g => star ((φ + φ').1 g)) = (fun g => star (φ.1 g)) + fun g => star (φ'.1 g) :=
      funext fun g => star_add _ _
    rw [e, perF_add_left _ (cv φ F) (cv φ' F), ad]
    rfl
  · have e : (fun g => star ((c • φ).1 g)) = starRingEnd ℂ c • fun g => star (φ.1 g) :=
      funext fun g => star_mul' _ _
    rw [e, perF_smul_left, moveL_smul]
    rfl
  · rw [Submodule.coe_add, perF_add_right _ hψ.1 hν (a2 F) (a2 F') (cv φ F) (cv φ F'), ad]
    rfl
  · rw [Submodule.coe_smul, perF_smul_right, moveL_smul]
    rfl
  · rw [period_eq', perF_indep P.bes hψ hA hμ hμ' hν hν' hs hs' (a1 φ) (a2 F)]
    rfl

end GlobalTheory.RootExch.PosLinear

end
