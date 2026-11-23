import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsOpenSameModel
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PeriodEqTriangularOrthonormal
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ImNegOfFramePeriodVector
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsHolomorphicPeriodsAdapted
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularFrameChangeOfTriangularPeriod
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPeriodMulVec
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCountableFlagSpaceAtlasStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsComponentOfModelChartsStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCountableHolomorphicFamiliesSmoothStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PeriodCoordinatesFramesLiftTendstoStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Formalism.LocalToGlobal.ProjectiveLattices.CompOrd
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain

open NumberField Topology Filter ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.Reg
open scoped Matrix

noncomputable section

namespace GlobalTheory.GenericFrames

theorem isMeagre_of_isSigmaCompact {X : Type} [TopologicalSpace X] [T2Space X] {s : Set X} (hs : IsSigmaCompact s)
    (hi : interior s = ∅) : IsMeagre s := by
  obtain ⟨K, hK, rfl⟩ := hs
  refine isMeagre_iUnion fun n => IsNowhereDense.isMeagre ?_
  rw [(hK n).isClosed.isNowhereDense_iff]
  exact Set.subset_eq_empty (interior_mono (Set.subset_iUnion K n)) hi

theorem exists_seq_of_isMeagre {X : Type} [TopologicalSpace X] {s : Set X} (hs : IsMeagre s) :
    ∃ S : ℕ → Set X, (∀ n, IsClosed (S n) ∧ interior (S n) = ∅) ∧ ∀ x ∈ s, ∃ n, x ∈ S n := by
  obtain ⟨T, hT, hc, hsT⟩ := isMeagre_iff_countable_union_isNowhereDense.1 hs
  obtain ⟨f, hf⟩ := (hc.insert ∅).exists_eq_range (Set.insert_nonempty _ _)
  refine ⟨fun n => closure (f n), fun n => ⟨isClosed_closure, ?_⟩, fun x hx => ?_⟩
  · have : f n ∈ insert ∅ T := hf ▸ Set.mem_range_self n
    rcases this with h | h
    · simp [h]
    · exact hT _ h
  · obtain ⟨t, ht, hxt⟩ := hsT hx
    obtain ⟨n, rfl⟩ : t ∈ Set.range f := hf ▸ Set.mem_insert_of_mem _ ht
    exact ⟨n, subset_closure hxt⟩

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def pc (x : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) (a : Fin r) : ℂ :=
  if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat x τ) a) (Data.emb τ.1 v) else ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 v) a

theorem continuous_pc (v : Fin r → E) (τ : X.Ψ) (a : Fin r) : Continuous fun x : X.dom => pc X x.1 v τ a := by
  have hm : Continuous fun x : X.dom => mat x.1 τ := (continuous_apply τ).comp continuous_subtype_val
  unfold pc
  split_ifs
  · unfold hermC col
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      ((hm.matrix_elem i a).mul continuous_const).mul continuous_const
  · have h3 : Continuous fun x : X.dom => (mat x.1 τ)⁻¹ := by
      simp only [Matrix.inv_def, Ring.inverse_eq_inv']
      exact (hm.matrix_det.inv₀ fun x => (x.2 τ).1).smul hm.matrix_adjugate
    exact (continuous_apply a).comp (h3.matrix_mulVec continuous_const)

variable {g m : ℕ} (idx : Fin g ≃ X.Ψ × Fin r) {La : Type} (φ : La → Fin r → E) (T : Fin g → Fin g → Prop)

def Rel (x : Frame X.Ψ r) (P : La → Fin g → ℂ) (h : Matrix (Fin g) (Fin g) ℂ) : Prop :=
  (∀ j j', h j j' ≠ 0 → T j j') ∧ ∀ a j, pc X x (φ a) (idx j).1 (idx j).2 = (h *ᵥ P a) j

variable {B : Set (Fin m → ℂ)} (hB : IsOpen B) (P : (Fin m → ℂ) → La → Fin g → ℂ)
  (hP : ∀ a, ContinuousOn (fun b => P b a) B) (f : (Fin m → ℂ) → ℂ)

include hB hP in
theorem isSigmaCompact_rel (hf : ContinuousOn f B) :
    IsSigmaCompact {x | x ∈ X.dom ∧ ∃ b ∈ B, f b = 0 ∧ ∃ h, Rel X idx φ T x (P b) h} := by
  haveI : LocallyCompactSpace X.dom := (FourierCoefficientDomain.isOpen_dom X).locallyCompactSpace
  haveI : LocallyCompactSpace B := hB.locallyCompactSpace
  let W : Set (X.dom × B × (Fin g → Fin g → ℂ)) := {p | f p.2.1 = 0 ∧ Rel X idx φ T p.1 (P p.2.1) p.2.2}
  have hW : IsClosed W := by
    have h1 : Continuous fun p : X.dom × B × (Fin g → Fin g → ℂ) => f p.2.1 :=
      (continuousOn_iff_continuous_restrict.1 hf).comp continuous_snd.fst
    simp only [W, Rel]
    refine (isClosed_eq h1 continuous_const).and (IsClosed.and ?_ ?_)
    · simp only [Set.setOf_forall, ne_eq, not_imp_comm (a := _ = (0 : ℂ))]
      refine isClosed_iInter fun j => isClosed_iInter fun j' => isClosed_iInter fun _ => ?_
      exact isClosed_eq (by fun_prop) continuous_const
    · simp only [Set.setOf_forall]
      refine isClosed_iInter fun a => isClosed_iInter fun j => isClosed_eq
        ((continuous_pc X _ _ _).comp continuous_fst) ?_
      have h2 : Continuous fun p : X.dom × B × (Fin g → Fin g → ℂ) => P p.2.1 a :=
        (continuousOn_iff_continuous_restrict.1 (hP a)).comp continuous_snd.fst
      have h3 : Continuous fun p : X.dom × B × (Fin g → Fin g → ℂ) => (p.2.2 : Matrix (Fin g) (Fin g) ℂ) :=
        continuous_snd.snd
      exact (continuous_apply j).comp (h3.matrix_mulVec h2)
  have := (isSigmaCompact_univ.of_isClosed_subset hW (Set.subset_univ _)).image
    (f := fun p => (p.1 : Frame X.Ψ r)) (by fun_prop)
  convert this using 1
  ext x
  constructor
  · rintro ⟨hx, b, hb, h0, h, hh⟩
    exact ⟨(⟨x, hx⟩, ⟨b, hb⟩, h), ⟨h0, hh⟩, rfl⟩
  · rintro ⟨⟨x, b, h⟩, ⟨h0, hh⟩, rfl⟩
    exact ⟨x.2, b, b.2, h0, h, hh⟩

include hB hP in
theorem interior_rel (hφ : ∀ v ∈ X.Λ, ∃ a, φ a = v) (hne : ∀ b ∈ B, ∃ᶠ b' in 𝓝 b, f b' ≠ 0)
    (honto : ∀ x₀ ∈ X.dom, ∀ b₀ ∈ B, ∀ h, Rel X idx φ T x₀ (P b₀) h → ∀ b ∈ B, ∃ x ∈ X.dom, Rel X idx φ T x (P b) h)
    (hmono : ∀ x ∈ X.dom, ∀ b ∈ B, ∀ b' ∈ B, ∀ h h', Rel X idx φ T x (P b) h → Rel X idx φ T x (P b') h' →
      f b = f b') :
    interior {x | x ∈ X.dom ∧ ∃ b ∈ B, f b = 0 ∧ ∃ h, Rel X idx φ T x (P b) h} = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x₀ hx₀ => ?_
  have hV := mem_interior_iff_mem_nhds.1 hx₀
  obtain ⟨hx₀d, b₀, hb₀, -, h, hh⟩ := interior_subset hx₀
  choose! x₁ hx₁ hr₁ using honto x₀ hx₀d b₀ hb₀ h hh
  have hBn : ∀ᶠ b in 𝓝 b₀, b ∈ B := hB.mem_nhds hb₀
  have key := GlobalTheory.T.period_coordinates_frames_lift_tendsto E r X _ (𝓝 b₀) x₀ x₁ hx₀d (hBn.mono hx₁) (fun v hv τ i => by
    obtain ⟨a, rfl⟩ := hφ v hv
    obtain ⟨j, hj⟩ := idx.surjective (τ, i)
    obtain ⟨rfl, rfl⟩ : τ = (idx j).1 ∧ i = (idx j).2 := by rw [hj]; exact ⟨rfl, rfl⟩
    change Tendsto (fun b => pc X (x₁ b) (φ a) _ _) _ (𝓝 (pc X x₀ (φ a) _ _))
    rw [hh.2]
    have hc : ContinuousAt (fun b => (h *ᵥ P b a) j) b₀ := by
      have h1 : Continuous fun w : Fin g → ℂ => (h *ᵥ w) j :=
        (continuous_apply j).comp (continuous_const.matrix_mulVec continuous_id)
      exact h1.continuousAt.comp ((hP a).continuousAt hBn)
    exact hc.tendsto.congr' (hBn.mono fun b hb => ((hr₁ b hb).2 a j).symm)) _ hV
  obtain ⟨b, hb0, hb, x, ⟨hx, b', hb', h0, h', hh'⟩, hxx⟩ := ((hne b₀ hb₀).and_eventually (hBn.and key)).exists
  refine hb0 ((hmono x hx b hb b' hb' h h' ⟨hh.1, fun a j => ?_⟩ hh').trans h0)
  exact (hxx _ _ _).trans ((hr₁ b hb).2 a j)

theorem isMeagre_translates {s : Set (Frame X.Ψ r)} (hs : IsSigmaCompact s) (hi : interior s = ∅) :
    IsMeagre (⋃ γ : GL (Fin r) E, lact γ '' s) := by
  refine isMeagre_iUnion fun γ => isMeagre_of_isSigmaCompact (hs.image (AR.Up.PairUnfoldPf.lact_cont X γ)) ?_
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  have h1 : lact γ⁻¹ x ∈ interior s := by
    refine mem_interior.2 ⟨lact γ ⁻¹' interior (lact γ '' s), fun y hy => ?_,
      isOpen_interior.preimage (AR.Up.PairUnfoldPf.lact_cont X γ), ?_⟩
    · obtain ⟨z, hz, e⟩ := interior_subset hy
      have := congrArg (lact γ⁻¹) e
      rw [AR.Up.PairUnfoldPf.lact_inv_lact, AR.Up.PairUnfoldPf.lact_inv_lact] at this
      exact this ▸ hz
    · rw [Set.mem_preimage, AR.Up.PairUnfoldPf.lact_lact_inv]
      exact hx
  rw [hi] at h1
  exact h1

end Frames

section Dictionary

open Formalism.L2.PjFree in

theorem dictionary {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} (c : Coeff l) (σ : c.F →+* ℂ) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (D : Datum H) {r : ℕ} (X : Data E r) (φ : D.La ≃ₗ[𝓞 E] X.Λ) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hp : D.p = Dw.p)
    (hq : D.q = Dw.q) (hr : r = Dw.p + Dw.q) (hp0 : X.p0 = Dw.q)
    (hty : ∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0)
    (hef : ∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b)))
    (hneg : r ≠ 0 → ∀ τ ∈ X.Ψ, (τ X.ξ0).im < 0) :
    ∃ idx : Fin g ≃ X.Ψ × Fin r,
      (∀ (x : Frame X.Ψ r) (v : Fin r → E) j,
        Formalism.L2.PjFree.perFr X x v (Formalism.L2.PjFree.relab c σ (e j).1) (e j).2 = pc X x v (idx j).1 (idx j).2) ∧
      (∀ b ∈ Bor X.Ψ r, ∀ j j', PerBor.moveMat X.p0 idx b j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) ∧
      ∀ P : D.La →+ (Fin g → ℂ), IsPeriod D (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P →
        ∃ x ∈ X.dom, ∀ a j, pc X x (φ a : Fin r → E) (idx j).1 (idx j).2 = P a j := by
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv X.Ψ X.cmType Dw.p Dw.q r hr (Formalism.L2.PjFree.relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  obtain ⟨idx, hi⟩ : ∃ idx : Fin g ≃ X.Ψ × Fin r, ∀ j,
      (Formalism.L2.PjFree.relab c σ (e j).1 ∈ X.Ψ ∧ (idx j).1.1 = Formalism.L2.PjFree.relab c σ (e j).1 ∧
        ((idx j).2 : ℕ) = Dw.q + (e j).2) ∨
      (Formalism.L2.PjFree.relab c σ (e j).1 ∉ X.Ψ ∧
        (idx j).1.1 = ComplexEmbedding.conjugate (Formalism.L2.PjFree.relab c σ (e j).1) ∧
        ((idx j).2 : ℕ) = Dw.q - 1 - (e j).2 ∧ ((e j).2 : ℕ) < Dw.q) := ⟨e.trans f, fun j => hf (e j)⟩
  have hty' : ∀ j, Formalism.L2.PjFree.relab c σ (e j).1 = if ((idx j).2 : ℕ) < D.q then
      ComplexEmbedding.conjugate (idx j).1.1 else (idx j).1.1 := by
    intro j
    rw [hq]
    rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
    · rw [if_neg (by omega), b]
    · rw [if_pos (by omega), b, hcc]
  have hqq : D.q = X.p0 := hq.trans hp0.symm
  refine ⟨idx, fun x v j => ?_, fun b hb j j' hne => ?_, fun P hP => ?_⟩
  · have h := hi j
    unfold pc
    generalize idx j = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rw [← hp0] at h
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold Formalism.L2.PjFree.perFr
      rw [dif_pos a, dif_pos hn]
    · rw [if_pos (by omega)]
      unfold Formalism.L2.PjFree.perFr
      rw [dif_neg a, dif_pos (show conjEmb (Formalism.L2.PjFree.relab c σ (e j).1) ∈ X.Ψ from hτ), dif_pos hn]
      rfl
  · obtain ⟨h1, h2⟩ := PerBor.moveMat_support _ idx hb j j' hne
    rw [← hqq] at h2
    have t1 := hty' j
    have t2 := hty' j'
    have c1 := hi j
    have c2 := hi j'
    by_cases hj : ((idx j).2 : ℕ) < D.q
    · rw [if_pos hj] at h2 t1
      have hj' : ((idx j').2 : ℕ) < D.q := by omega
      rw [if_pos hj'] at t2
      refine ⟨hbij.1 (by rw [t1, t2, h1]), ?_⟩
      rcases c1 with ⟨-, -, c1⟩ | ⟨-, -, c1, d1⟩ <;> rcases c2 with ⟨-, -, c2⟩ | ⟨-, -, c2, d2⟩ <;> omega
    · rw [if_neg hj] at h2 t1
      have hj' : ¬ ((idx j').2 : ℕ) < D.q := by omega
      rw [if_neg hj'] at t2
      refine ⟨hbij.1 (by rw [t1, t2, h1]), ?_⟩
      rcases c1 with ⟨-, -, c1⟩ | ⟨-, -, c1, d1⟩ <;> rcases c2 with ⟨-, -, c2⟩ | ⟨-, -, c2, d2⟩ <;> omega
  · rcases eq_or_ne r 0 with hr0 | hr0
    · subst hr0
      haveI : IsEmpty (Fin g) := idx.isEmpty
      obtain ⟨x, hx⟩ := (GlobalTheory.frames_isConnected E 0 X).nonempty
      exact ⟨x, hx, fun _ j => isEmptyElim j⟩
    have hpos : ∀ τ ∈ X.Ψ, 0 < (τ (-X.ξ0)).im := by
      intro τ hτ
      have := hneg hr0 τ hτ
      rw [map_neg, Complex.neg_im]
      linarith
    have hξ : cc (-X.ξ0) = -(-X.ξ0) := by
      have h := X.ξ0_im
      unfold cc at h ⊢
      rw [map_neg, h]
    let φ' : D.La →ₗ[𝓞 E] (Fin r → E) := X.Λ.subtype.comp φ.toLinearMap
    have hrange : Set.range φ' = X.Λ := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact (φ a).2
      · intro hy
        exact ⟨φ.symm ⟨y, hy⟩, by simp [φ']⟩
    obtain ⟨x, hx, hPx⟩ := GlobalTheory.exists_frame_of_isPeriod E H D r (-X.ξ0) X.Gm φ' X.Ψ hty g idx _ hty' hξ hpos
      ⟨fun a b hab => φ.injective (Subtype.ext hab), by rw [hrange]; exact X.Λ_span, X.Gm_herm, X.Gm_det, hef⟩
      (by rw [hp, hq, hr]) P hP
    rw [hqq] at hx hPx
    exact ⟨x, hx, fun a j => (hPx a j).symm⟩

end Dictionary

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem isMeagre_family (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) {A : Type} [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) {m : ℕ}
    {B : Set (Fin m → ℂ)} (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ))
    (hB : IsOpen B) (hφ : ∀ a, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (φ b a)) B)
    (hy : ∀ b ∈ B, FrMap (φ b) yA (y b))
    (hmono : ∀ b ∈ B, ∀ b' ∈ B, ∀ t, FrBor t (y b) (y b') → φ b = φ b') (a : A)
    (hne : ∀ b ∈ B, ∃ᶠ b' in 𝓝 b, Formalism.L2.PjFree.toC (φ b' a) ≠ 0) :
    IsMeagre {x | ∃ hx : x ∈ (U.X k).dom, ∃ b ∈ B, Formalism.L2.PjFree.toC (φ b a) = 0 ∧
      ∃ t, FrBor t (U.un k ⟨x, hx⟩) (y b)} := by
  obtain ⟨hr, hty, -, hfib, -, g, e, F, ik, ψ, hef, hun⟩ := hU
  obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)
  have loc : ∀ b₀ ∈ B, ∃ B' ∈ 𝓝[B] b₀, IsMeagre {x | ∃ hx : x ∈ (U.X k).dom, ∃ b ∈ B',
      Formalism.L2.PjFree.toC (φ b a) = 0 ∧ ∃ t, FrBor t (U.un k ⟨x, hx⟩) (y b)} := by
    intro b₀ hb₀
    obtain ⟨B', k', P, hB', hb', hs, hP, hyP⟩ :=
      GlobalTheory.AdaptedPeriods.exists_holPeriods_adapted E H Dw l Xo c σ g e F A yA m B φ y hB hφ hy b₀ hb₀
    refine ⟨B', mem_nhdsWithin_of_mem_nhds (hB'.mem_nhds hb'), ?_⟩
    rcases Set.eq_empty_or_nonempty {x | ∃ hx : x ∈ (U.X k).dom, ∃ b ∈ B',
      Formalism.L2.PjFree.toC (φ b a) = 0 ∧ ∃ t, FrBor t (U.un k ⟨x, hx⟩) (y b)} with h0 | ⟨x₁, hx₁, b₁, hb₁, -, t₁, ht₁⟩
    · rw [h0]
      exact IsMeagre.empty
    obtain ⟨P₁, hP₁, hP₁', hu₁, -⟩ := hun k ⟨x₁, hx₁⟩
    obtain rfl : ik k = k' := F.disj _ _ _ _ hP₁' (hP.1 b₁ hb₁) (hu₁.symm.trans (ht₁.1.symm.trans (hyP b₁ hb₁).1))
    obtain ⟨idx, hper, hsupp, honto⟩ := dictionary c σ e _ (U.X k) (ψ k) hσ (F.sig _).1 (F.sig _).2 hr
      (hty k).1 (hty k).2 (hef k) (GlobalTheory.FrameSign.im_neg_of_isPeriod E H Dw l c σ g e _ r (U.X k) (ψ k) hσ hr
        (hty k).1 (hty k).2 (hef k) x₁ hx₁ P₁ hP₁ hP₁')
    let T : Fin g → Fin g → Prop := fun j j' => (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2
    let ρ : (F.Di (ik k)).La → Fin r → E := fun v => ψ k v
    have hbor : ∀ x (hx : x ∈ (U.X k).dom), ∀ b ∈ B', ∀ h, Rel (U.X k) idx ρ T x (P b) h →
        IsUnit h.det ∧ ∃ t, FrBor t (U.un k ⟨x, hx⟩) (y b) := by
      intro x hx b hb h hh
      obtain ⟨P₀, hP₀, hP₀', hux, hud, -⟩ := hun k ⟨x, hx⟩
      have hPS : ∀ v, P₀ v = h *ᵥ P b v := fun v => funext fun j => (hP₀ v j).trans ((hper _ _ j).trans (hh.2 v j))
      obtain ⟨t, ht, -⟩ := GlobalTheory.FrameNorm.frBor_of_triangular_period E H Dw l Xo c σ g e F _ (P b) P₀ h (y b)
        (U.un k ⟨x, hx⟩) (hP.1 b hb) hP₀' hPS hh.1 (hyP b hb).1 hux (hyP b hb).2 hud
      exact ⟨(GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F _ (P b) P₀
        (LinearEquiv.refl _ _) h (hP.1 b hb) hP₀' (fun _ _ => rfl) (fun a _ => ⟨0, by simp⟩)
        (fun a => ⟨0, by simp⟩) hPS).1, t, ht⟩
    have hPc : ∀ v, ContinuousOn (fun b => P b v) B' := fun v => (hP.2 v).continuousOn
    have h1 := isSigmaCompact_rel (U.X k) idx ρ T hB' (fun b => P b) hPc (fun b => Formalism.L2.PjFree.toC (φ b a))
      ((hφ a).continuousOn.mono hs)
    have h2 := interior_rel (U.X k) idx ρ T hB' (fun b => P b) hPc (fun b => Formalism.L2.PjFree.toC (φ b a))
      (fun v hv => ⟨(ψ k).symm ⟨v, hv⟩, by simp [ρ]⟩) (fun b hb => hne b (hs hb))
      (fun x₀ hx₀ b₀ hb₀ h hh b hb => by
        obtain ⟨P', hP', hP'e⟩ := GlobalTheory.PeriodLin.exists_period_mulVec E H _ g _ (P b) h (hP.1 b hb)
          (hbor x₀ hx₀ b₀ hb₀ h hh).1 (fun j j' hj => by rw [(hh.1 j j' hj).1])
        obtain ⟨x, hx, hxe⟩ := honto P' hP'
        exact ⟨x, hx, hh.1, fun v j => (hxe v j).trans (congrFun (hP'e v) j)⟩)
      (fun x hx b hb b' hb' h h' hh hh' => by
        obtain ⟨-, t, ht⟩ := hbor x hx b hb h hh
        obtain ⟨-, t', ht'⟩ := hbor x hx b' hb' h' hh'
        rw [hmono b (hs hb) b' (hs hb') _ (hmul _ _ _ _ _ (hinv _ _ _ ht) ht')])
    refine (isMeagre_translates (U.X k) h1 h2).mono ?_
    rintro x ⟨hx, b, hb, h0, t, ht⟩
    obtain ⟨x', hx', hxe⟩ := honto (P b) (hP.1 b hb)
    obtain ⟨-, t', ht'⟩ := hbor x' hx' b hb 1 ⟨fun j j' hj => by
      obtain rfl : j = j' := by
        by_contra hjj
        exact hj (Matrix.one_apply_ne hjj)
      exact ⟨rfl, le_rfl⟩, fun v j => by rw [Matrix.one_mulVec]; exact hxe v j⟩
    obtain ⟨γ, -, β, hβ, hxγ⟩ := (hfib k k ⟨x', hx'⟩ ⟨x, hx⟩).1 ⟨_, hmul _ _ _ _ _ ht' (hinv _ _ _ ht)⟩
    have hxγ' : x = rmul (lact γ x') β := eq_of_heq (Sigma.mk.inj hxγ).2
    refine Set.mem_iUnion.2 ⟨γ, rmul x' β, ⟨OrthogonalFrameDomain.rmul_mem_dom _ hx' hβ, b, hb, h0,
      PerBor.moveMat (U.X k).p0 idx β, hsupp β hβ, fun v j => ?_⟩, ?_⟩
    · exact congrFun (PerBor.moveMat_mulVec _ idx hβ (U.X k).Gm x' (ρ v) (P b v)
        (fun j => pc (U.X k) (rmul x' β) (ρ v) (idx j).1 (idx j).2) (fun j => (hxe v j).symm) (fun _ => rfl)) j
    · rw [hxγ', AR.Up.PairUnfoldPf.rmul_lact]
  choose! B' hB' hM using loc
  obtain ⟨s, hsB, hsc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin hB'
  refine (isMeagre_biUnion hsc fun b hb => hM b (hsB hb)).mono ?_
  rintro x ⟨hx, b, hb, h⟩
  obtain ⟨b₀, hb₀, hbb⟩ := Set.mem_iUnion₂.1 (hcov hb)
  exact Set.mem_iUnion₂.2 ⟨b₀, hb₀, hx, b, hbb, h⟩

theorem isMeagre_chart (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) {h : GenFrEx Xo c} (C : FChart h) :
    IsMeagre {x | ∃ hx : x ∈ (U.X k).dom, ∃ (ψ : C.R →ₐ[c.F] CAt σ) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ),
      FrMap ψ C.y z ∧ FrBor t z (U.un k ⟨x, hx⟩) ∧ ¬ Function.Injective ψ} := by
  classical
  obtain ⟨hL, -, -, -⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨-, -, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI := C.sm
  haveI : Countable c.F := Countable.of_equiv _ (Module.finBasis ℚ c.F).equivFun.toEquiv.symm
  haveI : Countable C.R := by
    obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType c.F C.R)
    haveI : Countable (MvPolynomial (Fin n) c.F) := Cardinal.mk_le_aleph0_iff.1
      (MvPolynomial.cardinalMk_le_max.trans (by simp))
    exact hf.countable
  rcases Set.eq_empty_or_nonempty {x | ∃ hx : x ∈ (U.X k).dom, ∃ (ψ : C.R →ₐ[c.F] CAt σ) (z : FrPt Xo c (CAt σ))
      (t : Ix Dw → (CAt σ)ˣ), FrMap ψ C.y z ∧ FrBor t z (U.un k ⟨x, hx⟩) ∧ ¬ Function.Injective ψ} with
    h0 | ⟨-, -, ψ₀, -⟩
  · rw [h0]
    exact IsMeagre.empty
  obtain ⟨ι, _, m, B, φ, hB, hφσ, hd, hcov, hne⟩ := GlobalTheory.T.exists_countable_holomorphic_families_smooth c.F C.R σ
  let φ' : ∀ i, (Fin (m i) → ℂ) → (C.R →ₐ[c.F] CAt σ) := fun i b =>
    if hb : b ∈ B i then
      { (show C.R →+* CAt σ from φ i b) with commutes' := fun a => RingHom.congr_fun (hφσ i b hb) a }
    else ψ₀
  have hφ' : ∀ i, ∀ b ∈ B i, ∀ a, Formalism.L2.PjFree.toC (φ' i b a) = φ i b a := by
    intro i b hb a
    simp only [φ', dif_pos hb]
    rfl
  choose z hz using fun i b => hL.bc _ _ (φ' i b) C.y
  have key := fun (i : ι) (a : {a : C.R // a ≠ 0}) => isMeagre_family U hσ hU k C.y (φ' i) (z i) (hB i)
    (fun a => (hd i a).congr fun b hb => hφ' i b hb a) (fun b _ => hz i b)
    (fun b _ b' _ t ht => C.mono (CAt σ) _ _ _ _ t (hz i b) (hz i b') ht) a.1
    (fun b hb => ((hne i b hb a.1 a.2).and_eventually ((hB i).mem_nhds hb)).mono fun b' hb' => by
      rw [hφ' i b' hb'.2]
      exact hb'.1)
  refine (isMeagre_iUnion fun i => isMeagre_iUnion fun a => key i a).mono ?_
  rintro x ⟨hx, ψ, w, t, hw, ht, hni⟩
  obtain ⟨i, b, hb, e⟩ := hcov (ψ.toRingHom : C.R →+* ℂ) (RingHom.ext fun a => ψ.commutes a)
  have e' : φ' i b = ψ := AlgHom.ext fun a => by
    have := hφ' i b hb a
    rw [e] at this
    exact this
  obtain rfl : w = z i b := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ ψ C.y).1 _ _ hw (e' ▸ hz i b)
  rw [injective_iff_map_eq_zero] at hni
  push Not at hni
  obtain ⟨a, ha0, ha⟩ := hni
  refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨⟨a, ha⟩, hx, b, hb, ?_, _, hinv _ _ _ ht⟩⟩
  rw [e']
  exact ha0

theorem exists_generic_of_injective {h : GenFrEx Xo c} (C : FChart h) (ψ : C.R →ₐ[c.F] CAt σ)
    (hψ : Function.Injective ψ) {z : FrPt Xo c (CAt σ)} (hz : FrMap ψ C.y z) :
    ∃ (φ : Om C.Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ),
      FrMap φ (genFr h C.Z) y' ∧ FrBor t y' z := by
  obtain ⟨hL, -, -, -⟩ := evLaws_genFr_atlas E H Dw l Xo c
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI := GlobalTheory.SupGeneric.isFractionRing_chart C
  let φ : Om C.Z →ₐ[c.F] CAt σ := IsFractionRing.liftAlgHom hψ
  have e : φ.comp C.R.val = ψ := AlgHom.ext fun a => IsFractionRing.lift_algebraMap (K := Om C.Z) hψ a
  obtain ⟨w, hw⟩ := hL.bc _ _ φ (genFr h C.Z)
  obtain ⟨w', hw'⟩ := hL.bc _ _ φ C.yg
  obtain rfl : w' = z := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ ψ C.y).1 _ _
    (e ▸ PullbackSections.frMap_trans _ _ C.gen hw') hz
  exact ⟨φ, w, _, hw, GlobalTheory.SupGeneric.frBor_of_frMap _ C.bor hw hw'⟩

theorem exists_comp_generic_off_meagre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (h : GenFrEx Xo c) (k : U.Comp), ∃ Z : Comp Xo c, ∃ S : ℕ → Set (Frame (U.X k).Ψ r), (∀ n, IsClosed (S n) ∧ interior (S n) = ∅) ∧ ∀ x : (U.X k).dom, (∀ n, x.1 ∉ S n) → ∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y' := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU h k
  obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)
  obtain ⟨ι, _, C, hC⟩ := GlobalTheory.T.exists_countable_flagSpace_atlas E H Dw l Xo c h
  obtain ⟨Z, hZ⟩ := GlobalTheory.T.exists_component_of_modelCharts E H Dw l Xo c σ r (Formalism.L2.PjFree.Unf.ofPj U) hU h k
  obtain ⟨S, hS, hcov⟩ := exists_seq_of_isMeagre
    (isMeagre_iUnion fun i => isMeagre_chart (Formalism.L2.PjFree.Unf.ofPj U) hσ hU k (C i))
  refine ⟨Z, S, hS, fun x hx => ?_⟩
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  obtain ⟨i, ψ, z, t, hz, ht⟩ := hC (CAt σ) (U.un k x)
  obtain rfl := hZ x (C i) ψ z t hz ht
  have hψ : Function.Injective ψ := by
    by_contra hni
    obtain ⟨n, hn⟩ := hcov x.1 (Set.mem_iUnion.2 ⟨i, x.2, ψ, z, t, hz, ht, hni⟩)
    exact hx n hn
  obtain ⟨φ, y', t', hy', ht'⟩ := exists_generic_of_injective (C i) ψ hψ hz
  exact ⟨φ, y', _, hy', hinv _ _ _ (hmul _ _ _ _ _ ht' ht)⟩

end GlobalTheory.GenericFrames
