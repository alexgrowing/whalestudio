import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AtPBijective
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerSetEqRangeNormalForm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormCongruenceLiftSmallGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundIpow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundSkew
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueCommonStabilizerEqRadicalLeviMap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordOfMemXa
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsBlockOfFrame
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RefLatticeStabilizerMiddleBottomLayersStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueMulMemBoxTriangularLayersStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerFromCoordinatesProductLawStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingCommonStabilizerCoordinatesAtPlStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureCommonStabilizerCoordsBoxImageStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealFrameAutomorphismUnitriangularRowsCoordsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelMatrixSkewCoordinatesRationalAutStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealisationMemStandardMiddleSpaceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnimodularTraceOnMiddleSpaceLiftStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundamentalSetRowsMiddleSpaceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LayerCovolumeProductPowTwoSidedBoundsStatement

noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegVol.RefCov

theorem exu_pi {J A : Type} [AddCommGroup A] {Λ F : J → Set A} (h : ∀ i a, ∃! b, b ∈ Λ i ∧ b + a ∈ F i) (a : J → A) :
    ∃! b, b ∈ Set.pi Set.univ Λ ∧ b + a ∈ Set.pi Set.univ F := by
  choose b hb hu using fun i => h i (a i)
  exact ⟨b, ⟨fun i _ => (hb i).1, fun i _ => (hb i).2⟩, fun c hc => funext fun i => hu i _ ⟨hc.1 i trivial, hc.2 i trivial⟩⟩

theorem exu_prod {A B : Type} [AddCommGroup A] [AddCommGroup B] {Λ F : Set A} {Λ' F' : Set B}
    (h : ∀ a, ∃! b, b ∈ Λ ∧ b + a ∈ F) (h' : ∀ a, ∃! b, b ∈ Λ' ∧ b + a ∈ F') (a : A × B) :
    ∃! b, b ∈ Λ ×ˢ Λ' ∧ b + a ∈ F ×ˢ F' := by
  obtain ⟨b, hb, hu⟩ := h a.1
  obtain ⟨b', hb', hu'⟩ := h' a.2
  exact ⟨(b, b'), ⟨⟨hb.1, hb'.1⟩, hb.2, hb'.2⟩, fun c hc => Prod.ext (hu _ ⟨hc.1.1, hc.2.1⟩) (hu' _ ⟨hc.1.2, hc.2.2⟩)⟩

theorem exu_image {T A : Type} [AddCommGroup A] {P : T → Prop} {f : T → A} {F : Set A}
    (h : ∀ a, ∃! t, P t ∧ f t + a ∈ F) (a : A) : ∃! b, b ∈ f '' {t | P t} ∧ b + a ∈ F := by
  obtain ⟨t, ht, hu⟩ := h a
  refine ⟨f t, ⟨⟨t, ht.1, rfl⟩, ht.2⟩, ?_⟩
  rintro _ ⟨⟨t', ht', rfl⟩, h2⟩
  rw [hu t' ⟨ht', h2⟩]

theorem card_top (r j : ℕ) : Fintype.card {a : Fin r // j ≤ a.val} = r - j := by
  have h1 : Fintype.card {b : Fin r // b.val < j} = min r j := by
    rw [Fintype.card_subtype, Fin.card_filter_val_lt]
  have h2 := Fintype.card_subtype_compl fun b : Fin r => b.val < j
  rw [h1, Fintype.card_fin] at h2
  rw [Fintype.card_congr (Equiv.subtypeEquivRight fun b : Fin r => (not_lt (a := b.val) (b := j)).symm), h2]
  omega

theorem card_UT (r : ℕ) (P : UT r → Prop) [Fintype (Subtype P)] : Fintype.card (Subtype P) ≤ r ^ 2 := by
  refine (Fintype.card_le_of_injective (fun p : Subtype P => p.1.1) fun p q h => Subtype.ext (Subtype.ext h)).trans ?_
  simp [sq]

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} {N : NF H r} {k : ℕ} {ι : Type}
  {σ : ι → (K →+* ℂ)} {ρ : ℝ} {β : Fin r → ℕ} {Φ : ι → V → Fin (2 * r + k + 1) → ℂ} {z z' : ι → Fin (2 * r + k + 1) → ℂ}
  {g : ι → Mat k r}

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem rset_eq (hF : ∀ v, IsFrameOf N k (σ v) ρ β (Φ v) (z v) (z' v) (g v)) (v : ι) :
    Rset k r (g v) = Set.range (crd k r N.j β) ∧ IsClosedSub k r (Rset k r (g v)) ∧ Function.Injective (crd k r N.j β) := by
  obtain ⟨-, h1, h2, h3, ⟨c, hc⟩, -⟩ := hF v
  obtain ⟨a1, a2⟩ := rset_normal0 k r N.j N.j_le _ _ _ β c h1 h2 h3 hc
  obtain ⟨-, b1, b2, -⟩ := Swap.range_eq_and_injective_parabolic_unipotent_product k r N.j β hc.2.2.2.1 hc.2.2.2.2.1
  exact ⟨a1.trans b1, a2, b2⟩

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem exists_CC (hF : ∀ v, IsFrameOf N k (σ v) ρ β (Φ v) (z v) (z' v) (g v)) (m : ι → Mat k r)
    (hm : ∀ v, m v ∈ Rset k r (g v)) : ∃ p : Crd ι k r N.j β, CC p = m := by
  choose q hq using fun v => (rset_eq hF v).1 ▸ hm v
  obtain ⟨p, rfl⟩ := usage₂.2 q
  exact ⟨p, funext hq⟩

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem CC_law (hF : ∀ v, IsFrameOf N k (σ v) ρ β (Φ v) (z v) (z' v) (g v)) (p q : Crd ι k r N.j β) :
    ∃ w, CC p * CC q = CC w ∧
      (∀ i : UTin β, (∀ l : UTin β, l.1.1.2.val - l.1.1.1.val < i.1.1.2.val - i.1.1.1.val → p.1 l = 0) →
        w.1 i = p.1 i + q.1 i) ∧ (p.1 = 0 → w.2.1 = p.2.1 + q.2.1) ∧ (p.1 = 0 → p.2.1 = 0 → w.2.2 = p.2.2 + q.2.2) := by
  obtain ⟨w, hw⟩ := exists_CC hF (CC p * CC q) fun v =>
    (rset_eq hF v).2.1.2.2.2.1 _ ((rset_eq hF v).1 ▸ ⟨_, rfl⟩) _ ((rset_eq hF v).1 ▸ ⟨_, rfl⟩)
  have h := fun v => (GlobalTheory.T.commonStabilizerFromCoordinates_product_law k r N.j β).2 (atP p v) (atP q v) (atP w v) (congrFun hw v).symm
  refine ⟨w, hw.symm, fun i hi => funext fun v => (h v).1 i fun l hl => congrFun (hi l hl) v, fun h1 => ?_,
    fun h1 h2 => ?_⟩
  · funext a v
    exact congrFun ((h v).2.1 (funext fun i => congrFun (congrFun h1 i) v)) a
  · have h3 := fun v => (h v).2.2 (funext fun i => congrFun (congrFun h1 i) v) (funext fun i => congrFun (congrFun h2 i) v)
    refine Prod.ext ?_ ?_
    · funext a v
      exact congrFun (congrArg Prod.fst (h3 v)) a
    · funext a v
      exact congrFun (congrArg Prod.snd (h3 v)) a

theorem covol_ref : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (k : ℕ) (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)) (β : Fin r → ℕ) (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (z z' : ι → Fin (2 * r + k + 1) → ℂ) (g : ι → Mat k r), IsPlaces σ → Module.finrank K V = 2 * r + k + 1 → (∀ v, IsFrameOf N k (σ v) (2 * Formalism.HermitianLatticesTheory.vInv K) β (Φ v) (z v) (z' v) (g v)) → (Ideal.absNorm N.𝔡 : ℝ) = (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * Fintype.card ι) → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → ∀ L : Submodule (𝓞 K) V, IsUnimodMod H L (uPerp N.F N.F') (II N.F N.F') → N.F.z ∈ L → ∃ Ω : Set (ι → Mt k r), IsFund (realPts Φ (N.Gam (N.Ref L) : Set (V ≃ₗ[K] V))) (RP k r g) Ω ∧ ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv K ^ (k * (r - N.j) * Fintype.card ι) / (8 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * (r + 1) ^ 2 * Fintype.card ι)) ≤ Measure.pi (fun _ : ι => lebR0 k r N.j β) Ω ∧ Measure.pi (fun _ : ι => lebR0 k r N.j β) Ω ≤ ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv K ^ (k * (r - N.j) * Fintype.card ι) * (8 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * (r + 1) ^ 2 * Fintype.card ι)) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N k ι _ σ β Φ z z' g hσ hd hF hN hv L hL hz
  set ρ : ℝ := 2 * Formalism.HermitianLatticesTheory.vInv K with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  obtain ⟨v₀, -⟩ := hσ.2 w₀
  obtain ⟨c₀, hc₀⟩ := (hF v₀).2.2.2.2.1
  obtain ⟨m1, -, m3, -⟩ := RealMat.real_points K V H hK r N k ι σ β Φ z z' g hσ hd hF
  obtain ⟨t1, t2⟩ := TopLayer.top_layer K V H hK r N k ι σ β Φ z z' g hσ hd hF L hL hz
  obtain ⟨d1, d2, d3, d4⟩ := GlobalTheory.T.refLatticeStabilizer_middle_bottom_layers K V H hK r N L hL hz
  obtain ⟨HW, hB, hdW, hU⟩ := GlobalTheory.T.exists_unimodular_trace_on_middleSpace_lift K V H hK r N L hL
  have htop := fun v => GlobalTheory.T.realFrame_automorphism_unitriangular_rows_coords K V H r N k (σ v) ρ β (Φ v) (z v) (z' v) (g v) hρ0 (hF v)
  have hskew := fun v => GlobalTheory.T.besselModelMatrix_skew_coordinates_rational_aut K V H r N k (σ v) ρ β (Φ v) (z v) (z' v) (g v) hρ0 (hF v)
  have hne : ∀ n : ℕ, ∀ v : ι, ((ρ ^ n : ℝ) : ℂ) ≠ 0 := fun n _ => by exact_mod_cast (pow_pos hρ0 n).ne'
  choose F₁ hF₁m hF₁ hF₁v using fun i : UTin β => IdealFund.exists_fund_ipow K hK ι σ hσ N.𝔡
    ((i.1.1.1.val : ℤ) - i.1.1.2.val) (fun _ => ((ρ ^ (i.1.1.2.val - i.1.1.1.val) : ℝ) : ℂ)) N.𝔡_ne (hne _)
  choose F₂ hF₂m hF₂ hF₂v using fun b : {a : Fin r // N.j ≤ a.val} => GlobalTheory.T.exists_fundamental_set_rows_middleSpace K V H hK N.Wn HW k r ι σ Φ hB hσ
    (by omega) (fun v => (hF v).1) (fun v => GlobalTheory.T.realisation_mem_standard_middle_space K V H r N k (σ v) ρ β (Φ v) (z v) (z' v) (g v) hρ0 (hF v))
    L N.𝔡 (-((r : ℤ) - b.1.val)) (ρ ^ (r - b.1.val)) hU N.𝔡_ne (pow_pos hρ0 _)
  choose F₃ hF₃m hF₃ hF₃v using fun p : {p : UT r // N.j ≤ p.1.1.val} => IdealFund.exists_fund_ipow K hK ι σ hσ N.𝔡
    (-((r : ℤ) - p.1.1.1.val) - ((r : ℤ) - p.1.1.2.val))
    (fun _ => ((ρ ^ ((r - p.1.1.1.val) + (r - p.1.1.2.val)) : ℝ) : ℂ)) N.𝔡_ne (hne _)
  choose F₄ hF₄m hF₄ hF₄l hF₄u using fun a : {a : Fin r // N.j ≤ a.val} => SkewFund.exists_fund_skew K hK ι σ hσ N.𝔡
    (r - a.1.val) N.𝔡_ne N.𝔡_star hN hv
  obtain ⟨hΩm, hΩv⟩ := GlobalTheory.T.measure_commonStabilizerCoords_box_image ι k r N.j β hc₀.2.2.2.1 hc₀.2.2.2.2.1 (GlobalTheory.T.measurePreserving_commonStabilizerCoordinatesAtPlace ι k r N.j β) F₁ F₂ F₃ F₄
    hF₁m hF₂m hF₃m hF₄m _ rfl
  refine ⟨_, ⟨hΩm, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨q, rfl⟩ := exists_CC hF x hx
    have hex : ∀ s ∈ N.Gam (N.Ref L), ∃ p : Crd ι k r N.j β, ∀ v x, crd k r N.j β (atP p v) *ᵥ Φ v x = Φ v (s x) := by
      intro s hs
      obtain ⟨m, hm, -⟩ := m1 s
      obtain ⟨p, rfl⟩ := exists_CC hF m (m3 ⟨s, hs.1, hm⟩)
      exact ⟨p, hm⟩
    have hu0 : ∀ (s : V ≃ₗ[K] V) (p : Crd ι k r N.j β), (∀ v x, crd k r N.j β (atP p v) *ᵥ Φ v x = Φ v (s x)) →
        (∀ a : Fin r, s (N.F.e a.castSucc) = N.F.e a.castSucc) → p.1 = 0 := by
      intro s p hp he
      funext i v
      have := (htop v s _ (hp v)).1 i 0 (by simp [he])
      simpa [atP] using this
    have h10 : ∀ (p : Crd ι k r N.j β), p.1 = 0 → ∀ v, (atP p v).1 = 0 := fun p h v =>
      funext fun i => congrFun (congrFun h i) v
    have h20 : ∀ (p : Crd ι k r N.j β), p.2.1 = 0 → ∀ v, (atP p v).2.1 = 0 := fun p h v =>
      funext fun i => congrFun (congrFun h i) v
    have hcast : ∀ a : Fin r, -(2 * ((r - a.val : ℕ) : ℤ)) = -((r : ℤ) - a.val) - ((r : ℤ) - a.val) := fun a => by
      have := a.2; omega
    refine GlobalTheory.T.existsUnique_mul_mem_box_triangular_layers (ι → Mat k r) (UTin β) _ _ _ (fun l => l.1.1.2.val - l.1.1.1.val) CC
      (realPts Φ (N.Gam (N.Ref L) : Set (V ≃ₗ[K] V))) _ F₁ _ (Set.pi Set.univ F₂) _
      (Set.pi Set.univ F₃ ×ˢ Set.pi Set.univ F₄) ?_ ?_ (CC_law hF) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (fun i => exu_image (hF₁ i)) (exu_pi fun i => exu_image (hF₂ i))
      (exu_prod (exu_pi fun i => exu_image (hF₃ i)) (exu_pi fun i => exu_image (hF₄ i))) q
    · exact fun p p' h => usage₂.1 (funext fun v => (rset_eq hF v).2.2 (congrFun h v))
    · exact funext fun v => (GlobalTheory.T.commonStabilizerFromCoordinates_product_law k r N.j β).1
    · rintro m ⟨s, hs, hm⟩
      exact exists_CC hF m (m3 ⟨s, hs.1, hm⟩)
    · exact ⟨1, one_mem _, fun v x => Matrix.one_mulVec _⟩
    · rintro a ⟨s, hs, ha⟩ b ⟨t, ht, hb⟩
      refine ⟨s * t, mul_mem hs ht, fun v x => ?_⟩
      have := (Matrix.mulVec_mulVec (Φ v x) (Matrix.of (a v)) (Matrix.of (b v))).symm
      rw [hb, ha] at this
      exact this
    · rintro a ⟨s, hs, ha⟩
      obtain ⟨b, hb, -⟩ := m1 s⁻¹
      refine ⟨b, ⟨s⁻¹, inv_mem hs, hb⟩, funext fun v => RealMat.mat_unique (hF v).1 fun x => ?_⟩
      have := (Matrix.mulVec_mulVec (Φ v x) (Matrix.of (b v)) (Matrix.of (a v))).symm
      rw [ha, hb] at this
      refine this.trans ?_
      simp
    · rintro p ⟨s, hs, hp⟩ i
      obtain ⟨u, h1, h2, -⟩ := t1 s hs _ _ i.1.2
      exact ⟨u _, h2 _, funext fun v => ((htop v s _ (hp v)).1 i u h1).symm⟩
    · rintro p ⟨s, hs, hp⟩ h1 b -
      obtain ⟨y, hy, h⟩ := d1 s hs ((htop v₀ s _ (hp v₀)).2.1 (h10 p h1 v₀)) b.1 b.2
      exact ⟨y, hy, funext fun v => ((htop v s _ (hp v)).2.2 (h10 p h1 v) b y h).symm⟩
    · rintro p ⟨s, hs, hp⟩ h1 h2
      have h := fun v => hskew v s _ (hp v) (h10 p h1 v) (h20 p h2 v)
      have h3 := d3 s hs ((htop v₀ s _ (hp v₀)).2.1 (h10 p h1 v₀)) (h v₀).1
      refine ⟨fun i _ => ⟨_, (h3 i.1.1.1 i.1.1.2 i.2 (i.2.trans (le_of_lt i.1.2))).1, funext fun v => ((h v).2.1 i).symm⟩,
        fun a _ => ⟨_, ⟨?_, (h3 a.1 a.1 a.2 a.2).2⟩, funext fun v => ((h v).2.2 a).symm⟩⟩
      rw [hcast]
      exact (h3 a.1 a.1 a.2 a.2).1
    · rintro i _ ⟨t, ht, rfl⟩
      obtain ⟨s, hs, h⟩ := t2 _ _ i.1.2 i.2 t ht
      obtain ⟨p, hp⟩ := hex s hs
      refine ⟨p, ⟨s, hs, hp⟩, funext fun l => funext fun v => ?_⟩
      have := (htop v s _ (hp v)).1 l (Pi.single i.1.1.1 (if l.1.1.2 = i.1.1.2 then t else 0))
        (by rw [h]; simp [Pi.single_apply])
      refine this.trans ?_
      by_cases hl : l = i
      · subst hl; simp
      · rw [@Pi.single_eq_of_ne _ _ _ (fun a b => Classical.propDecidable (a = b)) _ _ hl]
        by_cases h1 : l.1.1.1 = i.1.1.1
        · have h2 : l.1.1.2 ≠ i.1.1.2 := fun h2 => hl (Subtype.ext (Subtype.ext (Prod.ext h1 h2)))
          simp [h2]
        · simp [Pi.single_eq_of_ne h1]
    · intro b hb
      choose y hy hyb using fun a => hb a trivial
      obtain ⟨s, hs, he, h⟩ := d2 (fun a => if h : N.j ≤ a.val then y ⟨a, h⟩ else 0) fun a => by
        by_cases h : N.j ≤ a.val
        · rw [dif_pos h]; exact hy ⟨a, h⟩
        · rw [dif_neg h]; exact Submodule.zero_mem _
      obtain ⟨p, hp⟩ := hex s hs
      have h1 := hu0 s p hp he
      refine ⟨p, ⟨s, hs, hp⟩, h1, funext fun a => ?_⟩
      rw [← hyb a]
      funext v
      refine (htop v s _ (hp v)).2.2 (h10 p h1 v) a (y a) ?_
      have := h a.1 a.2
      rwa [dif_pos a.2] at this
    · rintro d ⟨hd1, hd2⟩
      choose t ht htd using fun a => hd1 a trivial
      choose t' ht' htd' using fun a => hd2 a trivial
      let S : Fin r → Fin r → K := fun a b =>
        if h : N.j ≤ a.val ∧ N.j ≤ b.val then
          if h1 : a < b then t ⟨⟨(a, b), h1⟩, h.1⟩ else if h2 : b < a then -star (t ⟨⟨(b, a), h2⟩, h.2⟩) else t' ⟨a, h.1⟩
        else 0
      have hS : ∀ a b, S a b ∈ ipow N.𝔡 (-((r : ℤ) - a.val) - ((r : ℤ) - b.val)) ∧ S a b + star (S b a) = 0 := by
        intro a b
        by_cases h : N.j ≤ a.val ∧ N.j ≤ b.val
        · rcases lt_trichotomy a b with h1 | rfl | h1
          · simp only [S, dif_pos h, dif_pos h.symm, dif_pos h1, dif_neg h1.not_gt]
            exact ⟨ht ⟨⟨(a, b), h1⟩, h.1⟩, by simp⟩
          · simp only [S, dif_pos h, dif_neg (lt_irrefl a)]
            rw [← hcast]
            exact ht' ⟨a, h.1⟩
          · simp only [S, dif_pos h, dif_pos h.symm, dif_pos h1, dif_neg h1.not_gt]
            refine ⟨neg_mem (LiftS.ipow_star _ N.𝔡_ne N.𝔡_star _ ?_), by simp⟩
            rw [show -((r : ℤ) - a.val) - ((r : ℤ) - b.val) = -((r : ℤ) - b.val) - ((r : ℤ) - a.val) by ring]
            exact ht ⟨⟨(b, a), h1⟩, h.2⟩
        · simp [S, dif_neg h, dif_neg (mt And.symm h)]
      obtain ⟨s, hs, he, h⟩ := d4 S hS
      obtain ⟨p, hp⟩ := hex s hs
      have h1 := hu0 s p hp he
      have h2 : p.2.1 = 0 := by
        funext b v
        refine ((htop v s _ (hp v)).2.2 (h10 p h1 v) b 0 ?_).trans ?_
        · rw [h b.1 b.2, add_sub_cancel_left, sub_zero]
          refine Submodule.sum_mem _ fun a _ => ?_
          by_cases ha : N.j ≤ a.val
          · exact Submodule.smul_mem _ _ (NFGeom.e_mem_II N a ha)
          · simp [ha]
        · funext l
          simp [RealMat.phi_zero (hF v).1]
      have hSB : ∀ a b : Fin r, N.j ≤ a.val → N.j ≤ b.val → H.B (s (N.ist b)) (N.ist a) = S a b := by
        intro a b ha hb
        rw [h b hb]
        simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
          N.ist_iso b a hb ha, N.ist_e _ a ha]
        simp [ha]
      have h3 := fun v => hskew v s _ (hp v) (h10 p h1 v) (h20 p h2 v)
      have h4 : p = (0, 0, d) := by
        refine Prod.ext h1 (Prod.ext h2 (Prod.ext ?_ ?_))
        · funext i v
          have hi : N.j ≤ i.1.1.2.val := i.2.trans (le_of_lt i.1.2)
          refine ((h3 v).2.1 i).trans ?_
          rw [hSB _ _ i.2 hi]
          simp only [S, dif_pos (And.intro i.2 hi), dif_pos i.1.2]
          exact congrFun (htd i) v
        · funext a v
          refine ((h3 v).2.2 a).trans ?_
          rw [hSB _ _ a.2 a.2]
          simp only [S, dif_pos (And.intro a.2 a.2), dif_neg (lt_irrefl a.1)]
          exact congrFun (htd' a) v
      exact h4 ▸ ⟨s, hs, hp⟩
  · have hsc : ∀ (n : ℕ) (m : ℤ), m = -(n : ℤ) → (Ideal.absNorm N.𝔡 : ℝ) ^ m * (ρ ^ n) ^ (2 * Fintype.card ι) = 1 := by
      rintro n _ rfl
      rw [hN, _root_.zpow_neg, _root_.zpow_natCast, ← pow_mul, ← pow_mul, mul_comm n]
      exact inv_mul_cancel₀ (pow_pos hρ0 _).ne'
    have hsc' : ∀ (n : ℕ) (m : ℤ), m = -(n : ℤ) → Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι * (Ideal.absNorm N.𝔡 : ℝ) ^ m *
        ∏ _v : ι, ‖((ρ ^ n : ℝ) : ℂ)‖ ^ 2 = Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι := by
      intro n m h
      rw [Finset.prod_const, Finset.card_univ, Complex.norm_real, Real.norm_of_nonneg (pow_pos hρ0 n).le, ← pow_mul,
        mul_assoc, hsc n m h, mul_one]
    have e1 : ∀ i, volume (F₁ i) = ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι) := fun i => by
      rw [hF₁v, hsc']
      have : i.1.1.1.val < i.1.1.2.val := i.1.2
      omega
    have e2 : ∀ i, volume (F₂ i) = ENNReal.ofReal ((Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι) ^ (k + 1)) := fun i => by
      rw [hF₂v, mul_assoc, hsc, mul_one]
      have := i.1.2
      omega
    have e3 : ∀ i, volume (F₃ i) = ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι) := fun i => by
      rw [hF₃v, hsc']
      have := i.1.1.1.2
      have := i.1.1.2.2
      omega
    rw [hΩv]
    simp only [e1, e2, e3, Finset.prod_const, Finset.card_univ, card_top]
    refine GlobalTheory.T.layer_covolume_product_pow_two_sided_bounds _ _ k r _ _ _ _ hv (Nat.sub_le _ _) (card_UT r _) (card_UT r _) ?_ ?_
    · rw [← card_top, ← Finset.card_univ (α := {a : Fin r // N.j ≤ a.val}), ← Finset.prod_const]
      exact Finset.prod_le_prod' fun i _ => hF₄l i
    · rw [← card_top, ← Finset.card_univ (α := {a : Fin r // N.j ≤ a.val}), ← Finset.prod_const]
      exact Finset.prod_le_prod' fun i _ => hF₄u i

end GlobalTheory.DegVol.RefCov
