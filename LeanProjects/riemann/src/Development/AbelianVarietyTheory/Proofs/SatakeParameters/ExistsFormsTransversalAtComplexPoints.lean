import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFormsVanishingComplexPointsFullJetsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicSardShiftedFunctionsRegularZerosStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteComplexPointsTransversalZerosStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqTopOfForallComplexPointsMemOpensStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RatioSpanCotangentChangeDenominatorStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsProjFormNonvanishingGenericPointComplexPoiStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj.Transv

open GlobalTheory.ProjSpace GlobalTheory.ProjFrac

theorem mem_ptsIn_fOpen_iff {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {N : ℕ} (ι : X ⟶ PSpace ℂ N)
    (q : MvPolynomial (Fin (N + 1)) ℂ) (z : CxPts p (RingHom.id ℂ)) :
    z ∈ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι q) ↔
      q ∉ (ι.base (z.1 (IsLocalRing.closedPoint ℂ))).asHomogeneousIdeal :=
  CxPts.mem_ptsIn.trans (mem_fOpen ι q _)

theorem evHom_fRatio_eq_zero_iff {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {N n : ℕ} (ι : X ⟶ PSpace ℂ N)
    {f g : MvPolynomial (Fin (N + 1)) ℂ} (hf : f ∈ grading ℂ N n) (hg : g ∈ grading ℂ N n)
    {z : CxPts p (RingHom.id ℂ)} (hz : z ∈ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι g)) :
    CxPts.evHom hz (fRatio ι f g hf hg) = 0 ↔ z ∉ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι f) := by
  have e : X.basicOpen (fRatio ι f g hf hg) = fOpen ι g ⊓ fOpen ι f := by
    have e0 : X.basicOpen (fRatio ι f g hf hg) =
        ι ⁻¹ᵁ (PSpace ℂ N).basicOpen (frac (grading ℂ N) _ f g hf hg le_rfl) :=
      (Scheme.preimage_basicOpen ι _).symm
    rw [e0, basicOpen_frac]
    rfl
  have h1 := CxPts.mem_ptsIn_basicOpen hz (fRatio ι f g hf hg)
  rw [e, CxPts.mem_ptsIn_inf, CxPts.ev_eq hz] at h1
  constructor
  · intro h0 hf'
    exact (h1.1 ⟨hz, hf'⟩) h0
  · intro hn
    by_contra h0
    exact hn (h1.2 h0).2

theorem frac_smul_deg {N n : ℕ} (V : (PSpace ℂ N).Opens) (f g : MvPolynomial (Fin (N + 1)) ℂ)
    (hf : f ∈ grading ℂ N n) (hg : g ∈ grading ℂ N n) (hV : V ≤ Proj.basicOpen (grading ℂ N) g) (c : ℂ)
    (hcf : c • f ∈ grading ℂ N n) :
    frac (grading ℂ N) V (c • f) g hcf hg hV = algebraMap ℂ Γ(PSpace ℂ N, V) c * frac (grading ℂ N) V f g hf hg hV := by
  refine ext fun x hx => ?_
  obtain ⟨i, hi⟩ := exists_mem_chart ℂ N x
  have hW : V ⊓ chart ℂ N i ≤ V := inf_le_left
  have hxW : x ∈ V ⊓ chart ℂ N i := ⟨hx, hi⟩
  rw [← ev_resG hW x hxW, ← ev_resG hW x hxW, map_mul, resG_algebraMap, resG_frac, resG_frac,
    ← formOn_C (hi := (inf_le_right : V ⊓ chart ℂ N i ≤ chart ℂ N i)), formOn]
  congr 1
  refine (frac_mul_eq ?_).symm
  rw [MvPolynomial.smul_eq_C_mul]
  ring

theorem fRatio_add_smul {X : Scheme.{0}} (p : X ⟶ Sp ℂ) {N n : ℕ} (ι : X ⟶ PSpace ℂ N)
    (hp : ι ≫ PSpace.str ℂ N = p) {g h f₀ : MvPolynomial (Fin (N + 1)) ℂ} (hg : g ∈ grading ℂ N n)
    (hh : h ∈ grading ℂ N n) (hf₀ : f₀ ∈ grading ℂ N n) (c : ℂ) (hgh : g + c • h ∈ grading ℂ N n) :
    fRatio ι (g + c • h) f₀ hgh hf₀ =
      fRatio ι g f₀ hg hf₀ + ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (fOpen ι f₀) c * fRatio ι h f₀ hh hf₀ := by
  have hch : c • h ∈ grading ℂ N n := Submodule.smul_mem _ c hh
  unfold fRatio
  rw [frac_add (ha := hg) (ha₂ := hch), frac_smul_deg _ h f₀ hh hf₀ _ c hch, map_add, map_mul]
  congr 2
  subst hp
  rw [algebraMap_sections_eq]
  change _ = ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (ι ≫ PSpace.str ℂ N).appLE ⊤ (ι ⁻¹ᵁ _) le_top).hom c
  rw [Scheme.Hom.app_eq_appLE, ← Scheme.Hom.appLE_comp_appLE]
  rfl

end GlobalTheory.EtProj.Transv

namespace GlobalTheory.EtProj.Transv

open GlobalTheory.ProjSpace

theorem exists_transversal_forms_first_separate (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] (N : ℕ)
    (ι : X ⟶ PSpace ℂ N) (hι : IsClosedImmersion ι) (hp : ι ≫ PSpace.str ℂ N = p)
    (S : Finset (CxPts p (RingHom.id ℂ))) :
    ∃ (n : ℕ) (f₀ : MvPolynomial (Fin (N + 1)) ℂ) (F : Fin d → MvPolynomial (Fin (N + 1)) ℂ)
      (hf₀ : f₀ ∈ grading ℂ N n) (hF : ∀ j, F j ∈ grading ℂ N n), 0 < n ∧
      (fOpen ι f₀ ⊔ ⨆ j, fOpen ι (F j) = ⊤) ∧ genericPoint X ∈ fOpen ι f₀ ∧
      (∀ j, genericPoint X ∈ fOpen ι (F j)) ∧
      (∀ y ∈ S, ∃ hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι f₀), ∀ j,
        CxPts.evHom hy (fRatio ι (F j) f₀ (hF j) hf₀) = 0) ∧
      ∀ (y : CxPts p (RingHom.id ℂ)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι f₀)),
        (∀ j, CxPts.evHom hy (fRatio ι (F j) f₀ (hF j) hf₀) = 0) →
        RingHom.ker (CxPts.evHom hy) ≤ Ideal.span (Set.range fun j => fRatio ι (F j) f₀ (hF j) hf₀) ⊔
          RingHom.ker (CxPts.evHom hy) ^ 2 := by
  classical
  haveI : IsClosedImmersion ι := hι
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  obtain ⟨n, h, g, hh, hg, hn, hgen, hgS, hbase, hjet⟩ := GlobalTheory.T.exists_forms_vanishing_complexPoints_fullJets X p d N ι hι hp S
  have hUh : IsAffineOpen (fOpen ι h) := (Proj.isAffineOpen_basicOpen (grading ℂ N) h hh hn).preimage ι
  obtain ⟨E, hE, hEgood⟩ := GlobalTheory.T.algebraicSard_shifted_functions_regularZeros X p d (fOpen ι h) hUh (fun j => fRatio ι (g j) h (hg j) hh)
  have hB : ∀ j, ∃ a : ℂ, ∀ c : ℂ, genericPoint X ∉ fOpen ι (g j + c • h) → c = a := by
    intro j
    by_cases hx : ∃ c₀ : ℂ, genericPoint X ∉ fOpen ι (g j + c₀ • h)
    · obtain ⟨c₀, hc₀⟩ := hx
      refine ⟨c₀, fun c hc => ?_⟩
      by_contra hne
      rw [mem_fOpen, not_not] at hc hc₀
      set P := (ι.base (genericPoint X)).asHomogeneousIdeal.toIdeal
      have h1 : (c - c₀) • h ∈ P := by
        have := P.sub_mem hc hc₀
        rwa [add_sub_add_left_eq_sub, ← sub_smul] at this
      have h2 : h ∈ P := by
        have := P.mul_mem_left (MvPolynomial.C (c - c₀)⁻¹) h1
        rwa [← MvPolynomial.smul_eq_C_mul, smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hne), one_smul] at this
      have h3 : g j ∈ P := by
        have := P.sub_mem hc₀ (P.mul_mem_left (MvPolynomial.C c₀) h2)
        rwa [← MvPolynomial.smul_eq_C_mul, add_sub_cancel_right] at this
      exact (mem_fOpen ι (g j) _).1 (hgen j) h3
    · push_neg at hx
      exact ⟨0, fun c hc => absurd (hx c) hc⟩
  choose a ha using hB
  obtain ⟨c, hcE, hcB⟩ : ∃ c : Fin d → ℂ, c ∉ E ∧ ∀ j, c j ≠ a j := by
    have h0 : MeasureTheory.volume (E ∪ ⋃ j, {c : Fin d → ℂ | c j = a j}) = 0 := by
      refine MeasureTheory.measure_union_null hE (MeasureTheory.measure_iUnion_null fun j => ?_)
      rw [MeasureTheory.volume_pi]
      exact MeasureTheory.Measure.pi_hyperplane (μ := fun _ : Fin d => (MeasureTheory.volume : MeasureTheory.Measure ℂ)) j (a j)
    by_contra hne
    push_neg at hne
    have hu : (Set.univ : Set (Fin d → ℂ)) ⊆ E ∪ ⋃ j, {c : Fin d → ℂ | c j = a j} := by
      intro c _
      by_cases hc : c ∈ E
      · exact Or.inl hc
      · obtain ⟨j, hj⟩ := hne c hc
        exact Or.inr (Set.mem_iUnion.2 ⟨j, hj⟩)
    have := MeasureTheory.measure_mono_null hu h0
    exact (isOpen_univ.measure_pos MeasureTheory.volume Set.univ_nonempty).ne' this
  set F : Fin d → MvPolynomial (Fin (N + 1)) ℂ := fun j => g j + c j • h with hFdef
  have hF : ∀ j, F j ∈ grading ℂ N n := fun j => add_mem (hg j) (Submodule.smul_mem _ _ hh)
  have hFh : ∀ j, fRatio ι (F j) h (hF j) hh =
      fRatio ι (g j) h (hg j) hh + ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (fOpen ι h) (c j) := by
    intro j
    rw [fRatio_add_smul p ι hp (hg j) hh hh (c j) (hF j), fRatio_self, mul_one]
  have htrh : ∀ (z : CxPts p (RingHom.id ℂ)) (hz : z ∈ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι h)),
      (∀ j, z ∉ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι (F j))) →
      (∀ j, CxPts.evHom hz (fRatio ι (F j) h (hF j) hh) = 0) ∧
      RingHom.ker (CxPts.evHom hz) ≤ Ideal.span (Set.range fun j => fRatio ι (F j) h (hF j) hh) ⊔
        RingHom.ker (CxPts.evHom hz) ^ 2 := by
    intro z hz hzF
    have h0 : ∀ j, CxPts.evHom hz (fRatio ι (F j) h (hF j) hh) = 0 :=
      fun j => (evHom_fRatio_eq_zero_iff ι (hF j) hh hz).2 (hzF j)
    refine ⟨h0, ?_⟩
    have hc : ∀ j, CxPts.evHom hz (fRatio ι (g j) h (hg j) hh) + c j = 0 := by
      intro j
      have := h0 j
      rw [hFh, map_add, ← CxPts.ev_eq hz (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (fOpen ι h) (c j)),
        CxPts.ev_algX hz] at this
      exact this
    have := hEgood c hcE z hz hc
    simpa only [hFh] using this
  have hfin := GlobalTheory.T.finite_complexPoints_transversal_zeros X p (fOpen ι h) hUh d (fun j => fRatio ι (F j) h (hF j) hh)
  obtain ⟨f₀, hf₀, hf₀gen, hf₀F⟩ := GlobalTheory.T.exists_projForm_nonvanishing_genericPoint_complexPoints X p N ι n (S ∪ hfin.toFinset)
  have hbase' : ∀ z : CxPts p (RingHom.id ℂ), z ∉ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι h) →
      (∀ j, z ∉ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι (F j))) → z ∈ S := by
    intro z hzh hzF
    refine hbase z hzh fun j hzg => ?_
    rw [mem_ptsIn_fOpen_iff, not_not] at hzh
    have h1 := hzF j
    rw [mem_ptsIn_fOpen_iff, not_not] at h1
    rw [mem_ptsIn_fOpen_iff] at hzg
    apply hzg
    set P := (ι.base (z.1 (IsLocalRing.closedPoint ℂ))).asHomogeneousIdeal.toIdeal
    have := P.sub_mem h1 (P.mul_mem_left (MvPolynomial.C (c j)) hzh)
    rwa [← MvPolynomial.smul_eq_C_mul, add_sub_cancel_right] at this
  refine ⟨n, f₀, F, hf₀, hF, hn, ?_, hf₀gen, ?_, ?_, ?_⟩
  · refine GlobalTheory.T.eq_top_of_forall_complexPoints_mem_opens X p _ fun z => ?_
    by_cases hz0 : z ∈ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι f₀)
    · exact CxPts.ptsIn_mono le_sup_left hz0
    by_cases hzj : ∃ j, z ∈ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι (F j))
    · obtain ⟨j, hj⟩ := hzj
      exact CxPts.ptsIn_mono (le_sup_of_le_right (le_iSup (fun j => fOpen ι (F j)) j)) hj
    push_neg at hzj
    exfalso
    apply hz0
    refine hf₀F z ?_
    by_cases hzh : z ∈ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι h)
    · exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset hfin).2 ⟨hzh, htrh z hzh hzj⟩)
    · exact Finset.mem_union_left _ (hbase' z hzh hzj)
  · intro j
    by_contra hj
    exact hcB j (ha j (c j) hj)
  · intro y hy
    refine ⟨hf₀F y (Finset.mem_union_left _ hy), fun j => ?_⟩
    rw [evHom_fRatio_eq_zero_iff, mem_ptsIn_fOpen_iff, not_not]
    have hyh : h ∈ (ι.base (y.1 (IsLocalRing.closedPoint ℂ))).asHomogeneousIdeal := by
      have hyf₀ := hf₀F y (Finset.mem_union_left _ hy)
      have h2 := (hjet y hy f₀ hf₀ hyf₀).1
      have h3 : CxPts.evHom hyf₀ (fRatio ι h f₀ hh hf₀) = 0 :=
        RingHom.mem_ker.1 (Ideal.pow_le_self two_ne_zero h2)
      rw [evHom_fRatio_eq_zero_iff, mem_ptsIn_fOpen_iff, not_not] at h3
      exact h3
    have hyg := hgS y hy j
    rw [mem_ptsIn_fOpen_iff, not_not] at hyg
    set P := (ι.base (y.1 (IsLocalRing.closedPoint ℂ))).asHomogeneousIdeal.toIdeal
    have := P.add_mem hyg (P.mul_mem_left (MvPolynomial.C (c j)) hyh)
    rwa [← MvPolynomial.smul_eq_C_mul] at this
  · intro z hz h0
    have hzF : ∀ j, z ∉ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι (F j)) :=
      fun j => (evHom_fRatio_eq_zero_iff ι (hF j) hf₀ hz).1 (h0 j)
    by_cases hzS : z ∈ S
    · obtain ⟨h2, hJ⟩ := hjet z hzS f₀ hf₀ hz
      refine hJ.trans (sup_le ?_ le_sup_right)
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      have e := fRatio_add_smul p ι hp (hg j) hh hf₀ (c j) (hF j)
      have : fRatio ι (g j) f₀ (hg j) hf₀ = fRatio ι (F j) f₀ (hF j) hf₀ -
          ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (fOpen ι f₀) (c j) * fRatio ι h f₀ hh hf₀ := by
        rw [e, add_sub_cancel_right]
      show fRatio ι (g j) f₀ (hg j) hf₀ ∈ _
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.subset_span ⟨j, rfl⟩))
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ h2))
    · have hzh : z ∈ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι h) := by
        by_contra hzh
        exact hzS (hbase' z hzh hzF)
      exact GlobalTheory.T.ratio_span_cotangent_change_denominator X p N ι hι n hn d F h f₀ hF hh hf₀ z hzh hz (htrh z hzh hzF).2

end GlobalTheory.EtProj.Transv

namespace GlobalTheory.EtProj.Transv

open GlobalTheory.ProjSpace

theorem exists_forms_transversal (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ)
    [SmoothOfRelativeDimension d p] (N : ℕ)
    (ι : X ⟶ PSpace ℂ N) (hι : IsClosedImmersion ι) (hp : ι ≫ PSpace.str ℂ N = p)
    (S : Finset (CxPts p (RingHom.id ℂ))) :
    ∃ (n : ℕ) (f : Fin (d + 1) → MvPolynomial (Fin (N + 1)) ℂ) (hf : ∀ i, f i ∈ GlobalTheory.ProjSpace.grading ℂ N n), 0 < n ∧
      (⨆ i, GlobalTheory.EtProj.fOpen ι (f i) = ⊤) ∧ (∀ i, genericPoint X ∈ GlobalTheory.EtProj.fOpen ι (f i)) ∧
      (∀ y ∈ S, y ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι (f 0)) ∧ ∀ j : Fin d,
        CxPts.ev p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι (f 0)) (GlobalTheory.EtProj.fRatio ι (f j.succ) (f 0) (hf j.succ) (hf 0)) y = 0) ∧
      ∀ (y : CxPts p (RingHom.id ℂ)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι (f 0))),
        (∀ j : Fin d, CxPts.evHom hy (GlobalTheory.EtProj.fRatio ι (f j.succ) (f 0) (hf j.succ) (hf 0)) = 0) →
        RingHom.ker (CxPts.evHom hy) ≤ Ideal.span (Set.range fun j : Fin d => GlobalTheory.EtProj.fRatio ι (f j.succ) (f 0) (hf j.succ) (hf 0)) ⊔
          RingHom.ker (CxPts.evHom hy) ^ 2 := by
  obtain ⟨n, f₀, F, hf₀, hF, hn, hcov, hg0, hgF, hS, htr⟩ := exists_transversal_forms_first_separate X p d N ι hι hp S
  refine ⟨n, Fin.cons f₀ F, Fin.cases hf₀ hF, hn, ?_, Fin.cases hg0 hgF, ?_, ?_⟩
  · refine le_antisymm le_top (hcov.symm.le.trans (sup_le ?_ (iSup_le fun j => ?_)))
    · exact le_iSup (fun i => fOpen ι ((Fin.cons f₀ F : Fin (d + 1) → _) i)) 0
    · exact le_iSup (fun i => fOpen ι ((Fin.cons f₀ F : Fin (d + 1) → _) i)) j.succ
  · intro y hy
    obtain ⟨hy0, hyj⟩ := hS y hy
    refine ⟨hy0, fun j => ?_⟩
    have h1 := hyj j
    rw [← CxPts.ev_eq hy0] at h1
    exact h1
  · intro y hy h0
    exact htr y hy h0

end GlobalTheory.EtProj.Transv
