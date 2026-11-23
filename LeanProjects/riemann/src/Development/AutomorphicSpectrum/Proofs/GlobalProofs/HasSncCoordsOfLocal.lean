import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesExtendingRegularParameters
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.KaehlerBasisSpreadsToNeighbourhoodStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothLocalRingFreeDifferentialsStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RegularSequenceGermsRegularLocalStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.KaehlerBasisOnLocalizationAwayStatement

noncomputable section
namespace GlobalTheory.CompanionTheory.Geo.SncCoords
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

theorem relDim_of_dense {X S : Scheme.{0}} (f : X ⟶ S) [Smooth f] (D : ℕ) (W : X.Opens)
    (hW : Dense (W : Set X)) (hWD : SmoothOfRelativeDimension D (W.ι ≫ f)) :
    SmoothOfRelativeDimension D f := by
  choose n V hV hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim f
  have two : ∀ (A B : X.Opens) (a b : ℕ), SmoothOfRelativeDimension a (A.ι ≫ f) →
      SmoothOfRelativeDimension b (B.ι ≫ f) → ∀ x, x ∈ A → x ∈ B → a = b := by
    intro A B a b ha hb x hA hB
    have e₁ : SmoothOfRelativeDimension (0 + a) ((A ⊓ B).ι ≫ f) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_left : A ⊓ B ≤ A), Category.assoc]; infer_instance
    have e₂ : SmoothOfRelativeDimension (0 + b) ((A ⊓ B).ι ≫ f) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_right : A ⊓ B ≤ B), Category.assoc]; infer_instance
    simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ e₁ e₂ ⟨x, hA, hB⟩
  have hc : IsLocallyConstant n := (IsLocallyConstant.iff_exists_open n).2 fun x =>
    ⟨V x, (V x).isOpen, hV x, fun y hy => two _ _ _ _ (hd y) (hd x) y (hV y) hy⟩
  have hWsub : (W : Set X) ⊆ n ⁻¹' {D} := fun x hx => two _ _ _ _ (hd x) hWD x (hV x) hx
  have hall : ∀ x, n x = D := by
    have hcl : IsClosed (n ⁻¹' {D}) := (hc.isClopen_fiber D).isClosed
    have := hcl.closure_subset_iff.2 hWsub
    rw [hW.closure_eq] at this
    exact fun x => this (Set.mem_univ x)
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension D) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension D) V
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hV x⟩) fun x => ?_
  rw [← hall x]; exact hd x

theorem basis_spread (K A : Type) [Field K] [CommRing A] [Algebra K A] [Algebra.FinitePresentation K A]
    (P : Ideal A) [P.IsPrime] {n : ℕ} (x : Fin n → A)
    (hx : LinearIndependent (Localization.AtPrime P)
        (fun i => KaehlerDifferential.D K (Localization.AtPrime P) (algebraMap A _ (x i))) ∧
      Submodule.span (Localization.AtPrime P)
        (Set.range fun i => KaehlerDifferential.D K (Localization.AtPrime P) (algebraMap A _ (x i))) = ⊤) :
    ∃ s ∉ P, ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra K B] [IsScalarTower K A B]
      [IsLocalization.Away s B],
      LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap A B (x i))) ∧
        Submodule.span B (Set.range fun i => KaehlerDifferential.D K B (algebraMap A B (x i))) = ⊤ := GlobalTheory.T.kaehler_basis_spreads_to_neighbourhood K A P x hx

theorem omega_free (K : Type) [Field K] (D : ℕ) (Y : Scheme.{0}) (g : Y ⟶ Sp K)
    (hD : SmoothOfRelativeDimension D g) (U : Y.affineOpens) (P : Ideal Γ(Y, U.1)) [P.IsPrime] :
    letI := secAlgebra g U.1
    Algebra.FinitePresentation K Γ(Y, U.1) ∧
      Module.Free (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
      Module.Finite (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
      Module.finrank (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] = D := GlobalTheory.T.smooth_local_ring_free_differentials K D Y g hD U P

theorem stalk_transfer (Y : Scheme.{0}) (U : Y.affineOpens) (y : Y) (hy : y ∈ U.1)
    (hreg : IsRegularLocalRing (Y.presheaf.stalk y)) (m : ℕ) (f : Fin m → Γ(Y, U.1))
    (hf : FinalTheorems.Rsp (Y.presheaf.stalk y) m (fun i => Y.presheaf.germ U.1 y hy (f i))) :
    IsRegularLocalRing (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) ∧
      FinalTheorems.Rsp (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) m
        (fun i => algebraMap Γ(Y, U.1) _ (f i)) ∧
      ∀ s : Γ(Y, U.1), y ∈ Y.basicOpen s ↔ s ∉ (U.2.primeIdealOf ⟨y, hy⟩).asIdeal := GlobalTheory.T.regular_sequence_germs_regular_local Y U y hy hreg m f hf

theorem isCoords_basicOpen (K : Type) [Field K] (Y : Scheme.{0}) (g : Y ⟶ Sp K) (U : Y.affineOpens)
    (s : Γ(Y, U.1)) {n : ℕ} (x : Fin n → Γ(Y, U.1))
    (h : letI := secAlgebra g U.1
      ∀ (B : Type) [CommRing B] [Algebra Γ(Y, U.1) B] [Algebra K B] [IsScalarTower K Γ(Y, U.1) B]
        [IsLocalization.Away s B],
        LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) ∧
          Submodule.span B (Set.range fun i => KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) = ⊤) :
    IsCoords g (Y.basicOpen s) (fun i => Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op (x i)) := GlobalTheory.T.kaehler_basis_on_localization_away K Y g U s x h

theorem coords_at_point (K : Type) [Field K] [CharZero K] (D : ℕ) (Y : Scheme.{0}) (g : Y ⟶ Sp K)
    (hD : SmoothOfRelativeDimension D g) (U : Y.affineOpens) (y : Y) (hy : y ∈ U.1)
    (hreg : IsRegularLocalRing (Y.presheaf.stalk y)) (m : ℕ) (f : Fin m → Γ(Y, U.1))
    (hf : FinalTheorems.Rsp (Y.presheaf.stalk y) m (fun i => Y.presheaf.germ U.1 y hy (f i))) :
    ∃ (s : Γ(Y, U.1)) (x : Fin D → Γ(Y, U.1)) (e : Fin m ↪ Fin D), y ∈ Y.basicOpen s ∧
      (∀ j, x (e j) = f j) ∧
      IsCoords g (Y.basicOpen s) (fun i => Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op (x i)) := by
  let _ := secAlgebra g U.1
  obtain ⟨hregP, hrspP, hmem⟩ := stalk_transfer Y U y hy hreg m f hf
  obtain ⟨hfp, hfree, hfin, hrank⟩ := omega_free K D Y g hD U (U.2.primeIdealOf ⟨y, hy⟩).asIdeal
  obtain ⟨x, e, hxe, bs, hbs⟩ := GlobalTheory.exists_coords_extending_regularParams K Γ(Y, U.1)
    (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) (U.2.primeIdealOf ⟨y, hy⟩).asIdeal D hrank m f hrspP
  have hb : (fun i => KaehlerDifferential.D K (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal)
      (algebraMap Γ(Y, U.1) _ (x i))) = bs := funext fun i => (hbs i).symm
  obtain ⟨s, hs, hspread⟩ := basis_spread K Γ(Y, U.1) (U.2.primeIdealOf ⟨y, hy⟩).asIdeal x
    ⟨by rw [hb]; exact bs.linearIndependent, by rw [hb]; exact bs.span_eq⟩
  exact ⟨s, x, e, (hmem s).2 hs, hxe, isCoords_basicOpen K Y g U s x hspread⟩

theorem exists_perm_first {D : ℕ} (E : Finset (Fin D)) :
    ∃ σ : Fin D ≃ Fin D, ∀ i : Fin D, (i : ℕ) < E.card ↔ σ i ∈ E := by
  classical
  have hk : E.card ≤ D := by simpa using E.card_le_univ
  have h1 : Fintype.card {i : Fin D // (i : ℕ) < E.card} = Fintype.card {b : Fin D // b ∈ E} := by
    rw [Fintype.card_coe]
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun i : Fin D => (i : ℕ) < E.card) = (Finset.range E.card).attachFin (fun _ h => by simp at h; omega) := by
      ext i; simp
    rw [this, Finset.card_attachFin, Finset.card_range]
  have h2 : Fintype.card {i : Fin D // ¬ (i : ℕ) < E.card} = Fintype.card {b : Fin D // ¬ b ∈ E} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  let σ := Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2)
  refine ⟨σ, fun i => ?_⟩
  by_cases hi : (i : ℕ) < E.card
  · have : σ i = ((Fintype.equivOfCardEq h1) ⟨i, hi⟩ : Fin D) := by
      simp only [σ, Equiv.subtypeCongr, Equiv.trans_apply]
      rw [Equiv.sumCompl_symm_apply_of_pos (p := fun x : Fin D => (x : ℕ) < E.card) hi]; rfl
    rw [this]
    exact iff_of_true hi ((Fintype.equivOfCardEq h1) ⟨i, hi⟩).2
  · have : σ i = ((Fintype.equivOfCardEq h2) ⟨i, hi⟩ : Fin D) := by
      simp only [σ, Equiv.subtypeCongr, Equiv.trans_apply]
      rw [Equiv.sumCompl_symm_apply_of_neg (p := fun x : Fin D => (x : ℕ) < E.card) hi]; rfl
    rw [this]
    exact iff_of_false hi ((Fintype.equivOfCardEq h2) ⟨i, hi⟩).2

theorem isCoords_comp_equiv {K : Type} [Field K] {Y : Scheme.{0}} (g : Y ⟶ Sp K) (V : Y.Opens) {D : ℕ}
    (z : Fin D → Γ(Y, V)) (σ : Fin D ≃ Fin D) (h : IsCoords g V z) : IsCoords g V (z ∘ σ) := by
  letI := secAlgebra g V
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · exact h1.comp σ σ.injective
  · have : (Set.range fun i => KaehlerDifferential.D K Γ(Y, V) ((z ∘ σ) i)) =
        Set.range fun i => KaehlerDifferential.D K Γ(Y, V) (z i) :=
      σ.surjective.range_comp (fun i => KaehlerDifferential.D K Γ(Y, V) (z i))
    rw [this]; exact h2

theorem mem_basicOpen_prod {ι : Type} {Y : Scheme.{0}} {U : Y.Opens} (J : Finset ι) (f : ι → Γ(Y, U)) (w : Y) :
    w ∈ Y.basicOpen (∏ j ∈ J, f j) ↔ w ∈ U ∧ ∀ j ∈ J, w ∈ Y.basicOpen (f j) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [Scheme.basicOpen_one]
  | insert a J ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul]
    simp only [TopologicalSpace.Opens.mem_inf, ih, Finset.mem_insert, forall_eq_or_imp]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩
    · rintro ⟨h2, h1, h3⟩; exact ⟨h1, h2, h3⟩

theorem inter_eq_of_ideal {Y : Scheme.{0}} (T : Set Y) (hT : IsClosed T) (U : Y.affineOpens) (p : Γ(Y, U.1))
    (h : (Scheme.IdealSheafData.vanishingIdeal ⟨T, hT⟩).ideal U = Ideal.span {p}) :
    ((U.1 : Y.Opens) : Set Y) ∩ T = {x | x ∈ U.1 ∧ x ∉ Y.basicOpen p} := by
  have hsupp : ∀ x, x ∈ (Scheme.IdealSheafData.vanishingIdeal ⟨T, hT⟩).support ↔ x ∈ T := fun x => by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  ext x
  constructor
  · rintro ⟨hU, hx⟩
    refine ⟨hU, ?_⟩
    have hs := (hsupp x).2 hx
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hU, h, Scheme.mem_zeroLocus_iff] at hs
    exact hs p (Ideal.subset_span rfl)
  · rintro ⟨hU, hx⟩
    refine ⟨hU, (hsupp x).1 ?_⟩
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hU, h, Scheme.mem_zeroLocus_iff]
    intro q hq hqx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hq
    rw [Scheme.basicOpen_mul] at hqx
    exact hx hqx.2

theorem point_coords (K : Type) [Field K] [CharZero K] (D : ℕ) (Y : Scheme.{0}) (g : Y ⟶ Sp K)
    (T : Set Y) (hT : IsClosed T) (hD : SmoothOfRelativeDimension D g)
    (hsnc : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal ⟨T, hT⟩)) (y : Y) :
    ∃ (V : Y.affineOpens) (z : Fin D → Γ(Y, V.1)) (k : ℕ), y ∈ V.1 ∧ k ≤ D ∧ IsCoords g V.1 z ∧
      ((V.1 : Y.Opens) : Set Y) ∩ T = {x | x ∈ V.1 ∧ ∃ i : Fin D, (i : ℕ) < k ∧ x ∉ Y.basicOpen (z i)} := by
  classical
  obtain ⟨hreg, U, hy, m, f, J, hrsp, hid⟩ := hsnc y
  obtain ⟨s, x, e, hys, hxe, hco⟩ := coords_at_point K D Y g hD U y hy hreg m f hrsp
  obtain ⟨σ, hσ⟩ := exists_perm_first (J.map e)
  let r : Fin D → Γ(Y, Y.basicOpen s) := fun i => Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op (x i)
  have hr : ∀ i w, w ∈ Y.basicOpen s → (w ∈ Y.basicOpen (r i) ↔ w ∈ Y.basicOpen (x i)) := fun i w hw => by
    simp only [r, Scheme.basicOpen_res, TopologicalSpace.Opens.mem_inf, hw, true_and]
  have hset := inter_eq_of_ideal T hT U _ hid
  refine ⟨⟨Y.basicOpen s, U.2.basicOpen s⟩, r ∘ σ, (J.map e).card, hys,
    by simpa using (J.map e).card_le_univ, isCoords_comp_equiv g _ r σ hco, ?_⟩
  ext w
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Function.comp_apply]
  constructor
  · rintro ⟨hw, hwT⟩
    have hwU : w ∈ U.1 := Y.basicOpen_le s hw
    have h1 : w ∉ Y.basicOpen (∏ j ∈ J, f j) := (hset.subset ⟨hwU, hwT⟩).2
    rw [mem_basicOpen_prod] at h1
    push_neg at h1
    obtain ⟨j, hj, hwj⟩ := h1 hwU
    refine ⟨hw, σ.symm (e j), (hσ _).2 (by rw [Equiv.apply_symm_apply]; exact Finset.mem_map_of_mem e hj), ?_⟩
    rw [Equiv.apply_symm_apply, hr _ _ hw, hxe]; exact hwj
  · rintro ⟨hw, i, hi, hwi⟩
    have hwU : w ∈ U.1 := Y.basicOpen_le s hw
    refine ⟨hw, (hset.superset ⟨hwU, ?_⟩).2⟩
    obtain ⟨j, hj, hje⟩ := Finset.mem_map.1 ((hσ i).1 hi)
    rw [mem_basicOpen_prod]
    rintro ⟨-, hall⟩
    rw [hr _ _ hw, ← hje, hxe] at hwi
    exact hwi (hall j hj)

theorem hasSncCoords_of_local {K : Type} [Field K] (D : ℕ) {Y : Scheme.{0}} [CompactSpace Y] (g : Y ⟶ Sp K)
    (T : Set Y)
    (h : ∀ y : Y, ∃ (V : Y.affineOpens) (z : Fin D → Γ(Y, V.1)) (k : ℕ), y ∈ V.1 ∧ k ≤ D ∧ IsCoords g V.1 z ∧
      ((V.1 : Y.Opens) : Set Y) ∩ T = {x | x ∈ V.1 ∧ ∃ i : Fin D, (i : ℕ) < k ∧ x ∉ Y.basicOpen (z i)}) :
    HasSncCoords g D T := by
  classical
  choose V z k hy hk hz hT using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => ((V y).1 : Set Y)) (fun y => (V y).1.isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩)
  refine ⟨t.card, fun j => V (t.equivFin.symm j), fun y => ?_, fun j => ⟨z _, k _, hk _, hz _, hT _⟩⟩
  obtain ⟨a, ha, h⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  exact ⟨t.equivFin ⟨a, ha⟩, by simpa using h⟩

theorem coordsStatement : CoordsStatement := by
  intro K _ _ D Y g W T hT hc hs hW hWD hsnc
  have hD : SmoothOfRelativeDimension D g := relDim_of_dense g D W hW hWD
  exact ⟨hD, hasSncCoords_of_local D g T (point_coords K D Y g T hT hD hsnc)⟩

end GlobalTheory.CompanionTheory.Geo.SncCoords
