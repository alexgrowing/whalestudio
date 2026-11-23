import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Columns.PathCountSymmetricHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameCfgRefl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsLiftsHeckeOperatorsCommute
import Formalism.LocalToGlobal.Columns.ColumnsProofs.HeckeFieldSplit
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section
namespace GlobalTheory.Mem.HFld.Transp
open Formalism.L2.Col Polynomial

theorem chiC_apply {B : Base} {px : PreX B.toPre} (I : Col2.ColIn B px) (j : Fin B.R.m)
    (w : {w // w ∈ (B.primes px).vGs}) (y : 𝓞 B.host.E) (hu : IsUnit (Ideal.Quotient.mk w.1.asIdeal y)) :
    chiC I j w.1 y = B.embLL ((I.Ch.chi j w hu.unit : B.LLˣ) : B.LL) := by
  unfold chiC
  rw [dif_pos w.2, dif_pos hu]

theorem qC_xi {B : Base} {px : PreX B.toPre} {I : Col2.ColIn B px} (hI : I.Ok) (a : I.ι) : qC I (I.xi a) = I.Q a := by
  unfold qC
  rw [dif_pos ⟨a, rfl⟩]
  congr 1
  exact hI.xi_inj (Exists.choose_spec (⟨a, rfl⟩ : ∃ a', I.xi a' = I.xi a))

theorem rowTyQ_congr {X : Fields} (R : Ranks) {ξ ξ' : Chr X.F X.E X.K} (h : ξ = ξ')
    {Q Q' : Finset (HeightOneSpectrum (𝓞 X.E))} (Pp : Q) (hp : Pp.1 ∈ Q') :
    rowTyQ R ξ Q Pp = rowTyQ R ξ' Q' ⟨Pp.1, hp⟩ := by
  subst h
  rfl

theorem mtTyQ_congr {X : Fields} (R : Ranks) {ξ ξ' : Chr X.F X.E X.K} (h : ξ = ξ')
    {Q Q' : Finset (HeightOneSpectrum (𝓞 X.E))} (Pp : Q) (hp : Pp.1 ∈ Q') :
    mtTyQ R ξ Q Pp = mtTyQ R ξ' Q' ⟨Pp.1, hp⟩ := by
  subst h
  rfl

set_option maxHeartbeats 6000000 in
theorem core (B0 : Base) (px0 : PreX B0.toPre) (I0 : Col2.ColIn B0 px0) (B : Base) (px : PreX B.toPre)
    (I : Col2.ColIn B px) (hX0 : B0.fields.Ok) (hI0 : I0.Ok) (hI : I.Ok) (hcfg : SameCfg B px I B0 px0 I0)
    (ι : B0.LL →+* B.LL) (hι : B.embLL.comp ι = B0.embLL) (a : I.ι) :
    ∃ a0 : I0.ι, (∀ p : B0.LL[X], HeckePolyFor (heckeFamAll (rowPts B0.wts I0.Ch I0.sel (I0.tup a0)) ∅) p →
        (p.map ι).Splits → HeckeFieldsInAll (rowPts B.wts I.Ch I.sel (I.tup a)) ∅) ∧
      ∀ j : Fin B.R.m, ∀ p : B0.LL[X],
        HeckePolyFor (heckeFamAll (liftPts B0.wts I0.Ch I0.sel (I0.tup a0) (j.1 + 1)) ∅) p →
        (p.map ι).Splits → HeckeFieldsInAll (liftPts B.wts I.Ch I.sel (I.tup a) (j.1 + 1)) ∅ := by
  obtain ⟨hP, -, hXi, hpiG, hchi, hq⟩ := hcfg
  have hQa := qC_xi hI a
  have hxr := hI.xi_reads a
  have hchiA := chiC_apply I
  obtain ⟨P, LL, embLL, hcx, embE, hφ, LL0, _, Ks, _, _, _, _, _, _, _, _⟩ := B
  obtain ⟨P0, LL', embLL', hcx', embE', hφ', LL0', g0, Ks', k1, k2, k3, k4, k5, k6, k7, k8⟩ := B0
  obtain rfl : P = P0 := hP
  change LL' →+* LL at ι
  have hι' : ∀ x, embLL (ι x) = embLL' x := fun x => RingHom.congr_fun hι x
  have hE : embE = ι.comp embE' := by
    ext x
    apply embLL.injective
    have h1 := RingHom.congr_fun hφ x
    have h2 := RingHom.congr_fun hφ' x
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    rw [h1, hι', h2]
  subst hE
  obtain ⟨piG, _, _, _, piT, _, _, _, _, _, _, _, _, _, _, _, _⟩ := px
  obtain ⟨piG', _, _, _, piT', _, _, _, _, _, _, _, _, _, _, _, _⟩ := px0
  obtain rfl : piG = piG' := eq_of_heq hpiG
  have hXi' := eq_of_heq hXi
  obtain ⟨a0, ha0⟩ : ∃ a0, I0.xi a0 = I.xi a := by
    have h : I.xi a ∈ Set.range I.xi := ⟨a, rfl⟩
    rw [hXi'] at h
    exact h
  have hQ : I.Q a = I0.Q a0 := by
    rw [← hQa, ← qC_xi hI0 a0, ha0]
    exact congrFun (eq_of_heq hq) _
  have htup : (I.tup a).1 = chrMap ι (I0.tup a0).1 := by
    refine hxr.inj ?_
    intro x
    rw [← ha0]
    refine (hI0.xi_reads a0 x).trans ?_
    exact (hι' _).symm
  have hchi' := eq_of_heq hchi
  have hch : ∀ (j : Fin P.R.m) w, I.Ch.chi j w = (Units.map ι.toMonoidHom).comp (I0.Ch.chi j w) := by
    intro j w
    ext u
    apply embLL.injective
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 P.host.E ⧸ w.1.asIdeal)
    have hu : IsUnit (Ideal.Quotient.mk w.1.asIdeal y) := hy ▸ u.isUnit
    have hu' : hu.unit = u := Units.ext (by rw [IsUnit.unit_spec]; exact hy)
    have h1 := congrFun (congrFun (congrFun hchi' j) w.1) y
    rw [hchiA j w y hu, chiC_apply I0 j w y hu, hu'] at h1
    refine h1.trans ?_
    exact (hι' _).symm
  let B0' : Base := ⟨P, LL', embLL', hcx', embE', hφ', LL0', g0, Ks', k1, k2, k3, k4, k5, k6, k7, k8⟩
  have hQ' : QE I.sel (I.tup a).1 = QE I0.sel (I0.tup a0).1 := hQ
  have hca : ∀ w s, chiAt I.Ch w s = (Units.map ι.toMonoidHom).comp (chiAt I0.Ch w s) := by
    intro w s
    unfold chiAt
    rw [← extChi_coefMap]
    exact congrArg (fun f => extChi f s) (funext fun j => hch j w)
  have hA : rowTyK (R := P.R) I.Ch = (rowTyK (R := P.R) I0.Ch).coefMap ι := by
    funext w
    exact congrArg (Lev.mk (HKJ (𝓞 P.host.E ⧸ w.1.asIdeal) (P.R.N P.R.m - 1) P.R.r P.R.t P.R.m))
      ((congrArg (fun χ => lamK χ (P.R.N P.R.m - 1) P.R.r (List.replicate P.R.m P.R.t)) (funext (hca w))).trans
        (lamK_coefMap ι _ _ _))
  have hAm : ∀ k, mtTyK (R := P.R) I.Ch k = (mtTyK (R := P.R) I0.Ch k).coefMap ι := by
    intro k
    funext w
    have h : (fun _ : ℕ => (chiAt I.Ch w (k - 1))⁻¹) =
        fun _ : ℕ => (Units.map ι.toMonoidHom).comp (chiAt I0.Ch w (k - 1))⁻¹ :=
      funext fun _ => (congrArg (·⁻¹) (hca w (k - 1))).trans (coefMap_comp_inv ι _)
    exact congrArg (Lev.mk (HKV (𝓞 P.host.E ⧸ w.1.asIdeal) P.R.nV P.R.r P.R.t))
      ((congrArg (fun χ => lamK χ P.R.nV P.R.r [P.R.t]) h).trans (lamK_coefMap ι _ _ _))
  have hB : ∀ Pp : {Pp // Pp ∈ QE I.sel (I.tup a).1},
      rowTyQ P.R (I.tup a).1 (QE I.sel (I.tup a).1) Pp =
        (rowTyQ P.R (I0.tup a0).1 (QE I0.sel (I0.tup a0).1) ⟨Pp.1, hQ' ▸ Pp.2⟩).coefMap ι := by
    intro Pp
    rw [← rowTyQ_coefMap (L := LL) (ι := ι) P.R (I0.tup a0) (QE I0.sel (I0.tup a0).1) ⟨Pp.1, hQ' ▸ Pp.2⟩]
    exact rowTyQ_congr P.R htup Pp _
  have hBm : ∀ Pp : {Pp // Pp ∈ QE I.sel (I.tup a).1},
      mtTyQ P.R (I.tup a).1 (QE I.sel (I.tup a).1) Pp =
        (mtTyQ P.R (I0.tup a0).1 (QE I0.sel (I0.tup a0).1) ⟨Pp.1, hQ' ▸ Pp.2⟩).coefMap ι := by
    intro Pp
    rw [← mtTyQ_coefMap (L := LL) (ι := ι) P.R (I0.tup a0) (QE I0.sel (I0.tup a0).1) ⟨Pp.1, hQ' ▸ Pp.2⟩]
    exact mtTyQ_congr P.R htup Pp _
  have hTy : rowTyKK (R := P.R) I.Ch I.sel (I.tup a) =
      ((rowTyKK (R := P.R) I0.Ch I0.sel (I0.tup a0)).coefMap ι).reidx (congrArg (uSG _) hQ') :=
    LevFam.glue_coefMap_reidx ι hQ' _ _ _ _ hA hB
  have hTyL : ∀ k, mtTyKK (R := P.R) I.Ch I.sel (I.tup a) k =
      ((mtTyKK (R := P.R) I0.Ch I0.sel (I0.tup a0) k).coefMap ι).reidx (congrArg (uSG _) hQ') := fun k =>
    LevFam.glue_coefMap_reidx ι hQ' _ _ _ _ (hAm k) hBm
  refine ⟨a0, fun p hp hsp => ?_, fun j p hp hsp => ?_⟩
  · unfold HeckeFieldsInAll rowPts mtildeKGSD at *
    rw [hTy]
    have hfd := GSD.finiteDimensional_EqFun _ (mtildeKOk B0'.wts I0.Ch I0.sel (I0.tup a0) hX0)
    have key := hfs_splitAll_sq_reidx (X := B0'.fields) (L := LL) ι (congrArg (uSG _) hQ') B0'.wts.sgTrue
      (rowTyKK (R := P.R) I0.Ch I0.sel (I0.tup a0)) ∅ hfd (GlobalTheory.InertSame.heckeCommAll_all _ _) hp hsp
    exact key
  · unfold HeckeFieldsInAll liftPts mtKGSD at *
    rw [hTyL]
    have hfd := GSD.finiteDimensional_EqFun _ (mtKOk B0'.wts I0.Ch I0.sel (I0.tup a0) hX0 (j.1 + 1))
    have key := hfs_splitAll_rd_reidx (X := B0'.fields) (L := LL) ι (congrArg (uSG _) hQ') (B0'.wts.lamV (j.1 + 1))
      (mtTyKK (R := P.R) I0.Ch I0.sel (I0.tup a0) (j.1 + 1)) ∅ hfd (GlobalTheory.InertSame.heckeCommAll_all _ _) hp hsp
    exact key

theorem splits_of_roots_mem {K L : Type} [Field K] [Field L] (σ0 : K →+* ℂ) (σ : L →+* ℂ) (ι : K →+* L)
    (hι : σ.comp ι = σ0) (p : K[X]) (hr : ∀ z ∈ (p.map σ0).roots, ∃ y, σ y = z) : (p.map ι).Splits := by
  refine Polynomial.Splits.of_splits_map σ ?_ ?_
  · rw [Polynomial.map_map, hι]
    exact IsAlgClosed.splits _
  · intro z hz
    rw [Polynomial.map_map, hι] at hz
    obtain ⟨y, hy⟩ := hr z hz
    exact ⟨y, hy⟩

theorem transp : ∀ (B0 : Base) (px0 : PreX B0.toPre) (I0 : Col2.ColIn B0 px0), B0.fields.Ok → I0.Ok →
  ∃ s : Finset ℂ, (∀ z ∈ s, IsAlgebraic ℚ z) ∧
    ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), B.fields.Ok → I.Ok → GlobalTheory.Mem.HFld.SameCfg B px I B0 px0 I0 →
      (∀ z ∈ s, z ∈ B.LLC) → ∀ a : I.ι,
        Formalism.L2.Col.HeckeFieldsInAll (rowPts B.wts I.Ch I.sel (I.tup a)) ∅ ∧
          ∀ j : Fin B.R.m, Formalism.L2.Col.HeckeFieldsInAll (liftPts B.wts I.Ch I.sel (I.tup a) (j.1 + 1)) ∅ := by
  intro B0 px0 I0 hX0 hI0
  classical
  have hR : ∀ a0 : I0.ι, ∃ p, HeckePolyFor (heckeFamAll (rowPts B0.wts I0.Ch I0.sel (I0.tup a0)) ∅) p := fun a0 => by
    haveI := GSD.finiteDimensional_EqFun _ (mtildeKOk B0.wts I0.Ch I0.sel (I0.tup a0) hX0)
    exact hfs_exists_poly _
  have hL : ∀ (a0 : I0.ι) (k : ℕ), ∃ p, HeckePolyFor (heckeFamAll (liftPts B0.wts I0.Ch I0.sel (I0.tup a0) k) ∅) p :=
    fun a0 k => by
      haveI := GSD.finiteDimensional_EqFun _ (mtKOk B0.wts I0.Ch I0.sel (I0.tup a0) hX0 k)
      exact hfs_exists_poly _
  choose pR hpR using hR
  choose pL hpL using hL
  let bas := Module.finBasis ℚ B0.LL
  let rts : B0.LL[X] → Finset ℂ := fun p => (p.map B0.embLL).roots.toFinset
  let s : Finset ℂ := Finset.univ.image (fun i => B0.embLL (bas i)) ∪
    Finset.univ.biUnion (fun a0 : I0.ι => rts (pR a0) ∪ (Finset.range B0.R.m).biUnion (fun k => rts (pL a0 (k + 1))))
  have hrts : ∀ p : B0.LL[X], p ≠ 0 → ∀ z ∈ rts p, IsAlgebraic ℚ z := by
    intro p hp z hz
    letI : Algebra B0.LL ℂ := B0.embLL.toAlgebra
    haveI : IsScalarTower ℚ B0.LL ℂ := IsScalarTower.of_algebraMap_eq fun q => by simp
    have h1 : IsAlgebraic B0.LL z := ⟨p, hp, by
      have h2 : z ∈ (p.map B0.embLL).roots := Multiset.mem_toFinset.1 hz
      rw [Polynomial.mem_roots (Polynomial.map_ne_zero hp)] at h2
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      exact h2⟩
    exact h1.restrictScalars ℚ
  refine ⟨s, ?_, ?_⟩
  · intro z hz
    rcases Finset.mem_union.1 hz with h | h
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      exact (isAlgebraic_algHom_iff B0.embLL.toRatAlgHom B0.embLL.injective).2 (Algebra.IsAlgebraic.isAlgebraic _)
    · obtain ⟨a0, -, h⟩ := Finset.mem_biUnion.1 h
      rcases Finset.mem_union.1 h with h | h
      · exact hrts _ (hpR a0).1 z h
      · obtain ⟨k, -, h⟩ := Finset.mem_biUnion.1 h
        exact hrts _ (hpL a0 (k + 1)).1 z h
  · intro B px I hX hI hcfg hs a
    have hm : B.R.m = B0.R.m := congrArg (fun P : Pre => P.R.m) hcfg.1
    have hLL : ∀ x : B0.LL, ∃ y : B.LL, B.embLL y = B0.embLL x := by
      intro x
      have hb : ∀ i, B0.embLL (bas i) ∈ B.LLC := fun i =>
        hs _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
      have hx : B0.embLL x ∈ B.LLC := by
        rw [← bas.sum_repr x, map_sum]
        refine sum_mem fun i _ => ?_
        rw [map_rat_smul]
        exact SMulMemClass.smul_mem _ (hb i)
      exact hx
    choose f hf using hLL
    let ι : B0.LL →+* B.LL :=
      { toFun := f
        map_one' := B.embLL.injective (by rw [hf, map_one, map_one])
        map_mul' := fun x y => B.embLL.injective (by rw [hf, map_mul, map_mul, hf, hf])
        map_zero' := B.embLL.injective (by rw [hf, map_zero, map_zero])
        map_add' := fun x y => B.embLL.injective (by rw [hf, map_add, map_add, hf, hf]) }
    have hι : B.embLL.comp ι = B0.embLL := RingHom.ext hf
    have hsp : ∀ p : B0.LL[X], (∀ z ∈ rts p, z ∈ s) → (p.map ι).Splits := fun p hp =>
      splits_of_roots_mem B0.embLL B.embLL ι hι p fun z hz => hs z (hp z (Multiset.mem_toFinset.2 hz))
    obtain ⟨a0, hrow, hlift⟩ := core B0 px0 I0 B px I hX0 hI0 hI hcfg ι hι a
    refine ⟨hrow (pR a0) (hpR a0) (hsp _ fun z hz => ?_), fun j => hlift j (pL a0 (j.1 + 1)) (hpL a0 (j.1 + 1))
      (hsp _ fun z hz => ?_)⟩
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨a0, Finset.mem_univ _, Finset.mem_union_left _ hz⟩)
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨a0, Finset.mem_univ _, Finset.mem_union_right _ ?_⟩)
      exact Finset.mem_biUnion.2 ⟨j.1, Finset.mem_range.2 (hm ▸ j.2), hz⟩

end GlobalTheory.Mem.HFld.Transp
