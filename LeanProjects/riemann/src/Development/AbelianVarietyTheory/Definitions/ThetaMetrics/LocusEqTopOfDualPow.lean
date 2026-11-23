import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

noncomputable section

namespace GlobalTheory.AmpleModel

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LBGerm GlobalTheory.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}}

theorem locus_eq_top_of_dual_pow [IrreducibleSpace X] (hF : IsField Γ(X, ⊤)) {L : LB X} (hL : L.IsLB) {n : ℕ}
    (hn : 1 ≤ n) (t : (lbPow (CechPic.dual L) n).Sec) (ht : nonzeroLocus t ≠ ⊥) (s : L.Sec)
    (hs : nonzeroLocus s ≠ ⊥) : nonzeroLocus s = ⊤ := by
  obtain ⟨τ, hτ⟩ : ∃ τ : ∀ i, Γ(X, L.U i), ∀ i, τ i = powSecFn t i := ⟨fun i => powSecFn t i, fun _ => rfl⟩
  let f : ∀ i, Γ(X, L.U i) := fun i => τ i * s.f i ^ n
  have hc : TopCat.Presheaf.IsCompatible X.presheaf L.U f := fun i j => by
    have e1 := powSecFn_compat t i j
    have e2 := s.compat i j
    rw [← hτ, ← hτ] at e1
    change resG X (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (τ i) =
      ((L.g i j)⁻¹).val ^ n * resG X (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (τ j) at e1
    change resG X (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (s.f i) =
      (L.g i j).val * resG X (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (s.f j) at e2
    change resG X (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (f i) = resG X (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (f j)
    simp only [f, map_mul, map_pow]
    rw [e1, e2, mul_pow, mul_mul_mul_comm, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  obtain ⟨c, hc', -⟩ := X.sheaf.existsUnique_gluing' L.U ⊤ (fun i => homOfLE le_top) hL.cover.ge f hc
  have hci : ∀ i, resG X (le_top : L.U i ≤ ⊤) c = f i := hc'
  have hb : ∀ i, L.U i ⊓ X.basicOpen c = nonzeroLocus t ⊓ nonzeroLocus s ⊓ L.U i := fun i => by
    have e : X.basicOpen (resG X (le_top : L.U i ≤ ⊤) c) = L.U i ⊓ X.basicOpen c := X.basicOpen_res _ _
    have e3 : X.basicOpen (τ i) = nonzeroLocus t ⊓ L.U i := (hτ i).symm ▸ (nonzeroLocus_inf_powSecFn t i).symm
    rw [← e, hci, Scheme.basicOpen_mul, X.basicOpen_pow _ hn, e3, ← nonzeroLocus_inf_chart]
    ext y
    exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, h.2⟩⟩⟩
  have ne : ∀ U : X.Opens, U ≠ ⊥ → (U : Set X).Nonempty := fun U h => (Opens.ne_bot_iff_nonempty U).1 h
  obtain ⟨y, hyt, hys⟩ := nonempty_preirreducible_inter (nonzeroLocus t).isOpen (nonzeroLocus s).isOpen (ne _ ht) (ne _ hs)
  obtain ⟨i, hi⟩ := exists_chart hL y
  have hy : y ∈ X.basicOpen c := ((hb i).ge ⟨⟨hyt, hys⟩, hi⟩).2
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact (X.basicOpen_zero ⊤).le hy
  obtain ⟨d, hd⟩ := hF.mul_inv_cancel hc0
  have hu : X.basicOpen c = ⊤ := X.basicOpen_of_isUnit (IsUnit.of_mul_eq_one d hd)
  refine top_le_iff.1 fun z _ => ?_
  obtain ⟨j, hj⟩ := exists_chart hL z
  exact ((hb j).le ⟨hj, hu.ge trivial⟩).1.2

variable (K : Type) [Field K] (N : ℕ)

instance isIntegral_chartCover (i : Fin (N + 1)) : IsIntegral (Sp (MvPolynomial {j // j ≠ i} K)) := inferInstance

def genericPt : ProjectiveSpectrum (grading K N) where
  asHomogeneousIdeal := ⊥
  isPrime := Ideal.isPrime_bot
  not_irrelevant_le h := by
    have := h (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos (X_mem K N 0))
    exact X_ne_zero _ this

instance irreducibleSpace : IrreducibleSpace (PSpace K N) := by
  have h : closure {genericPt K N} = (Set.univ : Set (ProjectiveSpectrum (grading K N))) :=
    Set.eq_univ_of_forall fun x => (ProjectiveSpectrum.le_iff_mem_closure _ _ x).1 (show ⊥ ≤ x.asHomogeneousIdeal from bot_le)
  have h2 : IsIrreducible (Set.univ : Set (ProjectiveSpectrum (grading K N))) := h ▸ isIrreducible_singleton.closure
  exact (irreducibleSpace_def _).2 h2

instance isIntegral : IsIntegral (PSpace K N) := by
  have : ∀ i, IsReduced ((chartCover K N).X i) := fun i =>
    inferInstanceAs (IsReduced (Sp (MvPolynomial {j // j ≠ i} K)))
  have : IsReduced (PSpace K N) := IsReduced.of_openCover _ (chartCover K N)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem isField_global : IsField Γ(PSpace K N, ⊤) :=
  have := isProper_str K N
  isField_of_universallyClosed K (PSpace.str K N)

theorem coord_ne_bot : nonzeroLocus (coord K 1 1) ≠ ⊥ := by
  rw [nonzeroLocus_coord, Opens.ne_bot_iff_nonempty]
  exact ⟨genericPt K 1, fun h => X_ne_zero (R := K) (1 : Fin 2) h⟩

theorem coord_ne_top : nonzeroLocus (coord K 1 1) ≠ ⊤ := by
  intro h
  rw [nonzeroLocus_coord] at h
  have h1 : (PSpace K 1).basicOpen (ratio K 1 0 1) = chart K 1 0 :=
    basicOpen_ratioOn.trans ((congrArg (_ ⊓ ·) h).trans (inf_top_eq _))
  have h2 : IsUnit (ratio K 1 0 1) := (PSpace K 1).toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx =>
    ((PSpace K 1).mem_basicOpen _ x hx).1 (h1.ge hx)
  rw [← chartAlgEquiv_X K 1 0 ⟨1, by decide⟩] at h2
  have h3 := (h2.map (chartAlgEquiv K 1 0).symm).map constantCoeff
  rw [AlgEquiv.symm_apply_apply, constantCoeff_X] at h3
  exact not_isUnit_zero h3

theorem locus_dual_O1_pow {n : ℕ} (hn : 1 ≤ n) (t : (lbPow (CechPic.dual (O1 K 1)) n).Sec) : nonzeroLocus t = ⊥ := by
  by_contra ht
  exact coord_ne_top K (locus_eq_top_of_dual_pow (isField_global K 1) (O1_isLB K 1) hn t ht _ (coord_ne_bot K))

theorem not_isAmpleLB_dual_O1 : (CechPic.dual (O1 K 1)).IsLB ∧ ¬ IsAmpleLB (CechPic.dual (O1 K 1)) := by
  refine ⟨CechPic.isLB_dual (O1_isLB K 1), fun h => ?_⟩
  obtain ⟨n, hn, t, ht, -⟩ := h.exists_affine (genericPt K 1)
  rw [locus_dual_O1_pow K hn t] at ht
  exact ht

theorem not_isGenerated_dual_O1 : ¬ IsGenerated (CechPic.dual (O1 K 1)) := fun h => by
  obtain ⟨t, ht⟩ := h.exists_mem (genericPt K 1)
  rw [← nonzeroLocus_secToPow t le_rfl, locus_dual_O1_pow K le_rfl] at ht
  exact ht

theorem not_isAmpleLB_triv : IsGenerated (LB.triv (PSpace K 1)) ∧ ¬ IsAmpleLB (LB.triv (PSpace K 1)) := by
  refine ⟨isGenerated_triv _, fun h => ?_⟩
  have hq := isAmpleLB_triv_iff.1 h
  obtain ⟨x, hx⟩ := (Opens.ne_bot_iff_nonempty _).1 (coord_ne_bot K)
  obtain ⟨_, ⟨r, -, rfl⟩, hxr, hle⟩ := Opens.isBasis_iff_nbhd.1 (Scheme.IsQuasiAffine.isBasis_basicOpen (PSpace K 1)) hx
  have hr : r ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hxr
    exact hxr
  obtain ⟨d, hd⟩ := (isField_global K 1).mul_inv_cancel hr
  rw [(PSpace K 1).basicOpen_of_isUnit (IsUnit.of_mul_eq_one d hd)] at hle
  exact coord_ne_top K (top_le_iff.1 hle)

theorem ample_not_quasiAffine : IsAmpleLB (O1 K 1) ∧ ¬ (PSpace K 1).IsQuasiAffine :=
  ⟨isAmple_projective_O_one K 1, fun h => (not_isAmpleLB_triv K).2 (isAmpleLB_triv_iff.2 h)⟩

theorem not_isAmpleLB_pow_zero : ¬ IsAmpleLB (lbPow (O1 K 1) 0) := fun h =>
  (not_isAmpleLB_triv K).2 (h.of_lbIso (LB.isLB_triv _) (by
    refine ⟨⟨fun _ => 1⟩, fun p q => ?_⟩
    simp only [map_one, mul_one]
    have e := On_g K 1 0 p.1 q.1
    rw [zpow_zero] at e
    have e' : (lbPow (O1 K 1) 0).g p.1 q.1 = 1 := e
    simp only [LB.div, e', map_one, one_mul]
    exact Units.ext rfl))

theorem empty_ample [IsEmpty X] (L : LB X) : IsAmpleLB L ∧ IsGenerated L := by
  have hg : IsGenerated L := ⟨0, Fin.elim0, by ext x; exact isEmptyElim x⟩
  exact ⟨⟨hg.isLB, ⟨(Set.toFinite _).isCompact⟩, fun x => isEmptyElim x⟩, hg⟩

def signData (X : Scheme.{0}) : LB X := ⟨PUnit, fun _ => ⊤, fun _ _ => -1⟩

theorem signData_not_ample : ¬ IsAmpleLB (signData (Sp ℚ)) ∧ ¬ IsGenerated (signData (Sp ℚ)) ∧
    ∃ s : (lbPow (signData (Sp ℚ)) 2).Sec, nonzeroLocus s = ⊤ ∧ IsAffineOpen (nonzeroLocus s) := by
  have h : ¬ (signData (Sp ℚ)).IsLB := fun h => by
    have e := congrArg Units.val (h.g_self PUnit.unit)
    change resG (Sp ℚ) (le_inf le_rfl le_rfl : (⊤ : (Sp ℚ).Opens) ≤ ⊤ ⊓ ⊤) (-1) = 1 at e
    rw [map_neg, map_one] at e
    have e2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of ℚ)).hom.hom e
    rw [map_neg, map_one] at e2
    norm_num at e2
  let s : (lbPow (signData (Sp ℚ)) 2).Sec := powSecMk 2 (fun _ => 1) fun _ _ => by
    rw [map_one, map_one, mul_one]
    exact (neg_one_sq).symm
  have hs : nonzeroLocus s = ⊤ := by
    rw [nonzeroLocus_powSecMk]
    exact top_le_iff.1 (le_iSup_of_le PUnit.unit ((Sp ℚ).basicOpen_one (U := ⊤)).ge)
  exact ⟨fun h' => h h'.isLB, fun h' => h h'.isLB, s, hs, hs ▸ isAffineOpen_top _⟩

end GlobalTheory.AmpleModel
