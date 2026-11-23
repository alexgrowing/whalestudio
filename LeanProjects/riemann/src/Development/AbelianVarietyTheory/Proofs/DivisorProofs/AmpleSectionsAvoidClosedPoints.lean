import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EventuallySectionAndRelAmplePowDiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsSecNeObj

set_option autoImplicit false

noncomputable section

open NumberField CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.CechPic

namespace GlobalTheory.GenFibreSecs

theorem cls_comb {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {ι : Type} [Fintype ι]
    (L : ι → HermLB p) (n : ι → ℤ) :
    cls _ (ArInt.comb L n).isLB = ∑ i, n i • cls _ (L i).isLB := by
  have hz (A : HermLB p) (m : ℤ) : cls _ (zp A m).isLB = m • cls _ A.isLB := by
    have e : cls _ (zp A m).isLB = cls _ (isLB_lbPow A.isLB m.toNat) + -cls _ (isLB_lbPow A.isLB (-m).toNat) :=
      (cls_tens (A.pow m.toNat).isLB (A.pow (-m).toNat).dual.isLB _).trans
        (congrArg _ (cls_dual (A.pow (-m).toNat).isLB _))
    rw [e, cls_lbPow A.isLB, cls_lbPow A.isLB, ← natCast_zsmul, ← natCast_zsmul, ← sub_eq_add_neg,
      ← sub_smul, Int.toNat_sub_toNat_neg]
  rw [← Finset.sum_map_toList, ArInt.comb]
  induction (Finset.univ : Finset ι).toList with
  | nil =>
    exact (cls_eq_zero_iff (LB.isLB_triv X)).2 ⟨⟨fun _ => 1⟩, fun _ _ => by simp only [map_one, mul_one]⟩
  | cons i l ih =>
    rw [List.foldr_cons, List.map_cons, List.sum_cons, ← ih, ← hz]
    exact cls_tens _ _ _

theorem exists_secs_of_isGenerated {S T : Type} [CommRing S] [IsDomain S] [Field T] [Algebra S T] [IsFractionRing S T]
    {X X' : Scheme.{0}} {p : X ⟶ Sp S} {p' : X' ⟶ Sp T} {φ : X' ⟶ X}
    (H : IsPullback φ p' p (spMap (algebraMap S T))) [CompactSpace X] [IsSeparated p] {B : LB X} (hB : B.IsLB)
    (h : IsGenerated (B.pull φ)) : ∃ (m : ℕ) (s : Fin m → B.Sec), ∀ w : X', ∃ i, φ w ∈ nonzeroLocus (s i) := by
  have hB' := h.isLB
  obtain ⟨m, t, ht⟩ := h
  choose a ha s hs using fun i => exists_extend (nonZeroDivisors S) H hB hB'
    ((isGen_iff (idIso _)).1 (idIso_isGen hB')) (t i)
  refine ⟨m, s, fun w => ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (ht.ge (Set.mem_univ w))
  obtain ⟨j, hj⟩ := exists_chart hB (φ w)
  obtain ⟨k, hk⟩ := exists_chart hB' w
  refine ⟨i, (mem_nonzeroLocus_iff_isUnit (s i) hj).2 ?_⟩
  have u : IsUnit (gs φ w _ ((s i).f j)) := by
    rw [hs i w j k hj hk]
    refine IsUnit.mul ?_ ((Units.isUnit _).mul ((mem_nonzeroLocus_iff_isUnit (t i) hk).1 hi))
    rw [H.w, cst_comp]
    have h0 : algebraMap S T (a i) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (ha i)
    refine IsUnit.of_mul_eq_one (cst p' w (algebraMap S T (a i))⁻¹) ?_
    rw [← H1.cst_mul, mul_inv_cancel₀ h0, H1.cst_one]
  rw [gs_stalkMap φ w _ hj] at u
  exact isUnit_of_map_unit _ _ u

theorem main : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) (L M : HermLB V.p),
    IsAmpleLB (L.B.pull V.j) → ∃ (n m : ℕ) (s : Fin m → (ArInt.comb ![L, M] ![(n : ℤ), 1]).B.Sec),
      ∀ w : V.G, IsClosed ({w} : Set V.G) → ∃ i, V.j w ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i) := by
  intro F _ _ Y V L M hL
  obtain ⟨N, ι, _, hι⟩ := V.ar.isProjOver
  have := isProper_str (𝓞 F) N
  have : IsProper V.p := hι ▸ inferInstance
  have : IsProper (V.π ≫ Y.str) := MorphismProperty.of_isPullback (P := @IsProper) V.pb inferInstance
  have : CompactSpace V.X := QuasiCompact.compactSpace_of_compactSpace V.p
  have hM := LB.isLB_pull M.isLB V.j
  obtain ⟨n, hn⟩ := (AmpleDominates.eventually_isGenerated (V.π ≫ Y.str) hL (isLB_dual hM)).exists
  have hC := (ArInt.comb ![L, M] ![(n : ℤ), 1]).isLB
  have hG : IsGenerated ((ArInt.comb ![L, M] ![(n : ℤ), 1]).B.pull V.j) := by
    refine hn.of_lbIso (LB.isLB_pull hC _) ((cls_eq_iff (LB.isLB_pull hC _) hn.isLB).1 ?_)
    rw [cls_div (isLB_lbPow hL.isLB n) (isLB_dual hM), cls_lbPow hL.isLB, cls_dual hM, cls_pull hC, cls_pull L.isLB,
      cls_pull M.isLB, cls_comb]
    simp [Fin.sum_univ_two]
  obtain ⟨m, s, hs⟩ := exists_secs_of_isGenerated V.pb hC hG
  exact ⟨n, m, s, fun w _ => hs w⟩

end GlobalTheory.GenFibreSecs
