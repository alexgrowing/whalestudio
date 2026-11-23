import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsGrowthBasicPropertiesAbelianVarietyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalPolarisationVolumeFormSymmetricAmpleStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolarisationFormOfLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsCountSqEqDetFormOnTorsionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingTorsionBasisSymplecticStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.GraphVolume

open GlobalTheory.CechPic

private theorem sec_eq_sec_one_pow {X : Scheme.{0}} {A : LB X} (hA : A.IsLB) (s : A.Sec) :
    ∀ k : ℕ, ∃ u : (lbPow A (k + 1)).Sec, Out.nonzeroLocus u = Out.nonzeroLocus s := by
  intro k
  induction k with
  | zero =>
    have hA1 : (lbPow A (0 + 1)).IsLB := LB.isLB_linComb hA _ _
    refine exists_sec_nonzeroLocus_eq_of_lbIso hA1 hA ((cls_eq_iff hA1 hA).1 ?_) s
    rw [cls_lbPow hA _ hA1, zero_add, one_smul]
  | succ k ih =>
    obtain ⟨u, hu⟩ := ih
    have hB : (lbPow A (k + 1)).IsLB := LB.isLB_linComb hA _ _
    have hC : (lbPow A (k + 1 + 1)).IsLB := LB.isLB_linComb hA _ _
    have hD : (LB.div (lbPow A (k + 1 + 1)) (lbPow A (k + 1))).IsLB := LB.isLB_div hC hB
    have hI : LBIso (LB.div (lbPow A (k + 1 + 1)) (lbPow A (k + 1))) A := by
      refine (cls_eq_iff hD hA).1 ?_
      rw [cls_div hC hB hD, cls_lbPow hA _ hC, cls_lbPow hA _ hB, succ_nsmul, add_sub_cancel_left]
    obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hD hA hI s
    obtain ⟨w, hw⟩ := exists_sec_nonzeroLocus_eq_inf_div hB hC t u
    exact ⟨w, by rw [hw, ht, hu, inf_idem]⟩

private theorem mem_nonzeroLocus_pullSec {X : Scheme.{0}} {L : LB X} (f : X ⟶ X) (n : ℕ) (s : (lbPow L n).Sec) (x : X)
    (hx : f.base x ∈ Out.nonzeroLocus s) :
    x ∈ Out.nonzeroLocus (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec s f) := by
  obtain ⟨j, hj⟩ := exists_chart_of_mem_nonzeroLocus hx
  have hxj : x ∈ (LB.LinComb L (K := PUnit) (fun _ => f ≫ 𝟙 X) (fun _ => (n : ℤ))).U j :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hj k
  rw [mem_nonzeroLocus_iff_isUnit _ hxj]
  have e : gs (𝟙 X) x _ ((ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec s f).f j) = gs (𝟙 X ≫ f) x _ (s.f j) :=
    (gs_res _ x _ hxj _).trans (gs_pull _ f x _ hj _)
  rw [e]
  exact (mem_nonzeroLocus_iff_pull s (𝟙 X ≫ f) x (by simpa using hj)).1 (by simpa using hx)

theorem isAmpleLB_graph {X : Scheme.{0}} {L : LB X} (hL : IsAmpleLB L) (f : X ⟶ X) {N : ℕ} (hN : 1 ≤ N) :
    IsAmpleLB (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(N : ℤ), (N : ℤ)]) := by
  have hLB : L.IsLB := hL.isLB
  have hM : (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(N : ℤ), (N : ℤ)]).IsLB := LB.isLB_linComb hLB _ _
  refine { isLB := hM, compactSpace := hL.compactSpace, exists_affine := fun x => ?_ }
  obtain ⟨n1, hn1, s1, hx1, ha1⟩ := hL.exists_affine x
  obtain ⟨n2, hn2, s2, hx2, -⟩ := hL.exists_affine (f.base x)
  have hxt := mem_nonzeroLocus_pullSec f n2 s2 x hx2
  have hT : (LB.LinComb L (K := PUnit) (fun _ => f ≫ 𝟙 X) (fun _ => (n2 : ℤ))).IsLB := LB.isLB_linComb hLB _ _
  have hA : (lbPow L n1).IsLB := LB.isLB_linComb hLB _ _
  obtain ⟨k1, hk1⟩ : ∃ k, k + 1 = n2 * N := ⟨n2 * N - 1, by have := Nat.mul_pos hn2 hN; omega⟩
  obtain ⟨k2, hk2⟩ : ∃ k, k + 1 = n1 * N := ⟨n1 * N - 1, by have := Nat.mul_pos hn1 hN; omega⟩
  obtain ⟨u1, hu1⟩ := sec_eq_sec_one_pow hA s1 k1
  obtain ⟨u2, hu2⟩ := sec_eq_sec_one_pow hT (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec s2 f) k2
  have hA1 : (lbPow (lbPow L n1) (k1 + 1)).IsLB := LB.isLB_linComb hA _ _
  have hT2 : (lbPow (LB.LinComb L (K := PUnit) (fun _ => f ≫ 𝟙 X) (fun _ => (n2 : ℤ))) (k2 + 1)).IsLB :=
    LB.isLB_linComb hT _ _
  have hB : (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(N : ℤ), (N : ℤ)]) (n1 * n2)).IsLB :=
    LB.isLB_linComb hM _ _
  have hDv := LB.isLB_div hB hA1
  have hI : LBIso (LB.div (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(N : ℤ), (N : ℤ)]) (n1 * n2))
      (lbPow (lbPow L n1) (k1 + 1)))
      (lbPow (LB.LinComb L (K := PUnit) (fun _ => f ≫ 𝟙 X) (fun _ => (n2 : ℤ))) (k2 + 1)) := by
    refine (cls_eq_iff hDv hT2).1 ?_
    rw [cls_div hB hA1 hDv, cls_lbPow hM _ hB, cls_lbPow hA _ hA1, cls_lbPow hLB _ hA, cls_lbPow hT _ hT2,
      cls_linComb hLB _ _ hM, cls_linComb hLB _ _ hT, Fin.sum_univ_two, hk1, hk2]
    simp only [Finset.univ_unique, Finset.sum_singleton, Matrix.cons_val_zero, Matrix.cons_val_one,
      Category.comp_id, GlobalTheory.CechPic.pull_id]
    module
  obtain ⟨w, hw⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hDv hT2 hI u2
  obtain ⟨v, hv⟩ := exists_sec_nonzeroLocus_eq_inf_div hA1 hB w u1
  refine ⟨n1 * n2, Nat.mul_pos hn1 hn2, v, ?_, ?_⟩
  · rw [hv, hw, hu2, hu1]
    exact ⟨hxt, hx1⟩
  · rw [hv, hw, hu2, hu1]
    exact isAffineOpen_nonzeroLocus_inf hT _ ha1

theorem exists_sec_ne_zero {X : Scheme.{0}} [Nonempty X] {L : LB X} (hL : L.IsLB) (f : X ⟶ X) (N κ : ℕ)
    (hD : IsAmpleLB (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(κ : ℤ), -1])) :
    ∃ n, 1 ≤ n ∧ ∃ s : (LB.div (lbPow (lbPow L (N * (1 + κ))) n)
      (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(N : ℤ), (N : ℤ)]) n)).Sec, ∃ j, s.f j ≠ 0 := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨n, hn, s, hx, -⟩ := hD.exists_affine x
  refine ⟨n, hn, ?_⟩
  suffices H : ∃ v : (LB.div (lbPow (lbPow L (N * (1 + κ))) n)
      (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(N : ℤ), (N : ℤ)]) n)).Sec, x ∈ Out.nonzeroLocus v by
    obtain ⟨v, hxv⟩ := H
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hxv
    refine ⟨v, k, fun h0 => ?_⟩
    have hb := (mem_nonzeroLocus_iff_basicOpen v hk).1 hxv
    rw [h0, Scheme.basicOpen_zero] at hb
    exact hb
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hLc : (lbPow L (0 * (1 + κ))).IsLB := LB.isLB_linComb hL _ _
    have hLcn : (lbPow (lbPow L (0 * (1 + κ))) n).IsLB := LB.isLB_linComb hLc _ _
    have hM : (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ)]).IsLB := LB.isLB_linComb hL _ _
    have hMn : (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ)]) n).IsLB :=
      LB.isLB_linComb hM _ _
    have hQ := LB.isLB_div hLcn hMn
    obtain ⟨t, ht⟩ := (cls_eq_zero_iff hQ).1 (by
      rw [cls_div hLcn hMn hQ, cls_lbPow hLc _ hLcn, cls_lbPow hL _ hLc, cls_lbPow hM _ hMn,
        cls_linComb hL _ _ hM, Fin.sum_univ_two]
      simp)
    refine ⟨DVR.genSec t ht, ?_⟩
    rw [nonzeroLocus_genSec hQ t ht]
    trivial
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hDL : (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(κ : ℤ), -1]).IsLB := hD.isLB
  have hDn : (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(κ : ℤ), -1]) n).IsLB := LB.isLB_linComb hDL _ _
  obtain ⟨u, hu⟩ := sec_eq_sec_one_pow hDn s m
  have hDnm := LB.isLB_linComb hDn (K := PUnit) (fun _ => 𝟙 X) (fun _ => ((m + 1 : ℕ) : ℤ))
  have hLc : (lbPow L ((m + 1) * (1 + κ))).IsLB := LB.isLB_linComb hL _ _
  have hLcn : (lbPow (lbPow L ((m + 1) * (1 + κ))) n).IsLB := LB.isLB_linComb hLc _ _
  have hM : (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![((m + 1 : ℕ) : ℤ), ((m + 1 : ℕ) : ℤ)]).IsLB :=
    LB.isLB_linComb hL _ _
  have hMn : (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![((m + 1 : ℕ) : ℤ), ((m + 1 : ℕ) : ℤ)]) n).IsLB :=
    LB.isLB_linComb hM _ _
  have hQ := LB.isLB_div hLcn hMn
  have hI : LBIso (LB.div (lbPow (lbPow L ((m + 1) * (1 + κ))) n)
      (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![((m + 1 : ℕ) : ℤ), ((m + 1 : ℕ) : ℤ)]) n))
      (lbPow (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(κ : ℤ), -1]) n) (m + 1)) := by
    refine (cls_eq_iff hQ hDnm).1 ?_
    rw [cls_div hLcn hMn hQ, cls_lbPow hLc _ hLcn, cls_lbPow hL _ hLc, cls_lbPow hM _ hMn,
      cls_lbPow hDn _ hDnm, cls_lbPow hDL _ hDn, cls_linComb hL _ _ hM, cls_linComb hL _ _ hDL,
      Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, GlobalTheory.CechPic.pull_id]
    module
  obtain ⟨v, hv⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hQ hDnm hI u
  exact ⟨v, by rw [hv, hu]; exact hx⟩

theorem symB_graph {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (h : SymB L)
    (f : A ⟶ A) [IsMonHom f] (a b : ℤ) : SymB (LB.LinComb L (K := Fin 2) ![𝟙 A.left, f.left] ![a, b]) := by
  have hM := LB.isLB_linComb hL ![𝟙 A.left, f.left] ![a, b]
  have hMi := pull_isLB hM (GrpObj.inv : A ⟶ A).left
  have hLi := pull_isLB hL (GrpObj.inv : A ⟶ A).left
  have e0 : GlobalTheory.CechPic.pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL := by
    rw [← cls_pull hL _ hLi]
    exact ((cls_eq_iff hL hLi).2 h).symm
  have e1 : (GrpObj.inv : A ⟶ A).left ≫ f.left = f.left ≫ (GrpObj.inv : A ⟶ A).left := by
    rw [← Over.comp_left, ← Over.comp_left, GrpObj.inv_hom]
  refine (cls_eq_iff hM hMi).1 ?_
  rw [cls_pull hM _ hMi, cls_linComb hL _ _ hM, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, GlobalTheory.CechPic.pull_id, map_add, map_zsmul]
  rw [e0, ← GlobalTheory.CechPic.pull_comp, e1, GlobalTheory.CechPic.pull_comp, e0]

theorem eq_of_sq_eq {k B a b : ℕ} (hB : B ^ 2 < k) (ha : a ≤ B) (hb : b ≤ B)
    (h : (a : ZMod k) ^ 2 = (b : ZMod k) ^ 2) : a = b := by
  have ha2 : a ^ 2 < k := lt_of_le_of_lt (Nat.pow_le_pow_left ha 2) hB
  have hb2 : b ^ 2 < k := lt_of_le_of_lt (Nat.pow_le_pow_left hb 2) hB
  have h' : ((a ^ 2 : ℕ) : ZMod k) = ((b ^ 2 : ℕ) : ZMod k) := by push_cast; exact h
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha2, Nat.mod_eq_of_lt hb2] at h'
  exact Nat.pow_left_injective (by norm_num) h'

end GlobalTheory.GraphVolume

namespace GlobalTheory

open GraphVolume

theorem hilbert_graph_of_torsion : Out.Laws → Out.Laws2 → ∀ (g N κ l j : ℕ) (Mat : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod (l ^ j))), 1 ≤ N → l.Prime → (N * (1 + κ)) ^ (2 * g) < l ^ j → ∃ δ ≤ (N * (1 + κ)) ^ g, ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (pt : Fin (2 * g) → (Out.baseOver (Sp K) ⟶ P.A)) (ζ : Kˣ) (f : P.A ⟶ P.A), P.g = g → (l : K) ≠ 0 → IsPrimitiveRoot ζ (l ^ j) → TorsBasis P.A (l ^ j) pt → (∀ i i', Out.WeilIs P.A P.L ((l ^ j : ℕ) : ℤ) (pt i) (pt i') (unitOn (ζ ^ Out.stdSymp g i i'))) → IsMonHom f → ActsBy pt f Mat → Out.RelAmple P.A (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(κ : ℤ), -1]) → SymB (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(N : ℤ), (N : ℤ)]) ∧ ∀ e ≥ 1, SectionsHaveFiniteDimension P.A.hom (lbPow (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(N : ℤ), (N : ℤ)]) e) (δ * e ^ g) := by
  intro hL1 hL2 g N κ l j Mat hN hl hB
  obtain ⟨S, hS⟩ := GlobalTheory.T.weil_pairing_torsion_basis_symplectic hL1 hL2 g N (l ^ j) Mat
  classical
  have hBk : ((N * (1 + κ)) ^ g) ^ 2 < l ^ j := by rw [← pow_mul, mul_comm g 2]; exact hB
  refine ⟨if h : ∃ d ≤ (N * (1 + κ)) ^ g, (d : ZMod (l ^ j)) ^ 2 = S.det then Classical.choose h else 0, ?_, ?_⟩
  · split_ifs with h
    · exact (Classical.choose_spec h).1
    · exact Nat.zero_le _
  intro K _ _ P pt ζ f hg hl0 hζ hT hW hf hAct hD
  subst hg
  have := hf
  have hprop : IsProper P.A.hom := P.isAb.proper
  have hPL : P.L.IsLB := P.isLB
  set M := LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(N : ℤ), (N : ℤ)] with hMdef
  have hM : M.IsLB := LB.isLB_linComb hPL _ _
  have hSym : SymB M := symB_graph hPL (GlobalTheory.T.principalPolarisation_volume_form_symmetric_ample hL1 hL2 K P).2.2.1 f _ _
  have hAmpL : IsAmpleLB P.L := (relAmple_iff_isAmpleLB_of_isAffine P.A hPL).1 P.ample
  have hAmpM : IsAmpleLB M := isAmpleLB_graph hAmpL f.left hN
  have hRelM : Out.RelAmple P.A M := (relAmple_iff_isAmpleLB_of_isAffine P.A hM).2 hAmpM
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_polarisationForm_of_lineBundle hL1 hL2 K P M hM
  have hk : ((l ^ j : ℕ) : K) ≠ 0 := by push_cast; exact pow_ne_zero _ hl0
  have hSs : ActsBy pt s S := hS K P pt ζ f s hk hζ hT hW hf hAct hs
  obtain ⟨δ, hVol, hH0, hdet⟩ := GlobalTheory.T.sections_count_sq_eq_det_form_on_torsion hL1 hL2 K P M s l hl hl0 hM hRelM hSym hs
  have hδ2 : (δ : ZMod (l ^ j)) ^ 2 = S.det := hdet j pt S hT hSs

  have hc : 1 ≤ N * (1 + κ) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hDa : IsAmpleLB (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(κ : ℤ), -1]) :=
    (relAmple_iff_isAmpleLB_of_isAffine P.A (LB.isLB_linComb hPL _ _)).1 hD
  have hne : Nonempty (𝟙_ (Over (Sp K))).left := by
    change Nonempty (Sp K)
    infer_instance
  have : Nonempty P.A.left := ⟨(η[P.A] : 𝟙_ (Over (Sp K)) ⟶ P.A).left.base (Classical.choice hne)⟩
  obtain ⟨n, hn, t, ht⟩ := exists_sec_ne_zero hPL f.left N κ hDa
  have hLc : (lbPow P.L (N * (1 + κ))).IsLB := LB.isLB_linComb hPL _ _
  have hLcn : (lbPow (lbPow P.L (N * (1 + κ))) n).IsLB := LB.isLB_linComb hLc _ _
  have hMn : (lbPow M n).IsLB := LB.isLB_linComb hM _ _
  have V1 : Vol P.A.hom P.L P.g 1 := (GlobalTheory.T.principalPolarisation_volume_form_symmetric_ample hL1 hL2 K P).1
  have V2 : Vol P.A.hom (lbPow P.L (N * (1 + κ))) P.g (((N * (1 + κ) : ℕ) : ℝ) ^ P.g * 1) :=
    (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P P.L P.g hPL).2.2.2.1 _ 1 hc V1
  have V3 : Vol P.A.hom (lbPow (lbPow P.L (N * (1 + κ))) n) P.g
      ((n : ℝ) ^ P.g * (((N * (1 + κ) : ℕ) : ℝ) ^ P.g * 1)) :=
    (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P _ P.g hLc).2.2.2.1 n _ hn V2
  have V4 : Vol P.A.hom (lbPow M n) P.g ((n : ℝ) ^ P.g * (δ : ℝ)) :=
    (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P M P.g hM).2.2.2.1 n _ hn hVol
  have hle := ((GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P (lbPow M n) P.g hMn).2.2.2.2.2 _ t hLcn ht).2 _ _ V4 V3
  have hnpos : (0 : ℝ) < (n : ℝ) ^ P.g := pow_pos (by exact_mod_cast hn) _
  have hδB : δ ≤ (N * (1 + κ)) ^ P.g := by
    have h1 : (δ : ℝ) ≤ ((N * (1 + κ) : ℕ) : ℝ) ^ P.g := by
      have := le_of_mul_le_mul_left (by simpa using hle) hnpos
      simpa using this
    exact_mod_cast h1
  have hex : ∃ d ≤ (N * (1 + κ)) ^ P.g, (d : ZMod (l ^ j)) ^ 2 = S.det := ⟨δ, hδB, hδ2⟩
  rw [dif_pos hex]
  have hsp := Classical.choose_spec hex
  have hEq : δ = Classical.choose hex := eq_of_sq_eq hBk hδB hsp.1 (hδ2.trans hsp.2.symm)
  rw [← hEq]
  exact ⟨hSym, hH0⟩

end GlobalTheory
