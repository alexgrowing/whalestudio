import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackCartierDivisorBundleEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsLocallyGeneratedAffine
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.PullIdeal

open CartierDiv

theorem exists_pow_regularAt {Y : Scheme.{0}} [IsIntegral Y] (D : CartierDiv Y) {V : Y.Opens}
    (hV : IsCompact (V : Set Y)) (hηV : genericPoint Y ∈ V) (t : Γ(Y, V)) (F : Y.functionField)
    (hF : ∀ z ∈ Y.basicOpen t, D.RegularAt z F) :
    ∃ n : ℕ, ∀ z ∈ V, D.RegularAt z (fnOf V hηV t ^ n * F) := by
  by_cases ht : genericPoint Y ∈ Y.basicOpen t
  swap
  · refine ⟨1, fun z _ => ?_⟩
    have h0 : fnOf V hηV t = 0 := by
      by_contra h
      exact ht ((unitAt_fnOf_iff hηV hηV t).1 (unitAt_genericPoint h))
    rw [h0, pow_one, zero_mul]
    exact (D.vanishesAt_zero z).regularAt
  have loc : ∀ y : V, ∃ W : Y.Opens, y.1 ∈ W ∧ ∃ n : ℕ,
      ∀ z ∈ W, D.RegularAt z (fnOf V hηV t ^ n * F) := by
    intro y
    obtain ⟨V', hyV', g, hg⟩ := D.exists_isEqn_nhds y.1
    obtain ⟨W, hW, hyW, hWV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
      (show y.1 ∈ V ⊓ V' from ⟨y.2, hyV'⟩)
    have hWV1 : W ≤ V := hWV.trans inf_le_left
    set t' : Γ(Y, W) := Y.presheaf.map (homOfLE hWV1).op t
    have hB : Y.basicOpen t' = W ⊓ Y.basicOpen t := Y.basicOpen_res t _
    have hgen : genericPoint Y ∈ Y.basicOpen t' := hB ▸ memInf (gen_mem hyW) ht
    obtain ⟨b, hb⟩ := exists_fnOf_eq (f := F * (g : Y.functionField)) hgen fun z hz => by
      rw [hB] at hz
      exact (hg z (hWV hz.1).2).regularAt_iff.1 (hF z hz.2)
    obtain ⟨n, a, ha⟩ := exists_eq_pow_mul_of_isAffineOpen Y W hW t' b
    have key : fnOf W (gen_mem hyW) a = fnOf V hηV t ^ n * (F * (g : Y.functionField)) := by
      have e := congrArg (fnOf _ hgen) ha
      rw [map_mul, map_pow, hb] at e
      erw [SecPowLoc.fnOf_map, SecPowLoc.fnOf_map, SecPowLoc.fnOf_map] at e
      exact e
    refine ⟨W, hyW, n, fun z hz => (hg z (hWV hz).2).regularAt_iff.2 ?_⟩
    rw [mul_assoc, ← key]
    exact regAt_fnOf hz _ a
  choose W hyW n hn using loc
  obtain ⟨T, hT⟩ := hV.elim_finite_subcover (fun y : V => (W y : Set Y)) (fun y => (W y).isOpen)
    (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyW _⟩)
  refine ⟨T.sup n, fun z hz => ?_⟩
  obtain ⟨y, hyT, hzy⟩ := Set.mem_iUnion₂.1 (hT hz)
  have hle : n y ≤ T.sup n := Finset.le_sup hyT
  have hr := regAt_fnOf hz hηV (t ^ (T.sup n - n y))
  rw [map_pow] at hr
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
  exact (hn y z hzy).regAt_mul hr

theorem regAt_pull {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s]
    {U : X.Opens} {y : Y} (hy : s y ∈ U) (c : Γ(X, U)) :
    RegAt y (functionFieldMap s (fnOf U (gen_mem hy) c)) := by
  have hy' : y ∈ s ⁻¹ᵁ U := hy
  rw [← PullPres.fnOf_app s (gen_mem hy') c]
  exact regAt_fnOf hy' _ _

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s]
  (D : CartierDiv Y)

def pullIdeal (U : X.Opens) : Ideal Γ(X, U) where
  carrier := {f | ∀ (y : Y) (hy : s y ∈ U), D.RegularAt y (functionFieldMap s (fnOf U (gen_mem hy) f))}
  zero_mem' y hy := by rw [map_zero, map_zero]; exact (D.vanishesAt_zero y).regularAt
  add_mem' hf hg y hy := by rw [map_add, map_add]; exact (hf y hy).add (hg y hy)
  smul_mem' c f hf y hy := by
    rw [smul_eq_mul, map_mul, map_mul]
    exact (hf y hy).regAt_mul (regAt_pull s hy c)

def pullIdealSheaf [QuasiCompact s] : X.IdealSheafData where
  ideal U := pullIdeal s D U.1
  map_ideal_basicOpen U a := by
    show Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom (pullIdeal s D U.1) =
      pullIdeal s D (X.basicOpen a)
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap]
      intro y hy
      have := hf y (X.basicOpen_le a hy)
      convert this using 3
      exact SecPowLoc.fnOf_map _ _ _
    · intro h hh
      by_cases hg : genericPoint X ∈ X.basicOpen a
      swap
      · have : h = 0 := fn_ext fun h' => (hg h').elim
        rw [this]; exact zero_mem _
      obtain ⟨n, b, hb⟩ := exists_eq_pow_mul_of_isAffineOpen X U.1 U.2 a h
      have hU0 : genericPoint X ∈ U.1 := X.basicOpen_le a hg
      have e' : fnOf U.1 hU0 b = fnOf U.1 hU0 a ^ n * fnOf _ hg h := by
        have := congrArg (fnOf _ hg) hb
        rw [map_mul, map_pow] at this
        erw [SecPowLoc.fnOf_map, SecPowLoc.fnOf_map] at this
        exact this
      obtain ⟨M, hM⟩ : ∃ M : ℕ, a ^ M * b ∈ pullIdeal s D U.1 := by
        by_cases hηV : genericPoint Y ∈ s ⁻¹ᵁ U.1
        · obtain ⟨M, hM⟩ := exists_pow_regularAt D (s.isCompact_preimage U.2.isCompact) hηV
            ((s.app U.1).hom a) (functionFieldMap s (fnOf U.1 hU0 b)) (fun z hz => by
              rw [← Scheme.preimage_basicOpen] at hz
              rw [e', map_mul, map_pow]
              have hr := regAt_pull s (U := U.1) (X.basicOpen_le a hz) (a ^ n)
              rw [map_pow, map_pow] at hr
              exact (hh z hz).regAt_mul hr)
          refine ⟨M, fun y hy => ?_⟩
          have := hM y hy
          rw [PullPres.fnOf_app] at this
          rw [map_mul, map_mul, map_pow, map_pow]
          exact this
        · exact ⟨0, fun y hy => (hηV (gen_mem (x := y) hy)).elim⟩
      have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a) :=
        X.toRingedSpace.isUnit_res_basicOpen a
      have hb' : X.presheaf.map (homOfLE (X.basicOpen_le a)).op (a ^ M * b) =
          h * (hu.unit : Γ(X, X.basicOpen a)) ^ (n + M) := by
        have hb2 : X.presheaf.map (homOfLE (X.basicOpen_le a)).op b =
            X.presheaf.map (homOfLE (X.basicOpen_le a)).op a ^ n * h := hb
        rw [map_mul, map_pow, hb2]
        rw [IsUnit.unit_spec, pow_add]
        ring
      have : h = X.presheaf.map (homOfLE (X.basicOpen_le a)).op (a ^ M * b) *
          ((hu.unit⁻¹ ^ (n + M) : (Γ(X, X.basicOpen a))ˣ) : Γ(X, X.basicOpen a)) := by
        rw [hb', mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel,
          one_pow, Units.val_one, mul_one]
      rw [this]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hM)

theorem exists_idealSheaf : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s]
    [QuasiCompact s] (D : CartierDiv Y), ∃ J : X.IdealSheafData, (∀ (U : X.affineOpens) (f : Γ(X, U.1)),
    f ∈ J.ideal U ↔ ∀ (y : Y) (hy : s y ∈ U.1), D.RegularAt y (functionFieldMap s (fnOf U.1 (gen_mem hy) f))) := by
  intro X Y _ _ s _ _ D
  exact ⟨pullIdealSheaf s D, fun _ _ => Iff.rfl⟩

end GlobalTheory.Cartier.PullIdeal
