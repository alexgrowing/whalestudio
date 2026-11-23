import Mathlib
import ReciprocityTheory.DualLattices.IsPairingValueAddRight
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NEvalSqZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianFunctorNilChartNsmulAndKilledByPPowStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPowerSeriesOfNaturalNilpotentPointsStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PowerSeriesEqOfEvalAtNilpotentPointsEqStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

section Local
variable {O S : Type} [CommRing O] [CommRing S] [Algebra O S]

private theorem unit_of_nil {y x : S} (h : IsNilpotent (y - x)) (hx : IsUnit x) : IsUnit y := by
  have := h.isUnit_add_right_of_commute hx (Commute.all _ _)
  rwa [sub_add_cancel] at this

private theorem local_of_aug [IsLocalRing O] (h : ∀ y : S, ∃ r : O, IsNilpotent (y - algebraMap O S r))
    (e : S →+* IsLocalRing.ResidueField O) (he : ∀ r, e (algebraMap O S r) = IsLocalRing.residue O r) :
    IsLocalRing S ∧ IsLocalHom (algebraMap O S) := by
  haveI : Nontrivial S := e.domain_nontrivial
  refine ⟨IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun y => ?_, ⟨fun r hr => ?_⟩⟩
  · obtain ⟨r, hr⟩ := h y
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self r with hu | hu
    · exact Or.inl (unit_of_nil hr (hu.map _))
    · refine Or.inr (unit_of_nil (x := algebraMap O S (1 - r)) ?_ (hu.map _))
      have := hr.neg
      convert this using 1
      simp
  · have := hr.map e
    rw [he] at this
    exact (isUnit_map_iff (IsLocalRing.residue O) r).1 this

private theorem jet_local [IsLocalRing O] (I : Ideal O) (hI : I ≤ IsLocalRing.maximalIdeal O) (κ : Type) (k m : ℕ) :
    IsLocalRing (Geo.Tor.JetR O κ m ⧸ (I ^ (k + 1)).map (algebraMap O (Geo.Tor.JetR O κ m))) ∧
    IsLocalHom (algebraMap O (Geo.Tor.JetR O κ m ⧸ (I ^ (k + 1)).map (algebraMap O (Geo.Tor.JetR O κ m)))) := by
  let e0 : MvPolynomial κ O →ₐ[O] IsLocalRing.ResidueField O := MvPolynomial.aeval fun _ => 0
  have h0 : Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ O)) ≤ RingHom.ker e0 := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [e0]
  let e1 : Geo.Tor.JetR O κ m →ₐ[O] IsLocalRing.ResidueField O :=
    Ideal.Quotient.liftₐ _ e0 fun a ha => h0 (Ideal.pow_le_self (by omega) ha)
  have h1 : (I ^ (k + 1)).map (algebraMap O (Geo.Tor.JetR O κ m)) ≤ RingHom.ker e1 := by
    rw [Ideal.map_le_iff_le_comap]
    intro t ht
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes]
    exact (IsLocalRing.residue_eq_zero_iff t).2 (hI (Ideal.pow_le_self (by omega) ht))
  let e2 := Ideal.Quotient.liftₐ _ e1 fun a ha => h1 ha
  refine local_of_aug (fun y => ?_) e2.toRingHom fun r => e2.commutes r
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mkₐ_surjective O _ y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mkₐ_surjective O _ y
  refine ⟨MvPolynomial.constantCoeff y, ?_⟩
  rw [← AlgHom.commutes (Ideal.Quotient.mkₐ O _), ← map_sub]
  refine IsNilpotent.map ?_ _
  rw [← AlgHom.commutes (Ideal.Quotient.mkₐ O _), ← map_sub]
  refine ⟨m + 1, ?_⟩
  rw [← map_pow, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  refine Ideal.pow_mem_pow ?_ _
  induction y using MvPolynomial.induction_on with
  | C a => simp
  | add f f' hf hf' =>
    have := Ideal.add_mem _ hf hf'
    convert this using 1
    simp only [map_add]
    ring
  | mul_X f i _ =>
    simp only [map_mul, MvPolynomial.constantCoeff_X, mul_zero, map_zero, sub_zero]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

private theorem kills_iff (p : ℕ) : (∃ k, Kills (Ideal.span {(p : O)}) k S) ↔ IsNilpotent (p : S) := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    have := hk ((p : O) ^ (k + 1)) (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _)
    simpa using this
  · rintro ⟨k, hk⟩
    refine ⟨k, fun t ht => ?_⟩
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ht
    obtain ⟨c, rfl⟩ := ht
    simp [pow_succ, hk]

end Local

section Pair
variable {R₀ : Type} [CommRing R₀] {B : BX R₀} {O : LAlg R₀} {p : ℕ} {τ : ℕ → B.G O}

private theorem pair_up (h1 : ∀ n, (p ^ (n + 1)) • τ n = 0) (h2 : ∀ n, τ n = p • τ (n + 1)) {R : LAlg R₀}
    (s : LHom O R) {x : B.G R} {z : (R : Type)ˣ} {n m : ℕ} (hnm : n ≤ m)
    (h : B.IsPairing (p ^ (n + 1)) x (B.map s (τ n)) z) : B.IsPairing (p ^ (m + 1)) x (B.map s (τ m)) z := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ m _ ih =>
    have hx : p ^ (m + 1) • x = 0 := ih.1
    have hy : (p ^ (m + 1) * p) • B.map s (τ (m + 1)) = 0 := by
      rw [← pow_succ, ← map_nsmul, h1, map_zero]
    obtain ⟨z', hz'⟩ := B.pairing_exists (p ^ (m + 1) * p) x (B.map s (τ (m + 1)))
      (by rw [mul_comm, ← smul_smul, hx, nsmul_zero]) hy
    have h3 := B.pairing_mul _ _ _ _ _ hx hy hz'
    rw [← map_nsmul, ← h2] at h3
    rw [B.pairing_unique _ _ _ _ _ ih h3, pow_succ p (m + 1)]
    exact hz'

private def PVal (p : ℕ) (τ : ℕ → B.G O) {R : LAlg R₀} (s : LHom O R) (x : B.G R) (z : (R : Type)ˣ) : Prop :=
  ∃ n, B.IsPairing (p ^ (n + 1)) x (B.map s (τ n)) z

private theorem pval_mul (h1 : ∀ n, (p ^ (n + 1)) • τ n = 0) (h2 : ∀ n, τ n = p • τ (n + 1)) {R : LAlg R₀}
    {s : LHom O R} {x x' : B.G R} {z z' : (R : Type)ˣ} (h : PVal p τ s x z) (h' : PVal p τ s x' z') :
    PVal p τ s (x + x') (z * z') := by
  obtain ⟨n, h⟩ := h
  obtain ⟨m, h'⟩ := h'
  exact ⟨max n m, B.isPairingValue_add_left _ _ _ _ _ _ (pair_up h1 h2 s (le_max_left _ _) h)
    (pair_up h1 h2 s (le_max_right _ _) h')⟩

private theorem pval_unique (h1 : ∀ n, (p ^ (n + 1)) • τ n = 0) (h2 : ∀ n, τ n = p • τ (n + 1)) {R : LAlg R₀}
    {s : LHom O R} {x : B.G R} {z z' : (R : Type)ˣ} (h : PVal p τ s x z) (h' : PVal p τ s x z') : z = z' := by
  obtain ⟨n, h⟩ := h
  obtain ⟨m, h'⟩ := h'
  exact B.pairing_unique _ _ _ _ _ (pair_up h1 h2 s (le_max_left _ _) h) (pair_up h1 h2 s (le_max_right _ _) h')

private theorem pval_map {R R' : LAlg R₀} {s : LHom O R} (f : LHom R R') {x : B.G R} {z : (R : Type)ˣ}
    (h : PVal p τ s x z) : PVal p τ (f.comp s) (B.map f x) (Units.map (f.1 : R →* R') z) := by
  obtain ⟨n, h⟩ := h
  refine ⟨n, ?_⟩
  rw [B.map_comp]
  exact B.pairing_map f _ _ _ _ h

private theorem pval_exists (h1 : ∀ n, (p ^ (n + 1)) • τ n = 0) {R : LAlg R₀} (s : LHom O R) {x : B.G R}
    (hx : ∃ n, p ^ (n + 1) • x = 0) : ∃ z, PVal p τ s x z := by
  obtain ⟨n, hx⟩ := hx
  obtain ⟨z, hz⟩ := B.pairing_exists (p ^ (n + 1)) x (B.map s (τ n)) hx (by rw [← map_nsmul, h1, map_zero])
  exact ⟨z, n, hz⟩

private def LocO (O : LAlg R₀) (S : Type) [CommRing S] [Algebra (O : Type) S] : Prop :=
  IsLocalRing S ∧ IsLocalHom (algebraMap (O : Type) S)

private abbrev mkL (O : LAlg R₀) (S : Type) [CommRing S] [Algebra (O : Type) S] (h : LocO O S) : LAlg R₀ :=
  @LAlg.mk R₀ _ S _ ((algebraMap (O : Type) S).comp (algebraMap R₀ (O : Type))).toAlgebra h.1

private def mkH (R R' : LAlg R₀) (f : (R : Type) →+* (R' : Type))
    (h : ∀ r, f (algebraMap R₀ (R : Type) r) = algebraMap R₀ (R' : Type) r) (hl : IsLocalHom f) : LHom R R' :=
  ⟨{ f with commutes' := h }, hl⟩

private theorem lhom_ext {R R' : LAlg R₀} {f f' : LHom R R'} (h : ∀ r, f.1 r = f'.1 r) : f = f' :=
  Subtype.ext (AlgHom.ext h)

private def mkS (O : LAlg R₀) (S : Type) [CommRing S] [Algebra (O : Type) S] (h : LocO O S) : LHom O (mkL O S h) :=
  mkH O (mkL O S h) (algebraMap (O : Type) S) (fun _ => rfl) h.2

end Pair

theorem exists_character_pairSer : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (O : LAlg R₀) (g : ℕ) (F : FGLaw (O : Type) g) (Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R), BXChart B O F.F Y → ∀ (p : ℕ), ¬ IsUnit (p : (O : Type)) → IsAdicComplete (Ideal.span {(p : (O : Type))}) (O : Type) → ∀ τ : ℕ → B.G O, (∀ n, (p ^ (n + 1)) • τ n = 0) → (∀ n, τ n = p • τ (n + 1)) → ∃ u : PS (O : Type) 1 g, IsCh F.F u ∧ PairSer B O Y p τ u := by
  intro R₀ _ B O g F Y hY p hp hc τ h1 h2
  classical
  have hI : Ideal.span {(p : (O : Type))} ≤ IsLocalRing.maximalIdeal (O : Type) := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact hp
  have hI' : Ideal.span {(p : (O : Type))} ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  have hex : ∀ (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)), IsNilpotent (p : (R : Type)) →
      (∀ i, IsNilpotent (a i)) → ∃ z, PVal p τ s (Y R s a) z := fun R s a hR ha =>
    pval_exists h1 s (GlobalTheory.T.abelianFunctorNilChart_nsmul_and_killed_by_p_pow R₀ B O g F Y hY p R s a hR ha).2
  let c : ∀ (S : Type) [CommRing S] [Algebra (O : Type) S], (Fin 1 → Fin g → S) → S := fun S _ _ a =>
    if h : ∃ z : Sˣ, ∃ hL : LocO O S, PVal p τ (mkS O S hL) (Y _ (mkS O S hL) (a 0)) z then (h.choose : S) else 0
  have hcv : ∀ (S : Type) [CommRing S] [Algebra (O : Type) S] (a : Fin 1 → Fin g → S) (hL : LocO O S) (z : Sˣ),
      PVal p τ (mkS O S hL) (Y _ (mkS O S hL) (a 0)) z → c S a = z := by
    intro S _ _ a hL z hz
    have h : ∃ z : Sˣ, ∃ hL : LocO O S, PVal p τ (mkS O S hL) (Y _ (mkS O S hL) (a 0)) z := ⟨z, hL, hz⟩
    obtain ⟨_, h'⟩ := h.choose_spec
    have := pval_unique h1 h2 h' hz
    simp only [c, dif_pos h]
    exact congrArg Units.val this
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_powerSeries_of_natural_nilpotentPoints (O : Type) _ hc 1 g (fun S _ _ => LocO O S)
    (fun k m => jet_local _ hI _ k m) c (by
      intro S _ _ S' _ _ φ a hL hL' hS hk ha
      obtain ⟨z, hz⟩ := hex (mkL O S hL) (mkS O S hL) (a 0) ((kills_iff p).1 hk) (ha 0)
      have hφ : IsLocalHom (φ : S →+* S') := ⟨fun y hy => by
        obtain ⟨r, hr⟩ := hS y
        have h3 : IsNilpotent (algebraMap (O : Type) S' r - φ y) := by
          have := (hr.map φ).neg
          rwa [map_sub, AlgHom.commutes, neg_sub] at this
        exact unit_of_nil hr ((hL'.2.map_nonunit r (unit_of_nil h3 hy)).map _)⟩
      let f : LHom (mkL O S hL) (mkL O S' hL') :=
        mkH _ _ (φ : S →+* S') (fun r => φ.commutes _) hφ
      have hf : f.comp (mkS O S hL) = mkS O S' hL' := lhom_ext fun r => φ.commutes r
      have h4 := pval_map f hz
      rw [hY.nat _ _ _ f _ (ha 0), hf] at h4
      rw [hcv S a hL z hz, hcv S' (fun i j => φ (a i j)) hL' _ h4]
      rfl)
  have key : ∀ (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)) (z : (R : Type)ˣ),
      IsNilpotent (p : (R : Type)) → (∀ i, IsNilpotent (a i)) → PVal p τ s (Y R s a) z →
      (z : (R : Type)) = nv s.1.toRingHom u ![a] := by
    intro R s a z hR ha hz
    letI := algOf s
    have hL : LocO O (R : Type) := ⟨inferInstance, s.2⟩
    let f : LHom R (mkL O R hL) :=
      mkH _ _ (RingHom.id (R : Type)) (fun r => (s.1.commutes r).symm) ⟨fun _ h => h⟩
    have hf : f.comp s = mkS O R hL := lhom_ext fun r => rfl
    have h4 := pval_map f hz
    rw [hY.nat _ _ _ f _ ha, hf] at h4
    have h5 := hcv R ![a] hL _ h4
    rw [hu R ![a] hL ((kills_iff p).2 hR) (fun i j => by fin_cases i; exact ha j)] at h5
    exact h5.symm
  refine ⟨u, ⟨?_, ?_⟩, fun R s a n z hR ha hz => key R s a z hR ha ⟨n, hz⟩⟩
  · have h6 : (MvPowerSeries.C (MvPowerSeries.constantCoeff u) : PS (O : Type) 1 g) = 1 := by
      refine GlobalTheory.T.powerSeries_eq_of_evalAtNilpotentPoints_eq (O : Type) _ hc.toIsHausdorff 1 g _ _ fun S _ _ k hk hL a ha => ?_
      have hL : LocO O S := hL inferInstance hI'
      have hS := (kills_iff p).1 ⟨k, hk⟩
      obtain ⟨ψ, hψ, hψC, -⟩ := (nv_calculus _ S (algebraMap (O : Type) S) 1 g a ha).1
      rw [← hψ, ← hψ, hψC, map_one]
      obtain ⟨z, hz⟩ := hex (mkL O S hL) (mkS O S hL) 0 hS (fun _ => IsNilpotent.zero)
      have h7 := key _ _ _ _ hS (fun _ => IsNilpotent.zero) hz
      rw [hY.zero] at hz
      have h8 := pval_mul h1 h2 hz hz
      rw [add_zero] at h8
      have h9 : z = 1 := mul_eq_left.1 (pval_unique h1 h2 h8 hz)
      have h10 := (nv_calculus _ S (algebraMap (O : Type) S) 1 g ![0] (fun i j => by
        fin_cases i; exact IsNilpotent.zero)).2.2.2.2.2 (fun i j i' j' => by
        fin_cases i; exact zero_mul _) u
      rw [Finset.sum_eq_zero (fun q _ => by
        rw [Subsingleton.elim q.1 0]; exact mul_zero _), add_zero] at h10
      rw [← h10]
      rw [h9] at h7
      exact h7.symm
    simpa using congrArg MvPowerSeries.constantCoeff h6
  · refine GlobalTheory.T.powerSeries_eq_of_evalAtNilpotentPoints_eq (O : Type) _ hc.toIsHausdorff 2 g _ _ fun S _ _ k hk hL a ha => ?_
    have hL : LocO O S := hL inferInstance hI'
    have hS := (kills_iff p).1 ⟨k, hk⟩
    obtain ⟨⟨ψ, hψ, -, hψX⟩, hnil, hsub, -⟩ := nv_calculus _ S (algebraMap (O : Type) S) 2 g a ha
    have hpt : ∀ (i : Fin 2) (j : Fin g), nv (algebraMap (O : Type) S) (pt (O : Type) g i j) a = a i j :=
      fun i j => (hψ _).symm.trans (hψX (i, j))
    have hpt0 : ∀ (i : Fin 2) (j : Fin g), MvPowerSeries.constantCoeff (pt (O : Type) g i j) = 0 :=
      fun i j => MvPowerSeries.constantCoeff_X _
    have hadd : addOf F.F (pt (O : Type) (n := 2) g 0) (pt (O : Type) (n := 2) g 1) = F.F := by
      funext i
      have : (fun q : Fin 2 × Fin g => ![pt (O : Type) (n := 2) g 0, pt (O : Type) (n := 2) g 1] q.1 q.2) =
          MvPowerSeries.X := by
        funext ⟨i, j⟩
        fin_cases i <;> rfl
      simp only [addOf, ev, this]
      exact congrFun MvPowerSeries.subst_self _
    have hev : ∀ b : Fin g → PS (O : Type) 2 g, (∀ j, MvPowerSeries.constantCoeff (b j) = 0) →
        nv (algebraMap (O : Type) S) (ev (n := 2) ![b] u) a =
          nv (algebraMap (O : Type) S) u ![fun j => nv (algebraMap (O : Type) S) (b j) a] := by
      intro b hb
      refine (hsub 1 g ![b] u (fun i j => by fin_cases i; exact hb j)).trans ?_
      congr 1
      funext i j
      fin_cases i
      rfl
    rw [hadd, ← hψ (_ * _), map_mul, hψ, hψ, hev _ F.const, hev _ (hpt0 0), hev _ (hpt0 1)]
    simp only [hpt]
    obtain ⟨z, hz⟩ := hex (mkL O S hL) (mkS O S hL) (a 0) hS (ha 0)
    obtain ⟨z', hz'⟩ := hex (mkL O S hL) (mkS O S hL) (a 1) hS (ha 1)
    have h8 := pval_mul h1 h2 hz hz'
    rw [hY.law _ _ _ _ (ha 0) (ha 1)] at h8
    have ha2 : ![a 0, a 1] = a := by
      funext i
      fin_cases i <;> rfl
    have e1 := key _ _ _ _ hS (ha 0) hz
    have e2 := key _ _ _ _ hS (ha 1) hz'
    erw [ha2] at h8
    have e3 := key _ _ _ _ hS (fun j => (hnil _ (F.const j)).1) h8
    rw [Units.val_mul, e1, e2] at e3
    exact e3.symm

end GlobalTheory.ChF
