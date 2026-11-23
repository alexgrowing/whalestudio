import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open GlobalTheory.CechDR GlobalTheory.HodgeCoh KaehlerDifferential GlobalTheory.Points

namespace UpperTheory.Gal.W2

private theorem iso_alg {R : Type} [CommRing R] [Algebra ℂ R] [IsNoetherianRing R] {d : ℕ}
    (e : R →ₐ[ℂ] ℂ) (φ : Ω[R⁄ℂ] →ₗ[ℂ] (Fin d → ℂ))
    (hk : ∀ ω : Ω[R⁄ℂ], φ ω = 0 → ∃ (m : ℕ) (b : Fin m → R) (ω' : Fin m → Ω[R⁄ℂ]),
      (∀ i, e (b i) = 0) ∧ ω = ∑ i, b i • ω' i)
    (g : Fin d → R) (hg : ∀ j, e (g j) = 0) (M : Matrix (Fin d) (Fin d) ℂ)
    (hM : ∀ j, φ (D ℂ R (g j)) = M j) (hdet : M.det ≠ 0) :
    ∃ r : R, e r = 1 ∧ ∀ e' : R →ₐ[ℂ] ℂ, (∀ j, e' (g j) = 0) → e' r ≠ 0 → e' = e := by
  classical
  set m : Ideal R := RingHom.ker e with hm
  set Ig : Ideal R := Ideal.span (Set.range g) with hIgEq
  have hmem : ∀ x, x ∈ m ↔ e x = 0 := fun x => RingHom.mem_ker
  have hsub : ∀ x : R, x - algebraMap ℂ R (e x) ∈ m := fun x => by
    rw [hmem, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  let dl : R →ₗ[ℂ] R ⧸ m ^ 2 :=
    { toFun := fun x => Ideal.Quotient.mk (m ^ 2) (x - algebraMap ℂ R (e x))
      map_add' := fun x y => by
        simp only [map_add, map_sub]
        ring
      map_smul' := fun c x => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul, map_sub, AlgHom.commutes,
          Ideal.Quotient.mk_algebraMap, Algebra.algebraMap_self]
        ring }
  let dd : Derivation ℂ R (R ⧸ m ^ 2) := Derivation.mk' dl (fun a b => by
    simp only [dl, LinearMap.coe_mk, AddHom.coe_mk, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
    rw [← map_mul, ← map_mul, ← map_add, Ideal.Quotient.eq]
    have h2 : (a - algebraMap ℂ R (e a)) * (b - algebraMap ℂ R (e b)) ∈ m ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (hsub a) (hsub b)
    convert (m ^ 2).neg_mem_iff.mpr h2 using 1
    simp only [map_mul]
    ring)
  have hd : ∀ x, dd x = Ideal.Quotient.mk (m ^ 2) (x - algebraMap ℂ R (e x)) := fun x => rfl
  have hL : ∀ x, dd.liftKaehlerDifferential (D ℂ R x) = dd x := fun x =>
    Derivation.liftKaehlerDifferential_comp_D dd x
  have hkill : ∀ b ∈ m, ∀ ω, b • dd.liftKaehlerDifferential ω = 0 := by
    intro b hb
    have hz : (b • dd.liftKaehlerDifferential : Ω[R⁄ℂ] →ₗ[R] R ⧸ m ^ 2) = 0 := by
      refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun x => ?_)
      show (b • dd.liftKaehlerDifferential) (D ℂ R x) = (0 : Ω[R⁄ℂ] →ₗ[R] R ⧸ m ^ 2) (D ℂ R x)
      rw [LinearMap.smul_apply, LinearMap.zero_apply, hL, hd, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_two]
      exact Ideal.mul_mem_mul hb (hsub x)
    intro ω
    exact LinearMap.congr_fun hz ω
  have hle : m ≤ Ig ⊔ m ^ 2 := by
    intro x hx
    set c : Fin d → ℂ := Matrix.vecMul (φ (D ℂ R x)) M⁻¹ with hcEq
    have hc : ∑ j, c j • M j = φ (D ℂ R x) := by
      have h1 : Matrix.vecMul c M = φ (D ℂ R x) := by
        rw [hcEq, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
          Matrix.vecMul_one]
      rw [← h1]
      funext l
      simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
    set x' := x - ∑ j, c j • g j with hx'Eq
    have hx' : φ (D ℂ R x') = 0 := by
      simp only [hx'Eq, map_sub, map_sum, Derivation.map_smul, map_smul, hM, hc, sub_self]
    obtain ⟨k, b, ω', hb, hω⟩ := hk _ hx'
    have hx'm : x' ∈ m ^ 2 := by
      have h1 : dd.liftKaehlerDifferential (D ℂ R x') = 0 := by
        rw [hω, map_sum]
        exact Finset.sum_eq_zero fun i _ => by
          rw [map_smul]
          exact hkill _ ((hmem _).mpr (hb i)) _
      have hex' : e x' = 0 := by
        simp [hx'Eq, map_sub, map_sum, map_smul, hg, (hmem x).mp hx]
      rw [hL, hd, hex', map_zero, sub_zero, Ideal.Quotient.eq_zero_iff_mem] at h1
      exact h1
    have hsum : ∑ j, c j • g j ∈ Ig :=
      Ideal.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ (c j) (Ideal.subset_span ⟨j, rfl⟩)
    have hx : x = ∑ j, c j • g j + x' := by
      rw [hx'Eq]
      abel
    rw [hx]
    exact Submodule.add_mem_sup hsum hx'm
  have hfg : (Submodule.map (Submodule.mkQ Ig) m).FG := (IsNoetherian.noetherian m).map _
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m
    (Submodule.map (Submodule.mkQ Ig) m) hfg (by
      rw [← Submodule.map_smul'']
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, hi, q, hq, hiq⟩ := Submodule.mem_sup.mp (hle hx)
      refine ⟨q, ?_, ?_⟩
      · rw [pow_two, ← Ideal.smul_eq_mul] at hq
        exact hq
      · rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hiq]
        have : q - (i + q) = -i := by abel
        rw [this]
        exact Ig.neg_mem hi)
  refine ⟨r, ?_, ?_⟩
  · have h := (hmem _).mp hr1
    rw [map_sub, map_one, sub_eq_zero] at h
    exact h
  · intro e' he' hr'
    have hIg : Ig ≤ RingHom.ker e' := Ideal.span_le.mpr (by
      rintro _ ⟨j, rfl⟩
      exact he' j)
    have hmk : ∀ x ∈ m, e' x = 0 := by
      intro x hx
      have h0 := hr _ (Submodule.mem_map_of_mem hx)
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul] at h0
      have h3 := hIg h0
      rw [RingHom.mem_ker, map_mul] at h3
      exact (mul_eq_zero.mp h3).resolve_left hr'
    ext x
    have h := hmk _ (hsub x)
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at h
    exact h

private theorem ev_pull {Z Y : Scheme.{0}} {sZ : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ} {c : Y ⟶ Z}
    {U : Z.Opens} {V : Y.Opens} (hV : V ≤ c ⁻¹ᵁ U) {y : CxPts s' (RingHom.id ℂ)}
    (hy : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V) (f : Sec sZ U) :
    CxPts.ev s' (RingHom.id ℂ) V (Sec.res s' hV (appSec sZ s' c U f)) y = valR (y.1 ≫ c) U f :=
  (CxPts.ev_res hV hy _).trans (valR_comp _ _ _ _).symm

private def evAlg {Y : Scheme.{0}} {s' : Y ⟶ Sp ℂ} {V : Y.Opens} {y : CxPts s' (RingHom.id ℂ)}
    (h : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V) : Sec s' V →ₐ[ℂ] ℂ :=
  { (CxPts.evHom h : Sec s' V →+* ℂ) with
    commutes' := fun a => by
      have := CxPts.ev_algX h a
      rw [CxPts.ev_eq h] at this
      exact this }

private theorem evAlg_apply {Y : Scheme.{0}} {s' : Y ⟶ Sp ℂ} {V : Y.Opens} {y : CxPts s' (RingHom.id ℂ)}
    (h : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V) (f : Sec s' V) :
    evAlg h f = CxPts.ev s' (RingHom.id ℂ) V f y := (CxPts.ev_eq h f).symm

private theorem eq_of_evAlg {Y : Scheme.{0}} {s' : Y ⟶ Sp ℂ} {V : Y.Opens} (hV : IsAffineOpen V)
    {y y' : CxPts s' (RingHom.id ℂ)} (h : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V)
    (h' : y' ∈ CxPts.ptsIn s' (RingHom.id ℂ) V) (e : evAlg h' = evAlg h) : y' = y := by
  apply Subtype.ext
  rw [← specMap_valMap_fromSpec hV y'.1 h', ← specMap_valMap_fromSpec hV y.1 h]
  congr 2
  ext f
  exact congrArg (fun φ => φ f) e

private theorem isolated {Z Y : Scheme.{0}} {sZ : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ} {d : ℕ} {c₁ c₂ : Y ⟶ Z}
    {h₁ : c₁ ≫ sZ = s'} {h₂ : c₂ ≫ sZ = s'} [IsLocallyNoetherian Y] (y : CxPts s' (RingHom.id ℂ))
    (hfix : y.1 ≫ c₁ = y.1 ≫ c₂) {A : Matrix (Fin d) (Fin d) ℂ}
    (hT : GlobalTheory.W1.IsTan d c₁ c₂ h₁ h₂ y A) (hdet : (1 - A).det ≠ 0) :
    ∃ W : Y.Opens, y ∈ CxPts.ptsIn s' (RingHom.id ℂ) W ∧
      ∀ y' : CxPts s' (RingHom.id ℂ), y'.1 ≫ c₁ = y'.1 ≫ c₂ →
        y' ∈ CxPts.ptsIn s' (RingHom.id ℂ) W → y' = y := by
  obtain ⟨U, V, hV1, hV2, t, hyV, hU, hVa, φ, hφs, hφ1, hφ2, hφk⟩ := hT
  haveI : IsNoetherianRing (Sec s' V) := IsLocallyNoetherian.component_noetherian ⟨V, hVa⟩
  let g : Fin d → Sec s' V := fun j =>
    Sec.res s' hV1 (appSec sZ s' c₁ U (t j)) - Sec.res s' hV2 (appSec sZ s' c₂ U (t j))
  have hgz : ∀ (y' : CxPts s' (RingHom.id ℂ)) (hy' : y' ∈ CxPts.ptsIn s' (RingHom.id ℂ) V),
      y'.1 ≫ c₁ = y'.1 ≫ c₂ → ∀ j, evAlg hy' (g j) = 0 := by
    intro y' hy' hf j
    simp only [g, map_sub, evAlg_apply, ev_pull hV1 hy', ev_pull hV2 hy', hf, sub_self]
  have hk : ∀ ω : Ω[Sec s' V⁄ℂ], φ ω = 0 → ∃ (m : ℕ) (b : Fin m → Sec s' V)
      (ω' : Fin m → Ω[Sec s' V⁄ℂ]), (∀ i, evAlg hyV (b i) = 0) ∧ ω = ∑ i, b i • ω' i := by
    intro ω hω
    obtain ⟨m, b, ω', hb, hsum⟩ := hφk ω hω
    exact ⟨m, b, ω', fun i => by rw [evAlg_apply]; exact hb i, hsum⟩
  have hM : ∀ j, φ (D ℂ (Sec s' V) (g j)) = (1 - A) j := by
    intro j
    simp only [g, map_sub, hφ1, hφ2]
    funext l
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  obtain ⟨r, hr1, hr⟩ := iso_alg (evAlg hyV) φ hk g (hgz y hyV hfix) (1 - A) hM hdet
  refine ⟨Y.basicOpen r, ?_, ?_⟩
  · refine (CxPts.mem_ptsIn_basicOpen hyV r).mpr ?_
    rw [← evAlg_apply hyV, hr1]
    exact one_ne_zero
  · intro y' hf hy'
    have hy'V : y' ∈ CxPts.ptsIn s' (RingHom.id ℂ) V := CxPts.ptsIn_mono (Y.basicOpen_le r) hy'
    have hne : evAlg hy'V r ≠ 0 := by
      rw [evAlg_apply]
      exact (CxPts.mem_ptsIn_basicOpen hy'V r).mp hy'
    exact eq_of_evAlg hVa hyV hy'V (hr _ (hgz y' hy'V hf) hne)

theorem fixFinite_of : FixFinite := by
  intro Z Y sZ s' d c₁ c₂ h₁ h₂ _ _ _ hiso
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s'
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s'
  haveI : IsNoetherian Y := {}
  set F := {y : CxPts s' (RingHom.id ℂ) | y.1 ≫ c₁ = y.1 ≫ c₂} with hF
  have hW : ∀ y : F, ∃ W : Y.Opens, y.1 ∈ CxPts.ptsIn s' (RingHom.id ℂ) W ∧
      ∀ y' : CxPts s' (RingHom.id ℂ), y'.1 ≫ c₁ = y'.1 ≫ c₂ →
        y' ∈ CxPts.ptsIn s' (RingHom.id ℂ) W → y' = y.1 := by
    intro y
    obtain ⟨A, hT, hdet⟩ := hiso y.1 y.2
    exact isolated y.1 y.2 hT hdet
  choose W hyW hW' using hW
  have hcov : (fun y : CxPts s' (RingHom.id ℂ) => (y : Sp ℂ ⟶ Y) (IsLocalRing.closedPoint ℂ)) '' F ⊆
      ⋃ i : F, (W i : Set Y) := by
    rintro _ ⟨y, hy, rfl⟩
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, CxPts.mem_ptsIn.mp (hyW ⟨y, hy⟩)⟩
  obtain ⟨t, ht⟩ := (TopologicalSpace.NoetherianSpace.isCompact _).elim_finite_subcover
    (fun i : F => (W i : Set Y)) (fun i => (W i).isOpen) hcov
  refine (t.finite_toSet.image Subtype.val).subset ?_
  intro y' hy'
  obtain ⟨i, hi, hmem⟩ := Set.mem_iUnion₂.mp (ht ⟨y', hy', rfl⟩)
  exact ⟨i, hi, (hW' i y' hy' (CxPts.mem_ptsIn.mpr hmem)).symm⟩

end UpperTheory.Gal.W2
