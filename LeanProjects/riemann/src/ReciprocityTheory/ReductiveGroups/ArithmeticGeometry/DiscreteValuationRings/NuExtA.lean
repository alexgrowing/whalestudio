import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThickKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Out

section Dvr

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem exists_pow_le_span {ϖ : V} (hϖ : Irreducible ϖ) {r : V} (hr : r ≠ 0) :
    ∃ n : ℕ, IsLocalRing.maximalIdeal V ^ (n + 1) ≤ Ideal.span {r} := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  refine ⟨n, ?_⟩
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.span_singleton_pow, hu,
    Ideal.span_singleton_mul_left_unit u.isUnit]
  exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ n))

theorem mem_range_of_val_nonneg {ϖ : V} (hϖ : Irreducible ϖ) {v : AddValuation (FractionRing V) (WithTop ℚ)}
    (hv : ValOver ϖ (FractionRing V) v) (c : FractionRing V) (hc : 0 ≤ v c) :
    c ∈ (algebraMap V (FractionRing V)).range := by
  classical
  by_cases hc0 : c = 0
  · exact ⟨0, by rw [hc0, map_zero]⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) c
  have ha : a ≠ 0 := by
    rintro rfl
    exact hc0 (by simp)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨n1, u1, hu1⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨n2, u2, hu2⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hϖ0 : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero))
  have hu2' : algebraMap V (FractionRing V) (u2 : V) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero u2.ne_zero)
  set w : Vˣ := u1 * u2⁻¹ with hw
  have hval : HasVal ϖ (algebraMap V (FractionRing V) a / algebraMap V (FractionRing V) b) ((n1 : ℤ) - n2) := by
    refine ⟨w, ?_⟩
    rw [hu1, hu2, hw, zpow_sub₀ hϖ0, zpow_natCast, zpow_natCast]
    simp only [map_mul, map_pow, Units.val_mul]
    have hinv : algebraMap V (FractionRing V) ((u2⁻¹ : Vˣ) : V) = (algebraMap V (FractionRing V) (u2 : V))⁻¹ := by
      exact map_units_inv (algebraMap V (FractionRing V)) u2
    rw [hinv]
    field_simp
  have hv1 := hv _ _ hval
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hv1
  rw [hv1] at hc
  have hn : (0 : ℤ) ≤ (n1 : ℤ) - n2 := by
    have : ((0 : ℚ) : WithTop ℚ) ≤ (((n1 : ℤ) - n2 : ℤ) : ℚ) := by simpa using hc
    have h2 : (0 : ℚ) ≤ (((n1 : ℤ) - n2 : ℤ) : ℚ) := WithTop.coe_le_coe.mp this
    exact_mod_cast h2
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hn
  obtain ⟨w', hw'⟩ := hval
  refine ⟨ϖ ^ k * (w' : V), ?_⟩
  rw [hw', hk, zpow_natCast, map_mul, map_pow]

variable {X : Scheme.{0}}

theorem isUnit_cst (p : X ⟶ Sp V) (x : X) {r : V} (hx : r ∉ (p x).asIdeal) : IsUnit (cst p x r) := by
  have hmem : p x ∈ (Sp V).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r) := by
    have e := basicOpen_eq_of_affine (R := CommRingCat.of V) r
    exact (congrArg (fun U : (Sp V).Opens => p x ∈ U) e).mpr hx
  have e2 := Scheme.preimage_basicOpen p ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r)
  have hx' : x ∈ X.basicOpen ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r)) := by
    rw [← e2]; exact hmem
  have hu := (Scheme.mem_basicOpen X ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r)) x
    (show x ∈ p ⁻¹ᵁ ⊤ from trivial)).1 hx'
  rw [cst, gs_eq p x ⊤ (show p x ∈ (⊤ : (Sp V).Opens) from trivial)]
  exact hu

theorem exists_fst_eq (p : X ⟶ Sp V) (J : Ideal V) {r : V} (hJ : J ≤ Ideal.span {r}) (x : X)
    (hx : r ∈ (p x).asIdeal) :
    ∃ x', pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x' = x := by
  have h1 : x ∈ Set.range (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) := by
    rw [Scheme.Pullback.range_fst]
    show p x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J))
    rw [range_comap_of_surjective (V ⧸ J) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact fun y hy => (Ideal.span_singleton_le_iff_mem _).2 hx (hJ hy)
  exact h1

theorem exists_div_sec_of_thick (p : X ⟶ Sp V) [Flat p] (J : Ideal V) {r : V} (hr : r ≠ 0)
    (hJ : J ≤ Ideal.span {r}) {M : LB X} (s : LB.Sec M)
    (h : ∀ j (x' : ↑(pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))),
      pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x' ∈ M.U j →
      cst (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ≫ p) x' r ∣
        gs (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) x' (M.U j) (s.f j)) :
    ∃ s' : LB.Sec M, ∀ j, s.f j = constFn p _ r * s'.f j := by
  refine exists_div_sec p hr s fun j x hx => ?_
  by_cases hxr : r ∈ (p x).asIdeal
  · obtain ⟨x', rfl⟩ := exists_fst_eq p J hJ x hxr
    exact dvd_germ_of_thick p J hJ (s.f j) x' hx (h j x' hx)
  · exact (isUnit_cst p x hxr).dvd

end Dvr

section Sec

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]

theorem secScal_sval_c {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  have hc : LB.Coh L (Sum.elim φ₁ (fun k => h ≫ φ₂ k))
      (Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k))) := by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e
  have e := H _ _ hc
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    ⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ₂ k) r⟩
  have le : LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) ≤
      h ⁻¹ᵁ LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k)) :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  rw [sval_of s₂ (r ≫ h) z J (fun k => J (r ≫ h ≫ φ₂ k)) (fun k => by rw [Category.assoc])]
  have e2 := congrArg (gs r z _) e
  exact ((gs_res r z _ hm _).trans (gs_pull r h z _ (le hm.2) _)).symm.trans (e2.trans
    ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res r z le_top hm c) (gs_res r z _ hm _))))

end Sec

end ReciprocityTheory.ChartRestriction.G.DVR
