import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNumeratorOfInvolution
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsMulEqPolynomialWeierstrassP

open Filter PeriodPair Polynomial WeierstrassCurve UpperHalfPlane
open scoped Topology

noncomputable section

namespace GlobalTheory

variable {L L' : PeriodPair} {α : ℂ}

def latticeIsogeny (α : ℂ) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice) :
    (latticeCurve L).toAffine.Point →+ (latticeCurve L').toAffine.Point :=
  (QuotientAddGroup.lift L.lattice.toAddSubgroup
    ((latticePointHom L').comp (AddMonoidHom.mulLeft α))
    fun l hl ↦ latticePoint_of_mem L' (hα l hl)).comp (latticePointEquiv L).symm.toAddMonoidHom

@[simp] lemma latticeIsogeny_latticePoint (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice) (z : ℂ) :
    latticeIsogeny α hα (latticePoint L z) = latticePoint L' (α * z) := by
  rw [← latticePointEquiv_mk]
  simp [latticeIsogeny, -latticePointEquiv_mk]
  rfl

theorem card_ker_latticeIsogeny (hα0 : α ≠ 0) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice) :
    Nat.card (latticeIsogeny α hα).ker =
      (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft α)).relIndex
        L'.lattice.toAddSubgroup := by
  have h1 : (latticeIsogeny α hα).ker =
      (L'.lattice.toAddSubgroup.comap (AddMonoidHom.mulLeft α)).map (latticePointHom L) := by
    ext P
    obtain ⟨z, rfl⟩ := latticePoint_surjective L P
    rw [AddMonoidHom.mem_ker, latticeIsogeny_latticePoint, latticePoint_eq_zero_iff]
    refine ⟨fun h ↦ ⟨z, h, rfl⟩, ?_⟩
    rintro ⟨w, hw, e⟩
    have hw' : α * w ∈ L'.lattice := hw
    simpa [mul_sub] using sub_mem hw' (hα _ ((latticePoint_eq_iff L).mp e))
  have h2 : (L'.lattice.toAddSubgroup.comap (AddMonoidHom.mulLeft α)).map
      (AddMonoidHom.mulLeft α) = L'.lattice.toAddSubgroup :=
    AddSubgroup.map_comap_eq_self_of_surjective (mul_left_surjective₀ hα0) _
  rw [h1, ← AddSubgroup.relIndex_ker, ker_latticePointHom,
    ← AddSubgroup.relIndex_map_map_of_injective (f := AddMonoidHom.mulLeft α) _ _
      (mul_right_injective₀ hα0), h2]

lemma derivWeierstrassP_mul_eq (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice) {A D : ℂ[X]}
    (h : ∀ z, α * z ∉ L'.lattice → ℘[L'] (α * z) = A.eval (℘[L] z) / D.eval (℘[L] z))
    {z : ℂ} (hz : α * z ∉ L'.lattice) (hD : D.eval (℘[L] z) ≠ 0) :
    α * ℘'[L'] (α * z) =
      (derivative A * D - A * derivative D).eval (℘[L] z) / D.eval (℘[L] z) ^ 2 * ℘'[L] z := by
  have d := hasDerivAt_weierstrassP L (z := z) fun h ↦ hz (hα z h)
  have d1 := (hasDerivAt_weierstrassP L' hz).comp z ((hasDerivAt_id z).const_mul α)
  have d2 := ((A.hasDerivAt _).comp z d).div ((D.hasDerivAt _).comp z d) hD
  have := d1.unique (d2.congr_of_eventuallyEq (by
    filter_upwards [(continuous_const_mul α).continuousAt.eventually
      (eventually_notMem_periodLattice L' hz)] with w hw using h w hw))
  simp only [Function.comp_apply, mul_one] at this
  rw [mul_comm, this]
  simp only [eval_sub, eval_mul]
  ring

theorem exists_latticeIsogeny_eq_div (hα0 : α ≠ 0) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice)
    (k : Subfield ℂ) (h₂ : L.g₂ ∈ k) (h₃ : L.g₃ ∈ k) (hαk : α ∈ k)
    (hk : ∀ t ∉ L.lattice, α * t ∈ L'.lattice → ℘[L] t ∈ k) :
    ∃ A D : ℂ[X], (∀ i, A.coeff i ∈ k) ∧ (∀ i, D.coeff i ∈ k) ∧ D.Monic ∧
      A.leadingCoeff = (α ^ 2)⁻¹ ∧ IsCoprime A D ∧
      A.natDegree = Nat.card (latticeIsogeny α hα).ker ∧ D.natDegree + 1 = A.natDegree ∧
      ∀ (x y : ℂ) (h : (latticeCurve L).toAffine.Nonsingular x y),
        (D.eval x = 0 → latticeIsogeny α hα (.some x y h) = 0) ∧
        (D.eval x ≠ 0 → ∃ h', latticeIsogeny α hα (.some x y h) = .some (A.eval x / D.eval x)
          (α⁻¹ * ((derivative A * D - A * derivative D).eval x / D.eval x ^ 2) * y) h') := by
  obtain ⟨A, D, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ :=
    exists_weierstrassP_mul_eq_div hα0 hα k h₂ h₃ hαk hk
  refine ⟨A, D, c1, c2, c3, c4, c5, by rw [c6, card_ker_latticeIsogeny hα0], c7, fun x y h ↦ ?_⟩
  obtain ⟨z, hz⟩ := latticePoint_surjective L (.some x y h)
  have hzL : z ∉ L.lattice := fun h' ↦
    Affine.Point.some_ne_zero _ (hz.symm.trans (latticePoint_of_mem L h'))
  rw [← hz, latticeIsogeny_latticePoint]
  rw [latticePoint_of_notMem L hzL, Affine.Point.some.injEq] at hz
  obtain ⟨rfl, rfl⟩ := hz
  refine ⟨fun h0 ↦ latticePoint_of_mem L' ((c8 z hzL).mp h0), fun h0 ↦ ?_⟩
  have hz' := (c8 z hzL).not.mp h0
  have e : α⁻¹ * ((derivative A * D - A * derivative D).eval (℘[L] z) / D.eval (℘[L] z) ^ 2) *
      (℘'[L] z / 2) = ℘'[L'] (α * z) / 2 := by
    rw [mul_assoc, ← mul_div_assoc, ← derivWeierstrassP_mul_eq hα c9 hz' h0]
    field_simp
  rw [e, ← c9 z hz']
  exact ⟨_, latticePoint_of_notMem L' hz'⟩

lemma addMonoidHom_eq_zero_of_eventually {G : Type*} [AddCommGroup G] (χ : ℂ →+ G) {z₀ : ℂ}
    (h : ∀ᶠ z in 𝓝 z₀, χ z = 0) (z : ℂ) : χ z = 0 := by
  have h1 : Tendsto (fun n : ℕ ↦ z₀ + z / n) atTop (𝓝 z₀) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat z).const_add z₀
  obtain ⟨n, hn, hn0⟩ := ((h1.eventually h).and (eventually_gt_atTop 0)).exists
  rw [map_add, h.self_of_nhds, zero_add] at hn
  have : z = n • (z / n) := by
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    rw [nsmul_eq_mul]; field_simp
  rw [this, map_nsmul, hn, nsmul_zero]

theorem exists_eq_latticePoint_mul (ψ : ℂ →+ (latticeCurve L').toAffine.Point) {F : ℂ → ℂ}
    {z₀ : ℂ} (hF : AnalyticAt ℂ F z₀) (h : ∀ᶠ z in 𝓝 z₀, ∃ y h', ψ z = .some (F z) y h') :
    ∃ α : ℂ, ∀ z, ψ z = latticePoint L' (α * z) := by
  obtain ⟨z₁, h4, hF₁, h₁⟩ : ∃ z₁, (4 • ψ) z₁ ≠ 0 ∧ AnalyticAt ℂ F z₁ ∧
      ∀ᶠ z in 𝓝 z₁, ∃ y h', ψ z = .some (F z) y h' := by
    by_contra hc
    have h2 := addMonoidHom_eq_zero_of_eventually (4 • ψ) (z₀ := z₀) (by
      filter_upwards [hF.eventually_analyticAt, h.eventually_nhds] with z h1 h2
      by_contra h3
      exact hc ⟨z, h3, h1, h2⟩) (z₀ / 4)
    rw [AddMonoidHom.nsmul_apply, ← map_nsmul, show 4 • (z₀ / 4) = z₀ by simp; ring] at h2
    obtain ⟨y, h', e⟩ := h.self_of_nhds
    exact Affine.Point.some_ne_zero _ (e.symm.trans h2)
  obtain ⟨w, hw⟩ := latticePoint_surjective L' (ψ z₁)
  have hw4 : w + w + (w + w) ∉ L'.lattice := fun hc ↦ h4 (by
    rw [AddMonoidHom.nsmul_apply, ← hw, ← latticePointHom_apply, ← map_nsmul,
      latticePointHom_apply, latticePoint_eq_zero_iff]
    convert hc using 1
    simp; ring)
  have hw2 : w + w ∉ L'.lattice := fun hc ↦ hw4 (add_mem hc hc)
  have hw1 : w ∉ L'.lattice := fun hc ↦ hw2 (add_mem hc hc)
  have hwF : ℘[L'] w = F z₁ := by
    obtain ⟨y, h', e⟩ := h₁.self_of_nhds
    rw [e, latticePoint_of_notMem L' hw1, Affine.Point.some.injEq] at hw
    exact hw.1
  have hP := L'.analyticOnNhd_weierstrassP w hw1
  have hP' : deriv ℘[L'] w ≠ 0 := by simpa [derivWeierstrassP_eq_zero_iff L' hw1] using hw2
  obtain ⟨g, hg, hg0, hg1⟩ : ∃ g : ℂ → ℂ, AnalyticAt ℂ g (F z₁) ∧ g (F z₁) = w ∧
      ∀ᶠ x in 𝓝 (F z₁), ℘[L'] (g x) = x := by
    rw [← hwF]
    exact ⟨_, hP.analyticAt_localInverse hP', HasStrictFDerivAt.localInverse_apply_image ..,
      HasStrictDerivAt.eventually_right_inverse ..⟩
  let H : ℂ → ℂ := fun t ↦ g (F (z₁ + t))
  have hH : AnalyticAt ℂ H 0 :=
    (hg.comp hF₁).comp_of_eq (f := fun t ↦ z₁ + t) (by fun_prop) (by simp)
  have hH0 : H 0 = w := by simp [H, hg0]
  have hc := hH.continuousAt
  have hc' : ContinuousAt (fun t ↦ H (-t)) 0 :=
    ContinuousAt.comp_of_eq (f := fun t : ℂ ↦ -t) hc (by fun_prop) (by simp)
  have ev : ∀ {f : ℂ → ℂ}, ContinuousAt f 0 → f 0 ∉ L'.lattice → ∀ᶠ t in 𝓝 0, f t ∉ L'.lattice :=
    fun hf h0 ↦ hf.eventually (eventually_notMem_periodLattice L' h0)
  have ht : Tendsto (fun t ↦ z₁ + t) (𝓝 0) (𝓝 z₁) := Continuous.tendsto' (by fun_prop) _ _ (by simp)
  have s1 : ∀ᶠ t in 𝓝 0, ψ (z₁ + t) = latticePoint L' (H t) ∨
      ψ (z₁ + t) = latticePoint L' (-H t) := by
    filter_upwards [ht.eventually h₁, ht.eventually (hF₁.continuousAt.eventually hg1),
      ev hc (hH0 ▸ hw1)] with t ⟨y, h', e⟩ e' h3
    rw [latticePoint_neg, e, latticePoint_of_notMem L' h3]
    exact Affine.Point.X_eq_iff.mp e'.symm
  have s2 : ∀ᶠ t in 𝓝 0, ψ t = latticePoint L' (H t - w) := by
    filter_upwards [s1, (continuous_neg.tendsto' 0 0 neg_zero).eventually s1,
      ev (f := fun t ↦ -H t + H (-t) - (w + w)) ((hc.neg.add hc').sub continuousAt_const)
        (by simpa [hH0, -neg_add_rev] using hw2),
      ev (f := fun t ↦ -H t + -H (-t) - (w + w)) ((hc.neg.add hc'.neg).sub continuousAt_const)
        (fun hh ↦ hw4 (by convert neg_mem hh using 1; simp [hH0]; ring))] with t a b c d
    have key : ψ (z₁ + t) + ψ (z₁ + -t) = latticePoint L' (w + w) := by
      rw [latticePoint_add, hw, ← map_add, ← map_add]; congr 1; ring
    rcases a with a | a
    · rw [← latticePointHom_apply, map_sub, latticePointHom_apply, latticePointHom_apply, ← a, hw,
        map_add, add_sub_cancel_left]
    · rcases b with b | b <;> rw [a, b, ← latticePoint_add, latticePoint_eq_iff] at key
      exacts [(c key).elim, (d key).elim]
  let u : ℂ → ℂ := fun t ↦ H t - w
  have hu : AnalyticAt ℂ u 0 := by fun_prop
  have hu0 : u 0 = 0 := by simp [u, hH0]
  have t1 : Tendsto (fun p : ℂ × ℂ ↦ p.1) (𝓝 (0, 0)) (𝓝 0) := continuous_fst.tendsto _
  have t2 : Tendsto (fun p : ℂ × ℂ ↦ p.2) (𝓝 (0, 0)) (𝓝 0) := continuous_snd.tendsto _
  have t3 : Tendsto (fun p : ℂ × ℂ ↦ p.1 + p.2) (𝓝 (0, 0)) (𝓝 0) := by simpa using t1.add t2
  have tu : Tendsto u (𝓝 0) (𝓝 0) := by simpa [hu0] using hu.continuousAt.tendsto
  have s3 : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, 0), u (p.1 + p.2) = u p.1 + u p.2 := by
    have t4 : Tendsto (fun p : ℂ × ℂ ↦ u (p.1 + p.2) - (u p.1 + u p.2)) (𝓝 (0, 0)) (𝓝 0) := by
      simpa using (tu.comp t3).sub ((tu.comp t1).add (tu.comp t2))
    filter_upwards [t1.eventually s2, t2.eventually s2, t3.eventually s2,
      t4.eventually (L'.compl_lattice_sdiff_singleton_mem_nhds 0)] with p a b c d
    rw [map_add, a, b, ← latticePoint_add, eq_comm, latticePoint_eq_iff] at c
    by_contra hne
    exact d ⟨c, fun e ↦ hne (sub_eq_zero.mp e)⟩
  have s4 : ∀ᶠ s in 𝓝 0, deriv (fun t ↦ u t - deriv u 0 * t) s = 0 := by
    filter_upwards [s3.curry_nhds, hu.eventually_analyticAt] with s a b
    have d1 : HasDerivAt (fun t ↦ u (s + t)) (deriv u s) 0 :=
      HasDerivAt.comp_const_add s 0 (by simpa using b.differentiableAt.hasDerivAt)
    have d2 := d1.unique ((hu.differentiableAt.hasDerivAt.const_add (u s)).congr_of_eventuallyEq a)
    have d3 := (b.differentiableAt.hasDerivAt.sub ((hasDerivAt_id s).const_mul (deriv u 0))).deriv
    simpa [d2] using! d3
  have s5 := analyticOrderAt_eq_top.mp ((analyticOrderAt_deriv_eq_top_iff_of_eq_zero
    (f := fun t ↦ u t - deriv u 0 * t) (z₀ := 0) (by fun_prop) (by simp [hu0])).mp
      (analyticOrderAt_eq_top.mpr s4))
  refine ⟨deriv u 0, fun z ↦ sub_eq_zero.mp (addMonoidHom_eq_zero_of_eventually
    (ψ - (latticePointHom L').comp (AddMonoidHom.mulLeft (deriv u 0))) (z₀ := 0) ?_ z)⟩
  filter_upwards [s2, s5] with t a b
  change ψ t - latticePoint L' (deriv u 0 * t) = 0
  rw [a, ← sub_eq_zero.mp b, sub_self]

theorem exists_eq_latticeIsogeny
    (φ : (latticeCurve L).toAffine.Point →+ (latticeCurve L').toAffine.Point) (A B D : ℂ[X])
    (hD : D ≠ 0) (hφ : ∀ x y h, D.eval x ≠ 0 →
      ∃ y' h', φ (.some x y h) = .some ((A.eval x + B.eval x * y) / D.eval x) y' h') :
    ∃ (α : ℂ) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice), α ≠ 0 ∧ φ = latticeIsogeny α hα := by
  obtain ⟨x₀, hx₀⟩ : ∃ x, D.eval x ≠ 0 := by
    by_contra! hc
    exact hD (Polynomial.funext (by simpa using hc))
  obtain ⟨z₀, hz₀, rfl⟩ := exists_weierstrassP_eq L x₀
  have hP := L.analyticOnNhd_weierstrassP z₀ hz₀
  have hP' := L.analyticOnNhd_derivWeierstrassP z₀ hz₀
  have hp : ∀ Q : ℂ[X], AnalyticAt ℂ (fun z ↦ Q.eval (℘[L] z)) z₀ := fun Q ↦
    (Q.differentiable.analyticAt _).comp hP
  obtain ⟨α, hα⟩ := exists_eq_latticePoint_mul (φ.comp (latticePointHom L)) (z₀ := z₀)
    (F := fun z ↦ (A.eval (℘[L] z) + B.eval (℘[L] z) * (℘'[L] z / 2)) / D.eval (℘[L] z))
    (((hp A).add ((hp B).mul (by fun_prop (disch := simp)))).div (hp D) hx₀) (by
      filter_upwards [eventually_notMem_periodLattice L hz₀,
        (hp D).continuousAt.eventually_ne hx₀] with z h1 h2
      simpa [latticePoint_of_notMem L h1] using hφ _ _ (latticeCurve_nonsingular L h1) h2)
  simp only [AddMonoidHom.comp_apply, latticePointHom_apply] at hα
  refine ⟨α, fun l hl ↦ ?_, ?_, ?_⟩
  · rw [← latticePoint_eq_zero_iff, ← hα, latticePoint_of_mem L hl, map_zero]
  · rintro rfl
    obtain ⟨y, h', e⟩ := hφ _ _ (latticeCurve_nonsingular L hz₀) hx₀
    rw [← latticePoint_of_notMem L hz₀, hα, latticePoint_of_mem L' (by simp)] at e
    exact Affine.Point.some_ne_zero _ e.symm
  · ext P
    obtain ⟨z, rfl⟩ := latticePoint_surjective L P
    rw [hα, latticeIsogeny_latticePoint]

theorem weierstrass_uniformisation :
    (∀ L : PeriodPair, (latticeCurve L).IsElliptic) ∧
    (∀ L : PeriodPair, ∃ e : (ℂ ⧸ L.lattice.toAddSubgroup) ≃+ (latticeCurve L).toAffine.Point,
      ∀ z ∉ L.lattice, ∃ h, e (z : ℂ ⧸ L.lattice.toAddSubgroup) =
        .some (℘[L] z) (℘'[L] z / 2) h) ∧
    (∀ L : PeriodPair, (∃ (a : ℂ) (τ : ℍ), a ≠ 0 ∧
        ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) ∧
      ∀ (a : ℂ) (τ : ℍ), a ≠ 0 → (∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) →
        (latticeCurve L).j = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) ∧
    (∀ (L L' : PeriodPair) (α : ℂ), α ≠ 0 → (∀ l ∈ L.lattice, α * l ∈ L'.lattice) →
      ∃ A D : ℂ[X],
        (∀ i, A.coeff i ∈ Subfield.closure
          ({L.g₂, L.g₃, α} ∪ ℘[L] '' {t | t ∉ L.lattice ∧ α * t ∈ L'.lattice})) ∧
        (∀ i, D.coeff i ∈ Subfield.closure
          ({L.g₂, L.g₃, α} ∪ ℘[L] '' {t | t ∉ L.lattice ∧ α * t ∈ L'.lattice})) ∧
        D.Monic ∧ A.leadingCoeff = (α ^ 2)⁻¹ ∧ IsCoprime A D ∧
        A.natDegree = (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft α)).relIndex
          L'.lattice.toAddSubgroup ∧
        D.natDegree + 1 = A.natDegree ∧
        (∀ z ∉ L.lattice, D.eval (℘[L] z) = 0 ↔ α * z ∈ L'.lattice) ∧
        ∀ z, α * z ∉ L'.lattice → ℘[L'] (α * z) = A.eval (℘[L] z) / D.eval (℘[L] z)) ∧
    (∀ (L : PeriodPair) (f : ℂ → ℂ), Meromorphic f → (∀ z, ∀ l ∈ L.lattice, f (z + l) = f z) →
      (∀ z, f (-z) = f z) →
      ∃ A D : ℂ[X], D.Monic ∧ ∀ z ∉ L.lattice, f z * D.eval (℘[L] z) = A.eval (℘[L] z)) ∧
    (∀ (W : WeierstrassCurve ℂ) [W.IsElliptic],
      ∃ (L : PeriodPair) (C : VariableChange ℂ), C • W = latticeCurve L) ∧
    (∀ (L L' : PeriodPair)
      (φ : (latticeCurve L).toAffine.Point →+ (latticeCurve L').toAffine.Point) (A B D : ℂ[X]),
      D ≠ 0 → (∀ x y h, D.eval x ≠ 0 →
        ∃ y' h', φ (.some x y h) = .some ((A.eval x + B.eval x * y) / D.eval x) y' h') →
      ∃ α : ℂ, α ≠ 0 ∧ (∀ l ∈ L.lattice, α * l ∈ L'.lattice) ∧
        ∀ z, φ (latticePoint L z) = latticePoint L' (α * z)) :=
  ⟨latticeCurve_isElliptic,
    fun L ↦ ⟨latticePointEquiv L, fun _ hz ↦ ⟨_, latticePoint_of_notMem L hz⟩⟩,
    fun L ↦ ⟨exists_lattice_eq_mul_tau L, fun _ _ ha h ↦ latticeCurve_j ha h⟩,
    fun _ _ _ hα0 hα ↦ exists_weierstrassP_mul_eq_div hα0 hα _
      (Subfield.subset_closure (by simp)) (Subfield.subset_closure (by simp))
      (Subfield.subset_closure (by simp))
      fun t ht ht' ↦ Subfield.subset_closure (.inr ⟨t, ⟨ht, ht'⟩, rfl⟩),
    fun L _ hf hp hev ↦ exists_mul_eq_polynomial_weierstrassP L hf hp hev,
    fun W _ ↦ exists_variableChange_eq_latticeCurve W,
    fun _ _ φ A B D hD hφ ↦ by
      obtain ⟨α, hα, h0, rfl⟩ := exists_eq_latticeIsogeny φ A B D hD hφ
      exact ⟨α, h0, hα, latticeIsogeny_latticePoint hα⟩⟩

end GlobalTheory
