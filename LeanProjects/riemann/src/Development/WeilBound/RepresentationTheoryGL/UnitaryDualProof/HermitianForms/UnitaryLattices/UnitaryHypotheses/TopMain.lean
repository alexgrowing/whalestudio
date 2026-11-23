import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.TwistedKernelFormsNonvanishing

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.LocGL GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U PositivityTheory.RgUd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Factor

variable {V D : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup D] [Module ℂ D]

theorem factor {C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (hC : ∀ v w, C w v = starRingEnd ℂ (C v w)) (q : V →ₗ[ℂ] D)
    (hk : ∀ v ∈ LinearMap.ker q, ∀ w, C v w = 0) {v v' w w' : V} (hv : q v = q v') (hw : q w = q w') :
    C v w = C v' w' := by
  have h1 : v - v' ∈ LinearMap.ker q := by rw [LinearMap.mem_ker, map_sub, hv, sub_self]
  have h2 : w - w' ∈ LinearMap.ker q := by rw [LinearMap.mem_ker, map_sub, hw, sub_self]
  have e1 : C v w = C v' w := by
    have := hk _ h1 w
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  have e2 : C v' w = C v' w' := by
    have := hk _ h2 v'
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    rw [hC w v', hC w' v', this]
  rw [e1, e2]

end Factor

theorem dpow_val (n : ℕ) (t : ℝ) (g : GL (Fin n) k) :
    ((dpow n t g : ℂˣ) : ℂ) = ((nabs k (GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) := by
  simp only [dpow, detChar, MonoidHom.coe_comp, Function.comp_apply, absPow]
  rw [MonoidHom.coe_toHomUnits]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  rw [Complex.ofReal_cpow (nabs_pos k _).le]

theorem top_core {n N : ℕ} (h : n ≤ N) {V D : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup D] [Module ℂ D]
    [Nontrivial D] (π : Representation ℂ (GL (Fin N) k) V) (ρ : Representation ℂ (GL (Fin n) k) D)
    (hadm : IsAdmissible ρ) (q : V →ₗ[ℂ] D) (hqs : Function.Surjective q)
    (hqe : ∀ g v, q (π (blkAt k n N h g) v) = ρ g (q v)) (s t : ℝ) (hst : 2 * t + s = 0)
    (E : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hE1 : IsPsd E) (hE2 : ∀ v ∈ LinearMap.ker q, ∀ w, E v w = 0)
    (hE3 : ∀ v, E v v = 0 → v ∈ LinearMap.ker q)
    (hE4 : ∀ g v w, E (π (blkAt k n N h g) v) (π (blkAt k n N h g) w) =
      ((nabs k (GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * E v w)
    (hLift : ∀ C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ, IsPsd C → (∀ v ∈ LinearMap.ker q, ∀ w, C v w = 0) →
      (∀ g v w, C (π (blkAt k n N h g) v) (π (blkAt k n N h g) w) =
        ((nabs k (GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * C v w) →
      (∀ v, (C v v).re ≤ (E v v).re) → ∃ c : ℂ, ∀ v w, C v w = c * E v w) :
    (twist ρ (dpow n t)).IsIrreducible ∧ IsUnitarisable (twist ρ (dpow n t)) := by
  obtain ⟨r, hr⟩ := LinearMap.exists_rightInverse_of_surjective q (LinearMap.range_eq_top.2 hqs)
  have hqr : ∀ x, q (r x) = x := fun x => LinearMap.congr_fun hr x
  set Bt : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ := (E ∘ₗ r).compl₂ r with hBt
  have hBt_apply : ∀ x y, Bt x y = E (r x) (r y) := fun x y => rfl
  have hdesc : ∀ v w, Bt (q v) (q w) = E v w := fun v w => by
    rw [hBt_apply]
    exact factor hE1.1 q hE2 (hqr _) (hqr _)
  have hBh : ∀ x y, Bt y x = starRingEnd ℂ (Bt x y) := fun x y => by
    rw [hBt_apply, hBt_apply, hE1.1]
  have hBp : ∀ x, x ≠ 0 → 0 < (Bt x x).re := by
    intro x hx
    rw [hBt_apply]
    rcases (hE1.2 (r x)).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      apply hx
      have h0 : E (r x) (r x) = 0 := Complex.ext heq.symm (diag_real hE1.1 _)
      have := hE3 _ h0
      rw [LinearMap.mem_ker, hqr] at this
      exact this
  have hBe : ∀ g x y, Bt (ρ g x) (ρ g y) = ((nabs k (GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * Bt x y := by
    intro g x y
    obtain ⟨v, rfl⟩ := hqs x
    obtain ⟨w, rfl⟩ := hqs y
    rw [← hqe, ← hqe, hdesc, hdesc, hE4]
  refine ⟨?_, ⟨Bt, hBh, hBp, fun g x y => ?_⟩⟩
  · apply twist_irr
    obtain ⟨K₁, hK₁o, hK₁c, -⟩ := GlobalTheory.T.compact_open_subgroups_basis k n Set.univ Filter.univ_mem
    refine irr_of_forms ρ hadm K₁ hK₁o hK₁c (fun g => nabs k (GeneralLinearGroup.det g) ^ s) Bt hBh hBp hBe ?_
    intro Ct hCh hCp hCle hCe
    set C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := (Ct ∘ₗ q).compl₂ q with hC
    have hC_apply : ∀ v w, C v w = Ct (q v) (q w) := fun v w => rfl
    obtain ⟨c, hc⟩ := hLift C ⟨fun v w => by rw [hC_apply, hC_apply, hCh], fun v => by rw [hC_apply]; exact hCp _⟩
      (fun v hv w => by rw [hC_apply, LinearMap.mem_ker.1 hv, map_zero, LinearMap.zero_apply])
      (fun g v w => by rw [hC_apply, hC_apply, hqe, hqe, hCe])
      (fun v => by rw [hC_apply, ← hdesc]; exact hCle _)
    refine ⟨c, fun x y => ?_⟩
    obtain ⟨v, rfl⟩ := hqs x
    obtain ⟨w, rfl⟩ := hqs y
    rw [← hC_apply, hc, hdesc]
  · show Bt (((dpow n t g : ℂˣ) : ℂ) • ρ g x) (((dpow n t g : ℂˣ) : ℂ) • ρ g y) = Bt x y
    have hsm : ∀ (c : ℂ) (X Y : D), Bt (c • X) (c • Y) = c * (starRingEnd ℂ c * Bt X Y) := by
      intro c X Y
      rw [LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul]
    rw [hsm, hBe, dpow_val, Complex.conj_ofReal]
    have hpos := nabs_pos k (GeneralLinearGroup.det g)
    have e : (nabs k (GeneralLinearGroup.det g) ^ t) * ((nabs k (GeneralLinearGroup.det g) ^ t) *
        (nabs k (GeneralLinearGroup.det g) ^ s)) = 1 := by
      rw [← Real.rpow_add hpos, ← Real.rpow_add hpos, show t + (t + s) = 0 by linarith, Real.rpow_zero]
    calc ((nabs k (GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) * (((nabs k (GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) *
          (((nabs k (GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * Bt x y))
        = (((nabs k (GeneralLinearGroup.det g) ^ t) * ((nabs k (GeneralLinearGroup.det g) ^ t) *
          (nabs k (GeneralLinearGroup.det g) ^ s)) : ℝ) : ℂ) * Bt x y := by push_cast; ring
      _ = Bt x y := by rw [e]; simp

end PositivityTheory.RgUd.Form.U.Asm
