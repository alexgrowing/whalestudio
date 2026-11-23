import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DetMulMapDetEqOneOfSesq
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowEqOneOfIsIntegralOfMulComplexConjEqOne
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RootMulComplexConjEqOne
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DetOneAddCompCommField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem perDet_trace_mul_ext {E : Type} [Field E] [NumberField E] (u v : E)
    (h : ∀ a : 𝓞 E, Algebra.trace ℚ E (u * a) = Algebra.trace ℚ E (v * a)) : u = v := by
  have hnd := traceForm_nondegenerate ℚ E
  apply ((Algebra.traceForm ℚ E).toDual hnd).injective
  apply (integralBasis E).ext
  intro i
  simpa [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply, integralBasis_apply] using
    h (RingOfIntegers.basis E i)

theorem perDet_exists_herm {E : Type} [Field E] [NumberField E] {La : Type} [AddCommGroup La]
    [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La) (x y : La) :
    ∃ u : E, ∀ a : 𝓞 E, Algebra.trace ℚ E (u * a) = ((EF (a • x) y : ℤ) : ℚ) := by
  have hnd := traceForm_nondegenerate ℚ E
  let f : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ
    (fun i => ((EF (RingOfIntegers.basis E i • x) y : ℤ) : ℚ))
  obtain ⟨u, hu⟩ := ((Algebra.traceForm ℚ E).toDual hnd).surjective f
  refine ⟨u, fun a => ?_⟩
  have h1 : Algebra.trace ℚ E (u * a) = f a := by
    have := LinearMap.congr_fun hu (a : E)
    simpa [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply] using this
  rw [h1]
  let L1 : 𝓞 E →ₗ[ℤ] ℚ := AddMonoidHom.toIntLinearMap
    (f.toAddMonoidHom.comp (algebraMap (𝓞 E) E).toAddMonoidHom)
  let L2 : 𝓞 E →ₗ[ℤ] ℚ := AddMonoidHom.toIntLinearMap
    { toFun := fun a => ((EF (a • x) y : ℤ) : ℚ)
      map_zero' := by simp
      map_add' := fun a b => by simp [add_smul] }
  have hL : L1 = L2 := by
    apply (RingOfIntegers.basis E).ext
    intro i
    have hb : (algebraMap (𝓞 E) E) (RingOfIntegers.basis E i) = integralBasis E i :=
      (integralBasis_apply E i).symm
    change f (algebraMap (𝓞 E) E (RingOfIntegers.basis E i)) = _
    rw [hb]
    exact (integralBasis E).constr_basis ℚ _ i
  exact LinearMap.congr_fun hL a

theorem perDet_exists_clear {E : Type} [Field E] [NumberField E] {La : Type} [AddCommGroup La]
    [Module (𝓞 E) La] (v : E ⊗[𝓞 E] La) :
    ∃ (c : 𝓞 E) (x : La), c ≠ 0 ∧ ((c : E)) • v = (1 : E) ⊗ₜ[𝓞 E] x := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul e x =>
    obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
    have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
    have hcE : (algebraMap (𝓞 E) E c) ≠ 0 := by simpa using hc0
    refine ⟨c, b • x, hc0, ?_⟩
    rw [TensorProduct.smul_tmul', TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      smul_eq_mul, Algebra.smul_def (A := E) b (1 : E)]
    congr 1
    change algebraMap (𝓞 E) E c * _ = _
    field_simp
  | add v w hv hw =>
    obtain ⟨c, x, hc, hx⟩ := hv
    obtain ⟨d, y, hd, hy⟩ := hw
    refine ⟨c * d, d • x + c • y, mul_ne_zero hc hd, ?_⟩
    have hsm : ∀ (r : 𝓞 E) (t : La), (1 : E) ⊗ₜ[𝓞 E] (r • t) = ((r : E)) • ((1 : E) ⊗ₜ[𝓞 E] t) := by
      intro r t
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
        smul_eq_mul, _root_.mul_one, Algebra.smul_def, _root_.mul_one]
    rw [TensorProduct.tmul_add, hsm, hsm, ← hx, ← hy, smul_add, smul_smul, smul_smul]
    push_cast
    congr 2 <;> ring_nf

theorem perDet_det_mul_conj {E : Type} [Field E] [NumberField E] [IsCMField E]
    (bar : 𝓞 E ≃+* 𝓞 E)
    (hbar : ∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E))
    {La : Type} [AddCommGroup La] [Module (𝓞 E) La] [Module.Finite (𝓞 E) La]
    (EF : LinearMap.BilinForm ℤ La) (hinj : Function.Injective EF)
    (adj : ∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (bar a • y))
    (g : La →ₗ[𝓞 E] La) (hg : ∀ a b, EF (g a) (g b) = EF a b) :
    LinearMap.det (g.baseChange E) * IsCMField.complexConj E (LinearMap.det (g.baseChange E)) = 1 := by
  classical
  choose h hh using perDet_exists_herm (E := E) EF
  let σ : E →+* E := (IsCMField.complexConj E : E →+* E)
  have hσ : ∀ c : 𝓞 E, σ (c : E) = ((bar c : 𝓞 E) : E) := fun c => (hbar c).symm
  have hbb : ∀ c : 𝓞 E, bar (bar c) = c := by
    intro c
    apply RingOfIntegers.ext
    rw [hbar, hbar]
    exact IsCMField.complexConj_apply_apply E _
  have h_add_l : ∀ x x' y, h (x + x') y = h x y + h x' y := fun x x' y =>
    perDet_trace_mul_ext _ _ fun a => by
      rw [add_mul, map_add, hh, hh, hh, smul_add, map_add, LinearMap.add_apply]
      push_cast
      rfl
  have h_add_r : ∀ x y y', h x (y + y') = h x y + h x y' := fun x y y' =>
    perDet_trace_mul_ext _ _ fun a => by
      rw [add_mul, map_add, hh, hh, hh, map_add]
      push_cast
      rfl
  have h_smul_l : ∀ (c : 𝓞 E) x y, h (c • x) y = (c : E) * h x y := fun c x y =>
    perDet_trace_mul_ext _ _ fun a => by
      have e1 : (c : E) * h x y * (a : E) = h x y * ((a * c : 𝓞 E) : E) := by
        push_cast; ring
      rw [e1, hh, hh, smul_smul]
  have h_smul_r : ∀ (c : 𝓞 E) x y, h x (c • y) = σ (c : E) * h x y := fun c x y =>
    perDet_trace_mul_ext _ _ fun a => by
      have e1 : σ (c : E) * h x y * (a : E) = h x y * ((bar c * a : 𝓞 E) : E) := by
        rw [hσ]; push_cast; ring
      rw [e1, hh, hh, ← smul_smul, adj (bar c), hbb]
  have h_iso : ∀ x y, h (g x) (g y) = h x y := fun x y =>
    perDet_trace_mul_ext _ _ fun a => by
      rw [hh, hh, ← map_smul, hg]
  let f : La → (La →ₗ[𝓞 E] E) := fun y =>
    { toFun := fun x => h x y
      map_add' := fun x x' => h_add_l x x' y
      map_smul' := fun c x => by
        rw [h_smul_l, RingHom.id_apply, Algebra.smul_def] }
  let F : La → ((E ⊗[𝓞 E] La) →ₗ[E] E) := fun y => LinearMap.liftBaseChange E (f y)
  have F_tmul : ∀ y (e : E) x, F y (e ⊗ₜ[𝓞 E] x) = e * h x y := by
    intro y e x
    simp only [F, LinearMap.liftBaseChange_tmul, smul_eq_mul]
    rfl
  have F_add : ∀ y y', F (y + y') = F y + F y' := by
    intro y y'
    apply LinearMap.ext
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul e x => rw [LinearMap.add_apply, F_tmul, F_tmul, F_tmul, h_add_r, mul_add]
    | add a b ha hb =>
      rw [map_add, map_add, ha, hb]
  have F_smul : ∀ (c : 𝓞 E) y, F (c • y) = σ (c : E) • F y := by
    intro c y
    apply LinearMap.ext
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul e x =>
      rw [LinearMap.smul_apply, F_tmul, F_tmul, h_smul_r, smul_eq_mul]
      ring
    | add a b ha hb =>
      rw [map_add, map_add, ha, hb]
  let f0 : E →+ La →+ ((E ⊗[𝓞 E] La) →ₗ[E] E) := AddMonoidHom.mk'
    (fun e => AddMonoidHom.mk' (fun y => σ e • F y) (fun y y' => by rw [F_add, smul_add]))
    (fun e e' => by
      ext y : 1
      simp [add_smul])
  let G : (E ⊗[𝓞 E] La) →+ ((E ⊗[𝓞 E] La) →ₗ[E] E) := TensorProduct.liftAddHom f0
    (fun r e y => by
      change σ (r • e) • F y = σ e • F (r • y)
      rw [F_smul, smul_smul, Algebra.smul_def, map_mul, _root_.mul_comm])
  have G_tmul : ∀ (e : E) y, G (e ⊗ₜ[𝓞 E] y) = σ e • F y := fun e y => rfl
  have G_smul : ∀ (c : E) w, G (c • w) = σ c • G w := by
    intro c w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul e y =>
      rw [TensorProduct.smul_tmul', G_tmul, G_tmul, smul_eq_mul, map_mul, smul_smul]
    | add a b ha hb => rw [smul_add, map_add, map_add, ha, hb, smul_add]
  let Hf : (E ⊗[𝓞 E] La) →ₗ[E] (E ⊗[𝓞 E] La) →ₛₗ[σ] E :=
    LinearMap.mk₂'ₛₗ (RingHom.id E) σ (fun v w => G w v)
      (fun v v' w => map_add _ _ _)
      (fun c v w => by rw [map_smul]; rfl)
      (fun v w w' => by rw [map_add, LinearMap.add_apply])
      (fun c v w => by rw [G_smul, LinearMap.smul_apply])
  have hHf : ∀ v w, Hf v w = G w v := fun _ _ => rfl
  have hnd : ∀ v, (∀ w, Hf v w = 0) → v = 0 := by
    intro v hv
    obtain ⟨c, x, hc, hx⟩ := perDet_exists_clear v
    have hcE : (c : E) ≠ 0 := by simpa using hc
    have h0 : ∀ y, h x y = 0 := by
      intro y
      have h1 := hv ((1 : E) ⊗ₜ[𝓞 E] y)
      rw [hHf, G_tmul, map_one, one_smul] at h1
      have h2 : F y ((c : E) • v) = 0 := by rw [map_smul, h1, smul_zero]
      rw [hx, F_tmul, _root_.one_mul] at h2
      exact h2
    have hx0 : x = 0 := by
      apply hinj
      rw [map_zero]
      ext y
      have h3 := hh x y 1
      rw [h0 y] at h3
      simpa using h3.symm
    rw [hx0, TensorProduct.tmul_zero] at hx
    exact (smul_eq_zero.1 hx).resolve_left hcE
  have hiso : ∀ v w, Hf (g.baseChange E v) (g.baseChange E w) = Hf v w := by
    intro v w
    rw [hHf, hHf]
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, ha, hb]
    | tmul e y =>
      rw [LinearMap.baseChange_tmul, G_tmul, G_tmul, LinearMap.smul_apply, LinearMap.smul_apply]
      congr 1
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
      | tmul e' x => rw [LinearMap.baseChange_tmul, F_tmul, F_tmul, h_iso]
  exact det_mul_map_det_eq_one_of_sesq σ Hf hnd (g.baseChange E) hiso

theorem per_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (gam : D.La ≃ₗ[𝓞 E] D.La), (∀ a b, D.EF (gam a) (gam b) = D.EF a b) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gam a = a + l.M • e) → LinearMap.det ((gam : D.La →ₗ[𝓞 E] D.La).baseChange E) = 1 := by
  intro E _ _ _ H D l gam hiso hlev
  haveI := D.fin
  haveI := D.proj
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := Ideal.mem_span_singleton_self _
    rw [← l.prod] at h1
    have h2 : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb := Ideal.mul_le_left
    exact h2 h1
  have h1mem : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.coprime]; exact Submodule.mem_top
  obtain ⟨m', hm', m, hm, hmm⟩ := Submodule.mem_sup.1 h1mem
  have hcong : ∀ a, (gam : D.La →ₗ[𝓞 E] D.La) a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
    intro a
    obtain ⟨e, he⟩ := hlev (m • a) (Submodule.smul_mem_smul hm Submodule.mem_top)
    have h1 : m • gam a = m • a + ((l.M : ℕ) : 𝓞 E) • e := by
      rw [← map_smul, he, Nat.cast_smul_eq_nsmul]
    have h3 : gam a - a = m' • (gam a - a) + m • (gam a - a) := by
      rw [← add_smul, hmm, one_smul]
    have h4 : m • (gam a - a) = ((l.M : ℕ) : 𝓞 E) • e := by
      rw [smul_sub, h1, add_sub_cancel_left]
    rw [h4] at h3
    change gam a - a ∈ _
    rw [h3]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul hm' Submodule.mem_top)
      (Submodule.smul_mem_smul hM Submodule.mem_top)
  obtain ⟨u, hu1, hu2⟩ := exists_det_congr_one E D.La l.Mb (gam : D.La →ₗ[𝓞 E] D.La) hcong
  have hdet := perDet_det_mul_conj H.bar H.bar_eq D.EF D.unimod.1 D.adj
    (gam : D.La →ₗ[𝓞 E] D.La) hiso
  rw [← hu2] at hdet ⊢
  obtain ⟨n, hn, hun⟩ := pow_eq_one_of_isIntegral_of_mul_complexConj_eq_one E (u : E)
    (RingOfIntegers.isIntegral_coe u) hdet
  have hun' : u ^ n = 1 := RingOfIntegers.ext (by simpa using hun)
  have hu : u = 1 := root_eq_one_of_halfLevel E H.bar H.bar_eq l.Mb l.M l.three_le l.prod l.coprime
    u n hn hun' hu1
  rw [hu]
  simp

end GlobalTheory.CompanionTheory.Ar.Flat
