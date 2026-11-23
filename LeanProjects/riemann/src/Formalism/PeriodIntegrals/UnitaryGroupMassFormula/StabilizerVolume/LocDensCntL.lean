import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensCntRes

noncomputable section

namespace PI.VolStabS

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

structure AntiB (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) where
  δ : E
  D0 : F
  c : Module.Basis (Fin 2) F E
  hc0 : c 0 = 1
  hc1 : c 1 = δ
  hδ : δ * δ = algebraMap F E D0
  hσδ : σ δ = -δ
  hD0 : D0 ≠ 0

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem repr_change {ι ι' : Type} [Fintype ι'] (b : Module.Basis ι F E)
    (c : Module.Basis ι' F E) (z : Fv F v ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr z k =
      ∑ j, (Algebra.TensorProduct.basis (Fv F v) c).repr z j *
        algebraMap F (Fv F v) (b.repr (c j) k) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) c).sum_repr z]
  simp [map_sum, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_repr_tmul, mul_comm]

theorem int_iff {ι ι' : Type} [Fintype ι] [Fintype ι'] (b : Module.Basis ι F E)
    (c : Module.Basis ι' F E)
    (hbc : ∀ j k, algebraMap F (Fv F v) (b.repr (c j) k) ∈ v.adicCompletionIntegers F)
    (hcb : ∀ k j, algebraMap F (Fv F v) (c.repr (b k) j) ∈ v.adicCompletionIntegers F)
    (z : Fv F v ⊗[F] E) :
    (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr z k ∈ v.adicCompletionIntegers F) ↔
      (∀ j, (Algebra.TensorProduct.basis (Fv F v) c).repr z j ∈ v.adicCompletionIntegers F) := by
  constructor
  · intro h j
    rw [repr_change v c b z j]
    exact sum_mem (fun k _ => mul_mem (h k) (hcb k j))
  · intro h k
    rw [repr_change v b c z k]
    exact sum_mem (fun j _ => mul_mem (h j) (hbc j k))

variable {σ : E →ₐ[F] E} (A : AntiB F E σ)

abbrev Pt (x y : Fv F v) : Fv F v ⊗[F] E := x ⊗ₜ (1 : E) + y ⊗ₜ A.δ

abbrev Xc (z : Fv F v ⊗[F] E) : Fv F v := (Algebra.TensorProduct.basis (Fv F v) A.c).repr z 0

abbrev Yc (z : Fv F v ⊗[F] E) : Fv F v := (Algebra.TensorProduct.basis (Fv F v) A.c).repr z 1

theorem repr_Pt (x y : Fv F v) :
    (Algebra.TensorProduct.basis (Fv F v) A.c).repr (Pt v A x y) = Finsupp.single 0 x + Finsupp.single 1 y := by
  have h1 : A.c.repr 1 = Finsupp.single 0 1 := by rw [← A.hc0, Module.Basis.repr_self]
  have h2 : A.c.repr A.δ = Finsupp.single 1 1 := by rw [← A.hc1, Module.Basis.repr_self]
  rw [Pt, map_add, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul, h1, h2]
  simp

theorem Xc_Pt (x y : Fv F v) : Xc v A (Pt v A x y) = x := by
  simp only [Xc, repr_Pt]
  simp

theorem Yc_Pt (x y : Fv F v) : Yc v A (Pt v A x y) = y := by
  simp only [Yc, repr_Pt]
  simp

theorem decomp (z : Fv F v ⊗[F] E) : z = Pt v A (Xc v A z) (Yc v A z) := by
  apply (Algebra.TensorProduct.basis (Fv F v) A.c).repr.injective
  rw [repr_Pt]
  ext i
  fin_cases i <;> simp

theorem Pt_mul (x y x' y' : Fv F v) :
    Pt v A x y * Pt v A x' y' =
      Pt v A (x * x' + y * y' * algebraMap F (Fv F v) A.D0) (x * y' + y * x') := by
  simp only [Pt, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, A.hδ, TensorProduct.add_tmul]
  rw [Algebra.algebraMap_eq_smul_one A.D0, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
    mul_comm (algebraMap F (Fv F v) A.D0)]
  abel

theorem one_eq_Pt : (1 : Fv F v ⊗[F] E) = Pt v A 1 0 := by
  simp [Pt, Algebra.TensorProduct.one_def]

theorem sig_Pt (x y : Fv F v) : sigR (Fv F v) σ (Pt v A x y) = Pt v A x (-y) := by
  simp [Pt, sigR, Algebra.TensorProduct.map_tmul, A.hσδ, TensorProduct.tmul_neg, TensorProduct.neg_tmul]

theorem Xc_mul (z w : Fv F v ⊗[F] E) :
    Xc v A (z * w) = Xc v A z * Xc v A w + Yc v A z * Yc v A w * algebraMap F (Fv F v) A.D0 := by
  conv_lhs => rw [decomp v A z, decomp v A w]
  rw [Pt_mul, Xc_Pt]

theorem Yc_mul (z w : Fv F v ⊗[F] E) :
    Yc v A (z * w) = Xc v A z * Yc v A w + Yc v A z * Xc v A w := by
  conv_lhs => rw [decomp v A z, decomp v A w]
  rw [Pt_mul, Yc_Pt]

theorem Xc_sig (z : Fv F v ⊗[F] E) : Xc v A (sigR (Fv F v) σ z) = Xc v A z := by
  conv_lhs => rw [decomp v A z]
  rw [sig_Pt, Xc_Pt]

theorem Yc_sig (z : Fv F v ⊗[F] E) : Yc v A (sigR (Fv F v) σ z) = -Yc v A z := by
  conv_lhs => rw [decomp v A z]
  rw [sig_Pt, Yc_Pt]

theorem Xc_one : Xc v A 1 = 1 := by
  rw [one_eq_Pt v A, Xc_Pt]

theorem Yc_one : Yc v A 1 = 0 := by
  rw [one_eq_Pt v A, Yc_Pt]

theorem repr_incl (e : E) (j : Fin 2) :
    (Algebra.TensorProduct.basis (Fv F v) A.c).repr (inclR (Fv F v) e) j =
      algebraMap F (Fv F v) (A.c.repr e j) := by
  simp [inclR, Algebra.TensorProduct.basis_repr_tmul]

theorem Xc_add (z w : Fv F v ⊗[F] E) : Xc v A (z + w) = Xc v A z + Xc v A w := by
  simp only [Xc, map_add, Finsupp.add_apply]

theorem Yc_add (z w : Fv F v ⊗[F] E) : Yc v A (z + w) = Yc v A z + Yc v A w := by
  simp only [Yc, map_add, Finsupp.add_apply]

theorem Xc_neg (z : Fv F v ⊗[F] E) : Xc v A (-z) = -Xc v A z := by
  simp only [Xc, map_neg, Finsupp.neg_apply]

theorem Yc_neg (z : Fv F v ⊗[F] E) : Yc v A (-z) = -Yc v A z := by
  simp only [Yc, map_neg, Finsupp.neg_apply]

theorem Xc_zero : Xc v A 0 = 0 := by
  simp only [Xc, map_zero, Finsupp.zero_apply]

theorem Yc_zero : Yc v A 0 = 0 := by
  simp only [Yc, map_zero, Finsupp.zero_apply]

def InC (z : Fv F v ⊗[F] E) : Prop :=
  Xc v A z ∈ v.adicCompletionIntegers F ∧ Yc v A z ∈ v.adicCompletionIntegers F

variable (hD : algebraMap F (Fv F v) A.D0 ∈ v.adicCompletionIntegers F)

def lamC : Subring (Fv F v ⊗[F] E) where
  carrier := {z | InC v A z}
  mul_mem' {z w} hz hw := by
    change InC v A z at hz
    change InC v A w at hw
    change InC v A (z * w)
    refine ⟨?_, ?_⟩
    · rw [Xc_mul]
      exact add_mem (mul_mem hz.1 hw.1) (mul_mem (mul_mem hz.2 hw.2) hD)
    · rw [Yc_mul]
      exact add_mem (mul_mem hz.1 hw.2) (mul_mem hz.2 hw.1)
  one_mem' := by
    change InC v A 1
    refine ⟨?_, ?_⟩
    · rw [Xc_one]; exact one_mem _
    · rw [Yc_one]; exact zero_mem _
  add_mem' {z w} hz hw := by
    change InC v A z at hz
    change InC v A w at hw
    change InC v A (z + w)
    exact ⟨by rw [Xc_add]; exact add_mem hz.1 hw.1, by rw [Yc_add]; exact add_mem hz.2 hw.2⟩
  zero_mem' := by
    change InC v A 0
    exact ⟨by rw [Xc_zero]; exact zero_mem _, by rw [Yc_zero]; exact zero_mem _⟩
  neg_mem' {z} hz := by
    change InC v A z at hz
    change InC v A (-z)
    exact ⟨by rw [Xc_neg]; exact neg_mem hz.1, by rw [Yc_neg]; exact neg_mem hz.2⟩

theorem mem_lamC (z : Fv F v ⊗[F] E) : z ∈ lamC v A hD ↔
    Xc v A z ∈ v.adicCompletionIntegers F ∧ Yc v A z ∈ v.adicCompletionIntegers F :=
  Iff.rfl

theorem rho_mem {z : Fv F v ⊗[F] E} (hz : z ∈ lamC v A hD) : InC v A z :=
  hz

theorem incl_mem (e : E) (he : ∀ j, algebraMap F (Fv F v) (A.c.repr e j) ∈ v.adicCompletionIntegers F) :
    inclR (Fv F v) e ∈ lamC v A hD := by
  rw [mem_lamC]
  exact ⟨by rw [Xc, repr_incl]; exact he 0, by rw [Yc, repr_incl]; exact he 1⟩

theorem sig_mem {z : Fv F v ⊗[F] E} (hz : z ∈ lamC v A hD) : sigR (Fv F v) σ z ∈ lamC v A hD := by
  rw [mem_lamC] at hz ⊢
  rw [Xc_sig, Yc_sig]
  exact ⟨hz.1, neg_mem hz.2⟩

def sigC : lamC v A hD →+* lamC v A hD where
  toFun z := ⟨sigR (Fv F v) σ z, sig_mem v A hD z.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem coe_sigC (z : lamC v A hD) : (sigC v A hD z : Fv F v ⊗[F] E) = sigR (Fv F v) σ z := rfl

variable {K : Type} [CommRing K] [Algebra (𝓞 F ⧸ v.asIdeal) K] (r : K)
  (hr : r * r = algebraMap _ K (red v (algebraMap F (Fv F v) A.D0)))

include hr in

def rho : lamC v A hD →+* K where
  toFun z := algebraMap _ K (red v (Xc v A z)) + algebraMap _ K (red v (Yc v A z)) * r
  map_one' := by
    simp only [Subring.coe_one, Xc_one, Yc_one, red_one, red_zero, map_one, map_zero, zero_mul,
      add_zero]
  map_mul' z w := by
    have hz := z.2
    have hw := w.2
    rw [mem_lamC] at hz hw
    simp only [Subring.coe_mul, Xc_mul, Yc_mul]
    rw [red_add v (mul_mem hz.1 hw.1) (mul_mem (mul_mem hz.2 hw.2) hD),
      red_add v (mul_mem hz.1 hw.2) (mul_mem hz.2 hw.1), red_mul v hz.1 hw.1,
      red_mul v (mul_mem hz.2 hw.2) hD, red_mul v hz.2 hw.2, red_mul v hz.1 hw.2,
      red_mul v hz.2 hw.1]
    simp only [map_add, map_mul]
    linear_combination (-(algebraMap _ K (red v (Yc v A z)) * algebraMap _ K (red v (Yc v A w)))) * hr
  map_zero' := by
    simp only [ZeroMemClass.coe_zero, Xc_zero, Yc_zero, red_zero, map_zero, zero_mul, add_zero]
  map_add' z w := by
    have hz := z.2
    have hw := w.2
    rw [mem_lamC] at hz hw
    simp only [AddMemClass.coe_add, Xc_add, Yc_add]
    rw [red_add v hz.1 hw.1, red_add v hz.2 hw.2]
    simp only [map_add]
    ring

theorem rho_apply (z : lamC v A hD) : rho v A hD r hr z =
    algebraMap _ K (red v (Xc v A z)) + algebraMap _ K (red v (Yc v A z)) * r := rfl

theorem rho_sig (σ' : K ≃ₐ[𝓞 F ⧸ v.asIdeal] K) (hσr : σ' r = -r)
    (z : lamC v A hD) : rho v A hD r hr (sigC v A hD z) = σ' (rho v A hD r hr z) := by
  have hz := (mem_lamC v A hD _).1 z.2
  rw [rho_apply, rho_apply, coe_sigC, Xc_sig, Yc_sig, red_neg v hz.2, map_add, map_mul, AlgEquiv.commutes,
    AlgEquiv.commutes, hσr, map_neg]
  ring

variable (hbij : Function.Bijective
  (fun p : (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal) => algebraMap _ K p.1 + algebraMap _ K p.2 * r))

include hbij in
theorem rho_eq_zero (z : lamC v A hD) : rho v A hD r hr z = 0 ↔
    Valued.v (Xc v A z) < 1 ∧ Valued.v (Yc v A z) < 1 := by
  have hz := (mem_lamC v A hD _).1 z.2
  rw [rho_apply, ← red_eq_zero_iff v hz.1, ← red_eq_zero_iff v hz.2]
  constructor
  · intro h
    have h' := @hbij.1 (red v (Xc v A z), red v (Yc v A z)) (0, 0) (by simp only [map_zero, zero_mul, add_zero]; exact h)
    exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    simp

include hbij in
theorem rho_surj (w : K) : ∃ z : lamC v A hD, rho v A hD r hr z = w := by
  obtain ⟨⟨a, b⟩, hab⟩ := hbij.2 w
  obtain ⟨x, hx, rfl⟩ := red_surj v a
  obtain ⟨y, hy, rfl⟩ := red_surj v b
  refine ⟨⟨Pt v A x y, (mem_lamC v A hD _).2 ⟨by rw [Xc_Pt]; exact hx, by rw [Yc_Pt]; exact hy⟩⟩, ?_⟩
  rw [rho_apply]
  show algebraMap _ K (red v (Xc v A (Pt v A x y))) + algebraMap _ K (red v (Yc v A (Pt v A x y))) * r = w
  rw [Xc_Pt, Yc_Pt]
  exact hab

theorem smul_char (z : Fv F v ⊗[F] E) :
    (∃ z', z' ∈ lamC v A hD ∧ unifV v • z' = z) ↔
      (z ∈ lamC v A hD ∧ Valued.v (Xc v A z) < 1 ∧ Valued.v (Yc v A z) < 1) := by
  have hXs : ∀ (c : Fv F v) (z : Fv F v ⊗[F] E), Xc v A (c • z) = c * Xc v A z := fun c z => by
    simp only [Xc, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hYs : ∀ (c : Fv F v) (z : Fv F v ⊗[F] E), Yc v A (c • z) = c * Yc v A z := fun c z => by
    simp only [Yc, map_smul, Finsupp.smul_apply, smul_eq_mul]
  obtain ⟨hπ0, -, hπI⟩ := unifV_spec v
  have hπv : Valued.v (unifV v) < 1 := (lt_one_iff_unif v _).2 (by rw [inv_mul_cancel₀ hπ0, map_one])
  have hI : ∀ x : Fv F v, x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1 :=
    fun x => HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v
  constructor
  · rintro ⟨z', hz', rfl⟩
    rw [mem_lamC] at hz'
    rw [mem_lamC, hXs, hYs]
    refine ⟨⟨mul_mem hπI hz'.1, mul_mem hπI hz'.2⟩, ?_, ?_⟩
    · rw [map_mul]
      exact mul_lt_one_of_lt_of_le hπv ((hI _).1 hz'.1)
    · rw [map_mul]
      exact mul_lt_one_of_lt_of_le hπv ((hI _).1 hz'.2)
  · rintro ⟨hz, h1, h2⟩
    refine ⟨(unifV v)⁻¹ • z, ?_, ?_⟩
    · rw [mem_lamC, hXs, hYs, hI, hI]
      exact ⟨(lt_one_iff_unif v _).1 h1, (lt_one_iff_unif v _).1 h2⟩
    · rw [smul_smul, mul_inv_cancel₀ hπ0, one_smul]

end Lat

end PI.VolStabS
