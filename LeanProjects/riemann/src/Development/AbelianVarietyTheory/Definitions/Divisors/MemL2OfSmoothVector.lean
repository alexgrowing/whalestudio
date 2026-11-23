import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeL2InnerProduct

noncomputable section

open NumberField MeasureTheory Matrix
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.GLFin

section Abstract

variable {Γ K : Type*} [Group Γ] [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def algOp (σ : Γ →* (K →L[ℂ] K)) (c : Γ →₀ ℂ) : K →L[ℂ] K := c.sum fun γ z => z • σ γ

def typeOf (σ : Γ →* (K →L[ℂ] K)) (v : K) : Submodule ℂ K :=
  ⨅ c ∈ {c : Γ →₀ ℂ | ∀ γ, algOp σ c (σ γ v) = 0}, LinearMap.ker (algOp σ c : K →ₗ[ℂ] K)

theorem mem_typeOf {σ : Γ →* (K →L[ℂ] K)} {v w : K} :
    w ∈ typeOf σ v ↔ ∀ c : Γ →₀ ℂ, (∀ γ, algOp σ c (σ γ v) = 0) → algOp σ c w = 0 := by
  simp only [typeOf, Submodule.mem_iInf, LinearMap.mem_ker, Set.mem_setOf_eq, ContinuousLinearMap.coe_coe]

theorem self_mem_typeOf (σ : Γ →* (K →L[ℂ] K)) (v : K) : v ∈ typeOf σ v :=
  mem_typeOf.2 fun c hc => by simpa using hc 1

def orbitSpan (σ : Γ →* (K →L[ℂ] K)) (v : K) : Submodule ℂ K := Submodule.span ℂ (Set.range fun γ => σ γ v)

end Abstract

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

structure IsTestGL (f : GA E a → ℂ) : Prop where
  cont : Continuous f
  supp : HasCompactSupport f
  smooth : (fun g => f g⁻¹) ∈ Sm E a
  level : IsOpen {k : GL (Fin a) (Af E) | ∀ g, f (finGL E a k * g) = f g}

theorem isTestGL_zero : IsTestGL (fun _ : GA E a => (0 : ℂ)) :=
  ⟨continuous_const, HasCompactSupport.zero, (Sm E a).zero_mem, by simp⟩

structure IsDirac (μ : Measure (GA E a)) (U : Subgroup (GL (Fin a) (Af E))) (N : Set (GL (Fin a) (Cinf E)))
    (f : GA E a → ℂ) : Prop where
  test : IsTestGL f
  nonneg : ∀ g, 0 ≤ (f g).re ∧ (f g).im = 0
  mass : ∫ g, f g ∂μ = 1
  symm : ∀ g, f g⁻¹ = f g
  conj : ∀ (k : Kinf E a) g, f (infGL E a (Unitary.toUnits k) * g) = f (g * infGL E a (Unitary.toUnits k))
  left : ∀ u ∈ U, ∀ g, f (finGL E a u * g) = f g
  small : ∀ g, f g ≠ 0 → ∃ y ∈ N, ∃ u ∈ U, g = infGL E a y * finGL E a u

def kuHom (U : Subgroup (GL (Fin a) (Af E))) : Kinf E a × U →* GA E a where
  toFun p := infGL E a (Unitary.toUnits p.1) * finGL E a p.2
  map_one' := by simp
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Subgroup.coe_mul, mul_assoc]
    rw [← mul_assoc (infGL E a (Unitary.toUnits q.1)), infGL_comm, mul_assoc]

def word (l : List (Lie E a)) : Module.End ℂ (Sm E a) := (l.map (lie E a)).prod

variable (μ : Measure (GA E a)) [μ.IsMulLeftInvariant]

def good (H : Submodule ℂ (L2 (latticeGL E a) μ)) : Submodule ℂ (Sm E a) where
  carrier := {ψ | ψ.1 ∈ cuspCont E a ∧ IsOpen {k | finRep E a k ψ = ψ} ∧ (∃ C : ℝ, ∀ g, ‖ψ.1 g‖ ≤ C) ∧
    ∃ F ∈ H, lift (latticeGL E a) F =ᵐ[μ] ψ.1}
  zero_mem' := ⟨(cuspCont E a).zero_mem, by simp, ⟨0, by simp⟩, 0, H.zero_mem, ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _)⟩
  add_mem' := fun {φ ψ} ⟨h1, h2, ⟨C, h3⟩, F, hF, e⟩ ⟨h1', h2', ⟨C', h3'⟩, F', hF', e'⟩ =>
    ⟨add_mem h1 h1', isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset ((h2.inter h2').mem_nhds ⟨by simp, by simp⟩)
        fun k hk => by
          have e1 : finRep E a k φ = φ := hk.1
          have e2 : finRep E a k ψ = ψ := hk.2
          change finRep E a k (φ + ψ) = φ + ψ
          rw [map_add, e1, e2]),
      ⟨C + C', fun g => (norm_add_le _ _).trans (add_le_add (h3 g) (h3' g))⟩, F + F', add_mem hF hF',
      Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_add F F')) (e.add e')⟩
  smul_mem' := fun c φ ⟨h1, h2, ⟨C, h3⟩, F, hF, e⟩ =>
    ⟨Submodule.smul_mem _ c h1, isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (h2.mem_nhds (by simp))
        fun k hk => by
          have e1 : finRep E a k φ = φ := hk
          change finRep E a k (c • φ) = c • φ
          rw [map_smul, e1]),
      ⟨‖c‖ * C, fun g => (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (h3 g) (norm_nonneg c))⟩, c • F,
      H.smul_mem c hF, Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_smul c F)) (e.const_smul c)⟩

def smv (H : Submodule ℂ (L2 (latticeGL E a) μ)) : Submodule ℂ (Sm E a) := ⨅ l : List (Lie E a), (good μ H).comap (word l)

variable {μ} {H : Submodule ℂ (L2 (latticeGL E a) μ)}

theorem mem_smv {φ : Sm E a} : φ ∈ smv μ H ↔ ∀ l, word l φ ∈ good μ H := by
  simp only [smv, Submodule.mem_iInf, Submodule.mem_comap]

theorem good_of_mem_smv {φ : Sm E a} (h : φ ∈ smv μ H) : φ ∈ good μ H := by
  simpa [word] using mem_smv.1 h []

theorem lie_mem_smv (X : Lie E a) {φ : Sm E a} (h : φ ∈ smv μ H) : lie E a X φ ∈ smv μ H := by
  refine mem_smv.2 fun l => ?_
  have e : word l (lie E a X φ) = word (l ++ [X]) φ := by
    simp only [word, List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one, Module.End.mul_apply]
  rw [e]
  exact mem_smv.1 h _

theorem memL2_of_smoothVector : ∀ φ ∈ smv μ H, MemL2Quotient (latticeGL E a) μ φ.1 := by
  intro φ hφ
  obtain ⟨h1, -, -, F, -, e⟩ := good_of_mem_smv hφ
  have hl := leftInv_of_mem_cuspCont h1
  have hae : (F : GlobalTheory.AutomorphicL2Unitary.Quot (latticeGL E a) → ℂ) =ᵐ[GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ]
      descend (latticeGL E a) φ.1 := by
    refine (ae_quotMeasure_iff (μ := μ)).2 ?_
    filter_upwards [e] with g hg
    rw [hl.descend_mk]
    exact hg
  exact ⟨hl, (Lp.memLp F).ae_eq hae⟩

variable (μ H) in

def cls [μ.IsHaarMeasure] : smv μ H →ₗ[ℂ] L2 (latticeGL E a) μ := toL2ₗ μ (smv μ H) memL2_of_smoothVector

variable (μ H) in

def dR (X : Lie E a) : Module.End ℂ (smv μ H) := (lie E a X).restrict fun _ h => lie_mem_smv X h

variable (μ H) in

def kfv : Submodule ℂ (smv μ H) where
  carrier := {φ | FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ.1))}
  zero_mem' := by
    change FiniteDimensional ℂ _
    have : Submodule.span ℂ (Set.range fun k => cptRep E a k (0 : smv μ H).1) = ⊥ :=
      Submodule.span_eq_bot.2 (by rintro _ ⟨k, rfl⟩; simp)
    rw [this]; infer_instance
  add_mem' := fun {φ ψ} h h' => by
    haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ.1)) := h
    haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k ψ.1)) := h'
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E a k φ.1) ⊔
      Submodule.span ℂ (Set.range fun k => cptRep E a k ψ.1)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp only [Submodule.coe_add, map_add]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
  smul_mem' := fun c φ h => by
    haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ.1)) := h
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E a k φ.1))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp only [Submodule.coe_smul, map_smul]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨k, rfl⟩)

open Classical in

def eMat (w : InfinitePlace E) (i j : Fin a) (z : ℂ) : Lie E a := toL (Matrix.single i j (Pi.single w z))

variable (μ H) in

def cas : Module.End ℂ (smv μ H) := ∑ w : InfinitePlace E, ∑ i : Fin a, ∑ j : Fin a,
  (dR μ H (eMat w i j 1) * dR μ H (eMat w j i 1) - dR μ H (eMat w i j Complex.I) * dR μ H (eMat w j i Complex.I))

variable (μ H) in

def lap : Module.End ℂ (smv μ H) := ∑ w : InfinitePlace E, ∑ i : Fin a, ∑ j : Fin a,
  (dR μ H (eMat w i j 1) * dR μ H (eMat w i j 1) + dR μ H (eMat w i j Complex.I) * dR μ H (eMat w i j Complex.I))

end GlobalTheory.GLFin

end
