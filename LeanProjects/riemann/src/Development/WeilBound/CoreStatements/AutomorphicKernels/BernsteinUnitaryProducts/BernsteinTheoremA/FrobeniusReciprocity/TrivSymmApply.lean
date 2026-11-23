import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.TensInduction

noncomputable section

open Set MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil

namespace PositivityTheory.PfBern.Frob

structure Sec {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G) where

  s : G ⧸ H → G
  cont : Continuous s
  sec : ∀ c : G ⧸ H, ((s c : G) : G ⧸ H) = c

section Triv

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H : Subgroup G}
  {X : Type} [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  {p : X → G ⧸ H}

theorem Sec.inv_smul (σ : Sec H) (c : G ⧸ H) : (σ.s c)⁻¹ • c = ((1 : G) : G ⧸ H) := by
  have hc := σ.sec c
  calc (σ.s c)⁻¹ • c = (σ.s c)⁻¹ • ((σ.s c : G) : G ⧸ H) := by rw [hc]
    _ = ((1 : G) : G ⧸ H) := by rw [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel]

theorem Sec.inv_mul_mem (σ : Sec H) (g : G) : (σ.s (g : G ⧸ H))⁻¹ * g ∈ H := by
  have hg := σ.sec (g : G ⧸ H)
  rwa [QuotientGroup.eq] at hg

variable (hp : ∀ (g : G) (x : X), p (g • x) = g • p x) (σ : Sec H)

def zpart (x : X) : Fib p :=
  ⟨(σ.s (p x))⁻¹ • x, by rw [hp]; exact σ.inv_smul (p x)⟩

@[simp]
theorem zpart_val (x : X) : (zpart hp σ x).1 = (σ.s (p x))⁻¹ • x := rfl

include hp in
theorem p_smul_fib (g : G) (z : Fib p) : p (g • z.1) = (g : G ⧸ H) := by
  have hz : p z.1 = ((1 : G) : G ⧸ H) := z.2
  rw [hp, hz, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]

variable (hpc : Continuous p)

def triv : X × H ≃ₜ G × Fib p where
  toFun q := (σ.s (p q.1) * q.2, fibSmul hp q.2⁻¹ (zpart hp σ q.1))
  invFun r := (r.1 • r.2.1, ⟨(σ.s (r.1 : G ⧸ H))⁻¹ * r.1, σ.inv_mul_mem r.1⟩)
  left_inv q := by
    obtain ⟨x, h⟩ := q
    have e1 : ((σ.s (p x) * h : G) : G ⧸ H) = p x := by
      rw [QuotientGroup.mk_mul_of_mem _ h.2, σ.sec]
    refine Prod.ext ?_ (Subtype.ext ?_)
    · show (σ.s (p x) * h) • (((h⁻¹ : H) : G) • ((σ.s (p x))⁻¹ • x)) = x
      rw [smul_smul, smul_smul, Subgroup.coe_inv]
      simp [mul_assoc]
    · show (σ.s ((σ.s (p x) * h : G) : G ⧸ H))⁻¹ * (σ.s (p x) * h) = h
      rw [e1, inv_mul_cancel_left]
  right_inv r := by
    obtain ⟨g, z⟩ := r
    have e2 := p_smul_fib hp g z
    refine Prod.ext ?_ (Subtype.ext ?_)
    · show σ.s (p (g • z.1)) * ((σ.s (g : G ⧸ H))⁻¹ * g) = g
      rw [e2, mul_inv_cancel_left]
    · show (((⟨(σ.s (g : G ⧸ H))⁻¹ * g, σ.inv_mul_mem g⟩ : H)⁻¹ : H) : G) •
          ((σ.s (p (g • z.1)))⁻¹ • (g • z.1)) = z.1
      rw [e2, smul_smul, smul_smul, Subgroup.coe_inv]
      simp [mul_assoc]
  continuous_toFun := by
    refine Continuous.prodMk
      ((σ.cont.comp (hpc.comp continuous_fst)).mul (continuous_subtype_val.comp continuous_snd)) ?_
    exact Continuous.subtype_mk ((continuous_subtype_val.comp continuous_snd.inv).smul
      (((σ.cont.comp (hpc.comp continuous_fst)).inv).smul continuous_fst)) _
  continuous_invFun := by
    refine Continuous.prodMk (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) ?_
    exact Continuous.subtype_mk
      (((σ.cont.comp (QuotientGroup.continuous_mk.comp continuous_fst)).inv).mul continuous_fst) _

@[simp]
theorem triv_apply (q : X × H) :
    triv hp σ hpc q = (σ.s (p q.1) * q.2, fibSmul hp q.2⁻¹ (zpart hp σ q.1)) := rfl

@[simp]
theorem triv_symm_apply (r : G × Fib p) :
    (triv hp σ hpc).symm r = (r.1 • r.2.1, ⟨(σ.s (r.1 : G ⧸ H))⁻¹ * r.1, σ.inv_mul_mem r.1⟩) := rfl

end Triv

section Fap

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {H : Subgroup G} [LocallyCompactSpace H]
  {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] [MulAction G X] [ContinuousSMul G X]
  {p : X → G ⧸ H} (hp : ∀ (g : G) (x : X), p (g • x) = g • p x) (σ : Sec H)
  (hpc : Continuous p) (μH : Measure H) [μH.IsHaarMeasure]

def avg [LocallyCompactSpace (Fib p)] : SB (G × Fib p) →ₗ[ℂ] SB X :=
  intB μH (fun _ => (1 : ℂ)) continuous_const ∘ₗ pullHomeo (triv hp σ hpc)

def fap [LocallyCompactSpace (Fib p)] (α : SB G) (φ : SB (Fib p)) : SB X :=
  avg hp σ hpc μH (tens α φ)

theorem fap_apply [LocallyCompactSpace (Fib p)] (α : SB G) (φ : SB (Fib p)) (x : X) :
    ((fap hp σ hpc μH α φ : SB X) : X → ℂ) x = ∫ h, (α : G → ℂ) (σ.s (p x) * (h : G)) *
      (φ : Fib p → ℂ) (fibSmul hp h⁻¹ (zpart hp σ x)) ∂μH := by
  simp [fap, avg]

theorem fap_smul [LocallyCompactSpace (Fib p)] (α : SB G) (φ : SB (Fib p)) (g : G) (z : Fib p) :
    ((fap hp σ hpc μH α φ : SB X) : X → ℂ) (g • z.1) =
      ∫ h, (α : G → ℂ) (g * (h : G)) * (φ : Fib p → ℂ) (fibSmul hp h⁻¹ z) ∂μH := by
  rw [fap_apply, p_smul_fib hp g z]
  set s0 := σ.s (g : G ⧸ H)
  set k : H := ⟨s0⁻¹ * g, σ.inv_mul_mem g⟩
  conv_lhs => rw [← integral_mul_left_eq_self _ k]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  have e1 : s0 * ((k * h : H) : G) = g * h := by
    simp [k, mul_assoc]
  have e2 : fibSmul hp (k * h)⁻¹ (zpart hp σ (g • z.1)) = fibSmul hp h⁻¹ z := by
    apply Subtype.ext
    simp [k, s0, smul_smul, mul_assoc, p_smul_fib hp g z]
  simp only [e1, e2]

theorem eq_fap [LocallyCompactSpace (Fib p)] (α : SB G) (φ : SB (Fib p)) (f : SB X)
    (hf : ∀ (g : G) (z : Fib p), (f : X → ℂ) (g • z.1) =
      ∫ h, (α : G → ℂ) (g * (h : G)) * (φ : Fib p → ℂ) (fibSmul hp h⁻¹ z) ∂μH) :
    f = fap hp σ hpc μH α φ := by
  apply Subtype.ext
  funext x
  have hx : x = σ.s (p x) • (zpart hp σ x).1 := by simp
  rw [hx, hf, fap_smul]

end Fap

end PositivityTheory.PfBern.Frob
