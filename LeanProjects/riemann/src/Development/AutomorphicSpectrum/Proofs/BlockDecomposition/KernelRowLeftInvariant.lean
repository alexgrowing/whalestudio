import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def unitaryUnit {n : ℕ} (k : Matrix.unitaryGroup (Fin n) ℂ) : G n :=
  ⟨k.1, (k⁻¹).1,
    by have h : (k * k⁻¹).1 = 1 := by rw [mul_inv_cancel]; rfl
       exact h,
    by have h : (k⁻¹ * k).1 = 1 := by rw [inv_mul_cancel]; rfl
       exact h⟩

theorem unitaryUnit_inv_val {n : ℕ} (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ((unitaryUnit k)⁻¹ : G n).val = (k⁻¹).1 := rfl

theorem inner_cls {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (f g : Mat n → V) (hf : MemLp (fun y : G n => f y.val) 2 μ)
    (hg : MemLp (fun y : G n => g y.val) 2 μ) :
    ⟪cls μ f, cls μ g⟫_ℂ = ∫ y : G n, ⟪f y.val, g y.val⟫_ℂ ∂μ := by
  unfold cls
  rw [dif_pos hf, dif_pos hg, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem inner_cls_lTr {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : G n) (f g : Mat n → V)
    (hf : MemLp (fun y : G n => f y.val) 2 μ) (hf' : MemLp (fun y : G n => lTr x f y.val) 2 μ)
    (hg : MemLp (fun y : G n => g y.val) 2 μ) (hg' : MemLp (fun y : G n => lTr x⁻¹ g y.val) 2 μ) :
    ⟪cls μ (lTr x f), cls μ g⟫_ℂ = ⟪cls μ f, cls μ (lTr x⁻¹ g)⟫_ℂ := by
  rw [inner_cls μ _ _ hf' hg, inner_cls μ _ _ hf hg',
    ← integral_mul_left_eq_self (μ := μ) (fun y : G n => ⟪f y.val, lTr x⁻¹ g y.val⟫_ℂ) x]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have h : (x⁻¹ : G n).val * (x.val * y.val) = y.val := by
    rw [← Units.val_mul, ← Units.val_mul, inv_mul_cancel_left]
  simp only [lTr, Units.val_mul, h]

theorem isSec_lTr {n : ℕ} {E : KMod n} (x : G n) {f : Mat n → E.V} (hf : IsSec E f) : IsSec E (lTr x f) := by
  intro g hg k
  have hxg : x.val * g ∈ GLs n := by
    simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at hg ⊢
    exact mul_ne_zero (Matrix.isUnits_det_units x).ne_zero hg
  have := hf _ hxg k
  simpa only [lTr, mul_assoc] using this

theorem inner_rho {n : ℕ} (E : KMod n) (k : Matrix.unitaryGroup (Fin n) ℂ) (v w : E.V) :
    ⟪v, E.ρ k w⟫_ℂ = ⟪E.ρ k⁻¹ v, w⟫_ℂ := by
  have hI : ∀ a b : E.V, ⟪E.ρ k a, E.ρ k b⟫_ℂ = ⟪a, b⟫_ℂ := fun a b =>
    LinearIsometry.inner_map_map (⟨(E.ρ k : E.V →ₗ[ℂ] E.V), E.iso k⟩ : E.V →ₗᵢ[ℂ] E.V) a b
  have h1 : E.ρ k (E.ρ k⁻¹ v) = v := by
    have h := map_mul E.ρ k k⁻¹
    rw [mul_inv_cancel, map_one] at h
    have h2 := congrArg (fun S : E.V →L[ℂ] E.V => S v) h
    simpa using h2.symm
  rw [← hI (E.ρ k⁻¹ v) w, h1]

theorem one_mem_GLs (n : ℕ) : (1 : Mat n) ∈ GLs n := by
  simp [GLs]

theorem rowLeft (hLS : LtSob) (hLC : LtComm) : RowLeft := by
  intro n _ _ μ _ E _ Ω T F c hStd h A hR hRow k y hy v
  have hStd' := hStd
  obtain ⟨hLg, hUn, hRC, hSG, hAE, hWS, hWC, hCS, hSO, hPW, hS1, hS2, hS3, hS4, hOm, hc⟩ := hStd'
  have hCF := hCS.2.2.2.2.1 n μ E.V hUn
  have hSB := hCS.2.2.2.2.2.1 n μ E.V hLg hUn hRC
  obtain ⟨C, hC⟩ := hSO n μ E Ω T F hLg hUn hRC hSG hAE hCS hOm h hR
  have hLt := hLS n μ E.V hLg hUn hRC
  have hL2 : ∀ {f : Mat n → E.V}, Sob μ f → MemLp (fun y : G n => f y.val) 2 μ := fun hf => hf.2 []
  set x : G n := unitaryUnit k with hx
  set r : Mat n → E.V := fun y => A y v with hr
  set b : Mat n → E.V := fun y => A y (E.ρ k⁻¹ v) with hb
  set a : Mat n → E.V := lTr x r with ha
  have hrow := hRow v
  have hrowb := hRow (E.ρ k⁻¹ v)
  have hrS : Sob μ r := hrow.1
  have hbS : Sob μ b := hrowb.1
  have haS : Sob μ a := (hLt x r hrS).1
  have haSec : IsSec E a := isSec_lTr x hrow.2.1
  have hkey : ∀ ψ : Mat n → E.V, Sob μ ψ → IsSec E ψ → ⟪cls μ a, cls μ ψ⟫_ℂ = ⟪cls μ b, cls μ ψ⟫_ℂ := by
    intro ψ hψ hψs
    obtain ⟨ψ', hψ'S, hψ's, hψ'c, -⟩ := hC (cls μ ψ) (subset_closure ⟨ψ, hψ, hψs, rfl⟩)
    have hlψ := (hLt x⁻¹ ψ hψ).1
    have hlψ' := (hLt x⁻¹ ψ' hψ'S).1
    have hcomm := hLC n μ E Ω T F c hStd h x⁻¹ ψ ψ' hψ hψ'S hψ'c
    have e1 : ⟪cls μ a, cls μ ψ⟫_ℂ = ⟪cls μ r, cls μ (lTr x⁻¹ ψ)⟫_ℂ :=
      inner_cls_lTr μ x r ψ (hL2 hrS) (hL2 haS) (hL2 hψ) (hL2 hlψ)
    have e2 := hrow.2.2 (lTr x⁻¹ ψ) (lTr x⁻¹ ψ') hlψ (isSec_lTr _ hψs) hlψ' (isSec_lTr _ hψ's) hcomm
    have e3 : lTr x⁻¹ ψ' 1 = E.ρ k (ψ' 1) := by
      have h1 := hψ's 1 (one_mem_GLs n) k⁻¹
      rw [inv_inv, one_mul] at h1
      simpa only [lTr, mul_one, hx, unitaryUnit_inv_val] using h1
    have e4 := hrowb.2.2 ψ ψ' hψ hψs hψ'S hψ's hψ'c
    rw [e1, e2, e3, inner_rho, ← e4]
  set ψ : Mat n → E.V := (-1 : ℂ) • b + a with hψd
  have hψS : Sob μ ψ := ((hSB b hbS).2.2.2.1 (-1) a haS).1
  have hbSec : IsSec E b := hrowb.2.1
  have hψs : IsSec E ψ := by
    intro g hg k'
    simp only [hψd, Pi.add_apply, Pi.smul_apply, map_add, map_smul]
    rw [hbSec g hg k', haSec g hg k']
  have hcψ : cls μ ψ = cls μ a - cls μ b := by
    rw [hψd, hCF.2.1 (-1) b a (hL2 hbS) (hL2 haS)]
    simp [sub_eq_add_neg, add_comm]
  have hz := hkey ψ hψS hψs
  have hzero : cls μ a - cls μ b = 0 := by
    rw [hcψ] at hz
    have : ⟪cls μ a - cls μ b, cls μ a - cls μ b⟫_ℂ = 0 := by
      rw [inner_sub_left, hz, sub_self]
    exact inner_self_eq_zero.mp this
  have hfin := hCF.1 a b haS.1.continuousOn hbS.1.continuousOn (hL2 haS) (hL2 hbS) (sub_eq_zero.mp hzero) y hy
  exact hfin

end GlobalTheory.CompanionTheory.KerFc
