import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Fib

section Abstract

variable {G D W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddGroup D] [TopologicalSpace D] [IsTopologicalAddGroup D]
  [AddCommGroup W] [Module ℂ W]

theorem isLocallyConstant_translate (H : Subgroup G) (σ : Representation ℂ H W)
    (f : smoothPart (ind H σ)) (e : D → G) (he : Continuous e) (h0 : e 0 = 1)
    (hadd : ∀ a b, e (a + b) = e a * e b) (y : G) :
    IsLocallyConstant (fun d => f.1.1 (e d * y)) := by
  have hK : IsOpen {g : G | ind H σ g f.1 = f.1} := f.2
  let c : D → G := fun a => y⁻¹ * e a * y
  have hc : Continuous c := by fun_prop
  have hU : IsOpen (c ⁻¹' {g : G | ind H σ g f.1 = f.1}) := hK.preimage hc
  rw [IsLocallyConstant.iff_exists_open]
  intro d
  refine ⟨(fun x => -d + x) ⁻¹' (c ⁻¹' {g : G | ind H σ g f.1 = f.1}), hU.preimage (by fun_prop), ?_, ?_⟩
  · show ind H σ (c (-d + d)) f.1 = f.1
    simp [c, h0]
  · intro x hx
    have hx' : ind H σ (c (-d + x)) f.1 = f.1 := hx
    have h1 : e x = e d * e (-d + x) := by rw [← hadd, add_neg_cancel_left]
    have h2 := congrArg (fun v : indSpace H σ => v.1 (e d * y)) hx'
    have h3 : (ind H σ (c (-d + x)) f.1).1 (e d * y) = f.1.1 (e d * y * c (-d + x)) := rfl
    simp only [h3] at h2
    have h4 : e d * y * c (-d + x) = e x * y := by
      simp only [c, h1]; group
    simpa [h4] using h2

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ePG_true_val (i t : ℕ) (b : Fin t) : ((ePG i t ⟨true, b⟩ : Fin (i + t + 1)) : ℕ) = i + b := by
  simp [ePG]

theorem dEmb_zero (i t : ℕ) : dEmb k i t 0 = 1 := by
  apply Subtype.ext
  have : Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k) = 0 := by
    funext x; refine Fin.addCases ?_ ?_ x <;> simp
  simp [dEmb, this]

theorem dEmb_add (i t : ℕ) (a b : Fin (t + 1) → k) : dEmb k i t (a + b) = dEmb k i t a * dEmb k i t b := by
  apply Subtype.ext
  have : Fin.append (0 : Fin (i + 1) → k) (a + b) = Fin.append (0 : Fin (i + 1) → k) a + Fin.append (0 : Fin (i + 1) → k) b := by
    funext x; refine Fin.addCases ?_ ?_ x <;> simp
  simp only [dEmb, Subgroup.coe_mul, this, ofAdd_add, map_mul]

theorem continuous_dEmb (i t : ℕ) : Continuous (dEmb k i t) := by
  refine Continuous.subtype_mk ?_ _
  rw [Units.continuous_iff]
  have hcol : Continuous fun d : Fin (t + 1) → k => colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d) := by
    refine continuous_matrix fun r c => ?_
    by_cases hc : c = Fin.last _
    · subst hc
      refine Fin.lastCases ?_ (fun r' => ?_) r
      · simpa [colMat] using continuous_const
      · simp only [colMat, if_true, Fin.lastCases_castSucc]
        refine Fin.addCases (fun a => ?_) (fun a => ?_) r'
        · simpa using continuous_const
        · simpa using continuous_apply a
    · simpa [colMat, hc] using continuous_const
  constructor
  · exact continuous_const.add hcol
  · exact continuous_const.sub hcol

theorem dEmb_mul_entry (i t : ℕ) (d : Fin (t + 1) → k) (g : Mir k ((i + 1) + t + 1)) (b : Fin (t + 1)) :
    (((dEmb k i t d * g : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
        Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _) =
    ((g : GL (Fin ((i + 1) + t + 2)) k) : Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _) + d b := by
  have hg : ((g : GL (Fin ((i + 1) + t + 2)) k) : Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.last _) (Fin.last _) = 1 := by
    have := congrFun ((mem_Mir_iff k _).1 g.2) (Fin.last _)
    simpa [eLast] using this
  have hv : ((dEmb k i t d : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k).val =
      1 + colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d) := rfl
  have hc : colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _) = d b := by
    simp only [colMat, if_true, Fin.lastCases_castSucc, Fin.append_right]
  rw [Subgroup.coe_mul, Units.val_mul, hv, add_mul, one_mul, Matrix.add_apply, mul_apply,
    Finset.sum_eq_single (Fin.last _)]
  · rw [hc]
    exact congrArg (_ + ·) ((congrArg (d b * ·) hg).trans (mul_one _))
  · intro l _ hl
    simp [colMat, hl]
  · simp

theorem hpg_entry_eq_zero (i t : ℕ) (h : Mir k ((i + 1) + t + 1)) (hh : h ∈ HPG k (i + 1) (t + 1)) (b : Fin (t + 1)) :
    ((h : GL (Fin ((i + 1) + t + 2)) k) : Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _) = 0 := by
  have h1 := mem_parab_iff.1 (show ((h : GL (Fin ((i + 1) + (t + 1) + 1)) k)) ∈ parab k (ePG (i + 1) (t + 1)) from hh)
    true false b (Fin.last (i + 1)) (by decide)
  rw [ePG_false_last] at h1
  have h2 : ePG (i + 1) (t + 1) ⟨true, b⟩ = Fin.castSucc (Fin.natAdd (i + 1) b) := by
    apply Fin.ext
    rw [ePG_true_val]
    simp
  rw [h2] at h1
  exact h1

theorem fibre_isLocallyConstant_hasCompactSupport (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (y : Mir k ((i + 1) + t + 1)) :
    IsLocallyConstant (fun d : Fin (t + 1) → k => evX f (dEmb k i t d * y)) ∧
      HasCompactSupport (fun d : Fin (t + 1) → k => evX f (dEmb k i t d * y)) := by
  refine ⟨isLocallyConstant_translate (HPG k (i + 1) (t + 1)) (sigX τ σ) f.1 (dEmb k i t) (continuous_dEmb i t)
    (dEmb_zero i t) (dEmb_add i t) y, ?_⟩
  obtain ⟨C, hC, hf⟩ := f.2
  let φ : Mir k ((i + 1) + t + 1) → Fin (t + 1) → k := fun c b =>
    -(((y * c⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
        Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _)
  have hφ : Continuous φ := by
    refine continuous_pi fun b => Continuous.neg ?_
    have h1 : Continuous fun c : Mir k ((i + 1) + t + 1) =>
        (((y * c⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
          Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k) :=
      Units.continuous_val.comp (continuous_subtype_val.comp (continuous_const.mul continuous_inv))
    exact (continuous_apply_apply _ _).comp h1
  refine HasCompactSupport.intro (hC.image hφ) fun x hx => ?_
  by_contra hne
  obtain ⟨h, hh, c, hc, e⟩ := hf (dEmb k i t x * y) hne
  refine hx ⟨c, hc, ?_⟩
  have e1 : h = dEmb k i t x * (y * c⁻¹) := by
    rw [← mul_assoc]
    exact eq_mul_inv_of_mul_eq e.symm
  funext b
  have h0 := hpg_entry_eq_zero i t h hh b
  rw [e1, dEmb_mul_entry] at h0
  exact neg_eq_of_add_eq_zero_right h0

end GlobalTheory.CompanionTheory.BZPhiPG.Fib
