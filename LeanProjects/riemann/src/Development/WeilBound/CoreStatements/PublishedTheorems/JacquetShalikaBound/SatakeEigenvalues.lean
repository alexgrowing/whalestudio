import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.lift_levelP_alt₂
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SymmetricFunctionAbsoluteValues
import GroundTheory.IdeleRoots.TorusPowers.SatakeBoundAdic

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.LFun GroundTheory.Automorphic GroundTheory.Automorphic.Spherical
open scoped ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.JacquetShalikaLocal

namespace SatakeEigenvalues

open GLnLocal Iwasawa

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem qF_eq : qF (w.adicCompletion E) = Ideal.absNorm w.asIdeal :=
  GlobalTheory.LFun.SatBoundGL.resCard_completion w

theorem O_eq : 𝒪[w.adicCompletion E] = Formalism.UG.Ov E w := by
  ext x
  exact GroundTheory.Global.mem_valuationInteger_iff w x

theorem KGL_eq (n : ℕ) : KGL w n = integralGL (w.adicCompletion E) n :=
  (congrArg (Formalism.UG.GLint (Fin n)) (O_eq w)).symm.trans rfl

theorem isUnifV_uniformizer :
    Formalism.UG.IsUnifV E w (uniformizer (w.adicCompletion E) : w.adicCompletion E) :=
  GroundTheory.BlockD.SatakeBound.valued_uniformizer_eq w

theorem satEig_eq {n r : ℕ} (hr : r ≤ n) (z : Fin n → ℂˣ) :
    satEig (Formalism.UG.qV E w) n (Finset.univ.val.map z) r =
      sqrtQ (w.adicCompletion E) ^ (r * (n - r)) * evalAt z (esymmL n r) := by
  unfold satEig
  rw [Multiset.map_map, Finset.esymm_map_val, GlobalTheory.CompanionTheory.JSBound.evalAt_esymmL_eq_sum_prod]
  congr 1
  have hq : (Formalism.UG.qV E w : ℂ) = ((qF (w.adicCompletion E) : ℝ) : ℂ) := by
    rw [qF_eq]
    simp [Formalism.UG.qV]
  have he : ((r : ℂ) * ((n : ℂ) - r)) / 2 = ((((r * (n - r) : ℕ) : ℝ) / 2 : ℝ) : ℂ) := by
    push_cast [Nat.cast_sub hr]
    ring
  rw [hq, he, ← Complex.ofReal_cpow (Nat.cast_nonneg _), sqrtQ, ← Complex.ofReal_pow]
  congr 1
  rw [Real.coe_sqrt, NNReal.coe_natCast, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  ring

theorem Tj_eq {n r : ℕ} (hr : r ≤ n) :
    Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) (uniformizer (w.adicCompletion E) : w.adicCompletion E) r =
      (minusculeSet (w.adicCompletion E) n r).indicator (fun _ => (1 : ℂ)) := by
  have hK : Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E w) = integralGL (w.adicCompletion E) n := KGL_eq w n
  have hD : Formalism.UG.diagJ n (uniformizer (w.adicCompletion E) : w.adicCompletion E) r =
      ((torusPow (w.adicCompletion E) n (lamS (initSeg hr)) : GL (Fin n) (w.adicCompletion E)) :
        Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    rw [coe_torusPow, Formalism.UG.diagJ]
    congr 1
    funext i
    rw [lamS_apply]
    by_cases h : (i : ℕ) < r <;> simp [h, mem_initSeg]
  have hα : torusPow (w.adicCompletion E) n (lamS (initSeg hr)) ∈ minusculeSet (w.adicCompletion E) n r := by
    let c₀ : Pairs (initSeg hr) → 𝓀[w.adicCompletion E] := fun _ => 0
    have e : torusPow (w.adicCompletion E) n (lamS (initSeg hr)) =
        (unipC (initSeg hr) c₀)⁻¹ * gMat (initSeg hr) c₀ * 1 := by
      rw [gMat, inv_mul_cancel_left, mul_one]
    have h := mul_mem_minusculeSet (gMat_mem_minusculeSet _ c₀)
      ((integralGL (w.adicCompletion E) n).inv_mem (GroundTheory.BlockD.SatakeBound.unipC_mem_integralGL _ c₀))
      (integralGL (w.adicCompletion E) n).one_mem
    rw [card_initSeg] at h
    rw [e]
    exact h
  have hS : {g : GL (Fin n) (w.adicCompletion E) | ∃ a ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E w),
      ∃ b ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E w),
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = (a : Matrix (Fin n) (Fin n) (w.adicCompletion E)) *
        Formalism.UG.diagJ n (uniformizer (w.adicCompletion E) : w.adicCompletion E) r *
          (b : Matrix (Fin n) (Fin n) (w.adicCompletion E))} = minusculeSet (w.adicCompletion E) n r := by
    ext g
    rw [hK, hD]
    constructor
    · rintro ⟨a, ha, b, hb, e⟩
      have e' : g = a * torusPow (w.adicCompletion E) n (lamS (initSeg hr)) * b :=
        Units.ext (by rw [e, Units.val_mul, Units.val_mul])
      rw [e']
      exact mul_mem_minusculeSet hα ha hb
    · intro hg
      obtain ⟨S, hS, c, hc⟩ := exists_gMat hg
      have hk : (gMat S c)⁻¹ * g ∈ integralGL (w.adicCompletion E) n := QuotientGroup.eq.1 hc
      obtain ⟨P, hP, hPe⟩ := GroundTheory.BlockD.SatakeBound.exists_torusPow_lamS_eq (F := w.adicCompletion E)
        (A := S) (B := initSeg hr) (by rw [hS, card_initSeg])
      have e1 : g = gMat S c * ((gMat S c)⁻¹ * g) := by group
      set k := (gMat S c)⁻¹ * g with hkdef
      rw [gMat, hPe] at e1
      refine ⟨unipC S c * P⁻¹, (integralGL (w.adicCompletion E) n).mul_mem
        (GroundTheory.BlockD.SatakeBound.unipC_mem_integralGL S c) ((integralGL (w.adicCompletion E) n).inv_mem hP),
        P * k, (integralGL (w.adicCompletion E) n).mul_mem hP hk, ?_⟩
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      rw [e1]
      group
  rw [Formalism.UG.Tj, hS]
  rfl

end SatakeEigenvalues

theorem satake_eigenvalue_formula : lift_levelP_alt₂ := by
  intro E _ _ w
  refine ⟨SatakeEigenvalues.qF_eq w, ?_⟩
  intro n V _ _ ρ v z h
  obtain ⟨-, hfix, -, hT⟩ := h
  have hK := SatakeEigenvalues.KGL_eq w n
  refine ⟨fun g hg => GlobalTheory.LGrp.mem_fixed.1 hfix g (hK ▸ hg), fun r hr => ?_⟩
  have h1 := hT _ (SatakeEigenvalues.isUnifV_uniformizer w) r hr
  rw [heckeVec, SatakeEigenvalues.Tj_eq w hr, SatakeEigenvalues.satEig_eq w hr] at h1
  rw [hK] at h1
  exact h1

end PositivityTheory.JacquetShalikaLocal

end
