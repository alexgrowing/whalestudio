import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.REALTH
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th ComplexConjugate
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.PiKFUnr

theorem indicator_mul_of_modulus_eq_one {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {t : K} (ht : modulus t = 1) (y : K) :
    Set.indicator {x : K | x ∈ 𝒪[K]} (1 : K → ℂ) (y * t) =
      Set.indicator {x : K | x ∈ 𝒪[K]} (1 : K → ℂ) y := by
  have h : y * t ∈ 𝒪[K] ↔ y ∈ 𝒪[K] := by
    rw [← modulus_le_one_iff, ← modulus_le_one_iff, modulus_mul, ht, mul_one]
  by_cases hy : y ∈ 𝒪[K]
  · rw [Set.indicator_of_mem (show y * t ∈ {x : K | x ∈ 𝒪[K]} from h.2 hy),
      Set.indicator_of_mem (show y ∈ {x : K | x ∈ 𝒪[K]} from hy)]
    rfl
  · rw [Set.indicator_of_notMem (show y * t ∉ {x : K | x ∈ 𝒪[K]} from fun h' => hy (h.1 h')),
      Set.indicator_of_notMem (show y ∉ {x : K | x ∈ 𝒪[K]} from hy)]

theorem det_mem_of_entries {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {g : Matrix (Fin 2) (Fin 2) K} (h : ∀ i j, g i j ∈ 𝒪[K]) :
    g.det ∈ 𝒪[K] := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (h 0 0) (h 1 1)) (mul_mem (h 0 1) (h 1 0))

theorem modulus_eq_one_of_unit {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (u : Kˣ) (h1 : (u : K) ∈ 𝒪[K]) (h2 : ((u⁻¹ : Kˣ) : K) ∈ 𝒪[K]) :
    modulus (u : K) = 1 := by
  refine le_antisymm (modulus_le_one_iff.2 h1) ?_
  have h := modulus_le_one_iff.2 h2
  rw [Units.val_inv_eq_inv_val, modulus_inv] at h
  exact (inv_le_one₀ (modulus_pos u.ne_zero)).1 h

theorem pikf : Ad3.K.QuadraticBaseChangeGL3.Th.RWKF → Ad3.K.GL2LocalData.WMod → Ad3.K.QuadraticBaseChangeGL3.Th.NORMU → Ad3.K.QuadraticBaseChangeGL3.Th.PIKF := by
  intro hR hW hN F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hd hc σ hσ η hη hcond hres c hcu k hk
  obtain ⟨hk1, hk2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hk
  let u : Fˣ := Matrix.GeneralLinearGroup.det k
  have huv : (u : F) = (k.val).det := rfl
  have hu1 : (u : F) ∈ 𝒪[F] := det_mem_of_entries hk1
  have hu2 : ((u⁻¹ : Fˣ) : F) ∈ 𝒪[F] := by
    have : ((u⁻¹ : Fˣ) : F) = ((k⁻¹ : GL (Fin 2) F).val).det := by
      simp [u, map_inv]
    rw [this]
    exact det_mem_of_entries hk2
  have hmodu : modulus (k.val).det = 1 := modulus_eq_one_of_unit u hu1 hu2
  have hex : ∃ t : Eˣ, Algebra.norm F (t : E) = (k.val).det :=
    hN F χ hχ hχ1 E hd hc σ hσ η hη hres u hu1 hu2
  have hmodt : modulus (hex.choose : E) = 1 := by
    have h := hW F χ hχ hχ1 E hd hc σ hσ η hη (hex.choose : E)
    rw [hex.choose_spec, hmodu] at h
    exact_mod_cast h
  have htker : c hex.choose = 1 := by
    have hmem : hex.choose ∈ unitFiltrationUnits E 0 :=
      ord_eq_zero_iff_mem.1 (modulus_eq_one_iff.1 hmodt).2
    exact MonoidHom.mem_ker.1 (hcu hmem)
  let k' : Matrix (Fin 2) (Fin 2) F := !![k.val 0 0 / (k.val).det, k.val 0 1; k.val 1 0 / (k.val).det, k.val 1 1]
  have hd0 : (k.val).det ≠ 0 := by rw [← huv]; exact u.ne_zero
  have hdi : ((k.val).det)⁻¹ ∈ 𝒪[F] := by
    rw [← huv, ← Units.val_inv_eq_inv_val]; exact hu2
  have hk'det : k'.det = 1 := by
    have hdet := Matrix.det_fin_two k.val
    simp only [k', Matrix.det_fin_two_of]
    field_simp
    rw [hdet]
  have hk'int : ∀ i j, k' i j ∈ 𝒪[F] := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [k', div_eq_mul_inv]
    · exact mul_mem (hk1 0 0) hdi
    · exact hk1 0 1
    · exact mul_mem (hk1 1 0) hdi
    · exact hk1 1 1
  have hfix := hR F χ hχ hχ1 E hd hc σ hσ η hη hcond hres k' hk'det hk'int
  funext x
  show GL2LocalData.piG χ σ (GL2LocalData.muE E χ) (GL2LocalData.lamE E χ η) c k _ x = _
  unfold GL2LocalData.piG
  rw [dif_pos hex, htker, hmodu]
  have hfun : (fun y : E => Set.indicator {x : E | x ∈ 𝒪[E]} (1 : E → ℂ) (y * (hex.choose : E))) =
      Set.indicator {x : E | x ∈ 𝒪[E]} (1 : E → ℂ) :=
    funext fun y => indicator_mul_of_modulus_eq_one hmodt y
  rw [hfun]
  have hx : GL2LocalData.rW χ σ (GL2LocalData.muE E χ) (GL2LocalData.lamE E χ η) (k.val 0 0 / (k.val).det) (k.val 0 1)
      (k.val 1 0 / (k.val).det) (k.val 1 1) (Set.indicator {x : E | x ∈ 𝒪[E]} 1) x =
      Set.indicator {x : E | x ∈ 𝒪[E]} 1 x := congrFun hfix x
  simpa using hx

end GlobalTheory.CompanionTheory.PiKFUnr
