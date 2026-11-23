import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSymmetricImpliesSwapFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogSwapSymmetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianMetricGrading
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTest.GeoSwap

open HermLB

section Shift

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}

theorem isometric_pull_shift (L : HermLB p) (t : (k →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ)
    (π : Y ⟶ X) (hπ : π ≫ p = q) : ((L.shift t ht).pull π hπ).Isometric ((L.pull π hπ).shift t ht) :=
  isometric_of_eqOn fun σ a y _ => by
    exact (congrArg (· + 2 * t σ) (Weight.pull_φ (L.φ σ) π hπ a y)).trans
      (Weight.pull_φ ((L.φ σ).addFn fun _ => 2 * t σ) π hπ a y).symm

theorem isometric_shift_of_isometric {L M : HermLB p} (h : L.Isometric M) (t : (k →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) : (L.shift t ht).Isometric (M.shift t ht) := by
  obtain ⟨w, hw, h⟩ := h
  refine ⟨w, hw, fun σ a b y ha hb => ?_⟩
  have e := h σ a b y ha hb
  exact (congrArg (· + 2 * t σ) e).trans (add_right_comm _ _ _)

theorem isometric_tens_shift_left (L M : HermLB p) (t : (k →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) :
    ((L.shift t ht).tens M).Isometric ((L.tens M).shift t ht) :=
  isometric_of_eqOn fun σ a y _ => by
    show ((L.φ σ).φ a.1 y + (M.φ σ).φ a.2 y) + 2 * t σ = ((L.φ σ).φ a.1 y + 2 * t σ) + (M.φ σ).φ a.2 y
    ring

variable (p) in

def constB (t : ℝ) : HermLB p := (triv p).shift (fun _ => t) fun _ => rfl

theorem icls_shift_const (L : HermLB p) (t : ℝ) :
    (L.shift (fun _ => t) fun _ => rfl).icls = L.icls + (constB p t).icls := by
  rw [add_comm, constB, ← icls_tens, icls_eq_iff]
  exact (isometric_shift_of_isometric (isometric_triv_tens L).symm _ _).trans
    (isometric_tens_shift_left _ _ _ _).symm

theorem icls_constB_add (s t : ℝ) : (constB p (s + t)).icls = (constB p s).icls + (constB p t).icls := by
  rw [← icls_shift_const, icls_eq_iff]
  exact isometric_of_eqOn fun σ a y _ => by
    show ((0 : ℝ) + 2 * s) + 2 * t = (0 : ℝ) + 2 * (s + t)
    ring

variable (p) in

def constHom : ℝ →+ IsomClass p := AddMonoidHom.mk' (fun t => (constB p t).icls) icls_constB_add

theorem gdeg_shift_const (L : HermLB p) (t : (k →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (D : ℕ) :
    gdeg (L.shift t ht) D = gdeg L D := by
  simp only [gdeg, chInt, HermLB.shift, Weight.chernInt, Weight.chernPart_addFn_const]

theorem isometric_comb_three_shift (S Q A A' : HermLB p)
    (hA : A'.Isometric (A.shift (fun _ => 1) fun _ => rfl)) (m : Fin 3 → ℤ) (c : ℝ) (hc : ((m 2 : ℤ) : ℝ) = c) :
    (comb ![S, Q, A'] m).Isometric ((comb ![S, Q, A] m).shift (fun _ => c) fun _ => rfl) := by
  subst hc
  refine icls_eq_iff.1 ?_
  rw [icls_shift_const, icls_comb, icls_comb, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rw [icls_eq_iff.2 hA, icls_shift_const]
  have e : (constB p ((m 2 : ℤ) : ℝ)).icls = m 2 • (constB p 1).icls := by
    have := map_zsmul (constHom p) (m 2) 1
    simpa [constHom] using this
  rw [e, smul_add]
  abel

end Shift

theorem rename_lin_swap {κ : Type} [Fintype κ] [DecidableEq κ] (x y : κ) (c : κ → ℝ) :
    rename (Equiv.swap x y) (lin c) = lin fun z => c (Equiv.swap x y z) := by
  simp only [lin, map_sum, map_mul, rename_C, rename_X]
  exact Fintype.sum_equiv (Equiv.swap x y) _ _ fun z => by simp [Equiv.swap_apply_self]

theorem cast_triple (u v : ℤ) : (fun j => (((![u, v, 1] : Fin 3 → ℤ) j : ℤ) : ℝ)) = ![(u : ℝ), v, 1] := by
  funext j
  fin_cases j <;> simp

theorem geo_swap : ArCalc → RegularAlteration → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d D : ℕ), IsArithVar q d → IsArithVar p D → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ Ψ : MvPolynomial (Σ a, Fin (r a)) ℝ →ₗ[ℝ] ℝ, IsGeoFun (fun z : Σ a, Fin (r a) => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) D Ψ → ∀ (a : ι) (i i' : Fin (r a)), (i' : ℕ) = i + 1 → ∀ P : MvPolynomial (Σ a, Fin (r a)) ℝ, Ψ (rename (Equiv.swap (⟨a, i⟩ : Σ a, Fin (r a)) ⟨a, i'⟩) P) = -Ψ P := by
  intro hC hR k _ B Y _ _ q p d D hq hp π w ι _ E r h H fl hfl Ψ hΨ a i i' hi
  obtain ⟨G, -, hS⟩ := GlobalTheory.CovTest.homog_swap_exists_of_ar_calc hC hR
  obtain ⟨Y₁, q₁, d₁, ρ, wρ, E₁, h₁, H₁, fl₁, M, rfl, hY₁, hfl₁, hS0, hS1, hM⟩ :=
    GlobalTheory.SwapBundle.swapFl_bundle k B Y q p d D hq hp π w ι E r h H fl hfl a i i' hi
  haveI := hY₁.isIntegral
  set x : Σ a, Fin (r a) := ⟨a, i⟩ with hx
  set y : Σ a, Fin (r a) := ⟨a, i'⟩ with hy
  have hxy : x ≠ y := by
    intro e
    rw [hx, hy, Sigma.mk.inj_iff] at e
    have := congrArg Fin.val (eq_of_heq e.2)
    omega
  set L : (Σ a, Fin (r a)) → HermLB p := fun z => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w) with hL
  have key : ∀ n : (Σ a, Fin (r a)) → ℤ,
      Ψ (lin (fun z => (n z : ℝ)) ^ (d₁ + 1)) + Ψ (lin (fun z => (n (Equiv.swap x y z) : ℝ)) ^ (d₁ + 1)) = 0 := by
    intro n
    set n' : (Σ a, Fin (r a)) → ℤ := fun z => if z = x ∨ z = y then 0 else n z with hn'
    set A₀ : HermLB q₁ := comb M n' with hA₀
    set A₁ : HermLB q₁ := A₀.shift (fun _ => 1) fun _ => rfl with hA₁
    set S := VMetric.grLB fl₁ 0 (H₁.pull ρ wρ) with hSd
    set Q := VMetric.grLB fl₁ 1 (H₁.pull ρ wρ) with hQd
    set Mf : Fin 3 → HermLB p := ![S, Q, A₀.pull ρ wρ] with hMf
    set Mf' : Fin 3 → HermLB p := ![S, Q, A₁.pull ρ wρ] with hMf'
    set Am : Fin 3 → (Σ a, Fin (r a)) → ℤ := ![Pi.single x 1, Pi.single y 1, n'] with hAm
    have hiso : ∀ j, (comb L (Am j)).Isometric (Mf j) := by
      intro j
      fin_cases j
      · exact (isometric_comb_single L x).trans hS0.symm
      · exact (isometric_comb_single L y).trans hS1.symm
      · exact SwapFlProof.comb_isometric_pullback L M ρ wρ n' (fun z => z = x ∨ z = y) (fun z hz => if_pos hz)
          (fun z hz => hM z (fun e => hz (Or.inl e)) (fun e => hz (Or.inr e)))
    set f : Fin 3 → MvPolynomial (Σ a, Fin (r a)) ℝ := fun j => lin fun z => (Am j z : ℝ) with hf
    set Ψ₃ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ := Ψ ∘ₗ (aeval f : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] _).toLinearMap with hΨ₃
    have hΨ' : IsGeoFun Mf (d₁ + 1) Ψ₃ := by
      refine ⟨fun m => ?_, fun P e he hP => ?_⟩
      · rw [hΨ₃, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow, hf, aeval_lin]
        have h2 := hΨ.1 (fun z => ∑ j, m j * Am j z)
        simp only [Int.cast_sum, Int.cast_mul] at h2
        rw [h2]
        exact ((isometric_comb_comb L Am m).trans (isometric_comb_congr hiso m)).gdeg_eq _
      · rw [hΨ₃, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
        exact hΨ.2 _ e he (by simpa using hP.aeval _ fun j => isHomogeneous_lin _)
    have hA' : (A₁.pull ρ wρ).Isometric ((A₀.pull ρ wρ).shift (fun _ => 1) fun _ => rfl) :=
      isometric_pull_shift A₀ _ _ ρ wρ
    have hcomb : ∀ (m : Fin 3 → ℤ) (c : ℝ), ((m 2 : ℤ) : ℝ) = c →
        (comb Mf' m).Isometric ((comb Mf m).shift (fun _ => c) fun _ => rfl) :=
      fun m c hc => isometric_comb_three_shift S Q _ _ hA' m c hc
    have hΨ'' : IsGeoFun Mf' (d₁ + 1) Ψ₃ :=
      ⟨fun m => (hΨ'.1 m).trans (((hcomb m _ rfl).gdeg_eq _).trans (gdeg_shift_const _ _ _ _)).symm, hΨ'.2⟩
    obtain ⟨Φ, hΦ⟩ := ((hC.arExists k Y p (d₁ + 1) hp).2 (Fin 3) Mf).1
    obtain ⟨Φ', hΦ'⟩ := ((hC.arExists k Y p (d₁ + 1) hp).2 (Fin 3) Mf').1
    have e1 := hS k Y₁ Y q₁ p d₁ hY₁ hp ρ wρ E₁ h₁ H₁ fl₁ hfl₁ A₀ Φ Ψ₃ hΦ hΨ' (n x) (n y)
    have e2 := hS k Y₁ Y q₁ p d₁ hY₁ hp ρ wρ E₁ h₁ H₁ fl₁ hfl₁ A₁ Φ' Ψ₃ hΦ' hΨ'' (n x) (n y)
    have hsh : ∀ u v : ℤ, Φ' (lin ![(u : ℝ), v, 1] ^ (d₁ + 2)) =
        Φ (lin ![(u : ℝ), v, 1] ^ (d₁ + 2)) + (((d₁ + 1 : ℕ) : ℝ) + 1) * 1 * Ψ₃ (lin ![(u : ℝ), v, 1] ^ (d₁ + 1)) := by
      intro u v
      have h1 := hΦ.1 ![u, v, 1]
      have h2 := hΦ'.1 ![u, v, 1]
      rw [cast_triple] at h1 h2
      have h3 := hC.arShift k Y p (d₁ + 1) hp (comb Mf ![u, v, 1]) _ 1 h1
      have h4 := (hcomb ![u, v, 1] 1 (by simp)).symm.isSelfInter hp h3
      rw [h2.unique hp h4, ← cast_triple u v, hΨ'.1 ![u, v, 1]]
    rw [hsh, hsh] at e2
    have e3 : (((d₁ + 1 : ℕ) : ℝ) + 1) * (Ψ₃ (lin ![(n x : ℝ), n y, 1] ^ (d₁ + 1)) +
        Ψ₃ (lin ![(n y : ℝ), n x, 1] ^ (d₁ + 1))) = 0 := by linarith
    have hpos : (((d₁ + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
    have e4 := (mul_eq_zero.1 e3).resolve_left hpos
    have hx0 : n' x = 0 := if_pos (Or.inl rfl)
    have hy0 : n' y = 0 := if_pos (Or.inr rfl)
    have hne : ∀ z, z ≠ x → z ≠ y → n' z = n z := fun z h1 h2 => if_neg (by tauto)
    simp only [hΨ₃, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow, hf, aeval_lin] at e4
    rw [hAm, SwapFlProof.lin_update_two_coords x y hxy n n' hx0 hy0 hne (n x) (n y),
      SwapFlProof.lin_update_two_coords x y hxy n n' hx0 hy0 hne (n y) (n x)] at e4
    convert e4 using 4
    · congr 1
      funext z
      rw [Function.update_eq_self, Function.update_eq_self]
    · congr 1
      funext z
      by_cases h1 : z = x
      · subst h1; simp [Function.update_apply, hxy, Equiv.swap_apply_left]
      · by_cases h2 : z = y
        · subst h2; simp [Function.update_apply, Equiv.swap_apply_right]
        · simp [Function.update_apply, h1, h2, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hz := GlobalTheory.ArInt.Model.eq_zero_of_pow (d₁ + 1)
    (Ψ + Ψ ∘ₗ (rename (Equiv.swap x y) : MvPolynomial (Σ a, Fin (r a)) ℝ →ₐ[ℝ] _).toLinearMap)
    (fun n => by
      rw [LinearMap.add_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        map_pow (rename (Equiv.swap x y)), rename_lin_swap]
      exact key n)
    (fun P e he hP => by
      rw [LinearMap.add_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, hΨ.2 P e he hP,
        hΨ.2 _ e he (hP.rename_isHomogeneous), add_zero])
  intro P
  have := LinearMap.congr_fun hz P
  rw [LinearMap.add_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.zero_apply] at this
  linarith

end GlobalTheory.CovTest.GeoSwap

end
