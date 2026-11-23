import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealEmbeddingOrderingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealEmbeddingsLinearlyIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalAppellHumbertRealMultStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingPairingOnLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescaledUniformizationStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusFormPf

theorem embOfCM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (e₀ : Fin (Module.finrank ℚ (FR E)) ≃ I),
    ∃ e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ), ∀ j (x : FR E), (e j x : ℂ) = φ (e₀ j) (x : E) := GlobalTheory.T.exists_real_embedding_ordering

theorem realEmb_indep : ∀ (F : Type) [Field F] [NumberField F] (a : (F →+* ℝ) → ℝ),
    (∀ x : 𝓞 F, ∑ τ, a τ * τ (x : F) = 0) → a = 0 := GlobalTheory.T.real_embeddings_linearly_independent

theorem riemannForm_of_unif : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
    (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)),
    (∀ (a : 𝓞 F) w, u.ex (fun j ↦ (e j (a : F) : ℂ) * w j) = u.ex w ≫ X.rm.act a) →
    ∀ (h : Fin (Module.finrank ℚ F) → ℝ) (χ : u.Λ → ℂ), u.IsAH (Matrix.diagonal fun j ↦ (h j : ℂ)) χ →
    ∃ P : u.Λ → u.Λ → F, (∀ l l' : u.Λ, P l l' = -P l' l) ∧ (∀ l₁ l₂ l' : u.Λ, P (l₁ + l₂) l' = P l₁ l' + P l₂ l') ∧
      (∀ (a : 𝓞 F) (l l' al : u.Λ), (al : Fin (Module.finrank ℚ F) → ℂ) = (fun j ↦ (e j (a : F) : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) →
        P al l' = (a : F) * P l l') ∧
      (∀ l l' : u.Λ, (∑ j, (h j : ℂ) * ((l : Fin (Module.finrank ℚ F) → ℂ) j * starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im =
        2 * ((Algebra.trace ℚ F ((c : F) * P l l') : ℚ) : ℝ)) ∧
      (∀ l l' : u.Λ, P l l' ∈ dualLat 𝔠) ∧
      (∀ t ∈ dualLat 𝔠, t ∈ Submodule.span (𝓞 F) {t | ∃ l l' : u.Λ, t = P l l'}) := GlobalTheory.T.diagonal_appell_humbert_real_mult

theorem steinitz_sympl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ (𝔞 𝔟 : FracId (FR E)) (P : E → E → FR E),
    (∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, P x x' = -P x' x) →
    (∀ x₁ ∈ lattice c y, ∀ x₂ ∈ lattice c y, ∀ x' ∈ lattice c y, P (x₁ + x₂) x' = P x₁ x' + P x₂ x') →
    (∀ (a : 𝓞 (FR E)), ∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, P (((a : FR E) : E) * x) x' = (a : FR E) * P x x') →
    (∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, P x x' ∈ dualLat (𝔞 * 𝔟⁻¹)) →
    (∀ t ∈ dualLat (𝔞 * 𝔟⁻¹), t ∈ Submodule.span (𝓞 (FR E)) {t | ∃ x ∈ lattice c y, ∃ x' ∈ lattice c y, t = P x x'}) →
    ∃ ω₁ ω₂ : E, (∀ x, x ∈ lattice c y ↔ ∃ m ∈ dualLat 𝔞, ∃ β ∈ 𝔟.elt, x = (m : E) * ω₁ + (β : E) * ω₂) ∧
      ∀ m ∈ dualLat 𝔞, ∀ β ∈ 𝔟.elt, ∀ m' ∈ dualLat 𝔞, ∀ β' ∈ 𝔟.elt,
        P ((m : E) * ω₁ + (β : E) * ω₂) ((m' : E) * ω₁ + (β' : E) * ω₂) = β * m' - m * β' := GlobalTheory.T.alternating_pairing_on_lattice

theorem holUnif_rescale : ∀ (A : Over (Sp ℂ)) [GrpObj A] (Lb : LB A.left) (g : ℕ) (u : HolUnif A Lb g) (lam : Fin g → ℂ),
    (∀ j, lam j ≠ 0) → ∃ u' : HolUnif A Lb g, (∀ w, u'.ex w = u.ex (fun j ↦ lam j * w j)) ∧
      (∀ (d : Fin g → ℝ) χ, u.IsAH (Matrix.diagonal fun j ↦ (d j : ℂ)) χ →
        ∃ χ', u'.IsAH (Matrix.diagonal fun j ↦ ((d j * ‖lam j‖ ^ 2 : ℝ) : ℂ)) χ') ∧
      (∀ W v, u'.IsDiff W v ↔ u.IsDiff (fun j ↦ lam j * W j) v) := GlobalTheory.T.rescaled_uniformization

end GlobalTheory.TorusFormPf

namespace GlobalTheory.TorusFormPf

theorem lattice_add {E : Type} [Field E] [NumberField E] {c : Ideal (OF E)} {y : (Af E)ˣ} {x x' : E}
    (hx : x ∈ lattice c y) (hx' : x' ∈ lattice c y) : x + x' ∈ lattice c y := by
  simp only [lattice, Set.mem_setOf_eq, map_add, add_mul] at *
  exact Subring.add_mem _ hx hx'

theorem lattice_smul {E : Type} [Field E] [NumberField E] {c : Ideal (OF E)} {y : (Af E)ˣ} {x : E}
    (a : 𝓞 (FR E)) (hx : x ∈ lattice c y) : ((a : FR E) : E) * x ∈ lattice c y := by
  have := mul_mem_lattice (algebraMap_mem_orderC c a) hx
  convert this using 2
  first | rfl | simp [IsScalarTower.algebraMap_apply (OF E) (FR E) E] | exact (IsScalarTower.algebraMap_apply (OF E) (FR E) E a).symm

theorem torusForm : TorusForm := by
  intro E _ _ _ I _ 𝔞 𝔟 φ c y hCM hc z hz X U
  obtain ⟨e, he⟩ := embOfCM E I φ hCM U.e
  have hreal : ∀ j (x : FR E), starRingEnd ℂ (φ (U.e j) (x : E)) = φ (U.e j) (x : E) := by
    intro j x; rw [← he]; exact Complex.conj_ofReal _
  set D : E → Fin (Module.finrank ℚ (FR E)) → ℂ := fun x j ↦ defCoord φ z x (U.e j) with hD
  have hDadd : ∀ x x', D (x + x') = D x + D x' := by
    intro x x'; funext j; simp only [hD, defCoord, map_add, Pi.add_apply]; ring
  have hDsmul : ∀ (a : FR E) x, D ((a : E) * x) = fun j ↦ (e j a : ℂ) * D x j := by
    intro a x; funext j; simp only [hD, defCoord, map_mul]; rw [hreal j a, ← he]; ring
  have hact : ∀ (a : 𝓞 (FR E)) w, U.u.ex (fun j ↦ (e j (a : FR E) : ℂ) * w j) = U.u.ex w ≫ X.rm.act a := by
    intro a w; simpa only [he] using U.act a w
  obtain ⟨χ, hAH⟩ := U.ah
  obtain ⟨P, hPalt, hPadd, hPsmul, hPtr, hPmem, hPspan⟩ := riemannForm_of_unif (FR E) (𝔞 * 𝔟⁻¹) X U.c U.pos U.u e hact
    (fun j ↦ U.h (U.e j)) χ hAH
  have hDmem : ∀ x ∈ lattice c y, D x ∈ U.u.Λ := fun x hx ↦ (U.lat _).2 ⟨x, hx, rfl⟩
  classical
  let PL : E → E → FR E := fun x x' ↦
    if hx : x ∈ lattice c y ∧ x' ∈ lattice c y then P ⟨D x, hDmem x hx.1⟩ ⟨D x', hDmem x' hx.2⟩ else 0
  have hPL : ∀ x (hx : x ∈ lattice c y) x' (hx' : x' ∈ lattice c y),
      PL x x' = P ⟨D x, hDmem x hx⟩ ⟨D x', hDmem x' hx'⟩ := by
    intro x hx x' hx'; simp only [PL, dif_pos (And.intro hx hx')]
  obtain ⟨ω₁, ω₂, hL, hPω⟩ := steinitz_sympl E c y hc 𝔞 𝔟 PL
    (by intro x hx x' hx'; rw [hPL x hx x' hx', hPL x' hx' x hx]; exact hPalt _ _)
    (by
      intro x₁ h₁ x₂ h₂ x' h'
      rw [hPL _ (lattice_add h₁ h₂) x' h', hPL x₁ h₁ x' h', hPL x₂ h₂ x' h', ← hPadd]
      congr 1; exact Subtype.ext (hDadd x₁ x₂))
    (by
      intro a x hx x' hx'
      rw [hPL _ (lattice_smul a hx) x' hx', hPL x hx x' hx']
      exact hPsmul a _ _ _ (hDsmul (a : FR E) x))
    (by intro x hx x' hx'; rw [hPL x hx x' hx']; exact hPmem _ _)
    (by
      intro t ht
      have := hPspan t ht
      refine Submodule.span_mono ?_ this
      rintro s ⟨l, l', rfl⟩
      obtain ⟨x, hx, hxl⟩ := (U.lat l).1 l.2
      obtain ⟨x', hx', hxl'⟩ := (U.lat l').1 l'.2
      refine ⟨x, hx, x', hx', ?_⟩
      rw [hPL x hx x' hx']
      congr 1 <;> apply Subtype.ext <;> assumption)
  set A : Fin (Module.finrank ℚ (FR E)) → ℂ := D ω₁ with hA
  set B : Fin (Module.finrank ℚ (FR E)) → ℂ := D ω₂ with hB
  have hDlin : ∀ m β : FR E, D ((m : E) * ω₁ + (β : E) * ω₂) = fun j ↦ (e j m : ℂ) * A j + (e j β : ℂ) * B j := by
    intro m β; rw [hDadd, hDsmul, hDsmul]; rfl
  have hmemL : ∀ m ∈ dualLat 𝔞, ∀ β ∈ 𝔟.elt, (m : E) * ω₁ + (β : E) * ω₂ ∈ lattice c y :=
    fun m hm β hβ ↦ (hL _).2 ⟨m, hm, β, hβ, rfl⟩
  obtain ⟨β₀, hβ₀, hβ₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (fun h ↦ 𝔟.ne_zero (FractionalIdeal.coeToSubmodule_eq_bot.1 h))
  have hdual0 : dualLat 𝔞 ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ 𝔞.ne_zero
  obtain ⟨m₀, hm₀, hm₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (fun h ↦ hdual0 (FractionalIdeal.coeToSubmodule_eq_bot.1 h))
  have h0a : (0 : FR E) ∈ dualLat 𝔞 := (dualLat 𝔞 : Submodule (𝓞 (FR E)) (FR E)).zero_mem
  have h0b : (0 : FR E) ∈ 𝔟.elt := 𝔟.elt.zero_mem
  have hkey : ∀ x : 𝓞 (FR E), ∑ j, e j (x : FR E) * ((e j β₀ * e j m₀) *
      (U.h (U.e j) * (B j * starRingEnd ℂ (A j)).im - 2 * e j (U.c : FR E))) = 0 := by
    intro x
    have hxβ : (x : FR E) * β₀ ∈ 𝔟.elt := by
      have := 𝔟.elt.smul_mem x hβ₀; rwa [Algebra.smul_def] at this
    have m1 := hmemL 0 h0a _ hxβ
    have m2 := hmemL m₀ hm₀ 0 h0b
    have htr := hPtr ⟨_, hDmem _ m1⟩ ⟨_, hDmem _ m2⟩
    rw [← hPL _ m1 _ m2, hPω 0 h0a _ hxβ m₀ hm₀ 0 h0b, GlobalTheory.trace_eq_sum_realEmbeddings, ← e.sum_comp] at htr
    simp only [hDlin, Complex.im_sum] at htr
    have hl : ∀ j, ((U.h (U.e j) : ℂ) * ((((e j 0 : ℝ) : ℂ) * A j + ((e j ((x : FR E) * β₀) : ℝ) : ℂ) * B j) *
        starRingEnd ℂ (((e j m₀ : ℝ) : ℂ) * A j + ((e j 0 : ℝ) : ℂ) * B j))).im =
        e j (x : FR E) * (e j β₀ * e j m₀ * (U.h (U.e j) * (B j * starRingEnd ℂ (A j)).im)) := by
      intro j
      have : (U.h (U.e j) : ℂ) * ((((e j 0 : ℝ) : ℂ) * A j + ((e j ((x : FR E) * β₀) : ℝ) : ℂ) * B j) *
          starRingEnd ℂ (((e j m₀ : ℝ) : ℂ) * A j + ((e j 0 : ℝ) : ℂ) * B j)) =
          ((U.h (U.e j) * e j (x : FR E) * e j β₀ * e j m₀ : ℝ) : ℂ) * (B j * starRingEnd ℂ (A j)) := by
        simp only [map_zero, map_mul, map_add, Complex.ofReal_zero, Complex.conj_ofReal, zero_mul, zero_add, add_zero]
        push_cast; ring
      rw [this, Complex.im_ofReal_mul]; ring
    simp only [hl] at htr
    rw [← sub_eq_zero, Finset.mul_sum, ← Finset.sum_sub_distrib] at htr
    rw [← htr]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [map_mul, map_sub, map_zero, mul_zero, sub_zero]
    ring
  have hk : ∀ j, U.h (U.e j) * (B j * starRingEnd ℂ (A j)).im = 2 * e j (U.c : FR E) := by
    have hz := realEmb_indep (FR E) (fun σ ↦ (e (e.symm σ) β₀ * e (e.symm σ) m₀) *
      (U.h (U.e (e.symm σ)) * (B (e.symm σ) * starRingEnd ℂ (A (e.symm σ))).im - 2 * e (e.symm σ) (U.c : FR E))) (by
        intro x
        rw [← e.sum_comp]
        simp only [Equiv.symm_apply_apply]
        rw [← hkey x]
        exact Finset.sum_congr rfl fun j _ ↦ by ring)
    intro j
    have := congrFun hz (e j)
    simp only [Equiv.symm_apply_apply, Pi.zero_apply] at this
    have hne : e j β₀ * e j m₀ ≠ 0 := mul_ne_zero ((map_ne_zero _).2 hβ₀0) ((map_ne_zero _).2 hm₀0)
    have := (mul_eq_zero.1 this).resolve_left hne
    linarith
  have hhpos : ∀ j, 0 < U.h (U.e j) := by
    intro j
    have hne : (Pi.single j (1 : ℂ) : Fin (Module.finrank ℚ (FR E)) → ℂ) ≠ 0 := fun h ↦ by simpa using congrFun h j
    have := hAH.2.1 _ hne
    simpa [Matrix.mulVec_diagonal, dotProduct, Pi.single_apply] using this
  have hIm : ∀ j, 0 < (B j * starRingEnd ℂ (A j)).im := by
    intro j
    have hc := U.pos (e j)
    have : 0 < U.h (U.e j) * (B j * starRingEnd ℂ (A j)).im := by rw [hk j]; linarith
    exact pos_of_mul_pos_right this (le_of_lt (hhpos j))
  have hA0 : ∀ j, A j ≠ 0 := by
    intro j h; have := hIm j; rw [h] at this; simp at this
  set τ : (FR E →+* ℝ) → ℂ := fun σ ↦ B (e.symm σ) / A (e.symm σ) with hτdef
  set lam : Fin (Module.finrank ℚ (FR E)) → ℂ := fun j ↦ A j / (2 * Real.pi * Complex.I) with hlamdef
  have hτ : ∀ j, τ (e j) = B j / A j := by intro j; simp [hτdef]
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hlam : ∀ j, lam j ≠ 0 := fun j ↦ div_ne_zero (hA0 j) h2pi
  have hτim : ∀ j, (τ (e j)).im = (B j * starRingEnd ℂ (A j)).im / Complex.normSq (A j) := by
    intro j; rw [hτ, Complex.div_im]; simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
  obtain ⟨u', hex, hAH', hdiff⟩ := holUnif_rescale X.A (X.diag U.c) _ U.u lam hlam
  have hform : ∀ m β : FR E, (fun j ↦ lam j * (2 * Real.pi * Complex.I * ((e j m : ℂ) + (e j β : ℂ) * τ (e j)))) =
      D ((m : E) * ω₁ + (β : E) * ω₂) := by
    intro m β; rw [hDlin]; funext j; rw [hτ]; simp only [hlamdef]; have hAj := hA0 j; field_simp; try ring
  have hlat : ∀ w, w ∈ U.u.Λ ↔ ∃ m ∈ dualLat 𝔞, ∃ β ∈ 𝔟.elt,
      w = fun j ↦ lam j * (2 * Real.pi * Complex.I * ((e j m : ℂ) + (e j β : ℂ) * τ (e j))) := by
    intro w
    rw [U.lat]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨m, hm, β, hβ, rfl⟩ := (hL x).1 hx
      exact ⟨m, hm, β, hβ, (hform m β).symm⟩
    · rintro ⟨m, hm, β, hβ, rfl⟩
      exact ⟨_, hmemL m hm β hβ, hform m β⟩
  refine ⟨e, τ, lam, he, fun σ ↦ ?_, hlam, hlat, ?_⟩
  · have := hτim (e.symm σ)
    simp only [Equiv.apply_symm_apply] at this
    rw [this]
    exact div_pos (hIm _) (Complex.normSq_pos.2 (hA0 _))
  · intro δ hδ
    refine ⟨U.c, u', U.pos, ?_, ?_, ?_, ?_⟩
    · intro w
      have hk' : w ∈ u'.Λ ↔ (fun j ↦ lam j * w j) ∈ U.u.Λ := by rw [← u'.ker, ← U.u.ker, hex]
      rw [hk', hlat]
      refine exists_congr fun m ↦ and_congr_right fun _ ↦ exists_congr fun β ↦ and_congr_right fun _ ↦ ?_
      constructor
      · intro h; funext j; exact mul_left_cancel₀ (hlam j) (congrFun h j)
      · intro h; rw [h]
    · intro a w
      rw [hex, hex, ← hact]
      congr 1; funext j; ring
    · obtain ⟨χ', h'⟩ := hAH' (fun j ↦ U.h (U.e j)) χ hAH
      refine ⟨χ', ?_⟩
      have hm : (fun i ↦ (((2 * e i (U.c : FR E) / (4 * Real.pi ^ 2 * (τ (e i)).im)) : ℝ) : ℂ)) =
          fun j ↦ ((U.h (U.e j) * ‖lam j‖ ^ 2 : ℝ) : ℂ) := by
        funext j
        congr 1
        have hn : ‖lam j‖ ^ 2 = Complex.normSq (A j) / (4 * Real.pi ^ 2) := by
          rw [hlamdef, norm_div, div_pow, Complex.sq_norm]
          congr 1
          simp [Complex.norm_mul, abs_of_pos Real.pi_pos]; ring
        rw [hn, hτim, ← hk j]
        have := hIm j
        have := Complex.normSq_pos.2 (hA0 j)
        field_simp
      rw [hm]; exact h'
    · intro v W hW
      have hW' : ∀ i, U.u.IsDiff (fun j ↦ lam j * W i j) (v i).hom := fun i ↦ (hdiff _ _).1 (hW i)
      rw [hδ v (Matrix.of fun i j ↦ lam j * W i j) hW']
      have hdet : (Matrix.of fun i j ↦ lam j * W i j).det = W.det * ∏ j, lam j := by
        have : (Matrix.of fun i j ↦ lam j * W i j) = W * Matrix.diagonal lam := by
          ext i j; simp [Matrix.mul_diagonal, mul_comm]
        rw [this, Matrix.det_mul, Matrix.det_diagonal]
      rw [hdet]
      have hprod : ∏ j, lam j ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ ↦ hlam j
      have hΩ : (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) = ((Real.sqrt |(discr (FR E) : ℝ)| *
          (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 (FR E))⁰ (FR E)) : ℝ) : ℝ) : ℂ) := by
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm, Real.sqrt_eq_rpow]
      rw [hΩ]; field_simp

end GlobalTheory.TorusFormPf
