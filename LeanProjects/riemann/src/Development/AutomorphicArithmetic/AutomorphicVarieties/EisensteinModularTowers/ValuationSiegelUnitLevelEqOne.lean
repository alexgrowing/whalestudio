import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralModularTowerJCompGlTwoPosRat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoInvariantHolomorphicMemAdjoinJInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OverAffineJLineComapSlGalStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplexStatement
import Mathlib

open GlobalTheory.KZ GlobalTheory.Glue

namespace UpperTheory.V.L.SiegelUnitIntegral

open Polynomial
open scoped Matrix MatrixGroups

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem jhol (X : Tower Ω ε) : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero) := by
  obtain ⟨φ, h, d⟩ := X.j_hol
  exact ⟨φ, d, h⟩

private theorem val_one {K : Type} [Field K] (W : ValuationSubring K) {x : K} (h0 : x ≠ 0) (hx : x ∈ W) (hi : x⁻¹ ∈ W) :
    W.valuation x = 1 := by
  have hu : IsUnit (⟨x, hx⟩ : W) :=
    isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, hi⟩, Subtype.ext (by simp [h0])⟩
  exact (W.valuation_eq_one_iff ⟨x, hx⟩).mp hu

private theorem mem_of_int (X : Tower Ω ε) (W : ValuationSubring X.K) (hW : X.OverY W) {x : X.K}
    (h : IsIntegral (Algebra.adjoin Ω {X.jK}) x) : x ∈ W := by
  have hle : ∀ y ∈ Algebra.adjoin Ω {X.jK}, y ∈ W := X.adjoin_le_of_overY W hW
  let φ : Algebra.adjoin Ω {X.jK} →+* W :=
    { toFun := fun a => ⟨a, hle a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hi := IsIntegral.map_of_comp_eq φ (RingHom.id X.K) (by ext; rfl) h
  exact vs_mem_of_isIntegral W hi

private theorem sgC_hol {c : ℕ} {x : Fin 2 → ℚ} (hx : GlobalTheory.Sieg.admitted c x) : DifferentiableOn ℂ (sgC c x) Hs :=
  UpperHalfPlane.mdifferentiable_iff.1 (GlobalTheory.Sieg.mdifferentiable_sg c x hx)

private theorem sgC_ne {c : ℕ} {x : Fin 2 → ℚ} (hx : GlobalTheory.Sieg.admitted c x) (z : ℂ) : sgC c x z ≠ 0 :=
  GlobalTheory.Sieg.sg_ne_zero c x _ hx

private theorem siegel_hol [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {c : ℕ} {x : Fin 2 → ℚ} (hx : GlobalTheory.Sieg.admitted c x) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an (siegel X c x) = (φ : Mero) :=
  ⟨sgC c x, sgC_hol hx, GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε X c x hx⟩

private theorem siegel_inv_hol [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {c : ℕ} {x : Fin 2 → ℚ} (hx : GlobalTheory.Sieg.admitted c x) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an (siegel X c x)⁻¹ = (φ : Mero) := by
  refine ⟨fun z => (sgC c x z)⁻¹, (sgC_hol hx).inv fun z _ => sgC_ne hx z, ?_⟩
  have h1 := GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε X c x hx
  have h0 := GlobalTheory.T.siegelUnitInTower_ne_zero Ω ε X c x hx
  have h2 : ((sgC c x : ℂ → ℂ) : Mero) * (((fun z => (sgC c x z)⁻¹) : ℂ → ℂ) : Mero) = 1 :=
    SiegelModel.germ_eq_of_eqOn (φ := fun z => sgC c x z * (sgC c x z)⁻¹) (ψ := fun _ => 1)
      fun z _ => mul_inv_cancel₀ (sgC_ne hx z)
  have h3 : X.an (siegel X c x)⁻¹ * X.an (siegel X c x) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ h0, map_one]
  calc X.an (siegel X c x)⁻¹ = X.an (siegel X c x)⁻¹ * (((sgC c x : ℂ → ℂ) : Mero) * (((fun z => (sgC c x z)⁻¹) : ℂ → ℂ) : Mero)) := by
        rw [h2, mul_one]
    _ = (((fun z => (sgC c x z)⁻¹) : ℂ → ℂ) : Mero) := by
        rw [← mul_assoc, ← h1, h3, one_mul]

private theorem int_of_hol [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (f : X.K)
    (hf : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an f = (φ : Mero)) :
    IsIntegral (Algebra.adjoin Ω {X.jK}) f := by
  classical
  have hinj : Function.Injective ε := ε.injective
  obtain ⟨φ, hφ, hfφ⟩ := hf
  obtain ⟨M, hM, hlev⟩ := X.level f
  haveI : NeZero M := ⟨hM.ne'⟩
  set S : Set X.K := Set.range (fun γ : SL(2, ℤ) => X.sl (ofSL γ) f) with hSdef
  have hfac : ∀ γ γ' : SL(2, ℤ), Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ' →
      X.sl (ofSL γ) f = X.sl (ofSL γ') f := by
    intro γ γ' h
    have hδ : γ' * γ⁻¹ ∈ CongruenceSubgroup.Gamma M := by
      rw [CongruenceSubgroup.Gamma_mem', map_mul, map_inv, h, mul_inv_cancel]
    obtain ⟨δ, hδ', rfl⟩ : ∃ δ, δ ∈ CongruenceSubgroup.Gamma M ∧ γ' = δ * γ :=
      ⟨γ' * γ⁻¹, hδ, by group⟩
    rw [map_mul, X.sl_mul, hlev δ hδ']
  have hSfin : S.Finite := by
    let red := Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod M))
    let g : SL(2, ZMod M) → X.K := fun u => if h : ∃ γ, red γ = u then X.sl (ofSL h.choose) f else 0
    refine (Set.finite_range g).subset ?_
    rintro _ ⟨γ, rfl⟩
    refine ⟨red γ, ?_⟩
    have h : ∃ γ', red γ' = red γ := ⟨γ, rfl⟩
    simp only [g, dif_pos h]
    exact hfac _ _ h.choose_spec
  have hhol : ∀ h ∈ S, h ∈ JInt.holR X := by
    rintro _ ⟨γ, rfl⟩
    change ∃ ψ : ℂ → ℂ, DifferentiableOn ℂ ψ Hs ∧ X.an (X.sl (ofSL γ) f) = (ψ : Mero)
    refine ⟨fun z => φ (mob (ofSL γ) z), ?_, X.an_sl _ f φ hfφ⟩
    exact hφ.comp (JInt.mob_diff _) (fun z hz => JInt.mob_im _ hz)
  have hmapS : ∀ γ : SL(2, ℤ), ∀ h ∈ S, X.sl (ofSL γ) h ∈ S := by
    rintro γ _ ⟨γ', rfl⟩
    refine ⟨γ' * γ, ?_⟩
    show X.sl (ofSL (γ' * γ)) f = _
    rw [map_mul, X.sl_mul]
  set Fs := hSfin.toFinset with hFs
  set P : Polynomial X.K := ∏ h ∈ Fs, (Polynomial.X - Polynomial.C h) with hP
  have hcinv : ∀ γ : SL(2, ℤ), ∀ n, X.sl (ofSL γ) (P.coeff n) = P.coeff n := by
    intro γ n
    have hmap : P.map ((X.sl (ofSL γ) : X.K →+* X.K)) = P := by
      rw [hP, Polynomial.map_prod]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      refine Finset.prod_nbij' (i := fun h => X.sl (ofSL γ) h) (j := fun h => X.sl (ofSL γ⁻¹) h)
        ?_ ?_ ?_ ?_ ?_
      · intro h hh
        rw [Set.Finite.mem_toFinset] at hh ⊢
        exact hmapS γ h hh
      · intro h hh
        rw [Set.Finite.mem_toFinset] at hh ⊢
        exact hmapS γ⁻¹ h hh
      · intro h _
        show X.sl (ofSL γ⁻¹) (X.sl (ofSL γ) h) = h
        rw [← X.sl_mul, ← map_mul, mul_inv_cancel, map_one, X.sl_one]
      · intro h _
        show X.sl (ofSL γ) (X.sl (ofSL γ⁻¹) h) = h
        rw [← X.sl_mul, ← map_mul, inv_mul_cancel, map_one, X.sl_one]
      · intro h _
        rfl
    have h2 := congrArg (fun p => Polynomial.coeff p n) hmap
    simpa [Polynomial.coeff_map] using h2
  set Q : Polynomial (JInt.holR X) :=
    ∏ h ∈ Fs.attach, (Polynomial.X - Polynomial.C (⟨h.1, hhol h.1 (hSfin.mem_toFinset.mp h.2)⟩ : JInt.holR X))
    with hQ
  have hPQ : P = Q.map (JInt.holR X).subtype := by
    rw [hQ, hP, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rw [← Finset.prod_attach Fs]
    rfl
  have hchol : ∀ n, ∃ ψ : ℂ → ℂ, DifferentiableOn ℂ ψ Hs ∧ X.an (P.coeff n) = (ψ : Mero) := by
    intro n
    rw [hPQ, Polynomial.coeff_map]
    exact (Q.coeff n).2
  have hcoef : ∀ n, P.coeff n ∈ Algebra.adjoin Ω {X.jK} := fun n =>
    GlobalTheory.T.slTwo_invariant_holomorphic_mem_adjoin_jInvariant ε X hinj (jhol X) _ (fun γ => hcinv γ n) (hchol n)
  have hlift : P ∈ Polynomial.lifts (algebraMap (Algebra.adjoin Ω {X.jK}) X.K) :=
    (Polynomial.lifts_iff_coeff_lifts P).mpr fun n => ⟨⟨P.coeff n, hcoef n⟩, rfl⟩
  have hmon : P.Monic := Polynomial.monic_prod_of_monic _ _ (fun h _ => Polynomial.monic_X_sub_C h)
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmon
  have hfS : f ∈ Fs := by
    rw [Set.Finite.mem_toFinset]
    exact ⟨1, by simp only [map_one, X.sl_one]⟩
  refine ⟨q, hqm, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hq, hP, Polynomial.eval_prod]
  exact Finset.prod_eq_zero hfS (by simp)

private theorem admissible_index_siegel {c D : ℕ} (hc : 1 < c) (h6 : Nat.Coprime c 6) (hcD : Nat.Coprime c D) (hD : 0 < D) {a b : ℤ}
    (hab : ¬ ((D : ℤ) ∣ a ∧ (D : ℤ) ∣ b)) : GlobalTheory.Sieg.admitted c ![(a : ℚ) / D, (b : ℚ) / D] := by
  refine ⟨hc, h6, ?_⟩
  rintro ⟨⟨n0, hn0⟩, ⟨n1, hn1⟩⟩
  apply hab
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hcop : IsCoprime (D : ℤ) (c : ℤ) := Nat.isCoprime_iff_coprime.mpr hcD.symm
  have key : ∀ (a n : ℤ), (n : ℚ) = c * ((a : ℚ) / D) → (D : ℤ) ∣ a := by
    intro a n hn
    have h1 : (n : ℚ) * D = c * a := by rw [hn]; field_simp
    have h2 : n * (D : ℤ) = c * a := by exact_mod_cast h1
    have h3 : (D : ℤ) ∣ c * a := ⟨n, by rw [← h2]; ring⟩
    exact hcop.dvd_of_dvd_mul_left h3
  exact ⟨key a n0 (by simpa using hn0), key b n1 (by simpa using hn1)⟩

private theorem val_sl [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {c : ℕ} {x : Fin 2 → ℚ} (hx : GlobalTheory.Sieg.admitted c x) (g : GQ)
    (W : ValuationSubring X.K) (hW : X.OverY W) : W.valuation (X.sl g (siegel X c x)) = 1 := by
  have hY := (GlobalTheory.T.overAffineJLine_comap_sl_gal ε X ε.injective (jhol X) W hW).1 g
  have h1 := mem_of_int X _ hY (int_of_hol X _ (siegel_hol X hx))
  have h2 := mem_of_int X _ hY (int_of_hol X _ (siegel_inv_hol X hx))
  rw [ValuationSubring.mem_comap] at h1 h2
  refine val_one W ((_root_.map_ne_zero _).2 (GlobalTheory.T.siegelUnitInTower_ne_zero Ω ε X c x hx)) h1 ?_
  rw [← map_inv₀]
  exact h2

end UpperTheory.V.L.SiegelUnitIntegral

theorem UpperTheory.valuation_siegelUnitLevel_eq_one :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (c N D : ℕ) (a : ℤ × ℤ), 1 < c → Nat.Coprime c 6 → Nat.Coprime c D → 0 < N → 0 < D → ¬ ((D : ℤ) ∣ a.1 ∧ (D : ℤ) ∣ a.2) → ∀ W : ValuationSubring X.K, X.OverY W → W.valuation (sgN X c N D a) = 1 := by
  intro Ω _ _ _ ε X c N D a hc h6 hcD _ hD ha W hW
  exact UpperTheory.V.L.SiegelUnitIntegral.val_sl X (UpperTheory.V.L.SiegelUnitIntegral.admissible_index_siegel hc h6 hcD hD ha) _ W hW
