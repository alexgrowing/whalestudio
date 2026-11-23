import Mathlib
import Development.AutomorphicArithmetic.DivisorFrames.ProductFormulaHeight
import Development.AutomorphicArithmetic.DivisorFrames.AlgebraicPointsDegreeSum
import Development.AutomorphicArithmetic.DivisorFrames.PointFieldExtensionLift
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad

private theorem embedding_extends_algebraicClosure {K Ω : Type} [Field K] [NumberField K] [Field Ω] [IsAlgClosed Ω] (ι : K →+* Qb)
    (θ : K →+* Ω) : ∃ θ' : Qb →+* Ω, θ'.comp ι = θ := by
  letI : Algebra K Qb := ι.toAlgebra
  letI : Algebra K Ω := θ.toAlgebra
  haveI : IsScalarTower ℚ K Qb := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have halg : Algebra.IsAlgebraic ℚ Qb := algebraicClosure.isAlgebraic ℚ ℂ
  haveI : Algebra.IsAlgebraic K Qb := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let j : Qb →ₐ[K] Ω := IsAlgClosed.lift
  exact ⟨j.toRingHom, j.comp_algebraMap⟩

private theorem sum_embeddings_fibrewise {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] (φ : F →+* K)
    (G : (K →+* ℂ) → ℝ) :
    ∑ σ : F →+* ℂ, ∑ᶠ (θ : K →+* ℂ) (_ : θ.comp φ = σ), G θ = ∑ θ, G θ := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun θ : K →+* ℂ => θ.comp φ)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [finsum_eq_sum_of_fintype, Finset.sum_filter]
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [finsum_eq_if]

private theorem embedding_sum_relative_degree {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (ρ : K →+* L) :
    ∃ e : ℕ, e * Module.finrank ℚ K = Module.finrank ℚ L ∧
      ∀ G : (K →+* ℂ) → ℝ, ∑ θ : L →+* ℂ, G (θ.comp ρ) = e * ∑ σ, G σ := by
  classical
  letI : Algebra K L := ρ.toAlgebra
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  refine ⟨Module.finrank K L, by rw [mul_comm, Module.finrank_mul_finrank], fun G => ?_⟩
  rw [← Finset.sum_fiberwise Finset.univ (fun θ : L →+* ℂ => θ.comp ρ), Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => G σ) fun θ hθ => congrArg G (Finset.mem_filter.1 hθ).2,
    Finset.sum_const, nsmul_eq_mul]
  congr 2
  letI : Algebra K ℂ := σ.toAlgebra
  have e : {θ : L →+* ℂ // θ.comp ρ = σ} ≃ (L →ₐ[K] ℂ) :=
    ⟨fun θ => ⟨θ.1, fun a => RingHom.congr_fun θ.2 a⟩, fun θ => ⟨θ.toRingHom, θ.comp_algebraMap⟩,
      fun _ => rfl, fun _ => rfl⟩
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Nat.card_congr e, Nat.card_eq_fintype_card, AlgHom.card]

private theorem finsum_sub_smul {α : Type} [Finite α] (P : α → Prop) (a b : α → ℝ) (t : ℝ) :
    ∑ᶠ (x : α) (_ : P x), (a x - t * b x) = ∑ᶠ (x : α) (_ : P x), a x - t * ∑ᶠ (x : α) (_ : P x), b x := by
  classical
  have := Fintype.ofFinite α
  simp only [finsum_eq_sum_of_fintype (α := α), finsum_eq_if, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

theorem UpperTheory.height_log_norm_formula :
    ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] (C : CxSt F) (Y : Var F) (A : Adl C Y) (φ : F →+* Qb) (p : Sp Qb ⟶ Y.X) (ι : K →+* Qb) (β : Qb) (c : K) (t : ℝ) (g : (K →+* ℂ) → ℝ), A.n = 1 → A.ci = 0 → p ≫ Y.str = spMap φ → β ≠ 0 → c ≠ 0 → (∀ (θ : Qb →+* ℂ) (σ : F →+* ℂ) (z : Pts Y σ), z.1 = spMap θ ≫ p → Real.log (C.pn Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D (below p))⁻¹ : Y.Fnˣ)) z) / 2 = Real.log ‖θ β‖ + g (θ.comp ι)) → (∀ (v : HeightOneSpectrum (𝓞 F)) (ε : GlobalTheory.TrueGeo.Ext v) (θ : Qb →+* AlgebraicClosure F) (z : AlgPt Y), z.1 = spMap θ ≫ p → A.lg v ε z = Real.log (ε.w (θ β)) - t * Real.log (ε.w (θ (ι c)))) → A.ht (below p) = (-(t * ∑ σ : K →+* ℂ, Real.log ‖σ c‖) - ∑ σ : K →+* ℂ, g σ) / (Module.finrank ℚ K : ℝ) := by
  intro F K _ _ _ _ C Y A φ p ι β c t g hn hci hp hβ hc hinf hfin
  obtain ⟨K', _, _, ι', φ', ρ, b, q, hφ, hρ, hb, hq, hqs⟩ := UpperTheory.point_field_extension_lift F K Y φ p hp ι β
  have hpq : below p = below q := by
    rw [← hq]
    have hsub : Subsingleton (Sp K') := inferInstanceAs (Subsingleton (PrimeSpectrum K'))
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg q (Subsingleton.elim _ _))
  have hlift {Ω : Type} [Field Ω] (θ' : Qb →+* Ω) : spMap (θ'.comp ι') ≫ q = spMap θ' ≫ p := by
    rw [← hq, ← Category.assoc]
    exact congrArg (· ≫ q) (Spec.map_comp (CommRingCat.ofHom ι') (CommRingCat.ofHom θ'))
  obtain ⟨d, hd0, hd, hcount⟩ := UpperTheory.algebraic_points_degree_sum F K' Y φ' q hqs
  obtain ⟨e, he, hsum⟩ := embedding_sum_relative_degree ρ
  have hb0 : b ≠ 0 := by rintro rfl; exact hβ (hb.symm.trans (map_zero _))
  have hc0 : ρ c ≠ 0 := (map_ne_zero ρ).2 hc
  let ε : ∀ v : HeightOneSpectrum (𝓞 F), GlobalTheory.TrueGeo.Ext v := fun v => (GlobalTheory.TrueGeo.Ext.instNonempty v).some
  obtain ⟨fb, pb⟩ := UpperTheory.product_formula_height F K' φ' ε b hb0
  obtain ⟨fc, pc⟩ := UpperTheory.product_formula_height F K' φ' ε (ρ c) hc0
  have h1 : (d : ℝ) * ∑ σ : F →+* ℂ, ∑ᶠ (z : Pts Y σ) (_ : below z.1 = below p),
      (Real.log (C.pn Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D (below p))⁻¹ : Y.Fnˣ)) z) / 2 -
        (A.n : ℕ) * A.ci (InfinitePlace.mk σ)) = ∑ θ : K' →+* ℂ, Real.log ‖θ b‖ + e * ∑ σ, g σ := by
    rw [← hsum g, ← Finset.sum_add_distrib, ← sum_embeddings_fibrewise φ', Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have := hcount ℂ σ (fun z : Pts Y σ => Real.log (C.pn Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D (below p))⁻¹ : Y.Fnˣ)) z) / 2 -
        (A.n : ℕ) * A.ci (InfinitePlace.mk σ)) (fun θ => Real.log ‖θ b‖ + g (θ.comp ρ)) (fun θ z _ hz => by
      obtain ⟨θ', rfl⟩ := embedding_extends_algebraicClosure ι' θ
      have h := hinf θ' σ z (hz.trans (hlift θ'))
      rw [← hb, ← hρ] at h
      simp only [hci, Pi.zero_apply, mul_zero, sub_zero]
      exact h)
    rw [← hpq] at this
    exact this
  have h2 : (d : ℝ) * ∑ᶠ v : HeightOneSpectrum (𝓞 F), ∑ᶠ (y : AlgPt Y) (_ : below y.1 = below p), A.lg v (ε v) y =
      -∑ θ : K' →+* ℂ, Real.log ‖θ b‖ + t * (e * ∑ σ : K →+* ℂ, Real.log ‖σ c‖) := by
    have hv (v : HeightOneSpectrum (𝓞 F)) :
        (d : ℝ) * ∑ᶠ (y : AlgPt Y) (_ : below y.1 = below p), A.lg v (ε v) y =
          ∑ᶠ (θ : K' →+* AlgebraicClosure F) (_ : θ.comp φ' = algebraMap F (AlgebraicClosure F)),
            Real.log ((ε v).w (θ b)) -
          t * ∑ᶠ (θ : K' →+* AlgebraicClosure F) (_ : θ.comp φ' = algebraMap F (AlgebraicClosure F)),
            Real.log ((ε v).w (θ (ρ c))) := by
      rw [← finsum_sub_smul]
      have := hcount (AlgebraicClosure F) (algebraMap F _) (fun y : AlgPt Y => A.lg v (ε v) y)
        (fun θ => Real.log ((ε v).w (θ b)) - t * Real.log ((ε v).w (θ (ρ c)))) (fun θ z _ hz => by
          obtain ⟨θ', rfl⟩ := embedding_extends_algebraicClosure ι' θ
          have h := hfin v (ε v) θ' z (hz.trans (hlift θ'))
          rw [← hb, ← hρ] at h
          exact h)
      rw [← hpq] at this
      exact this
    rw [mul_finsum, finsum_congr hv, finsum_sub_distrib fb (fc.subset (Function.support_mul_subset_right _ _)),
      ← mul_finsum, ← hsum fun σ => Real.log ‖σ c‖]
    simp only [RingHom.comp_apply]
    linear_combination pb - t * pc
  have hN : (d : ℝ) * (Module.finrank ℚ F : ℝ) * (Nat.card {y : AlgPt Y // below y.1 = below p} : ℝ) =
      e * (Module.finrank ℚ K : ℝ) := by
    rw [hpq]; exact_mod_cast hd.trans he.symm
  have hK : (Module.finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have he0 : (e : ℝ) ≠ 0 := by
    have : e * Module.finrank ℚ K ≠ 0 := he ▸ Module.finrank_pos.ne'
    exact_mod_cast left_ne_zero_of_mul this
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
  unfold Adl.ht
  rw [finsum_congr fun v => dif_pos (GlobalTheory.TrueGeo.Ext.instNonempty v), ← mul_div_mul_left _ _ hd', mul_neg, mul_add, h1, h2,
    hn, PNat.one_coe, Nat.cast_one, one_mul, ← mul_assoc (d : ℝ), hN]
  field_simp
  ring
