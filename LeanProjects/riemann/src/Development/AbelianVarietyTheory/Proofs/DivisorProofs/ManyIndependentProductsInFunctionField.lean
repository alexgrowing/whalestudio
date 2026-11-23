import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootMapComplexLinearIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalBranchesOfSeparableReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveMonicSeparableSpecializationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankMulPowLeFinrankOfPowerSeriesStatement

open Filter Topology

namespace GlobalTheory

theorem prod_mem_span_range_prod_mul {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {J : Type*} [Fintype J] (g : J → A) (m : ℕ) (f : Fin m → A)
    (hf : ∀ l, f l ∈ Submodule.span R (Set.range g)) (y : A) :
    (∏ l, f l) * y ∈
      Submodule.span R (Set.range fun u : Fin m → J => (∏ l, g (u l)) * y) := by
  choose c hc using fun l => (Submodule.mem_span_range_iff_exists_fun R).1 (hf l)
  have h : (∏ l, f l) * y = ∑ u : Fin m → J, (∏ l, c l (u l)) • ((∏ l, g (u l)) * y) := by
    simp_rw [← hc, Fintype.prod_sum, Finset.sum_mul, Algebra.smul_def, Finset.prod_mul_distrib,
      map_prod, mul_assoc]
  rw [h]
  exact Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, rfl⟩)

theorem many_independent_products_in_function_field : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ)
    (x : Fin D → K), IsTranscendenceBasis ℤ x → ∀ (J : Type) [Fintype J] (e : J → K),
    LinearIndependent ℤ e → ∀ m : ℕ, 0 < m → ∃ v : Fin (Fintype.card J * m ^ D) → K,
    LinearIndependent ℤ v ∧ ∀ s, ∃ (u : Fin m → J) (a : Fin D → ℕ), (∀ i, a i < m) ∧
      v s = (∏ l, e (u l)) * ∏ i, x i ^ a i := by
  intro K _ _ D x hx J _ e he m hm
  haveI : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have hxQ : IsTranscendenceBasis ℚ x := (Algebra.IsAlgebraic.isTranscendenceBasis_iff ℤ ℚ).1 hx
  have heQ : LinearIndependent ℚ e := (LinearIndependent.iff_fractionRing ℤ ℚ).1 he
  obtain ⟨P, ψ, g, c, hPm, hψ, hψx, hg, hge, hsep⟩ := GlobalTheory.T.exists_primitive_monic_separable_specialization' K D x hxQ J e
  choose e' he' using fun j => (AlgHom.mem_range ψ).1 (hge j)
  have he'Q : LinearIndependent ℚ e' := by
    have h1 : LinearIndependent ℚ (fun j => g * e j) := by
      refine heQ.map' (LinearMap.mulLeft ℚ g) (LinearMap.ker_eq_bot.2 ?_)
      exact mul_right_injective₀ hg
    have h2 : (ψ.toLinearMap ∘ e') = fun j => g * e j := funext he'
    exact LinearIndependent.of_comp ψ.toLinearMap (h2 ▸ h1)
  obtain ⟨τ, hτX, hτq, hτind⟩ := GlobalTheory.T.adjoinRoot_complex_map_linearIndependent D P hPm
  have hPCm : (P.map (MvPolynomial.map (algebraMap ℚ ℂ))).Monic := hPm.map _
  have hsepC : ((P.map (MvPolynomial.map (algebraMap ℚ ℂ))).map
      (MvPolynomial.eval (fun i => (c i : ℂ)))).Separable := by
    have h : (P.map (MvPolynomial.map (algebraMap ℚ ℂ))).map (MvPolynomial.eval (fun i => (c i : ℂ))) =
        (P.map (MvPolynomial.eval c)).map (algebraMap ℚ ℂ) := by
      rw [Polynomial.map_map, Polynomial.map_map]
      congr 1
      ext <;> simp
    rw [h]; exact hsep.map
  let PC := P.map (MvPolynomial.map (algebraMap ℚ ℂ))
  obtain ⟨n, φ, hφinj, hφX⟩ := GlobalTheory.T.exists_formal_branches_of_separable_reduction D PC (fun i => (c i : ℂ)) hPCm hsepC
  let w : (Fin m → J) × (Fin D → Fin m) → AdjoinRoot P := fun ub =>
    (∏ l, e' (ub.1 l)) * ∏ i, AdjoinRoot.of P (MvPolynomial.X i) ^ (ub.2 i : ℕ)
  obtain ⟨κ, a, ha, hspan, hind⟩ := exists_linearIndependent' ℚ w
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  let xC : Fin D → AdjoinRoot PC := fun i => AdjoinRoot.of PC (MvPolynomial.X i)
  let F : Submodule ℂ (AdjoinRoot PC) := Submodule.span ℂ (Set.range fun j => τ (e' j))
  let G : Submodule ℂ (AdjoinRoot PC) := Submodule.span ℂ (Set.range fun k => τ (w (a k)))
  haveI : Module.Finite ℂ F := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  haveI : Module.Finite ℂ G := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hτspan : ∀ u ∈ Submodule.span ℚ (Set.range (w ∘ a)), τ u ∈ G := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy => obtain ⟨k, rfl⟩ := hy; exact Submodule.subset_span ⟨k, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact G.add_mem hy hz
    | smul q y _ hy => rw [hτq]; exact G.smul_mem _ hy
  have key := GlobalTheory.T.finrank_mul_pow_le_finrank_of_prod_mem D n (AdjoinRoot PC) φ xC (fun i => (c i : ℂ)) hφinj hφX F G m hm (by
    intro f b hf hb
    have h1 := prod_mem_span_range_prod_mul (R := ℂ) (fun j => τ (e' j)) m f hf (∏ i, xC i ^ b i)
    refine Submodule.span_le.2 ?_ h1
    rintro _ ⟨u, rfl⟩
    have hw : w (u, fun i => ⟨b i, hb i⟩) ∈ Submodule.span ℚ (Set.range (w ∘ a)) := by
      rw [hspan]; exact Submodule.subset_span ⟨_, rfl⟩
    have h2 := hτspan _ hw
    simpa [w, map_prod, map_mul, map_pow, hτX, xC] using h2)
  have hFr : Module.finrank ℂ F = Fintype.card J := finrank_span_eq_card (hτind J e' he'Q)
  have hGr : Module.finrank ℂ G ≤ Fintype.card κ := finrank_range_le_card _
  let L : AdjoinRoot P →ₗ[ℚ] K := (LinearMap.mulLeft ℚ ((g ^ m)⁻¹)).comp ψ.toLinearMap
  have hL : LinearMap.ker L = ⊥ := by
    refine LinearMap.ker_eq_bot.2 ?_
    show Function.Injective (fun u => (g ^ m)⁻¹ * ψ u)
    exact (mul_right_injective₀ (inv_ne_zero (pow_ne_zero _ hg))).comp hψ
  have hindK : LinearIndependent ℚ (L ∘ (w ∘ a)) := hind.map' L hL
  have hcard : Fintype.card J * m ^ D ≤ Fintype.card κ := hFr ▸ (key.trans hGr)
  let emb : Fin (Fintype.card J * m ^ D) ↪ κ :=
    (Fin.castLEEmb hcard).trans (Fintype.equivFin κ).symm.toEmbedding
  refine ⟨L ∘ (w ∘ a) ∘ emb, ?_, ?_⟩
  · exact (hindK.comp emb emb.injective).restrict_scalars' ℤ
  · intro s
    refine ⟨(a (emb s)).1, fun i => ((a (emb s)).2 i : ℕ), fun i => ((a (emb s)).2 i).isLt, ?_⟩
    simp only [Function.comp_apply, L, w, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      LinearMap.mulLeft_apply, map_mul, map_prod, map_pow, hψx, he', Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    field_simp

end GlobalTheory
