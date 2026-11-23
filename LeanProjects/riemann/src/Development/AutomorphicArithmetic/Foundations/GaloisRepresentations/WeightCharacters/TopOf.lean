import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.LacunaryBaseWeightAntitone
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowValAdd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorSmallSubFiniteEigenApproxInequalityStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicFormWeightLevelSmoothAtPlaceStatement

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

open UpperTheory.Gal.Gen UpperTheory.Gal.Int.Cong in
theorem top_of : FamEx → FamProj → FamWt → UpperTheory.Gal.Int.Cong.WtLacEx := by
  intro hEx hPr hWt E _ _ _ l _ ι a ha w₀ hw₀ hs₀ v' hv' hsv hap K hK hKv Kv hKvo lam Jx t η ht htv hact τ₀ hτ₀ U hU ε hε
  classical
  obtain ⟨W, f, hW, hf0, hfU, hfK, -⟩ := GlobalTheory.T.exists_algebraicForm_weight_level_smooth_at_place E a lam _ U (inf_le_left.trans hK.fin) hU w₀
  obtain rfl : lam = W.at := (funext hW).symm
  obtain ⟨X, b, hbd, hdef, hne⟩ := Loc.frame denomBdd_holds rhoBound_holds latFacts_holds levelEx_holds ι W t fun j => Or.inr (ht j)
  obtain ⟨g₀, i₀, hz⟩ : ∃ g i, f.1 (b g i) g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (hdef f h)
  set z₀ := f.1 (b g₀ i₀) g₀ with hz₀
  let f₁ : algForms W := z₀⁻¹ • f
  have hf₁ : ∀ v g, f₁.1 v g = z₀⁻¹ * f.1 v g := fun v g => rfl
  have hf₁K : f₁ ∈ fixedBy W (K ⊓ Kv.comap (cLoc v')) := fun k hk v g => by rw [hf₁, hf₁, hfK k hk v g]
  have hf₁U : ∀ v, f₁.1 v ∈ U := fun v => U.smul_mem _ (hfU v)
  obtain ⟨d, M, hM, hB⟩ := hEx E l ι a ha w₀ hw₀ hs₀ v' hsv hap K hK hKv Kv hKvo W f₁ hf₁K τ₀ hτ₀ X b hbd ε hε
  let N : ℕ := (a + 1) * (2 * (2 * d) + a) + 1
  let ν : DomWeight a := ⟨fun k => (N : ℤ) * mu0 a k, fun _ _ h => mul_le_mul_of_nonneg_left (lacunaryBaseWeight_antitone a h) (Int.natCast_nonneg N)⟩
  obtain ⟨B, hFam, hnear⟩ := hB ν
  obtain ⟨s₀, F, hF, hsum⟩ := hPr E a τ₀ W K ν d B hFam
  let I := s₀.filter fun V => ∃ y₁ y₂ v, F V y₁ y₂ v ≠ 0
  let Ft : Submodule ℂ (UA E a → ℂ) → (W.Sp →ₗ[ℂ] (UA E a → ℂ)) := fun V =>
    LinearMap.pi fun g => (LinearMap.proj g) ∘ₗ F V (M g) (M g)
  have hFt : ∀ V v g, Ft V v g = F V (M g) (M g) v g := fun _ _ _ => rfl
  let T : Jx → Module.End ℂ (W.Sp →ₗ[ℂ] (UA E a → ℂ)) := fun j =>
    LinearMap.llcomp ℂ W.Sp (UA E a → ℂ) (UA E a → ℂ) (GlobalTheory.CongSc.opL (t j))
  let ev : UA E a × X → (W.Sp →ₗ[ℂ] (UA E a → ℂ)) →ₗ[ℂ] ℂ := fun x =>
    (LinearMap.proj x.1) ∘ₗ (LinearMap.applyₗ (b x.1 x.2))
  have hT : ∀ j (F' : W.Sp →ₗ[ℂ] (UA E a → ℂ)) v, T j F' v = opOf (RU E a) (t j) (F' v) := fun _ _ _ => rfl
  have hev : ∀ x (F' : W.Sp →ₗ[ℂ] (UA E a → ℂ)), ev x F' = F' (b x.1 x.2) x.1 := fun _ _ => rfl
  have hne' : ∀ (F' : W.Sp →ₗ[ℂ] (UA E a → ℂ)) (R' : ℝ), (∀ x, ‖ι.symm (ev x F')‖ ≤ R') →
      ∀ j x, ‖ι.symm (ev x (T j F'))‖ ≤ R' := fun F' R' hR' j x =>
    hne F' R' (fun g i => hR' (g, i)) j x.1 x.2
  have heig0 : ∀ j, T j f₁.1 = η U j • f₁.1 := by
    intro j; apply LinearMap.ext; intro v
    rw [hT, LinearMap.smul_apply]
    exact hact U hU.aut (f₁.1 v) (hf₁U v) (fun x hx => funext fun g => hf₁K x hx v g) j
  have hnorm : ‖ι.symm (ev (g₀, i₀) f₁.1)‖ = 1 := by
    have : ev (g₀, i₀) f₁.1 = 1 := by
      rw [hev]
      show z₀⁻¹ * f.1 (b g₀ i₀) g₀ = 1
      exact inv_mul_cancel₀ hz
    rw [this, map_one, norm_one]
  let vv : ↥I → (W.Sp →ₗ[ℂ] (UA E a → ℂ)) := fun V => -Ft V.1
  have hop : ∀ j (φ : UA E a → ℂ) g, opOf (RU E a) (t j) φ g = ∑ h ∈ (t j).support, t j h * φ (g * h) := fun j φ g => by
    simp only [opOf, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, RU_apply, smul_eq_mul]
  have heig : ∀ (V : ↥I) j, T j (vv V) = η V.1 j • vv V := by
    rintro ⟨V, hV⟩ j
    obtain ⟨h1, h2, h3⟩ := hF V (Finset.mem_filter.1 hV).1
    have h : T j (Ft V) = η V j • Ft V := by
      apply LinearMap.ext; intro v
      funext g
      have e := congrFun (hact V h1 _ (h3 (M g) (M g) v) (fun x hx => h2.fix x hx.1 _ _ _) j) g
      rw [hT, hop, LinearMap.smul_apply, Pi.smul_apply, hFt]
      rw [hop, Pi.smul_apply] at e
      rw [← e]
      refine Finset.sum_congr rfl fun h hh => ?_
      rw [hFt, hM g h (ht j h hh).1 ((htv j h hh).2 v' (not_apart_self v'))]
    show T j (-Ft V) = η V j • -Ft V
    rw [map_neg, h, smul_neg]
  have hbound : ∀ x, ‖ι.symm (ev x (f₁.1 + ∑ V, vv V))‖ ≤ ε := by
    intro x
    have h1 : ev x (f₁.1 + ∑ V, vv V) = f₁.1 (b x.1 x.2) x.1 - B (M x.1) (M x.1) (b x.1 x.2) x.1 := by
      rw [map_add, map_sum, hev, sub_eq_add_neg, ← hsum, Finset.sum_apply, ← Finset.sum_neg_distrib]
      congr 1
      rw [Finset.sum_coe_sort I (fun V => ev x (-Ft V))]
      refine (Finset.sum_filter_of_ne fun V _ hV => ?_).trans (Finset.sum_congr rfl fun V _ => rfl)
      by_contra h
      push_neg at h
      refine hV ?_
      rw [map_neg, hev, hFt, h, Pi.zero_apply, neg_zero]
    rw [h1]
    exact hnear _ _
  obtain ⟨s, c, hs, hP⟩ := GlobalTheory.T.eigenvector_small_sub_finite_eigen_approx_inequality l ι (W.Sp →ₗ[ℂ] (UA E a → ℂ)) (UA E a × X) Jx
    ↥I T ev hne' f₁.1 (η U) (g₀, i₀) heig0 hnorm vv (fun V => η V.1) heig ε hbound
  refine ⟨s, c, ?_, hP⟩
  intro z hz'
  obtain ⟨⟨V, hV⟩, rfl⟩ := hs z hz'
  obtain ⟨hV1, hV2⟩ := Finset.mem_filter.1 hV
  obtain ⟨h1, h2, h3⟩ := hF V hV1
  obtain ⟨mu, g1, g2, g3⟩ := hWt E a τ₀ W K ν d (F V) h2 V h1 h3 hV2
  refine ⟨V, mu, fun τ hτ => ?_, gapJ_of_near (mu τ₀) N (2 * d) g3 (Nat.lt_succ_self _), g1, rfl⟩
  have e : InfinitePlace.mk τ = InfinitePlace.mk τ₀ := by
    by_contra h
    exact hτ (g2 τ h)
  rcases InfinitePlace.mk_eq_iff.1 e with rfl | rfl
  · exact Or.inl hτ₀
  · refine Or.inr fun x hx => ?_
    have := hτ₀ x hx
    rwa [ComplexEmbedding.conjugate_coe_eq, ← IsCMField.complexEmbedding_complexConj] at this

end UpperTheory.Gal.Wt

end
