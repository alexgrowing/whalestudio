import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteOrderHeckeCharGalois
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormCharacterGaloisCofinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobDenseOffFinite
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SelfTwWeak

theorem trace_of_charpoly {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (N : Matrix (Fin a) (Fin a) (Qbar l))
    (S : Multiset ℂ) (h : N.charpoly.map ι.toRingHom = (S.map fun b => X - C b).prod) : ι N.trace = S.sum := by
  have h1 := congrArg Polynomial.nextCoeff h
  rw [nextCoeff_map ι.injective, multiset_prod_X_sub_C_nextCoeff] at h1
  rw [Matrix.trace_eq_neg_charpoly_nextCoeff, map_neg]
  change -(ι.toRingHom N.charpoly.nextCoeff) = _
  rw [h1, neg_neg]

theorem algSat_mul (n q : ℕ) (B : Multiset ℂˣ) (e : ℂˣ) :
    (UpperTheory.V.Af.algSat n q (B.map (· * e))).sum = (e : ℂ) * (UpperTheory.V.Af.algSat n q B).sum := by
  simp only [UpperTheory.V.Af.algSat]
  simp
  simp only [mul_assoc, Multiset.sum_map_mul_left, Multiset.sum_map_mul_right]
  ring

theorem selfTw_mul_trace_inv (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub K a)
    (r : G K Ω →* GL (Fin a) (Qbar l)) (hr : Weak π ι r) (η : HChar K)
    (hη : UpperTheory.V.Published.SelfTw (CG.mk π).HasSat η) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ∀ (A : ValuationSubring Ω) (σ : G K Ω),
      IsPlaceOver A v → IsFrob A (normV v) σ →
        (η.val v : ℂ) * ι (r σ⁻¹).val.trace = ι (r σ⁻¹).val.trace := by
  obtain ⟨-, -, hev⟩ := hr
  filter_upwards [hev, hη] with v hv1 hv2 A σ hA hσ
  obtain ⟨B, hB, hF⟩ := hv1
  obtain ⟨-, B', hB', hBη⟩ := hv2
  have hBB : B' = B := hB'.unique hB
  subst hBB
  have ht := trace_of_charpoly ι _ _ ((hF A hA).2 σ hσ)
  rw [ht]
  conv_rhs => rw [← hBη]
  rw [algSat_mul]

theorem ne_one_of_moves (Ω : Type) [Field Ω] (K : Type) [Field K] [Algebra K Ω] (M : Type) [Field M] [Algebra M Ω]
    [Algebra K M] [IsScalarTower K M Ω] [FiniteDimensional K M] [IsGalois K M] (hp : (Module.finrank K M).Prime)
    (χ : G K Ω →* ℂˣ) (hne : χ ≠ 1)
    (h3 : ∀ g : G K Ω, (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) → χ g = 1) (g : G K Ω)
    (hg : ∃ x : M, g (algebraMap M Ω x) ≠ algebraMap M Ω x) : χ g ≠ 1 := by
  classical
  let ρ : G K Ω →* (M ≃ₐ[K] M) := AlgEquiv.restrictNormalHom M
  have hfix : ∀ k : G K Ω, ρ k = 1 → ∀ x : M, k (algebraMap M Ω x) = algebraMap M Ω x := by
    intro k hk x
    have := AlgEquiv.restrictNormal_commutes k M x
    rw [← this]
    change algebraMap M Ω (ρ k x) = _
    rw [hk]; rfl
  haveI : Fact (Nat.card (M ≃ₐ[K] M)).Prime := ⟨by
    first
      | (rw [IsGalois.card_aut_eq_finrank]; exact hp)
      | (convert hp using 1; rw [Nat.card_eq_fintype_card]; convert IsGalois.card_aut_eq_finrank K M)⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((χ.ker).map ρ) with hH | hH
  · intro hχg
    obtain ⟨x, hx⟩ := hg
    have : ρ g ∈ (χ.ker).map ρ := ⟨g, hχg, rfl⟩
    rw [hH, Subgroup.mem_bot] at this
    exact hx (hfix g this x)
  · exfalso
    apply hne
    ext k
    have : ρ k ∈ (χ.ker).map ρ := by rw [hH]; trivial
    obtain ⟨k', hk', hkk⟩ := this
    have h1 : χ (k * k'⁻¹) = 1 := h3 _ (hfix _ (by rw [map_mul, map_inv, hkk, mul_inv_cancel]))
    rw [map_mul, map_inv, MonoidHom.mem_ker.1 hk', inv_one, mul_one] at h1
    simp [h1]

theorem inv_moves {Ω K M : Type} [Field Ω] [Field K] [Algebra K Ω] [Field M] [Algebra M Ω] (g : G K Ω)
    (hg : ∃ x : M, g (algebraMap M Ω x) ≠ algebraMap M Ω x) : ∃ x : M, g⁻¹ (algebraMap M Ω x) ≠ algebraMap M Ω x := by
  obtain ⟨x, hx⟩ := hg
  refine ⟨x, fun h => hx ?_⟩
  have e : (g * g⁻¹) (algebraMap M Ω x) = algebraMap M Ω x := by rw [mul_inv_cancel]; rfl
  rw [AlgEquiv.mul_apply, h] at e
  exact e

theorem trace_eq_zero_of_selfTw : ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower K M Ω] [IsGalois K M], (Module.finrank K M).Prime → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub K a) (r : G K Ω →* GL (Fin a) (Qbar l)), Weak π ι r → ∀ η : HChar K, UpperTheory.V.Published.IsNormChar M η → UpperTheory.V.Published.SelfTw (CG.mk π).HasSat η → ∀ g : G K Ω, (∃ x : M, g (algebraMap M Ω x) ≠ algebraMap M Ω x) → (r g).val.trace = 0 := by
  intro Ω _ K _ _ _ _ _ M _ _ _ _ _ _ _ _ hp l _ ι a π r hr η hη hst g hg
  obtain ⟨χ, hχo, hχ1, hχf⟩ :=
    GlobalTheory.HeckeToGal.exists_galChar_of_finite_order Ω K η (Module.finrank K M) hp.pos hη.2.1
  have hχne : χ ≠ 1 := fun h => hη.1 (hχ1 h)
  have h3 := GlobalTheory.trivial_on_ext_of_frob_eq_normChar Ω K M η hη χ hχo hχf
  have hne := ne_one_of_moves Ω K M hp χ hχne h3 g⁻¹ (inv_moves g hg)
  have h1 := selfTw_mul_trace_inv Ω K l ι a π r hr η hst
  have hcont : Continuous r := hr.1
  have hUo : IsOpen {k : G K Ω | χ k ≠ 1} := by
    have hc : IsClosed (χ.ker : Set (G K Ω)) := Subgroup.isClosed_of_isOpen _ hχo
    have : {k : G K Ω | χ k ≠ 1} = (χ.ker : Set (G K Ω))ᶜ := by ext k; simp [MonoidHom.mem_ker]
    rw [this]; exact hc.isOpen_compl
  have hT := Filter.eventually_cofinite.1 (h1.and hχf)
  have hD := GlobalTheory.frob_dense_off_finite K Ω _ hT
  have hc : Continuous fun k : G K Ω => (r k⁻¹).val.trace :=
    (Units.continuous_val.comp (hcont.comp continuous_inv)).matrix_trace
  have hZ : IsClosed {k : G K Ω | (r k⁻¹).val.trace = 0} := isClosed_eq hc continuous_const
  have hsub := hD.open_subset_closure_inter hUo hne
  have key : (r g⁻¹⁻¹).val.trace = 0 := by
    refine closure_minimal ?_ hZ hsub
    rintro σ ⟨hσU, v, hv, A, hA, hσ⟩
    simp only [Set.mem_setOf_eq, not_not] at hv
    have e1 := hv.1 A σ hA hσ
    have e2 := hv.2 A σ hA hσ
    have hv1 : (η.val v : ℂ) ≠ 1 := by
      intro h; apply hσU; rw [e2]; exact Units.val_eq_one.1 h
    have : ι (r σ⁻¹).val.trace = 0 := by
      have h0 : ((η.val v : ℂ) - 1) * ι (r σ⁻¹).val.trace = 0 := by rw [sub_mul, e1, one_mul, sub_self]
      exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hv1)
    exact (map_eq_zero_iff ι ι.injective).1 this
  rwa [inv_inv] at key

end GlobalTheory.SelfTwWeak

end
