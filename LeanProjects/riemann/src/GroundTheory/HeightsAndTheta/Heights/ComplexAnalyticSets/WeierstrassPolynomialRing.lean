import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.WeierstrassRemainderUnique
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAnalyticGermsNoetherian
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolGermsDomain
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

noncomputable section

theorem prime_map_of_prime {R S : Type*} [CommRing R] [CommRing S] (Ψ : R →+* S) {ω : R} (hω : Prime ω)
    (hne : Ψ ω ≠ 0) (hsurj : ∀ g : S, ∃ (Q : S) (p : R), g = Ψ ω * Q + Ψ p)
    (hdvd : ∀ p : R, Ψ ω ∣ Ψ p → ω ∣ p) : Prime (Ψ ω) := by
  refine ⟨hne, fun hu => hω.not_isUnit (isUnit_of_dvd_one (hdvd 1 (by rw [map_one]; exact hu.dvd))), ?_⟩
  intro g h hgh
  obtain ⟨Q₁, p₁, rfl⟩ := hsurj g
  obtain ⟨Q₂, p₂, rfl⟩ := hsurj h
  have h12 : Ψ ω ∣ Ψ (p₁ * p₂) := by
    have e : Ψ (p₁ * p₂) = (Ψ ω * Q₁ + Ψ p₁) * (Ψ ω * Q₂ + Ψ p₂) -
        Ψ ω * (Q₁ * (Ψ ω * Q₂ + Ψ p₂) + Ψ p₁ * Q₂) := by rw [map_mul]; ring
    rw [e]; exact dvd_sub hgh (dvd_mul_right _ _)
  rcases hω.dvd_or_dvd (hdvd _ h12) with h1 | h1
  · exact Or.inl (dvd_add (dvd_mul_right _ _) (map_dvd Ψ h1))
  · exact Or.inr (dvd_add (dvd_mul_right _ _) (map_dvd Ψ h1))

def mkGerm {τ : Type} [Fintype τ] (f : (τ → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) : holGerms (0 : τ → ℂ) :=
  ⟨↑f, f, hf, rfl⟩

def germValue {τ : Type} [Fintype τ] (w : τ → ℂ) : holGerms w →+* ℂ :=
  Germ.valueRingHom.comp (holGerms w).subtype

def lastProj (σ : Type) [Fintype σ] : (Option σ → ℂ) →L[ℂ] (σ → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option σ => ℂ) (some i)

def germLift (σ : Type) [Fintype σ] : holGerms (0 : σ → ℂ) →+* holGerms (0 : Option σ → ℂ) :=
  germPull (lastProj σ) ((lastProj σ).analyticAt 0) (map_zero _)

def lastVarGerm (σ : Type) [Fintype σ] : holGerms (0 : Option σ → ℂ) :=
  mkGerm (fun x : Option σ → ℂ => x none)
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option σ => ℂ) none).analyticAt 0)

def polyToGerm (σ : Type) [Fintype σ] : (holGerms (0 : σ → ℂ))[X] →+* holGerms (0 : Option σ → ℂ) :=
  eval₂RingHom (germLift σ) (lastVarGerm σ)

def finPoly {R : Type*} [CommRing R] {d : ℕ} (b : Fin d → R) : R[X] :=
  ∑ j : Fin d, C (b j) * X ^ (j : ℕ)

def weierstrassPoly {σ : Type} [Fintype σ] {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ) (hc : ∀ j, AnalyticAt ℂ (c j) 0) :
    (holGerms (0 : σ → ℂ))[X] :=
  X ^ d + finPoly (fun j => mkGerm (c j) (hc j))

theorem weierstrassPoly_monic {σ : Type} [Fintype σ] {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) 0) : (weierstrassPoly c hc).Monic :=
  monic_X_pow_add (degree_sum_fin_lt _)

theorem polyToGerm_finPoly {σ : Type} [Fintype σ] {d : ℕ} (a : Fin d → (σ → ℂ) → ℂ)
    (ha : ∀ j, AnalyticAt ℂ (a j) 0) :
    ((polyToGerm σ (finPoly fun j => mkGerm (a j) (ha j)) : holGerms (0 : Option σ → ℂ)) :
      Germ (𝓝 (0 : Option σ → ℂ)) ℂ) =
      ↑(fun x : Option σ → ℂ => ∑ j : Fin d, a j (fun i => x (some i)) * x none ^ (j : ℕ)) := by
  have hι : ∀ j, ((germLift σ (mkGerm (a j) (ha j)) : holGerms (0 : Option σ → ℂ)) :
      Germ (𝓝 (0 : Option σ → ℂ)) ℂ) = ↑(a j ∘ lastProj σ) :=
    fun j => germPull_coe _ _ _ (mkGerm (a j) (ha j)) (a j) rfl
  simp only [finPoly, polyToGerm, map_sum, map_mul, map_pow, coe_eval₂RingHom, eval₂_C, eval₂_X]
  rw [AddSubmonoidClass.coe_finsetSum]
  simp only [Subring.coe_mul, Subring.coe_pow, hι]
  change ∑ j : Fin d, Germ.coeRingHom _ (a j ∘ lastProj σ) *
      Germ.coeRingHom _ (fun x : Option σ → ℂ => x none) ^ (j : ℕ) = Germ.coeRingHom _ _
  simp only [← map_mul, ← map_pow, ← map_sum]
  congr 1
  funext x
  simp [Finset.sum_apply, lastProj]

theorem polyToGerm_weierstrassPoly {σ : Type} [Fintype σ] {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) 0) :
    ((polyToGerm σ (weierstrassPoly c hc) : holGerms (0 : Option σ → ℂ)) : Germ (𝓝 (0 : Option σ → ℂ)) ℂ) =
      ↑(weierstrassPolynomial c) := by
  rw [weierstrassPoly, map_add, Subring.coe_add, polyToGerm_finPoly, map_pow, Subring.coe_pow]
  have hX : ((polyToGerm σ X : holGerms (0 : Option σ → ℂ)) : Germ (𝓝 (0 : Option σ → ℂ)) ℂ) =
      ↑(fun x : Option σ → ℂ => x none) := by
    simp only [polyToGerm, coe_eval₂RingHom, eval₂_X]; rfl
  rw [hX]
  change Germ.coeRingHom _ (fun x : Option σ → ℂ => x none) ^ d + Germ.coeRingHom _ _ = Germ.coeRingHom _ _
  rw [← map_pow, ← map_add]
  rfl

theorem germValue_polyToGerm {σ : Type} [Fintype σ] (p : (holGerms (0 : σ → ℂ))[X]) :
    germValue 0 (polyToGerm σ p) = (p.map (germValue 0)).eval 0 := by
  have h1 : (germValue (0 : Option σ → ℂ)).comp (germLift σ) = germValue 0 := by
    ext φ
    obtain ⟨f, -, hf⟩ := φ.2
    show Germ.value ((germLift σ φ : holGerms (0 : Option σ → ℂ)) : Germ (𝓝 (0 : Option σ → ℂ)) ℂ) =
      Germ.value (φ : Germ (𝓝 (0 : σ → ℂ)) ℂ)
    rw [germLift, germPull_coe _ _ _ φ f hf, ← hf]
    simp [lastProj]
    rfl
  rw [eval_map, polyToGerm, coe_eval₂RingHom, hom_eval₂, h1]
  rfl

theorem weierstrassPoly_dvd_of_polyToGerm_dvd {σ : Type} [Fintype σ] {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) 0) (hc0 : ∀ j, c j 0 = 0) (p : (holGerms (0 : σ → ℂ))[X])
    (h : polyToGerm σ (weierstrassPoly c hc) ∣ polyToGerm σ p) : weierstrassPoly c hc ∣ p := by
  have hm := weierstrassPoly_monic c hc
  have hdeg : (weierstrassPoly c hc).natDegree = d := by
    rw [weierstrassPoly, finPoly, natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_sum_fin_lt _),
      natDegree_X_pow]
  rw [← modByMonic_eq_zero_iff_dvd hm]
  have hrdeg : (p %ₘ weierstrassPoly c hc).degree < d := by
    have := degree_modByMonic_lt p hm
    rwa [degree_eq_natDegree hm.ne_zero, hdeg] at this
  choose a ha hae using fun j : Fin d => ((p %ₘ weierstrassPoly c hc).coeff j).2
  have hcoeff : ∀ j : Fin d, (p %ₘ weierstrassPoly c hc).coeff j = mkGerm (a j) (ha j) :=
    fun j => Subtype.ext (hae j).symm
  have hr : p %ₘ weierstrassPoly c hc = finPoly fun j => mkGerm (a j) (ha j) := by
    conv_lhs => rw [← sum_C_mul_X_pow_eq (p %ₘ weierstrassPoly c hc)]
    rw [← sum_fin (fun n b => C b * X ^ n) (by simp) hrdeg, finPoly]
    exact Finset.sum_congr rfl fun j _ => by rw [hcoeff j]

  obtain ⟨Q, hQ⟩ := h
  have himg : polyToGerm σ (p %ₘ weierstrassPoly c hc) =
      polyToGerm σ (weierstrassPoly c hc) * (Q - polyToGerm σ (p /ₘ weierstrassPoly c hc)) := by
    have e := congrArg (polyToGerm σ) (modByMonic_add_div p (weierstrassPoly c hc))
    rw [map_add, map_mul] at e
    rw [mul_sub, ← hQ, ← e]; ring
  obtain ⟨m, hmA, hmQ⟩ := (Q - polyToGerm σ (p /ₘ weierstrassPoly c hc)).2
  have hgerm := congrArg (fun φ : holGerms (0 : Option σ → ℂ) => (φ : Germ (𝓝 (0 : Option σ → ℂ)) ℂ)) himg
  simp only [Subring.coe_mul] at hgerm
  rw [hr, polyToGerm_finPoly, polyToGerm_weierstrassPoly, ← hmQ] at hgerm
  have hev : ∀ᶠ x in 𝓝 (0 : Option σ → ℂ),
      ∑ j : Fin d, a j (fun i => x (some i)) * x none ^ (j : ℕ) = m x * weierstrassPolynomial c x := by
    have := Germ.coe_eq.1 (hgerm.trans (Germ.coe_mul _ _).symm)
    filter_upwards [this] with x hx
    rw [hx]; exact mul_comm _ _
  have hzero := weierstrass_remainder_eq_zero c (fun j => (hc j).continuousAt) hc0 a m hmA hev
  rw [hr]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : mkGerm (a j) (ha j) = 0 := Subtype.ext (Germ.coe_eq.2 (hzero j))
  show C (mkGerm (a j) (ha j)) * X ^ (j : ℕ) = 0
  rw [this, C_0, zero_mul]

theorem weierstrassPoly_irreducible {σ : Type} [Fintype σ] {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) 0) (hc0 : ∀ j, c j 0 = 0)
    (hirr : Irreducible (polyToGerm σ (weierstrassPoly c hc))) : Irreducible (weierstrassPoly c hc) := by
  have hm := weierstrassPoly_monic c hc
  refine ⟨fun hu => hirr.not_isUnit (hu.map _), fun a b hab => ?_⟩
  have hlc : a.leadingCoeff * b.leadingCoeff = 1 := by
    rw [← leadingCoeff_mul, ← hab]; exact hm
  obtain ⟨u, hu⟩ : IsUnit a.leadingCoeff := IsUnit.of_mul_eq_one _ hlc
  have ha' : (a * C (↑u⁻¹ : holGerms (0 : σ → ℂ))).Monic := by
    rw [Monic, leadingCoeff_mul, leadingCoeff_C, ← hu, Units.mul_inv]
  have hb' : (b * C (u : holGerms (0 : σ → ℂ))).Monic := by
    rw [Monic, leadingCoeff_mul, leadingCoeff_C, hu, mul_comm, hlc]
  have hab' : weierstrassPoly c hc = (a * C (↑u⁻¹ : holGerms (0 : σ → ℂ))) * (b * C (u : holGerms (0 : σ → ℂ))) := by
    rw [hab, show (a * C (↑u⁻¹ : holGerms (0 : σ → ℂ))) * (b * C (u : holGerms (0 : σ → ℂ))) =
      a * b * C ((↑u⁻¹ : holGerms (0 : σ → ℂ)) * u) by rw [C_mul]; ring, Units.inv_mul, C_1, mul_one]
  have hmap : (weierstrassPoly c hc).map (germValue 0) = X ^ d := by
    simp only [weierstrassPoly, finPoly, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_sum,
      Polynomial.map_mul, map_C]
    have : ∀ j, germValue 0 (mkGerm (c j) (hc j)) = 0 := fun j => hc0 j
    simp [this]

  have key : ∀ (a' b' : (holGerms (0 : σ → ℂ))[X]), a'.Monic → b'.Monic → weierstrassPoly c hc = a' * b' →
      IsUnit (polyToGerm σ a') → a' = 1 := by
    intro a' b' ha'm hb'm he hunit
    have hdvdX : a'.map (germValue 0) ∣ X ^ d := ⟨b'.map (germValue 0), by rw [← Polynomial.map_mul, ← he, hmap]⟩
    obtain ⟨k, -, hassoc⟩ := (dvd_prime_pow prime_X d).1 hdvdX
    have hka : a'.map (germValue 0) = X ^ k := eq_of_monic_of_associated (ha'm.map _) (monic_X_pow k) hassoc
    have hv := (hunit.map (germValue 0)).ne_zero
    rw [germValue_polyToGerm, hka, eval_pow, eval_X] at hv
    have hk0 : k = 0 := by
      by_contra hk0; exact hv (zero_pow hk0)
    have hdeg0 : a'.natDegree = 0 := by
      rw [← ha'm.natDegree_map (germValue 0), hka, hk0, pow_zero, natDegree_one]
    exact ha'm.natDegree_eq_zero.1 hdeg0
  rw [hab', map_mul] at hirr
  rcases hirr.isUnit_or_isUnit rfl with h1 | h1
  · left
    have e := key _ _ ha' hb' hab' h1
    have : a = C (u : holGerms (0 : σ → ℂ)) := by
      calc a = (a * C (↑u⁻¹ : holGerms (0 : σ → ℂ))) * C (u : holGerms (0 : σ → ℂ)) := by
              rw [mul_assoc, ← C_mul, Units.inv_mul, C_1, mul_one]
        _ = C (u : holGerms (0 : σ → ℂ)) := by rw [e, one_mul]
    rw [this]; exact isUnit_C.2 u.isUnit
  · right
    have e := key _ _ hb' ha' (by rw [hab', mul_comm]) h1
    have : b = C (↑u⁻¹ : holGerms (0 : σ → ℂ)) := by
      calc b = (b * C (u : holGerms (0 : σ → ℂ))) * C (↑u⁻¹ : holGerms (0 : σ → ℂ)) := by
              rw [mul_assoc, ← C_mul, Units.mul_inv, C_1, mul_one]
        _ = C (↑u⁻¹ : holGerms (0 : σ → ℂ)) := by rw [e, one_mul]
    rw [this]; exact isUnit_C.2 u⁻¹.isUnit

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
