import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsGaussEqZero

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.VacFactor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} {κ : Type} [Fintype κ]

def evIHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evIHom_apply (a : AF F) : evIHom a = evI F a := rfl

theorem evI_realAd_mul (t : ℝ) (c : AF F) : evI F (realAd F t * c) = t • evI F c := by
  rw [← evIHom_apply, map_mul, evIHom_apply, evIHom_apply, Algebra.smul_def]
  congr 1
  simp [evI, realAd]

theorem realAd_mul_snd (t : ℝ) (c : AF F) : (realAd F t * c).2 = 0 := by
  show (realAd F t).2 * c.2 = 0
  simp [realAd]

theorem at_realAd_mul (t : ℝ) (c : AF F) : At (evI F) (realAd F t * c) := by
  intro b hb
  have h1 : b.1 = 0 := by
    have : InfiniteAdeleRing.ringEquiv_mixedSpace F b.1 = 0 := hb
    exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp this
  rw [smul_eq_mul, ← mul_assoc]
  have : b * realAd F t = 0 := Prod.ext (by show b.1 * _ = 0; rw [h1, zero_mul]) (by show _ * (realAd F t).2 = 0; simp [realAd])
  rw [this, zero_mul]

def gam (w : (κ → AF F) × (κ → AF F)) (f : SInf F κ) (t : ℝ) (y : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) *
      ((t * Algebra.trace ℝ _ (y ⬝ᵥ fun i => evI F (w.2 i)) + t ^ 2 * Algebra.trace ℝ _ (evI F (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) : ℝ) : ℂ)) *
    f (y + t • fun i => evI F (w.1 i))

theorem gam_differentiableAt (w : (κ → AF F) × (κ → AF F)) (f : SInf F κ) (y : κ → mixedEmbedding.mixedSpace F) :
    DifferentiableAt ℝ (fun t => gam w f t y) 0 := by
  unfold gam
  fun_prop

theorem schr_pureA (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F)) (t : ℝ) (f : SInf F κ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : κ → AF F) :
    schr ψ (realAd F t • w) (pureA F f g) x = gam w f t (fun i => evI F (x i)) * g (fun i => (x i).2) := by
  have hK : x ⬝ᵥ (realAd F t • w).2 + ⅟(2 : AF F) * ((realAd F t • w).1 ⬝ᵥ (realAd F t • w).2) =
      realAd F t * (x ⬝ᵥ w.2 + realAd F t * (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) := by
    simp only [Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  have hev : evI F (realAd F t * (x ⬝ᵥ w.2 + realAd F t * (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)))) =
      t • ((fun i => evI F (x i)) ⬝ᵥ (fun i => evI F (w.2 i)) + t • evI F (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) := by
    rw [evI_realAd_mul]
    congr 1
    rw [← evIHom_apply, map_add, evIHom_apply, evIHom_apply, evI_realAd_mul, ← evIHom_apply (x ⬝ᵥ w.2),
      RingHom.map_dotProduct]
    rfl
  unfold schr pureA gam
  rw [hK, hψ.2.2 _ (at_realAd_mul _ _), hev]
  have hf : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + (realAd F t • w).1) i).1) =
      (fun i => evI F (x i)) + t • fun i => evI F (w.1 i) := by
    funext i
    show evIHom (x i + realAd F t * w.1 i) = evI F (x i) + t • evI F (w.1 i)
    rw [map_add, evIHom_apply, evIHom_apply, evI_realAd_mul]
  have hg : (fun i => ((x + (realAd F t • w).1) i).2) = fun i => (x i).2 := by
    funext i
    show (x i).2 + (realAd F t * w.1 i).2 = (x i).2
    rw [realAd_mul_snd, add_zero]
  rw [hf, hg]
  simp only [map_smul, map_add, smul_eq_mul]
  ring_nf

end GlobalTheory.VacFactor

noncomputable section

namespace GlobalTheory.VacFactor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} {κ : Type} [Fintype κ]

def dgam (w : (κ → AF F) × (κ → AF F)) (f : SInf F κ) (y : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  deriv (fun t => gam w f t y) 0

theorem exists_indep {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    ∃ (m : ℕ) (f : Fin m → SInf F κ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      (∀ k, g k ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ LinearIndependent ℂ g ∧ Φ = ∑ k, pureA F (f k) (g k) := by
  obtain ⟨m₀, c, p, hp⟩ := Submodule.mem_span_set'.mp hΦ
  choose f₀ g₀ hg₀ hp₀ using fun i => (p i).2
  set f₁ : Fin m₀ → SInf F κ := fun i => c i • f₀ i
  have hΦ' : Φ = ∑ i, pureA F (f₁ i) (g₀ i) := by
    rw [← hp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hp₀ i]
    funext x
    simp [f₁, pureA, mul_assoc]
  set V := Submodule.span ℂ (Set.range g₀)
  haveI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range g₀)
  let b := Module.finBasis ℂ V
  have hmem : ∀ i, g₀ i ∈ V := fun i => Submodule.subset_span ⟨i, rfl⟩
  let a : Fin m₀ → Fin (Module.finrank ℂ V) → ℂ := fun i j => b.repr ⟨g₀ i, hmem i⟩ j
  have hg : ∀ i z, g₀ i z = ∑ j, a i j * (b j : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) z := by
    intro i z
    have := congrArg (fun v : V => (v : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) z) (b.sum_repr ⟨g₀ i, hmem i⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  refine ⟨Module.finrank ℂ V, fun j => ∑ i, a i j • f₁ i, fun j => (b j : _), fun j => ?_, ?_, ?_⟩
  · exact (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hg₀ i)) (b j).2
  · exact b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  · rw [hΦ']
    funext x
    simp only [Finset.sum_apply, pureA, hg, Finset.mul_sum, Finset.sum_mul, SchwartzMap.sum_apply,
      SchwartzMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem heisLine_pureA (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (u : Matrix (Fin n) (Fin d) (AE F E))
    (t : ℝ) (f : SInf F (Fin n × Fin d)) (g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : Fin n × Fin d → AF F) :
    M.heisLine ψ u t (pureA F f g) x = gam (M.co.e u) f t (fun i => evI F (x i)) * g (fun i => (x i).2) := by
  unfold Model.heisLine Darboux.rho
  rw [map_smul, schr_pureA ψ hψ]

theorem hasDerivAt_heisLine_pureA (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (AE F E)) (f : SInf F (Fin n × Fin d)) (g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : Fin n × Fin d → AF F) :
    HasDerivAt (fun t : ℝ => M.heisLine ψ u t (pureA F f g) x)
      (dgam (M.co.e u) f (fun i => evI F (x i)) * g (fun i => (x i).2)) 0 := by
  simp only [heisLine_pureA M ψ hψ]
  exact (gam_differentiableAt _ _ _).hasDerivAt.mul_const _

theorem hasDerivAt_heisLine_sum (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (AE F E)) {m : ℕ} (f : Fin m → SInf F (Fin n × Fin d))
    (g : Fin m → (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : Fin n × Fin d → AF F) :
    HasDerivAt (fun t : ℝ => M.heisLine ψ u t (∑ k, pureA F (f k) (g k)) x)
      (∑ k, dgam (M.co.e u) (f k) (fun i => evI F (x i)) * g k (fun i => (x i).2)) 0 := by
  have e : (fun t : ℝ => M.heisLine ψ u t (∑ k, pureA F (f k) (g k)) x) =
      fun t => ∑ k, M.heisLine ψ u t (pureA F (f k) (g k)) x := by
    funext t
    simp only [Model.heisLine, Darboux.rho, schr, Finset.sum_apply, Finset.mul_sum]
  rw [e]
  exact HasDerivAt.fun_sum fun k _ => hasDerivAt_heisLine_pureA M ψ hψ u (f k) (g k) x

end GlobalTheory.VacFactor

open GlobalTheory.VacFactor in

theorem GlobalTheory.VacFactor.mem_span_of_isGaussEq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), GlobalTheory.VacDatum.IsGaussEq M ψ τ Φ →
      Φ ∈ Submodule.span ℂ {Φ' | ∃ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ),
        f ∈ M.Pol ψ τ ∧ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∧ Φ' = GlobalTheory.WeilM.pureA F f g} := by
  intro F E _ _ _ _ _ σ n d X W M ψ τ hψ Φ hΦ hG
  obtain ⟨m, f, g, hg, hgi, rfl⟩ := exists_indep hΦ
  obtain ⟨ε, hε⟩ := hG
  let mk : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) →
      (Fin n × Fin d → AF F) :=
    fun y z i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), z i)
  have hmk1 : ∀ y z, (fun i => evI F (mk y z i)) = y := fun y z => by
    funext i
    simp [mk, evI]
  have hmk2 : ∀ y z, (fun i => (mk y z i).2) = z := fun y z => rfl
  have key : ∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) u' →
      (∀ w, u'.map (piInf (τ w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (τ w)) * (W.θ w)ᵀ)) →
      ∀ k y, dgam (M.co.e u') (f k) y = Complex.I * dgam (M.co.e u) (f k) y := by
    intro u u' hu hu' hr k y
    have h0 : ∑ k, (dgam (M.co.e u') (f k) y - Complex.I * dgam (M.co.e u) (f k) y) • g k = 0 := by
      funext z
      have e := hε u u' hu hu' hr (mk y z)
      rw [(hasDerivAt_heisLine_sum M ψ hψ u' f g (mk y z)).deriv,
        (hasDerivAt_heisLine_sum M ψ hψ u f g (mk y z)).deriv, hmk1, hmk2] at e
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul, Finset.sum_sub_distrib]
      rw [e, Finset.mul_sum]
      simp only [mul_assoc, sub_self]
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hgi _ h0 k)
  have hgne : ∀ k, ∃ z, g k z ≠ 0 := fun k => by
    by_contra h
    push Not at h
    exact hgi.ne_zero k (funext h)
  have gauss : ∀ k, M.IsGauss ψ τ (f k) := by
    intro k
    obtain ⟨z₀, hz₀⟩ := hgne k
    refine ⟨ε, fun u u' hu hu' hr f₁ f₁' h1 h1' => ?_⟩
    have hR : Rest (evI F) (⇑(f k)) (fun x : Fin n × Fin d → AF F => g k (fun i => (x i).2)) := by
      refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨f k, g k, hg k, rfl⟩⟩
      have hz2 : ∀ i, (z i).2 = 0 := by
        intro i
        have h0 : evI F (show AF F from ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))) = 0 := by
          show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
          exact map_zero _
        have := congrArg (fun v : Fin n × Fin d → AF F => (v i).2) (hz _ h0)
        change (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 at this
        simpa using this
      have hxz : (fun i => ((x + z) i).2) = fun i => (x i).2 := by
        funext i
        show (x i).2 + (z i).2 = (x i).2
        rw [hz2, add_zero]
      exact congrArg (g k) hxz
    have hD : ∀ (v : Matrix (Fin n) (Fin d) (AE F E)) (f₂ : SInf F (Fin n × Fin d)),
        ActsD (evI F) (M.heisLine ψ v) (⇑(f k)) (⇑f₂) → ∀ y, f₂ y = dgam (M.co.e v) (f k) y := by
      intro v f₂ h y
      have a := h _ hR (mk y z₀)
      have b := hasDerivAt_heisLine_pureA M ψ hψ v (f k) (g k) (mk y z₀)
      have := a.unique b
      simp only [tens, hmk1, hmk2] at this
      exact mul_right_cancel₀ hz₀ this
    refine DFunLike.ext _ _ fun y => ?_
    rw [hD u' f₁' h1' y, key u u' hu hu' hr k y, ← hD u f₁ h1 y]
    simp
  refine Submodule.sum_mem _ fun k _ => Submodule.subset_span ⟨f k, g k, ?_, hg k, rfl⟩
  exact Submodule.mem_sInf.mpr fun N hN => hN.1 _ (gauss k)

end
