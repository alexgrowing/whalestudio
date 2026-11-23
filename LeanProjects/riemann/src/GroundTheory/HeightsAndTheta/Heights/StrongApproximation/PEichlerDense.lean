import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

namespace EichlerDense

section Ring

variable {R : Type*} [CommRing R] {N : ℕ}

def param (σ : R →+* R) (J : Matrix (Fin N) (Fin N) R) (e f : Fin N → R) (κ : R)
    (p : (Fin N → R) × R) : Matrix (Fin N) (Fin N) R :=
  eich σ J e (perpProj σ J e f p.1)
    (p.2 - σ p.2 - κ * hf σ J (perpProj σ J e f p.1) (perpProj σ J e f p.1))

theorem hf_map {S : Type*} [CommRing S] (σ : R →+* R) (σ' : S →+* S) (φ : R →+* S)
    (hφ : ∀ x, φ (σ x) = σ' (φ x)) (J : Matrix (Fin N) (Fin N) R) (x y : Fin N → R) :
    hf σ' (J.map φ) (φ ∘ x) (φ ∘ y) = φ (hf σ J x y) := by
  simp [hf, map_sum, map_mul, hφ]

theorem eich_map {S : Type*} [CommRing S] (σ : R →+* R) (σ' : S →+* S) (φ : R →+* S)
    (hφ : ∀ x, φ (σ x) = σ' (φ x)) (J : Matrix (Fin N) (Fin N) R) (e u : Fin N → R) (c : R) :
    (eich σ J e u c).map φ = eich σ' (J.map φ) (φ ∘ e) (φ ∘ u) (φ c) := by
  ext i j
  simp [eich, vecMulVec_apply, mulVec, dotProduct, map_sum, hφ, Matrix.one_apply, apply_ite φ]

theorem param_map {S : Type*} [CommRing S] (σ : R →+* R) (σ' : S →+* S) (φ : R →+* S)
    (hφ : ∀ x, φ (σ x) = σ' (φ x)) (J : Matrix (Fin N) (Fin N) R) (e f : Fin N → R) (κ : R)
    (p : (Fin N → R) × R) :
    (param σ J e f κ p).map φ = param σ' (J.map φ) (φ ∘ e) (φ ∘ f) (φ κ) (φ ∘ p.1, φ p.2) := by
  have hP : φ ∘ perpProj σ J e f p.1 = perpProj σ' (J.map φ) (φ ∘ e) (φ ∘ f) (φ ∘ p.1) := by
    funext i
    simp only [perpProj, Function.comp_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub,
      map_mul, hf_map σ σ' φ hφ]
  rw [param, param, eich_map σ σ' φ hφ, ← hP, map_sub, map_sub, map_mul, hφ, hf_map σ σ' φ hφ]

variable {σ : R →+* R} (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin N) (Fin N) R} (hJ : Jᵀ = J.map σ)
  {e f : Fin N → R} {κ : R} (hκ : κ + κ = 1) (hσκ : σ κ = κ)
include hσ hJ hκ hσκ

theorem param_mem
    (hP : ∀ u, hf σ J (perpProj σ J e f u) e = 0 ∧ hf σ J (perpProj σ J e f u) f = 0)
    (p : (Fin N → R) × R) : param σ J e f κ p ∈ eichAlong σ J e f := by
  refine ⟨perpProj σ J e f p.1, _, (hP p.1).1, (hP p.1).2, ?_, rfl⟩
  have hh := hf_symm hσ hJ (perpProj σ J e f p.1) (perpProj σ J e f p.1)
  rw [map_sub, map_sub, map_mul, hσ, hσκ, hh]
  linear_combination (-(hf σ J (perpProj σ J e f p.1) (perpProj σ J e f p.1))) * hκ

omit hσ hJ in

theorem eq_param
    (hfix : ∀ u, hf σ J u e = 0 → hf σ J u f = 0 → perpProj σ J e f u = u)
    {M : Matrix (Fin N) (Fin N) R} (hM : M ∈ eichAlong σ J e f) : ∃ p, M = param σ J e f κ p := by
  obtain ⟨u, c, hue, huf, hc, rfl⟩ := hM
  refine ⟨(u, κ * c), ?_⟩
  simp only [param, hfix u hue huf]
  congr 1
  rw [map_mul, hσκ]
  linear_combination κ * hc - c * hκ

end Ring

section Top

variable {X : Type*} [TopologicalSpace X] {S : Type*} [CommRing S] [TopologicalSpace S]
  [IsTopologicalRing S] {N : ℕ} {σ : S →+* S}

theorem continuous_hf (hσ : Continuous σ) (J : Matrix (Fin N) (Fin N) S) {x y : X → Fin N → S}
    (hx : Continuous x) (hy : Continuous y) : Continuous fun t => hf σ J (x t) (y t) := by
  unfold hf
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (((continuous_apply i).comp hx).mul continuous_const).mul
    (hσ.comp ((continuous_apply j).comp hy))

theorem continuous_eich (hσ : Continuous σ) (J : Matrix (Fin N) (Fin N) S) (e : Fin N → S)
    {g : X → Fin N → S} {k : X → S} (hg : Continuous g) (hk : Continuous k) :
    Continuous fun t => eich σ J e (g t) (k t) := by
  have hσg : Continuous fun t => σ ∘ g t :=
    continuous_pi fun i => hσ.comp ((continuous_apply i).comp hg)
  unfold eich
  fun_prop

end Top

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem c_invol (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (x : E) :
    c (c x) = x := by
  classical
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hle : Fintype.card (E ≃ₐ[F] E) ≤ 2 := h2 ▸ AlgEquiv.card_le
  have hge : 2 ≤ Fintype.card (E ≃ₐ[F] E) := by
    rw [← Finset.card_pair (Ne.symm hc)]
    exact Finset.card_le_univ _
  have hsq : c ^ 2 = 1 := by
    rw [← le_antisymm hle hge]
    exact pow_card_eq_one
  have := congrArg (fun g : E ≃ₐ[F] E => g x) hsq
  simpa [pow_two] using this

omit [NumberField E] in
theorem sigA_inclA' (c : E ≃ₐ[F] E) (x : E) : sigA c (inclA F E x) = inclA F E (c x) := by
  simp [sigA, inclA, Algebra.TensorProduct.map_tmul]

omit [NumberField E] in
theorem sigA_invol' (c : E ≃ₐ[F] E) (hc2 : ∀ x, c (c x) = x) (a : AE F E) :
    sigA c (sigA c a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigA, Algebra.TensorProduct.map_tmul, hc2]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem along (hT : AETopologicalRing.Statement) (hD : EDenseInAE.Statement)
    (hO : OrthProjection.Statement) (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (N : ℕ) (J : Matrix (Fin N) (Fin N) E) (hJ : Jᵀ = J.map c) (e f : Fin N → E)
    (he : hf c.toRingHom J e e = 0) (hff : hf c.toRingHom J f f = 0) (hef : hf c.toRingHom J e f = 1)
    [TopologicalSpace (AE F E)] [IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (AE F E)] :
    eichAlong (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ f) ⊆
      closure ((fun γ : Matrix (Fin N) (Fin N) E => γ.map (inclA F E)) ''
        eichAlong c.toRingHom J e f) := by
  obtain ⟨hring, hσc, -, -⟩ := hT F E c h2 hc
  have hc2 : ∀ x, c.toRingHom (c.toRingHom x) = x := c_invol c h2 hc
  have hσA : ∀ x, sigA c (sigA c x) = x := sigA_invol' c (c_invol c h2 hc)
  have hφ : ∀ x, inclA F E (c.toRingHom x) = sigA c (inclA F E x) := fun x => (sigA_inclA' c x).symm
  have hJA : (J.map (inclA F E))ᵀ = (J.map (inclA F E)).map (sigA c) := by
    ext i j
    have := congrFun (congrFun hJ i) j
    simp only [transpose_apply, map_apply] at this ⊢
    rw [this, sigA_inclA']
  have hκ : (2 : E)⁻¹ + (2 : E)⁻¹ = 1 := by
    rw [← two_mul, mul_inv_cancel₀ two_ne_zero]
  have hcκ : c.toRingHom (2 : E)⁻¹ = (2 : E)⁻¹ := by rw [map_inv₀, map_ofNat]
  have hκA : inclA F E (2 : E)⁻¹ + inclA F E (2 : E)⁻¹ = 1 := by rw [← map_add, hκ, map_one]
  have hσκA : sigA c (inclA F E (2 : E)⁻¹) = inclA F E (2 : E)⁻¹ := by rw [← hφ, hcκ]
  have heA : hf (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ e) = 0 := by
    rw [hf_map c.toRingHom (sigA c) (inclA F E) hφ, he, map_zero]
  have hffA : hf (sigA c) (J.map (inclA F E)) (inclA F E ∘ f) (inclA F E ∘ f) = 0 := by
    rw [hf_map c.toRingHom (sigA c) (inclA F E) hφ, hff, map_zero]
  have hefA : hf (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ f) = 1 := by
    rw [hf_map c.toRingHom (sigA c) (inclA F E) hφ, hef, map_one]
  obtain ⟨hP1, hP2⟩ := hO
  obtain ⟨-, -, hPE, -⟩ := hP1 E c.toRingHom hc2 N J hJ e f he hff hef
  obtain ⟨-, -, -, hfixA⟩ := hP1 (AE F E) (sigA c) hσA N (J.map (inclA F E)) hJA _ _ heA hffA hefA
  obtain ⟨hPcont, -⟩ := hP2 F E c h2 hc N J e f
  have hcont : Continuous (param (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ f)
      (inclA F E (2 : E)⁻¹)) := by
    have hu : Continuous fun p : (Fin N → AE F E) × AE F E =>
        perpProj (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ f) p.1 :=
      hPcont.comp continuous_fst
    exact continuous_eich hσc _ _ hu ((continuous_snd.sub (hσc.comp continuous_snd)).sub
      (continuous_const.mul (continuous_hf hσc _ hu hu)))
  have hdense : DenseRange (Prod.map (Pi.map fun _ : Fin N => inclA F E) (inclA F E)) :=
    (DenseRange.piMap fun _ => hD F E c h2 hc).prodMap (hD F E c h2 hc)
  intro M hM
  obtain ⟨p, rfl⟩ := eq_param hκA hσκA hfixA hM
  refine map_mem_closure hcont (hdense p) ?_
  rintro _ ⟨⟨w, t⟩, rfl⟩
  exact ⟨param c.toRingHom J e f (2 : E)⁻¹ (w, t), param_mem hc2 hJ hκ hcκ hPE (w, t),
    param_map c.toRingHom (sigA c) (inclA F E) hφ J e f (2 : E)⁻¹ (w, t)⟩

end Field

end EichlerDense

theorem EichlerDense.proof (h₁ : AETopologicalRing.Statement) (h₂ : EDenseInAE.Statement)
    (h₃ : OrthProjection.Statement) : EichlerDense.Statement := by
  intro F E _ _ _ _ _ c h2 hc N J hJ e f he hff hef _ _
  have hfe : hf c.toRingHom J f e = 1 :=
    hf_fe (fun x => EichlerDense.c_invol c h2 hc x) hJ he hff hef
  exact ⟨EichlerDense.along h₁ h₂ h₃ c h2 hc N J hJ e f he hff hef,
    EichlerDense.along h₁ h₂ h₃ c h2 hc N J hJ f e hff he hfe⟩

end StrongApprox

end GroundTheory.Heights₂.Heights
