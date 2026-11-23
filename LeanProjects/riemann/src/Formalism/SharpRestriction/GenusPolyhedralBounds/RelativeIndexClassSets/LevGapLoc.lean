import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapFacts
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLat
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapSplit
import Formalism.LocalRingCardinality.SpanPowerMembership.Adelic
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtB
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelvsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeRes
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

noncomputable section

namespace Formalism.MainNotions.Gaps.LG

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.FrobeniusOrbits
open scoped TensorProduct

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

structure SplitCore (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) where
  φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F
  sig : ∀ x, φ (sigR σ (v.adicCompletion F) x) = swapR _ (φ x)
  alg : ∀ c : v.adicCompletion F, φ ((1 : E) ⊗ₜ[F] c) = (c, c)
  int : ∀ x, x ∈ intV E v ↔ (φ x).1 ∈ v.adicCompletionIntegers F ∧ (φ x).2 ∈ v.adicCompletionIntegers F

def SplitAt.core {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} {a : E} (s : SplitAt σ v a) : SplitCore σ v :=
  ⟨s.φ, s.sig, s.alg, s.int⟩

end Core

section SC

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sc_exists_emb {K : Type} [Field K] [Algebra F K] (sig : E →ₐ[F] E) (hsig : ∀ x, sig (sig x) = x)
    (hfix : ∀ x, sig x = x → ∃ a, algebraMap F E a = x) (b : E) (hb0 : b ≠ 0) (hb : sig b = -b)
    (D : F) (hb2 : b ^ 2 = algebraMap F E D) (r : K) (hr : r ^ 2 = algebraMap F K D) :
    ∃ ψ : E →ₐ[F] K, ψ b = r := by
  have hd : algebraMap F E D = b ^ 2 := hb2.symm
  have h2E : (2 : E) ≠ 0 := two_ne_zero
  have hα : ∀ x, ∃ a, algebraMap F E a = (x + sig x) / 2 := fun x =>
    hfix _ (by rw [map_div₀, map_add, hsig, map_ofNat, add_comm])
  have hβ : ∀ x, ∃ a, algebraMap F E a = (x - sig x) / (2 * b) := fun x =>
    hfix _ (by rw [map_div₀, map_sub, hsig, map_mul, map_ofNat, hb]; field_simp; ring)
  choose α hα using hα
  choose β hβ using hβ
  have inj := (algebraMap F E).injective
  have αm : ∀ x y, α (x * y) = α x * α y + D * (β x * β y) := fun x y => inj (by
    simp only [map_add, map_mul, hα, hβ, hd]; field_simp; ring)
  have βm : ∀ x y, β (x * y) = α x * β y + β x * α y := fun x y => inj (by
    simp only [map_add, map_mul, hα, hβ]; field_simp; ring)
  have αa : ∀ x y, α (x + y) = α x + α y := fun x y => inj (by
    simp only [map_add, hα]; ring)
  have βa : ∀ x y, β (x + y) = β x + β y := fun x y => inj (by
    simp only [map_add, hβ]; ring)
  have αc : ∀ a, α (algebraMap F E a) = a := fun a => inj (by rw [hα, sig.commutes]; ring)
  have βc : ∀ a, β (algebraMap F E a) = 0 := fun a => inj (by rw [hβ, sig.commutes]; simp)
  have αb : α b = 0 := inj (by rw [hα, hb]; simp)
  have βb : β b = 1 := inj (by rw [hβ, hb, map_one]; field_simp; ring)
  have hc : ∀ a, algebraMap F K (α (algebraMap F E a)) + algebraMap F K (β (algebraMap F E a)) * r =
      algebraMap F K a := fun a => by rw [αc, βc]; simp
  refine ⟨{ toFun := fun x => algebraMap F K (α x) + algebraMap F K (β x) * r
            map_one' := by simpa using hc 1
            map_zero' := by simpa using hc 0
            map_mul' := fun x y => by
              rw [αm, βm]
              simp only [map_add, map_mul]
              linear_combination (-(algebraMap F K (β x) * algebraMap F K (β y))) * hr
            map_add' := fun x y => by rw [αa, βa, map_add, map_add]; ring
            commutes' := hc }, ?_⟩
  show algebraMap F K (α b) + algebraMap F K (β b) * r = r
  rw [αb, βb]; simp

theorem sc_exists_iso {K : Type} [Field K] [Algebra F K] (sig : E →ₐ[F] E)
    (h2 : Module.finrank F E = 2) (ψ : E →ₐ[F] K) (b : E) (hb0 : b ≠ 0) (hb : sig b = -b) :
    ∃ φ : E ⊗[F] K ≃+* K × K, ∀ (x : E) (c : K), φ (x ⊗ₜ[F] c) = (c * ψ x, c * ψ (sig x)) := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  let e : K ⊗[F] E →ₐ[K] K × K :=
    Algebra.TensorProduct.lift (Algebra.ofId K (K × K)) (ψ.prod (ψ.comp sig)) (fun _ _ => Commute.all _ _)
  have he : ∀ (a : K) (x : E), e (a ⊗ₜ x) = (a * ψ x, a * ψ (sig x)) := fun a x =>
    Algebra.TensorProduct.lift_tmul _ _ (fun _ _ => Commute.all _ _) a x
  have hr : ψ b ≠ 0 := (map_ne_zero ψ).mpr hb0
  have hsurj : Function.Surjective e := by
    rintro ⟨x, y⟩
    refine ⟨((x + y) / 2) ⊗ₜ 1 + ((x - y) / (2 * ψ b)) ⊗ₜ b, ?_⟩
    have h2K : (2 : K) ≠ 0 := two_ne_zero
    rw [map_add, he, he, hb, map_one sig, map_one ψ, map_neg]
    have aux : ∀ r : K, r ≠ 0 → ((x + y) / 2 * 1 + (x - y) / (2 * r) * r = x ∧
        (x + y) / 2 * 1 + (x - y) / (2 * r) * -r = y) := fun r hr => by
      have h1 : (x - y) / (2 * r) * r = (x - y) / 2 := by
        rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hr]
      have h3 : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2K
      rw [mul_neg, h1, div_eq_mul_inv, div_eq_mul_inv]
      constructor
      · linear_combination x * h3
      · linear_combination y * h3
    exact Prod.ext (aux _ hr).1 (aux _ hr).2
  have hdim : Module.finrank K (K ⊗[F] E) = Module.finrank K (K × K) := by
    rw [Module.finrank_baseChange, h2]; simp
  have hinj : Function.Injective e :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := e.toLinearMap)).mpr hsurj
  refine ⟨(Algebra.TensorProduct.comm F E K).toRingEquiv.trans
    (AlgEquiv.ofBijective e ⟨hinj, hsurj⟩).toRingEquiv, fun x c => ?_⟩
  show e (Algebra.TensorProduct.comm F E K (x ⊗ₜ[F] c)) = _
  rw [Algebra.TensorProduct.comm_tmul, he]

theorem sc_emb_int (v : HeightOneSpectrum (𝓞 F)) (ψ : E →ₐ[F] v.adicCompletion F) (x : 𝓞 E) :
    ψ (x : E) ∈ v.adicCompletionIntegers F := by
  have h1 : IsIntegral ℤ (ψ (x : E)) := (RingOfIntegers.isIntegral_coe x).map ψ
  have h2 : IsIntegral (v.adicCompletionIntegers F) (ψ (x : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := v.adicCompletionIntegers F)
    (K := v.adicCompletion F)).1 h2
  rw [← hy]; exact y.2

theorem sc_val_one (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) (hx : x ∉ v.asIdeal) :
    Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F x)) = 1 := by
  have h := Formalism.UG.P.csApprox_val_int v x
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)] at h
  rw [h]
  exact le_antisymm (v.intValuation_le_one x)
    (not_lt.mp fun h' => hx ((HeightOneSpectrum.intValuation_lt_one_iff_mem v x).mp h'))

theorem sc_val_lt_one (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) (hx : x ∈ v.asIdeal) :
    Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F x)) < 1 := by
  have h := Formalism.UG.P.csApprox_val_int v x
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)] at h
  rw [h]
  exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v x).mpr hx

theorem sc_left_mem (v : HeightOneSpectrum (𝓞 F)) (y : 𝓞 E) :
    (y : E) ⊗ₜ[F] (1 : v.adicCompletion F) ∈ intV E v := Subring.subset_closure (Or.inl ⟨⟨(y : E), y, rfl⟩, rfl⟩)

theorem sc_right_mem (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F)
    (hc : c ∈ v.adicCompletionIntegers F) : (1 : E) ⊗ₜ[F] c ∈ intV E v := Subring.subset_closure (Or.inr ⟨⟨c, hc⟩, rfl⟩)

open Polynomial in

theorem sc_core (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x = x → ∃ a, algebraMap F E a = x) (h2 : Module.finrank F E = 2)
    (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 E) (t N : 𝓞 F)
    (ht : algebraMap F E (t : F) = (a : E) + σ a) (hN : algebraMap F E (N : F) = (a : E) * σ a)
    (hNv : N ∈ v.asIdeal) (htv : t ∉ v.asIdeal) : Nonempty (SplitCore σ v) := by
  let f : Polynomial (v.adicCompletionIntegers F) :=
    X ^ 2 - C (algebraMap (𝓞 F) (v.adicCompletionIntegers F) t) * X +
      C (algebraMap (𝓞 F) (v.adicCompletionIntegers F) N)
  have hf : f.Monic := by
    show (X ^ 2 - C _ * X + C _ : Polynomial (v.adicCompletionIntegers F)).Monic
    monicity!
  have h₁ : f.eval 0 ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    have : f.eval 0 = algebraMap (𝓞 F) (v.adicCompletionIntegers F) N := by simp [f]
    rw [this, Examples₂.adicInt_mem_max_iff]
    exact sc_val_lt_one v N hNv
  have h₂ : IsUnit (f.derivative.eval 0) := by
    have : f.derivative.eval 0 = - algebraMap (𝓞 F) (v.adicCompletionIntegers F) t := by
      simp [f, derivative_pow]
    rw [this]
    exact (Examples₂.adicInt_isUnit_of_not_mem v t htv).neg
  obtain ⟨r, hr, -⟩ := HenselianLocalRing.is_henselian f hf 0 h₁ h₂
  have hr0 : r ^ 2 - algebraMap (𝓞 F) (v.adicCompletionIntegers F) t * r +
      algebraMap (𝓞 F) (v.adicCompletionIntegers F) N = 0 := by
    have := hr
    simpa [f, IsRoot.def] using this
  have hr' : (r : v.adicCompletion F) ^ 2 - algebraMap F (v.adicCompletion F) (t : F) * r +
      algebraMap F (v.adicCompletion F) (N : F) = 0 :=
    congrArg (fun z : v.adicCompletionIntegers F => (z : v.adicCompletion F)) hr0
  have hb : σ ((a : E) - σ a) = -((a : E) - σ a) := by rw [map_sub, hσ]; ring
  have hb2 : ((a : E) - σ a) ^ 2 = algebraMap F E ((t : F) ^ 2 - 4 * (N : F)) := by
    rw [map_sub, map_pow, map_mul, ht, hN, map_ofNat]; ring
  have hρ2 : (2 * (r : v.adicCompletion F) - algebraMap F (v.adicCompletion F) (t : F)) ^ 2 =
      algebraMap F (v.adicCompletion F) ((t : F) ^ 2 - 4 * (N : F)) := by
    rw [map_sub, map_pow, map_mul, map_ofNat]
    linear_combination 4 * hr'
  have hDv : t ^ 2 - 4 * N ∉ v.asIdeal := fun h => by
    have : t ^ 2 ∈ v.asIdeal := by
      have := add_mem h (v.asIdeal.mul_mem_left 4 hNv)
      simpa using this
    exact htv (v.isPrime.mem_of_pow_mem 2 this)
  have hD : Valued.v (algebraMap F (v.adicCompletion F) ((t : F) ^ 2 - 4 * (N : F))) = 1 := by
    have e : (t : F) ^ 2 - 4 * (N : F) = algebraMap (𝓞 F) F (t ^ 2 - 4 * N) := by
      rw [map_sub, map_pow, map_mul, map_ofNat]
    rw [e]; exact sc_val_one v _ hDv
  have hρv : Valued.v (2 * (r : v.adicCompletion F) - algebraMap F (v.adicCompletion F) (t : F)) = 1 := by
    have : Valued.v (2 * (r : v.adicCompletion F) - algebraMap F (v.adicCompletion F) (t : F)) ^ 2 = 1 := by
      rw [← map_pow, hρ2, hD]
    exact (pow_eq_one_iff.1 this).resolve_right two_ne_zero
  have hb0 : (a : E) - σ a ≠ 0 := fun h => by
    rw [h] at hb2
    have h0 : ((t : F) ^ 2 - 4 * (N : F)) = 0 := by
      apply (algebraMap F E).injective
      rw [← hb2]; simp
    rw [h0] at hD
    simp at hD
  obtain ⟨ψ, hψb⟩ := sc_exists_emb σ hσ hfix _ hb0 hb _ hb2 _ hρ2
  obtain ⟨φ, hφ⟩ := sc_exists_iso σ h2 ψ _ hb0 hb
  set ρ := 2 * (r : v.adicCompletion F) - algebraMap F (v.adicCompletion F) (t : F) with hρ
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at hρv; simp at hρv
  refine ⟨⟨φ, fun x => ?_, fun c => ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩⟩
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
    | tmul x c =>
      have : sigR σ (v.adicCompletion F) (x ⊗ₜ[F] c) = σ x ⊗ₜ[F] c := rfl
      rw [this, hφ, hφ, hσ]; rfl
  · rw [hφ]; simp
  · have hle : intV E v ≤ ((v.adicCompletionIntegers F).toSubring.prod
        (v.adicCompletionIntegers F).toSubring).comap φ.toRingHom := by
      refine Subring.closure_le.2 ?_
      rintro _ (⟨⟨_, ⟨y, rfl⟩⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
      · show φ ((algebraMap (𝓞 E) E y) ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ Subring.prod _ _
        have hσy : ∃ y' : 𝓞 E, (y' : E) = σ (y : E) :=
          ⟨⟨σ (y : E), (RingOfIntegers.isIntegral_coe y).map σ⟩, rfl⟩
        obtain ⟨y', hy'⟩ := hσy
        rw [hφ]
        refine ⟨?_, ?_⟩
        · simpa using sc_emb_int v ψ y
        · show (1 : v.adicCompletion F) * ψ (σ (algebraMap (𝓞 E) E y)) ∈ _
          rw [one_mul]
          have := sc_emb_int v ψ y'
          rwa [hy'] at this
      · show φ ((1 : E) ⊗ₜ[F] c) ∈ Subring.prod _ _
        rw [hφ]
        refine ⟨?_, ?_⟩ <;> simpa using hc
    exact hle hx
  · obtain ⟨h1, h2'⟩ := hx
    have hσa : ∃ y' : 𝓞 E, (y' : E) = σ (a : E) :=
      ⟨⟨σ (a : E), (RingOfIntegers.isIntegral_coe a).map σ⟩, rfl⟩
    obtain ⟨a', ha'⟩ := hσa
    have hρi : ρ⁻¹ ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hρv, inv_one]
    have he1 : ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F) - (1 : E) ⊗ₜ[F] ψ (σ a)) * ((1 : E) ⊗ₜ[F] ρ⁻¹) ∈ intV E v := by
      refine mul_mem (sub_mem (sc_left_mem v a) (sc_right_mem v _ ?_)) (sc_right_mem v _ hρi)
      rw [← ha']; exact sc_emb_int v ψ a'
    have hφe : φ (((a : E) ⊗ₜ[F] (1 : v.adicCompletion F) - (1 : E) ⊗ₜ[F] ψ (σ a)) * ((1 : E) ⊗ₜ[F] ρ⁻¹)) = (1, 0) := by
      rw [map_mul, map_sub, hφ, hφ, hφ]
      have hd : ψ (a : E) - ψ (σ a) = ρ := by rw [← map_sub, hψb]
      refine Prod.ext ?_ ?_
      · show (1 * ψ (a : E) - ψ (σ a) * ψ 1) * (ρ⁻¹ * ψ 1) = 1
        rw [map_one, one_mul, mul_one, mul_one, hd, mul_inv_cancel₀ hρ0]
      · show (1 * ψ (σ (a : E)) - ψ (σ a) * ψ (σ 1)) * (ρ⁻¹ * ψ (σ 1)) = 0
        rw [map_one, map_one]; ring
    obtain ⟨e₁, he1, hφe⟩ : ∃ e₁, e₁ ∈ intV E v ∧ φ e₁ = (1, 0) := ⟨_, he1, hφe⟩
    have hx : x = (1 : E) ⊗ₜ[F] (φ x).1 * e₁ + (1 : E) ⊗ₜ[F] (φ x).2 * (1 - e₁) := by
      apply φ.injective
      rw [map_add, map_mul, map_mul, map_sub, map_one, hφe, hφ, hφ]
      refine Prod.ext ?_ ?_
      · show (φ x).1 = (φ x).1 * ψ 1 * 1 + (φ x).2 * ψ 1 * (1 - 1)
        rw [map_one]; ring
      · show (φ x).2 = (φ x).1 * ψ (σ 1) * 0 + (φ x).2 * ψ (σ 1) * (1 - 0)
        rw [map_one, map_one]; ring
    rw [hx]
    exact add_mem (mul_mem (sc_right_mem v _ h1) he1)
      (mul_mem (sc_right_mem v _ h2') (sub_mem (one_mem _) he1))

def SplitCore.swap {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (s : SplitCore σ v) : SplitCore σ v where
  φ := s.φ.trans RingEquiv.prodComm
  sig x := by
    show ((s.φ (sigR σ _ x)).2, (s.φ (sigR σ _ x)).1) = _
    rw [s.sig]; rfl
  alg c := by
    show ((s.φ _).2, (s.φ _).1) = _
    rw [s.alg]
  int x := by
    rw [s.int x, and_comm]; rfl

theorem sc_sig_fst {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (s : SplitCore σ v) (a : E) :
    (s.φ (σ a ⊗ₜ[F] (1 : v.adicCompletion F))).1 = (s.φ (a ⊗ₜ[F] (1 : v.adicCompletion F))).2 := by
  have h := congrArg Prod.fst (s.sig (a ⊗ₜ[F] (1 : v.adicCompletion F)))
  simpa [sigR, swapR] using h

theorem sc_norm {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (s : SplitCore σ v) (a : E) (g : F)
    (h : a * σ a = algebraMap F E g) :
    (s.φ (a ⊗ₜ[F] (1 : v.adicCompletion F))).1 * (s.φ (a ⊗ₜ[F] (1 : v.adicCompletion F))).2 =
      algebraMap F (v.adicCompletion F) g := by
  have h1 : s.φ (a ⊗ₜ[F] (1 : v.adicCompletion F)) * s.φ (σ a ⊗ₜ[F] (1 : v.adicCompletion F)) =
      (algebraMap F (v.adicCompletion F) g, algebraMap F (v.adicCompletion F) g) := by
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, h, ← s.alg]
    congr 1
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have h2 := congrArg Prod.fst h1
  rw [Prod.fst_mul, sc_sig_fst] at h2
  exact h2

theorem sc_orient {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (s : SplitCore σ v) (a : 𝓞 E) (g : 𝓞 F)
    (hg : g ∈ v.asIdeal) (h : (a : E) * σ a = algebraMap F E (g : F)) :
    Nonempty (SplitAt σ v (σ (a : E))) := by
  have hn := sc_norm s (a : E) (g : F) h
  have hi := (s.int _).1 (sc_left_mem v a)
  have hv := sc_val_lt_one v g hg
  have hv' : Valued.v (s.φ ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1 *
      Valued.v (s.φ ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2 < 1 := by
    rw [← map_mul, hn]; exact hv
  by_cases h2 : Valued.v (s.φ ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2 < 1
  · exact ⟨⟨s.φ, s.sig, s.alg, s.int, by rw [sc_sig_fst]; exact h2⟩⟩
  · have h2' : Valued.v (s.φ ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2 = 1 :=
      le_antisymm hi.2 (not_lt.1 h2)
    rw [h2', mul_one] at hv'
    refine ⟨⟨s.swap.φ, s.swap.sig, s.swap.alg, s.swap.int, ?_⟩⟩
    rw [sc_sig_fst]; exact hv'

end SC

section HostSplit

open Formalism.MainNotions.Gaps.LevGap

variable {R : Ranks} (H : Host R)

theorem hs_conj_ne_one : H.conj ≠ 1 := by
  intro h
  have h1 := Examples₂.conj_bE H
  rw [h] at h1
  have h2 := Examples₂.bE_sq H
  have h3 : (H.sqd : H.E) = 0 := by
    have h4 : (H.sqd : H.E) = - H.sqd := h1
    have h5 : (2 : H.E) * H.sqd = 0 := by linear_combination h4
    rcases mul_eq_zero.1 h5 with h6 | h6
    · exact absurd h6 two_ne_zero
    · exact h6
  rw [h3] at h2
  exact (Nat.cast_ne_zero.mpr H.hyp.2.1.ne_zero : (H.d : H.E) ≠ 0) (by simpa using h2.symm)

theorem hs_elt (p : ℕ) (hp : p.Prime)
    (hs : {w : HeightOneSpectrum (𝓞 H.E) | ((p : ℕ) : 𝓞 H.E) ∈ w.asIdeal}.ncard = Module.finrank ℚ H.E)
    (v : HeightOneSpectrum (𝓞 H.F)) (hv : (p : 𝓞 H.F) ∈ v.asIdeal) :
    ∃ (a : 𝓞 H.E) (t N : 𝓞 H.F), algebraMap H.F H.E (t : H.F) = (a : H.E) + Examples₂.conjF H a ∧
      algebraMap H.F H.E (N : H.F) = (a : H.E) * Examples₂.conjF H a ∧ N ∈ v.asIdeal ∧ t ∉ v.asIdeal := by
  obtain ⟨w, rfl⟩ := exists_underPl_eq H.F v
  have hw : (p : 𝓞 H.E) ∈ w.asIdeal := (natCast_mem_underPl H.F w p).1 hv
  have hinj := pullPl_injective p hp hs w hw
  have hne : pullPl H.conj w ≠ pullPl 1 w := fun h => hs_conj_ne_one H (hinj h)
  have hcc : ∀ x : 𝓞 H.E, H.conj • (H.conj • x) = x := fun x =>
    RingOfIntegers.ext (conj_conj H (x : H.E))
  obtain ⟨a, haw, hca⟩ : ∃ a : 𝓞 H.E, a ∈ w.asIdeal ∧ H.conj • a ∉ w.asIdeal := by
    by_contra hcon
    push Not at hcon
    apply hne
    apply HeightOneSpectrum.ext
    ext x
    rw [mem_pullPl, mem_pullPl, one_smul]
    refine ⟨fun h => ?_, fun h => hcon x h⟩
    have := hcon _ h
    rwa [hcc] at this
  have hfix1 : (((a + H.conj • a : 𝓞 H.E)) : H.E) ∈ H.F := by
    rw [mem_F_iff]
    show H.conj ((a : H.E) + H.conj (a : H.E)) = (a : H.E) + H.conj (a : H.E)
    rw [map_add, conj_conj, add_comm]
  have hfix2 : (((a * H.conj • a : 𝓞 H.E)) : H.E) ∈ H.F := by
    rw [mem_F_iff]
    show H.conj ((a : H.E) * H.conj (a : H.E)) = (a : H.E) * H.conj (a : H.E)
    rw [map_mul, conj_conj, mul_comm]
  obtain ⟨t, ht⟩ := exists_int_of_mem H.F _ hfix1
  obtain ⟨N, hN⟩ := exists_int_of_mem H.F _ hfix2
  refine ⟨a, t, N, ?_, ?_, ?_, ?_⟩
  · exact congrArg (fun z : 𝓞 H.E => (z : H.E)) ht
  · exact congrArg (fun z : 𝓞 H.E => (z : H.E)) hN
  · rw [mem_underPl, hN]
    exact Ideal.mul_mem_right _ _ haw
  · rw [mem_underPl, ht]
    intro h
    exact hca ((Ideal.add_mem_iff_right _ haw).1 h)

theorem hs_val (p : ℕ) (hp : p.Prime)
    (hs : {w : HeightOneSpectrum (𝓞 H.E) | ((p : ℕ) : 𝓞 H.E) ∈ w.asIdeal}.ncard = Module.finrank ℚ H.E)
    (v : HeightOneSpectrum (𝓞 H.F)) (hv : (p : 𝓞 H.F) ∈ v.asIdeal) :
    Valued.v ((p : ℕ) : v.adicCompletion H.F) = WithZero.exp (-1 : ℤ) := by
  rw [← map_natCast (algebraMap H.F (v.adicCompletion H.F)), Examples₂.adicCompl_val_algebraMap]
  exact Examples₂.val_eq_of_split H p hp hs v hv

open Ideal in

theorem hs_card (p : ℕ) (hp : p.Prime)
    (hs : {w : HeightOneSpectrum (𝓞 H.E) | ((p : ℕ) : 𝓞 H.E) ∈ w.asIdeal}.ncard = Module.finrank ℚ H.E)
    (v : HeightOneSpectrum (𝓞 H.F)) (hv : (p : 𝓞 H.F) ∈ v.asIdeal) :
    Nat.card (𝓞 H.F ⧸ v.asIdeal) = p := by
  have : IsGaloisGroup Gal(H.E/ℚ) ℤ (𝓞 H.E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ H.E
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (span {(p : ℤ)}).IsPrime := (span_singleton_prime hpZ.ne_zero).2 hpZ
  have hpM : (span {(p : ℤ)}).IsMaximal :=
    hpI.isMaximal (by rw [Ne, span_singleton_eq_bot]; exact hpZ.ne_zero)
  have hne0 : ∀ I : Ideal (𝓞 H.E), I.LiesOver (span {(p : ℤ)}) → I ≠ ⊥ := by
    rintro I hI rfl
    have h0 : span {(p : ℤ)} = ⊥ := by
      rw [hI.over]; exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 H.E))
    exact hpZ.ne_zero (span_singleton_eq_bot.1 h0)
  have himg : (fun w : HeightOneSpectrum (𝓞 H.E) => w.asIdeal) ''
      {w : HeightOneSpectrum (𝓞 H.E) | ((p : ℕ) : 𝓞 H.E) ∈ w.asIdeal} =
      (span {(p : ℤ)}).primesOver (𝓞 H.E) := by
    ext I
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.isPrime, ⟨?_⟩⟩
      have hle : span {(p : ℤ)} ≤ w.asIdeal.under ℤ := by
        rw [span_le, Set.singleton_subset_iff]
        change algebraMap ℤ (𝓞 H.E) p ∈ w.asIdeal
        have hw' : ((p : ℕ) : 𝓞 H.E) ∈ w.asIdeal := hw
        simpa using hw'
      have := w.isPrime
      exact hpM.eq_of_le (Ideal.IsPrime.under ℤ w.asIdeal).ne_top hle
    · rintro ⟨hI, hIl⟩
      refine ⟨⟨I, hI, hne0 I hIl⟩, ?_, rfl⟩
      change ((p : ℕ) : 𝓞 H.E) ∈ I
      have : (p : ℤ) ∈ I.under ℤ := by rw [← hIl.over]; exact mem_span_singleton_self _
      simpa using this
  have key := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (span {(p : ℤ)}) (𝓞 H.E) Gal(H.E/ℚ)
  rw [← himg, Set.ncard_image_of_injective _ (fun v w h => HeightOneSpectrum.ext h), hs,
    IsGalois.card_aut_eq_finrank] at key
  have hpos : 0 < Module.finrank ℚ H.E := Module.finrank_pos
  have hf : inertiaDegIn (span {(p : ℤ)}) (𝓞 H.E) = 1 :=
    Nat.eq_one_of_mul_eq_one_left ((Nat.mul_eq_left hpos.ne').mp key)
  have hvp := v.isPrime
  have hvl : v.asIdeal.LiesOver (span {(p : ℤ)}) := ⟨by
    refine hpM.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top ?_
    rw [span_le, Set.singleton_subset_iff]
    change algebraMap ℤ (𝓞 H.F) p ∈ v.asIdeal
    simpa using hv⟩
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty (v.asIdeal.primesOver (𝓞 H.E)) := inferInstance
  have hPZ : P.LiesOver (span {(p : ℤ)}) := Ideal.LiesOver.trans P v.asIdeal _
  rw [inertiaDegIn_eq_inertiaDeg (span {(p : ℤ)}) P Gal(H.E/ℚ),
    Ideal.inertiaDeg_tower (R := ℤ) v.asIdeal P] at hf
  have h1 : v.asIdeal.inertiaDeg ℤ = 1 := Nat.eq_one_of_mul_eq_one_right hf
  have hvM : v.asIdeal.IsMaximal := v.isMaximal
  have h2 := absNorm_eq_pow_inertiaDeg' (p := p) v.asIdeal hp
  rw [inertiaDeg'_eq_inertiaDeg, h1, pow_one] at h2
  rw [← h2, absNorm_apply, Submodule.cardQuot_apply]

end HostSplit

section IwGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem iw_iwU_le (k : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    iwU F k v ≤ GLint (Fin k) (v.adicCompletionIntegers F).toSubring := by
  rintro x ⟨g, -, rfl⟩
  exact ⟨g, rfl⟩

theorem iw_tmul_mem (v : HeightOneSpectrum (𝓞 F)) (e : 𝓞 E) (c : v.adicCompletionIntegers F) :
    ((e : E) ⊗ₜ[F] (c : v.adicCompletion F)) ∈ intV E v := by
  have h := mul_mem (sc_left_mem (F := F) v e) (sc_right_mem (E := E) v (c : v.adicCompletion F) c.2)
  rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at h

theorem iw_Lb_le_std (k : ℕ) (pz : 𝓞 E) : LbOf k pz ≤ stdLat (n := Fin k) (A := E) (𝓞 E) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  intro j _
  by_cases hij : j = i
  · subst hij
    by_cases h0 : j.1 = 0
    · exact ⟨pz, by simp [lbVec, h0]⟩
    · exact ⟨1, by simp [lbVec, h0]⟩
  · exact ⟨0, by simp [lbVec, hij]⟩

theorem iw_latS_eq (k : ℕ) (pz pzc : 𝓞 E) (T : ℕ) (hpz : (pz : E) * (pzc : E) = (T : E))
    (v : HeightOneSpectrum (𝓞 F)) (hTv : (T : 𝓞 F) ∉ v.asIdeal) :
    latS (F := F) (v.adicCompletion F) (intV E v) (LbOf k pz) =
      latS (F := F) (v.adicCompletion F) (intV E v) (stdLat (n := Fin k) (A := E) (𝓞 E)) := by
  apply le_antisymm
  · exact Submodule.span_mono (Set.image_mono (iw_Lb_le_std k pz))
  · obtain ⟨tu, htu⟩ := Examples₂.adicInt_isUnit_of_not_mem (K := F) v _ hTv
    have hinv : ((T : ℕ) : v.adicCompletion F) * ((tu⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F).1 = 1 := by
      have h1 : (tu : v.adicCompletionIntegers F) * ((tu⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) = 1 :=
        tu.mul_inv
      rw [htu, map_natCast] at h1
      have := congrArg (fun z : v.adicCompletionIntegers F => (z : v.adicCompletion F)) h1
      simpa using this
    set ti : v.adicCompletionIntegers F := ((tu⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) with hti
    have hsm : ∀ (u : intV E v) (y : Fin k → E ⊗[F] v.adicCompletion F) (j : Fin k),
        (u • y) j = (u : E ⊗[F] v.adicCompletion F) * y j := fun _ _ _ => rfl
    have hsingle : ∀ (i : Fin k) (c : 𝓞 E),
        (fun j => inclE (F := F) (v.adicCompletion F) ((Pi.single i (c : E) : Fin k → E) j)) ∈
          latS (F := F) (v.adicCompletion F) (intV E v) (LbOf k pz) := by
      intro i c
      have hgen : (fun j => inclE (F := F) (v.adicCompletion F) (lbVec k pz i j)) ∈
          latS (F := F) (v.adicCompletion F) (intV E v) (LbOf k pz) :=
        Submodule.subset_span ⟨lbVec k pz i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
      by_cases h0 : i.1 = 0
      · have hu := Submodule.smul_mem _ (⟨_, iw_tmul_mem (F := F) v (c * pzc) ti⟩ : intV E v) hgen
        convert hu using 1
        ext j
        by_cases hij : j = i
        · subst hij
          have e1 : (((c * pzc : 𝓞 E) : E) * (pz : E)) = algebraMap F E ((T : ℕ) : F) * (c : E) := by
            rw [map_natCast, ← hpz]; push_cast; ring
          rw [hsm]
          simp only [lbVec, h0, Pi.single_eq_same, if_true, inclE,
            Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
          rw [e1, ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def, map_natCast, hinv]
        · rw [hsm]
          simp [lbVec, hij]
      · have hu := Submodule.smul_mem _ (⟨_, iw_tmul_mem (F := F) v c 1⟩ : intV E v) hgen
        convert hu using 1
        ext j
        by_cases hij : j = i
        · subst hij
          rw [hsm]
          simp [lbVec, h0, inclE]
        · rw [hsm]
          simp [lbVec, hij]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    have hx' : ∀ i, ∃ c : 𝓞 E, (c : E) = x i := fun i => hx i (Set.mem_univ i)
    choose c hc using hx'
    have hsum : (fun j => inclE (F := F) (v.adicCompletion F) (x j)) =
        ∑ i, (fun j => inclE (F := F) (v.adicCompletion F) ((Pi.single i (c i : E) : Fin k → E) j)) := by
      ext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · simp [hc]
      · intro b _ hb
        simp [Pi.single_eq_of_ne (Ne.symm hb)]
      · intro h; exact absurd (Finset.mem_univ j) h
    show (fun j => inclE (F := F) (v.adicCompletion F) (x j)) ∈ _
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => hsingle i (c i)

variable {k : ℕ} (P : Par F E k)

theorem iw_le (hJ : P.J = 1) (pzc : 𝓞 E) (hpz : (P.pz : E) * (pzc : E) = (P.T : E))
    (v : HeightOneSpectrum (𝓞 F)) (hTv : (P.T : 𝓞 F) ∉ v.asIdeal) (s : SplitCore P.σ v) :
    P.iwPre v s.φ ≤ levelVL P.σ P.J v P.Lb := by
  intro x hx
  obtain ⟨hxU, hxI⟩ := hx
  have hG : bc ((RingHom.fst _ _).comp s.φ.toRingHom) x ∈ GLint (Fin k) (v.adicCompletionIntegers F).toSubring :=
    iw_iwU_le k v hxI
  have hu : ∃ u ∈ GLint (Fin k) (v.adicCompletionIntegers F).toSubring,
      (u : Matrix (Fin k) (Fin k) (v.adicCompletion F)) =
        fun i j => (s.φ (inclE (F := F) (v.adicCompletion F) (P.J i j))).1 := by
    refine ⟨1, one_mem _, ?_⟩
    ext i j
    rw [hJ]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have h1 : x ∈ levelV P.σ P.J v :=
    (Formalism.UG.P.level_subgroup_split F E (Fin k) P.σ P.J v s.φ s.sig s.int hu x hxU).2 hG
  rw [← Formalism.UG.P.level_subgroup_local_standard F E (Fin k) P.σ P.J v] at h1
  unfold levelVL at h1 ⊢
  have := iw_latS_eq (F := F) k P.pz pzc P.T hpz v hTv
  unfold Par.Lb
  rw [this]
  exact h1

end IwGen

section IwHost

variable {R : Ranks} (H : Host R)

theorem iw_one_mem {T : ℕ} {pz : 𝓞 H.E} {piG : Fin 2 → 𝓞 H.E} (h : LevHyp H T pz piG) (i : Fin 2)
    (w : Ideal (𝓞 H.E)) (hg : ((H.g i : ℕ) : 𝓞 H.E) ∈ w) (hT : ((T : ℕ) : 𝓞 H.E) ∈ w) :
    (1 : 𝓞 H.E) ∈ w := by
  obtain ⟨pzc, hpzc⟩ := Formalism.MainNotions.Gaps.LevGap.map_int_mem (H.conj : H.E →+* H.E) pz
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h.pz_cong
  obtain ⟨cc, hcc⟩ := Formalism.MainNotions.Gaps.LevGap.map_int_mem (H.conj : H.E →+* H.E) c
  have hM : ((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E) ∈ w := by
    have hd : H.g i ∣ H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 := by
      refine Dvd.dvd.mul_left (Dvd.dvd.trans ?_ (dvd_pow_self _ two_ne_zero)) _
      fin_cases i
      · exact Dvd.intro _ rfl
      · exact Dvd.intro_left _ rfl
    obtain ⟨m, hm⟩ := hd
    rw [hm, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hg
  have h1 : pz - 1 ∈ w := by rw [← hc]; exact Ideal.mul_mem_left _ _ hM
  have h2 : pzc - 1 = cc * ((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E) := by
    apply RingOfIntegers.ext
    have e := congrArg (fun z : 𝓞 H.E => (H.conj : H.E →+* H.E) (z : H.E)) hc
    simp only [map_mul, map_sub, map_one, map_natCast] at e
    have e1 : ((pzc : 𝓞 H.E) : H.E) = (H.conj : H.E →+* H.E) (pz : H.E) := hpzc
    have e2 : ((cc : 𝓞 H.E) : H.E) = (H.conj : H.E →+* H.E) (c : H.E) := hcc
    simp only [map_mul, map_sub, map_one, map_natCast, e1, e2]
    exact e.symm
  have h3 : pzc - 1 ∈ w := by rw [h2]; exact Ideal.mul_mem_left _ _ hM
  have h4 : pz * pzc = ((T : ℕ) : 𝓞 H.E) := by
    apply RingOfIntegers.ext
    have e1 : ((pzc : 𝓞 H.E) : H.E) = H.conj (pz : H.E) := hpzc
    simp only [map_mul, map_natCast, e1]
    exact h.pz_norm
  have h5 : (1 : 𝓞 H.E) = ((T : ℕ) : 𝓞 H.E) - ((pz - 1) * pzc + (pzc - 1)) := by
    rw [← h4]; ring
  rw [h5]
  exact sub_mem hT (add_mem (Ideal.mul_mem_right _ _ h1) h3)

theorem iw_T_ne_g {T : ℕ} {pz : 𝓞 H.E} {piG : Fin 2 → 𝓞 H.E} (h : LevHyp H T pz piG) (i : Fin 2) :
    T ≠ H.g i := by
  intro hT
  have hpos : 0 < {v : HeightOneSpectrum (𝓞 H.E) | ((H.g i : ℕ) : 𝓞 H.E) ∈ v.asIdeal}.ncard := by
    rw [h.g_split i]; exact Module.finrank_pos
  obtain ⟨w, hw⟩ := (Set.ncard_pos (Set.finite_of_ncard_pos hpos)).1 hpos
  have hw' : ((H.g i : ℕ) : 𝓞 H.E) ∈ w.asIdeal := hw
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (iw_one_mem H h i w.asIdeal hw' (hT ▸ hw')))

theorem iw_T_not_mem {T : ℕ} {pz : 𝓞 H.E} {piG : Fin 2 → 𝓞 H.E} (h : LevHyp H T pz piG) (i : Fin 2)
    (v : HeightOneSpectrum (𝓞 H.F)) (hv : (H.g i : 𝓞 H.F) ∈ v.asIdeal) : (T : 𝓞 H.F) ∉ v.asIdeal := by
  intro hT
  have hvp := v.isPrime
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty (v.asIdeal.primesOver (𝓞 H.E)) := inferInstance
  have h1 : ((H.g i : ℕ) : 𝓞 H.E) ∈ P := by
    have := (Ideal.mem_of_liesOver P v.asIdeal _).1 hv
    simpa using this
  have h2 : ((T : ℕ) : 𝓞 H.E) ∈ P := by
    have := (Ideal.mem_of_liesOver P v.asIdeal _).1 hT
    simpa using this
  exact hPp.ne_top ((Ideal.eq_top_iff_one _).2 (iw_one_mem H h i P h1 h2))

end IwHost

theorem factIwLe : FactIwLe := by
  intro R H T pz piG h i v hv s
  obtain ⟨pzc, hpzc⟩ := Formalism.MainNotions.Gaps.LevGap.map_int_mem (H.conj : H.E →+* H.E) pz
  have hpz : (((hostPar H T pz piG).pz : 𝓞 H.E) : H.E) * (pzc : H.E) = (((hostPar H T pz piG).T : ℕ) : H.E) := by
    have e1 : ((pzc : 𝓞 H.E) : H.E) = H.conj (pz : H.E) := hpzc
    rw [e1]; exact h.pz_norm
  exact iw_le (hostPar H T pz piG) rfl pzc hpz v (iw_T_not_mem H h i v hv) s.core

section FM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem fm_card_residue (v : HeightOneSpectrum (𝓞 F)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Nat.card (𝓞 F ⧸ v.asIdeal) := by
  let f : 𝓞 F →+* IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
    (IsLocalRing.residue _).comp (algebraMap (𝓞 F) (v.adicCompletionIntegers F))
  have hs : Function.Surjective f := Examples₂.adicInt_residue_surj (K := F) v
  have hk : RingHom.ker f = v.asIdeal := by
    ext r
    rw [RingHom.mem_ker]
    simp only [f, RingHom.coe_comp, Function.comp_apply, IsLocalRing.residue_eq_zero_iff]
    rw [Examples₂.adicInt_mem_max_iff, HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact v.valuation_lt_one_iff_mem r
  rw [← hk]
  exact (Nat.card_congr (RingHom.quotientKerEquivOfSurjective hs).toEquiv).symm

def fm_swap {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (s : SplitCore σ v) : SplitCore σ v where
  φ := s.φ.trans RingEquiv.prodComm
  sig x := by
    show swapR _ (s.φ (sigR σ _ x)) = swapR _ (swapR _ (s.φ x))
    rw [s.sig]
  alg c := by
    show Prod.swap (s.φ _) = _
    rw [s.alg]; rfl
  int x := by
    rw [s.int x]; exact and_comm

theorem fm_swap_apply {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (s : SplitCore σ v)
    (x : E ⊗[F] v.adicCompletion F) : (fm_swap s).φ x = ((s.φ x).2, (s.φ x).1) := rfl

theorem fm_incl_mem (v : HeightOneSpectrum (𝓞 F)) (c : 𝓞 E) :
    inclE (F := F) (v.adicCompletion F) (c : E) ∈ intV E v := sc_left_mem v c

theorem fm_one_tmul_mem (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletionIntegers F) :
    (1 : E) ⊗ₜ[F] (c : v.adicCompletion F) ∈ intV E v := sc_right_mem v (c : v.adicCompletion F) c.2

theorem fm_mem_latS {n : Type} [Fintype n] [DecidableEq n] (v : HeightOneSpectrum (𝓞 F)) (a : n → E)
    (y : n → E ⊗[F] v.adicCompletion F) :
    y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (LevGap.diagLat a) ↔
      ∀ i, ∃ c : intV E v, y i = inclE (F := F) (v.adicCompletion F) (a i) * (c : E ⊗[F] v.adicCompletion F) := by
  constructor
  · intro hy
    unfold latS at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x0, hx0, rfl⟩ := hx
      intro i
      obtain ⟨c, hc⟩ := LevGap.mem_diagLat.1 hx0 i
      exact ⟨⟨_, fm_incl_mem v c⟩, by simp only [hc, map_mul]⟩
    | zero => intro i; exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro i
      obtain ⟨c, hc⟩ := hx i
      obtain ⟨d, hd⟩ := hy i
      exact ⟨c + d, by simp [hc, hd, mul_add]⟩
    | smul r x _ hx =>
      intro i
      obtain ⟨c, hc⟩ := hx i
      exact ⟨r * c, by
        show (r : E ⊗[F] _) * x i = _
        rw [hc]; push_cast; ring⟩
  · intro h
    choose c hc using h
    have : y = ∑ i, c i • (fun j => inclE (F := F) (v.adicCompletion F) ((Pi.single i (a i) : n → E) j)) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · show y j = (c j : E ⊗[F] v.adicCompletion F) *
          inclE (F := F) (v.adicCompletion F) ((Pi.single j (a j) : n → E) j)
        rw [Pi.single_eq_same, hc j, mul_comm]
      · intro b _ hb
        show (c b : E ⊗[F] v.adicCompletion F) *
          inclE (F := F) (v.adicCompletion F) ((Pi.single b (a b) : n → E) j) = 0
        rw [Pi.single_eq_of_ne hb.symm, map_zero, mul_zero]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, LevGap.single_mem_diagLat a i, rfl⟩)

def fm_pr {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (s : SplitCore σ v) :
    intV E v →+* v.adicCompletionIntegers F :=
  { toFun := fun x => ⟨(s.φ x).1, ((s.int x).1 x.2).1⟩
    map_one' := Subtype.ext (by
      show (s.φ (1 : E ⊗[F] v.adicCompletion F)).1 = 1
      rw [map_one]; rfl)
    map_mul' := fun x y => Subtype.ext (by
      show (s.φ ((x : E ⊗[F] v.adicCompletion F) * y)).1 = (s.φ x).1 * (s.φ y).1
      rw [map_mul]; rfl)
    map_zero' := Subtype.ext (by
      show (s.φ (0 : E ⊗[F] v.adicCompletion F)).1 = 0
      rw [map_zero]; rfl)
    map_add' := fun x y => Subtype.ext (by
      show (s.φ ((x : E ⊗[F] v.adicCompletion F) + y)).1 = (s.φ x).1 + (s.φ y).1
      rw [map_add]; rfl) }

theorem fm_pr_coe {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (s : SplitCore σ v) (x : intV E v) :
    ((fm_pr s x : v.adicCompletionIntegers F) : v.adicCompletion F) = (s.φ x).1 := rfl

def fm_rho {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (s : SplitCore σ v) :
    intV E v →+* IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
  (IsLocalRing.residue _).comp (fm_pr s)

theorem fm_rho_surj {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (s : SplitCore σ v) :
    Function.Surjective (fm_rho s) := by
  intro y
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective y
  refine ⟨⟨(1 : E) ⊗ₜ[F] (c : v.adicCompletion F), sc_right_mem v (c : v.adicCompletion F) c.2⟩, ?_⟩
  show IsLocalRing.residue _ (fm_pr s _) = _
  congr 1
  apply Subtype.ext
  show (s.φ ((1 : E) ⊗ₜ[F] (c : v.adicCompletion F))).1 = c
  rw [s.alg]

theorem fm_rho_eq_zero {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (s : SplitCore σ v) (p : intV E v)
    (h1 : Valued.v (s.φ p).1 = WithZero.exp (-1 : ℤ)) (h2 : Valued.v (s.φ p).2 = 1) (x : intV E v) :
    fm_rho s x = 0 ↔ ∃ z : intV E v, x = p * z := by
  show IsLocalRing.residue _ (fm_pr s x) = 0 ↔ _
  rw [IsLocalRing.residue_eq_zero_iff, Examples₂.adicInt_mem_max_iff, fm_pr_coe]
  constructor
  · intro hx
    have hx' := (Examples₂.wz_lt_one_iff _).1 hx
    have hp1 : (s.φ p).1 ≠ 0 := by
      intro h; rw [h, map_zero] at h1; exact WithZero.exp_ne_zero h1.symm
    have hp2 : (s.φ p).2 ≠ 0 := by
      intro h; rw [h, map_zero] at h2; exact zero_ne_one h2
    let z : E ⊗[F] v.adicCompletion F := s.φ.symm ((s.φ x).1 / (s.φ p).1, (s.φ x).2 / (s.φ p).2)
    have hz : z ∈ intV E v := by
      rw [s.int]
      simp only [z, RingEquiv.apply_symm_apply]
      constructor
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, h1]
        exact div_le_one_of_le₀ hx' zero_le
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, h2, div_one]
        exact ((s.int x).1 x.2).2
    refine ⟨⟨z, hz⟩, Subtype.ext (s.φ.injective ?_)⟩
    show s.φ x = s.φ ((p : E ⊗[F] v.adicCompletion F) * z)
    rw [map_mul]
    simp only [z, RingEquiv.apply_symm_apply]
    apply Prod.ext
    · show (s.φ x).1 = (s.φ p).1 * ((s.φ x).1 / (s.φ p).1)
      rw [mul_div_cancel₀ _ hp1]
    · show (s.φ x).2 = (s.φ p).2 * ((s.φ x).2 / (s.φ p).2)
      rw [mul_div_cancel₀ _ hp2]
  · rintro ⟨z, rfl⟩
    show Valued.v (s.φ ((p : E ⊗[F] v.adicCompletion F) * z)).1 < 1
    rw [map_mul, Prod.fst_mul, map_mul, h1]
    have hz : Valued.v (s.φ z).1 ≤ 1 := ((s.int z).1 z.2).1
    calc WithZero.exp (-1 : ℤ) * Valued.v (s.φ z).1 ≤ WithZero.exp (-1 : ℤ) * 1 := by gcongr
      _ < 1 := by rw [mul_one, Examples₂.wz_lt_one_iff]

variable {k : ℕ} (P : Par F E k)

theorem card_residue_of_uniformizer_valuation (hk : 0 < k) (hJ : P.J = 1) (pzc : 𝓞 E) (hc : (pzc : E) = P.σ (P.pz : E))
    (hz : (P.pz : E) ≠ 0) (v : HeightOneSpectrum (𝓞 F)) (s : SplitCore P.σ v)
    (h1 : Valued.v (s.φ ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1 = WithZero.exp (-1 : ℤ))
    (h2 : Valued.v (s.φ ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2 = 1) :
    Nat.card (P.fM v) = Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := by
  classical
  let i0 : Fin k := ⟨0, hk⟩
  let ι : E →+* E ⊗[F] v.adicCompletion F := inclE (F := F) (E := E) (v.adicCompletion F)
  have hzc : P.σ (P.pz : E) ≠ 0 := (map_ne_zero _).2 hz
  have hinv : ι (P.σ (P.pz : E)) * ι (P.σ (P.pz : E))⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hzc, map_one]
  have hLb : P.LbV v = latS (F := F) (v.adicCompletion F) (intV E v)
      (LevGap.diagLat (LevGap.vecAt i0 (P.pz : E))) := by
    unfold Par.LbV Par.Lb; rw [LevGap.LbOf_eq_latT hk]; rfl
  have hLd : P.LdV v = latS (F := F) (v.adicCompletion F) (intV E v)
      (LevGap.diagLat (LevGap.vecAt i0 (P.σ (P.pz : E))⁻¹)) := by
    unfold Par.LdV; rw [LevGap.Ld_eq hk P hJ hz]
  have memLb : ∀ y, y ∈ P.LbV v ↔ ∀ i, ∃ c : intV E v,
      y i = ι (LevGap.vecAt i0 (P.pz : E) i) * (c : E ⊗[F] v.adicCompletion F) := fun y => by
    rw [hLb]; exact fm_mem_latS v _ y
  have memLd : ∀ y, y ∈ P.LdV v ↔ ∀ i, ∃ c : intV E v,
      y i = ι (LevGap.vecAt i0 (P.σ (P.pz : E))⁻¹ i) * (c : E ⊗[F] v.adicCompletion F) := fun y => by
    rw [hLd]; exact fm_mem_latS v _ y
  let sp : intV E v := ⟨ι (pzc : E), fm_incl_mem v pzc⟩
  have hc0 : ∀ y : P.LdV v, ι (P.σ (P.pz : E)) * y.1 i0 ∈ intV E v := by
    intro y
    obtain ⟨c, hc'⟩ := (memLd y.1).1 y.2 i0
    rw [hc', LevGap.vecAt_same, ← mul_assoc, hinv, one_mul]
    exact c.2
  let c0 : P.LdV v →ₗ[intV E v] intV E v :=
    { toFun := fun y => ⟨ι (P.σ (P.pz : E)) * y.1 i0, hc0 y⟩
      map_add' := fun x y => Subtype.ext (by
        show ι (P.σ (P.pz : E)) * (x.1 i0 + y.1 i0) = ι (P.σ (P.pz : E)) * x.1 i0 + ι (P.σ (P.pz : E)) * y.1 i0
        ring)
      map_smul' := fun r y => Subtype.ext (by
        show ι (P.σ (P.pz : E)) * ((r : E ⊗[F] v.adicCompletion F) * y.1 i0) =
          (r : E ⊗[F] v.adicCompletion F) * (ι (P.σ (P.pz : E)) * y.1 i0)
        ring) }
  let _ : Module (intV E v) (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Module.compHom _ (fm_rho s)
  let ρl : intV E v →ₗ[intV E v] IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
    { toFun := fm_rho s
      map_add' := map_add _
      map_smul' := fun r x => by
        show fm_rho s (r * x) = fm_rho s r * fm_rho s x
        exact map_mul _ _ _ }
  let θ : P.LdV v →ₗ[intV E v] IsLocalRing.ResidueField (v.adicCompletionIntegers F) := ρl.comp c0
  have hθ : ∀ y, θ y = fm_rho s (c0 y) := fun _ => rfl
  have hsm : ∀ (r : intV E v) (y : P.LdV v), θ (r • y) = fm_rho s r * θ y := fun r y => by
    rw [map_smul]; rfl
  have hu0 : (Pi.single i0 (ι (P.σ (P.pz : E))⁻¹) : Fin k → E ⊗[F] v.adicCompletion F) ∈ P.LdV v := by
    rw [memLd]
    intro i
    by_cases hi : i = i0
    · subst hi
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [Pi.single_eq_of_ne hi]⟩
  let u0 : P.LdV v := ⟨_, hu0⟩
  have hc0u : c0 u0 = 1 := Subtype.ext (by
    show ι (P.σ (P.pz : E)) * (Pi.single i0 (ι (P.σ (P.pz : E))⁻¹) : Fin k → E ⊗[F] v.adicCompletion F) i0 = 1
    rw [Pi.single_eq_same, hinv])
  have hsurj : Function.Surjective θ := by
    intro y
    obtain ⟨c, rfl⟩ := fm_rho_surj s y
    refine ⟨c • u0, ?_⟩
    rw [hsm, hθ, hc0u, map_one, mul_one]
  have hzero := fm_rho_eq_zero s (P.pzV v) h1 h2
  have hker : LinearMap.ker θ = P.fKer v := by
    apply le_antisymm
    · intro y hy
      have hy' : fm_rho s (c0 y) = 0 := hy
      obtain ⟨z, hz'⟩ := (hzero _).1 hy'
      have hz'' : ι (P.σ (P.pz : E)) * y.1 i0 = ι (P.pz : E) * (z : E ⊗[F] v.adicCompletion F) :=
        congrArg Subtype.val hz'
      unfold Par.fKer
      rw [Submodule.mem_sup]
      refine ⟨y - P.pzV v • (z • u0), ?_, P.pzV v • (z • u0), ⟨z • u0, rfl⟩, sub_add_cancel _ _⟩
      show (y - P.pzV v • (z • u0)).1 ∈ P.LbV v
      rw [memLb]
      intro i
      have hcoord : (y - P.pzV v • (z • u0)).1 i = y.1 i - ι (P.pz : E) * ((z : E ⊗[F] v.adicCompletion F) *
          (Pi.single i0 (ι (P.σ (P.pz : E))⁻¹) : Fin k → E ⊗[F] v.adicCompletion F) i) := rfl
      rw [hcoord]
      by_cases hi : i = i0
      · subst hi
        refine ⟨0, ?_⟩
        rw [Pi.single_eq_same]
        have : y.1 i0 = ι (P.σ (P.pz : E))⁻¹ * (ι (P.σ (P.pz : E)) * y.1 i0) := by
          rw [← mul_assoc, mul_comm (ι (P.σ (P.pz : E))⁻¹), hinv, one_mul]
        rw [this, hz'']
        simp only [ZeroMemClass.coe_zero, mul_zero]
        ring
      · obtain ⟨c, hc'⟩ := (memLd y.1).1 y.2 i
        refine ⟨c, ?_⟩
        rw [Pi.single_eq_of_ne hi, mul_zero, mul_zero, sub_zero, hc', LevGap.vecAt_ne hi, LevGap.vecAt_ne hi]
    · unfold Par.fKer
      apply sup_le
      · intro y hy
        have hy' : y.1 ∈ P.LbV v := hy
        obtain ⟨c, hc'⟩ := (memLb _).1 hy' i0
        rw [LinearMap.mem_ker, hθ, hzero]
        refine ⟨sp * c, Subtype.ext ?_⟩
        show ι (P.σ (P.pz : E)) * y.1 i0 = ι (P.pz : E) * (ι (pzc : E) * (c : E ⊗[F] v.adicCompletion F))
        rw [hc', LevGap.vecAt_same, hc]
        ring
      · rintro _ ⟨y, rfl⟩
        rw [LinearMap.mem_ker]
        show θ (P.pzV v • y) = 0
        rw [hsm, (hzero _).2 ⟨1, (mul_one _).symm⟩, zero_mul]
  show Nat.card (P.LdV v ⧸ P.fKer v) = _
  rw [← hker]
  exact Nat.card_congr (θ.quotKerEquivOfSurjective hsurj).toEquiv

theorem fm_card (hk : 0 < k) (hJ : P.J = 1) (pzc : 𝓞 E) (hc : (pzc : E) = P.σ (P.pz : E))
    (hpz : (P.pz : E) * P.σ (P.pz : E) = (P.T : E)) (hT : P.T ≠ 0) (v : HeightOneSpectrum (𝓞 F))
    (s : SplitCore P.σ v)
    (hval : Valued.v ((P.T : ℕ) : v.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (hcard : Nat.card (𝓞 F ⧸ v.asIdeal) = P.T) : Nat.card (P.fM v) = P.T := by
  have hz : (P.pz : E) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hpz
    exact hT (by exact_mod_cast hpz.symm)
  have hsw : s.φ ((P.σ (P.pz : E)) ⊗ₜ[F] (1 : v.adicCompletion F)) =
      ((s.φ ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2, (s.φ ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1) :=
    s.sig ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))
  have e1 : ((P.T : ℕ) : E) ⊗ₜ[F] (1 : v.adicCompletion F) = ((P.T : ℕ) : E ⊗[F] v.adicCompletion F) :=
    map_natCast (inclE (F := F) (E := E) (v.adicCompletion F)) P.T
  have e2 : (1 : E) ⊗ₜ[F] ((P.T : ℕ) : v.adicCompletion F) = ((P.T : ℕ) : E ⊗[F] v.adicCompletion F) :=
    map_natCast (Algebra.TensorProduct.includeRight : v.adicCompletion F →ₐ[F] E ⊗[F] v.adicCompletion F) P.T
  have hprod : (s.φ ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1 *
      (s.φ ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2 = ((P.T : ℕ) : v.adicCompletion F) := by
    have h0 : ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((P.σ (P.pz : E)) ⊗ₜ[F] (1 : v.adicCompletion F)) =
        (1 : E) ⊗ₜ[F] ((P.T : ℕ) : v.adicCompletion F) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, hpz, mul_one, e1, e2]
    have h := congrArg s.φ h0
    rw [map_mul, hsw, s.alg] at h
    exact congrArg Prod.fst h
  have hint := (s.int _).1 (P.pzV v).2
  have hv1 : Valued.v (s.φ ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1 ≤ 1 := hint.1
  have hv2 : Valued.v (s.φ ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2 ≤ 1 := hint.2
  have hvp := congrArg Valued.v hprod
  rw [map_mul, hval] at hvp
  rw [← hcard, ← fm_card_residue v]
  by_cases h : Valued.v (s.φ ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1 = 1
  · rw [h, one_mul] at hvp
    exact card_residue_of_uniformizer_valuation P hk hJ pzc hc hz v (fm_swap s) hvp h
  · have h1 := (Examples₂.wz_lt_one_iff _).1 (lt_of_le_of_ne hv1 h)
    have h2 : Valued.v (s.φ ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2 = 1 := by
      by_contra h2
      have h2' := (Examples₂.wz_lt_one_iff _).1 (lt_of_le_of_ne hv2 h2)
      have : WithZero.exp (-1 : ℤ) ≤ WithZero.exp (-1 : ℤ) * WithZero.exp (-1 : ℤ) := by
        calc WithZero.exp (-1 : ℤ) = _ := hvp.symm
          _ ≤ _ := mul_le_mul' h1 h2'
      rw [← WithZero.exp_add, WithZero.exp_le_exp] at this
      omega
    rw [h2, mul_one] at hvp
    exact card_residue_of_uniformizer_valuation P hk hJ pzc hc hz v s hvp h2

end FM

section Final

variable {R : Ranks} (H : Host R)

theorem host_core (p : ℕ) (hp : p.Prime)
    (hs : {w : HeightOneSpectrum (𝓞 H.E) | ((p : ℕ) : 𝓞 H.E) ∈ w.asIdeal}.ncard = Module.finrank ℚ H.E)
    (v : HeightOneSpectrum (𝓞 H.F)) (hv : (p : 𝓞 H.F) ∈ v.asIdeal) : Nonempty (SplitCore (Examples₂.conjF H) v) := by
  obtain ⟨a, t, N, ht, hN, hNv, htv⟩ := hs_elt H p hp hs v hv
  exact sc_core (Examples₂.conjF H) (Examples₂.conjF_conjF H)
    (fun x hx => ⟨⟨x, (Examples₂.conj_eq_self_iff H x).mp hx⟩, rfl⟩) (Examples₂.finrank_FE H) v a t N ht hN hNv htv

end Final

theorem factSplitG : FactSplitG := by
  intro R H T pz piG h i v hv
  obtain ⟨s⟩ := host_core H (H.g i) (H.g_prime i) (h.g_split i) v hv
  refine sc_orient s (piG i) ((H.g i : ℕ) : 𝓞 H.F) hv ?_
  rw [Examples₂.conjF_apply, h.piG_norm i]
  simp

theorem factFMCard : FactFMCard := by
  intro R H T pz piG h v hv
  have hs := Formalism.MainNotions.Gaps.LevGap.T_split_of_levHyp H T pz piG h
  obtain ⟨s⟩ := host_core H T h.T_prime hs v hv
  obtain ⟨pzc, hpzc⟩ := Formalism.MainNotions.Gaps.LevGap.map_int_mem (H.conj : H.E →+* H.E) pz
  exact fm_card (hostPar H T pz piG) (Formalism.MainNotions.Gaps.LevGap.k_pos R) rfl pzc hpzc h.pz_norm h.T_prime.ne_zero v s
    (hs_val H T h.T_prime hs v hv) (hs_card H T h.T_prime hs v hv)

end Formalism.MainNotions.Gaps.LG

end
