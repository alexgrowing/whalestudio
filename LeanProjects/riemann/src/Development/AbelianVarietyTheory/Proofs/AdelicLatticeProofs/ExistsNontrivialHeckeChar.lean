import Mathlib
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsPrimeIdemOfComp
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTensorFiniteAdeleEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom

open HeckeCharacterZeroLocus.ThmBIn NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.HeckeInhabitant

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_arch : ∃ (θ : AE F E →+* ℂ) (τ : E →+* ℂ), Continuous θ ∧ (∀ x, θ (incA F E x) = τ x) ∧
    ∀ α, θ (algebraMap (AF F) (AE F E) (pairA F 0 α)) = 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  letI : Algebra F ℂ := w.embedding.toAlgebra
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  let τ : E →ₐ[F] ℂ := IsAlgClosed.lift
  let g0 : AF F →+* ℂ := (InfinitePlace.Completion.extensionEmbedding w).comp
    ((Pi.evalRingHom (fun u : InfinitePlace F => u.Completion) w).comp (RingHom.fst (Ainf F) (Af F)))
  let g : AF F →ₐ[F] ℂ := ⟨g0, fun x => InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ x)⟩
  let θ : AE F E →+* ℂ := (Algebra.TensorProduct.productMap g τ).toRingHom
  have hθ : ∀ a x, θ (a ⊗ₜ[F] x) = g0 a * τ x := fun a x => rfl
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  refine ⟨θ, τ, ?_, fun x => ?_, fun α => ?_⟩
  · refine IsModuleTopology.continuous_of_ringHom (R := AF F) θ ?_
    have : Continuous g0 := (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
      ((continuous_apply w).comp continuous_fst)
    refine this.congr fun a => ?_
    change _ = θ (a ⊗ₜ[F] 1)
    rw [hθ, map_one, mul_one]
  · change θ (1 ⊗ₜ[F] x) = _
    rw [hθ, map_one, one_mul]; rfl
  · change θ (_ ⊗ₜ[F] 1) = _
    rw [hθ, map_one, mul_one]
    exact map_zero (InfinitePlace.Completion.extensionEmbedding w)

theorem exists_fin : ∃ Φ : AE F E →+* FiniteAdeleRing (𝓞 E) E, Continuous Φ ∧
    (∀ x, Φ (incA F E x) = algebraMap E _ x) ∧
    ∀ y, finPart F E y ∈ intAE F E ↔ ∀ P, Valued.v (Φ y P) ≤ 1 := by
  obtain ⟨ι, h1, h2, -⟩ := GlobalTheory.AdeleBaseChange.exists_tensor_finiteAdele_equiv F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  refine ⟨ι.toRingHom.comp (finPart F E), ?_, fun x => h1 x, fun y => h2 _⟩
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) _ ?_
  have := GlobalTheory.HeckeTensorRead.continuous_of_map_integral
    (ι.toRingHom.comp (algebraMap (Af F) (Af F ⊗[F] E))) (fun a ha P =>
      (h2 (a ⊗ₜ[F] (1 : E))).1 (AddSubgroup.subset_closure ⟨a, ha, 1, rfl⟩) P)
  exact this.comp continuous_snd

theorem cA_base (σ : E →ₐ[F] E) (a : AF F) : cA σ (algebraMap (AF F) (AE F E) a) = algebraMap (AF F) (AE F E) a := by
  change a ⊗ₜ[F] σ 1 = a ⊗ₜ[F] (1 : E)
  rw [map_one]

theorem cA_inc (σ : E →ₐ[F] E) (x : E) : cA σ (incA F E x) = incA F E (σ x) := rfl

theorem cA_cont (σ : E →ₐ[F] E) : Continuous (cA σ) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) _ ?_
  have : Continuous (algebraMap (AF F) (AE F E)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AE F E))
  exact this.congr fun a => (cA_base σ a).symm

theorem cA_int (σ : E →ₐ[F] E) (y : AE F E) (h : finPart F E y ∈ intAE F E) :
    finPart F E (cA σ y) ∈ intAE F E := by
  have e : finPart F E (cA σ y) = sigR (Af F) σ (finPart F E y) := by
    clear h
    induction y using TensorProduct.induction_on with
    | zero => simp only [RingHom.map_zero]
    | add x y hx hy => simp only [RingHom.map_add, hx, hy]
    | tmul a x => rfl
  rw [e]
  generalize finPart F E y = z at h
  induction h using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨a, ha, RingOfIntegers.mapRingHom (σ : E →+* E) x, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem idem_arch {σ : E →ₐ[F] E} {θ : AE F E →+* ℂ} (hθ : ∀ α, θ (algebraMap (AF F) (AE F E) (pairA F 0 α)) = 0)
    {P : HeightOneSpectrum (𝓞 E)} {e f : AE F E} (h : IsPrimeIdem σ P e f) : θ e = 0 ∧ θ (cA σ e) = 0 := by
  rcases h with ⟨⟨⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h3⟩, -⟩, -⟩ | ⟨-, ⟨v, ε, ⟨α, rfl, -⟩, rfl⟩, -⟩
  · have a1 := congrArg θ h1
    have a2 := congrArg θ h2
    have a3 := congrArg θ h3
    rw [hθ, RingHom.map_add] at a3
    rw [RingHom.map_mul] at a1 a2
    rw [RingHom.map_zero] at a2
    have : θ e = 0 := by linear_combination θ e * a3 - a1 - a2
    exact ⟨this, by rw [this, zero_add] at a3; exact a3⟩
  · rw [cA_base]
    exact ⟨hθ α, hθ α⟩

theorem idem_fin {σ : E →ₐ[F] E} {Φ : AE F E →+* FiniteAdeleRing (𝓞 E) E}
    (hι : ∀ x, Φ (incA F E x) = algebraMap E _ x)
    (hint : ∀ y, finPart F E y ∈ intAE F E ↔ ∀ P, Valued.v (Φ y P) ≤ 1)
    {P : HeightOneSpectrum (𝓞 E)} {e f : AE F E} (h : IsPrimeIdem σ P e f) :
    Φ e P = 1 ∧ ∀ Q, Q ≠ P → Φ e Q = 0 := by
  have h' : e * e = e ∧ ∀ x : 𝓞 E, x ≠ 0 →
      (x ∈ P.asIdeal ↔ finPart F E (e * incA F E ((x : E)⁻¹)) ∉ intAE F E) := by
    rcases h with ⟨⟨⟨h1, -⟩, h2⟩, -⟩ | ⟨-, ⟨v, ε, ⟨α, rfl, a1, a0⟩, rfl⟩, h2⟩
    · exact ⟨h1, h2⟩
    · refine ⟨?_, h2⟩
      rw [← map_mul]
      refine congrArg _ (Prod.ext (mul_zero (0 : Ainf F)) (GlobalTheory.PlaceIdem.adele_ext fun u => ?_))
      change evalV F u α * evalV F u α = evalV F u α
      by_cases hu : u = v
      · subst hu; rw [a1, mul_one]
      · rw [a0 u hu, mul_zero]
  obtain ⟨hee, hx⟩ := h'
  obtain ⟨g, hg⟩ : ∃ g, g = Φ e := ⟨_, rfl⟩
  have hgg : g * g = g := by rw [hg, ← RingHom.map_mul, hee]
  have hg01 : ∀ R, g R ≠ 0 → g R = 1 := by
    intro R hR
    have : g R * g R = g R * 1 := by rw [← GlobalTheory.PlaceIdem.mul_ap, hgg, mul_one]
    exact mul_left_cancel₀ hR this
  have key : ∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ ∃ R, g R ≠ 0 ∧ x ∈ R.asIdeal) := by
    intro x hx0
    rw [hx x hx0, hint, RingHom.map_mul, ← hg, hι, not_forall]
    refine exists_congr fun R => ?_
    rw [GlobalTheory.PlaceIdem.mul_ap]
    by_cases hR : g R = 0
    · simp [hR]
    · rw [hg01 R hR, one_mul, GlobalTheory.PlaceIdem.val_inv_le_one R hx0]
      simp
  have h0 : ∀ Q, Q ≠ P → g Q = 0 := by
    intro Q hQ
    by_contra hne
    refine hQ (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top fun x hxQ => ?_))
    by_cases hx0 : x = 0
    · rw [hx0]; exact zero_mem _
    · exact (key x hx0).2 ⟨Q, hne, hxQ⟩
  rw [← hg]
  refine ⟨?_, h0⟩
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  obtain ⟨R, hR, -⟩ := (key x hx0).1 hxP
  by_cases hRP : R = P
  · subst hRP
    exact hg01 _ hR
  · exact absurd (h0 R hRP) hR

theorem val_alg (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    Valued.v (algebraMap E (FiniteAdeleRing (𝓞 E) E) x P) = P.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P x

theorem unif_val {σ : E →ₐ[F] E} {Φ : AE F E →+* FiniteAdeleRing (𝓞 E) E}
    (hι : ∀ x, Φ (incA F E x) = algebraMap E _ x)
    (hint : ∀ y, finPart F E y ∈ intAE F E ↔ ∀ P, Valued.v (Φ y P) ≤ 1)
    {P : HeightOneSpectrum (𝓞 E)} {π : 𝓞 E} (hπ : P.asIdeal = Ideal.span {π}) {x : (AE F E)ˣ}
    (h : IsUnifIdele σ P x) (Q : HeightOneSpectrum (𝓞 E)) :
    Valued.v (Φ (x : AE F E) Q) = Q.valuation E (π : E) := by
  obtain ⟨e, f, ϖ, he, h1, h2, hx⟩ := h
  obtain ⟨d1, d0⟩ := idem_fin hι hint he
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact P.ne_bot (by rw [hπ]; simp)
  have e1 : Φ (x : AE F E) Q = Φ e Q * algebraMap E (FiniteAdeleRing (𝓞 E) E) (ϖ : E) Q + (1 - Φ e Q) := by
    rw [hx, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hι]
    rfl
  have e2 : ∀ y : 𝓞 E, Q.valuation E (y : E) = Q.intValuation y := fun y => HeightOneSpectrum.valuation_of_algebraMap Q y
  rw [e1, e2]
  by_cases hQ : Q = P
  · subst hQ
    rw [d1, one_mul, sub_self, add_zero, val_alg, e2, HeightOneSpectrum.intValuation_singleton Q hπ0 hπ]
    have a1 := (HeightOneSpectrum.intValuation_le_pow_iff_mem Q ϖ 1).2 (by rwa [pow_one])
    have a2 := mt (HeightOneSpectrum.intValuation_le_pow_iff_mem Q ϖ 2).1 h2
    have a0 : Q.intValuation ϖ ≠ 0 := fun h => a2 (by rw [h]; exact zero_le)
    rw [← WithZero.exp_log a0] at a1 a2 ⊢
    rw [WithZero.exp_le_exp] at a1 a2
    congr 1
    omega
  · rw [d0 Q hQ, zero_mul, zero_add, sub_zero, map_one, eq_comm, HeightOneSpectrum.intValuation_eq_one_iff]
    intro hm
    refine hQ (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top ?_).symm)
    rw [hπ, Ideal.span_singleton_le_iff_mem]
    exact hm

theorem exists_char (σ : E →ₐ[F] E) {k : ℕ} (hk : ∀ u : (𝓞 E)ˣ, u ^ k = 1)
    {θ : AE F E →+* ℂ} {τ : E →+* ℂ} (hθc : Continuous θ) (hθ : ∀ x, θ (incA F E x) = τ x)
    {Φ : AE F E →+* FiniteAdeleRing (𝓞 E) E} (hΦc : Continuous Φ)
    (hι : ∀ x, Φ (incA F E x) = algebraMap E _ x)
    (hint : ∀ y, finPart F E y ∈ intAE F E ↔ ∀ P, Valued.v (Φ y P) ≤ 1) :
    ∃ χ : (AE F E)ˣ →* Circle, IsHeckeChar F E χ ∧ (∀ a : (AF F)ˣ, χ (idF F E a) = 1) ∧
      ∀ x : (AE F E)ˣ, finPart F E (x : AE F E) ∈ intAE F E → finPart F E ((x⁻¹ : (AE F E)ˣ) : AE F E) ∈ intAE F E →
        (χ x : ℂ) = (θ x / θ (cA σ x) / star (θ x / θ (cA σ x))) ^ k := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  let S : Submonoid (AE F E) :=
    { carrier := {z | ∀ P, Valued.v (Φ z P) ≤ 1}
      one_mem' := fun P => by
        rw [RingHom.map_one]
        exact (map_one (Valued.v : Valuation (P.adicCompletion E) _)).le
      mul_mem' := fun {a b} ha hb P => by
        rw [RingHom.map_mul, GlobalTheory.PlaceIdem.mul_ap, map_mul]
        exact mul_le_one' (ha P) (hb P) }
  have hO : IsOpen {a : FiniteAdeleRing (𝓞 E) E | ∀ v, a v ∈ v.adicCompletionIntegers E} :=
    RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  have hS : IsOpen (S : Set (AE F E)) := hO.preimage hΦc
  let t : (AE F E)ˣ →* ℂˣ := Units.map θ.toMonoidHom
  let b : ℂˣ →* ℂˣ := Units.map (starRingEnd ℂ).toMonoidHom
  let ψ : (AE F E)ˣ →* ℂˣ := (t / b.comp t) ^ k
  have hψ : ∀ x, ((ψ x : ℂˣ) : ℂ) = (θ x / star (θ x)) ^ k := fun x => by
    change (((t x / b (t x)) ^ k : ℂˣ) : ℂ) = _
    rw [Units.val_pow_eq_pow_val, Units.val_div_eq_div_val]
    rfl
  have ht : Continuous t := Continuous.units_map _ hθc
  have hb : Continuous b := Continuous.units_map _ Complex.continuous_conj
  have hψc : Continuous ψ := (ht.div' (hb.comp ht)).pow k
  let α : Eˣ →* (AE F E)ˣ := Units.map (incA F E).toMonoidHom
  obtain ⟨ν, hν, hνu, hνU, hν1⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (AE F E)ˣ Eˣ S.units
    (Submonoid.isOpen_units hS) α 1 ψ hψc
    (fun x => by
      have : θ x ≠ 0 := (t x).ne_zero
      rw [hψ, norm_pow, norm_div, norm_star, div_self (norm_ne_zero_iff.2 this), one_pow])
    (fun _ => by simp)
    (fun y hy => by
      obtain ⟨h1, h2⟩ := (Submonoid.mem_units_iff _ _).1 hy
      obtain ⟨p, hp⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E (y : E) (R := 𝓞 E) fun P => by
        rw [← val_alg, ← hι]; exact h1 P
      obtain ⟨q, hq⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E ((y⁻¹ : Eˣ) : E) (R := 𝓞 E) fun P => by
        rw [← val_alg, ← hι]; exact h2 P
      have hpq : p * q = 1 := by
        apply FaithfulSMul.algebraMap_injective (𝓞 E) E
        rw [map_mul, hp, hq, map_one, Units.mul_inv]
      have h3 := congrArg (fun u : (𝓞 E)ˣ => τ (algebraMap (𝓞 E) E u)) (hk (Units.mkOfMulEqOne p q hpq))
      simp only [Units.val_pow_eq_pow_val, Units.val_mkOfMulEqOne, map_pow, hp, Units.val_one, map_one] at h3
      apply Units.ext
      rw [hψ]
      change (1 : ℂ) = (θ (incA F E y) / star (θ (incA F E y))) ^ k
      rw [hθ, div_pow, ← star_pow, h3, star_one, div_one])
  let C : (AE F E)ˣ →* (AE F E)ˣ := Units.map (cA σ).toMonoidHom
  have hC : Continuous C := Continuous.units_map _ (cA_cont σ)
  let μ : (AE F E)ˣ →* ℂˣ := ν.comp (MonoidHom.id _ / C)
  have hμ : ∀ x, μ x = ν (x / C x) := fun x => rfl
  have hμc : Continuous μ := hν.comp (continuous_id.div' hC)
  refine ⟨GlobalTheory.unitaryCharToCircle μ fun x => hνu _,
    ⟨Continuous.subtype_mk (Units.continuous_val.comp hμc) _, fun x => Circle.ext ?_⟩, fun a => Circle.ext ?_,
    fun x h1 h2 => ?_⟩
  · change ((ν (α x / C (α x)) : ℂˣ) : ℂ) = 1
    have : C (α x) = α (Units.map (σ : E →+* E).toMonoidHom x) := Units.ext rfl
    rw [this, ← map_div, hν1]
    rfl
  · change ((ν (idF F E a / C (idF F E a)) : ℂˣ) : ℂ) = 1
    have : C (idF F E a) = idF F E a := Units.ext (cA_base σ a)
    rw [this, div_self', map_one]
    rfl
  · change ((ν (x / C x) : ℂˣ) : ℂ) = _
    have m1 : x ∈ S.units := (Submonoid.mem_units_iff _ _).2 ⟨(hint _).1 h1, (hint _).1 h2⟩
    have m2 : C x ∈ S.units := (Submonoid.mem_units_iff _ _).2 ⟨(hint _).1 (cA_int σ _ h1), (hint _).1 (cA_int σ _ h2)⟩
    have e : θ ((x / C x : (AE F E)ˣ) : AE F E) = θ x / θ (cA σ x) := by
      change ((t (x / C x) : ℂˣ) : ℂ) = _
      rw [map_div, Units.val_div_eq_div_val]
      rfl
    rw [hνU _ (div_mem m1 m2), hψ, e]

theorem exists_of_principal (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) [IsPrincipalIdealRing (𝓞 E)] {k : ℕ}
    (hk : ∀ u : (𝓞 E)ˣ, u ^ k = 1) (a : 𝓞 E) (ha : σ (a : E) ^ (2 * k) ≠ (a : E) ^ (2 * k)) :
    ∃ χ : (AE F E)ˣ →* Circle, IsHeckeChar F E χ ∧ (∀ a : (AF F)ˣ, χ (idF F E a) = 1) ∧ χ ≠ 1 ∧
      ∃ P : HeightOneSpectrum (𝓞 E), chiAt σ χ P ≠ 0 ∧ chiAt σ χ P ≠ 1 := by
  obtain ⟨θ, τ, hθc, hθ, hθ0⟩ := exists_arch (F := F) (E := E)
  obtain ⟨Φ, hΦc, hι, hint⟩ := exists_fin (F := F) (E := E)
  obtain ⟨χ, hχ, hχF, hχU⟩ := exists_char σ hk hθc hθ hΦc hι hint
  obtain ⟨π, hπ, hne⟩ : ∃ π : 𝓞 E, Prime π ∧ σ (π : E) ^ (2 * k) ≠ (π : E) ^ (2 * k) := by
    by_contra hc
    push Not at hc
    refine ha (UniqueFactorizationMonoid.induction_on_prime
      (P := fun b : 𝓞 E => σ (b : E) ^ (2 * k) = (b : E) ^ (2 * k)) a ?_ ?_ ?_)
    · change σ 0 ^ _ = 0 ^ _
      rw [map_zero]
    · rintro x ⟨u, rfl⟩
      have h3 := congrArg (fun u : (𝓞 E)ˣ => algebraMap (𝓞 E) E u) (hk u)
      simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at h3
      change σ (algebraMap (𝓞 E) E u) ^ _ = (algebraMap (𝓞 E) E u) ^ _
      rw [← map_pow, pow_mul', h3, one_pow, map_one]
    · intro b p _ hp hb
      change σ ((p : E) * b) ^ _ = ((p : E) * b) ^ _
      rw [map_mul, mul_pow, mul_pow, hb, hc p hp]
  let P : HeightOneSpectrum (𝓞 E) :=
    ⟨Ideal.span {π}, (Ideal.span_singleton_prime hπ.ne_zero).2 hπ, by simpa using hπ.ne_zero⟩
  have hex : ∃ x, IsUnifIdele σ P x := by
    by_contra hc
    have := GlobalTheory.CMPrimeIdele.chiAt_one F E σ hσ P
    rw [chiAt, dif_neg fun h => hc h.2] at this
    exact zero_ne_one this
  have harch : ∀ {e f z : AE F E} {x : AE F E}, IsPrimeIdem σ P e f → x = e * z + (1 - e) →
      θ x = 1 ∧ θ (cA σ x) = 1 := by
    intro e f z x he hx
    obtain ⟨d1, d2⟩ := idem_arch hθ0 he
    constructor
    · rw [hx, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, d1]; ring
    · rw [hx]
      simp only [RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, d2]; ring
  have hunr : IsUnramAt σ χ P := by
    obtain ⟨x, e, f, ϖ, he, -⟩ := hex
    refine ⟨e, f, he, fun y hy h1 h2 => Circle.ext ?_⟩
    obtain ⟨d1, d2⟩ := harch he hy
    rw [hχU y h1 h2, d1, d2]
    simp
  have hval : ∀ x, IsUnifIdele σ P x → χ x ≠ 1 := by
    intro x hx h1
    have hπ0 : (π : E) ≠ 0 := by exact_mod_cast hπ.ne_zero
    let p : (AE F E)ˣ := Units.map (incA F E).toMonoidHom (Units.mk0 (π : E) hπ0)
    have hv := unif_val hι hint (P := P) (π := π) rfl hx
    obtain ⟨e, f, ϖ, he, -, -, hx⟩ := hx
    obtain ⟨d1, d2⟩ := harch he hx
    have hp : ∀ Q : HeightOneSpectrum (𝓞 E), Valued.v (Φ (p : AE F E) Q) = Q.valuation E (π : E) := fun Q => by
      change Valued.v (Φ (incA F E (π : E)) Q) = _
      rw [hι, val_alg]
    have hq : ∀ y z : (AE F E)ˣ, (∀ Q : HeightOneSpectrum (𝓞 E), Valued.v (Φ (y : AE F E) Q) = Q.valuation E (π : E)) →
        (∀ Q : HeightOneSpectrum (𝓞 E), Valued.v (Φ (z : AE F E) Q) = Q.valuation E (π : E)) →
        finPart F E ((y / z : (AE F E)ˣ) : AE F E) ∈ intAE F E := by
      intro y z hy hz
      refine (hint _).2 fun Q => le_of_eq ?_
      have h2 := hy Q
      rw [← div_mul_cancel y z, Units.val_mul, RingHom.map_mul, GlobalTheory.PlaceIdem.mul_ap, map_mul, hz] at h2
      have h0 : Q.valuation E (π : E) ≠ 0 := by simpa using hπ0
      exact mul_right_cancel₀ h0 (h2.trans (one_mul _).symm)
    have h2 := hχU (p / x) (hq _ _ hp hv) (by rw [inv_div]; exact hq _ _ hv hp)
    have h3 : θ ((p / x : (AE F E)ˣ) : AE F E) = τ π := by
      have := congrArg (fun y : (AE F E)ˣ => θ (y : AE F E)) (div_mul_cancel p x)
      simp only [Units.val_mul, RingHom.map_mul, d1, mul_one] at this
      exact this.trans (hθ _)
    have h4 : θ (cA σ ((p / x : (AE F E)ˣ) : AE F E)) = star (τ π) := by
      have := congrArg (fun y : (AE F E)ˣ => θ (cA σ (y : AE F E))) (div_mul_cancel p x)
      simp only [Units.val_mul, RingHom.map_mul, d2, mul_one] at this
      exact this.trans ((hθ (σ π)).trans (hσ.2.2.2 τ _))
    have h5 : χ p = 1 := hχ.2 _
    rw [map_div, h5, h1, div_one, h3, h4] at h2
    have t0 : τ π ≠ 0 := by simpa using hπ0
    have t1 : star (τ π) ≠ 0 := by simpa using hπ0
    apply hne
    apply τ.injective
    rw [map_pow, map_pow, hσ.2.2.2, eq_comm, ← div_eq_one_iff_eq (pow_ne_zero _ t1), ← div_pow, pow_mul]
    rw [star_div₀, star_star] at h2
    refine Eq.trans ?_ h2.symm
    congr 1
    field_simp
  have hc : chiAt σ χ P = ((χ hex.choose : Circle) : ℂ) := by
    rw [chiAt, dif_pos ⟨hunr, hex⟩]
  refine ⟨χ, hχ, hχF, fun h => hval _ hex.choose_spec (by rw [h]; rfl), P, ?_, ?_⟩
  · rw [hc]; exact Circle.coe_ne_zero _
  · rw [hc]; exact fun h => hval _ hex.choose_spec (Circle.ext h)

end General

theorem exists_nontrivial_heckeChar : ∃ (F E : Type) (_ : Field F) (_ : NumberField F) (_ : Field E) (_ : NumberField E) (_ : Algebra F E) (σ : E →ₐ[F] E), IsCMExt F E σ ∧ ∃ χ : (AE F E)ˣ →* Circle, IsHeckeChar F E χ ∧ (∀ a : (AF F)ˣ, χ (idF F E a) = 1) ∧ χ ≠ 1 ∧ ∃ P : HeightOneSpectrum (𝓞 E), chiAt σ χ P ≠ 0 ∧ chiAt σ χ P ≠ 1 := by
  let K := CyclotomicField 3 ℚ
  haveI : IsCMField K := IsCyclotomicExtension.Rat.isCMField K (S := {3}) ⟨3, rfl, by norm_num⟩
  haveI := IsCyclotomicExtension.Rat.three_pid K
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let σ : K →ₐ[maximalRealSubfield K] K := IsCMField.complexConj K
  have hσ : IsCMExt (maximalRealSubfield K) K σ :=
    ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
      fun τ x => IsCMField.complexEmbedding_complexConj K τ x⟩
  refine ⟨maximalRealSubfield K, K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, σ, hσ,
    exists_of_principal σ hσ (k := 6) (fun u => ?_) (3 + hζ.toInteger) ?_⟩
  · have hu := IsCyclotomicExtension.Rat.Three.Units.mem hζ u
    generalize hη : (IsUnit.unit _ : (𝓞 K)ˣ) = η at hu
    have h3 : η ^ 3 = 1 := by
      apply Units.ext
      rw [← hη, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
      exact hζ.toInteger_isPrimitiveRoot.pow_eq_one
    have h6 : η ^ 6 = 1 := by rw [show 6 = 3 * 2 from rfl, pow_mul, h3, one_pow]
    have ev : Even 6 := by decide
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [ev.neg_pow, one_pow, h6, pow_right_comm _ 2 6]
  · obtain ⟨ζ, hz⟩ : ∃ ζ, ζ = IsCyclotomicExtension.zeta 3 ℚ K := ⟨_, rfl⟩
    change σ (3 + IsCyclotomicExtension.zeta 3 ℚ K) ^ _ ≠ (3 + IsCyclotomicExtension.zeta 3 ℚ K) ^ _
    rw [← hz] at hζ ⊢
    have h1 : ζ ^ 2 = -1 - ζ := by
      have := hζ.geom_sum_eq_zero (by norm_num)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
      linear_combination this
    have a2 : (3 + ζ) ^ 2 = 8 + 5 * ζ := by linear_combination h1
    have a4 : (8 + 5 * ζ) ^ 2 = 39 + 55 * ζ := by linear_combination 25 * h1
    have a8 : (39 + 55 * ζ) ^ 2 = -1504 + 1265 * ζ := by linear_combination 3025 * h1
    have a12 : (3 + ζ) ^ (2 * 6) = -128231 - 102960 * ζ := by
      rw [show 2 * 6 = 2 * 2 * 3 from rfl, pow_mul, pow_mul, a2, a4, pow_succ, a8]
      linear_combination 69575 * h1
    intro h
    rw [← map_pow, a12, map_sub, map_mul, map_neg, map_ofNat, map_ofNat] at h
    have h2 : σ ζ = ζ := by linear_combination (-1 / 102960 : K) * h
    obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have h3 := hσ.2.2.2 τ ζ
    rw [h2] at h3
    have h4 := congrArg τ h1
    rw [map_pow, map_sub, map_neg, map_one] at h4
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h3.symm
    rw [hr] at h4
    have h5 : r ^ 2 = -1 - r := by exact_mod_cast h4
    nlinarith [sq_nonneg (2 * r + 1)]

end GlobalTheory.HeckeInhabitant
