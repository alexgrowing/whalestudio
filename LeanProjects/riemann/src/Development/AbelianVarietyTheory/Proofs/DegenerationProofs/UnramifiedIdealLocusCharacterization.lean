import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Imports
open TensorProduct MvPolynomial
noncomputable section
namespace GlobalTheory.SS.Dil

theorem exists_lift {R B S W : Type} [CommRing R] [CommRing B] [CommRing S] [Algebra R B] [Algebra B S]
    [AddCommGroup W] [Module S W] (D : B → W) (ha : ∀ x y, D (x + y) = D x + D y)
    (hm : ∀ x y, D (x * y) = algebraMap B S x • D y + algebraMap B S y • D x)
    (hr : ∀ r, D (algebraMap R B r) = 0) :
    ∃ l : S ⊗[B] (KaehlerDifferential R B) →ₗ[S] W, ∀ b, l (1 ⊗ₜ KaehlerDifferential.D R B b) = D b := by
  letI : Module B W := Module.compHom W (algebraMap B S)
  letI : Module R W := Module.compHom W ((algebraMap B S).comp (algebraMap R B))
  have e1 : ∀ (b : B) (w : W), b • w = algebraMap B S b • w := fun _ _ => rfl
  have e2 : ∀ (b : R) (w : W), b • w = algebraMap B S (algebraMap R B b) • w := fun _ _ => rfl
  haveI : IsScalarTower R B W := ⟨fun r b w => by
    rw [e2, e1, e1, Algebra.smul_def, map_mul, mul_smul]⟩
  haveI : IsScalarTower B S W := ⟨fun r b w => by
    rw [e1, Algebra.smul_def, mul_smul]⟩
  let L : B →ₗ[R] W :=
    { toFun := D
      map_add' := ha
      map_smul' := fun r x => by
        rw [Algebra.smul_def, hm, hr, smul_zero, add_zero, RingHom.id_apply, e2] }
  let d : Derivation R B W := Derivation.mk' L (fun x y => hm x y)
  refine ⟨LinearMap.liftBaseChange S d.liftKaehlerDifferential, fun b => ?_⟩
  rw [LinearMap.liftBaseChange_tmul, one_smul, Derivation.liftKaehlerDifferential_comp_D]
  rfl

theorem span_d (R B S : Type) [CommRing R] [CommRing B] [CommRing S] [Algebra R B] [Algebra B S]
    (Q : Submodule S (S ⊗[B] (KaehlerDifferential R B))) (h : ∀ b, (1 : S) ⊗ₜ[B] KaehlerDifferential.D R B b ∈ Q) :
    ∀ x, x ∈ Q := by
  have h1 : ∀ ω : KaehlerDifferential R B, (1 : S) ⊗ₜ[B] ω ∈ Q := by
    intro ω
    have : ω ∈ Submodule.span B (Set.range (KaehlerDifferential.D R B)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction this using Submodule.span_induction with
    | mem x hx => obtain ⟨b, rfl⟩ := hx; exact h b
    | zero => simp
    | add x y _ _ hx hy => rw [tmul_add]; exact Q.add_mem hx hy
    | smul b x _ hx =>
      rw [tmul_smul, ← algebraMap_smul S b]; exact Q.smul_mem _ hx
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact Q.zero_mem
  | tmul s ω =>
    have := Q.smul_mem s (h1 ω)
    rwa [smul_tmul', smul_eq_mul, mul_one] at this
  | add x y hx hy => exact Q.add_mem hx hy

def dd (R B S : Type) [CommRing R] [CommRing B] [CommRing S] [Algebra R B] [Algebra B S] (b : B) :
    S ⊗[B] (KaehlerDifferential R B) := (1 : S) ⊗ₜ[B] KaehlerDifferential.D R B b

section
variable {R B S : Type} [CommRing R] [CommRing B] [CommRing S] [Algebra R B] [Algebra B S]
theorem dd_add (x y : B) : dd R B S (x + y) = dd R B S x + dd R B S y := by
  simp [dd, tmul_add]
theorem dd_mul (x y : B) :
    dd R B S (x * y) = algebraMap B S x • dd R B S y + algebraMap B S y • dd R B S x := by
  simp [dd, tmul_add]
theorem dd_algebraMap (r : R) : dd R B S (algebraMap R B r) = 0 := by
  simp [dd]
theorem dd_zero : dd R B S 0 = 0 := by
  simp [dd]
end

theorem chain {R S W : Type} {n : ℕ} [CommRing R] [CommRing S] [AddCommGroup W] [Module S W]
    (σ : MvPolynomial (Fin n) R →+* S) (D : MvPolynomial (Fin n) R → W) (ha : ∀ x y, D (x + y) = D x + D y)
    (hm : ∀ x y, D (x * y) = σ x • D y + σ y • D x) (hr : ∀ r, D (C r) = 0) (p : MvPolynomial (Fin n) R) :
    D p = ∑ i, σ (pderiv i p) • D (X i) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [hr]
  | add p q hp hq => simp [ha, hp, hq, add_smul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    rw [hm, hp]
    have : ∀ i, σ (pderiv i (p * X j)) • D (X i) =
        (if i = j then σ p • D (X j) else 0) + σ (X j) • σ (pderiv i p) • D (X i) := by
      intro i
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, add_smul, mul_smul, mul_smul]
      by_cases h : i = j
      · subst h; simp
      · rw [pderiv_X_of_ne (Ne.symm h)]; simp [h]
    simp only [this, Finset.sum_add_distrib, Finset.smul_sum]
    simp

def gr {R S : Type} {n : ℕ} [CommRing R] [CommRing S] (σ : MvPolynomial (Fin n) R →+* S)
    (p : MvPolynomial (Fin n) R) : Fin n → S := fun i => σ (pderiv i p)

section
variable {R S : Type} {n : ℕ} [CommRing R] [CommRing S] (σ : MvPolynomial (Fin n) R →+* S)
theorem gr_add (x y) : gr σ (x + y) = gr σ x + gr σ y := by
  funext i; simp [gr]
theorem gr_sub (x y) : gr σ (x - y) = gr σ x - gr σ y := by
  funext i; simp [gr]
theorem gr_mul (x y) : gr σ (x * y) = σ x • gr σ y + σ y • gr σ x := by
  funext i; simp [gr]
theorem gr_C (x) : gr σ (C x) = 0 := by
  funext i; simp [gr]
theorem gr_zero : gr σ 0 = 0 := by
  funext i; simp [gr]
theorem gr_sum (f : Fin n → MvPolynomial (Fin n) R) : gr σ (∑ j, f j) = ∑ j, gr σ (f j) := by
  funext i; simp [gr]
theorem gr_X (j) : gr σ (X j) = Pi.single j 1 := by
  funext i
  by_cases h : i = j
  · subst h; simp [gr]
  · simp [gr, pderiv_X_of_ne (Ne.symm h), h]
end

theorem ker_le {R B S : Type} {n : ℕ} [CommRing R] [CommRing B] [CommRing S] [Algebra R B] [Algebra B S]
    (q : MvPolynomial (Fin n) R →ₐ[R] B) (hq : Function.Surjective q) (σ : MvPolynomial (Fin n) R →+* S)
    (hσ : ∀ p, σ p = algebraMap B S (q p)) (N : Submodule S (Fin n → S)) (hN : ∀ f, q f = 0 → gr σ f ∈ N)
    (u : Fin n → S) (hu : ∑ i, u i • dd R B S (q (X i)) = 0) : u ∈ N := by
  let D : B → (Fin n → S) ⧸ N := fun b => N.mkQ (gr σ (Function.surjInv hq b))
  have hD : ∀ p, D (q p) = N.mkQ (gr σ p) := by
    intro p
    apply (Submodule.Quotient.eq N).2
    rw [← gr_sub]
    apply hN
    rw [map_sub, Function.surjInv_eq hq, sub_self]
  obtain ⟨l, hl⟩ := exists_lift (R := R) (S := S) D
    (by
      intro x y
      obtain ⟨x, rfl⟩ := hq x; obtain ⟨y, rfl⟩ := hq y
      rw [← map_add, hD, hD, hD, gr_add, map_add])
    (by
      intro x y
      obtain ⟨x, rfl⟩ := hq x; obtain ⟨y, rfl⟩ := hq y
      rw [← map_mul, hD, hD, hD, gr_mul, map_add, map_smul, map_smul, hσ, hσ])
    (by
      intro r
      rw [← q.commutes, hD, algebraMap_eq, gr_C, map_zero])
  have h := congrArg l hu
  rw [map_sum, map_zero] at h
  simp only [map_smul, dd, hl, hD, gr_X] at h
  simp only [← map_smul, ← map_sum] at h
  have h2 : ∑ i, u i • (Pi.single i 1 : Fin n → S) = u := by
    funext j; simp [Pi.single_apply]
  rw [h2] at h
  exact (Submodule.Quotient.mk_eq_zero N).1 h

theorem factA {R k C : Type} {n : ℕ} [CommRing R] [CommRing k] [CommRing C] [Algebra R k] [Algebra k C]
    [Algebra R C] [IsScalarTower R k C] (π : R) (hk : Function.Surjective (algebraMap R k))
    (hπ : ∀ r, algebraMap R k r = 0 ↔ π ∣ r) [Algebra.FormallySmooth k C]
    (σ : MvPolynomial (Fin n) R →ₐ[R] C) (hσ : Function.Surjective σ) (I : Ideal (MvPolynomial (Fin n) R))
    (hI : ∀ p, p ∈ I ↔ σ p = 0) :
    ∃ h : Fin n → MvPolynomial (Fin n) R, (∀ j, h j ∈ I) ∧
      ∀ g ∈ I, ∃ p, g - ∑ j, pderiv j g * h j - MvPolynomial.C π * p ∈ I * I := by
  let T : Ideal (MvPolynomial (Fin n) R) := Ideal.span {MvPolynomial.C π} ⊔ I * I
  have hπI : MvPolynomial.C π ∈ I := by
    rw [hI, ← algebraMap_eq, σ.commutes, IsScalarTower.algebraMap_apply R k C, (hπ π).2 dvd_rfl, map_zero]
  have hT : T ≤ I := sup_le ((Ideal.span_singleton_le_iff_mem _).2 hπI) Ideal.mul_le_left
  let A := MvPolynomial (Fin n) R ⧸ T
  let m : MvPolynomial (Fin n) R →ₐ[R] A := Ideal.Quotient.mkₐ R T
  have hm : Function.Surjective m := Ideal.Quotient.mkₐ_surjective R T
  have hm0 : ∀ p, m p = 0 ↔ p ∈ T := fun p => Ideal.Quotient.eq_zero_iff_mem
  let κ : k →+* A := RingHom.liftOfSurjective (algebraMap R k) hk ⟨algebraMap R A, by
    intro r hr
    obtain ⟨c, rfl⟩ := (hπ r).1 hr
    rw [RingHom.mem_ker, map_mul, ← m.commutes π, (hm0 _).2, zero_mul]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)⟩
  have hκ : ∀ r, κ (algebraMap R k r) = algebraMap R A r := fun r =>
    RingHom.liftOfSurjective_comp_apply _ _ _ _
  letI : Algebra k A := κ.toAlgebra
  let ρ0 : A →ₐ[R] C := Ideal.Quotient.liftₐ T σ (fun a ha => (hI a).1 (hT ha))
  have hρ0 : ∀ p, ρ0 (m p) = σ p := fun p => rfl
  let ρ : A →ₐ[k] C :=
    { ρ0.toRingHom with
      commutes' := fun c => by
        obtain ⟨r, rfl⟩ := hk c
        show ρ0 (κ _) = _
        rw [hκ, ρ0.commutes, IsScalarTower.algebraMap_apply R k C] }
  have hρ : ∀ p, ρ (m p) = σ p := fun p => rfl
  have hsq : ∀ x y : A, ρ x = 0 → ρ y = 0 → x * y = 0 := by
    intro x y hx hy
    obtain ⟨x, rfl⟩ := hm x; obtain ⟨y, rfl⟩ := hm y
    rw [← map_mul, hm0]
    exact Ideal.mem_sup_right (Ideal.mul_mem_mul ((hI x).2 hx) ((hI y).2 hy))
  have hnil : IsNilpotent (RingHom.ker (ρ : A →+* C)) := ⟨2, by
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    exact hsq x y hx hy⟩
  have hρs : Function.Surjective ρ := fun c => by
    obtain ⟨p, rfl⟩ := hσ c; exact ⟨m p, rfl⟩
  let s : C →ₐ[k] A := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k C) ρ hρs hnil
  have hs : ∀ c, ρ (s c) = c := fun c =>
    Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id k C) ρ hρs hnil c
  let D : MvPolynomial (Fin n) R → A := fun p => m p - s (σ p)
  have hD : ∀ p, ρ (D p) = 0 := fun p => by simp only [D, map_sub, hs, hρ, sub_self]
  have hch := chain (W := A) m.toRingHom D (fun x y => by simp only [D, map_add]; ring)
    (fun x y => by
      have := hsq _ _ (hD x) (hD y)
      simp only [D, map_mul, smul_eq_mul] at this ⊢
      show _ = m x * _ + m y * _
      linear_combination (-1 : A) * this)
    (fun r => by
      simp only [D]
      rw [← algebraMap_eq, m.commutes, σ.commutes, IsScalarTower.algebraMap_apply R k C, s.commutes, ← hκ]
      exact sub_self _)
  choose h hh using fun j => hm (D (X j))
  refine ⟨h, fun j => (hI _).2 (by rw [← hρ, hh, hD]), fun g hg => ?_⟩
  have h1 : g - ∑ j, pderiv j g * h j ∈ T := by
    rw [← hm0, map_sub, map_sum]
    have := hch g
    simp only [D, (hI g).1 hg, map_zero, sub_zero] at this
    rw [this, sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hh]; rfl
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
  obtain ⟨p, rfl⟩ := Ideal.mem_span_singleton.1 hx
  exact ⟨p, by rw [← hxy]; simpa using hy⟩

theorem factB {R B S : Type} {n : ℕ} [CommRing R] [CommRing B] [CommRing S] [Algebra R B] [Algebra B S]
    (q : MvPolynomial (Fin n) R →ₐ[R] B) (hq : Function.Surjective q) (σ : MvPolynomial (Fin n) R →+* S)
    (hσ : ∀ p, σ p = algebraMap B S (q p)) (hs : Function.Surjective σ)
    [Module.Projective S (S ⊗[B] KaehlerDifferential R B)] :
    ∃ h : Fin n → MvPolynomial (Fin n) R, (∀ j, q (h j) = 0) ∧
      ∀ f, q f = 0 → gr σ (f - ∑ j, pderiv j f * h j) = 0 := by
  let τ : (Fin n → S) →ₗ[S] S ⊗[B] KaehlerDifferential R B := Fintype.linearCombination S (fun i => dd R B S (q (X i)))
  have hτ : ∀ u, τ u = ∑ i, u i • dd R B S (q (X i)) := fun u => Fintype.linearCombination_apply _ _ _
  have hτg : ∀ p, τ (gr σ p) = dd R B S (q p) := fun p => by
    rw [hτ]
    exact (chain σ (fun p => dd R B S (q p)) (fun x y => by rw [map_add, dd_add])
      (fun x y => by rw [map_mul, dd_mul, hσ, hσ]) (fun r => by rw [← algebraMap_eq, q.commutes, dd_algebraMap]) p).symm
  have hsur : Function.Surjective τ := fun x => span_d R B S (LinearMap.range τ) (fun b => by
    obtain ⟨p, rfl⟩ := hq b
    exact ⟨_, hτg p⟩) x
  obtain ⟨s, hs'⟩ := Module.projective_lifting_property τ LinearMap.id hsur
  let N : Submodule S (Fin n → S) :=
    { carrier := {u | ∃ f, q f = 0 ∧ gr σ f = u}
      zero_mem' := ⟨0, map_zero _, gr_zero σ⟩
      add_mem' := by
        rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
        exact ⟨f + g, by rw [map_add, hf, hg, add_zero], gr_add σ _ _⟩
      smul_mem' := by
        rintro c _ ⟨f, hf, rfl⟩
        obtain ⟨p, rfl⟩ := hs c
        exact ⟨p * f, by rw [map_mul, hf, mul_zero], by rw [gr_mul, hσ f, hf, map_zero, zero_smul, add_zero]⟩ }
  let r : (Fin n → S) →ₗ[S] (Fin n → S) := LinearMap.id - s ∘ₗ τ
  have hr : ∀ u, r u ∈ N := fun u => ker_le q hq σ hσ N (fun f hf => ⟨f, hf, rfl⟩) _ (by
    rw [← hτ]
    have := LinearMap.congr_fun hs' (τ u)
    simp only [r, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub] at this ⊢
    rw [this, sub_self])
  choose h hh1 hh2 using fun j => hr (Pi.single j 1)
  refine ⟨h, hh1, fun f hf => ?_⟩
  have h1 : r (gr σ f) = gr σ f := by
    simp only [r, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, hτg, hf, dd_zero, map_zero, sub_zero]
  have h2 : ∑ i, gr σ f i • (Pi.single i 1 : Fin n → S) = gr σ f := by
    funext j; simp [Pi.single_apply]
  rw [gr_sub, gr_sum, sub_eq_zero, ← h1]
  conv_lhs => rw [← h2, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gr_mul, hσ (h j), hh1, map_zero, zero_smul, add_zero, hh2, map_smul]; rfl

theorem core {R B B' S : Type} {n : ℕ} [CommRing R] [CommRing B] [CommRing B'] [CommRing S] [Algebra R B] [Algebra R B']
    [Algebra B S] [Algebra B' S] (q : MvPolynomial (Fin n) R →ₐ[R] B) (hq : Function.Surjective q)
    (σ : MvPolynomial (Fin n) R →+* S) (hσ : ∀ p, σ p = algebraMap B S (q p))
    (φ : B →ₐ[R] B') (hφ : ∀ b, algebraMap B' S (φ b) = algebraMap B S b) (π : R) (ϖ : S)
    (hϖ : algebraMap B' S (algebraMap R B' π) = ϖ) (hreg : ∀ x, ϖ * x = 0 → x = 0)
    (hreg' : ∀ x, algebraMap R B' π * x = 0 → x = 0) (I : Ideal (MvPolynomial (Fin n) R))
    (hβ : ∀ g ∈ I, ∃ b', algebraMap R B' π * b' = φ (q g)) (hJ : ∀ f, q f = 0 → f ∈ I)
    (hgen : ∀ Q : B' → Prop, (∀ b, Q (φ b)) → (∀ g ∈ I, ∀ b', algebraMap R B' π * b' = φ (q g) → Q b') →
      (∀ x y, Q x → Q y → Q (x + y)) → (∀ x y, Q x → Q y → Q (x * y)) → ∀ x, Q x)
    (h : Fin n → MvPolynomial (Fin n) R) (hh : ∀ j, h j ∈ I)
    (hA : ∀ g ∈ I, ∃ p, g - ∑ j, pderiv j g * h j - MvPolynomial.C π * p ∈ I * I)
    (h' : Fin n → MvPolynomial (Fin n) R) (hh' : ∀ j, q (h' j) = 0)
    (hB : ∀ f, q f = 0 → f - ∑ j, pderiv j f * h' j ∈ I * I)
    (m : S ⊗[B'] KaehlerDifferential R B') :
    ∃ u : Fin n → S, ϖ • m = ∑ i, u i • dd R B' S (φ (q (X i))) ∧
      ∀ c : ℕ, ϖ ^ (c + 1) • ∑ i, u i • dd R B S (q (X i)) = 0 → ϖ ^ c • m = 0 := by
  have hσ' : ∀ p, σ p = algebraMap B' S (φ (q p)) := fun p => by rw [hφ, hσ]
  have hregF : ∀ u : Fin n → S, ϖ • u = 0 → u = 0 := fun u hu => funext fun i => hreg _ (congrFun hu i)
  have huniq : ∀ x y, algebraMap R B' π * x = algebraMap R B' π * y → x = y := fun x y e =>
    sub_eq_zero.1 (hreg' _ (by rw [mul_sub, e, sub_self]))
  have hCπ : φ (q (C π)) = algebraMap R B' π := by rw [← algebraMap_eq, q.commutes, φ.commutes]
  let ψ : (Fin n → S) →ₗ[S] S ⊗[B'] KaehlerDifferential R B' :=
    Fintype.linearCombination S (fun i => dd R B' S (φ (q (X i))))
  have hψ : ∀ u, ψ u = ∑ i, u i • dd R B' S (φ (q (X i))) := fun u => Fintype.linearCombination_apply _ _ _
  have hψg : ∀ p, ψ (gr σ p) = dd R B' S (φ (q p)) := fun p => by
    rw [hψ]
    exact (chain σ (fun p => dd R B' S (φ (q p))) (fun x y => by rw [map_add, map_add, dd_add])
      (fun x y => by rw [map_mul, map_mul, dd_mul, hσ', hσ'])
      (fun r => by rw [← algebraMap_eq, q.commutes, φ.commutes, dd_algebraMap]) p).symm
  let j : (Fin n → S) →ₗ[S] (Fin n → S) × (S ⊗[B'] KaehlerDifferential R B') := LinearMap.prod (ϖ • LinearMap.id) ψ
  have hj : ∀ u, j u = (ϖ • u, ψ u) := fun u => rfl
  have hval : ∀ g b', algebraMap R B' π * b' = φ (q g) → σ g = ϖ * algebraMap B' S b' := fun g b' e => by
    rw [hσ', ← e, map_mul, hϖ]
  have hdd : ∀ g b', algebraMap R B' π * b' = φ (q g) → ϖ • dd R B' S b' = ψ (gr σ g) := fun g b' e => by
    rw [hψg, ← e, dd_mul, dd_algebraMap, smul_zero, add_zero, hϖ]
  choose β hβh using fun i => hβ (h i) (hh i)
  let θ : (Fin n → S) →ₗ[S] (Fin n → S) × (S ⊗[B'] KaehlerDifferential R B') :=
    Fintype.linearCombination S (fun i => (gr σ (h i), dd R B' S (β i)))
  have hθ : ∀ u, θ u = ∑ i, u i • (gr σ (h i), dd R B' S (β i)) := fun u => Fintype.linearCombination_apply _ _ _
  have hθϖ : ∀ u, ϖ • θ u ∈ LinearMap.range j := fun u => by
    rw [hθ, Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [smul_comm]
    refine Submodule.smul_mem _ _ ⟨gr σ (h i), ?_⟩
    rw [hj, Prod.smul_mk, hdd _ _ (hβh i)]
  let W : Submodule S ((Fin n → S) × (S ⊗[B'] KaehlerDifferential R B')) :=
    (LinearMap.range j).comap (LinearMap.id - θ ∘ₗ LinearMap.fst S _ _)
  have hW : ∀ w, w ∈ W ↔ w - θ w.1 ∈ LinearMap.range j := fun w => Iff.rfl
  have hjW : ∀ w ∈ LinearMap.range j, w ∈ W := by
    rintro _ ⟨u, rfl⟩
    rw [hW]
    refine Submodule.sub_mem _ ⟨u, rfl⟩ ?_
    rw [hj, map_smul]; exact hθϖ u
  have key : ∀ x, ((0 : Fin n → S), x) ∈ W → x = 0 := by
    intro x hx
    rw [hW, map_zero, sub_zero] at hx
    obtain ⟨u, hu⟩ := hx
    rw [hj, Prod.mk.injEq] at hu
    rw [← hu.2, hregF u hu.1, map_zero]
  have S1 : ∀ e ∈ I * I, ∃ b', algebraMap R B' π * b' = φ (q e) ∧ (gr σ e, dd R B' S b') ∈ LinearMap.range j := by
    intro e he
    refine Submodule.mul_induction_on he ?_ ?_
    · intro g hg g' hg'
      obtain ⟨b, hb⟩ := hβ g hg
      obtain ⟨b', hb'⟩ := hβ g' hg'
      refine ⟨φ (q g) * b', by rw [map_mul, map_mul, ← hb']; ring,
        algebraMap B' S b • gr σ g' + algebraMap B' S b' • gr σ g, ?_⟩
      rw [hj, gr_mul, dd_mul, ← hσ', hval g b hb, hval g' b' hb', map_add, map_smul, map_smul, ← hdd g' b' hb', hψg]
      congr 1
      · rw [smul_add, mul_smul, mul_smul]
      · rw [mul_comm, mul_smul]
    · rintro x y ⟨b, hb, hx⟩ ⟨b', hb', hy⟩
      refine ⟨b + b', by rw [mul_add, hb, hb', map_add, map_add], ?_⟩
      rw [gr_add, dd_add]
      exact Submodule.add_mem _ hx hy
  have hΔ : ∀ g ∈ I, ∀ b', algebraMap R B' π * b' = φ (q g) → (gr σ g, dd R B' S b') ∈ W := by
    intro g hg b' hb'
    obtain ⟨p, hp⟩ := hA g hg
    obtain ⟨e, he, he'⟩ := S1 _ hp
    have e1 : b' = e + ∑ i, φ (q (pderiv i g)) * β i + φ (q p) := by
      apply huniq
      rw [mul_add, mul_add, he, hb', Finset.mul_sum]
      simp only [map_sub, map_sum, map_mul, hCπ, ← hβh]
      simp only [mul_left_comm (algebraMap R B' π)]
      ring
    have ddsum : ∀ f : Fin n → B', dd R B' S (∑ i, f i) = ∑ i, dd R B' S (f i) := fun f => by
      simp [dd, tmul_sum]
    have e2 : (gr σ g, dd R B' S b') - θ (gr σ g) =
        (gr σ (g - ∑ j, pderiv j g * h j - MvPolynomial.C π * p), dd R B' S e) + j (gr σ p) +
          ∑ i, algebraMap B' S (β i) • j (gr σ (pderiv i g)) := by
      rw [hθ]
      ext1
      · simp only [Prod.fst_sub, Prod.fst_add, Prod.fst_sum, Prod.smul_fst, hj, gr_sub, gr_sum, gr_mul, gr_C,
          hσ' (C π), hCπ, hϖ, smul_zero, add_zero, Finset.sum_add_distrib, fun i => hval _ _ (hβh i), smul_smul,
          mul_comm ϖ]
        have : ∀ i, gr σ g i = σ (pderiv i g) := fun _ => rfl
        simp only [this]
        abel
      · simp only [Prod.snd_sub, Prod.snd_add, Prod.snd_sum, Prod.smul_snd, hj, hψg]
        rw [e1, dd_add, dd_add, ddsum]
        have : ∀ i, gr σ g i = σ (pderiv i g) := fun _ => rfl
        simp only [this, dd_mul, ← hσ', Finset.sum_add_distrib]
        abel
    rw [hW]
    show (gr σ g, dd R B' S b') - θ (gr σ g) ∈ _
    rw [e2]
    exact Submodule.add_mem _ (Submodule.add_mem _ he' ⟨_, rfl⟩)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ⟨_, rfl⟩)
  have S2 : ∀ e ∈ I * I, ∃ b', algebraMap R B' π * (algebraMap R B' π * b') = φ (q e) ∧
      ∃ u, ϖ • u = gr σ e ∧ (u, dd R B' S b') ∈ W := by
    intro e he
    refine Submodule.mul_induction_on he ?_ ?_
    · intro g hg g' hg'
      obtain ⟨b, hb⟩ := hβ g hg
      obtain ⟨b', hb'⟩ := hβ g' hg'
      refine ⟨b * b', by rw [map_mul, map_mul, ← hb', ← hb]; ring,
        algebraMap B' S b • gr σ g' + algebraMap B' S b' • gr σ g, ?_, ?_⟩
      · rw [gr_mul, hval g b hb, hval g' b' hb', smul_add, mul_smul, mul_smul]
      · rw [dd_mul]
        exact W.add_mem (W.smul_mem _ (hΔ g' hg' b' hb')) (W.smul_mem _ (hΔ g hg b hb))
    · rintro x y ⟨b, hb, u, hu, hx⟩ ⟨b', hb', u', hu', hy⟩
      refine ⟨b + b', by rw [mul_add, mul_add, hb, hb', map_add, map_add], u + u', by rw [smul_add, hu, hu', gr_add], ?_⟩
      rw [dd_add]
      exact W.add_mem hx hy
  let θ' : (Fin n → S) →ₗ[S] (Fin n → S) := Fintype.linearCombination S (fun i => gr σ (h' i))
  have hθ' : ∀ u, θ' u = ∑ i, u i • gr σ (h' i) := fun u => Fintype.linearCombination_apply _ _ _
  let W₁ : Submodule S (Fin n → S) := W.comap (LinearMap.inl S _ _)
  have hW₁ : ∀ u, u ∈ W₁ ↔ (u, (0 : S ⊗[B'] KaehlerDifferential R B')) ∈ W := fun _ => Iff.rfl
  have hθ'W : ∀ u, θ' u ∈ W₁ := fun u => by
    rw [hθ']
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have := hΔ (h' i) (hJ _ (hh' i)) 0 (by rw [hh', map_zero, mul_zero])
    rwa [dd_zero] at this
  let N : Submodule S (Fin n → S) := (W₁.map (ϖ • LinearMap.id)).comap (LinearMap.id - θ')
  have hN : ∀ v, v ∈ N ↔ ∃ u ∈ W₁, ϖ • u = v - θ' v := fun _ => Iff.rfl
  have hNJ : ∀ f, q f = 0 → gr σ f ∈ N := by
    intro f hf
    obtain ⟨b, hb, u, hu, hw⟩ := S2 _ (hB f hf)
    have hb0 : b = 0 := hreg' _ (hreg' _ (by rw [hb]; simp [hf, hh']))
    rw [hb0, dd_zero] at hw
    refine (hN _).2 ⟨u, hw, ?_⟩
    rw [hu, gr_sub, gr_sum, hθ']
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gr_mul, hσ (h' i), hh', map_zero, zero_smul, add_zero]; rfl
  have hsur : m ∈ W.map (LinearMap.snd S _ _) := by
    refine span_d R B' S _ (fun b => ?_) m
    show dd R B' S b ∈ _
    refine hgen (fun b => dd R B' S b ∈ W.map (LinearMap.snd S _ _)) ?_ ?_ ?_ ?_ b
    · intro b
      obtain ⟨p, rfl⟩ := hq b
      exact ⟨j (gr σ p), hjW _ ⟨_, rfl⟩, hψg p⟩
    · intro g hg b' hb'
      exact ⟨_, hΔ g hg b' hb', rfl⟩
    · intro x y hx hy
      show dd R B' S (x + y) ∈ _
      rw [dd_add]; exact Submodule.add_mem _ hx hy
    · intro x y hx hy
      show dd R B' S (x * y) ∈ _
      rw [dd_mul]; exact Submodule.add_mem _ (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hx)
  obtain ⟨⟨u, m⟩, hw, rfl⟩ := hsur
  show ∃ u : Fin n → S, ϖ • m = ∑ i, u i • dd R B' S (φ (q (X i))) ∧
      ∀ c : ℕ, ϖ ^ (c + 1) • ∑ i, u i • dd R B S (q (X i)) = 0 → ϖ ^ c • m = 0
  refine ⟨u, ?_, fun c hc => ?_⟩
  · have h1 : ϖ • (u, m) ∈ LinearMap.range j := by
      have := Submodule.add_mem _ (Submodule.smul_mem _ ϖ ((hW _).1 hw)) (hθϖ u)
      rwa [← smul_add, sub_add_cancel] at this
    obtain ⟨v, hv⟩ := h1
    rw [hj, Prod.smul_mk, Prod.mk.injEq] at hv
    have : v = u := sub_eq_zero.1 (hregF _ (by rw [smul_sub, hv.1, sub_self]))
    rw [← hv.2, this, hψ]
  · have h1 : ϖ • ϖ ^ c • u ∈ N := ker_le q hq σ hσ N hNJ _ (by
      rw [← hc, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, smul_smul, pow_succ']; rfl)
    obtain ⟨v, hv, e⟩ := (hN _).1 h1
    have e' : ϖ ^ c • u = v + θ' (ϖ ^ c • u) := sub_eq_zero.1 (hregF _ (by
      rw [smul_sub, smul_add, e, map_smul θ' ϖ]; abel))
    have h2 : ϖ ^ c • u ∈ W₁ := by rw [e']; exact W₁.add_mem hv (hθ'W _)
    apply key
    have := W.sub_mem (W.smul_mem (ϖ ^ c) hw) ((hW₁ _).1 h2)
    simpa using this

theorem tors {R B B' S : Type} [CommRing R] [CommRing B] [CommRing B'] [CommRing S] [Algebra R B] [Algebra R B']
    [Algebra B S] [Algebra B' S] (φ : B →ₐ[R] B') (hφ : ∀ b, algebraMap B' S (φ b) = algebraMap B S b) (π : R) (ϖ : S)
    (hϖ : algebraMap B' S (algebraMap R B' π) = ϖ) (hreg : ϖ ∈ nonZeroDivisors S) (hinj : Function.Injective φ)
    (hden : ∀ b' : B', ∃ (n : ℕ) (b : B), algebraMap R B' π ^ n * b' = φ b) {n : ℕ} (u : Fin n → S) (x : Fin n → B)
    (hu : ∑ i, u i • dd R B' S (φ (x i)) ∈ Submodule.torsion S (S ⊗[B'] KaehlerDifferential R B')) :
    ∑ i, u i • dd R B S (x i) ∈ Submodule.torsion S (S ⊗[B] KaehlerDifferential R B) := by
  let ι := LocalizedModule.mkLinearMap (nonZeroDivisors S) (S ⊗[B] KaehlerDifferential R B)
  have hbij : ∀ k : ℕ, Function.Bijective
      (fun w : LocalizedModule (nonZeroDivisors S) (S ⊗[B] KaehlerDifferential R B) => ϖ ^ k • w) := fun k =>
    (Module.End.isUnit_iff _).1 (IsLocalizedModule.map_units ι ⟨ϖ ^ k, pow_mem hreg k⟩)
  have hϖ' : algebraMap B S (algebraMap R B π) = ϖ := by rw [← hφ, φ.commutes, hϖ]
  have hpow : ∀ (k : ℕ) b, dd R B S (algebraMap R B π ^ k * b) = ϖ ^ k • dd R B S b := fun k b => by
    rw [dd_mul, ← map_pow, dd_algebraMap, smul_zero, add_zero, map_pow, map_pow, hϖ']
  choose N c hc using hden
  choose D hD using fun b' => (hbij (N b')).2 (ι (dd R B S (c b')))
  have hD' : ∀ (k : ℕ) b b', algebraMap R B' π ^ k * b' = φ b → ϖ ^ k • D b' = ι (dd R B S b) := by
    intro k b b' e
    apply (hbij (N b')).1
    have e1 : algebraMap R B π ^ N b' * b = algebraMap R B π ^ k * c b' := hinj (by
      rw [map_mul, map_mul, map_pow, map_pow, φ.commutes, ← e, ← hc]; ring)
    have := hD b'
    simp only at this ⊢
    rw [smul_comm, this, ← map_smul, ← map_smul, ← hpow, ← hpow, e1]
  have hval : ∀ b', algebraMap B S (c b') = ϖ ^ N b' * algebraMap B' S b' := fun b' => by
    rw [← hφ, ← hc, map_mul, map_pow, hϖ]
  obtain ⟨l, hl⟩ := exists_lift (R := R) (S := S) D
    (fun x y => by
      apply (hbij (N x + N y)).1
      simp only
      rw [hD' _ (algebraMap R B π ^ N y * c x + algebraMap R B π ^ N x * c y) _ (by
        simp only [map_add, map_mul, map_pow, φ.commutes, ← hc]; ring), dd_add, hpow, hpow, map_add, map_smul,
        map_smul, ← hD' _ _ _ (hc x), ← hD' _ _ _ (hc y), smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm (N y)])
    (fun x y => by
      apply (hbij (N x + N y)).1
      simp only
      rw [hD' _ (c x * c y) _ (by
        simp only [map_mul, ← hc]; ring), dd_mul, map_add, map_smul,
        map_smul, ← hD' _ _ _ (hc x), ← hD' _ _ _ (hc y), hval, hval, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
      congr 2 <;> ring)
    (fun r => by
      have := hD' 0 (algebraMap R B r) (algebraMap R B' r) (by simp)
      rwa [pow_zero, one_smul, dd_algebraMap, map_zero] at this)
  have hlφ : ∀ b, l (dd R B' S (φ b)) = ι (dd R B S b) := fun b => by
    have := hD' 0 b (φ b) (by simp)
    rw [pow_zero, one_smul] at this
    rw [← this]; exact hl _
  obtain ⟨r, hr⟩ := hu
  have h1 : ι ((r : S) • ∑ i, u i • dd R B S (x i)) = 0 := by
    have := congrArg l hr
    rw [Submonoid.smul_def, map_smul, map_sum, map_zero] at this
    simp only [map_smul, hlφ] at this
    rw [map_smul, map_sum]
    simpa only [map_smul] using this
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors S) ι).1 h1
  exact ⟨s * r, by rw [mul_smul]; exact hs⟩

theorem exists_dil (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R) (hπ : Irreducible π)
    (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B] (I : Ideal B) :
    ∃ (B' : Type) (_ : CommRing B') (_ : Algebra R B') (φ : B →ₐ[R] B'), Algebra.FiniteType R B' ∧ Module.Flat R B' ∧
      Function.Injective φ ∧ (∀ b' : B', ∃ (n : ℕ) (b : B), algebraMap R B' π ^ n * b' = φ b) ∧
      (∀ x, algebraMap R B' π * x = 0 → x = 0) ∧ (∀ g ∈ I, ∃ b', algebraMap R B' π * b' = φ g) ∧
      (∀ Q : B' → Prop, (∀ b, Q (φ b)) → (∀ g ∈ I, ∀ b', algebraMap R B' π * b' = φ g → Q b') →
        (∀ x y, Q x → Q y → Q (x + y)) → (∀ x y, Q x → Q y → Q (x * y)) → ∀ x, Q x) := by
  first
  | exact @_root_.GlobalTheory.FiniteFieldCountEstimate.main
  | exact _root_.GlobalTheory.FiniteFieldCountEstimate.main
  | (apply _root_.GlobalTheory.FiniteFieldCountEstimate.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteFieldCountEstimate.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteFieldCountEstimate.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteFieldCountEstimate.main ..)

theorem exists_ext {R B B' S : Type} [CommRing R] [CommRing B] [CommRing B'] [CommRing S] [Algebra R B] [Algebra R B']
    [Algebra R S] (φ : B →ₐ[R] B') (π : R) (I : Ideal B) (hinj : Function.Injective φ)
    (hden : ∀ b' : B', ∃ (n : ℕ) (b : B), algebraMap R B' π ^ n * b' = φ b)
    (hgen : ∀ Q : B' → Prop, (∀ b, Q (φ b)) → (∀ g ∈ I, ∀ b', algebraMap R B' π * b' = φ g → Q b') →
        (∀ x y, Q x → Q y → Q (x + y)) → (∀ x y, Q x → Q y → Q (x * y)) → ∀ x, Q x)
    (a : B →ₐ[R] S) (hreg : algebraMap R S π ∈ nonZeroDivisors S) (ha : ∀ g ∈ I, algebraMap R S π ∣ a g) :
    ∃ a' : B' →ₐ[R] S, a'.comp φ = a := by
  let Rel : B' → S → Prop := fun b' s => ∃ (k : ℕ) (b : B), algebraMap R B' π ^ k * b' = φ b ∧
    algebraMap R S π ^ k * s = a b
  have radd : ∀ x y s t, Rel x s → Rel y t → Rel (x + y) (s + t) := by
    rintro x y s t ⟨k, b, h1, h2⟩ ⟨l, c, h3, h4⟩
    refine ⟨k + l, algebraMap R B π ^ l * b + algebraMap R B π ^ k * c, ?_, ?_⟩
    · simp only [map_add, map_mul, map_pow, φ.commutes, ← h1, ← h3]; ring
    · simp only [map_add, map_mul, map_pow, a.commutes, ← h2, ← h4]; ring
  have rmul : ∀ x y s t, Rel x s → Rel y t → Rel (x * y) (s * t) := by
    rintro x y s t ⟨k, b, h1, h2⟩ ⟨l, c, h3, h4⟩
    refine ⟨k + l, b * c, ?_, ?_⟩
    · simp only [map_mul, ← h1, ← h3]; ring
    · simp only [map_mul, ← h2, ← h4]; ring
  have rφ : ∀ b, Rel (φ b) (a b) := fun b => ⟨0, b, by simp, by simp⟩
  have runiq : ∀ x s t, Rel x s → Rel x t → s = t := by
    rintro x s t ⟨k, b, h1, h2⟩ ⟨l, c, h3, h4⟩
    have e1 : algebraMap R B π ^ l * b = algebraMap R B π ^ k * c := hinj (by
      rw [map_mul, map_mul, map_pow, map_pow, φ.commutes, ← h1, ← h3]; ring)
    have e2 := congrArg a e1
    simp only [map_mul, map_pow, a.commutes, ← h2, ← h4] at e2
    apply (mul_cancel_left_mem_nonZeroDivisors (pow_mem hreg (k + l))).1
    linear_combination e2
  have rex : ∀ x, ∃ s, Rel x s := by
    refine hgen _ (fun b => ⟨_, rφ b⟩) ?_ ?_ ?_
    · intro g hg b' hb'
      obtain ⟨s, hs⟩ := ha g hg
      exact ⟨s, 1, g, by rwa [pow_one], by rw [pow_one, hs]⟩
    · rintro x y ⟨s, hs⟩ ⟨t, ht⟩; exact ⟨_, radd _ _ _ _ hs ht⟩
    · rintro x y ⟨s, hs⟩ ⟨t, ht⟩; exact ⟨_, rmul _ _ _ _ hs ht⟩
  choose f hf using rex
  have fφ : ∀ b, f (φ b) = a b := fun b => runiq _ _ _ (hf _) (rφ b)
  refine ⟨{ toFun := f
            map_one' := by rw [← map_one φ, fφ, map_one]
            map_zero' := by rw [← map_zero φ, fφ, map_zero]
            map_mul' := fun x y => runiq _ _ _ (hf _) (rmul _ _ _ _ (hf x) (hf y))
            map_add' := fun x y => runiq _ _ _ (hf _) (radd _ _ _ _ (hf x) (hf y))
            commutes' := fun r => by
              show f _ = _
              rw [← φ.commutes, fφ, a.commutes] }, AlgHom.ext fφ⟩

end GlobalTheory.SS.Dil
namespace GlobalTheory.SS
open Dil

theorem dilatation_lowers_defect : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R), Irreducible π → ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B] (E : ∀ (R' : Type) [CommRing R'] [Algebra R R'], (B →ₐ[R] R') → Prop), (∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → Unr π R') → ∀ (I : Ideal B), (∀ b, b ∈ I ↔ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → algebraMap R R' π ∣ a b) → ∀ (k : Type) [Field k] [Algebra R k] [Algebra k (B ⧸ I)] [IsScalarTower R k (B ⧸ I)], Function.Surjective (algebraMap R k) → Algebra.Smooth k (B ⧸ I) → Module.Free (B ⧸ I) (TensorProduct B (B ⧸ I) (KaehlerDifferential R B)) → ∃ (B' : Type) (_ : CommRing B') (_ : Algebra R B') (φ : B →ₐ[R] B'), Algebra.FiniteType R B' ∧ Module.Flat R B' ∧ Function.Injective φ ∧ (∀ b' : B', ∃ (n : ℕ) (b : B), algebraMap R B' π ^ n * b' = φ b) ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R') (c : ℕ), E R' a → Defect a π (c + 1) → ∃ a' : B' →ₐ[R] R', a'.comp φ = a ∧ Defect a' π c := by
  intro R _ _ _ π hπ B _ _ _ _ E hE I hI k _ _ _ _ hk hsm hfree
  obtain ⟨B', _, _, φ, hft, hfl, hinj, hden, hreg', hβ, hgen⟩ := exists_dil R π hπ B I
  refine ⟨B', inferInstance, inferInstance, φ, hft, hfl, hinj, hden, ?_⟩
  obtain ⟨n, q, hq⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType R B)
  let σ₀ : MvPolynomial (Fin n) R →ₐ[R] B ⧸ I := (Ideal.Quotient.mkₐ R I).comp q
  have hσ₀ : Function.Surjective σ₀ := (Ideal.Quotient.mkₐ_surjective R I).comp hq
  let I₀ : Ideal (MvPolynomial (Fin n) R) := I.comap q
  have hI₀ : ∀ p, p ∈ I₀ ↔ σ₀ p = 0 := fun p => (Ideal.Quotient.eq_zero_iff_mem (I := I) (a := q p)).symm
  have hker : ∀ r, algebraMap R k r = 0 ↔ π ∣ r := fun r => by
    have h1 : RingHom.ker (algebraMap R k) = IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hk)
    rw [← RingHom.mem_ker, h1, hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
  obtain ⟨h, hh, hA⟩ := factA π hk hker σ₀ hσ₀ I₀ hI₀
  obtain ⟨h', hh', hB⟩ := factB q hq σ₀.toRingHom (fun _ => rfl) hσ₀
  have hJ : ∀ f, q f = 0 → f ∈ I₀ := fun f hf => by
    show q f ∈ I
    rw [hf]; exact I.zero_mem
  have hCπ : q (C π) = algebraMap R B π := by rw [← algebraMap_eq, q.commutes]
  have hπI : C π ∈ I₀ := by
    show q (C π) ∈ I
    rw [hCπ, hI]
    intro R' _ _ a _
    rw [a.commutes]
  have hB' : ∀ f, q f = 0 → f - ∑ j, pderiv j f * h' j ∈ I₀ * I₀ := by
    intro f hf
    have h0 := hB f hf
    have h1 : q (f - ∑ j, pderiv j f * h' j) = 0 := by simp [hf, hh']
    generalize f - ∑ j, pderiv j f * h' j = g at h0 h1 ⊢
    obtain ⟨p, hp⟩ := hA g (hJ g h1)
    have h2 : ∑ j, pderiv j g * h j ∈ I₀ * I₀ :=
      Ideal.sum_mem _ fun j _ => Ideal.mul_mem_mul ((hI₀ _).2 (congrFun h0 j)) (hh j)
    have h3 : g - C π * p ∈ I₀ * I₀ := by
      have := Ideal.add_mem _ hp h2
      convert this using 1; ring
    have h4 : p ∈ I₀ := by
      show q p ∈ I
      rw [hI]
      intro R' _ _ a ha
      obtain ⟨_, _, hirr⟩ := hE R' a ha
      have h5 : ∀ e ∈ I₀ * I₀, algebraMap R R' π * algebraMap R R' π ∣ a (q e) := fun e he =>
        Submodule.mul_induction_on he
          (fun x hx y hy => by
            rw [map_mul, map_mul]
            exact mul_dvd_mul ((hI _).1 hx R' a ha) ((hI _).1 hy R' a ha))
          (fun x y hx hy => by rw [map_add, map_add]; exact dvd_add hx hy)
      have h6 := h5 _ h3
      rw [map_sub, h1, zero_sub, map_neg, dvd_neg, map_mul, map_mul, hCπ, a.commutes] at h6
      exact (mul_dvd_mul_iff_left hirr.ne_zero).1 h6
    have := Ideal.add_mem _ h3 (Ideal.mul_mem_mul hπI h4)
    rwa [sub_add_cancel] at this
  intro R' _ _ a c ha hdef
  obtain ⟨_, _, hirr⟩ := hE R' a ha
  have hreg : algebraMap R R' π ∈ nonZeroDivisors R' := mem_nonZeroDivisors_of_ne_zero hirr.ne_zero
  obtain ⟨a', ha'⟩ := exists_ext φ π I hinj hden hgen a hreg (fun g hg => (hI g).1 hg R' a ha)
  refine ⟨a', ha', ?_⟩
  letI := a.toRingHom.toAlgebra
  letI := a'.toRingHom.toAlgebra
  have hφ : ∀ b, algebraMap B' R' (φ b) = algebraMap B R' b := fun b => AlgHom.congr_fun ha' b
  have hϖ : algebraMap B' R' (algebraMap R B' π) = algebraMap R R' π := a'.commutes π
  intro m hm
  obtain ⟨u, hu, hc⟩ := core q hq (a.comp q).toRingHom (fun _ => rfl) φ hφ π _ hϖ
    (fun x hx => (mul_eq_zero.1 hx).resolve_left hirr.ne_zero) hreg' I₀ (fun g hg => hβ _ hg) hJ
    (fun Q h1 h2 => hgen Q h1 (fun g hg b' hb' => by
      obtain ⟨p, rfl⟩ := hq g
      exact h2 p hg b' hb')) h hh hA h' hh' hB' m
  exact hc c (hdef _ (tors φ hφ π _ hϖ hreg hinj hden u _ (hu ▸ Submodule.smul_mem _ _ hm)))
end GlobalTheory.SS
end
