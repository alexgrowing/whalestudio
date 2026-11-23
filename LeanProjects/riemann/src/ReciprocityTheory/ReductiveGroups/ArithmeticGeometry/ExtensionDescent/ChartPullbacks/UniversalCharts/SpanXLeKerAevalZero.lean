import Mathlib

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Chart

open MvPolynomial

section Jet

variable (R : Type) [CommRing R]

abbrev JetR (κ : Type) (m : ℕ) : Type :=
  MvPolynomial κ R ⧸ (Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R))) ^ (m + 1)

def jetTruncR (κ : Type) (m : ℕ) : JetR R κ (m + 1) →ₐ[R] JetR R κ m :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega))

def jetZeroR (κ : Type) (m : ℕ) : JetR R κ m →ₐ[R] JetR R κ 0 :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega))

variable {R}

abbrev zR {κ : Type} (m : ℕ) (j : κ) : JetR R κ m := Ideal.Quotient.mk _ (MvPolynomial.X j)

variable (R)

theorem span_X_le_ker_aeval_zero (κ : Type) :
    Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R)) ≤
      RingHom.ker (MvPolynomial.aeval (R := R) (fun _ : κ => (0 : R))) := by
  rw [Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  simp

def jetAug (κ : Type) (m : ℕ) : JetR R κ m →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (fun _ : κ => (0 : R))) (fun a ha =>
    span_X_le_ker_aeval_zero R κ (Ideal.pow_le_self (by omega) ha))

variable {R}

theorem jetAug_zR {κ : Type} (m : ℕ) (j : κ) : jetAug R κ m (zR m j) = 0 := by
  show MvPolynomial.aeval (fun _ : κ => (0 : R)) (MvPolynomial.X j) = 0
  simp

theorem jet_ext {κ : Type} {m : ℕ} {A : Type} [CommRing A] [Algebra R A] {ψ₁ ψ₂ : JetR R κ m →ₐ[R] A}
    (h : ∀ j, ψ₁ (zR (R := R) m j) = ψ₂ (zR (R := R) m j)) : ψ₁ = ψ₂ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro j
  exact h j

variable (R) in

def jetLift {κ : Type} {m : ℕ} {A : Type} [CommRing A] [Algebra R A] (J : Ideal A) (hJ : J ^ (m + 1) = ⊥)
    (b : κ → A) (hb : ∀ j, b j ∈ J) : JetR R κ m →ₐ[R] A :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval b) (fun a ha => by
    have h1 : Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R)) ≤
        J.comap (MvPolynomial.aeval (R := R) b) := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      simpa using hb j
    have h2 : a ∈ (J ^ (m + 1)).comap (MvPolynomial.aeval (R := R) b) :=
      Ideal.le_comap_pow _ (m + 1) (Ideal.pow_right_mono h1 (m + 1) ha)
    rw [hJ] at h2
    exact h2)

theorem jetLift_zR {κ : Type} {m : ℕ} {A : Type} [CommRing A] [Algebra R A] (J : Ideal A)
    (hJ : J ^ (m + 1) = ⊥) (b : κ → A) (hb : ∀ j, b j ∈ J) (j : κ) :
    jetLift R J hJ b hb (zR m j) = b j := by
  show MvPolynomial.aeval b (MvPolynomial.X j) = b j
  simp

theorem sub_const_mem_span_X {κ : Type} (p : MvPolynomial κ R) :
    p - MvPolynomial.C (MvPolynomial.aeval (fun _ : κ => (0 : R)) p) ∈
      Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R)) := by
  classical
  have hs : Set.range (MvPolynomial.X : κ → MvPolynomial κ R) = MvPolynomial.X '' Set.univ := by
    rw [Set.image_univ]
  rw [hs, MvPolynomial.mem_ideal_span_X_image]
  intro mono hm
  by_contra hcon
  push Not at hcon
  have h0 : mono = 0 := by
    ext i
    exact hcon i (Set.mem_univ i)
  subst h0
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_pos rfl] at hm
  apply hm
  rw [sub_eq_zero, MvPolynomial.aeval_zero', ← MvPolynomial.constantCoeff_eq]
  rfl

theorem ker_jetAug_pow (κ : Type) (m : ℕ) : (RingHom.ker (jetAug R κ m)) ^ (m + 1) = ⊥ := by
  have hle : RingHom.ker (jetAug R κ m) ≤
      (Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R))).map (Ideal.Quotient.mk _) := by
    intro x hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hp : MvPolynomial.aeval (fun _ : κ => (0 : R)) p = 0 := hx
    have := sub_const_mem_span_X (R := R) p
    rw [hp, map_zero, sub_zero] at this
    exact Ideal.mem_map_of_mem _ this
  rw [← le_bot_iff]
  calc (RingHom.ker (jetAug R κ m)) ^ (m + 1)
      ≤ ((Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R))).map (Ideal.Quotient.mk _)) ^ (m + 1) :=
        Ideal.pow_right_mono hle _
    _ = ((Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R))) ^ (m + 1)).map (Ideal.Quotient.mk _) :=
        (Ideal.map_pow _ _ _).symm
    _ = ⊥ := Ideal.map_quotient_self _

theorem ker_jetAug_nil (κ : Type) (m : ℕ) : IsNilpotent (RingHom.ker (jetAug R κ m)) :=
  ⟨m + 1, by rw [ker_jetAug_pow, Ideal.zero_eq_bot]⟩

theorem zR_mem_ker {κ : Type} (m : ℕ) (j : κ) : zR (R := R) m j ∈ RingHom.ker (jetAug R κ m) :=
  jetAug_zR m j

end Jet

section Etale

variable {R : Type} [CommRing R] {n : ℕ} {S : Type} [CommRing S] [Algebra R S]
  [Algebra (MvPolynomial (Fin n) R) S] [IsScalarTower R (MvPolynomial (Fin n) R) S]

variable (R) in

abbrev sX (j : Fin n) : S := algebraMap (MvPolynomial (Fin n) R) S (MvPolynomial.X j)

variable [Algebra.FormallyEtale (MvPolynomial (Fin n) R) S] (ε : S →ₐ[R] R)

theorem etale_ext {A : Type} [CommRing A] [Algebra R A] (aug : A →ₐ[R] R)
    (hJ : IsNilpotent (RingHom.ker aug)) (φ₁ φ₂ : S →ₐ[R] A) (h1 : aug.comp φ₁ = ε) (h2 : aug.comp φ₂ = ε)
    (hs : ∀ j : Fin n, φ₁ (sX (S := S) R j) = φ₂ (sX (S := S) R j)) : φ₁ = φ₂ := by
  let ρ : MvPolynomial (Fin n) R →ₐ[R] A := φ₁.comp (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R) S)
  have hρ2 : φ₂.comp (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R) S) = ρ := by
    apply MvPolynomial.algHom_ext
    intro j
    exact (hs j).symm
  letI : Algebra (MvPolynomial (Fin n) R) A := ρ.toRingHom.toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin n) R) A := IsScalarTower.of_algebraMap_eq (fun r => (ρ.commutes r).symm)
  let ψ₁ : S →ₐ[MvPolynomial (Fin n) R] A :=
    { φ₁.toRingHom with commutes' := fun p => rfl }
  let ψ₂ : S →ₐ[MvPolynomial (Fin n) R] A :=
    { φ₂.toRingHom with commutes' := fun p => AlgHom.congr_fun hρ2 p }
  have : ψ₁ = ψ₂ := by
    apply Algebra.FormallyUnramified.lift_unique (RingHom.ker aug) hJ
    ext x
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero]
    exact (AlgHom.congr_fun h1 x).trans (AlgHom.congr_fun h2 x).symm
  ext x
  exact AlgHom.congr_fun this x

theorem etale_exists {A : Type} [CommRing A] [Algebra R A] (aug : A →ₐ[R] R)
    (hJ : IsNilpotent (RingHom.ker aug)) (b : Fin n → A) (hb : ∀ j, aug (b j) = ε (sX R j)) :
    ∃ φ : S →ₐ[R] A, aug.comp φ = ε ∧ ∀ j, φ (sX R j) = b j := by
  let ρ : MvPolynomial (Fin n) R →ₐ[R] A := MvPolynomial.aeval b
  letI : Algebra (MvPolynomial (Fin n) R) A := ρ.toRingHom.toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin n) R) A := IsScalarTower.of_algebraMap_eq (fun r => (ρ.commutes r).symm)
  let J := RingHom.ker aug
  let mk : A →ₐ[MvPolynomial (Fin n) R] A ⧸ J := Ideal.Quotient.mkₐ _ J
  have hmkR : ∀ a : A, mk a = Ideal.Quotient.mk J (algebraMap R A (aug a)) := by
    intro a
    show Ideal.Quotient.mk J a = Ideal.Quotient.mk J (algebraMap R A (aug a))
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  let f₀r : S →+* A ⧸ J := (Ideal.Quotient.mk J).comp ((algebraMap R A).comp ε.toRingHom)
  have hf₀ : ∀ p : MvPolynomial (Fin n) R, f₀r (algebraMap _ S p) = algebraMap _ (A ⧸ J) p := by
    have : f₀r.comp (algebraMap (MvPolynomial (Fin n) R) S) = algebraMap (MvPolynomial (Fin n) R) (A ⧸ J) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        show Ideal.Quotient.mk J (algebraMap R A (ε (algebraMap (MvPolynomial (Fin n) R) S (MvPolynomial.C r)))) =
          Ideal.Quotient.mk J (ρ (MvPolynomial.C r))
        rw [MvPolynomial.aeval_C, show algebraMap (MvPolynomial (Fin n) R) S (MvPolynomial.C r) = algebraMap R S r from
          (IsScalarTower.algebraMap_apply R (MvPolynomial (Fin n) R) S r).symm, AlgHom.commutes,
          Algebra.algebraMap_self, RingHom.id_apply]
      · intro j
        show Ideal.Quotient.mk J (algebraMap R A (ε (sX R j))) = Ideal.Quotient.mk J (ρ (MvPolynomial.X j))
        rw [MvPolynomial.aeval_X, Ideal.Quotient.eq, RingHom.mem_ker, map_sub, AlgHom.commutes,
          Algebra.algebraMap_self, RingHom.id_apply, hb, sub_self]
    exact fun p => RingHom.congr_fun this p
  let f₀ : S →ₐ[MvPolynomial (Fin n) R] A ⧸ J := { f₀r with commutes' := hf₀ }
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hker : IsNilpotent (RingHom.ker (mk : A →+* A ⧸ J)) := by
    have : RingHom.ker (mk : A →+* A ⧸ J) = J := Ideal.mk_ker
    rw [this]
    exact hJ
  let φ' := Algebra.FormallySmooth.liftOfSurjective f₀ mk hmk hker
  have hφ' : mk.comp φ' = f₀ := Algebra.FormallySmooth.comp_liftOfSurjective f₀ mk hmk hker
  refine ⟨φ'.restrictScalars R, ?_, ?_⟩
  · ext x
    have e1 := AlgHom.congr_fun hφ' x
    simp only [AlgHom.comp_apply] at e1
    rw [hmkR] at e1
    have e2 : (Ideal.Quotient.mk J) (algebraMap R A (aug (φ' x))) = (Ideal.Quotient.mk J) (algebraMap R A (ε x)) := e1
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, RingHom.id_apply, sub_eq_zero] at e2
    exact e2
  · intro j
    show φ' (algebraMap (MvPolynomial (Fin n) R) S (MvPolynomial.X j)) = b j
    rw [AlgHom.commutes]
    show ρ (MvPolynomial.X j) = b j
    exact MvPolynomial.aeval_X b j

end Etale

end ReciprocityTheory.ChartRestriction.G.Chart
