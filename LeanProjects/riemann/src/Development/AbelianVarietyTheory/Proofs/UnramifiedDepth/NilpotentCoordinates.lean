import Mathlib
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NilCoord

section Alg

variable {R : Type} [CommRing R] {n : ℕ} {B : Type} [CommRing B] [Algebra R B]

theorem ext_of_nil (π : MvPolynomial (Fin n) R →ₐ[R] B) (hπ : π.toRingHom.Etale)
    {A : Type} [CommRing A] [Algebra R A] (φ₁ φ₂ : B →ₐ[R] A)
    (h : ∀ b, IsNilpotent (φ₁ b - φ₂ b))
    (hs : ∀ j : Fin n, φ₁ (π (MvPolynomial.X j)) = φ₂ (π (MvPolynomial.X j))) : φ₁ = φ₂ := by
  letI : Algebra (MvPolynomial (Fin n) R) B := π.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin n) R) B := hπ
  let ρ : MvPolynomial (Fin n) R →ₐ[R] A := φ₁.comp π
  have hρ2 : φ₂.comp π = ρ := by
    apply MvPolynomial.algHom_ext
    intro j
    exact (hs j).symm
  letI : Algebra (MvPolynomial (Fin n) R) A := ρ.toRingHom.toAlgebra
  let ψ₁ : B →ₐ[MvPolynomial (Fin n) R] A :=
    { φ₁.toRingHom with commutes' := fun p => rfl }
  let ψ₂ : B →ₐ[MvPolynomial (Fin n) R] A :=
    { φ₂.toRingHom with commutes' := fun p => AlgHom.congr_fun hρ2 p }
  obtain ⟨s, hsg⟩ := (inferInstance : Algebra.FiniteType (MvPolynomial (Fin n) R) B).out
  let J : Ideal A := Ideal.span ((fun b => φ₁ b - φ₂ b) '' (s : Set B))
  have hJ : IsNilpotent J := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical
      (Submodule.fg_span (s.finite_toSet.image _)), Ideal.span_le]
    rintro _ ⟨b, -, rfl⟩
    exact h b
  have : ψ₁ = ψ₂ := by
    apply Algebra.FormallyUnramified.lift_unique J hJ
    apply AlgHom.ext_of_adjoin_eq_top hsg
    intro b hb
    simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq]
    exact Ideal.subset_span ⟨b, hb, rfl⟩
  ext x
  exact AlgHom.congr_fun this x

theorem exists_of_nil (π : MvPolynomial (Fin n) R →ₐ[R] B) (hπ : π.toRingHom.Etale)
    {A : Type} [CommRing A] [Algebra R A] (e : B →ₐ[R] A) (a : Fin n → A)
    (ha : ∀ j, IsNilpotent (a j)) :
    ∃ φ : B →ₐ[R] A, (∀ b, IsNilpotent (φ b - e b)) ∧
      ∀ j, φ (π (MvPolynomial.X j)) = e (π (MvPolynomial.X j)) + a j := by
  letI : Algebra (MvPolynomial (Fin n) R) B := π.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin n) R) B := hπ
  let ρ : MvPolynomial (Fin n) R →ₐ[R] A :=
    MvPolynomial.aeval (fun j => e (π (MvPolynomial.X j)) + a j)
  letI : Algebra (MvPolynomial (Fin n) R) A := ρ.toRingHom.toAlgebra
  let J : Ideal A := Ideal.span (Set.range a)
  have hJ : IsNilpotent J := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical
      (Submodule.fg_span (Set.finite_range _)), Ideal.span_le]
    rintro _ ⟨b, rfl⟩
    exact ha b
  let mk : A →ₐ[MvPolynomial (Fin n) R] A ⧸ J := Ideal.Quotient.mkₐ _ J
  have hf₀ : ((Ideal.Quotient.mkₐ R J).comp e).comp π = (Ideal.Quotient.mkₐ R J).comp ρ := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ρ,
      MvPolynomial.aeval_X]
    rw [eq_comm, Ideal.Quotient.eq, add_sub_cancel_left]
    exact Ideal.subset_span ⟨j, rfl⟩
  let f₀ : B →ₐ[MvPolynomial (Fin n) R] A ⧸ J :=
    { ((Ideal.Quotient.mkₐ R J).comp e).toRingHom with
      commutes' := fun p => AlgHom.congr_fun hf₀ p }
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hker : IsNilpotent (RingHom.ker (mk : A →+* A ⧸ J)) := by
    have : RingHom.ker (mk : A →+* A ⧸ J) = J := Ideal.mk_ker
    rw [this]
    exact hJ
  let φ' := Algebra.FormallySmooth.liftOfSurjective f₀ mk hmk hker
  have hφ' : mk.comp φ' = f₀ := Algebra.FormallySmooth.comp_liftOfSurjective f₀ mk hmk hker
  have hc : ∀ p, φ' (π p) = ρ p := fun p => φ'.commutes p
  refine ⟨{ φ'.toRingHom with commutes' := fun r => ?_ }, fun b => ?_, fun j => ?_⟩
  · show φ' (algebraMap R B r) = _
    rw [← π.commutes, hc, ρ.commutes]
  · have e1 : Ideal.Quotient.mk J (φ' b) = Ideal.Quotient.mk J (e b) := AlgHom.congr_fun hφ' b
    rw [Ideal.Quotient.eq] at e1
    obtain ⟨N, hN⟩ := hJ
    refine ⟨N, ?_⟩
    have := Ideal.pow_mem_pow e1 N
    rw [hN, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact this
  · show φ' (π _) = _
    rw [hc]
    exact MvPolynomial.aeval_X _ j

end Alg

theorem exists_etale_chart {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G]
    [IsLocalRing R₀] (g : ℕ) (hG : SmoothOfRelativeDimension g G.hom) :
    ∃ (C : Chart G) (π : MvPolynomial (Fin g) R₀ →ₐ[R₀] Γ(G.left, C.U)), π.toRingHom.Etale := by
  let e0 : Spec (CommRingCat.of R₀) ⟶ G.left := (η[G]).left
  obtain ⟨U, hU, V, hV, hx, e, h⟩ :=
    hG.exists_isStandardSmoothOfRelativeDimension (e0 (IsLocalRing.closedPoint R₀))
  have hsp : ∀ p : PrimeSpectrum R₀, p ⤳ IsLocalRing.closedPoint R₀ := fun p =>
    (PrimeSpectrum.le_iff_specializes _ _).mp
      (IsLocalRing.le_maximalIdeal (p : PrimeSpectrum R₀).isPrime.ne_top)
  have hw : e0 ≫ G.hom = 𝟙 _ := Over.w (η[G])
  have hU' : U = ⊤ := by
    rw [eq_top_iff]
    intro p _
    refine (hsp p).mem_open U.isOpen ?_
    have h1 : (e0 ≫ G.hom) (IsLocalRing.closedPoint R₀) ∈ U := by
      exact (Scheme.Hom.comp_apply e0 G.hom (IsLocalRing.closedPoint R₀)).symm ▸ e hx
    rw [hw] at h1
    exact h1
  subst hU'
  let C : Chart G := ⟨V, hV, fun p _ => (hsp p).mem_open (e0 ⁻¹ᵁ V).isOpen hx⟩
  have h2 : RingHom.IsStandardSmoothOfRelativeDimension g (alg0 C) :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of R₀)).symm.commRingCatIsoToRingEquiv h
  obtain ⟨π, hπ1, hπ2⟩ := h2.exists_etale_mvPolynomial
  clear_value C
  exact ⟨C, { π with commutes' := fun r => RingHom.congr_fun hπ1 r }, hπ2⟩

theorem nilpotent_coordinates :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] [IsLocalRing R₀] (g : ℕ), SmoothOfRelativeDimension g G.hom →
    ∃ x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G),
      (∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : Fin g → S),
        (∀ i, IsNilpotent (a i)) → spMap φ ≫ x S a = x S' (fun i => φ (a i))) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (ρ : S →ₐ[R₀] S'), Function.Surjective ρ →
        (∀ a ∈ RingHom.ker ρ, IsNilpotent a) → ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
        ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)) := by
  intro R₀ _ G _ _ _ g hG
  classical
  obtain ⟨C, π, hπ⟩ := exists_etale_chart G g hG
  have key : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S),
      ∃ φ : Γ(G.left, C.U) →ₐ[R₀] S, (∀ i, IsNilpotent (a i)) →
        (∀ b, IsNilpotent (φ b - algebraMap R₀ S (eps C b))) ∧
        ∀ j, φ (π (MvPolynomial.X j)) = algebraMap R₀ S (eps C (π (MvPolynomial.X j))) + a j := by
    intro S _ _ a
    by_cases ha : ∀ i, IsNilpotent (a i)
    · obtain ⟨φ, h⟩ := exists_of_nil π hπ ((Algebra.ofId R₀ S).comp (eps C)) a ha
      exact ⟨φ, fun _ => h⟩
    · exact ⟨(Algebra.ofId R₀ S).comp (eps C), fun h => absurd h ha⟩
  choose F hF using key
  have uniq : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S) (φ : Γ(G.left, C.U) →ₐ[R₀] S),
      (∀ i, IsNilpotent (a i)) → (∀ b, IsNilpotent (φ b - algebraMap R₀ S (eps C b))) →
      (∀ j, φ (π (MvPolynomial.X j)) = algebraMap R₀ S (eps C (π (MvPolynomial.X j))) + a j) →
      φ = F S a := by
    intro S _ _ a φ ha h1 h2
    refine ext_of_nil π hπ _ _ (fun b => ?_) (fun j => ?_)
    · have := (Commute.all _ _).isNilpotent_sub (h1 b) ((hF S a ha).1 b)
      rwa [sub_sub_sub_cancel_right] at this
    · rw [h2, (hF S a ha).2]
  refine ⟨fun S _ _ a => pt C (F S a), ?_, ?_, ?_, ?_⟩
  · intro S _ _
    show pt C (F S 0) = 1
    rw [← uniq S 0 ((Algebra.ofId R₀ S).comp (eps C)) (fun _ => IsNilpotent.zero)
      (fun b => by simp [Algebra.ofId_apply]) (fun j => by simp [Algebra.ofId_apply]), pt_eps]
  · intro S _ _ S' _ _ φ a ha
    show spMap φ ≫ pt C (F S a) = pt C (F S' _)
    rw [spMap_pt]
    congr 1
    refine uniq S' _ _ (fun i => (ha i).map φ) (fun b => ?_) (fun j => ?_)
    · have := ((hF S a ha).1 b).map φ
      rwa [map_sub, AlgHom.commutes] at this
    · rw [AlgHom.comp_apply, (hF S a ha).2, map_add, AlgHom.commutes]
  · intro S _ _ a b ha hb h
    have h1 : F S a = F S b := pt_injective C h
    funext j
    have h2 := (hF S a ha).2 j
    rw [h1, (hF S b hb).2 j] at h2
    exact (add_left_cancel h2).symm
  · intro S _ _ S' _ _ ρ hρ hn z hz
    rw [← pt_eps C S'] at hz
    obtain ⟨φ, rfl⟩ := exists_pt C z (le_preimage_of_nil C ρ hρ hn z _ hz)
    rw [spMap_pt] at hz
    have h1 := pt_injective C hz
    have h2 : ∀ b, φ b - algebraMap R₀ S (eps C b) ∈ RingHom.ker ρ := by
      intro b
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero]
      exact AlgHom.congr_fun h1 b
    refine ⟨fun j => φ (π (MvPolynomial.X j)) - algebraMap R₀ S (eps C (π (MvPolynomial.X j))),
      fun j => h2 _, ?_⟩
    show pt C φ = pt C (F S _)
    congr 1
    exact uniq S _ φ (fun j => hn _ (h2 _)) (fun b => hn _ (h2 b)) (fun j => by rw [add_sub_cancel])

end GlobalTheory.NilCoord
