import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartFilt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresMaximalIdealGrZeroEqSupSpanMonomials

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem UpperTheory.V.Ws.sxContGr_pow {Λ K R : Type} [CommRing Λ] [CommRing K] [CommRing R] [Algebra Λ K] [Algebra Λ R]
    (e : K →ₐ[Λ] R) (J : Ideal K) (Q : Submodule Λ R) (hQ : ∀ x ∈ Q, ∃ y ∈ J, e y = x) (n : ℕ) :
    ∀ x ∈ Q ^ n, ∃ y ∈ J ^ n, e y = x := by
  induction n with
  | zero =>
    intro x hx
    rw [pow_zero, Submodule.one_eq_range] at hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨algebraMap Λ K a, by simp, e.commutes a⟩
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := ih a ha
      obtain ⟨v, hv, rfl⟩ := hQ b hb
      exact ⟨u * v, by rw [pow_succ]; exact Ideal.mul_mem_mul hu hv, map_mul e u v⟩
    · rintro a b ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
      exact ⟨u + v, add_mem hu hv, map_add e u v⟩

private theorem UpperTheory.V.Ws.sxContGr_mul {Λ K R : Type} [CommRing Λ] [CommRing K] [CommRing R] [Algebra Λ K] [Algebra Λ R]
    (e : K →ₐ[Λ] R) (J : Ideal K) (Q P : Submodule Λ R) (hQ : ∀ x ∈ Q, ∃ y ∈ J, e y = x)
    (hP : ∀ x ∈ P, ∃ y, e y = x) : ∀ x ∈ Q * P, ∃ y ∈ J, e y = x := by
  intro x hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := hQ a ha
    obtain ⟨v, rfl⟩ := hP b hb
    exact ⟨u * v, J.mul_mem_right v hu, map_mul e u v⟩
  · rintro a b ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    exact ⟨u + v, add_mem hu hv, map_add e u v⟩

private theorem UpperTheory.V.Ws.sxContGr_cont {Λ K R Γ : Type} [CommRing Λ] [CommRing K] [CommRing R] [Algebra Λ K] [Algebra Λ R]
    [TopologicalSpace Γ] (e : K →ₐ[Λ] R) (he : Function.Injective e) (I : Ideal R) (J : Ideal K) (Q P P' : Submodule Λ R)
    (hQ : ∀ x ∈ Q, ∃ y ∈ J, e y = x) (hP : ∀ x ∈ P, ∃ y, e y = x) (hP' : ∀ x ∈ P', ∃ y, e y = x)
    (h : ∀ n : ℕ, ∃ M : ℕ, P' ⊓ (I ^ M).restrictScalars Λ ≤ Q ^ n * P * P')
    (φ : Γ → K) (hφ : ∀ g, e (φ g) ∈ P') (hc : AdicCont I fun g => e (φ g)) : AdicCont J φ := by
  intro N
  obtain ⟨M, hM⟩ := h N
  have key : ∀ x ∈ Q ^ N * P * P', ∃ y ∈ J ^ N, e y = x := by
    intro x hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := UpperTheory.V.Ws.sxContGr_mul e (J ^ N) (Q ^ N) P
        (UpperTheory.V.Ws.sxContGr_pow e J Q hQ N) hP a ha
      obtain ⟨v, rfl⟩ := hP' b hb
      exact ⟨u * v, (J ^ N).mul_mem_right v hu, map_mul e u v⟩
    · rintro a b ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
      exact ⟨u + v, add_mem hu hv, map_add e u v⟩
  have hcM : IsLocallyConstant fun g => (Ideal.Quotient.mk (I ^ M)) (e (φ g)) := hc M
  refine (IsLocallyConstant.iff_exists_open _).2 fun g0 => ?_
  refine ⟨{g | (Ideal.Quotient.mk (I ^ M)) (e (φ g)) = (Ideal.Quotient.mk (I ^ M)) (e (φ g0))},
    hcM.isOpen_fiber _, rfl, fun g hg => ?_⟩
  have hd : e (φ g) - e (φ g0) ∈ I ^ M := Ideal.Quotient.eq.1 hg
  have hd' : e (φ g) - e (φ g0) ∈ P' ⊓ (I ^ M).restrictScalars Λ :=
    Submodule.mem_inf.2 ⟨sub_mem (hφ g) (hφ g0), (Submodule.restrictScalars_mem _ _ _).2 hd⟩
  obtain ⟨y, hy, hye⟩ := key _ (hM hd')
  rw [← map_sub] at hye
  have : y = φ g - φ g0 := he hye
  exact Ideal.Quotient.eq.2 (this ▸ hy)

theorem UpperTheory.V.Ws.sxContGr :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (W : WPres Λ X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ [IsCO Λ (W.gr 0)] {Γ : Type} [TopologicalSpace Γ], (∀ (j : X) (φ : Γ → W.A), (∀ g, φ g ∈ W.gr j) → AdicCont (maximalIdeal R) (fun g => (φ g : R)) → AdicCont ((maximalIdeal (W.gr 0)).map (algebraMap (W.gr 0) W.A)) φ) ∧ ∀ φ : Γ → W.gr 0, AdicCont (maximalIdeal R) (fun g => ((φ g : W.A) : R)) → AdicCont (maximalIdeal (W.gr 0)) φ := by
  intro Λ _ _ _ _ X _ _ _ _ R _ _ _ W hz _ Γ _
  obtain ⟨hmax, -⟩ := wPres_maximalIdeal_gr_zero_eq_sup_span_monomials Λ X R W hz
  have hfilt := part_filt Λ X R W hz
  have hb : ∀ b : W.gr 0, algebraMap (W.gr 0) W.A b = (b : W.A) := fun b => by first | rfl | simp
  have ha : ∀ a : Λ, ((algebraMap Λ (W.gr 0) a : W.A) : R) = algebraMap Λ R a :=
    fun a => by first | rfl | simp
  refine ⟨fun j φ hφ hc => ?_, fun φ hc => ?_⟩
  · refine UpperTheory.V.Ws.sxContGr_cont W.A.val Subtype.val_injective (maximalIdeal R)
      ((maximalIdeal (W.gr 0)).map (algebraMap (W.gr 0) W.A))
      (W.part 0 ⊓ (maximalIdeal R).restrictScalars Λ) (W.part 0) (W.part j) ?_ ?_ ?_
      (fun n => hfilt j n) φ (fun g => hφ g) hc
    · intro x hx
      obtain ⟨hx0, hxm⟩ := Submodule.mem_inf.1 hx
      refine ⟨algebraMap (W.gr 0) W.A ⟨⟨x, W.part_le_A hx0⟩, hx0⟩,
        Ideal.mem_map_of_mem _ ((hmax _).2 ((Submodule.restrictScalars_mem _ _ _).1 hxm)), ?_⟩
      rw [hb]
      rfl
    · exact fun x hx => ⟨⟨x, W.part_le_A hx⟩, rfl⟩
    · exact fun x hx => ⟨⟨x, W.part_le_A hx⟩, rfl⟩
  · let e : W.gr 0 →ₐ[Λ] R := AlgHom.mk ((W.A.val : W.A →+* R).comp (algebraMap (W.gr 0) W.A))
      (fun a => by
        show W.A.val (algebraMap (W.gr 0) W.A (algebraMap Λ (W.gr 0) a)) = _
        rw [hb]
        exact ha a)
    have he : ∀ b : W.gr 0, e b = ((b : W.A) : R) := fun b => by
      show W.A.val (algebraMap (W.gr 0) W.A b) = _
      rw [hb]
      rfl
    have hinj : Function.Injective e := by
      intro b c hbc
      rw [he, he] at hbc
      exact Subtype.ext (Subtype.ext hbc)
    have hc' : AdicCont (maximalIdeal R) fun g => e (φ g) := by
      have hfun : (fun g => e (φ g)) = fun g => ((φ g : W.A) : R) := funext fun g => he _
      rw [hfun]
      exact hc
    refine UpperTheory.V.Ws.sxContGr_cont e hinj (maximalIdeal R) (maximalIdeal (W.gr 0))
      (W.part 0 ⊓ (maximalIdeal R).restrictScalars Λ) (W.part 0) (W.part 0) ?_ ?_ ?_
      (fun n => hfilt 0 n) φ (fun g => by rw [he]; exact (φ g).2) hc'
    · intro x hx
      obtain ⟨hx0, hxm⟩ := Submodule.mem_inf.1 hx
      exact ⟨⟨⟨x, W.part_le_A hx0⟩, hx0⟩,
        (hmax _).2 ((Submodule.restrictScalars_mem _ _ _).1 hxm), he _⟩
    · exact fun x hx => ⟨⟨⟨x, W.part_le_A hx⟩, hx⟩, he _⟩
    · exact fun x hx => ⟨⟨⟨x, W.part_le_A hx⟩, hx⟩, he _⟩
