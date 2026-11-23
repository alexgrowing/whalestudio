import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistTwD
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.Fourier

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5 GlobalTheory.GalOfCusp

private theorem lift_map {A K Q : Type} [CommRing A] [CommRing K] [CommGroup Q] (x : A →+* K) (χ : Q →* K) :
    ∃ e : MonoidAlgebra A Q →+* K, (∀ a, e (algebraMap A _ a) = x a) ∧ (∀ z, e (MonoidAlgebra.single z 1) = χ z) ∧
      ∀ y, e y = MonoidAlgebra.lift K K Q χ (MonoidAlgebra.mapRingHom Q x y) := by
  refine ⟨(MonoidAlgebra.lift K K Q χ).toRingHom.comp (MonoidAlgebra.mapRingHom Q x), ?_, ?_, fun y => rfl⟩
  · intro a
    simp [MonoidAlgebra.coe_algebraMap, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.lift_single]
  · intro z
    simp [MonoidAlgebra.mapRingHom_single, MonoidAlgebra.lift_single]

theorem UpperTheory.V.Ws.H5.levelJ :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V.frame c.O n} (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B), B.Dense J → B.TwistOk J → ∀ (Q : Type) [CommGroup Q] [Finite Q], IsPGroup l Q → ∀ q : V.frame.G₀ →* Q, IsOpen (q.ker : Set V.frame.G₀) → Anti V.frame q → ∀ tw : B.B →ₐ[c.O] MonoidAlgebra B.B Q, TwMap B (algebraMap B.B (MonoidAlgebra B.B Q)) (tw : B.B →+* MonoidAlgebra B.B Q) ((MonoidAlgebra.of B.B Q).toHomUnits.comp q) → ∀ b ∈ J, ∀ z : Q, (tw b).coeff z ∈ J := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B J hD hT Q _ _ hQ q hq hA tw htw b hb z
  let h0 : s.Wt n := fun _ j _ => (j : ℤ)
  have hinc : h0.Incr := by
    intro v τ a a' hlt
    show ((a : ℕ) : ℤ) < ((a' : ℕ) : ℤ)
    exact_mod_cast hlt
  refine hD h0 hinc _ ?_
  intro x hxJ hxG
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := l) (G := Q)).1 hQ
  have hzero : MonoidAlgebra.mapRingHom Q (x : B.B →+* Qbar l) (tw b) = 0 := by
    apply Ws.H5.fourier (Qbar l) Q
    intro χ
    obtain ⟨e, he1, he2, he3⟩ := lift_map (x : B.B →+* Qbar l) ((Units.coeHom (Qbar l)).comp χ)
    rw [← he3]
    let β : V.frame.G₀ →* (Qbar l)ˣ := χ.comp q
    let x' : B.Pt :=
      { toRingHom := e.comp (tw : B.B →+* MonoidAlgebra B.B Q)
        commutes' := by
          intro o
          show e (tw (algebraMap c.O B.B o)) = algebraMap c.O (Qbar l) o
          rw [tw.commutes, IsScalarTower.algebraMap_apply c.O B.B (MonoidAlgebra B.B Q), he1]
          exact x.commutes o }
    have hker : q.ker ≤ β.ker := by
      intro g hg
      rw [MonoidHom.mem_ker] at hg ⊢
      show χ (q g) = 1
      rw [hg, map_one]
    have htw' : TwMap B (x : B.B →+* Qbar l) (x' : B.B →+* Qbar l) β := by
      have h2 := htw.comp e
      have ea : e.comp (algebraMap B.B (MonoidAlgebra B.B Q)) = (x : B.B →+* Qbar l) := by
        ext a
        exact he1 a
      have eb : pushCh e ((MonoidAlgebra.of B.B Q).toHomUnits.comp q) = β := by
        ext g
        exact he2 (q g)
      rw [ea, eb] at h2
      exact h2
    have hx'J : J ≤ RingHom.ker (x' : B.B →+* Qbar l) := by
      refine hT x x' h0 β hxJ hxG (Subgroup.isOpen_mono hker hq) ⟨k, ?_⟩ ?_ ?_ ?_ ?_ ?_
      · ext g
        show (χ (q g) ^ l ^ k : (Qbar l)ˣ).1 = 1
        rw [← map_pow, ← hk, pow_card_eq_one', map_one]
        rfl
      · ext g
        show (χ (q (V.frame.conj g)) : Qbar l) = ((χ (q g))⁻¹ : (Qbar l)ˣ)
        rw [eq_inv_of_mul_eq_one_left (hA.conj g), map_inv]
      · intro u
        exact (hA.iu u).trans hker
      · exact hA.i0.trans hker
      · exact isTwistOf B _ _ β htw'
      · intro v j
        ext g
        show e (tw ((B.u.ψ v j g : (B.B)ˣ) : B.B)) = x ((B.u.ψ v j g : (B.B)ˣ) : B.B) * (χ (q (V.pr (g : G L Ω))) : Qbar l)
        refine (congrArg e (htw.2 v j g)).trans ?_
        rw [map_mul, he1]
        congr 1
        exact he2 _
    exact hx'J hb
  have := congrArg (fun y => y.coeff z) hzero
  simp only [MonoidAlgebra.mapRingHom_apply] at this
  exact this
