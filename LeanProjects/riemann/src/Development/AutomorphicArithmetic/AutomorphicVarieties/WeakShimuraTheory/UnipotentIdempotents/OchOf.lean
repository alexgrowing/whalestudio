import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuChi

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.ochOf :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} (Q : QCh T) (c' : Coef l) (h : c.O ≤ c'.O) (κ β : G T.L Ω →* c'.Oˣ), toQ κ = Q.κ → toQ β = Q.β → (AdicCont (maximalIdeal c'.O) fun g => (κ g : c'.O)) → (AdicCont (maximalIdeal c'.O) fun g => (β g : c'.O)) → (∀ g, residue c'.O (β g) = 1) → Nonempty (OCh T c' h) := by
  intro Ω _ _ _ l _ c D T Q c' h κ β hκQ hβQ hκc hβc hβr
  let U : (c'.O)ˣ →* (PadicAlgCl l)ˣ := Units.map (algebraMap c'.O (PadicAlgCl l) : c'.O →* PadicAlgCl l)
  have hUinj : Function.Injective U := fun a b hab => Units.ext (Subtype.val_injective (congrArg Units.val hab))
  have hUκ : ∀ g, U (κ g) = Q.κ g := fun g => by
    rw [← hκQ]
    rfl
  have hUβ : ∀ g, U (β g) = Q.β g := fun g => by
    rw [← hβQ]
    rfl
  have hUchi : ∀ g, U (chiO T.L Ω l c'.O g) = cycBar T.L Ω l g := fun g => by
    rw [← (auChi T.L Ω c').1]
    rfl
  have hUth : ∀ r, ((inc h (D.th r : c.O) : c'.O) : PadicAlgCl l) = ((toQ D.th r : (PadicAlgCl l)ˣ) : PadicAlgCl l) := fun r => rfl
  refine ⟨{ κ := κ, β := β, t := Q.t, κ_cont := hκc, β_cont := hβc, t_cont := Q.t_cont, β_t := ?_, β_red := hβr, conj := ?_, t_unr := Q.t_unr, unr := ?_, tame := ?_, mu := ?_, cyc := ?_ }⟩
  · intro g hg
    have h1 := Q.β_t hg
    rw [MonoidHom.mem_ker] at h1 ⊢
    apply hUinj
    rw [hUβ, map_one]
    exact h1
  · intro σ hσ g g' hg
    obtain ⟨e1, e2, e3⟩ := Q.conj σ hσ g g' hg
    refine ⟨?_, ?_, e3⟩
    · apply Subtype.val_injective
      have e1' := congrArg Units.val e1
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one] at e1'
      have k1 : ((κ g : c'.O) : PadicAlgCl l) = (Q.κ g : PadicAlgCl l) := congrArg Units.val (hUκ g)
      have k2 : ((κ g' : c'.O) : PadicAlgCl l) = (Q.κ g' : PadicAlgCl l) := congrArg Units.val (hUκ g')
      have k3 : ((chiO T.L Ω l c'.O g : c'.O) : PadicAlgCl l) = (cycBar T.L Ω l g : PadicAlgCl l) := congrArg Units.val (hUchi g)
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, OneMemClass.coe_one, k1, k2, k3, hUth]
      exact e1'
    · apply hUinj
      rw [map_mul, hUβ, hUβ, map_one]
      exact e2
  · intro A hA g hg
    have h1 := Q.unr A hA hg
    rw [MonoidHom.mem_ker] at h1 ⊢
    apply hUinj
    rw [hUκ, map_one]
    exact h1
  · obtain ⟨m, hm, hmA⟩ := Q.tame
    refine ⟨m, hm, fun A hA g hg => hUinj ?_⟩
    rw [map_pow, hUκ, map_one]
    exact hmA A hA g hg
  · intro g a ha
    refine ⟨hUinj ?_, (Q.mu g a ha).2⟩
    rw [hUκ, map_one]
    exact (Q.mu g a ha).1
  · intro A hA
    obtain ⟨a, b, k, hk, hb, hall⟩ := Q.cyc A hA
    refine ⟨a, b, k, hk, hb, fun g hg => ⟨hUinj ?_, hUinj ?_⟩⟩
    · rw [map_pow, map_mul, map_zpow, hUκ, hUchi, map_one]
      exact (hall g hg).1
    · rw [map_pow, map_mul, map_pow, map_zpow, hUβ, hUchi, map_one]
      exact (hall g hg).2
