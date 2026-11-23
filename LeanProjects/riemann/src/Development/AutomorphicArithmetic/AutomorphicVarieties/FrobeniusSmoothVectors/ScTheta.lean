import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HthPlace

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.sc_theta :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (w : ℕ), w.Prime → w ≡ 1 [MOD l] → ∃ θ : G ℚ Ω →* (Qbar l)ˣ, θ.ker = Hth Ω l w ∧ θ ≠ 1 ∧ θ ^ l = 1 ∧ Af.KillsMu w θ := by
  intro Ω _ _ _ l _ w hw hwl
  obtain ⟨-, hc, hidx, -, -⟩ := hth Ω l w hw hwl
  haveI hN : (Hth Ω l w).Normal := ⟨fun n hn g => by
    have h0 := Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n)
    rw [commutatorElement_def] at h0
    have h1 := hc h0
    have h2 : g * n * g⁻¹ = g * n * g⁻¹ * n⁻¹ * n := by group
    rw [h2]
    exact (Hth Ω l w).mul_mem h1 hn⟩
  have hcardQ : Nat.card (G ℚ Ω ⧸ Hth Ω l w) = l := hidx
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Qbar l) l
  have hcardR : Nat.card (rootsOfUnity l (Qbar l)) = l := hζ.card_rootsOfUnity
  let e := mulEquivOfPrimeCardEq hcardQ hcardR
  let θ : G ℚ Ω →* (Qbar l)ˣ :=
    (rootsOfUnity l (Qbar l)).subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' (Hth Ω l w)))
  have hθ : ∀ s, θ s = ((e (QuotientGroup.mk' (Hth Ω l w) s) : rootsOfUnity l (Qbar l)) : (Qbar l)ˣ) :=
    fun s => rfl
  have hker : θ.ker = Hth Ω l w := by
    ext s
    rw [MonoidHom.mem_ker, hθ]
    constructor
    · intro h
      have h' : e (QuotientGroup.mk' (Hth Ω l w) s) = 1 := Subtype.ext h
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h'
      exact h'
    · intro h
      have h' : QuotientGroup.mk' (Hth Ω l w) s = 1 := (QuotientGroup.eq_one_iff s).mpr h
      rw [h', map_one]
      rfl
  refine ⟨θ, hker, ?_, ?_, ?_⟩
  · intro h1
    have htop : Hth Ω l w = ⊤ := by rw [← hker, h1, MonoidHom.ker_one]
    rw [htop, Subgroup.index_top] at hidx
    exact (Fact.out : l.Prime).one_lt.ne hidx
  · ext s
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, hθ]
    exact congrArg Units.val ((mem_rootsOfUnity _ _).mp (e (QuotientGroup.mk' (Hth Ω l w) s)).2)
  · unfold Af.KillsMu
    intro s hs
    rw [← MonoidHom.mem_ker, hker]
    unfold Hth
    refine ⟨⟨1, fun z hz => ?_⟩, ⟨1, fun z hz => ?_⟩⟩
    · rw [one_pow, pow_one]
      exact hs z hz
    · rw [one_pow, pow_one]
      have e1 := congrArg (s⁻¹ : G ℚ Ω) (hs z hz)
      rw [← e1]
      simp
