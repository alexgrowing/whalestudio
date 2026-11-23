import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

noncomputable section

namespace UpperTheory.V.Pa.B2

section Pull

variable {A Γ Γ' : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ']

private def pull (p : Γ →* Γ') (hp : Continuous p) (M : FRep A Γ') : FRep A Γ where
  X := M.X
  ρ := M.ρ.comp p
  cont := M.cont.comp (hp.prodMap continuous_id)

variable (p : Γ ≃* Γ') (hp : Continuous p) (hq : Continuous p.symm) (M : FRep A Γ')

private def r1 : H1 M.ρ →ₗ[A] H1 (pull p.toMonoidHom hp M).ρ :=
  pairH1DecompositionMap M.ρ (pull p.toMonoidHom hp M).ρ p.toMonoidHom hp LinearMap.id continuous_id fun _ _ => rfl

private def r2 : H2 M.ρ →ₗ[A] H2 (pull p.toMonoidHom hp M).ρ :=
  compatiblePairH2 M.ρ (pull p.toMonoidHom hp M).ρ p.toMonoidHom hp LinearMap.id continuous_id fun _ _ => rfl

private theorem back (g : Γ') (m : M.X) : (pull p.toMonoidHom hp M).ρ (p.symm g) m = M.ρ g m := by
  show M.ρ (p.toMonoidHom (p.symm g)) m = M.ρ g m
  simp

include hq in
private theorem restriction_one_bijective : Function.Bijective (r1 p hp M) := by
  let s : H1 (pull p.toMonoidHom hp M).ρ →ₗ[A] H1 M.ρ :=
    pairH1DecompositionMap (pull p.toMonoidHom hp M).ρ M.ρ p.symm.toMonoidHom hq LinearMap.id continuous_id
      fun g m => back p hp M g m
  refine Function.bijective_iff_has_inverse.mpr ⟨s, fun x => ?_, fun x => ?_⟩
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [s, r1, pairH1DecompositionMap, Submodule.mapQ_apply]
    congr 1
    ext g
    exact congrArg z.1 (p.apply_symm_apply g)
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [s, r1, pairH1DecompositionMap, Submodule.mapQ_apply]
    congr 1
    ext g
    exact congrArg z.1 (p.symm_apply_apply g)

include hq in
private theorem restriction_two_bijective : Function.Bijective (r2 p hp M) := by
  let s : H2 (pull p.toMonoidHom hp M).ρ →ₗ[A] H2 M.ρ :=
    compatiblePairH2 (pull p.toMonoidHom hp M).ρ M.ρ p.symm.toMonoidHom hq LinearMap.id continuous_id
      fun g m => back p hp M g m
  refine Function.bijective_iff_has_inverse.mpr ⟨s, fun x => ?_, fun x => ?_⟩
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [s, r2, compatiblePairH2, Submodule.mapQ_apply]
    congr 1
    ext g
    exact congrArg z.1 (Prod.ext (p.apply_symm_apply g.1) (p.apply_symm_apply g.2))
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [s, r2, compatiblePairH2, Submodule.mapQ_apply]
    congr 1
    ext g
    exact congrArg z.1 (Prod.ext (p.symm_apply_apply g.1) (p.symm_apply_apply g.2))

private theorem card_H0_pullback_eq : Nat.card (H0 (pull p.toMonoidHom hp M).ρ) = Nat.card (H0 M.ρ) := by
  have e : H0 (pull p.toMonoidHom hp M).ρ = H0 M.ρ := by
    ext m
    simp only [H0, Representation.mem_invariants]
    constructor
    · intro h g
      rw [← back p hp M g m]
      exact h _
    · intro h g
      exact h (p g)
  rw [e]
  rfl

include hp hq in
private theorem finH_iso (l : ℕ) (h : FinH l Γ) : FinH l Γ' := by
  intro A _ M hl
  obtain ⟨h1, h2⟩ := h A (pull p.toMonoidHom hp M) hl
  exact ⟨Finite.of_equiv _ (Equiv.ofBijective _ (restriction_one_bijective p hp hq M)).symm,
    Finite.of_equiv _ (Equiv.ofBijective _ (restriction_two_bijective p hp hq M)).symm⟩

include hp hq in
private theorem onto_iso (l : ℕ) (h : SecondCohomologyRightExactModL l Γ) : SecondCohomologyRightExactModL l Γ' := by
  intro A _ M M' hl u hu hs y
  have hu' : ∀ (g : Γ) (m : (pull p.toMonoidHom hp M).X),
      u ((pull p.toMonoidHom hp M).ρ g m) = (pull p.toMonoidHom hp M').ρ g (u m) :=
    fun g m => hu (p g) m
  have key : ∀ x, r2 p hp M' (mapH2 M.ρ M'.ρ u continuous_of_discreteTopology hu x) =
      mapH2 (pull p.toMonoidHom hp M).ρ (pull p.toMonoidHom hp M').ρ u continuous_of_discreteTopology hu'
        (r2 p hp M x) := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [r2, compatiblePairH2, mapH2, Submodule.mapQ_apply]
    rfl
  obtain ⟨x', hx'⟩ := h A (pull p.toMonoidHom hp M) (pull p.toMonoidHom hp M') hl u hu' hs (r2 p hp M' y)
  obtain ⟨x, rfl⟩ := (restriction_two_bijective p hp hq M).2 x'
  refine ⟨x, (restriction_two_bijective p hp hq M').1 ?_⟩
  rw [key, hx']

end Pull

section Gl

variable {l : ℕ} [Fact l.Prime] {L : Loc} {G G' : Glob l L} (e : G.Hom G') {A : Type} [CommRing A]

private theorem pl_φ (w : (plOf G).ι) (g : (plOf G).G w) : e.p ((plOf G).φ w g) = (plOf G').φ w g := by
  cases w with
  | inl v => exact e.φ v g
  | inr u => exact e.φu u g

private def pullD (D : Dat A (plOf G')) : Dat A (plOf G) where
  M := pull e.p e.cont D.M
  Q w := D.Q w
  π w := D.π w
  surj w := D.surj w
  equiv w g m := by
    have h := D.equiv w g m
    rw [← pl_φ e w g] at h
    exact h

end Gl

end UpperTheory.V.Pa.B2

theorem UpperTheory.V.Pa.B2.cohAxIso :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (e : G.Hom G') (d : ℕ) (dv : L.Vl → ℕ), Function.Injective e.p → CohAx G d dv → CohAx G' d dv := by
  intro l _ L G G' e d dv hinj hG
  haveI : T2Space G'.Γ := inferInstance
  let q : G.Γ ≃* G'.Γ := MulEquiv.ofBijective e.p ⟨hinj, e.surj⟩
  have hq : Continuous q := e.cont
  have hqs : Continuous q.symm :=
    (Continuous.homeoOfEquivCompactToT2 (f := q.toEquiv) e.cont).symm.continuous
  refine ⟨hG.sum, finH_iso q hq hqs l hG.fin, hG.finV, hG.finU, onto_iso q hq hqs l hG.onto, ?_,
    hG.leV, hG.leU, hG.ur, ?_⟩
  · obtain ⟨c, hc, hf⟩ := hG.ge
    refine ⟨fun i => e.p (c i), fun i => ⟨by rw [e.η]; exact (hc i).1, by rw [← map_mul, (hc i).2, map_one]⟩, ?_⟩
    intro A _ M hl
    have h := hf A (pull q.toMonoidHom hq M) hl
    rw [card_H0_pullback_eq] at h
    rw [Nat.card_congr (Equiv.ofBijective _ (restriction_two_bijective q hq hqs M)),
      Nat.card_congr (Equiv.ofBijective _ (restriction_one_bijective q hq hqs M))]
    exact h
  · intro A _ D hl
    have h := hG.ck A (pullD e D) hl
    have hc : ∀ x, D.loc2 x = (pullD e D).loc2 (r2 q hq D.M x) := by
      intro x
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      funext w
      simp only [Dat.loc2, LinearMap.pi_apply, r2, compatiblePairH2, Submodule.mapQ_apply]
      congr 1
      ext y
      show D.π w (z.1 ((plOf G').φ w y.1, (plOf G').φ w y.2)) =
        D.π w (z.1 (e.p ((plOf G).φ w y.1), e.p ((plOf G).φ w y.2)))
      rw [pl_φ e w y.1, pl_φ e w y.2]
    have hr : (pullD e D).loc2.range = D.loc2.range := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        obtain ⟨x0, rfl⟩ := (restriction_two_bijective q hq hqs D.M).2 x
        exact ⟨x0, hc x0⟩
      · rintro ⟨x, rfl⟩
        exact ⟨r2 q hq D.M x, (hc x).symm⟩
    have h1 : Nat.card (pullD e D).Ck2 = Nat.card D.Ck2 := by
      show Nat.card (_ ⧸ (pullD e D).loc2.range) = Nat.card (_ ⧸ D.loc2.range)
      rw [hr]
      rfl
    rw [← h1]
    refine h.trans (le_of_eq (Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_)))
    constructor
    · intro hf g m
      obtain ⟨g0, rfl⟩ := e.surj g
      rw [e.ε]
      exact hf g0 m
    · intro hf g m
      have := hf (e.p g) m
      rw [e.ε] at this
      exact this
