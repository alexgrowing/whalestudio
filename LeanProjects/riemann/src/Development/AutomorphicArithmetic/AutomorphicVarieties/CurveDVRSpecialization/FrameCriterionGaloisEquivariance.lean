import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CrDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

open scoped Pointwise in
private theorem val_smul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (g : G F Ω) (A : ValuationSubring Ω) (x : Ω) :
    (g • A).valuation (g x) < 1 ↔ A.valuation x < 1 := by
  have key : ∀ y : Ω, g.toRingEquiv y ∈ g • A ↔ y ∈ A := by
    intro y
    constructor
    · intro hy
      obtain ⟨z, hz, hzy⟩ := (ValuationSubring.mem_smul_pointwise_iff_exists _ _ _).1 hy
      have hzy' : g z = g y := hzy
      rw [g.injective hzy'] at hz
      exact hz
    · intro hy
      exact ValuationSubring.smul_mem_pointwise_smul g y A hy
  exact val_lt_one key x

open scoped Pointwise in
private theorem place_smul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (g : G F Ω) {A : ValuationSubring Ω}
    {v : W.Plc F} (h : IsPlaceOver A v) : IsPlaceOver (g • A) v := by
  intro x
  have hx : g ((algebraMap F Ω) (x : F)) = (algebraMap F Ω) (x : F) := g.commutes _
  rw [← hx, val_smul]
  exact h x

open scoped Pointwise in
theorem UpperTheory.frame_criterion_galois_equivariance :
    UpperTheory.V.Pr.CrE := by
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ _ Φ k hB
  have hsm : ∀ (τ : G (W.Lp L) Ω) (X : ValuationSubring Ω),
      τ • X = ((toUpl Ω L τ : upl Ω L) : Gal(Ω/ℚ)) • X := by
    intro τ X
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    have hinv : ((toUpl Ω L τ : upl Ω L) : Gal(Ω/ℚ))⁻¹ = ((toUpl Ω L τ⁻¹ : upl Ω L) : Gal(Ω/ℚ)) := by
      rw [map_inv]
      rfl
    rw [hinv]
    rfl
  have hpl : ∀ w : Φ.V, (k.pl w).valuation (l : Ω) < 1 := by
    intro w
    obtain ⟨γ, -, hγ⟩ := k.pl_conj w
    have h1 := (val_smul γ B (l : Ω)).2 hB
    rw [map_natCast] at h1
    rw [hγ]
    exact h1
  have hpick : ∀ v : W.Vl l L, ∃ w : Φ.V, IsPlaceOver (k.pl w) (v : W.Plc (W.Lp L)) := by
    intro v
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω (v : W.Plc (W.Lp L))
    have hlA : A.valuation (l : Ω) < 1 := by
      rw [natCast_place hA]
      exact v.2
    obtain ⟨w, ⟨u, hu, hAu⟩, -⟩ := k.pl_all A hlA
    obtain ⟨g, hg⟩ := toUpl_surj (Ω := Ω) (L := L) (⟨u, hu⟩⁻¹)
    refine ⟨w, ?_⟩
    have heq : g • A = k.pl w := by
      rw [hsm, hg, hAu]
      change u⁻¹ • u • k.pl w = k.pl w
      rw [inv_smul_smul]
    rw [← heq]
    exact place_smul g hA
  choose e he using hpick
  have hinj : Function.Injective e := by
    intro v v' hvv
    have h2 := he v'
    rw [← hvv] at h2
    exact Subtype.ext (eq_of_isPlaceOver (he v) h2)
  have hsurj : Function.Surjective e := by
    intro w
    have hfacts := places (W.Lp L) Ω l (k.pl w)
    have hne : k.pl w ≠ ⊤ := by
      intro htop
      exact (hfacts.2.1 htop).2 (hpl w)
    obtain ⟨v0, hv0⟩ := hfacts.1 hne
    have hl0 : ((l : 𝓞 (W.Lp L))) ∈ v0.asIdeal := (natCast_place hv0 l).1 (hpl w)
    let v : W.Vl l L := ⟨v0, hl0⟩
    refine ⟨v, ?_⟩
    obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isPlaceOver (he v) hv0
    obtain ⟨w', -, huniq⟩ := k.pl_all (k.pl w) (hpl w)
    have hw : w = w' := huniq w ⟨1, one_mem _, (one_smul _ _).symm⟩
    have hev : e v = w' := huniq (e v) ⟨_, (toUpl Ω L τ).2, by rw [← hsm, hτ]⟩
    rw [hw, hev]
  exact ⟨Equiv.ofBijective e ⟨hinj, hsurj⟩, he⟩
