import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GoodOAdicCompleteCompactBasisStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsDualLatticesStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LatticeOpenCompactNhdsBasisStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ActQIsLocallyConstant
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GrowthGaloisInvariantsModPrimePowerLattice

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace PositivityTheory.LocalTateOrthogonality.Bk

theorem card_pow_le {O M Z N : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [AddCommGroup M]
    [Module O M] [Module.Finite O M] [Finite N] (a : O) (p : Z → M) (hp : Function.Surjective p)
    (f : Z → N) (hf : ∀ x y, f x = f y → ∃ w, p x - p y = a • w) :
    Nat.card (O ⧸ Ideal.span {a}) ^ finrank O M ≤ Nat.card N := by
  classical
  set I : Ideal O := Ideal.span {a}
  let F := M ⧸ Submodule.torsion O M
  let b := Module.finBasis O F
  have e : finrank O F = finrank O M := finrank_quotient_eq_of_le_torsion le_rfl
  let ψL : M →ₗ[O] (Fin (finrank O F) → O) := b.equivFun.toLinearMap ∘ₗ (Submodule.torsion O M).mkQ
  let ψ : M → (Fin (finrank O F) → O ⧸ I) := fun m i => Ideal.Quotient.mk I (ψL m i)
  have hψ : ∀ x y, (∃ w, x - y = a • w) → ψ x = ψ y := by
    rintro x y ⟨w, hw⟩
    funext i
    refine Ideal.Quotient.eq.mpr ?_
    have h1 : ψL x i - ψL y i = a * ψL w i := by
      rw [← Pi.sub_apply, ← map_sub, hw, map_smul]
      rfl
    rw [h1]
    exact Ideal.mem_span_singleton'.mpr ⟨ψL w i, mul_comm _ _⟩
  have hsurj : Function.Surjective (fun z => ψ (p z)) := by
    intro t
    choose c hc using fun i => Ideal.Quotient.mk_surjective (I := I) (t i)
    obtain ⟨m, hm⟩ := (Submodule.torsion O M).mkQ_surjective (b.equivFun.symm c)
    obtain ⟨z, rfl⟩ := hp m
    refine ⟨z, ?_⟩
    funext i
    simp only [ψ, ψL, LinearMap.coe_comp, Function.comp_apply, hm, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, hc]
  let g : Set.range f → (Fin (finrank O F) → O ⧸ I) := fun n => ψ (p (Classical.choose n.2))
  have hg : Function.Surjective g := by
    intro t
    obtain ⟨z, hz⟩ := hsurj t
    refine ⟨⟨f z, z, rfl⟩, ?_⟩
    have hz' : f (Classical.choose (⟨z, rfl⟩ : ∃ y, f y = f z)) = f z := Classical.choose_spec (⟨z, rfl⟩ : ∃ y, f y = f z)
    simp only [g]
    rw [hψ _ _ (hf _ _ hz')]
    exact hz
  have h1 := Nat.card_le_card_of_surjective g hg
  have h2 : Nat.card (Set.range f) ≤ Nat.card N := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  rw [Nat.card_fun, Nat.card_fin, e] at h1
  exact h1.trans h2

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
  [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
  (A : GRep G Qp LL O) (L : Lattice (O := O) A.ρ)

open GlobalTheory.CompanionTheory.GrowthOfInvariants in

theorem redT_mem {ϖ : O} {r : ℕ} (hW : (fun x => ϖ ^ r • x) '' (L.T : Set A.V) ∈ nhds (0 : A.V))
    (hI : StableSub L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) (c : ↥(latticeCocycles L)) :
    redT L _ c ∈ quotientCocycles L _ hI := by
  obtain ⟨⟨hcont, hcoc⟩, _⟩ := c.2
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro g0
    have hW' : (fun x => ϖ ^ r • x) '' (L.T : Set A.V) ∈ nhds ((c : _ → A.V) g0 + -(c : _ → A.V) g0) := by
      rw [add_neg_cancel]
      exact hW
    filter_upwards [(hcont.tendsto g0).add_const (-(c : _ → A.V) g0) hW'] with g hg
    obtain ⟨x, hx, hxe⟩ := hg
    refine (Submodule.Quotient.eq _).mpr ?_
    have : (evT L g c - evT L g0 c : ↥L.T) = ϖ ^ r • (⟨x, hx⟩ : ↥L.T) := by
      apply Subtype.ext
      simp only [Submodule.coe_sub, SetLike.val_smul]
      have hxe' : ϖ ^ r • x = (c : _ → A.V) g + -(c : _ → A.V) g0 := hxe
      rw [hxe', sub_eq_add_neg]
      rfl
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  · intro g h
    show Submodule.Quotient.mk (evT L (g * h) c) = Submodule.Quotient.mk (evT L g c) + actQ L _ hI g (Submodule.Quotient.mk (evT L h c))
    rw [actQ, Submodule.mapQ_apply, ← Submodule.Quotient.mk_add]
    congr 1
    apply Subtype.ext
    exact hcoc g h

open GlobalTheory.CompanionTheory.GrowthOfInvariants in

theorem exists_div_class [IsDomain O] [IsFractionRing O LL] {a : O} (ha : a ≠ 0)
    (hI : StableSub L (Ideal.span {a} • ⊤ : Submodule O ↥L.T)) (c : ↥(latticeCocycles L))
    (hc : redT L (Ideal.span {a} • ⊤ : Submodule O ↥L.T) c ∈ BQ L _ hI) :
    ∃ w : LatticeCohomology L, (Submodule.Quotient.mk c : LatticeCohomology L) = a • w := by
  obtain ⟨t, ht⟩ := hc
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  have hd : ∀ g, ∃ y : ↥L.T, a • y = evT L g c - (actT L g x - x) := by
    intro g
    have h1 := congrFun ht g
    simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply] at h1
    change actQ L _ hI g (Submodule.Quotient.mk x) - Submodule.Quotient.mk x = Submodule.Quotient.mk (evT L g c) at h1
    rw [actQ, Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub, eq_comm, Submodule.Quotient.eq,
      Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨y, _, hy⟩ := h1
    exact ⟨y, hy⟩
  choose y hy using hd
  obtain ⟨⟨hcont, hcoc⟩, _⟩ := c.2
  set α : LL := algebraMap O LL a with hαdef
  have hα : α ≠ 0 := fun h => ha ((IsFractionRing.injective O LL) (h.trans (map_zero _).symm))
  have hyV : ∀ g, a • ((y g : ↥L.T) : A.V) = (c : G → A.V) g - (A.ρ g (x : A.V) - (x : A.V)) := by
    intro g
    have := congrArg Subtype.val (hy g)
    exact this
  have hyL : ∀ g, α • ((y g : ↥L.T) : A.V) = (c : G → A.V) g - (A.ρ g (x : A.V) - (x : A.V)) := by
    intro g
    rw [hαdef, algebraMap_smul]
    exact hyV g
  let e : G → A.V := fun g => (y g : A.V)
  have he_form : e = fun g => α⁻¹ • ((c : G → A.V) g + (-1 : LL) • A.ρ g (x : A.V) + (x : A.V)) := by
    funext g
    have h2 : (c : G → A.V) g + (-1 : LL) • A.ρ g (x : A.V) + (x : A.V) = α • e g := by
      rw [hyL g, neg_one_smul]
      abel
    rw [h2, inv_smul_smul₀ hα]
  have he : e ∈ latticeCocycles L := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [he_form]
      exact ((hcont.add ((A.cont (x : A.V)).const_smul (-1 : LL))).add continuous_const).const_smul α⁻¹
    · intro g h
      apply smul_right_injective A.V hα
      simp only [smul_add, e, hyL, ← map_smul, hcoc, map_mul, Module.End.mul_apply, map_sub]
      abel
    · intro g _
      exact (y g).2
  refine ⟨Submodule.Quotient.mk ⟨e, he⟩, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap]
  refine ⟨x, x.2, ?_⟩
  funext g
  change A.ρ g (x : A.V) - (x : A.V) = (c : G → A.V) g - a • e g
  rw [show a • e g = a • ((y g : ↥L.T) : A.V) from rfl, hyV g, sub_sub_cancel]

end Gen

theorem card_lower_bound : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), TateFiniteness ((D.loc l).PD K) → FinZQ ((D.loc l).PD K) → ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), ∀ ϖ : O, Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), Nat.card (O ⧸ Ideal.span {ϖ}) ^ (r * finrank O (LatticeCohomology LA)) ≤ Nat.card (QuotientCohomology LA _ hI) := by
  intro D l _ K hfin hZ LL _ _ _ O _ _ hO A LA ϖ hϖ r hI
  obtain ⟨⟨hD, hV, hF⟩, -⟩ := id hO
  obtain ⟨-, hB, -⟩ := GlobalTheory.T.lattice_open_compact_nhds_basis D l K LL O hO A LA ϖ hϖ
  have hW : (fun x => ϖ ^ r • x) '' (LA.T : Set A.V) ∈ nhds (0 : A.V) := hB.mem_of_mem trivial
  have := hfin LL O hO A LA
  have := hZ LL O hO A LA ϖ hϖ r hI
  have : Finite (QuotientCohomology LA _ hI) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  rw [pow_mul, ← GlobalTheory.CompanionTheory.GrowthOfInvariants.card_quot_pow ϖ hϖ.ne_zero r]
  refine card_pow_le (ϖ ^ r) (fun c : ↥(latticeCocycles LA) => (Submodule.Quotient.mk c : LatticeCohomology LA))
    (Submodule.Quotient.mk_surjective _)
    (fun c => (Submodule.Quotient.mk ⟨redT LA _ c, redT_mem A LA hW hI c⟩ : QuotientCohomology LA _ hI)) ?_
  intro x y h
  rw [← Submodule.Quotient.mk_sub]
  refine exists_div_class A LA (pow_ne_zero r hϖ.ne_zero) hI _ ?_
  rw [map_sub]
  have h' := (Submodule.Quotient.eq _).1 h
  exact h'

end PositivityTheory.LocalTateOrthogonality.Bk
