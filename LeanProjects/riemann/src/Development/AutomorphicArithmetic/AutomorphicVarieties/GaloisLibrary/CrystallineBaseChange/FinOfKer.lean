import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.HfStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CuspSet
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CtMoves
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CoRatAff
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.HolCuspFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolLin
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinSmoothContinuous
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PeriodicIntegralFundamentalDomainInvariant
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinConstantTermUpperBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinConstantTermOfPeriodMeanOfUpperBlock

open NumberField IsDedekindDomain MeasureTheory Topology Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Eis

private theorem fin_of_ker {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Finite ι] (P Q : Set V) (h0 : (0 : V) ∈ P)
    (hP : ∀ x y (z : ℂ), x ∈ P → y ∈ P → x + z • y ∈ P) (hQ : FiniteDimensional ℂ (Submodule.span ℂ Q)) (L : V → ι → ℂ)
    (hL0 : L 0 = 0) (hL : ∀ x y (z : ℂ), x ∈ P → y ∈ P → L (x + z • y) = L x + z • L y) (hk : ∀ x ∈ P, L x = 0 → x ∈ Q) :
    FiniteDimensional ℂ (Submodule.span ℂ P) := by
  let W : Submodule ℂ V :=
    { carrier := P
      zero_mem' := h0
      add_mem' := fun {x y} hx hy => by simpa using hP x y 1 hx hy
      smul_mem' := fun z y hy => by simpa using hP 0 y z h0 hy }
  have hW : Submodule.span ℂ P = W := Submodule.span_eq W
  rw [hW]
  let f : W →ₗ[ℂ] (ι → ℂ) :=
    { toFun := fun x => L x.1
      map_add' := fun x y => by simpa using hL x.1 y.1 1 x.2 y.2
      map_smul' := fun z y => by simpa [hL0] using hL 0 y.1 z h0 y.2 }
  let j : LinearMap.ker f →ₗ[ℂ] Submodule.span ℂ Q :=
    LinearMap.codRestrict _ (W.subtype.comp (LinearMap.ker f).subtype) fun x =>
      Submodule.subset_span (hk _ x.1.2 x.2)
  have hj : Function.Injective j := fun x y h => by
    have e := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext e)
  haveI : Module.Finite ℂ (LinearMap.ker f) := Module.Finite.of_injective j hj
  haveI : Module.Finite ℂ (W ⧸ LinearMap.ker f) := Module.Finite.equiv f.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker f)

theorem UpperTheory.V.Br.holFin0 :
    UpperTheory.V.Sd.HolFin := by
  intro F _ _ _ k c hc ω hω
  obtain ⟨⟨M, hM, hlev⟩, hfin⟩ := UpperTheory.V.Br.holCuspFin F k c hc ω hω
  obtain ⟨S, hS, hgen⟩ := UpperTheory.V.Br.cuspSet F M hM
  obtain ⟨_, _, μ, _, D, hD, hone⟩ := UpperTheory.V.Br.ctOne F
  obtain ⟨h0, -, hadd, -⟩ := UpperTheory.V.Sd.holLin F k c ω
  have hint : ∀ φ : TR.Sm F 2, IsHol k c ω φ → ∀ g, IntegrableOn (fun x : NA F => φ.1 (unip x * g)) D μ := fun φ hφ =>
    (UpperTheory.eisenstein_constantTerm_of_periodMean_of_upperBlock UpperTheory.periodic_integral_fundamentalDomain_invariant UpperTheory.eisenstein_constantTerm_upperBlock F μ D hD φ.1 (UpperTheory.eisenstein_smooth_continuous F 2 φ hφ.aut.level) hφ.aut.left).1
  haveI : Finite S := hS
  refine fin_of_ker _ _ h0 hadd hfin (fun φ (s : S) => cterm μ D φ.1 s.1) ?_ (fun φ ψ z hφ hψ => ?_) fun φ hφ h => ?_
  · funext s
    simp [cterm]
  · funext s
    simp only [cterm, Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_add (hint φ hφ s.1) ((hint ψ hψ s.1).const_mul z), integral_const_mul]
  · have hu := hgen {g | cterm μ D φ.1 g = 0} (fun s hs => congrFun h ⟨s, hs⟩)
      (UpperTheory.V.Br.ctMoves F μ D hD k c ω hω φ hφ M (hlev φ hφ))
    exact ⟨hφ, hφ.aut, hone φ.1 hφ.aut.left fun g => (hu.ge (Set.mem_univ g) :)⟩
