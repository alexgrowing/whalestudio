import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

section Hecke

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

private theorem isOpen_ker_kills {M : ℕ} (hM : 1 ≤ M) {φ : G F Ω →* (Qbar l)ˣ} (hφ : KillsMu M φ) :
    IsOpen (φ.ker : Set (G F Ω)) := by
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hM] using hζ
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := F) ζ).mem_nhds ?_) fun s hs => ?_)
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · simp only [Set.mem_iInter] at hs
    exact hφ s fun ζ hζ => hs ζ hζ

private theorem exists_hchar_fin {art : Ideles F →* Gab F Ω} (ha : IsGlobalArtin art) (ι : Qbar l ≃+* ℂ)
    {M : ℕ} (hM : 1 ≤ M) {φ : G F Ω →* (Qbar l)ˣ} (hφ : KillsMu M φ) :
    ∃ χ : HChar F, IsAlgPos χ 0 ∧ IsLAdicOf art ι χ 0 φ := by
  have ho := isOpen_ker_kills hM hφ
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have hfi : Finite (G F Ω ⧸ φ.ker) := Subgroup.quotient_finite_of_isOpen _ ho
  have hpos : 0 < φ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  obtain ⟨χ, ⟨h1, h2⟩, -⟩ := exists_unique_hchar_of_finite_order ha ι φ (continuous_of_isOpen_ker' φ ho) hpos
    (MonoidHom.ext fun s => by
      rw [MonoidHom.pow_apply, ← map_pow]
      exact φ.ker.pow_index_mem s)
  exact ⟨χ, isAlgPos_zero_of_orderDvd hpos h1, h2⟩

private theorem isAlgPos_mul {χ χ' : HChar F} {n n' : (F →+* ℂ) → ℤ} (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') :
    IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

private theorem isAlgPos_inv {χ : HChar F} {n : (F →+* ℂ) → ℤ} (h : IsAlgPos χ n) : IsAlgPos χ⁻¹ (-n) := fun k hk => by
  have e : (χ⁻¹).inf k = (χ.inf k)⁻¹ := rfl
  rw [e, Units.val_inv_eq_inv_val, h k hk, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm

private theorem exists_hchar_cyc {art : Ideles F →* Gab F Ω} (ha : IsGlobalArtin art) (ι : Qbar l ≃+* ℂ) (j : ℤ) :
    ∃ (χ : HChar F) (n : (F →+* ℂ) → ℤ), IsAlgPos χ n ∧ IsLAdicOf art ι χ n (cycBar F Ω l ^ j) := by
  have key : ∀ m : ℕ, ∃ (χ : HChar F) (n : (F →+* ℂ) → ℤ), IsAlgPos χ n ∧ IsLAdicOf art ι χ n (cycBar F Ω l ^ m) := fun m => by
    have h := GlobalTheory.Published.CharAboveModel.absPow_isAlgPos F m
    obtain ⟨μ, hμ, hL⟩ := ha.exists_isLAdicOf ι h
    have e : μ = cycBar F Ω l ^ m := GlobalTheory.Published.CharAboveModel.eq_cyc_pow ha hμ hL
    exact ⟨_, _, h, e ▸ hL⟩
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · simpa using key m
  · obtain ⟨χ, n, h1, h2⟩ := key m
    exact ⟨_, _, isAlgPos_inv h1, by simpa using h2.inv⟩

private theorem continuous_cyc {art : Ideles F →* Gab F Ω} (ha : IsGlobalArtin art) (ι : Qbar l ≃+* ℂ) :
    Continuous (cycBar F Ω l) := by
  have h := GlobalTheory.Published.CharAboveModel.absPow_isAlgPos F 1
  obtain ⟨μ, hμ, hL⟩ := ha.exists_isLAdicOf ι h
  have e : μ = cycBar F Ω l ^ 1 := GlobalTheory.Published.CharAboveModel.eq_cyc_pow ha hμ hL
  rw [pow_one] at e
  exact e ▸ hμ

end Hecke

theorem UpperTheory.exists_algebraic_heckeChar_cyclotomic :
    UpperTheory.V.Af.Bc.CycHecke := by
  intro H F Ω _ _ _ _ _ l _ ι wt θ hθ
  obtain ⟨art, ha⟩ := H F Ω
  obtain ⟨M, φ, hM, hφ, rfl⟩ := hθ
  obtain ⟨χ, h1, h2⟩ := exists_hchar_fin ha ι hM hφ
  obtain ⟨χ', n, h3, h4⟩ := exists_hchar_cyc ha ι wt
  refine ⟨?_, _, art, _, ha, isAlgPos_mul h3 h1, h4.mul h2⟩
  have hc : Continuous φ := continuous_of_isOpen_ker' φ (isOpen_ker_kills hM hφ)
  exact ((continuous_cyc ha ι).zpow wt).mul hc
