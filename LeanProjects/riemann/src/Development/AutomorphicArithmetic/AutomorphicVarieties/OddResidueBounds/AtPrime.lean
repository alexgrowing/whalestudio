import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ShaDecompSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ExistsO
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.PsiReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ChiFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ActFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ActConj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem divE {ι : Type} (T : Finset ι) (m r : ℕ∞) (f : ι → ℕ∞) (g : ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hr0 : r ≠ 0) (hr : r ≠ ⊤) (h : m * r ≤ ∑ i ∈ T, f i)
    (hf : ∀ i ∈ T, f i ≠ ⊤ ∧ ((f i).toNat : ℝ) * L ≤ (r.toNat : ℝ) * g i) :
    m ≠ ⊤ ∧ (m.toNat : ℝ) * L ≤ ∑ i ∈ T, g i := by
  have hfe : ∑ i ∈ T, f i = ((∑ i ∈ T, (f i).toNat : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun i hi => (ENat.coe_toNat (hf i hi).1).symm)
  lift r to ℕ using hr
  have hm : m ≠ ⊤ := by
    rintro rfl
    rw [hfe, ENat.top_mul hr0] at h
    exact ENat.coe_ne_top _ (top_le_iff.1 h)
  lift m to ℕ using hm
  refine ⟨ENat.coe_ne_top _, ?_⟩
  rw [hfe, ← Nat.cast_mul, Nat.cast_le] at h
  simp only [ENat.toNat_coe] at hf ⊢
  have hrpos : (0 : ℝ) < r := by
    have : r ≠ 0 := by exact_mod_cast hr0
    exact_mod_cast Nat.pos_of_ne_zero this
  have h1 : (m : ℝ) * r * L ≤ ∑ i ∈ T, ((f i).toNat : ℝ) * L := by
    rw [← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right _ hL
    exact_mod_cast h
  have h2 : ∑ i ∈ T, ((f i).toNat : ℝ) * L ≤ ∑ i ∈ T, (r : ℝ) * g i :=
    Finset.sum_le_sum (fun i hi => (hf i hi).2)
  rw [← Finset.mul_sum] at h2
  have h3 : (r : ℝ) * ((m : ℝ) * L) ≤ (r : ℝ) * ∑ i ∈ T, g i :=
    calc (r : ℝ) * ((m : ℝ) * L) = (m : ℝ) * r * L := by ring
      _ ≤ _ := h1.trans h2
  exact le_of_mul_le_mul_left h3 hrpos

private theorem keyO (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [Algebra ℚ Ω]
    [IsScalarTower ℚ E Ω] [IsAlgClosure ℚ Ω] [IsAlgClosure E Ω] [IsAbelianGalois ℚ E] (l : ℕ) [Fact l.Prime] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [HasEnoughRootsOfUnity O (Monoid.exponent (E ≃ₐ[ℚ] E))] (D : LData E Ω l) (e : ℕ) (hl2 : l ≠ 2) (c : E ≃ₐ[ℚ] E)
    (hc : c * c = 1) (hcE : c.toRingEquiv = cE E) (T : Finset ((E ≃ₐ[ℚ] E) →* Oˣ))
    (hT : ∀ ψ, ((ψ c : Oˣ) : O) = (-1) ^ (e + 1) → ψ ∈ T) :
    minusLen D e * eO l O ≤ ∑ ψ ∈ T, psiLen (l := l) Ω e ψ := by
  haveI : Fintype ((E ≃ₐ[ℚ] E) →* Oˣ) := Fintype.ofFinite _
  have key := shaDecompSign ℚ E Ω l O D (e : ℤ) hl2 c ((-1) ^ (e + 1)) hc T (fun ψ h => hT ψ (by simpa using h))
  have hsgn : ((((-1) ^ (e + 1) : ℤˣ) : ℤ) : ℤ_[l]) = (-1) ^ (e + 1) := by simp
  rw [hcE, hsgn] at key
  exact key

theorem UpperTheory.V.Odd.atPrime :
    PsiBound → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), IsCycAct Ω N ρ → ∀ (l : ℕ) [Fact l.Prime] (D : LData E Ω l), l ≠ 2 → ¬ l ∣ Module.finrank ℚ E → ∀ e : ℕ, 1 ≤ e → minusLen D e ≠ ⊤ ∧ ∃ T : Finset (DirichletCharacter (PadicAlgCl l) N), (T : Set _) ⊆ charSet (PadicAlgCl l) (parE ρ (e + 1)) ∧ ((minusLen D e).toNat : ℝ) * Real.log l ≤ ∑ χ ∈ T, -Real.log ‖alN (e + 1) χ‖ := by
  classical
  intro hPB E Ω _ _ _ _ _ _ N _ ρ hρ l _ D hl2 hld e he
  obtain ⟨hsurj, hab, -, -, -⟩ := UpperTheory.V.Odd.actFacts E Ω N ρ hρ
  haveI := hab
  obtain ⟨hcE, -⟩ := UpperTheory.V.Odd.actConj E Ω N ρ hρ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ E Ω
  haveI : NeZero (Monoid.exponent (E ≃ₐ[ℚ] E)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨O, hO1, hO2, hO3⟩ := UpperTheory.V.Base.existsO l (Monoid.exponent (E ≃ₐ[ℚ] E))
  haveI := hO1
  haveI := hO2
  haveI := hO3
  haveI := Fintype.ofFinite ((E ≃ₐ[ℚ] E) →* Oˣ)
  obtain ⟨-, -, -, -, -, heO0, heOle, -, -⟩ := UpperTheory.V.Base.dvrFacts l O
  have hc : ρ (-1) * ρ (-1) = 1 := by
    rw [← map_mul]
    simp
  let T : Finset ((E ≃ₐ[ℚ] E) →* Oˣ) :=
    Finset.univ.filter (fun ψ => ((ψ (ρ (-1)) : Oˣ) : O) = (-1) ^ (e + 1))
  have hkey := keyO E Ω l O D e hl2 (ρ (-1)) hc hcE T
    (fun ψ hψ => Finset.mem_filter.2 ⟨Finset.mem_univ _, hψ⟩)
  have hpar : ∀ ψ ∈ T, chiOf ρ ψ (-1) = (-1) ^ (e + 1) := by
    intro ψ hψ
    have hψ' := (Finset.mem_filter.1 hψ).2
    have h1 := chiOf_unit ρ ψ (-1)
    rw [Units.val_neg, Units.val_one] at h1
    rw [h1, hψ']
    simp
  have hfin : eO l O ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) heOle
  have hL : 0 ≤ Real.log l := Real.log_nonneg (by exact_mod_cast (Fact.out : l.Prime).one_lt.le)
  obtain ⟨hm, hle⟩ := divE T (minusLen D e) (eO l O) (fun ψ => psiLen (l := l) Ω e ψ)
    (fun ψ => -Real.log ‖alN (e + 1) (chiOf ρ ψ)‖) (Real.log l) hL heO0 hfin hkey
    (fun ψ hψ => UpperTheory.V.Odd.psiReal hPB E Ω N ρ hρ l hl2 hld O e he ψ (hpar ψ hψ))
  refine ⟨hm, T.image (fun ψ => chiOf ρ ψ), ?_, ?_⟩
  · rw [Finset.coe_image]
    rintro _ ⟨ψ, hψ, rfl⟩
    exact ((UpperTheory.V.Odd.chiFacts E N ρ hsurj l O).2 ψ (e + 1)).1 (hpar ψ hψ)
  · rw [Finset.sum_image (fun x _ y _ h => (UpperTheory.V.Odd.chiFacts E N ρ hsurj l O).1 h)]
    exact hle
