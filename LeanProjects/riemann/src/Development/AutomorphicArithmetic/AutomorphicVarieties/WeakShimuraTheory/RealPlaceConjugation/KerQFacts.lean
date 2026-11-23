import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.PrincTop

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem mem_princ_of_pow {l : ℕ} [Fact l.Prime] {u : ℤ_[l]ˣ} (hu : u ∈ KStar.TotallyRealRoots.princ l 1) {n : ℕ}
    (h : u ^ (l - 1) ∈ KStar.TotallyRealRoots.princ l n) : u ∈ KStar.TotallyRealRoots.princ l n := by
  have hl : l.Prime := Fact.out
  rw [KStar.TotallyRealRoots.mem_princ] at hu h ⊢
  rw [Units.val_pow_eq_pow_val] at h
  set x : ℤ_[l] := (u : ℤ_[l]) with hx
  set S : ℤ_[l] := ∑ i ∈ Finset.range (l - 1), x ^ i with hSdef
  have hgeom : x ^ (l - 1) - 1 = (x - 1) * S := by
    rw [hSdef, mul_comm, geom_sum_mul]
  have hl1 : (l : ℤ_[l]) ∣ x - 1 := by simpa using hu
  have hdiff : (l : ℤ_[l]) ∣ ∑ i ∈ Finset.range (l - 1), (x ^ i - 1) :=
    Finset.dvd_sum fun i _ => dvd_trans hl1 (by simpa [one_pow] using sub_dvd_pow_sub_pow x 1 i)
  have hSeq : S = ∑ i ∈ Finset.range (l - 1), (x ^ i - 1) + ((l : ℤ_[l]) - 1) := by
    rw [Finset.sum_sub_distrib, hSdef]
    simp [Nat.cast_sub hl.one_le]
  have hlnu : ¬IsUnit (l : ℤ_[l]) := by
    rw [PadicInt.not_isUnit_iff, PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.one_lt)
  have hS : IsUnit S := by
    by_contra hne
    rw [PadicInt.not_isUnit_iff, PadicInt.norm_lt_one_iff_dvd] at hne
    apply hlnu
    apply isUnit_of_dvd_one
    have h2 := dvd_sub (dvd_add hdiff (dvd_refl (l : ℤ_[l]))) hne
    convert h2 using 1
    rw [hSeq]
    ring
  rw [hgeom] at h
  exact hS.dvd_mul_right.mp h

private theorem comm_le_ker {Γ M : Type} [Group Γ] [Monoid M] (f : Γ →* M) (hf : ∀ a b, f (a * b) = f (b * a)) :
    commutator Γ ≤ f.ker := by
  rw [commutator, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, ← map_mul f a b, hf a b,
    map_mul, mul_assoc (f b), ← map_mul f a a⁻¹, mul_inv_cancel, map_one, mul_one, ← map_mul,
    mul_inv_cancel, map_one]

theorem UpperTheory.V.Ws.kerOverRationals_open_commutator_layer :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (F : IntermediateField ℚ Ω) [NumberField F] [IsAbelianGalois ℚ F], IsOpen (kerQ D F : Set (G ℚ Ω)) ∧ commutator (G ℚ Ω) ≤ kerQ D F ∧ ∀ (m : ℕ) (F' : IntermediateField ℚ Ω), IsLayer l m F F' → kerQ D F' = levU l (kerQ D F) (m + 1) ∧ cycU l (kerQ D F) ≤ F'.fixingSubgroup := by
  intro Ω _ _ _ l _ c D hD F hnf hab
  haveI := hnf
  haveI := hab
  have hnorm : Normal ℚ F := by
    haveI : IsGalois ℚ F := IsAbelianGalois.toIsGalois
    exact IsGalois.to_normal
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hrb, -, -⟩ := UpperTheory.V.GradeZeroInterpolatingElement.facts D hD
  have hcm : (cycMod ℚ Ω l 1).ker = Subgroup.comap (cycZ ℚ Ω l) (KStar.TotallyRealRoots.princ l 1) := rfl
  have key : ∀ g, g ∈ (cycMod ℚ Ω l 1).ker ↔ cycZ ℚ Ω l g ∈ KStar.TotallyRealRoots.princ l 1 := fun g => by
    rw [hcm]
    rfl
  have hdiag : ∀ g, D.rbar g = Matrix.diagonal fun i => IsLocalRing.residue c.O ((D.ps i g : (c.O)ˣ) : c.O) := by
    intro g
    ext i j
    simp [Raw.rbar, Raw.r0, UpperTheory.V.GradeZeroInterpolatingElement.mapRep, UpperTheory.V.GradeZeroInterpolatingElement.diagRep, Matrix.diagonal_apply]
    split_ifs <;> simp
  have hrc : ∀ a b, D.rbar (a * b) = D.rbar (b * a) := by
    intro a b
    rw [map_mul, map_mul, hdiag, hdiag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  refine ⟨?_, ?_, ?_⟩
  · show IsOpen ((F.fixingSubgroup ⊓ D.rbar.ker ⊓ (cycMod ℚ Ω l 1).ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω))
    rw [Subgroup.coe_inf, Subgroup.coe_inf, hcm, Subgroup.coe_comap]
    exact (F.fixingSubgroup_isOpen.inter hrb).inter
      ((KStar.TotallyRealRoots.isOpen_princ 1).preimage (continuous_cycZ ℚ Ω l))
  · refine le_inf (le_inf ?_ ?_) ?_
    · rw [← @IntermediateField.restrictNormalHom_ker _ _ _ _ _ F hnorm]
      exact comm_le_ker _ fun a b => by
        rw [map_mul, map_mul]
        exact (IsMulCommutative.is_comm (M := Gal(F/ℚ))).comm _ _
    · exact comm_le_ker _ hrc
    · exact comm_le_ker _ fun a b => by rw [map_mul, map_mul, mul_comm]
  · intro m F' hL
    constructor
    · ext g
      simp only [kerQ, levU, Subgroup.mem_inf, Subgroup.mem_comap, key, hL g]
      constructor
      · rintro ⟨⟨⟨hF, hp⟩, hr⟩, h1⟩
        exact ⟨⟨⟨hF, hr⟩, h1⟩, mem_princ_of_pow h1 hp⟩
      · rintro ⟨⟨⟨hF, hr⟩, h1⟩, hn⟩
        exact ⟨⟨⟨hF, Subgroup.pow_mem _ hn _⟩, hr⟩, h1⟩
    · intro g hg
      simp only [cycU, kerQ, Subgroup.mem_inf, MonoidHom.mem_ker] at hg
      rw [hL g]
      refine ⟨hg.1.1.1, ?_⟩
      rw [hg.2, one_pow]
      exact one_mem _
