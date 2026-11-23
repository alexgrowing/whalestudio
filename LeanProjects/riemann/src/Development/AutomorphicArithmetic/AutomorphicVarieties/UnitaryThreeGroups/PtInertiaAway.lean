import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMoreTail
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormSumLt

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem norm_sum_lt' {F ι : Type} [NormedField F] [IsUltrametricDist F] (s : Finset ι) (f : ι → F) {C : ℝ}
    (hC : 0 < C) (h : ∀ i ∈ s, ‖f i‖ < C) : ‖∑ i ∈ s, f i‖ < C :=
  _root_.UpperTheory.Reformulated.B.Qe17.norm_sum_lt s f hC h

private theorem det_ne_zero' {F : Type} [NormedField F] [IsUltrametricDist F] {m : ℕ} (t : F) (ht : ‖t‖ = 1)
    (E : Matrix (Fin m) (Fin m) F) (hE : ∀ a b, ‖E a b‖ < 1) : (t • (1 : Matrix (Fin m) (Fin m) F) + E).det ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.Qi6.det_ne_zero t ht E hE

private theorem conj_of_close {F Γ : Type} [NormedField F] [IsUltrametricDist F] [Group Γ] [Fintype Γ] {m : ℕ}
    (hΓ : ‖(Fintype.card Γ : F)‖ = 1) (ρ ρ₀ : Γ →* GL (Fin m) F)
    (hi : ∀ g a b, ‖(ρ g : Matrix (Fin m) (Fin m) F) a b‖ ≤ 1)
    (hc : ∀ g a b, ‖(ρ g : Matrix (Fin m) (Fin m) F) a b - (ρ₀ g : Matrix (Fin m) (Fin m) F) a b‖ < 1) :
    ∃ M : GL (Fin m) F, ∀ g, (M : Matrix (Fin m) (Fin m) F) * ρ g = ρ₀ g * M := by
  have hi₀ : ∀ g a b, ‖(ρ₀ g : Matrix (Fin m) (Fin m) F) a b‖ ≤ 1 := fun g a b => by
    have e : (ρ₀ g : Matrix (Fin m) (Fin m) F) a b = (ρ g : Matrix (Fin m) (Fin m) F) a b +
      -((ρ g : Matrix (Fin m) (Fin m) F) a b - (ρ₀ g : Matrix (Fin m) (Fin m) F) a b) := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hi g a b) (by rw [norm_neg]; exact (hc g a b).le))
  set M : Matrix (Fin m) (Fin m) F := ∑ g, (ρ₀ g⁻¹ : Matrix (Fin m) (Fin m) F) * ρ g with hM
  have hsplit : M = (Fintype.card Γ : F) • (1 : Matrix (Fin m) (Fin m) F) +
      ∑ g, (ρ₀ g⁻¹ : Matrix (Fin m) (Fin m) F) * ((ρ g : Matrix (Fin m) (Fin m) F) - ρ₀ g) := by
    have e : ∀ g, (ρ₀ g⁻¹ : Matrix (Fin m) (Fin m) F) * ρ g =
        1 + (ρ₀ g⁻¹ : Matrix (Fin m) (Fin m) F) * ((ρ g : Matrix (Fin m) (Fin m) F) - ρ₀ g) := fun g => by
      rw [Matrix.mul_sub, ← Units.val_mul (ρ₀ g⁻¹) (ρ₀ g), ← map_mul, inv_mul_cancel, map_one, Units.val_one]
      abel
    rw [hM, Finset.sum_congr rfl fun g _ => e g, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Nat.cast_smul_eq_nsmul]
  have hdet : M.det ≠ 0 := by
    rw [hsplit]
    refine det_ne_zero' _ hΓ _ fun a b => ?_
    rw [Matrix.sum_apply]
    refine norm_sum_lt' _ _ one_pos fun g _ => ?_
    rw [Matrix.mul_apply]
    refine norm_sum_lt' _ _ one_pos fun k _ => ?_
    rw [norm_mul, Matrix.sub_apply]
    exact mul_lt_one_of_nonneg_of_lt_one_right (hi₀ _ _ _) (norm_nonneg _) (hc g k b)
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, fun h => ?_⟩
  show M * _ = _ * M
  rw [hM, Finset.sum_mul, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => ?_
  simp only [Equiv.coe_mulRight]
  rw [← Matrix.mul_assoc, ← Units.val_mul (ρ₀ h), ← map_mul, map_mul ρ, Units.val_mul, ← Matrix.mul_assoc]
  congr 4
  group

theorem UpperTheory.V.U3.pt_inertia_away :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG 3 (PadicAlgCl l)} (h : D.IsPt U g₁ r),
      ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∃ M : GL (Fin 3) (PadicAlgCl l), ∀ g ∈ Ine (F := ℚ) A, D.η g = 1 →
        (M : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) * (r g).mat = (r0 D.η D.ΨQ g).mat * M := by
  intro Ω _ _ _ K _ _ _ l hl c N _ e ψ D U g₁ _ r h A hA
  obtain ⟨-, -, -, -, -, hk0, -, -, -, hK, -⟩ := dat_facts D
  let H : Subgroup (G ℚ Ω) := Ine (F := ℚ) A ⊓ D.η.ker
  let i : H →* D.η.ker := Subgroup.inclusion inf_le_right
  let χ : H →* c.Oˣ := (Chr.dirG ℚ Ω ψ).comp H.subtype
  let ρ : H →* GL (Fin 3) (PadicAlgCl l) := (glPart D.η r h.mult).comp i
  let ρ₀ : H →* GL (Fin 3) (PadicAlgCl l) := (glPart D.η (r0 D.η D.ΨQ) (hasSimilitudeFactor_diagonalRepr _ _)).comp i
  have hkill : ∀ g : H, g ∈ χ.ker → (g : G ℚ Ω) ∈ D.Kill := fun g hg => (hK g).2 ⟨A, hA, g.2.1, g.2.2, hg⟩
  have hρ : χ.ker ≤ ρ.ker := fun g hg => by
    show (r g).left = 1
    rw [h.kill g (hkill g hg)]; rfl
  have hρ₀ : χ.ker ≤ ρ₀.ker := fun g hg => by
    show tor _ (D.ΨQ g) = 1
    have h1 : tor _ (D.Ψ g) = 1 := congrArg SemidirectProduct.left (hk0 g (hkill g hg))
    have h2 : D.Ψ g = 1 := by
      have : (tor _ (D.Ψ g) : Matrix (Fin 3) (Fin 3) c.O) 0 0 = 1 := by rw [h1]; simp
      rw [tor_val] at this
      apply Units.ext
      simpa [wt1] using this
    have h3 : D.ΨQ g = 1 := by
      unfold Dat.ΨQ
      rw [MonoidHom.comp_apply, h2, map_one]
    rw [h3, map_one]
  have hfin : Finite χ.range := by
    have : χ.range ≤ ψ.toUnitHom.range := by
      rintro _ ⟨g, rfl⟩
      exact ⟨_, rfl⟩
    have h2 : Finite ψ.toUnitHom.range := Finite.of_surjective _ ψ.toUnitHom.rangeRestrict_surjective
    exact Finite.of_injective _ (Subgroup.inclusion_injective this)
  have hfinQ : Finite (H ⧸ χ.ker) := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange χ).symm.toEquiv
  letI : Fintype (H ⧸ χ.ker) := Fintype.ofFinite _
  have hpow : ∀ x : H ⧸ χ.ker, x ^ orderOf ψ = 1 := fun x => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, MonoidHom.mem_ker, map_pow]
    apply Units.ext
    show ((ψ.toUnitHom (Chr.cls ℚ Ω N g) ^ orderOf ψ : c.Oˣ) : c.O) = 1
    rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe]
  have hnd : ¬ l ∣ Fintype.card (H ⧸ χ.ker) := fun hd => by
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card l hd
    exact D.gd.ord (hx.symm.dvd.trans (orderOf_dvd_of_pow_eq_one (hpow x)))
  have hnorm : ‖(Fintype.card (H ⧸ χ.ker) : PadicAlgCl l)‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
    exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hnd)
  obtain ⟨M, hM⟩ := conj_of_close hnorm (QuotientGroup.lift _ ρ hρ) (QuotientGroup.lift _ ρ₀ hρ₀)
    (fun x a b => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      exact h.int g a b)
    (fun x a b => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      exact h.red g a b)
  exact ⟨M, fun g hg hη => hM (QuotientGroup.mk (⟨g, hg, hη⟩ : H))⟩
