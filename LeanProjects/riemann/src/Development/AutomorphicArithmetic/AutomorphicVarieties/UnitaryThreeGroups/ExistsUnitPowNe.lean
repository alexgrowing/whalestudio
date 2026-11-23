import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Clifford
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtIneL
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CoboundaryLemmaNoColumn
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem matIrr_ker {Γ κ Z : Type} [Group Γ] [Field κ] [IsAlgClosed κ] [CharZero κ] [CommGroup Z]
    (ρ : Γ →* GL (Fin 2) κ) (χ : Γ →* Z) (I : Subgroup Γ) (Ψ : Γ →* κˣ)
    (hsurj : ∀ g, ∃ s ∈ I, χ s = χ g)
    (htr : ∀ s ∈ I, (ρ s : Matrix (Fin 2) (Fin 2) κ).trace = (Ψ s : κ) + (Ψ s : κ)⁻¹)
    (hinf : ∃ u ∈ I, Ψ u ^ 8 ≠ 1)
    (hirr : MatIrr ⊤ fun g => (ρ g : Matrix (Fin 2) (Fin 2) κ)) :
    MatIrr χ.ker fun g => (ρ g : Matrix (Fin 2) (Fin 2) κ) := by
  by_contra hred
  obtain ⟨φ, h1, hker, h2, M, hM⟩ := exists_selfTwist ρ χ.ker (fun a b => by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [mul_comm (χ a) (χ b), mul_inv_cancel_right, mul_inv_cancel]) hirr hred
  obtain ⟨g, hg⟩ : ∃ g, φ g ≠ 1 := by
    by_contra hne
    push Not at hne
    exact h1 (MonoidHom.ext hne)
  obtain ⟨s, hs, hsg⟩ := hsurj g
  have hφs : φ s ≠ 1 := by
    intro h
    have : φ (s⁻¹ * g) = 1 := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hsg, inv_mul_cancel])
    rw [map_mul, map_inv, h, inv_one, one_mul] at this
    exact hg this
  have key : ∀ t ∈ I, φ t ≠ 1 → Ψ t ^ 4 = 1 := by
    intro t ht hφ
    have e : (φ t : κ) • (ρ t : Matrix (Fin 2) (Fin 2) κ) =
        ((M⁻¹ : GL (Fin 2) κ) : Matrix (Fin 2) (Fin 2) κ) * (ρ t * M) := by
      rw [← hM t trivial, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have e2 := congrArg Matrix.trace e
    rw [Matrix.trace_smul, Matrix.trace_mul_comm, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one,
      htr t ht, smul_eq_mul] at e2
    have e3 : (φ t : κ) - 1 ≠ 0 := fun h => hφ (Units.ext (sub_eq_zero.1 h))
    have e4 : (Ψ t : κ) + (Ψ t : κ)⁻¹ = 0 := by
      refine (mul_eq_zero.1 (?_ : ((φ t : κ) - 1) * _ = 0)).resolve_left e3
      rw [sub_mul, e2, one_mul, sub_self]
    have e5 : (Ψ t : κ) * (Ψ t : κ)⁻¹ = 1 := mul_inv_cancel₀ (Ψ t).ne_zero
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    linear_combination ((Ψ t : κ) ^ 3 - (Ψ t : κ)) * e4 - ((Ψ t : κ) ^ 2 - 1) * e5
  obtain ⟨u, hu, hu8⟩ := hinf
  have hu2 : φ (u ^ 2) = 1 := by
    rw [map_pow]
    exact DFunLike.congr_fun h2 u
  have h3 := key (s * u ^ 2) (mul_mem hs (pow_mem hu 2)) (by rwa [map_mul, hu2, mul_one])
  rw [map_mul, mul_pow, key s hs hφs, one_mul, map_pow, ← pow_mul] at h3
  exact hu8 h3

private theorem exists_unit_pow_ne (l : ℕ) [Fact l.Prime] : ∃ v : ℤ_[l]ˣ, ∀ n : ℕ, n ≠ 0 → v ^ n ≠ 1 := by
  have hu : IsUnit ((1 + l : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    simp
  refine ⟨hu.unit, fun n hn h => ?_⟩
  have h2 := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at h2
  have h3 : (1 + l) ^ n = 1 := by exact_mod_cast h2
  have := (Fact.out : l.Prime).pos
  rcases Nat.pow_eq_one.1 h3 with h4 | h4
  · omega
  · exact hn h4

theorem UpperTheory.V.U3.typeII_irr_cyc :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG 3 (PadicAlgCl l)} (h : D.IsPt U g₁ r),
      TypeII D.η r → ∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l), D.IsExt r W →
        Af.IsIrr ((W.comp (galEmb ℚ K Ω)).comp (cycBar K Ω l).ker.subtype) := by
  intro hC Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hM r h hII W hW
  obtain ⟨A, hA, -⟩ := dat_loc D
  have hIK : Ine (F := ℚ) A ≤ D.η.ker := ((dat_facts D).2.2.2.2.2.2.2.2.2.2 A hA).1
  have hch := (pt_inertia_above hC D hM h A hA).1
  have h11 := (typeII_facts hC D hM h hII).1
  have hmem : ∀ s, galEmb ℚ K Ω s ∈ D.η.ker := fun s => D.η_ker ▸ galEmb_mem ℚ K Ω s
  have hlift : ∀ g ∈ D.η.ker, ∃ s, galEmb ℚ K Ω s = g := fun g hg => by
    rw [D.η_ker, ← range_galEmb] at hg
    exact hg
  have hsur : ∀ v : ℤ_[l]ˣ, ∃ s : G K Ω, galEmb ℚ K Ω s ∈ Ine (F := ℚ) A ∧ cycZ K Ω l s = v := fun v => by
    obtain ⟨σ, hσ, hv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA v
    obtain ⟨s, rfl⟩ := hlift σ (hIK hσ)
    exact ⟨s, hσ, hv⟩
  have main := matIrr_ker (W.comp (galEmb ℚ K Ω)) (cycBar K Ω l) ((Ine (F := ℚ) A).comap (galEmb ℚ K Ω))
    (D.ΨQ.comp (galEmb ℚ K Ω)) (fun g => ?_) (fun s hs => ?_) ?_ (fun X hX => ?_)
  · refine ⟨top_ne_bot, fun _ _ _ => trivial, fun X _ hX => main X fun g hg v hv => hX ⟨g, hg⟩ v hv⟩
  · obtain ⟨s, hs, hv⟩ := hsur (cycZ K Ω l g)
    refine ⟨s, hs, ?_⟩
    simp only [cycBar, MonoidHom.comp_apply, hv]
  · have h1 := Matrix.trace_eq_neg_charpoly_coeff (r (galEmb ℚ K Ω s)).mat
    rw [hch _ hs, ← Matrix.trace_eq_neg_charpoly_coeff] at h1
    rw [MonoidHom.comp_apply, hW.1 _ (hmem s), MonoidHom.comp_apply]
    have h2 := h11 _ (hmem s)
    have h3 : (corner (r (galEmb ℚ K Ω s)).mat).trace =
        (r (galEmb ℚ K Ω s)).mat 0 0 + (r (galEmb ℚ K Ω s)).mat 2 2 := Matrix.trace_fin_two _
    have h4 : (r0 D.η D.ΨQ (galEmb ℚ K Ω s)).mat.trace = (D.ΨQ (galEmb ℚ K Ω s) : PadicAlgCl l) + 1 +
        (D.ΨQ (galEmb ℚ K Ω s) : PadicAlgCl l)⁻¹ := by
      simp [GG.mat, tor_val, wt1, Fin.sum_univ_three]
    rw [Matrix.trace_fin_three, h4, h2] at h1
    rw [h3]
    linear_combination h1
  · obtain ⟨v, hv⟩ := exists_unit_pow_ne l
    obtain ⟨s, hs, hsv⟩ := hsur v
    refine ⟨s, hs, fun h8 => ?_⟩
    have ho : orderOf ψ ≠ 0 := fun h0 => D.gd.ord (h0 ▸ dvd_zero l)
    have he : e ≠ 0 := Nat.one_le_iff_ne_zero.1 D.gd.e_pos
    have h1 : D.Ψ (galEmb ℚ K Ω s) ^ 8 = 1 := by
      apply Units.ext
      apply Subtype.val_injective
      have := congrArg Units.val h8
      exact this
    have h2 : Chr.dirG ℚ Ω ψ (galEmb ℚ K Ω s) ^ orderOf ψ = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Chr.dirG, MonoidHom.comp_apply, MulChar.coe_toUnitHom,
        ← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe, Units.val_one]
    have h3 : D.Ψ (galEmb ℚ K Ω s) = Units.map (algebraMap ℤ_[l] c.O).toMonoidHom v ^ e *
        Chr.dirG ℚ Ω ψ (galEmb ℚ K Ω s) := by
      rw [← hsv, ← zpow_natCast]
      rfl
    have h4 : Units.map (algebraMap ℤ_[l] c.O).toMonoidHom (v ^ (e * (8 * orderOf ψ))) = 1 := by
      have := congrArg (· ^ orderOf ψ) h1
      simp only [one_pow] at this
      rw [← pow_mul, h3, mul_pow, mul_comm 8, pow_mul (Chr.dirG ℚ Ω ψ _), h2, one_pow, mul_one,
        ← pow_mul, mul_comm _ 8] at this
      rw [map_pow, this]
    refine hv (e * (8 * orderOf ψ)) (mul_ne_zero he (mul_ne_zero (by norm_num) ho)) ?_
    have hinj : Function.Injective (algebraMap ℤ_[l] c.O) := fun x y hxy => by
      have : algebraMap ℤ_[l] (PadicAlgCl l) x = algebraMap ℤ_[l] (PadicAlgCl l) y := congrArg Subtype.val hxy
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l) y] at this
      exact Subtype.val_injective ((algebraMap ℚ_[l] (PadicAlgCl l)).injective this)
    exact (Units.map_injective (f := (algebraMap ℤ_[l] c.O).toMonoidHom) hinj) (h4.trans (map_one _).symm)
  · refine hII.2 X fun g hg v hv => ?_
    obtain ⟨s, rfl⟩ := hlift g hg
    have := hX s trivial v hv
    simp only [MonoidHom.comp_apply, hW.1 _ hg] at this
    exact this
