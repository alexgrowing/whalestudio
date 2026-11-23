import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.LevCompact

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.homExt :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G F Ω)) (M : Type) [AddCommGroup M] (φ : cycU l U → M), IsClosed (U : Set (G F Ω)) → IsLocallyConstant φ → (∀ a b, φ (a * b) = φ a + φ b) →
    ∃ (n : ℕ) (ψ : levU l U n → M), IsLocallyConstant ψ ∧ (∀ a b, ψ (a * b) = ψ a + ψ b) ∧ ∀ u : cycU l U, ψ ⟨u.1, cycU_le_levU l U n u.2⟩ = φ u := by
  intro F Ω _ _ _ _ _ l _ U M _ φ hU hφ hmul
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI hroots : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have hlp : l.Prime := Fact.out
  have hφ1 : φ 1 = 0 := by
    have h := hmul 1 1
    simpa using h
  have hprinc : ∀ (x : ℤ_[l]ˣ) (n : ℕ), x ∈ KStar.TotallyRealRoots.princ l n ↔ PadicInt.toZModPow n (x : ℤ_[l]) = 1 := by
    intro x n
    simp only [KStar.TotallyRealRoots.princ, KStar.TotallyRealRoots.redPow, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map,
      Units.val_one, MonoidHom.coe_coe]
    exact Iff.rfl
  have hopen_n : ∀ n, IsOpen ((Subgroup.comap (cycZ F Ω l) (KStar.TotallyRealRoots.princ l n) : Subgroup (G F Ω)) : Set (G F Ω)) := by
    intro n
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hlp.ne_zero⟩
    apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
    rw [krullTopology_mem_nhds_one_iff]
    refine ⟨IntermediateField.adjoin F {ζ}, IntermediateField.adjoin.finiteDimensional
      ((hζ.isIntegral (Nat.pos_of_neZero _)).tower_top), ?_⟩
    intro σ hσ
    simp only [SetLike.mem_coe, Subgroup.mem_comap]
    rw [hprinc]
    rcases Nat.eq_zero_or_pos n with h0 | hn0
    · subst h0
      haveI : Subsingleton (ZMod (l ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero l)
      exact Subsingleton.elim _ _
    show (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G F Ω) Ω σ)).val.toZModPow n = 1
    rw [cyclotomicCharacter.toZModPow, eq_comm]
    apply modularCyclotomicCharacter.unique
    intro t ht
    obtain ⟨i, hi, rfl⟩ := (hζ.isUnit_unit NeZero.out).eq_pow_of_mem_rootsOfUnity ht
    rw [ZMod.val_one'', pow_one]
    · exact hσ ⟨ζ ^ i, pow_mem (IntermediateField.mem_adjoin_simple_self F ζ) _⟩
    · exact (one_lt_pow₀ hlp.one_lt hn0.ne').ne'
  have hprinc_anti : ∀ (x : ℤ_[l]ˣ) (n m : ℕ), n ≤ m → x ∈ KStar.TotallyRealRoots.princ l m → x ∈ KStar.TotallyRealRoots.princ l n := by
    intro x n m hnm hx
    rw [hprinc] at hx ⊢
    rw [← PadicInt.cast_toZModPow n m hnm, hx]
    exact ZMod.cast_one (pow_dvd_pow l hnm)
  have hlev_anti : ∀ n m : ℕ, n ≤ m → (levU l U m : Set (G F Ω)) ⊆ levU l U n := by
    intro n m hnm x hx
    simp only [levU, SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_comap] at hx ⊢
    exact ⟨hx.1, hprinc_anti _ n m hnm hx.2⟩
  have hclosed : ∀ n, IsClosed ((levU l U n : Subgroup (G F Ω)) : Set (G F Ω)) := by
    intro n
    simp only [levU, Subgroup.coe_inf]
    exact hU.inter (Subgroup.isClosed_of_isOpen _ (hopen_n n))
  obtain ⟨O, hOo, hOeq⟩ := isOpen_induced_iff.mp (hφ.isOpen_fiber (φ 1))
  have h1O : (1 : G F Ω) ∈ O := by
    have h : (1 : cycU l U) ∈ Subtype.val ⁻¹' O := by rw [hOeq]; rfl
    simpa using h
  obtain ⟨E, hEfin, hEnorm, hEsub⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal F Ω O).mp (hOo.mem_nhds h1O)
  haveI := hEfin
  haveI := hEnorm
  have hNnorm : (E.fixingSubgroup : Subgroup (G F Ω)).Normal := by
    rw [← IntermediateField.restrictNormalHom_ker]
    exact MonoidHom.normal_ker _
  have hNopen : IsOpen ((E.fixingSubgroup : Subgroup (G F Ω)) : Set (G F Ω)) := E.fixingSubgroup_isOpen
  have hNker : ∀ c : cycU l U, (c : G F Ω) ∈ E.fixingSubgroup → φ c = 0 := by
    intro c hc
    have h : c ∈ Subtype.val ⁻¹' O := hEsub hc
    rw [hOeq] at h
    rw [← hφ1]
    exact h
  have hwd : ∀ (c c' : cycU l U) (w w' : G F Ω), w ∈ E.fixingSubgroup → w' ∈ E.fixingSubgroup →
      (c : G F Ω) * w = c' * w' → φ c = φ c' := by
    intro c c' w w' hw hw' h
    have hmem : ((c'⁻¹ * c : cycU l U) : G F Ω) ∈ E.fixingSubgroup := by
      have e : ((c'⁻¹ * c : cycU l U) : G F Ω) = w' * w⁻¹ := by
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
        rw [eq_mul_inv_iff_mul_eq, mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [e]
      exact Subgroup.mul_mem _ hw' (Subgroup.inv_mem _ hw)
    have h0 := hNker _ hmem
    rw [hmul] at h0
    have hinv : φ c'⁻¹ + φ c' = 0 := by rw [← hmul]; simp [hφ1]
    have e1 : φ c'⁻¹ = -φ c' := eq_neg_of_add_eq_zero_left hinv
    rw [e1] at h0
    exact (neg_add_eq_zero.mp h0).symm
  have hinter : ∀ x ∈ ⋂ n, (levU l U n : Set (G F Ω)), x ∈ cycU l U := by
    intro x hx
    simp only [Set.mem_iInter, levU, SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_comap] at hx
    simp only [cycU, Subgroup.mem_inf, MonoidHom.mem_ker]
    refine ⟨(hx 0).1, ?_⟩
    apply Units.ext
    apply (PadicInt.ext_of_toZModPow).mp
    intro n
    rw [(hprinc _ n).mp (hx n).2, Units.val_one, map_one]
  obtain ⟨n, hn⟩ := exists_subset_nhds_of_compactSpace (X := G F Ω) (ι := ℕ)
    (V := fun n => (levU l U n : Set (G F Ω)))
    (fun i j => ⟨max i j, hlev_anti _ _ (le_max_left _ _), hlev_anti _ _ (le_max_right _ _)⟩)
    hclosed
    (U := {a | ∃ c ∈ cycU l U, ∃ w ∈ E.fixingSubgroup, a = c * w})
    (by
      intro x hx
      have hxc := hinter x hx
      refine Filter.mem_of_superset
        (IsOpen.mem_nhds (hNopen.preimage (continuous_mul_left x⁻¹)) (by simpa using Subgroup.one_mem _))
        (fun a ha => ⟨x, hxc, x⁻¹ * a, ha, by group⟩))
  have hex : ∀ y : levU l U n, ∃ c : cycU l U, ∃ w ∈ E.fixingSubgroup, (y : G F Ω) = c * w := by
    intro y
    obtain ⟨c, hc, w, hw, e⟩ := hn y.2
    exact ⟨⟨c, hc⟩, w, hw, e⟩
  choose cf wf hwf hcw using hex
  refine ⟨n, fun y => φ (cf y), ?_, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro y
    refine ⟨{z : levU l U n | (y : G F Ω)⁻¹ * z ∈ E.fixingSubgroup},
      hNopen.preimage (continuous_const.mul continuous_subtype_val), by simpa using Subgroup.one_mem _, ?_⟩
    intro z hz
    exact hwd (cf z) (cf y) (wf z) (wf y * ((y : G F Ω)⁻¹ * z)) (hwf z)
      (Subgroup.mul_mem _ (hwf y) hz)
      (by rw [← hcw z, ← mul_assoc, ← hcw y]; group)
  · intro a b
    rw [← hmul]
    have hv : ((cf b : G F Ω)⁻¹ * wf a * cf b) * wf b ∈ E.fixingSubgroup := by
      refine Subgroup.mul_mem _ ?_ (hwf b)
      have := hNnorm.conj_mem _ (hwf a) ((cf b : G F Ω)⁻¹)
      simpa using this
    refine hwd (cf (a * b)) (cf a * cf b) (wf (a * b)) _ (hwf _) hv ?_
    rw [← hcw (a * b), Subgroup.coe_mul, hcw a, hcw b, Subgroup.coe_mul]
    group
  · intro u
    exact hwd _ u (wf _) 1 (hwf _) (Subgroup.one_mem _) (by rw [← hcw, mul_one])
