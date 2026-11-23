import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ExtCocycle
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CobOfGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ExistsGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.QzBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaInfl
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.NonemptyH0GlobalEquivGaloisImage
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowN

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem UpperTheory.V.Kum.decCob {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {e : ℤ} (he : e ≠ 0) (hP : Procyc F Ω l) {v : HeightOneSpectrum (𝓞 F)}
    {A : ValuationSubring Ω} (hv : v ∈ Above F l) (hA : IsPlaceOver A v) {z : G F Ω → QZ l}
    (hz : z ∈ Z1 (qzG F Ω l e)) (h0 : ∀ g ∈ Dec (F := F) A, cycZ F Ω l g = 1 → z g = 0) :
    ∃ m, ∀ g ∈ Dec (F := F) A, z g = qzG F Ω l e g m - m := by
  haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.mp (isClosed_Dec A).isCompact
  let χ : Dec (F := F) A →* ℤ_[l]ˣ := (cycZ F Ω l).comp (Dec (F := F) A).subtype
  let ρ : Representation ℤ_[l] (Dec (F := F) A) (QZ l) := (qzG F Ω l e).comp (Dec (F := F) A).subtype
  have hV : IsClosed (decImage F l A : Set ℤ_[l]ˣ) := Subgroup.isClosed_of_isOpen _ (isOpen_decImage hv hA)
  have hVp : l ≠ 2 ∨ decImage F l A ≤ KStar.TotallyRealRoots.princ l 2 := by
    rcases hP with h | h
    · exact Or.inl h
    · right
      rintro _ ⟨g, -, rfl⟩
      have h1 := h g
      simp only [cycR, MonoidHom.comp_apply, Units.ext_iff, Units.coe_map, Units.val_one] at h1
      rw [KStar.TotallyRealRoots.mem_princ]
      have h2 : PadicInt.toZModPow 2 ((cycZ F Ω l g : ℤ_[l]) - 1) = 0 := by
        rw [map_sub, map_one]
        simpa using sub_eq_zero.mpr h1
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h2
      exact_mod_cast h2
  obtain ⟨γ', hγ'V, hgen'⟩ := existsGen l (decImage F l A) hV hVp
  obtain ⟨γ, hγ, hγχ⟩ := Subgroup.mem_map.mp hγ'V
  have hq : Continuous fun p : G F Ω × QZ l => qzG F Ω l e p.1 p.2 := contAction_qzG e
  have hpm : Continuous fun p : Dec (F := F) A × QZ l => ((p.1 : G F Ω), p.2) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hρc0 := hq.comp hpm
  have hρc : ReciprocityTheory.Gal.ContAction ρ := by
    unfold ReciprocityTheory.Gal.ContAction
    refine hρc0.congr fun p => ?_
    simp only [ρ, Function.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype]
  have hχc0 := (continuous_cycZ F Ω l).comp (continuous_subtype_val (p := fun g : G F Ω => g ∈ Dec (F := F) A))
  have hχc : Continuous χ := by
    refine hχc0.congr fun g => ?_
    simp only [χ, Function.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype]
  have htriv : ∀ g, χ g = 1 → ∀ m, ρ g m = m := by
    intro g hg m
    simp only [χ, MonoidHom.comp_apply, Subgroup.coe_subtype] at hg
    simp only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, qzG_apply, hg, one_zpow, Units.val_one, one_smul]
  have hgen : ∀ g, χ g ∈ (Subgroup.zpowers (χ ⟨γ, hγ⟩)).topologicalClosure := by
    intro g
    have h1 : χ ⟨γ, hγ⟩ = γ' := by
      simp only [χ, MonoidHom.comp_apply, Subgroup.coe_subtype]
      exact hγχ
    rw [h1]
    apply hgen'
    simp only [χ, MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact Subgroup.mem_map_of_mem _ g.2
  have hne : (cycZ F Ω l γ) ^ (-e) ≠ 1 := by
    intro h1
    obtain ⟨g, hg, hg1⟩ := GlobalTheory.CycDec.exists_mem_Dec_cycZ_zpow_ne_one F Ω l v A hv hA (-e) (neg_ne_zero.mpr he)
    let K : Subgroup ℤ_[l]ˣ := (zpowGroupHom (-e) : ℤ_[l]ˣ →* ℤ_[l]ˣ).ker
    have hK : IsClosed (K : Set ℤ_[l]ˣ) := by
      have : (K : Set ℤ_[l]ˣ) = {x : ℤ_[l]ˣ | x ^ (-e) = 1} := by
        ext x
        simp [K]
      rw [this]
      exact isClosed_eq (continuous_zpow (-e)) continuous_const
    have hzK : Subgroup.zpowers γ' ≤ K := by
      rw [Subgroup.zpowers_le, MonoidHom.mem_ker, zpowGroupHom_apply, ← hγχ]
      exact h1
    have hmem := Subgroup.topologicalClosure_minimal _ hzK hK (hgen' (Subgroup.mem_map_of_mem _ hg))
    rw [MonoidHom.mem_ker, zpowGroupHom_apply] at hmem
    exact hg1 hmem
  have hsurj : Function.Surjective fun m => ρ ⟨γ, hγ⟩ m - m := by
    intro y
    have hu : ((cycZ F Ω l γ ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) - 1 ≠ 0 := by
      intro h0'
      exact hne (Units.val_eq_one.mp (sub_eq_zero.mp h0'))
    obtain ⟨x, hx⟩ := (qzBasic l).1 _ hu y
    refine ⟨x, ?_⟩
    simp only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, qzG_apply]
    rw [← hx]
    simp only [sub_smul, one_smul]
  have hzr : (fun g : Dec (F := F) A => z g) ∈ Z1 ρ := by
    refine ⟨hz.1.comp continuous_subtype_val, fun a b => ?_⟩
    have := hz.2 a b
    simp only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.coe_mul]
    exact this
  have hB := cobOfGen l (Dec (F := F) A) χ ℤ_[l] (QZ l) ρ ⟨γ, hγ⟩ hχc hρc htriv hgen hsurj _ hzr
    (fun g hg => h0 g g.2 (by simpa [χ] using hg))
  obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ _).mp hB
  refine ⟨m, fun g hg => ?_⟩
  have := hm ⟨g, hg⟩
  simpa [ρ] using this

theorem UpperTheory.V.Kum.resInfOnto :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ), e ≠ 0 → Procyc F Ω l → (Sha D e).map (resInf D e) = EqHom l (Uinf F Ω l) (qzG F Ω l e) := by
  intro F Ω _ _ _ _ _ l _ D e he hP
  apply le_antisymm (resInfMem F Ω l D e)
  intro φ hφ
  have hX := (Submodule.mem_inf.mp hφ).1
  have hC := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hφ).2
  have hlc : IsLocallyConstant φ := hX.1
  have hadd : ∀ a b, φ (a * b) = φ a + φ b := hX.2.1
  have hIne : ∀ (A : ValuationSubring Ω) (u : Uinf F Ω l), (u : G F Ω) ∈ Ine A → φ u = 0 := hX.2.2.1
  have hDec : ∀ (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 →
      ∀ u : Uinf F Ω l, (u : G F Ω) ∈ Dec A → φ u = 0 := hX.2.2.2
  have hmemU : ∀ g : G F Ω, cycZ F Ω l g = 1 → g ∈ Uinf F Ω l := by
    intro g hg
    simp only [Uinf, cycU, Subgroup.mem_inf, MonoidHom.mem_ker]
    exact ⟨Subgroup.mem_top g, hg⟩
  have htriv : ∀ u ∈ Uinf F Ω l, ∀ m, qzG F Ω l e u m = m := by
    intro u hu m
    simp only [Uinf, cycU, Subgroup.mem_inf, MonoidHom.mem_ker] at hu
    rw [qzG_apply, hu.2, one_zpow, Units.val_one, one_smul]
  obtain ⟨z, hz, hzφ⟩ := extCocycle F Ω l ℤ_[l] (QZ l) (qzG F Ω l e) φ hP (contAction_qzG e) htriv
    (qzBasic l).2.1 hlc hadd hC
  have hρ' : ∀ g m, ((qzTw D e).comp (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))))) g m = qzG F Ω l e g m := by
    intro g m
    rw [qzTw_comp_toGS]
  have hz' : z ∈ Z1 ((qzTw D e).comp (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))))) := by
    rw [qzTw_comp_toGS]
    exact hz
  have hsha := shaInfl F Ω D.S D.A D.hA ℤ_[l] (QZ l) (qzTw D e) (contTw F Ω l D e).1
  have hmk : (Submodule.Quotient.mk ⟨z, hz'⟩ : H1 ((qzTw D e).comp (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))))) ∈
      ShaAbs ((qzTw D e).comp (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))))) (D.S : Set (HeightOneSpectrum (𝓞 F))) := by
    rw [mk_mem_ShaAbs]
    refine ⟨fun v hv A hA => ?_, fun v hv A hA => ⟨0, fun g hg => ?_⟩⟩
    · rw [D.hS] at hv
      have hAl : A.valuation (l : Ω) < 1 := ((placeDict F Ω).2.2.2 A v l hA).mpr hv
      obtain ⟨m, hm⟩ := decCob he hP hv hA hz (fun g hg hg1 => by
        rw [show z g = φ ⟨g, hmemU g hg1⟩ from hzφ ⟨g, hmemU g hg1⟩]
        exact hDec A hAl ⟨g, hmemU g hg1⟩ hg)
      refine ⟨m, fun g hg => ?_⟩
      rw [hρ']
      exact hm g hg
    · have hgN : g ∈ NS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) :=
        Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure
          (Set.mem_biUnion (x := v) hv (Set.mem_biUnion (x := A) hA hg)))
      have hg1 : cycZ F Ω l g = 1 := by
        rw [← DFunLike.congr_fun D.hchi g, MonoidHom.comp_apply]
        have : toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) g = 1 := (QuotientGroup.eq_one_iff g).mpr hgN
        rw [this, map_one]
      simp only [map_zero, sub_zero]
      show z g = 0
      rw [show z g = φ ⟨g, hmemU g hg1⟩ from hzφ ⟨g, hmemU g hg1⟩]
      exact hIne A ⟨g, hmemU g hg1⟩ hg
  rw [← hsha] at hmk
  obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.mp hmk
  refine Submodule.mem_map.mpr ⟨y, hy, ?_⟩
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  change Submodule.Quotient.mk (restrictCocycles1 (qzTw D e) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))) _ w) =
    Submodule.Quotient.mk ⟨z, hz'⟩ at hyz
  rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1] at hyz
  obtain ⟨m, hm⟩ := hyz
  funext u
  have h1 := hm u
  rw [hρ', htriv u u.2, sub_self, Submodule.coe_sub, Pi.sub_apply, sub_eq_zero] at h1
  rw [resInf_mk, ← hzφ u]
  exact h1
