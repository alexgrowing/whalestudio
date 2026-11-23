import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.PotMove
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base
open scoped Pointwise

private theorem fixAux {K Ω : Type} [Field K] [NumberField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (u : G ℚ Ω) (c : G K Ω ≃* G K Ω)
    (hc : ∀ s, galEmb ℚ K Ω (c s) = u * galEmb ℚ K Ω s * u⁻¹) (x : K) :
    ∃ y : K, algebraMap K Ω y = u (algebraMap K Ω x) := by
  haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω
  have h1 : u (algebraMap K Ω x) ∈ (⊥ : IntermediateField K Ω) := by
    rw [← InfiniteGalois.fixedField_bot, IntermediateField.mem_fixedField_iff]
    intro s _
    obtain ⟨t, rfl⟩ := c.surjective s
    have h2 : (c t) (u (algebraMap K Ω x)) = (u * galEmb ℚ K Ω t * u⁻¹) (u (algebraMap K Ω x)) :=
      DFunLike.congr_fun (hc t) _
    have h3 : (galEmb ℚ K Ω t) (algebraMap K Ω x) = algebraMap K Ω x := t.commutes x
    rw [h2]
    simp [h3]
  obtain ⟨y, hy⟩ := IntermediateField.mem_bot.1 h1
  exact ⟨y, hy⟩

private theorem mem_decomposition_conj_iff {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (u : G ℚ Ω) (A A' : ValuationSubring Ω)
    (hu : ∀ x, x ∈ A' ↔ u x ∈ A) (t : G ℚ Ω) :
    t ∈ Dec (F := ℚ) A' ↔ u * t * u⁻¹ ∈ Dec (F := ℚ) A := by
  have hgA : u • A' = A := by
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hu]
    simp [AlgEquiv.smul_def]
  rw [mem_Dec, mem_Dec, ← hgA, mul_smul, inv_smul_smul, mul_smul, smul_left_cancel_iff]

private theorem partialTrace_valuation_sum {K Ω : Type} [Field K] [NumberField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    (u : G ℚ Ω) (c : G K Ω ≃* G K Ω) (hc : ∀ s, galEmb ℚ K Ω (c s) = u * galEmb ℚ K Ω s * u⁻¹)
    (r : G K Ω →* GL (Fin n) (Qbar l)) (A A' : ValuationSubring Ω) (hu : ∀ x, x ∈ A' ↔ u x ∈ A)
    (hA : PotCrysAt r A) : PotCrysAt (r.comp c.toMonoidHom) A' := by
  obtain ⟨O, i1, i2, i3, Bw, hj, LL', r', ⟨hle, hmap⟩, K', hK', hcr⟩ := hA
  have hc' : ∀ s, galEmb ℚ K Ω (c.symm s) = u⁻¹ * galEmb ℚ K Ω s * u := fun s => by
    have h := hc (c.symm s)
    rw [c.apply_symm_apply] at h
    rw [h]; group
  have hmem : ∀ s : G K Ω, s ∈ Dec (F := K) A' ↔ c s ∈ Dec (F := K) A := fun s => by
    change galEmb ℚ K Ω s ∈ Dec (F := ℚ) A' ↔ galEmb ℚ K Ω (c s) ∈ Dec (F := ℚ) A
    rw [hc]
    exact mem_decomposition_conj_iff u A A' hu _
  let φ : ↥(Dec (F := K) A') ≃* ↥(Dec (F := K) A) :=
    { toFun := fun s => ⟨c s, (hmem s).1 s.2⟩
      invFun := fun t => ⟨c.symm t, (hmem _).2 (by rw [c.apply_symm_apply]; exact t.2)⟩
      left_inv := fun s => Subtype.ext (c.symm_apply_apply _)
      right_inv := fun t => Subtype.ext (c.apply_symm_apply _)
      map_mul' := fun s t => Subtype.ext (map_mul c _ _) }
  have hemb := (galEmbTop ℚ K Ω).1
  have hcc : Continuous c := hemb.continuous_iff.2 (by
    have e : (galEmb ℚ K Ω) ∘ c = fun s => u * galEmb ℚ K Ω s * u⁻¹ := funext hc
    rw [e]
    exact (continuous_const.mul hemb.continuous).mul continuous_const)
  have hcs : Continuous c.symm := hemb.continuous_iff.2 (by
    have e : (galEmb ℚ K Ω) ∘ c.symm = fun s => u⁻¹ * galEmb ℚ K Ω s * u := funext hc'
    rw [e]
    exact (continuous_const.mul hemb.continuous).mul continuous_const)
  have hφ : Continuous φ := (hcc.comp continuous_subtype_val).subtype_mk _
  have hφs : Continuous φ.symm := (hcs.comp continuous_subtype_val).subtype_mk _
  let Bw' : LocBridge l K Ω (Dec (F := K) A') O :=
    { Kw := Bw.Kw, j := Bw.j.comp (u : Ω →+* Ω)
      j_E := fun x => by
        change Bw.j (u (algebraMap K Ω x)) ∈ _
        obtain ⟨y, hy⟩ := fixAux u c hc x
        rw [← hy]; exact Bw.j_E y
      j_dense := Bw.j_dense.trans (closure_mono (by
        rintro _ ⟨x, rfl⟩
        obtain ⟨y, hy⟩ := fixAux u⁻¹ c.symm hc' x
        refine ⟨y, ?_⟩
        change Bw.j (u (algebraMap K Ω y)) = Bw.j (algebraMap K Ω x)
        rw [hy]
        simp))
      e := φ.trans Bw.e
      e_cont := Bw.e_cont.comp hφ, e_symm_cont := hφs.comp Bw.e_symm_cont
      e_comm := fun s x => by
        refine (Bw.e_comm (φ s) (u x)).trans ?_
        have h2 : (c (s : G K Ω)) (u x) = (u * galEmb ℚ K Ω (s : G K Ω) * u⁻¹) (u x) :=
          DFunLike.congr_fun (hc s) _
        change Bw.j ((c (s : G K Ω)) (u x)) = Bw.j (u ((s : G K Ω) x))
        rw [h2]
        congr 1
        simp
        rfl
      LL := Bw.LL, LL_split := Bw.LL_split, eO := Bw.eO, eO_alg := Bw.eO_alg
      eO_cont := Bw.eO_cont, eO_symm_cont := Bw.eO_symm_cont }
  refine ⟨O, i1, i2, i3, Bw', fun x => (hu x).trans (hj (u x)), LL', r'.comp φ.toMonoidHom,
    ⟨hle, MonoidHom.ext fun s => DFunLike.congr_fun hmap (φ s)⟩, K', hK', ?_⟩
  have e : Bw'.repE LL' (r'.comp φ.toMonoidHom) = Bw.repE LL' r' := by
    refine MonoidHom.ext fun t => ?_
    simp [LocBridge.repE, Bw']
  rw [e]
  exact hcr

end

theorem UpperTheory.potentiallyCrystalline_comp_conjugation :
    ∀ {K Ω : Type} [Field K] [NumberField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω] [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
        (u : G ℚ Ω) (c : G K Ω ≃* G K Ω), (∀ s, UpperTheory.V.Base.galEmb ℚ K Ω (c s) = u * UpperTheory.V.Base.galEmb ℚ K Ω s * u⁻¹) →
        ∀ (r : G K Ω →* GL (Fin n) (Qbar l)) (A A' : ValuationSubring Ω), (∀ x, x ∈ A' ↔ u x ∈ A) →
          UpperTheory.V.Af.PotCrysAt r A → UpperTheory.V.Af.PotCrysAt (r.comp c.toMonoidHom) A' := by
  intro K Ω _ _ _ _ _ _ _ l _ n u c hc r A A' hu hA
  exact partialTrace_valuation_sum u c hc r A A' hu hA
