import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.LeviConstTerm

theorem setIntegral_comp_aut {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G) [μ.IsAddHaarMeasure] (𝓕 : Set G)
    (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h1 : μ 𝓕 = 1) (T : G ≃ₜ+ G) (hT : ∀ x ∈ Γ, T x ∈ Γ)
    (hT' : ∀ x ∈ Γ, T.symm x ∈ Γ) (h : G → ℂ) (hinv : ∀ (γ : Γ) (x : G), h (γ +ᵥ x) = h x) :
    ∫ x in 𝓕, h (T x) ∂μ = ∫ x in 𝓕, h x ∂μ := by
  have key : ∀ U : G ≃ₜ+ G, (∀ x ∈ Γ, U x ∈ Γ) → (∀ x ∈ Γ, U.symm x ∈ Γ) →
      MeasurePreserving U μ μ ∧ IsAddFundamentalDomain Γ (U ⁻¹' 𝓕) μ := by
    intro U hU hU'
    have hmeas : Measurable U := U.continuous.measurable
    haveI : (μ.map U).IsAddHaarMeasure := U.isAddHaarMeasure_map μ
    have hc := Measure.isAddLeftInvariant_eq_smul (μ.map U) μ
    have hq : Measure.QuasiMeasurePreserving U μ μ := ⟨hmeas, by rw [hc]; exact Measure.smul_absolutelyContinuous⟩
    have hS : IsAddFundamentalDomain Γ (U ⁻¹' 𝓕) μ := by
      refine h𝓕.preimage_of_equiv (e := fun γ : Γ => (⟨U.symm γ, hU' _ γ.2⟩ : Γ)) hq ?_ ?_
      · refine ⟨fun x y hxy => Subtype.ext (U.symm.injective (congrArg Subtype.val hxy)), fun y => ⟨⟨U y, hU _ y.2⟩, ?_⟩⟩
        exact Subtype.ext (U.symm_apply_apply _)
      · intro γ x
        change U (U.symm γ + x) = (γ : G) + U x
        rw [map_add, U.apply_symm_apply]
    refine ⟨⟨hmeas, ?_⟩, hS⟩
    have h2 : μ (U ⁻¹' 𝓕) = 1 := (hS.measure_eq h𝓕).trans h1
    have h3 : μ.map U 𝓕 = 1 := by
      rw [Measure.map_apply₀ hmeas.aemeasurable (h𝓕.nullMeasurableSet.mono_ac hq.2), h2]
    rw [hc, Measure.smul_apply, h1] at h3
    have h4 : (μ.map U).addHaarScalarFactor μ = 1 := by
      simpa [ENNReal.smul_def] using h3
    rw [hc, h4, one_smul]
  have hmp := (key T hT hT').1
  have hS := (key T.symm hT' hT).2
  have hemb : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  have hpre : T ⁻¹' (T.symm ⁻¹' 𝓕) = 𝓕 := by ext x; simp
  calc ∫ x in 𝓕, h (T x) ∂μ = ∫ x in T ⁻¹' (T.symm ⁻¹' 𝓕), h (T x) ∂μ := by rw [hpre]
    _ = ∫ x in T.symm ⁻¹' 𝓕, h x ∂μ := hmp.setIntegral_preimage_emb hemb h _
    _ = ∫ x in 𝓕, h x ∂μ := hS.setIntegral_eq h𝓕 hinv

variable {R : Type} [CommRing R] {a r : ℕ}

def IsBlockSL2Embedding (r : ℕ) (m : Matrix (Fin a) (Fin a) R) : Prop :=
  ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ m i j = 0

def conjN (m n : Matrix (Fin a) (Fin a) R) (x : BlockIx a r → R) : BlockIx a r → R :=
  fun p => (m * nilM x * n) p.1.1 p.1.2

theorem nilM_conjN {m n : Matrix (Fin a) (Fin a) R} (hm : IsBlockSL2Embedding r m) (hn : IsBlockSL2Embedding r n) (x : BlockIx a r → R) :
    nilM (conjN m n x) = m * nilM x * n := by
  ext i j
  by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
  · simp only [nilM, Matrix.of_apply, dif_pos h]; rfl
  · rw [nilM, Matrix.of_apply, dif_neg h, Matrix.mul_apply]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    rcases hn k j with h1 | h1
    · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
      intro l _
      rcases hm i l with h2 | h2
      · rw [nilM, Matrix.of_apply, dif_neg (fun h' => h (by omega)), mul_zero]
      · rw [h2, zero_mul]
    · rw [h1, mul_zero]

theorem nilM_add (x y : BlockIx a r → R) : nilM (x + y) = nilM x + nilM y := by
  ext i j; simp only [nilM, Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp

theorem conjN_add (m n : Matrix (Fin a) (Fin a) R) (x y : BlockIx a r → R) :
    conjN m n (x + y) = conjN m n x + conjN m n y := by
  funext p
  simp only [conjN, nilM_add, mul_add, add_mul, Matrix.add_apply, Pi.add_apply]

theorem conjN_conjN {m n m' n' : Matrix (Fin a) (Fin a) R} (hm : IsBlockSL2Embedding r m) (hn : IsBlockSL2Embedding r n)
    (h1 : m' * m = 1) (h2 : n * n' = 1) (x : BlockIx a r → R) : conjN m' n' (conjN m n x) = x := by
  funext p
  have : m' * (m * nilM x * n) * n' = nilM x := by
    rw [show m' * (m * nilM x * n) * n' = (m' * m) * nilM x * (n * n') by simp only [mul_assoc], h1, h2, one_mul,
      mul_one]
  rw [conjN, nilM_conjN hm hn, this, nilM, Matrix.of_apply, dif_pos p.2]

theorem continuous_conjN [TopologicalSpace R] [IsTopologicalRing R] (m n : Matrix (Fin a) (Fin a) R) :
    Continuous (conjN (r := r) m n) := by
  have h : Continuous (nilM : (BlockIx a r → R) → Matrix (Fin a) (Fin a) R) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [nilM, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  refine continuous_pi fun p => ?_
  exact ((continuous_const.matrix_mul h).matrix_mul continuous_const).matrix_elem _ _

theorem conjN_map {S : Type} [CommRing S] (φ : R →+* S) (m n : Matrix (Fin a) (Fin a) R) (x : BlockIx a r → R) :
    conjN (m.map φ) (n.map φ) (fun p => φ (x p)) = fun p => φ (conjN m n x p) := by
  have : nilM (fun p => φ (x p)) = (nilM x).map φ := by
    ext i j; simp only [nilM, Matrix.of_apply, Matrix.map_apply]; split_ifs <;> simp
  funext p
  rw [conjN, conjN, this, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]

theorem IsBlockSL2Embedding.map {S : Type} [CommRing S] (φ : R →+* S) {m : Matrix (Fin a) (Fin a) R} (hm : IsBlockSL2Embedding r m) :
    IsBlockSL2Embedding r (m.map φ) := fun i j => (hm i j).imp id fun h => by rw [Matrix.map_apply, h, map_zero]

theorem unip_mul (m : GL (Fin a) R) (hm : IsBlockSL2Embedding r m.val) (hm' : IsBlockSL2Embedding r m⁻¹.val) (x : BlockIx a r → R) :
    unip x * m = m * unip (conjN m⁻¹.val m.val x) := by
  apply Units.ext
  change (1 + nilM x) * m.val = m.val * (1 + nilM (conjN m⁻¹.val m.val x))
  rw [nilM_conjN hm' hm, mul_add, add_mul, one_mul, mul_one, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]

theorem constTerm_levi_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ f : GA E a → ℂ, (∀ γ g, f (ratGL E a γ * g) = f g) → ∀ (γ : GL (Fin r) E × GL (Fin (a - r)) E) (g : GA E a), ∫ x in 𝓕, f (unip x * (ratGL E a (GlobalTheory.LeviGA.blkGL hr γ) * g)) ∂μ = ∫ x in 𝓕, f (unip x * g) ∂μ := by
  intro E _ _ _ a r hr _ _ μ 𝓕 hμ h𝓕 h1 f hf γ g
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (ratN E a r) := by
    have : ((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)) = Set.range
        (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) := AddMonoidHom.coe_range _
    change Countable (((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)))
    rw [this]; exact (Set.countable_range _).to_subtype
  haveI : SecondCountableTopology (Ad E) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : LocallyCompactSpace (Ad E) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  set h : (BlockIx a r → Ad E) → ℂ := fun x => f (unip x * g) with hh
  have hinv : ∀ (γ : ratN E a r) (x : BlockIx a r → Ad E), h (γ +ᵥ x) = h x := by
    rintro ⟨_, e, rfl⟩ x
    change f (unip ((fun p => algebraMap E (Ad E) (e p)) + x) * g) = f (unip x * g)
    rw [unip_add, unip_algebraMap, mul_assoc, hf]
  obtain ⟨m, hm⟩ : ∃ m, m = GlobalTheory.LeviGA.blkGL hr γ := ⟨_, rfl⟩
  have hb : IsBlockSL2Embedding r m.val := hm ▸ GlobalTheory.LeviGA.blkGL_block hr γ
  have hb' : IsBlockSL2Embedding r m⁻¹.val := by
    rw [hm, ← map_inv]; exact GlobalTheory.LeviGA.blkGL_block hr γ⁻¹
  rw [← hm]
  have e1 : (ratGL E a m).val = m.val.map (algebraMap E (Ad E)) := rfl
  have e2 : (ratGL E a m)⁻¹.val = m⁻¹.val.map (algebraMap E (Ad E)) := rfl
  have hB : IsBlockSL2Embedding r (ratGL E a m).val := e1 ▸ hb.map _
  have hB' : IsBlockSL2Embedding r (ratGL E a m)⁻¹.val := e2 ▸ hb'.map _
  let T : (BlockIx a r → Ad E) ≃ₜ+ (BlockIx a r → Ad E) :=
    { toFun := conjN (ratGL E a m)⁻¹.val (ratGL E a m).val
      invFun := conjN (ratGL E a m).val (ratGL E a m)⁻¹.val
      left_inv := conjN_conjN hB' hB (Units.mul_inv _) (Units.mul_inv _)
      right_inv := conjN_conjN hB hB' (Units.inv_mul _) (Units.inv_mul _)
      map_add' := conjN_add _ _
      continuous_toFun := continuous_conjN _ _
      continuous_invFun := continuous_conjN _ _ }
  have hL : ∀ x, f (unip x * (ratGL E a m * g)) = h (T x) := fun x => by
    rw [← mul_assoc, unip_mul _ hB hB', mul_assoc, hf]; rfl
  simp_rw [hL]
  refine setIntegral_comp_aut (ratN E a r) μ 𝓕 h𝓕 h1 T ?_ ?_ h hinv
  · rintro _ ⟨e, rfl⟩
    exact ⟨conjN m⁻¹.val m.val e, (conjN_map (algebraMap E (Ad E)) _ _ e).symm⟩
  · rintro _ ⟨e, rfl⟩
    exact ⟨conjN m.val m⁻¹.val e, (conjN_map (algebraMap E (Ad E)) _ _ e).symm⟩

end GlobalTheory.LeviConstTerm
