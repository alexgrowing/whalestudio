import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegreeCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpFibreSemilocal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocCentreDom
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocFamilyFinite
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocFibreFinite
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocFibreMinimal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocFinite
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocInChart
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocLocalization
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocMaxCentre
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocMax
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocMaxPoint
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocPointLoc
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocPointMax
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocRingFrac
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocRingInj
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocRingIso
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpColonFinite
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingDimLe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingIsLocal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingLocal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingMem
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingNoetherian
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleHomLoc
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PChartsInColon
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPowSpanFinrankBounded
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPrincipalReductionOfBoundedGens
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMultiHomogPrimeAvoid
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealCorresp
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFDegree

namespace PositivityTheory.Xgn.A_s_blowupfibre
open GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers MvPolynomial

theorem inertiaDeg_eq_relfinrank {A B E : Type*} [CommRing A] [CommRing B] [Algebra A B] [Field E]
    (L M : Subfield E) (τ : B →+* E) (𝔫 : Ideal B) (h𝔫 : ∀ b, b ∈ 𝔫 ↔ τ b = 0)
    (hM : ∀ z, z ∈ M ↔ ∃ b, τ b = z) (hL : ∀ z, z ∈ L ↔ ∃ a, τ (algebraMap A B a) = z) :
    𝔫.inertiaDeg A = Subfield.relfinrank L M := by
  have hLM : L ≤ M := fun z hz => by
    obtain ⟨a, ha⟩ := (hL z).mp hz
    exact (hM z).mpr ⟨_, ha⟩
  let τ' : B →+* (Subfield.extendScalars hLM) :=
    τ.codRestrict (Subfield.extendScalars hLM) (fun b => (hM _).mpr ⟨b, rfl⟩)
  let σ : A →+* L := (τ.comp (algebraMap A B)).codRestrict L (fun a => (hL _).mpr ⟨a, rfl⟩)
  have hτ : Function.Surjective τ' := by
    rintro ⟨z, hz⟩
    obtain ⟨b, rfl⟩ := (hM z).mp hz
    exact ⟨b, rfl⟩
  have hσ : Function.Surjective σ := by
    rintro ⟨z, hz⟩
    obtain ⟨a, rfl⟩ := (hL z).mp hz
    exact ⟨a, rfl⟩
  have hk : 𝔫 = RingHom.ker τ' := by
    ext b
    rw [h𝔫, RingHom.mem_ker, ← ZeroMemClass.coe_eq_zero]
    rfl
  subst hk
  have : (RingHom.ker τ').IsMaximal := RingHom.ker_isMaximal_of_surjective τ' hτ
  have : (RingHom.ker σ).IsMaximal := RingHom.ker_isMaximal_of_surjective σ hσ
  have : (RingHom.ker τ').LiesOver (RingHom.ker σ) := ⟨by
    ext a
    rw [Ideal.under_def, Ideal.mem_comap, h𝔫, RingHom.mem_ker, ← ZeroMemClass.coe_eq_zero]
    rfl⟩
  rw [Ideal.inertiaDeg_eq_of_isMaximal (RingHom.ker σ), Subfield.relfinrank_eq_finrank_of_le hLM]
  refine Algebra.finrank_eq_of_equiv_equiv (RingHom.quotientKerEquivOfSurjective hσ)
    (RingHom.quotientKerEquivOfSurjective hτ) ?_
  ext a
  rfl

theorem exists_residue {S F E : Type*} [CommRing S] [Field F] [Field E] (ev : S →+* F) (r : S →+* E)
    (hker : ∀ s, ev s = 0 → r s = 0) (Ω : Subring F)
    (hΩ : ∀ z ∈ Ω, ∃ f g, r g ≠ 0 ∧ z = ev f / ev g) :
    ∃ ρ : Ω →+* E, ∀ (x : Ω) f g, r g ≠ 0 → (x : F) = ev f / ev g → ρ x = r f / r g := by
  have hne : ∀ {g}, r g ≠ 0 → ev g ≠ 0 := fun hg h => hg (hker _ h)
  have hwd : ∀ {f g f' g'}, r g ≠ 0 → r g' ≠ 0 → ev f / ev g = ev f' / ev g' →
      r f / r g = r f' / r g' := by
    intro f g f' g' hg hg' h
    rw [div_eq_div_iff (hne hg) (hne hg')] at h
    rw [div_eq_div_iff hg hg', ← sub_eq_zero, ← map_mul, ← map_mul, ← map_sub]
    apply hker
    rw [map_sub, map_mul, map_mul, h, sub_self]
  choose nu de hde hrep using hΩ
  have key : ∀ (x : Ω) f g, r g ≠ 0 → (x : F) = ev f / ev g →
      r (nu x.1 x.2) / r (de x.1 x.2) = r f / r g := fun x f g hg hx =>
    hwd (hde _ _) hg ((hrep _ _).symm.trans hx)
  refine ⟨{ toFun := fun x => r (nu x.1 x.2) / r (de x.1 x.2)
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, key⟩
  · rw [key 1 1 1 (by simp) (by simp)]; simp
  · intro x y
    have hx := hde x.1 x.2
    have hy := hde y.1 y.2
    rw [key (x * y) (nu x.1 x.2 * nu y.1 y.2) (de x.1 x.2 * de y.1 y.2)
      (by rw [map_mul]; exact mul_ne_zero hx hy)
      (by rw [map_mul, map_mul, ← div_mul_div_comm, ← hrep, ← hrep]; rfl), map_mul, map_mul,
      div_mul_div_comm]
  · rw [key 0 0 1 (by simp) (by simp)]; simp
  · intro x y
    have hx := hde x.1 x.2
    have hy := hde y.1 y.2
    rw [key (x + y) (nu x.1 x.2 * de y.1 y.2 + de x.1 x.2 * nu y.1 y.2) (de x.1 x.2 * de y.1 y.2)
      (by rw [map_mul]; exact mul_ne_zero hx hy)
      (by rw [map_add, map_mul, map_mul, map_mul, ← div_add_div _ _ (hne hx) (hne hy), ← hrep,
        ← hrep]; rfl), map_add, map_mul, map_mul, map_mul, div_add_div _ _ hx hy]

theorem homog_map {O k K : Type} [CommRing O] [CommRing k] [DecidableEq K] {ι : K → Type}
    (π : O →+* k) {f : MRing ι O} {b : K → ℕ} (hf : IsMultiHomog f b) :
    IsMultiHomog (MvPolynomial.map π f : MRing ι k) b := by
  intro d hd
  apply hf
  intro h
  apply hd
  rw [coeff_map, h, map_zero]

theorem exists_homog_lift {O k K : Type} [CommRing O] [CommRing k] [DecidableEq K] {ι : K → Type}
    (π : O →+* k) (hπ : Function.Surjective π) {f : MRing ι k} {b : K → ℕ} (hf : IsMultiHomog f b) :
    ∃ f' : MRing ι O, IsMultiHomog f' b ∧ MvPolynomial.map π f' = f := by
  classical
  obtain ⟨f₀, rfl⟩ := MvPolynomial.map_surjective π hπ f
  refine ⟨weightedHomogeneousComponent (blockWeight ι) b f₀,
    weightedHomogeneousComponent_isWeightedHomogeneous _ _, ?_⟩
  ext d
  rw [coeff_map, coeff_weightedHomogeneousComponent]
  split_ifs with h
  · rw [coeff_map]
  · rw [map_zero]
    by_contra h0
    exact h (hf (Ne.symm h0))

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem exists_residue_hom {O k K : Type} [CommRing O] [Field k] [DecidableEq K] {ι : K → Type}
    (π : O →+* k) (hπ : Function.Surjective π) (P W : Ideal (MRing ι O)) [P.IsPrime]
    (hPW : P ≤ W) (V : Ideal (MRing ι k)) [V.IsPrime]
    (hV : ∀ f : MRing ι O, MvPolynomial.map π f ∈ V ↔ f ∈ W) :
    ∃ ρ : homLocRing P W →+* FractionRing (MRing ι k ⧸ V),
      (∀ (x : homLocRing P W) (f g : MRing ι O), g ∉ W →
        (x : FractionRing (MRing ι O ⧸ P)) =
          algebraMap (MRing ι O ⧸ P) _ (Ideal.Quotient.mk P f) /
            algebraMap (MRing ι O ⧸ P) _ (Ideal.Quotient.mk P g) →
        ρ x = algebraMap (MRing ι k ⧸ V) _ (Ideal.Quotient.mk V (MvPolynomial.map π f)) /
            algebraMap (MRing ι k ⧸ V) _ (Ideal.Quotient.mk V (MvPolynomial.map π g))) ∧
      (∀ x, ρ x ≠ 0 → IsUnit x) ∧
      ∀ z, z ∈ homFracDegZero V ↔ ∃ x, ρ x = z := by
  have hW : W.IsPrime := by
    have : W = V.comap (MvPolynomial.map π) := by
      ext f; rw [Ideal.mem_comap, hV]
    rw [this]
    exact Ideal.comap_isPrime _ _
  let ev : MRing ι O →+* FractionRing (MRing ι O ⧸ P) :=
    (algebraMap (MRing ι O ⧸ P) _).comp (Ideal.Quotient.mk P)
  let r : MRing ι O →+* FractionRing (MRing ι k ⧸ V) :=
    ((algebraMap (MRing ι k ⧸ V) _).comp (Ideal.Quotient.mk V)).comp (MvPolynomial.map π)
  have hr : ∀ f, r f = 0 ↔ f ∈ W := fun f => by
    show algebraMap (MRing ι k ⧸ V) (FractionRing (MRing ι k ⧸ V))
      (Ideal.Quotient.mk V (MvPolynomial.map π f)) = 0 ↔ _
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem, hV]
  have hev : ∀ f, ev f = 0 ↔ f ∈ P := fun f => by
    show algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P))
      (Ideal.Quotient.mk P f) = 0 ↔ _
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hmem := HomLocRingMem.proof O K ι P W hW hPW
  have hunit := (HomLocRingIsLocal.proof HomLocRingMem.proof O K ι P W hW hPW).2
  obtain ⟨ρ, hρ⟩ := exists_residue ev r (fun s hs => (hr s).mpr (hPW ((hev s).mp hs)))
    (homLocRing P W) (fun z hz => by
      obtain ⟨b, f, g, -, -, hg, rfl⟩ := (hmem z).mp hz
      exact ⟨f, g, fun h => hg ((hr g).mp h), rfl⟩)
  have hρ' : ∀ (x : homLocRing P W) (f g : MRing ι O), g ∉ W → (x : FractionRing (MRing ι O ⧸ P)) =
      ev f / ev g → ρ x = r f / r g := fun x f g hg hx => hρ x f g (fun h => hg ((hr g).mp h)) hx
  have hu : ∀ x, ρ x ≠ 0 → IsUnit x := by
    rintro ⟨x, hx⟩ h0
    obtain ⟨b, f, g, hf, hg, hgW, rfl⟩ := (hmem x).mp hx
    rw [hunit b f g hf hg hgW hx]
    intro hfW
    apply h0
    rw [hρ' _ f g hgW rfl, (hr f).mpr hfW, zero_div]
  refine ⟨ρ, hρ', hu, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · have hgen : ∀ (b : K → ℕ) (f g : MRing ι k), IsMultiHomog f b → IsMultiHomog g b → g ∉ V →
        ∃ x, ρ x = algebraMap (MRing ι k ⧸ V) _ (Ideal.Quotient.mk V f) /
          algebraMap (MRing ι k ⧸ V) _ (Ideal.Quotient.mk V g) := by
      intro b f g hf hg hgV
      obtain ⟨f, hf', rfl⟩ := exists_homog_lift π hπ hf
      obtain ⟨g, hg', rfl⟩ := exists_homog_lift π hπ hg
      have hgW : g ∉ W := fun h => hgV ((hV g).mpr h)
      exact ⟨⟨_, (hmem _).mpr ⟨b, f, g, hf', hg', hgW, rfl⟩⟩, hρ' _ f g hgW rfl⟩
    unfold homFracDegZero at hz
    induction hz using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨b, f, g, hf, hg, hgV, rfl⟩ := hx
      exact hgen b f g hf hg hgV
    | algebraMap c =>
      obtain ⟨x, hx⟩ := hgen 0 (C c) 1 (isWeightedHomogeneous_C _ _) (isWeightedHomogeneous_one _ _)
        ((Ideal.ne_top_iff_one V).mp Ideal.IsPrime.ne_top')
      refine ⟨x, hx.trans ?_⟩
      rw [map_one, map_one, div_one, IsScalarTower.algebraMap_apply k (MRing ι k ⧸ V),
        ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]
    | add x y _ _ hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      exact ⟨x + y, map_add _ _ _⟩
    | inv x _ hx =>
      obtain ⟨x, rfl⟩ := hx
      by_cases h0 : ρ x = 0
      · exact ⟨0, by rw [h0, map_zero, inv_zero]⟩
      · obtain ⟨v, rfl⟩ := hu x h0
        exact ⟨(v⁻¹ : _ˣ), by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      exact ⟨x * y, map_mul _ _ _⟩
  · rintro ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨b, f, g, hf, hg, hgW, rfl⟩ := (hmem x).mp hx
    rw [hρ' _ f g hgW rfl]
    exact IntermediateField.subset_adjoin _ _
      ⟨b, _, _, homog_map π hf, homog_map π hg, fun h => hgW ((hV g).mp h), rfl⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem inertiaDeg_eq_relDeg {O k K : Type} [CommRing O] [Field k] [Fintype K] [DecidableEq K]
    {ι : K → Type} {J : Type}
    (π : O →+* k) (hπ : Function.Surjective π) (P W : Ideal (MRing ι O)) [P.IsPrime]
    (hPW : P ≤ W) (u : J → MRing ι O) (W' : Ideal (MRing (extIdx ι J) O))
    (hbl : blowUpOf P u ≤ W') (hW' : W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W)
    (V' : Ideal (MRing (extIdx ι J) k)) [V'.IsPrime]
    (hV' : ∀ f : MRing (extIdx ι J) O, MvPolynomial.map π f ∈ V' ↔ f ∈ W')
    (h : blowUpOverLoc P W u ≤ blowUpLocRing P u W') (𝔫 : Ideal (blowUpOverLoc P W u))
    (h𝔫 : 𝔫.IsMaximal)
    (hloc : letI := (Subring.inclusion h).toAlgebra
      haveI := h𝔫.isPrime
      IsLocalization.AtPrime (blowUpLocRing P u W') 𝔫) :
    𝔫.inertiaDeg (homLocRing P W) = relDeg Function.Embedding.some V' := by
  let _ := (Subring.inclusion h).toAlgebra
  have := h𝔫.isPrime
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  have hml : ∀ f : MRing ι O, (MvPolynomial.map π (liftForm (J := J) f) : MRing (extIdx ι J) k) =
      rename (blockIncl Function.Embedding.some (extIdx ι J)) (MvPolynomial.map π f) :=
    fun f => MvPolynomial.map_rename _ _ _
  let V : Ideal (MRing ι k) := contractPrime Function.Embedding.some V'
  have : V.IsPrime := contractPrime.isPrime Function.Embedding.some V'
  have hV : ∀ f : MRing ι O, MvPolynomial.map π f ∈ V ↔ f ∈ W := fun f => by
    rw [← hW', Ideal.mem_comap, ← hV', hml]
    rfl
  have hW : W.IsPrime := by
    have : W = V.comap (MvPolynomial.map π) := by
      ext f; rw [Ideal.mem_comap, hV]
    rw [this]
    exact Ideal.comap_isPrime _ _
  obtain ⟨ρ, hρ, hρu, hρr⟩ := exists_residue_hom π hπ (blowUpOf P u) W' hbl V' hV'
  obtain ⟨ρA, hρA, -, hρAr⟩ := exists_residue_hom π hπ P W hPW V hV
  obtain ⟨φ, hφ⟩ := BlowUpLocRingIso.proof O K ι J P u W' hbl
  let ρ' : blowUpLocRing P u W' →+* FractionRing (MRing (extIdx ι J) k ⧸ V') :=
    ρ.comp φ.symm.toRingHom
  let τ : blowUpOverLoc P W u →+* FractionRing (MRing (extIdx ι J) k ⧸ V') :=
    ρ'.comp (algebraMap (blowUpOverLoc P W u) (blowUpLocRing P u W'))
  have hτ : ∀ b, τ b = ρ' (algebraMap (blowUpOverLoc P W u) (blowUpLocRing P u W') b) := fun _ => rfl
  have hker : ∀ b, b ∈ 𝔫 ↔ τ b = 0 := by
    intro b
    rw [← not_iff_not, ← Ideal.mem_primeCompl_iff,
      ← IsLocalization.AtPrime.isUnit_to_map_iff (blowUpLocRing P u W') 𝔫 b]
    refine ⟨fun hb => (hb.map ρ').ne_zero, fun hb => ?_⟩
    have := (hρu _ hb).map φ
    simpa using this
  refine inertiaDeg_eq_relfinrank _ _ τ 𝔫 hker (fun z => ?_) (fun z => ?_)
  · refine (hρr z).trans ⟨?_, ?_⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj 𝔫.primeCompl (φ y)
      obtain ⟨t, m, hm, htm⟩ := h𝔫.exists_inv s.2
      refine ⟨b * t, ?_⟩
      have h1 : τ t * τ s = 1 := by
        rw [← map_mul, ← add_zero (τ _), ← (hker m).mp hm, ← map_add, htm, map_one]
      have h2 : ρ y * τ s = τ b := by
        rw [hτ, hτ, ← hbs, map_mul]
        congr 1
        show _ = ρ (φ.symm (φ y))
        rw [RingEquiv.symm_apply_apply]
      rw [map_mul, ← h2, mul_assoc, mul_comm (τ s), h1, mul_one]
    · rintro ⟨b, rfl⟩
      exact ⟨_, rfl⟩
  · have hcomp : ∀ a : homLocRing P W, τ (algebraMap _ _ a) =
        contractFracMap Function.Embedding.some V' (ρA a) := by
      rintro ⟨a, ha⟩
      obtain ⟨b, f, g, hf, hg, hgW, rfl⟩ := (HomLocRingMem.proof O K ι P W hW hPW a).mp ha
      have hgl : liftForm (J := J) g ∉ W' := fun hm => hgW (by rw [← hW']; exact hm)
      have h1 := hφ (liftMDeg b) _ _ (isMultiHomog_liftForm hf) (isMultiHomog_liftForm hg) hgl
      rw [blowUpEval_liftForm, blowUpEval_liftForm] at h1
      have h2 : φ.symm (algebraMap (blowUpOverLoc P W u) (blowUpLocRing P u W')
          (algebraMap (homLocRing P W) (blowUpOverLoc P W u) ⟨_, ha⟩)) =
          ⟨_, Subring.subset_closure ⟨liftMDeg b, _, _, isMultiHomog_liftForm hf,
            isMultiHomog_liftForm hg, hgl, rfl⟩⟩ := by
        rw [RingEquiv.symm_apply_eq]
        exact Subtype.ext h1.symm
      have h3 := congrArg (contractFracMap Function.Embedding.some V') (hρA ⟨_, ha⟩ f g hgW rfl)
      refine Eq.trans ?_ h3.symm
      refine (congrArg ρ h2).trans ((hρ _ _ _ hgl rfl).trans ?_)
      rw [hml, hml, ← contractFracMap_algebraMap, ← contractFracMap_algebraMap, ← map_div₀]
      rfl
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨a, rfl⟩ := (hρAr w).mp hw
      exact ⟨a, hcomp a⟩
    · rintro ⟨a, rfl⟩
      exact ⟨ρA a, (hρAr _).mpr ⟨a, rfl⟩, (hcomp a).symm⟩

theorem hloc : HomLocRingLocal.Statement.{0} :=
  HomLocRingLocal.proof (HomLocRingIsLocal.proof HomLocRingMem.proof)
    (HomLocRingNoetherian.proof HomLocRingMem.proof)
    (HomLocRingDimLe.proof HomLocRingMem.proof (HomLocRingIsLocal.proof HomLocRingMem.proof))

theorem hfin : BlowUpOverLocFinite.Statement.{0} :=
  BlowUpOverLocFinite.proof hloc BlowUpOverLocInChart.proof ChartsInColon.proof
    (BlowUpColonFinite.proof PowSpanFinrankBounded.proof PrincipalReductionOfBoundedGens.proof)

theorem hfam : BlowUpOverLocFamilyFinite.Statement.{0} :=
  BlowUpOverLocFamilyFinite.proof BlowUpOverLocFibreFinite.proof

theorem hcen : BlowUpOverLocMaxCentre.Statement.{0} :=
  BlowUpOverLocMaxCentre.proof BlowUpOverLocCentreDom.proof
    (BlowUpOverLocLocalization.proof hfam) hfin BlowUpLocRingIso.proof

theorem hptloc : BlowUpOverLocPointLoc.Statement.{0} :=
  BlowUpOverLocPointLoc.proof hfin hcen BlowUpLocRingInj.proof

theorem hptmax : BlowUpOverLocPointMax.Statement.{0} :=
  BlowUpOverLocPointMax.proof hfin BlowUpLocRingIso.proof
    (BlowUpLocRingFrac.proof BlowUpLocRingIso.proof hfam MultiHomogPrimeAvoid.proof)

theorem of_deg (hdeg : BlowUpOverLocPointDeg.Statement.{0}) : BlowUpFibreSemilocal.Statement.{0} :=
  BlowUpFibreSemilocal.proof hloc (DivCycleHomLoc.proof hloc) BlowUpLocRingIso.proof hfin
    (BlowUpOverLocMax.proof
      (BlowUpOverLocMaxPoint.proof hcen
        (BlowUpOverLocFibreMinimal.proof hptloc BlowUpLocRingInj.proof) hdeg)
      hptmax BlowUpLocRingInj.proof)

theorem hdeg : BlowUpOverLocPointDeg.Statement.{0} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel W' hW'min hW'rel hW'W
  have := hP.multiProj.isPrime
  obtain ⟨h, 𝔫, h𝔫, hl⟩ := hptmax O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
    W' hW'min hW'rel hW'W
  refine ⟨h, 𝔫, h𝔫, hl, ?_⟩
  have hϖW' : (C ϖ : MRing (extIdx ι J) O) ∈ W' := by
    rw [← hW'W, Ideal.mem_comap] at hϖW
    simpa [liftForm] using hϖW
  have hp : (specialIdeal W').IsPrime :=
    (SpecialIdealCorresp.proof O ϖ hϖ (Option K) (extIdx ι J) W' W' hW'min.1.1 hϖW').1
  rw [specialRelDeg, dif_pos hp]
  refine inertiaDeg_eq_relDeg (IsLocalRing.residue O) IsLocalRing.residue_surjective P W
    (le_sup_left.trans hWmin.1.2) u W' (le_sup_left.trans hW'min.1.2) hW'W (specialIdeal W')
    (fun f => ?_) h 𝔫 h𝔫 hl
  rw [← Ideal.mem_comap, specialIdeal, Ideal.comap_map_of_surjective' _
    (MvPolynomial.map_surjective _ IsLocalRing.residue_surjective), ker_map_residue_eq_span hϖ,
    sup_eq_left.mpr (by rwa [Ideal.span_le, Set.singleton_subset_iff])]

end PositivityTheory.Xgn.A_s_blowupfibre

theorem PositivityTheory.Xgn.t_s_blowupfibre : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpFibreSemilocal.Statement.{0} :=
  PositivityTheory.Xgn.A_s_blowupfibre.of_deg PositivityTheory.Xgn.A_s_blowupfibre.hdeg
