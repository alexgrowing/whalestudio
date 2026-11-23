import Mathlib
import Formalism.FormalDegreeBessel.FinalG
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentLeviRadicalCoordsHomeomorphStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

noncomputable section
namespace GlobalTheory.Amp.NHaar

def lmat {r : ℕ} (x0 : UT r → ℂ) : Matrix (UT r) (UT r) ℂ := fun p q =>
  if p.1.2 = q.1.2 then upper x0 p.1.1 q.1.1 else 0

theorem det_lmat {r : ℕ} (x0 : UT r → ℂ) : (lmat x0).det = 1 := by
  have h : (lmat x0).BlockTriangular (fun p : UT r => p.1.1) := by
    intro p q hpq
    have hpq' : q.1.1 < p.1.1 := hpq
    simp only [lmat, upper]
    rw [dif_neg (not_lt.2 hpq'.le), if_neg hpq'.ne']
    simp
  rw [h.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : (lmat x0).toSquareBlock (fun p : UT r => p.1.1) a = 1 := by
    ext p q
    have hp : p.1.1.1 = a := p.2
    have hq : q.1.1.1 = a := q.2
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply, lmat, upper, hp, hq, lt_irrefl, dif_neg, not_false_eq_true, if_true,
      Matrix.one_apply]
    congr 1
    apply propext
    constructor
    · intro h
      apply Subtype.ext; apply Subtype.ext; apply Prod.ext
      · rw [hp, hq]
      · exact h
    · intro h; rw [h]
  rw [this, Matrix.det_one]

theorem upper_mul {r : ℕ} (x0 x : UT r → ℂ) : upper x0 * upper x = upper (x0 + lmat x0 *ᵥ x) := by
  ext a b
  rw [Matrix.mul_apply]
  have key : ∀ c : Fin r, upper x0 a c * upper x c b =
      (if c = b then upper x0 a b else 0) + ∑ q : UT r, if q.1.1 = c then (if b = q.1.2 then upper x0 a q.1.1 else 0) * x q else 0 := by
    intro c
    by_cases h : c < b
    · rw [Finset.sum_eq_single ⟨(c, b), h⟩]
      · simp [h.ne, show upper x c b = x ⟨(c, b), h⟩ from dif_pos h]
      · intro q _ hq
        by_cases h1 : q.1.1 = c
        · by_cases h2 : b = q.1.2
          · exact absurd (Subtype.ext (Prod.ext h1 h2.symm)) hq
          · simp [h2]
        · simp [h1]
      · simp
    · rw [Finset.sum_eq_zero]
      · rw [show upper x c b = if c = b then 1 else 0 from dif_neg h]
        split_ifs with h1
        · simp [h1]
        · simp
      · intro q _
        by_cases h1 : q.1.1 = c
        · by_cases h2 : b = q.1.2
          · exact absurd (by rw [← h1, h2]; exact q.2) h
          · simp [h2]
        · simp [h1]
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases h : a < b
  · rw [show upper (x0 + lmat x0 *ᵥ x) a b = (x0 + lmat x0 *ᵥ x) ⟨(a, b), h⟩ from dif_pos h,
      show upper x0 a b = x0 ⟨(a, b), h⟩ from dif_pos h]
    rfl
  · rw [show upper (x0 + lmat x0 *ᵥ x) a b = if a = b then 1 else 0 from dif_neg h,
      show upper x0 a b = if a = b then 1 else 0 from dif_neg h, Finset.sum_eq_zero, add_zero]
    intro q _
    by_cases h2 : b = q.1.2
    · have h3 : q.1.1 < a := lt_of_lt_of_le (h2 ▸ q.2) (not_lt.1 h)
      simp [upper, not_lt.2 h3.le, h3.ne']
    · simp [h2]

theorem mp_upper {r : ℕ} (x0 : UT r → ℂ) :
    MeasurePreserving (fun x : UT r → ℂ => x0 + lmat x0 *ᵥ x) volume volume := by
  have hd : LinearMap.det ((Matrix.toLin' (lmat x0)).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', det_lmat, map_one]
  have h1 : MeasurePreserving ((Matrix.toLin' (lmat x0)).restrictScalars ℝ) volume volume := by
    refine ⟨(LinearMap.continuous_of_finiteDimensional _).measurable, ?_⟩
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hd]; exact one_ne_zero), hd]
    simp
  exact (measurePreserving_add_left volume x0).comp h1

theorem skewM_add {r : ℕ} (s s' : UT r → ℂ) (t t' : Fin r → ℝ) :
    skewM (s + s') (t + t') = skewM s t + skewM s' t' := by
  ext a b
  simp only [skewM, Matrix.add_apply, Pi.add_apply]
  split_ifs
  · rfl
  · simp; ring
  · push_cast; ring

theorem upper_zero {r : ℕ} : upper (0 : UT r → ℂ) = 1 := by
  ext a b
  simp only [upper, Matrix.one_apply]
  split_ifs with h1 h2
  · exact absurd h2 h1.ne
  · rfl
  · rfl
  · rfl

theorem star_herm (k : ℕ) (v w : Fin (k + 1) → ℂ) : star (herm (Hb k) v w) = herm (Hb k) w v := by
  simp only [herm, Hb, dotProduct, Matrix.mulVec_diagonal, star_sum, star_mul', Pi.star_apply, star_star]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp <;> ring

instance borelST (r : ℕ) : BorelSpace ((UT r → ℂ) × (Fin r → ℝ)) := inferInstance
instance borelPPar (k r : ℕ) : BorelSpace (PPar k r) := Prod.borelSpace
instance secondPPar (k r : ℕ) : SecondCountableTopology (PPar k r) := inferInstance
instance borelAll (k r : ℕ) : BorelSpace ((UT r → ℂ) × PPar k r) := Prod.borelSpace
instance sigmaST (r : ℕ) : SigmaFinite (volume : Measure ((UT r → ℂ) × (Fin r → ℝ))) := inferInstance
instance sigmaPPar (k r : ℕ) : SigmaFinite (volume : Measure (PPar k r)) := Measure.prod.instSigmaFinite
instance sigmaAll (k r : ℕ) : SigmaFinite (volume : Measure ((UT r → ℂ) × PPar k r)) := Measure.prod.instSigmaFinite

theorem volume_ne_zero (k r : ℕ) : (volume : Measure ((UT r → ℂ) × PPar k r)) ≠ 0 := by
  rw [← Measure.measure_univ_ne_zero, Measure.volume_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod,
    Measure.volume_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod,
    Measure.volume_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod]
  have h1 : (volume : Measure (Fin (k + 1) → ℂ)).IsOpenPosMeasure := inferInstance
  have : (volume : Measure (Fin r → Fin (k + 1) → ℂ)).IsOpenPosMeasure :=
    Measure.pi.isOpenPosMeasure (μ := fun _ : Fin r => (volume : Measure (Fin (k + 1) → ℂ)))
  refine mul_ne_zero ?_ (mul_ne_zero ?_ (mul_ne_zero ?_ ?_)) <;>
    exact (isOpen_univ.measure_pos _ Set.univ_nonempty).ne'

abbrev coord (k r : ℕ) (q : (UT r → ℂ) × PPar k r) : Mat k r := uEmb k r (upper q.1) * pOf k r q.2

theorem coord_zero (k r : ℕ) (q : PPar k r) : coord k r (0, q) = pOf k r q := by
  simp only [coord, upper_zero, (GlobalTheory.Amp.UEmb.uEmb_hom k r).2.1, one_mul]

theorem pOf_mul (k r : ℕ) (q0 : PPar k r) (B : Fin r → Fin (k + 1) → ℂ) :
    ∃ v : (UT r → ℂ) × (Fin r → ℝ), ∀ st, pOf k r q0 * pOf k r (B, st) = pOf k r (q0.1 + B, v + st) := by
  obtain ⟨-, hsk, hex, hmul, -⟩ := GlobalTheory.Amp.Rad.radical k r
  obtain ⟨v, hv, -⟩ := hex (skewM q0.2.1 q0.2.2 +
      Matrix.of fun a b => (herm (Hb k) (q0.1 b) (B a) - herm (Hb k) (B b) (q0.1 a)) / 2) (by
    rw [Matrix.conjTranspose_add, hsk, neg_add]
    congr 1
    ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.neg_apply, star_div₀, star_sub, star_herm]
    simp
    ring)
  refine ⟨v, fun st => ?_⟩
  simp only [pOf, hmul, Prod.fst_add, Prod.snd_add, skewM_add, ← hv]
  congr 1
  abel

theorem mp_rad (k r : ℕ) (q0 : PPar k r) :
    ∃ g : PPar k r → PPar k r, MeasurePreserving g volume volume ∧ ∀ q, pOf k r q0 * pOf k r q = pOf k r (g q) := by
  obtain ⟨-, hΦ, c, hc, hcΦ⟩ := GlobalTheory.T.unipotent_levi_radical_coords_homeomorph k r
  choose v hv using pOf_mul k r q0
  have hvm : Continuous v := by
    have : v = fun B => (c (pOf k r q0 * coord k r (0, (B, 0)))).2.2 := by
      funext B
      rw [coord_zero, hv, ← coord_zero, hcΦ, add_zero]
    rw [this]
    have h2 : Continuous fun B : Fin r → Fin (k + 1) → ℂ => coord k r (0, (B, 0)) :=
      hΦ.comp (by fun_prop)
    exact (hc.comp (continuous_const.matrix_mul h2)).snd.snd
  refine ⟨fun q => (q0.1 + q.1, v q.1 + q.2), ?_, fun q => hv q.1 q.2⟩
  have hI : (volume : Measure ((UT r → ℂ) × (Fin r → ℝ))).IsAddLeftInvariant :=
    Measure.prod.instIsAddLeftInvariant
  exact (measurePreserving_add_left volume q0.1).skew_product (g := fun B st => v B + st)
    (Continuous.measurable (by fun_prop))
    (Filter.Eventually.of_forall fun B => (measurePreserving_add_left volume (v B)).map_eq)

theorem conj_rad (k r : ℕ) (q0 : PPar k r) (x : UT r → ℂ) :
    ∃ q1 : PPar k r, pOf k r q0 * uEmb k r (upper x) = uEmb k r (upper x) * pOf k r q1 := by
  obtain ⟨hbij, -, -⟩ := GlobalTheory.T.unipotent_levi_radical_coords_homeomorph k r
  obtain ⟨hmul, -, hact, hdet⟩ := GlobalTheory.Amp.UEmb.uEmb_hom k r
  obtain ⟨hp, hsk, -⟩ := GlobalTheory.Amp.Rad.radical k r
  obtain ⟨-, hNm, hNi⟩ := Formalism.QuantumDeterminants.nSubgroup k r
  have hu : IsUnit (upper x).det := by rw [(hdet x).1]; exact isUnit_one
  have hui : IsUnit (upper x)⁻¹.det := Matrix.isUnit_nonsing_inv_det _ hu
  have hp0 : pOf k r q0 ∈ Nset k r := ((hp _ _).2.2.2 (hsk _ _)).1
  have hinv : uEmb k r (upper x) * (uEmb k r (upper x))⁻¹ = 1 := by
    rw [(hact _ hu).2.1, ← hmul _ _ hu hui, Matrix.mul_nonsing_inv _ hu, (GlobalTheory.Amp.UEmb.uEmb_hom k r).2.1]
  have hinv' : (uEmb k r (upper x))⁻¹ * uEmb k r (upper x) = 1 := mul_eq_one_comm.1 hinv
  obtain ⟨⟨x1, q1⟩, -, h1⟩ := hbij.surjOn
    (hNm _ (hNi _ (hdet x).2) _ (hNm _ hp0 _ (hdet x).2))
  have h1' : uEmb k r (upper x1) * pOf k r q1 =
    (uEmb k r (upper x))⁻¹ * (pOf k r q0 * uEmb k r (upper x)) := h1
  have hu1 : IsUnit (upper x1).det := by rw [(hdet x1).1]; exact isUnit_one
  have hfix : ∀ (q : PPar k r) (b : Fin r), pOf k r q *ᵥ bvec (eI k r b) = bvec (eI k r b) :=
    fun q b => (hp _ _).1 b
  have hx1 : x1 = 0 := by
    funext p
    have h2 := congrArg (fun g => g *ᵥ bvec (eI k r p.1.2)) h1'
    have h3 : pOf k r q0 *ᵥ (uEmb k r (upper x) *ᵥ bvec (eI k r p.1.2)) =
        uEmb k r (upper x) *ᵥ bvec (eI k r p.1.2) := by
      rw [(hact _ hu).2.2.1, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, hfix]
    simp only [← Matrix.mulVec_mulVec, hfix, h3] at h2
    rw [Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec] at h2
    have h4 := congrFun h2 (eI k r p.1.1)
    have hne : eI k r p.1.1 ≠ eI k r p.1.2 := fun h => by
      have := congrArg Fin.val h
      exact p.2.ne (Fin.ext this)
    rw [bvec, Matrix.mulVec_single_one, Pi.single_eq_of_ne hne] at h4
    have h5 : uEmb k r (upper x1) (eI k r p.1.1) (eI k r p.1.2) = x1 p := by
      have : uEmb k r (upper x1) (eI k r p.1.1) (eI k r p.1.2) = upper x1 p.1.1 p.1.2 :=
        dif_pos (⟨p.1.1.2, p.1.2.2⟩ : (eI k r p.1.1).val < r ∧ (eI k r p.1.2).val < r)
      rw [this]; exact dif_pos p.2
    rw [← h5]; exact h4
  refine ⟨q1, ?_⟩
  rw [hx1, upper_zero, (GlobalTheory.Amp.UEmb.uEmb_hom k r).2.1, one_mul] at h1'
  rw [h1', ← Matrix.mul_assoc, hinv, one_mul]

theorem mp_radMul (k r : ℕ) (q0 : PPar k r) :
    ∃ T : (UT r → ℂ) × PPar k r → (UT r → ℂ) × PPar k r, MeasurePreserving T volume volume ∧
      ∀ q, pOf k r q0 * coord k r q = coord k r (T q) := by
  obtain ⟨-, hΦ, c, hc, hcΦ⟩ := GlobalTheory.T.unipotent_levi_radical_coords_homeomorph k r
  choose q1 hq1 using conj_rad k r q0
  choose g hg hg' using mp_rad k r
  have key : ∀ q : (UT r → ℂ) × PPar k r, pOf k r q0 * coord k r q = coord k r (q.1, g (q1 q.1) q.2) := by
    intro q
    simp only [coord]
    rw [← Matrix.mul_assoc, hq1, Matrix.mul_assoc, hg']
  refine ⟨fun q => (q.1, g (q1 q.1) q.2), ?_, key⟩
  have hm : Measurable (Function.uncurry fun x q => g (q1 x) q) := by
    have : (Function.uncurry fun x q => g (q1 x) q) = fun q => (c (pOf k r q0 * coord k r q)).2 := by
      funext q
      rw [key, hcΦ]; rfl
    rw [this]
    exact (hc.comp (continuous_const.matrix_mul hΦ)).snd.measurable
  exact (MeasurePreserving.id volume).skew_product hm
    (Filter.Eventually.of_forall fun x => (hg (q1 x)).map_eq)

theorem mp_mul (k r : ℕ) (q0 : (UT r → ℂ) × PPar k r) :
    ∃ T : (UT r → ℂ) × PPar k r → (UT r → ℂ) × PPar k r, MeasurePreserving T volume volume ∧
      ∀ q, coord k r q0 * coord k r q = coord k r (T q) := by
  obtain ⟨hmul, -, -, hdet⟩ := GlobalTheory.Amp.UEmb.uEmb_hom k r
  have hu : ∀ x : UT r → ℂ, IsUnit (upper x).det := fun x => by rw [(hdet x).1]; exact isUnit_one
  obtain ⟨T, hT, hT'⟩ := mp_radMul k r q0.2
  refine ⟨Prod.map (fun x => q0.1 + lmat q0.1 *ᵥ x) id ∘ T,
    ((mp_upper q0.1).prod (MeasurePreserving.id volume)).comp hT, fun q => ?_⟩
  rw [coord, Matrix.mul_assoc, hT']
  simp only [coord]
  rw [← Matrix.mul_assoc, ← hmul _ _ (hu _) (hu _), upper_mul]
  rfl

theorem isHaarOn_lebN : ∀ k r : ℕ, IsHaarOn (Nset k r) (lebN k r) := by
  intro k r
  obtain ⟨hbij, hΦ, c, hc, hcΦ⟩ := GlobalTheory.T.unipotent_levi_radical_coords_homeomorph k r
  let Φ : (UT r → ℂ) × PPar k r → Mt k r := fun q => Matrix.of.symm (coord k r q)
  let c' : Mt k r → (UT r → ℂ) × PPar k r := fun x => c (Matrix.of x)
  have hΦ' : Continuous Φ := hΦ
  have hc' : Continuous c' := hc
  have hcΦ' : c' ∘ Φ = id := funext hcΦ
  have hleb : lebN k r = Measure.map Φ volume := rfl
  have hmap : (lebN k r).map c' = volume := by
    rw [hleb, Measure.map_map hc'.measurable hΦ'.measurable, hcΦ', Measure.map_id]
  refine ⟨SigmaFinite.of_map _ hc'.measurable.aemeasurable (by rw [hmap]; infer_instance), ?_, ?_, ?_⟩
  · intro h
    rw [h, Measure.map_zero] at hmap
    exact volume_ne_zero k r hmap.symm
  · have hset : {x : Mt k r | Matrix.of x ∉ Nset k r} = {x | Φ (c' x) = x}ᶜ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
      refine not_congr ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨q, -, hq⟩ := hbij.surjOn h
        have hq' : x = Φ q := hq.symm
        rw [hq', show c' (Φ q) = q from hcΦ q]
      · rw [← h]; exact hbij.mapsTo (Set.mem_univ _)
    have hcl : IsClosed {x | Φ (c' x) = x} := isClosed_eq (hΦ'.comp hc') continuous_id
    rw [hset, hleb, Measure.map_apply hΦ'.measurable hcl.measurableSet.compl]
    convert measure_empty (μ := (volume : Measure ((UT r → ℂ) × PPar k r)))
    ext q
    simp [show c' (Φ q) = q from hcΦ q]
  · intro s hs
    obtain ⟨q0, -, rfl⟩ := hbij.surjOn hs
    obtain ⟨T, hT, hT'⟩ := mp_mul k r q0
    have hl : Continuous (lmulM (coord k r q0) : Mt k r → Mt k r) :=
      continuous_const.matrix_mul (continuous_id (X := Mat k r))
    have : lmulM (coord k r q0) ∘ Φ = Φ ∘ T := funext hT'
    show Measure.map (lmulM (coord k r q0)) _ = _
    rw [hleb, Measure.map_map hl.measurable hΦ'.measurable, this, ← Measure.map_map hΦ'.measurable hT.measurable,
      hT.map_eq]

end GlobalTheory.Amp.NHaar
