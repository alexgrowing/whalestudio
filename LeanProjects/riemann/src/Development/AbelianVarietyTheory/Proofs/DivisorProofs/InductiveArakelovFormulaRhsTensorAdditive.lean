import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace GlobalTheory.MixHt

variable {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}

theorem divOfRatSec_congr {B : LB Y} (hB : B.IsLB) {t t' : B.ι → Y.functionFieldˣ} (ht : IsRatSec B t)
    (ht' : IsRatSec B t') (e : ∀ c, genericPoint Y ∈ B.U c → t c = t' c) :
    divOfRatSec hB ht = divOfRatSec hB ht' :=
  CartierDiv.ext_of_isEqn fun z => by
    obtain ⟨c, hc⟩ := exists_chart hB z
    refine ⟨t c, (presents_divOfRatSec hB ht).isEqn c z hc, ?_⟩
    rw [e c (gen_mem hc)]
    exact (presents_divOfRatSec hB ht').isEqn c z hc

theorem logNorm_congr {σ : k →+* ℂ} {B : LB Y} (φ : Weight q σ B) {t t' : B.ι → Y.functionFieldˣ}
    (e : ∀ c, genericPoint Y ∈ B.U c → t c = t' c) (y : CxPts q σ) : logNorm φ t y = logNorm φ t' y := by
  rw [logNorm, logNorm, e _ (gen_mem (mem_ptsIn.1 (mem_pick φ.isLB y)))]

theorem logNorm_tens_mul {σ : k →+* ℂ} (M A : HermLB q) {r : M.B.ι → Y.functionFieldˣ}
    {u : A.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) (hu : IsRatSec A.B u) {y : CxPts q σ}
    (hyr : y ∈ offSupp q σ (M.div hr)) (hyu : y ∈ offSupp q σ (A.div hu)) :
    logNorm ((M.tens A).φ σ) (fun c : M.B.ι × A.B.ι => r c.1 * u c.2) y =
      logNorm (M.φ σ) r y + logNorm (A.φ σ) u y := by
  obtain ⟨h₁, h₂⟩ := mem_ptsIn_inf.1 (mem_pick ((M.tens A).φ σ).isLB y)
  have hu₁ := hr.unitAt M.isLB hyr h₁
  have hu₂ := hu.unitAt A.isLB hyu h₂
  rw [logNorm_eq (M.φ σ) hr hyr h₁, logNorm_eq (A.φ σ) hu hyu h₂]
  change Real.log ‖ratVal ((r (pick ((M.tens A).φ σ).isLB y).1 * u (pick ((M.tens A).φ σ).isLB y).2 :
      Y.functionFieldˣ) : Y.functionField) y‖ - ((M.φ σ).φ (pick ((M.tens A).φ σ).isLB y).1 y +
      (A.φ σ).φ (pick ((M.tens A).φ σ).isLB y).2 y) / 2 = _
  rw [Units.val_mul, ratVal_mul hu₁.regAt hu₂.regAt, norm_mul,
    Real.log_mul (norm_ne_zero_iff.2 (ratVal_ne_zero hu₁)) (norm_ne_zero_iff.2 (ratVal_ne_zero hu₂))]
  ring

theorem chernInt_eq_of_null {D : ℕ} (hY : IsArithVar q D) {σ : k →+* ℂ} {B : LB Y} (φ : Weight q σ B)
    {S S' : Set (CxPts q σ)} (hS : S ⊆ S') (Z : Set Y) (hZ : IsClosed Z) (hg : genericPoint Y ∉ Z)
    (hd : S' \ S ⊆ {y | under y ∈ Z}) (f : CxPts q σ → ℝ) : φ.chernInt D S' f = φ.chernInt D S f := by
  have h (ε : ℤˣ) : S' =ᵐ[φ.chernPart D ε] S := ae_eq_set.2
    ⟨measure_mono_null hd (ChernNull.chernPart_over_closed hY Z hZ hg σ φ ε), by
      rw [Set.diff_eq_empty.2 hS]; exact measure_empty⟩
  rw [Weight.chernInt, Weight.chernInt, setIntegral_congr_set (h 1), setIntegral_congr_set (h (-1))]

theorem chernInt_tens {D : ℕ} (hY : IsArithVar q D) (σ : k →+* ℂ) {B : LB Y} (φ : Weight q σ B)
    (M A : HermLB q) {r : M.B.ι → Y.functionFieldˣ} {u : A.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r)
    (hu : IsRatSec A.B u) {t : (M.tens A).B.ι → Y.functionFieldˣ} (ht : IsRatSec (M.tens A).B t)
    (htu : ∀ c : M.B.ι × A.B.ι, genericPoint Y ∈ (M.tens A).B.U c → t c = r c.1 * u c.2)
    (h₁ : φ.ChernIntegrableOn D (offSupp q σ (M.div hr)) (logNorm (M.φ σ) r))
    (h₂ : φ.ChernIntegrableOn D (offSupp q σ (A.div hu)) (logNorm (A.φ σ) u)) :
    φ.chernInt D (offSupp q σ ((M.tens A).div ht)) (logNorm ((M.tens A).φ σ) t) =
      φ.chernInt D (offSupp q σ (M.div hr)) (logNorm (M.φ σ) r) +
        φ.chernInt D (offSupp q σ (A.div hu)) (logNorm (A.φ σ) u) := by
  let S := offSupp q σ (M.div hr) ∩ offSupp q σ (A.div hu) ∩ offSupp q σ ((M.tens A).div ht)
  let Z : Set Y := ((M.div hr).supp : Set Y) ∪ (A.div hu).supp ∪ ((M.tens A).div ht).supp
  have hZ : IsClosed Z :=
    ((M.div hr).supp.isClosed.union (A.div hu).supp.isClosed).union ((M.tens A).div ht).supp.isClosed
  have hg : genericPoint Y ∉ Z := by
    simp only [Z, Set.mem_union, SetLike.mem_coe, not_or]
    exact ⟨⟨CartierDiv.genericPoint_notMem_supp _, CartierDiv.genericPoint_notMem_supp _⟩,
      CartierDiv.genericPoint_notMem_supp _⟩
  have hd (T : Set (CxPts q σ)) : T \ S ⊆ {y | under y ∈ Z} := fun y hy => by
    by_contra hz
    simp only [Set.mem_setOf_eq, Z, Set.mem_union, SetLike.mem_coe, not_or] at hz
    exact hy.2 ⟨⟨mem_offSupp.2 hz.1.1, mem_offSupp.2 hz.1.2⟩, mem_offSupp.2 hz.2⟩
  have hSm : MeasurableSet S :=
    (((isOpen_offSupp _).inter (isOpen_offSupp _)).inter (isOpen_offSupp _)).measurableSet
  rw [chernInt_eq_of_null hY φ (fun _ h => h.2) Z hZ hg (hd _),
    chernInt_eq_of_null hY φ (fun _ h => h.1.1) Z hZ hg (hd _) (logNorm (M.φ σ) r),
    chernInt_eq_of_null hY φ (fun _ h => h.1.2) Z hZ hg (hd _) (logNorm (A.φ σ) u),
    Weight.chernInt_congr hSm (g := fun y => logNorm (M.φ σ) r y + logNorm (A.φ σ) u y) ?_]
  · exact Weight.chernInt_add ⟨h₁.1.mono_set fun _ h => h.1.1, h₁.2.mono_set fun _ h => h.1.1⟩
      ⟨h₂.1.mono_set fun _ h => h.1.2, h₂.2.mono_set fun _ h => h.1.2⟩
  · intro y hy
    rw [logNorm_congr _ htu y]
    exact logNorm_tens_mul M A hr hu hy.1.1 hy.1.2

theorem archInt_tens (hAI : ArchInteg) {e : ℕ} (hY : IsArithVar q e) (N M A : HermLB q)
    {r : M.B.ι → Y.functionFieldˣ} {u : A.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r)
    (hu : IsRatSec A.B u) {t : (M.tens A).B.ι → Y.functionFieldˣ} (ht : IsRatSec (M.tens A).B t)
    (htu : ∀ c : M.B.ι × A.B.ι, genericPoint Y ∈ (M.tens A).B.U c → t c = r c.1 * u c.2) :
    N.archInt (M.tens A) e ht = N.archInt M e hr + N.archInt A e hu := by
  have := hY.finite_emb
  unfold HermLB.archInt
  rw [← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finsum_congr fun σ => chernInt_tens hY σ (N.φ σ) M A hr hu ht htu
    (hAI k Y q e hY M N r hr σ) (hAI k Y q e hY A N u hu σ)

theorem archInt_of_isEmpty (hE : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) (N M : HermLB q)
    {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) (e : ℕ) : N.archInt M e hr = 0 := by
  unfold HermLB.archInt
  refine (finsum_congr fun σ => ?_).trans finsum_zero
  have := hE σ
  rw [Weight.chernInt, Set.eq_empty_of_isEmpty (offSupp q σ (M.div hr))]
  simp only [Measure.restrict_empty, integral_zero_measure, sub_zero]

theorem isArithVar_or_isEmpty (hq : IsAmb q) {e : ℕ} (he : topologicalKrullDim Y = (e + 1 : ℕ)) :
    IsArithVar q e ∨ ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ) := by
  obtain ⟨ℓ, _⟩ := CharP.exists Γ(Y, ⊤)
  rcases CharP.char_is_prime_or_zero Γ(Y, ⊤) ℓ with hℓ | rfl
  · refine .inr fun σ => ⟨fun y => ?_⟩
    let f : Γ(Y, ⊤) →+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp y.1.appTop.hom
    have h0 : (ℓ : ℂ) = 0 := by rw [← map_natCast f, CharP.cast_eq_zero, map_zero]
    exact hℓ.ne_zero (Nat.cast_eq_zero.1 h0)
  · have := CharP.charP_to_charZero Γ(Y, ⊤)
    exact .inl ⟨hq.1, hq.2, ‹_›, hq.3, (flat_int_iff_charZero _).2 this, he⟩

theorem pol_add {ι : Type} [Fintype ι] (a b : (ι → ℤ) → ℝ) :
    FibreProj.pol (fun n => a n + b n) = FibreProj.pol a + FibreProj.pol b := by
  simp only [FibreProj.pol, mul_add, Finset.sum_add_distrib]

theorem finsum_mult_add [IsLocallyNoetherian Y] [CompactSpace Y] (D E : CartierDiv Y) (h : Y → ℝ) :
    ∑ᶠ z, ((D + E).mult z : ℝ) * h z = ∑ᶠ z, (D.mult z : ℝ) * h z + ∑ᶠ z, (E.mult z : ℝ) * h z := by
  have hfin (D : CartierDiv Y) : (Function.support fun z => (D.mult z : ℝ) * h z).Finite :=
    D.finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
  simp only [CartierDiv.mult_add, Int.cast_add, add_mul]
  exact finsum_add_distrib (hfin D) (hfin E)

theorem recVal_tens : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → ∀ (h : Y → ℝ) (L : Fin e → HermLB q) (M A : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r) (u : A.B.ι → Y.functionFieldˣ) (hu : IsRatSec A.B u) (t : (M.tens A).B.ι → Y.functionFieldˣ) (ht : IsRatSec (M.tens A).B t), (∀ (i : M.B.ι) (j : A.B.ι), genericPoint Y ∈ M.B.U i → genericPoint Y ∈ A.B.U j → t (i, j) = r i * u j) → recVal h L (M.tens A) ht = recVal h L M hr + recVal h L A hu := by
  intro hAI k _ Y _ _ q hq e he h L M A r hr u hu t ht htu
  have := hq.isNoetherian
  have htu' : ∀ c : M.B.ι × A.B.ι, genericPoint Y ∈ (M.tens A).B.U c → t c = r c.1 * u c.2 :=
    fun c hc => htu c.1 c.2 hc.1 hc.2
  have hdiv : (M.tens A).div ht = M.div hr + A.div hu :=
    (divOfRatSec_congr _ ht (PtHtComb.isRatSec_tens hr hu) htu').trans (PtHtComb.div_tens M A hr hu)
  have hmix : mixArch L (M.tens A) ht = mixArch L M hr + mixArch L A hu := by
    rcases isArithVar_or_isEmpty hq he with hY | hE
    · unfold mixArch
      rw [← add_div, ← pol_add]
      congr 2
      funext n
      exact archInt_tens hAI hY (comb L n) M A hr hu ht htu'
    · have h0 (N' : HermLB q) {r' : N'.B.ι → Y.functionFieldˣ} (hr' : IsRatSec N'.B r') :
          mixArch L N' hr' = 0 := by
        simp [mixArch, archInt_of_isEmpty hE, FibreProj.pol]
      rw [h0, h0, h0, add_zero]
  unfold recVal
  rw [hdiv, finsum_mult_add, hmix]
  ring

end GlobalTheory.MixHt
