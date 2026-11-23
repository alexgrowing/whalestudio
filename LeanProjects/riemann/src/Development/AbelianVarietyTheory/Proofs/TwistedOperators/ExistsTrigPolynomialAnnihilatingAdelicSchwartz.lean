import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import GroundTheory.GlobalFields.Adele.Compact
import GroundTheory.GlobalFields.TateThesis.AdelicChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntLevelSchwartzBruhatFiniteAdelicStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardCharSeparatesIntegralFiniteAdelesStatement

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

noncomputable section

namespace GlobalTheory.FinTrig

theorem inv_level : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ x u : κ → FiniteAdeleRing (𝓞 F) F,
      (∀ i, ∀ v : HeightOneSpectrum (𝓞 F),
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) v ∈ v.adicCompletionIntegers F) →
      g (x + u) = g x := GlobalTheory.T.exists_int_level_schwartzBruhat_finiteAdelic

theorem sep_char : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ b : FiniteAdeleRing (𝓞 F) F, ¬ (∀ v : HeightOneSpectrum (𝓞 F), b v ∈ v.adicCompletionIntegers F) →
    ∃ s : F, ψ (((0 : InfiniteAdeleRing F), b * algebraMap F (FiniteAdeleRing (𝓞 F) F) s) : AF F) ≠ 1 ∧
      ∀ w : FiniteAdeleRing (𝓞 F) F, (∀ v : HeightOneSpectrum (𝓞 F), w v ∈ v.adicCompletionIntegers F) →
        ψ (((0 : InfiniteAdeleRing F), w * algebraMap F (FiniteAdeleRing (𝓞 F) F) s) : AF F) = 1 := GlobalTheory.T.standardChar_separates_integralFiniteAdeles

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

local notation "Ô" => GroundTheory.Global.integralFiniteAdeles (𝓞 F) F

def Lev (d : 𝓞 F) (u : κ → FiniteAdeleRing (𝓞 F) F) : Prop :=
  ∀ i, algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i ∈ Ô

theorem int_mem (r : 𝓞 F) : algebraMap F (FiniteAdeleRing (𝓞 F) F) (r : F) ∈ Ô :=
  fun v => GroundTheory.Global.coe_algebraMap_mem_adicCompletionIntegers v r

theorem lev_zero (d : 𝓞 F) : Lev d (0 : κ → FiniteAdeleRing (𝓞 F) F) := fun i => by
  simp only [Pi.zero_apply, mul_zero]; exact zero_mem _

theorem lev_add {d : 𝓞 F} {u u' : κ → FiniteAdeleRing (𝓞 F) F} (h : Lev d u) (h' : Lev d u') :
    Lev d (u + u') := fun i => by
  simp only [Pi.add_apply, mul_add]; exact add_mem (h i) (h' i)

theorem lev_of_mul {d e : 𝓞 F} (he : e ≠ 0) {u : κ → FiniteAdeleRing (𝓞 F) F} (h : Lev (d * e) u) :
    Lev d u := fun i => by
  have he' : (e : F) ≠ 0 := by exact_mod_cast he
  have e1 : algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i =
      algebraMap F _ (e : F) * (algebraMap F _ (((d * e : 𝓞 F) : F))⁻¹ * u i) := by
    rw [← mul_assoc, ← map_mul]
    congr 2
    push_cast
    rw [mul_inv, mul_left_comm, mul_inv_cancel₀ he', mul_one]
  rw [e1]
  exact mul_mem (int_mem e) (h i)

theorem isOpen_lev (d : 𝓞 F) (a : κ → FiniteAdeleRing (𝓞 F) F) :
    IsOpen {z : κ → FiniteAdeleRing (𝓞 F) F | Lev d (z - a)} := by
  have e : {z : κ → FiniteAdeleRing (𝓞 F) F | Lev d (z - a)} = ⋂ i, (fun z : κ → FiniteAdeleRing (𝓞 F) F =>
      algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * (z i - a i)) ⁻¹' (Ô : Set _) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Lev, Pi.sub_apply, SetLike.mem_coe]
  rw [e]
  exact isOpen_iInter_of_finite fun i => (GroundTheory.Global.isOpen_integralFiniteAdeles (R := 𝓞 F) (K := F)).preimage
    (continuous_const.mul ((continuous_apply i).sub continuous_const))

theorem fst_eq_zero {a : AF F} (h : evI F a = 0) : a.1 = 0 :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact h)

def Good (Φ : (κ → AF F) → ℂ) : Prop :=
  ∃ d : 𝓞 F, d ≠ 0 ∧ ∃ T : Set (κ → FiniteAdeleRing (𝓞 F) F), IsCompact T ∧
    (∀ x : κ → AF F, (fun i => (x i).2) ∉ T → Φ x = 0) ∧
    ∀ x x' : κ → AF F, (∀ i, (x i).1 = (x' i).1) → Lev d (fun i => (x i).2 - (x' i).2) → Φ x = Φ x'

theorem good_of_mem {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) : Good Φ := by
  induction h using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    obtain ⟨d, hd, hinv⟩ := inv_level g hg
    refine ⟨d, hd, tsupport g, hg.2, fun x hx => ?_, fun x x' h1 h2 => ?_⟩
    · simp only [pureA]
      rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
    · simp only [pureA]
      have e1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) =
          fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x' i).1 := funext fun i => by rw [h1 i]
      have e2 : (fun i => (x i).2) = (fun i => (x' i).2) + fun i => (x i).2 - (x' i).2 := by
        funext i; simp
      rw [e1, e2, hinv _ _ h2]
  | zero => exact ⟨1, one_ne_zero, ∅, isCompact_empty, fun x _ => rfl, fun _ _ _ _ => rfl⟩
  | add Φ Ψ _ _ hΦ hΨ =>
    obtain ⟨d, hd, T, hT, h0, hi⟩ := hΦ
    obtain ⟨d', hd', T', hT', h0', hi'⟩ := hΨ
    refine ⟨d * d', mul_ne_zero hd hd', T ∪ T', hT.union hT', fun x hx => ?_, fun x x' h1 h2 => ?_⟩
    · simp only [Set.mem_union, not_or] at hx
      simp [h0 x hx.1, h0' x hx.2]
    · have h2' : Lev (d' * d) (fun i => (x i).2 - (x' i).2) := by rw [mul_comm]; exact h2
      simp only [Pi.add_apply]
      rw [hi x x' h1 (lev_of_mul hd' h2), hi' x x' h1 (lev_of_mul hd h2')]
  | smul a Φ _ hΦ =>
    obtain ⟨d, hd, T, hT, h0, hi⟩ := hΦ
    exact ⟨d, hd, T, hT, fun x hx => by simp [h0 x hx], fun x x' h1 h2 => by simp [hi x x' h1 h2]⟩

def chi (ψ : AddChar (AF F) ℂ) (q : κ → AF F) : (κ → AF F) → ℂ := fun x => ψ (x ⬝ᵥ q)

def Q0 : Set (κ → AF F) := {q | ∀ i, evI F (q i) = 0}

def TP (ψ : AddChar (AF F) ℂ) : Submodule ℂ ((κ → AF F) → ℂ) := Submodule.span ℂ (chi ψ '' (Q0 (F := F) (κ := κ)))

theorem chi_mul (ψ : AddChar (AF F) ℂ) (q q' : κ → AF F) : chi ψ q * chi ψ q' = chi ψ (q + q') := by
  funext x
  simp only [chi, Pi.mul_apply, dotProduct_add, AddChar.map_add_eq_mul]

theorem add_mem_adelicVectorsZeroArchimedean {q q' : κ → AF F} (h : q ∈ Q0) (h' : q' ∈ Q0) : q + q' ∈ Q0 := fun i => by
  have e : evI F ((q + q') i) = evI F (q i) + evI F (q' i) :=
    map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (q i).1 (q' i).1
  rw [e, h i, h' i, add_zero]

theorem zero_mem_adelicVectorsZeroArchimedean : (0 : κ → AF F) ∈ Q0 := fun i => map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem chi_zero (ψ : AddChar (AF F) ℂ) : chi ψ (0 : κ → AF F) = 1 := by
  funext x; simp [chi]

theorem chi_mem (ψ : AddChar (AF F) ℂ) {q : κ → AF F} (hq : q ∈ Q0) : chi ψ q ∈ TP ψ :=
  Submodule.subset_span ⟨q, hq, rfl⟩

theorem one_mem_TP (ψ : AddChar (AF F) ℂ) : (1 : (κ → AF F) → ℂ) ∈ TP ψ := by
  rw [← chi_zero ψ]; exact chi_mem ψ zero_mem_adelicVectorsZeroArchimedean

theorem mul_mem_TP (ψ : AddChar (AF F) ℂ) {f g : (κ → AF F) → ℂ} (hf : f ∈ TP ψ) (hg : g ∈ TP ψ) :
    f * g ∈ TP ψ := by
  have hle : TP ψ * TP ψ ≤ TP (κ := κ) ψ := by
    rw [TP, Submodule.span_mul_span]
    apply Submodule.span_mono
    rintro _ ⟨a, ⟨q, hq, rfl⟩, b, ⟨q', hq', rfl⟩, rfl⟩
    exact ⟨q + q', add_mem_adelicVectorsZeroArchimedean hq hq', (chi_mul ψ q q').symm⟩
  exact hle (Submodule.mul_mem_mul hf hg)

theorem prod_mem_TP (ψ : AddChar (AF F) ℂ) {ι : Type} (t : Finset ι) (f : ι → (κ → AF F) → ℂ)
    (h : ∀ a ∈ t, f a ∈ TP ψ) : (∏ a ∈ t, f a) ∈ TP ψ :=
  Finset.prod_induction f (· ∈ TP ψ) (fun _ _ => mul_mem_TP ψ) (one_mem_TP ψ) h

theorem exists_of_mem_TP (ψ : AddChar (AF F) ℂ) {P : (κ → AF F) → ℂ} (h : P ∈ TP ψ) :
    ∃ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ q ∈ s, ∀ i, evI F (q i) = 0) ∧
      ∀ x, P x = ∑ q ∈ s, c q * ψ (x ⬝ᵥ q) := by
  rw [TP, Finsupp.mem_span_image_iff_linearCombination] at h
  obtain ⟨l, hl, rfl⟩ := h
  refine ⟨l.support, l, fun q hq => (Finsupp.mem_supported ℂ l).1 hl hq, fun x => ?_⟩
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply]
  rfl

def vecFin (u : κ → FiniteAdeleRing (𝓞 F) F) : κ → AF F := fun i => ((0 : InfiniteAdeleRing F), u i)

theorem vecFin_add (u u' : κ → FiniteAdeleRing (𝓞 F) F) : vecFin (u + u') = vecFin u + vecFin u' := by
  funext i
  exact Prod.ext (show (0 : InfiniteAdeleRing F) = 0 + 0 by rw [add_zero]) rfl

theorem dot_eq_vecFin {q : κ → AF F} (hq : q ∈ Q0) (x : κ → AF F) :
    x ⬝ᵥ q = vecFin (fun i => (x i).2) ⬝ᵥ q := by
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Prod.ext (show (x i).1 * (q i).1 = (0 : InfiniteAdeleRing F) * (q i).1 by
    rw [fst_eq_zero (hq i), mul_zero, mul_zero]) rfl

theorem exists_sep (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (d : 𝓞 F) (a : κ → FiniteAdeleRing (𝓞 F) F)
    (ha : ¬ Lev d a) : ∃ q ∈ (Q0 : Set (κ → AF F)), ψ (vecFin a ⬝ᵥ q) ≠ 1 ∧
      ∀ u, Lev d u → ψ (vecFin u ⬝ᵥ q) = 1 := by
  classical
  simp only [Lev, not_forall] at ha
  obtain ⟨i, hi⟩ := ha
  obtain ⟨s, hs1, hs2⟩ := sep_char ψ hψ _ hi
  set c : AF F := ((0 : InfiniteAdeleRing F), algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹ * s))
  have key : ∀ u : κ → FiniteAdeleRing (𝓞 F) F, vecFin u ⬝ᵥ Pi.single i c =
      ((0 : InfiniteAdeleRing F), algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) s) := by
    intro u
    rw [dotProduct_single]
    refine Prod.ext (show (0 : InfiniteAdeleRing F) * 0 = 0 from mul_zero _) ?_
    show u i * algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹ * s) = _
    rw [map_mul]; ring
  refine ⟨Pi.single i c, fun j => ?_, ?_, fun u hu => ?_⟩
  · by_cases hj : j = i
    · subst hj; rw [Pi.single_eq_same]; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    · rw [Pi.single_eq_of_ne hj]; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  · rw [key]; exact hs1
  · rw [key]; exact hs2 _ (hu i)

theorem vecFin_zero : vecFin (0 : κ → FiniteAdeleRing (𝓞 F) F) = 0 := by
  funext i; rfl

theorem loc_chars : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ Φ ∈ schA F κ, ∀ y : κ → AF F, (∀ z, At (evI F) z → Φ (y + z) = 0) →
    ∃ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ q ∈ s, ∀ i, evI F (q i) = 0) ∧
      ∑ q ∈ s, c q * ψ (y ⬝ᵥ q) = 1 ∧ ∀ x, (∑ q ∈ s, c q * ψ (x ⬝ᵥ q)) * Φ x = 0 := by
  intro F _ _ κ _ ψ hψ Φ hΦ y hy
  classical
  obtain ⟨d, hd, T, hT, h0, hinv⟩ := good_of_mem hΦ
  set yf : κ → FiniteAdeleRing (𝓞 F) F := fun i => (y i).2 with hyf
  set C := T ∩ {z | Lev d (z - yf)}ᶜ with hCdef
  have hC : IsCompact C := hT.inter_right (isOpen_lev d yf).isClosed_compl
  obtain ⟨t, htC, hcov⟩ := hC.elim_nhds_subcover (fun a => {z | Lev d (z - a)})
    (fun a _ => (isOpen_lev d a).mem_nhds (by simp only [Set.mem_setOf_eq, sub_self]; exact lev_zero d))
  have hsep : ∀ a ∈ C, ∃ q ∈ (Q0 : Set (κ → AF F)), ψ (vecFin (a - yf) ⬝ᵥ q) ≠ 1 ∧
      ∀ u, Lev d u → ψ (vecFin u ⬝ᵥ q) = 1 := fun a ha => exists_sep ψ hψ d (a - yf) ha.2
  choose! q hq0 hq1 hq2 using hsep
  set c : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := fun a => ψ (vecFin (a - yf) ⬝ᵥ q a) with hc
  set φ : (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AF F) → ℂ := fun a =>
    (1 - c a)⁻¹ • (ψ (-(y ⬝ᵥ q a)) • chi ψ (q a) - c a • 1) with hφ
  have hφx : ∀ a ∈ C, ∀ x, φ a x = (1 - c a)⁻¹ * (ψ (vecFin ((fun i => (x i).2) - yf) ⬝ᵥ q a) - c a) := by
    intro a ha x
    have e1 : ψ (-(y ⬝ᵥ q a)) * ψ (x ⬝ᵥ q a) = ψ (vecFin ((fun i => (x i).2) - yf) ⬝ᵥ q a) := by
      rw [← AddChar.map_add_eq_mul, neg_add_eq_sub, ← sub_dotProduct, dot_eq_vecFin (hq0 a ha)]
      rfl
    simp only [hφ, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, chi, Pi.one_apply, mul_one]
    rw [e1]
  have hφmem : ∀ a ∈ t, φ a ∈ TP ψ := fun a ha =>
    Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ (chi_mem ψ (hq0 a (htC a ha))))
      (Submodule.smul_mem _ _ (one_mem_TP ψ)))
  obtain ⟨s, cc, hs, hP⟩ := exists_of_mem_TP ψ (prod_mem_TP ψ t φ hφmem)
  refine ⟨s, cc, hs, ?_, fun x => ?_⟩
  · rw [← hP y, Finset.prod_apply]
    refine Finset.prod_eq_one fun a ha => ?_
    rw [hφx a (htC a ha)]
    have e0 : (fun i => (y i).2) - yf = 0 := sub_self _
    have hne : 1 - c a ≠ 0 := sub_ne_zero.mpr (Ne.symm (hq1 a (htC a ha)))
    rw [e0, vecFin_zero, zero_dotProduct, AddChar.map_zero_eq_one, inv_mul_cancel₀ hne]
  · rw [← hP x, Finset.prod_apply]
    by_cases hxT : (fun i => (x i).2) ∈ T
    · by_cases hL : Lev d ((fun i => (x i).2) - yf)
      · set z : κ → AF F := fun i => (((x i).1 - (y i).1 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F)) with hz
        have hzA : At (evI F) z := by
          intro u hu
          have h1 := fst_eq_zero hu
          funext i
          show u * z i = 0
          exact Prod.ext (show u.1 * ((x i).1 - (y i).1) = 0 by rw [h1, zero_mul])
            (show u.2 * (0 : FiniteAdeleRing (𝓞 F) F) = 0 from mul_zero _)
        have e2 : (fun i => (x i).2 - ((y + z) i).2) = (fun i => (x i).2) - yf := by
          funext i
          show (x i).2 - ((y i).2 + 0) = (x i).2 - (y i).2
          rw [add_zero]
        have e3 := hinv x (y + z) (fun i => (add_sub_cancel (y i).1 (x i).1).symm) (by rw [e2]; exact hL)
        rw [e3, hy z hzA, mul_zero]
      · have hxC : (fun i => (x i).2) ∈ C := ⟨hxT, hL⟩
        obtain ⟨a, hat, hxa⟩ := Set.mem_iUnion₂.mp (hcov hxC)
        rw [Finset.prod_eq_zero hat, zero_mul]
        rw [hφx a (htC a hat)]
        have e : (fun i => (x i).2) - yf = ((fun i => (x i).2) - a) + (a - yf) := (sub_add_sub_cancel _ _ _).symm
        rw [e, vecFin_add, add_dotProduct, AddChar.map_add_eq_mul, hq2 a (htC a hat) _ hxa, one_mul, sub_self,
          mul_zero]
    · rw [h0 x hxT, mul_zero]

end GlobalTheory.FinTrig
