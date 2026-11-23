import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSmoothProjectiveVarietyProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleModuloEffectiveAwayFromPointPullAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleBaseChangeFieldExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigLineBundleOfSmulClassEqAmpleAtAddNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneLeIntersectionNumberSubvarietyThroughPositive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNefBigOfClassEqSmulAddSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulIntersectionLeOfNefClassOnClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSectionsFiniteSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionOverFieldEqOfClosedPointImageEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageSectionProjectiveOverField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleValueAtPointNeZeroIffMemNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingsAgreeOnSubfieldNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.HSApp GlobalTheory.Cartier

namespace GlobalTheory.TwoPoint

theorem nef_pull (hN : GlobalTheory.Published.NefNumerics) {F E : Type} [Field F] [Field E] {X Y : Scheme.{0}} (pX : X ⟶ Sp F)
    (pY : Y ⟶ Sp E) (g : Y ⟶ X) (hX : IsProjOver pX) (hY : IsProjOver pY) (L : LB X)
    (hL : letI := algebraΓOfHom pX; IsNef F L) : letI := algebraΓOfHom pY; IsNef E (L.pull g) := by
  letI := algebraΓOfHom pX
  letI := algebraΓOfHom pY
  obtain ⟨hpp, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB pX).1 hX
  obtain ⟨B, hB⟩ := exists_isAmpleLB_of_isProjOver hY
  have : IsProper (strHom F X) := by rw [strHom_eq (f := pX) fun _ => rfl]; exact hpp
  exact NefFieldExt.isNef_pull hN hL hA hB g

section Descent

open GlobalTheory.Vanishing.H0 GlobalTheory.TangentOrigin GlobalTheory.Adelic
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

theorem sum_val_pull_eq_zero {F : Type} [Field F] [Algebra F ℂ] {Y : Scheme.{0}} (p : Y ⟶ Sp F) (n : ℕ)
    [SmoothOfRelativeDimension n p] (hp : IsProjOver p) (hc : GeometricallyConnected p) (hn : 1 ≤ n) {T : LB Y}
    (hT : T.IsLB) {J : Type} [Fintype J] (x : J → (Sp ℂ ⟶ pullback p (spMap (algebraMap F ℂ))))
    (hx : ∀ j, x j ≫ pullback.snd _ _ = 𝟙 _) (k : J → T.ι)
    (hk : ∀ j, ⊤ ≤ (x j ≫ pullback.fst _ _) ⁻¹ᵁ T.U (k j))
    (hk' : ∀ j, ⊤ ≤ x j ⁻¹ᵁ (T.pull (pullback.fst _ _)).U (pIdx T _ (k j))) (a : J → ℂ)
    (h : ∀ g : H0 p T ⊤, ∑ j, a j * val (x j ≫ pullback.fst _ _) (k j) le_top (hk j) g = 0)
    (g : H0 (pullback.snd p (spMap (algebraMap F ℂ))) (T.pull (pullback.fst _ _)) ⊤) :
    ∑ j, a j * val (x j) (pIdx T _ (k j)) le_top (hk' j) g = 0 := by
  let Z : Scheme.{0} := pullback p (spMap (algebraMap F ℂ))
  let π : Z ⟶ Y := pullback.fst p (spMap (algebraMap F ℂ))
  let q : Z ⟶ Sp ℂ := pullback.snd p (spMap (algebraMap F ℂ))
  let S : LinSys F := ⟨Y, p, n, T, hT, 0, Fin.elim0⟩
  letI := algebraΓOfHom q
  obtain ⟨N, b, hb⟩ : ∃ (N : ℕ) (b : Fin N → T.Sec), ∀ t : (T.pull π).Sec, ∃ u : Fin N → ℂ,
      ∑ i, algebraMap ℂ Γ(Z, ⊤) (u i) • secPull (b i) π = t :=
    SectionsFieldChange.exists_pullSecs_spanning F ℂ S ⟨inferInstance, hp, hc, hn⟩
  obtain ⟨t, rfl⟩ := (bijective_ofSec_top (p := q) (B := T.pull π)).2 g
  obtain ⟨u, hu⟩ := hb t
  have e (c : ℂ) : algebraMap ℂ Γ(Z, ⊤) c = algX q ⊤ c := by
    change q.appTop _ = _
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have ht : t = ∑ i, algX q ⊤ (u i) • secPull (b i) π := by
    rw [← hu]
    exact Finset.sum_congr rfl fun i _ => by rw [e]
  have hx' : ∀ j, x j ≫ q = spMap (RingHom.id ℂ) := fun j =>
    (hx j).trans (Spec.map_id (CommRingCat.of ℂ)).symm
  have hv : ∀ j i, val (x j) (pIdx T π (k j)) le_top (hk' j) (ofSec q ⊤ (secPull (b i) π)) =
      val (x j ≫ π) (k j) le_top (hk j) (ofSec p ⊤ (b i)) := fun j i => by
    refine (val_ofSec (p := q) (O := ⊤) (x j) _ le_top (hk' j) _).trans
      (Eq.trans ?_ (val_ofSec (p := p) (O := ⊤) (x j ≫ π) _ le_top (hk j) _).symm)
    exact congrArg (fun g => (g ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom ((b i).f (k j)))
      (Scheme.Hom.appLE_comp_appLE (x j) π (T.U (k j)) _ ⊤ ((chartPullPull T π).le (pIdx T π (k j))) (hk' j))
  have hs : ∀ j, val (x j) (pIdx T π (k j)) le_top (hk' j) (ofSec q ⊤ t) =
      ∑ i, u i * val (x j ≫ π) (k j) le_top (hk j) (ofSec p ⊤ (b i)) := fun j => by
    rw [ht, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ofSec_smul]
    exact (H0.val_smul (O := ⊤) (x j) (hx' j) _ le_top (hk' j) _ _).trans (congrArg (u i * ·) (hv j i))
  calc _ = ∑ j, ∑ i, u i * (a j * val (x j ≫ π) (k j) le_top (hk j) (ofSec p ⊤ (b i))) :=
        Finset.sum_congr rfl fun j _ => by
          rw [hs j, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by
        rw [Finset.sum_comm]
        exact Finset.sum_eq_zero fun i _ => by rw [← Finset.mul_sum, h, mul_zero]

abbrev tensPullChart {X Y : Scheme.{0}} {K B : LB Y} (π : X ⟶ Y) (hK : K.IsLB) (hB : B.IsLB) :
    ProdChart (LB.triv X) (tens (K.pull π) (B.pull π)) ((tens K B).pull π) where
  isLB₁ := LB.isLB_triv X
  isLB₂ := isLB_tens (LB.isLB_pull hK π) (LB.isLB_pull hB π)
  isLB₃ := LB.isLB_pull (isLB_tens hK hB) π
  τ := K.ι × B.ι
  a _ := PUnit.unit
  b t := (pIdx K π t.1, pIdx B π t.2)
  c t := pIdx (tens K B) π t
  cover x := by
    obtain ⟨j, hj⟩ := exists_chart hK (π x)
    obtain ⟨l, hl⟩ := exists_chart hB (π x)
    exact ⟨(j, l), trivial, ⟨mem_pIdx.2 hj, mem_pIdx.2 hl⟩, mem_pIdx.2 ⟨hj, hl⟩⟩
  rule x t t' e e' := by
    have h1 : tr (LB.triv X) x PUnit.unit PUnit.unit = 1 := map_one _
    rw [h1, one_mul, tr_tens _ _ x e.2.1 e'.2.1, tr_pull _ π x e.2.2 e'.2.2, tr_pull _ π x e.2.1.1 e'.2.1.1,
      tr_pull _ π x e.2.1.2 e'.2.1.2, tr_tens _ _ (π x) (mem_pull.1 e.2.2) (mem_pull.1 e'.2.2), map_mul]
    rfl

theorem exists_val_eq_tens_pull {k : Type} [CommRing k] {X Y : Scheme.{0}} (q : X ⟶ Sp k) {K B : LB Y} (π : X ⟶ Y)
    (hK : K.IsLB) (hB : B.IsLB) (g : H0 q (tens (K.pull π) (B.pull π)) ⊤) :
    ∃ g' : H0 q ((tens K B).pull π) ⊤, ∀ (x : Sp ℂ ⟶ X) (t : (tens K B).ι)
      (h : ⊤ ≤ x ⁻¹ᵁ (tens (K.pull π) (B.pull π)).U (pIdx K π t.1, pIdx B π t.2))
      (h' : ⊤ ≤ x ⁻¹ᵁ ((tens K B).pull π).U (pIdx (tens K B) π t)),
      val x (pIdx (tens K B) π t) le_top h' g' = val x (pIdx K π t.1, pIdx B π t.2) le_top h g := by
  let one : (LB.triv X).Sec := ⟨fun _ => 1, fun _ _ => by simp⟩
  refine ⟨(tensPullChart π hK hB).mul (ofSec q ⊤ one) g, fun x t h h' => ?_⟩
  have e := (tensPullChart π hK hB).val_mul (ofSec q ⊤ one) g t x le_top le_top h h'
  have e₁ : val x PUnit.unit le_top le_top (ofSec q ⊤ one) = 1 :=
    (val_ofSec (p := q) (O := ⊤) x _ le_top le_top one).trans (map_one _)
  exact e.trans ((congrArg (· * _) e₁).trans (one_mul _))

end Descent

def SeparatesOnSmooth : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (q : X ⟶ Sp ℂ) (D : ℕ) [SmoothOfRelativeDimension D q],
    IsProjOver q → 1 ≤ D → letI := algebraΓOfHom q
    ∀ (K : CanonLB q D) (B : LB X) (x₁ x₂ : X), IsNef ℂ B → IsBig ℂ B →
      IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → x₁ ≠ x₂ →
      (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x₁ ∈ Z ∨ x₂ ∈ Z → 1 ≤ e →
        topologicalKrullDim (Z : Set X) = e →
        ((((D + 2).choose 2 - 1 : ℕ) : ℤ)) ^ e < interNumRed ℂ Z fun _ : Fin e => B) →
      ∃ s : (tens K.bundle B).Sec,
        (x₁ ∈ nonzeroLocus s ∧ x₂ ∉ nonzeroLocus s) ∨ (x₂ ∈ nonzeroLocus s ∧ x₁ ∉ nonzeroLocus s)

theorem separate_complex (hS : SeparatesOnSmooth) (hNN : GlobalTheory.Published.NefNumerics)
    (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (q : X ⟶ Sp ℂ) (D : ℕ)
    [SmoothOfRelativeDimension D q] (hq : IsProjOver q) (hD : 1 ≤ D) :
    letI := algebraΓOfHom q
    ∀ (K : CanonLB q D) (N N' B : LB X) (hN : N.IsLB) (hN' : N'.IsLB) (hB : B.IsLB) (m : ℕ) (x₁ x₂ : X),
      IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → IsNef ℂ N → IsBig ℂ N → IsNef ℂ N' →
      (D + 2).choose 2 ≤ m →
      (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x₁ ∈ Z ∨ x₂ ∈ Z → 1 ≤ e →
        topologicalKrullDim (Z : Set X) = e → 1 ≤ interNumRed ℂ Z (fun _ : Fin e => N)) →
      cls B hB = m • cls N hN + cls N' hN' → ∃ s : (tens K.bundle B).Sec,
        (x₁ ∈ nonzeroLocus s ∧ x₂ ∉ nonzeroLocus s) ∨ (x₂ ∈ nonzeroLocus s ∧ x₁ ∉ nonzeroLocus s) := by
  letI := algebraΓOfHom q
  intro K N N' B hN hN' hB m x₁ x₂ h₁ h₂ hne hNn hNb hN'n hm hpos hBc
  have hc : 0 < (D + 2).choose 2 := Nat.choose_pos (by omega)
  have hBc' : cls B hB = m • cls N hN + 1 • cls N' hN' := by rw [hBc, one_smul]
  obtain ⟨N₀, h₀, hc₀, hn₀, hb₀⟩ :=
    GlobalTheory.nef_big_of_cls_eq_smul_add_smul hNN ℂ X q hq N N' hN hN' m 1 hNn hNb hN'n (by omega)
  refine hS X q D hq hD K B x₁ x₂ (hn₀.of_cls_eq hB (hBc'.trans hc₀.symm)) (hb₀.of_cls_eq hB (hBc'.trans hc₀.symm))
    h₁ h₂ hne fun Z e hZ hx he hd => ?_
  have h1 := hpos Z e hZ hx he hd
  have h2 := GlobalTheory.mixExp_interNumRed hNN ℂ X q hq N N' B hN hN' hB m 1 Z e hNn hN'n hBc' hd
  have h3 : (((D + 2).choose 2 - 1 : ℕ) : ℤ) ^ e < (m : ℤ) ^ e :=
    pow_lt_pow_left₀ (by exact_mod_cast (by omega : (D + 2).choose 2 - 1 < m)) (by positivity) (by omega)
  have h4 : (0 : ℤ) ≤ (m : ℤ) ^ e := by positivity
  nlinarith

theorem separate_two (hS : SeparatesOnSmooth) (hNN : GlobalTheory.Published.NefNumerics)
    (F : Type) [Field F] (σ : F →+* ℂ) (Y : Scheme.{0}) (p : Y ⟶ Sp F) (D : ℕ) [SmoothOfRelativeDimension D p]
    (hp : IsProjOver p) (hc : GeometricallyConnected p) (hD : 1 ≤ D) (K : CanonLB p D) (N N' B N₁ N₂ : LB Y)
    (hN : N.IsLB) (hN' : N'.IsLB) (hB : B.IsLB) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB) (a m : ℕ)
    (hNn : letI := algebraΓOfHom p; IsNef F N) (hN'n : letI := algebraΓOfHom p; IsNef F N')
    (hN₂n : letI := algebraΓOfHom p; IsNef F N₂) (hm : (D + 2).choose 2 ≤ m) (ha : 0 < a)
    (hdec : a • cls N hN = cls N₁ h₁ + cls N₂ h₂) (hBc : cls B hB = m • cls N hN + cls N' hN')
    (z : Fin 2 → (Sp ℂ ⟶ Y)) (hz : z 0 ≠ z 1) (hzp : ∀ j, z j ≫ p = spMap σ) (hzA : ∀ j s, AmpleAt N₁ (z j s))
    (k : Fin 2 → (tens K.bundle B).ι) (hk : ∀ j, ⊤ ≤ z j ⁻¹ᵁ (tens K.bundle B).U (k j)) (c : Fin 2 → ℂ)
    (hc0 : ∀ j, c j ≠ 0) :
    ¬ ∀ g : H0 p (tens K.bundle B) ⊤, ∑ j, c j * H0.val (z j) (k j) le_top (hk j) g = 0 := by
  intro h
  letI : Algebra F ℂ := σ.toAlgebra
  let π := pullback.fst p (spMap (algebraMap F ℂ))
  let q := pullback.snd p (spMap (algebraMap F ℂ))
  have H : IsPullback π q p (spMap (algebraMap F ℂ)) := IsPullback.of_hasPullback _ _
  obtain ⟨hXi, hXn, hsm, hq, -⟩ := BaseChangeVariety.baseChange_props F ℂ Y _ p q π D H hp hc
  haveI := hXi; haveI := hXn; haveI := hsm
  haveI : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  let zC : Fin 2 → (Sp ℂ ⟶ pullback p (spMap (algebraMap F ℂ))) := fun j =>
    H.lift (z j) (𝟙 _) (by rw [hzp j, Category.id_comp])
  have hz₁ : ∀ j, zC j ≫ π = z j := fun j => H.lift_fst _ _ _
  have hz₂ : ∀ j, zC j ≫ q = 𝟙 _ := fun j => H.lift_snd _ _ _
  let s₀ : Sp ℂ := IsLocalRing.closedPoint ℂ
  have hπx : ∀ j, π (zC j s₀) = z j s₀ := fun j => congrArg (fun g => g s₀) (hz₁ j)
  letI := algebraΓOfHom q
  have hNC := LB.isLB_pull hN π
  have hA : ∀ j, AmpleAt (N₁.pull π) (zC j s₀) := fun j =>
    AmplePull.ampleAt_pull Y _ π N₁ h₁ _ (by rw [hπx]; exact hzA j s₀)
  have hNnC : IsNef ℂ (N.pull π) := nef_pull hNN p q π hp hq N hNn
  have hN₂C : IsNef ℂ (N₂.pull π) := nef_pull hNN p q π hp hq N₂ hN₂n
  have hcl : a • cls (N.pull π) hNC = cls (N₁.pull π) (LB.isLB_pull h₁ π) + cls (N₂.pull π) (LB.isLB_pull h₂ π) := by
    rw [cls_pull hN, cls_pull h₁, cls_pull h₂, ← map_nsmul, hdec, map_add]
  have hbig : IsBig ℂ (N.pull π) :=
    isBig_of_smul_cls_eq_add_ampleAt hNN ℂ _ q hq _ _ _ hNC _ _ a (zC 0 s₀) hNnC ha hcl (hA 0) hN₂C
  have hpos := fun j => GlobalTheory.PosThrough.one_le_interNumRed hNN ℂ _ q hq _ _ _ hNC _ _ a (zC j s₀) hNnC ha hcl (hA j) hN₂C
  have hcB : cls (B.pull π) (LB.isLB_pull hB π) =
      m • cls (N.pull π) hNC + cls (N'.pull π) (LB.isLB_pull hN' π) := by
    rw [cls_pull hB, cls_pull hN, cls_pull hN', hBc, map_add, map_nsmul]
  have hpt : ∀ (W : Scheme.{0}) (y : Sp ℂ ⟶ W) (O : W.Opens), y s₀ ∈ O → ⊤ ≤ y ⁻¹ᵁ O := by
    intro W y O hs t _
    rw [Subsingleton.elim t s₀]
    exact hs
  have hkM : ∀ j, ⊤ ≤ (zC j ≫ π) ⁻¹ᵁ (tens K.bundle B).U (k j) := fun j => by rw [hz₁]; exact hk j
  have hk₁ : ∀ j, ⊤ ≤ zC j ⁻¹ᵁ (tens (K.bundle.pull π) (B.pull π)).U (pIdx _ π (k j).1, pIdx B π (k j).2) :=
    fun j => hpt _ _ _ ⟨mem_pIdx.2 (hkM j trivial).1, mem_pIdx.2 (hkM j trivial).2⟩
  have hk₂ : ∀ j, ⊤ ≤ zC j ⁻¹ᵁ ((tens K.bundle B).pull π).U (pIdx _ π (k j)) :=
    fun j => hpt _ _ _ (mem_pIdx.2 (hkM j trivial))
  have hne : zC 0 s₀ ≠ zC 1 s₀ := fun e => hz (by
    rw [← hz₁, ← hz₁ 1, GlobalTheory.section_eq_of_point_eq ℂ _ q _ _ (hz₂ 0) (hz₂ 1) e])
  obtain ⟨s, hs⟩ := separate_complex hS hNN _ q D hq hD (CanonLB.baseChange H K) (N.pull π) (N'.pull π) (B.pull π)
    hNC _ _ m (zC 0 s₀) (zC 1 s₀) (GlobalTheory.secClosed_closedPoint ℂ _ q _ hq (hz₂ 0))
    (GlobalTheory.secClosed_closedPoint ℂ _ q _ hq (hz₂ 1)) hne hNnC hbig (nef_pull hNN p q π hp hq N' hN'n) hm
    (fun Z e hZ hx he hd => hx.elim (fun hx => hpos 0 Z e hZ hx he hd) fun hx => hpos 1 Z e hZ hx he hd) hcB
  obtain ⟨g', hg'⟩ := exists_val_eq_tens_pull q π K.isLB hB (H0.ofSec q ⊤ s)
  have key := sum_val_pull_eq_zero p D hp hc hD (isLB_tens K.isLB hB) zC hz₂ k hkM hk₂ c (fun g => by
    rw [← h g]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hv : ∀ {y y' : Sp ℂ ⟶ Y} (_ : y = y') (hy : ⊤ ≤ y ⁻¹ᵁ (tens K.bundle B).U (k j))
        (hy' : ⊤ ≤ y' ⁻¹ᵁ (tens K.bundle B).U (k j)),
        H0.val y (k j) le_top hy g = H0.val y' (k j) le_top hy' g := by
      rintro y _ rfl _ _
      rfl
    exact congrArg (c j * ·) (hv (hz₁ j) (hkM j) (hk j))) g'
  rw [Fin.sum_univ_two, hg' (zC 0) (k 0) (hk₁ 0) (hk₂ 0), hg' (zC 1) (k 1) (hk₁ 1) (hk₂ 1)] at key
  have hv := fun j => GlobalTheory.ValNe.val_ofSec_ne_zero_iff ℂ _ q _ s (zC j) _ (hk₁ j)
  rcases hs with ⟨h0, h1⟩ | ⟨h1, h0⟩
  · have e := not_not.1 (mt (hv 1).1 h1)
    exact mul_ne_zero (hc0 0) ((hv 0).2 h0) (by
      have := key
      erw [e, mul_zero, add_zero] at this
      exact this)
  · have e := not_not.1 (mt (hv 0).1 h0)
    exact mul_ne_zero (hc0 1) ((hv 1).2 h1) (by
      have := key
      erw [e, mul_zero, zero_add] at this
      exact this)

open Cardinal in

theorem nonempty_ringHom_complex (K : Type) [Field K] [CharZero K] [Countable K] : Nonempty (K →+* ℂ) := by
  let F := FractionRing (MvPolynomial ℝ K)
  let L := AlgebraicClosure F
  have hF : #F = 𝔠 := by
    have hK : #K ≤ 𝔠 := Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum
    rw [Cardinal.mk_fractionRing, MvPolynomial.cardinalMk_eq_max, Cardinal.mk_real, max_eq_right hK,
      max_eq_left Cardinal.aleph0_le_continuum]
  have hL : #L = 𝔠 := by
    refine le_antisymm ?_ (hF ▸ Cardinal.mk_le_of_injective (algebraMap F L).injective)
    have := Algebra.IsAlgebraic.cardinalMk_le_max F L
    rwa [hF, max_eq_left Cardinal.aleph0_le_continuum] at this
  let j : K →+* L := (algebraMap F L).comp ((algebraMap (MvPolynomial ℝ K) F).comp MvPolynomial.C)
  have : CharZero L := (RingHom.charZero_iff j.injective).1 inferInstance
  obtain ⟨e⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := L) (L := ℂ)
    (hL ▸ Cardinal.aleph0_lt_continuum) (Cardinal.eq.1 (hL.trans Cardinal.mk_complex.symm))
  exact ⟨e.toRingHom.comp j⟩

theorem exists_two_embeddings (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] [CharZero L] [Countable Ω] (a : Ω)
    (ha : a ∉ Set.range (algebraMap L Ω)) :
    ∃ i₁ i₂ : Ω →+* ℂ, i₁.comp (algebraMap L Ω) = i₂.comp (algebraMap L Ω) ∧ i₁ ≠ i₂ := by
  obtain ⟨F, _, j₁, j₂, hj, hne⟩ := GlobalTheory.exists_embeddings_agree_on_subfield_ne L Ω a ha
  let S : Subfield F := Subfield.closure (Set.range j₁ ∪ Set.range j₂)
  have hS : Countable S := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (Subfield.cardinalMk_closure_le_max _).trans (max_le ?_ le_rfl)
    rw [Cardinal.mk_le_aleph0_iff]
    exact ((Set.countable_range _).union (Set.countable_range _)).to_subtype
  let k₁ : Ω →+* S := j₁.codRestrict S fun x => Subfield.subset_closure (Or.inl ⟨x, rfl⟩)
  let k₂ : Ω →+* S := j₂.codRestrict S fun x => Subfield.subset_closure (Or.inr ⟨x, rfl⟩)
  haveI : CharZero S := (RingHom.charZero_iff (k₁.comp (algebraMap L Ω)).injective).1 inferInstance
  obtain ⟨e⟩ := nonempty_ringHom_complex S
  refine ⟨e.comp k₁, e.comp k₂, RingHom.ext fun x => congrArg e (Subtype.ext (RingHom.congr_fun hj x)), fun h => hne ?_⟩
  exact congrArg Subtype.val (e.injective (RingHom.congr_fun h a))

theorem countable_of_fg (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Countable K]
    (h : (⊤ : IntermediateField K Ω).FG) : Countable Ω := by
  obtain ⟨s, hs⟩ := h
  rw [← Cardinal.mk_le_aleph0_iff]
  have := IntermediateField.cardinalMk_adjoin_le K (s : Set Ω)
  rw [hs, Cardinal.mk_congr IntermediateField.topEquiv.toEquiv] at this
  exact this.trans (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl)

theorem sum_rpow_le (D : ℕ) :
    ∑ e ∈ Finset.Icc 1 D, (2 : ℝ) ^ (1 / (e : ℝ)) * e ≤ (((D + 2).choose 2 - 1 : ℕ) : ℝ) := by
  have h : ∀ e : ℕ, 1 ≤ e → (2 : ℝ) ^ (1 / (e : ℝ)) * e ≤ e + 1 := fun e he => by
    have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
    have := rpow_one_add_le_one_add_mul_self (s := 1) (p := 1 / (e : ℝ)) (by norm_num) (by positivity)
      ((div_le_one (by positivity)).2 he')
    rw [one_add_one_eq_two, mul_one] at this
    calc (2 : ℝ) ^ (1 / (e : ℝ)) * e ≤ (1 + 1 / (e : ℝ)) * e := by gcongr
      _ = e + 1 := by field_simp
  induction D with
  | zero => simp
  | succ D ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have e : (D + 1 + 2).choose 2 - 1 = ((D + 2).choose 2 - 1) + (D + 2) := by
      have h1 : (D + 1 + 2).choose 2 = (D + 2).choose 1 + (D + 2).choose 2 := Nat.choose_succ_succ' (D + 2) 1
      have h2 : 0 < (D + 2).choose 2 := Nat.choose_pos (by omega)
      rw [h1, Nat.choose_one_right]
      omega
    rw [e]
    have := h (D + 1) (by omega)
    push_cast at this ih ⊢
    linarith

open GlobalTheory.Discrepancy GlobalTheory.TopForm GlobalTheory.QCoh in

theorem separatesOnSmooth_of_pair (h : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    letI := algebraΓOfHom p
    ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (r : ℕ) (N₀ : LB X) (x₁ x₂ : X) (c : ℕ → ℝ),
      M.IsLB → IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G →
      0 < r → IsNef ℂ N₀ → IsBig ℂ N₀ →
      (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) =
        interNumRed ℂ C ![toLB G] / m + interNumRed ℂ C ![N₀] / r) →
      IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → x₁ ≠ x₂ →
      (∀ e ∈ Finset.Icc 1 n, 0 < c e) →
      (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x₁ ∈ Z ∨ x₂ ∈ Z → 1 ≤ e →
        topologicalKrullDim (Z : Set X) = e →
        c e ^ e < (interNumRed ℂ Z fun _ : Fin e => N₀ : ℝ) / (r : ℝ) ^ e) →
      ∑ e ∈ Finset.Icc 1 n, (2 : ℝ) ^ (1 / (e : ℝ)) * e / c e ≤ 1 →
      ∃ s : M.Sec, (x₁ ∈ nonzeroLocus s ∧ x₂ ∉ nonzeroLocus s) ∨ (x₂ ∈ nonzeroLocus s ∧ x₁ ∉ nonzeroLocus s)) :
    SeparatesOnSmooth := by
  intro X _ _ q D _ hproj hD K B x₁ x₂ hnef hbig h₁ h₂ hne hZ
  letI := algebraΓOfHom q
  haveI := SmoothOfRelativeDimension.smooth D q
  haveI : IsNormalScheme X := isNormalScheme_of_smooth q
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hproj
  have hdim := NadelApp.topologicalKrullDim_eq_of_smooth X q D
  have hK := K.isLB
  have hB := hnef.isLB
  have hKB := isLB_tens hK hB
  obtain ⟨-, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB q).1 hproj
  have hcan : toPic (canonical q D) = cls _ hK :=
    (presents_canonical q D).toPic_eq.trans ((cls_eq_iff _ _).2 (CanonLB.lbIso _ K))
  have hc : (0 : ℝ) < (((D + 2).choose 2 - 1 : ℕ) : ℝ) := by
    have h1 : (D + 2).choose 2 = (D + 1).choose 1 + (D + 1).choose 2 := Nat.choose_succ_succ' (D + 1) 1
    rw [Nat.choose_one_right] at h1
    exact_mod_cast (by omega : 0 < (D + 2).choose 2 - 1)
  have h0 : qWeil (0 : CartierDiv X) 1 = 0 := funext fun z => by
    have := CartierDiv.mult_add (0 : CartierDiv X) 0 z
    rw [add_zero] at this
    simp [qWeil, left_eq_add.1 this]
  have hlc := isLogCanonicalMultiple_canonical (p := q) hdim (0 : CartierDiv X) one_pos
  rw [h0] at hlc
  refine h X q D hproj hdim (tens K.bundle B) 0 1 _ 1 B x₁ x₂ (fun _ => (((D + 2).choose 2 - 1 : ℕ) : ℝ)) hKB
    ⟨by simp, by simp, fun _ => le_rfl⟩ (kltAt_zero_of_smooth hdim) one_pos hlc one_pos hnef hbig (fun C hC => ?_)
    h₁ h₂ hne (fun _ _ => hc) (fun Z e a b c d => ?_) ?_
  · have e1 := hC.interNumRed_of_cls_eq_add hH hKB (isLB_toLB (1 • canonical q D + 0)) hB (by
      rw [cls_tens hK hB hKB, ← toPic_apply, add_zero, one_smul, hcan])
    rw [e1]
    simp
  · have := hZ Z e a b c d
    simp only [Nat.cast_one, one_pow, div_one]
    exact_mod_cast this
  · rw [← Finset.sum_div, div_le_one hc]
    exact sum_rpow_le D

end GlobalTheory.TwoPoint
