import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.GenIdeal
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.MemMinimalPrimesIff

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open GroundTheory.Heights₂.Heights (IsProjPrime IsHomogIdeal relComps localMult)

namespace ChowFormHeightComparison₂.CF.P

open ChowFormHeightComparison₂.CF.A

variable {R : Type} [CommRing R] {Z : Scheme.{0}} {B : LB Z} {m : ℕ} {p : Z ⟶ Sp R} {s : Fin m → B.Sec}

theorem len_equiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (a : A) :
    Module.length B (B ⧸ Ideal.span {e a}) = Module.length A (A ⧸ Ideal.span {a}) := by
  rw [Module.length_quotient, Module.length_quotient]
  have hmap : (Ideal.span {e a} : Ideal B) =
      (Ideal.relIsoOfBijective (e : A →+* B) e.bijective).symm (Ideal.span {a}) := by
    show _ = Ideal.map (e : A →+* B) _
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [hmap]
  exact Order.coheight_orderIso _ _

abbrev qOf {U : Z.Opens} (hU : IsAffineOpen U) {z : Z} (hz : z ∈ U) : Ideal Γ(Z, U) :=
  (hU.primeIdealOf ⟨z, hz⟩).asIdeal

theorem mem_qOf {U : Z.Opens} (hU : IsAffineOpen U) {z : Z} (hz : z ∈ U) (a : Γ(Z, U)) :
    a ∈ qOf hU hz ↔ ¬ IsUnit ((Z.presheaf.germ U z hz).hom a) := by
  letI : Algebra Γ(Z, U) (Z.presheaf.stalk z) := (Z.presheaf.germ U z hz).hom.toAlgebra
  haveI := hU.isLocalization_stalk ⟨z, hz⟩
  have h := IsLocalization.AtPrime.isUnit_to_map_iff (Z.presheaf.stalk z) (qOf hU hz) a
  rw [← not_iff_not, not_not]
  exact h.symm

structure Ch (p : Z ⟶ Sp R) (s : Fin m → B.Sec) (k : Fin m) (t : Fin m → Γ(Z, nonzeroLocus (s k))) : Prop where
  aff : IsAffineOpen (nonzeroLocus (s k))
  surj : Function.Surjective (eval₂Hom (algX p (nonzeroLocus (s k))) t)
  rel : ∀ j i, resG Z (inf_le_right : nonzeroLocus (s k) ⊓ B.U i ≤ B.U i) ((s j).f i) =
      resG Z (inf_le_left : nonzeroLocus (s k) ⊓ B.U i ≤ nonzeroLocus (s k)) (t j) *
        resG Z (inf_le_right : nonzeroLocus (s k) ⊓ B.U i ≤ B.U i) ((s k).f i)

theorem exists_ch (hE : Emb p s) (k : Fin m) : ∃ t, Ch p s k t :=
  have ⟨h1, t, h2, h3⟩ := hE.chart k
  ⟨t, h1, h2, h3⟩

theorem exists_mem (hE : Emb p s) (z : Z) : ∃ k, z ∈ nonzeroLocus (s k) := by
  have hz : z ∈ (⨆ k, nonzeroLocus (s k)) := by
    rw [hE.cover]
    trivial
  exact Opens.mem_iSup.mp hz

variable {k : Fin m} {t : Fin m → Γ(Z, nonzeroLocus (s k))}

theorem Ch.germ (h : Ch p s k t) {z : Z} (hz : z ∈ nonzeroLocus (s k)) {i : B.ι} (hi : z ∈ B.U i) (j : Fin m) :
    (Z.presheaf.germ _ z hi).hom ((s j).f i) =
      (Z.presheaf.germ _ z hz).hom (t j) * (Z.presheaf.germ _ z hi).hom ((s k).f i) := by
  have hzi : z ∈ nonzeroLocus (s k) ⊓ B.U i := ⟨hz, hi⟩
  have hc := congrArg (Z.presheaf.germ _ z hzi).hom (h.rel j i)
  rw [map_mul] at hc
  erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
    TopCat.Presheaf.germ_res_apply] at hc
  exact hc

theorem isUnit_germ {u : B.Sec} {z : Z} {i : B.ι} (hi : z ∈ B.U i) :
    z ∈ nonzeroLocus u ↔ IsUnit ((Z.presheaf.germ _ z hi).hom (u.f i)) := by
  constructor
  · intro hz
    unfold nonzeroLocus at hz
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp hz
    have hzk : z ∈ B.U k := Z.basicOpen_le _ hk
    have hu := (Z.mem_basicOpen _ _ hzk).mp hk
    have hzik : z ∈ B.U i ⊓ B.U k := ⟨hi, hzk⟩
    have hc := congrArg (Z.presheaf.germ (B.U i ⊓ B.U k) z hzik).hom (u.compat i k)
    rw [map_mul] at hc
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at hc
    erw [hc]
    exact ((Units.isUnit _).map _).mul hu
  · intro hu
    unfold nonzeroLocus
    exact Opens.mem_iSup.mpr ⟨i, (Z.mem_basicOpen _ _ hi).mpr hu⟩

theorem Ch.one (h : Ch p s k t) (hB : B.IsLB) : t k = 1 := by
  apply TopCat.Presheaf.section_ext Z.sheaf
  intro z hz
  have hzc : z ∈ (⨆ i, B.U i) := by
    rw [hB.cover]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hzc
  have hg := h.germ hz hi k
  have hu := (isUnit_germ (u := s k) hi).mp hz
  change (Z.presheaf.germ _ z hz).hom (t k) = (Z.presheaf.germ _ z hz).hom 1
  rw [map_one]
  exact (hu.mul_right_cancel (by rw [one_mul]; exact hg)).symm

theorem germ_algX {U W : Z.Opens} {z : Z} (hU : z ∈ U) (hW : z ∈ W) (r : R) :
    (Z.presheaf.germ _ z hU).hom (algX p U r) = (Z.presheaf.germ _ z hW).hom (algX p W r) := by
  have hUW : z ∈ U ⊓ W := ⟨hU, hW⟩
  have e1 : algX p (U ⊓ W) r = resG Z (inf_le_left : U ⊓ W ≤ U) (algX p U r) := by
    rw [← GlobalTheory.TopForm.resG_comp_algX p (inf_le_left : U ⊓ W ≤ U)]
    rfl
  have e2 : algX p (U ⊓ W) r = resG Z (inf_le_right : U ⊓ W ≤ W) (algX p W r) := by
    rw [← GlobalTheory.TopForm.resG_comp_algX p (inf_le_right : U ⊓ W ≤ W)]
    rfl
  have g1 := congrArg (Z.presheaf.germ _ z hUW).hom e1
  have g2 := congrArg (Z.presheaf.germ _ z hUW).hom e2
  have r1 := Z.presheaf.germ_res_apply (homOfLE (inf_le_left : U ⊓ W ≤ U)) z hUW (algX p U r)
  have r2 := Z.presheaf.germ_res_apply (homOfLE (inf_le_right : U ⊓ W ≤ W)) z hUW (algX p W r)
  exact r1.symm.trans ((g1.symm.trans g2).trans r2)

theorem Ch.germ_eval (h : Ch p s k t) {z : Z} (hz : z ∈ nonzeroLocus (s k)) {i : B.ι} (hi : z ∈ B.U i) {d : ℕ}
    {g : MvPolynomial (Fin m) R} (hg : g.IsHomogeneous d) :
    (Z.presheaf.germ _ z hi).hom (eval₂Hom (algX p (B.U i)) (fun j => (s j).f i) g) =
      (Z.presheaf.germ _ z hz).hom (eval₂Hom (algX p _) t g) * (Z.presheaf.germ _ z hi).hom ((s k).f i) ^ d := by
  rw [coe_eval₂Hom, coe_eval₂Hom, hom_eval₂, hom_eval₂]
  have hc : (Z.presheaf.germ _ z hi).hom.comp (algX p (B.U i)) =
      (Z.presheaf.germ _ z hz).hom.comp (algX p (nonzeroLocus (s k))) := by
    ext r
    exact germ_algX hi hz r
  have hfun : (fun j => (Z.presheaf.germ _ z hi).hom ((s j).f i)) =
      fun j => (Z.presheaf.germ _ z hz).hom (t j) * (Z.presheaf.germ _ z hi).hom ((s k).f i) :=
    funext fun j => h.germ hz hi j
  rw [hfun, hc]
  have := eval₂Hom_mul ((Z.presheaf.germ _ z hz).hom.comp (algX p (nonzeroLocus (s k))))
    (fun j => (Z.presheaf.germ _ z hz).hom (t j)) hg ((Z.presheaf.germ _ z hi).hom ((s k).f i))
  rw [coe_eval₂Hom, coe_eval₂Hom] at this
  exact this

theorem mem_ker_coneHom {z : Z} {i : B.ι} (hi : z ∈ B.U i) (g : MvPolynomial (Fin m) R) :
    g ∈ RingHom.ker (coneHom p s z i hi) ↔ ∀ d, ¬ IsUnit ((Z.presheaf.germ _ z hi).hom
      (eval₂Hom (algX p (B.U i)) (fun j => (s j).f i) (homogeneousComponent d g))) := by
  rw [RingHom.mem_ker]
  change ChowFormHeightComparison₂.CF.A.cone ((Z.evaluation (B.U i) z hi).hom.comp (algX p (B.U i)))
    (fun k => (Z.evaluation (B.U i) z hi).hom ((s k).f i)) g = 0 ↔ _
  rw [Polynomial.ext_iff]
  simp only [coeff_cone, Polynomial.coeff_zero]
  apply forall_congr'
  intro d
  have e := Scheme.evaluation_eq_zero_iff_notMem_basicOpen Z z hi
    (eval₂Hom (algX p (B.U i)) (fun j => (s j).f i) (homogeneousComponent d g))
  rw [Scheme.mem_basicOpen Z _ z hi] at e
  rw [coe_eval₂Hom, ← hom_eval₂]
  exact e

theorem Ch.ptIdeal_eq (h : Ch p s k t) (hB : B.IsLB) {z : Z} (hz : z ∈ nonzeroLocus (s k)) :
    ptIdeal p s z = pr (algX p _) t (qOf h.aff hz) := by
  ext g
  have hzc : z ∈ (⨆ i, B.U i) := by
    rw [hB.cover]
    trivial
  obtain ⟨i0, hi0⟩ := Opens.mem_iSup.mp hzc
  have key : ∀ i (hi : z ∈ B.U i) (d : ℕ),
      IsUnit ((Z.presheaf.germ _ z hi).hom
        (eval₂Hom (algX p (B.U i)) (fun j => (s j).f i) (homogeneousComponent d g))) ↔
      IsUnit ((Z.presheaf.germ _ z hz).hom (eval₂Hom (algX p _) t (homogeneousComponent d g))) := by
    intro i hi d
    rw [h.germ_eval hz hi (homogeneousComponent_isHomogeneous d g)]
    exact IsUnit.mul_iff.trans (and_iff_left (((isUnit_germ hi).mp hz).pow d))
  rw [ChowFormHeightComparison₂.CF.A.mem_pr]
  simp only [ptIdeal, Submodule.mem_iInf, mem_ker_coneHom]
  constructor
  · intro H d
    rw [mem_qOf]
    exact (key i0 hi0 d).not.mp (H i0 hi0 d)
  · intro H i hi d
    exact (key i hi d).not.mpr ((mem_qOf _ _ _).mp (H d))

theorem isProjPrime (hE : Emb p s) (z : Z) : IsProjPrime (ptIdeal p s z) := by
  obtain ⟨k, hk⟩ := exists_mem hE z
  obtain ⟨t, h⟩ := exists_ch hE k
  rw [h.ptIdeal_eq hE.isLB hk]
  exact isProjPrime_pr (h.one hE.isLB) _

private theorem linForm_isHomogeneous_one_minimal_prime_dimensions (u : Fin m → R) :
    (GroundTheory.Heights₂.Heights.linForm u).IsHomogeneous 1 := by
  unfold GroundTheory.Heights₂.Heights.linForm
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X (u j) j

theorem Ch.germ_comb (h : Ch p s k t) {u : Fin m → R} {su : B.Sec} (hu : IsComb p s u su) {z : Z}
    (hz : z ∈ nonzeroLocus (s k)) {i : B.ι} (hi : z ∈ B.U i) :
    (Z.presheaf.germ _ z hi).hom (su.f i) =
      (Z.presheaf.germ _ z hz).hom (eval₂Hom (algX p _) t (GroundTheory.Heights₂.Heights.linForm u)) *
        (Z.presheaf.germ _ z hi).hom ((s k).f i) := by
  have heq : su.f i = eval₂Hom (algX p (B.U i)) (fun j => (s j).f i)
      (GroundTheory.Heights₂.Heights.linForm u) := by
    rw [hu i]
    simp [GroundTheory.Heights₂.Heights.linForm, map_sum]
  rw [heq, h.germ_eval hz hi (linForm_isHomogeneous_one_minimal_prime_dimensions u), pow_one]

theorem mem_iff (hE : Emb p s) {u : Fin m → R} {su : B.Sec} (hu : IsComb p s u su) (z : Z) :
    z ∈ nonzeroLocus su ↔ GroundTheory.Heights₂.Heights.linForm u ∉ ptIdeal p s z := by
  obtain ⟨k, hk⟩ := exists_mem hE z
  obtain ⟨t, h⟩ := exists_ch hE k
  obtain ⟨i, hi⟩ := LB.mem_of_cover hE.isLB z
  rw [h.ptIdeal_eq hE.isLB hk, mem_pr_homog (isHomog_linForm u), mem_qOf, not_not, isUnit_germ hi,
    h.germ_comb hu hk hi, IsUnit.mul_iff, and_iff_left ((isUnit_germ hi).1 hk)]

theorem mem_iff_X (hE : Emb p s) (j : Fin m) (z : Z) : z ∈ nonzeroLocus (s j) ↔ X j ∉ ptIdeal p s z := by
  obtain ⟨k, hz⟩ := exists_mem hE z
  obtain ⟨t, h⟩ := exists_ch hE k
  have hzc : z ∈ (⨆ i, B.U i) := by
    rw [hE.isLB.cover]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hzc
  rw [h.ptIdeal_eq hE.isLB hz, ChowFormHeightComparison₂.CF.A.mem_pr_homog (isHomogeneous_X R j), mem_qOf, not_not,
    eval₂Hom_X', isUnit_germ hi, h.germ hz hi j]
  exact IsUnit.mul_iff.trans (and_iff_left ((isUnit_germ hi).mp hz))

theorem qOf_le_iff {U : Z.Opens} (hU : IsAffineOpen U) {z z' : Z} (hz : z ∈ U) (hz' : z' ∈ U) :
    qOf hU hz ≤ qOf hU hz' ↔ z ⤳ z' := by
  have e := (hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff
    (x := hU.primeIdealOf ⟨z, hz⟩) (y := hU.primeIdealOf ⟨z', hz'⟩))
  rw [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at e
  rw [e]
  exact PrimeSpectrum.le_iff_specializes _ _

theorem specializes_iff (hE : Emb p s) (z z' : Z) : z ⤳ z' ↔ ptIdeal p s z ≤ ptIdeal p s z' := by
  obtain ⟨k, hz'⟩ := exists_mem hE z'
  obtain ⟨t, h⟩ := exists_ch hE k
  have h1 := h.one hE.isLB
  constructor
  · intro hsp
    have hz : z ∈ nonzeroLocus (s k) := hsp.mem_open (nonzeroLocus (s k)).isOpen hz'
    rw [h.ptIdeal_eq hE.isLB hz, h.ptIdeal_eq hE.isLB hz', ChowFormHeightComparison₂.CF.A.pr_le_iff h.surj h1,
      qOf_le_iff]
    exact hsp
  · intro hle
    have hz : z ∈ nonzeroLocus (s k) :=
      (mem_iff_X hE k z).mpr fun hx => (mem_iff_X hE k z').mp hz' (hle hx)
    rw [h.ptIdeal_eq hE.isLB hz, h.ptIdeal_eq hE.isLB hz', ChowFormHeightComparison₂.CF.A.pr_le_iff h.surj h1,
      qOf_le_iff] at hle
    exact hle

theorem injective (hE : Emb p s) : Function.Injective (ptIdeal p s) := fun z z' h =>
  (((specializes_iff hE z z').2 h.le).antisymm ((specializes_iff hE z' z).2 h.ge)).eq

variable [IsIntegral Z]

theorem qOf_generic {U : Z.Opens} (hU : IsAffineOpen U) (hz : genericPoint Z ∈ U) : qOf hU hz = ⊥ := by
  haveI : Nonempty U := ⟨⟨_, hz⟩⟩
  show (hU.primeIdealOf ⟨genericPoint Z, hz⟩).asIdeal = ⊥
  rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
  rfl

theorem exists_pt (hE : Emb p s) (W : Ideal (MvPolynomial (Fin m) R)) (hW : IsProjPrime W)
    (hle : ptIdeal p s (genericPoint Z) ≤ W) : ∃ z, ptIdeal p s z = W := by
  obtain ⟨k, hk⟩ := hW.isRelevant
  obtain ⟨t, h⟩ := exists_ch hE k
  have h1 := h.one hE.isLB
  have hη : genericPoint Z ∈ nonzeroLocus (s k) := (mem_iff_X hE k _).mpr fun hx => hk (hle hx)
  rw [h.ptIdeal_eq hE.isLB hη, qOf_generic] at hle
  obtain ⟨q, hq, hqW⟩ := ChowFormHeightComparison₂.CF.A.exists_eq_pr h.surj h1 hW.isPrime hW.isHomog hk hle
  let P : PrimeSpectrum Γ(Z, nonzeroLocus (s k)) := ⟨q, hq⟩
  have hmem : h.aff.fromSpec P ∈ nonzeroLocus (s k) := by
    rw [← SetLike.mem_coe, ← h.aff.range_fromSpec]
    exact ⟨P, rfl⟩
  refine ⟨h.aff.fromSpec P, ?_⟩
  rw [h.ptIdeal_eq hE.isLB hmem, ← hqW]
  congr 1
  have hinj : h.aff.primeIdealOf ⟨_, hmem⟩ = P :=
    h.aff.fromSpec.isOpenEmbedding.injective (h.aff.fromSpec_primeIdealOf ⟨_, hmem⟩)
  show (h.aff.primeIdealOf ⟨_, hmem⟩).asIdeal = q
  rw [hinj]

end ChowFormHeightComparison₂.CF.P

namespace ChowFormHeightComparison₂.CF

theorem stPts : StPts := fun _ _ _ _ _ _ _ _ hE =>
  ⟨P.isProjPrime hE, P.specializes_iff hE, P.exists_pt hE, fun _ _ hu => P.mem_iff hE hu⟩

private theorem mem_minimalPrimes_span_iff_mem_height_eq_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (q : Ideal A) [q.IsPrime] {f : A} (hf : f ≠ 0) :
    q ∈ (Ideal.span {f}).minimalPrimes ↔ f ∈ q ∧ q.height = 1 := by
  have hpos : ∀ (p : Ideal A) [p.IsPrime], f ∈ p → 1 ≤ p.height := by
    intro p _ hfp
    have hlt : (⊥ : Ideal A) < p := by
      refine bot_lt_iff_ne_bot.mpr fun hp => hf ?_
      rw [hp, Ideal.mem_bot] at hfp
      exact hfp
    exact le_trans le_add_self (Ideal.height_add_one_le_of_lt_of_isPrime hlt)
  constructor
  · intro hq
    have hfq : f ∈ q := hq.1.2 (Ideal.mem_span_singleton_self f)
    exact ⟨hfq, le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq)
      (hpos q hfq)⟩
  · rintro ⟨hfq, hq1⟩
    refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).mpr hfq⟩, ?_⟩
    rintro p ⟨hp, hfp⟩ hpq
    haveI := hp
    by_contra hne
    have hlt : p < q := lt_of_le_not_ge hpq hne
    have h1 := hpos p ((Ideal.span_singleton_le_iff_mem _).mp hfp)
    have h2 := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
    rw [hq1] at h2
    exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

open ChowFormHeightComparison₂.CF.A ChowFormHeightComparison₂.CF.P in
theorem stDiv : StDiv := by
  intro R _ _ Z _ _ p B m s hE u su hsu hu
  have hB := hE.isLB
  have core : ∀ z : Z,
      ((divOfSec hB su hu).mult z ≠ 0 ↔ ptIdeal p s z ∈
        relComps (ptIdeal p s (genericPoint Z) ⊔ Ideal.span {GroundTheory.Heights₂.Heights.linForm u})) ∧
      ((divOfSec hB su hu).mult z ≠ 0 → (divOfSec hB su hu).mult z =
        ↑(localMult (ptIdeal p s (genericPoint Z) ⊔ Ideal.span {GroundTheory.Heights₂.Heights.linForm u})
          (ptIdeal p s z))) := by
    intro z
    obtain ⟨k, hz⟩ := P.exists_mem hE z
    obtain ⟨t, h⟩ := P.exists_ch hE k
    have h1 := h.one hB
    have hη : genericPoint Z ∈ nonzeroLocus (s k) :=
      ((genericPoint_spec Z).mem_open_set_iff (nonzeroLocus (s k)).isOpen).mpr
        ⟨z, Set.mem_univ _, hz⟩
    haveI : Nonempty (nonzeroLocus (s k)) := ⟨⟨z, hz⟩⟩
    haveI : IsNoetherianRing Γ(Z, nonzeroLocus (s k)) :=
      IsLocallyNoetherian.component_noetherian ⟨_, h.aff⟩
    have hf0 : eval₂Hom (algX p (nonzeroLocus (s k))) t (GroundTheory.Heights₂.Heights.linForm u) ≠ 0 := by
      have hnm := (P.mem_iff hE hsu (genericPoint Z)).mp hu
      rw [h.ptIdeal_eq hB hη, qOf_generic, ChowFormHeightComparison₂.CF.A.mem_pr_homog (linForm_isHomogeneous_one_minimal_prime_dimensions u)] at hnm
      intro h0
      exact hnm (by rw [Ideal.mem_bot]; exact h0)
    rw [h.ptIdeal_eq hB hz, h.ptIdeal_eq hB hη, qOf_generic]
    have hrel : pr (algX p (nonzeroLocus (s k))) t (qOf h.aff hz) ∈
        relComps (pr (algX p (nonzeroLocus (s k))) t ⊥ ⊔ Ideal.span {GroundTheory.Heights₂.Heights.linForm u}) ↔
        qOf h.aff hz ∈ (Ideal.span {eval₂Hom (algX p (nonzeroLocus (s k))) t
          (GroundTheory.Heights₂.Heights.linForm u)}).minimalPrimes := by
      rw [← ChowFormHeightComparison₂.CF.A.mem_minimalPrimes_iff h.surj h1 u (qOf h.aff hz)]
      exact ⟨fun H => H.1, fun H => ⟨H, k, ChowFormHeightComparison₂.CF.A.X_notMem_pr h1 _⟩⟩
    rw [hrel, ChowFormHeightComparison₂.CF.A.localMult_pr h.surj h1 u (qOf h.aff hz)]
    have hzc : z ∈ (⨆ i, B.U i) := by
      rw [hB.cover]
      trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hzc
    letI : Algebra Γ(Z, nonzeroLocus (s k)) (Z.presheaf.stalk z) :=
      (Z.presheaf.germ _ z hz).hom.toAlgebra
    haveI : IsLocalization.AtPrime (Z.presheaf.stalk z) (qOf h.aff hz) :=
      h.aff.isLocalization_stalk ⟨z, hz⟩
    have hht : Order.coheight z = (qOf h.aff hz).height := by
      have e1 := ringKrullDim_stalk_eq_coheight z
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height (qOf h.aff hz) (Z.presheaf.stalk z)] at e1
      exact (WithBot.coe_inj.mp e1).symm
    have hg := h.germ_comb hsu hz hi
    have hunit := (isUnit_germ hi).mp hz
    have hspan : Ideal.span {(Z.presheaf.germ _ z hi).hom (su.f i)} =
        Ideal.span {algebraMap _ (Z.presheaf.stalk z)
          (eval₂Hom (algX p (nonzeroLocus (s k))) t (GroundTheory.Heights₂.Heights.linForm u))} := by
      rw [hg]
      exact Ideal.span_singleton_mul_right_unit hunit _
    have hlen : Module.length (Z.presheaf.stalk z) (Z.presheaf.stalk z ⧸ Ideal.span {algebraMap _
          (Z.presheaf.stalk z) (eval₂Hom (algX p (nonzeroLocus (s k))) t
            (GroundTheory.Heights₂.Heights.linForm u))}) =
        Module.length (Localization.AtPrime (qOf h.aff hz))
          (Localization.AtPrime (qOf h.aff hz) ⧸ Ideal.map (algebraMap _ (Localization.AtPrime
            (qOf h.aff hz))) (Ideal.span {eval₂Hom (algX p (nonzeroLocus (s k))) t
              (GroundTheory.Heights₂.Heights.linForm u)})) := by
      have he := (IsLocalization.algEquiv (qOf h.aff hz).primeCompl
        (Localization.AtPrime (qOf h.aff hz)) (Z.presheaf.stalk z)).commutes
          (eval₂Hom (algX p (nonzeroLocus (s k))) t (GroundTheory.Heights₂.Heights.linForm u))
      rw [Ideal.map_span, Set.image_singleton, ← he]
      exact len_equiv (IsLocalization.algEquiv (qOf h.aff hz).primeCompl
        (Localization.AtPrime (qOf h.aff hz)) (Z.presheaf.stalk z)).toRingEquiv _
    have hLM : localMult (Ideal.span {eval₂Hom (algX p (nonzeroLocus (s k))) t
          (GroundTheory.Heights₂.Heights.linForm u)}) (qOf h.aff hz) =
        (Module.length (Z.presheaf.stalk z) (Z.presheaf.stalk z ⧸ Ideal.span {algebraMap _
          (Z.presheaf.stalk z) (eval₂Hom (algX p (nonzeroLocus (s k))) t
            (GroundTheory.Heights₂.Heights.linForm u))})).toNat := by
      rw [hlen]
      unfold localMult
      rw [dif_pos (show (qOf h.aff hz).IsPrime from inferInstance)]
    by_cases hc : Order.coheight z = 1
    · have hmult := GlobalTheory.Cartier.mult_divOfSec (hL := hB) (s := su) (hs := hu) hc hi
      rw [hmult, hspan, ← hLM]
      refine ⟨?_, fun _ => rfl⟩
      rw [mem_minimalPrimes_span_iff_mem_height_eq_one _ hf0, ← hht, hc, and_iff_left rfl, hLM]
      haveI : Ring.KrullDimLE 1 (Z.presheaf.stalk z) := krullDimLE_of_coheight_le hc.le
      have hne0 : algebraMap _ (Z.presheaf.stalk z)
          (eval₂Hom (algX p (nonzeroLocus (s k))) t (GroundTheory.Heights₂.Heights.linForm u)) ≠ 0 := by
        intro h0
        apply hf0
        exact germ_injective_of_isIntegral Z z hz (h0.trans (map_zero _).symm)
      have hfin := isFiniteLength_quotient_span_singleton (Z.presheaf.stalk z)
        (mem_nonZeroDivisors_of_ne_zero hne0)
      have hntop := Module.length_ne_top_iff.mpr hfin
      rw [Nat.cast_ne_zero, Ne, ENat.toNat_eq_zero, or_iff_left hntop, Module.length_eq_zero_iff,
        Ideal.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top,
        IsLocalization.AtPrime.isUnit_to_map_iff (Z.presheaf.stalk z) (qOf h.aff hz)]
      exact not_not
    · have h0 : (divOfSec hB su hu).mult z = 0 := by
        by_contra hne
        exact hc (GlobalTheory.Cartier.CartierDiv.coheight_eq_one_of_mult_ne_zero hne)
      rw [h0]
      refine ⟨⟨fun H => absurd rfl H, fun H => absurd ?_ hc⟩, fun H => absurd rfl H⟩
      rw [hht]
      exact ((mem_minimalPrimes_span_iff_mem_height_eq_one _ hf0).mp H).2
  exact ⟨fun z => (core z).1, fun z => (core z).2⟩

end ChowFormHeightComparison₂.CF
