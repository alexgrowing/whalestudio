import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjDehom
import ReciprocityTheory.AnalyticForms.RegularLocalRings.LogResStC
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinTypeQE
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHypA
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHypStalk
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHypB
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHypC

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

instance isNoetherian_projX {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    IsNoetherian (projX P hP) :=
  (isNoetherian_iff_of_finite_iSup_eq_top (S := chartOpen hP) (iSup_chartOpen_eq_top hP)).mpr
    (isNoetherianRing_gammaChart hP)

theorem isReduced_projX {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hrad : P.IsRadical) : IsReduced (projX P hP) := by
  haveI : ∀ x : projX P hP, _root_.IsReduced ((projX P hP).presheaf.stalk x) := by
    intro x
    obtain ⟨p, hp⟩ := chartOpen_cover hP x
    have hU := (chartOpen hP p).2
    let x' : ((chartOpen hP p).1 : Set (projX P hP)) := ⟨x, hp⟩
    show _root_.IsReduced ((projX P hP).presheaf.stalk (x' : projX P hP))
    letI := TopCat.Presheaf.algebra_section_stalk (projX P hP).presheaf x'
    haveI := hU.isLocalization_stalk x'
    exact isReduced_localizationPreserves (hU.primeIdealOf x').asIdeal.primeCompl _
      (isReduced_gammaChart hP hrad p)
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk _

theorem qe_projX {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hQE : FinalTheorems.FinTypeQE) : FinalTheorems.QE (projX P hP) := by
  intro x
  obtain ⟨p, hp⟩ := chartOpen_cover hP x
  exact ⟨chartOpen hP p, hp, qeRing_gammaChart hP hQE p⟩

theorem fFinRes_projX {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    FinalTheorems.FFinRes (projX P hP) := by
  intro x p _ hchar
  obtain ⟨q, hq⟩ := chartOpen_cover hP x
  let f : ℂ →+* (projX P hP).residueField x :=
    ((projX P hP).residue x).hom.comp (((projX P hP).presheaf.germ (chartOpen hP q).1 x hq).hom.comp
      ((gammaChart hP q).symm.toRingHom.comp (algebraMap ℂ (chartRing P q))))
  exfalso
  have h1 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have h2 : f (p : ℂ) = 0 := by
    rw [map_natCast]
    exact CharP.cast_eq_zero _ p
  exact h1 (f.injective (by rw [h2, map_zero]))

def projB (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P) :
    TopologicalSpace.Closeds (projX P hP) :=
  letI := segreGraded hP
  ⟨ProjectiveSpectrum.zeroLocus (segreGrading P) (Ideal.Quotient.mk (segreIdeal P) '' (segreIdeal D : Set _)),
    ProjectiveSpectrum.isClosed_zeroLocus _ _⟩

theorem mem_projB_iff {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hD : IsMultiHomogIdeal D) (p : (k : K) → ι k) (x : projX P hP) (hx : x ∈ (chartOpen hP p).1) :
    x ∈ projB P D hP ↔
      ∀ f ∈ D, (projX P hP).evaluation _ x hx ((gammaChart hP p).symm (Ideal.Quotient.mk _ f)) = 0 := by
  letI := segreGraded hP
  have hsec : ∀ f, (gammaChart hP p).symm (Ideal.Quotient.mk _ f) =
      Proj.awayToSection (segreGrading P) (segreW P p) (polyToAway hP p f) := fun f => rfl
  show (Ideal.Quotient.mk (segreIdeal P) '' (segreIdeal D : Set _)) ⊆
    (ProjectiveSpectrum.asHomogeneousIdeal (𝒜 := segreGrading P) x : Set _) ↔ _
  constructor
  · intro hx'
    obtain ⟨S, hS, rfl⟩ := hD
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, ha⟩ := hS f hf
      have hrn : rename (chartUpd p) f ∈ segreIdeal (Ideal.span S) := by
        show segreMap (rename (chartUpd p) f) ∈ Ideal.span S
        rw [segre_rename_chartUpd p ha]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span hf)
      have hhom := (isHomogeneous_of_isMultiHomog ha).rename_isHomogeneous (f := chartUpd p)
      rw [hsec, away_eq_mk_of_val hP p _ hhom _ (val_polyToAway_mul_pow hP p ha)]
      exact (evaluation_awayToSection_eq_zero_iff _ _ x hx _).mpr (hx' ⟨_, hrn, rfl⟩)
    | zero => simp
    | add f g _ _ h1 h2 => simp only [map_add, h1, h2, add_zero]
    | smul a f _ h1 => simp only [smul_eq_mul, map_mul, h1, mul_zero]
  · intro h g hg
    obtain ⟨g, hg, rfl⟩ := hg
    rw [← sum_homogeneousComponent g, map_sum]
    show _ ∈ (ProjectiveSpectrum.asHomogeneousIdeal (𝒜 := segreGrading P) x).toIdeal
    refine Ideal.sum_mem _ fun d _ => ?_
    have hgd : homogeneousComponent d g ∈ segreIdeal D :=
      homogeneousComponent_mem_of_mem (segreIdeal_isHomogeneous hD) hg d
    have hv := h _ hgd
    rw [hsec, away_eq_mk_of_val hP p _ (homogeneousComponent_isHomogeneous d g) _
      (val_polyToAway_segre_mul_pow hP p (homogeneousComponent_isHomogeneous d g))] at hv
    exact (evaluation_awayToSection_eq_zero_iff _ _ x hx _).mp hv

def ptIdealOf {σ : Type} (z : σ → ℂ) : Ideal (MvPolynomial σ ℂ) :=
  RingHom.ker (MvPolynomial.eval z : MvPolynomial σ ℂ →+* ℂ)

instance ptIdealOf_isPrime {σ : Type} (z : σ → ℂ) : (ptIdealOf z).IsPrime :=
  RingHom.ker_isPrime _

abbrev locAt {σ : Type} (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) : Type :=
  Localization.AtPrime (ptIdealOf z) ⧸
    Ideal.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (ptIdealOf z))) I

abbrev chartLocRing (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (y : (Σ k, ι k) → ℂ) :
    Type :=
  locAt (chartIdeal P p) y

theorem exists_closedPoint_stalk {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (x : projX P hP) (hx : x ∈ (chartOpen hP p).1) (hc : IsClosed ({x} : Set (projX P hP))) :
    ∃ y : (Σ k, ι k) → ℂ, (∀ h ∈ chartIdeal P p, eval y h = 0) ∧
      (∀ q, val (toSpecC hP) (chartCoord hP p q) x hx = y q) ∧
      Nonempty ((projX P hP).presheaf.stalk x ≃+* chartLocRing P p y) := by
  exact exists_closedPoint_stalk' hP p x hx hc

theorem isClosed_sing {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hQE : FinalTheorems.FinTypeQE) : IsClosed (FinalTheorems.Sing (projX P hP)) := by
  have hopen := isOpen_regularLocus_of_cover (fun p => chartOpen hP p) (chartOpen_cover hP)
    (fun p => (qeRing_gammaChart hP hQE p).2.2 _)
  exact hopen.isClosed_compl

theorem sing_subset_projB {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hD : IsMultiHomogIdeal D) (hQE : FinalTheorems.FinTypeQE)
    (hsing : ∀ (p : (k : K) → ι k) (y : (Σ k, ι k) → ℂ), (∀ h ∈ chartIdeal P p, eval y h = 0) →
      ¬ IsRegularLocalRing (chartLocRing P p y) → ∀ f ∈ D, eval y f = 0) :
    FinalTheorems.Sing (projX P hP) ⊆ (projB P D hP : Set (projX P hP)) := by
  intro x hx
  by_contra hxB
  have : JacobsonSpace (projX P hP) := LocallyOfFiniteType.jacobsonSpace (toSpecC hP)
  have hZ : IsLocallyClosed (FinalTheorems.Sing (projX P hP) ∩ (projB P D hP : Set (projX P hP))ᶜ) :=
    (isClosed_sing hP hQE).isLocallyClosed.inter (projB P D hP).isClosed.isOpen_compl.isLocallyClosed
  obtain ⟨c, ⟨hcS, hcB⟩, hcc⟩ := nonempty_inter_closedPoints
    (Z := FinalTheorems.Sing (projX P hP) ∩ (projB P D hP : Set (projX P hP))ᶜ) ⟨x, hx, hxB⟩ hZ
  obtain ⟨p, hp⟩ := chartOpen_cover hP c
  obtain ⟨y, hy, hval, ⟨e⟩⟩ := exists_closedPoint_stalk hP p c hp hcc
  have hreg : ¬ IsRegularLocalRing (chartLocRing P p y) := fun h =>
    hcS (IsRegularLocalRing.of_ringEquiv e.symm)
  have hDy := hsing p y hy hreg
  apply hcB
  rw [SetLike.mem_coe, mem_projB_iff hP hD p c hp]
  intro f hf
  rw [← val_eq_zero_iff (toSpecC hP) _ c hp hcc]
  obtain ⟨φ, hφ⟩ := val_ringHom (toSpecC hP) (chartOpen hP p).1 c hp hcc
  rw [← hφ, gammaChart_symm_mk, eval₂_comp_left]
  have h1 : φ.comp (constSec (toSpecC hP) (chartOpen hP p).1) = RingHom.id ℂ := by
    ext a; simp [hφ, val_const (toSpecC hP) _ c hp hcc]
  have h2 : (φ ∘ chartCoord hP p) = y := by
    funext q; simp [hφ, hval]
  rw [h1, h2]
  exact hDy f hf

theorem interior_projB {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hD : IsMultiHomogIdeal D) (hmin : ∀ q ∈ P.minimalPrimes, IsRelevant q → ¬ D ≤ q) :
    interior (projB P D hP : Set (projX P hP)) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨p, hp⟩ := chartOpen_cover hP x
  have hA : IsAffineOpen (chartOpen hP p).1 := (chartOpen hP p).2
  obtain ⟨𝔮, h𝔮min, h𝔮le⟩ :=
    Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ (hA.primeIdealOf ⟨x, hp⟩).asIdeal)
  have h𝔮p : 𝔮.IsPrime := h𝔮min.1.1
  let η : PrimeSpectrum Γ(projX P hP, (chartOpen hP p).1) := ⟨𝔮, h𝔮p⟩
  have hspec : hA.fromSpec η ⤳ x := by
    have h1 : η ⤳ hA.primeIdealOf ⟨x, hp⟩ := (PrimeSpectrum.le_iff_specializes _ _).mp h𝔮le
    have h2 := h1.map (hA.fromSpec).continuous
    rwa [hA.fromSpec_primeIdealOf] at h2
  have hηO : hA.fromSpec η ∈ interior (projB P D hP : Set (projX P hP)) :=
    hspec.mem_open isOpen_interior hx
  have hηU : hA.fromSpec η ∈ (chartOpen hP p).1 := hA.range_fromSpec.le ⟨η, rfl⟩
  have hηB : hA.fromSpec η ∈ (projB P D hP : Set (projX P hP)) := interior_subset hηO
  rw [SetLike.mem_coe, mem_projB_iff hP hD p _ hηU] at hηB
  have hpη : hA.primeIdealOf ⟨hA.fromSpec η, hηU⟩ = η :=
    (hA.fromSpec).isOpenEmbedding.injective (hA.fromSpec_primeIdealOf ⟨hA.fromSpec η, hηU⟩)
  let θ : MvPolynomial (Σ k, ι k) ℂ →+* Γ(projX P hP, (chartOpen hP p).1) :=
    (gammaChart hP p).symm.toRingHom.comp (Ideal.Quotient.mk (chartIdeal P p))
  have hθs : Function.Surjective θ :=
    (gammaChart hP p).symm.surjective.comp Ideal.Quotient.mk_surjective
  have hθk : RingHom.ker θ = chartIdeal P p := by
    ext f
    simp [θ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  have hDM : D ≤ 𝔮.comap θ := fun f hf => by
    have h1 := hηB f hf
    rw [evaluation_eq_zero_iff_mem_primeIdealOf hA _ hηU, hpη] at h1
    exact h1
  have hMmin : 𝔮.comap θ ∈ (chartIdeal P p).minimalPrimes := by
    refine ⟨⟨Ideal.comap_isPrime θ 𝔮, fun f hf => ?_⟩, fun J hJ hJM => ?_⟩
    · have : θ f = 0 := by rw [← RingHom.mem_ker, hθk]; exact hf
      show θ f ∈ 𝔮
      rw [this]; exact 𝔮.zero_mem
    · haveI := hJ.1
      have hk : RingHom.ker θ ≤ J := hθk ▸ hJ.2
      have hJ' : (J.map θ).IsPrime := Ideal.map_isPrime_of_surjective hθs hk
      have hle : J.map θ ≤ 𝔮 := Ideal.map_le_iff_le_comap.mpr hJM
      have h3 : 𝔮 ≤ J.map θ := h𝔮min.2 ⟨hJ', bot_le⟩ hle
      calc 𝔮.comap θ ≤ (J.map θ).comap θ := Ideal.comap_mono h3
        _ = J := by rw [Ideal.comap_map_of_surjective θ hθs, sup_eq_left]; exact le_trans (by
            rw [← RingHom.ker_eq_comap_bot]) hk
  obtain ⟨q, hq, hrel, hDq⟩ := exists_relevant_minimalPrime_of_chart hP hD p _ hMmin hDM
  exact hmin q hq hrel hDq

end

end ReciprocityTheory.AnForm.R
