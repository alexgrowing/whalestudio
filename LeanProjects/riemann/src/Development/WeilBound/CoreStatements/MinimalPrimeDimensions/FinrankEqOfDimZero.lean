import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.GenIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier
open GroundTheory.Heights₂.Heights (IsProjPrime IsHomogIdeal IsRelevant relComps localMult chowDegree reduceMod divCycle)

namespace ChowFormHeightComparison₂.CF.V

section Alg

variable {κ Ω : Type} [Field κ] [Field Ω] [Algebra κ Ω] {m : ℕ}

theorem ker_aeval_eq (τ : Fin m → Ω) (k : Fin m) (hk : τ k = 1) :
    RingHom.ker (aeval τ : MvPolynomial (Fin m) κ →ₐ[κ] Ω) = GlobalTheory.CompHt.coneIdeal κ τ ⊔ Ideal.span {X k - 1} := by
  have hcomp : ∀ g : MvPolynomial (Fin m) κ, aeval τ g =
      ∑ d ∈ Finset.range (g.totalDegree + 1), aeval τ (homogeneousComponent d g) := by
    intro g
    conv_lhs => rw [← sum_homogeneousComponent g]
    rw [map_sum]
  apply le_antisymm
  · intro g hg
    rw [RingHom.mem_ker] at hg
    set N := g.totalDegree
    set h := ∑ d ∈ Finset.range (N + 1), X k ^ (N - d) * homogeneousComponent d g with hh
    have hhom : h.IsHomogeneous N := by
      apply IsHomogeneous.sum
      intro d hd
      have hdN : N - d + d = N := by
        have := Finset.mem_range.mp hd
        omega
      have := (isHomogeneous_X_pow (R := κ) k (N - d)).mul (homogeneousComponent_isHomogeneous d g)
      rwa [hdN] at this
    have hh0 : aeval τ h = 0 := by
      simp only [hh, map_sum, map_mul, map_pow, aeval_X, hk, one_pow, one_mul]
      rw [← hcomp]
      exact hg
    have hdiff : g - h ∈ Ideal.span {X k - 1} := by
      have hg' : g = ∑ d ∈ Finset.range (N + 1), homogeneousComponent d g :=
        (sum_homogeneousComponent g).symm
      have : g - h = ∑ d ∈ Finset.range (N + 1), (1 - X k ^ (N - d)) * homogeneousComponent d g := by
        rw [hh, sub_eq_iff_eq_add, ← Finset.sum_add_distrib]
        conv_lhs => rw [hg']
        refine Finset.sum_congr rfl fun d _ => ?_
        ring
      rw [this]
      refine Ideal.sum_mem _ fun d _ => Ideal.mul_mem_right _ _ ?_
      rw [Ideal.mem_span_singleton]
      have := sub_dvd_pow_sub_pow (X k : MvPolynomial (Fin m) κ) 1 (N - d)
      rw [one_pow] at this
      rw [← neg_sub (X k ^ (N - d)) (1 : MvPolynomial (Fin m) κ)]
      exact dvd_neg.mpr this
    have hcone : h ∈ GlobalTheory.CompHt.coneIdeal κ τ :=
      (GlobalTheory.CompHt.mem_coneIdeal_of_isHomogeneous τ hhom).mpr hh0
    have : g = h + (g - h) := by ring
    rw [this]
    exact Submodule.add_mem_sup hcone hdiff
  · refine sup_le ?_ ?_
    · intro g hg
      rw [GlobalTheory.CompHt.mem_coneIdeal_iff] at hg
      rw [RingHom.mem_ker, hcomp]
      exact Finset.sum_eq_zero fun d _ => hg d
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      show _ ∈ RingHom.ker _
      rw [RingHom.mem_ker]
      simp [hk]

theorem le_ker_constantCoeff {P : Ideal (MvPolynomial (Fin m) κ)} (h : IsProjPrime P) :
    P ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin m) κ →+* κ) := by
  intro f hf
  rw [RingHom.mem_ker]
  by_contra hne
  have h0 := h.isHomog f hf 0
  rw [homogeneousComponent_zero, ← constantCoeff_eq] at h0
  exact h.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 ((Ne.isUnit hne).map C))

end Alg

variable {Z : Scheme.{0}} {B : LB Z} {m : ℕ}

theorem evaluation_resG {U V : Z.Opens} (h : V ≤ U) (z : Z) (hz : z ∈ V) (a : Γ(Z, U)) :
    Z.evaluation V z hz (resG Z h a) = Z.evaluation U z (h hz) a := by
  simp only [resG, ← Scheme.germ_residue, CommRingCat.comp_apply]
  rw [← CommRingCat.comp_apply (Z.presheaf.map (homOfLE h).op), TopCat.Presheaf.germ_res]

theorem evaluation_algX {R : Type} [CommRing R] (p : Z ⟶ Sp R) {U : Z.Opens} (z : Z) (hz : z ∈ U) (r : R) :
    Z.evaluation U z hz (algX p U r) = Z.evaluation ⊤ z trivial (algX p ⊤ r) := by
  rw [← TopForm.resG_comp_algX p (le_top : U ≤ ⊤), RingHom.comp_apply, evaluation_resG]

variable {κ : Type} [Field κ] {p : Z ⟶ Sp κ} {s : Fin m → B.Sec}

theorem ptIdeal_eq_coneIdeal (hB : B.IsLB) {k : Fin m} (t : Fin m → Γ(Z, nonzeroLocus (s k)))
    (ht : ∀ j i, resG Z (inf_le_right : nonzeroLocus (s k) ⊓ B.U i ≤ B.U i) ((s j).f i) =
      resG Z (inf_le_left : nonzeroLocus (s k) ⊓ B.U i ≤ nonzeroLocus (s k)) (t j) *
        resG Z (inf_le_right : nonzeroLocus (s k) ⊓ B.U i ≤ B.U i) ((s k).f i))
    (z : Z) (hz : z ∈ nonzeroLocus (s k)) :
    letI := ((Z.evaluation ⊤ z trivial).hom.comp (algX p ⊤)).toAlgebra
    ptIdeal p s z = GlobalTheory.CompHt.coneIdeal κ (fun j => Z.evaluation _ z hz (t j)) ∧ Z.evaluation _ z hz (t k) = 1 := by
  letI alg : Algebra κ (Z.residueField z) := ((Z.evaluation ⊤ z trivial).hom.comp (algX p ⊤)).toAlgebra
  set y : Fin m → Z.residueField z := fun j => Z.evaluation _ z hz (t j) with hy
  have key : ∀ i (hi : z ∈ B.U i) j, Z.evaluation (B.U i) z hi ((s j).f i) =
      y j * Z.evaluation (B.U i) z hi ((s k).f i) := by
    intro i hi j
    have := congrArg (fun x => Z.evaluation (nonzeroLocus (s k) ⊓ B.U i) z ⟨hz, hi⟩ x) (ht j i)
    dsimp only at this
    rw [map_mul] at this
    have e1 := evaluation_resG (Z := Z) (inf_le_right : nonzeroLocus (s k) ⊓ B.U i ≤ B.U i) z ⟨hz, hi⟩ ((s j).f i)
    have e2 := evaluation_resG (Z := Z) (inf_le_left : nonzeroLocus (s k) ⊓ B.U i ≤ nonzeroLocus (s k)) z
      ⟨hz, hi⟩ (t j)
    have e3 := evaluation_resG (Z := Z) (inf_le_right : nonzeroLocus (s k) ⊓ B.U i ≤ B.U i) z ⟨hz, hi⟩ ((s k).f i)
    simp only [hy]
    rw [← e1, ← e2, ← e3]
    exact this
  have hcone : ∀ i (hi : z ∈ B.U i), coneHom p s z i hi =
      (Polynomial.aeval (Polynomial.C (Z.evaluation (B.U i) z hi ((s k).f i)) * Polynomial.X)).toRingHom.comp
        (GlobalTheory.CompHt.coneMap κ y).toRingHom := by
    intro i hi
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [coneHom, GlobalTheory.CompHt.coneMap, evaluation_algX, Polynomial.algebraMap_apply,
        RingHom.algebraMap_toAlgebra]
    · intro j
      simp [coneHom, GlobalTheory.CompHt.coneMap, key i hi j]
      ring
  have hz' := hz
  simp only [nonzeroLocus, Opens.mem_iSup] at hz'
  obtain ⟨i₀, hb⟩ := hz'
  have hi₀ : z ∈ B.U i₀ := Z.basicOpen_le _ hb
  have ha : Z.evaluation (B.U i₀) z hi₀ ((s k).f i₀) ≠ 0 :=
    by
    rw [Ne, Scheme.evaluation_eq_zero_iff_notMem_basicOpen, not_not]
    exact hb
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · intro g hg
    have hg' := Ideal.mem_iInf.mp (Ideal.mem_iInf.mp hg i₀) hi₀
    rw [RingHom.mem_ker, hcone i₀ hi₀] at hg'
    show g ∈ RingHom.ker _
    rw [RingHom.mem_ker]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply] at hg'
    rw [← Polynomial.comp_eq_aeval, Polynomial.comp_eq_zero_iff] at hg'
    rcases hg' with h | ⟨_, h⟩
    · exact h
    · exfalso
      have := congrArg (fun q => Polynomial.coeff q 1) h
      simp at this
      exact this hb
  · intro g hg
    have hg0 : GlobalTheory.CompHt.coneMap κ y g = 0 := hg
    simp only [ptIdeal, Ideal.mem_iInf, RingHom.mem_ker]
    intro i hi
    rw [hcone i hi]
    simp [hg0]
  · have := key i₀ hi₀ k
    have h1 : (1 : Z.residueField z) * Z.evaluation (B.U i₀) z hi₀ ((s k).f i₀) =
        y k * Z.evaluation (B.U i₀) z hi₀ ((s k).f i₀) := by
      rw [one_mul]
      exact this
    exact (mul_right_cancel₀ ha h1).symm

theorem isComb_single {R : Type} [CommRing R] (p : Z ⟶ Sp R) (s : Fin m → B.Sec) (k : Fin m) :
    IsComb p s (Pi.single k 1) (s k) := by
  intro i
  simp [Pi.single_apply, apply_ite, ite_mul]

theorem linForm_single {R : Type} [CommRing R] (k : Fin m) :
    GroundTheory.Heights₂.Heights.linForm (Pi.single k (1 : R)) = X k := by
  simp [GroundTheory.Heights₂.Heights.linForm, Pi.single_apply]

variable [IsIntegral Z]

theorem dim_add_one_le (h1 : StPts) (hE : Emb p s) :
    topologicalKrullDim Z + 1 ≤ ringKrullDim (MvPolynomial (Fin m) κ ⧸ ptIdeal p s (genericPoint Z)) := by
  classical
  set I := ptIdeal p s (genericPoint Z) with hIdef
  obtain ⟨hprime, hspec, -, -⟩ := h1 κ Z p B m s hE
  let gen : IrreducibleCloseds Z → Z := fun S => S.isIrreducible.genericPoint
  have hgen : ∀ S : IrreducibleCloseds Z, closure {gen S} = (S : Set Z) := by
    intro S
    have := S.isIrreducible.isGenericPoint_genericPoint_closure
    rw [S.isClosed.closure_eq] at this
    exact this
  have hle : ∀ S T : IrreducibleCloseds Z,
      (T : Set Z) ⊆ S ↔ ptIdeal p s (gen S) ≤ ptIdeal p s (gen T) := by
    intro S T
    rw [← hspec (gen S) (gen T), specializes_iff_closure_subset, hgen, hgen]
  have hI : ∀ S : IrreducibleCloseds Z, I ≤ ptIdeal p s (gen S) := fun S =>
    (hspec _ _).mp ((genericPoint_spec Z).specializes (Set.mem_univ _))
  have hM : ∀ S : IrreducibleCloseds Z,
      ptIdeal p s (gen S) < RingHom.ker (constantCoeff : MvPolynomial (Fin m) κ →+* κ) := by
    intro S
    refine lt_of_le_of_ne (le_ker_constantCoeff (hprime _)) fun h => ?_
    obtain ⟨j, hj⟩ := (hprime (gen S)).isRelevant
    apply hj
    rw [h, RingHom.mem_ker, constantCoeff_X]
  have hMI : I ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin m) κ →+* κ) :=
    le_ker_constantCoeff (hprime _)
  haveI : Nonempty (IrreducibleCloseds Z) :=
    ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩⟩
  let g : WithTop (IrreducibleCloseds Z)ᵒᵈ →
      PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin m) κ) (I : Set (MvPolynomial (Fin m) κ)) :=
    fun x => WithTop.recTopCoe
      ⟨⟨RingHom.ker (constantCoeff : MvPolynomial (Fin m) κ →+* κ), RingHom.ker_isPrime _⟩,
        (PrimeSpectrum.mem_zeroLocus _ _).mpr hMI⟩
      (fun S => ⟨⟨ptIdeal p s (gen (OrderDual.ofDual S)), (hprime _).isPrime⟩,
        (PrimeSpectrum.mem_zeroLocus _ _).mpr (hI _)⟩) x
  have hg : StrictMono g := by
    intro a b hab
    induction a using WithTop.recTopCoe with
    | top => exact absurd hab (not_top_lt)
    | coe S =>
      induction b using WithTop.recTopCoe with
      | top =>
        show (⟨ptIdeal p s (gen (OrderDual.ofDual S)), _⟩ : PrimeSpectrum _) <
          ⟨RingHom.ker (constantCoeff : MvPolynomial (Fin m) κ →+* κ), _⟩
        exact hM _
      | coe T =>
        rw [WithTop.coe_lt_coe] at hab
        have hab' : OrderDual.ofDual T < OrderDual.ofDual S := hab
        show (⟨ptIdeal p s (gen (OrderDual.ofDual S)), _⟩ : PrimeSpectrum _) <
          ⟨ptIdeal p s (gen (OrderDual.ofDual T)), _⟩
        refine lt_of_le_not_ge ((hle _ _).mp hab'.le) fun h => ?_
        exact hab'.not_ge ((hle _ _).mpr h)
  calc topologicalKrullDim Z + 1 = Order.krullDim (WithTop (IrreducibleCloseds Z)ᵒᵈ) := by
        rw [Order.krullDim_WithTop, Order.krullDim_orderDual]
        rfl
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin m) κ) (I : Set _)) :=
        Order.krullDim_le_of_strictMono g hg
    _ = ringKrullDim (MvPolynomial (Fin m) κ ⧸ I) := (ringKrullDim_quotient I).symm

private theorem algX_strHom_top {κ : Type} [Field κ] {Z : Scheme.{0}} [Algebra κ Γ(Z, ⊤)] :
    algX (strHom κ Z) ⊤ = algebraMap κ Γ(Z, ⊤) := by
  ext r
  rw [algebraMap_eq_strHom]
  simp [algX, Scheme.Hom.appLE, Scheme.Hom.appTop]
  rfl

private theorem evaluation_genericPoint_eq_zero_iff {Z : Scheme.{0}} [IsIntegral Z] {U : Z.Opens}
    (hU : genericPoint Z ∈ U) (a : Γ(Z, U)) :
    Z.evaluation U (genericPoint Z) hU a = 0 ↔ a = 0 := by
  rw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen]
  constructor
  · intro h
    by_contra ha
    apply h
    have hne : Z.basicOpen a ≠ ⊥ := by
      rwa [Ne, basicOpen_eq_bot_iff]
    show genericPoint Z ∈ (Z.basicOpen a : Set Z)
    rw [(genericPoint_spec Z).mem_open_set_iff (Z.basicOpen a).isOpen, Set.univ_inter]
    rwa [Ne, ← Opens.not_nonempty_iff_eq_bot, not_not] at hne
  · rintro rfl
    simp

private theorem resG_bijective_of_eq_top {Z : Scheme.{0}} {V : Z.Opens} (hV : V = ⊤) :
    Function.Bijective (resG Z (le_top : V ≤ ⊤)) := by
  subst hV
  have : (homOfLE (le_top : (⊤ : Z.Opens) ≤ ⊤)) = 𝟙 _ := Subsingleton.elim _ _
  simp only [resG, this, op_id, CategoryTheory.Functor.map_id]
  exact Function.bijective_id

theorem finrank_eq_of_dim_zero [Algebra κ Γ(Z, ⊤)] {s : Fin m → B.Sec} (hE : Emb (strHom κ Z) s)
    (hd : topologicalKrullDim Z ≤ 0) {k : Fin m} (hk : genericPoint Z ∈ nonzeroLocus (s k)) :
    Module.finrank κ (MvPolynomial (Fin m) κ ⧸ (ptIdeal (strHom κ Z) s (genericPoint Z) ⊔ Ideal.span {X k - 1})) =
      Module.finrank κ Γ(Z, ⊤) := by
  classical
  set η := genericPoint Z
  have hall : ∀ z : Z, z = η := by
    intro z
    have hmax := Order.krullDim_nonpos_iff_forall_isMax.mp hd
    let Sz : IrreducibleCloseds Z := ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
    let U : IrreducibleCloseds Z := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩
    have h1 : Sz = U := (hmax Sz).eq_of_le (show (Sz : Set Z) ⊆ U from Set.subset_univ _)
    have h2 : IsGenericPoint z Set.univ := by
      have := congrArg (fun S : IrreducibleCloseds Z => (S : Set Z)) h1
      exact this
    exact h2.eq (genericPoint_spec Z)
  have hW : nonzeroLocus (s k) = ⊤ := eq_top_iff.mpr fun z _ => (hall z) ▸ hk
  obtain ⟨-, t, hsurj, ht⟩ := hE.chart k
  obtain ⟨hJ, htk⟩ := ptIdeal_eq_coneIdeal (p := strHom κ Z) hE.isLB t ht η hk
  letI alg : Algebra κ (Z.residueField η) :=
    ((Z.evaluation ⊤ η trivial).hom.comp (algX (strHom κ Z) ⊤)).toAlgebra
  have hinj : Function.Injective (Z.evaluation (nonzeroLocus (s k)) η hk).hom :=
    (injective_iff_map_eq_zero _).mpr fun a ha => (evaluation_genericPoint_eq_zero_iff hk a).mp ha
  have hker : RingHom.ker (eval₂Hom (algX (strHom κ Z) (nonzeroLocus (s k))) t) =
      ptIdeal (strHom κ Z) s η ⊔ Ideal.span {X k - 1} := by
    rw [hJ, ← ker_aeval_eq _ k htk]
    have hcomp : (Z.evaluation (nonzeroLocus (s k)) η hk).hom.comp (eval₂Hom (algX (strHom κ Z) (nonzeroLocus (s k))) t) =
        (aeval (fun j => Z.evaluation (nonzeroLocus (s k)) η hk (t j)) :
          MvPolynomial (Fin m) κ →ₐ[κ] Z.residueField η).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [evaluation_algX, RingHom.algebraMap_toAlgebra]
      · intro j
        simp
    rw [← RingHom.ker_comp_of_injective _ hinj, hcomp]
    rfl
  let ρ : Γ(Z, ⊤) ≃+* Γ(Z, nonzeroLocus (s k)) :=
    RingEquiv.ofBijective (resG Z (le_top : nonzeroLocus (s k) ≤ ⊤)) (resG_bijective_of_eq_top hW)
  let φ : (MvPolynomial (Fin m) κ ⧸ (ptIdeal (strHom κ Z) s η ⊔ Ideal.span {X k - 1})) ≃+* Γ(Z, ⊤) :=
    (Ideal.quotEquivOfEq hker.symm).trans ((RingHom.quotientKerEquivOfSurjective hsurj).trans ρ.symm)
  have hφ : ∀ c : κ, φ (algebraMap κ _ c) = algebraMap κ Γ(Z, ⊤) c := by
    intro c
    rw [← algX_strHom_top]
    simp only [φ, RingEquiv.trans_apply, RingEquiv.symm_apply_eq]
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
    simp only [ρ, RingEquiv.ofBijective_apply, MvPolynomial.algebraMap_eq, eval₂Hom_C]
    rw [← TopForm.resG_comp_algX (strHom κ Z) (le_top : nonzeroLocus (s k) ≤ ⊤), RingHom.comp_apply]
  exact (AlgEquiv.ofRingEquiv (f := φ) hφ).toLinearEquiv.finrank_eq

end ChowFormHeightComparison₂.CF.V
