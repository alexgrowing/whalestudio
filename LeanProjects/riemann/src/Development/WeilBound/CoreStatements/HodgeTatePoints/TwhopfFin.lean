import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicIntAlgebraOfIsAdicCompleteMatrixUnique
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFinOpenSubOfFinite
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinitePointExtendsSection
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.HtPt.Twhopf

theorem finite_part : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f], ∃ U : X.Opens, IsFinite (U.ι ≫ f) ∧ ∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U := by
  intro R _ _ X f _ _ _ _
  exact ⟨GlobalTheory.finitePart f, GlobalTheory.isFinite_finitePart (R := CommRingCat.of R) f,
    GlobalTheory.mem_finitePart_of_eq_closedPoint (R := CommRingCat.of R) f⟩

theorem finite_le : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (U U' : X.Opens), IsFinite (U.ι ≫ f) → (∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U') → U ≤ U' := by
  intro R _ _ X f U U' hU hU' x hx
  exact (GlobalTheory.preimage_eq_top_of_closedFibre_subset (R := CommRingCat.of R) f U' hU' U.ι).ge
    (Set.mem_univ ⟨x, hx⟩)

theorem mem_of_finite {R : Type} [CommRing R] [IsLocalRing R]
    {X : Over (Spec (CommRingCat.of R))} (W : X.left.Opens)
    (hW : ∀ x : X.left, X.hom x = IsLocalRing.closedPoint R → x ∈ W)
    (Y : Over (Spec (CommRingCat.of R))) (hY : IsFinite Y.hom) (h : Y ⟶ X) (z : Y.left) :
    h.left z ∈ W := by
  haveI : IsFinite (h.left ≫ X.hom) := by rw [Over.w h]; exact hY
  exact (GlobalTheory.preimage_eq_top_of_closedFibre_subset (R := CommRingCat.of R) X.hom W hW h.left).ge
    (Set.mem_univ z)

theorem finite_sub : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (T : Type) [CommGroup T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), IsFinite (U.ι ≫ Γ.G.hom) → (∀ x : Γ.G.left, Γ.G.hom x = IsLocalRing.closedPoint R → x ∈ U) → Γ.IsFinOpenSub U := by
  intro R _ _ _ T _ Γ U hfin hU
  haveI := hfin
  have hV : IsFinite (openOver Γ.G U).hom := hfin
  haveI := hV
  refine ⟨hfin, ?_, ?_, ?_⟩
  · intro x
    refine mem_of_finite U hU (𝟙_ _) ?_ η[Γ.G] x
    show IsFinite (𝟙 _)
    infer_instance
  · intro S x y hx hy z
    obtain ⟨x', rfl⟩ := exists_factor_openIncl U x hx
    obtain ⟨y', rfl⟩ := exists_factor_openIncl U y hy
    have hP : IsFinite (openOver Γ.G U ⊗ openOver Γ.G U).hom := by
      rw [Over.tensorObj_hom]
      infer_instance
    have key := mem_of_finite U hU _ hP
      ((fst _ _ ≫ openIncl Γ.G U) * (snd _ _ ≫ openIncl Γ.G U))
    have heq : x' ≫ openIncl Γ.G U * y' ≫ openIncl Γ.G U =
        lift x' y' ≫ ((fst _ _ ≫ openIncl Γ.G U) * (snd _ _ ≫ openIncl Γ.G U)) := by
      rw [comp_mul]
      simp
    rw [heq]
    simpa using key ((lift x' y').left z)
  · intro S x hx z
    obtain ⟨x', rfl⟩ := exists_factor_openIncl U x hx
    have key := mem_of_finite U hU _ hV (openIncl Γ.G U)⁻¹
    have heq : (x' ≫ openIncl Γ.G U)⁻¹ = x' ≫ (openIncl Γ.G U)⁻¹ := by
      simp [Hom.inv_def]
    rw [heq]
    simpa using key (x'.left z)

theorem mem_iff_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), IsFinite (U.ι ≫ Γ.G.hom) → (∀ g : Γ.G.left, Γ.G.hom g = IsLocalRing.closedPoint R → g ∈ U) → ∀ t, (⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U ↔ ∃ σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G, toUnit (genPt R) ≫ σ = Γ.pt t) := by
  intro R _ _ _ _ T _ _ Γ U hfin hU t
  constructor
  · intro ht
    obtain ⟨σ, -, hσ⟩ := exists_section_of_generic_point R T Γ U hfin t ht
    exact ⟨σ, hσ⟩
  · rintro ⟨σ, hσ⟩ z _
    have key := mem_of_finite U hU (𝟙_ _) (show IsFinite (𝟙 _) from inferInstance) σ
      ((toUnit (genPt R)).left z)
    rw [← hσ]
    simpa using key

open Polynomial in

theorem exists_root_near (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)]
    (a₀ : V) (n : ℕ) : ∀ f : V[X], f.Monic → f.natDegree = n → f.eval a₀ ∈ IsLocalRing.maximalIdeal V →
      ∃ a, f.IsRoot a ∧ a - a₀ ∈ IsLocalRing.maximalIdeal V := by
  induction n with
  | zero =>
    intro f hf hn h
    rw [hf.natDegree_eq_zero.1 hn, eval_one] at h
    exact absurd ((Ideal.eq_top_iff_one _).2 h) (IsLocalRing.maximalIdeal.isMaximal V).ne_top
  | succ n ih =>
    intro f hf hn h
    have hinj := IsFractionRing.injective V (FractionRing V)
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective (FractionRing V) hinj f
      (by rw [degree_eq_natDegree hf.ne_zero, hn]; exact_mod_cast n.succ_ne_zero)
    obtain ⟨r, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 (⟨f, hf, by rwa [← aeval_def]⟩ : IsIntegral V x)
    have hr : f.IsRoot r := hinj (by rw [map_zero, ← hx, aeval_algebraMap_apply_eq_algebraMap_eval])
    obtain ⟨g, rfl⟩ := dvd_iff_isRoot.2 hr
    have hg : g.Monic := (monic_X_sub_C r).of_mul_monic_left hf
    rw [eval_mul] at h
    rcases (IsLocalRing.maximalIdeal.isMaximal V).isPrime.mem_or_mem h with h | h
    · refine ⟨r, hr, ?_⟩
      have := neg_mem h
      simpa using this
    · have hd : g.natDegree = n := by
        rw [(monic_X_sub_C r).natDegree_mul hg, natDegree_X_sub_C] at hn
        omega
      obtain ⟨a, ha, ha'⟩ := ih g hg hd h
      exact ⟨a, ha.dvd (dvd_mul_left _ _), ha'⟩

theorem henselian_of_algClosed : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)], HenselianLocalRing V := by
  intro V _ _ _ _
  exact ⟨fun f hf a₀ h _ => exists_root_near V a₀ _ f hf rfl h⟩

theorem padic_alg : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O), Nonempty (Algebra ℤ_[p] O) ∧ HenselianLocalRing O ∧ IsIntegrallyClosed O ∧ ValuationRing O ∧ IsAlgClosed (FractionRing O) ∧ IsFractionRing O C := by
  intro p _ C _ _ _ v O _ _ _ hv _ hO
  haveI := hO
  haveI hval : ValuationRing O := ValuationRing.of_integers v hv
  haveI hfr : IsFractionRing O C := hv.isFractionRing
  haveI hac : IsAlgClosed (FractionRing O) :=
    IsAlgClosed.of_ringEquiv C _ (FractionRing.algEquiv O C).symm.toRingEquiv
  exact ⟨(GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique p O).1,
    henselian_of_algClosed O, inferInstance, hval, hac, hfr⟩

theorem prime_eq_bot_or_max : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] [IsLocalRing O], v.Integers O → ∀ P : Ideal O, P.IsPrime → P = ⊥ ∨ P = IsLocalRing.maximalIdeal O := by
  intro C _ v O _ _ _ _ hv P hP
  by_cases h0 : P = ⊥
  · exact .inl h0
  right
  refine le_antisymm (IsLocalRing.le_maximalIdeal hP.ne_top) fun x hx => ?_
  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have hx1 : v (algebraMap O C x) < 1 :=
    lt_of_le_of_ne (hv.map_le_one x) fun h => hx (hv.isUnit_of_one' h)
  have ha : 0 < v (algebraMap O C a) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff v).2 ((map_ne_zero_iff _ hv.hom_inj).2 ha0))
  obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one ha hx1
  have hd : a ∣ x ^ n := hv.dvd_of_le (by rw [map_pow, map_pow]; exact hn.le)
  exact hP.mem_of_pow_mem n (P.mem_of_dvd hd haP)

end PositivityTheory.HtPt.Twhopf
