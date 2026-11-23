import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.UnifJac

theorem valT_comp {T : Type} [CommRing T] {X Y : Scheme.{0}} (w : Sp T ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (f : Γ(Y, U)) : valT (w ≫ φ) U f = valT w (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by
  unfold valT
  by_cases h : ⊤ ≤ w ⁻¹ᵁ (φ ⁻¹ᵁ U)
  · rw [dif_pos h, dif_pos (show ⊤ ≤ (w ≫ φ) ⁻¹ᵁ U from h)]
    rfl
  · rw [dif_neg h, dif_neg (show ¬ ⊤ ≤ (w ≫ φ) ⁻¹ᵁ U from h)]

variable {A : Over (Sp ℂ)} [GrpObj A]

theorem translate_left {T : Over (Sp ℂ)} (z : 𝟙_ (Over (Sp ℂ)) ⟶ A) (v : T ⟶ A) :
    ((toUnit T ≫ z) * v).left = v.left ≫ ((toUnit A ≫ z) * 𝟙 A).left := by
  rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem le_of_isTangent {v : epsR ℂ ⟶ A} (hv : IsTangent v) (U : A.left.Opens)
    (h : ⊤ ≤ η[A].left ⁻¹ᵁ U) : ⊤ ≤ v.left ⁻¹ᵁ U := by
  intro p _
  have hp : p = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom (IsLocalRing.closedPoint ℂ) := by
    have : Subsingleton (PrimeSpectrum (DualNumber ℂ)) := by
      refine ⟨fun a b => ?_⟩
      have hn : ∀ c : PrimeSpectrum (DualNumber ℂ), c.asIdeal = IsLocalRing.maximalIdeal _ := fun c => by
        refine le_antisymm (IsLocalRing.le_maximalIdeal c.isPrime.ne_top) ?_
        rw [DualNumber.maximalIdeal_eq_span_singleton_eps, Ideal.span_singleton_le_iff_mem]
        exact c.isPrime.mem_of_pow_mem 2 (by rw [sq, DualNumber.eps_mul_eps]; exact zero_mem _)
      exact PrimeSpectrum.ext ((hn a).trans (hn b).symm)
    exact Subsingleton.elim (α := PrimeSpectrum (DualNumber ℂ)) _ _
  have h1 : η[A].left (IsLocalRing.closedPoint ℂ) ∈ U := h (show _ ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  rw [← hv] at h1
  rw [hp]
  exact h1

variable {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_zero : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem

theorem ex_translate (z w : Fin g → ℂ) :
    (u.ex w).left ≫ ((toUnit A ≫ u.ex z) * 𝟙 A).left = (u.ex (z + w)).left := by
  rw [← translate_left, u.ex_add, toUnit_unique (toUnit (𝟙_ (Over (Sp ℂ)))) (𝟙 _), Category.id_comp]

theorem snd_valT_translate {v : epsR ℂ ⟶ A} (hv : IsTangent v) {w : Fin g → ℂ} (hd : u.IsDiff w v)
    (z : Fin g → ℂ) (U : A.left.Opens) (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ U) (f : Γ(A.left, U)) :
    TrivSqZeroExt.snd (valT (T := DualNumber ℂ) ((toUnit (epsR ℂ) ≫ u.ex z) * v).left U f) =
      fderiv ℂ (fun y => valAt' (u.ex y).left U f) z w := by
  have h0 : ⊤ ≤ η[A].left ⁻¹ᵁ (((toUnit A ≫ u.ex z) * 𝟙 A).left ⁻¹ᵁ U) := by
    have e := ex_translate u z 0
    rw [add_zero, ex_zero] at e
    rw [← e] at hz
    have e1 : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A) = η[A] := by
      rw [Hom.one_def, toUnit_unique (toUnit (𝟙_ (Over (Sp ℂ)))) (𝟙 _), Category.id_comp]
    rw [e1] at hz
    exact hz
  have h1 := le_of_isTangent hv _ h0
  rw [translate_left]
  refine (congrArg _ (valT_comp _ _ _ _)).trans ?_
  refine (congrArg TrivSqZeroExt.snd (dif_pos h1)).trans ((hd _ h1 _).trans ?_)
  have e : (fun y => valAt' (u.ex y).left (((toUnit A ≫ u.ex z) * 𝟙 A).left ⁻¹ᵁ U)
      ((((toUnit A ≫ u.ex z) * 𝟙 A).left.app U).hom f)) = fun y => valAt' (u.ex (z + y)).left U f := by
    funext y
    rw [← ex_translate]
    exact (valT_comp (T := ℂ) _ _ _ _).symm
  rw [e, fderiv_comp_add_left (f := fun y => valAt' (u.ex y).left U f), add_zero]

theorem fderiv_val (c : L.ι) (f : Γ(A.left, L.U c)) (F : (Fin g → ℂ) → ℂ) (hF : Differentiable ℂ F) (n : ℕ)
    (hf : ∀ y, ⊤ ≤ (u.ex y).left ⁻¹ᵁ L.U c → valAt' (u.ex y).left (L.U c) f = F y * u.fr c y ^ n)
    (z : Fin g → ℂ) (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U c) (h0 : F z = 0) (w : Fin g → ℂ) :
    fderiv ℂ (fun y => valAt' (u.ex y).left (L.U c) f) z w = u.fr c z ^ n * fderiv ℂ F z w := by
  have hn := (u.hol (L.U c) f).1.mem_nhds hz
  have e : (fun y => valAt' (u.ex y).left (L.U c) f) =ᶠ[nhds z] fun y => F y * u.fr c y ^ n :=
    Filter.eventually_of_mem hn hf
  have hd : DifferentiableAt ℂ (fun y => u.fr c y ^ n) z := ((u.fr_hol c).differentiableAt hn).pow n
  rw [e.fderiv_eq, fderiv_fun_mul (hF z) hd, h0]
  simp

end GlobalTheory.UnifJac

namespace GlobalTheory

open UnifJac in

theorem unif_value_jac_zeros : ThetaUnifAV → ∀ (g : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (n : ℕ) (s : Fin x.P.g → RR x n) (F : Fin x.P.g → (Fin g → ℂ) → ℂ) (z : Fin g → ℂ) (c : x.P.L.ι), Wit x h u τ a b → (∀ i, Differentiable ℂ (F i) ∧ FnPw x u (s i) (F i)) → ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U c → (∀ i, valT (T := ℂ) (u.ex z).left (x.P.L.U c) ((s i).f c) = F i z * u.fr c z ^ n) ∧ ((∀ i, F i z = 0) → jac x s (u.ex z) c = u.fr c z ^ (g * n) * (Matrix.of fun i k : Fin x.P.g => (2 * Real.pi * Complex.I)⁻¹ * fderiv ℂ (F i) z (Pi.single (k.cast h) 1)).det) ∧ ∀ (d : ℕ) (zs : Fin d → Fin g → ℂ), (∀ y, (∀ i, F i y = 0) → ∃ a, ∃ e ∈ u.Λ, y = zs a + e) → ∀ y : x.P.A.left, (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ a, ∃ p : Sp ℂ, (u.ex (zs a)).left p = y := by
  intro _ g x h u τ a b n s F z c hW hF hz
  refine ⟨fun i => (hF i).2 c z hz, fun h0 => ?_, fun d zs hzs y hy => ?_⟩
  · subst h
    unfold jac
    rw [mul_comm x.P.g n, pow_mul, show (u.fr c z ^ n) ^ x.P.g = (u.fr c z ^ n) ^ Fintype.card (Fin x.P.g) by
      rw [Fintype.card_fin], ← Matrix.det_smul]
    congr 1
    ext i k
    have hd := hW.2.2.2.2.2 k
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    refine (snd_valT_translate u (x.basis.1 k) hd z _ hz _).trans ?_
    refine (fderiv_val u c _ (F i) (hF i).1 n ((hF i).2 c) z hz (h0 i) _).trans ?_
    rw [show (Pi.single k (2 * Real.pi * Complex.I)⁻¹ : Fin x.P.g → ℂ) =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • Pi.single k 1 by rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one], map_smul]
    rfl
  · haveI := x.P.isAb.smooth
    by_contra hne
    have hcl : IsClosed {y : x.P.A.left | ∃ a, ∃ p : Sp ℂ, (u.ex (zs a)).left p = y} := by
      have : {y : x.P.A.left | ∃ a, ∃ p : Sp ℂ, (u.ex (zs a)).left p = y} =
          ⋃ a, Set.range (u.ex (zs a)).left := by
        ext y; simp
      rw [this]
      refine isClosed_iUnion_of_finite fun a => ?_
      haveI := x.P.isAb.proper
      have : IsClosedImmersion (u.ex (zs a)).left := by
        have hw : (u.ex (zs a)).left ≫ x.P.A.hom = 𝟙 _ := Over.w _
        have : IsClosedImmersion ((u.ex (zs a)).left ≫ x.P.A.hom) := by rw [hw]; infer_instance
        exact IsClosedImmersion.of_comp _ x.P.A.hom
      exact (u.ex (zs a)).left.isClosedEmbedding.isClosed_range
    have hcz : IsClosed {y : x.P.A.left | ∀ i, y ∉ Out.nonzeroLocus (s i)} := by
      rw [Set.setOf_forall]
      exact isClosed_iInter fun i => (Out.nonzeroLocus (s i)).isOpen.isClosed_compl
    obtain ⟨q, hq, hqZ⟩ := ComplexPoints.exists_point_mem x.P.A.hom
      (hcz.isLocallyClosed.inter hcl.isOpen_compl.isLocallyClosed) ⟨y, hy, hne⟩
    obtain ⟨w, hw⟩ := u.ex_onto (Over.homMk q hq)
    have hw' : (u.ex w).left = q := congrArg (fun φ => φ.left) hw
    let p : Sp ℂ := IsLocalRing.closedPoint ℂ
    obtain ⟨j, hj⟩ : ∃ j, q p ∈ x.P.L.U j :=
      TopologicalSpace.Opens.mem_iSup.1 (by rw [x.P.isLB.cover]; trivial)
    have hj' : ⊤ ≤ q ⁻¹ᵁ x.P.L.U j := (ComplexPoints.top_le_preimage_iff q _ p).2 hj
    obtain ⟨a', e, he, hwe⟩ := hzs w fun i => by
      by_contra hi
      refine (hqZ p).1 i (TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_⟩)
      refine (ComplexPoints.top_le_preimage_iff q _ p).1
        ((ComplexPoints.top_le_preimage_basicOpen_iff q _ hj' _).2 ?_)
      have hv := (hF i).2 j w (by rw [hw']; exact hj')
      rw [hw'] at hv
      exact ((dif_pos hj').symm.trans hv).trans_ne (mul_ne_zero hi (pow_ne_zero _ (u.fr_ne j w (by rw [hw']; exact hj'))))
    refine (hqZ p).2 ⟨a', p, ?_⟩
    rw [← hw', hwe, u.ex_add, (u.ker e).2 he, _root_.mul_one]

end GlobalTheory

end
