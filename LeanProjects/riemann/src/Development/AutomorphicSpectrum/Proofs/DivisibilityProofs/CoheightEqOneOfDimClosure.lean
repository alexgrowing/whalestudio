import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimLeZeroOfSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.InterNumEqSumLengthMulInterNumRed
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.IntersectionMultiplicitySection

open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.QCoh

theorem coheight_eq_one_of_dim_closure {X : Scheme.{0}} {n : ℕ}
    (hX : topologicalKrullDim X ≤ (n + 1 : ℕ)) {w : X} (hw : ¬ IsMax w)
    (hd : topologicalKrullDim (closure ({w} : Set X)) = n) : Order.coheight w = 1 := by
  have key : ∀ {a b : X}, a < b → topologicalKrullDim (closure ({a} : Set X)) + 1 ≤
      topologicalKrullDim (closure ({b} : Set X)) := by
    intro a b hab
    refine topologicalKrullDim_add_one_le isClosed_closure isClosed_closure
      fun x hx => ⟨b, subset_closure rfl, fun hb => ?_, ?_⟩
    · exact hab.not_ge (specializes_iff_mem_closure.2 hb)
    · have h1 : b ⤳ a := hab.le
      have h2 : a ⤳ x := specializes_iff_mem_closure.2 hx
      exact h1.trans h2
  have hle : ∀ b : X, topologicalKrullDim (closure ({b} : Set X)) ≤ topologicalKrullDim X :=
    fun b => Topology.IsInducing.subtypeVal.topologicalKrullDim_le
  refine le_antisymm ((Order.coheight_le_coe_iff (n := 1)).2 fun y hy => ?_) ?_
  · by_contra hc
    have hy0 : ¬ IsMax y := fun h => hc (by rw [Order.coheight_eq_zero.2 h]; exact zero_lt_one)
    obtain ⟨b, hyb⟩ := not_isMax_iff.1 hy0
    have h := ((add_le_add (hd ▸ key hy : (n : WithBot ℕ∞) + 1 ≤ _) (le_refl (1 : WithBot ℕ∞))).trans
      (key hyb)).trans ((hle b).trans hX)
    norm_cast at h
    omega
  · rw [ENat.one_le_iff_ne_zero]
    exact fun h => hw (Order.coheight_eq_zero.1 h)

open scoped Pointwise

theorem mult_divOfSec_eq_length_cut {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {M : LB X} (hM : M.IsLB) (s : M.Sec) (hs : genericPoint X ∈ nonzeroLocus s) {w : X}
    (hw : Order.coheight w = 1) :
    (divOfSec hM s hs).mult w = ((Module.length (X.presheaf.stalk w)
      ((cut (structureModule X) hM s).presheaf.stalk w :)).toNat : ℤ) := by
  obtain ⟨i, hi⟩ := exists_chart hM w
  obtain ⟨q⟩ := CutDegree.nonempty_stalk_cut_equiv (structureModule X) hM s i hi
  set g := X.presheaf.germ _ w hi (s.f i)
  have e1 : Module.length (X.presheaf.stalk w) (X.presheaf.stalk w ⧸ Ideal.span {g}) =
      Module.length (X.presheaf.stalk w) (QuotSMulTop g (X.presheaf.stalk w)) := by
    refine (Submodule.quotEquivOfEq (Ideal.span {g}) (g • (⊤ : Submodule (X.presheaf.stalk w)
      (X.presheaf.stalk w))) ?_).length_eq
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  rw [mult_divOfSec hw hi, ← q.length_eq,
    (QuotSMulTop.congr g (structureModuleStalkEquiv w)).length_eq, ← e1]

theorem mult_divOfSec_ne_zero {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {M : LB X} (hM : M.IsLB) (s : M.Sec) (hs : genericPoint X ∈ nonzeroLocus s) {w : X}
    (hw : Order.coheight w = 1) (hws : w ∉ nonzeroLocus s) : (divOfSec hM s hs).mult w ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_chart hM w
  have : Ring.KrullDimLE 1 (X.presheaf.stalk w) := krullDimLE_of_coheight_le hw.le
  have e := algebraMap_germ hi (s.f i)
  have hg0 : X.presheaf.germ _ w hi (s.f i) ≠ 0 := fun h0 => fnOf_sec_ne_zero hs (gen_mem hi)
    (e.symm.trans ((congrArg _ h0).trans (map_zero _)))
  have htop := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hg0)
  have hu : ¬ IsUnit (X.presheaf.germ _ w hi (s.f i)) := fun h =>
    hws ((mem_nonzeroLocus_iff s i hi).2 ((Scheme.mem_basicOpen _ _ _ _).2 h))
  rw [mult_divOfSec hw hi, Nat.cast_ne_zero, Ne, ENat.toNat_eq_zero, not_or]
  refine ⟨fun h0 => hu ?_, htop⟩
  rw [Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top] at h0
  exact h0

theorem interNum_cons_eq_finsum_mult : ∀ (κ : Type) [Field κ] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [Algebra κ Γ(X, ⊤)], IsProjOver (strHom κ X) → ∀ (n : ℕ), topologicalKrullDim X ≤ (n + 1 : ℕ) → ∀ (M : LB X) (hM : M.IsLB) (P : Fin n → LB X), (∀ i, (P i).IsLB) → ∀ (s : M.Sec) (hs : genericPoint X ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s), interNum κ (structureModule X) (Fin.cons M P : Fin (n + 1) → LB X) = ∑ᶠ w, (divOfSec hM s hs).mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
  intro κ _ X _ _ _ hproj n hX M hM P hP s hs
  have hf := algebraMap_eq_strHom κ X
  have := isNoetherian_of_isProjOver hproj
  have : IsProper (strHom κ X) := (isProper_and_exists_isAmpleLB_of_isProjOver hproj).1
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hproj
  have hmono := (mono_cutHom_structureModule_iff hM s).2 hs
  have hfin : FiniteCohTwists κ (structureModule X) := hH.finiteCohTwists hf _
  rw [interNum_cons_eq_interNum_cut hM s hP hfin]
  have hsupp : suppDim (cut (structureModule X) hM s) ≤ (Fintype.card (Fin n) : ℕ) := by
    rw [Fintype.card_fin]
    exact suppDim_cut_le _ hM s (by rwa [QCoh.suppDim_structureModule])
  have hfs := (divOfSec hM s hs).finite_support_mult
  have hS : ∀ w ∈ support (cut (structureModule X) hM s),
      topologicalKrullDim (closure ({w} : Set X)) = (Fintype.card (Fin n) : ℕ) → w ∈ hfs.toFinset := by
    intro w hw hd
    rw [Fintype.card_fin] at hd
    rw [support_cut, QCoh.support_structureModule] at hw
    have hmax : ¬ IsMax w := fun h => hw.2 ((h (genericPoint_specializes w) :
      w ⤳ genericPoint X).mem_open (nonzeroLocus s).isOpen hs)
    have hc := coheight_eq_one_of_dim_closure hX hmax hd
    simpa using mult_divOfSec_ne_zero hM s hs hc hw.2
  rw [GlobalTheory.CompanionTheory.Ar.IntersectionNumberLength.interNum_eq_sum_length_mul_interNumRed κ X hproj (Fin n) P hP _ hsupp hfs.toFinset hS,
    finsum_eq_sum_of_support_subset _ (s := hfs.toFinset) ?_]
  · refine Finset.sum_congr rfl fun w hw => ?_
    have hw' : (divOfSec hM s hs).mult w ≠ 0 := by simpa using hw
    rw [mult_divOfSec_eq_length_cut hM s hs (CartierDiv.coheight_eq_one_of_mult_ne_zero hw')]
  · intro w hw
    simpa using Function.support_mul_subset_left _ _ hw

end GlobalTheory.CompanionTheory.Ar.IntersectionMultiplicitySection
