import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.SlopeMaxOpenOfHookTwoLeV
import Formalism.LocalToGlobal.GlobalTheory.GL4.PTenFrames

open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.BasicNotions.SkeletonIndexLemmas Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions.flipTwoThree
open Formalism.LFunctionChainParameters.slopeLatticeData (FinPl)

structure ZBasis {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) where
  J0 : Type
  [fin : Fintype J0]
  [dec : DecidableEq J0]
  bZ : J0 → MvPolynomial (ι × Fin n × Fin n) ℤ
  span_eq : Submodule.span ℤ (Set.range bZ) = Submodule.span ℤ
    {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) ℤ, (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧ p = Formalism.MainNotions.flipTwoThree.ten f}
  li : ∀ (F : Type) [Field F] [CharZero F], LinearIndependent F fun i => MvPolynomial.map (Int.castRingHom F) (bZ i)
  span_F : ∀ (F : Type) [Field F] [CharZero F],
    Submodule.span F (Set.range fun i => MvPolynomial.map (Int.castRingHom F) (bZ i)) = VV F lam

attribute [instance] ZBasis.fin ZBasis.dec

namespace ZBasis

variable {ι : Type} [Fintype ι] {n : ℕ} {lam : ι → DomWeight n} (Z : ZBasis lam)

def basis (F : Type) [Field F] [CharZero F] : Basis Z.J0 F (VV F lam) :=
  (Basis.span (Z.li F)).map (LinearEquiv.ofEq _ _ (Z.span_F F))

theorem basis_coe (F : Type) [Field F] [CharZero F] (i : Z.J0) :
    ((Z.basis F i : VV F lam) : Pol F ι n) = MvPolynomial.map (Int.castRingHom F) (Z.bZ i) := by
  simp only [basis, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply]

end ZBasis

section Gen

variable {K : Type} [Field K] {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {Cl : Type} [Fintype Cl] [DecidableEq Cl] {J0 : Type} [Fintype J0] [DecidableEq J0]

theorem sumBasis_repr [NumberField K] (coE : V ≃ₗ[K] (Cl → W)) (BK : Basis J0 K W) (x : V) (i : J0) (c : Cl) :
    (sumBasis coE BK).repr x (i, c) = BK.repr (coE x c) i := by
  unfold sumBasis
  rw [Basis.repr_reindex_apply, Basis.map_repr]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_symm]
  rfl

theorem mem_span_sumBasis [NumberField K] (R : Subring K) (coE : V ≃ₗ[K] (Cl → W)) (BK : Basis J0 K W) (x : V) :
    x ∈ Submodule.span R (Set.range (sumBasis coE BK)) ↔ ∀ c, coE x c ∈ Submodule.span R (Set.range BK) := by
  simp only [Basis.mem_span_iff_repr_mem, Prod.forall, sumBasis_repr]
  exact forall_comm

end Gen

section Rec

variable (D : D7)

theorem int_mem_intW (w : D.what₂.places.Pl) (o : 𝓞 D.what₂.LL) : (o : D.what₂.LL) ∈ intW D.what₂.places w :=
  (D.val_nonneg_iff w _).2 ((D.plEq w).valuation_le_one o)

theorem mem_localization_latticeOf_iff (w : D.what₂.places.Pl) {V : Type} [AddCommGroup V] [Module D.what₂.LL V]
    [Module (𝓞 D.what₂.LL) V] [IsScalarTower (𝓞 D.what₂.LL) D.what₂.LL V] {J : Type} (f : J → V) (x : V) :
    x ∈ localization₂ (D.plEq w).asIdeal (latOf (K := D.what₂.LL) f) ↔ x ∈ Submodule.span (intW D.what₂.places w) (Set.range f) := by
  have h0 : x ∈ localization₂ (D.plEq w).asIdeal (latOf (K := D.what₂.LL) f) ↔ x ∈ locW D.what₂.places w (latOf (K := D.what₂.LL) f) :=
    (D.mem_locW_iff w _ x).symm
  rw [h0]
  unfold locW
  have : Submodule.span (intW D.what₂.places w) ((latOf (K := D.what₂.LL) f : Submodule (𝓞 D.what₂.LL) V) : Set V) =
      Submodule.span (intW D.what₂.places w) (Set.range f) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span hy
      | zero => exact Submodule.zero_mem _
      | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
      | smul o y _ hy =>
        have : o • y = (⟨(o : D.what₂.LL), int_mem_intW D w o⟩ : intW D.what₂.places w) • y := by
          rw [Subring.smul_def, ← algebraMap_smul D.what₂.LL o]
        rw [SetLike.mem_coe, this]
        exact Submodule.smul_mem _ _ hy
    · exact Submodule.span_mono Submodule.subset_span
  rw [this]

theorem mem_localization_iff_localizationAtPlace (w : D.what₂.places.Pl) {V : Type} [AddCommGroup V] [Module D.what₂.LL V]
    [Module (𝓞 D.what₂.LL) V] [IsScalarTower (𝓞 D.what₂.LL) D.what₂.LL V] (A : Submodule (𝓞 D.what₂.LL) V) (x : V) :
    x ∈ localization₂ (D.plEq w).asIdeal A ↔ x ∈ locW D.what₂.places w A := (D.mem_locW_iff w _ x).symm

variable {D}

theorem map_ten {n : ℕ} (f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ) :
    Formalism.MainNotions.flipTwoThree.ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)) =
      MvPolynomial.map (Int.castRingHom D.what₂.LL) (Formalism.MainNotions.flipTwoThree.ten f) := by
  simp only [Formalism.MainNotions.flipTwoThree.ten, map_prod, MvPolynomial.map_rename]

theorem intCast_mem_intW (w : D.what₂.places.Pl) (z : ℤ) : (z : D.what₂.LL) ∈ intW D.what₂.places w := by
  first
    | exact Subring.intCast_mem _ z
    | exact intCast_mem _ z

theorem mem_intSpanAt_iff {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) (Z : ZBasis lam)
    (y : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL) :
    y ∈ IntSpanAt D w lam ↔ y ∈ Submodule.span (intW D.what₂.places w)
      (Set.range fun i => MvPolynomial.map (Int.castRingHom D.what₂.LL) (Z.bZ i)) := by
  constructor
  · intro hy
    unfold IntSpanAt at hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨r, f, hr, hf, rfl⟩ := hy
      rw [map_ten]
      have h1 : Formalism.MainNotions.flipTwoThree.ten f ∈ Submodule.span ℤ (Set.range Z.bZ) := by
        rw [Z.span_eq]; exact Submodule.subset_span ⟨f, hf, rfl⟩
      have h2 : MvPolynomial.map (Int.castRingHom D.what₂.LL) (Formalism.MainNotions.flipTwoThree.ten f) ∈ Submodule.span (intW D.what₂.places w)
          (Set.range fun i => MvPolynomial.map (Int.castRingHom D.what₂.LL) (Z.bZ i)) := by
        generalize Formalism.MainNotions.flipTwoThree.ten f = q0 at h1 ⊢
        induction h1 using Submodule.span_induction with
        | mem q hq => obtain ⟨i, rfl⟩ := hq; exact Submodule.subset_span ⟨i, rfl⟩
        | zero => rw [map_zero]; exact Submodule.zero_mem _
        | add p q _ _ hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq
        | smul z q _ hq =>
          rw [zsmul_eq_mul, map_mul, map_intCast, ← zsmul_eq_mul]
          exact zsmul_mem hq z
      exact Submodule.smul_mem _ (⟨r, hr⟩ : intW D.what₂.places w) h2
    | zero => exact Submodule.zero_mem _
    | add p q _ _ hp hq => exact Submodule.add_mem _ hp hq
    | neg p _ hp => exact Submodule.neg_mem _ hp
  · intro hy
    have hsm : ∀ (r : intW D.what₂.places w) (q : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL),
        q ∈ IntSpanAt D w lam → r • q ∈ IntSpanAt D w lam := by
      intro r q hq
      unfold IntSpanAt at hq ⊢
      induction hq using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨r', f, hr', hf, rfl⟩ := hy
        refine AddSubgroup.subset_closure ⟨(r : D.what₂.LL) * r', f, mul_mem r.2 hr', hf, ?_⟩
        rw [Subring.smul_def, smul_smul]
      | zero => rw [smul_zero]; exact zero_mem _
      | add p q _ _ hp hq => rw [smul_add]; exact add_mem hp hq
      | neg p _ hp => rw [smul_neg]; exact neg_mem hp
    induction hy using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨i, rfl⟩ := hq
      have h1 : Z.bZ i ∈ Submodule.span ℤ
          {p | ∃ f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ, (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧ p = Formalism.MainNotions.flipTwoThree.ten f} := by
        rw [← Z.span_eq]; exact Submodule.subset_span ⟨i, rfl⟩
      show MvPolynomial.map (Int.castRingHom D.what₂.LL) (Z.bZ i) ∈ IntSpanAt D w lam
      generalize Z.bZ i = q0 at h1 ⊢
      induction h1 using Submodule.span_induction with
      | mem q hq =>
        obtain ⟨f, hf, rfl⟩ := hq
        refine AddSubgroup.subset_closure ⟨1, f, one_mem _, hf, ?_⟩
        rw [one_smul, map_ten]
      | zero => rw [map_zero]; exact zero_mem _
      | add p q _ _ hp hq => rw [map_add]; exact add_mem hp hq
      | smul z q _ hq =>
        rw [zsmul_eq_mul, map_mul, map_intCast, ← zsmul_eq_mul]
        exact zsmul_mem hq z
    | zero => exact zero_mem _
    | add p q _ _ hp hq => exact add_mem hp hq
    | smul r q _ hq => exact hsm r q hq

end Rec

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
