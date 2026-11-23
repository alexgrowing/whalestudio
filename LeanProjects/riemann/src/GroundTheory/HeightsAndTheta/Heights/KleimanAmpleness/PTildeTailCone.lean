import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsTildeTail
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Cone

variable (S : Type u) [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}

def ConeLaurent (_S : Type u) (_x : Fin (N + 1) → Ω) : Type w := LaurentPolynomial Ω

variable (x : Fin (N + 1) → Ω)

instance : CommRing (ConeLaurent S x) := inferInstanceAs (CommRing (LaurentPolynomial Ω))

def ConeLaurent.toLP : ConeLaurent S x →+* LaurentPolynomial Ω := RingHom.id _

def ConeLaurent.ofLP : LaurentPolynomial Ω →+* ConeLaurent S x := RingHom.id _

omit [CommRing S] [Algebra S Ω] in
variable {S x} in
@[simp] theorem ConeLaurent.toLaurent_ofLaurent (y : LaurentPolynomial Ω) :
    ConeLaurent.toLP S x (ConeLaurent.ofLP S x y) = y := rfl

def coneLaurent : Poly S N →+* ConeLaurent S x :=
  (ConeLaurent.ofLP S x).comp ((Polynomial.toLaurent : Polynomial Ω →+* LaurentPolynomial Ω).comp
    (cone (S := S) x).toRingHom)

instance : Module (Poly S N) (ConeLaurent S x) := Module.compHom _ (coneLaurent S x)

instance : Module S (ConeLaurent S x) :=
  Module.compHom _ ((coneLaurent S x).comp (algebraMap S (Poly S N)))

instance : IsScalarTower S (Poly S N) (ConeLaurent S x) where
  smul_assoc s p w := by
    change coneLaurent S x (s • p) * w = coneLaurent S x (algebraMap S (Poly S N) s) * (coneLaurent S x p * w)
    rw [Algebra.smul_def, map_mul, mul_assoc]

variable {S x}

theorem coneLaurent_smul (p : Poly S N) (w : ConeLaurent S x) : p • w = coneLaurent S x p * w := rfl

theorem coneLaurent_smul_scalar (s : S) (w : ConeLaurent S x) :
    s • w = algebraMap S (Poly S N) s • w := rfl

theorem coneLaurent_of_isHomogeneous {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) :
    coneLaurent S x f = ConeLaurent.ofLP S x (AddMonoidAlgebra.single (e : ℤ) (aeval x f)) := by
  show Polynomial.toLaurent (cone (S := S) x f) = AddMonoidAlgebra.single (e : ℤ) (aeval x f)
  rw [cone_of_isHomogeneous x hf, Polynomial.toLaurent_C_mul_X_pow, ← LaurentPolynomial.single_eq_C_mul_T]

variable (S x)

def coeffAt (c : ℤ) : ConeLaurent S x →ₗ[S] Ω where
  toFun w := (ConeLaurent.toLP S x w).coeff c
  map_add' a b := by rw [map_add]; rfl
  map_smul' s w := by
    change (ConeLaurent.toLP S x (coneLaurent S x (C s) * w)).coeff c = _
    rw [map_mul, coneLaurent_of_isHomogeneous (isHomogeneous_C _ s), ConeLaurent.toLaurent_ofLaurent,
      AddMonoidAlgebra.coeff_single_mul_apply, aeval_C, RingHom.id_apply, Algebra.smul_def]
    simp

def coneSingle (c : ℤ) : Ω →ₗ[S] ConeLaurent S x where
  toFun v := ConeLaurent.ofLP S x (AddMonoidAlgebra.single c v)
  map_add' a b := by rw [AddMonoidAlgebra.single_add, map_add]
  map_smul' s v := by
    change ConeLaurent.ofLP S x (AddMonoidAlgebra.single c (s • v)) =
      coneLaurent S x (C s) * ConeLaurent.ofLP S x (AddMonoidAlgebra.single c v)
    rw [coneLaurent_of_isHomogeneous (isHomogeneous_C _ s), ← map_mul, AddMonoidAlgebra.single_mul_single,
      aeval_C, Algebra.smul_def]
    simp

variable {S x}

theorem coeffAt_coneSingle_same (c : ℤ) (v : Ω) : coeffAt S x c (coneSingle S x c v) = v := by
  change (Finsupp.single c v) c = v
  rw [Finsupp.single_eq_same]

theorem coeffAt_coneSingle_ne {c d : ℤ} (h : c ≠ d) (v : Ω) : coeffAt S x d (coneSingle S x c v) = 0 := by
  change (Finsupp.single c v) d = 0
  rw [Finsupp.single_eq_of_ne h.symm]

theorem coneLaurent_ext {w w' : ConeLaurent S x} (h : ∀ d, coeffAt S x d w = coeffAt S x d w') : w = w' :=
  LaurentPolynomial.ext (R := Ω) (p := ConeLaurent.toLP S x w) (q := ConeLaurent.toLP S x w') h

def coneSupp (w : ConeLaurent S x) : Finset ℤ := (ConeLaurent.toLP S x w).coeff.support

theorem mem_coneSupp {w : ConeLaurent S x} {d : ℤ} : d ∈ coneSupp w ↔ coeffAt S x d w ≠ 0 :=
  Finsupp.mem_support_iff

theorem sum_coneSingle (w : ConeLaurent S x) :
    ∑ c ∈ coneSupp w, coneSingle S x c (coeffAt S x c w) = w := by
  refine coneLaurent_ext fun d => ?_
  rw [map_sum]
  by_cases hd : d ∈ coneSupp w
  · rw [Finset.sum_eq_single d (fun c _ hc => coeffAt_coneSingle_ne hc _) (fun h => absurd hd h),
      coeffAt_coneSingle_same]
  · rw [Finset.sum_eq_zero fun c hc => coeffAt_coneSingle_ne (fun h => hd (by rw [← h]; exact hc)) _]
    by_contra h
    exact hd (mem_coneSupp.mpr (Ne.symm h))

theorem coeffAt_smul_of_isHomogeneous {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e)
    (w : ConeLaurent S x) (c : ℤ) : coeffAt S x c (f • w) = aeval x f * coeffAt S x (c - e) w := by
  change (ConeLaurent.toLP S x (coneLaurent S x f * w)).coeff c = _
  rw [map_mul, coneLaurent_of_isHomogeneous hf, ConeLaurent.toLaurent_ofLaurent,
    AddMonoidAlgebra.coeff_single_mul_apply, neg_add_eq_sub]
  rfl

theorem smul_coneSingle {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) (c : ℤ) (v : Ω) :
    f • coneSingle S x c v = coneSingle S x (c + e) (aeval x f * v) := by
  change coneLaurent S x f * ConeLaurent.ofLP S x (AddMonoidAlgebra.single c v) =
    ConeLaurent.ofLP S x (AddMonoidAlgebra.single (c + e) (aeval x f * v))
  rw [coneLaurent_of_isHomogeneous hf, ← map_mul, AddMonoidAlgebra.single_mul_single, add_comm]

theorem isUnit_coneSingle (c : ℤ) {a : Ω} (ha : a ≠ 0) : IsUnit (coneSingle S x c a) := by
  refine IsUnit.of_mul_eq_one (coneSingle S x (-c) a⁻¹) ?_
  change ConeLaurent.ofLP S x (AddMonoidAlgebra.single c a) *
    ConeLaurent.ofLP S x (AddMonoidAlgebra.single (-c) a⁻¹) = 1
  rw [← map_mul, AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_inv_cancel₀ ha]
  exact map_one _

end Cone

section Sub

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} (M : FinGradedSub (S := S) (x := x) Ω)

def FinGradedSub.coneSub : Submodule (Poly S N) (ConeLaurent S x) where
  carrier := {w | ∀ c, coeffAt S x c w ∈ M.piece c}
  add_mem' ha hb c := by rw [map_add]; exact add_mem (ha c) (hb c)
  zero_mem' c := by rw [map_zero]; exact zero_mem _
  smul_mem' p w hw c := by
    change coeffAt S x c (p • w) ∈ M.piece c
    rw [← sum_homogeneousComponent p, Finset.sum_smul, map_sum]
    refine Submodule.sum_mem _ fun e _ => ?_
    rw [coeffAt_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous e p)]
    have := M.smul_mem e (c - e) _ _ (homogeneousComponent_isHomogeneous e p) (hw (c - e))
    rwa [sub_add_cancel, smul_eq_mul] at this

theorem FinGradedSub.mem_coneSub {w : ConeLaurent S x} : w ∈ M.coneSub ↔ ∀ c, coeffAt S x c w ∈ M.piece c :=
  Iff.rfl

theorem FinGradedSub.coneSingle_mem_coneSub {c : ℤ} {v : Ω} (hv : v ∈ M.piece c) :
    coneSingle S x c v ∈ M.coneSub := fun d => by
  by_cases h : c = d
  · subst h; rw [coeffAt_coneSingle_same]; exact hv
  · rw [coeffAt_coneSingle_ne h]; exact zero_mem _

def FinGradedSub.conePiece (a : ℤ) : Submodule S M.coneSub where
  carrier := {m | ∀ d, d ≠ a → coeffAt S x d (m : ConeLaurent S x) = 0}
  add_mem' ha hb d hd := by rw [Submodule.coe_add, map_add, ha d hd, hb d hd, add_zero]
  zero_mem' d _ := by rw [Submodule.coe_zero, map_zero]
  smul_mem' s m hm d hd := by rw [Submodule.coe_smul_of_tower, map_smul, hm d hd, smul_zero]

theorem FinGradedSub.eq_coneSingle_of_mem_conePiece {a : ℤ} {m : M.coneSub} (hm : m ∈ M.conePiece a) :
    (m : ConeLaurent S x) = coneSingle S x a (coeffAt S x a m) := by
  refine coneLaurent_ext fun d => ?_
  by_cases h : a = d
  · subst h; rw [coeffAt_coneSingle_same]
  · rw [coeffAt_coneSingle_ne h, hm d (Ne.symm h)]

theorem FinGradedSub.coneSingle_mem_conePiece {c : ℤ} {v : Ω} (hv : v ∈ M.piece c) :
    (⟨coneSingle S x c v, M.coneSingle_mem_coneSub hv⟩ : M.coneSub) ∈ M.conePiece c :=
  fun _ hd => coeffAt_coneSingle_ne (Ne.symm hd) v

def FinGradedSub.coneGraded : GradedPMod S N M.coneSub where
  piece := M.conePiece
  isInternal := by
    refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
    · refine iSupIndep_def.mpr fun a => Submodule.disjoint_def.mpr fun m hm hm' => ?_
      have h0 : coeffAt S x a (m : ConeLaurent S x) = 0 := by
        have hle : (⨆ (j : ℤ) (_ : j ≠ a), M.conePiece j) ≤
            LinearMap.ker ((coeffAt S x a).comp ((M.coneSub.subtype).restrictScalars S)) :=
          iSup₂_le fun j hj m hm => hm a (Ne.symm hj)
        exact hle hm'
      apply Subtype.ext
      rw [M.eq_coneSingle_of_mem_conePiece hm, h0, map_zero]
      rfl
    · refine eq_top_iff.mpr fun m _ => ?_
      have hm : m = ∑ c ∈ coneSupp (m : ConeLaurent S x),
          (⟨coneSingle S x c (coeffAt S x c m), M.coneSingle_mem_coneSub (m.2 c)⟩ : M.coneSub) := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        exact (sum_coneSingle (m : ConeLaurent S x)).symm
      rw [hm]
      exact Submodule.sum_mem _ fun c _ =>
        Submodule.mem_iSup_of_mem c (M.coneSingle_mem_conePiece (m.2 c))
  smul_mem d c p m hp hm e he := by
    change coeffAt S x e (p • (m : ConeLaurent S x)) = 0
    rw [coeffAt_smul_of_isHomogeneous hp, hm (e - d) (by omega), mul_zero]

theorem FinGradedSub.coneSub_finite : Module.Finite (Poly S N) M.coneSub := by
  obtain ⟨n, deg, gen, hgen, hspan⟩ := M.fg
  have heq : M.coneSub = Submodule.span (Poly S N) (Set.range fun j => coneSingle S x (deg j) (gen j)) := by
    refine le_antisymm (fun w hw => ?_) (Submodule.span_le.mpr ?_)
    · rw [← sum_coneSingle w]
      refine Submodule.sum_mem _ fun c _ => ?_
      have hv := hspan c (hw c)
      refine Submodule.span_induction (p := fun v _ => coneSingle S x c v ∈
        Submodule.span (Poly S N) (Set.range fun j => coneSingle S x (deg j) (gen j))) ?_ ?_ ?_ ?_ hv
      · rintro _ ⟨j, f, e, hf, hej, rfl⟩
        have : coneSingle S x c (aeval x f • gen j) = f • coneSingle S x (deg j) (gen j) := by
          rw [smul_coneSingle hf, smul_eq_mul, show deg j + (e : ℤ) = c by omega]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      · rw [map_zero]; exact zero_mem _
      · intro a b _ _ ha hb; rw [map_add]; exact add_mem ha hb
      · intro s a _ ha; rw [map_smul]; exact Submodule.smul_of_tower_mem _ s ha
    · rintro _ ⟨j, rfl⟩
      exact M.coneSingle_mem_coneSub (hgen j)
  rw [Module.Finite.iff_fg, heq]
  exact Submodule.fg_span (Set.finite_range _)

end Sub

end

end GroundTheory.Heights₂.Heights.Kleiman
