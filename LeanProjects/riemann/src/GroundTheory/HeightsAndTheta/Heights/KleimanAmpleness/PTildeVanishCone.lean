import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeTailLoc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section ConeE

variable (S : Type u) [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

def ConeE (_S : Type u) (_x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] : Type v := ℤ →₀ E

instance : AddCommGroup (ConeE S x E) := inferInstanceAs (AddCommGroup (ℤ →₀ E))
instance : Module Ω (ConeE S x E) := inferInstanceAs (Module Ω (ℤ →₀ E))
instance : Module S (ConeE S x E) := inferInstanceAs (Module S (ℤ →₀ E))

def coeffE (c : ℤ) : ConeE S x E →ₗ[S] E := Finsupp.lapply c

def singleE (c : ℤ) : E →ₗ[S] ConeE S x E := Finsupp.lsingle c

variable {S x E}

theorem coneE_ext {w w' : ConeE S x E} (h : ∀ d, coeffE S x E d w = coeffE S x E d w') : w = w' :=
  Finsupp.ext h

theorem coeffE_singleE_same (c : ℤ) (v : E) : coeffE S x E c (singleE S x E c v) = v :=
  Finsupp.single_eq_same

theorem coeffE_singleE_ne {c d : ℤ} (h : c ≠ d) (v : E) : coeffE S x E d (singleE S x E c v) = 0 :=
  Finsupp.single_eq_of_ne h.symm

theorem coeffE_omega_smul (a : Ω) (w : ConeE S x E) (c : ℤ) : coeffE S x E c (a • w) = a • coeffE S x E c w :=
  rfl

def suppE (w : ConeE S x E) : Finset ℤ := Finsupp.support (show ℤ →₀ E from w)

theorem mem_suppE {w : ConeE S x E} {d : ℤ} : d ∈ suppE w ↔ coeffE S x E d w ≠ 0 :=
  Finsupp.mem_support_iff

theorem sum_singleE (w : ConeE S x E) : ∑ c ∈ suppE w, singleE S x E c (coeffE S x E c w) = w :=
  Finsupp.sum_single (show ℤ →₀ E from w)

variable (S x E)

def shiftE : Multiplicative ℤ →* Module.End Ω (ConeE S x E) where
  toFun n := (Finsupp.domLCongr (M := E) (R := Ω) (Equiv.addRight n.toAdd)).toLinearMap
  map_one' := LinearMap.ext fun w => Finsupp.ext fun c => by
    change (Finsupp.equivMapDomain (Equiv.addRight (0 : ℤ)) (show ℤ →₀ E from w)) c = (show ℤ →₀ E from w) c
    rw [Finsupp.equivMapDomain_apply]
    simp only [Equiv.addRight_symm_apply, neg_zero, add_zero]
  map_mul' a b := LinearMap.ext fun w => Finsupp.ext fun c => by
    change (Finsupp.equivMapDomain (Equiv.addRight (a.toAdd + b.toAdd)) (show ℤ →₀ E from w)) c =
      (Finsupp.equivMapDomain (Equiv.addRight a.toAdd)
        (Finsupp.equivMapDomain (Equiv.addRight b.toAdd) (show ℤ →₀ E from w))) c
    rw [Finsupp.equivMapDomain_apply, Finsupp.equivMapDomain_apply, Finsupp.equivMapDomain_apply]
    simp only [Equiv.addRight_symm_apply]
    congr 1
    abel

variable {S x E} in
theorem coeffE_shiftE (n : ℤ) (w : ConeE S x E) (c : ℤ) :
    coeffE S x E c (shiftE S x E (Multiplicative.ofAdd n) w) = coeffE S x E (c - n) w := by
  change (Finsupp.equivMapDomain (Equiv.addRight n) (show ℤ →₀ E from w)) c = _
  rw [Finsupp.equivMapDomain_apply]
  simp only [Equiv.addRight_symm_apply]
  rfl

def lpActE : LaurentPolynomial Ω →ₐ[Ω] Module.End Ω (ConeE S x E) :=
  AddMonoidAlgebra.lift Ω (Module.End Ω (ConeE S x E)) ℤ (shiftE S x E)

def coneE : Poly S N →+* Module.End Ω (ConeE S x E) :=
  (lpActE S x E).toRingHom.comp ((ConeLaurent.toLP S x).comp (coneLaurent S x))

instance : Module (Poly S N) (ConeE S x E) := Module.compHom _ (coneE S x E)

variable {S x E}

theorem coneE_smul (p : Poly S N) (w : ConeE S x E) : p • w = coneE S x E p w := rfl

theorem coeffE_smul_of_isHomogeneous {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e)
    (w : ConeE S x E) (c : ℤ) : coeffE S x E c (f • w) = aeval x f • coeffE S x E (c - e) w := by
  rw [coneE_smul]
  change coeffE S x E c (lpActE S x E (ConeLaurent.toLP S x (coneLaurent S x f)) w) = _
  rw [coneLaurent_of_isHomogeneous hf, ConeLaurent.toLaurent_ofLaurent, lpActE, AddMonoidAlgebra.lift_single,
    LinearMap.smul_apply, coeffE_omega_smul, coeffE_shiftE]

theorem coneE_C (s : S) (w : ConeE S x E) : coneE S x E (C s) w = s • w := by
  refine coneE_ext fun d => ?_
  have h := coeffE_smul_of_isHomogeneous (x := x) (isHomogeneous_C (Fin (N + 1)) s) w d
  rw [coneE_smul] at h
  rw [h, aeval_C, Nat.cast_zero, sub_zero, algebraMap_smul, map_smul]

instance : IsScalarTower S (Poly S N) (ConeE S x E) where
  smul_assoc s p w := by
    rw [Algebra.smul_def, mul_smul, MvPolynomial.algebraMap_eq]
    exact coneE_C s (p • w)

theorem smul_singleE {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) (c : ℤ) (v : E) :
    f • singleE S x E c v = singleE S x E (c + e) (aeval x f • v) := by
  refine coneE_ext fun d => ?_
  rw [coeffE_smul_of_isHomogeneous hf]
  by_cases h : c + e = d
  · rw [← h, add_sub_cancel_right, coeffE_singleE_same, coeffE_singleE_same]
  · rw [coeffE_singleE_ne h, coeffE_singleE_ne (by omega), smul_zero]

theorem bijective_smul_of_isHomogeneous {s : Poly S N} {e : ℕ} (hs : s.IsHomogeneous e)
    (h0 : aeval x s ≠ 0) : Function.Bijective (fun w : ConeE S x E => s • w) := by
  refine ⟨fun w w' h => coneE_ext fun d => ?_, fun w => ?_⟩
  · have h1 := congrArg (coeffE S x E (d + e)) h
    simp only [coeffE_smul_of_isHomogeneous hs, add_sub_cancel_right] at h1
    exact smul_right_injective E h0 h1
  · refine ⟨shiftE S x E (Multiplicative.ofAdd (-(e : ℤ))) ((aeval x s)⁻¹ • w), coneE_ext fun d => ?_⟩
    change coeffE S x E d (s • _) = _
    rw [coeffE_smul_of_isHomogeneous hs, coeffE_shiftE, coeffE_omega_smul, smul_smul,
      mul_inv_cancel₀ h0, one_smul, sub_neg_eq_add, sub_add_cancel]

end ConeE

section SubE

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  (M : FinGradedSub (S := S) (x := x) E)

def FinGradedSub.coneSubE : Submodule (Poly S N) (ConeE S x E) where
  carrier := {w | ∀ c, coeffE S x E c w ∈ M.piece c}
  add_mem' ha hb c := by rw [map_add]; exact add_mem (ha c) (hb c)
  zero_mem' c := by rw [map_zero]; exact zero_mem _
  smul_mem' p w hw c := by
    change coeffE S x E c (p • w) ∈ M.piece c
    rw [← sum_homogeneousComponent p, Finset.sum_smul, map_sum]
    refine Submodule.sum_mem _ fun e _ => ?_
    rw [coeffE_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous e p)]
    have := M.smul_mem e (c - e) _ _ (homogeneousComponent_isHomogeneous e p) (hw (c - e))
    rwa [sub_add_cancel] at this

theorem FinGradedSub.singleE_mem_coneSubE {c : ℤ} {v : E} (hv : v ∈ M.piece c) :
    singleE S x E c v ∈ M.coneSubE := fun d => by
  by_cases h : c = d
  · subst h; rw [coeffE_singleE_same]; exact hv
  · rw [coeffE_singleE_ne h]; exact zero_mem _

def FinGradedSub.conePieceE (a : ℤ) : Submodule S M.coneSubE where
  carrier := {m | ∀ d, d ≠ a → coeffE S x E d (m : ConeE S x E) = 0}
  add_mem' ha hb d hd := by rw [Submodule.coe_add, map_add, ha d hd, hb d hd, add_zero]
  zero_mem' d _ := by rw [Submodule.coe_zero, map_zero]
  smul_mem' s m hm d hd := by rw [Submodule.coe_smul_of_tower, map_smul, hm d hd, smul_zero]

theorem FinGradedSub.eq_singleE_of_mem_conePieceE {a : ℤ} {m : M.coneSubE} (hm : m ∈ M.conePieceE a) :
    (m : ConeE S x E) = singleE S x E a (coeffE S x E a m) := by
  refine coneE_ext fun d => ?_
  by_cases h : a = d
  · subst h; rw [coeffE_singleE_same]
  · rw [coeffE_singleE_ne h, hm d (Ne.symm h)]

theorem FinGradedSub.singleE_mem_conePieceE {c : ℤ} {v : E} (hv : v ∈ M.piece c) :
    (⟨singleE S x E c v, M.singleE_mem_coneSubE hv⟩ : M.coneSubE) ∈ M.conePieceE c :=
  fun _ hd => coeffE_singleE_ne (Ne.symm hd) v

def FinGradedSub.coneGradedE : GradedPMod S N M.coneSubE where
  piece := M.conePieceE
  isInternal := by
    refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
    · refine iSupIndep_def.mpr fun a => Submodule.disjoint_def.mpr fun m hm hm' => ?_
      have h0 : coeffE S x E a (m : ConeE S x E) = 0 := by
        have hle : (⨆ (j : ℤ) (_ : j ≠ a), M.conePieceE j) ≤
            LinearMap.ker ((coeffE S x E a).comp ((M.coneSubE.subtype).restrictScalars S)) :=
          iSup₂_le fun j hj m hm => hm a (Ne.symm hj)
        exact hle hm'
      apply Subtype.ext
      rw [M.eq_singleE_of_mem_conePieceE hm, h0, map_zero]
      rfl
    · refine eq_top_iff.mpr fun m _ => ?_
      have hm : m = ∑ c ∈ suppE (m : ConeE S x E),
          (⟨singleE S x E c (coeffE S x E c m), M.singleE_mem_coneSubE (m.2 c)⟩ : M.coneSubE) := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        exact (sum_singleE (m : ConeE S x E)).symm
      rw [hm]
      exact Submodule.sum_mem _ fun c _ =>
        Submodule.mem_iSup_of_mem c (M.singleE_mem_conePieceE (m.2 c))
  smul_mem d c p m hp hm e he := by
    change coeffE S x E e (p • (m : ConeE S x E)) = 0
    rw [coeffE_smul_of_isHomogeneous hp, hm (e - d) (by omega), smul_zero]

theorem FinGradedSub.coneSubE_finite : Module.Finite (Poly S N) M.coneSubE := by
  obtain ⟨n, deg, gen, hgen, hspan⟩ := M.fg
  have heq : M.coneSubE = Submodule.span (Poly S N) (Set.range fun j => singleE S x E (deg j) (gen j)) := by
    refine le_antisymm (fun w hw => ?_) (Submodule.span_le.mpr ?_)
    · rw [← sum_singleE w]
      refine Submodule.sum_mem _ fun c _ => ?_
      have hv := hspan c (hw c)
      refine Submodule.span_induction (p := fun v _ => singleE S x E c v ∈
        Submodule.span (Poly S N) (Set.range fun j => singleE S x E (deg j) (gen j))) ?_ ?_ ?_ ?_ hv
      · rintro _ ⟨j, f, e, hf, hej, rfl⟩
        have : singleE S x E c (aeval x f • gen j) = f • singleE S x E (deg j) (gen j) := by
          rw [smul_singleE hf, show deg j + (e : ℤ) = c by omega]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      · rw [map_zero]; exact zero_mem _
      · intro a b _ _ ha hb; rw [map_add]; exact add_mem ha hb
      · intro s a _ ha; rw [map_smul]; exact Submodule.smul_of_tower_mem _ s ha
    · rintro _ ⟨j, rfl⟩
      exact M.singleE_mem_coneSubE (hgen j)
  rw [Module.Finite.iff_fg, heq]
  exact Submodule.fg_span (Set.finite_range _)

end SubE

end

end GroundTheory.Heights₂.Heights.Kleiman
