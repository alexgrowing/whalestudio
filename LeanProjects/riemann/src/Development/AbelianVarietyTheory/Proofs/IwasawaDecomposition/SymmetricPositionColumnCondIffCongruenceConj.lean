import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymAllowed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjIdempotentSubOneMemPlaceIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormMiddleSymmetricFrameNotOneAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianE0SymmetricFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipotentDualVectorPairingSymmetricFrameModPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDualVectorPairingSymmetricFrameModPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianZ0SymmetricFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InModIffForallPlaceMemSpanModulo
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.GroupLoc.Dual

open GlobalTheory.SeeConjRead (flagV)

section Comb

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {ρ k n : ℕ}

theorem fl_e (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n) (a : Fin ρ) (h : i.1 = a.1) :
    flagV ρ k n e f b z i = e a := by
  have := a.2
  unfold flagV
  rw [dif_pos (by omega)]
  exact congrArg e (Fin.ext h)

theorem fl_b (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n) (a : Fin k) (h : i.1 = ρ + a.1) :
    flagV ρ k n e f b z i = b a := by
  have := a.2
  unfold flagV
  rw [dif_neg (by omega), dif_pos (by omega)]
  exact congrArg b (Fin.ext (by simp only; omega))

theorem symmetricFlagBasisVectors_apply_centre (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n) (h : i.1 = ρ + k) :
    flagV ρ k n e f b z i = z := by
  unfold flagV
  rw [dif_neg (by omega), dif_neg (by omega), dif_pos h]

theorem fl_f (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n) (a : Fin ρ) (h : i.1 + a.1 = 2 * ρ + k) :
    flagV ρ k n e f b z i = f a := by
  have := a.2
  unfold flagV
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  exact congrArg f (Fin.ext (by simp only; omega))

theorem img_e (hn : n = 2 * ρ + k + 1) (e f : Fin ρ → M) (b : Fin k → M) (z : M) {m : ℕ} (hm : m ≤ ρ) :
    e '' {a | a.1 < m} = flagV ρ k n e f b z '' {j | j.1 < m} := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    have := a.2
    exact ⟨⟨a.1, by omega⟩, ha, fl_e e f b z _ a rfl⟩
  · rintro ⟨j, hj, rfl⟩
    have hj' : j.1 < m := hj
    exact ⟨⟨j.1, by omega⟩, hj, (fl_e e f b z _ _ rfl).symm⟩

theorem range_eq_img (e : Fin ρ → M) : Set.range e = e '' {a | a.1 < ρ} := by
  rw [show {a : Fin ρ | a.1 < ρ} = Set.univ from Set.eq_univ_of_forall fun a => a.2, Set.image_univ]

theorem img_b (hn : n = 2 * ρ + k + 1) (e f : Fin ρ → M) (b : Fin k → M) (z : M) {m : ℕ} (hm : m ≤ k) :
    Set.range e ∪ b '' {a | a.1 < m} = flagV ρ k n e f b z '' {j | j.1 < ρ + m} := by
  ext x
  constructor
  · rintro (⟨a, rfl⟩ | ⟨a, ha, rfl⟩)
    · have := a.2
      exact ⟨⟨a.1, by omega⟩, show a.1 < ρ + m by omega, fl_e e f b z _ a rfl⟩
    · have ha' : a.1 < m := ha
      exact ⟨⟨ρ + a.1, by omega⟩, show ρ + a.1 < ρ + m by omega, fl_b e f b z _ a rfl⟩
  · rintro ⟨j, hj, rfl⟩
    have hj' : j.1 < ρ + m := hj
    by_cases h : j.1 < ρ
    · exact Or.inl ⟨⟨j.1, h⟩, (fl_e e f b z _ _ rfl).symm⟩
    · exact Or.inr ⟨⟨j.1 - ρ, by omega⟩, show j.1 - ρ < m by omega,
        (fl_b e f b z _ _ (show j.1 = ρ + (j.1 - ρ) by omega)).symm⟩

theorem img_f (hn : n = 2 * ρ + k + 1) (e f : Fin ρ → M) (b : Fin k → M) (z : M) {m : ℕ} (hm : m ≤ ρ) :
    f '' {a | a.1 < m} = flagV ρ k n e f b z '' {j | 2 * ρ + k < j.1 + m} := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' : a.1 < m := ha
    exact ⟨⟨2 * ρ + k - a.1, by omega⟩, show 2 * ρ + k < 2 * ρ + k - a.1 + m by omega,
      fl_f e f b z _ a (show 2 * ρ + k - a.1 + a.1 = _ by omega)⟩
  · rintro ⟨j, hj, rfl⟩
    have hj' : 2 * ρ + k < j.1 + m := hj
    have := j.2
    exact ⟨⟨2 * ρ + k - j.1, by omega⟩, show 2 * ρ + k - j.1 < m by omega,
      (fl_f e f b z _ _ (show j.1 + (2 * ρ + k - j.1) = _ by omega)).symm⟩

theorem img_rev (hn : n = 2 * ρ + k + 1) (e f : Fin ρ → M) (b : Fin k → M) (z : M) {m : ℕ} (hm : m ≤ k) :
    Set.range f ∪ b '' {a | a.1 < m} =
      flagV ρ k n e f (fun i => b (Fin.rev i)) z '' {j | ρ + k ≤ j.1 + m ∧ j.1 ≠ ρ + k} := by
  ext x
  constructor
  · rintro (⟨a, rfl⟩ | ⟨a, ha, rfl⟩)
    · have := a.2
      exact ⟨⟨2 * ρ + k - a.1, by omega⟩, show ρ + k ≤ 2 * ρ + k - a.1 + m ∧ 2 * ρ + k - a.1 ≠ ρ + k by omega,
        fl_f e f _ z _ a (show 2 * ρ + k - a.1 + a.1 = _ by omega)⟩
    · have ha' : a.1 < m := ha
      refine ⟨⟨ρ + k - 1 - a.1, by omega⟩, show ρ + k ≤ ρ + k - 1 - a.1 + m ∧ ρ + k - 1 - a.1 ≠ ρ + k by omega, ?_⟩
      rw [fl_b e f _ z _ (Fin.rev a) (by rw [Fin.val_rev]; simp only; omega), Fin.rev_rev]
  · rintro ⟨j, hj, rfl⟩
    have hj' : ρ + k ≤ j.1 + m ∧ j.1 ≠ ρ + k := hj
    have := j.2
    by_cases h : j.1 < ρ + k
    · refine Or.inr ⟨Fin.rev ⟨j.1 - ρ, by omega⟩, ?_,
        (fl_b e f (fun i => b (Fin.rev i)) z j ⟨j.1 - ρ, by omega⟩ (show j.1 = ρ + (j.1 - ρ) by omega)).symm⟩
      show (Fin.rev _).1 < m
      rw [Fin.val_rev]; simp only; omega
    · exact Or.inl ⟨⟨2 * ρ + k - j.1, by omega⟩,
        (fl_f e f _ z _ _ (show j.1 + (2 * ρ + k - j.1) = _ by omega)).symm⟩

theorem comb (hn : n = 2 * ρ + k + 1) (e f : Fin ρ → M) (z : M) (b ε εd : Fin k → M) (W W' : Submodule R M)
    (T T' : M → M) (hneg : T' (-z) = -T' z) (P : Fin n → Fin n → Prop)
    (hcol : ∀ i S, T (flagV ρ k n e f ε z i) ∈ Submodule.span R (flagV ρ k n e f ε z '' S) ⊔ W ↔ ∀ j ∉ S, P j i)
    (hrow : ∀ j S, T' (flagV ρ k n f e εd (-z) j) ∈ Submodule.span R (flagV ρ k n f e εd (-z) '' S) ⊔ W' ↔
      ∀ i ∉ S, P j i)
    (hcase : (ε = b ∧ ∀ i, T' (b i) ∈ W') ∨ (εd = (fun i => b (Fin.rev i)) ∧ ∀ i, T (b i) ∈ W)) :
    (∀ i, T (flagV ρ k n e f ε z i) ∈ Submodule.span R (flagV ρ k n e f ε z '' {j | symAllowed ρ k i j}) ⊔ W) ↔
      ((∀ a : Fin ρ, T (e a) ∈ Submodule.span R (e '' {c | c.1 < a.1}) ⊔ W) ∧
        T z ∈ Submodule.span R (Set.range e) ⊔ W ∧
        ∀ i : Fin k, T (b i) ∈ Submodule.span R (Set.range e ∪ b '' {j | j.1 < i.1}) ⊔ W) ∧
      ((∀ a : Fin ρ, T' (e a) ∈ Submodule.span R (e '' {c | c.1 < a.1}) ⊔ W') ∧
        T' z ∈ Submodule.span R (Set.range e) ⊔ W' ∧
        ∀ i : Fin k, T' (b i) ∈ Submodule.span R (Set.range e ∪ b '' {j | j.1 < i.1}) ⊔ W') := by
  have c1 : ∀ (a : Fin ρ) (i : Fin n), i.1 = a.1 →
      (T (e a) ∈ Submodule.span R (e '' {c | c.1 < a.1}) ⊔ W ↔ ∀ j : Fin n, ¬ j.1 < a.1 → P j i) := fun a i h => by
    rw [img_e hn e f ε z a.2.le, ← fl_e e f ε z i a h]; exact hcol _ _
  have c2 : ∀ i : Fin n, i.1 = ρ + k →
      (T z ∈ Submodule.span R (Set.range e) ⊔ W ↔ ∀ j : Fin n, ¬ j.1 < ρ → P j i) := fun i h => by
    have := hcol i {j | j.1 < ρ}
    rw [symmetricFlagBasisVectors_apply_centre e f ε z i h, ← img_e hn e f ε z le_rfl, ← range_eq_img] at this
    exact this
  have c3 : ∀ (a : Fin k) (i : Fin n), i.1 = ρ + a.1 →
      (T (ε a) ∈ Submodule.span R (Set.range e ∪ ε '' {c | c.1 < a.1}) ⊔ W ↔
        ∀ j : Fin n, ¬ j.1 < ρ + a.1 → P j i) := fun a i h => by
    rw [img_b hn e f ε z a.2.le, ← fl_b e f ε z i a h]; exact hcol _ _
  have r1 : ∀ (a : Fin ρ) (j : Fin n), j.1 + a.1 = 2 * ρ + k →
      (T' (e a) ∈ Submodule.span R (e '' {c | c.1 < a.1}) ⊔ W' ↔
        ∀ i : Fin n, ¬ 2 * ρ + k < i.1 + a.1 → P j i) := fun a j h => by
    rw [img_f hn f e εd (-z) a.2.le, ← fl_f f e εd (-z) j a h]; exact hrow _ _
  have r2 : ∀ j : Fin n, j.1 = ρ + k →
      (T' z ∈ Submodule.span R (Set.range e) ⊔ W' ↔ ∀ i : Fin n, ¬ 2 * ρ + k < i.1 + ρ → P j i) := fun j h => by
    have := hrow j {i | 2 * ρ + k < i.1 + ρ}
    rw [symmetricFlagBasisVectors_apply_centre f e εd (-z) j h, ← img_f hn f e εd (-z) le_rfl, ← range_eq_img, hneg, neg_mem_iff] at this
    exact this
  have r3 : εd = (fun i => b (Fin.rev i)) → ∀ (a : Fin k) (j : Fin n), j.1 + a.1 + 1 = ρ + k →
      (T' (b a) ∈ Submodule.span R (Set.range e ∪ b '' {c | c.1 < a.1}) ⊔ W' ↔
        ∀ i : Fin n, ¬ (ρ + k ≤ i.1 + a.1 ∧ i.1 ≠ ρ + k) → P j i) := fun hd a j h => by
    have := hrow j {i | ρ + k ≤ i.1 + a.1 ∧ i.1 ≠ ρ + k}
    have ha := a.2
    rw [hd, fl_b f e _ (-z) j (Fin.rev a) (by rw [Fin.val_rev]; omega), ← img_rev hn f e b (-z) a.2.le,
      Fin.rev_rev] at this
    exact this
  simp only [hcol, Set.mem_setOf_eq, symAllowed]
  constructor
  · intro H
    refine ⟨⟨fun a => ?_, ?_, fun a => ?_⟩, fun a => ?_, ?_, fun a => ?_⟩
    · have := a.2
      exact (c1 a ⟨a.1, by omega⟩ rfl).2 fun j hj => H _ _ (by simp only; omega)
    · exact (c2 ⟨ρ + k, by omega⟩ rfl).2 fun j hj => H _ _ (by dsimp only; omega)
    · have := a.2
      rcases hcase with ⟨rfl, -⟩ | ⟨-, h⟩
      · exact (c3 a ⟨ρ + a.1, by omega⟩ rfl).2 fun j hj => H _ _ (by simp only; omega)
      · exact Submodule.mem_sup_right (h a)
    · have := a.2
      exact (r1 a ⟨2 * ρ + k - a.1, by omega⟩ (by simp only; omega)).2 fun j hj => H _ _ (by simp only; omega)
    · exact (r2 ⟨ρ + k, by omega⟩ rfl).2 fun j hj => H _ _ (by simp only; omega)
    · have := a.2
      rcases hcase with ⟨-, h⟩ | ⟨h, -⟩
      · exact Submodule.mem_sup_right (h a)
      · exact (r3 h a ⟨ρ + k - 1 - a.1, by omega⟩ (by simp only; omega)).2 fun j hj => H _ _ (by simp only; omega)
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ i j hij
    have hi := i.2
    have hj := j.2
    by_cases a1 : i.1 < ρ
    · exact (c1 ⟨i.1, a1⟩ i rfl).1 (h1 _) j (by simp only; omega)
    by_cases a2 : i.1 = ρ + k
    · exact (c2 i a2).1 h2 j (by omega)
    by_cases a3 : ρ + k < j.1
    · exact (r1 ⟨2 * ρ + k - j.1, by omega⟩ j (by simp only; omega)).1 (h4 _) i (by simp only; omega)
    by_cases a4 : j.1 = ρ + k
    · exact (r2 j a4).1 h5 i (by omega)
    rcases hcase with ⟨rfl, -⟩ | ⟨h, -⟩
    · exact (c3 ⟨i.1 - ρ, by omega⟩ i (by simp only; omega)).1 (h3 _) j (by simp only; omega)
    · exact (r3 h ⟨ρ + k - 1 - j.1, by omega⟩ j (by simp only; omega)).1 (h6 _) i (by simp only; omega)

end Comb

open Formalism.L2.SG.Pf.unitaryCongruence GlobalTheory.Mem.SymChar GlobalTheory.Mem.SymFrame GlobalTheory.DimPartsCompare

variable {D : D7} (X : HidaSetting D)

theorem sig_mem (w : HeightOneSpectrum (𝓞 D.host.E)) {c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F}
    (hc : c ∈ wInt X w) : sigA X.B.I c ∈ wInt X (cPl w) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨a, ⟨b, hb, hab⟩, rfl⟩ := hc
    rw [sigA_inclE]
    refine Submodule.subset_span ⟨RingOfIntegers.mapRingEquiv X.ιE.symm (GlobalTheory.SumWCompare.cj _ b),
      ⟨GlobalTheory.SumWCompare.cj _ b, by rw [mem_cPl, GlobalTheory.SumWCompare.cj_cj]; exact hb, X.ιE.apply_symm_apply _⟩, ?_⟩
    congr 1
    apply X.ιE.injective
    rw [X.ιE_conj, hab, ← star_conj, ← GlobalTheory.SumWCompare.cj_coe]
    exact (X.ιE.apply_symm_apply _).symm
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul r a _ ha =>
    show sigA X.B.I ((r : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * a) ∈ _
    rw [map_mul]
    exact (wInt X (cPl w)).smul_mem ⟨_, sigA_mem X.B.I r.2⟩ ha

theorem mul_mem_wInt (w : HeightOneSpectrum (𝓞 D.host.E)) {t c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F}
    (ht : t ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) (hc : c ∈ wInt X w) : t * c ∈ wInt X w :=
  (wInt X w).smul_mem ⟨t, ht⟩ hc

theorem coords (w : HeightOneSpectrum (𝓞 D.host.E)) {n : ℕ} (u v : Fin n → VA X.B.I)
    (hu : ∀ i, u i ∈ X.B.I.Lf) (hv : ∀ i, v i ∈ X.B.I.Lf)
    (hd : ∀ j i, hA X.B.I (v j) (u i) - (if i = j then 1 else 0) ∈ wInt X w)
    {y : VA X.B.I} (hy : GroupLoc.ModW X w (Set.range u) y) (S : Set (Fin n)) :
    GroupLoc.ModW X w (u '' S) y ↔ ∀ j ∉ S, hA X.B.I (v j) y ∈ wInt X w := by
  constructor
  · intro h j hj
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 h
    rw [hA_add_right]
    refine add_mem ?_ (hA_mem_wInt X w (hv j) ht)
    clear h hy
    induction hs using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨i, hi, rfl⟩ := hs
      have := hd j i
      rwa [if_neg (fun (e : i = j) => hj (e ▸ hi)), sub_zero] at this
    | zero => rw [hA_zero_right']; exact zero_mem _
    | add a b _ _ ha hb => rw [hA_add_right]; exact add_mem ha hb
    | smul r a _ ha =>
      show hA X.B.I (v j) ((r : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • a) ∈ _
      rw [hA_smul_right]
      exact mul_mem_wInt X w r.2 ha
  · intro h
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hs
    refine add_mem (sum_mem fun j _ => ?_) (Submodule.mem_sup_right ht)
    by_cases hj : j ∈ S
    · exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩))
    refine Submodule.mem_sup_right (smul_mem_wLf_of_mem_wInt X w (c := c j) ?_ (hu j))
    have h1 := h j hj
    rw [hA_add_right, hA_sum_right'] at h1
    have h2 := sub_mem h1 (hA_mem_wInt X w (hv j) ht)
    rw [add_sub_cancel_right] at h2
    have h3 : ∑ i, ((c i : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) *
        (hA X.B.I (v j) (u i) - (if i = j then 1 else 0))) ∈ wInt X w :=
      sum_mem fun i _ => mul_mem_wInt X w (c i).2 (hd j i)
    have h4 : ∀ i, hA X.B.I (v j) (c i • u i) =
        (c i : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * hA X.B.I (v j) (u i) := fun i => hA_smul_right _ _ _ _
    simp only [h4] at h2
    have h5 := sub_mem h2 h3
    simpa [mul_sub, Finset.sum_sub_distrib] using h5

theorem pres_w (w : HeightOneSpectrum (𝓞 D.host.E)) {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (S : Set (VA X.B.I))
    (hS : ∀ s ∈ S, GroupLoc.ModW X w S ((X.B.I.fmat x - 1) *ᵥ s)) {y : VA X.B.I} (hy : GroupLoc.ModW X w S y) :
    GroupLoc.ModW X w S (X.B.I.fmat x *ᵥ y) := by
  have h : Submodule.span (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) S ⊔ wLf X w ≤
      (Submodule.span (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) S ⊔ wLf X w).comap (mvO X.B.I (X.B.I.fmat x)) := by
    refine sup_le (Submodule.span_le.2 fun s hs => ?_)
      (fun s hs => Submodule.mem_sup_right (fmat_mulVec_mem_wLf X w hx hs))
    show GroupLoc.ModW X w S (X.B.I.fmat x *ᵥ s)
    have e : X.B.I.fmat x *ᵥ s = s + (X.B.I.fmat x - 1) *ᵥ s := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [e]
    exact add_mem (Submodule.mem_sup_left (Submodule.subset_span hs)) (hS s hs)
  exact h hy

theorem modW_mono {w : HeightOneSpectrum (𝓞 D.host.E)} {S T : Set (VA X.B.I)} (h : S ⊆ T) {y : VA X.B.I}
    (hy : GroupLoc.ModW X w S y) : GroupLoc.ModW X w T y :=
  (sup_le_sup_right (Submodule.span_mono h) _ : Submodule.span _ S ⊔ wLf X w ≤ _) hy

theorem condAt_inv (w : HeightOneSpectrum (𝓞 D.host.E)) {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (h : CondAt X w x) :
    CondAt X w x⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := h
  have key : ∀ (S : Set (VA X.B.I)) (y : VA X.B.I), (∀ s ∈ S, GroupLoc.ModW X w S ((X.B.I.fmat x⁻¹ - 1) *ᵥ s)) →
      GroupLoc.ModW X w S ((X.B.I.fmat x - 1) *ᵥ y) → GroupLoc.ModW X w S ((X.B.I.fmat x⁻¹ - 1) *ᵥ y) := fun S y hS hy => by
    rw [inv_id]
    exact neg_mem (pres_w X w (K_inv _ hx) S hS hy)
  have e1 : ∀ m : ℕ, ∀ a : Fin D.R.rS, a.1 < m →
      GroupLoc.ModW X w (X.e0 '' {b | b.1 < a.1}) ((X.B.I.fmat x⁻¹ - 1) *ᵥ X.e0 a) := by
    intro m
    induction m with
    | zero => intro a h; exact absurd h (Nat.not_lt_zero _)
    | succ m ih =>
      intro a ha
      refine key _ _ ?_ (h1 a)
      rintro _ ⟨b, hb, rfl⟩
      have hb' : b.1 < a.1 := hb
      exact modW_mono X (Set.image_mono (lt_sub hb'.le)) (ih b (by omega))
  have e3 : ∀ m : ℕ, ∀ i : Fin D.R.k, i.1 < m →
      GroupLoc.ModW X w (Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1}) ((X.B.I.fmat x⁻¹ - 1) *ᵥ X.bw i) := by
    intro m
    induction m with
    | zero => intro a h; exact absurd h (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi
      refine key _ _ ?_ (h3 i)
      rintro _ (⟨b, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact modW_mono X ((Set.image_subset_range _ _).trans Set.subset_union_left) (e1 _ b (Nat.lt_succ_self _))
      · have hj' : j.1 < i.1 := hj
        exact modW_mono X (Set.union_subset_union_right _ (Set.image_mono (lt_sub hj'.le))) (ih j (by omega))
  refine ⟨fun a => e1 _ a (Nat.lt_succ_self _), key _ _ ?_ h2, fun i => e3 _ i (Nat.lt_succ_self _)⟩
  rintro _ ⟨b, rfl⟩
  exact modW_mono X (Set.image_subset_range _ _) (e1 _ b (Nat.lt_succ_self _))

theorem rank_eq (D : D7) : D.R.r = 2 * D.R.rS + D.R.k + 1 := by
  have := D.R.rS_two
  unfold Ranks.r
  omega

theorem span_frame (w : HeightOneSpectrum (𝓞 D.host.E)) (k : Fin 2)
    (hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) (u : Fin D.R.r → VA X.B.I)
    (he : ∀ a, GroupLoc.ModW X w (Set.range u) (X.e0 a)) (hf : ∀ a, GroupLoc.ModW X w (Set.range u) (X.f0 a))
    (hz : GroupLoc.ModW X w (Set.range u) X.z0) (hb : ∀ a, GroupLoc.ModW X w (Set.range u) (X.bw a))
    (hb' : ∀ a, GroupLoc.ModW X w (Set.range u) (X.bwd a)) {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) :
    GroupLoc.ModW X w (Set.range u) y := by
  have h := X.latticeSpan y hy
  refine (sup_le (Submodule.span_le.2 ?_) (le_trans ?_ le_sup_right) :
    _ ≤ Submodule.span (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) (Set.range u) ⊔ wLf X w) h
  · rintro _ ((((⟨a, rfl⟩ | ⟨a, rfl⟩) | rfl) | ⟨a, rfl⟩) | ⟨a, rfl⟩)
    exacts [he a, hf a, hz, hb a, hb' a]
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact smul_mem_wLf_of_mem_wInt X w (wInt_of_zmod X k hg ⟨1, one_mem _, (mul_one _).symm⟩) hx

theorem flagV_mem {e f : Fin D.R.rS → VA X.B.I} {b : Fin D.R.k → VA X.B.I} {z : VA X.B.I}
    (he : ∀ a, e a ∈ X.B.I.Lf) (hf : ∀ a, f a ∈ X.B.I.Lf) (hb : ∀ a, b a ∈ X.B.I.Lf) (hz : z ∈ X.B.I.Lf)
    (i : Fin D.R.r) : flagV D.R.rS D.R.k D.R.r e f b z i ∈ X.B.I.Lf := by
  unfold flagV
  split_ifs
  exacts [he _, hb _, hz, hf _, zero_mem _]

theorem modW_range {w : HeightOneSpectrum (𝓞 D.host.E)} {u : Fin D.R.r → VA X.B.I} {y : VA X.B.I} (i : Fin D.R.r)
    (h : u i = y) : GroupLoc.ModW X w (Set.range u) y :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨i, h⟩)

theorem one_sub_ew (w : HeightOneSpectrum (𝓞 D.host.E)) (k : Fin 2)
    (hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) (h : EwAt X w) : 1 - X.ew ∈ wInt X w := by
  have h1 := hA_mem_wInt X w X.vectorsInLattice.2.1 (h _ X.vectorsInLattice.2.1)
  rw [hA_smul_right] at h1
  have h2 := mul_mem_wInt X w (sub_mem (one_mem _) X.ew_int) (wInt_of_zmod X k hg X.formsAtZero.1)
  have h3 := sub_mem h2 h1
  rwa [mul_add, add_sub_cancel_left, mul_one] at h3

open Classical in

def epsD (w : HeightOneSpectrum (𝓞 D.host.E)) : Fin D.R.k → VA X.B.I :=
  if EwAt X w then X.bwd else fun i => X.bw (Fin.rev i)

def dualVec (w : HeightOneSpectrum (𝓞 D.host.E)) : Fin D.R.r → VA X.B.I :=
  flagV D.R.rS D.R.k D.R.r X.f0 X.e0 (epsD X w) (-X.z0)

theorem hA_neg_left (x y : VA X.B.I) : hA X.B.I (-x) y = -hA X.B.I x y := by
  rw [← neg_one_smul (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) x, hA_smul_left, map_neg, map_one, neg_one_mul]

theorem hA_adj (x : X.B.I.Gf) (a b : VA X.B.I) :
    hA X.B.I b ((X.B.I.fmat x⁻¹ - 1) *ᵥ a) = sigA X.B.I (hA X.B.I a ((X.B.I.fmat x - 1) *ᵥ b)) := by
  have h := GlobalTheory.St.G.FrameClose.hA_unitary x b (X.B.I.fmat x⁻¹ *ᵥ a)
  have e : X.B.I.fmat x * X.B.I.fmat x⁻¹ = 1 := by rw [← fmat_mul, mul_inv_cancel, fmat_one]
  rw [Matrix.mulVec_mulVec, e, Matrix.one_mulVec] at h
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right, map_sub]
  rw [← h, ← hA_symm, ← hA_symm]

theorem colCond_iff_condAt : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ k ∈ X.B.I.Kset, ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (GlobalTheory.Mem.GroupLoc.ColCond X (D.naut.plGw kv.1 kv.2) k ↔ GlobalTheory.Mem.GroupLoc.CondAt X (D.naut.plGw kv.1 kv.2) k ∧ GlobalTheory.Mem.GroupLoc.CondAt X (GlobalTheory.DimPartsCompare.cPl (D.naut.plGw kv.1 kv.2)) k) := by
  intro D X hI hι hgs x hx kv
  have hg := hgs kv
  have hn := rank_eq D
  have hA_e0 := hA_e0_symVec D X kv hg
  have hA_z0 := ZPair.hA_z0_symVec D X kv hg
  have hA_bw := Resid.hA_bw_symVec_not_ewAt D X kv hg
  have hsig := sigA_ew_sub_one_mem_wInt D X hI hι kv hg
  generalize D.naut.plGw kv.1 kv.2 = w at *
  have hg' : ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (cPl w).asIdeal := by rw [mem_cPl, map_natCast]; exact hg
  obtain ⟨ief, iz, ib⟩ := X.vectorsInLattice
  have hse := sigA_mem X.B.I X.ew_int

  have p1 : EwAt X w → sigA X.B.I X.ew ∈ wInt X w := fun h => by
    have := mul_mem_wInt X w hse (one_sub_ew X w kv.1 hg h)
    rwa [mul_sub, mul_one, mul_comm, X.ew_orth, sub_zero] at this
  have p2 : ¬ EwAt X w → X.ew ∈ wInt X w := fun h => by
    have := neg_mem (mul_mem_wInt X w X.ew_int (hsig h))
    rwa [mul_sub, mul_one, X.ew_orth, zero_sub, neg_neg] at this
  have q1 : EwAt X w → ∀ i, X.bwd i ∈ wLf X w := fun h i => by
    rw [X.bwd_w]; exact smul_mem_wLf_of_mem_wInt X w (p1 h) (ib i).2
  have q2 : EwAt X w → ∀ i, X.bw i ∈ wLf X (cPl w) := fun h i => by
    have := sig_mem X w (p1 h)
    rw [sigA_sigA] at this
    rw [X.bw_w]; exact smul_mem_wLf_of_mem_wInt X _ this (ib i).1
  have q3 : ¬ EwAt X w → ∀ i, X.bw i ∈ wLf X w := fun h i => by
    rw [X.bw_w]; exact smul_mem_wLf_of_mem_wInt X w (p2 h) (ib i).1
  have q4 : ¬ EwAt X w → ∀ i, X.bwd i ∈ wLf X (cPl w) := fun h i => by
    rw [X.bwd_w]; exact smul_mem_wLf_of_mem_wInt X _ (sig_mem X w (p2 h)) (ib i).2
  have hu : ∀ i, symVec X w i ∈ X.B.I.Lf :=
    flagV_mem X (fun a => (ief a).1) (fun a => (ief a).2)
      (fun a => by unfold epsW; split_ifs; exacts [(ib _).1, (ib _).2]) iz
  have hv : ∀ i, dualVec X w i ∈ X.B.I.Lf :=
    flagV_mem X (fun a => (ief a).2) (fun a => (ief a).1)
      (fun a => by unfold epsD; split_ifs; exacts [(ib _).2, (ib _).1]) (neg_mem iz)

  have hd : ∀ j i, hA X.B.I (dualVec X w j) (symVec X w i) - (if i = j then 1 else 0) ∈ wInt X w := by
    intro j i
    have hj := j.2
    unfold dualVec
    by_cases a1 : j.1 < D.R.rS
    · rw [fl_e _ _ _ _ j ⟨j.1, a1⟩ rfl]
      exact hA_symVec_sub_ite_mem_wInt D X w kv.1 hg ⟨j.1, a1⟩ i
    by_cases a2 : j.1 < D.R.rS + D.R.k
    · rw [fl_b _ _ _ _ j ⟨j.1 - D.R.rS, by omega⟩ (by simp only; omega)]
      unfold epsD
      by_cases h : EwAt X w
      · rw [if_pos h]
        have := Resid.hA_bwd_symVec D X w kv.1 hg h (one_sub_ew X w kv.1 hg h) ⟨j.1 - D.R.rS, by omega⟩ i
        rwa [show Resid.posB D ⟨j.1 - D.R.rS, by omega⟩ = j from Fin.ext (by simp only [Resid.posB]; omega)] at this
      · rw [if_neg h]
        have := hA_bw h (hsig h) (Fin.rev ⟨j.1 - D.R.rS, by omega⟩) i
        rwa [show D.R.rS + D.R.k - 1 - (Fin.rev (⟨j.1 - D.R.rS, by omega⟩ : Fin D.R.k)).1 = j.1 by
          rw [Fin.val_rev]; simp only; omega, if_congr Fin.val_inj rfl rfl] at this
    by_cases a3 : j.1 = D.R.rS + D.R.k
    · rw [symmetricFlagBasisVectors_apply_centre _ _ _ _ j a3, hA_neg_left]
      have := neg_mem (hA_z0 i)
      rw [← a3, if_congr Fin.val_inj rfl rfl] at this
      convert this using 1
      split_ifs <;> ring
    · rw [fl_f _ _ _ _ j ⟨2 * D.R.rS + D.R.k - j.1, by omega⟩ (by simp only; omega)]
      have := hA_e0 ⟨2 * D.R.rS + D.R.k - j.1, by omega⟩ i
      rwa [show 2 * D.R.rS + D.R.k - (⟨2 * D.R.rS + D.R.k - j.1, by omega⟩ : Fin D.R.rS).1 = j.1 by
          simp only; omega, if_congr Fin.val_inj rfl rfl] at this
  have hd' : ∀ i j, hA X.B.I (symVec X w i) (dualVec X w j) - (if j = i then 1 else 0) ∈ wInt X (cPl w) := by
    intro i j
    have := sig_mem X w (hd j i)
    rwa [map_sub, ← hA_symm, apply_ite (sigA X.B.I), map_one, map_zero, if_congr eq_comm rfl rfl] at this

  have su : ∀ y ∈ X.B.I.Lf, GroupLoc.ModW X w (Set.range (symVec X w)) y := fun y hy => by
    refine span_frame X w kv.1 hg _ (fun a => ?_) (fun a => ?_) ?_ (fun a => ?_) (fun a => ?_) hy
    · have := a.2
      exact modW_range X ⟨a.1, by omega⟩ (fl_e _ _ _ _ _ a rfl)
    · have := a.2
      exact modW_range X ⟨2 * D.R.rS + D.R.k - a.1, by omega⟩ (fl_f _ _ _ _ _ a (by simp only; omega))
    · exact modW_range X ⟨D.R.rS + D.R.k, by omega⟩ (symmetricFlagBasisVectors_apply_centre _ _ _ _ _ rfl)
    · have := a.2
      by_cases h : EwAt X w
      · exact modW_range X ⟨D.R.rS + a.1, by omega⟩ ((fl_b _ _ _ _ _ a rfl).trans (by rw [epsW, if_pos h]))
      · exact Submodule.mem_sup_right (q3 h a)
    · have := a.rev.2
      by_cases h : EwAt X w
      · exact Submodule.mem_sup_right (q1 h a)
      · exact modW_range X ⟨D.R.rS + a.rev.1, by omega⟩ ((fl_b _ _ _ _ _ a.rev rfl).trans
          (by rw [epsW, if_neg h]; exact congrArg X.bwd (Fin.rev_rev a)))
  have sv : ∀ y ∈ X.B.I.Lf, GroupLoc.ModW X (cPl w) (Set.range (dualVec X w)) y := fun y hy => by
    refine span_frame X _ kv.1 hg' _ (fun a => ?_) (fun a => ?_) ?_ (fun a => ?_) (fun a => ?_) hy
    · have := a.2
      exact modW_range X ⟨2 * D.R.rS + D.R.k - a.1, by omega⟩ (fl_f _ _ _ _ _ a (by simp only; omega))
    · have := a.2
      exact modW_range X ⟨a.1, by omega⟩ (fl_e _ _ _ _ _ a rfl)
    · exact neg_mem_iff.1 (modW_range X ⟨D.R.rS + D.R.k, by omega⟩ (symmetricFlagBasisVectors_apply_centre _ _ _ _ _ rfl))
    · have := a.rev.2
      by_cases h : EwAt X w
      · exact Submodule.mem_sup_right (q2 h a)
      · exact modW_range X ⟨D.R.rS + a.rev.1, by omega⟩ ((fl_b _ _ _ _ _ a.rev rfl).trans
          (by rw [epsD, if_neg h]; exact congrArg X.bw (Fin.rev_rev a)))
    · have := a.2
      by_cases h : EwAt X w
      · exact modW_range X ⟨D.R.rS + a.1, by omega⟩ ((fl_b _ _ _ _ _ a rfl).trans (by rw [epsD, if_pos h]))
      · exact Submodule.mem_sup_right (q4 h a)
  have sub_w : ∀ (w' : HeightOneSpectrum (𝓞 D.host.E)) (y : X.B.I.Gf), y ∈ X.B.I.Kset → ∀ s ∈ wLf X w',
      (X.B.I.fmat y - 1) *ᵥ s ∈ wLf X w' := fun w' y hy s hs => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem (fmat_mulVec_mem_wLf X w' hy hs) hs
  have main := comb (R := Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hn X.e0 X.f0 X.z0 X.bw (epsW X w) (epsD X w) (wLf X w)
    (wLf X (cPl w)) (fun y => (X.B.I.fmat x - 1) *ᵥ y) (fun y => (X.B.I.fmat x⁻¹ - 1) *ᵥ y)
    (Matrix.mulVec_neg _ _)
    (fun j i => hA X.B.I (dualVec X w j) ((X.B.I.fmat x - 1) *ᵥ symVec X w i) ∈ wInt X w)
    (fun i S => coords X w _ _ hu hv hd (su _ (K_sub_mv _ hx (hu i))) S)
    (fun j S => (coords X (cPl w) _ _ hv hu hd' (sv _ (K_sub_mv _ (K_inv _ hx) (hv j))) S).trans
      (forall₂_congr fun i _ => by
        rw [hA_adj]
        refine ⟨fun h => ?_, sig_mem X w⟩
        have := sig_mem X _ h
        rwa [sigA_sigA, cPl_cPl] at this))
    (by
      by_cases h : EwAt X w
      · exact Or.inl ⟨by rw [epsW, if_pos h], fun i => sub_w _ _ (K_inv _ hx) _ (q2 h i)⟩
      · exact Or.inr ⟨by rw [epsD, if_neg h], fun i => sub_w _ _ hx _ (q3 h i)⟩)
  refine Iff.trans main (and_congr Iff.rfl ⟨fun h => ?_, fun h => condAt_inv X _ hx h⟩)
  have := condAt_inv X (cPl w) (K_inv _ hx) h
  rwa [inv_inv] at this

end GlobalTheory.Mem.GroupLoc.Dual

end
