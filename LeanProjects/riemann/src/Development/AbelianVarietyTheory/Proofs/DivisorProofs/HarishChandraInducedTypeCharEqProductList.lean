import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsCharOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockParabolicUnitriangularSubgroupsGLnPrimeFiel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypeCharacterConjugateInverse

noncomputable section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel GlobalTheory.GLq
open scoped Classical

namespace GlobalTheory.TypeCharProduct

section Abstract

variable {G L : Type} [Group G] [Fintype G] [Group L] [Fintype L]

def ind (P : G → Prop) (f : G → ℂ) (x : G) : ℂ :=
  ((Finset.univ.filter P).card : ℂ)⁻¹ * ∑ y : G, if P (y⁻¹ * x * y) then f (y⁻¹ * x * y) else 0

theorem ind_congr {P P' : G → Prop} {f f' : G → ℂ} (w : G) (hP : ∀ g, P g ↔ P' (w⁻¹ * g * w))
    (hf : ∀ g, P g → f g = f' (w⁻¹ * g * w)) : ind P f = ind P' f' := by
  funext x
  unfold ind
  congr 1
  · congr 2
    refine Finset.card_bijective (fun g => w⁻¹ * g * w) ?_ (by simpa using hP)
    exact ((Equiv.mulLeft w⁻¹).trans (Equiv.mulRight w)).bijective
  · refine Fintype.sum_equiv (Equiv.mulRight w) _ _ fun y => ?_
    have h : (Equiv.mulRight w y)⁻¹ * x * (Equiv.mulRight w y) = w⁻¹ * (y⁻¹ * x * y) * w := by
      simp only [Equiv.coe_mulRight]
      group
    rw [h]
    by_cases hy : P (y⁻¹ * x * y)
    · rw [if_pos hy, if_pos ((hP _).1 hy), hf _ hy]
    · rw [if_neg hy, if_neg fun h' => hy ((hP _).2 h')]

theorem sum_comp_surj (Q : Subgroup G) (π : Q →* L) (hπ : Function.Surjective π) (F : L → ℂ) :
    (Fintype.card L : ℂ) * ∑ q : Q, F (π q) = (Fintype.card Q : ℂ) * ∑ l, F l := by
  have h1 : ∀ l : L, ∑ q : Q, F (π q) = ∑ q : Q, F (π q * l) := by
    intro l
    obtain ⟨s, rfl⟩ := hπ l
    symm
    exact Fintype.sum_equiv (Equiv.mulRight s) _ _ fun q => by simp
  have h2 : ∀ q : Q, ∑ l, F (π q * l) = ∑ l, F l := fun q =>
    Fintype.sum_equiv (Equiv.mulLeft (π q)) _ _ fun l => by simp
  calc (Fintype.card L : ℂ) * ∑ q : Q, F (π q) = ∑ _l : L, ∑ q : Q, F (π q) := by simp
    _ = ∑ l : L, ∑ q : Q, F (π q * l) := Finset.sum_congr rfl fun l _ => h1 l
    _ = ∑ q : Q, ∑ l : L, F (π q * l) := Finset.sum_comm
    _ = _ := by simp [h2]

theorem ind_trans (Q : Subgroup G) (π : G → L) (hmul : ∀ a ∈ Q, ∀ b ∈ Q, π (a * b) = π a * π b)
    (hπ : ∀ l, ∃ q ∈ Q, π q = l) (A : G → ℂ) (hA : ∀ z ∈ Q, ∀ q ∈ Q, A (q⁻¹ * z * q) = A z)
    (P' : L → Prop) (f' : L → ℂ) :
    ind (fun g => g ∈ Q) (fun g => A g * ind P' f' (π g)) =
      ind (fun g => g ∈ Q ∧ P' (π g)) (fun g => A g * f' (π g)) := by
  funext x
  let φ : Q →* L := MonoidHom.mk' (fun q => π q) fun a b => hmul _ a.2 _ b.2
  have hφ : Function.Surjective φ := fun l => by
    obtain ⟨q, hq, rfl⟩ := hπ l
    exact ⟨⟨q, hq⟩, rfl⟩
  have hL : (Fintype.card L : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hQ : (Fintype.card Q : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcQ : (Finset.univ.filter fun g => g ∈ Q).card = Fintype.card Q := by
    rw [Fintype.card_subtype]
  have hc : (Fintype.card L : ℂ) * ((Finset.univ.filter fun g => g ∈ Q ∧ P' (π g)).card : ℂ) =
      (Fintype.card Q : ℂ) * ((Finset.univ.filter P').card : ℂ) := by
    have h := sum_comp_surj Q φ hφ fun l => if P' l then 1 else 0
    rw [Finset.sum_boole, Finset.sum_boole] at h
    rw [← h]
    congr 2
    symm
    refine Finset.card_bij (fun q _ => (q : G)) ?_ ?_ ?_
    · intro q hq
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, q.2, (Finset.mem_filter.1 hq).2⟩
    · intro a _ b _ h
      exact Subtype.ext h
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
      exact ⟨⟨g, hg.1⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hg.2⟩, rfl⟩
  set F : G → ℂ := fun g => if g ∈ Q ∧ P' (π g) then A g * f' (π g) else 0 with hF
  have key : ∀ z : G, (Fintype.card Q : ℂ) * (if z ∈ Q then A z * ind P' f' (π z) else 0) =
      ((Finset.univ.filter P').card : ℂ)⁻¹ * (Fintype.card L : ℂ) * ∑ q : Q, F ((q : G)⁻¹ * z * q) := by
    intro z
    by_cases hz : z ∈ Q
    · rw [if_pos hz]
      have h := sum_comp_surj Q φ hφ fun l => if P' (l⁻¹ * π z * l) then f' (l⁻¹ * π z * l) else 0
      have h2 : ∀ q : Q, F ((q : G)⁻¹ * z * q) =
          A z * if P' ((φ q)⁻¹ * π z * φ q) then f' ((φ q)⁻¹ * π z * φ q) else 0 := by
        intro q
        have hm : (q : G)⁻¹ * z * q ∈ Q := Q.mul_mem (Q.mul_mem (Q.inv_mem q.2) hz) q.2
        have e : π ((q : G)⁻¹ * z * q) = (φ q)⁻¹ * π z * φ q := by
          have := map_mul φ (q⁻¹ * ⟨z, hz⟩) q
          rw [map_mul φ q⁻¹, map_inv] at this
          exact this
        simp only [hF, hm, true_and, e, hA z hz q q.2, mul_ite, mul_zero]
      simp only [h2, ← Finset.mul_sum]
      unfold ind
      linear_combination (-(((Finset.univ.filter P').card : ℂ)⁻¹ * A z)) * h
    · rw [if_neg hz, mul_zero, Finset.sum_eq_zero, mul_zero]
      intro q _
      refine if_neg fun h => hz ?_
      have := Q.mul_mem (Q.mul_mem q.2 h.1) (Q.inv_mem q.2)
      simpa [mul_assoc] using this
  have hs : ∀ q : Q, ∑ y : G, F ((q : G)⁻¹ * (y⁻¹ * x * y) * q) = ∑ y : G, F (y⁻¹ * x * y) := fun q =>
    Fintype.sum_equiv (Equiv.mulRight (q : G)) _ _ fun y => by
      congr 1
      simp only [Equiv.coe_mulRight]
      group
  have h3 : (Fintype.card Q : ℂ) * ∑ y : G, (if y⁻¹ * x * y ∈ Q then A (y⁻¹ * x * y) * ind P' f' (π (y⁻¹ * x * y)) else 0) =
      (Fintype.card Q : ℂ) * (((Finset.univ.filter P').card : ℂ)⁻¹ * (Fintype.card L : ℂ) * ∑ y : G, F (y⁻¹ * x * y)) := by
    rw [Finset.mul_sum]
    simp only [key]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have h4 := mul_left_cancel₀ hQ h3
  have h5 : ((Finset.univ.filter fun g => g ∈ Q ∧ P' (π g)).card : ℂ) =
      (Fintype.card L : ℂ)⁻¹ * ((Fintype.card Q : ℂ) * ((Finset.univ.filter P').card : ℂ)) := by
    rw [← hc, inv_mul_cancel_left₀ hL]
  suffices hh : ((Finset.univ.filter fun g => g ∈ Q).card : ℂ)⁻¹ * ∑ y : G,
      (if y⁻¹ * x * y ∈ Q then A (y⁻¹ * x * y) * ind P' f' (π (y⁻¹ * x * y)) else 0) =
    ((Finset.univ.filter fun g => g ∈ Q ∧ P' (π g)).card : ℂ)⁻¹ * ∑ y : G, F (y⁻¹ * x * y) by
    rw [ind, ind]
    convert hh
  rw [h4, hcQ, h5, mul_inv, mul_inv, inv_inv]
  ring

end Abstract

variable {p : ℕ} [Fact p.Prime]

theorem coe_toG {n : ℕ} {M : Mt p n} (h : IsUnit M) : ((toG M : Gn p n) : Mt p n) = M := by
  unfold toG
  rw [dif_pos h]
  exact IsUnit.unit_spec _

def stdP (L : List (Pc p)) : (n : ℕ) → Mt p n → Prop :=
  List.rec (motive := fun _ => (n : ℕ) → Mt p n → Prop) (fun _ _ => True)
    (fun q L ih _ M => InPar q.1 M ∧ ih (degL L) (br q.1 (degL L) M)) L

def stdF (L : List (Pc p)) : (n : ℕ) → Mt p n → ℂ :=
  List.rec (motive := fun _ => (n : ℕ) → Mt p n → ℂ) (fun _ _ => 1)
    (fun q L ih _ M => q.2 (toG (tl q.1 M)) * ih (degL L) (br q.1 (degL L) M)) L

theorem hcL_eq_ind (L : List (Pc p)) (hL : ∀ q ∈ L, IsClass q.2) :
    hcL L (degL L) = ind (fun g : Gn p (degL L) => stdP L _ (g : Mt p (degL L)))
      (fun g => stdF L _ (g : Mt p (degL L))) := by
  induction L with
  | nil =>
    funext x
    have hG : (Fintype.card (Gn p (degL ([] : List (Pc p)))) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    show 1 = ind (fun _ => True) (fun _ => 1) x
    simp only [ind, if_true, Finset.sum_const, Finset.filter_true, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    rw [inv_mul_cancel₀ hG]
  | cons q L ih =>
    obtain ⟨⟨Q, hQ⟩, -, hu, hm, hfib, -⟩ :=
      GlobalTheory.GLm.ParBasic.par_basic p q.1 (degL L) (degL (q :: L)) rfl
    have htl : ∀ a ∈ Q, ∀ b ∈ Q, toG (tl q.1 (a * b).val) =
        toG (tl q.1 a.val) * toG (tl q.1 b.val) := by
      intro a ha b hb
      apply Units.ext
      rw [Units.val_mul (toG _), coe_toG (hu _ ((hQ _).1 ha)).1, coe_toG (hu _ ((hQ _).1 hb)).1,
        coe_toG (hu _ ((hQ _).1 (Q.mul_mem ha hb))).1]
      exact (hm _ _ ((hQ _).1 ha) ((hQ _).1 hb)).1
    have hbr : ∀ a ∈ Q, ∀ b ∈ Q, toG (br q.1 (degL L) (a * b).val) =
        toG (br q.1 (degL L) a.val) * toG (br q.1 (degL L) b.val) := by
      intro a ha b hb
      apply Units.ext
      rw [Units.val_mul (toG _), coe_toG (hu _ ((hQ _).1 ha)).2, coe_toG (hu _ ((hQ _).1 hb)).2,
        coe_toG (hu _ ((hQ _).1 (Q.mul_mem ha hb))).2]
      exact (hm _ _ ((hQ _).1 ha) ((hQ _).1 hb)).2
    have hsurj : ∀ l : Gn p (degL L), ∃ g ∈ Q, toG (br q.1 (degL L) g.val) = l := by
      intro l
      have h := hfib 1 l
      have hpos : 0 < p ^ (q.1 * degL L) := pow_pos (Fact.out : p.Prime).pos _
      rw [← h] at hpos
      obtain ⟨g, hg⟩ := Finset.card_pos.1 hpos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
      refine ⟨g, (hQ _).2 hg.1, Units.ext ?_⟩
      rw [coe_toG (hu _ hg.1).2, hg.2.2]
    have hA : ∀ z ∈ Q, ∀ y ∈ Q, q.2 (toG (tl q.1 (y⁻¹ * z * y).val)) =
        q.2 (toG (tl q.1 z.val)) := by
      intro z hz y hy
      let φ : Q →* Gn p q.1 := MonoidHom.mk' (fun a : Q => toG (tl q.1 a.val.val))
        fun a b => htl _ a.2 _ b.2
      have h := map_mul φ (⟨y, hy⟩⁻¹ * ⟨z, hz⟩) ⟨y, hy⟩
      rw [map_mul φ _ ⟨z, hz⟩, map_inv] at h
      have h2 := hL q List.mem_cons_self (φ ⟨z, hz⟩) (φ ⟨y, hy⟩)⁻¹
      rw [inv_inv, ← h] at h2
      exact h2
    have h := ind_trans (G := Gn p (degL (q :: L))) (L := Gn p (degL L)) Q
      (fun g : Gn p (degL (q :: L)) => toG (br q.1 (degL L) g.val)) hbr hsurj
      (fun g : Gn p (degL (q :: L)) => q.2 (toG (tl q.1 g.val))) hA
      (fun g : Gn p (degL L) => stdP L _ (g : Mt p (degL L))) (fun g => stdF L _ (g : Mt p (degL L)))
    rw [← ih fun q' hq' => hL q' (List.mem_cons_of_mem _ hq')] at h
    have e1 : hcL (q :: L) (degL (q :: L)) = ind (fun g : Gn p (degL (q :: L)) => InPar q.1 g.val)
        (fun g => q.2 (toG (tl q.1 g.val)) * hcL L (degL L) (toG (br q.1 (degL L) g.val))) := by
      funext x
      rw [hcL_cons]
      unfold hc hcT ind
      congr!
    rw [e1]
    refine (ind_congr 1 (fun g => ?_) fun g _ => ?_).trans (h.trans (ind_congr 1 (fun g => ?_) fun g hg => ?_))
    · simp [hQ]
    · simp
    · rw [inv_one, one_mul, mul_one, hQ]
      refine and_congr_right fun hg => ?_
      rw [coe_toG (hu _ hg).2]
      rfl
    · rw [inv_one, one_mul, mul_one, coe_toG (hu _ ((hQ _).1 hg.1)).2]
      rfl

theorem ind_eq_hcL (L : List (Pc p)) (hL : ∀ q ∈ L, IsClass q.2) (n : ℕ) (σ : Fin (degL L) → Fin n)
    (hσ : Function.Bijective σ) (P : Gn p n → Prop) (f : Gn p n → ℂ)
    (hP : ∀ g, P g ↔ stdP L _ ((g : Mt p n).submatrix σ σ))
    (hf : ∀ g, P g → f g = stdF L _ ((g : Mt p n).submatrix σ σ)) : ind P f = hcL L n := by
  have hn : degL L = n := by simpa using Fintype.card_of_bijective hσ
  subst hn
  rw [hcL_eq_ind L hL]
  let e : Fin (degL L) ≃ Fin (degL L) := Equiv.ofBijective σ hσ
  let w : Gn p (degL L) := ⟨e.symm.toPEquiv.toMatrix, e.toPEquiv.toMatrix,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp⟩
  have hw : ∀ g : Gn p (degL L), (w⁻¹ * g * w).val = g.val.submatrix σ σ := by
    intro g
    show e.toPEquiv.toMatrix * g.val * e.symm.toPEquiv.toMatrix = _
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    rfl
  refine ind_congr w (fun g => ?_) fun g hg => ?_
  · rw [hw, hP]
  · rw [hw, hf g hg]

theorem exists_enum {ι κ : Type} [LinearOrder κ] (b : ι → κ) (d : κ → ℕ) (α : ∀ c, Gn p (d c) → ℂ)
    (j : ∀ c, Fin (d c) → ι) (hj : ∀ c, Function.Injective (j c)) (hb : ∀ c t, b (j c t) = c)
    (hs : ∀ i, ∃ t, j (b i) t = i) (l : List κ) (hl : l.Pairwise (· < ·)) :
    ∃ σ : Fin (degL (l.map fun c => (⟨d c, α c⟩ : Pc p))) → ι, Function.Injective σ ∧ (∀ t, b (σ t) ∈ l) ∧
      (∀ i, b i ∈ l → ∃ t, σ t = i) ∧ ∀ M : Matrix ι ι (ZMod p),
        (stdP (l.map fun c => (⟨d c, α c⟩ : Pc p)) _ (M.submatrix σ σ) ↔
          ∀ i k, b i ∈ l → b k ∈ l → b k < b i → M i k = 0) ∧
        stdF (l.map fun c => (⟨d c, α c⟩ : Pc p)) _ (M.submatrix σ σ) =
          (l.map fun c => α c (toG (M.submatrix (j c) (j c)))).prod := by
  induction l with
  | nil =>
    refine ⟨fun t => Fin.elim0 t, fun t => Fin.elim0 t, fun t => Fin.elim0 t, by simp, fun M => ?_⟩
    simp [stdP, stdF]
  | cons c l ih =>
    rw [List.pairwise_cons] at hl
    obtain ⟨σ, h1, h2, h3, h4⟩ := ih hl.2
    let τ : Fin (d c + degL (l.map fun c => (⟨d c, α c⟩ : Pc p))) → ι := Fin.append (j c) σ
    refine ⟨τ, ?_, ?_, ?_, fun M => ?_⟩
    · refine Fin.append_injective_iff.2 ⟨hj c, h1, fun s t h => ?_⟩
      have := hl.1 _ (h2 t)
      rw [← h, hb] at this
      exact lt_irrefl _ this
    · intro t
      refine Fin.addCases (motive := fun t => b (τ t) ∈ c :: l) (fun s => ?_) (fun s => ?_) t
      · simp [τ, hb]
      · simp [τ, h2]
    · intro i hi
      rcases List.mem_cons.1 hi with h | h
      · subst h
        obtain ⟨t, ht⟩ := hs i
        exact ⟨Fin.castAdd _ t, (Fin.append_left _ _ t).trans ht⟩
      · obtain ⟨t, ht⟩ := h3 i h
        exact ⟨Fin.natAdd _ t, (Fin.append_right _ _ t).trans ht⟩
    · have etl : tl (d c) (M.submatrix τ τ) = M.submatrix (j c) (j c) := by
        ext s t
        rw [GlobalTheory.GLm.ParBasic.tl_apply]
        simp [τ]
      have ebr : br (d c) _ (M.submatrix τ τ) = M.submatrix σ σ := by
        ext s t
        rw [GlobalTheory.GLm.ParBasic.br_apply]
        simp [τ]
      constructor
      · show InPar (d c) (M.submatrix τ τ) ∧ stdP _ _ (br (d c) _ (M.submatrix τ τ)) ↔ _
        rw [ebr, (h4 M).1, GlobalTheory.GLm.ParBasic.inPar_iff]
        simp only [τ, Matrix.submatrix_apply, Fin.append_left, Fin.append_right]
        constructor
        · rintro ⟨hA, hB⟩ i k hi hk hik
          rcases List.mem_cons.1 hi with hi' | hi'
          · rcases List.mem_cons.1 hk with hk' | hk'
            · rw [hi', hk'] at hik
              exact absurd hik (lt_irrefl _)
            · rw [hi'] at hik
              exact absurd hik (hl.1 _ hk').not_gt
          · rcases List.mem_cons.1 hk with hk' | hk'
            · subst hk'
              obtain ⟨s, rfl⟩ := h3 i hi'
              obtain ⟨t, ht⟩ := hs k
              rw [← ht]
              exact hA s t
            · exact hB i k hi' hk' hik
        · intro h
          refine ⟨fun s t => h _ _ (List.mem_cons_of_mem _ (h2 s)) (by simp [hb]) ?_, fun i k hi hk =>
            h i k (List.mem_cons_of_mem _ hi) (List.mem_cons_of_mem _ hk)⟩
          rw [hb]
          exact hl.1 _ (h2 s)
      · show α c (toG (tl (d c) (M.submatrix τ τ))) * stdF _ _ (br (d c) _ (M.submatrix τ τ)) = _
        rw [etl, ebr, (h4 M).2, List.map_cons, List.prod_cons]

theorem finrank_eigenspace_le {k ι : Type} [Field k] [Fintype ι] [DecidableEq ι] (u v h : Matrix ι ι k)
    (hvu : v * u = 1) (z : k) :
    Module.finrank k (Module.End.eigenspace (Matrix.toLin' h) z) ≤
      Module.finrank k (Module.End.eigenspace (Matrix.toLin' (u * h * v)) z) := by
  have hm : ∀ x ∈ Module.End.eigenspace (Matrix.toLin' h) z,
      Matrix.toLin' u x ∈ Module.End.eigenspace (Matrix.toLin' (u * h * v)) z := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    simp only [Matrix.toLin'_apply] at hx ⊢
    rw [Matrix.mulVec_mulVec, mul_assoc, hvu, mul_one, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]
  refine LinearMap.finrank_le_finrank_of_injective (f := (Matrix.toLin' u).restrict hm) fun x y hxy => ?_
  have h1 : u.mulVec x = u.mulVec y := congrArg Subtype.val hxy
  have h2 := congrArg v.mulVec h1
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hvu, Matrix.one_mulVec, Matrix.one_mulVec] at h2
  exact Subtype.ext h2

theorem finrank_eigenspace_conj {k ι : Type} [Field k] [Fintype ι] [DecidableEq ι] (u v h : Matrix ι ι k)
    (hvu : v * u = 1) (z : k) :
    Module.finrank k (Module.End.eigenspace (Matrix.toLin' (u * h * v)) z) =
      Module.finrank k (Module.End.eigenspace (Matrix.toLin' h) z) := by
  refine le_antisymm ?_ (finrank_eigenspace_le u v h hvu z)
  have := finrank_eigenspace_le v u (u * h * v) (mul_eq_one_comm.1 hvu) z
  rwa [show v * (u * h * v) * u = (v * u) * h * (v * u) by simp only [mul_assoc], hvu, one_mul, mul_one] at this

theorem cuspChar_conj {ι : Type} [Fintype ι] [DecidableEq ι] (θ : Tor p (Fintype.card ι) →* ℂˣ)
    (u v h : Matrix ι ι (ZMod p)) (hvu : v * u = 1) : cuspChar θ (u * h * v) = cuspChar θ h := by
  have h1 : (u * h * v).charpoly = h.charpoly := by
    rw [Matrix.charpoly_mul_comm, ← mul_assoc, hvu, one_mul]
  have h2 : v.map (algebraMap (ZMod p) (Fbar p)) * u.map (algebraMap (ZMod p) (Fbar p)) = 1 := by
    rw [← Matrix.map_mul, hvu, Matrix.map_one _ (map_zero _) (map_one _)]
  have h3 : ∀ z, Module.finrank (Fbar p) (Module.End.eigenspace
      (Matrix.toLin' ((u * h * v).map (algebraMap (ZMod p) (Fbar p)))) z) =
      Module.finrank (Fbar p) (Module.End.eigenspace (Matrix.toLin' (h.map (algebraMap (ZMod p) (Fbar p)))) z) := by
    intro z
    rw [Matrix.map_mul, Matrix.map_mul, finrank_eigenspace_conj _ _ _ h2]
  unfold cuspChar
  simp only [h1, h3]

theorem isClass_cuspOn {ι : Type} [Fintype ι] [DecidableEq ι] (θ : Tor p (Fintype.card ι) →* ℂˣ) :
    IsClass (cuspOn θ) := by
  intro x y
  unfold cuspOn
  rw [Units.val_mul, Units.val_mul, ← Matrix.submatrix_mul_equiv _ _ _ (Fintype.equivFin ι),
    ← Matrix.submatrix_mul_equiv _ _ _ (Fintype.equivFin ι)]
  refine cuspChar_conj θ _ _ _ ?_
  rw [Matrix.submatrix_mul_equiv, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.submatrix_one_equiv]

theorem cuspOn_toG {ι : Type} [Fintype ι] [DecidableEq ι] (θ : Tor p (Fintype.card ι) →* ℂˣ)
    (h h' : Matrix ι ι (ZMod p)) (hh : h * h' = 1) :
    cuspOn θ (toG (h.submatrix (Fintype.equivFin ι).symm (Fintype.equivFin ι).symm)) = cuspChar θ h := by
  unfold cuspOn
  rw [coe_toG]
  · simp
  · refine IsUnit.of_mul_eq_one (h'.submatrix (Fintype.equivFin ι).symm (Fintype.equivFin ι).symm) ?_
    rw [Matrix.submatrix_mul_equiv, hh, Matrix.submatrix_one_equiv]

theorem typeChar_eq_hcL : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) (s : SSParam p ℂ r), ∃ l : List (Cyc s.1), l.Nodup ∧ (∀ c, c ∈ l) ∧
    typeChar s = GlobalTheory.GLq.hcL (l.map fun c => (⟨cycLen s.1 c, cuspOn (s.2 c)⟩ : GlobalTheory.GLq.Pc p)) r := by
  intro p _ r s
  let l : List (Cyc s.1) := Finset.univ.sort (· ≤ ·)
  have hmem : ∀ c, c ∈ l := fun c => by simp [l]
  have hnd : l.Nodup := Finset.sort_nodup _ _
  have hl : l.Pairwise (· < ·) := by
    have h : l.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
    exact (h.and hnd).imp fun h => lt_of_le_of_ne h.1 h.2
  refine ⟨l, hnd, hmem, ?_⟩
  let b : Fin r → Cyc s.1 := fun i => ⟨s.1 i, i, rfl⟩
  let j : ∀ c : Cyc s.1, Fin (cycLen s.1 c) → Fin r := fun c t =>
    ((Fintype.equivFin {i : Fin r // s.1 i = c.1}).symm t).1
  obtain ⟨σ, h1, -, h3, h4⟩ := exists_enum b (cycLen s.1) (fun c => cuspOn (s.2 c)) j
    (fun c => Subtype.val_injective.comp (Equiv.injective _))
    (fun c t => Subtype.ext ((Fintype.equivFin {i : Fin r // s.1 i = c.1}).symm t).2)
    (fun i => ⟨Fintype.equivFin {k : Fin r // s.1 k = (b i).1} ⟨i, rfl⟩, by simp [j]⟩) l hl
  rw [← ind_eq_hcL _ (fun q hq => ?_) r σ ⟨h1, fun i => h3 i (hmem _)⟩
    (fun g => (g : Mt p r).BlockTriangular s.1)
    (fun g => ∏ c : Cyc s.1, cuspChar (s.2 c) ((g : Mt p r).toSquareBlock s.1 c.1)) (fun g => ?_) fun g hg => ?_]
  · funext x
    unfold typeChar ind
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr!
  · obtain ⟨c, -, rfl⟩ := List.mem_map.1 hq
    exact isClass_cuspOn (s.2 c)
  · rw [(h4 _).1]
    exact ⟨fun h i k _ _ hik => h hik, fun h i k hik => h i k (hmem _) (hmem _) hik⟩
  · refine Eq.trans ?_ (h4 _).2.symm
    rw [← List.prod_toFinset (l := l) _ hnd]
    refine Finset.prod_congr (by ext c; simp [hmem]) fun c _ => ?_
    exact (cuspOn_toG (s.2 c) _ _ (GlobalTheory.TypeCharacterConjugateInverse.toSquareBlock_mul_inv g hg c.1)).symm

end GlobalTheory.TypeCharProduct

end
