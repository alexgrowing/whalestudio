import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIntegralIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem cj_int (L : LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at hx ⊢
  exact hx.map L.cj

theorem hf_sum_left (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) {ι : Type} (s : Finset ι)
    (a : ι → Fin n → E) (y : Fin n → E) : hf L H (∑ i ∈ s, a i) y = ∑ i ∈ s, hf L H (a i) y := by
  induction s using Finset.cons_induction with
  | empty => simp [hf]
  | cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, hf_add_left, ih]

theorem hf_sum_right (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) {ι : Type} (s : Finset ι)
    (a : ι → Fin n → E) (y : Fin n → E) : hf L H y (∑ i ∈ s, a i) = ∑ i ∈ s, hf L H y (a i) := by
  induction s using Finset.cons_induction with
  | empty => simp [hf]
  | cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, hf_add_right, ih]

theorem mem_perp_span (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (s : Set (Fin n → E))
    (x : Fin n → E) : x ∈ perp L H (Submodule.span E s) ↔ ∀ y ∈ s, hf L H x y = 0 := by
  have hmem : x ∈ perp L H (Submodule.span E s) ↔ ∀ y ∈ Submodule.span E s, hf L H x y = 0 := Iff.rfl
  rw [hmem]
  constructor
  · intro hx y hy
    exact hx y (Submodule.subset_span hy)
  · intro h y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact h z hz
    | zero => simp [hf]
    | add u v _ _ hu hv => rw [hf_add_right, hu, hv, add_zero]
    | smul c u _ hu => rw [hf_smul_right, hu, mul_zero]

section General
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem spanTo_eq (g : Fin (r + 1) → S.V) :
    S.spanTo g r = Submodule.span E (Set.range fun j : Fin r => g j.castSucc) := by
  unfold Frames.spanTo
  congr 1
  ext v
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j.castSucc, j.isLt, rfl⟩

def proj (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) : S.V →ₗ[E] S.V where
  toFun v := v - ∑ j, hf L S.Hm v (gs j) • g j.castSucc - ∑ j, hf L S.Hm v (g j.castSucc) • gs j
  map_add' a b := by
    simp only [hf_add_left, add_smul, Finset.sum_add_distrib]; abel
  map_smul' c a := by
    simp only [hf_smul_left, mul_smul, RingHom.id_apply, smul_sub, Finset.smul_sum]

theorem proj_apply (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (v : S.V) : proj S g gs v =
    v - ∑ j, hf L S.Hm v (gs j) • g j.castSucc - ∑ j, hf L S.Hm v (g j.castSucc) • gs j := rfl

def innerOf (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (Λ : Submodule L.O S.V) : Submodule L.O S.V :=
  (perp L S.Hm (S.spanTo g r)).restrictScalars L.O ⊓ Λ.comap ((proj S g gs).restrictScalars L.O)

theorem mem_innerOf (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (Λ : Submodule L.O S.V) (x : S.V) :
    x ∈ innerOf S g gs Λ ↔ (∀ j : Fin r, hf L S.Hm x (g j.castSucc) = 0) ∧ proj S g gs x ∈ Λ := by
  simp only [innerOf, Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_comap,
    LinearMap.coe_restrictScalars, spanTo_eq, mem_perp_span, Set.forall_mem_range]

theorem inner_spec (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (Λ : Submodule L.O S.V)
    (hg : ∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0)
    (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (hi : ∀ i j, hf L S.Hm (gs i) (gs j) = 0)
    (hΛ : IsSD L S.Hm Λ) (hgΛ : ∀ a, g a ∈ Λ) (hsΛ : ∀ j, gs j ∈ Λ)
    (c : E) (hc : c ∈ L.O) (hcz : c * hf L S.Hm (g (Fin.last r)) (g (Fin.last r)) = 1) :
    S.IsInner g gs (innerOf S g gs Λ) ∧ Λ = S.stdLat g gs (innerOf S g gs Λ) := by
  have hsym : ∀ x y, hf L S.Hm y x = L.cj (hf L S.Hm x y) := hf_symm L S.herm.1
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, hf L S.Hm x y ∈ L.O := fun x hx y hy => (hΛ.2 y).2 hy x hx
  have hsm : ∀ c ∈ L.O, ∀ x ∈ Λ, c • x ∈ Λ := fun c hc x hx => Λ.smul_mem ⟨c, hc⟩ hx
  have hsg : ∀ a (j : Fin r), hf L S.Hm (gs j) (g a) = if a = j.castSucc then 1 else 0 := by
    intro a j
    rw [hsym, hd]
    split_ifs <;> simp
  have hgg : ∀ i j : Fin r, hf L S.Hm (gs j) (g i.castSucc) = if i = j then 1 else 0 := by
    intro i j
    rw [hsg]
    simp [Fin.castSucc_inj]
  have hA1 : ∀ v (i : Fin r), hf L S.Hm (proj S g gs v) (g i.castSucc) = 0 := by
    intro v i
    simp only [proj_apply, hf_sub_left, hf_sum_left, hf_smul_left, hg, mul_zero,
      Finset.sum_const_zero, sub_zero, hgg, mul_ite, mul_one, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, sub_self]
  have hA2 : ∀ v (i : Fin r), hf L S.Hm (proj S g gs v) (gs i) = 0 := by
    intro v i
    simp only [proj_apply, hf_sub_left, hf_sum_left, hf_smul_left, hi, hd, Fin.castSucc_inj, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, sub_self]
  have hB : ∀ v, v = proj S g gs v + ∑ j, hf L S.Hm v (gs j) • g j.castSucc +
      ∑ j, hf L S.Hm v (g j.castSucc) • gs j := by
    intro v
    rw [proj_apply]
    abel
  have hD : ∀ v, (∀ j : Fin r, hf L S.Hm v (g j.castSucc) = 0) → (∀ j, hf L S.Hm v (gs j) = 0) →
      proj S g gs v = v := by
    intro v h1 h2
    simp [proj_apply, h1, h2]
  have hC : ∀ v ∈ Λ, proj S g gs v ∈ Λ := by
    intro v hv
    rw [proj_apply]
    exact Λ.sub_mem (Λ.sub_mem hv (Λ.sum_mem fun j _ => hsm _ (hint _ hv _ (hsΛ j)) _ (hgΛ _)))
      (Λ.sum_mem fun j _ => hsm _ (hint _ hv _ (hgΛ _)) _ (hsΛ j))
  have hE : ∀ v, proj S g gs (proj S g gs v) = proj S g gs v := fun v => hD _ (hA1 v) (hA2 v)
  have hH : ∀ w, (∀ j : Fin r, hf L S.Hm w (g j.castSucc) = 0) → (∀ j, hf L S.Hm w (gs j) = 0) →
      ∀ y, hf L S.Hm w (proj S g gs y) = hf L S.Hm w y := by
    intro w h1 h2 y
    simp [proj_apply, hf_sub_right, hf_sum_right, hf_smul_right, h1, h2]
  have hH' : ∀ w, (∀ j : Fin r, hf L S.Hm w (g j.castSucc) = 0) → (∀ j, hf L S.Hm w (gs j) = 0) →
      ∀ x, hf L S.Hm (proj S g gs x) w = hf L S.Hm x w := by
    intro w h1 h2 x
    have h1' : ∀ j : Fin r, hf L S.Hm (g j.castSucc) w = 0 := fun j => by rw [hsym, h1, map_zero]
    have h2' : ∀ j, hf L S.Hm (gs j) w = 0 := fun j => by rw [hsym, h2, map_zero]
    simp [proj_apply, hf_sub_left, hf_sum_left, hf_smul_left, h1', h2']
  have hH2 : ∀ x y, (∀ j : Fin r, hf L S.Hm x (g j.castSucc) = 0) →
      (∀ j : Fin r, hf L S.Hm y (g j.castSucc) = 0) → hf L S.Hm (proj S g gs x) y = hf L S.Hm x y := by
    intro x y hx hy
    have hy' : ∀ j : Fin r, hf L S.Hm (g j.castSucc) y = 0 := fun j => by rw [hsym, hy, map_zero]
    simp [proj_apply, hf_sub_left, hf_sum_left, hf_smul_left, hx, hy']
  have hmemA := mem_innerOf S g gs Λ
  have hperpP : ∀ x, x ∈ perp L S.Hm (S.spanTo g r) ↔ ∀ j : Fin r, hf L S.Hm x (g j.castSucc) = 0 := by
    intro x
    simp only [spanTo_eq, mem_perp_span, Set.forall_mem_range]
  have hperpS : ∀ x, x ∈ perp L S.Hm (Submodule.span E (Set.range gs)) ↔
      ∀ j, hf L S.Hm x (gs j) = 0 := by
    intro x
    simp only [mem_perp_span, Set.forall_mem_range]
  have hprojA : ∀ z ∈ Λ, proj S g gs z ∈ innerOf S g gs Λ := fun z hz =>
    (hmemA _).2 ⟨hA1 z, by rw [hE]; exact hC z hz⟩
  have hPA : ∀ x ∈ S.spanTo g r,
      (∀ j : Fin r, hf L S.Hm x (g j.castSucc) = 0) ∧ proj S g gs x = 0 := by
    intro x hx
    rw [spanTo_eq] at hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      refine ⟨fun j => hg _ j, ?_⟩
      simp only [proj_apply, hd, Fin.castSucc_inj, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true, hg, Finset.sum_const_zero, sub_self]
    | zero => exact ⟨fun j => by simp [hf], map_zero _⟩
    | add u v _ _ hu hv =>
      exact ⟨fun j => by rw [hf_add_left, hu.1, hv.1, add_zero], by rw [map_add, hu.2, hv.2, add_zero]⟩
    | smul c u _ hu =>
      exact ⟨fun j => by rw [hf_smul_left, hu.1, mul_zero], by rw [map_smul, hu.2, smul_zero]⟩
  have hlast : g (Fin.last r) ∈ innerOf S g gs Λ := (hmemA _).2 ⟨fun j => hg _ j, hC _ (hgΛ _)⟩
  have hIs : S.IsInner g gs (innerOf S g gs Λ) := by
    refine ⟨fun x hx => (hmemA x).2 ⟨(hPA x hx).1, by rw [(hPA x hx).2]; exact Λ.zero_mem⟩,
      fun x hx => (hperpP x).2 ((hmemA x).1 hx).1, ?_, ?_, hlast, ?_⟩
    · have heq : innerOf S g gs Λ ⊓ (perp L S.Hm (Submodule.span E (Set.range gs))).restrictScalars L.O =
          Λ.map ((proj S g gs).restrictScalars L.O) := by
        ext x
        simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_map,
          LinearMap.coe_restrictScalars]
        constructor
        · rintro ⟨hxA, hxS⟩
          have h1 := (hmemA x).1 hxA
          have hpx : proj S g gs x = x := hD x h1.1 ((hperpS x).1 hxS)
          exact ⟨x, by rw [← hpx]; exact h1.2, hpx⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨hprojA y hy, (hperpS _).2 (hA2 y)⟩
      rw [heq]
      exact hΛ.1.1.map _
    · intro y hy
      have hyg := (hperpP y).1 hy
      simp only [Frames.h]
      constructor
      · intro h
        refine (hmemA y).2 ⟨hyg, (hΛ.2 _).1 fun z hz => ?_⟩
        rw [← hH' _ (hA1 y) (hA2 y) z, hH _ (hA1 z) (hA2 z)]
        exact h _ (hprojA z hz)
      · intro hyA x hxA
        have hx := (hmemA x).1 hxA
        rw [← hH2 x y hx.1 hyg, ← hH _ (hA1 x) (hA2 x)]
        exact hint _ hx.2 _ ((hmemA y).1 hyA).2
    · refine ⟨L.cj c • g (Fin.last r), (innerOf S g gs Λ).smul_mem ⟨L.cj c, cj_int L hc⟩ hlast, ?_⟩
      simp only [Frames.h]
      rw [hf_smul_right, L.cj_cj, hcz]
  refine ⟨hIs, ?_⟩
  unfold Frames.stdLat
  refine le_antisymm ?_ ?_
  · intro z hz
    rw [hB z]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_inf.2
        ⟨hprojA z hz, (Submodule.restrictScalars_mem _ _ _).2 ((hperpS _).2 (hA2 z))⟩))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ (⟨_, hint _ hz _ (hsΛ j)⟩ : L.O) (Submodule.subset_span ⟨j, rfl⟩)))
    · exact Submodule.mem_sup_right (Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ (⟨_, hint _ hz _ (hgΛ _)⟩ : L.O) (Submodule.subset_span ⟨j, rfl⟩))
  · refine sup_le (sup_le ?_ ?_) ?_
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hgΛ _
    · intro x hx
      rw [Submodule.mem_inf, Submodule.restrictScalars_mem] at hx
      have h1 := (hmemA x).1 hx.1
      rw [← hD x h1.1 ((hperpS x).1 hx.2)]
      exact h1.2
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hsΛ j

theorem isTermW_of_isSD (Λ : Submodule L.O S.V) (hΛ : IsSD L S.Hm Λ)
    (hf1 : ∀ a, S.f a ∈ Λ) (hf2 : ∀ a, S.f' a ∈ Λ) (hs1 : ∀ j, S.es j ∈ Λ) (hs2 : ∀ j, S.es' j ∈ Λ)
    (hT : ((S.T⁻¹ : Fˣ) : F) ∈ 𝒪[F]) (hT' : ((S.T'⁻¹ : Fˣ) : F) ∈ 𝒪[F])
    (hth : ∀ b, S.InTh Λ (S.f' b - S.f b)) :
    S.IsTermW (innerOf S S.f S.es Λ, innerOf S S.f' S.es' Λ, S.graphOf Λ) Λ 1 1 := by
  have hne : ∀ j : Fin r, (j.castSucc : Fin (r + 1)) ≠ Fin.last r := fun j => (Fin.castSucc_lt_last j).ne
  obtain ⟨h1, h1'⟩ := inner_spec S S.f S.es Λ
    (fun a j => by rw [S.gram, if_neg (fun h => hne j h.2)]) S.dual S.iso hΛ hf1 hs1
    (-algebraMap F E ((S.T⁻¹ : Fˣ) : F)) (neg_mem ((algebraMap_mem_iff L _).2 hT))
    (by rw [S.gram, if_pos ⟨rfl, rfl⟩, neg_mul_neg, ← map_mul, Units.inv_mul, map_one])
  obtain ⟨h2, h2'⟩ := inner_spec S S.f' S.es' Λ
    (fun a j => by rw [S.gram', if_neg (fun h => hne j h.2)]) S.dual' S.iso' hΛ hf2 hs2
    (-algebraMap F E ((S.T'⁻¹ : Fˣ) : F)) (neg_mem ((algebraMap_mem_iff L _).2 hT'))
    (by rw [S.gram', if_pos ⟨rfl, rfl⟩, neg_mul_neg, ← map_mul, Units.inv_mul, map_one])
  refine ⟨h1, h2, S.N.one_mem, S.N'.one_mem, ?_, ?_, fun b => hth b, rfl⟩
  · rw [one_smul]
    exact h1'
  · rw [one_smul]
    exact h2'

end General

theorem mem_stdLat (L : LocE F E) {n : ℕ} (x : Fin n → E) : x ∈ stdLat L n ↔ ∀ i, x i ∈ L.O := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      intro i
      show (Pi.single j 1 : Fin n → E) i ∈ L.O
      rw [Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    | zero => intro i; exact zero_mem _
    | add u v _ _ hu hv => intro i; exact add_mem (hu i) (hv i)
    | smul c u _ hu =>
      intro i
      rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
      exact mul_mem c.2 (hu i)
  · intro hx
    have hsum : x = ∑ i, (⟨x i, hx i⟩ : L.O) • (Pi.single i 1 : Fin n → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Subring.smul_def]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem isSD_stdLat (L : LocE F E) {n : ℕ} (H K : Matrix (Fin n) (Fin n) E) (hH : IsIntM L H)
    (hK : IsIntM L K) (hKH : K * H = 1) : IsSD L H (stdLat L n) := by
  refine ⟨⟨Submodule.fg_span (Set.finite_range _), ?_⟩, ?_⟩
  · rw [eq_top_iff]
    intro v _
    have hsum : v = ∑ i, v i • (Pi.single i 1 : Fin n → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span ⟨i, rfl⟩))
  · intro y
    rw [mem_stdLat]
    constructor
    · intro h j
      have hrow : ∀ i, (Matrix.mulVec H fun k => L.cj (y k)) i ∈ L.O := by
        intro i
        have hs : (Pi.single i 1 : Fin n → E) ∈ stdLat L n := (mem_stdLat L _).2 fun k => by
          rw [Pi.single_apply]
          split_ifs
          · exact one_mem _
          · exact zero_mem _
        have := h _ hs
        simpa [hf, Pi.single_apply, Matrix.mulVec, dotProduct] using this
      have hcK : (fun k => L.cj (y k)) = Matrix.mulVec K (Matrix.mulVec H fun k => L.cj (y k)) := by
        rw [Matrix.mulVec_mulVec, hKH, Matrix.one_mulVec]
      have hcj : (Matrix.mulVec K (Matrix.mulVec H fun k => L.cj (y k))) j ∈ L.O := by
        simp only [Matrix.mulVec, dotProduct]
        exact Subring.sum_mem _ fun i _ => mul_mem (hK j i) (hrow i)
      rw [← hcK] at hcj
      have := cj_int L hcj
      simpa [L.cj_cj] using this
    · intro h x hx
      rw [mem_stdLat] at hx
      exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ =>
        mul_mem (mul_mem (hx i) (hH i j)) (cj_int L (h j))

section Blocks
variable {s m N : ℕ} (e : Fin s ⊕ Fin m ≃ Fin N)

def extZ (x : Fin s → E) : Fin N → E := Sum.elim x 0 ∘ e.symm

def big (H : Matrix (Fin s) (Fin s) E) : Matrix (Fin N) (Fin N) E :=
  Matrix.reindex e e (Matrix.fromBlocks H 0 0 (1 : Matrix (Fin m) (Fin m) E))

theorem hf_extZ (L : LocE F E) (H : Matrix (Fin s) (Fin s) E) (x y : Fin s → E) :
    hf L (big e H) (extZ e x) (extZ e y) = hf L H x y := by
  have key : ∀ f : Fin N → E, ∑ i, f i = ∑ p, f (e p) := fun f => (e.sum_comp f).symm
  simp only [hf, key, Fintype.sum_sum_type, extZ, big, Matrix.reindex_apply, Matrix.submatrix_apply,
    Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
    Matrix.fromBlocks_apply₁₁, zero_mul, map_zero, mul_zero, Finset.sum_const_zero, add_zero]

theorem big_mul (H K : Matrix (Fin s) (Fin s) E) (h : K * H = 1) : big e K * big e H = 1 := by
  simp [big, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, h,
    Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem big_herm (L : LocE F E) (H K : Matrix (Fin s) (Fin s) E) (hH : ∀ a b, L.cj (H b a) = H a b)
    (h : K * H = 1) : IsHermND L (big e H) := by
  refine ⟨?_, Matrix.isUnit_det_of_left_inverse (big_mul e H K h)⟩
  unfold IsHerm
  ext a b
  obtain ⟨p, rfl⟩ := e.surjective a
  obtain ⟨q, rfl⟩ := e.surjective b
  simp only [cT, big, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases p with p | p <;> rcases q with q | q
  · simpa using hH p q
  · simp
  · simp
  · by_cases hpq : p = q
    · subst hpq
      simp
    · simp [Matrix.one_apply_ne hpq, Matrix.one_apply_ne (Ne.symm hpq)]

theorem big_int (L : LocE F E) (H : Matrix (Fin s) (Fin s) E) (hH : IsIntM L H) : IsIntM L (big e H) := by
  intro a b
  obtain ⟨p, rfl⟩ := e.surjective a
  obtain ⟨q, rfl⟩ := e.surjective b
  simp only [big, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases p with p | p <;> rcases q with q | q
  · simpa using hH p q
  · simp
  · simp
  · rw [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem extZ_mem (L : LocE F E) (x : Fin s → E) (hx : ∀ i, x i ∈ L.O) : extZ e x ∈ stdLat L N := by
  rw [mem_stdLat]
  intro i
  simp only [extZ, Function.comp_apply]
  rcases e.symm i with a | a
  · exact hx a
  · exact zero_mem _

theorem extZ_sub_eq (x y z : Fin s → E) (c : E) (h : x - y = c • z) :
    extZ e x - extZ e y = c • extZ e z := by
  funext i
  simp only [extZ, Pi.sub_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
  rcases e.symm i with a | a
  · simpa using congrFun h a
  · simp

end Blocks

def e4 (m : ℕ) : Fin 4 ⊕ Fin m ≃ Fin (m + 1 + 2 * 1 + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

def H4 : Matrix (Fin 4) (Fin 4) E := !![0,0,0,1; 0,-1,-1,0; 0,-1,0,0; 1,0,0,-1]

def K4 : Matrix (Fin 4) (Fin 4) E := !![1,0,0,1; 0,0,-1,0; 0,-1,1,0; 1,0,0,0]

theorem hermitian_four_inverse_mul : (K4 : Matrix (Fin 4) (Fin 4) E) * H4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [K4, H4, Matrix.mul_apply, Fin.sum_univ_succ]

def toyExample (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : ℕ) : Frames L 1 (m + 1) where
  ϖ := ϖ
  ϖ_irr := hϖ
  Hm := big (e4 m) H4
  herm := big_herm _ L _ K4 (by intro a b; fin_cases a <;> fin_cases b <;> simp [H4]) hermitian_four_inverse_mul
  T := 1
  T' := 1
  f := ![extZ (e4 m) ![1,0,0,0], extZ (e4 m) ![0,1,0,0]]
  f' := ![extZ (e4 m) ![0,0,1,0], extZ (e4 m) ![0,0,0,1]]
  es := ![extZ (e4 m) ![0,1,-1,1]]
  es' := ![extZ (e4 m) ![1,-1,0,1]]
  gram := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hf_extZ] <;> simp [H4, hf, Fin.sum_univ_succ, Fin.last]
  gram' := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hf_extZ] <;> simp [H4, hf, Fin.sum_univ_succ, Fin.last]
  dual := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hf_extZ] <;> simp [H4, hf, Fin.sum_univ_succ]
  dual' := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hf_extZ] <;> simp [H4, hf, Fin.sum_univ_succ]
  iso := by
    intro a b; fin_cases a; fin_cases b; simp [hf_extZ]; simp [H4, hf, Fin.sum_univ_succ]
  iso' := by
    intro a b; fin_cases a; fin_cases b; simp [hf_extZ]; simp [H4, hf, Fin.sum_univ_succ]
  w := ⟨[(1, 2)], rfl⟩
  relevant := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [hf_extZ] <;> simp [H4, hf, Fin.sum_univ_succ, Pt.mat, ptEntryL]
  G_ne := by
    haveI := nontrivial L
    simp [lead, Matrix.det_succ_row_zero, hf_extZ, Fin.sum_univ_succ, Fin.last, Fin.castLE, Fin.succAbove]
    simp [H4, hf, Fin.sum_univ_succ]
  gg := false
  gg_ok := by simp

theorem exampleFrame_G (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : ℕ) : (toyExample L ϖ hϖ m).G = 1 := by
  have hZ : (toyExample L ϖ hϖ m).Zh = !![0, 1; -1, 0] := by
    ext a b
    rw [Frames.Zh, Matrix.of_apply, Frames.h, (toyExample L ϖ hϖ m).relevant]
    fin_cases a <;> fin_cases b <;> simp [toyExample, Pt.mat, ptEntryL]
  simp only [Frames.G, Frames.D, hZ, lead_last]
  rw [show ((Fin.last 1).castSucc : Fin (1 + 1 + 1)) = ⟨1, by omega⟩ from rfl, lead_one]
  simp [toyExample, Matrix.det_fin_two_of]

theorem exampleFrame_a (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : ℕ) : (toyExample L ϖ hϖ m).a = 0 := by
  have h := vE_pow L ϖ hϖ 1 0
  simp only [zpow_zero, Units.val_one, OneMemClass.coe_one, mul_one, map_one] at h
  have hϖ' : (toyExample L ϖ hϖ m).ϖ = ϖ := rfl
  have hgg : (toyExample L ϖ hϖ m).gg = false := rfl
  simp only [Frames.a, exampleFrame_G, Frames.vth, hϖ', h, hgg]
  norm_num

private theorem isIntM_H4 (L : LocE F E) : IsIntM L (H4 : Matrix (Fin 4) (Fin 4) E) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [H4]

private theorem isIntM_K4 (L : LocE F E) : IsIntM L (K4 : Matrix (Fin 4) (Fin 4) E) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [K4]

theorem exampleFrame_isSelfDual (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : ℕ) :
    IsSD L (toyExample L ϖ hϖ m).Hm (stdLat L _) := by
  exact isSD_stdLat L (big (e4 m) H4) (big (e4 m) K4) (big_int _ L _ (isIntM_H4 L))
    (big_int _ L _ (isIntM_K4 L)) (big_mul _ _ _ hermitian_four_inverse_mul)

theorem exampleFrame_exists_isTerm (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : ℕ) :
    ∃ d, (toyExample L ϖ hϖ m).IsTerm d (stdLat L _) := by
  have hF : ∀ a, (toyExample L ϖ hϖ m).f a ∈ stdLat L _ := by
    intro a
    fin_cases a <;> exact extZ_mem _ L _ (by intro i; fin_cases i <;> simp)
  have hF' : ∀ a, (toyExample L ϖ hϖ m).f' a ∈ stdLat L _ := by
    intro a
    fin_cases a <;> exact extZ_mem _ L _ (by intro i; fin_cases i <;> simp)
  have hS : ∀ j, (toyExample L ϖ hϖ m).es j ∈ stdLat L _ := by
    intro j
    fin_cases j
    exact extZ_mem _ L _ (by intro i; fin_cases i <;> simp)
  have hS' : ∀ j, (toyExample L ϖ hϖ m).es' j ∈ stdLat L _ := by
    intro j
    fin_cases j
    exact extZ_mem _ L _ (by intro i; fin_cases i <;> simp)
  have hth : ∀ b, (toyExample L ϖ hϖ m).InTh (stdLat L _) ((toyExample L ϖ hϖ m).f' b - (toyExample L ϖ hϖ m).f b) := by
    intro b
    refine ⟨_, Submodule.sub_mem _ (hF' b) (hF b), ?_⟩
    simp [Frames.th, toyExample]
  exact ⟨_, (1, 1), isTermW_of_isSD _ _ (exampleFrame_isSelfDual L ϖ hϖ m) hF hF' hS hS' (by simp [toyExample])
    (by simp [toyExample]) hth⟩

def e6 (m : ℕ) : Fin 6 ⊕ Fin m ≃ Fin (m + 3 + 2 * 1 + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

def H6 : Matrix (Fin 6) (Fin 6) E :=
  !![0,1,0,0,0,0; 1,0,0,0,0,0; 0,0,0,1,0,0; 0,0,1,0,0,0; 0,0,0,0,-1,0; 0,0,0,0,0,1]

theorem hermitian_six_mul_self : (H6 : Matrix (Fin 6) (Fin 6) E) * H6 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H6, Matrix.mul_apply, Fin.sum_univ_succ]

theorem hermitian_form_six_apply (L : LocE F E) (x y : Fin 6 → E) : hf L H6 x y =
    x 0 * L.cj (y 1) + x 1 * L.cj (y 0) + x 2 * L.cj (y 3) + x 3 * L.cj (y 2) - x 4 * L.cj (y 4) +
      x 5 * L.cj (y 5) := by
  simp [hf, Fin.sum_univ_succ, H6]
  ring

theorem isUnit_one_sub_sq (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) : IsUnit (1 - ϖ ^ 2) := by
  have hv := Valuation.integer.integers (valuation F)
  have h1 : valuation F (ϖ : F) < 1 := by
    have hne : valuation F (algebraMap 𝒪[F] F ϖ) ≠ 1 := fun h =>
      hϖ.not_isUnit (hv.isUnit_iff_valuation_eq_one.2 h)
    exact lt_of_le_of_ne ((Valuation.mem_integer_iff _ _).1 ϖ.2) hne
  rw [hv.isUnit_iff_valuation_eq_one]
  have h2 : valuation F ((ϖ : F) ^ 2) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le h1 (by norm_num)
  have h3 : algebraMap 𝒪[F] F (1 - ϖ ^ 2) = 1 - (ϖ : F) ^ 2 := by
    rw [map_sub, map_one, map_pow]
    rfl
  rw [h3]
  exact Valuation.map_one_sub_of_lt _ h2

theorem coe_ne_zero (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) : (ϖ : F) ≠ 0 := by
  intro h
  exact hϖ.ne_zero (Subtype.ext h)

def toyG (L : LocE F E) (hE : ¬ IsField E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : ℕ) :
    Frames L 1 (m + 3) where
  ϖ := ϖ
  ϖ_irr := hϖ
  Hm := big (e6 m) H6
  herm := big_herm _ L _ H6 (by intro a b; fin_cases a <;> fin_cases b <;> simp [H6]) hermitian_six_mul_self
  T := 1
  T' := Units.map (𝒪[F]).subtype.toMonoidHom (isUnit_one_sub_sq ϖ hϖ).unit
  f := ![extZ (e6 m) ![1,0,0,0,0,0], extZ (e6 m) ![0,0,0,0,1,0]]
  f' := ![extZ (e6 m) ![1, -(algebraMap F E ϖ) ^ 2, algebraMap F E ϖ, algebraMap F E ϖ, 0, 0],
    extZ (e6 m) ![0,0,0,0,1,algebraMap F E ϖ]]
  es := ![extZ (e6 m) ![0,1,0,0,0,0]]
  es' := ![extZ (e6 m) ![0,1,0,0,0,0]]
  gram := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hf_extZ, hermitian_form_six_apply, Fin.last]
  gram' := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hf_extZ, hermitian_form_six_apply, Fin.last] <;> ring
  dual := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hf_extZ, hermitian_form_six_apply]
  dual' := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hf_extZ, hermitian_form_six_apply]
  iso := by
    intro a b; fin_cases a; fin_cases b; simp [hf_extZ, hermitian_form_six_apply]
  iso' := by
    intro a b; fin_cases a; fin_cases b; simp [hf_extZ, hermitian_form_six_apply]
  w := ⟨[(Units.map (algebraMap F E).toMonoidHom (Units.mk0 (ϖ : F) (coe_ne_zero ϖ hϖ)) ^ 2, 1), (-1, 1)], rfl⟩
  relevant := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [hf_extZ, hermitian_form_six_apply, Pt.mat, ptEntryL]
  G_ne := by
    haveI := nontrivial L
    have h6 : (algebraMap F E ϖ) ^ 6 ≠ 0 := by
      rw [← map_pow]
      exact (map_ne_zero _).2 (pow_ne_zero _ (coe_ne_zero ϖ hϖ))
    convert h6 using 1
    simp [lead, Matrix.det_succ_row_zero, hf_extZ, hermitian_form_six_apply, Fin.sum_univ_succ, Fin.last, Fin.castLE,
      Fin.succAbove]
    ring
  gg := true
  gg_ok := fun _ => ⟨hE, ⟨1, rfl⟩, ⟨(isUnit_one_sub_sq ϖ hϖ).unit, rfl⟩⟩

theorem splitExampleFrame_G (L : LocE F E) (hE : ¬ IsField E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : ℕ) :
    (toyG L hE ϖ hϖ m).G = algebraMap F E ((ϖ : F) ^ 6) := by
  have hcj : ∀ a : F, L.cj (algebraMap F E a) = algebraMap F E a := fun a => L.cj.commutes a
  have hZ : (toyG L hE ϖ hϖ m).Zh = !![-(algebraMap F E ϖ) ^ 2, 0; 0, -1] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Frames.Zh, Frames.h, toyG, hf_extZ, hermitian_form_six_apply]
  simp only [Frames.G, Frames.D, hZ, lead_last]
  rw [show ((Fin.last 1).castSucc : Fin (1 + 1 + 1)) = ⟨1, by omega⟩ from rfl, lead_one]
  simp [toyG, Matrix.det_fin_two_of, hcj]
  ring

theorem splitExampleFrame_a (L : LocE F E) (hE : ¬ IsField E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : ℕ) :
    (toyG L hE ϖ hϖ m).a = 2 := by
  have h := vE_pow L ϖ hϖ 1 6
  simp only [zpow_ofNat, Units.val_one, OneMemClass.coe_one, mul_one] at h
  have hϖ' : (toyG L hE ϖ hϖ m).ϖ = ϖ := rfl
  have hgg : (toyG L hE ϖ hϖ m).gg = true := rfl
  simp only [Frames.a, splitExampleFrame_G, Frames.vth, hϖ', h, hgg]
  norm_num

private theorem isIntM_H6 (L : LocE F E) : IsIntM L (H6 : Matrix (Fin 6) (Fin 6) E) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [H6]

theorem splitExampleFrame_isSelfDual (L : LocE F E) (hE : ¬ IsField E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : ℕ) :
    IsSD L (toyG L hE ϖ hϖ m).Hm (stdLat L _) := by
  exact isSD_stdLat L (big (e6 m) H6) (big (e6 m) H6) (big_int _ L _ (isIntM_H6 L))
    (big_int _ L _ (isIntM_H6 L)) (big_mul _ _ _ hermitian_six_mul_self)

theorem splitExampleFrame_exists_isTerm (L : LocE F E) (hE : ¬ IsField E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : ℕ) :
    ∃ d, (toyG L hE ϖ hϖ m).IsTerm d (stdLat L _) := by
  have ha : algebraMap F E (ϖ : F) ∈ L.O := (algebraMap_mem_iff L _).2 ϖ.2
  have hF : ∀ a, (toyG L hE ϖ hϖ m).f a ∈ stdLat L _ := by
    intro a
    fin_cases a <;> exact extZ_mem _ L _ (by intro i; fin_cases i <;> simp)
  have hF' : ∀ a, (toyG L hE ϖ hϖ m).f' a ∈ stdLat L _ := by
    intro a
    fin_cases a <;> exact extZ_mem _ L _ (by intro i; fin_cases i <;> simp [ha, pow_mem])
  have hS : ∀ j, (toyG L hE ϖ hϖ m).es j ∈ stdLat L _ := by
    intro j
    fin_cases j
    exact extZ_mem _ L _ (by intro i; fin_cases i <;> simp)
  have hS' : ∀ j, (toyG L hE ϖ hϖ m).es' j ∈ stdLat L _ := by
    intro j
    fin_cases j
    exact extZ_mem _ L _ (by intro i; fin_cases i <;> simp)
  have hth' : (toyG L hE ϖ hϖ m).th = (ϖ : F) := by simp [Frames.th, toyG]
  have hth : ∀ b, (toyG L hE ϖ hϖ m).InTh (stdLat L _)
      ((toyG L hE ϖ hϖ m).f' b - (toyG L hE ϖ hϖ m).f b) := by
    intro b
    unfold Frames.InTh
    rw [hth']
    fin_cases b
    · refine ⟨extZ (e6 m) ![0, -algebraMap F E ϖ, 1, 1, 0, 0], extZ_mem _ L _ ?_,
        extZ_sub_eq _ _ _ _ _ ?_⟩
      · intro i
        fin_cases i <;> simp [ha]
      · funext i
        fin_cases i <;> simp <;> ring
    · refine ⟨extZ (e6 m) ![0, 0, 0, 0, 0, 1], extZ_mem _ L _ ?_, extZ_sub_eq _ _ _ _ _ ?_⟩
      · intro i
        fin_cases i <;> simp
      · funext i
        fin_cases i <;> simp
  have hT' : (((toyG L hE ϖ hϖ m).T'⁻¹ : Fˣ) : F) ∈ 𝒪[F] := by
    show (((Units.map (𝒪[F]).subtype.toMonoidHom (isUnit_one_sub_sq ϖ hϖ).unit)⁻¹ : Fˣ) : F) ∈ 𝒪[F]
    rw [← map_inv]
    exact (((isUnit_one_sub_sq ϖ hϖ).unit⁻¹ : 𝒪[F]ˣ) : 𝒪[F]).2
  exact ⟨_, (1, 1), isTermW_of_isSD _ _ (splitExampleFrame_isSelfDual L hE ϖ hϖ m) hF hF' hS hS' (by simp [toyG]) hT' hth⟩

theorem exists_frames_term (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : ℕ) :
    (∃ S : Frames L 1 (m + 1), S.ϖ = ϖ ∧ S.w.blocks = [(1, 2)] ∧ S.T = 1 ∧ S.T' = 1 ∧ S.gg = false ∧
      S.G = 1 ∧ S.a = 0 ∧ ∃ d Λ, S.IsTerm d Λ ∧ IsSD L S.Hm Λ) ∧
    (¬ IsField E → ∃ S : Frames L 1 (m + 3), S.ϖ = ϖ ∧ S.gg = true ∧
      S.G = algebraMap F E ((ϖ : F) ^ 6) ∧ S.a = 2 ∧ ∃ d Λ, S.IsTerm d Λ ∧ IsSD L S.Hm Λ) := by
  refine ⟨⟨toyExample L ϖ hϖ m, rfl, rfl, rfl, rfl, rfl, exampleFrame_G L ϖ hϖ m, exampleFrame_a L ϖ hϖ m, ?_⟩, fun hE =>
    ⟨toyG L hE ϖ hϖ m, rfl, rfl, splitExampleFrame_G L hE ϖ hϖ m, splitExampleFrame_a L hE ϖ hϖ m, ?_⟩⟩
  · obtain ⟨d, hd⟩ := exampleFrame_exists_isTerm L ϖ hϖ m
    exact ⟨d, _, hd, exampleFrame_isSelfDual L ϖ hϖ m⟩
  · obtain ⟨d, hd⟩ := splitExampleFrame_exists_isTerm L hE ϖ hϖ m
    exact ⟨d, _, hd, splitExampleFrame_isSelfDual L hE ϖ hϖ m⟩

theorem exists_frames_term_split [IsNonarchimedeanLocalField F] (m : ℕ) :
    ∃ L : LocE F (F × F),
      (∃ S : Frames L 1 (m + 1), S.gg = false ∧ ∃ d Λ, S.IsTerm d Λ) ∧
      ∃ S : Frames L 1 (m + 3), S.gg = true ∧ ∃ d Λ, S.IsTerm d Λ := by
  obtain ⟨L, -, -⟩ := nonempty_split (F := F)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hE : ¬ IsField (F × F) := by
    intro h
    obtain ⟨b, hb⟩ := h.mul_inv_cancel (a := ((0 : F), (1 : F))) (by simp)
    have h0 := congrArg Prod.fst hb
    simp at h0
  obtain ⟨⟨S, -, -, -, -, hg, -, -, d, Λ, hd, -⟩, h2⟩ := exists_frames_term L ϖ hϖ m
  obtain ⟨S', -, hg', -, -, d', Λ', hd', -⟩ := h2 hE
  exact ⟨L, ⟨S, hg, d, Λ, hd⟩, S', hg', d', Λ', hd'⟩

end GlobalTheory.HL.Inhab
