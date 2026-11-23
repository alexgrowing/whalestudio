import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualUnipotentGroupActsUnitriangularOnto
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardLatticeDualVectorsChangeUnipotentStatement

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ToC

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
  {H : HermSp M V} {r k : ℕ}

def swapEs (Fr : LocNG.FrameD H r) (es₂ : Fin r → V) (h1 : ∀ i j, H.h (es₂ i) (es₂ j) = 0)
    (h2 : ∀ i j : Fin r, H.h (Fr.f i.castSucc) (es₂ j) = if i = j then 1 else 0)
    (h3 : ∀ i, H.h (es₂ i) (Fr.f (Fin.last r)) = 0) : LocNG.FrameD H r :=
  ⟨Fr.f, es₂, Fr.T, Fr.h_iso, Fr.h_zz, h1, h2, h3⟩

lemma mem_img (g : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) (x : V) :
    x ∈ LocNG.img g Λ ↔ ∃ y ∈ Λ, g y = x := by
  simp [LocNG.img, Submodule.mem_map]

lemma img_mul (g k : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) :
    LocNG.img (g * k) Λ = LocNG.img g (LocNG.img k Λ) := by
  ext x
  simp only [mem_img]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨k y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

lemma h_sum_left (H : HermSp M V) {ι : Type} (s : Finset ι) (c : ι → E) (v : ι → V) (y : V) :
    H.h (∑ i ∈ s, c i • v i) y = ∑ i ∈ s, c i * H.h (v i) y := by
  induction s using Finset.induction_on with
  | empty => simp [H.h_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]

lemma pair_eq (hM : M.OK) (Fr : LocNG.FrameD H r) (es₂ : Fin r → V) (h1 : ∀ i j, H.h (es₂ i) (es₂ j) = 0)
    (h2 : ∀ i j : Fin r, H.h (Fr.f i.castSucc) (es₂ j) = if i = j then 1 else 0)
    (h3 : ∀ i, H.h (es₂ i) (Fr.f (Fin.last r)) = 0) (hT : Fr.T ≠ 0) {n : V ≃ₗ[E] V} (hn : n ∈ Fr.N)
    (b : Fin (r + 1)) (a : Fin r) : H.h (n (Fr.f b)) (es₂ a) = H.h (n (Fr.f b)) (Fr.es a) := by
  obtain ⟨A, -, hA⟩ := (GlobalTheory.LocOver.UnipOnto.unipotent_onto M hM H r Fr hT).2.1 n hn
  have hb : ∀ c, H.h (Fr.f c) (es₂ a) = H.h (Fr.f c) (Fr.es a) := by
    intro c
    induction c using Fin.lastCases with
    | last =>
      have e1 : H.h (Fr.f (Fin.last r)) (es₂ a) = M.L.cj (H.h (es₂ a) (Fr.f (Fin.last r))) := H.h_herm _ _
      have e2 : H.h (Fr.f (Fin.last r)) (Fr.es a) = M.L.cj (H.h (Fr.es a) (Fr.f (Fin.last r))) := H.h_herm _ _
      rw [e1, e2, h3, Fr.h_sz]
    | cast i => rw [h2, Fr.h_es]
  rw [show n (Fr.f b) = _ from hA b, h_sum_left, h_sum_left]
  exact Finset.sum_congr rfl fun c _ => by rw [hb c]

lemma pulled (S : Frames M.L r k) (e : V ≃ₗ[E] S.V) (he : ∀ x y, S.h (e x) (e y) = H.h x y)
    (f : Fin (r + 1) → V) (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (hg : ∀ a, g a = e (f a))
    (hdual : ∀ a j, hf M.L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (hiso : ∀ i j, hf M.L S.Hm (gs i) (gs j) = 0) :
    (∀ i j, H.h (e.symm (gs i)) (e.symm (gs j)) = 0) ∧
    (∀ i j : Fin r, H.h (f i.castSucc) (e.symm (gs j)) = if i = j then 1 else 0) ∧
    (∀ i, H.h (e.symm (gs i)) (f (Fin.last r)) = 0) := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i => ?_⟩
  · rw [← he, e.apply_symm_apply, e.apply_symm_apply]; exact hiso i j
  · rw [← he, e.apply_symm_apply, ← hg]
    change hf M.L S.Hm _ _ = _
    rw [hdual]; simp [Fin.castSucc_inj]
  · rw [H.h_herm, ← he, e.apply_symm_apply, ← hg]
    change M.L.cj (hf M.L S.Hm _ _) = _
    rw [hdual]
    have : Fin.last r ≠ i.castSucc := (Fin.castSucc_lt_last i).ne'
    simp [this]

variable {P : LocNG.FPair H r} {S : Frames M.L r k}

def pair₂ (c : WCoord P S) : LocNG.FPair H r :=
  ⟨swapEs P.A (fun a => c.e.symm (S.es a))
      (pulled S c.e c.h_eq P.A.f S.f S.es c.f_eq S.dual S.iso).1
      (pulled S c.e c.h_eq P.A.f S.f S.es c.f_eq S.dual S.iso).2.1
      (pulled S c.e c.h_eq P.A.f S.f S.es c.f_eq S.dual S.iso).2.2,
    swapEs P.B (fun a => c.e.symm (S.es' a))
      (pulled S c.e c.h_eq P.B.f S.f' S.es' c.f'_eq S.dual' S.iso').1
      (pulled S c.e c.h_eq P.B.f S.f' S.es' c.f'_eq S.dual' S.iso').2.1
      (pulled S c.e c.h_eq P.B.f S.f' S.es' c.f'_eq S.dual' S.iso').2.2⟩

def coord₂ (c : WCoord P S) : Coord (pair₂ c) S :=
  ⟨c.e, c.h_eq, c.f_eq, c.f'_eq, fun a => (c.e.apply_symm_apply _).symm,
    fun a => (c.e.apply_symm_apply _).symm, c.T_eq, c.T'_eq, c.gg_none, c.gg_some⟩

def datEq (c : WCoord P S) : LocNG.Datum P ≃ LocNG.Datum (pair₂ c) where
  toFun d := ⟨d.L, d.L', d.hL, d.hL', d.io, d.io_L⟩
  invFun d := ⟨d.L, d.L', d.hL, d.hL', d.io, d.io_L⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem std_swap : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : LocNG.FrameD H r) (es₂ : Fin r → V) (h1 : ∀ i j, H.h (es₂ i) (es₂ j) = 0) (h2 : ∀ i j : Fin r, H.h (Fr.f i.castSucc) (es₂ j) = if i = j then 1 else 0) (h3 : ∀ i, H.h (es₂ i) (Fr.f (Fin.last r)) = 0), Fr.T ≠ 0 → ∀ L : Submodule M.L.O (H.Wb Fr.f), Fr.IsInner L → ∃ m ∈ Fr.N, (∀ b, m (Fr.f b) = Fr.f b) ∧ (⟨Fr.f, es₂, Fr.T, Fr.h_iso, Fr.h_zz, h1, h2, h3⟩ : LocNG.FrameD H r).LamStd L = LocNG.img m (Fr.LamStd L) :=
  GlobalTheory.T.standardLattice_dualVectors_change_unipotent

lemma inv_fix {m : V ≃ₗ[E] V} {x : V} (hx : m x = x) : m⁻¹ x = x := by
  conv_lhs => rw [← hx]
  show (m⁻¹ * m) x = x
  rw [inv_mul_cancel]; rfl

lemma side_iff (hM : M.OK) (Fr : LocNG.FrameD H r) (es₂ : Fin r → V) (h1 : ∀ i j, H.h (es₂ i) (es₂ j) = 0)
    (h2 : ∀ i j : Fin r, H.h (Fr.f i.castSucc) (es₂ j) = if i = j then 1 else 0)
    (h3 : ∀ i, H.h (es₂ i) (Fr.f (Fin.last r)) = 0) (hT : Fr.T ≠ 0)
    (L : Submodule M.L.O (H.Wb Fr.f)) (hL : Fr.IsInner L) (f : Fin (r + 1) → V) (Λ : Submodule M.L.O V) :
    (∃ n ∈ Fr.N, f = (fun b => n (Fr.f b)) ∧ Λ = LocNG.img n (Fr.LamStd L)) ↔
      ∃ n ∈ (swapEs Fr es₂ h1 h2 h3).N, f = (fun b => n ((swapEs Fr es₂ h1 h2 h3).f b)) ∧
        Λ = LocNG.img n ((swapEs Fr es₂ h1 h2 h3).LamStd L) := by
  obtain ⟨m, hm, hmf, hmΛ⟩ := std_swap M hM H r Fr es₂ h1 h2 h3 hT L hL
  have e : (swapEs Fr es₂ h1 h2 h3).LamStd L = LocNG.img m (Fr.LamStd L) := hmΛ
  rw [e]
  constructor
  · rintro ⟨n, hn, hf, hΛ⟩
    refine ⟨n * m⁻¹, Fr.N.mul_mem hn (Fr.N.inv_mem hm), ?_, ?_⟩
    · rw [hf]; funext b; show n (Fr.f b) = n (m⁻¹ (Fr.f b)); rw [inv_fix (hmf b)]
    · rw [← img_mul, mul_assoc, inv_mul_cancel, mul_one]; exact hΛ
  · rintro ⟨n, hn, hf, hΛ⟩
    refine ⟨n * m, Fr.N.mul_mem hn hm, ?_, ?_⟩
    · rw [hf]; funext b; show n (Fr.f b) = n (m (Fr.f b)); rw [hmf b]
    · rw [img_mul]; exact hΛ

end

theorem changed_duals : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : WCoord P S), ∃ (P₂ : LocNG.FPair H r) (c₂ : Coord P₂ S) (φ : LocNG.Datum P ≃ LocNG.Datum P₂), c₂.e = c.e ∧ P₂.St = P.St ∧ P₂.K0 = P.K0 ∧ P₂.UW0 = P.UW0 ∧ P₂.Hp = P.Hp ∧ (P₂.PrimeTo ↔ P.PrimeTo) ∧ (∀ d, c₂.dat (φ d) = c.dat d) ∧ (∀ d t, LocNG.IsTermOver P d t ↔ LocNG.IsTermOver P₂ (φ d) t) ∧ (∀ d t, LocNG.IsTermOver P d t → LocNG.om P₂ t = LocNG.om P t) ∧ ∀ g d d', LocNG.Datum.Moves g d d' ↔ LocNG.Datum.Moves g (φ d) (φ d') := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c
  have hTA : P.A.T ≠ 0 := by rw [← c.T_eq]; exact S.T.ne_zero
  have hTB : P.B.T ≠ 0 := by rw [← c.T'_eq]; exact S.T'.ne_zero
  have pA := pulled S c.e c.h_eq P.A.f S.f S.es c.f_eq S.dual S.iso
  have pB := pulled S c.e c.h_eq P.B.f S.f' S.es' c.f'_eq S.dual' S.iso'
  have kA : ∀ n ∈ P.A.N, ∀ b a, H.h (n ((pair₂ c).A.f b)) ((pair₂ c).A.es a) = H.h (n (P.A.f b)) (P.A.es a) :=
    fun n hn b a => pair_eq hM P.A _ pA.1 pA.2.1 pA.2.2 hTA hn b a
  have kB : ∀ n ∈ P.B.N, ∀ b a, H.h (n ((pair₂ c).B.f b)) ((pair₂ c).B.es a) = H.h (n (P.B.f b)) (P.B.es a) :=
    fun n hn b a => pair_eq hM P.B _ pB.1 pB.2.1 pB.2.2 hTB hn b a
  refine ⟨pair₂ c, coord₂ c, datEq c, rfl, rfl, ?_, rfl, rfl, Iff.rfl, fun d => rfl, ?_, ?_, fun g d d' => Iff.rfl⟩
  · unfold LocNG.FPair.K0
    congr 1
    ext s
    constructor
    · rintro ⟨hs, h⟩
      have hs' := Subgroup.mem_inf.mp hs
      refine ⟨hs, fun a b => ?_⟩
      rw [← kA s hs'.1 b a, ← kB s hs'.2 b a]
      exact h a b
    · rintro ⟨hs, h⟩
      have hs' := Subgroup.mem_inf.mp hs
      refine ⟨hs, fun a b => ?_⟩
      rw [kA s hs'.1 b a, kB s hs'.2 b a]
      exact h a b
  · intro d t
    exact and_congr Iff.rfl (and_congr Iff.rfl
      (and_congr (side_iff hM P.A _ pA.1 pA.2.1 pA.2.2 hTA d.L d.hL t.f t.abelian₂)
        (and_congr (side_iff hM P.B _ pB.1 pB.2.1 pB.2.2 hTB d.L' d.hL' t.f' t.abelian₂) Iff.rfl)))
  · rintro d t ⟨-, -, ⟨n, hn, hf, -⟩, ⟨n', hn', hf', -⟩, -⟩
    have e1 : (pair₂ c).A.coefSum t.f = P.A.coefSum t.f := by
      unfold LocNG.FrameD.coefSum; rw [hf]
      exact Finset.sum_congr rfl fun a _ => kA n hn a.succ a
    have e2 : (pair₂ c).B.coefSum t.f' = P.B.coefSum t.f' := by
      unfold LocNG.FrameD.coefSum; rw [hf']
      exact Finset.sum_congr rfl fun a _ => kB n' hn' a.succ a
    unfold LocNG.om LocNG.FrameD.psiOf
    rw [e1, e2]

end GlobalTheory.HL.ToC
