import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

section Abs
variable {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E)

private theorem pyc_inSp_act {κ : Type} [Fintype κ] {R : Subalgebra ℂ S} {M : Submodule ℂ E} (hst : Stab act R M)
    {r : κ → S} {g : S} (hg : InSp R r g) {m : E} (hm : m ∈ M) : act g m ∈ sm act M (Set.range r) := by
  obtain ⟨a, ha, rfl⟩ := hg
  rw [map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l _ => ?_
  have e1 : act (a l * r l) m = act (r l) (act (a l) m) := by
    rw [mul_comm, map_mul, Module.End.mul_apply]
  rw [e1]
  exact Submodule.mem_iSup_of_mem (r l) (Submodule.mem_iSup_of_mem ⟨l, rfl⟩
    (Submodule.mem_map_of_mem (hst _ (ha l) _ hm)))

private theorem pyc_sm_le {κ : Type} [Fintype κ] {R : Subalgebra ℂ S} {M : Submodule ℂ E} (hst : Stab act R M)
    {T : Set S} {r : κ → S} (h : ∀ g ∈ T, InSp R r g) : sm act M T ≤ sm act M (Set.range r) := by
  refine iSup₂_le fun g hg => ?_
  rintro _ ⟨m, hm, rfl⟩
  exact pyc_inSp_act act hst (h g hg) hm

private theorem pyc_kosZ_mono {κ : Type} [LinearOrder κ] {M M' : Submodule ℂ E} (h : M ≤ M') (r : κ → S) (m : ℤ) :
    (kos act M r).Z m ≤ (kos act M' r).Z m := by
  intro c hc
  refine ⟨?_, hc.2⟩
  intro s _
  have h1 := hc.1 s (Set.mem_univ _)
  by_cases hs : (s.card : ℤ) = m
  · simp only [kos, acx, if_pos hs] at h1 ⊢
    exact h h1
  · simp only [kos, acx, if_neg hs] at h1 ⊢
    exact h1

private theorem pyc_kstep (k2 : KoszulBoundaryOfComponentMemIdeal) (k3 : K3) {κ0 : Type} [LinearOrder κ0] [Fintype κ0] (R : Subalgebra ℂ S)
    (M : Submodule ℂ E) {d : ℕ} (ρ : κ0 ⊕ₗ Fin d → S) (e : Fin d ↪o κ0) (N : Matrix (Fin d) (Fin d) S)
    (hst : Stab act R M) (hρ : ∀ l, ρ l ∈ R) (hN : ∀ a j, N a j ∈ R)
    (hrel : ∀ a, ρ (inlE (e a)) = ∑ j, N a j * ρ (inrE j))
    (hKt : KE (kos act M fun j => ρ (inrE j)) d) (hKr : KE (kos act M fun j => ρ (inlE (e j))) d)
    (hsm : sm act M (Set.range fun j => ρ (inrE j)) ≤ sm act M (Set.range fun j => ρ (inlE (e j))))
    {v : Finset (κ0 ⊕ₗ Fin d) → E} (hv : v ∈ (kos act M ρ).Z d) {w : Finset κ0 → E}
    (hw : w ∈ (kos act M fun l => ρ (inlE l)).Z d) {y : E}
    (hy : y - act N.det (v (img inrE)) ∈ sm act M (Set.range fun j => ρ (inrE j)))
    (hwy : w (img e) = y - v (img (e.trans inlE))) :
    w ∈ (kos act M fun l => ρ (inlE l)).B d := by
  have hne : ∀ a j, (e.trans inlE) a ≠ (inrE : Fin d ↪o κ0 ⊕ₗ Fin d) j := by
    intro a j h
    exact absurd h (by simp [inlE, inrE])
  have q := k3 S E act (κ0 ⊕ₗ Fin d) R M ρ d inrE (e.trans inlE) N hst hρ hN hrel hne hKt v hv
  refine k2 S E act κ0 R M (fun l => ρ (inlE l)) d e hst (fun l => hρ _) hKr w hw ?_
  rw [hwy]
  have e1 : y - v (img (e.trans inlE)) =
      (y - act N.det (v (img inrE))) - (v (img (e.trans inlE)) - act N.det (v (img inrE))) := by abel
  rw [e1]
  exact hsm (sub_mem hy q)

end Abs

private theorem pyc_val {L : Type} [Field L] [Algebra ℂ L] (hVB : ValBasic) (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ)
    {s a b : L} {cs ca cb : ℂ} (hs : Val B e s cs) (ha : Val B e a ca) (hb : Val B e b cb) (hc : cs = ca * cb) :
    Val B e (s - a * b) 0 := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hVB L B e
  obtain ⟨ms, rfl⟩ := (hev _ _).1 hs
  obtain ⟨ma, rfl⟩ := (hev _ _).1 ha
  obtain ⟨mb, rfl⟩ := (hev _ _).1 hb
  refine (hev _ _).2 ⟨sub_mem ms (mul_mem ma mb), ?_⟩
  have e1 : (⟨s - a * b, sub_mem ms (mul_mem ma mb)⟩ : loc B e) = ⟨s, ms⟩ - ⟨a, ma⟩ * ⟨b, mb⟩ := rfl
  rw [e1, map_sub, map_mul, hc, sub_self]

section Conc
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] {d : ℕ}
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')

private theorem pyc_tt {κ : Type} [LinearOrder κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K) (j : Fin d) :
    (sysY x j2 d).r (app (app n11 n) n10) (app (gG x j2 z) (gT x j2)) 0 0 (inrE j) = tt K' x j := by
  change ((sysY x j2 d).X j.succ : K') * (((sysY x j2 d).X 0 ^ 1 * (sysY x j2 d).Y 0 ^ 0)⁻¹ : K'ˣ) = _
  simp [tt, sysY, div_eq_mul_inv]

private theorem pyc_local (hYC : YCols) (hFL : FixLoc) (k1 : K1) (k2 : KoszulBoundaryOfComponentMemIdeal) (k3 : K3) (hLR : LocReg) (hLM : LocMax)
    (hLF : LocForms) (hVB : ValBasic) (hOm : OmLoc)
    {Fx : Finset (fib ℂ K' (xv x))} {A : fib ℂ K' (xv x) → Matrix (Fin d) (Fin d) ℂ} (hY : Y1 x j2 Fx A)
    {κ : Type} [LinearOrder κ] [Fintype κ] {n : κ → ℕ × ℕ} {z : κ → K ⊗[ℂ] K} (hZ : ZF K x n z)
    (h : rB ℂ K' (xv x) {0}) (s : K') {e0 : fib ℂ K' (xv x)} (he0 : e0 ∈ Fx)
    (hs : Val (rB ℂ K' (xv x) {0}) e0.1 s (e0.1 h * (1 - A e0).det))
    (hle : RY (xv x) j2 {0} {0} ≤ loc (rB ℂ K' (xv x) {0}) e0.1)
    {v : Finset ((Mi d ⊕ₗ κ) ⊕ₗ Fin d) → DR ℂ K'}
    (hv : v ∈ (kos (sysY x j2 d).act (omB ℂ K' (loc (rB ℂ K' (xv x) {0}) e0.1) d)
      ((sysY x j2 d).r (app (app n11 n) n10) (app (gG x j2 z) (gT x j2)) 0 0)).Z d)
    {w : Finset (Mi d ⊕ₗ κ) → DR ℂ K'}
    (hw : w ∈ (kos (sysY x j2 d).act (omB ℂ K' (loc (rB ℂ K' (xv x) {0}) e0.1) d)
      ((sysY x j2 d).r (app n11 n) (gG x j2 z) 0 0)).Z d)
    (hvt : v (img inrE) = ((-1) ^ d * (h : K')) • dtS K' x Finset.univ)
    (hwt : w (img ((dj 0 : Fin d ↪o Mi d).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ))) = ((-1) ^ d * s) • dtS K' x Finset.univ -
      v (img (((dj 0 : Fin d ↪o Mi d).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ)).trans (inlE : Mi d ⊕ₗ κ ↪o (Mi d ⊕ₗ κ) ⊕ₗ Fin d)))) :
    w ∈ (kos (sysY x j2 d).act (omB ℂ K' (loc (rB ℂ K' (xv x) {0}) e0.1) d)
      ((sysY x j2 d).r (app n11 n) (gG x j2 z) 0 0)).B d := by
  have cov := hY.toY0.covY
  have red := hY.toY0.red
  obtain ⟨ev, -⟩ := (hVB K' _ e0.1).2.1
  have hst : Stab (sysY x j2 d).act (loc (rB ℂ K' (xv x) {0}) e0.1) (omB ℂ K' (loc (rB ℂ K' (xv x) {0}) e0.1) d) :=
    (hOm K' _ ev d).2.1
  obtain ⟨N, hN, hdet, hrow, hgen⟩ := hFL F K K' d x j2 Fx A hY e0 he0
  obtain ⟨a1, -, a3, -⟩ := hYC F K K' d x j2 Fx A hY κ n z hZ
  have hρ : ∀ l, (sysY x j2 d).r (app (app n11 n) n10) (app (gG x j2 z) (gT x j2)) 0 0 l ∈
      loc (rB ℂ K' (xv x) {0}) e0.1 := fun l => hle (a3 0 0 l)
  have ht : (fun j => (sysY x j2 d).r (app (app n11 n) n10) (app (gG x j2 z) (gT x j2)) 0 0 (inrE j)) = tt K' x :=
    funext (pyc_tt x j2 n z)
  have htO : ∀ l, tt K' x l ∈ loc (rB ℂ K' (xv x) {0}) e0.1 := fun l => pyc_tt x j2 n z l ▸ hρ _
  have hreg := hLR F K' d x cov red e0
  have hKt : KE (kos (sysY x j2 d).act (omB ℂ K' (loc (rB ℂ K' (xv x) {0}) e0.1) d) (tt K' x)) d := by
    refine k1 K' (DR ℂ K') (sysY x j2 d).act (Fin d) _ _ (tt K' x) d (tt K' x) hst htO hreg fun j => ?_
    refine ⟨Pi.single j 1, fun l => ?_, ?_⟩
    · by_cases hl : l = j
      · subst hl
        simpa using one_mem _
      · simpa [Pi.single_eq_of_ne hl] using zero_mem _
    · simp [Pi.single_apply]
  have hKr : KE (kos (sysY x j2 d).act (omB ℂ K' (loc (rB ℂ K' (xv x) {0}) e0.1) d)
      fun a => (sysY x j2 d).r n11 (sysY x j2 d).mu 0 0 (dj 0 a)) d :=
    k1 K' (DR ℂ K') (sysY x j2 d).act (Fin d) _ _ _ d (tt K' x) hst (fun a => hρ (inlE (inlE (dj 0 a)))) hreg hgen
  have hdt : dtS K' x Finset.univ ∈ omB ℂ K' (loc (rB ℂ K' (xv x) {0}) e0.1) d := by
    refine (hLF F K' d x cov red e0 d _).2 ⟨fun _ => 1, fun _ => one_mem _, ?_⟩
    have e1 : (Finset.univ : Finset (Fin d)).powersetCard d = {Finset.univ} := by
      simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin d))
    simp [e1]
  have hval := pyc_val hVB _ e0.1 hs hdet ((hVB K' _ e0.1).2.2.1 h) (mul_comm _ _)
  have hsp := hLM F K' d x cov red e0 _ hval
  have hy : ((-1) ^ d * s) • dtS K' x Finset.univ - (sysY x j2 d).act N.det (v (img inrE)) ∈
      sm (sysY x j2 d).act (omB ℂ K' (loc (rB ℂ K' (xv x) {0}) e0.1) d)
        (Set.range fun j => (sysY x j2 d).r (app (app n11 n) n10) (app (gG x j2 z) (gT x j2)) 0 0 (inrE j)) := by
    rw [ht, hvt]
    have e1 : ((-1) ^ d * s) • dtS K' x Finset.univ -
        (sysY x j2 d).act N.det (((-1) ^ d * (h : K')) • dtS K' x Finset.univ) =
        (sysY x j2 d).act (s - N.det * h) (((-1 : K') ^ d) • dtS K' x Finset.univ) := by
      change ((-1) ^ d * s) • dtS K' x Finset.univ - N.det • (((-1) ^ d * (h : K')) • dtS K' x Finset.univ) =
        (s - N.det * h) • (((-1 : K') ^ d) • dtS K' x Finset.univ)
      simp only [smul_smul, ← sub_smul]
      congr 1
      ring
    rw [e1]
    exact pyc_inSp_act _ hst hsp (hst _ (pow_mem (neg_mem (one_mem _)) d) _ hdt)
  have hsm : sm (sysY x j2 d).act (omB ℂ K' (loc (rB ℂ K' (xv x) {0}) e0.1) d)
        (Set.range fun j => (sysY x j2 d).r (app (app n11 n) n10) (app (gG x j2 z) (gT x j2)) 0 0 (inrE j)) ≤
      sm (sysY x j2 d).act (omB ℂ K' (loc (rB ℂ K' (xv x) {0}) e0.1) d)
        (Set.range fun a => (sysY x j2 d).r n11 (sysY x j2 d).mu 0 0 (dj 0 a)) := by
    rw [ht]
    refine pyc_sm_le _ hst ?_
    rintro _ ⟨l, rfl⟩
    exact hgen l
  have hrel : ∀ a, (sysY x j2 d).r (app (app n11 n) n10) (app (gG x j2 z) (gT x j2)) 0 0
      (inlE (((dj 0 : Fin d ↪o Mi d).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ)) a)) =
      ∑ j, N a j * (sysY x j2 d).r (app (app n11 n) n10) (app (gG x j2 z) (gT x j2)) 0 0 (inrE j) := by
    intro a
    simp only [pyc_tt]
    exact hrow a
  exact pyc_kstep (sysY x j2 d).act k2 k3 _ _ ((sysY x j2 d).r (app (app n11 n) n10) (app (gG x j2 z) (gT x j2)) 0 0)
    ((dj 0 : Fin d ↪o Mi d).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ)) N hst hρ hN hrel (by rw [ht]; exact hKt) hKr hsm hv hw hy hwt

end Conc

section Idx
variable {β γ : Type} [LinearOrder β] [LinearOrder γ]

private theorem pyc_img_uni {d : ℕ} (e : Fin d ↪o β) :
    img ((e : Fin d ↪o β).trans (inlE : β ↪o β ⊕ₗ γ)) = uni (img e) (∅ : Finset γ) := by
  ext t
  simp only [img, uni, inlE, Finset.mem_map, Finset.mem_univ, true_and, Finset.disjSum_empty]
  simp

private theorem pyc_img_map {δ : Type} [LinearOrder δ] {d : ℕ} (e : Fin d ↪o β) (f : β ↪o δ) :
    img ((e : Fin d ↪o β).trans f) = (img e).map f.toEmbedding := by
  ext t
  simp [img]

end Idx

private theorem pyc_colZ (hSB : SysBasic) {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) {κ : Type} [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → S)
    {c : Finset (Two d ⊕ₗ κ) → E} (hc : c ∈ (T.cx n z).Z ((d : ℤ) + 2)) {I J : Finset (Fin (d + 1))}
    (hI : I.card = 1) (hJ : J.card = 1) : col c (uni I J) ∈ (T.colCx n z I J).Z d := by
  obtain ⟨b1, -, -, -, b5, -⟩ := hSB d S E T κ n z ((d : ℤ) + 2)
  have h5 := b5 c hc I J (Finset.card_pos.1 (by omega)) (Finset.card_pos.1 (by omega)) fun I' J' L hlt => by
    refine b1 c hc.1 I' J' L ?_
    by_cases h0 : I' = ∅
    · exact Or.inl h0
    · refine Or.inr (Or.inl ?_)
      have : 0 < I'.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 h0)
      exact Finset.card_eq_zero.1 (by omega)
  have e1 : (d : ℤ) + 2 - (I.card : ℤ) - (J.card : ℤ) = d := by
    rw [hI, hJ]; push_cast; ring
  rwa [e1] at h5

section Conc2
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] {d : ℕ}
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')

private theorem pyc_prodT {κ : Type} [LinearOrder κ] (n : κ → ℕ × ℕ) :
    ∏ l ∈ img (inrE : Fin d ↪o (Mi d ⊕ₗ κ) ⊕ₗ Fin d), (sysY x j2 d).u (app (app n11 n) n10) 0 0 l =
      (sysY x j2 d).X 0 ^ d := by
  have e1 : ∀ a : Fin d, (sysY x j2 d).u (app (app n11 n) n10) 0 0 ((inrE : Fin d ↪o (Mi d ⊕ₗ κ) ⊕ₗ Fin d) a) = (sysY x j2 d).X 0 ^ 1 * (sysY x j2 d).Y 0 ^ 0 :=
    fun _ => rfl
  rw [img, Finset.prod_map]
  refine (Finset.prod_congr rfl fun a _ => e1 a).trans ?_
  simp

private theorem pyc_prodG {κ : Type} [LinearOrder κ] (n : κ → ℕ × ℕ) :
    ∏ l ∈ img ((dj 0 : Fin d ↪o Mi d).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ)), (sysY x j2 d).u (app n11 n) 0 0 l =
      ((sysY x j2 d).X 0 * (sysY x j2 d).Y 0) ^ d := by
  have e1 : ∀ a : Fin d, (sysY x j2 d).u (app n11 n) 0 0 (((dj 0 : Fin d ↪o Mi d).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ)) a) =
      (sysY x j2 d).X 0 ^ 1 * (sysY x j2 d).Y 0 ^ 1 := fun _ => rfl
  rw [img, Finset.prod_map]
  refine (Finset.prod_congr rfl fun a _ => e1 a).trans ?_
  simp

private theorem pyc_prodG' {κ : Type} [LinearOrder κ] (n : κ → ℕ × ℕ) :
    ∏ l ∈ img (((dj 0 : Fin d ↪o Mi d).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ)).trans (inlE : Mi d ⊕ₗ κ ↪o (Mi d ⊕ₗ κ) ⊕ₗ Fin d)),
      (sysY x j2 d).u (app (app n11 n) n10) 0 0 l = ((sysY x j2 d).X 0 * (sysY x j2 d).Y 0) ^ d := by
  have e1 : ∀ a : Fin d, (sysY x j2 d).u (app (app n11 n) n10) 0 0
      ((((dj 0 : Fin d ↪o Mi d).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ)).trans (inlE : Mi d ⊕ₗ κ ↪o (Mi d ⊕ₗ κ) ⊕ₗ Fin d)) a) =
      (sysY x j2 d).X 0 ^ 1 * (sysY x j2 d).Y 0 ^ 1 := fun _ => rfl
  rw [img, Finset.prod_map]
  refine (Finset.prod_congr rfl fun a _ => e1 a).trans ?_
  simp

end Conc2

section Col
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] {d : ℕ}
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')

private theorem collapsed_column_origin (hYC : YCols) (hYKE : YKE) (hPtG : PtG) (hFL : FixLoc) (k1 : K1) (k2 : KoszulBoundaryOfComponentMemIdeal) (k3 : K3)
    (hLR : LocReg) (hLM : LocMax) (hLF : LocForms) (hSB : SysBasic) (hSO : SysOk) (hRS : RS) (hVB : ValBasic)
    (hRY : RYBasic) (hOm : OmLoc) (hWU : WdUni)
    {Fx : Finset (fib ℂ K' (xv x))} {A : fib ℂ K' (xv x) → Matrix (Fin d) (Fin d) ℂ} (hY : Y1 x j2 Fx A)
    {κ : Type} [LinearOrder κ] [Fintype κ] {n : κ → ℕ × ℕ} {z : κ → K ⊗[ℂ] K} (hZ : ZF K x n z)
    (h : rB ℂ K' (xv x) {0}) (s : K')
    (hs : ∀ e ∈ Fx, Val (rB ℂ K' (xv x) {0}) e.1 s (e.1 h * (1 - A e).det))
    {c : Finset (Two d ⊕ₗ ((Mi d ⊕ₗ κ) ⊕ₗ Fin d)) → DR ℂ K'}
    (hc : c ∈ ((sysY x j2 d).cx (app (app n11 n) n10) (app (gG x j2 z) (gT x j2))).Z ((d : ℤ) + 2))
    (hc0 : c (uni (uni {0} {0}) (img inrE)) = ((-1) ^ d * algebraMap F K' (x 0) ^ d * (h : K')) • dtS K' x Finset.univ)
    {c' : Finset (Two d ⊕ₗ (Mi d ⊕ₗ κ)) → DR ℂ K'}
    (hc0' : c' (uni (uni {0} {0}) (uni (img (dj 0)) ∅)) =
      ((-1) ^ d * (algebraMap F K' (x 0) * j2 (algebraMap F K (x 0))) ^ d * s) • dtS K' x Finset.univ)
    (hD : c' - resK inlE c ∈ ((sysY x j2 d).cx (app n11 n) (gG x j2 z)).Z ((d : ℤ) + 2)) :
    col (c' - resK inlE c) (uni {0} {0}) ∈ ((sysY x j2 d).colCx (app n11 n) (gG x j2 z) {0} {0}).B d := by
  have good := (hRY F K K' d x j2 hY.toY0).2.1 d
  obtain ⟨a1, -, a3, -⟩ := hYC F K K' d x j2 Fx A hY κ n z hZ
  have e0c := (hSO d K' (DR ℂ K') (sysY x j2 d) (Mi d ⊕ₗ κ) (app n11 n) (gG x j2 z) good a1).2.1 {0} {0} 0 (by simp) 0 (by simp)
  have e1c := (hSO d K' (DR ℂ K') (sysY x j2 d) ((Mi d ⊕ₗ κ) ⊕ₗ Fin d) (app (app n11 n) n10) (app (gG x j2 z) (gT x j2)) good a3).2.1
    {0} {0} 0 (by simp) 0 (by simp)
  have hzD := pyc_colZ hSB (sysY x j2 d) (app n11 n) (gG x j2 z) hD (I := {0}) (J := {0}) (by simp) (by simp)
  have hzc := pyc_colZ hSB (sysY x j2 d) (app (app n11 n) n10) (app (gG x j2 z) (gT x j2)) hc (I := {0}) (J := {0}) (by simp) (by simp)
  rw [e0c.2] at hzD ⊢
  rw [e1c.2] at hzc
  have R0 := hRS K' (DR ℂ K') (sysY x j2 d).act (Mi d ⊕ₗ κ) ((sysY x j2 d).M {0} {0}) ((sysY x j2 d).u (app n11 n) 0 0)
    ((sysY x j2 d).r (app n11 n) (gG x j2 z) 0 0) (gG x j2 z) (fun _ => rfl) d (col (c' - resK inlE c) (uni {0} {0}))
  have R1 := hRS K' (DR ℂ K') (sysY x j2 d).act ((Mi d ⊕ₗ κ) ⊕ₗ Fin d) ((sysY x j2 d).M {0} {0})
    ((sysY x j2 d).u (app (app n11 n) n10) 0 0)
    ((sysY x j2 d).r (app (app n11 n) n10) (app (gG x j2 z) (gT x j2)) 0 0) (app (gG x j2 z) (gT x j2)) (fun _ => rfl) d
    (col c (uni {0} {0}))
  have hw := R0.2.1.1 hzD
  have hv := R1.2.1.1 hzc
  refine R0.2.2.1.2 ?_
  refine (hYKE F K K' d x j2 hY.toY0 (Mi d ⊕ₗ κ) ((sysY x j2 d).r (app n11 n) (gG x j2 z) 0 0) {0} {0} (by simp)
    (fun l => a1 0 0 l)).2.1 d _ hw fun e he => ?_
  obtain ⟨-, e0, he0, -, hO2, -⟩ := hPtG F K K' d x j2 Fx A hY κ n z hZ {0} {0} 0 (by simp) 0 (by simp) e he
  have hle : RY (xv x) j2 {0} {0} ≤ loc (rB ℂ K' (xv x) {0}) e0.1 := hO2 ▸ (hVB K' _ e).1
  have hMle : (sysY x j2 d).M {0} {0} ≤ omB ℂ K' (loc (rB ℂ K' (xv x) {0}) e0.1) d := (hOm K' _ e d).2.2 _ hle
  rw [hO2]
  refine pyc_local x j2 hYC hFL k1 k2 k3 hLR hLM hLF hVB hOm hY hZ h s he0 (hs e0 he0) hle
    (pyc_kosZ_mono _ hMle _ _ hv) (pyc_kosZ_mono _ hMle _ _ hw) ?_ ?_
  · have e2 := pyc_prodT x j2 n
    change (sysY x j2 d).act (((∏ l ∈ img (inrE : Fin d ↪o (Mi d ⊕ₗ κ) ⊕ₗ Fin d), (sysY x j2 d).u (app (app n11 n) n10) 0 0 l)⁻¹ : K'ˣ) : K')
      (c (uni (uni {0} {0}) (img inrE))) = _
    rw [e2, hc0]
    change ((((sysY x j2 d).X 0 ^ d)⁻¹ : K'ˣ) : K') •
      (((-1) ^ d * ((sysY x j2 d).X 0 : K') ^ d * (h : K')) • dtS K' x Finset.univ) = _
    rw [smul_smul]
    congr 1
    have hG : ((((sysY x j2 d).X 0 ^ d)⁻¹ : K'ˣ) : K') * ((sysY x j2 d).X 0 : K') ^ d = 1 := by
      rw [← Units.val_pow_eq_pow_val]
      exact Units.inv_mul _
    linear_combination ((-1) ^ d * (h : K')) * hG
  · have e2 := pyc_prodG x j2 n
    have e3 := pyc_prodG' x j2 n
    have l1 := (hWU _ _ ℂ 0 0 (uni {0} {0} : Finset (Two d)) (img ((dj 0 : Fin d ↪o Mi d).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ)))).2.1
    have l2 := (hWU _ _ ℂ 0 0 (uni {0} {0} : Finset (Two d)) (img ((dj 0 : Fin d ↪o Mi d).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ)))).2.2.1
    have r1 : resK inlE c (uni (uni {0} {0}) (img ((dj 0 : Fin d ↪o Mi d).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ)))) = c (uni (uni {0} {0}) (img (((dj 0 : Fin d ↪o Mi d).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ)).trans (inlE : Mi d ⊕ₗ κ ↪o (Mi d ⊕ₗ κ) ⊕ₗ Fin d)))) := by
      rw [pyc_img_map ((dj 0 : Fin d ↪o Mi d).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ)) (inlE : Mi d ⊕ₗ κ ↪o (Mi d ⊕ₗ κ) ⊕ₗ Fin d)]
      simp only [resK, l1, l2]
    have e4 : col (c' - resK inlE c) (uni {0} {0}) (img ((dj 0 : Fin d ↪o Mi d).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ))) =
        c' (uni (uni {0} {0}) (uni (img (dj 0)) ∅)) - c (uni (uni {0} {0}) (img (((dj 0 : Fin d ↪o Mi d).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ)).trans (inlE : Mi d ⊕ₗ κ ↪o (Mi d ⊕ₗ κ) ⊕ₗ Fin d)))) := by
      rw [← r1, ← pyc_img_uni]
      rfl
    change (sysY x j2 d).act (((∏ l ∈ img ((dj 0 : Fin d ↪o Mi d).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ)), (sysY x j2 d).u (app n11 n) 0 0 l)⁻¹ : K'ˣ) : K')
        (col (c' - resK inlE c) (uni {0} {0}) (img ((dj 0 : Fin d ↪o Mi d).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ)))) = _ -
      (sysY x j2 d).act (((∏ l ∈ img (((dj 0 : Fin d ↪o Mi d).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ)).trans (inlE : Mi d ⊕ₗ κ ↪o (Mi d ⊕ₗ κ) ⊕ₗ Fin d)), (sysY x j2 d).u (app (app n11 n) n10) 0 0 l)⁻¹ : K'ˣ) : K')
        (c (uni (uni {0} {0}) (img (((dj 0 : Fin d ↪o Mi d).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ)).trans (inlE : Mi d ⊕ₗ κ ↪o (Mi d ⊕ₗ κ) ⊕ₗ Fin d)))))
    rw [e2, e3, e4, hc0', map_sub]
    congr 1
    change ((((sysY x j2 d).X 0 * (sysY x j2 d).Y 0) ^ d)⁻¹ : K'ˣ).val •
      (((-1) ^ d * (((sysY x j2 d).X 0 * (sysY x j2 d).Y 0 : K'ˣ) : K') ^ d * s) • dtS K' x Finset.univ) = _
    rw [smul_smul]
    congr 1
    have hG : ((((sysY x j2 d).X 0 * (sysY x j2 d).Y 0) ^ d)⁻¹ : K'ˣ).val *
        (((sysY x j2 d).X 0 * (sysY x j2 d).Y 0 : K'ˣ) : K') ^ d = 1 := by
      rw [← Units.val_pow_eq_pow_val]
      exact Units.inv_mul _
    linear_combination ((-1) ^ d * s) * hG

end Col

theorem UpperTheory.Gal.productCup_of_system.yCmpG_of :
    YCols → YKE → PtG → FixLoc → K1 → KoszulBoundaryOfComponentMemIdeal → K3 → LocReg → LocMax → LocForms → CechKoszulSystemBoundaryCriterion → SysBasic → SysOk → RS → ValBasic → RYBasic → OmLoc → WdUni → YCmpG := by
  intro hYC hYKE hPtG hFL k1 k2 k3 hLR hLM hLF hL1 hSB hSO hRS hVB hRY hOm hWU
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A hY κ _ _ n z hZ h s hs c hc hc0 c' hc' hc0'
  have good := (hRY F K K' d x j2 hY.toY0).2.1 d
  obtain ⟨a1, -, -, hKE⟩ := hYC F K K' d x j2 Fx A hY κ n z hZ
  obtain ⟨b1, -, -, b4, -, -⟩ := hSB d K' (DR ℂ K') (sysY x j2 d) (Mi d ⊕ₗ κ) (app n11 n) (gG x j2 z) ((d : ℤ) + 2)
  have hc'' : resK inlE c ∈ ((sysY x j2 d).cx (app n11 n) (gG x j2 z)).Z ((d : ℤ) + 2) :=
    (hSB d K' (DR ℂ K') (sysY x j2 d) ((Mi d ⊕ₗ κ) ⊕ₗ Fin d) (app (app n11 n) n10) (app (gG x j2 z) (gT x j2))
      ((d : ℤ) + 2)).2.2.2.2.2 (Mi d ⊕ₗ κ) inlE c hc
  have hD : c' - resK inlE c ∈ ((sysY x j2 d).cx (app n11 n) (gG x j2 z)).Z ((d : ℤ) + 2) := sub_mem hc' hc''
  have hB := hL1 d K' (DR ℂ K') (sysY x j2 d) (Mi d ⊕ₗ κ) (app n11 n) (gG x j2 z) ((d : ℤ) + 2) good a1
    (fun I J hI hJ => (hKE I J hI hJ).1) (c' - resK inlE c) hD ?_ ?_
  · have e1 : top (c' - resK inlE c) = top c' - top c := by
      funext b
      have l1 := (hWU _ _ ℂ 0 0 b (∅ : Finset (Mi d ⊕ₗ κ))).2.1
      have l2 := (hWU _ _ ℂ 0 0 b (∅ : Finset (Mi d ⊕ₗ κ))).2.2.1
      simp [top, resK, l1, l2]
    rw [← e1]
    exact b4 _ hB
  · intro b L hL
    rw [← (hWU (Fin (d + 1)) (Fin (d + 1)) ℂ 0 0 ∅ ∅).2.2.2.2 b]
    refine b1 _ hD.1 _ _ L ?_
    by_cases h1 : lft b = ∅
    · exact Or.inl h1
    by_cases h2 : rgt b = ∅
    · exact Or.inr (Or.inl h2)
    refine Or.inr (Or.inr ?_)
    have p1 : 0 < (lft b).card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 h1)
    have p2 : 0 < (rgt b).card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 h2)
    push_cast
    omega
  · intro I J hI hJ hcard
    have p1 := Finset.card_pos.2 hI
    have p2 := Finset.card_pos.2 hJ
    push_cast at hcard
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 (show I.card = 1 by omega)
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 (show J.card = 1 by omega)
    by_cases hij : i = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := hij
      exact collapsed_column_origin x j2 hYC hYKE hPtG hFL k1 k2 k3 hLR hLM hLF hSB hSO hRS hVB hRY hOm hWU hY hZ h s hs hc hc0 hc0' hD
    · have hz := pyc_colZ hSB (sysY x j2 d) (app n11 n) (gG x j2 z) hD (I := {i}) (J := {j}) (by simp) (by simp)
      refine (((hKE {i} {j} hI hJ).2.2.2 ?_ d).1) hz
      by_contra hcon
      push_neg at hcon
      exact hij ⟨Finset.singleton_injective hcon.1, Finset.singleton_injective hcon.2⟩
