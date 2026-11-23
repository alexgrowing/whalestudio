import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomLocBijectiveGrSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

section Tower

variable {ι : Type} [LinearOrder ι] {R : Type} [CommRing R] {g : ℕ} (ρ : Fin g → R)
  {T : ℕ → ℤ → Finset ι → Type} [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)]
  (res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S')
  (p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S)
  (mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S)

def TowerAx : Prop :=
  (∀ e t S S' (h : S ⊆ S') a, S.Nonempty →
    p e t S' (res (e + 1) t S S' h a) = res e t S S' h (p e t S a)) ∧
  (∀ j e t S a, S.Nonempty → p e (t + 1) S (mm j (e + 1) t S a) = mm j e t S (p e t S a)) ∧
  (∀ j e t S S' (h : S ⊆ S') a, S.Nonempty →
    res e (t + 1) S S' h (mm j e t S a) - mm j e t S' (res e t S S' h a) ∈
      Ideal.span (Set.range ρ) • (⊤ : Submodule R (T e (t + 1) S'))) ∧
  (∀ e t S, S.Nonempty → Function.Surjective (p e t S)) ∧
  (∀ e t S, S.Nonempty → LinearMap.ker (p e t S) = Ideal.span (Set.range ρ) ^ (e + 1) • ⊤) ∧
  (∀ e t S, S.Nonempty → Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (T e t S)) = ⊥)

def Ks (e : ℕ) (t : ℤ) (S : Finset ι) : Submodule R (T (e + 1) t S) :=
  if S.Nonempty then LinearMap.ker (p e t S) else ⊥

variable {ρ res p mm}

theorem mem_Ks {e : ℕ} {t : ℤ} {S : Finset ι} (hS : S.Nonempty) {a : T (e + 1) t S} :
    a ∈ Ks p e t S ↔ p e t S a = 0 := by
  simp [Ks, hS]

theorem eq_zero_of_mem_Ks {e : ℕ} {t : ℤ} {S : Finset ι} (hS : ¬S.Nonempty) {a : T (e + 1) t S}
    (ha : a ∈ Ks p e t S) : a = 0 := by
  simp only [Ks, if_neg hS, Submodule.mem_bot] at ha
  exact ha

theorem rho_mem (l : Fin g) : ρ l ∈ Ideal.span (Set.range ρ) := Ideal.subset_span ⟨l, rfl⟩

namespace TowerAx

variable (H : TowerAx ρ res p mm)
include H

theorem p_res (e t S S') (h : S ⊆ S') (a) (hS : S.Nonempty) :
    p e t S' (res (e + 1) t S S' h a) = res e t S S' h (p e t S a) := H.1 e t S S' h a hS

theorem p_mm (j e t S a) (hS : S.Nonempty) :
    p e (t + 1) S (mm j (e + 1) t S a) = mm j e t S (p e t S a) := H.2.1 j e t S a hS

theorem res_mm (j e t S S') (h : S ⊆ S') (a) (hS : S.Nonempty) :
    res e (t + 1) S S' h (mm j e t S a) - mm j e t S' (res e t S S' h a) ∈
      Ideal.span (Set.range ρ) • (⊤ : Submodule R (T e (t + 1) S')) := H.2.2.1 j e t S S' h a hS

theorem surj (e t S) (hS : S.Nonempty) : Function.Surjective (p e t S) := H.2.2.2.1 e t S hS

theorem ker_eq (e t S) (hS : S.Nonempty) :
    LinearMap.ker (p e t S) = Ideal.span (Set.range ρ) ^ (e + 1) • ⊤ := H.2.2.2.2.1 e t S hS

theorem kill (e t S) (hS : S.Nonempty) :
    Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (T e t S)) = ⊥ := H.2.2.2.2.2 e t S hS

theorem smul_eq_zero_of_mem {e : ℕ} {t : ℤ} {S : Finset ι} (hS : S.Nonempty) {m n : ℕ}
    (hmn : m + n = e + 1) {r : R} (hr : r ∈ Ideal.span (Set.range ρ) ^ m) {w : T e t S}
    (hw : w ∈ Ideal.span (Set.range ρ) ^ n • (⊤ : Submodule R (T e t S))) : r • w = 0 := by
  have hrw : r • w ∈ (Ideal.span (Set.range ρ) ^ m * Ideal.span (Set.range ρ) ^ n) •
      (⊤ : Submodule R (T e t S)) := by
    rw [Submodule.mul_smul]
    exact Submodule.smul_mem_smul hr hw
  rw [← pow_add, hmn, H.kill e t S hS] at hrw
  exact (Submodule.mem_bot R).1 hrw

theorem smul_eq_zero_of_p {e : ℕ} {t : ℤ} {S : Finset ι} (hS : S.Nonempty) {r : R}
    (hr : r ∈ Ideal.span (Set.range ρ)) {a : T (e + 1) t S} (ha : p e t S a = 0) : r • a = 0 := by
  have hw : a ∈ Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (T (e + 1) t S)) := by
    rw [← H.ker_eq e t S hS]
    exact LinearMap.mem_ker.mpr ha
  exact H.smul_eq_zero_of_mem hS (m := 1) (n := e + 1) (by omega) (by rwa [pow_one]) hw

theorem rho_smul_surjInv (l : Fin g) {e : ℕ} {t : ℤ} {S : Finset ι} (hS : S.Nonempty)
    (b : T (e + 1 + 1) t S) :
    ρ l • Function.surjInv (H.surj (e + 1) t S hS) (p (e + 1) t S b) = ρ l • b := by
  have h : p (e + 1) t S (Function.surjInv (H.surj (e + 1) t S hS) (p (e + 1) t S b) - b) = 0 := by
    rw [map_sub, Function.surjInv_eq (H.surj (e + 1) t S hS), sub_self]
  have := H.smul_eq_zero_of_p hS (rho_mem l) h
  rwa [smul_sub, sub_eq_zero] at this

omit H in

def lam (H : TowerAx ρ res p mm) (l : Fin g) (e : ℕ) (t : ℤ) (S : Finset ι) (hS : S.Nonempty) :
    T (e + 1) t S →ₗ[R] T (e + 1 + 1) t S where
  toFun a := ρ l • Function.surjInv (H.surj (e + 1) t S hS) a
  map_add' a b := by
    obtain ⟨a, rfl⟩ := H.surj (e + 1) t S hS a
    obtain ⟨b, rfl⟩ := H.surj (e + 1) t S hS b
    rw [← map_add, H.rho_smul_surjInv l hS, H.rho_smul_surjInv l hS, H.rho_smul_surjInv l hS,
      smul_add]
  map_smul' r a := by
    obtain ⟨a, rfl⟩ := H.surj (e + 1) t S hS a
    rw [← map_smul, H.rho_smul_surjInv l hS, H.rho_smul_surjInv l hS, RingHom.id_apply, smul_comm]

omit H in
theorem lam_p (H : TowerAx ρ res p mm) (l : Fin g) {e : ℕ} {t : ℤ} {S : Finset ι}
    (hS : S.Nonempty) (b : T (e + 1 + 1) t S) :
    H.lam l e t S hS (p (e + 1) t S b) = ρ l • b := H.rho_smul_surjInv l hS b

omit H in

def yK (H : TowerAx ρ res p mm) (l : Fin g) (e : ℕ) (t : ℤ) (S : Finset ι) :
    Ks p e t S →ₗ[R] Ks p (e + 1) t S :=
  if hS : S.Nonempty then
    (H.lam l e t S hS).restrict fun a ha => by
      obtain ⟨b, rfl⟩ := H.surj (e + 1) t S hS a
      rw [mem_Ks hS, H.lam_p, map_smul]
      exact H.smul_eq_zero_of_p hS (rho_mem l) ((mem_Ks hS).1 ha)
  else 0

omit H in

theorem coe_yK (H : TowerAx ρ res p mm) (l : Fin g) {e : ℕ} {t : ℤ} {S : Finset ι}
    (hS : S.Nonempty) (a : Ks p e t S) (b : T (e + 1 + 1) t S) (hb : p (e + 1) t S b = a) :
    (H.yK l e t S a : T (e + 1 + 1) t S) = ρ l • b := by
  simp only [yK, dif_pos hS, LinearMap.restrict_coe_apply]
  rw [← hb, H.lam_p]

omit H in

def xK (H : TowerAx ρ res p mm) (j : ι) (e : ℕ) (t : ℤ) (S : Finset ι) :
    Ks p e t S →ₗ[R] Ks p e (t + 1) S :=
  (mm j (e + 1) t S).restrict fun a ha => by
    by_cases hS : S.Nonempty
    · rw [mem_Ks hS, H.p_mm j e t S a hS, (mem_Ks hS).1 ha, map_zero]
    · rw [eq_zero_of_mem_Ks hS ha, map_zero]
      exact zero_mem _

omit H in
@[simp]
theorem coe_xK (H : TowerAx ρ res p mm) (j : ι) (e : ℕ) (t : ℤ) (S : Finset ι) (a : Ks p e t S) :
    (H.xK j e t S a : T (e + 1) (t + 1) S) = mm j (e + 1) t S a := rfl

omit H in

def resK (H : TowerAx ρ res p mm) (e : ℕ) (t : ℤ) {S S' : Finset ι} (h : S ⊆ S') :
    Ks p e t S →ₗ[R] Ks p e t S' :=
  (res (e + 1) t S S' h).restrict fun a ha => by
    by_cases hS : S.Nonempty
    · rw [mem_Ks (hS.mono h), H.p_res e t S S' h a hS, (mem_Ks hS).1 ha, map_zero]
    · rw [eq_zero_of_mem_Ks hS ha, map_zero]
      exact zero_mem _

omit H in
@[simp]
theorem coe_resK (H : TowerAx ρ res p mm) (e : ℕ) (t : ℤ) {S S' : Finset ι} (h : S ⊆ S')
    (a : Ks p e t S) : (H.resK e t h a : T (e + 1) t S') = res (e + 1) t S S' h a := rfl

omit H in

def ops (H : TowerAx ρ res p mm)
    (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S) fun j t => mm j e t S)
    (S : Finset ι) : BiOps (R := R) (fun e t => Ks p e t S) ι (Fin g) where
  x j e t := H.xK j e t S
  y l e t := H.yK l e t S
  hx i j e t a := Subtype.ext (hc (e + 1) S i j t a)
  hy k l e t a := by
    by_cases hS : S.Nonempty
    · obtain ⟨b, hb⟩ := H.surj (e + 1) t S hS a
      obtain ⟨c, hc'⟩ := H.surj (e + 1 + 1) t S hS b
      have h1 (l : Fin g) : p (e + 1 + 1) t S (ρ l • c) = H.yK l e t S a := by
        rw [map_smul, hc', H.coe_yK l hS a b hb]
      apply Subtype.ext
      rw [H.coe_yK k hS _ _ (h1 l), H.coe_yK l hS _ _ (h1 k), smul_comm]
    · apply Subtype.ext
      simp [yK, hS]
  hxy j l e t a := by
    by_cases hS : S.Nonempty
    · obtain ⟨b, hb⟩ := H.surj (e + 1) t S hS a
      apply Subtype.ext
      have h1 : p (e + 1) (t + 1) S (mm j (e + 1 + 1) t S b) = H.xK j e t S a := by
        rw [H.p_mm j (e + 1) t S b hS, hb, coe_xK]
      rw [H.coe_yK l hS _ _ h1, coe_xK, H.coe_yK l hS a b hb, map_smul]
    · apply Subtype.ext
      simp [yK, hS]

omit H in

theorem resK_xK (H : TowerAx ρ res p mm) (j : ι) (e : ℕ) (t : ℤ) {S S' : Finset ι} (h : S ⊆ S')
    (a : Ks p e t S) :
    H.resK e (t + 1) h (H.xK j e t S a) = H.xK j e t S' (H.resK e t h a) := by
  apply Subtype.ext
  simp only [coe_resK, coe_xK]
  by_cases hS : S.Nonempty
  · have hS' : S'.Nonempty := hS.mono h
    have ha : (a : T (e + 1) t S) ∈
        Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (T (e + 1) t S)) := by
      rw [← H.ker_eq e t S hS]
      exact LinearMap.mem_ker.mpr ((mem_Ks hS).1 a.2)
    have key : Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (T (e + 1) t S)) ≤
        LinearMap.ker (res (e + 1) (t + 1) S S' h ∘ₗ mm j (e + 1) t S -
          mm j (e + 1) t S' ∘ₗ res (e + 1) t S S' h) := by
      rw [Submodule.smul_le]
      intro r hr x _
      rw [LinearMap.mem_ker, map_smul]
      refine H.smul_eq_zero_of_mem hS' (m := e + 1) (n := 1) rfl hr ?_
      rw [pow_one]
      exact H.res_mm j (e + 1) t S S' h x hS
    have hk := key ha
    rw [LinearMap.mem_ker] at hk
    simpa [sub_eq_zero] using hk
  · rw [eq_zero_of_mem_Ks hS a.2]
    simp

omit H in

theorem resK_yK (H : TowerAx ρ res p mm) (l : Fin g) (e : ℕ) (t : ℤ) {S S' : Finset ι}
    (h : S ⊆ S') (a : Ks p e t S) :
    H.resK (e + 1) t h (H.yK l e t S a) = H.yK l e t S' (H.resK e t h a) := by
  apply Subtype.ext
  by_cases hS : S.Nonempty
  · obtain ⟨b, hb⟩ := H.surj (e + 1) t S hS a
    have h1 : p (e + 1) t S' (res (e + 1 + 1) t S S' h b) = H.resK e t h a := by
      rw [H.p_res (e + 1) t S S' h b hS, hb, coe_resK]
    rw [H.coe_yK l (hS.mono h) _ _ h1, coe_resK, H.coe_yK l hS a b hb, map_smul]
  · obtain rfl : a = 0 := Subtype.ext (eq_zero_of_mem_Ks hS a.2)
    simp

variable (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S)
  fun j t => mm j e t S)

omit H in

abbrev Tot (H : TowerAx ρ res p mm) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R)
    (A := fun t => T e t S) fun j t => mm j e t S) (S : Finset ι) : Type :=
  (H.ops hc S).Tot

omit H in

def resTot (H : TowerAx ρ res p mm) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R)
    (A := fun t => T e t S) fun j t => mm j e t S) (S S' : Finset ι) (h : S ⊆ S') :
    H.Tot hc S →ₗ[MvPolynomial ι (MvPolynomial (Fin g) R)] H.Tot hc S' :=
  (H.ops hc S).map (H.ops hc S') (fun e t => H.resK e t h) (fun j e t a => H.resK_xK j e t h a)
    fun l e t a => H.resK_yK l e t h a

omit H in
@[simp]
theorem resTot_of (H : TowerAx ρ res p mm) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R)
    (A := fun t => T e t S) fun j t => mm j e t S) {S S' : Finset ι} (h : S ⊆ S') (e : ℕ) (t : ℤ)
    (a : Ks p e t S) :
    H.resTot hc S S' h ((H.ops hc S).of e t a) = (H.ops hc S').of e t (H.resK e t h a) :=
  BiOps.map_of (H.ops hc S) (H.ops hc S') (fun e t => H.resK e t h)
    (fun j e t a => H.resK_xK j e t h a) (fun l e t a => H.resK_yK l e t h a) e t a

omit H in

theorem comp_resTot (H : TowerAx ρ res p mm) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R)
    (A := fun t => T e t S) fun j t => mm j e t S) {S S' : Finset ι} (h : S ⊆ S') (e : ℕ) (t : ℤ)
    (m : H.Tot hc S) :
    (H.ops hc S').comp e t (H.resTot hc S S' h m) = H.resK e t h ((H.ops hc S).comp e t m) :=
  BiOps.comp_map (H.ops hc S) (H.ops hc S') (fun e t => H.resK e t h)
    (fun j e t a => H.resK_xK j e t h a) (fun l e t a => H.resK_yK l e t h a) e t m

omit H in
theorem isGradedMap_resTot (H : TowerAx ρ res p mm) (hc : ∀ e S, OperatorsCommute (ι := ι)
    (R := R) (A := fun t => T e t S) fun j t => mm j e t S) {S S' : Finset ι} (h : S ⊆ S') :
    IsGradedMap (H.ops hc S).grading (H.ops hc S').grading (H.resTot hc S S' h) :=
  BiOps.isGradedMap_map (H.ops hc S) (H.ops hc S') (fun e t => H.resK e t h)
    (fun j e t a => H.resK_xK j e t h a) (fun l e t a => H.resK_yK l e t h a)

end TowerAx

end Tower

end GlobalTheory.CompanionTheory.FormalAlg.Lift
