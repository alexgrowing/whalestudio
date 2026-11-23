import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActRel

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def prodPow {r : ℕ} (f : Fin r → (A ⟶ A)) (c : Fin r → ℤ) : A ⟶ A := ∏ k, f k ^ c k

theorem prodPow_add {r : ℕ} (f : Fin r → (A ⟶ A)) (c d : Fin r → ℤ) :
    prodPow f (c + d) = prodPow f c * prodPow f d := by
  simp [prodPow, zpow_add, Finset.prod_mul_distrib]

theorem prodPow_zero {r : ℕ} (f : Fin r → (A ⟶ A)) : prodPow f 0 = 1 := by
  simp [prodPow]

theorem prodPow_zsmul {r : ℕ} (f : Fin r → (A ⟶ A)) (n : ℤ) (c : Fin r → ℤ) :
    prodPow f (n • c) = prodPow f c ^ n := by
  simp [prodPow, zpow_mul', Finset.prod_zpow]

theorem prodPow_single {r : ℕ} (f : Fin r → (A ⟶ A)) (k : Fin r) : prodPow f (Pi.single k 1) = f k := by
  unfold prodPow
  rw [Finset.prod_eq_single k]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

def prodPowHom {r : ℕ} (f : Fin r → (A ⟶ A)) : Multiplicative (Fin r → ℤ) →* (A ⟶ A) :=
  MonoidHom.mk' (fun c => prodPow f c.toAdd) (fun c d => prodPow_add f c.toAdd d.toAdd)

theorem prodPow_sum {r : ℕ} (f : Fin r → (A ⟶ A)) {J : Type} (s : Finset J) (g : J → Fin r → ℤ) :
    prodPow f (∑ i ∈ s, g i) = ∏ i ∈ s, prodPow f (g i) := by
  have := map_prod (prodPowHom f) (fun i => Multiplicative.ofAdd (g i)) s
  rw [← ofAdd_sum] at this
  exact this

def precompHom (h : A ⟶ A) : (A ⟶ A) →* (A ⟶ A) :=
  MonoidHom.mk' (fun x => h ≫ x) (fun x y => MonObj.comp_mul h x y)

def postcompHom (h : A ⟶ A) [IsMonHom h] : (A ⟶ A) →* (A ⟶ A) :=
  MonoidHom.mk' (fun x => x ≫ h) (fun x y => MonObj.mul_comp x y h)

end GlobalTheory.ActRel

namespace GlobalTheory.ActRel

theorem prodPow_comp {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {r : ℕ} (f : Fin r → (A ⟶ A))
    (hf : ∀ k, IsMonHom (f k)) (cm : Fin r → Fin r → Fin r → ℤ) (hm : ∀ i j, f i ≫ f j = prodPow f (cm i j))
    (c d : Fin r → ℤ) :
    prodPow f c ≫ prodPow f d = prodPow f (∑ k, ∑ l, (c k * d l) • cm k l) := by
  haveI : IsMonHom (prodPow f d) := isMonHom_prodPow f hf d
  have h1 : prodPow f c ≫ prodPow f d = ∏ k, (f k ≫ prodPow f d) ^ c k := by
    have := map_prod (postcompHom (prodPow f d)) (fun k => f k ^ c k) Finset.univ
    refine this.trans (Finset.prod_congr rfl fun k _ => ?_)
    show (f k ^ c k) ≫ prodPow f d = _
    exact GrpObj.zpow_comp (f k) (c k) (prodPow f d)
  have h2 : ∀ k, f k ≫ prodPow f d = ∏ l, prodPow f (cm k l) ^ d l := by
    intro k
    have := map_prod (precompHom (f k)) (fun l => f l ^ d l) Finset.univ
    refine this.trans (Finset.prod_congr rfl fun l _ => ?_)
    show f k ≫ f l ^ d l = _
    rw [GrpObj.comp_zpow, hm]
  rw [h1, prodPow_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [h2, prodPow_sum, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [prodPow_zsmul, ← zpow_mul, mul_comm]

theorem ringAct_iff_relations : ∀ (O : Type) [Ring O] (r : ℕ) (e : Fin r → O),
    Submodule.span ℤ (Set.range e) = ⊤ → ∃ (m : ℕ) (N : Fin m → Fin r → ℤ) (c1 : Fin r → ℤ)
      (cm : Fin r → Fin r → Fin r → ℤ), ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A]
      (f : Fin r → (A ⟶ A)), (∀ k, IsMonHom (f k)) → ((∃ act : O → (A ⟶ A), IsRAct A act ∧ ∀ k, act (e k) = f k) ↔
        ((∀ j, ∏ k, f k ^ N j k = 1) ∧ ∏ k, f k ^ c1 k = 𝟙 A ∧
          ∀ i j, f i ≫ f j = ∏ k, f k ^ cm i j k)) := by
  intro O _ r e he
  let φ : (Fin r → ℤ) →ₗ[ℤ] O :=
    { toFun := fun c => ∑ k, c k • e k
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun n c => by simp [Finset.smul_sum, mul_smul] }
  have hφ : ∀ c, φ c = ∑ k, c k • e k := fun _ => rfl
  have hsurj : ∀ a, ∃ c, φ c = a := fun a => by
    have : a ∈ Submodule.span ℤ (Set.range e) := he ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp this
    exact ⟨c, hc⟩
  obtain ⟨m, N, hN⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (LinearMap.ker φ))
  choose coef hcoef using hsurj
  refine ⟨m, N, coef 1, fun i j => coef (e i * e j), ?_⟩
  intro S A _ _ f hf
  have hker : (∀ j, prodPow f (N j) = 1) → ∀ c ∈ LinearMap.ker φ, prodPow f c = 1 := by
    intro hNj c hc
    rw [← hN] at hc
    induction hc using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hNj j
    | zero => exact prodPow_zero f
    | add x y _ _ hx hy => rw [prodPow_add, hx, hy, _root_.mul_one]
    | smul n x _ hx => rw [prodPow_zsmul, hx, one_zpow]
  have hwd : (∀ j, prodPow f (N j) = 1) → ∀ c d, φ c = φ d → prodPow f c = prodPow f d := by
    intro hNj c d h
    have hcd : c - d ∈ LinearMap.ker φ := by simp [LinearMap.mem_ker, map_sub, h]
    calc prodPow f c = prodPow f (d + (c - d)) := by rw [add_sub_cancel]
      _ = prodPow f d := by rw [prodPow_add, hker hNj _ hcd, _root_.mul_one]
  have hmul : ∀ c d : Fin r → ℤ, φ c * φ d = ∑ k, ∑ l, (c k * d l) • (e k * e l) := by
    intro c d
    rw [hφ, hφ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, mul_smul]
  constructor
  · rintro ⟨act, hact, hek⟩
    have h0 : act 0 = 1 := by
      have := hact.2.2.2 0 0
      rw [add_zero] at this
      exact mul_eq_left.mp this.symm
    let H : Multiplicative O →* (A ⟶ A) :=
      MonoidHom.mk' (fun a => act a.toAdd) (fun a b => hact.2.2.2 a.toAdd b.toAdd)
    have hact' : ∀ c, act (φ c) = prodPow f c := by
      intro c
      have : act (φ c) = H (Multiplicative.ofAdd (∑ k, c k • e k)) := rfl
      rw [this, ofAdd_sum, map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [ofAdd_zsmul, map_zpow]
      show act (e k) ^ c k = _
      rw [hek]
    refine ⟨fun j => ?_, ?_, fun i j => ?_⟩
    · show prodPow f (N j) = 1
      have hNj : N j ∈ LinearMap.ker φ := hN ▸ Submodule.subset_span ⟨j, rfl⟩
      rw [← hact', LinearMap.mem_ker.mp hNj, h0]
    · show prodPow f (coef 1) = 𝟙 A
      rw [← hact', hcoef, hact.2.1]
    · show f i ≫ f j = prodPow f (coef (e i * e j))
      rw [← hact', hcoef, hact.2.2.1, hek, hek]
  · rintro ⟨hNj, h1, hm⟩
    refine ⟨fun a => prodPow f (coef a), ⟨fun a => isMonHom_prodPow f hf _, h1, fun a b => ?_, fun a b => ?_⟩,
      fun k => ?_⟩
    · rw [prodPow_comp f hf _ hm]
      apply hwd hNj
      rw [hcoef, map_sum]
      simp only [map_sum, map_zsmul, hcoef]
      rw [← hmul, hcoef, hcoef]
    · rw [← prodPow_add]
      apply hwd hNj
      rw [map_add, hcoef, hcoef, hcoef]
    · show prodPow f (coef (e k)) = f k
      rw [hwd hNj (coef (e k)) (Pi.single k 1) (by rw [hcoef, hφ]; simp [Pi.single_apply]),
        prodPow_single]

end GlobalTheory.ActRel
