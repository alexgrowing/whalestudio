import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.LocalHeckeLevel

theorem sum_mul_left_eq {Gp M : Type} [Group Gp] [AddCommMonoid M] (K : Subgroup Gp) (α : Gp) (C : Finset Gp)
    (h1 : ∀ γ ∈ C, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * α * k₂)
    (h2 : ∀ x : Gp, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * α * k₂) → ∃! γ, γ ∈ C ∧ γ⁻¹ * x ∈ K)
    (F : Gp → M) (hF : ∀ x, ∀ κ ∈ K, F (x * κ) = F x) {k₀ : Gp} (hk₀ : k₀ ∈ K) :
    ∑ δ ∈ C, F (k₀ * δ) = ∑ δ ∈ C, F δ := by
  classical
  have hmem : ∀ k ∈ K, ∀ δ ∈ C, ∃ k₁ ∈ K, ∃ k₂ ∈ K, k * δ = k₁ * α * k₂ := by
    intro k hk δ hδ
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := h1 δ hδ
    exact ⟨k * k₁, K.mul_mem hk hk₁, k₂, hk₂, by simp only [mul_assoc]⟩
  let s : Gp → Gp → Gp := fun k δ =>
    if h : ∃ k₁ ∈ K, ∃ k₂ ∈ K, k * δ = k₁ * α * k₂ then (h2 _ h).exists.choose else δ
  have hs : ∀ k ∈ K, ∀ δ ∈ C, s k δ ∈ C ∧ (s k δ)⁻¹ * (k * δ) ∈ K := by
    intro k hk δ hδ
    have h := hmem k hk δ hδ
    have e : s k δ = (h2 _ h).exists.choose := dif_pos h
    rw [e]
    exact (h2 _ h).exists.choose_spec
  have huniq : ∀ k ∈ K, ∀ δ ∈ C, ∀ γ ∈ C, γ⁻¹ * (k * δ) ∈ K → s k δ = γ := by
    intro k hk δ hδ γ hγ hγK
    exact (h2 _ (hmem k hk δ hδ)).unique (hs k hk δ hδ) ⟨hγ, hγK⟩
  have hinv : ∀ δ ∈ C, s k₀⁻¹ (s k₀ δ) = δ := by
    intro δ hδ
    obtain ⟨hm, hK⟩ := hs k₀ hk₀ δ hδ
    apply huniq _ (K.inv_mem hk₀) _ hm _ hδ
    have e : δ⁻¹ * (k₀⁻¹ * s k₀ δ) = ((s k₀ δ)⁻¹ * (k₀ * δ))⁻¹ := by group
    rw [e]
    exact K.inv_mem hK
  have hinv' : ∀ δ ∈ C, s k₀ (s k₀⁻¹ δ) = δ := by
    intro δ hδ
    obtain ⟨hm, hK⟩ := hs k₀⁻¹ (K.inv_mem hk₀) δ hδ
    apply huniq _ hk₀ _ hm _ hδ
    have e : δ⁻¹ * (k₀ * s k₀⁻¹ δ) = ((s k₀⁻¹ δ)⁻¹ * (k₀⁻¹ * δ))⁻¹ := by group
    rw [e]
    exact K.inv_mem hK
  refine Finset.sum_nbij' (s k₀) (s k₀⁻¹) (fun δ hδ => (hs k₀ hk₀ δ hδ).1)
    (fun δ hδ => (hs _ (K.inv_mem hk₀) δ hδ).1) hinv hinv' ?_
  intro δ hδ
  obtain ⟨_, hK⟩ := hs k₀ hk₀ δ hδ
  calc F (k₀ * δ) = F (s k₀ δ * ((s k₀ δ)⁻¹ * (k₀ * δ))) := by rw [mul_inv_cancel_left]
    _ = F (s k₀ δ) := hF _ _ hK

variable {D : D7}

theorem mt_mul (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul]

theorem mt_one (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [map_one, Units.val_one]

theorem mt_injective (V : HSp D) {a b : GA D V} (h : mt V a = mt V b) : a = b :=
  Subtype.val_injective (Units.ext h)

theorem suppF_mul {V : HSp D} {f : AE D} {a b : GA D V} (ha : SuppF V f a) (hb : SuppF V f b) :
    SuppF V f (a * b) := by
  intro i j
  have e : mt V (a * b) - 1 = (mt V a - 1) * mt V b + (mt V b - 1) := by
    rw [mt_mul, sub_mul, one_mul]; abel
  rw [e, Matrix.add_apply, Matrix.mul_apply, mul_add, Finset.mul_sum, hb i j]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_assoc, ha i l]

theorem suppF_inv {V : HSp D} {f : AE D} {a : GA D V} (ha : SuppF V f a) : SuppF V f a⁻¹ := by
  intro i j
  have e : mt V a⁻¹ - 1 = -(mt V a⁻¹ * (mt V a - 1)) := by
    rw [mul_sub, ← mt_mul, inv_mul_cancel, mt_one, mul_one]; abel
  rw [e, Matrix.neg_apply, Matrix.mul_apply, mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm, ha l j]

theorem suppF_one (V : HSp D) (f : AE D) : SuppF V f (1 : GA D V) := by
  intro i j
  simp [mt_one]

def suppSub (V : HSp D) (f : AE D) : Subgroup (GA D V) where
  carrier := {g | SuppF V f g}
  mul_mem' := suppF_mul
  one_mem' := suppF_one V f
  inv_mem' := suppF_inv

theorem comm_of_suppF_trivAt {V : HSp D} {f : AE D} {a b : GA D V} (ha : SuppF V f a) (hb : TrivAt V f b) :
    a * b = b * a := by
  apply mt_injective
  have hAB : (mt V a - 1) * (mt V b - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← ha i l, mul_assoc, mul_left_comm, hb l j, mul_zero]
  have hBA : (mt V b - 1) * (mt V a - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← ha l j, mul_left_comm, ← mul_assoc, hb i l, zero_mul]
  have e1 : mt V a * mt V b = (mt V a - 1) * (mt V b - 1) + mt V a + mt V b - 1 := by noncomm_ring
  have e2 : mt V b * mt V a = (mt V b - 1) * (mt V a - 1) + mt V b + mt V a - 1 := by noncomm_ring
  rw [mt_mul, mt_mul, e1, e2, hAB, hBA, zero_add, zero_add, add_comm (mt V a)]

theorem heckeOn_mem_wall : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}, LevProd R i → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → ∀ (α : GA D (Wc D i)), SuppF (Wc D i) f α → ∀ (C : Finset (GA D (Wc D i))), (∀ γ ∈ C, SuppF (Wc D i) f γ) → IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C → ∀ T ∈ R.Wall i (sg0 D A), heckeOn (R.MW i (sg0 D A)) C T ∈ R.Wall i (sg0 D A) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i hLP v f hf α _ C hC hrep Tm hT
  obtain ⟨hle, hchi, cmp, hcmp1, hcmp2⟩ := hLP
  have hT' : IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) Tm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hT
  refine (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).2
    (GlobalTheory.HeckeParts.isMultMap_heckeOn hT' (fun γ hγ => (hrep.1 γ hγ).1) ?_)
  intro w κ hκ g
  have hκ' : κ ∈ levW R i := hκ
  rw [hchi κ hκ', one_mul]
  show ∑ δ ∈ C, Tm w (g * κ * δ) = ∑ δ ∈ C, Tm w (g * δ)
  have hF : ∀ x, ∀ c ∈ levW R i, Tm w (x * c) = Tm w x := fun x c hc => by
    rw [hT'.lev w c hc x, hchi c hc, one_mul]
  obtain ⟨hs, ht⟩ := hcmp1 v f hf κ
  have hkv : cmp v κ ∈ levW R i := ((hcmp2 κ (hle hκ')).1.1 hκ') v
  have hk' : κ * (cmp v κ)⁻¹ ∈ levW R i := mul_mem hκ' (inv_mem hkv)
  calc ∑ δ ∈ C, Tm w (g * κ * δ) = ∑ δ ∈ C, Tm w (g * (κ * (cmp v κ)⁻¹) * (cmp v κ * δ)) :=
        Finset.sum_congr rfl fun δ _ => by group
    _ = ∑ δ ∈ C, Tm w (g * (κ * (cmp v κ)⁻¹) * δ) :=
        sum_mul_left_eq (levW R i ⊓ suppSub (Wc D i) f) α C (fun γ hγ => (hrep.1 γ hγ).2)
          (fun x hx => hrep.2 x hx) (fun x => Tm w (g * (κ * (cmp v κ)⁻¹) * x))
          (fun x c hc => by simp only [← mul_assoc]; exact hF _ c hc.1) (k₀ := cmp v κ) ⟨hkv, hs⟩
    _ = ∑ δ ∈ C, Tm w (g * δ) := Finset.sum_congr rfl fun δ hδ => by
        rw [mul_assoc, ← comm_of_suppF_trivAt (hC δ hδ) ht, ← mul_assoc, hF _ _ hk']

end GlobalTheory.LocalHeckeLevel

end
