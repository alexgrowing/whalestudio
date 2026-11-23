import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CmHalfIntegralGeneratorMemAlgebraicClosure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition

open Matrix Finset
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.Qx4

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section gen
variable {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)

lemma h_add_left (u u' v : Fin n → ℂ) : herm H (u + u') v = herm H u v + herm H u' v := B2x8.herm_add_left H u u' v
lemma h_add_right (u v v' : Fin n → ℂ) : herm H u (v + v') = herm H u v + herm H u v' := B2x8.herm_add_right H u v v'
lemma h_smul_left (c : ℂ) (u v : Fin n → ℂ) : herm H (c • u) v = c * herm H u v := B2x8.herm_smul_left H c u v
lemma h_smul_right (c : ℂ) (u v : Fin n → ℂ) : herm H u (c • v) = conj c * herm H u v := B2x8.herm_smul_right H c u v
lemma h_neg_left (u v : Fin n → ℂ) : herm H (-u) v = -herm H u v := B2x8.al_herm_neg_left H u v
lemma h_neg_right (u v : Fin n → ℂ) : herm H u (-v) = -herm H u v := B2x8.al_herm_neg_right H u v
lemma h_sub_left (u u' v : Fin n → ℂ) : herm H (u - u') v = herm H u v - herm H u' v := by
  rw [sub_eq_add_neg, h_add_left, h_neg_left, sub_eq_add_neg]
lemma h_sub_right (u v v' : Fin n → ℂ) : herm H u (v - v') = herm H u v - herm H u v' := by
  rw [sub_eq_add_neg, h_add_right, h_neg_right, sub_eq_add_neg]
lemma h_zero_left (u : Fin n → ℂ) : herm H 0 u = 0 := B2x8.al_herm_zero_left H u
lemma h_zero_right (u : Fin n → ℂ) : herm H u 0 = 0 := B2x8.al_herm_zero_right H u
lemma h_conj (hH : Hᴴ = H) (u v : Fin n → ℂ) : conj (herm H u v) = herm H v u := B2x8.herm_conj H hH u v

def hs (p v : Fin n → ℂ) (σ : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 - Matrix.vecMulVec p (fun j => herm H (bvec j) v) + Matrix.vecMulVec (v + σ • p) (fun j => herm H (bvec j) p)

lemma hs_act (p v u : Fin n → ℂ) (σ : ℂ) :
    hs H p v σ *ᵥ u = u - herm H u v • p + herm H u p • (v + σ • p) := by
  ext i
  simp only [hs, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  have h1 : ∀ (w φ : Fin n → ℂ), (Matrix.vecMulVec w φ *ᵥ u) i = (∑ j, φ j * u j) * w i := by
    intro w φ
    simp only [mulVec, dotProduct, vecMulVec_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [h1, h1, B2x6.herm_sum, B2x6.herm_sum]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

lemma hs_mem (hH : Hᴴ = H) {p v : Fin n → ℂ} {σ : ℂ} (hpp : herm H p p = 0) (hvp : herm H v p = 0)
    (hσ : σ + conj σ + herm H v v = 0) : hs H p v σ ∈ UH H := by
  apply B2x8.mem_UH_of
  intro u w
  have hpv : herm H p v = 0 := by rw [← h_conj H hH, hvp, map_zero]
  have h1 : herm H p w = conj (herm H w p) := (h_conj H hH w p).symm
  have h2 : herm H v w = conj (herm H w v) := (h_conj H hH w v).symm
  rw [hs_act, hs_act]
  simp only [h_add_left, h_add_right, h_sub_left, h_sub_right, h_smul_left, h_smul_right, hpp, hvp, hpv, h1, h2]
  linear_combination (herm H u p * conj (herm H w p)) * hσ

lemma mat_ext {A B : Matrix (Fin n) (Fin n) ℂ} (h : ∀ u, A *ᵥ u = B *ᵥ u) : A = B := B2x6.mat_ext h

end gen

variable {k r : ℕ}

local notation "⟪" u ", " v "⟫" => herm (Hpk k r) u v

lemma Hh : (Hpk k r)ᴴ = Hpk k r := B2x8.Hpk_herm k r

lemma herm_bvec_right (u : Fin (2 * r + k + 1) → ℂ) (j : Fin (2 * r + k + 1)) :
    ⟪u, bvec j⟫ = (Hpk k r *ᵥ u) j := by
  simp [herm, bvec, Pi.star_single]

lemma herm_e_right (u : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : ⟪u, bvec (eI k r a)⟫ = u (esI k r a) := by
  rw [herm_bvec_right, B2x6.hpk_mulVec]
  have h1 : WeylGroupFacts.tau k r (eI k r a) = esI k r a := by
    apply Fin.ext; rw [B2x6.tau_out _ (by simp only [eI]; omega)]; simp [eI, esI]
  have h2 : WeylGroupFacts.sgn k r (eI k r a) = 1 := by
    unfold WeylGroupFacts.sgn; rw [if_neg (by simp only [eI]; omega)]
  rw [h1, h2, one_mul]

lemma herm_es_right (u : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : ⟪u, bvec (esI k r a)⟫ = u (eI k r a) := by
  rw [herm_bvec_right, B2x6.hpk_mulVec]
  have h1 : WeylGroupFacts.tau k r (esI k r a) = eI k r a := by
    apply Fin.ext; rw [B2x6.tau_out _ (by simp only [esI]; omega)]; simp only [eI, esI]; omega
  have h2 : WeylGroupFacts.sgn k r (esI k r a) = 1 := by
    unfold WeylGroupFacts.sgn; rw [if_neg (by simp only [esI]; omega)]
  rw [h1, h2, one_mul]

lemma eI_ne_esI (a b : Fin r) : eI k r a ≠ esI k r b := by
  intro h; have := congrArg Fin.val h; simp only [eI, esI] at this; omega

lemma eI_inj {a b : Fin r} : eI k r a = eI k r b ↔ a = b := by
  constructor
  · intro h; have := congrArg Fin.val h; simp only [eI] at this; exact Fin.ext this
  · rintro rfl; rfl

lemma esI_inj {a b : Fin r} : esI k r a = esI k r b ↔ a = b := by
  constructor
  · intro h; have := congrArg Fin.val h; simp only [esI] at this; exact Fin.ext (by omega)
  · rintro rfl; rfl

lemma h_e_e (a b : Fin r) : ⟪bvec (eI k r a), bvec (eI k r b)⟫ = 0 := by
  rw [herm_e_right]; exact Pi.single_eq_of_ne (eI_ne_esI a b).symm _
lemma h_es_es (a b : Fin r) : ⟪bvec (esI k r a), bvec (esI k r b)⟫ = 0 := by
  rw [herm_es_right]; exact Pi.single_eq_of_ne (eI_ne_esI b a) _
lemma h_e_es (a b : Fin r) : ⟪bvec (eI k r a), bvec (esI k r b)⟫ = if a = b then 1 else 0 := by
  rw [herm_es_right]; simp only [bvec, Pi.single_apply, eI_inj]
  by_cases h : a = b
  · simp [h]
  · rw [if_neg h, if_neg (Ne.symm h)]
lemma h_es_e (a b : Fin r) : ⟪bvec (esI k r a), bvec (eI k r b)⟫ = if a = b then 1 else 0 := by
  rw [herm_e_right]; simp only [bvec, Pi.single_apply, esI_inj]
  by_cases h : a = b
  · simp [h]
  · rw [if_neg h, if_neg (Ne.symm h)]

lemma uh_one : (1 : Mx k r) ∈ UH (Hpk k r) := B2x8.al_one_mem k r
lemma uh_mul {g h : Mx k r} (hg : g ∈ UH (Hpk k r)) (hh : h ∈ UH (Hpk k r)) : g * h ∈ UH (Hpk k r) :=
  B2x8.al_mul_mem hg hh
lemma uh_inv {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ ∈ UH (Hpk k r) := B2x8.al_inv_mem hg
lemma uh_unit {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : IsUnit g.det := B2x8.al_unit hg
lemma uh_herm {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (u v : Fin (2 * r + k + 1) → ℂ) : ⟪g *ᵥ u, g *ᵥ v⟫ = ⟪u, v⟫ :=
  B2x8.herm_UH _ hg u v
lemma uh_mul_inv {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ (uh_unit hg)
lemma uh_inv_mul {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul _ (uh_unit hg)
lemma uh_inv_fix {g : Mx k r} (hg : g ∈ UH (Hpk k r)) {v w : Fin (2 * r + k + 1) → ℂ} (h : g *ᵥ v = w) : g⁻¹ *ᵥ w = v :=
  B2x8.al_inv_mulVec (uh_unit hg) h
lemma uh_herm_inv {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (u v : Fin (2 * r + k + 1) → ℂ) : ⟪g *ᵥ u, v⟫ = ⟪u, g⁻¹ *ᵥ v⟫ := by
  rw [← uh_herm hg u (g⁻¹ *ᵥ v), Matrix.mulVec_mulVec, uh_mul_inv hg, Matrix.one_mulVec]

lemma glev_one (i : Fin (r + 1)) : (1 : Mx k r) ∈ Glev k r i :=
  ⟨uh_one, fun a _ => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩⟩
lemma glev_mul {i : Fin (r + 1)} {g h : Mx k r} (hg : g ∈ Glev k r i) (hh : h ∈ Glev k r i) : g * h ∈ Glev k r i :=
  ⟨uh_mul hg.1 hh.1, fun a ha => ⟨by rw [← Matrix.mulVec_mulVec, (hh.2 a ha).1, (hg.2 a ha).1],
    by rw [← Matrix.mulVec_mulVec, (hh.2 a ha).2, (hg.2 a ha).2]⟩⟩
lemma glev_inv {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) : g⁻¹ ∈ Glev k r i :=
  ⟨uh_inv hg.1, fun a ha => ⟨uh_inv_fix hg.1 (hg.2 a ha).1, uh_inv_fix hg.1 (hg.2 a ha).2⟩⟩

lemma glev_succ_iff (l : Fin r) (g : Mx k r) : g ∈ Glev k r l.succ ↔
    g ∈ Glev k r l.castSucc ∧ g *ᵥ bvec (eI k r l) = bvec (eI k r l) ∧ g *ᵥ bvec (esI k r l) = bvec (esI k r l) := by
  constructor
  · intro hg
    refine ⟨⟨hg.1, fun a ha => hg.2 a ?_⟩, (hg.2 l ?_).1, (hg.2 l ?_).2⟩
    · simp only [Fin.val_castSucc, Fin.val_succ] at *; omega
    · simp only [Fin.val_succ]; omega
    · simp only [Fin.val_succ]; omega
  · rintro ⟨hg, h1, h2⟩
    refine ⟨hg.1, fun a ha => ?_⟩
    by_cases h : a = l
    · subst h; exact ⟨h1, h2⟩
    · apply hg.2 a
      have : a.val ≠ l.val := fun h' => h (Fin.ext h')
      simp only [Fin.val_castSucc, Fin.val_succ] at *; omega

lemma uw_glev {z : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z) (i : Fin (r + 1)) : h ∈ Glev k r i :=
  ⟨hh.1, fun a _ => hh.2.1 a⟩

variable {l : Fin r}

local notation "𝐞" => bvec (eI k r l)
local notation "𝐬" => bvec (esI k r l)

def UP (k r : ℕ) (l : Fin r) : Set (Mx k r) :=
  {u | u ∈ Glev k r l.castSucc ∧ u *ᵥ bvec (eI k r l) = bvec (eI k r l) ∧
    ∀ y, herm (Hpk k r) y (bvec (eI k r l)) = 0 → ∃ t : ℂ, u *ᵥ y = y + t • bvec (eI k r l)}

lemma up_one : (1 : Mx k r) ∈ UP k r l :=
  ⟨glev_one _, Matrix.one_mulVec _, fun y _ => ⟨0, by simp⟩⟩

lemma up_mul {u u' : Mx k r} (hu : u ∈ UP k r l) (hu' : u' ∈ UP k r l) : u * u' ∈ UP k r l := by
  refine ⟨glev_mul hu.1 hu'.1, by rw [← Matrix.mulVec_mulVec, hu'.2.1, hu.2.1], fun y hy => ?_⟩
  obtain ⟨t', ht'⟩ := hu'.2.2 y hy
  obtain ⟨t, ht⟩ := hu.2.2 y hy
  refine ⟨t + t', ?_⟩
  rw [← Matrix.mulVec_mulVec, ht', Matrix.mulVec_add, Matrix.mulVec_smul, hu.2.1, ht, add_smul]
  exact add_assoc _ _ _

lemma up_inv {u : Mx k r} (hu : u ∈ UP k r l) : u⁻¹ ∈ UP k r l := by
  refine ⟨glev_inv hu.1, uh_inv_fix hu.1.1 hu.2.1, fun y hy => ?_⟩
  obtain ⟨t, ht⟩ := hu.2.2 y hy
  refine ⟨-t, uh_inv_fix hu.1.1 ?_⟩
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, hu.2.1, ht, neg_smul, add_neg_cancel_right]

lemma up_conj {u p : Mx k r} (hu : u ∈ UP k r l) (hp : p ∈ Glev k r l.succ) : p * u * p⁻¹ ∈ UP k r l := by
  obtain ⟨hp0, hp1, -⟩ := (glev_succ_iff l p).1 hp
  have hpi : p⁻¹ *ᵥ 𝐞 = 𝐞 := uh_inv_fix hp0.1 hp1
  refine ⟨glev_mul (glev_mul hp0 hu.1) (glev_inv hp0), ?_, fun y hy => ?_⟩
  · rw [← Matrix.mulVec_mulVec, hpi, ← Matrix.mulVec_mulVec, hu.2.1, hp1]
  · have h1 : ⟪p⁻¹ *ᵥ y, 𝐞⟫ = 0 := by
      rw [← hpi, uh_herm (uh_inv hp0.1), hy]
    obtain ⟨t, ht⟩ := hu.2.2 _ h1
    refine ⟨t, ?_⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ht, Matrix.mulVec_add, Matrix.mulVec_smul, hp1,
      Matrix.mulVec_mulVec, uh_mul_inv hp0.1, Matrix.one_mulVec]

lemma up_conj' {u p : Mx k r} (hu : u ∈ UP k r l) (hp : p ∈ Glev k r l.succ) : p⁻¹ * u * p ∈ UP k r l := by
  have := up_conj hu (glev_inv hp)
  rwa [Matrix.nonsing_inv_nonsing_inv _ (uh_unit hp.1)] at this

lemma up_nset {u : Mx k r} (hu : u ∈ UP k r l) : u ∈ Nset k r := by
  rw [WeylGroupFacts.nset_iff]
  refine ⟨hu.1.1, fun i j hj hi => ?_⟩
  rw [B2x6.ent u i j]
  have hl := l.isLt
  by_cases hjl : j.val < l.val
  · have e : eI k r ⟨j.val, by omega⟩ = j := Fin.ext rfl
    have := (hu.1.2 ⟨j.val, by omega⟩ (by simpa using hjl)).1
    rw [e] at this
    rw [this]; simp only [bvec, Pi.single_apply]
  · by_cases hjl' : j.val = l.val
    · have e : eI k r l = j := Fin.ext hjl'.symm
      rw [← e, hu.2.1]; simp only [bvec, Pi.single_apply]
    · have h0 : ⟪bvec j, 𝐞⟫ = 0 := by
        rw [herm_e_right]
        apply Pi.single_eq_of_ne
        intro h; have := congrArg Fin.val h; simp only [esI] at this; omega
      obtain ⟨t, ht⟩ := hu.2.2 _ h0
      rw [ht]
      have : (bvec (eI k r l) : Fin (2 * r + k + 1) → ℂ) i = 0 := by
        apply Pi.single_eq_of_ne
        intro h; have := congrArg Fin.val h; simp only [eI] at this; omega
      rw [Pi.add_apply, Pi.smul_apply, this, smul_zero, add_zero]; simp only [bvec, Pi.single_apply]

lemma up_nlev {u : Mx k r} (hu : u ∈ UP k r l) : u ∈ Nlev k r l.castSucc := ⟨up_nset hu, hu.1⟩

def IsX (k r : ℕ) (l : Fin r) (x : Fin (2 * r + k + 1) → ℂ) : Prop :=
  herm (Hpk k r) x (bvec (eI k r l)) = 1 ∧ herm (Hpk k r) x x = 0 ∧
    ∀ a : Fin r, a.val < l.val → herm (Hpk k r) (bvec (eI k r a)) x = 0 ∧ herm (Hpk k r) (bvec (esI k r a)) x = 0

lemma hs_glev {i : Fin (r + 1)} {p v : Fin (2 * r + k + 1) → ℂ} {σ : ℂ} (hpp : ⟪p, p⟫ = 0) (hvp : ⟪v, p⟫ = 0)
    (hσ : σ + conj σ + ⟪v, v⟫ = 0)
    (hp : ∀ a : Fin r, a.val < i.val → ⟪bvec (eI k r a), p⟫ = 0 ∧ ⟪bvec (esI k r a), p⟫ = 0)
    (hv : ∀ a : Fin r, a.val < i.val → ⟪bvec (eI k r a), v⟫ = 0 ∧ ⟪bvec (esI k r a), v⟫ = 0) :
    hs (Hpk k r) p v σ ∈ Glev k r i := by
  refine ⟨hs_mem _ Hh hpp hvp hσ, fun a ha => ⟨?_, ?_⟩⟩
  · rw [hs_act, (hp a ha).1, (hv a ha).1]; simp
  · rw [hs_act, (hp a ha).2, (hv a ha).2]; simp

def hx (k r : ℕ) (l : Fin r) (x : Fin (2 * r + k + 1) → ℂ) : Mx k r :=
  hs (Hpk k r) (bvec (eI k r l))
    (x - bvec (esI k r l) - herm (Hpk k r) x (bvec (esI k r l)) • bvec (eI k r l)) (herm (Hpk k r) x (bvec (esI k r l)))

lemma ne_of_val_lt {a : Fin r} (h : a.val < l.val) : a ≠ l := fun h' => by rw [h'] at h; exact lt_irrefl _ h

lemma hx_up {x : Fin (2 * r + k + 1) → ℂ} (hx' : IsX k r l x) : hx k r l x ∈ UP k r l := by
  obtain ⟨h1, h2, h3⟩ := hx'
  have h1' : ⟪𝐞, x⟫ = 1 := by rw [← h_conj _ Hh, h1, map_one]
  have h4 : ⟪𝐬, x⟫ = conj ⟪x, 𝐬⟫ := (h_conj _ Hh _ _).symm
  have hvp : ⟪x - 𝐬 - ⟪x, 𝐬⟫ • 𝐞, 𝐞⟫ = 0 := by
    simp only [h_sub_left, h_smul_left, h1, h_es_e, h_e_e, if_true]; ring
  refine ⟨hs_glev (h_e_e l l) hvp ?_ ?_ ?_, ?_, fun y hy => ?_⟩
  · simp only [h_sub_left, h_sub_right, h_smul_left, h_smul_right, h1, h1', h2, h4, h_es_e, h_e_e, h_e_es, h_es_es, if_true]
    ring
  · intro a ha
    exact ⟨h_e_e a l, by rw [h_es_e, if_neg (ne_of_val_lt ha)]⟩
  · intro a ha
    simp only [h_sub_right, h_smul_right, (h3 a ha).1, (h3 a ha).2, h_e_e, h_es_es, h_e_es, h_es_e,
      if_neg (ne_of_val_lt ha)]
    constructor <;> ring
  · unfold hx; rw [hs_act, h_e_e]
    have : ⟪𝐞, x - 𝐬 - ⟪x, 𝐬⟫ • 𝐞⟫ = 0 := by rw [← h_conj _ Hh, hvp, map_zero]
    rw [this]; simp
  · unfold hx; rw [hs_act, hy]
    exact ⟨-⟪y, x - 𝐬 - ⟪x, 𝐬⟫ • 𝐞⟫, by simp [sub_eq_add_neg]⟩

lemma hx_es {x : Fin (2 * r + k + 1) → ℂ} (hx' : IsX k r l x) : hx k r l x *ᵥ 𝐬 = x := by
  obtain ⟨h1, h2, h3⟩ := hx'
  have h4 : ⟪𝐬, x⟫ = conj ⟪x, 𝐬⟫ := (h_conj _ Hh _ _).symm
  unfold hx; rw [hs_act]
  have : ⟪𝐬, x - 𝐬 - ⟪x, 𝐬⟫ • 𝐞⟫ = 0 := by
    simp only [h_sub_right, h_smul_right, h4, h_es_es, h_es_e, if_true]; ring
  rw [this, h_es_e, if_pos rfl]
  simp

lemma isX_of_glev {g : Mx k r} (hg : g ∈ Glev k r l.castSucc) (he : g *ᵥ 𝐞 = 𝐞) : IsX k r l (g *ᵥ 𝐬) := by
  refine ⟨?_, ?_, fun a ha => ⟨?_, ?_⟩⟩
  · conv_lhs => rw [← he]
    rw [uh_herm hg.1, h_es_e, if_pos rfl]
  · rw [uh_herm hg.1, h_es_es]
  · conv_lhs => rw [← (hg.2 a (by simpa using ha)).1]
    rw [uh_herm hg.1, h_e_es, if_neg (ne_of_val_lt ha)]
  · conv_lhs => rw [← (hg.2 a (by simpa using ha)).2]
    rw [uh_herm hg.1, h_es_es]

lemma up_unique {u u' : Mx k r} (hu : u ∈ UP k r l) (hu' : u' ∈ UP k r l) (h : u *ᵥ 𝐬 = u' *ᵥ 𝐬) : u = u' := by
  apply mat_ext
  intro y
  have hy0 : ⟪y - ⟪y, 𝐞⟫ • 𝐬, 𝐞⟫ = 0 := by
    simp only [h_sub_left, h_smul_left, h_es_e, if_true]; ring
  obtain ⟨t, ht⟩ := hu.2.2 _ hy0
  obtain ⟨t', ht'⟩ := hu'.2.2 _ hy0
  have e1 := uh_herm hu.1.1 (y - ⟪y, 𝐞⟫ • 𝐬) 𝐬
  have e2 := uh_herm hu'.1.1 (y - ⟪y, 𝐞⟫ • 𝐬) 𝐬
  have e3 : ⟪𝐞, u' *ᵥ 𝐬⟫ = 1 := by
    conv_lhs => rw [← hu'.2.1]
    rw [uh_herm hu'.1.1, h_e_es, if_pos rfl]
  rw [ht, h, h_add_left, h_smul_left, e3] at e1
  rw [ht', h_add_left, h_smul_left, e3] at e2
  have htt : t = t' := by linear_combination e1 - e2
  have hy : y = (y - ⟪y, 𝐞⟫ • 𝐬) + ⟪y, 𝐞⟫ • 𝐬 := by simp
  rw [hy, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, ht, ht', h, htt]

lemma up_hx {u : Mx k r} (hu : u ∈ UP k r l) : hx k r l (u *ᵥ 𝐬) = u :=
  up_unique (hx_up (isX_of_glev hu.1 hu.2.1)) hu (hx_es (isX_of_glev hu.1 hu.2.1))

lemma stab_dec {g : Mx k r} (hg : g ∈ Glev k r l.castSucc) (he : g *ᵥ 𝐞 = 𝐞) :
    ∃ u ∈ UP k r l, ∃ g₁ ∈ Glev k r l.succ, g = u * g₁ := by
  have hX := isX_of_glev hg he
  have hu := hx_up hX
  refine ⟨hx k r l (g *ᵥ 𝐬), hu, (hx k r l (g *ᵥ 𝐬))⁻¹ * g, ?_, ?_⟩
  · rw [glev_succ_iff]
    refine ⟨glev_mul (glev_inv hu.1) hg, ?_, ?_⟩
    · rw [← Matrix.mulVec_mulVec, he]; exact uh_inv_fix hu.1.1 hu.2.1
    · rw [← Matrix.mulVec_mulVec]; exact uh_inv_fix hu.1.1 (hx_es hX)
  · rw [← Matrix.mul_assoc, uh_mul_inv hu.1.1, Matrix.one_mul]

lemma stab_dec' {g : Mx k r} (hg : g ∈ Glev k r l.castSucc) (he : g *ᵥ 𝐞 = 𝐞) :
    ∃ u ∈ UP k r l, ∃ g₁ ∈ Glev k r l.succ, g = g₁ * u := by
  obtain ⟨u, hu, g₁, hg₁, h⟩ := stab_dec (glev_inv hg) (uh_inv_fix hg.1 he)
  refine ⟨u⁻¹, up_inv hu, g₁⁻¹, glev_inv hg₁, ?_⟩
  rw [← Matrix.mul_inv_rev, ← h, Matrix.nonsing_inv_nonsing_inv _ (uh_unit hg.1)]

lemma weyl_cell_apply_dual_basis (c : ℂ) (q : Fin (2 * r + k + 1)) :
    w1 k r l c (esI k r l) q = if q = eI k r l then c else 0 := by
  unfold w1
  by_cases h : q = eI k r l
  · simp [h]
  · simp [h, (eI_ne_esI l l).symm]

lemma weyl_cell_apply_basis (c : ℂ) (q : Fin (2 * r + k + 1)) :
    w1 k r l c (eI k r l) q = if q = esI k r l then (star c)⁻¹ else 0 := by
  unfold w1
  by_cases h : q = esI k r l
  · simp [h, eI_ne_esI l l]
  · simp [h, eI_ne_esI l l]

lemma weyl_cell_apply_other (c : ℂ) {p : Fin (2 * r + k + 1)} (h1 : p ≠ eI k r l) (h2 : p ≠ esI k r l)
    (q : Fin (2 * r + k + 1)) : w1 k r l c p q = if q = p then 1 else 0 := by
  unfold w1
  by_cases h : q = p
  · simp [h, h1, h2]
  · simp [h1, h2, h, Ne.symm h]

lemma weyl_cell_mulVec (c : ℂ) (y : Fin (2 * r + k + 1) → ℂ) :
    w1 k r l c *ᵥ y = y + (c * ⟪y, 𝐬⟫ - ⟪y, 𝐞⟫) • 𝐬 + ((conj c)⁻¹ * ⟪y, 𝐞⟫ - ⟪y, 𝐬⟫) • 𝐞 := by
  ext p
  rw [herm_e_right, herm_es_right]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply, mulVec, dotProduct]
  by_cases h2 : p = esI k r l
  · subst h2
    simp only [weyl_cell_apply_dual_basis, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, (eI_ne_esI l l).symm, if_false]
    ring
  · by_cases h1 : p = eI k r l
    · subst h1
      simp only [weyl_cell_apply_basis, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, eI_ne_esI l l, if_false]
      rw [Complex.star_def]; ring
    · simp only [weyl_cell_apply_other c h1 h2, ite_mul, zero_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, h1, h2,
        if_false]
      ring

lemma w1_mulVec_bvec_eI (c : ℂ) : w1 k r l c *ᵥ 𝐞 = c • 𝐬 := by
  rw [weyl_cell_mulVec, h_e_e, h_e_es, if_pos rfl]
  simp

lemma w1_mulVec_bvec_esI (c : ℂ) : w1 k r l c *ᵥ 𝐬 = (conj c)⁻¹ • 𝐞 := by
  rw [weyl_cell_mulVec, h_es_e, h_es_es, if_pos rfl]
  simp

lemma weyl_cell_mem_level_group {c : ℂ} (hc : c ≠ 0) : w1 k r l c ∈ Glev k r l.castSucc := by
  have hc' : conj c ≠ 0 := (map_ne_zero _).2 hc
  refine ⟨?_, fun a ha => ?_⟩
  · apply B2x8.mem_UH_of
    intro u w
    have h1 : ⟪𝐞, w⟫ = conj ⟪w, 𝐞⟫ := (h_conj _ Hh _ _).symm
    have h2 : ⟪𝐬, w⟫ = conj ⟪w, 𝐬⟫ := (h_conj _ Hh _ _).symm
    rw [weyl_cell_mulVec, weyl_cell_mulVec]
    simp only [h_add_left, h_add_right, h_smul_left, h_smul_right, h_e_e, h_es_es, h_e_es, h_es_e, if_true, h1, h2,
      map_sub, map_mul, map_inv₀, Complex.conj_conj]
    field_simp
    ring
  · have hne : a ≠ l := ne_of_val_lt (by simpa using ha)
    constructor
    · rw [weyl_cell_mulVec, h_e_e, h_e_es, if_neg hne]; simp
    · rw [weyl_cell_mulVec, h_es_e, h_es_es, if_neg hne]; simp

lemma w1_commute_of_mem_Glev (c : ℂ) {g : Mx k r} (hg : g ∈ Glev k r l.succ) : w1 k r l c * g = g * w1 k r l c := by
  obtain ⟨hg0, h1, h2⟩ := (glev_succ_iff l g).1 hg
  apply mat_ext
  intro y
  have e1 : ⟪g *ᵥ y, 𝐞⟫ = ⟪y, 𝐞⟫ := by
    conv_lhs => rw [← h1]
    exact uh_herm hg0.1 _ _
  have e2 : ⟪g *ᵥ y, 𝐬⟫ = ⟪y, 𝐬⟫ := by
    conv_lhs => rw [← h2]
    exact uh_herm hg0.1 _ _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, weyl_cell_mulVec, weyl_cell_mulVec, e1, e2, Matrix.mulVec_add, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul, h1, h2]

lemma weyl_cell_mul_conj {c : ℂ} (hc : c ≠ 0) : w1 k r l c * w1 k r l (conj c) = 1 := by
  have hc' : conj c ≠ 0 := (map_ne_zero _).2 hc
  apply mat_ext
  intro y
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec, weyl_cell_mulVec (conj c), Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul, w1_mulVec_bvec_eI, w1_mulVec_bvec_esI, weyl_cell_mulVec, Complex.conj_conj]
  ext p
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

lemma weyl_cell_inv {c : ℂ} (hc : c ≠ 0) : (w1 k r l c)⁻¹ = w1 k r l (conj c) :=
  Matrix.inv_eq_right_inv (weyl_cell_mul_conj hc)

structure Dec (k r : ℕ) (l : Fin r) (g : Mx k r) (c : ℂ) (u g₁ u' : Mx k r) : Prop where
  hc : c ≠ 0
  hu : u ∈ UP k r l
  hg : g₁ ∈ Glev k r l.succ
  hu' : u' ∈ UP k r l
  eq : g = u * (w1 k r l c * g₁) * u'

lemma glev_succ_le {g : Mx k r} (hg : g ∈ Glev k r l.succ) : g ∈ Glev k r l.castSucc := ((glev_succ_iff l g).1 hg).1

lemma Dec.mem {g u g₁ u' : Mx k r} {c : ℂ} (h : Dec k r l g c u g₁ u') : g ∈ Glev k r l.castSucc := by
  rw [h.eq]
  exact glev_mul (glev_mul h.hu.1 (glev_mul (weyl_cell_mem_level_group h.hc) (glev_succ_le h.hg))) h.hu'.1

lemma dec_exists {g : Mx k r} (hg : g ∈ Glev k r l.castSucc) (hc : ⟪g *ᵥ 𝐞, 𝐞⟫ ≠ 0) :
    ∃ u g₁ u', Dec k r l g ⟪g *ᵥ 𝐞, 𝐞⟫ u g₁ u' := by
  set c := ⟪g *ᵥ 𝐞, 𝐞⟫ with hcdef
  have hc' : conj c ≠ 0 := (map_ne_zero _).2 hc
  have hX : IsX k r l (c⁻¹ • (g *ᵥ 𝐞)) := by
    refine ⟨?_, ?_, fun a ha => ⟨?_, ?_⟩⟩
    · rw [h_smul_left, ← hcdef, inv_mul_cancel₀ hc]
    · rw [h_smul_left, h_smul_right, uh_herm hg.1, h_e_e]; simp
    · rw [h_smul_right]
      conv_lhs => rw [← (hg.2 a (by simpa using ha)).1]
      rw [uh_herm hg.1, h_e_e, mul_zero]
    · rw [h_smul_right]
      conv_lhs => rw [← (hg.2 a (by simpa using ha)).2]
      rw [uh_herm hg.1, h_es_e, if_neg (ne_of_val_lt ha), mul_zero]
  have hu := hx_up hX
  set u := hx k r l (c⁻¹ • (g *ᵥ 𝐞)) with hudef
  have hues : u *ᵥ 𝐬 = c⁻¹ • (g *ᵥ 𝐞) := hx_es hX
  have hw := weyl_cell_mem_level_group (k := k) (r := r) (l := l) hc
  have hg' : (w1 k r l c)⁻¹ * (u⁻¹ * g) ∈ Glev k r l.castSucc := glev_mul (glev_inv hw) (glev_mul (glev_inv hu.1) hg)
  have he' : ((w1 k r l c)⁻¹ * (u⁻¹ * g)) *ᵥ 𝐞 = 𝐞 := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    apply uh_inv_fix hw.1
    symm
    apply uh_inv_fix hu.1.1
    rw [w1_mulVec_bvec_eI, Matrix.mulVec_smul, hues, smul_smul, mul_inv_cancel₀ hc, one_smul]
  obtain ⟨u', hu', g₁, hg₁, h⟩ := stab_dec' hg' he'
  refine ⟨u, g₁, u', hc, hu, hg₁, hu', ?_⟩
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← h, ← Matrix.mul_assoc (w1 k r l c), uh_mul_inv hw.1, Matrix.one_mul,
    ← Matrix.mul_assoc, uh_mul_inv hu.1.1, Matrix.one_mul]

theorem cellDecomp : CellDecomp := by
  intro k r l g hg
  obtain ⟨u, g₁, u', h⟩ := dec_exists hg.1 hg.2
  exact ⟨u, up_nlev h.hu, u', up_nlev h.hu', g₁, h.hg, h.eq⟩

lemma hs_poly (p v₀ : Fin (2 * r + k + 1) → ℂ) (κ : ℂ) (t : ℝ) :
    hs (Hpk k r) p ((t : ℂ) • v₀) ((t : ℂ) ^ 2 * κ) =
      1 + (t : ℂ) • (Matrix.vecMulVec v₀ (fun j => ⟪bvec j, p⟫) - Matrix.vecMulVec p (fun j => ⟪bvec j, v₀⟫)) +
        ((t : ℂ) ^ 2 * κ) • Matrix.vecMulVec p (fun j => ⟪bvec j, p⟫) := by
  ext i j
  simp only [hs, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, h_smul_right, Complex.conj_ofReal,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma zero_mem_closure_poly {A B : ℂ} (h : A ≠ 0 ∨ B ≠ 0) :
    (0 : ℝ) ∈ closure {t : ℝ | (t : ℂ) * (A + t * B) ≠ 0} := by
  have hs : ({t : ℝ | (t : ℂ) * (A + t * B) ≠ 0}ᶜ).Countable := by
    apply Set.Countable.mono (s₂ := {0, (-A / B).re})
    · intro t ht
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not, mul_eq_zero] at ht
      rcases ht with ht | ht
      · left; exact_mod_cast ht
      · right
        have hB : B ≠ 0 := by
          intro hB
          rw [hB, mul_zero, add_zero] at ht
          rcases h with h | h
          · exact h ht
          · exact h hB
        have h2 : (t : ℂ) = -A / B := by
          field_simp
          linear_combination ht
        simp [← h2]
    · exact (Set.toFinite _).countable
  have h2 := hs.dense_compl ℝ
  rw [compl_compl] at h2
  exact h2 0

lemma herm_H_bvec (y : Fin (2 * r + k + 1) → ℂ) (j : Fin (2 * r + k + 1)) : ⟪Hpk k r *ᵥ y, bvec j⟫ = y j := by
  rw [herm_bvec_right, Matrix.mulVec_mulVec, B2x8.Hpk_sq, Matrix.one_mulVec]

open scoped ComplexOrder in
theorem cellDense : CellDense := by
  intro k r l g hg
  by_cases hc : herm (Hpk k r) (g *ᵥ bvec (eI k r l)) (bvec (eI k r l)) = 0
  swap
  · exact subset_closure ⟨hg, hc⟩
  set x := g⁻¹ *ᵥ bvec (eI k r l) with hx
  set α := herm (Hpk k r) x (bvec (esI k r l)) with hα
  set x₀ := x - α • bvec (eI k r l) with hx₀
  set v₀ := Hpk k r *ᵥ x₀ with hv₀
  set q := herm (Hpk k r) v₀ v₀ with hq
  set κ := Complex.I - q / 2 with hκ
  have hex : herm (Hpk k r) (bvec (eI k r l)) x = 0 := by rw [hx, ← uh_herm_inv hg.1, hc]
  have hxe : herm (Hpk k r) x (bvec (eI k r l)) = 0 := by rw [← h_conj _ Hh, hex, map_zero]
  have hve : herm (Hpk k r) v₀ (bvec (eI k r l)) = 0 := by
    rw [hv₀, herm_H_bvec, ← herm_es_right x₀ l, hx₀, h_sub_left, h_smul_left, h_e_es, if_pos rfl, ← hα]; ring
  have hvs : herm (Hpk k r) v₀ (bvec (esI k r l)) = 0 := by
    rw [hv₀, herm_H_bvec, ← herm_e_right x₀ l, hx₀, h_sub_left, h_smul_left, h_e_e, hxe]; ring
  have hev : herm (Hpk k r) (bvec (eI k r l)) v₀ = 0 := by rw [← h_conj _ Hh, hve, map_zero]
  have hva : ∀ a : Fin r, a.val < (l.castSucc).val →
      herm (Hpk k r) (bvec (eI k r a)) v₀ = 0 ∧ herm (Hpk k r) (bvec (esI k r a)) v₀ = 0 := by
    intro a ha
    have hne : a ≠ l := ne_of_val_lt (by simpa using ha)
    have hgi := glev_inv hg
    constructor
    · rw [← h_conj _ Hh, hv₀, herm_H_bvec, ← herm_es_right x₀ a, hx₀, h_sub_left, h_smul_left, h_e_es, if_neg (Ne.symm hne), hx]
      conv_lhs => rw [← (hgi.2 a ha).2]
      rw [uh_herm hgi.1, h_e_es, if_neg (Ne.symm hne)]; simp
    · rw [← h_conj _ Hh, hv₀, herm_H_bvec, ← herm_e_right x₀ a, hx₀, h_sub_left, h_smul_left, h_e_e, hx]
      conv_lhs => rw [← (hgi.2 a ha).1]
      rw [uh_herm hgi.1, h_e_e]; simp
  have hqc : conj q = q := h_conj _ Hh _ _
  have hκ0 : κ ≠ 0 := by
    intro h
    have h1 := congrArg Complex.im h
    have h2 : q.im = 0 := B2x8.herm_self_im k r v₀
    simp [hκ, h2] at h1
  set A := herm (Hpk k r) v₀ x with hA
  set B := κ * conj α with hB
  have hAB : A ≠ 0 ∨ B ≠ 0 := by
    by_cases h0 : x₀ = 0
    · right
      have hα0 : α ≠ 0 := by
        intro h
        have hx0 : x = 0 := by
          have : x = x₀ + α • bvec (eI k r l) := by rw [hx₀]; simp
          rw [this, h0, h]; simp
        have h1 : g *ᵥ x = bvec (eI k r l) := by
          rw [hx, Matrix.mulVec_mulVec, uh_mul_inv hg.1, Matrix.one_mulVec]
        rw [hx0, Matrix.mulVec_zero] at h1
        have h2 := congrFun h1 (eI k r l)
        simp [bvec] at h2
      exact mul_ne_zero hκ0 ((map_ne_zero _).2 hα0)
    · left
      have h1 : A = star x₀ ⬝ᵥ x₀ := by
        have : x = x₀ + α • bvec (eI k r l) := by rw [hx₀]; simp
        rw [hA, this, h_add_right, h_smul_right, hve, mul_zero, add_zero, hv₀]
        unfold herm
        rw [Matrix.mulVec_mulVec, B2x8.Hpk_sq, Matrix.one_mulVec]
      rw [h1]
      intro h2
      exact h0 (dotProduct_star_self_eq_zero.mp h2)
  let γ : ℝ → Mx k r := fun t => g * hs (Hpk k r) (bvec (esI k r l)) ((t : ℂ) • v₀) ((t : ℂ) ^ 2 * κ)
  have hγc : Continuous γ := by
    have : γ = fun t : ℝ => g * (1 + (t : ℂ) • (Matrix.vecMulVec v₀ (fun j => herm (Hpk k r) (bvec j) (bvec (esI k r l))) -
        Matrix.vecMulVec (bvec (esI k r l)) (fun j => herm (Hpk k r) (bvec j) v₀)) +
        ((t : ℂ) ^ 2 * κ) • Matrix.vecMulVec (bvec (esI k r l)) (fun j => herm (Hpk k r) (bvec j) (bvec (esI k r l)))) := by
      funext t; simp only [γ]; rw [hs_poly]
    rw [this]
    fun_prop
  have hγ0 : γ 0 = g := by
    simp only [γ]; rw [hs_poly]; simp
  rw [← hγ0]
  refine map_mem_closure hγc (zero_mem_closure_poly hAB) ?_
  intro t ht
  have hk : hs (Hpk k r) (bvec (esI k r l)) ((t : ℂ) • v₀) ((t : ℂ) ^ 2 * κ) ∈ Glev k r l.castSucc := by
    apply hs_glev (h_es_es l l)
    · rw [h_smul_left, hvs, mul_zero]
    · rw [h_smul_left, h_smul_right, ← hq, map_mul, map_pow, Complex.conj_ofReal, hκ, map_sub, map_div₀, hqc,
        Complex.conj_I]
      simp only [map_ofNat]
      ring
    · intro a ha
      have hne : a ≠ l := ne_of_val_lt (by simpa using ha)
      exact ⟨by rw [h_e_es, if_neg hne], h_es_es a l⟩
    · intro a ha
      rw [h_smul_right, h_smul_right, (hva a ha).1, (hva a ha).2]
      simp
  refine ⟨glev_mul hg hk, ?_⟩
  show herm (Hpk k r) (γ t *ᵥ bvec (eI k r l)) (bvec (eI k r l)) ≠ 0
  have : herm (Hpk k r) (γ t *ᵥ bvec (eI k r l)) (bvec (eI k r l)) = (t : ℂ) * (A + t * B) := by
    simp only [γ]
    rw [← Matrix.mulVec_mulVec, uh_herm_inv hg.1, ← hx, hs_act, h_smul_right, hev, h_e_es, if_pos rfl]
    simp only [h_add_left, h_sub_left, h_smul_left, hex, ← hA]
    rw [← h_conj _ Hh x, ← hα, hB]
    ring
  rw [this]
  exact ht

def cF (k r : ℕ) (l : Fin r) (g : Mx k r) : ℂ := herm (Hpk k r) (g *ᵥ bvec (eI k r l)) (bvec (eI k r l))

def iH (g : Mx k r) : Mx k r := Hpk k r * gᴴ * Hpk k r

def uL (k r : ℕ) (l : Fin r) (g : Mx k r) : Mx k r := hx k r l ((cF k r l g)⁻¹ • (g *ᵥ bvec (eI k r l)))

def rho (k r : ℕ) (l : Fin r) (g : Mx k r) : Mx k r :=
  w1 k r l (conj (cF k r l g)) * iH (uL k r l g) * g * uL k r l (iH g)

lemma iH_eq {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : iH g = g⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  unfold iH
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h, B2x8.Hpk_sq]

lemma inv_inv' {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹⁻¹ = g := Matrix.nonsing_inv_nonsing_inv _ (uh_unit hg)

lemma Dec.inv {g u g₁ u' : Mx k r} {c : ℂ} (h : Dec k r l g c u g₁ u') : Dec k r l g⁻¹ (conj c) u'⁻¹ g₁⁻¹ u⁻¹ := by
  refine ⟨(map_ne_zero _).2 h.hc, up_inv h.hu', glev_inv h.hg, up_inv h.hu, ?_⟩
  rw [h.eq, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_inv_rev, weyl_cell_inv h.hc, ← w1_commute_of_mem_Glev _ (glev_inv h.hg)]
  simp only [Matrix.mul_assoc]

lemma Dec.act_e {g u g₁ u' : Mx k r} {c : ℂ} (h : Dec k r l g c u g₁ u') : g *ᵥ 𝐞 = c • (u *ᵥ 𝐬) := by
  rw [h.eq, ← Matrix.mulVec_mulVec, h.hu'.2.1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ((glev_succ_iff l g₁).1 h.hg).2.1, w1_mulVec_bvec_eI, Matrix.mulVec_smul]

lemma Dec.cF_eq {g u g₁ u' : Mx k r} {c : ℂ} (h : Dec k r l g c u g₁ u') : cF k r l g = c := by
  unfold cF
  rw [h.act_e, h_smul_left, (isX_of_glev h.hu.1 h.hu.2.1).1, mul_one]

lemma Dec.uL_eq {g u g₁ u' : Mx k r} {c : ℂ} (h : Dec k r l g c u g₁ u') : uL k r l g = u := by
  unfold uL
  rw [h.cF_eq, h.act_e, smul_smul, inv_mul_cancel₀ h.hc, one_smul, up_hx h.hu]

lemma Dec.uL_iH {g u g₁ u' : Mx k r} {c : ℂ} (h : Dec k r l g c u g₁ u') : uL k r l (iH g) = u'⁻¹ := by
  rw [iH_eq h.mem.1, h.inv.uL_eq]

lemma Dec.rho_eq {g u g₁ u' : Mx k r} {c : ℂ} (h : Dec k r l g c u g₁ u') : rho k r l g = g₁ := by
  unfold rho
  rw [h.uL_iH, h.uL_eq, h.cF_eq, iH_eq h.hu.1.1, ← weyl_cell_inv h.hc]
  conv_lhs => rw [h.eq]
  have hw := weyl_cell_mem_level_group (k := k) (r := r) (l := l) h.hc
  calc (w1 k r l c)⁻¹ * u⁻¹ * (u * (w1 k r l c * g₁) * u') * u'⁻¹
      = (w1 k r l c)⁻¹ * ((u⁻¹ * u) * ((w1 k r l c) * (g₁ * (u' * u'⁻¹)))) := by simp only [Matrix.mul_assoc]
    _ = g₁ := by
      rw [uh_inv_mul h.hu.1.1, uh_mul_inv h.hu'.1.1, Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc,
        uh_inv_mul hw.1, Matrix.one_mul]

lemma Dec.leftG {g u g₁ u' p : Mx k r} {c : ℂ} (h : Dec k r l g c u g₁ u') (hp : p ∈ Glev k r l.succ) :
    Dec k r l (p * g) c (p * u * p⁻¹) (p * g₁) u' := by
  refine ⟨h.hc, up_conj h.hu hp, glev_mul hp h.hg, h.hu', ?_⟩
  rw [← Matrix.mul_assoc (w1 k r l c), w1_commute_of_mem_Glev c hp, h.eq]
  calc p * (u * (w1 k r l c * g₁) * u') = p * u * (1 * (w1 k r l c * (g₁ * u'))) := by
        simp only [Matrix.mul_assoc, Matrix.one_mul]
    _ = p * u * p⁻¹ * (p * w1 k r l c * g₁) * u' := by
        rw [← uh_inv_mul hp.1]; simp only [Matrix.mul_assoc]

lemma Dec.leftU {g u g₁ u' u₂ : Mx k r} {c : ℂ} (h : Dec k r l g c u g₁ u') (hp : u₂ ∈ UP k r l) :
    Dec k r l (u₂ * g) c (u₂ * u) g₁ u' :=
  ⟨h.hc, up_mul hp h.hu, h.hg, h.hu', by rw [h.eq]; simp only [Matrix.mul_assoc]⟩

lemma Dec.rightG {g u g₁ u' p : Mx k r} {c : ℂ} (h : Dec k r l g c u g₁ u') (hp : p ∈ Glev k r l.succ) :
    Dec k r l (g * p) c u (g₁ * p) (p⁻¹ * u' * p) := by
  refine ⟨h.hc, h.hu, glev_mul h.hg hp, up_conj' h.hu' hp, ?_⟩
  rw [h.eq]
  calc u * (w1 k r l c * g₁) * u' * p = u * (w1 k r l c * (g₁ * (1 * (u' * p)))) := by
        simp only [Matrix.mul_assoc, Matrix.one_mul]
    _ = u * (w1 k r l c * (g₁ * p)) * (p⁻¹ * u' * p) := by
        rw [← uh_mul_inv hp.1]; simp only [Matrix.mul_assoc]

lemma Dec.rightU {g u g₁ u' u₂ : Mx k r} {c : ℂ} (h : Dec k r l g c u g₁ u') (hp : u₂ ∈ UP k r l) :
    Dec k r l (g * u₂) c u g₁ (u' * u₂) :=
  ⟨h.hc, h.hu, h.hg, up_mul h.hu' hp, by rw [h.eq]; simp only [Matrix.mul_assoc]⟩

lemma dec_w {c : ℂ} (hc : c ≠ 0) {g : Mx k r} (hg : g ∈ Glev k r l.succ) : Dec k r l (w1 k r l c * g) c 1 g 1 :=
  ⟨hc, up_one, hg, up_one, by rw [Matrix.one_mul, Matrix.mul_one]⟩

lemma nlev_e {n : Mx k r} (hn : n ∈ Nlev k r l.castSucc) : n *ᵥ 𝐞 = 𝐞 := by
  ext i
  by_cases hi : l.val ≤ i.val
  · rw [← B2x6.ent, hn.1.2.1 l i hi]; simp only [bvec, Pi.single_apply]
  · have hl := l.isLt
    have e : eI k r ⟨i.val, by omega⟩ = i := Fin.ext rfl
    have ha : (⟨i.val, by omega⟩ : Fin r).val < (l.castSucc).val := by simp only [Fin.val_castSucc]; omega
    have hne : l ≠ ⟨i.val, by omega⟩ := fun h => hi (by rw [h])
    rw [← e, ← herm_es_right (n *ᵥ bvec (eI k r l))]
    conv_lhs => rw [← (hn.2.2 _ ha).2]
    rw [uh_herm hn.2.1, h_e_es, if_neg hne]
    symm
    apply Pi.single_eq_of_ne
    intro h; exact hne (eI_inj.1 h).symm

lemma nlev_dec {n : Mx k r} (hn : n ∈ Nlev k r l.castSucc) :
    ∃ u ∈ UP k r l, ∃ n₁ ∈ Nlev k r l.succ, n = u * n₁ := by
  obtain ⟨u, hu, g₁, hg₁, h⟩ := stab_dec hn.2 (nlev_e hn)
  refine ⟨u, hu, g₁, ⟨?_, hg₁⟩, h⟩
  have : g₁ = u⁻¹ * n := by rw [h, ← Matrix.mul_assoc, uh_inv_mul hu.1.1, Matrix.one_mul]
  rw [this]
  exact WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_inv (up_nset hu)) hn.1

lemma nlev_dec' {n : Mx k r} (hn : n ∈ Nlev k r l.castSucc) :
    ∃ u ∈ UP k r l, ∃ n₁ ∈ Nlev k r l.succ, n = n₁ * u := by
  obtain ⟨u, hu, g₁, hg₁, h⟩ := stab_dec' hn.2 (nlev_e hn)
  refine ⟨u, hu, g₁, ⟨?_, hg₁⟩, h⟩
  have : g₁ = n * u⁻¹ := by rw [h, Matrix.mul_assoc, uh_mul_inv hu.1.1, Matrix.mul_one]
  rw [this]
  exact WeylGroupFacts.mem_n_mul hn.1 (WeylGroupFacts.mem_n_inv (up_nset hu))

lemma psi_mul {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {n n' : Mx k r} (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) :
    psi k r z cStd (n * n') = psi k r z cStd n * psi k r z cStd n' := (psiChar k r z cStd hz n hn).1 n' hn'

lemma psi_ne {z : Fin (2 * r + k + 1) → ℂ} (n : Mx k r) : psi k r z cStd n ≠ 0 := Complex.exp_ne_zero _

lemma psi_one {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : psi k r z cStd (1 : Mx k r) = 1 := by
  have h := psi_mul hz (WeylGroupFacts.mem_n_one (k := k) (r := r)) WeylGroupFacts.mem_n_one
  rw [Matrix.one_mul] at h
  exact (mul_eq_left₀ (psi_ne _)).1 h.symm

lemma psi_conjN {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {n u : Mx k r} (hn : n ∈ Nset k r) (hu : u ∈ Nset k r) :
    psi k r z cStd (n * u * n⁻¹) = psi k r z cStd u := by
  have h1 := psi_mul hz (WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_mul hn hu) (WeylGroupFacts.mem_n_inv hn)) hn
  rw [Matrix.mul_assoc, uh_inv_mul hn.1, Matrix.mul_one, psi_mul hz hn hu, mul_comm] at h1
  exact (mul_right_cancel₀ (psi_ne _) h1).symm

lemma psi_conjN' {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {n u : Mx k r} (hn : n ∈ Nset k r) (hu : u ∈ Nset k r) :
    psi k r z cStd (n⁻¹ * u * n) = psi k r z cStd u := by
  have := psi_conjN hz (WeylGroupFacts.mem_n_inv hn) hu
  rwa [inv_inv' hn.1] at this

lemma psi_conjW {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h u : Mx k r} (hh : h ∈ UWset k r z) (hu : u ∈ Nset k r) :
    psi k r z cStd (h * u * h⁻¹) = psi k r z cStd u := by
  unfold psi
  rw [(uWNormal k r z hz h hh u hu).2]

lemma psi_conjW' {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h u : Mx k r} (hh : h ∈ UWset k r z) (hu : u ∈ Nset k r) :
    psi k r z cStd (h⁻¹ * u * h) = psi k r z cStd u := by
  have := psi_conjW hz (WeylGroupFacts.uw_inv hh) hu
  rwa [inv_inv' hh.1] at this

section smooth
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℕ}

def SmM (f : X → Matrix (Fin m) (Fin m) ℂ) (s : Set X) : Prop := ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s

def SmV (f : X → Fin m → ℂ) (s : Set X) : Prop := ∀ i, ContDiffOn ℝ ∞ (fun x => f x i) s

lemma sm_conj {f : X → ℂ} {s : Set X} (hf : ContDiffOn ℝ ∞ f s) : ContDiffOn ℝ ∞ (fun x => conj (f x)) s :=
  Complex.conjCLE.contDiff.comp_contDiffOn hf

lemma smM_const (A : Matrix (Fin m) (Fin m) ℂ) (s : Set X) : SmM (fun _ => A) s := fun _ _ => contDiffOn_const
lemma smV_const (v : Fin m → ℂ) (s : Set X) : SmV (fun _ => v) s := fun _ => contDiffOn_const

lemma smM_mul {f g : X → Matrix (Fin m) (Fin m) ℂ} {s : Set X} (hf : SmM f s) (hg : SmM g s) :
    SmM (fun x => f x * g x) s := by
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun p _ => (hf i p).mul (hg p j)

lemma smM_conjT {f : X → Matrix (Fin m) (Fin m) ℂ} {s : Set X} (hf : SmM f s) : SmM (fun x => (f x)ᴴ) s := by
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact sm_conj (hf j i)

lemma smV_mulVec {f : X → Matrix (Fin m) (Fin m) ℂ} {v : X → Fin m → ℂ} {s : Set X} (hf : SmM f s) (hv : SmV v s) :
    SmV (fun x => f x *ᵥ v x) s := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiffOn.sum fun p _ => (hf i p).mul (hv p)

lemma smV_smul {c : X → ℂ} {v : X → Fin m → ℂ} {s : Set X} (hc : ContDiffOn ℝ ∞ c s) (hv : SmV v s) :
    SmV (fun x => c x • v x) s := by
  intro i
  simp only [Pi.smul_apply, smul_eq_mul]
  exact hc.mul (hv i)

lemma smV_add {u v : X → Fin m → ℂ} {s : Set X} (hu : SmV u s) (hv : SmV v s) : SmV (fun x => u x + v x) s :=
  fun i => (hu i).add (hv i)
lemma smV_sub {u v : X → Fin m → ℂ} {s : Set X} (hu : SmV u s) (hv : SmV v s) : SmV (fun x => u x - v x) s :=
  fun i => (hu i).sub (hv i)

lemma sm_herm (H : Matrix (Fin m) (Fin m) ℂ) {u v : X → Fin m → ℂ} {s : Set X} (hu : SmV u s) (hv : SmV v s) :
    ContDiffOn ℝ ∞ (fun x => herm H (u x) (v x)) s := by
  simp only [herm, dotProduct, Pi.star_apply]
  exact ContDiffOn.sum fun p _ => (sm_conj (hv p)).mul (smV_mulVec (smM_const H s) hu p)

lemma smM_hs (H : Matrix (Fin m) (Fin m) ℂ) {p v : X → Fin m → ℂ} {σ : X → ℂ} {s : Set X} (hp : SmV p s) (hv : SmV v s)
    (hσ : ContDiffOn ℝ ∞ σ s) : SmM (fun x => hs H (p x) (v x) (σ x)) s := by
  intro i j
  simp only [hs, Matrix.add_apply, Matrix.sub_apply, vecMulVec_apply]
  exact (contDiffOn_const.sub ((hp i).mul (sm_herm H (smV_const _ s) hv))).add
    ((smV_add hv (smV_smul hσ hp) i).mul (sm_herm H (smV_const _ s) hp))

lemma smM_contDiffOn {f : X → Matrix (Fin m) (Fin m) ℂ} {s : Set X} (hf : SmM f s) : ContDiffOn ℝ ∞ f s := by
  have h : ContDiffOn ℝ ∞ (fun x => (f x : Fin m → Fin m → ℂ)) s :=
    contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => hf i j
  exact h

end smooth

lemma smM_id (s : Set (Mx k r)) : SmM (fun g : Mx k r => g) s := fun i j =>
  (contDiff_apply_apply ℝ ℂ i j).contDiffOn

section smooth2
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma smM_iH {f : X → Mx k r} {s : Set X} (hf : SmM f s) : SmM (fun x => iH (f x)) s :=
  smM_mul (smM_mul (smM_const _ s) (smM_conjT hf)) (smM_const _ s)

lemma sm_cF {f : X → Mx k r} {s : Set X} (hf : SmM f s) : ContDiffOn ℝ ∞ (fun x => cF k r l (f x)) s :=
  sm_herm _ (smV_mulVec hf (smV_const _ s)) (smV_const _ s)

lemma smM_hx {x : X → Fin (2 * r + k + 1) → ℂ} {s : Set X} (hx' : SmV x s) : SmM (fun y => hx k r l (x y)) s :=
  smM_hs _ (smV_const _ s)
    (smV_sub (smV_sub hx' (smV_const _ s)) (smV_smul (sm_herm _ hx' (smV_const _ s)) (smV_const _ s)))
    (sm_herm _ hx' (smV_const _ s))

lemma smM_uL {f : X → Mx k r} {s : Set X} (hf : SmM f s) (h0 : ∀ x ∈ s, cF k r l (f x) ≠ 0) :
    SmM (fun x => uL k r l (f x)) s :=
  smM_hx (smV_smul ((sm_cF hf).inv h0) (smV_mulVec hf (smV_const _ s)))

lemma smooth_map_weyl_cell {c : X → ℂ} {s : Set X} (hc : ContDiffOn ℝ ∞ c s) (h0 : ∀ x ∈ s, c x ≠ 0) :
    SmM (fun x => w1 k r l (c x)) s := by
  intro i j
  simp only [w1]
  split_ifs
  · exact hc
  · exact (sm_conj hc).inv fun x hx => (map_ne_zero _).2 (h0 x hx)
  · exact contDiffOn_const
  · exact contDiffOn_const

lemma sm_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) {f : X → Mx k r} {s : Set X} (hf : SmM f s) :
    ContDiffOn ℝ ∞ (fun x => psi k r z c (f x)) s := by
  have h1 : ContDiffOn ℝ ∞ (fun x => ell k r z (f x)) s := by
    unfold ell
    apply ContDiffOn.sum
    intro a _
    split_ifs
    · exact hf _ _
    · exact smV_mulVec hf (smV_const _ s) _
  have h2 : ContDiffOn ℝ ∞ (fun x => c * ell k r z (f x)) s := contDiffOn_const.mul h1
  have h3 : ContDiffOn ℝ ∞ (fun x => (c * ell k r z (f x)).re) s := Complex.reCLM.contDiff.comp_contDiffOn h2
  have h4 : ContDiffOn ℝ ∞ (fun x => (((c * ell k r z (f x)).re : ℝ) : ℂ)) s :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn h3
  unfold psi
  exact (contDiffOn_const.mul h4).cexp

end smooth2

def C0 (k r : ℕ) (l : Fin r) : Set (Mx k r) := {g | cF k r l g ≠ 0 ∧ cF k r l (iH g) ≠ 0}

lemma smM_rho : SmM (rho k r l) (C0 k r l) := by
  have h1 := smM_id (C0 k r l)
  have h2 : SmM (fun g => uL k r l g) (C0 k r l) := smM_uL h1 fun x hx => hx.1
  have h3 : SmM (fun g => uL k r l (iH g)) (C0 k r l) := smM_uL (smM_iH h1) fun x hx => hx.2
  exact smM_mul (smM_mul (smM_mul (smooth_map_weyl_cell (sm_conj (sm_cF h1)) fun x hx => (map_ne_zero _).2 hx.1) (smM_iH h2)) h1) h3

lemma isOpen_adelicUnipotentTimesIntegralOutsideSet : IsOpen (C0 k r l) := by
  have h1 : Continuous fun g : Mx k r => cF k r l g :=
    continuousOn_univ.1 (sm_cF (smM_id Set.univ)).continuousOn
  have h2 : Continuous fun g : Mx k r => cF k r l (iH g) :=
    continuousOn_univ.1 (sm_cF (smM_iH (smM_id Set.univ))).continuousOn
  exact (isOpen_ne_fun h1 continuous_const).inter (isOpen_ne_fun h2 continuous_const)

lemma Dec.cell_decomposition_mem {g u g₁ u' : Mx k r} {c : ℂ} (h : Dec k r l g c u g₁ u') : g ∈ C0 k r l := by
  refine ⟨by rw [h.cF_eq]; exact h.hc, ?_⟩
  rw [iH_eq h.mem.1, h.inv.cF_eq]
  exact h.inv.hc

section ext
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

def D0 (k r : ℕ) (l : Fin r) (D₁ : Set (Mx k r)) : Set (Mx k r) := C0 k r l ∩ rho k r l ⁻¹' D₁

def Jx (k r : ℕ) (l : Fin r) (z z' : Fin (2 * r + k + 1) → ℂ) (φ : ℂ → ℂ) (Ψ : Mx k r → (Wq →L[ℂ] Wp)) (g : Mx k r) :
    Wq →L[ℂ] Wp :=
  (psi k r z cStd (uL k r l g) * psi k r z' cStd (iH (uL k r l (iH g)))) • (φ (cF k r l g) • Ψ (rho k r l g))

lemma Dec.Jx_eq {g u g₁ u' : Mx k r} {c : ℂ} (h : Dec k r l g c u g₁ u') (z z' : Fin (2 * r + k + 1) → ℂ) (φ : ℂ → ℂ)
    (Ψ : Mx k r → (Wq →L[ℂ] Wp)) :
    Jx k r l z z' φ Ψ g = (psi k r z cStd u * psi k r z' cStd u') • (φ c • Ψ g₁) := by
  unfold Jx
  rw [h.uL_eq, h.uL_iH, h.cF_eq, h.rho_eq, iH_eq (up_inv h.hu').1.1, inv_inv' h.hu'.1.1]

lemma mem_cell_domain_iff {D₁ : Set (Mx k r)} {g : Mx k r} :
    g ∈ Glev k r l.castSucc ∩ D0 k r l D₁ ↔ ∃ c u g₁ u', Dec k r l g c u g₁ u' ∧ g₁ ∈ D₁ := by
  constructor
  · rintro ⟨hg, hC, hρ⟩
    obtain ⟨u, g₁, u', h⟩ := dec_exists hg hC.1
    refine ⟨_, u, g₁, u', h, ?_⟩
    rw [← h.rho_eq]; exact hρ
  · rintro ⟨c, u, g₁, u', h, hg₁⟩
    refine ⟨h.mem, h.cell_decomposition_mem, ?_⟩
    show rho k r l g ∈ D₁
    rw [h.rho_eq]; exact hg₁

lemma isOpen_cell_domain {D₁ : Set (Mx k r)} (hD : IsOpen D₁) : IsOpen (D0 k r l D₁) :=
  (smM_contDiffOn smM_rho).continuousOn.isOpen_inter_preimage isOpen_adelicUnipotentTimesIntegralOutsideSet hD

theorem resSurj : ResSurj := by
  intro Wp Wq _ _ _ _ k r z z' π π' l D₁ φ Ψ hz hz' hD₁ hφ hΨ
  obtain ⟨hΨs, hΨL, hΨR, hΨW⟩ := hΨ
  refine ⟨D0 k r l D₁, ⟨isOpen_cell_domain hD₁.1, ?_⟩, ?_, ?_, Jx k r l z z' φ Ψ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    rintro g hg s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
    obtain ⟨c, u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg
    obtain ⟨u₂, hu₂, n₁, hn₁, rfl⟩ := nlev_dec hm
    obtain ⟨u₃, hu₃, n₃, hn₃, rfl⟩ := nlev_dec' hm'
    have d1 := (((((d.leftG hn₁.2).leftU hu₂).leftG (uw_glev hh _)).rightG (uw_glev hh' _)).rightG hn₃.2).rightU hu₃
    have e : h * (u₂ * n₁) * g * (h' * (n₃ * u₃)) = h * (u₂ * (n₁ * g)) * h' * n₃ * u₃ := by
      simp only [Matrix.mul_assoc]
    rw [e]
    refine (mem_cell_domain_iff.2 ⟨_, _, _, _, d1, ?_⟩).2
    have h2 := hD₁.2 g₁ ⟨d.hg, hg₁⟩ (h * n₁) ⟨h, hh, n₁, hn₁, rfl⟩ (h' * n₃) ⟨h', hh', n₃, hn₃, rfl⟩
    have e2 : h * (n₁ * g₁) * h' * n₃ = h * n₁ * g₁ * (h' * n₃) := by simp only [Matrix.mul_assoc]
    rw [e2]; exact h2
  · intro g hg
    exact hg.1.1
  · intro c hc g hg
    have d := dec_w (l := l) hc hg
    constructor
    · intro h
      have h2 : rho k r l (w1 k r l c * g) ∈ D₁ := h.2
      rwa [d.rho_eq] at h2
    · intro h
      refine ⟨d.cell_decomposition_mem, ?_⟩
      show rho k r l (w1 k r l c * g) ∈ D₁
      rw [d.rho_eq]; exact h
  ·
    intro g₀ hg₀
    obtain ⟨c, u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg₀
    obtain ⟨U₁, F₁, hU₁, hmem, hF₁, hag⟩ := hΨs g₁ ⟨d.hg, hg₁⟩
    refine ⟨C0 k r l ∩ rho k r l ⁻¹' U₁, fun g => (psi k r z cStd (uL k r l g) * psi k r z' cStd (iH (uL k r l (iH g)))) •
      (φ (cF k r l g) • F₁ (rho k r l g)), (smM_contDiffOn smM_rho).continuousOn.isOpen_inter_preimage isOpen_adelicUnipotentTimesIntegralOutsideSet hU₁,
      ⟨d.cell_decomposition_mem, ?_⟩, ?_, ?_⟩
    · show rho k r l g₀ ∈ U₁
      rw [d.rho_eq]; exact hmem
    · have hs : C0 k r l ∩ rho k r l ⁻¹' U₁ ⊆ C0 k r l := Set.inter_subset_left
      have h1 := smM_id (C0 k r l ∩ rho k r l ⁻¹' U₁)
      have h2 : SmM (fun g => uL k r l g) (C0 k r l ∩ rho k r l ⁻¹' U₁) := smM_uL h1 fun x hx => hx.1.1
      have h3 : SmM (fun g => uL k r l (iH g)) (C0 k r l ∩ rho k r l ⁻¹' U₁) := smM_uL (smM_iH h1) fun x hx => hx.1.2
      have h4 : ContDiffOn ℝ ∞ (fun g => φ (cF k r l g)) (C0 k r l ∩ rho k r l ⁻¹' U₁) :=
        hφ.comp (sm_cF h1) fun x hx => hx.1.1
      have h5 : ContDiffOn ℝ ∞ (fun g => F₁ (rho k r l g)) (C0 k r l ∩ rho k r l ⁻¹' U₁) :=
        hF₁.comp ((smM_contDiffOn smM_rho).mono hs) fun x hx => hx.2
      exact ((sm_psi z cStd h2).mul (sm_psi z' cStd (smM_iH h3))).smul (h4.smul h5)
    · intro g hgU hgG
      obtain ⟨u₂, g₂, u₂', d₂⟩ := dec_exists hgG hgU.1.1
      unfold Jx
      rw [hag (rho k r l g) hgU.2 (by rw [d₂.rho_eq]; exact d₂.hg)]
  ·
    intro g hg n hn
    obtain ⟨c, u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg
    obtain ⟨u₂, hu₂, n₁, hn₁, rfl⟩ := nlev_dec hn
    have d1 := (d.leftG hn₁.2).leftU hu₂
    rw [Matrix.mul_assoc, d1.Jx_eq, d.Jx_eq, hΨL g₁ ⟨d.hg, hg₁⟩ n₁ hn₁,
      psi_mul hz (up_nset hu₂) (up_nset (up_conj d.hu hn₁.2)), psi_conjN hz hn₁.1 (up_nset d.hu),
      psi_mul hz (up_nset hu₂) hn₁.1]
    simp only [smul_smul]
    congr 1
    ring
  ·
    intro g hg n hn
    obtain ⟨c, u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg
    obtain ⟨u₃, hu₃, n₃, hn₃, rfl⟩ := nlev_dec' hn
    have d1 := (d.rightG hn₃.2).rightU hu₃
    rw [← Matrix.mul_assoc, d1.Jx_eq, d.Jx_eq, hΨR g₁ ⟨d.hg, hg₁⟩ n₃ hn₃,
      psi_mul hz' (up_nset (up_conj' d.hu' hn₃.2)) (up_nset hu₃), psi_conjN' hz' hn₃.1 (up_nset d.hu'),
      psi_mul hz' hn₃.1 (up_nset hu₃)]
    simp only [smul_smul]
    congr 1
    ring
  ·
    intro g hg h hh h' hh'
    obtain ⟨c, u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg
    have d1 := (d.leftG (uw_glev hh _)).rightG (uw_glev hh' _)
    rw [d1.Jx_eq, d.Jx_eq, hΨW g₁ ⟨d.hg, hg₁⟩ h hh h' hh', psi_conjW hz hh (up_nset d.hu),
      psi_conjW' hz' hh' (up_nset d.hu')]
    ext v
    simp
  · intro c hc g hg
    rw [(dec_w hc hg.1).Jx_eq, psi_one hz, psi_one hz', one_mul, one_smul]

end ext

section transfer
variable {r' : ℕ}

open Formalism.FourierDecayAlt.B2 (a0)
open B2x6 (lv blk)

lemma lv_eI (a : Fin r') : lv k r' (eI k r' a) = eI k (1 + r') ⟨a.val + 1, by omega⟩ :=
  Fin.ext (by rw [B2x6.lv_val]; simp only [eI])

lemma lv_esI (a : Fin r') : lv k r' (esI k r' a) = esI k (1 + r') ⟨a.val + 1, by omega⟩ :=
  Fin.ext (by rw [B2x6.lv_val]; simp only [esI]; omega)

lemma level_one_eq_embedding {x : Mx k (1 + r')} (hx : x ∈ Glev k (1 + r') ⟨1, by omega⟩) :
    ∃ g ∈ UH (Hpk k r'), x = ιLev k 1 r' g :=
  B2x8.al_fix hx.1 (hx.2 (a0 r') (by simp [a0])).1 (hx.2 (a0 r') (by simp [a0])).2

lemma blk_lev (g : Mx k r') : blk (ιLev k 1 r' g) = g := by
  ext i j; exact B2x6.lev_mm g i j

lemma glev0 {g : Mx k r'} (hg : g ∈ UH (Hpk k r')) : g ∈ Glev k r' 0 :=
  ⟨hg, fun a ha => absurd ha (by simp)⟩

lemma lev_nset {g : Mx k r'} (hg : g ∈ UH (Hpk k r')) (h : ιLev k 1 r' g ∈ Nset k (1 + r')) : g ∈ Nset k r' := by
  rw [WeylGroupFacts.nset_iff] at h ⊢
  refine ⟨hg, fun i j hj hi => ?_⟩
  have h2 := h.2 (lv k r' i) (lv k r' j) (by rw [B2x6.lv_val]; omega) (by rw [B2x6.lv_val, B2x6.lv_val]; omega)
  rw [B2x6.lev_mm] at h2
  simpa only [B2x6.lv_inj] using h2

lemma lift_inj {y y' : Fin (2 * r' + k + 1) → ℂ} (h : liftVec k 1 r' y = liftVec k 1 r' y') : y = y' := by
  have := congrArg B2x6.res h
  simpa using this

lemma lev_uw {z : Fin (2 * r' + k + 1) → ℂ} {g : Mx k r'} (hg : g ∈ UH (Hpk k r'))
    (h : ιLev k 1 r' g ∈ UWset k (1 + r') (liftVec k 1 r' z)) : g ∈ UWset k r' z := by
  refine ⟨hg, fun a => ⟨?_, ?_⟩, ?_⟩
  · have h2 := (h.2.1 ⟨a.val + 1, by omega⟩).1
    rw [← lv_eI, B2x6.bvec_lv, B2x5.lev_lift] at h2
    exact lift_inj h2
  · have h2 := (h.2.1 ⟨a.val + 1, by omega⟩).2
    rw [← lv_esI, B2x6.bvec_lv, B2x5.lev_lift] at h2
    exact lift_inj h2
  · have h2 := h.2.2
    rw [B2x5.lev_lift] at h2
    exact lift_inj h2

lemma lift_inWb {z : Fin (2 * r' + k + 1) → ℂ} (hz : inWb k r' z) : inWb k (1 + r') (liftVec k 1 r' z) := by
  intro i hi
  unfold liftVec
  split_ifs with hp
  · apply hz
    simp only
    omega
  · rfl

lemma ell_lev (z : Fin (2 * r' + k + 1) → ℂ) (g : Mx k r') :
    ell k (1 + r') (liftVec k 1 r' z) (ιLev k 1 r' g) = ell k r' z g := by
  unfold ell
  symm
  apply Fintype.sum_of_injective (fun a : Fin r' => (⟨a.val + 1, by omega⟩ : Fin (1 + r')))
  · intro a b h
    have := congrArg Fin.val h
    simp only at this
    exact Fin.ext (by omega)
  · intro a ha
    have ha0 : a.val = 0 := by
      by_contra h0
      apply ha
      have := a.isLt
      exact ⟨⟨a.val - 1, by omega⟩, Fin.ext (by simp only; omega)⟩
    have e : eI k (1 + r') a = B2x6.iF k r' := Fin.ext (by rw [B2x6.iF_val]; exact ha0)
    split_ifs with h
    · rw [e, B2x6.lev_F, if_neg]
      intro h2
      have := congrArg Fin.val h2
      rw [B2x6.iF_val] at this
      simp only [eI] at this
      omega
    · rw [e, B2x6.lev_mulVec_F, B2x6.lift_F]
  · intro a
    by_cases h : a.val + 1 < r'
    · rw [dif_pos h, dif_pos (by simp only; omega)]
      have e2 : eI k (1 + r') ⟨a.val + 1 + 1, by omega⟩ = lv k r' (eI k r' ⟨a.val + 1, h⟩) := (lv_eI (k := k) (⟨a.val + 1, h⟩ : Fin r')).symm
      rw [← lv_eI a]
      exact (B2x6.lev_mm g _ _).symm.trans (by rw [e2])
    · rw [dif_neg h, dif_neg (by simp only; omega), ← lv_eI a, B2x5.lev_lift]
      exact (congrFun (B2x6.lift_res (g *ᵥ z)) (eI k r' a)).symm

lemma psi_lev (z : Fin (2 * r' + k + 1) → ℂ) (c : ℂ) (g : Mx k r') :
    psi k (1 + r') (liftVec k 1 r' z) c (ιLev k 1 r' g) = psi k r' z c g := by
  unfold psi; rw [ell_lev]

lemma smM_blk (s : Set (Mx k (1 + r'))) : SmM (fun x : Mx k (1 + r') => (blk x : Mx k r')) s := fun i j =>
  (contDiff_apply_apply ℝ ℂ (lv k r' i) (lv k r' j)).contDiffOn

lemma cont_blk : Continuous (fun x : Mx k (1 + r') => (blk x : Mx k r')) :=
  continuousOn_univ.1 (smM_contDiffOn (smM_blk Set.univ)).continuousOn

theorem fFTransfer : FFTransfer := by
  intro Wp Wq _ _ _ _ k r' z z' π π' D hz hz' hD J hJ
  obtain ⟨hJs, hJL, hJR, hJW⟩ := hJ
  refine ⟨fun x => π (blk x), fun x => π' (blk x), (fun x : Mx k (1 + r') => (blk x : Mx k r')) ⁻¹' D,
    fun x => J (blk x), lift_inWb hz, lift_inWb hz', ⟨hD.1.preimage cont_blk, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rintro x hx s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
    obtain ⟨g, hg, rfl⟩ := level_one_eq_embedding hx.1
    obtain ⟨h₁, hh₁, rfl⟩ := level_one_eq_embedding (uw_glev hh _)
    obtain ⟨m₁, hm₁, rfl⟩ := level_one_eq_embedding hm.2
    obtain ⟨h₂, hh₂, rfl⟩ := level_one_eq_embedding (uw_glev hh' _)
    obtain ⟨m₂, hm₂, rfl⟩ := level_one_eq_embedding hm'.2
    have hgD : g ∈ D := by
      have := hx.2
      simp only [Set.mem_preimage, blk_lev] at this
      exact this
    show blk (ιLev k 1 r' h₁ * ιLev k 1 r' m₁ * ιLev k 1 r' g * (ιLev k 1 r' h₂ * ιLev k 1 r' m₂)) ∈ D
    rw [← B2x8.al_lev_mul, ← B2x8.al_lev_mul, ← B2x8.al_lev_mul, ← B2x8.al_lev_mul, blk_lev]
    exact hD.2 g ⟨glev0 hg, hgD⟩ (h₁ * m₁) ⟨h₁, lev_uw hh₁ hh, m₁, ⟨lev_nset hm₁ hm.1, glev0 hm₁⟩, rfl⟩
      (h₂ * m₂) ⟨h₂, lev_uw hh₂ hh', m₂, ⟨lev_nset hm₂ hm'.1, glev0 hm₂⟩, rfl⟩
  · intro x₀ hx₀
    obtain ⟨g₀, hg₀, rfl⟩ := level_one_eq_embedding hx₀.1
    have hgD : g₀ ∈ D := by
      have := hx₀.2
      simp only [Set.mem_preimage, blk_lev] at this
      exact this
    obtain ⟨U, F, hU, hmem, hF, hag⟩ := hJs g₀ ⟨glev0 hg₀, hgD⟩
    refine ⟨(fun x : Mx k (1 + r') => (blk x : Mx k r')) ⁻¹' U, fun x => F (blk x), hU.preimage cont_blk, ?_, ?_, ?_⟩
    · simp only [Set.mem_preimage, blk_lev]; exact hmem
    · exact hF.comp (smM_contDiffOn (smM_blk _)) fun x hx => hx
    · intro x hxU hxG
      obtain ⟨g, hg, rfl⟩ := level_one_eq_embedding hxG
      simp only [Set.mem_preimage, blk_lev] at hxU
      simp only [blk_lev]
      exact hag g hxU (glev0 hg)
  · intro x hx n hn
    obtain ⟨g, hg, rfl⟩ := level_one_eq_embedding hx.1
    obtain ⟨n₁, hn₁, rfl⟩ := level_one_eq_embedding hn.2
    have hgD : g ∈ D := by
      have := hx.2
      simp only [Set.mem_preimage, blk_lev] at this
      exact this
    rw [← B2x8.al_lev_mul, psi_lev]
    simp only [blk_lev]
    exact hJL g ⟨glev0 hg, hgD⟩ n₁ ⟨lev_nset hn₁ hn.1, glev0 hn₁⟩
  · intro x hx n hn
    obtain ⟨g, hg, rfl⟩ := level_one_eq_embedding hx.1
    obtain ⟨n₁, hn₁, rfl⟩ := level_one_eq_embedding hn.2
    have hgD : g ∈ D := by
      have := hx.2
      simp only [Set.mem_preimage, blk_lev] at this
      exact this
    rw [← B2x8.al_lev_mul, psi_lev]
    simp only [blk_lev]
    exact hJR g ⟨glev0 hg, hgD⟩ n₁ ⟨lev_nset hn₁ hn.1, glev0 hn₁⟩
  · intro x hx h hh h' hh'
    obtain ⟨g, hg, rfl⟩ := level_one_eq_embedding hx.1
    obtain ⟨h₁, hh₁, rfl⟩ := level_one_eq_embedding (uw_glev hh _)
    obtain ⟨h₂, hh₂, rfl⟩ := level_one_eq_embedding (uw_glev hh' _)
    have hgD : g ∈ D := by
      have := hx.2
      simp only [Set.mem_preimage, blk_lev] at this
      exact this
    rw [← B2x8.al_lev_mul, ← B2x8.al_lev_mul]
    simp only [blk_lev]
    exact hJW g ⟨glev0 hg, hgD⟩ h₁ (lev_uw hh₁ hh) h₂ (lev_uw hh₂ hh')
  · intro g _
    simp only [Set.mem_preimage, blk_lev, true_and, iff_self]

end transfer

end Formalism.FourierDecayAlt.P.Qx4

namespace Formalism.FourierDecayAlt.P

theorem resSurj_statement : Formalism.FourierDecayAlt.Q.ResSurj := Qx4.resSurj
theorem cell_decomposition : Formalism.FourierDecayAlt.Q.CellDecomp := Qx4.cellDecomp
theorem cells_dense : Formalism.FourierDecayAlt.Q.CellDense := Qx4.cellDense
theorem flag_frame_transfer : Formalism.FourierDecayAlt.Q.FFTransfer := Qx4.fFTransfer

end Formalism.FourierDecayAlt.P
