import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BicechCohomologyKunnethDecomposition

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {ι G : Type} [LinearOrder ι] [AddCommGroup G] [Module ℂ G]

private def kdTw (c : Finset (ι ⊕ₗ ι) → G) : Finset ι × Finset ι → G :=
  fun x => ((-1 : ℤ) ^ x.2.card) • c (uni x.1 x.2)

private def kdUn : (Finset ι × Finset ι → G) →ₗ[ℂ] (Finset (ι ⊕ₗ ι) → G) :=
  LinearMap.pi fun s => ((-1 : ℤ) ^ (rgt s).card) •
    LinearMap.proj (R := ℂ) (φ := fun _ : Finset ι × Finset ι => G) (lft s, rgt s)

private theorem kdUn_apply (z : Finset ι × Finset ι → G) (s : Finset (ι ⊕ₗ ι)) :
    kdUn z s = ((-1 : ℤ) ^ (rgt s).card) • z (lft s, rgt s) := by
  simp [kdUn]

private theorem kd_wd_one (c : Finset ι → G) (t : Finset ι) :
    wd (fun _ => (1 : Module.End ℂ G)) c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • c (t.erase i) := by
  simp [wd, LinearMap.sum_apply]

private theorem kd_biD (z : Finset ι × Finset ι → G) (I J : Finset ι) :
    biD ℂ ι ι G z (I, J) = ∑ i ∈ I, GlobalTheory.cubeSign I i • z (I.erase i, J) +
      ((-1 : ℤ) ^ (I.card + 1)) • ∑ j ∈ J, GlobalTheory.cubeSign J j • z (I, J.erase j) := by
  simp [biD, LinearMap.sum_apply]

private theorem kd_neg_sq (n : ℕ) (x : G) : ((-1 : ℤ) ^ n) • ((-1 : ℤ) ^ n) • x = x := by
  rw [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

private theorem kdUn_tw (hU : WdUni) (c : Finset (ι ⊕ₗ ι) → G) : kdUn (kdTw c) = c := by
  funext s
  rw [kdUn_apply]
  have h := (hU ι ι G (fun _ => 1) c ∅ ∅).2.2.2.2 s
  simp only [kdTw, h]
  exact kd_neg_sq _ _

private theorem kdTw_un (hU : WdUni) (z : Finset ι × Finset ι → G) : kdTw (kdUn z) = z := by
  funext x
  obtain ⟨I, J⟩ := x
  have h := hU ι ι G (fun _ => 1) (fun _ => 0) I J
  simp only [kdTw]
  rw [kdUn_apply, h.2.1, h.2.2.1]
  exact kd_neg_sq _ _

private theorem kd_biD_tw (hU : WdUni) (c : Finset (ι ⊕ₗ ι) → G) :
    biD ℂ ι ι G (kdTw c) = kdTw (wd (fun _ => (1 : Module.End ℂ G)) c) := by
  funext x
  obtain ⟨I, J⟩ := x
  have h := hU ι ι G (fun _ => 1) c I J
  rw [kd_biD]
  simp only [kdTw, h.1, kd_wd_one]
  simp only [smul_add, Finset.smul_sum, smul_smul]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.card_erase_of_mem hj]
    obtain ⟨n, hn⟩ : ∃ n, J.card = n + 1 :=
      Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero_of_mem hj)
    rw [hn, Nat.add_sub_cancel]
    congr 1
    ring

private theorem kd_wd_un (hU : WdUni) (y : Finset ι × Finset ι → G) :
    wd (fun _ => (1 : Module.End ℂ G)) (kdUn y) = kdUn (biD ℂ ι ι G y) := by
  have h := kd_biD_tw hU (kdUn y)
  rw [kdTw_un hU] at h
  rw [h, kdUn_tw hU]

end

section
variable {ι E E' G : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
  [AddCommGroup G] [Module ℂ G]

private theorem kd_cech_val {A : Finset ι → Submodule ℂ E} {a : Finset ι → E} {p : ℤ} (ha : a ∈ (cech A).Z p)
    {s : Finset ι} (hs : (s.card : ℤ) ≠ p + 1) : a s = 0 := by
  unfold cech Cx.Z at ha
  simp [cechC] at ha
  have h := ha.1 s
  rw [if_neg (fun h' => hs h'.2)] at h
  simpa using h

private theorem kd_cech_zero {A : Finset ι → Submodule ℂ E} {a : Finset ι → E} {p : ℤ} (ha : a ∈ (cech A).Z p)
    (hp : p < 0) : a = 0 := by
  unfold cech Cx.Z at ha
  simp [cechC] at ha
  funext s
  have h := ha.1 s
  rw [if_neg] at h
  · simpa using h
  · rintro ⟨hne, hc⟩
    have := hne.card_pos
    omega

private theorem kd_single (μ : E →ₗ[ℂ] E' →ₗ[ℂ] G) (A : Finset ι → Submodule ℂ E) (B : Finset ι → Submodule ℂ E')
    (d : ℕ) (p : ℤ) (a : Finset ι → E) (b : Finset ι → E') (ha : a ∈ (cech A).Z p) (hb : b ∈ (cech B).Z ((d : ℤ) - p)) :
    ∃ (q : ℕ) (a' : Finset ι → E) (b' : Finset ι → E'),
      (q ≤ d ∧ a' ∈ (cech A).Z ((d : ℤ) - q) ∧ b' ∈ (cech B).Z q) ∧ join μ a' b' = kdUn (boxC μ a b) := by
  rcases lt_or_ge p 0 with hp | hp
  · refine ⟨0, 0, 0, ⟨Nat.zero_le _, Submodule.zero_mem _, Submodule.zero_mem _⟩, ?_⟩
    rw [kd_cech_zero ha hp]
    funext s
    simp [join, boxC, kdUn_apply]
  rcases lt_or_ge (d : ℤ) p with hd | hd
  · refine ⟨0, 0, 0, ⟨Nat.zero_le _, Submodule.zero_mem _, Submodule.zero_mem _⟩, ?_⟩
    rw [kd_cech_zero hb (by omega)]
    funext s
    simp [join, boxC, kdUn_apply]
  obtain ⟨q, hq⟩ : ∃ q : ℕ, (q : ℤ) = d - p := ⟨(d - p).toNat, Int.toNat_of_nonneg (by omega)⟩
  refine ⟨q, a, ((-1 : ℤ) ^ (q + 1)) • b, ⟨by omega, ?_, ?_⟩, ?_⟩
  · have e : (d : ℤ) - q = p := by omega
    rw [e]
    exact ha
  · rw [hq]
    exact zsmul_mem hb _
  · funext s
    rw [kdUn_apply]
    simp only [join, boxC, Pi.smul_apply, map_zsmul]
    by_cases hc : (rgt s).card = q + 1
    · rw [hc]
    · have h0 : b (rgt s) = 0 := kd_cech_val hb (by omega)
      simp [h0]

private theorem kd_disj (A : Finset ι → Submodule ℂ E) (B : Finset ι → Submodule ℂ E') :
    Disjoint₂ (TensorProduct.mk ℂ E E') A B := by
  intro I J
  exact TensorProduct.map_injective_of_flat_flat (A I).subtype (B J).subtype
    (A I).injective_subtype (B J).injective_subtype

end

private theorem kdTw_mem_bicech_Z_of_mem_acx_Z {ι E E' : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    [AddCommGroup E'] [Module ℂ E'] (hU : WdUni) (A : Finset ι → Submodule ℂ E)
    (B : Finset ι → Submodule ℂ E') (d : ℕ) (t : Finset (ι ⊕ₗ ι) → E ⊗[ℂ] E')
    (ht : t ∈ (acx (mixF fun I J => Submodule.map₂ (TensorProduct.mk ℂ E E') (A I) (B J))
      fun _ => (1 : Module.End ℂ (E ⊗[ℂ] E'))).Z ((d : ℤ) + 2)) :
    kdTw t ∈ (bicech (TensorProduct.mk ℂ E E') A B).Z d := by
  unfold acx Cx.Z at ht
  dsimp only at ht
  simp only [Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_pi, Set.mem_univ,
    true_implies] at ht
  obtain ⟨ht1, ht2⟩ := ht
  unfold bicech Cx.Z
  dsimp only
  simp only [bicechC, Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_pi, Set.mem_univ,
    true_implies]
  refine ⟨?_, ?_⟩
  · rintro ⟨I, J⟩
    dsimp only
    have h := hU ι ι (E ⊗[ℂ] E') (fun _ => 1) t I J
    have hm := ht1 (uni I J)
    rw [h.2.2.2.1] at hm
    simp only [mixF, h.2.1, h.2.2.1] at hm
    simp only [kdTw]
    by_cases hc : I.Nonempty ∧ J.Nonempty ∧ ((I.card + J.card : ℕ) : ℤ) = (d : ℤ) + 2
    · rw [if_pos hc]
      rw [if_pos hc.2.2, if_pos ⟨hc.1, hc.2.1⟩] at hm
      exact zsmul_mem hm _
    · rw [if_neg hc]
      have h0 : t (uni I J) = 0 := by
        by_cases h1 : ((I.card + J.card : ℕ) : ℤ) = (d : ℤ) + 2
        · rw [if_pos h1, if_neg (fun h2 => hc ⟨h2.1, h2.2, h1⟩)] at hm
          simpa using hm
        · rw [if_neg h1] at hm
          simpa using hm
      rw [h0, smul_zero]
      exact Submodule.zero_mem _
  · rw [kd_biD_tw hU, ht2]
    funext x
    simp [kdTw]

private theorem kdUn_mem_acx_B_of_mem_bicech_B {ι E E' : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    [AddCommGroup E'] [Module ℂ E'] (hU : WdUni) (A : Finset ι → Submodule ℂ E)
    (B : Finset ι → Submodule ℂ E') (d : ℕ) (y : Finset ι × Finset ι → E ⊗[ℂ] E')
    (hy : y ∈ (bicech (TensorProduct.mk ℂ E E') A B).B d) :
    kdUn y ∈ (acx (mixF fun I J => Submodule.map₂ (TensorProduct.mk ℂ E E') (A I) (B J))
      fun _ => (1 : Module.End ℂ (E ⊗[ℂ] E'))).B ((d : ℤ) + 2) := by
  unfold bicech Cx.B at hy
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hy
  show kdUn (biD ℂ ι ι (E ⊗[ℂ] E') w) ∈ _
  rw [← kd_wd_un hU]
  unfold acx Cx.B
  refine Submodule.mem_map.2 ⟨kdUn w, ?_, rfl⟩
  dsimp only at hw ⊢
  simp only [bicechC, Submodule.mem_pi, Set.mem_univ, true_implies] at hw
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies]
  intro s
  rw [kdUn_apply]
  have h := hU ι ι (E ⊗[ℂ] E') (fun _ => 1) (fun _ => 0) (lft s) (rgt s)
  have hcs : s.card = (lft s).card + (rgt s).card := by
    rw [← h.2.2.2.1, h.2.2.2.2 s]
  have hw' := hw (lft s, rgt s)
  dsimp only at hw'
  by_cases hc : (lft s).Nonempty ∧ (rgt s).Nonempty ∧
      (((lft s).card + (rgt s).card : ℕ) : ℤ) = (d : ℤ) - 1 + 2
  · rw [if_pos hc] at hw'
    have hcard : ((s.card : ℕ) : ℤ) = (d : ℤ) + 2 - 1 := by
      rw [hcs]
      have := hc.2.2
      push_cast at this ⊢
      omega
    rw [if_pos hcard]
    simp only [mixF, if_pos (And.intro hc.1 hc.2.1)]
    exact zsmul_mem hw' _
  · rw [if_neg hc] at hw'
    have h0 : w (lft s, rgt s) = 0 := by simpa using hw'
    rw [h0, smul_zero]
    exact Submodule.zero_mem _

theorem UpperTheory.Gal.productCup_of_system.kunDec_of :
    WdUni → KunDec := by
  intro hU
  unfold KunDec
  intro ι E E' _ _ _ _ _ _ A B d hA hB t ht
  have hz := kdTw_mem_bicech_Z_of_mem_acx_Z hU A B d t ht
  obtain ⟨m, p, a, b, hab, hB'⟩ := UpperTheory.Cb.bicech_cohomology_kunneth_decomposition ℂ ι ι E E' (E ⊗[ℂ] E')
    (TensorProduct.mk ℂ E E') A B hA hB (kd_disj A B) (d : ℤ) (kdTw t) hz
  have hs := fun l => kd_single (TensorProduct.mk ℂ E E') A B d (p l) (a l) (b l) (hab l).1 (hab l).2
  choose q a' b' hq hj using hs
  refine ⟨m, q, a', b', fun l => hq l, ?_⟩
  have key := kdUn_mem_acx_B_of_mem_bicech_B hU A B d _ hB'
  rw [map_sub, kdUn_tw hU, map_sum] at key
  have e : ∑ l, kdUn (boxC (TensorProduct.mk ℂ E E') (a l) (b l)) =
      ∑ l, join (TensorProduct.mk ℂ E E') (a' l) (b' l) :=
    Finset.sum_congr rfl fun l _ => (hj l).symm
  rw [e] at key
  exact key
