import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 GlobalTheory.W1.Lef UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

namespace UpperTheory.Gal.productCup_of_system

section
variable {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L] [IsScalarTower ℂ F L] {d : ℕ}

private theorem locCoch_mem_Z (x : Fin (d + 1) → Fˣ) (h : L) (hh : h ∈ rB ℂ L (xv x) Finset.univ) :
    locCoch ℂ L (xv x) h ∈ (omCx (rB ℂ L (xv x)) d).Z d := by
  have ht : ∀ j : Fin d, algebraMap F L ((x j.succ : F) / x 0) ∈ rB ℂ L (xv x) Finset.univ := fun j =>
    (integralClosure (rA ℂ (xv x) Finset.univ) L).algebraMap_mem
      ⟨(x j.succ : F) / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_univ _, j.succ, rfl⟩⟩
  have hti : ∀ j : Fin d, (algebraMap F L ((x j.succ : F) / x 0))⁻¹ ∈ rB ℂ L (xv x) Finset.univ := fun j => by
    have := (integralClosure (rA ℂ (xv x) Finset.univ) L).algebraMap_mem
      ⟨(x 0 : F) / x j.succ, Algebra.subset_adjoin ⟨j.succ, Finset.mem_univ _, 0, rfl⟩⟩
    rw [← map_inv₀, inv_div]
    exact this
  refine ⟨?_, ?_⟩
  · show _ ∈ cechC _ _
    rw [cechC, Submodule.mem_pi]
    intro s _
    by_cases hs : s = Finset.univ
    · subst hs
      rw [if_pos ⟨Finset.univ_nonempty, by simp⟩]
      have hv : locCoch ℂ L (xv x) h Finset.univ = (h * ∏ j : Fin d, (algebraMap F L ((x j.succ : F) / x 0))⁻¹) •
          ExteriorAlgebra.ιMulti L d fun j => D ℂ L (algebraMap F L ((x j.succ : F) / x 0)) := by
        rw [locCoch, if_pos rfl, vol0, mul_smul]
        congr 1
        exact (ExteriorAlgebra.ιMulti L d).toMultilinearMap.map_smul_univ _ _
      rw [hv]
      exact Submodule.subset_span ⟨_, mul_mem hh (prod_mem fun j _ => hti j), _, ht, rfl⟩
    · have : locCoch ℂ L (xv x) h s = 0 := if_neg hs
      rw [this]
      exact zero_mem _
  · refine LinearMap.mem_ker.2 ?_
    funext t
    show GlobalTheory.DI.delta _ t = 0
    unfold GlobalTheory.DI.delta
    refine Finset.sum_eq_zero fun i hi => ?_
    have : locCoch ℂ L (xv x) h (t.erase i) = 0 := if_neg fun h' => by
      have := Finset.mem_univ i
      rw [← h'] at this
      exact Finset.notMem_erase i t this
    simp [this]

private theorem pk_single (i : Fin (d + 1)) : pk ({i} : Finset (Fin (d + 1))) = i := by
  simp [pk]

end

section
variable {β κ₁ κ₂ : Type} [LinearOrder β] [LinearOrder κ₁] [LinearOrder κ₂]

private theorem map_inlE (L : Finset κ₁) : L.map (inlE : κ₁ ↪o κ₁ ⊕ₗ κ₂).toEmbedding = uni L ∅ := by
  ext t
  simp only [uni, inlE, Finset.mem_map, Finset.mem_disjSum, Finset.notMem_empty]
  simp

private theorem prod_u {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
    (n : κ₂ → ℕ × ℕ) (L : Finset κ₁) (i j : Fin (d + 1)) :
    ∏ l ∈ uni L (∅ : Finset κ₂), T.u (app n11 n) i j l = (T.X i * T.Y j) ^ L.card := by
  rw [← map_inlE, Finset.prod_map]
  have : ∀ l : κ₁, T.u (app n11 n) i j ((inlE : κ₁ ↪o κ₁ ⊕ₗ κ₂).toEmbedding l) = T.X i * T.Y j := fun l => by
    simp [Sys.u, app, n11, inlE]
  rw [Finset.prod_congr rfl fun l _ => this l, Finset.prod_const]

end

section
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → Fˣ)

private theorem valuation_power_identity {K : Type} [Field K] (e P X : K) (d : ℕ) (hX : X ≠ 0) (he : e * (-1) ^ d = 1) :
    e * ((X * X) ^ d)⁻¹ * ((-1) ^ d * (P * X ^ d)) = P / X ^ d := by
  have h1 : X ^ d ≠ 0 := pow_ne_zero _ hX
  rw [mul_pow]
  calc _ = (e * (-1) ^ d) * (P * (X ^ d * (X ^ d * X ^ d)⁻¹)) := by ring
    _ = _ := by
      rw [he, one_mul]
      field_simp

private theorem lmul_X (a : ℕ) (i : Fin (d + 1)) :
    Algebra.TensorProduct.lmul' ℂ (((sysZ K x a).X i : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) = algebraMap F K (x i) := by
  simp [sysZ]

private theorem lmul_Y (a : ℕ) (i : Fin (d + 1)) :
    Algebra.TensorProduct.lmul' ℂ (((sysZ K x a).Y i : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) = algebraMap F K (x i) := by
  simp [sysZ]

private theorem kap_dj (hTh : ThMu) :
    kap K x (img (dj (0 : Fin (d + 1)))) = (∏ l : Fin d, algebraMap F K (x l.succ)) * algebraMap F K (x 0) ^ d := by
  unfold kap
  rw [(hTh d (K ⊗[ℂ] K) (DR ℂ K ⊗[ℂ] DR ℂ K) (sysZ K x 0)).2.2.2]
  simp only [map_mul, map_prod, map_pow, lmul_X, lmul_Y]

private theorem omG_zero : algebraMap F K (omG x 0) =
    (∏ l : Fin d, algebraMap F K (x l.succ)) / algebraMap F K (x 0) ^ d := by
  have h0 : algebraMap F K (x 0) ≠ 0 := by simp
  rw [omG, Fin.prod_univ_succ, div_self (x 0).ne_zero, one_mul, map_prod]
  simp only [map_div₀]
  rw [Finset.prod_div_distrib]
  simp

end

theorem yMain_of :
    ValG → YBig → YCmpT → YCmpG → GMap → CRT → ThMu → KapInd → ActsLin → DtBasic → SysBasic → RYBasic → OmLoc → WdUni → YMain := by
  intro hVal hBig hCT hCG hG hCRT hTh _ hAL _ hSB hRY _ hWU F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A hY τ hτ a ha κ _ _ n z hz c hc hD
  classical
  obtain ⟨-, hcrt⟩ := hCRT F K' d x hY.covY
  obtain ⟨h, hh⟩ := hcrt fun e => if e ∈ Fx then locTerm (A e) a else 0
  have hoff : ∀ e : fib ℂ K' (xv x), e ∉ Fx → e.1 h = 0 := fun e he => by rw [hh, if_neg he]
  have hon : ∀ e ∈ Fx, e.1 h = locTerm (A e) a := fun e he => by rw [hh, if_pos he]
  have hsum : ∑ᶠ e : fib ℂ K' (xv x), e.1 h = ∑ e ∈ Fx, locTerm (A e) a := by
    rw [finsum_eq_sum_of_support_subset (s := Fx) _ fun e he => ?_]
    · exact Finset.sum_congr rfl hon
    · by_contra hn
      exact he (hoff e hn)
  have hloc : locCoch ℂ K' (xv x) h ∈ (omCx (rB ℂ K' (xv x)) d).Z d := by
    obtain ⟨h1, -, h3, -⟩ := hRY F K K' d x j2 hY.toY0
    refine locCoch_mem_Z x _ ?_
    have := h3 {0} Finset.univ ∅ ∅ (Finset.subset_univ _) subset_rfl
    rw [h1, h1] at this
    exact this h.2
  refine ⟨h, ?_, hloc, hsum⟩
  have hlr : ∀ {β γ : Type} [LinearOrder β] [LinearOrder γ] (b : Finset β) (L : Finset γ),
      lft (uni b L) = b ∧ rgt (uni b L) = L ∧ (uni b L).card = b.card + L.card := fun b L =>
    ⟨(hWU _ _ ℂ 0 0 b L).2.1, (hWU _ _ ℂ 0 0 b L).2.2.1, (hWU _ _ ℂ 0 0 b L).2.2.2.1⟩
  have hcardI : (img (dj (0 : Fin (d + 1)))).card = d := by simp [img]
  have hcard0 : (uni (img (dj (0 : Fin (d + 1)))) (∅ : Finset κ)).card = d := by
    rw [(hlr _ _).2.2, hcardI]; simp
  set L0 : Finset (Mi d ⊕ₗ κ) := uni (img (dj (0 : Fin (d + 1)))) ∅ with hL0
  set c0 := c (uni (uni {0} {0}) L0) with hc0

  have hcol := ((hSB d _ _ (sysZ K x a) (Mi d ⊕ₗ κ) (app n11 n) (app (sysZ K x a).mu z) ((d : ℤ) + 2)).2.1 c).1 hc.1 {0} {0}
  rw [if_pos ⟨Finset.singleton_nonempty _, Finset.singleton_nonempty _⟩] at hcol
  have h3 : c0 ∈ ((sysZ K x a).M {0} {0}).map ((sysZ K x a).act
      ((∏ l ∈ L0, (sysZ K x a).u (app n11 n) (pk {0}) (pk {0}) l : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K)) := by
    have := hcol L0 (Set.mem_univ _)
    dsimp only at this
    rw [SetLike.mem_coe, if_pos (by rw [hcard0]; simp; ring)] at this
    exact this
  rw [pk_single, hL0, prod_u, hcardI] at h3
  obtain ⟨m', hm', hm'eq⟩ := h3

  set U : (K ⊗[ℂ] K)ˣ := ((sysZ K x a).X 0 * (sysZ K x a).Y 0) ^ d with hU
  have hm'eq' : actZ K (U : K ⊗[ℂ] K) m' = c0 := hm'eq
  set ε : ℂ := (-1) ^ d with hε
  have hεε : ε * ε = 1 := by rw [hε, ← mul_pow]; simp
  set s0 : K ⊗[ℂ] K := algebraMap ℂ _ ε * ((U⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) with hs0
  have hm_eq : actZ K s0 c0 = ε • m' := by
    rw [← hm'eq', ← Module.End.mul_apply, ← map_mul, hs0, mul_assoc, Units.inv_mul, mul_one, AlgHom.commutes,
      Module.algebraMap_end_apply]
  have hmM : actZ K s0 c0 ∈ (sysZ K x a).M {0} {0} := by
    rw [hm_eq]
    exact Submodule.smul_mem _ _ hm'
  have hdiag : Acts (F := F) K τ a c0 ((-1) ^ d * kap K x (img (dj (0 : Fin (d + 1))))) := by
    have := hD 0 0 (img (dj 0)) hcardI
    have he : resK inlE c (uni (uni {0} {0}) (img (dj (0 : Fin (d + 1))))) = c0 := by
      show c (uni (lft _) ((rgt _).map _)) = _
      rw [(hlr _ _).1, (hlr _ _).2.1, map_inlE]
    rwa [he] at this
  have hact := (hAL F K d x hY.covZ τ hτ a).2.1 _ _ s0 hdiag
  have hX0 : algebraMap F K (x 0) ≠ 0 := by simp
  have hlU : Algebra.TensorProduct.lmul' ℂ ((U⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) * (algebraMap F K (x 0) * algebraMap F K (x 0)) ^ d = 1 := by
    have h1 : Algebra.TensorProduct.lmul' ℂ (U : K ⊗[ℂ] K) = (algebraMap F K (x 0) * algebraMap F K (x 0)) ^ d := by
      rw [hU, Units.val_pow_eq_pow_val, map_pow, Units.val_mul, map_mul, lmul_X, lmul_Y]
    rw [← h1, ← map_mul, Units.inv_mul, map_one]
  have hval : Algebra.TensorProduct.lmul' ℂ s0 * ((-1) ^ d * kap K x (img (dj (0 : Fin (d + 1))))) = algebraMap F K (omG x 0) := by
    have hε' : algebraMap ℂ K ε * (-1) ^ d = 1 := by
      rw [hε, map_pow, map_neg, map_one, ← mul_pow]; simp
    rw [hs0, map_mul, AlgHom.commutes, kap_dj x hTh, omG_zero]
    have hi : Algebra.TensorProduct.lmul' ℂ ((U⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) = ((algebraMap F K (x 0) * algebraMap F K (x 0)) ^ d)⁻¹ :=
      eq_inv_of_mul_eq_one_left hlU
    rw [hi]
    exact valuation_power_identity _ _ _ d hX0 hε'
  rw [hval] at hact
  obtain ⟨s, hs1, hs2⟩ := hVal F K K' d x j2 Fx A hY τ hτ a ha _ hmM hact
  obtain ⟨gmu, gact, -, -, gZ⟩ := hG F K K' d x j2 hY.toY0 a ha
  have hgG : (fun l => gS j2 (app (sysZ K x a).mu z l)) = gG x j2 z := by
    funext t
    show gS j2 (Sum.elim _ _ (ofLex t)) = Sum.elim _ _ (ofLex t)
    cases ofLex t with
    | inl l => exact gmu l
    | inr l => rfl
  have hc' : (fun t => gY j2 (c t)) ∈ ((sysY x j2 d).cx (app n11 n) (gG x j2 z)).Z ((d : ℤ) + 2) := by
    rw [← hgG]
    exact gZ (Mi d ⊕ₗ κ) (app n11 n) (app (sysZ K x a).mu z) ((d : ℤ) + 2) c hc
  have hgX : gS j2 (((sysZ K x a).X 0 : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) = algebraMap F K' (x 0) := by
    simp [sysZ, gS, ← IsScalarTower.algebraMap_apply]
  have hgY : gS j2 (((sysZ K x a).Y 0 : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) = j2 (algebraMap F K (x 0)) := by
    simp [sysZ, gS]
  have hc'v : gY j2 c0 = ((-1) ^ d * (algebraMap F K' (x 0) * j2 (algebraMap F K (x 0))) ^ d * s) • dtS K' x Finset.univ := by
    have ht : actZ K (algebraMap ℂ _ ε * (U : K ⊗[ℂ] K)) (actZ K s0 c0) = c0 := by
      rw [← Module.End.mul_apply, ← map_mul, hs0]
      have : algebraMap ℂ (K ⊗[ℂ] K) ε * (U : K ⊗[ℂ] K) * (algebraMap ℂ (K ⊗[ℂ] K) ε * ((U⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K)) = 1 := by
        rw [mul_mul_mul_comm, ← map_mul, hεε, map_one, one_mul, Units.mul_inv]
      rw [this, map_one, Module.End.one_apply]
    have hgU : gS j2 (algebraMap ℂ _ ε * (U : K ⊗[ℂ] K)) = (-1) ^ d * (algebraMap F K' (x 0) * j2 (algebraMap F K (x 0))) ^ d := by
      rw [map_mul, AlgHom.commutes, hU, Units.val_pow_eq_pow_val, Units.val_mul, map_pow (gS j2), map_mul (gS j2), hgX, hgY, hε]
      simp
    calc gY j2 c0 = gY j2 (actZ K (algebraMap ℂ _ ε * (U : K ⊗[ℂ] K)) (actZ K s0 c0)) := by rw [ht]
      _ = _ := by rw [gact, hs1, smul_smul, hgU]
  have hsv : ∀ e ∈ Fx, Val (rB ℂ K' (xv x) {0}) e.1 s (e.1 h * (1 - A e).det) := fun e he => by
    rw [hon e he, locTerm, div_mul_cancel₀ _ (hY.det e he)]
    exact hs2 e he
  obtain ⟨c1, hc1, hc1v, hc1z⟩ := hBig F K K' d x j2 Fx A hY κ n z hz h hoff
  have hCmp := hCG F K K' d x j2 Fx A hY κ n z hz h s hsv c1 hc1 hc1v _ hc' hc'v
  have hres := (hSB d _ _ (sysY x j2 d) ((Mi d ⊕ₗ κ) ⊕ₗ Fin d) (app (app n11 n) n10) (app (gG x j2 z) (gT x j2))
    ((d : ℤ) + 2)).2.2.2.2.2 (Fin d) inrE c1 hc1
  have e1 : (fun l : Fin d => app (app n11 n) n10 ((inrE : Fin d ↪o (Mi d ⊕ₗ κ) ⊕ₗ Fin d) l)) = n10 := funext fun l => rfl
  have e2 : (fun l : Fin d => app (gG x j2 z) (gT x j2) ((inrE : Fin d ↪o (Mi d ⊕ₗ κ) ⊕ₗ Fin d) l)) = gT x j2 := funext fun l => rfl
  rw [e1, e2] at hres
  have hres1 : resK (inrE : Fin d ↪o (Mi d ⊕ₗ κ) ⊕ₗ Fin d) c1 (uni (uni {0} {0}) Finset.univ) =
      ((-1) ^ d * algebraMap F K' (x 0) ^ d * (h : K')) • dtS K' x Finset.univ := by
    show c1 (uni (lft _) ((rgt _).map _)) = _
    rw [(hlr _ _).1, (hlr _ _).2.1]
    exact hc1v
  have hres2 : ∀ i j, (i ≠ 0 ∨ j ≠ 0) → col (resK (inrE : Fin d ↪o (Mi d ⊕ₗ κ) ⊕ₗ Fin d) c1) (uni {i} {j}) = 0 := fun i j hij => by
    funext L
    show c1 (uni (lft _) ((rgt _).map _)) = 0
    rw [(hlr _ _).1, (hlr _ _).2.1]
    exact congrFun (hc1z i j hij) _
  have hT := hCT F K K' d x j2 Fx A hY h hoff (resK (inrE : Fin d ↪o (Mi d ⊕ₗ κ) ⊕ₗ Fin d) c1) hres hres1 hres2
  have htop : top (resK (inrE : Fin d ↪o (Mi d ⊕ₗ κ) ⊕ₗ Fin d) c1) = top c1 := by
    funext b
    show c1 (uni (lft _) ((rgt _).map _)) = c1 _
    rw [(hlr _ _).1, (hlr _ _).2.1, Finset.map_empty]
  rw [htop] at hT
  have := add_mem hCmp hT
  rw [sub_add_sub_cancel] at this
  have hfin : top (fun t => gY j2 (c t)) = fun s => gY j2 (top c s) := rfl
  rw [hfin] at this
  exact this

end UpperTheory.Gal.productCup_of_system
