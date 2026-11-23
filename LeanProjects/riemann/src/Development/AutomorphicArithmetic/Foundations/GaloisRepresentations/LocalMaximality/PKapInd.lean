import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

namespace UpperTheory.Gal.productCup_of_system

private theorem wd_apply' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (w : ι → Module.End ℂ E) (c : Finset ι → E) (t : Finset ι) :
    wd w c t = ∑ i ∈ t, GlobalTheory.cubeSign t i • w i (c (t.erase i)) := by
  simp [wd, LinearMap.sum_apply]

private theorem map_detC' {S S' κ : Type} [CommRing S] [CommRing S'] [Algebra ℂ S] [Algebra ℂ S']
    [LinearOrder κ] {p : ℕ} (φ : S →ₐ[ℂ] S') (ρ : κ → Fin p → S) (s : Finset κ) :
    φ (detC ρ s) = detC (fun t b => φ (ρ t b)) s := by
  unfold detC
  split_ifs with h
  · rw [AlgHom.map_det]
    congr 1
  · simp

private def rho0 {d : ℕ} {K : Type} [Field K] (y : Fin (d + 1) → K) :
    Fin (d + 1) ⊕ₗ Mi d → Fin (d + 1) → K := fun t => Sum.elim (fun i => Pi.single i 1)
  (fun l m => (if m = (ofLex l).1 then y m * y (ofLex l).2 else 0) -
    if m = (ofLex l).2 then y m * y (ofLex l).1 else 0) (ofLex t)

private theorem map_rowMu {d : ℕ} {K S E : Type} [Field K] [Algebra ℂ K] [CommRing S] [Algebra ℂ S]
    [AddCommGroup E] [Module ℂ E] (T : Sys d S E) (π : S →ₐ[ℂ] K) (y : Fin (d + 1) → K)
    (hX : ∀ i, π (T.X i) = y i) (hY : ∀ i, π (T.Y i) = y i) (s : Finset (Fin (d + 1) ⊕ₗ Mi d)) :
    π (detC T.rowMu s) = detC (rho0 y) s := by
  rw [map_detC']
  congr 1
  funext t b
  rcases ht : ofLex t with i | l
  · simp only [Sys.rowMu, rho0, ht, Sum.elim_inl, Pi.single_apply]
    split_ifs <;> simp
  · simp only [Sys.rowMu, rho0, ht, Sum.elim_inr, map_sub, apply_ite π, map_mul, hX, hY, map_zero]

private theorem map_mu {d : ℕ} {K S E : Type} [Field K] [Algebra ℂ K] [CommRing S] [Algebra ℂ S]
    [AddCommGroup E] [Module ℂ E] (T : Sys d S E) (π : S →ₐ[ℂ] K) (y : Fin (d + 1) → K)
    (hX : ∀ i, π (T.X i) = y i) (hY : ∀ i, π (T.Y i) = y i) (l : Mi d) : π (T.mu l) = 0 := by
  simp only [Sys.mu, map_sub, map_mul, hX, hY]
  ring

private theorem ind_of {d : ℕ} {K S E : Type} [Field K] [Algebra ℂ K] [CommRing S] [Algebra ℂ S]
    [AddCommGroup E] [Module ℂ E] (hM : ThMu) (hU : WdUni) (T : Sys d S E) (π : S →ₐ[ℂ] K)
    (y : Fin (d + 1) → K) (hX : ∀ i, π (T.X i) = y i) (hY : ∀ i, π (T.Y i) = y i)
    (i : Fin (d + 1)) (L : Finset (Mi d)) :
    π (detC T.rowMu (uni {i} L)) = π (detC T.rowMu (uni {0} L)) := by
  by_cases h : i = 0
  · rw [h]
  have h0 : (0 : Fin (d + 1)) ≠ i := fun e => h e.symm
  have h1 := congrFun (hM d S E T).1 (uni {0, i} L)
  rw [(hU _ _ _ _ _ {0, i} L).1] at h1
  have hl : wd (fun j : Fin (d + 1) => (Algebra.lmul ℂ S) (app (fun _ => 1) T.mu (inlE j : Fin (d + 1) ⊕ₗ Mi d)))
      (fun b' => detC T.rowMu (uni b' L)) {0, i} =
      detC T.rowMu (uni {i} L) - detC T.rowMu (uni {0} L) := by
    have e0 : ({0, i} : Finset (Fin (d + 1))).erase 0 = {i} := by
      ext a; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨ha, hb | hb⟩
        · exact absurd hb ha
        · exact hb
      · rintro rfl; exact ⟨h, Or.inr rfl⟩
    have ei : ({0, i} : Finset (Fin (d + 1))).erase i = {0} := by
      ext a; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨ha, hb | hb⟩
        · exact hb
        · exact absurd hb ha
      · rintro rfl; exact ⟨h0, Or.inl rfl⟩
    have s0 : GlobalTheory.cubeSign ({0, i} : Finset (Fin (d + 1))) 0 = 1 := by
      simp [GlobalTheory.cubeSign, Finset.filter_eq_empty_iff]
    have si : GlobalTheory.cubeSign ({0, i} : Finset (Fin (d + 1))) i = -1 := by
      have hp : (0 : Fin (d + 1)) < i := Fin.pos_iff_ne_zero.2 h
      have : ({0, i} : Finset (Fin (d + 1))).filter (· < i) = {0} := by
        ext a; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl, hb⟩
          · rfl
          · exact absurd hb (lt_irrefl _)
        · rintro rfl; exact ⟨Or.inl rfl, hp⟩
      simp [GlobalTheory.cubeSign, this]
    rw [wd_apply', Finset.sum_pair h0, e0, ei, s0, si]
    simp [app, inlE, sub_eq_add_neg, add_comm]
  have hr : π (wd (fun l : Mi d => (Algebra.lmul ℂ S) (app (fun _ => 1) T.mu (inrE l : Fin (d + 1) ⊕ₗ Mi d)))
      (fun L' => detC T.rowMu (uni {0, i} L')) L) = 0 := by
    rw [wd_apply', map_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    have : app (fun _ : Fin (d + 1) => (1 : S)) T.mu (inrE l : Fin (d + 1) ⊕ₗ Mi d) = T.mu l := by simp [app, inrE]
    rw [map_zsmul]
    simp [this, map_mu T π y hX hY l]
  rw [hl] at h1
  have h2 := congrArg π h1
  rw [map_add, map_zsmul, hr, smul_zero, add_zero, map_sub] at h2
  simpa [sub_eq_zero] using h2

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.kapInd_of :
    ThMu → WdUni → KapInd := by
  intro hM hU F K _ _ _ _ _ _ d x _ S E _ _ _ _ T π hX hY i L _
  have hZ : ∀ j, Algebra.TensorProduct.lmul' ℂ ((sysZ K x 0).X j : K ⊗[ℂ] K) = algebraMap F K (x j) := by
    intro j; simp [sysZ]
  have hZ' : ∀ j, Algebra.TensorProduct.lmul' ℂ ((sysZ K x 0).Y j : K ⊗[ℂ] K) = algebraMap F K (x j) := by
    intro j; simp [sysZ]
  rw [ind_of hM hU T π _ hX hY i L, kap,
    map_rowMu T π (fun j => algebraMap F K (x j)) hX hY,
    map_rowMu (sysZ K x 0) (Algebra.TensorProduct.lmul' ℂ) (fun j => algebraMap F K (x j)) hZ hZ']
