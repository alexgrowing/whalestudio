import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem exists_conj_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : OpenSubgroup G) (s : Finset G) : ∃ U₁ : OpenSubgroup G, ∀ u ∈ U₁, ∀ x ∈ s, x⁻¹ * u * x ∈ U := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, by simp⟩
  | insert a s _ ih =>
    obtain ⟨V, hV⟩ := ih
    have hc : Continuous (MulAut.conj a⁻¹).toMonoidHom := by
      change Continuous fun u : G => a⁻¹ * u * a⁻¹⁻¹
      fun_prop
    refine ⟨V ⊓ U.comap (MulAut.conj a⁻¹).toMonoidHom hc, fun u hu x hx => ?_⟩
    obtain ⟨h1, h2⟩ := OpenSubgroup.mem_inf.1 hu
    rcases Finset.mem_insert.1 hx with rfl | hx
    · have h3 : x⁻¹ * u * x⁻¹⁻¹ ∈ U := OpenSubgroup.mem_comap.1 h2
      rwa [inv_inv] at h3
    · exact hV u h1 x hx

private theorem supN_one {R : Type} [CommRing R] {n : ℕ} : supN (1 : Matrix (Fin n) (Fin n) R) = 0 := by
  unfold supN
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h
  · exact Matrix.one_apply_ne (by rintro rfl; omega)
  · rfl

private theorem rowM_one {R : Type} [CommRing R] {n : ℕ} (m : Fin n) :
    rowM m ((1 : Matrix (Fin n) (Fin n) R) m) = 1 := by
  ext i j
  simp only [rowM, Matrix.of_apply]
  split_ifs with h
  · rw [h.1]
  · rfl

private theorem isWh_comb {R : Type} [CommRing R] {n : ℕ} {ψ : R → ℂ} {W : GL (Fin n) R → ℂ} (hW : IsWh ψ W)
    (c : GL (Fin n) R →₀ ℂ) : IsWh ψ (comb c W) := by
  intro ν hν g
  unfold comb
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [mul_assoc, hW ν hν]
  ring

theorem UpperTheory.V.Af.Smo.locKir :
    UpperTheory.V.Af.Smo.ColConj → UpperTheory.V.Af.Smo.RowStep → UpperTheory.V.Af.Smo.LocStep → UpperTheory.V.Af.Smo.LocKir := by
  classical
  intro hcol hrow hstep E _ _ w ψ h0 h1 n m hm U
  induction m with
  | zero =>
    refine ⟨Finsupp.single 1 1, fun p => ψ (supN p.val), ?_, fun W hW _ p hp => ?_⟩
    · simp only [Units.val_one, supN_one, AddChar.map_zero_eq_one]
    · unfold comb
      rw [Finsupp.sum_single_index (by simp), one_mul, hW p hp]
  | succ m ih =>
    obtain ⟨c₀, H₀, hH₀, hc₀⟩ := ih (by omega)
    obtain ⟨U₁, hU₁⟩ := exists_conj_le U c₀.support
    let m' : Fin n := ⟨m, by omega⟩
    obtain ⟨c₁, h, hh1, hh, hc₁⟩ := hstep E w ψ h0 h1 n m' hm U₁
    obtain ⟨c, -, hc⟩ := exists_comb_comb c₁ c₀
    have hσ : ∃ σ : (Fin n → w.adicCompletion E) → GL (Fin n) (w.adicCompletion E),
        ∀ ξ (s : GL (Fin n) (w.adicCompletion E)), s.val = rowM m' ξ → σ ξ = s := by
      refine ⟨fun ξ => if e : ∃ s : GL (Fin n) (w.adicCompletion E), s.val = rowM m' ξ then e.choose else 1,
        fun ξ s hs => ?_⟩
      have e : ∃ s : GL (Fin n) (w.adicCompletion E), s.val = rowM m' ξ := ⟨s, hs⟩
      simp only [dif_pos e]
      exact Units.ext (e.choose_spec.trans hs.symm)
    obtain ⟨σ, hσ⟩ := hσ
    refine ⟨c, fun p => h (p.val m') * H₀ (p * (σ (p.val m'))⁻¹), ?_, fun W hW hWU p hp => ?_⟩
    · have : σ ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) m') = 1 := hσ _ 1 (rowM_one m').symm
      simp only [Units.val_one, hh1, this, inv_one, mul_one, one_mul, hH₀]
    · have hinv : ∀ g, ∀ u ∈ U₁, comb c₀ W (g * u) = comb c₀ W g := by
        intro g u hu
        unfold comb
        refine Finsupp.sum_congr fun x hx => ?_
        rw [← hWU (g * x) _ (hU₁ u hu x hx)]
        congr 2
        group
      rw [hc, hc₁ (comb c₀ W) hinv p (p.val m') ?_]
      · by_cases hz : h (p.val m') = 0
        · simp only [hz, zero_mul]
        · obtain ⟨s, hsU, hs⟩ := hh _ hz
          simp only [hσ _ s hs]
          rw [← hinv p s⁻¹ (U₁.inv_mem hsU), hc₀ W hW hWU _ (hrow _ n m' p s hp hs), mul_assoc]
      · intro u t ht
        obtain ⟨ν, hν, e1, e2⟩ := hcol _ n m' hm p hp u
        have e : p * t = ν * p := Units.ext (by rw [Units.val_mul, Units.val_mul, ht, e2])
        rw [e, isWh_comb hW c₀ ν hν, e1]
