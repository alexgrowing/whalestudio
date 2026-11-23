import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaCellsDisjointOffFinset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipMulMemCell
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.WhitRed

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem compV_eq (w : HeightOneSpectrum (𝓞 E)) (x : GA E n) :
    GlobalTheory.CellDec.compV E n w x = GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) x) :=
  Units.ext (Matrix.ext fun _ _ => rfl)

theorem map_pLoc_prod_of_notMem (f : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin n) (w.adicCompletion E))
    (v : HeightOneSpectrum (𝓞 E)) : ∀ L : List (HeightOneSpectrum (𝓞 E)), v ∉ L →
    GeneralLinearGroup.map (pLoc E v) (L.map fun w => locGL E n w (f w)).prod = 1
  | [], _ => by simp
  | w :: L, h => by
    rw [List.mem_cons, not_or] at h
    rw [List.map_cons, List.prod_cons, map_mul, map_pLoc_prod_of_notMem f v L h.2, pLoc_locGL_of_ne h.1, one_mul]

theorem map_pLoc_prod_of_mem (f : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin n) (w.adicCompletion E))
    (v : HeightOneSpectrum (𝓞 E)) : ∀ L : List (HeightOneSpectrum (𝓞 E)), L.Nodup → v ∈ L →
    GeneralLinearGroup.map (pLoc E v) (L.map fun w => locGL E n w (f w)).prod = f v
  | [], _, h => absurd h List.not_mem_nil
  | w :: L, hL, h => by
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, map_mul]
    by_cases hv : v = w
    · subst hv
      rw [pLoc_locGL, map_pLoc_prod_of_notMem f v L hL.1, mul_one]
    · rw [pLoc_locGL_of_ne hv, one_mul]
      exact map_pLoc_prod_of_mem f v L hL.2 ((List.mem_cons.1 h).resolve_left hv)

theorem row_mul_inv {R : Type} [CommRing R] {a : ℕ} (A B : GL (Fin a) R) (i : Fin a)
    (h : ∀ j, A.val i j = B.val i j) (j : Fin a) : (A * B⁻¹).val i j = (1 : Matrix (Fin a) (Fin a) R) i j := by
  have e : (A * B⁻¹).val i j = (B * B⁻¹).val i j := by
    simp only [Units.val_mul, Matrix.mul_apply, h]
  rw [e, mul_inv_cancel, Units.val_one]

variable [IsTotallyComplex E]

theorem compV_infGL (w : HeightOneSpectrum (𝓞 E)) (y : GL (Fin n) (Cinf E)) :
    GlobalTheory.CellDec.compV E n w (infGL E n y) = 1 := by
  rw [compV_eq, pFin_infGL, map_one]

theorem comm_of_supp {x y : GA E n} (hinf : GeneralLinearGroup.map (pInf E) x = 1)
    (hw : ∀ w, GlobalTheory.CellDec.compV E n w x = 1 ∨ GlobalTheory.CellDec.compV E n w y = 1) : x * y = y * x := by
  refine ga_ext (by rw [map_mul, map_mul, hinf, one_mul, mul_one]) (GlobalTheory.CellDec.GL_ext_pLoc fun w => ?_)
  rw [map_mul, map_mul, map_mul, map_mul, ← compV_eq, ← compV_eq]
  rcases hw w with h | h <;> rw [h] <;> simp

end GlobalTheory.WhitRed

open GlobalTheory.WhitRed in

theorem GlobalTheory.WhitRed.exists_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (F : GA E (m + 1) → ℂ)
    (U : Subgroup (GL (Fin (m + 1)) (Af E))) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
    (∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g) →
    (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g) →
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    (∀ y : Fin (m + 1) → Af E, y - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ κ ∈ U, (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
        ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
          pLoc E w (y j)) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, IsUnit (pInf E (g.val (Fin.last m) (Fin.last m))) →
      (fun i => pFin E (g.val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ p ∈ GlobalTheory.JSW.mirS E T m, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T,
        ‖GlobalTheory.JSW.whit F (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g *
          (infGL E (m + 1) (GlobalTheory.RSTheta.rowGL (Fin.last m) (fun i => pInf E (g.val (Fin.last m) i))))⁻¹)‖ =
        ‖GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l.1)‖ := by
  intro E _ _ _ m T ϖ F U J hU hK hN hκ g hg hu hy
  obtain ⟨u₁, hu₁, k, hk, he⟩ := hg
  have hrow : ∀ j, g.val (Fin.last m) j = k.val (Fin.last m) j := by
    intro j
    obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu₁
    rw [he, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
    · rw [h2, one_mul]
    · intro i _ hi
      rw [h1 _ _ (lt_of_le_of_ne (Fin.le_last i) hi), zero_mul]
    · simp
  have hσrow : ∀ j, (GlobalTheory.RSTheta.rowGL (Fin.last m) (fun i => pInf E (g.val (Fin.last m) i))).val (Fin.last m) j =
      pInf E (g.val (Fin.last m) j) := by
    intro j
    have := congrFun (GlobalTheory.RSTheta.single_vecMul_rowGL (ℓ := Fin.last m) (y := fun i => pInf E (g.val (Fin.last m) i)) hu) j
    rwa [Matrix.single_one_vecMul] at this
  generalize GlobalTheory.RSTheta.rowGL (Fin.last m) (fun i => pInf E (g.val (Fin.last m) i)) = σ at hσrow ⊢
  obtain ⟨κ, hκU, hκoff, hκT⟩ := hκ _ hy
  obtain ⟨hf, hhf⟩ : ∃ hf : GL (Fin (m + 1)) (Af E),
      hf = (T.toList.map fun w => locGL E (m + 1) w (GlobalTheory.CellDec.compV E (m + 1) w k)).prod := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : GA E (m + 1), h = infGL E (m + 1) (GeneralLinearGroup.map (pInf E) k) * finGL E (m + 1) hf :=
    ⟨_, rfl⟩
  have hhinf : GeneralLinearGroup.map (pInf E) h = GeneralLinearGroup.map (pInf E) k := by
    rw [hh, map_mul, pInf_infGL, pInf_finGL, mul_one]
  have hhon : ∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w h = GlobalTheory.CellDec.compV E (m + 1) w k := by
    intro w hw
    rw [hh, map_mul, compV_infGL, one_mul, GlobalTheory.CellDec.compV_finGL, hhf,
      map_pLoc_prod_of_mem _ w _ T.nodup_toList (Finset.mem_toList.2 hw)]
  have hhoff : ∀ w ∉ T, GlobalTheory.CellDec.compV E (m + 1) w h = 1 := by
    intro w hw
    rw [hh, map_mul, compV_infGL, one_mul, GlobalTheory.CellDec.compV_finGL, hhf,
      map_pLoc_prod_of_notMem _ w _ (fun h' => hw (Finset.mem_toList.1 h'))]
  have hkT : h⁻¹ * k ∈ GlobalTheory.CellDec.US E (m + 1) T := by
    rw [GlobalTheory.CellDec.mem_US] at hk ⊢
    intro v hv
    rw [map_mul, map_inv, hhoff v hv, inv_one, one_mul]
    exact hk v hv
  have hkTinf : GeneralLinearGroup.map (pInf E) (h⁻¹ * k) = 1 := by
    rw [map_mul, map_inv, hhinf, inv_mul_cancel]
  have hkTT : ∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w (h⁻¹ * k) = 1 := by
    intro w hw
    rw [map_mul, map_inv, hhon w hw, inv_mul_cancel]
  obtain ⟨p, hp⟩ : ∃ p : GA E (m + 1), p = h * (infGL E (m + 1) σ)⁻¹ * (finGL E (m + 1) κ)⁻¹ := ⟨_, rfl⟩
  have hpoff : ∀ w ∉ T, GlobalTheory.CellDec.compV E (m + 1) w p = 1 := by
    intro w hw
    rw [hp, map_mul, map_mul, map_inv, map_inv, hhoff w hw, compV_infGL, GlobalTheory.CellDec.compV_finGL, hκoff w hw]
    simp
  refine ⟨p, ⟨fun w hw => hpoff w hw, fun j => ?_⟩, fun l => ?_⟩
  · apply ad_ext
    · have e1 : pInf E (p.val (Fin.last m) j) = (GeneralLinearGroup.map (pInf E) p).val (Fin.last m) j := rfl
      have e2 : GeneralLinearGroup.map (pInf E) p = GeneralLinearGroup.map (pInf E) k * σ⁻¹ := by
        rw [hp, map_mul, map_mul, map_inv, map_inv, hhinf, pInf_infGL, pInf_finGL, inv_one, mul_one]
      have hkr : ∀ j, (GeneralLinearGroup.map (pInf E) k).val (Fin.last m) j = σ.val (Fin.last m) j := by
        intro j
        rw [hσrow, hrow]
        rfl
      rw [e1, e2, row_mul_inv _ _ _ hkr]
      by_cases hj : j = Fin.last m
      · subst hj; simp
      · rw [if_neg hj, map_zero, Matrix.one_apply_ne (Ne.symm hj)]
    · refine IsDedekindDomain.FiniteAdeleRing.ext _ fun w => ?_
      change (GlobalTheory.CellDec.compV E (m + 1) w p).val (Fin.last m) j =
        pLoc E w (pFin E (if j = Fin.last m then (1 : Ad E) else 0))
      have eR : pLoc E w (pFin E (if j = Fin.last m then (1 : Ad E) else 0)) =
          (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j := by
        by_cases hj : j = Fin.last m
        · subst hj; simp
        · rw [if_neg hj, map_zero, map_zero, Matrix.one_apply_ne (Ne.symm hj)]
      rw [eR]
      by_cases hw : w ∈ T
      · have e2 : GlobalTheory.CellDec.compV E (m + 1) w p =
            GlobalTheory.CellDec.compV E (m + 1) w k * (GeneralLinearGroup.map (pLoc E w) κ)⁻¹ := by
          rw [hp, map_mul, map_mul, map_inv, map_inv, hhon w hw, compV_infGL, GlobalTheory.CellDec.compV_finGL, inv_one, mul_one]
        rw [e2]
        refine row_mul_inv _ _ _ (fun j => ?_) j
        rw [hκT w hw j]
        show pLoc E w (pFin E (k.val _ _)) = _
        rw [← hrow]
      · rw [hpoff w hw]
        rfl
  · obtain ⟨t, ht⟩ : ∃ t : GA E (m + 1), t = GlobalTheory.CellDec.tl (m + 1) ϖ l.1 := ⟨_, rfl⟩
    rw [← ht]
    have htinf : GeneralLinearGroup.map (pInf E) t = 1 := by
      rw [ht, GlobalTheory.CellDec.tl]
      exact pInf_finGL _
    have htT : ∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w t = 1 := by
      intro w hw
      rw [ht, GlobalTheory.CellDec.compV_tl, l.2 w hw, GlobalTheory.IwaCell.tD_zero]
    have hc1 : (h⁻¹ * k) * (infGL E (m + 1) σ)⁻¹ = (infGL E (m + 1) σ)⁻¹ * (h⁻¹ * k) :=
      comm_of_supp hkTinf fun w => Or.inr (by rw [map_inv, compV_infGL, inv_one])
    have hc2 : t * p = p * t := comm_of_supp htinf fun w => by
      by_cases hw : w ∈ T
      · exact Or.inl (htT w hw)
      · exact Or.inr (hpoff w hw)
    have hp' : h * (infGL E (m + 1) σ)⁻¹ = p * finGL E (m + 1) κ := by
      rw [hp, inv_mul_cancel_right]
    have key : t * g * (infGL E (m + 1) σ)⁻¹ =
        (t * u₁ * t⁻¹) * ((p * t * finGL E (m + 1) κ) * (h⁻¹ * k)) := by
      calc t * g * (infGL E (m + 1) σ)⁻¹ = t * u₁ * (h * ((h⁻¹ * k) * (infGL E (m + 1) σ)⁻¹)) := by
            rw [he]; group
        _ = t * u₁ * ((h * (infGL E (m + 1) σ)⁻¹) * (h⁻¹ * k)) := by rw [hc1]; group
        _ = t * u₁ * t⁻¹ * ((t * p) * finGL E (m + 1) κ * (h⁻¹ * k)) := by rw [hp']; group
        _ = _ := by rw [hc2]
    have hu₁' : t * u₁ * t⁻¹ ∈ GlobalTheory.CellDec.NA E (m + 1) := by
      rw [ht]; exact GlobalTheory.CellDec.tl_conj_mem ϖ l.1 hu₁
    rw [key, hN _ hu₁', hK _ hkT hkTinf hkTT, hU κ hκU]
