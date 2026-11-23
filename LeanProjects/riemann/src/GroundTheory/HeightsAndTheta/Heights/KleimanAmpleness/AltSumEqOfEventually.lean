import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraLast
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastMore
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideExtra
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreAlt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeMIdealOverGraph
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrLenPrimeOfEqFinrank
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

noncomputable section

section Poly

variable {K : Type}

theorem eval_bind₁_shift (p : MvPolynomial K ℚ) (a z : K → ℚ) :
    eval z (bind₁ (fun k => X k - C (a k)) p) = eval (z - a) p := by
  show eval₂Hom (RingHom.id ℚ) z _ = _
  rw [eval₂Hom_bind₁]
  have hfun : (fun i => eval₂Hom (RingHom.id ℚ) z (X i - C (a i))) = z - a := funext fun k => by simp
  rw [hfun]
  rfl

theorem altSum_eq_of_eventually (p : MvPolynomial K ℚ) {n : ℕ} (δ : Fin n → K → ℤ) (D : ℚ)
    (h : ∀ᶠ m : K → ℤ in atTop,
      ∑ T : Finset (Fin n), (-1 : ℚ) ^ T.card * eval (fun k => (((m - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p = D)
    (z : K → ℤ) :
    ∑ T : Finset (Fin n), (-1 : ℚ) ^ T.card * eval (fun k => (((z - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p = D := by
  classical
  let q : MvPolynomial K ℚ := ∑ T : Finset (Fin n),
    C ((-1 : ℚ) ^ T.card) * bind₁ (fun k => X k - C (((∑ i ∈ T, δ i) k : ℤ) : ℚ)) p
  have hq : ∀ w : K → ℤ, eval (fun k => (w k : ℚ)) q =
      ∑ T : Finset (Fin n), (-1 : ℚ) ^ T.card * eval (fun k => (((w - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p := by
    intro w
    simp only [q, map_sum, map_mul, eval_C, eval_bind₁_shift]
    refine Finset.sum_congr rfl fun T _ => ?_
    congr 3
    funext k
    simp
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp h
  let s : K → Set ℚ := fun k => (fun t : ℤ => (t : ℚ)) '' Set.Ici (m₀ k)
  have hs : ∀ k, (s k).Infinite := fun k =>
    (Set.Ici_infinite (m₀ k)).image (fun a _ b _ hab => Int.cast_injective hab)
  have hqD : q = C D := by
    refine funext_set s hs fun w hw => ?_
    have hw' : ∀ k, ∃ t : ℤ, m₀ k ≤ t ∧ (t : ℚ) = w k := fun k => hw k (Set.mem_univ k)
    choose m hm1 hm2 using hw'
    have hwm : w = fun k => (m k : ℚ) := funext fun k => (hm2 k).symm
    rw [hwm, hq, eval_C]
    exact hm₀ m hm1
  rw [← hq, hqD, eval_C]

end Poly

theorem NumModel.proof (hT : TensorRealise.Statement) (hS : SectionsPoly.Statement) (hD : ModelDim.Statement) :
    NumModel.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hmod n L δ hL hsub
  classical
  obtain ⟨i₀, hi₀⟩ := hmod.1 k₀
  have hj : x (e i₀) ≠ 0 := by
    rw [hx]
    simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi₀
  have hP := isMultiProjPrime_mIdealOver (S := F) y hmod.1
  have hdim := (hD F K ι Ω y k₀ N e x hx hmod n).mp hsub
  obtain ⟨p, hpH, hpS⟩ := hS F K ι Ω y k₀ hmod
  have hMD := (FieldNumbers.MixedDiffConst.full F K ι (mIdealOver F y) hP.multiHomog hP.relevant n hdim).1 δ
  set D := NumbersDVR.intNum F (mIdealOver F y) δ with hD_def

  have hev : ∀ᶠ m : K → ℤ in atTop, ∑ T : Finset (Fin n),
      (-1 : ℚ) ^ T.card * eval (fun k => (((m - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p = D := by
    have h2 : ∀ T : Finset (Fin n), ∀ᶠ m : K → ℤ in atTop,
        (NumbersDVR.hilbFn (mIdealOver F y) (m - ∑ i ∈ T, δ i) : ℚ) =
          eval (fun k => (((m - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p := fun T =>
      ((tendsto_atTop_add_const_right atTop (-(∑ i ∈ T, δ i)) tendsto_id).eventually hpH).mono
        fun m hm => by simpa only [id, sub_eq_add_neg] using hm
    filter_upwards [hMD, eventually_all.mpr h2] with m h1 h2
    rw [mixedDiff_eq_sum] at h1
    have h1' := congrArg (Int.cast : ℤ → ℚ) h1
    push_cast at h1'
    rw [← h1']
    exact Finset.sum_congr rfl fun T _ => by rw [h2 T]
  have hall := altSum_eq_of_eventually p δ (D : ℚ) hev

  have hsecs : ∀ T : Finset (Fin n), ∀ᶠ c : ℕ in atTop,
      ((restrLen (primeOf (S := F) x)
          ((tensorSub (fun i => (L i).toSubSystem) T).twist (twistSys F x (c : ℤ))) : ℤ) : ℚ) =
        eval (fun k => (((∑ i ∈ T, δ i + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k : ℤ) : ℚ)) p := fun T => by
    filter_upwards [hT F K ι Ω y k₀ N e x hx hmod n L δ hL T, hpS (∑ i ∈ T, δ i)] with c h1 h2
    rw [restrLen_primeOf_eq_finrank x hj, h1, ← h2]
    simp
  have hfin : ∀ᶠ c : ℕ in atTop, interSum (primeOf (S := F) x) (fun i => (L i).toSubSystem) c = D := by
    filter_upwards [eventually_all.mpr hsecs] with c hc
    apply Int.cast_injective (α := ℚ)
    rw [interSum, ← hall (∑ i, δ i + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)]
    push_cast
    refine Fintype.sum_bijective compl compl_involutive.bijective _ _ fun T => ?_
    have hcard : Tᶜ.card = n - T.card := by rw [Finset.card_compl, Fintype.card_fin]
    have hvec : (∑ i, δ i + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) - ∑ i ∈ Tᶜ, δ i =
        ∑ i ∈ T, δ i + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ := by
      rw [← Finset.sum_add_sum_compl T δ]
      abel
    rw [hc T, hcard, hvec]
  unfold interNum
  exact (tendsto_const_nhds.congr' (hfin.mono fun c h => h.symm)).limUnder_eq

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
