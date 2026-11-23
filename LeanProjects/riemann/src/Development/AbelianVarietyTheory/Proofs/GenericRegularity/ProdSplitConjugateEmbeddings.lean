import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FrameEx
import Formalism.LocalToGlobal.ProjectiveLattices.FrameExBor
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NormDiagEqNormBdiag

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.BorelChar

theorem prod_shift_eq_prod_ite (m p0 r : ℕ) (hm : p0 + m = r) (f : ℕ → ℂ) :
    ∏ i : Fin m, f (p0 + i) = ∏ j : Fin r, (if p0 ≤ (j : ℕ) then f j else 1) := by
  have h1 : ∏ j : Fin r, (if p0 ≤ (j : ℕ) then f j else 1) =
      ∏ j ∈ Finset.range r, (if p0 ≤ j then f j else 1) :=
    Fin.prod_univ_eq_prod_range (fun j => if p0 ≤ j then f j else 1) r
  have h2 : ∏ i : Fin m, f (p0 + i) = ∏ i ∈ Finset.range m, f (p0 + i) :=
    Fin.prod_univ_eq_prod_range (fun i => f (p0 + i)) m
  rw [h1, h2, ← hm, Finset.prod_range_add, Finset.prod_eq_one (s := Finset.range p0), one_mul]
  · exact Finset.prod_congr rfl (fun i _ => by simp)
  · intro j hj
    simp only [Finset.mem_range] at hj
    exact if_neg (by omega)

theorem prod_reflect_eq_prod_ite (m p0 r : ℕ) (hm : m = p0) (hp : p0 ≤ r) (f : ℕ → ℂ) :
    ∏ i : Fin m, f (p0 - 1 - i) = ∏ j : Fin r, (if (j : ℕ) < p0 then f j else 1) := by
  subst hm
  have h1 : ∏ j : Fin r, (if (j : ℕ) < m then f j else 1) =
      ∏ j ∈ Finset.range r, (if j < m then f j else 1) :=
    Fin.prod_univ_eq_prod_range (fun j => if j < m then f j else 1) r
  have h2 : ∏ i : Fin m, f (m - 1 - i) = ∏ i ∈ Finset.range m, f (m - 1 - i) :=
    Fin.prod_univ_eq_prod_range (fun i => f (m - 1 - i)) m
  have h3 : r = m + (r - m) := by omega
  rw [h1, h2, Finset.prod_range_reflect f m, h3, Finset.prod_range_add]
  have h4 : ∏ x ∈ Finset.range (r - m), (if m + x < m then f (m + x) else 1) = 1 :=
    Finset.prod_eq_one (fun j _ => if_neg (by omega))
  rw [h4, mul_one]
  exact Finset.prod_congr rfl (fun j hj => (if_pos (Finset.mem_range.1 hj)).symm)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {l : Level H} {r : ℕ}

theorem conjEmb_conjEmb_generic_regularity (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ := by
  ext x
  simp [conjEmb]

theorem relabel_injective (c : Coeff l) (σ : c.F →+* ℂ) : Function.Injective (relab (E := E) c σ) := by
  intro τ₁ τ₂ h
  ext a
  have := congrArg (fun f : E →+* ℂ => f a) h
  exact congrArg Subtype.val (σ.injective this)

theorem prod_split_conjugate_embeddings {R : (E →+* ℂ) → (E →+* ℂ)} (hR : Function.Bijective R) (X : Data E r)
    (G : (E →+* ℂ) → ℂ) :
    ∏ τ, G τ = ∏ τ' : X.Ψ, (G (Function.invFun R τ'.1) * G (Function.invFun R (conjEmb τ'.1))) := by
  classical
  have h1 : ∏ τ, G τ = ∏ τ'', G (Function.invFun R τ'') :=
    Fintype.prod_bijective R hR _ _ (fun τ => by rw [Function.leftInverse_invFun hR.1 τ])
  rw [h1, ← Finset.prod_mul_prod_compl X.Ψ, Finset.prod_mul_distrib]
  congr 1
  · exact (Finset.prod_coe_sort X.Ψ (fun τ'' => G (Function.invFun R τ''))).symm
  · rw [Finset.prod_coe_sort X.Ψ (fun τ' => G (Function.invFun R (conjEmb τ')))]
    refine Finset.prod_nbij' conjEmb conjEmb (fun τ h => ?_) (fun τ h => ?_) (fun τ _ => conjEmb_conjEmb_generic_regularity τ)
      (fun τ _ => conjEmb_conjEmb_generic_regularity τ) (fun τ _ => by rw [conjEmb_conjEmb_generic_regularity])
    · have h' : τ ∉ X.Ψ := by simpa using h
      have := (not_congr (X.cmType τ)).1 h'
      rw [conjEmb_eq']
      simpa using this
    · have := (X.cmType τ).1 h
      rw [conjEmb_eq']
      simpa using this

theorem borel_diagonal_positive (X : Data E r) (b : Frame X.Ψ r) (τ' : E →+* ℂ) (h : τ' ∈ X.Ψ) (i : ℕ)
    (hi : X.p0 + i < r) : bdiag X b τ' i = b ⟨τ', h⟩ ⟨X.p0 + i, hi⟩ ⟨X.p0 + i, hi⟩ := by
  unfold bdiag
  rw [dif_pos h, dif_pos hi]

theorem borel_diagonal_negative (X : Data E r) (b : Frame X.Ψ r) (τ' : E →+* ℂ) (h : τ' ∈ X.Ψ) (i : ℕ)
    (hi : X.p0 - 1 - i < r) :
    bdiag X b (conjEmb τ') i = (b ⟨τ', h⟩ ⟨X.p0 - 1 - i, hi⟩ ⟨X.p0 - 1 - i, hi⟩)⁻¹ := by
  have hn : conjEmb τ' ∉ X.Ψ := by
    rw [conjEmb_eq']
    exact (X.cmType τ').1 h
  have hc : conjEmb (conjEmb τ') ∈ X.Ψ := by
    rw [conjEmb_conjEmb_generic_regularity]
    exact h
  unfold bdiag
  rw [dif_neg hn, dif_pos hc, dif_pos hi]
  have : (⟨conjEmb (conjEmb τ'), hc⟩ : X.Ψ) = ⟨τ', h⟩ := Subtype.ext (conjEmb_conjEmb_generic_regularity τ')
  rw [this]

variable {Dw : Datum H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

theorem bchar_laU_eq (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp)
    (b : Frame (U.X k).Ψ r) (hb : b ∈ Bor (U.X k).Ψ r) (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (hm : n = m + m) :
    bchar (laU U a n k) b = bdet (U.X k) b ^ m *
      ∏ τ : E →+* ℂ, ∏ i : Fin (Dw.mult τ), bdiag (U.X k) b (relab c σ τ) i ^ a (τ, i) := by
  classical
  have hn2 : n / 2 = m := by omega
  have hinj := relabel_injective (E := E) c σ
  have hbij : Function.Bijective (relab (E := E) c σ) := ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  have hRinv : ∀ τ', relab c σ (Function.invFun (relab c σ) τ') = τ' := Function.rightInverse_invFun hbij.2
  have hp0r : (U.X k).p0 ≤ r := (U.X k).p0_le
  have hpos : ∀ τ, relab c σ τ ∈ (U.X k).Ψ → (U.X k).p0 + Dw.mult τ = r := by
    intro τ h
    have h1 : τ (H.rt : E) = H.rt0 := (relab_rt_iff c σ hσ τ).1 (((hU.2.1 k).2 _).1 h)
    have hm : Dw.mult τ = Dw.p := by unfold Datum.mult; rw [if_pos h1]
    have h2 := hU.1
    rw [(hU.2.1 k).1, hm]
    omega
  have hneg : ∀ τ, relab c σ τ ∉ (U.X k).Ψ → Dw.mult τ = (U.X k).p0 := by
    intro τ h
    have h1 : ¬ τ (H.rt : E) = H.rt0 := fun h1 => h (((hU.2.1 k).2 _).2 ((relab_rt_iff c σ hσ τ).2 h1))
    have hm : Dw.mult τ = Dw.q := by unfold Datum.mult; rw [if_neg h1]
    rw [(hU.2.1 k).1, hm]
  rw [prod_split_conjugate_embeddings hbij (U.X k)]
  have hfac : ∀ τ' : (U.X k).Ψ, ∏ j : Fin r, b τ' j j ^ laU U a n k τ' j =
      (∏ j : Fin r, b τ' j j ^ (if (U.X k).p0 ≤ (j : ℕ) then (1 : ℤ) else -1)) ^ m *
      ((∏ i : Fin (Dw.mult (Function.invFun (relab c σ) τ'.1)),
          bdiag (U.X k) b (relab c σ (Function.invFun (relab c σ) τ'.1)) i ^
            a (Function.invFun (relab c σ) τ'.1, i)) *
        ∏ i : Fin (Dw.mult (Function.invFun (relab c σ) (conjEmb τ'.1))),
          bdiag (U.X k) b (relab c σ (Function.invFun (relab c σ) (conjEmb τ'.1))) i ^
            a (Function.invFun (relab c σ) (conjEmb τ'.1), i)) := by
    intro τ'
    have hτ1 := hRinv τ'.1
    have hτ2 := hRinv (conjEmb τ'.1)
    have hm1 : (U.X k).p0 + Dw.mult (Function.invFun (relab c σ) τ'.1) = r :=
      hpos _ (by rw [hτ1]; exact τ'.2)
    have hm2 : Dw.mult (Function.invFun (relab c σ) (conjEmb τ'.1)) = (U.X k).p0 :=
      hneg _ (by rw [hτ2, conjEmb_eq']; exact ((U.X k).cmType τ'.1).1 τ'.2)
    have hsplit : ∀ j : Fin r, b τ' j j ^ laU U a n k τ' j =
        (b τ' j j ^ (if (U.X k).p0 ≤ (j : ℕ) then (1 : ℤ) else -1)) ^ m *
        ((if (U.X k).p0 ≤ (j : ℕ) then
            b τ' j j ^ a (Function.invFun (relab c σ) τ'.1, (j : ℕ) - (U.X k).p0) else 1) *
          (if (j : ℕ) < (U.X k).p0 then
            (b τ' j j)⁻¹ ^ a (Function.invFun (relab c σ) (conjEmb τ'.1), (U.X k).p0 - 1 - (j : ℕ)) else 1)) := by
      intro j
      have hb0 := bor_diag_ne (U.X k) hb τ' j
      have hlaU : laU U a n k τ' j = if (U.X k).p0 ≤ (j : ℕ) then
          (a (Function.invFun (relab c σ) τ'.1, (j : ℕ) - (U.X k).p0) : ℤ) + ((n / 2 : ℕ) : ℤ)
          else -(a (Function.invFun (relab c σ) (conjEmb τ'.1), (U.X k).p0 - 1 - (j : ℕ)) : ℤ) - ((n / 2 : ℕ) : ℤ) :=
        rfl
      rw [hlaU]
      by_cases hj : (U.X k).p0 ≤ (j : ℕ)
      · rw [if_pos hj, if_pos hj, if_pos hj, if_neg (by omega)]
        simp only [hn2, zpow_add₀ hb0, zpow_natCast, zpow_one, mul_one]
        ring
      · rw [if_neg hj, if_neg hj, if_neg hj, if_pos (by omega)]
        simp only [hn2, sub_eq_add_neg, zpow_add₀ hb0, zpow_neg, zpow_natCast, zpow_one, inv_pow, one_mul]
        ring
    rw [Finset.prod_congr rfl (fun j _ => hsplit j), Finset.prod_mul_distrib, Finset.prod_pow,
      Finset.prod_mul_distrib]
    congr 2
    · rw [hτ1]
      calc ∏ j : Fin r, (if (U.X k).p0 ≤ (j : ℕ) then
              b τ' j j ^ a (Function.invFun (relab c σ) τ'.1, (j : ℕ) - (U.X k).p0) else 1)
          = ∏ j : Fin r, (if (U.X k).p0 ≤ (j : ℕ) then
              (fun j' : ℕ => if h : j' < r then
                b τ' ⟨j', h⟩ ⟨j', h⟩ ^ a (Function.invFun (relab c σ) τ'.1, j' - (U.X k).p0) else 1) j
              else 1) := by
            refine Finset.prod_congr rfl (fun j _ => ?_)
            simp [j.isLt]
        _ = ∏ i : Fin (Dw.mult (Function.invFun (relab c σ) τ'.1)),
              (fun j' : ℕ => if h : j' < r then
                b τ' ⟨j', h⟩ ⟨j', h⟩ ^ a (Function.invFun (relab c σ) τ'.1, j' - (U.X k).p0) else 1)
                ((U.X k).p0 + i) := (prod_shift_eq_prod_ite _ _ _ hm1 (fun j' : ℕ => if h : j' < r then
                b τ' ⟨j', h⟩ ⟨j', h⟩ ^ a (Function.invFun (relab c σ) τ'.1, j' - (U.X k).p0) else 1)).symm
        _ = ∏ i : Fin (Dw.mult (Function.invFun (relab c σ) τ'.1)),
              bdiag (U.X k) b τ'.1 i ^ a (Function.invFun (relab c σ) τ'.1, i) := by
            refine Finset.prod_congr rfl (fun i _ => ?_)
            have hi : (U.X k).p0 + (i : ℕ) < r := by have := i.isLt; omega
            rw [borel_diagonal_positive _ _ _ τ'.2 _ hi]
            simp [hi]
    · rw [hτ2]
      calc ∏ j : Fin r, (if (j : ℕ) < (U.X k).p0 then
              (b τ' j j)⁻¹ ^ a (Function.invFun (relab c σ) (conjEmb τ'.1), (U.X k).p0 - 1 - (j : ℕ)) else 1)
          = ∏ j : Fin r, (if (j : ℕ) < (U.X k).p0 then
              (fun j' : ℕ => if h : j' < r then
                (b τ' ⟨j', h⟩ ⟨j', h⟩)⁻¹ ^ a (Function.invFun (relab c σ) (conjEmb τ'.1), (U.X k).p0 - 1 - j')
                else 1) j
              else 1) := by
            refine Finset.prod_congr rfl (fun j _ => ?_)
            simp [j.isLt]
        _ = ∏ i : Fin (Dw.mult (Function.invFun (relab c σ) (conjEmb τ'.1))),
              (fun j' : ℕ => if h : j' < r then
                (b τ' ⟨j', h⟩ ⟨j', h⟩)⁻¹ ^ a (Function.invFun (relab c σ) (conjEmb τ'.1), (U.X k).p0 - 1 - j')
                else 1) ((U.X k).p0 - 1 - i) := (prod_reflect_eq_prod_ite _ _ _ hm2 hp0r (fun j' : ℕ => if h : j' < r then
                (b τ' ⟨j', h⟩ ⟨j', h⟩)⁻¹ ^ a (Function.invFun (relab c σ) (conjEmb τ'.1), (U.X k).p0 - 1 - j')
                else 1)).symm
        _ = ∏ i : Fin (Dw.mult (Function.invFun (relab c σ) (conjEmb τ'.1))),
              bdiag (U.X k) b (conjEmb τ'.1) i ^ a (Function.invFun (relab c σ) (conjEmb τ'.1), i) := by
            refine Finset.prod_congr rfl (fun i _ => ?_)
            have hi0 := i.isLt
            have hi : (U.X k).p0 - 1 - (i : ℕ) < r := by omega
            have hii : (U.X k).p0 - 1 - ((U.X k).p0 - 1 - (i : ℕ)) = i := by omega
            rw [borel_diagonal_negative _ _ _ τ'.2 _ hi]
            simp [hi, hii]
  rw [show bchar (laU U a n k) b =
      ∏ τ' : (U.X k).Ψ, ∏ j : Fin r, b τ' j j ^ laU U a n k τ' j from rfl]
  rw [Finset.prod_congr rfl (fun τ' _ => hfac τ')]
  conv_lhs => rw [Finset.prod_mul_distrib, Finset.prod_pow]
  rfl

end GlobalTheory.BorelChar
