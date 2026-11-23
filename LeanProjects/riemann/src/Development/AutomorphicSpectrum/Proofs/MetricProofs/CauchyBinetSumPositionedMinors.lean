import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DetMemSubring
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.Inv

variable {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}

theorem bExt_posOf (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω) (s : Ψ ⊕ Ψ)
    (l : Fin (rk Ψ p q s)) (j : Fin (n s)) : bExt B s (posOf p q s l) j = B s l j := by
  have hinj := (BlockEmbeddings.posOf_strictMono (Ψ := Ψ) (p := p) (q := q) s).injective
  unfold bExt
  rw [Finset.sum_eq_single l]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg fun h => hb (hinj h)]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem aExt_posOf (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (s : Ψ ⊕ Ψ)
    (j : Fin (n s)) (l : Fin (rk Ψ p q s)) : aExt C s j (posOf p q s l) = C s j l := by
  have hinj := (BlockEmbeddings.posOf_strictMono (Ψ := Ψ) (p := p) (q := q) s).injective
  unfold aExt
  rw [Finset.sum_eq_single l]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg fun h => hb (hinj h)]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem aExt_of_forall_ne (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (s : Ψ ⊕ Ψ)
    (j : Fin (n s)) {b : Fin (p + q)} (h : ∀ l, posOf p q s l ≠ b) : aExt C s j b = 0 :=
  Finset.sum_eq_zero fun l _ => if_neg (h l)

theorem bExt_mul_aExt_row (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω) (hBC : ∀ s, B s * C s = 1) (s : Ψ ⊕ Ψ)
    (l : Fin (rk Ψ p q s)) (b : Fin (p + q)) :
    (bExt B s * aExt C s) (posOf p q s l) b = (1 : Matrix (Fin (p + q)) (Fin (p + q)) Ω) (posOf p q s l) b := by
  have hinj := (BlockEmbeddings.posOf_strictMono (Ψ := Ψ) (p := p) (q := q) s).injective
  rw [Matrix.mul_apply]
  simp only [bExt_posOf]
  by_cases hb : ∃ l', posOf p q s l' = b
  · obtain ⟨l', rfl⟩ := hb
    simp only [aExt_posOf]
    have h := congrFun (congrFun (hBC s) l) l'
    rw [Matrix.mul_apply] at h
    rw [h]
    by_cases e : l = l'
    · subst e
      simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne fun h' => e (hinj h')]
  · have hb' : ∀ l', posOf p q s l' ≠ b := fun l' h' => hb ⟨l', h'⟩
    simp only [aExt_of_forall_ne C s _ hb', mul_zero, Finset.sum_const_zero]
    rw [Matrix.one_apply_ne (hb' l)]

theorem sum_strictMono_eq {M : Type} [AddCommMonoid M] {d m : ℕ} (f : (Fin d → Fin m) → M)
    (hf : ∀ J, ¬ StrictMono J → f J = 0) :
    ∑ J, f J = ∑ s : GroundTheory.PAdicHodge.KSubset m d, f s.emb := by
  classical
  symm
  refine Fintype.sum_of_injective (fun s : GroundTheory.PAdicHodge.KSubset m d => (s.emb : Fin d → Fin m))
    ?_ _ _ ?_ fun _ => rfl
  · intro s s' h
    have h' : Set.range s.emb = Set.range s'.emb := congrArg Set.range h
    rw [GroundTheory.PAdicHodge.KSubset.range_emb, GroundTheory.PAdicHodge.KSubset.range_emb] at h'
    exact Subtype.ext (Finset.coe_injective h')
  · intro J hJ
    refine hf J fun hm => hJ ?_
    have hc : (Finset.univ.image J).card = d := by
      rw [Finset.card_image_of_injective _ hm.injective]
      simp
    refine ⟨⟨Finset.univ.image J, hc⟩, ?_⟩
    exact (Finset.orderEmbOfFin_unique hc (fun x => by simp) hm).symm

theorem sum_sMin_mul_cMin : ∀ {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
    (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω)
    (hBC : ∀ s, B s * C s = 1) (t : StepIx Ψ p q) (I I' : Finset (Fin (p + q)))
    (hI : I.card = (t.2 : ℕ) + 1) (hI' : I'.card = (t.2 : ℕ) + 1)
    (hp : ∀ a ∈ I, ∃ l, posOf p q t.1 l = a) (hp' : ∀ a ∈ I', ∃ l, posOf p q t.1 l = a),
    ∑ J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1), sMin B t I J * cMin C t J I' = if I = I' then 1 else 0 := by
  intro Ψ p q Ω _ n C B hBC t I I' hI hI' hp _
  classical
  rw [sum_strictMono_eq (fun J => sMin B t I J * cMin C t J I') (fun J hJ => by
    simp only [sMin, if_neg hJ, zero_mul])]
  have hterm : ∀ s : GroundTheory.PAdicHodge.KSubset (n t.1) ((t.2 : ℕ) + 1),
      sMin B t I s.emb * cMin C t s.emb I' =
        (((bExt B t.1).submatrix (I.orderEmbOfFin hI) id).submatrix id s.emb).det *
          (((aExt C t.1).submatrix id (I'.orderEmbOfFin hI')).submatrix s.emb id).det := by
    intro s
    simp only [sMin, if_pos s.emb.strictMono, bMin, cMin, dif_pos hI, dif_pos hI']
    rfl
  simp only [hterm]
  rw [← GroundTheory.PAdicHodge.det_mul_eq_sum_minors]
  have hmat : (bExt B t.1).submatrix (I.orderEmbOfFin hI) id * (aExt C t.1).submatrix id (I'.orderEmbOfFin hI') =
      (1 : Matrix (Fin (p + q)) (Fin (p + q)) Ω).submatrix (I.orderEmbOfFin hI) (I'.orderEmbOfFin hI') := by
    ext x y
    obtain ⟨l, hl⟩ := hp _ (Finset.orderEmbOfFin_mem I hI x)
    have h := bExt_mul_aExt_row C B hBC t.1 l (I'.orderEmbOfFin hI' y)
    rw [hl] at h
    simpa [Matrix.mul_apply] using h
  rw [hmat]
  by_cases e : I = I'
  · subst e
    rw [if_pos rfl, Matrix.submatrix_one _ (I.orderEmbOfFin hI).injective, Matrix.det_one]
  · rw [if_neg e]
    have hns : ¬ I ⊆ I' := fun hs => e (Finset.eq_of_subset_of_card_le hs (by omega))
    obtain ⟨a, ha, ha'⟩ := Finset.not_subset.1 hns
    have hr : a ∈ Set.range (I.orderEmbOfFin hI) := by
      rw [Finset.range_orderEmbOfFin]
      exact ha
    obtain ⟨x, rfl⟩ := hr
    refine Matrix.det_eq_zero_of_row_eq_zero x fun y => ?_
    rw [Matrix.submatrix_apply]
    refine Matrix.one_apply_ne fun h => ha' ?_
    rw [h]
    exact Finset.orderEmbOfFin_mem _ _ _

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.Inv
