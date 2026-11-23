import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Formalism.LocalToGlobal.LatticeGeometry.RealizationNorms.MkTauEmbInjective
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SmoothBigCellSectionsExist

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open Formalism.MainNotions.S (Point ptMat ptEntry)

namespace Formalism.L2.SG.Pf.CarrierTop

open Formalism.L2.SG.RealObj

theorem placeTie_ePl {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (x : InfinitePlace D.host.E) :
    InfinitePlace.mk ((X.B.I.φ (X.pl.symm ((Formalism.L2.Geo.Rec.StarEmbeddingNorm.ePl D).symm x))).comp X.ιE.symm.toRingHom) = x := by
  have h : (X.B.I.φ (X.pl.symm ((Formalism.L2.Geo.Rec.StarEmbeddingNorm.ePl D).symm x))).comp X.ιE.symm.toRingHom =
      Formalism.BasicNotions.DV.tauEmb D ((Formalism.L2.Geo.Rec.StarEmbeddingNorm.ePl D).symm x) := by
    ext y
    show X.B.I.φ _ (X.ιE.symm y) = _
    rw [X.φ_eq, Equiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    rfl
  rw [h]
  exact (Formalism.L2.Geo.Rec.StarEmbeddingNorm.ePl D).apply_symm_apply x

section Mat

variable {r : ℕ}

theorem dl_diag (a b : Fin (r + 1) → ℂ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) {l : ℕ} (hl : l ≤ r + 1) :
    RealObj.Dl (Matrix.diagonal a * Z * Matrix.diagonal b) l =
      (∏ i : Fin l, a (Fin.castLE hl i)) * (∏ i : Fin l, b (Fin.castLE hl i)) * RealObj.Dl Z l := by
  have hsub : (Matrix.diagonal a * Z * Matrix.diagonal b).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal (fun i => a (Fin.castLE hl i)) * Z.submatrix (Fin.castLE hl) (Fin.castLE hl) *
        Matrix.diagonal (fun i => b (Fin.castLE hl i)) := by
    ext i j
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [RealObj.Dl, dif_pos hl]
  rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
  ring

theorem prod_castLE_succ (x : Fin (r + 1) → ℂ) (h : r + 1 ≤ r + 1) :
    ∏ i : Fin (r + 1), x (Fin.castLE h i) = (∏ i : Fin r, x (Fin.castLE (Nat.le_succ r) i)) * x (Fin.last r) := by
  rw [Fin.prod_univ_castSucc]
  rfl

def sgnV (r : ℕ) : Fin (r + 1) → ℂ := fun b => (-1 : ℂ) ^ (r - b.1)

theorem zhatO_eq_mul (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    RealObj.ZhatO Z = Matrix.diagonal (fun _ => 1) * Z * Matrix.diagonal (sgnV r) := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [RealObj.ZhatO, sgnV]
  ring

theorem zhatO_invol (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : RealObj.ZhatO (RealObj.ZhatO Z) = Z := by
  ext a b
  simp only [RealObj.ZhatO]
  rw [← mul_assoc, ← pow_add, Even.neg_one_pow ⟨r - b.1, rfl⟩, one_mul]

theorem norm_prod_sgn {l : ℕ} (hl : l ≤ r + 1) : ‖∏ i : Fin l, sgnV r (Fin.castLE hl i)‖ = 1 := by
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro i _
  simp [sgnV]

theorem prod_one' (l : ℕ) (hl : l ≤ r + 1) : ∏ _i : Fin l, (fun _ : Fin (r + 1) => (1 : ℂ)) (Fin.castLE hl _i) = 1 := by
  simp

theorem norm_dl_zhatO (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) {l : ℕ} (hl : l ≤ r + 1) :
    ‖RealObj.Dl Z l‖ = ‖RealObj.Dl (RealObj.ZhatO Z) l‖ := by
  rw [zhatO_eq_mul, dl_diag _ _ _ hl, norm_mul, norm_mul, norm_prod_sgn hl]
  simp

end Mat

section Pt

theorem ptEntry_app_lt {K : Type*} [Zero K] : ∀ (L0 L1 : List (K × ℕ)) (i j : ℕ),
    i < (L0.map Prod.snd).sum → j < (L0.map Prod.snd).sum → ptEntry (L0 ++ L1) i j = ptEntry L0 i j
  | [], _, _, _, hi, _ => by simp at hi
  | (t, s) :: bs, L1, i, j, hi, hj => by
    simp only [List.map_cons, List.sum_cons] at hi hj
    simp only [List.cons_append, ptEntry]
    split_ifs <;> first | rfl | exact ptEntry_app_lt bs L1 (i - s) (j - s) (by omega) (by omega)

theorem ptEntry_app_ge {K : Type*} [Zero K] : ∀ (L0 L1 : List (K × ℕ)) (i j : ℕ),
    (L0.map Prod.snd).sum ≤ i →
    ptEntry (L0 ++ L1) i j =
      if (L0.map Prod.snd).sum ≤ j then ptEntry L1 (i - (L0.map Prod.snd).sum) (j - (L0.map Prod.snd).sum) else 0
  | [], L1, i, j, _ => by simp
  | (t, s) :: bs, L1, i, j, hi => by
    simp only [List.map_cons, List.sum_cons] at hi ⊢
    simp only [List.cons_append, ptEntry]
    rw [if_neg (by omega)]
    by_cases hs : s ≤ j
    · rw [if_pos ⟨by omega, hs⟩, ptEntry_app_ge bs L1 (i - s) (j - s) (by omega)]
      by_cases hj : (bs.map Prod.snd).sum ≤ j - s
      · rw [if_pos hj, if_pos (by omega), Nat.sub_sub, Nat.sub_sub]
      · rw [if_neg hj, if_neg (by omega)]
    · rw [if_neg (by omega), if_neg (by omega)]

variable {K : Type} [Field K] {r : ℕ}

theorem dl_pt_last (σ : K →+* ℂ) (w : Point K (r + 1)) (L : List (K × ℕ)) (t : K)
    (hw : w.1 = L ++ [(t, 1)]) (hs : (L.map Prod.snd).sum = r) :
    RealObj.Dl ((ptMat w).map σ) (r + 1) = RealObj.Dl ((ptMat w).map σ) r * σ t ∧ RealObj.Dl ((ptMat w).map σ) r ≠ 0 := by
  have hL : ∀ b ∈ L, b.1 ≠ 0 ∧ 1 ≤ b.2 := fun b hb => w.2.1 b (by rw [hw]; exact List.mem_append_left _ hb)
  let w0 : Point K r := ⟨L, hL, hs⟩
  set M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := (ptMat w).map σ with hM

  have hsub : M.submatrix Fin.castSucc Fin.castSucc = (ptMat w0).map σ := by
    ext i j
    simp only [hM, Matrix.submatrix_apply, Matrix.map_apply, ptMat, Fin.val_castSucc]
    rw [hw, ptEntry_app_lt L _ i j (by rw [hs]; exact i.2) (by rw [hs]; exact j.2)]
  have hDr : RealObj.Dl M r = ((ptMat w0).map σ).det := by
    unfold RealObj.Dl
    rw [dif_pos (Nat.le_succ r), ← hsub]
    rfl
  have hDtop : RealObj.Dl M (r + 1) = M.det := by
    unfold RealObj.Dl
    rw [dif_pos le_rfl]
    rfl
  have hrow : ∀ j : Fin (r + 1), M (Fin.last r) j = if j = Fin.last r then σ t else 0 := by
    intro j
    simp only [hM, Matrix.map_apply, ptMat, Fin.val_last]
    rw [hw, ptEntry_app_ge L _ r j (by rw [hs]), hs]
    by_cases hj : j = Fin.last r
    · subst hj
      simp [ptEntry]
    · have hjr : (j : ℕ) < r := by
        have := j.2
        have : (j : ℕ) ≠ r := fun h => hj (Fin.ext h)
        omega
      rw [if_neg (by omega), if_neg hj, map_zero]
  have hdet : M.det = σ t * ((ptMat w0).map σ).det := by
    rw [Matrix.det_succ_row M (Fin.last r), Finset.sum_eq_single (Fin.last r)]
    · rw [hrow, if_pos rfl, Fin.succAbove_last, hsub, Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow,
        one_mul]
    · intro j _ hj
      rw [hrow, if_neg hj]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hne : ((ptMat w0).map σ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero σ).mpr (Formalism.MainNotions.BridgeLemma.ptMat_det_ne w0)
  refine ⟨?_, ?_⟩
  · rw [hDtop, hDr, hdet, mul_comm]
  · rw [hDr]
    exact hne

end Pt

section Sign

open Formalism.L2.SG.DataInst

theorem signFlip_append {K : Type} [Ring K] (r : ℕ) : ∀ (b : ℕ) (x y : Formalism.FourierDecayAlt.TB.Pt K),
    signAux r b (x ++ y) = signAux r b x ++ signAux r (b + (x.map Prod.fst).sum) y
  | b, [], y => by simp [signAux]
  | b, (s, t) :: rest, y => by
    simp only [List.cons_append, signAux, List.map_cons, List.sum_cons, List.cons.injEq, true_and]
    rw [signFlip_append r (b + s) rest y, add_assoc]

theorem signFlip_singleton_last {K : Type} [Ring K] (r : ℕ) (t : K) : signAux r (r + 1) [(1, t)] = [(1, t)] := by
  simp [signAux]

theorem pt_last {D : D7} (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1))
    (hp : ptOfL (D := D) (D.R.rS + 1) p = some w) (h1 : p.getLast?.map Prod.fst = some 1) :
    ∃ (L : List (D.host.E × ℕ)) (t : D.host.E), w.1 = L ++ [(t, 1)] ∧ (L.map Prod.snd).sum = D.R.rS ∧
      p.getLast? = some (1, t) := by
  unfold ptOfL ptOfList at hp
  split_ifs at hp with hPt
  obtain rfl := Option.some.inj hp
  have hsum : ((signPt D.R.rS p).map Prod.fst).sum = D.R.rS + 1 := hPt.1
  unfold signPt at hsum
  rw [sign_list_fst] at hsum
  have hne : p ≠ [] := by
    rintro rfl
    simp at hsum
  obtain ⟨q, hq⟩ : ∃ q, p.getLast? = some q := ⟨p.getLast hne, List.getLast?_eq_some_getLast hne⟩
  have hq1 : q.1 = 1 := by
    rw [hq] at h1
    simpa using h1
  have hp' : p = p.dropLast ++ [q] := by
    rw [List.getLast?_eq_some_getLast hne, Option.some.injEq] at hq
    rw [← hq]
    exact (List.dropLast_append_getLast hne).symm
  obtain ⟨s, t⟩ := q
  simp only at hq1
  subst hq1
  have hs0 : ((p.dropLast).map Prod.fst).sum = D.R.rS := by
    rw [hp'] at hsum
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
    omega
  refine ⟨(signAux D.R.rS 1 p.dropLast).map Prod.swap, t, ?_, ?_, hq⟩
  · show (signPt D.R.rS p).map Prod.swap = _
    unfold signPt
    conv_lhs => rw [hp']
    rw [signFlip_append, hs0, add_comm, signFlip_singleton_last, List.map_append]
    rfl
  · rw [List.map_map]
    have : Prod.snd ∘ Prod.swap = (Prod.fst : ℕ × D.host.E → ℕ) := rfl
    rw [this, sign_list_fst, hs0]

end Sign

section G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def cS (r : ℕ) (sc : ℝ) : Fin (r + 1) → ℂ := fun a => ((sc : ℂ) ^ (r - a.1))⁻¹

theorem zx_sc (u u' : D.what₂.Word) (sc : ℝ) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    ZX X u u' sc γ v = Matrix.diagonal (cS D.R.rS sc) * ZX X u u' 1 γ v * Matrix.diagonal (cS D.R.rS sc) := by
  ext a b
  simp only [ZX, Zhat, frm, famSc, Formalism.L2.SG.HidaSetting.hJ, Matrix.mul_diagonal, Matrix.diagonal_mul, cS]
  simp only [Complex.ofReal_one, one_pow, inv_one, one_smul, Matrix.mulVec_smul, star_smul, smul_eq_mul,
    Complex.star_def, map_inv₀, map_pow, Complex.conj_ofReal]
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

variable {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

theorem topTie_G (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) (u u' : D.what₂.Word) (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (hemb : ∀ j x, S.emb j (X.ιE x) = X.B.I.φ (τ j) x)
    (hG : ∀ j q, (S.pd j).G q = Complex.normSq (Formalism.FourierDecayAlt.D.ptLast q).2 - Tw (D := D) u * Tw (D := D) u') :
    ∀ j (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)),
      ptOfL (D := D) (D.R.rS + 1) p = some w → (∃ γ, IsPtRep X u u' w γ) →
        (Formalism.FourierDecayAlt.D.ptLast (Formalism.FourierDecayAlt.C.loc (S.emb j) p)).1 = 1 →
        (S.pd j).G (Formalism.FourierDecayAlt.C.loc (S.emb j) p) =
          GX X u u' D.host.rdE (gamW X u u' w) (τ j) /
            ‖RealObj.Dl (ZX X u u' D.host.rdE (gamW X u u' w) (τ j)) D.R.rS‖ ^ 2 := by
  intro j p w hp hex h1
  have hrep : IsPtRep X u u' w (gamW X u u' w) := by
    unfold gamW
    rw [dif_pos hex]
    exact hex.choose_spec

  have hloc : ∀ (σ : D.host.E →+* ℂ), (Formalism.FourierDecayAlt.C.loc σ p).getLast? = p.getLast?.map (fun b => (b.1, σ b.2)) := by
    intro σ
    unfold Formalism.FourierDecayAlt.C.loc
    rw [List.getLast?_map]
  have h1' : p.getLast?.map Prod.fst = some 1 := by
    unfold Formalism.FourierDecayAlt.D.ptLast at h1
    rw [hloc] at h1
    cases hq : p.getLast? with
    | none => rw [hq] at h1; simp at h1
    | some q => rw [hq] at h1; simpa using h1
  obtain ⟨L, t, hw, hs, hlast⟩ := pt_last p w hp h1'
  let σ : D.host.E →+* ℂ := (X.B.I.φ (τ j)).comp X.ιE.symm.toRingHom
  have hσ : S.emb j t = σ t := by
    have := hemb j (X.ιE.symm t)
    rw [RingEquiv.apply_symm_apply] at this
    rw [this]
    rfl
  have hL : Formalism.FourierDecayAlt.D.ptLast (Formalism.FourierDecayAlt.C.loc (S.emb j) p) = (1, σ t) := by
    unfold Formalism.FourierDecayAlt.D.ptLast
    rw [hloc, hlast]
    simp [hσ]
  rw [hG, hL]

  obtain ⟨hA, hB⟩ := dl_pt_last σ w L t hw hs
  have hP : ptC X (τ j) w = (ptMat w).map σ := rfl
  have hZ1 : ZX X u u' 1 (gamW X u u' w) (τ j) = RealObj.ZhatO ((ptMat w).map σ) := by
    rw [← hP, ← hrep (τ j), zhatO_invol]
  have hrd : 0 < D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    exact Real.rpow_pos_of_pos (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.E)) _
  have hc0 : ∀ a, cS D.R.rS D.host.rdE a ≠ 0 := fun a => by
    unfold cS
    exact inv_ne_zero (pow_ne_zero _ (by exact_mod_cast hrd.ne'))
  have hclast : cS D.R.rS D.host.rdE (Fin.last D.R.rS) = 1 := by simp [cS]
  set P := (ptMat w).map σ with hPdef
  set a : ℂ := ∏ i : Fin D.R.rS, cS D.R.rS D.host.rdE (Fin.castLE (Nat.le_succ D.R.rS) i) with ha
  have ha0 : a ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hc0 _
  have hZ := zx_sc X u u' D.host.rdE (gamW X u u' w) (τ j)
  have hN : ∀ {l : ℕ} (hl : l ≤ D.R.rS + 1),
      ‖RealObj.Dl (ZX X u u' D.host.rdE (gamW X u u' w) (τ j)) l‖ =
        ‖∏ i : Fin l, cS D.R.rS D.host.rdE (Fin.castLE hl i)‖ ^ 2 * ‖RealObj.Dl P l‖ := by
    intro l hl
    rw [hZ, dl_diag _ _ _ hl, norm_mul, norm_mul, hZ1, ← norm_dl_zhatO _ hl]
    ring
  have hNr := hN (Nat.le_succ D.R.rS)
  have hNt := hN (le_refl (D.R.rS + 1))
  rw [prod_castLE_succ, hclast, mul_one, ← ha, hA, norm_mul] at hNt
  rw [← ha] at hNr
  unfold GX Gv
  rw [hNt, hNr, Complex.normSq_eq_norm_sq]
  have hB' : ‖RealObj.Dl P D.R.rS‖ ≠ 0 := norm_ne_zero_iff.mpr hB
  have ha' : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha0
  field_simp

theorem topTie_of (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) (u u' : D.what₂.Word) (sc : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (FdN FdN' : Set X.B.I.Ginf)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (hPG : Formalism.FourierDecayAlt.C.PropGram S (VtPt X u u' sc i0 i0' FdN FdN' νq))
    (hemb : ∀ j x, S.emb j (X.ιE x) = X.B.I.φ (τ j) x)
    (hG : ∀ j q, (S.pd j).G q = Complex.normSq (Formalism.FourierDecayAlt.D.ptLast q).2 - Tw (D := D) u * Tw (D := D) u') :
    TopTie X S u u' sc i0 i0' FdN FdN' νq τ := by
  exact ⟨hPG, hemb, topTie_G X S u u' τ hemb hG⟩

end G

end Formalism.L2.SG.Pf.CarrierTop
