import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ValUniqOf

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

theorem isLatTup_smul_iff {p : ℕ} {G : GAtP p} (i : G.comp) (γ : (G.lev i).Γ) (L : G.P.Tup) :
    G.P.IsLatTup ((G.lev i).smul γ L) ↔ G.P.IsLatTup L := by
  constructor
  · intro h v
    obtain ⟨g', hg', hL⟩ := h v
    refine ⟨(((G.lev i).act v γ)⁻¹ : GL (Fin (G.P.m + 1)) (G.P.Qq v)).1 * g', ?_, ?_⟩
    · rw [Matrix.det_mul]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 ((G.lev i).act v γ)⁻¹.isUnit).mul hg'
    · have hinj : Function.Injective ((Matrix.mulVecLin (((G.lev i).act v γ : GL (Fin (G.P.m + 1)) (G.P.Qq v)) :
          Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))).restrictScalars (G.P.W v)) :=
        Matrix.mulVec_injective_of_isUnit ((G.lev i).act v γ).isUnit
      apply Submodule.map_injective_of_injective hinj
      rw [colSpan_map, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
      exact hL
  · intro h v
    obtain ⟨g, hg, hL⟩ := h v
    refine ⟨((G.lev i).act v γ).1 * g, ?_, ?_⟩
    · rw [Matrix.det_mul]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 ((G.lev i).act v γ).isUnit).mul hg
    · show (L v).map _ = _
      rw [hL, colSpan_map]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {LL : Type} [Field LL] {p : ℕ}
  {S : StepLevel F E σ J T f bad} {emb : Tau → E →+* ℂ} {embLL : LL →+* ℂ}
  {G : GAtP p} {e : LL →+* G.Kf} {A : LocAt F E n G} {pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau}
  {V cls : Type} [AddCommGroup V] [Module LL V] {embV : V →ₛₗ[embLL] (cls → Frames (gramC J emb) → ℂ)}
  {yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F)}

theorem valC_equiv (tE : Tau → E →+* LL) (htE : ∀ τ x, embLL (tE τ x) = emb τ x)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (hBs : cT (σ : E →+* E) A.B.1 * J * A.B.1 = 1) (hA : A.ActB)
    (hex : ValEx S emb embLL G A pos embV yc)
    (hpos : ∀ v (s : Fin (G.P.n' v)) (x : E),
      e (tE (pos ⟨v, s⟩) (if Even s.val then x else σ x)) = G.P.ι v ((G.P.σ v ^ s.val) (A.iw v x)))
    (hchi : ∀ i (γ : (G.lev i).Γ) (κ : S.U), A.IsAway i γ κ.1 →
      ∃ r : LL, embLL r = (S.chi κ : ℂ) ∧ algebraMap G.O G.Kf ((G.lev i).χ γ : G.O) * e r = 1)
    (hi : EvInj emb G A pos (J := J)) (hp : PtEx S G A yc)
    (x : V) (i : G.comp) (γ : (G.lev i).Γ) (hγ : A.gamI i γ ∈ UJ (σ : E →+* E) J) (κ : S.U) (hκ : A.IsAway i γ κ.1)
    (r : LL) (hr : embLL r = (S.chi κ : ℂ)) (L : G.P.Tup) (hL : G.P.IsLatTup L) :
    r • valC S emb embLL G A pos embV yc x i ((G.lev i).smul γ L) =
      natActR G.P LL (blkLL A σ tE pos (A.gamI i γ)) (valC S emb embLL G A pos embV yc x i L) := by
  choose g0 hg0 hLg using hL
  let g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v) := fun v => ((Matrix.isUnit_iff_isUnit_det _).2 (hg0 v)).unit
  have hg : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) := hLg
  obtain ⟨c, γ₀, κ₀, hγ₀, hpt⟩ := hp i g
  apply MvPolynomial.map_injective embLL embLL.injective
  apply sub_eq_zero.1
  apply hi
  funext z
  obtain ⟨z₁, hz₁⟩ := frames_tr emb hc (A.gamI i γ) hγ z
  obtain ⟨z₂, hz₂⟩ := frames_tr emb hc γ₀ hγ₀ z₁
  have h := (cmpC_tie (e := e) tE hex hpos hchi).val_equiv htE hBs hA x i L g hg γ hγ κ hκ c γ₀ hγ₀ κ₀ hpt z z₁ z₂ hz₁ hz₂
  rw [map_sub, Pi.sub_apply, map_smul', map_smul, Pi.smul_apply, smul_eq_mul, hr]
  exact sub_eq_zero.2 h

theorem cmpC_equiv (tE : Tau → E →+* LL) (htE : ∀ τ x, embLL (tE τ x) = emb τ x)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (hBs : cT (σ : E →+* E) A.B.1 * J * A.B.1 = 1) (hA : A.ActB)
    (hex : ValEx S emb embLL G A pos embV yc)
    (hpos : ∀ v (s : Fin (G.P.n' v)) (x : E),
      e (tE (pos ⟨v, s⟩) (if Even s.val then x else σ x)) = G.P.ι v ((G.P.σ v ^ s.val) (A.iw v x)))
    (hchi : ∀ i (γ : (G.lev i).Γ) (κ : S.U), A.IsAway i γ κ.1 →
      ∃ r : LL, embLL r = (S.chi κ : ℂ) ∧ algebraMap G.O G.Kf ((G.lev i).χ γ : G.O) * e r = 1)
    (hi : EvInj emb G A pos (J := J)) (hp : PtEx S G A yc)
    (hU : ∀ i (γ : (G.lev i).Γ), A.gamI i γ ∈ UJ (σ : E →+* E) J)
    (haw : ∀ i (γ : (G.lev i).Γ), ∃ κ : S.U, A.IsAway i γ κ.1)
    (x : V) (i : G.comp) (γ : (G.lev i).Γ) (L : G.P.Tup) :
    cmpC S emb embLL G e A pos embV yc x i ((G.lev i).smul γ L) =
      ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (cmpC S emb embLL G e A pos embV yc x i L) := by
  unfold cmpC
  by_cases hL : G.P.IsLatTup L
  · have hL' : G.P.IsLatTup ((G.lev i).smul γ L) := (isLatTup_smul_iff i γ L).2 hL
    obtain ⟨κ, hκ⟩ := haw i γ
    obtain ⟨r, hr, hr1⟩ := hchi i γ κ hκ
    rw [if_pos hL, if_pos hL', actX_map A tE pos e hA hpos i γ,
      ← valC_equiv tE htE hc hBs hA hex hpos hchi hi hp x i γ (hU i γ) κ hκ r hr L hL, map_smul',
      ← algebraMap_smul G.Kf ((G.lev i).χ γ : G.O), smul_smul, hr1, one_smul]
  · have hL' : ¬ G.P.IsLatTup ((G.lev i).smul γ L) := fun h => hL ((isLatTup_smul_iff i γ L).1 h)
    rw [if_neg hL, if_neg hL', map_zero, smul_zero]

end Formalism.L2.G.Cmp

end
