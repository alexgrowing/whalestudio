import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.IsLatTupSmulIff

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

theorem mem_funMod_iff {p : ℕ} (G : GAtP p) (Hv : G.P.Tup → Submodule G.O G.P.Xsp) (Fn : G.Fn) :
    Fn ∈ G.funMod Hv ↔ ∀ i, (∀ L, G.P.IsLatTup L → Fn i L ∈ Hv L) ∧ (∀ L, ¬ G.P.IsLatTup L → Fn i L = 0) ∧
      ∀ (γ : (G.lev i).Γ) (L : G.P.Tup), Fn i ((G.lev i).smul γ L) = ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (Fn i L) := by
  unfold GAtP.funMod Level.funMod
  simp only [Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.mem_ker, LinearMap.proj_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.restrictScalars_apply, sub_eq_zero, and_assoc]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {LL : Type} [Field LL] {p : ℕ}
  {S : StepLevel F E σ J T f bad} {emb : Tau → E →+* ℂ} {embLL : LL →+* ℂ}
  {G : GAtP p} {e : LL →+* G.Kf} {A : LocAt F E n G} {pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau}
  {V cls : Type} [AddCommGroup V] [Module LL V] {embV : V →ₛₗ[embLL] (cls → Frames (gramC J emb) → ℂ)}
  {yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F)}

theorem cmpC_mem_funMod (tE : Tau → E →+* LL) (htE : ∀ τ x, embLL (tE τ x) = emb τ x)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (hBs : cT (σ : E →+* E) A.B.1 * J * A.B.1 = 1) (hA : A.ActB)
    (hex : ValEx S emb embLL G A pos embV yc)
    (hpos : ∀ v (s : Fin (G.P.n' v)) (x : E),
      e (tE (pos ⟨v, s⟩) (if Even s.val then x else σ x)) = G.P.ι v ((G.P.σ v ^ s.val) (A.iw v x)))
    (hchi : ∀ i (γ : (G.lev i).Γ) (κ : S.U), A.IsAway i γ κ.1 →
      ∃ r : LL, embLL r = (S.chi κ : ℂ) ∧ algebraMap G.O G.Kf ((G.lev i).χ γ : G.O) * e r = 1)
    (hi : EvInj emb G A pos (J := J)) (hp : PtEx S G A yc)
    (hU : ∀ i (γ : (G.lev i).Γ), A.gamI i γ ∈ UJ (σ : E →+* E) J)
    (haw : ∀ i (γ : (G.lev i).Γ), ∃ κ : S.U, A.IsAway i γ κ.1)
    (Hv : G.P.Tup → Submodule G.O G.P.Xsp) (x : V)
    (hval : ∀ i L, G.P.IsLatTup L → MvPolynomial.map e (valC S emb embLL G A pos embV yc x i L) ∈ Hv L) :
    cmpC S emb embLL G e A pos embV yc x ∈ G.funMod Hv := by
  rw [mem_funMod_iff]
  intro i
  refine ⟨fun L hL => ?_, fun L hL => ?_, fun γ L => ?_⟩
  · unfold cmpC
    rw [if_pos hL]
    exact hval i L hL
  · unfold cmpC
    rw [if_neg hL]
  · exact cmpC_equiv tE htE hc hBs hA hex hpos hchi hi hp hU haw x i γ L

end Formalism.L2.G.Cmp

end
