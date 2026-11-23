import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.HomogeneousComponentMulForm
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepTwoFilt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationExists
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PExtension
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepTwoPiece
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PIdealTwistFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace SnapperQuotFilt

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

def pieceIso (N₀ N₁ : FinGradedSub (S := S) (x := x) E) {g : E} {e : ℤ} {pp : Ideal (Poly S N)}
    (Q : LineBundle S x) (c : ℤ) (hpp : pp.IsPrime) (hg : g ∈ N₁.piece e)
    (hN : ∀ c, N₁.piece c = N₀.piece c ⊔ Submodule.span S
      {z | ∃ (f : Poly S N) (d : ℕ), f.IsHomogeneous d ∧ e + d = c ∧ z = aeval x f • g})
    (hiff : ∀ (f : Poly S N) (d : ℕ), f.IsHomogeneous d → (f ∈ pp ↔ aeval x f • g ∈ N₀.piece (e + d))) :
    QuotIso ((N₁.tildeSys 0).twist (Q.twist (twistSys S x c))) ((N₀.tildeSys 0).twist (Q.twist (twistSys S x c)))
      (Q.twist (twistSys S x (c - e))) ((Q.twist (twistSys S x (c - e))).twist (idealSys x pp)) where
  equiv I := (LinearEquiv.ofBijective (StepTwo.Piece.gBar N₀ N₁ Q c hg hiff I)
    (StepTwo.Piece.gBar_bijective N₀ N₁ Q c hpp hg hN hiff I)).symm
  comm I J h y := by
    apply (LinearEquiv.ofBijective _ (StepTwo.Piece.gBar_bijective N₀ N₁ Q c hpp hg hN hiff J)).injective
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.ofBijective_apply, StepTwo.Piece.gBar_comm]
    congr 1
    exact ((LinearEquiv.ofBijective _ (StepTwo.Piece.gBar_bijective N₀ N₁ Q c hpp hg hN hiff I)).apply_symm_apply
      y).symm

end SnapperQuotFilt

open SnapperQuotFilt in

theorem SnapperQuotFilt.proof : SnapperQuotFilt.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F₁ F₂ hfg hle J hJ hxJ hJF
  classical
  have hfg₂ : ∀ I, (F₂.sub I).FG := fg_of_le F₁ F₂ hfg hle
  obtain ⟨M₁, -, hM₁⟩ := Extension.proof k Ω N x E F₁ hfg
  obtain ⟨M₀, -, hM₀⟩ := Extension.proof k Ω N x E F₂ hfg₂
  obtain ⟨H, hHJ, hHspan, hHhom⟩ := IdealTwistFamily.exists_finset_forms J hJ
  set hs : Fin H.card → Poly k N := fun l => (H.equivFin.symm l : Poly k N) with hs_def
  have hrange : Set.range hs = ↑H := by
    ext f
    constructor
    · rintro ⟨l, rfl⟩
      exact (H.equivFin.symm l).2
    · intro hf
      exact ⟨H.equivFin ⟨f, hf⟩, by simp [hs_def]⟩
  have hhom : ∀ l, (hs l).IsHomogeneous (hs l).totalDegree := fun l => hHhom _ (H.equivFin.symm l).2
  have hsJ : ∀ l, hs l ∈ J := fun l => hHJ (H.equivFin.symm l).2
  set A := gsup M₁ M₀ with hA_def
  set B := gsup M₀ (gmul A hs fun l => (hs l).totalDegree) with hB_def
  have hA : ∀ I, A.tilde 0 I = F₁.sub I := fun I => by
    rw [hA_def, tilde_gsup, hM₁, hM₀]
    exact sup_eq_left.mpr (hle I)
  have hB : ∀ I, B.tilde 0 I = F₂.sub I := fun I => by
    rw [hB_def, tilde_gsup, hM₀]
    exact sup_eq_left.mpr ((tilde_gmul_le A hs _ hhom hsJ F₁.toSubSystem (fun I => (hA I).le) I).trans (hJF I))
  have hBA : ∀ c, B.piece c ≤ A.piece c := fun c => by
    refine sup_le le_sup_right (Submodule.span_le.mpr ?_)
    rintro _ ⟨l, b, m, hm, hb, rfl⟩
    have := A.smul_mem _ b (hs l) m (hhom l) hm
    rwa [hb] at this
  have hkill : ∀ (f : Poly k N) (e : ℕ), f ∈ J → f.IsHomogeneous e → ∀ (a : ℤ), ∀ z ∈ A.piece a,
      aeval x f • z ∈ B.piece (a + e) := fun f e hf hfe a z hz =>
    Submodule.mem_sup_right (smul_mem_gmul A hs _ hhom (by rw [hrange, hHspan]) hf hfe hz)
  obtain ⟨n, Nf, g, deg, pr, h0, hlast, hk⟩ :=
    StepTwo.Filt.proof PrimeFiltration.Exists.proof k Ω N x E A B hBA J hkill
  have hstep : ∀ (j : Fin n) (c : ℤ), (Nf j.castSucc).piece c ≤ (Nf j.succ).piece c := fun j c => by
    rw [(hk j).2.2.2.2.2.1 c]
    exact le_sup_left
  have hmono : ∀ (i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) (c : ℤ),
      (Nf ⟨i, by omega⟩).piece c ≤ (Nf ⟨j, by omega⟩).piece c := by
    intro i j hij hj c
    induction j with
    | zero =>
      obtain rfl : i = 0 := by omega
      exact le_rfl
    | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with h | h
      · subst h
        exact le_rfl
      · exact (ih (by omega) (by omega)).trans (hstep ⟨j, by omega⟩ c)
  have hNf : ∀ m (hm : m ≤ n), Nf ⟨min m n, by omega⟩ = Nf ⟨m, by omega⟩ := fun m hm =>
    congrArg Nf (Fin.ext (Nat.min_eq_left hm))
  set G : ℕ → SubFamily k x E := fun m => tildeFam (Nf ⟨min m n, by omega⟩) with hG_def
  have hGle : ∀ m I, (G m).sub I ≤ F₁.sub I := fun m I => by
    rw [← hA, ← hlast]
    exact tilde_mono (hmono _ n (by omega) le_rfl) 0 I
  refine ⟨n, G, pr, fun m => -deg m, fun m I => fg_of_le F₁ (G m) hfg (hGle m) I, ?_, ?_, ?_, ?_, ?_⟩
  · refine SubSystem.ext_sub fun I => ?_
    change (Nf ⟨min 0 n, _⟩).tilde 0 I = F₂.sub I
    rw [hNf 0 (Nat.zero_le n), Fin.mk_zero, h0, hB]
  · refine SubSystem.ext_sub fun I => ?_
    change (Nf ⟨min n n, _⟩).tilde 0 I = F₁.sub I
    rw [hNf n le_rfl]
    change (Nf (Fin.last n)).tilde 0 I = F₁.sub I
    rw [hlast, hA]
  · intro m hm I
    change (Nf ⟨min m n, _⟩).tilde 0 I ≤ (Nf ⟨min (m + 1) n, _⟩).tilde 0 I
    rw [hNf m hm.le, hNf (m + 1) hm]
    exact tilde_mono (hstep ⟨m, hm⟩) 0 I
  · intro m
    obtain ⟨hp, hh, -, hJf, -⟩ := hk m
    exact ⟨hp, hh, le_of_forms hJ hJf⟩
  · intro m t L n' c
    obtain ⟨hp, -, -, -, hg, hN, hiff⟩ := hk m
    dsimp only
    have e1 : (G (m + 1)).toSubSystem = (Nf m.succ).tildeSys 0 := by
      change (Nf ⟨min (m + 1) n, _⟩).tildeSys 0 = _
      rw [hNf _ m.2]
      rfl
    have e2 : (G m).toSubSystem = (Nf m.castSucc).tildeSys 0 := by
      change (Nf ⟨min m n, _⟩).tildeSys 0 = _
      rw [hNf _ m.2.le]
      rfl
    have hs1 : ∀ T : SubSystem k x E, (T.twistPows t (fun j => (L j).toSubSystem) n').twist (twistSys k x c) =
        T.twist ((powsBundle t L n').toSubSystem.twist (twistSys k x c)) := fun T => by
      rw [twistPows_eq, twist_twist]
    have ht1 : ((twistSys k x (-deg m)).twistPows t (fun j => (L j).toSubSystem) n').twist (twistSys k x c) =
        (powsBundle t L n').toSubSystem.twist (twistSys k x (c - deg m)) := by
      rw [twistPows_eq]
      refine SubSystem.ext_sub fun I => ?_
      simp only [SubSystem.twist_sub_eq_mul_of_line]
      rw [sub_eq_add_neg, ← twistSys_sub_mul]
      ring
    have ht2 : (((twistSys k x (-deg m)).twist (idealSys x (pr m))).twistPows t (fun j => (L j).toSubSystem)
        n').twist (twistSys k x c) =
        ((powsBundle t L n').toSubSystem.twist (twistSys k x (c - deg m))).twist (idealSys x (pr m)) := by
      rw [twistPows_eq]
      refine SubSystem.ext_sub fun I => ?_
      simp only [SubSystem.twist_sub_eq_mul_of_line]
      rw [sub_eq_add_neg, ← twistSys_sub_mul]
      ring
    rw [e1, e2, hs1, hs1, ht1, ht2]
    exact ⟨pieceIso (Nf m.castSucc) (Nf m.succ) (powsBundle t L n') c hp hg hN hiff⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
