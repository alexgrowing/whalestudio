import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.DuFormulaOfFibreCount
import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.CardFilterSubtype

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

variable {D : D7} {u : D.what₂.Word}

def DUPt0F (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0),
  ∃ (γ : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) →
      UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (κ : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → T.cls0.lev.U)
    (Mu : ∀ g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c),
      {x : (D.fm u).lv 0 v ((D.fm u).dn 0 v c g) // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x = 1} →
        UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    DnMvs T v c γ η κ ∧ (∀ g x, IsUpMvF T v ((D.fm u).dn 0 v c g) x.1 (Mu g x)) ∧
    ∃ (ι : ∀ g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c),
        {x : (D.fm u).lv 0 v ((D.fm u).dn 0 v c g) // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x = 1} → (D.fm u).lk 0 v c)
      (τ : ((D.mem u).A.Fv v)ˣ ≃ ((D.mem u).A.Fv v)ˣ),
      (∀ g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c), g ≠ 0 → ∀ x, g (ι g x) = 1) ∧
      (∀ g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c), g ≠ 0 → ∀ y, g y = 1 → ∃! x, ι g x = y) ∧
      ∀ G ∈ AdFun T.cls0.lev (embT D),
        (∀ p : PD D u v c, ι p.1.1 p.2 = (D.fm u).te 0 v c →
          G (T.cls0.y c * hcomp T (η p.1.1) (κ p.1.1) (Mu p.1.1 p.2)) = G (T.cls0.y c)) ∧
        (∀ (p : PD D u v c) (q : PE D u v c), ι p.1.1 p.2 = ι q.1.1 q.2 →
          G (T.cls0.y c * hcomp T (η p.1.1) (κ p.1.1) (Mu p.1.1 p.2)) =
          G (T.cls0.y c * hcomp T (η q.1.1) (κ q.1.1) (Mu q.1.1 q.2))) ∧
        (∀ p q : PE D u v c, ι p.1.1 p.2 = ι q.1.1 q.2 →
          G (T.cls0.y c * hcomp T (η p.1.1) (κ p.1.1) (Mu p.1.1 p.2)) =
          G (T.cls0.y c * hcomp T (η q.1.1) (κ q.1.1) (Mu q.1.1 q.2))) ∧
        (∀ (a : ((D.mem u).A.Fv v)ˣ) (q : PE D u v c), ι q.1.1 q.2 = (a : (D.mem u).A.Fv v) • (D.fm u).te 0 v c →
          ∀ (k : ℤ), (k : (D.mem u).A.Fv v) = ((τ a : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) →
          ∀ δ, IsDia T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 k δ →
          G (T.cls0.y c * hcomp T (η q.1.1) (κ q.1.1) (Mu q.1.1 q.2)) = G (T.cls0.y c * δ))

set_option maxHeartbeats 4000000 in
theorem duFib_of_pt (T : Forms0 D u) (h : DUPt0F T) : DUFib0F T := by
  intro v c
  obtain ⟨γ, η, κ, Mu, hmv, hMu, ι, τ, hι, hu, hval⟩ := h v c
  have hK : Fintype.card ((D.mem u).A.Fv v) = (D.mem u).A.T := (D.mem u).A.card_Fv v
  have hr : Module.finrank ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) = D.R.N 0 := (D.fm u).lk_rank 0 v c
  have hte := (D.fm u).te_ne 0 v c
  refine ⟨γ, η, κ, Mu, hmv, hMu, fun p => ι p.1.1 p.2, fun q => ι q.1.1 q.2, τ, fun y => ?_, fun y => ?_, hval⟩
  · refine (card_sig_fib (A := {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // g ≠ 0})
      (fun g x => ι g.1 x) (fun g y => g.1 y = 1) (fun g x => hι g.1 g.2 x) (fun g y hy => hu g.1 g.2 y hy) y).trans ?_
    rw [card_filter_subtype (fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) => g ≠ 0) (fun g => g y = 1)]
    split_ifs with hy
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro g - ⟨-, h1⟩
      rw [hy, map_zero] at h1
      exact zero_ne_one h1
    · rw [Finset.filter_congr (q := fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) => g y = 1)
        (fun g _ => ⟨fun h => h.2, fun h => ⟨fun h0 => by rw [h0, LinearMap.zero_apply] at h; exact zero_ne_one h, h⟩⟩),
        card_dual_one y hy, hK, hr]
  · refine (card_sig_fib (A := {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // g ((D.fm u).te 0 v c) = 1})
      (fun g x => ι g.1 x) (fun g y => g.1 y = 1) (fun g x => hι g.1 (fun h0 => ?_) x)
      (fun g y hy => hu g.1 (fun h0 => ?_) y hy) y).trans ?_
    · have := g.2; rw [h0, LinearMap.zero_apply] at this; exact zero_ne_one this
    · have := g.2; rw [h0, LinearMap.zero_apply] at this; exact zero_ne_one this
    rw [card_filter_subtype (fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) => g ((D.fm u).te 0 v c) = 1)
      (fun g => g y = 1)]
    split_ifs with h1 h2
    · rw [h1, Finset.filter_congr (q := fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) =>
        g ((D.fm u).te 0 v c) = 1) (fun g _ => and_self_iff), card_dual_one _ hte, hK, hr]
    · exact card_dual_line _ y h2 h1
    · rw [card_dual_two _ y hte h2, hK, hr]

theorem dUAll_of_pt (h : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), DUPt0F T) : Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.DUAll := fun D u T => du_formula_of_fibre_count T (duFib_of_pt T (h D u T))

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
