import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.NatTr0Sum

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

section Pairs

variable (D : D7) (u : D.what₂.Word)

abbrev PD (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) : Type :=
  Σ g : {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // g ((D.fm u).te 0 v c) = 1},
    {x : (D.fm u).lv 0 v ((D.fm u).dn 0 v c g.1) // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g.1) x = 1}

abbrev PE (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) : Type :=
  Σ g : {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // g ≠ 0},
    {x : (D.fm u).lv 0 v ((D.fm u).dn 0 v c g.1) // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g.1) x = 1}

end Pairs

variable {D : D7} {u : D.what₂.Word}

def DnMvs (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (γ : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) →
      UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (κ : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → T.cls0.lev.U) : Prop :=
  ∀ g, g ≠ 0 → (∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') (η g).1 = 1) ∧
    bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ g).1 *
      (T.cls0.y ((D.fm u).dn 0 v c g)).1 = (T.cls0.y c).1 * (η g).1 * (κ g).1 ∧
    ∀ h, (D.fm u).dnT 0 v c g h = natTr0 T (γ g) (κ g) h

def DUFib0F (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0),
  ∃ (γ : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) →
      UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (κ : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → T.cls0.lev.U)
    (Mu : ∀ g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c),
      {x : (D.fm u).lv 0 v ((D.fm u).dn 0 v c g) // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x = 1} →
        UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    DnMvs T v c γ η κ ∧ (∀ g x, IsUpMvF T v ((D.fm u).dn 0 v c g) x.1 (Mu g x)) ∧
    ∃ (πD : PD D u v c → (D.fm u).lk 0 v c) (πE : PE D u v c → (D.fm u).lk 0 v c)
      (τ : ((D.mem u).A.Fv v)ˣ ≃ ((D.mem u).A.Fv v)ˣ),
      (∀ x, (Finset.univ.filter (fun q => πE q = x)).card =
        if x = 0 then 0 else (D.mem u).A.T ^ (D.R.N 0 - 1)) ∧
      (∀ x, (Finset.univ.filter (fun p => πD p = x)).card =
        if x = (D.fm u).te 0 v c then (D.mem u).A.T ^ (D.R.N 0 - 1)
        else if x ∈ Submodule.span ((D.mem u).A.Fv v) {(D.fm u).te 0 v c} then 0
        else (D.mem u).A.T ^ (D.R.N 0 - 2)) ∧
      ∀ G ∈ AdFun T.cls0.lev (embT D),
        (∀ p, πD p = (D.fm u).te 0 v c →
          G (T.cls0.y c * hcomp T (η p.1.1) (κ p.1.1) (Mu p.1.1 p.2)) = G (T.cls0.y c)) ∧
        (∀ p q, πD p = πE q → G (T.cls0.y c * hcomp T (η p.1.1) (κ p.1.1) (Mu p.1.1 p.2)) =
          G (T.cls0.y c * hcomp T (η q.1.1) (κ q.1.1) (Mu q.1.1 q.2))) ∧
        (∀ p q, πE p = πE q → G (T.cls0.y c * hcomp T (η p.1.1) (κ p.1.1) (Mu p.1.1 p.2)) =
          G (T.cls0.y c * hcomp T (η q.1.1) (κ q.1.1) (Mu q.1.1 q.2))) ∧
        (∀ (a : ((D.mem u).A.Fv v)ˣ) q, πE q = (a : (D.mem u).A.Fv v) • (D.fm u).te 0 v c →
          ∀ (k : ℤ), (k : (D.mem u).A.Fv v) = ((τ a : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) →
          ∀ δ, IsDia T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 k δ →
          G (T.cls0.y c * hcomp T (η q.1.1) (κ q.1.1) (Mu q.1.1 q.2)) = G (T.cls0.y c * δ))

set_option maxHeartbeats 4000000 in

theorem dopU_eq (T : Forms0 D u) (v : (D.mem u).A.vT) (ψ : Fn D u 0)
    {G : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → Fr D 0 (Nat.zero_le _) → ℂ}
    (hG : G ∈ AdFun T.cls0.lev (embT D))
    (hψ : ∀ c, ψ c = fun s => G (T.cls0.y c) (T.val0.eY s)) (c : (D.mem u).C.cls 0)
    (γ : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) →
      UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (κ : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → T.cls0.lev.U)
    (Mu : ∀ g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c),
      {x : (D.fm u).lv 0 v ((D.fm u).dn 0 v c g) // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x = 1} →
        UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hmv : DnMvs T v c γ η κ) (hMu : ∀ g x, IsUpMvF T v ((D.fm u).dn 0 v c g) x.1 (Mu g x)) :
    Dop D u 0 v (Uop D u 0 v ψ) c = fun s => ∑ p : PD D u v c,
      G (T.cls0.y c * hcomp T (η p.1.1) (κ p.1.1) (Mu p.1.1 p.2)) (T.val0.eY s) := by
  funext s
  simp only [Formalism.MainNotions.product_first_zeroth_parts.Dop, LinearMap.pi_apply, LinearMap.sum_apply, Finset.sum_apply]
  rw [Finset.sum_subtype (Finset.univ.filter (fun x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) =>
    x ((D.fm u).te 0 v c) = 1))
    (p := fun x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) => x ((D.fm u).te 0 v c) = 1) (by intro x; simp),
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe]
  have hg0 : g.1 ≠ 0 := by
    intro h0; have := g.2; rw [h0, LinearMap.zero_apply] at this; exact zero_ne_one this
  obtain ⟨-, h2, h3⟩ := hmv g.1 hg0
  exact congrFun (dnU_term T v ψ hG hψ c g.1 (γ g.1) (η g.1) (κ g.1) h2 h3 (Mu g.1) (hMu g.1)) s

set_option maxHeartbeats 4000000 in

theorem eopU_eq (T : Forms0 D u) (v : (D.mem u).A.vT) (ψ : Fn D u 0)
    {G : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → Fr D 0 (Nat.zero_le _) → ℂ}
    (hG : G ∈ AdFun T.cls0.lev (embT D))
    (hψ : ∀ c, ψ c = fun s => G (T.cls0.y c) (T.val0.eY s)) (c : (D.mem u).C.cls 0)
    (γ : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) →
      UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (κ : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → T.cls0.lev.U)
    (Mu : ∀ g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c),
      {x : (D.fm u).lv 0 v ((D.fm u).dn 0 v c g) // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x = 1} →
        UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hmv : DnMvs T v c γ η κ) (hMu : ∀ g x, IsUpMvF T v ((D.fm u).dn 0 v c g) x.1 (Mu g x)) :
    Eop D u 0 v (Uop D u 0 v ψ) c = fun s => ∑ p : PE D u v c,
      G (T.cls0.y c * hcomp T (η p.1.1) (κ p.1.1) (Mu p.1.1 p.2)) (T.val0.eY s) := by
  funext s
  simp only [Formalism.MainNotions.product_first_zeroth_parts.Eop, LinearMap.pi_apply, LinearMap.sum_apply, Finset.sum_apply]
  rw [Finset.sum_subtype (Finset.univ.filter (fun x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) => x ≠ 0))
    (p := fun x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) => x ≠ 0) (by intro x; simp),
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe]
  obtain ⟨-, h2, h3⟩ := hmv g.1 g.2
  exact congrFun (dnU_term T v ψ hG hψ c g.1 (γ g.1) (η g.1) (κ g.1) h2 h3 (Mu g.1) (hMu g.1)) s

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
