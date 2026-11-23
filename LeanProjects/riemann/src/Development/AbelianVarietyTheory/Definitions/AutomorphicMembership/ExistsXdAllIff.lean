import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal

noncomputable section

namespace GlobalTheory.HeightCounting.Up.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {hL : GlobalTheory.Published.LocalLanglandsGL}

theorem AtMem.imp {p q : LayP hL} (h : AtMem hL p)
    (hpq : ∀ K B f T w Z Wt p0 t nch n c, p K B f T w Z Wt p0 t nch n c → q K B f T w Z Wt p0 t nch n c) : AtMem hL q :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c a b d =>
    hpq _ B f T w Z Wt p0 t nch n c (H kp w Z Wt p0 t nch n xd c a b d)

theorem AtMem.and {p q : LayP hL} (h : AtMem hL p) (h' : AtMem hL q) :
    AtMem hL fun K B f T w Z Wt p0 t nch n c => p K B f T w Z Wt p0 t nch n c ∧ q K B f T w Z Wt p0 t nch n c :=
  EvG.imp (EvG.inter h h') fun _ _ _ _ _ hK => large₂.imp (large₂.inter hK.1 hK.2) fun _ _ _ _ H kp w Z Wt p0 t nch n xd c a b d =>
    ⟨H.1 kp w Z Wt p0 t nch n xd c a b d, H.2 kp w Z Wt p0 t nch n xd c a b d⟩

theorem rootsLL_pow {D : D7} (h : RootsLL D) : ∃ ζ : D.what₂.LL, ζ ^ D.what₂.restRowsFiniteGroupCard = 1 ∧ orderOf ζ = D.what₂.restRowsFiniteGroupCard ∧ 0 < orderOf ζ := by
  obtain ⟨ζ, hζ⟩ := h
  exact ⟨ζ, hζ.pow_eq_one, hζ.eq_orderOf.symm, hζ.eq_orderOf ▸ D.what₂.restRowsFiniteGroupCard_pos⟩

theorem sumUsed_ref {D : D7} {M : MtFam D} (h : SumUsed D M) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    GlobalTheory.CoefDuty.ClassSum (M D.what₂.mu0 j h1 h2) := h _ (Or.inl rfl) j h1 h2

theorem used_loc {D : D7} (i : D.nd.Loc) : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) :=
  Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩

theorem sumUsed_loc {D : D7} {M : MtFam D} (h : SumUsed D M) (i : D.nd.Loc) : GlobalTheory.CoefDuty.ClassSum (M.loc i) :=
  h _ (used_loc i) _ _ _

theorem exists_xdAll_iff (D : D7) : (∃ xd : ThData D, XdAll xd) ↔
    ∀ i j b, 1 ≤ j → j ≤ D.R.m → ∀ (a : D.nexp.Dat i j b) (u : D.nexp.U), D.nexp.actG i j b u (D.nexp.th i j b a) =
      ((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) • D.nexp.th i j b a := by
  constructor
  · rintro ⟨xd, h⟩ i j b h1 h2 a u
    exact xd.thetaBase_invariant_action i j b a (by rw [h i j b h1 h2]; trivial) u
  · intro h
    refine ⟨⟨fun i j b => {_a | 1 ≤ j ∧ j ≤ D.R.m}, fun i j b a ha u => h i j b ha.1 ha.2 a u⟩, fun i j b h1 h2 => ?_⟩
    exact Set.eq_univ_of_forall fun _ => ⟨h1, h2⟩

theorem isot_withLoc {D : D7} (L : LocAll (lay0 D)) : Rows.IsotInternal (withLoc L).what₂ ↔ Rows.IsotInternal D.what₂ := Iff.rfl

end GlobalTheory.HeightCounting.Up.Model

end
