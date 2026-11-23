import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.L2.Theta Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem hkRow_move (Rl : RealDat3 D A3 Ks) {i' i : Fin D.R.m} (h : i' = i) (k : ℕ) (P : PlE D.host)
    (u v : Fin (Rl.nW i') → D.what₂.LL) (u' v' : Fin (Rl.nW i) → D.what₂.LL) (hu : HEq u u') (hv : HEq v v')
    (hec : ∀ (α : GA D (Wc D i')) (R : Finset (GA D (Wc D i'))), IsHeckeAt (Wc D i') P k α →
      Bridge.IsDC (levG (Wc D i') (Rl.βW i') (Rl.datWp i' Rl.triv)) α R →
      (Rl.HW i' (sg0 D A3.A)).e ((Rl.FW i').j (sg0 D A3.A) u) =
        hkNorm Rl i' k P • heckeOn (Rl.MW i' (sg0 D A3.A)) R ((Rl.HW i' (sg0 D A3.A)).e ((Rl.FW i').j (sg0 D A3.A) v))) :
    ∀ (α : GA D (Wc D i)) (R : Finset (GA D (Wc D i))), IsHeckeAt (Wc D i) P k α →
      Bridge.IsDC (levG (Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α R →
      (Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) u') =
        hkNorm Rl i k P • heckeOn (Rl.MW i (sg0 D A3.A)) R ((Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) v')) := by
  subst h
  cases hu
  cases hv
  exact hec

theorem hkRow_of_ad (Rl : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x)
    (Y : NExpRealS Rl cG (ratDatR Rl cG kKs hk)) (H : NExpRealH Rl cG _ Y) (Sb : Finset (PlE D.host))
    (hfi : ∀ i x, HEq ((Y.fi i).e x) x) (hS : ∀ i, Sb ⊆ D.ntw.S0 i)
    (hec : ∀ j k P α Rr, 1 ≤ j → j ≤ D.R.m → HkDat Rl Sb (idxOf D j) k P α Rr → ∀ x : Fin (Rl.nW (idxOf D j)) → D.what₂.LL,
      (Rl.HW (idxOf D j) (sg0 D A3.A)).e ((Rl.FW (idxOf D j)).j (sg0 D A3.A) (H.hL j k P x)) =
        hkNorm Rl (idxOf D j) k P • heckeOn (Rl.MW (idxOf D j) (sg0 D A3.A)) Rr
          ((Rl.HW (idxOf D j) (sg0 D A3.A)).e ((Rl.FW (idxOf D j)).j (sg0 D A3.A) x))) :
    NExpHeckeRowX Rl cG _ Y H fun _ => LinearMap.id := by
  refine ⟨fun i k P hsp _ hoff h2 hkr α R hα hR x _ => ?_⟩
  obtain ⟨i', hi'⟩ := hoff
  exact hkRow_move Rl (idxOf_succ D i) k P (H.hL ((i : ℕ) + 1) k P x) x ((Y.fi i).e (H.hL ((i : ℕ) + 1) k P x)) ((Y.fi i).e x)
    (hfi i _).symm (hfi i _).symm
    (fun α' R' hα' hR' => hec ((i : ℕ) + 1) k P α' R' (by omega) (by have := i.2; omega)
      ⟨hsp, fun h => hi' (hS i' h), h2, hkr, hα', hR'⟩ x) α R hα hR

end Gen

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

theorem hkRowX {x : St P} (l : LC hL x) : NExpHeckeRowX x.m.z.R x.m.z.cG _ l.b.YS (hkH l) fun _ => LinearMap.id :=
  hkRow_of_ad x.m.z.R x.m.z.cG l.rat.kKs l.rat.hk l.b.YS (hkH l) l.rat.In.Sb l.b.fi l.b.Sb_le l.rat.rat.hecke

theorem hkRowL {x : St P} (L : LocAll (lay0 (Dof x))) (l : LC hL x) :
    NExpHeckeRowX (datL x L).R (datL x L).cG _ (ysL L l) (hkHL L l) fun _ => LinearMap.id :=
  ⟨(by with_unfolding_all exact ((hkRowX l).tie :))⟩

end GlobalTheory.HeightCounting.Fin3
