import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFixingSubgroupMaxUnramifiedOfMemLocalGalois

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open TensorProduct

noncomputable section

namespace GlobalTheory.ExtDict

theorem dict_K_free : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; (ell S = 2 → ∃ i : S.K, i ^ 2 = -1) → ∀ (T Yt Z : LocLat S.G S.Qp S.LL S.O) (ι : LatHom T.L Yt.L) (π : LatHom Yt.L Z.L), IsSESLat (Qp := S.Qp) ι π → ∀ (yt : ↥Yt.L.T) (z : ↥Z.L.T) (e : S.W.DD Yt), (z : Z.V) = π.f yt → E.jD Z (S.W.map π e) = (1 : S.RW) ⊗ₜ[S.O] z → (∀ δ ∈ S.W.DelF, S.W.γD Yt δ e = e) → ∀ pr : ↥(S.W.wachCocyclesDelta T), S.W.map ι (pr : S.W.DD T × S.W.DD T).1 = S.W.φD Yt e - e → S.W.map ι (pr : S.W.DD T × S.W.DD T).2 = S.W.γD Yt S.W.gamK e - e → ∀ c : ↥(latticeCocycles T.L), (∀ g : S.G, ι.f ((c : S.G → T.V) g) = Yt.ρ g yt - yt) → S.W.clK T pr = Submodule.Quotient.mk c := by
  intro D HW F l _ K s LL h S E hi T Yt Z ι π hs yt z e hz he hδ pr h1 h2 c hc
  have hp : ell S = l := (D.loc l).PD_p K
  have hG : l = 2 → GK K ≤ Gj K 2 := fun hl => by
    obtain ⟨i, hi⟩ := hi (hp.trans hl)
    exact localGalois_le_cyclotomicLevelTwo_of_sqrt_neg_one K hl i hi
  haveI : IsTopologicalRing S.LL := inferInstanceAs (IsTopologicalRing ↥LL.1.toSubring)
  haveI : T2Space S.LL := inferInstanceAs (T2Space ↥LL.1)
  exact dict_of_dense S E (algebraMap_RW_injective LL)
    (fun hl => DelF_eq_one (D.loc l) S.W (D.locA l) hG (hp.symm.trans hl))
    (dense_DelF_gamK (D.loc l) S.W (D.locA l) hG) T Yt Z ι π hs yt z e hz he hδ pr h1 h2 c hc

end GlobalTheory.ExtDict
