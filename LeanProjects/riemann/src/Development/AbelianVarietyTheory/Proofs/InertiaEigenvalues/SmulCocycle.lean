import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.HerrClassFieldOfNorms
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocLatV
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFixingSubgroupMaxUnramifiedOfMemLocalGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAndDecompletion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlWcbInjective

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

namespace GlobalTheory.HerrExtUnit

theorem exists_unit (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) :
    let S := sit D.loc HW l (D.locA l) K s LL h
    let E : S.Comparison₂ := ((F l).E K s LL h).tie
    ∀ (e : S.W.DD S.W.one) (t : ↥S.W.one.L.T),
      S.W.N S.W.one = Submodule.span (LetA S.O S.n) {e} → S.W.φD S.W.one e = e →
      Submodule.span S.O {(t : S.W.one.V)} = S.W.one.L.T →
      ∃ u : (S.O)ˣ, ∀ a : S.O,
        E.jD S.W.one (a • e) = (1 : S.RW) ⊗ₜ[S.O] (((u : S.O) * a) • t) := by
  intro S E e t hN hφ ht
  obtain ⟨u, hu'⟩ : ∃ u : (S.O)ˣ, E.jD S.W.one e = (algebraMap S.O S.RW (u : S.O)) ⊗ₜ[S.O] t :=
    GlobalTheory.Cyc.UnitGen.main D HW F l K s LL h e t hN hφ ht
  refine ⟨u, fun a => ?_⟩
  rw [map_smul, hu', Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
    ← TensorProduct.tmul_smul, smul_smul, mul_comm]

theorem smul_cocycle (S : Sit) {T Tp : LocLat S.G S.Qp S.LL S.O} (ι : LatHom T.L Tp.L) (x : T.V)
    (g : S.G) (et : Tp.V) (hx : ι.f x = Tp.ρ g et - et) (b : S.O) :
    ι.f (b • x) = Tp.ρ g (b • et) - b • et := by
  rw [← algebraMap_smul S.LL b x, ← algebraMap_smul S.LL b et, map_smul, map_smul, hx, smul_sub]

theorem smul_proj (S : Sit) {Tp Z : LocLat S.G S.Qp S.LL S.O} (π : LatHom Tp.L Z.L)
    (et : Tp.V) (b : S.O) : b • π.f et = π.f (b • et) := by
  rw [← algebraMap_smul S.LL b et, map_smul, algebraMap_smul]

theorem over_Ks (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) :
    Formalism.MainNotions.ElementDenominator.coreHerrExt (sit D.loc HW l (D.locA l) K s LL h).W := by
  intro T Tp ι π _ _ c hc hE e he
  obtain ⟨hS, et, het, hgen, hcoc⟩ := hE
  obtain ⟨u, hu⟩ := exists_unit D HW F l K s LL h e ⟨π.f et, π.T_le _ het⟩ he.1 he.2.1 hgen
  refine ⟨u, fun x a hx y z hyz h1 h2 => ?_⟩
  have key := GlobalTheory.Cyc.dict_ext_Ks D HW F (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h
    T Tp _ ι π hS (sit D.loc HW l (D.locA l) K s LL h).W.one_triv
    ((u.1 * a) • ⟨et, het⟩) ((u.1 * a) • ⟨π.f et, π.T_le _ het⟩) x
    (smul_proj _ π et _) (by rw [hx]; exact hu a) ⟨(y, z), hyz⟩ h1 h2
    ((u.1 * a) • ⟨_, resFun_Z1T T _ c hc⟩)
    (fun g => smul_cocycle _ ι _ g et (hcoc g) _)
  exact key.trans (Submodule.Quotient.mk_smul _ _ _)

theorem over_K (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) :
    Formalism.MainNotions.ElementDenominator.coreHerrExtΔ (sit D.loc HW l (D.locA l) K s LL h).W := by
  intro _ hp T Tp ι π _ _ c hc hE e he
  obtain ⟨hS, et, het, hgen, hcoc⟩ := hE
  obtain ⟨u, hu⟩ := exists_unit D HW F l K s LL h e ⟨π.f et, π.T_le _ het⟩ he.1 he.2.1 hgen
  refine ⟨u, fun x a hδ hx y z hyz h1 h2 => ?_⟩
  have key := GlobalTheory.ExtDict.dict_K D HW F (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h
    (fun h2 => absurd h2 hp) T Tp _ ι π hS (sit D.loc HW l (D.locA l) K s LL h).W.one_triv
    ((u.1 * a) • ⟨et, het⟩) ((u.1 * a) • ⟨π.f et, π.T_le _ het⟩) x
    (smul_proj _ π et _) (by rw [hx]; exact hu a) hδ ⟨(y, z), hyz⟩ h1 h2
    ((u.1 * a) • ⟨c, hc⟩)
    (fun g => smul_cocycle _ ι _ g et (hcoc g) _)
  exact key.trans (Submodule.Quotient.mk_smul _ _ _)

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    Formalism.MainNotions.HerrComplexNaturality.HerrExtensionUpToUnit D HW F :=
  fun D HW F l _ K s LL h => ⟨over_Ks D HW F l K s LL h, over_K D HW F l K s LL h⟩

end GlobalTheory.HerrExtUnit
