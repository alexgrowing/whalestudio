import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FiberCount

noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DensCong : Prop :=
  ∀ (F E : Type) {_ : Field F} {_ : ValuativeRel F} {_ : TopologicalSpace F} {_ : CommRing E} {_ : Algebra F E}
    {_ : TopologicalSpace E} {_ : MeasurableSpace E} (M : Loc.Model F E) (V : Type) {_ : AddCommGroup V}
    {_ : Module E V} (H : Loc.HermSp M V) (ϖ : 𝒪[F]) (abelian₂ : Submodule M.L.O V) (ι : Type) {_ : Fintype ι}
    {_ : DecidableEq ι} (G A : Matrix ι ι E),
    (∀ i j, A i j ∈ M.L.O) → (∃ y ∈ M.L.O, A.det * y = 1) →
      H.dens ϖ abelian₂ ((A.map M.L.cj).transpose * G * A) = H.dens ϖ abelian₂ G

section Steps

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)

def GaPlusTh : Prop :=
  (∀ p, Agree δ M p) → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] → PrimeHyp D u (Tu D u') →
  ∀ (w w' : Point D.host.E (D.R.rS + 1)) (Z Z' : PairVal.MatR D), kind w = kind w' → AtMat w Z → AtMat w' Z' →
  ∀ p, FCount.thZ M δ u u' w Z p ≠ none → FCount.thZ M δ u u' w Z p = FCount.thZ M δ u u' w' Z' p →
    ∃ A : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep,
      (∀ i j, A i j ∈ (M p).L.O) ∧ (∃ y ∈ (M p).L.O, A.det * y = 1) ∧
      CntLocal.GaPlus M δ p (CntLocal.Tn u) (CntLocal.Tn u') Z' =
        (A.map (M p).L.cj).transpose * CntLocal.GaPlus M δ p (CntLocal.Tn u) (CntLocal.Tn u') Z * A

end Steps

theorem densTh_of {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    {δ : ∀ p : PlF D, (D.s.atP p).Fp} {L : CntLocal.LocSp D M} {u u' : D.what₂.Word}
    (hC : DensCong) (hG : GaPlusTh M δ u u') : FCount.DensTh M δ L u u' := by
  intro hA hT hPH ϖ _ w w' Z Z' hk hZ hZ' p hne heq
  obtain ⟨A, hAO, hAd, hGa⟩ := hG hA hT hPH w w' Z Z' hk hZ hZ' p hne heq
  unfold CntLocal.densP
  rw [hGa]
  exact (hC (D.s.atP p).Fp (D.s.atP p).Ep (M p) (L.V p) (L.H p) (ϖ p) (CntLocal.lattice₂ L p (VS D).L0)
    (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (CntLocal.GaPlus M δ p (CntLocal.Tn u) (CntLocal.Tn u') Z) A hAO hAd).symm

end Formalism.L2.SG.Pf.Coef
