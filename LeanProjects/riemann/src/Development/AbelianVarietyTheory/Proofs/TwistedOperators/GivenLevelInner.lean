import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaAtMoveLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCColumnLatticeOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAtPlacesMemCompletedHermitianLa
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeCompletionAtPlacesOfFinPartMemHatLatti
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFrameFinitePartMulOfCarriesLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffFrameStabiliserAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeStabilizerOfLocalIntegralInBasis
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGLintOfEntries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryInBasisIntegralAtConjugatePlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LastRowLat

open GlobalTheory.FinPl (Moves Lat)
open Matrix

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

variable (G) in

theorem givenLevel_inner (t : T) (w : Pl D.host.E) : ∀ X : ℕ × ℕ, 1 ≤ X.1 → 1 ≤ X.2 →
    givenLevel G t w X = GlobalTheory.SplitWeil.KO (Kw w) _
  | (_ + 1, _ + 1), _, _ => rfl
  | (0, _), h, _ => absurd h (by omega)
  | (_ + 1, 0), _, h => absurd h (by omega)

theorem inBasis_KO {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E)
    (K : Subgroup (GL (Fin n') (Kw w))) (hK : K = GlobalTheory.SplitWeil.KO (Kw w) (Fin n')) (hx : inBasis h β w x ∈ K) :
    inBasis rfl β w x ∈ GlobalTheory.SplitWeil.KO (Kw w) (Fin n) := by
  subst h; subst hK; exact hx

theorem isFrame_grid (S : GridChoice W U) : ∀ {i : ℕ}, 1 ≤ i → i ≤ D.R.m → IsFrame (S.B.β i D.R.m) (G.Λ (.grid i D.R.m))
  | 0, h, _ => absurd h (by omega)
  | i + 1, _, hi => S.B.isFrame (i + 1) D.R.m (by omega) hi le_rfl

theorem isSelfDual_grid : ∀ {i : ℕ}, 1 ≤ i → i ≤ D.R.m → IsSelfDualC (G.V (.grid i D.R.m)) (G.Λ (.grid i D.R.m))
  | 0, h, _ => absurd h (by omega)
  | i + 1, _, hi => (G.sp.V_is (i + 1) D.R.m (by omega) hi le_rfl).sd

theorem levRow_mem_St (S : GridChoice W U) (t : T) (k : FinPt G (.grid D.R.m D.R.m))
    (hk : finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl) :
    finG (G.V (.grid D.R.m D.R.m)) k ∈ St (S.B.β D.R.m D.R.m) := by
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hfr := isFrame_grid S hm le_rfl
  have hsd := isSelfDual_grid (G := G) hm le_rfl
  have hU : finG (G.V (.grid D.R.m D.R.m)) k ∈ UA D.sp.cm (G.V (.grid D.R.m D.R.m)).gram := GlobalTheory.LevSplit.finE_mem_UA _ _
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hk
  have hP : ∀ w0 ∈ locPl G t, inBasis rfl (S.B.β D.R.m D.R.m) w0 (finG (G.V (.grid D.R.m D.R.m)) k) ∈ GlobalTheory.SplitWeil.KO (Kw w0) _ := fun w0 hw0 =>
    inBasis_KO _ _ _ _ _ (givenLevel_inner G t w0 (D.R.m, D.R.m) hm hm) (Subgroup.mem_iInf.1 h1 ⟨w0, hw0⟩)
  refine GlobalTheory.Adopt.mem_latticeStabilizer_of_local_integral_inBasis _ _ fun w => ?_
  by_cases hw : ∃ w0 ∈ locPl G t, w.under (𝓞 D.host.F) = w0.under (𝓞 D.host.F)
  · obtain ⟨w0, hw0, e⟩ := hw
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e with rfl | rfl
    · exact hP w hw0
    · exact GlobalTheory.T.unitaryInBasis_integral_at_conjugatePlace _ _ _ hfr (GlobalTheory.AdIsom.dualL_eq hsd) _ hU w0 (hP w0 hw0)
  · push_neg at hw
    exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 w) hw

theorem hat_stab_of_St {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (β M : GL (Fin n) (Lev.EAf D))
    (hβ : IsFrame β Λ) (hM : M ∈ St β) (z : Fin n → Lev.EAf D) :
    z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ M.val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  refine ⟨GlobalTheory.LatStab.mulVec_mem_of_mem_St Λ β M hβ hM z, fun h => ?_⟩
  have e : (M⁻¹).val *ᵥ (M.val *ᵥ z) = z := by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  rw [← e]
  exact GlobalTheory.LatStab.mulVec_mem_of_mem_St Λ β M⁻¹ hβ (inv_mem hM) _ h

theorem hat_stab_conj (V : HSp D) (u k : GA D V) (Λ M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hu : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) M ↔ (Lev.finE V u).val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (hk : ∀ z, z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ (Lev.finE V k).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (v : Fin V.rank → Lev.EAf D) :
    v ∈ Formalism.L2.Herm.hatL (F := D.host.F) M ↔
      (Lev.finE V (u⁻¹ * k * u)).val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) M := by
  have e : (Lev.finE V u).val *ᵥ ((Lev.finE V (u⁻¹ * k * u)).val *ᵥ v) =
      (Lev.finE V k).val *ᵥ ((Lev.finE V u).val *ᵥ v) := by
    rw [map_mul, map_mul, map_inv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  refine (hu v).trans ((hk _).trans ?_)
  rw [← e]
  exact (hu _).symm

theorem moves_of_hat (V : HSp D) (g : GA D V) (Λ : Lat V)
    (h : ∀ z, z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ (Lev.finE V g).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    Moves V g Λ Λ (fun _ => True) := by
  intro y hy
  have hy' : ∀ i, (Formalism.L2.Theta.mt V g *ᵥ y) i ∈ GlobalTheory.FinPl.idAt D (fun _ => True) :=
    GlobalTheory.Core.Mi.FrameMove.mulVec_mem_ideal _ hy
  constructor
  · intro h1
    refine GlobalTheory.HatLatV.mem_latV_of_hatL D V Λ _ _ hy' ?_
    rw [GlobalTheory.Core.Mi.FrameMove.finE_mulVec_hat]
    exact (h _).1 (GlobalTheory.LatVHat.latV_mem_hatL D V Λ _ y h1)
  · intro h1
    refine GlobalTheory.HatLatV.mem_latV_of_hatL D V Λ _ _ hy ?_
    have h2 := GlobalTheory.LatVHat.latV_mem_hatL D V Λ _ _ h1
    rw [GlobalTheory.Core.Mi.FrameMove.finE_mulVec_hat] at h2
    exact (h _).2 h2

theorem moves_neg (V : HSp D) (g : GA D V) (Λ : Lat V) {P : GlobalTheory.FinPl.Pl D → Prop} (h : Moves V g Λ Λ P) :
    Moves (negSp V) (negGA V g) Λ Λ P := h

theorem moves_cast (S : GridChoice W U) : ∀ (i : ℕ) (e : D.R.m = i) (g : FinPt G (.grid D.R.m D.R.m)),
    Moves (G.V (.grid D.R.m D.R.m)) g.1 (colLat (S.N.fr (.grid D.R.m D.R.m))) (colLat (S.N.fr (.grid D.R.m D.R.m)))
      (fun _ => True) →
    Moves (G.V (.grid i D.R.m)) (e ▸ g : FinPt G (.grid i D.R.m)).1 (colLat (S.N.fr (.grid i D.R.m)))
      (colLat (S.N.fr (.grid i D.R.m))) (fun _ => True) := by
  rintro i rfl g h
  exact h

end GlobalTheory.LastRowLat

namespace GlobalTheory.LastRowLat

open GlobalTheory.FinPl (Moves Lat)
open Matrix

theorem rowPt_mem_stdLat : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ k : FinPt G (.grid D.R.m D.R.m),
    finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl →
    ∀ x : WO (G.pS (.chi (lastIx D) D.R.m : Pair T)) (G.pT (.chi (lastIx D) D.R.m : Pair T)),
    actO _ _ (rowPt S k).1⁻¹ (rowPt S k).2⁻¹ x ∈ stdLat S (.chi (lastIx D) D.R.m) ↔ x ∈ stdLat S (.chi (lastIx D) D.R.m) := by
  intro D T L sc G W U S t _ k hk x
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hX : DefNode D.R.m (.grid D.R.m D.R.m) := ⟨le_rfl, rfl⟩
  have hk' := hat_stab_of_St _ _ _ (isFrame_grid S hm le_rfl) (levRow_mem_St S t k hk)
  have hg := hat_stab_conj (G.V (.grid D.R.m D.R.m)) (S.N.u (.grid D.R.m D.R.m)).1 k.1 _ _
    (S.N.u_lat _ hX) hk'
  have mv : Moves (G.V (.grid D.R.m D.R.m)) ((S.N.u (.grid D.R.m D.R.m))⁻¹ * k * S.N.u (.grid D.R.m D.R.m)).1
      (colLat (S.N.fr (.grid D.R.m D.R.m))) (colLat (S.N.fr (.grid D.R.m D.R.m))) (fun _ => True) :=
    moves_of_hat _ _ _ hg
  have mv2 := moves_cast S _ (lastIx_succ D) _ mv
  have mvS : Moves (G.pS (.chi (lastIx D) D.R.m : Pair T)) (rowPt S k).1⁻¹ (S.N.latS (.chi (lastIx D) D.R.m))
      (S.N.latS (.chi (lastIx D) D.R.m)) (fun _ => True) :=
    GlobalTheory.VacMove.moves_inv (moves_neg _ _ _ mv2)
  have mvT : Moves (G.pT (.chi (lastIx D) D.R.m : Pair T)) (rowPt S k).2⁻¹ (S.N.latT (.chi (lastIx D) D.R.m))
      (S.N.latT (.chi (lastIx D) D.R.m)) (fun _ => True) := by
    have e2 : (rowPt S k).2 = 1 := rfl
    rw [e2, inv_one]
    intro y _
    rw [GlobalTheory.VacMove.mt_one₀, Matrix.one_mulVec]
  have hl := (lastIx D).2
  have sdS : IsSelfDualC (G.pS (.chi (lastIx D) D.R.m : Pair T)) (S.N.latS (.chi (lastIx D) D.R.m)) :=
    isSelfDualC_neg (OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on _ ⟨by omega, rfl⟩))
  have sdT : IsSelfDualC (G.pT (.chi (lastIx D) D.R.m : Pair T)) (S.N.latT (.chi (lastIx D) D.R.m)) :=
    OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on _ ⟨by omega, rfl⟩)
  exact (GlobalTheory.VacMove.mem_latO_iff_actO sdS sdS sdT sdT mvS mvT x).symm

end GlobalTheory.LastRowLat
