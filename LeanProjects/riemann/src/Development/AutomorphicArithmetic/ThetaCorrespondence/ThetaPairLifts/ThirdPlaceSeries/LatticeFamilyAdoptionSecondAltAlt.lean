import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionSecond
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT

set_option synthInstance.maxHeartbeats 200000

section
namespace GroupAverageFixedPoints
section
noncomputable section
open scoped TensorProduct
open Module
namespace GlobalTheory.CompanionTheory.LatSpan
section Rep
variable {F M Γ : Type} [Field F] [AddCommGroup M] [Module F M] [Group Γ] [Fintype Γ]
variable (a : Γ →* Module.End F M) (P : Subgroup Γ) [Fintype P] (t : P →* Fˣ) (E : Module.End F M)
end Rep
section Ext
variable {O K K'' Fm : Type} [CommRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
  [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm]
end Ext
end GlobalTheory.CompanionTheory.LatSpan
noncomputable section
open scoped TensorProduct
open Module NumberField
namespace GlobalTheory.CompanionTheory.LatSpan
section Main
variable {LL O K K'' Fm WL Γ : Type} [Field LL] [CharZero LL] [AddCommGroup WL] [Module LL WL]
  [CommRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
  [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm] [Group Γ] [Fintype Γ]
end Main
section Lat
variable {LL Oe K'' V T : Type} [Field LL] [NumberField LL] [AddCommGroup V] [Module LL V] [Module (𝓞 LL) V]
  [IsScalarTower (𝓞 LL) LL V] [CommRing Oe] [IsDomain Oe] [Field K''] [Algebra Oe K''] [IsFractionRing Oe K'']
  [AddCommGroup T] [Module K'' T] [Module Oe T] [IsScalarTower Oe K'' T]
end Lat
end GlobalTheory.CompanionTheory.LatSpan
end
end
end
section
noncomputable section
open scoped TensorProduct
open Module NumberField
namespace GlobalTheory.CompanionTheory.LatSpan
open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases
section Form
variable {Ks LL WL : Type} [Field Ks] [Field LL] [Algebra Ks LL]
  [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  {WK : Submodule Ks WL}
  {O K K'' : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] [Algebra Ks K]
  [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
  {Fm : Type} [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm]
end Form
section Iso
open Formalism.IndefR.NX Formalism.IndefR.Arith
variable {LL Ks Ks' WL WL' G G' : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  [Field Ks'] [NumberField Ks'] [Algebra Ks' LL]
  [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL]
  [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
  [AddCommGroup WL'] [Module LL WL'] [Module Ks' WL'] [IsScalarTower Ks' LL WL'] [Module (𝓞 LL) WL']
  [IsScalarTower (𝓞 LL) LL WL'] [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
  {W W' : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)] [Group G] [Group G']
end Iso
end GlobalTheory.CompanionTheory.LatSpan
end
end
section
noncomputable section
open scoped TensorProduct
open Module NumberField
namespace GlobalTheory.CompanionTheory.LatSpan
open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion Formalism.BasicNotions Formalism.IndefR.NX
section PiLocalization₂
variable {D : D7} (c : NChoice D) (w : D.what₂.places.Pl)
attribute [local instance] algKK
variable {c w}
end PiLocalization₂
end GlobalTheory.CompanionTheory.LatSpan
noncomputable section
open scoped TensorProduct
open Module NumberField
namespace GlobalTheory.CompanionTheory.LatSpan
section Alg
variable {k A G : Type} [Field k] [Ring A] [Algebra k A] [Group G]
end Alg
end GlobalTheory.CompanionTheory.LatSpan
noncomputable section
open scoped TensorProduct
open Module NumberField
namespace GlobalTheory.CompanionTheory.LatSpan
open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion Formalism.BasicNotions Formalism.IndefR.NX Formalism.IndefR.Arith
section Stage2
variable {D : D7} {c : NChoice D} {w : D.what₂.places.Pl}
attribute [local instance] algKK
end Stage2
end GlobalTheory.CompanionTheory.LatSpan
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CompanionTheory.LatSpan
attribute [local instance] algKK
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem lattice_of_lifts_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (_ : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (_ : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q) (jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] B.Q.Sx.WL j) (eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), NChTie D ex.nch → (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V) (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL), HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x) = jDL B.Q.Rl B.Q.F.lv2 i y) → (∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx j), jD j x = ∑ k, a k • (show ↥(B.Q.Sx.A j).WK from f k).1 → eM w j x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)] (B.Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k)) → ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → NForms.IsLatIn (Submodule.span (ex.nch.Oe w) (eM w j '' ((Y.MjH j).L : Set (Y.MjH j).V))) ((((NForms.V0 D (ex.nch.twI w) j (ex.nch.sd w)).restrictScalars (D.ntw.O (ex.nch.twI w))).baseChange (FractionRing (ex.nch.Oe w))).restrictScalars (ex.nch.Oe w)) := by
  intro D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B hPin hRec jD eM hN hjD hSum w j hne h1 h2
  obtain ⟨i, rfl⟩ : ∃ i : Fin D.R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  have hgrp := P.tied.div.grp
  have hIe : P.I.eG = B.Q.Rl.eG.trans B.Q.cG := hPin.eGtie
  have hC : ∀ h, (Formalism.L2.DIV.idemOf P.A3.A.X).coeff h = ((D.nexp.eLL0 (P.I.eG h) : D.LL0) : D.what₂.LL) := fun h =>
    D.what₂.embLL.injective ((hgrp.e0 h).trans (D.nStage_trivialCharacter_coeff_eq _).symm)
  obtain ⟨e, he1, he2⟩ := stage2 (w := w) hN P.I.eG B.Q.Sx ((i : ℕ) + 1) (B.Q.Rl.FW i) (B.Q.nexp.fi i) (B.fw.ks i)
    (fun s => by rw [hIe]; exact B.Q.nexp.geq i s) (B.Q.nexp.rho _ h1 h2) (B.Q.nexp.chi _ h1 h2)
    (B.Q.nexp.eF _ _ _ h1 h2) (B.Q.nexp.act _ _ _ h1 h2) (fun g => (Formalism.L2.DIV.idemOf P.A3.A.X).coeff g) hC P.P0 P.ψ0⁻¹
    hgrp.lvl0 (fun u hu => by
      obtain ⟨x, hx1, hx2⟩ := hgrp.psi0 u hu (ex.nch.twI w) (ex.nch.sd w)
      exact ⟨x, hx1, hx2⟩)
  have hd := _root_.Formalism.IndefR.finrank_WL_eq_dW B.Q i
  have hForm := isKsForm_of_iso (B.Q.nexp.fi i) (B.fw.ks i)
  have heM : ∀ x, eM w ((i : ℕ) + 1) x = e (jD ((i : ℕ) + 1) x) := by
    intro x
    obtain ⟨n, b, hbK, -, -, -, hsp⟩ := hForm
    have hx : jD ((i : ℕ) + 1) x ∈ Submodule.span D.what₂.LL (Set.range b) := hsp ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun D.what₂.LL).1 hx
    let f : Fin n → FmK B.Q.Sx ((i : ℕ) + 1) := fun k => ⟨b k, hbK k⟩
    have h5 := hSum w ((i : ℕ) + 1) h1 h2 x n a f ha.symm
    rw [h5, ← ha]
    exact (he1 n a f).symm
  have hWg : (B.Q.Rl.FW i).Wgood P.P0 P.ψ0⁻¹ (fun g => (Formalism.L2.DIV.idemOf P.A3.A.X).coeff g) =
      B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i := rfl
  have hrange : Set.range (eM w ((i : ℕ) + 1)) =
      (fun y => e ((B.Q.nexp.fi i).e.symm y)) ''
        ((B.Q.Rl.FW i).Wgood P.P0 P.ψ0⁻¹ (fun g => (Formalism.L2.DIV.idemOf P.A3.A.X).coeff g) : Set _) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x), ?_, ?_⟩
      · rw [hjD i x _ (heq_cast hd ((P.JM.eW i).symm x))]
        rw [SetLike.mem_coe, hWg]
        simp only [Formalism.IndefR.NX.jDL, Fintype.linearCombination_apply]
        exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Module.finBasis D.what₂.LL _ k).2
      · simp only [LinearEquiv.symm_apply_apply, heM]
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, hWg] at hy
      let Bs := Module.finBasis D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)
      let z : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL := Bs.equivFun ⟨y, hy⟩
      let x := P.JM.eW i (z ∘ Fin.cast hd.symm)
      have hH : HEq ((P.JM.eW i).symm x) z := by
        simp only [x, LinearEquiv.symm_apply_apply]
        exact (heq_cast hd.symm z).symm
      have h6 := hjD i x z hH
      have h7 : Formalism.IndefR.NX.jDL B.Q.Rl B.Q.F.lv2 i z = y := by
        simp only [Formalism.IndefR.NX.jDL, Fintype.linearCombination_apply]
        have h8 := Bs.sum_equivFun ⟨y, hy⟩
        have h9 : ((∑ k, Bs.equivFun ⟨y, hy⟩ k • Bs k : B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i) : Fin (B.Q.Rl.nW i) → D.what₂.LL) = y :=
          congrArg Subtype.val h8
        rw [AddSubmonoidClass.coe_finset_sum] at h9
        exact h9
      refine ⟨x, ?_⟩
      rw [heM]
      change e _ = e ((B.Q.nexp.fi i).e.symm y)
      rw [← h7, ← h6, LinearEquiv.symm_apply_apply]
  refine isLatIn_span (ex.nch.embW w) (integers_embed _) (eM w ((i : ℕ) + 1)) (Y.MjH ((i : ℕ) + 1)).L
    (Y.MjH_good _).2.1 (Y.MjH_good _).2.2 _ ?_
  rw [hrange]
  exact he2
end GlobalTheory.CompanionTheory.LatSpan
end
end
end
end
end GroupAverageFixedPoints
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.Adopt.lattice_family_adoption_second_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (_ : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (_ : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q) (jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] B.Q.Sx.WL j) (eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), NChTie D ex.nch → (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V) (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL), HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x) = jDL B.Q.Rl B.Q.F.lv2 i y) → (∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx j), jD j x = ∑ k, a k • (show ↥(B.Q.Sx.A j).WK from f k).1 → eM w j x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)] (B.Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k)) → ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → NForms.IsLatIn (Submodule.span (ex.nch.Oe w) (eM w j '' ((Y.MjH j).L : Set (Y.MjH j).V))) ((((NForms.V0 D (ex.nch.twI w) j (ex.nch.sd w)).restrictScalars (D.ntw.O (ex.nch.twI w))).baseChange (FractionRing (ex.nch.Oe w))).restrictScalars (ex.nch.Oe w)) := by
  first | exact @_root_.GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.lattice_of_lifts_alt | exact _root_.GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.lattice_of_lifts_alt | (intros; apply _root_.GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.lattice_of_lifts_alt <;> assumption)
end
end
