import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondModelFinitePartFrameActionMatrix
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAtPlacesMemCompletedHermitianLa
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeCompletionAtPlacesOfFinPartMemHatLatti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CrdLatEqLatFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch.TraceX

theorem mulVec_mem_ideal {R : Type} [CommRing R] {I : Ideal R} {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) {y : Fin n → R}
    (hy : ∀ i, y i ∈ I) (k : Fin m) : (A *ᵥ y) k ∈ I := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun i _ => I.mul_mem_left _ (hy i)

theorem latV_iff_hatL {D : D7} (S : HSp D) (L : Lat S) (P : GlobalTheory.FinPl.Pl D → Prop) (y : Fin S.rank → AE D)
    (hy : ∀ i, y i ∈ idAt D P) :
    y ∈ latV S L P ↔ (fun i => toEAf D (y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L :=
  ⟨GlobalTheory.LatVHat.latV_mem_hatL D S L P y, GlobalTheory.HatLatV.mem_latV_of_hatL D S L P y hy⟩

theorem hat_reindex {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m n : ℕ} (hn : m = n)
    (L : Submodule (𝓞 E) (Fin n → E)) (z : Fin m → E ⊗[F] Formalism.L2.Herm.Af F) :
    z ∈ Formalism.L2.Herm.hatL (F := F) (L.map ((LinearEquiv.funCongrLeft E E (finCongr hn)).toLinearMap.restrictScalars (𝓞 E))) ↔
      (fun j => z (Fin.cast hn.symm j)) ∈ Formalism.L2.Herm.hatL (F := F) L := by
  subst hn
  have e : L.map ((LinearEquiv.funCongrLeft E E (finCongr (rfl : m = m))).toLinearMap.restrictScalars (𝓞 E)) = L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [e]
  rfl

theorem transport (D : D7) (I : AutInst) (ιE : I.E ≃+* D.host.E) (hId : ∀ y, HEq (ιE y) y)
    (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (hr : (D.sp.Y 0).rank = I.n)
    (ιA : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (hrat : ∀ x : I.E, ιA (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) =
      Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (ιE x))
    (hint : ∀ a, a ∈ IntAf I.F I.E ↔ ιA a ∈ IntAf D.host.F D.host.E)
    {n : ℕ} (q : Fin n → Fin I.n → I.E) (c : Fin n → GlobalTheory.AdForm.EF D) :
    (∑ i, ιA.symm (c i) • incl I (q i)) ∈ I.Lf ↔
      (∑ i, c i • fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) (ιE (q i (Fin.cast hr k)))) ∈
        Formalism.L2.Herm.hatL (F := D.host.F) (latS D) := by
  subst hI
  have hid : ∀ y, ιE y = y := fun y => eq_of_heq (hId y)
  have hA : ∀ a, ιA a = a := GlobalTheory.Core.Mi.FinFrame.eq_self_of_rat_of_int (Formalism.L2.SG.InstExistsPf.instOf D).F
    (Formalism.L2.SG.InstExistsPf.instOf D).E ιA.toRingHom
    (fun x => (hrat x).trans (congrArg _ (hid x))) (fun a ha => (hint a).1 ha)
  have hA' : ∀ a, ιA.symm a = a := fun a => (hA _).symm.trans (ιA.apply_symm_apply a)
  simp only [hid, hA']
  have e : latS D = GlobalTheory.PlaceModel.latFrame (Yc D 0) := GlobalTheory.ConjPlaceRed.crdLat_eq_latFrame (D.sp.Y 0)
  rw [e]
  exact (GlobalTheory.ConjPlaceRed.mem_Lf D _).symm

theorem fin_emb {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (w : Fin A.rank → AE D) :
    (fun k => toEAf D ((d.j0 *ᵥ (o.jA *ᵥ w)) k)) =
      ∑ i, toEAf D (w i) • fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) ((d.i₀ * o.iA) k i) := by
  have h2 : HMul.hMul d.j0 o.jA = (d.i₀ * o.iA).map (incA D) := (Matrix.map_mul (f := incA D)).symm
  rw [Matrix.mulVec_mulVec, h2]
  funext k
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    GlobalTheory.Core.Mi.FinFrame.toEAf_incA]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem fin_mt {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (y : Fin V.rank → AE D) :
    GlobalTheory.AdForm.finM V hn g *ᵥ (fun j => toEAf D (y (Fin.cast hn.symm j))) =
      fun j => toEAf D ((Formalism.L2.Theta.mt V g *ᵥ y) (Fin.cast hn.symm j)) := by
  subst hn
  funext i
  exact (RingHom.map_mulVec (toEAf D) (Formalism.L2.Theta.mt V g) y i).symm

set_option maxHeartbeats 1600000 in

theorem trace_iff : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (B : SBes X h u ψ (D.sp.X 0)) (a₀ : GA D (D.sp.X 0)), GlobalTheory.Core.Mi.IdE X → Formalism.L2.SG.ColDict.LevelMatch X tr hK → B.Adapted tr.wt → IsTransportAdelicCorrection tr a₀ → ∀ (v : GlobalTheory.FinPl.Pl D) (y : Fin (D.sp.X 0).rank → AE D), (∀ i, y i ∈ idAt D (· = v)) → (y ∈ latV (D.sp.X 0) (lat0 F) (· = v) ↔ B.d.j0 *ᵥ (B.o.jA *ᵥ (Formalism.L2.Theta.mt (D.sp.X 0) a₀ *ᵥ y)) ∈ latV (D.sp.Y 0) (latS D) (· = v)) := by
  intro D X h u ψ F tr hK B a₀ hId hL hAd h0 v y hy
  have hn := Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)
  have hy' : ∀ k, (B.d.j0 *ᵥ (B.o.jA *ᵥ (Formalism.L2.Theta.mt (D.sp.X 0) a₀ *ᵥ y))) k ∈ idAt D (· = v) :=
    mulVec_mem_ideal _ (mulVec_mem_ideal _ (mulVec_mem_ideal _ hy))
  refine (latV_iff_hatL _ _ _ _ hy).trans
    (Iff.trans ?_ (latV_iff_hatL _ _ _ _ hy').symm)
  change (fun i => toEAf D (y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (lat0 F) ↔
    (fun k => toEAf D ((B.d.j0 *ᵥ (B.o.jA *ᵥ (Formalism.L2.Theta.mt (D.sp.X 0) a₀ *ᵥ y))) k)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (latS D)
  refine (hat_reindex hn F.cls0.lev.Lb _).trans ?_
  have H := hL.1 (tr.h0.1.1 *ᵥ fun j => toEAf D (y (Fin.cast hn.symm j)))
  have e1 : (tr.h0⁻¹).1.1 *ᵥ (tr.h0.1.1 *ᵥ fun j => toEAf D (y (Fin.cast hn.symm j))) =
      fun j => toEAf D (y (Fin.cast hn.symm j)) := by
    rw [Matrix.mulVec_mulVec]
    have : HMul.hMul (tr.h0⁻¹).1.1 tr.h0.1.1 = 1 := Units.inv_mul tr.h0.1
    rw [this, Matrix.one_mulVec]
  rw [e1] at H
  refine H.trans ?_
  rw [← h0.2, fin_mt, fin_emb]
  refine (transport D X.B.I X.ιE hId h (rank_eq X h) tr.ιA tr.ιA_rat tr.ιA_int
    (fun i => X.crd (Formalism.L2.SG.ColDict.qFr tr.wt i)) _).trans ?_
  simp only [hAd _ _]
  refine iff_of_eq (congrArg (· ∈ Formalism.L2.Herm.hatL (F := D.host.F) (latS D)) ?_)
  exact (Fintype.sum_equiv (finCongr hn) _ _ fun i => rfl).symm

end GlobalTheory.Core.Mi.LatMatch.TraceX
