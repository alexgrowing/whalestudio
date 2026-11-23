import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIInfEigenspaceEqTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWIffGoodFormsOrthSum
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BadPlacesGoodCoefficients
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualAdelicFrameLevelOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBilinCyclic
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypeDatumOfNormEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameIntegralGramMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodParameterFirstSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIntegralAdelicElementExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdempotentCoefficientConjugate

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.factPrime

namespace GlobalTheory.PartsOccurProof

section Flip

variable {k k' : Type} [CommRing k] [CommRing k'] {r : ℕ}

def tw (x : GL (Fin r) k) : GL (Fin r) k where
  val := (x⁻¹).val.transpose.submatrix Fin.revPerm Fin.revPerm
  inv := x.val.transpose.submatrix Fin.revPerm Fin.revPerm
  val_inv := by
    rw [Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.submatrix_one_equiv]
  inv_val := by
    rw [Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.submatrix_one_equiv]

theorem tw_apply (x : GL (Fin r) k) (i j : Fin r) : (tw x).val i j = (x⁻¹).val j.rev i.rev := rfl

theorem tw_tw (x : GL (Fin r) k) : tw (tw x) = x := by
  ext i j
  show x.val i.rev.rev j.rev.rev = _
  rw [Fin.rev_rev, Fin.rev_rev]

end Flip

variable {D : D7}

section Transport

variable {V : HSp D} {β β' : GL (Fin V.rank) (EAf D)} {L L' : LevDat D.host.E ℂ V.rank}
  {ι : G0 L.Pg L.r → G0 L'.Pg L'.r}
  (hpar : parLev D.sp.cm V.gram β' L' = parLev D.sp.cm V.gram β L)
  (htup : ∀ x ∈ parLev D.sp.cm V.gram β L, rTup β' L' x = ι (rTup β L x))

include hpar htup

end Transport

section Groups

variable {Pg Pg' : Finset (Pl D.host.E)} (pl : LevelCuspCharacters.Sq D.host ≃ ↥Pg)
  (red : ∀ v : LevelCuspCharacters.Sq D.host, kP (pl v).1 ≃+* ZMod (D.host.g v.1)) (b : ↥Pg' ≃ LevelCuspCharacters.Sq D.host)
  (φ : ∀ PP : ↥Pg', ZMod (D.host.g (b PP).1) ≃+* kP PP.1) (S : Set (LevelCuspCharacters.Sq D.host))

open Classical in

def fl (z : LevelCuspCharacters.LevelGroup D.host) : LevelCuspCharacters.LevelGroup D.host := fun v => if v ∈ S then tw (z v) else z v

def iota {n : ℕ} (hn : n = D.R.r) (x : G0 Pg n) : G0 Pg' D.R.r :=
  BadPlacesGoodCoefficients.toG0 b φ (fl S (GoodReductionModelReading.readG0 pl red hn x))

theorem reduction_reading_apply (x : G0 Pg D.R.r) (v : LevelCuspCharacters.Sq D.host) :
    GoodReductionModelReading.readG0 pl red rfl x v = Matrix.GeneralLinearGroup.map (red v).toRingHom (x (pl v)) := by
  ext a b
  rfl

theorem mem_lastZeroOrthImageSubspace_iff {Q : Finset (Pl D.host.E)} {n : ℕ} (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (u : G0 Q n) :
    u ∈ (P0 Q n ψ).H ↔ ∀ PP, u PP ∈ unip (kP PP.1) n :=
  ⟨fun h PP => h PP (Set.mem_univ _), fun h PP _ => h PP⟩

end Groups

section Frames

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem restrictedBlock_self_apply {κ : Type} [CommRing κ] (hr : n ≤ n) (g : GL (Fin n) κ) : upperLeftBlock hr g = g := by
  apply Units.ext
  rw [upper_block_val_submatrix hr (fun i j hij => by simp [blk2] at hij)]
  rfl

end Frames

section Main

variable {Pg Pg' : Finset (Pl D.host.E)} (pl : LevelCuspCharacters.Sq D.host ≃ ↥Pg)
  (red : ∀ v : LevelCuspCharacters.Sq D.host, kP (pl v).1 ≃+* ZMod (D.host.g v.1)) (b : ↥Pg' ≃ LevelCuspCharacters.Sq D.host)
  (φ : ∀ PP : ↥Pg', ZMod (D.host.g (b PP).1) ≃+* kP PP.1) (S : Set (LevelCuspCharacters.Sq D.host))

theorem redFn_same {n : ℕ} (β x : GL (Fin n) (EAf D)) {w w' : Pl D.host.E} (h : w = w') {p : ℕ} (e : kP w ≃+* ZMod p)
    (e' : ZMod p ≃+* kP w') (i j : Fin n) : (redFn β w' x).val i j = e' (e ((redFn β w x).val i j)) := by
  subst h
  obtain rfl : e' = e.symm := RingEquiv.toRingHom_injective (Subsingleton.elim _ _)
  exact (e.symm_apply_apply _).symm

theorem exists_move {n : ℕ} (hn : n = D.R.r) (hr : D.R.r ≤ n) (J : Matrix (Fin n) (Fin n) D.host.E) (β : GL (Fin n) (EAf D))
    (G : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hG : (intGL D.host.F D.host.E n G).val = Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) β.val *
      J.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * β.val)
    (hb : BadPlacesGoodCoefficients.IsBelow b) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (hSF : ∀ v, v.2.1 ∈ SF ↔ v ∈ S)
    (hS : ∀ PP : ↥Pg', (b PP ∉ S → (pl (b PP)).1 = PP.1) ∧ (b PP ∈ S → IsConjPl (pl (b PP)).1 PP.1)) :
    ∃ y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E), ∀ x ∈ UA D.sp.cm J, x ∈ St β →
      (fun PP : ↥Pg' => upperLeftBlock hr (redFn (β * intGL D.host.F D.host.E n y) PP.1 x)) =
        iota pl red b φ S hn (fun PP : ↥Pg => upperLeftBlock le_rfl (redFn β PP.1 x)) := by
  subst hn
  obtain ⟨y, hy⟩ := GlobalTheory.T.unitary_integral_adelic_element_exists D _ J β G hG SF
  refine ⟨y, fun x hx hx' => funext fun PP => ?_⟩
  have h := hy x hx hx' PP.1 (b PP).2.1 (hb PP).symm
  simp only [restrictedBlock_self_apply]
  ext i j
  show _ = φ PP ((fl S (GoodReductionModelReading.readG0 pl red rfl fun PP : ↥Pg => redFn β PP.1 x) (b PP)).val i j)
  unfold fl
  rw [reduction_reading_apply]
  split_ifs with hv
  · rw [h.2 ((hSF _).2 hv) _ ((hS PP).2 hv) _ (red (b PP)) (φ PP), tw_apply, ← map_inv]
    rfl
  · rw [h.1 (fun h' => hv ((hSF _).1 h'))]
    exact redFn_same β x ((hS PP).1 hv) (red (b PP)) (φ PP) i j

end Main

theorem below_of_match {Pg : Finset (Pl D.host.E)} {pl : LevelCuspCharacters.Sq D.host ≃ ↥Pg} (h : GoodReductionModelReading.IsPlaceMatch pl)
    (v : LevelCuspCharacters.Sq D.host) : (pl v).1.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.2.1.asIdeal := by
  ext x
  exact (h v x _ rfl).symm

theorem exists_frame (V : HSp D) : ∃ β, BadPlacesGoodCoefficients.IsFrameAtG V β := by
  have hs := (GlobalTheory.PlaceModel.isSelfDualC_latFrame V).2
  have hd : Formalism.L2.Herm.dualL D.sp.cm V (GlobalTheory.PlaceModel.latFrame V) = GlobalTheory.PlaceModel.latFrame V := by
    have : dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram (GlobalTheory.PlaceModel.latFrame V) =
        (GlobalTheory.PlaceModel.latFrame V : Set _) := Set.ext fun y => (hs y).symm
    unfold Formalism.L2.Herm.dualL
    rw [this, Submodule.span_eq]
  obtain ⟨β, c, h⟩ := GlobalTheory.AdelicFrame.exists_isSDFrame D V _ (GlobalTheory.PlaceModel.coe_latFrame V) hd
  exact ⟨β, _, 0, by rwa [one_pow] at h⟩

end GlobalTheory.PartsOccurProof
