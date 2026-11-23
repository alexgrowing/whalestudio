import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.HWDefs
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharMulVecArtinianReduced
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrablePowerNormCompact

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwsHwfin

open GlobalTheory.StdUnn NumberField IsDedekindDomain

section Blocks

variable {R : Type} {n : ℕ}

def topV (z : Fin (n + n) → R) : Fin n → R := fun i => z (finSumFinEquiv (Sum.inl i))

def botV (z : Fin (n + n) → R) : Fin n → R := fun i => z (finSumFinEquiv (Sum.inr i))

def joinV (y y' : Fin n → R) : Fin (n + n) → R := fun j => Sum.elim y y' (finSumFinEquiv.symm j)

theorem topV_joinV (y y' : Fin n → R) : topV (joinV y y') = y := by
  funext i; simp [topV, joinV]

theorem botV_joinV (y y' : Fin n → R) : botV (joinV y y') = y' := by
  funext i
  show Sum.elim y y' (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i))) = y' i
  rw [Equiv.symm_apply_apply]
  rfl

theorem joinV_mem {p : R → Prop} {y y' : Fin n → R} (hy : ∀ i, p (y i)) (hy' : ∀ i, p (y' i)) :
    ∀ j, p (joinV y y' j) := by
  intro j
  show p (Sum.elim y y' (finSumFinEquiv.symm j))
  generalize finSumFinEquiv.symm j = s
  rcases s with i | i
  · exact hy i
  · exact hy' i

theorem blk4_mul'' [CommRing R] (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem mapMatrix_blk4 {S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    f.mapMatrix (blk4 a b c d) = blk4 (f.mapMatrix a) (f.mapMatrix b) (f.mapMatrix c) (f.mapMatrix d) := by
  simp only [RingHom.mapMatrix_apply]
  unfold blk4
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]

theorem botV_blk4_mulVec [CommRing R] (A B C D : Matrix (Fin n) (Fin n) R) (z : Fin (n + n) → R) :
    botV (blk4 A B C D *ᵥ z) = C *ᵥ topV z + D *ᵥ botV z := by
  funext i
  unfold botV topV blk4
  rw [Matrix.submatrix_mulVec_equiv, Function.comp_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_mulVec,
    Sum.elim_inr]
  rfl

theorem hg_of [CommRing R] (av dv bv b0v : Matrix (Fin n) (Fin n) R) (Mk : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (h : blk4 0 1 (-1) 0 * blk4 1 bv 0 1 = blk4 av 0 0 dv * blk4 1 b0v 0 1 * Mk) :
    blk4 0 1 (-1) (-bv) = blk4 av (av * b0v) 0 dv * Mk := by
  have h1 : (blk4 0 1 (-1) 0 * blk4 1 bv 0 1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = blk4 0 1 (-1) (-bv) := by
    rw [blk4_mul'']; simp
  have h2 : (blk4 av 0 0 dv * blk4 1 b0v 0 1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = blk4 av (av * b0v) 0 dv := by
    rw [blk4_mul'']; simp
  rw [← h1, h, h2]

theorem key_bot [CommRing R] (b d A Bm : Matrix (Fin n) (Fin n) R) (Mk : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (hg : blk4 0 1 (-1) (-b) = blk4 A Bm 0 d * Mk) (z : Fin (n + n) → R) :
    -topV z - b *ᵥ botV z = d *ᵥ botV (Mk *ᵥ z) := by
  have h : botV (blk4 0 1 (-1) (-b) *ᵥ z) = botV ((blk4 A Bm 0 d * Mk) *ᵥ z) := by rw [hg]
  rw [← Matrix.mulVec_mulVec, botV_blk4_mulVec, botV_blk4_mulVec, Matrix.zero_mulVec, zero_add, Matrix.neg_mulVec,
    Matrix.neg_mulVec, Matrix.one_mulVec] at h
  rw [sub_eq_add_neg, h]

theorem image_eq [CommRing R] (S : Subring R) (O : AddSubgroup (Fin n → R)) (hO : ∀ y, y ∈ O ↔ ∀ i, y i ∈ S)
    (b d A Bm : Matrix (Fin n) (Fin n) R) (Mk Mk' : Matrix (Fin (n + n)) (Fin (n + n)) R) (hkk : Mk * Mk' = 1)
    (hK : ∀ z : Fin (n + n) → R, (∀ j, z j ∈ S) ↔ ∀ j, (Mk *ᵥ z) j ∈ S)
    (hg : blk4 0 1 (-1) (-b) = blk4 A Bm 0 d * Mk) :
    {x | ∃ y ∈ O, ∃ y' ∈ O, x = y + b *ᵥ y'} = (fun y => d *ᵥ y) '' (O : Set (Fin n → R)) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe, hO]
  constructor
  · rintro ⟨y, hy, y', hy', rfl⟩
    have hz : ∀ j, joinV (-y) (-y') j ∈ S :=
      joinV_mem (p := (· ∈ S)) (fun i => S.neg_mem (hy i)) (fun i => S.neg_mem (hy' i))
    refine ⟨botV (Mk *ᵥ joinV (-y) (-y')), fun i => (hK _).1 hz _, ?_⟩
    rw [← key_bot b d A Bm Mk hg, topV_joinV, botV_joinV, Matrix.mulVec_neg, neg_neg, sub_neg_eq_add]
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨z, hzdef⟩ : ∃ z, z = Mk' *ᵥ joinV 0 u := ⟨_, rfl⟩
    have hMz : Mk *ᵥ z = joinV 0 u := by rw [hzdef, Matrix.mulVec_mulVec, hkk, Matrix.one_mulVec]
    have hz : ∀ j, z j ∈ S := (hK z).2 (by
      rw [hMz]; exact joinV_mem (p := (· ∈ S)) (fun _ => S.zero_mem) hu)
    refine ⟨-topV z, fun i => S.neg_mem (hz (finSumFinEquiv (Sum.inl i))), -botV z,
      fun i => S.neg_mem (hz (finSumFinEquiv (Sum.inr i))), ?_⟩
    have h := key_bot b d A Bm Mk hg z
    rw [hMz, botV_joinV] at h
    rw [← h, Matrix.mulVec_neg, sub_eq_add_neg]

end Blocks

section Haar

theorem nu2_eq_modu {B : Type} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [LocallyCompactSpace B]
    [T2Space B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B] (hA : IsArtinianRing B)
    (hR : IsReduced B) {n : ℕ} (lam : Measure (Fin n → B)) [lam.IsAddHaarMeasure] (O : Set (Fin n → B))
    (hOo : IsOpen O) (hOc : IsCompact O) (hO0 : (0 : Fin n → B) ∈ O) (d : Matrix (Fin n) (Fin n) B)
    (hd : IsUnit d.det) :
    (lam ((fun y => d *ᵥ y) '' O) / lam O).toReal = (GlobalTheory.GaugeEx.modu B d.det : ℝ) := by
  have hc := GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE B hA hR (Fin n) d hd
  have hpre := addEquivAddHaarChar_smul_preimage lam (X := (fun y => d *ᵥ y) '' O) (GlobalTheory.ModuLR.mulVecCE d hd)
  have e : ⇑(GlobalTheory.ModuLR.mulVecCE d hd) ⁻¹' ((fun y => d *ᵥ y) '' O) = O := by
    have hf : (fun y => d *ᵥ y) = ⇑(GlobalTheory.ModuLR.mulVecCE d hd) := rfl
    rw [hf]
    exact Set.preimage_image_eq O (GlobalTheory.ModuLR.mulVecCE d hd).injective
  rw [e, hc, ENNReal.smul_def, smul_eq_mul] at hpre
  have h0 : lam O ≠ 0 := (hOo.measure_pos lam ⟨0, hO0⟩).ne'
  have ht : lam O ≠ ⊤ := hOc.measure_lt_top.ne
  rw [← hpre, mul_div_assoc, ENNReal.div_self h0 ht, mul_one, ENNReal.coe_toReal]

end Haar

set_option maxHeartbeats 4000000 in

theorem hwFin : PositivityTheory.PfSWUS.SwFockk.HWFin := by
  intro D n w hw nb hnb b p k hp hk hwk a ha v lam hlam
  obtain ⟨m, u, b0, rfl, hm, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hp a ha
  haveI := hlam
  haveI : IsTopologicalRing (Fv D.host.F v ⊗[D.host.F] D.host.E) := GlobalTheory.LocTateInt.isTopologicalRing_Ev v
  haveI : T2Space (Fv D.host.F v ⊗[D.host.F] D.host.E) := GlobalTheory.LocTateInt.t2Space_Fv_tensor v
  haveI : LocallyCompactSpace (Fv D.host.F v ⊗[D.host.F] D.host.E) := GlobalTheory.LocTateInt.locallyCompactSpace_Ev v
  haveI : SecondCountableTopology (Fv D.host.F v ⊗[D.host.F] D.host.E) := GlobalTheory.LocTateInt.secondCountable_Ev v
  haveI : BorelSpace (Fv D.host.F v ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ D.host.F D.host.E
  have hAr : IsArtinianRing (Fv D.host.F v ⊗[D.host.F] D.host.E) := IsArtinianRing.of_finite (Fv D.host.F v) _
  have hRd : IsReduced (Fv D.host.F v ⊗[D.host.F] D.host.E) := by
    haveI : Algebra.FormallyUnramified D.host.F D.host.E := Algebra.FormallyUnramified.of_isSeparable _ _
    exact Algebra.FormallyUnramified.isReduced_of_field (Fv D.host.F v) _
  set cf := compFin D.host.F D.host.E v with hcf

  have e : cf.mapMatrix (mat w * mat (nb b)) = cf.mapMatrix (mat m * mat u * mat k) := by
    have := congrArg (fun g => cf.mapMatrix (mat g)) hwk
    exact this
  simp only [map_mul] at e
  rw [hw, hnb b, hm, hu] at e
  simp only [mapMatrix_blk4, map_zero, map_one, map_neg] at e
  have hg := hg_of _ _ _ _ _ e

  have hk' : k ∈ GlobalTheory.AdelicU.levelAll D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) 1 := hk
  have hkv := (GlobalTheory.AdelicU.mem_levelAll.1 hk').1 v
  have hK : ∀ z : Fin (n + n) → Fv D.host.F v ⊗[D.host.F] D.host.E,
      (∀ j, z j ∈ intLoc D.host.F D.host.E v) ↔ ∀ j, (cf.mapMatrix (mat k) *ᵥ z) j ∈ intLoc D.host.F D.host.E v := by
    intro z
    have h := GlobalTheory.AdelicU.mem_stabLoc.1 hkv z
    rw [mem_latLoc_stdLattice, mem_latLoc_stdLattice] at h
    exact h
  have hkk : cf.mapMatrix (mat k) * cf.mapMatrix (mat k⁻¹) = 1 := by
    rw [← map_mul, ← GlobalTheory.StdUnn.LeftInvSect.mat_mul, mul_inv_cancel, GlobalTheory.StdUnn.LeftInvSect.mat_one, map_one]
  have hset := image_eq (intLoc D.host.F D.host.E v) (PositivityTheory.PfSWUS.SwFockk.lstd D.host.F D.host.E n v)
    (fun y => Iff.rfl) (cf.mapMatrix b.1) _ _ _ _ _ hkk hK hg

  have hcA : ∀ z : AF D.host.F ⊗[D.host.F] D.host.E, cf (cA D z) = sigR (Fv D.host.F v) D.sp.cm.sig (cf z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => rfl
  have hdetinv : ((a⁻¹ : GL (Fin n) (AE D)).1).det = (((Matrix.GeneralLinearGroup.det a)⁻¹ : (AE D)ˣ) : AE D) :=
    congrArg Units.val (map_inv Matrix.GeneralLinearGroup.det a)
  have hadj : (adj (a⁻¹).1 : Mx D n n).det = cA D ((a⁻¹ : GL (Fin n) (AE D)).1).det := by
    show ((((a⁻¹ : GL (Fin n) (AE D)).1).map (cA D))ᵀ).det = _
    rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hdet : (cf.mapMatrix (adj (a⁻¹).1)).det = ((conjUnit D.sp.cm.sig
      (unitFin D.host.F D.host.E v (Matrix.GeneralLinearGroup.det a))⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) :
        Fv D.host.F v ⊗[D.host.F] D.host.E) := by
    rw [← RingHom.map_det, hadj, hcA, hdetinv]
    rfl
  have hx : IsUnit (cf.mapMatrix (adj (a⁻¹).1)).det := by rw [hdet]; exact Units.isUnit _
  have hmodu : (GlobalTheory.GaugeEx.modu (Fv D.host.F v ⊗[D.host.F] D.host.E) (cf.mapMatrix (adj (a⁻¹).1)).det : ℝ) =
      ((absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v (Matrix.GeneralLinearGroup.det a)) : ℝ≥0) : ℝ)⁻¹ := by
    rw [GlobalTheory.GaugeEx.modu, dif_pos hx, GlobalTheory.LocTateInt.distribHaarChar_Ev, IsUnit.unit_spec, hdet, ← absEv_apply,
      absEv_conjUnit, map_inv, NNReal.coe_inv]

  have hOset : ((PositivityTheory.PfSWUS.SwFockk.lstd D.host.F D.host.E n v : AddSubgroup _) :
      Set (Fin n → Fv D.host.F v ⊗[D.host.F] D.host.E)) =
      Set.pi Set.univ fun _ => (intLoc D.host.F D.host.E v : Set (Fv D.host.F v ⊗[D.host.F] D.host.E)) := by
    ext y
    simp only [Set.mem_pi, Set.mem_univ, true_implies, SetLike.mem_coe]
    exact Iff.rfl
  obtain ⟨hc, ho⟩ := GlobalTheory.ThK.isCompact_isOpen_intLoc (F := D.host.F) (E := D.host.E) v
  have hOo : IsOpen ((PositivityTheory.PfSWUS.SwFockk.lstd D.host.F D.host.E n v : AddSubgroup _) :
      Set (Fin n → Fv D.host.F v ⊗[D.host.F] D.host.E)) := by
    rw [hOset]; exact isOpen_set_pi Set.finite_univ fun _ _ => ho
  have hOc : IsCompact ((PositivityTheory.PfSWUS.SwFockk.lstd D.host.F D.host.E n v : AddSubgroup _) :
      Set (Fin n → Fv D.host.F v ⊗[D.host.F] D.host.E)) := by
    rw [hOset]; exact isCompact_univ_pi fun _ => hc
  unfold PositivityTheory.SiegelWeilFormula.Gen.nu2
  have hbv : PositivityTheory.SiegelWeilFormula.Gen.matV v b.1 = cf.mapMatrix b.1 := rfl
  rw [hbv, hset, nu2_eq_modu hAr hRd lam _ hOo hOc (PositivityTheory.PfSWUS.SwFockk.lstd D.host.F D.host.E n v).zero_mem _ hx,
    hmodu]

end PositivityTheory.PfSWUS.SwsHwfin

end
