import Mathlib
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.AinfMapSurjective
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.PhiGalCris
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InstCommRingBcris

noncomputable section

namespace PositivityTheory.LocInh

open GroundTheory.PAdicHodge Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem actC_eq (AI : LocAinf l P) (g : GQ l) (y : ℂ_[l]) : AI.actC g y = actC l g y :=
  congrFun (eq_galCp_of_continuous (Per6.toBot g) (AI.actC g)
    (AddMonoidHomClass.isometry_of_norm (AI.actC g) (AI.actC_norm g)).continuous
    (AI.actC_ext g)) y

theorem actT_eq (AI : LocAinf l P) (g : GQ l) (x : OCb l) : AI.actT g x = galT g x :=
  (galT_ext fun n y hy => by
    obtain ⟨y', h1, h2⟩ := AI.actT_coeff g x n y hy
    exact ⟨y', h1.trans (actC_eq AI g y), h2⟩).symm

theorem tiltMap_ε (AI : LocAinf l P) : Per6.tiltMap l AI.ε =
    IsPerfectoidField.ofCompatible l (fun n => Per6.intEquiv l (AI.ζ n))
      (fun n => by rw [← map_pow, AI.ζ_succ]) :=
  Perfection.ext fun n => frob_coeff_tiltMap AI.ε n (AI.ζ n) (AI.ε_coeff n)

theorem untilt_ε (AI : LocAinf l P) : PreTilt.untilt (Per6.tiltMap l AI.ε) = 1 := by
  rw [tiltMap_ε, IsPerfectoidField.untilt_ofCompatible, AI.ζ_zero, map_one]

theorem untilt_ε_root (AI : LocAinf l P) :
    PreTilt.untilt ((frobeniusEquiv (PreTilt ↥(normInteger ℂ_[l]) l) l).symm
      (Per6.tiltMap l AI.ε)) = Per6.intEquiv l (AI.ζ 1) := by
  rw [tiltMap_ε, AInf.frobeniusEquiv_symm_ofCompatible, IsPerfectoidField.untilt_ofCompatible]

theorem untilt_ε_root_ne_one (AI : LocAinf l P) :
    PreTilt.untilt ((frobeniusEquiv (PreTilt ↥(normInteger ℂ_[l]) l) l).symm
      (Per6.tiltMap l AI.ε)) ≠ 1 := by
  rw [untilt_ε_root]
  exact fun h => AI.ζ_one ((Per6.intEquiv l).injective (h.trans (map_one _).symm))

theorem ιB_algebraMap_K0 (P : LocPrime l) (K : FinExt l) (c : ↥(K0 K)) :
    P.ιB (algebraMap ↥(K0 K) P.R.B c) = algebraMap (Om l) P.R.BdR (c : Om l) :=
  (P.PD_ι K _).symm.trans ((P.PD K).ι.commutes c)

theorem ιB_algebraMap (P : LocPrime l) (c : ↥(MaximalUnramifiedExtension l)) :
    P.ιB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap (Om l) P.R.BdR (c : Om l) :=
  ιB_algebraMap_K0 P ⟨IntermediateField.adjoin ℚ_[l] {(c : Om l)},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)⟩
    ⟨c, IntermediateField.subset_adjoin _ _ (Set.mem_singleton _), c.2⟩

variable (T : LocTied6 l P AI)

theorem tie_ι (b : P.R.B) : T.eD (P.ιB b) = ιCD l (T.eB b) := by
  have h := RingHom.congr_fun ((isCrisDR_iff _).1 T.incl) (T.eB b)
  rw [← h]
  simp

theorem tie_a (a : Ainf l) :
    T.eD (P.ιB (AI.ιA a)) = algebraMap (Per6.BdRp l) (Per6.BdR l) (Per6.aD l a) := by
  rw [tie_ι, T.ιA, ιCD_aB]

theorem tie_qD (q : ℚ_[l]) :
    T.eD (algebraMap ℚ_[l] P.R.BdR q) = oD l (algebraMap ℚ_[l] (Om l) q) :=
  RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (S := ℚ_[l])
    (j := T.eD.toRingHom.comp (algebraMap ℚ_[l] P.R.BdR))
    (k := (oD l).comp (algebraMap ℚ_[l] (Om l)))
    (RingHom.ext fun z => (T.zD z).trans (oD_coe z).symm)) q

theorem tie_o (x : Om l) : T.eD (algebraMap (Om l) P.R.BdR x) = oD l x := by
  choose y hy hθ using T.om
  have hj := IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
  let f : Om l →ₐ[ℚ_[l]] Per6.BdRp l :=
    { toFun := y
      map_one' := hj (by rw [← hy, map_one, map_one, map_one])
      map_mul' := fun a b => hj (by rw [← hy, map_mul, map_mul, map_mul, hy, hy])
      map_zero' := hj (by rw [← hy, map_zero, map_zero, map_zero])
      map_add' := fun a b => hj (by rw [← hy, map_add, map_add, map_add, hy, hy])
      commutes' := fun q => hj (by
        rw [← hy, ← IsScalarTower.algebraMap_apply, tie_qD, frob_oD_apply, AlgHom.commutes]) }
  have hf : f = algClToBdR l := eq_algClToBdR l f hθ
  rw [hy, frob_oD_apply, ← hf]
  rfl

theorem tie_u (c : ↥(MaximalUnramifiedExtension l)) : T.eB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = uB l c :=
  ιCD_injective (by rw [← tie_ι, ιB_algebraMap, tie_o, ιCD_uB])

theorem tie_q (q : ℚ_[l]) : T.eB (algebraMap ℚ_[l] P.R.B q) = qB l q := by
  rw [IsScalarTower.algebraMap_apply ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B, tie_u, uB_algebraMap]

theorem tie_t : T.eD (P.ιB P.tB) =
    algebraMap (Per6.BdRp l) (Per6.BdR l) (fontaineT (Per6.tiltMap l AI.ε) (untilt_ε AI)) := by
  obtain ⟨y, hy, h⟩ := T.t
  obtain ⟨_, rfl⟩ := (isLog_iff _ _).1 hy
  exact h

theorem maximalIdeal_eq_span_t (AI : LocAinf l P) : IsLocalRing.maximalIdeal (Per6.BdRp l) =
    Ideal.span {fontaineT (Per6.tiltMap l AI.ε) (untilt_ε AI)} :=
  maximalIdeal_eq_span_fontaineT (untilt_ε AI) (untilt_ε_root_ne_one AI)

theorem tie_fil_zero (K : FinExt l) (x : P.R.BdR) : x ∈ (P.PD K).Fil 0 ↔
    ∃ y : Per6.BdRp l, T.eD x = algebraMap (Per6.BdRp l) (Per6.BdR l) y :=
  (T.fil K 0 x).trans (IsPerfectoidField.mem_fil_zero_iff ℂ_[l] l)

end PositivityTheory.LocInh
