import Mathlib
import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypTwA
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.LocalToGlobal.HermitianColumns.FullSym
import Formalism.LocalToGlobal.Columns.RecLevelLoc
import Formalism.LocalRingCardinality.SpanPowerMembership.Places
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.LatSOfLocBasis
import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.TiedCls
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.MemAll
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK

noncomputable section

section
namespace GlobalTheory.Port

open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv Formalism.MainNotions.G.ChF

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags Formalism.L2.Forms Formalism.L2.Herm Formalism.UG NumberField IsDedekindDomain Matrix
  Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.MainNotions.G.ChartsLv
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

set_option maxHeartbeats 1000000 in

theorem det_stab_loc (v : HeightOneSpectrum (𝓞 F)) (Lb : Submodule (𝓞 E) (Fin n → E)) (hfg : Lb.FG)
    (hsp : Submodule.span E (Lb : Set (Fin n → E)) = ⊤) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hg : g ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) Lb)) :
    (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)).det ∈ intV E v := by
  obtain ⟨q, hq, hv⟩ := Formalism.BasicNotions.Examples₂.PlacesToy.exists_prime_mem v
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨B, hB⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis q _ Lb hfg hsp
  rw [latS_of_locBasis v hq hv Lb B hB] at hg
  obtain ⟨Bv, hBv⟩ : ∃ Bv, Bv = bc (inclE (F := F) (v.adicCompletion F)) B := ⟨_, rfl⟩
  have hent : ∀ a b, ((Bv⁻¹ * g * Bv : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b ∈ intV E v := by
    intro a b
    have h1 : (Bv : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ (Pi.single b 1) ∈
        latS (F := F) (v.adicCompletion F) (intV E v) (latB B) := by
      refine (mem_latS_latB v B _).2 fun a' => ?_
      rw [← hBv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      by_cases h : a' = b
      · subst h
        rw [Pi.single_eq_same]
        exact one_mem _
      · rw [Pi.single_eq_of_ne h]
        exact zero_mem _
    have h3 := (mem_latS_latB v B _).1 ((hg _).1 h1) a
    rw [← hBv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h3
    rw [Units.val_mul, Units.val_mul]
    exact h3
  have hd := det_mem_sub (intV E v) _ hent
  have e3 : Matrix.GeneralLinearGroup.det (Bv⁻¹ * g * Bv) = Matrix.GeneralLinearGroup.det g := by
    rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  have e4 : ((Bv⁻¹ * g * Bv : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)).det =
      (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)).det := congrArg Units.val e3
  rw [← e4]
  exact hd

variable {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

set_option maxHeartbeats 1000000 in

theorem det_int_of_level (S : StepLevel F E σ J T f bad) (x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hx : x ∈ S.U) :
    (x : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).det ∈ intAf F E := by
  refine Formalism.L2.Col.rll_int_of_loc _ fun v => ?_
  have h2 := (S.Uloc_lev v (((S.U_eq x).1 hx).2 v)).2
  have h3 := det_stab_loc v S.Lb (Module.Finite.iff_fg.1 S.Lb_fin) S.Lb_span _ h2
  rw [RingHom.map_det]
  exact h3

theorem det_norm_one (hJ : IsUnit J.det) (x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hx : x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) (x : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).det *
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).det = 1 := by
  have h := congrArg Matrix.det (show cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (x : Matrix (Fin n) (Fin n) _) *
    J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) * (x : Matrix (Fin n) (Fin n) _) =
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) from hx)
  have hu : IsUnit (J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).det := by
    have e : (J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).det = inclE (F := F) (FiniteAdeleRing (𝓞 F) F) J.det :=
      (RingHom.map_det _ J).symm
    rw [e]
    exact hJ.map _
  rw [Matrix.det_mul, Matrix.det_mul, cT, Matrix.det_transpose] at h
  have e2 : ((x : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).map (sigR σ (FiniteAdeleRing (𝓞 F) F))).det =
      sigR σ (FiniteAdeleRing (𝓞 F) F) (x : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).det :=
    (RingHom.map_det _ _).symm
  rw [e2] at h
  refine hu.mul_right_cancel ?_
  rw [one_mul, mul_right_comm]
  exact h

end Gen

variable {D : D7}

theorem scalar_mem_U1Af (d : (D.host.E ⊗[D.host.F] Af D.host.F)ˣ)
    (h : sigR D.sp.cm.sig (Af D.host.F) (d : D.host.E ⊗[D.host.F] Af D.host.F) * d = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 1) d ∈ unitaryOneFiniteAdeles D.sp.cm := by
  show cT _ _ * _ * _ = _
  ext a b
  fin_cases a; fin_cases b
  simp [cT, Matrix.mul_apply, Matrix.GeneralLinearGroup.scalar, h]

theorem scalar_stab {A : Type} [CommRing A] (R : Subring A) (d : Aˣ) (h1 : (d : A) ∈ R) (h2 : ((d⁻¹ : Aˣ) : A) ∈ R) :
    Matrix.GeneralLinearGroup.scalar (Fin 1) d ∈ stabGL (stdLat (n := Fin 1) (A := A) ↥R) := by
  intro y
  have hmem : ∀ y : Fin 1 → A, y ∈ stdLat (n := Fin 1) (A := A) ↥R ↔ ∀ a, y a ∈ R := by
    intro y
    constructor
    · intro hy a
      obtain ⟨r, hr⟩ := hy a trivial
      rw [← hr]
      exact r.2
    · intro hy a _
      exact ⟨⟨y a, hy a⟩, rfl⟩
  have hsm : ∀ a, ((Matrix.GeneralLinearGroup.scalar (Fin 1) d : GL (Fin 1) A) : Matrix (Fin 1) (Fin 1) A).mulVec y a = d * y a := by
    intro a
    fin_cases a
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.mulVec, dotProduct]
  rw [hmem, hmem]
  constructor
  · intro hy a
    rw [hsm]
    exact mul_mem h1 (hy a)
  · intro hy a
    have h3 := mul_mem h2 (hy a)
    rw [hsm, ← mul_assoc, Units.inv_mul, one_mul] at h3
    exact h3

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem scalar_mem_U1int (d : (D.host.E ⊗[D.host.F] Af D.host.F)ˣ)
    (h : sigR D.sp.cm.sig (Af D.host.F) (d : D.host.E ⊗[D.host.F] Af D.host.F) * d = 1)
    (h1 : (d : D.host.E ⊗[D.host.F] Af D.host.F) ∈ intAf D.host.F D.host.E)
    (h2 : ((d⁻¹ : (D.host.E ⊗[D.host.F] Af D.host.F)ˣ) : D.host.E ⊗[D.host.F] Af D.host.F) ∈ intAf D.host.F D.host.E) :
    Matrix.GeneralLinearGroup.scalar (Fin 1) d ∈ IntegralUnitGroup D.sp.cm :=
  ⟨scalar_mem_U1Af d h, scalar_stab _ d h1 h2⟩

variable (D) in

def detU (i : ℕ) (hi : i ≤ D.R.m) : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) →* unitaryOneFiniteAdeles D.sp.cm :=
  (((Matrix.GeneralLinearGroup.scalar (Fin 1)).comp Matrix.GeneralLinearGroup.det).comp
    (UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).subtype).codRestrict (unitaryOneFiniteAdeles D.sp.cm)
    fun x => scalar_mem_U1Af _ (det_norm_one (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) x.1 x.2)

theorem det_detU (i : ℕ) (hi : i ≤ D.R.m) (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    Matrix.GeneralLinearGroup.det (detU D i hi x : GL (Fin 1) (D.host.E ⊗[D.host.F] Af D.host.F)) =
      Matrix.GeneralLinearGroup.det (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
  show Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) _) = _
  rw [Matrix.GeneralLinearGroup.det_scalar]
  simp

variable {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}

set_option maxHeartbeats 2000000 in

def detTieOf (H : SymmetricHermitianColumns D) (S : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) : DetTie S where
  dt := H.dt.comp (detU D i hi)
  dt_rat := by
    intro γ hγ x hx
    have hz : star (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).det *
        (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).det = 1 := by
      have h := congrArg Matrix.det (show cT (sigD D : D.host.E →+* D.host.E) γ.1 * gramN D i hi * γ.1 = gramN D i hi from hγ)
      rw [Matrix.det_mul, Matrix.det_mul, cT, Matrix.det_transpose] at h
      have e2 : ((γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).map (sigD D : D.host.E →+* D.host.E)).det =
          (sigD D : D.host.E →+* D.host.E) (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).det := (RingHom.map_det _ _).symm
      rw [e2] at h
      refine (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi).mul_right_cancel ?_
      rw [one_mul, mul_right_comm]
      exact h
    refine ⟨⟨(γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).det, Unitary.mem_iff.2 ⟨hz, by rw [mul_comm]; exact hz⟩⟩, rfl, ?_⟩
    refine (H.dt_rat _ _ ?_).symm
    rw [det_detU, hx, det_bc]
    exact Units.ext rfl
  dt_U := by
    intro x hx
    rw [H.dt_UO]
    refine ⟨detU D i hi x, Subgroup.mem_subgroupOf.2 ?_, rfl⟩
    refine scalar_mem_U1int _ (det_norm_one (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) x.1 x.2) (det_int_of_level S x.1 hx) ?_
    rw [← map_inv]
    exact det_int_of_level S x.1⁻¹ (S.U.inv_mem hx)

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX}

end GlobalTheory.Port

end

end
