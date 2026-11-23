import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorIdentificationNaturalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulNormLe
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CocycleNat

theorem exists_pow_smul_mem {l : ℕ} [hl : Fact l.Prime] {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] {G : Type} [Group G] [TopologicalSpace G]
    (T : LocLat G ℚ_[l] K O) (v : T.V) : ∃ n : ℕ, (l : K) ^ n • v ∈ T.L.T := by
  first
  | exact @_root_.GlobalTheory.NatCastNormLtOne.main
  | exact _root_.GlobalTheory.NatCastNormLtOne.main
  | (apply _root_.GlobalTheory.NatCastNormLtOne.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatCastNormLtOne.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatCastNormLtOne.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatCastNormLtOne.main ..)

end GlobalTheory.CocycleNat

noncomputable section

namespace GlobalTheory.CocycleNat

theorem actB_map {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [Algebra O K]
    [NormedAlgebra ℚ_[l] K] {G : Type} [Group G] [TopologicalSpace G] (s : G →* GQ l)
    {T₁ T₂ : LocLat G ℚ_[l] K O} (f : LatHom T₁.L T₂.L) (g : G) (z : TW (OB l O) T₁) :
    TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) (actB s T₁ g z) =
      actB s T₂ g (TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul r x =>
    simp only [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply]
    congr 1
    exact Subtype.ext (f.equiv g x)
  | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.CocycleNat

namespace GlobalTheory.CocycleNat

theorem main (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ)
    (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (T₁ T₂ : LocLat (Gl l) ℚ_[l] K O)
    (R₁ : GalDat t ϖ (sQ l) D₁ T₁) (R₂ : GalDat t ϖ (sQ l) D₂ T₂) (f : LatHom T₁.L T₂.L) (F : BKHom D₁ D₂) :
    IsMapOf R₁.I R₂.I f F.toHom → ∀ y c, R₁.ClassOf y c → R₂.ClassOf (F.app y) (f.post c) := by
  intro hF y c hc
  obtain ⟨b, ⟨hy, m₀, σ, b₀, h1, h2, h3, h4, hb⟩, hcob⟩ := hc
  have N := GlobalTheory.T.bcrisTensorIdentification_natural l a e O K t ϖ ι D₁.toPhiMod T₁ R₁.I R₁.jB R₁.cmp κ D₂.toPhiMod T₂ R₂.I R₂.jB f
    F.toHom R₂.cmp hF
  set Φ := TensorProduct.map (R := O) (LinearMap.id (R := O) (M := OB l O))
    ((f.f.restrictScalars O).restrict f.T_le) with hΦ
  have hy' : F.app y ∈ ME D₂.toPhiMod := F.app_mem_Mext (le_away _ _) hy
  have hσ' : F.app σ.1 ∈ D₂.MMl := F.toHom.app_mem_ext ((A_le_S (l := l) (e := e)).trans (le_away _ _)) σ.2
  refine ⟨Φ b, ⟨hy', homW t ϖ F.toHom m₀, ⟨F.app σ.1, hσ'⟩, Φ b₀, ?_, F.app_mem_inv h2, ?_, ?_, ?_⟩, ?_⟩
  · rw [← homW_phiW, ← map_sub, h1, homW_toW]
  · change D₂.conn (F.app σ.1) = D₂.zeta (F.app y)
    rw [← F.toHom.app_conn, h3, F.toHom.app_zeta]
  · have := N.2 _ _ h4
    rwa [homW_phiW] at this
  · rw [hb, map_sub, N.1 σ ⟨F.app σ.1, hσ'⟩ rfl]
  · intro g n x' hx'
    obtain ⟨N', hN'⟩ := exists_pow_smul_mem T₁ (c g)
    have hc2 := congrArg Φ (hcob g N' ⟨_, hN'⟩ rfl)
    rw [map_smul, map_sub, actB_map, hΦ, TensorProduct.map_tmul, LinearMap.id_apply] at hc2
    rw [← hΦ] at hc2
    have hsm : ∀ (k : ℕ) (v : T₂.V), ((l : O) ^ k) • v = (l : K) ^ k • v := fun k v => by
      rw [← algebraMap_smul K ((l : O) ^ k) v, map_pow, map_natCast]
    have hx'' : (l : O) ^ N' • x' = (l : O) ^ n • ((f.f.restrictScalars O).restrict f.T_le ⟨_, hN'⟩) := by
      apply Subtype.ext
      change (l : O) ^ N' • (x' : T₂.V) = (l : O) ^ n • f.f ((l : K) ^ N' • c g)
      rw [hx', hsm, hsm, map_smul, smul_smul, smul_smul, mul_comm]
      rfl
    have key : ∀ z w : TW (OB l O) T₂, (l : O) ^ N' • z = (l : O) ^ N' • w → z = w := by
      intro z w h
      have hu : IsUnit ((l : OB l O) ^ N') := by
        have := (GlobalTheory.MemLoc.isUnit_l_Bcris l).map
          (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O)
        rw [map_natCast] at this
        exact this.pow N'
      rw [← algebraMap_smul (OB l O) ((l : O) ^ N') z, ← algebraMap_smul (OB l O) ((l : O) ^ N') w,
        map_pow, map_natCast] at h
      exact hu.smul_left_cancel.1 h
    apply key
    rw [← TensorProduct.tmul_smul, hx'', TensorProduct.tmul_smul, hc2, smul_comm]

end GlobalTheory.CocycleNat
