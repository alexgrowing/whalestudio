import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.Per Matrix

namespace GlobalTheory.BKReal.Full

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e}
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

section Lat

variable {G : Type} [Group G] [TopologicalSpace G] {T T' : LocLat G ℚ_[l] K O}

omit [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K] in

theorem latW_smul (f : LatHom T.L T'.L) (r : OW l O) (y : TW (OW l O) T) :
    latW f (r • y) = r • latW f y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul w x => rfl
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

omit [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K] in

theorem latW_frob (f : LatHom T.L T'.L) (y : TW (OW l O) T) :
    latW f (TWmap (frobOW l O) T y) = TWmap (frobOW l O) T' (latW f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

def latZ (f : LatHom T.L T'.L) :
    letI := zlLat T
    letI := zlLat T'
    ↥T.L.T →ₗ[ℤ_[l]] ↥T'.L.T :=
  letI := zlLat T
  letI := zlLat T'
  { toFun := (f.f.restrictScalars O).restrict f.T_le
    map_add' := map_add _
    map_smul' := fun z x => ((f.f.restrictScalars O).restrict f.T_le).map_smul (algebraMap ℤ_[l] O z) x }

omit [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K] in

theorem kappa_latZ (f : LatHom T.L T'.L) :
    letI := zlLat T
    letI := zlLat T'
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T' ((latZ f).lTensor (WCb l) y) = latW f (kappa T y) := by
  let _ := zlLat T
  let _ := zlLat T'
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ}

theorem exists_isMapOf (I : Ident t ϖ P T) (I' : Ident t ϖ Q T') (f : LatHom T.L T'.L)
    (h : ∀ (m : Vec K a ι) (hm : m ∈ P.M), ∃ (m' : Vec K a κ) (hm' : m' ∈ Q.M),
      latW f (I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) = I'.j (toW t ϖ Q ⟨m', mem_ME_of_mem_M hm'⟩)) :
    ∃ F, IsMapOf I I' f F := by
  have hb : ∀ j : ι, (fun _ => Pi.single j 1 : Vec K a ι) ∈ P.M := fun j => mem_tot.2 fun τ i => by
    by_cases hij : i = j
    · subst hij; rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne hij]; exact zero_mem _
  have hb' : ∀ j : ι, toW t ϖ P ⟨_, mem_ME_of_mem_M (hb j)⟩ = Pi.single j 1 := fun j => funext fun i => by
    rw [toW_apply]
    by_cases hij : i = j
    · subst hij
      rw [Pi.single_eq_same (M := fun _ => OW l O), ← map_one (ϖ.iW t K)]
      exact congrArg _ (funext fun τ => Subtype.ext (Pi.single_eq_same (M := fun _ => K⟦X⟧) i 1))
    · rw [Pi.single_eq_of_ne (M := fun _ => OW l O) hij, ← map_zero (ϖ.iW t K)]
      exact congrArg _ (funext fun τ => Subtype.ext (Pi.single_eq_of_ne (M := fun _ => K⟦X⟧) hij 1))
  choose m hm hmj using fun j => h _ (hb j)
  simp only [hb'] at hmj
  let Y : Matrix κ ι (OW l O) :=
    Matrix.of fun i j => inclO l O (ϖ.iTot t K fun τ => ⟨m j τ i, mem_tot.1 (hm j) τ i⟩)
  have hY : ∀ j, toW t ϖ Q ⟨m j, mem_ME_of_mem_M (hm j)⟩ = fun i => Y i j := fun j => funext fun i =>
    ϖ.iW_of_mem t K fun τ => ⟨m j τ i, mem_tot.1 (hm j) τ i⟩
  have key : ∀ v, I'.j (Y *ᵥ v) = latW f (I.j v) := fun v => by
    have h1 : Y *ᵥ v = ∑ j, v j • fun i => Y i j := by
      ext1 i
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    conv_rhs => rw [pi_eq_sum_univ' v, map_sum, map_sum]
    rw [h1, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul I.j, latW_smul, hmj, hY, map_smul I'.j]
  have hmat : Y * frobMat t ϖ P = frobMat t ϖ Q * Y.map (frobOW l O) := by
    have h1 : ∀ v, Y *ᵥ phiW t ϖ P v = phiW t ϖ Q (Y *ᵥ v) := fun v => I'.j.injective (by
      rw [key, I.j_φ, latW_frob, I'.j_φ, key])
    ext1 i j
    have h2 := congrFun (h1 (Pi.single j 1)) i
    have h3 : (fun k => frobOW l O (Pi.single (M := fun _ : ι => OW l O) j 1 k)) = Pi.single j 1 :=
      funext fun k => by simp only [Pi.single_apply, apply_ite (frobOW l O), map_one, map_zero]
    rw [phiW_apply, phiW_apply, h3, Matrix.mulVec_mulVec, Matrix.mulVec_single_one,
      Matrix.mulVec_single_one] at h2
    exact h2
  refine ⟨⟨fun τ => Matrix.of fun i j => m j τ i, fun τ i j => mem_tot.1 (hm j) τ i, fun τ => ?_⟩, key⟩
  ext1 i j
  have h1 := congrFun₂ hmat i j
  change ∑ k, inclO l O (ϖ.iTot t K _) * ϖ.iW t K _ =
    ∑ k, ϖ.iW t K _ * frobOW l O (inclO l O (ϖ.iTot t K _)) at h1
  simp only [frobOW_inclO, ← PiSys.iTot_frob] at h1
  simp only [← ϖ.iW_of_mem t K, ← map_mul] at h1
  rw [← map_sum, ← map_sum] at h1
  have h2 := congrArg Subtype.val (congrFun (ϖ.iW_injective t K h1) τ)
  rw [Finset.sum_apply, Finset.sum_apply, AddSubmonoidClass.coe_finsetSum,
    AddSubmonoidClass.coe_finsetSum] at h2
  exact h2

end Lat

theorem main (BS : GlobalTheory.Published.BhattScholzeCrystallineLattices) (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a]
    [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T T' : Lat a O K ϖ)
    (I : Ident t ϖ P T) (I' : Ident t ϖ Q T') (H : IsBK I) (H' : IsBK I') (f : LatHom T.L T'.L) :
    ∃ F, IsMapOf I I' f F := by
  let _ := zlLat T
  let _ := zlLat T'
  obtain ⟨E, j, hE, h⟩ := H
  obtain ⟨E', j', hE', h'⟩ := H'
  obtain ⟨u, hu, -⟩ := (BS l (ϖ.field a) _ _ (isAinf_ainfObj _)).2 _ _ _ _ E E' j j' hE hE' (latZ f)
    fun g x => Subtype.ext (f.equiv g x)
  refine exists_isMapOf I I' f fun m hm => (h' _).1 ?_
  obtain ⟨x, hx⟩ := (h _).2 ⟨m, hm, rfl⟩
  refine ⟨u.u _ x, ?_⟩
  rw [hx, ← u.u_tr, hu]
  exact (kappa_latZ f _).symm

end GlobalTheory.BKReal.Full
