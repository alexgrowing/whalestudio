import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineFilteredDeRhamComparisonStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.CrysCoordDR

variable {l : ℕ} [Fact l.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V]
  [IsScalarTower ℤ_[l] ℚ_[l] V]

def basisQ (T : Submodule ℤ_[l] V) (hT : Submodule.span ℚ_[l] (T : Set V) = ⊤) {d : ℕ}
    (b : Module.Basis (Fin d) ℤ_[l] T) : Module.Basis (Fin d) ℚ_[l] V :=
  Module.Basis.mk (v := fun i => (b i : V))
    ((b.linearIndependent.map' T.subtype (Submodule.ker_subtype T)).localization ℚ_[l]
      (nonZeroDivisors ℤ_[l]))
    (by
      rw [← hT]
      refine Submodule.span_le.2 fun x hx => ?_
      have h := b.sum_repr ⟨x, hx⟩
      have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : V) := by
        have := congrArg Subtype.val h
        rw [AddSubmonoidClass.coe_finsetSum] at this
        simp only [SetLike.val_smul] at this
        exact this.symm
      rw [hx']
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem basisQ_apply (T : Submodule ℤ_[l] V) (hT : Submodule.span ℚ_[l] (T : Set V) = ⊤) {d : ℕ}
    (b : Module.Basis (Fin d) ℤ_[l] T) (i : Fin d) : basisQ T hT b i = (b i : V) := by
  unfold basisQ
  exact Module.Basis.mk_apply _ _ _

end GlobalTheory.CrysCoordDR

noncomputable section

namespace GlobalTheory.CrysCoordDR

variable {l : ℕ} [Fact l.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
  {B : Type} [CommRing B] [Algebra ℚ_[l] B]

def coord {d : ℕ} (e : Module.Basis (Fin d) ℚ_[l] V) (r : Fin d) : V ⊗[ℚ_[l]] B →ₗ[ℚ_[l]] B :=
  (TensorProduct.lid ℚ_[l] B).toLinearMap ∘ₗ TensorProduct.map (e.coord r) LinearMap.id

theorem coord_tmul {d : ℕ} (e : Module.Basis (Fin d) ℚ_[l] V) (r : Fin d) (v : V) (x : B) :
    coord e r (v ⊗ₜ x) = e.repr v r • x := by
  simp [coord]

theorem coord_mulLeft {d : ℕ} (e : Module.Basis (Fin d) ℚ_[l] V) (r : Fin d) (c : B)
    (x : V ⊗[ℚ_[l]] B) :
    coord e r (AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V)
      (LinearMap.mulLeft ℚ_[l] c) x) = c * coord e r x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simp [coord_tmul, mul_smul_comm]
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]

theorem coord_mem {d : ℕ} (e : Module.Basis (Fin d) ℚ_[l] V) (r : Fin d) (F : Submodule ℚ_[l] B)
    (x : V ⊗[ℚ_[l]] B)
    (hx : x ∈ LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V) F.subtype)) :
    coord e r x ∈ F := by
  obtain ⟨w, rfl⟩ := hx
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simpa [coord_tmul] using F.smul_mem (e.repr v r) y.2
  | add x y hx hy => simpa only [map_add] using F.add_mem hx hy

theorem coord_map {d : ℕ} (e : Module.Basis (Fin d) ℚ_[l] V) (s : Fin d) (f : V →ₗ[ℚ_[l]] V)
    (τ : B →ₗ[ℚ_[l]] B) (x : V ⊗[ℚ_[l]] B) :
    coord e s (AlgebraTensorModule.map f τ x) =
      ∑ r, LinearMap.toMatrix e e f s r • τ (coord e r x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v y =>
    simp only [AlgebraTensorModule.map_tmul, coord_tmul, map_smul, smul_smul]
    rw [← Finset.sum_smul, ← LinearMap.toMatrix_mulVec_repr e e f v]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy, smul_add, Finset.sum_add_distrib]

end GlobalTheory.CrysCoordDR

noncomputable section

namespace GlobalTheory.CrysCoordDR

theorem toMatrix_basisQ {l : ℕ} [Fact l.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] {G : Type} [Group G]
    {ρ : Representation ℚ_[l] G V} (L : Lattice (O := ℤ_[l]) ρ) {d : ℕ}
    (b : Module.Basis (Fin d) ℤ_[l] ↥L.T) (g : G) (s r : Fin d) :
    LinearMap.toMatrix (basisQ L.T L.span b) (basisQ L.T L.span b) (ρ g) s r =
      ((LinearMap.toMatrix b b (actT L g) s r : ℤ_[l]) : ℚ_[l]) := by
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  have h : ρ g (basisQ L.T L.span b r) =
      ∑ s', ((b.repr (actT L g (b r)) s' : ℤ_[l]) : ℚ_[l]) • basisQ L.T L.span b s' := by
    have := congrArg Subtype.val (b.sum_repr (actT L g (b r)))
    rw [AddSubmonoidClass.coe_finsetSum] at this
    simp only [SetLike.val_smul] at this
    simp only [basisQ_apply]
    rw [show ρ g (b r : V) = ((actT L g (b r) : ↥L.T) : V) from rfl, ← this]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [← algebraMap_smul ℚ_[l] (b.repr (actT L g (b r)) s') ((b s' : ↥L.T) : V)]
    rfl
  rw [h, Module.Basis.repr_sum_self]

end GlobalTheory.CrysCoordDR

open GlobalTheory.CrysCoordDR in
theorem GlobalTheory.crysLattice_basis_mem_sum_fil_dR : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ), IsCrys (P.PD K) ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[l] ↥L.T), ∀ j : Fin d, ∃ (m : ℕ) (k : Fin m → ℤ) (c : Fin m → Per.BdR l) (v : Fin m → Fin d → Per.BdR l), (∀ i (g : ↥(GK K)), ((LinearMap.toMatrix b b (actT L g)).map (Per.zD l)).mulVec (fun r => Per.σD (g : GQ l) (v i r)) = v i) ∧ (∀ i r, v i r ∈ Per.FilD l (k i)) ∧ (∀ i, c i ∈ Per.FilD l (-k i)) ∧ (Pi.single j 1 : Fin d → Per.BdR l) = ∑ i, c i • v i := by
  intro l _ K P AI T V _ _ _ _ _ ρ L hcrys d b j
  have hy : ((b j : ↥L.T) : V) ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) 0 :=
    ⟨((b j : ↥L.T) : V) ⊗ₜ ⟨1, (P.PD K).one_mem⟩, by simp [AlgebraTensorModule.map_tmul]⟩
  obtain ⟨m, k, c, dd, hdd, hsum⟩ := GlobalTheory.T.crystalline_filtered_deRham_comparison l P AI T K V ρ hcrys 0 _ hy
  refine ⟨m, k, fun i => T.eD (c i), fun i r => T.eD (coord (basisQ L.T L.span b) r (dd i)),
    ?_, ?_, ?_, ?_⟩
  · intro i g
    funext s
    have hinv : actVdR (P.PD K) ρ g (dd i) = dd i := by
      have := (hdd i).1
      simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at this
      exact this g
    show _ = T.eD (coord (basisQ L.T L.span b) s (dd i))
    conv_rhs => rw [← hinv]
    rw [actVdR, coord_map, map_sum]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [toMatrix_basisQ, Algebra.smul_def, map_mul, T.zD]
    congr 1
    change _ = T.eD ((P.PD K).actdR g _)
    rw [P.PD_actdR K g, T.actD]
  · intro i r
    rw [← T.fil K]
    exact coord_mem _ r (((P.PD K).Fil (k i)).restrictScalars ℚ_[l]) _ (hdd i).2.1
  · intro i
    rw [← T.fil K]
    simpa using (hdd i).2.2
  · funext r
    have h1 := congrArg (coord (basisQ L.T L.span b) r) hsum
    rw [← basisQ_apply L.T L.span b j, coord_tmul, map_sum] at h1
    simp only [coord_mulLeft, Module.Basis.repr_self] at h1
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    have h2 := congrArg T.eD h1
    rw [map_sum] at h2
    simp only [map_mul] at h2
    rw [← h2]
    by_cases hr : r = j
    · subst hr; simp
    · simp [hr, Finsupp.single_apply, Pi.single_apply, Ne.symm hr]
