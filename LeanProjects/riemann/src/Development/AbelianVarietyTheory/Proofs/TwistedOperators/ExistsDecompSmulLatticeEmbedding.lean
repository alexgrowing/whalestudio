import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEmbeddingContinuousMulRational
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitaryEmbeddingLattice

variable {D : D7} {Y V : HSp D}

local notation "inc" => Formalism.UG.inclE (F := D.host.F) (E := D.host.E) (Formalism.L2.Herm.Af D.host.F)

def phiRow (d : HermitianOrthogonalExtensionData Y V 1 1) : Matrix (Fin 1) (Fin V.rank) D.host.E :=
  Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.a * V.gram

theorem cT_zero {m p : ℕ} : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (0 : Matrix (Fin m) (Fin p) D.host.E) = 0 := by
  ext i j; simp [Formalism.UG.cT]

theorem qM_mul_a (d : HermitianOrthogonalExtensionData Y V 1 1) : GlobalTheory.UnitaryEmbeddingProperties.qM d * d.a = 0 := by
  rw [GlobalTheory.UnitaryEmbeddingProperties.qM, Matrix.mul_assoc, d.perp, Matrix.mul_zero]

theorem phiRow_mul_P (d : HermitianOrthogonalExtensionData Y V 1 1) : phiRow d * frameMat V Y d.ι = 0 := by
  have h := congrArg (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)) d.perp
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, GlobalTheory.AutFunCounterexample.gram_herm, GlobalTheory.AutFunCounterexample.cT_cT, cT_zero] at h
  rw [phiRow, Matrix.mul_assoc, h]

theorem phiRow_mul_a (d : HermitianOrthogonalExtensionData Y V 1 1) : phiRow d * d.a = 1 := by
  rw [phiRow, d.gram]
  ext i j
  fin_cases i; fin_cases j
  simp [antiDiagonalSignGramMatrix]

theorem P_Q_add (d : HermitianOrthogonalExtensionData Y V 1 1) : frameMat V Y d.ι * GlobalTheory.UnitaryEmbeddingProperties.qM d + d.a * phiRow d = 1 := by
  have h : Matrix.fromRows (GlobalTheory.UnitaryEmbeddingProperties.qM d) (phiRow d) * Matrix.fromCols (frameMat V Y d.ι) d.a = 1 := by
    rw [Matrix.fromRows_mul_fromCols, GlobalTheory.UnitaryEmbeddingProperties.qM_mul, qM_mul_a, phiRow_mul_P, phiRow_mul_a, Matrix.fromBlocks_one]
  have h2 := (Matrix.mul_eq_one_comm_of_equiv (finSumFinEquiv.trans (finCongr d.rank))).1 h
  rwa [Matrix.fromCols_mul_fromRows] at h2

theorem decomp (d : HermitianOrthogonalExtensionData Y V 1 1) (v : Fin V.rank → D.host.E) :
    v = frameMat V Y d.ι *ᵥ (GlobalTheory.UnitaryEmbeddingProperties.qM d *ᵥ v) + (phiRow d *ᵥ v) 0 • zv d := by
  conv_lhs => rw [← Matrix.one_mulVec v, ← P_Q_add d]
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  congr 1
  funext i
  simp [Matrix.mulVec, dotProduct, zv, mul_comm]

theorem finiteAdele_unitaryEmbedding (d : HermitianOrthogonalExtensionData Y V 1 1) (h : GA D Y) :
    (Lev.finE V (stabilizerEmbedding d h)).1 = GlobalTheory.UnitaryEmbeddingProperties.ex ((frameMat V Y d.ι).map inc) ((GlobalTheory.UnitaryEmbeddingProperties.qM d).map inc)
      (Lev.finE Y h).1 := by
  rw [GlobalTheory.LevSplit.finE_val, GlobalTheory.LevSplit.finE_val]
  unfold Formalism.L2.Theta.mt
  rw [GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_matrix_formula, GlobalTheory.UnitaryEmbeddingProperties.ex_map, Matrix.map_map, Matrix.map_map]
  rfl

theorem summandEmbedding_inv (d : HermitianOrthogonalExtensionData Y V 1 1) (h : GA D Y) : stabilizerEmbedding d h⁻¹ = (stabilizerEmbedding d h)⁻¹ :=
  map_inv (MonoidHom.mk' (stabilizerEmbedding d) (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul d)) h

theorem Q_ex {R : Type} [CommRing R] {n r : ℕ} (P : Matrix (Fin n) (Fin r) R) (Q : Matrix (Fin r) (Fin n) R)
    (hQP : Q * P = 1) (h : Matrix (Fin r) (Fin r) R) : Q * GlobalTheory.UnitaryEmbeddingProperties.ex P Q h = h * Q := by
  simp only [GlobalTheory.UnitaryEmbeddingProperties.ex, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hQP, Matrix.one_mul,
    Matrix.sub_mul]
  abel

theorem row_ex {R : Type} [CommRing R] {n r k : ℕ} (P : Matrix (Fin n) (Fin r) R) (Q : Matrix (Fin r) (Fin n) R)
    (φ : Matrix (Fin k) (Fin n) R) (hφ : φ * P = 0) (h : Matrix (Fin r) (Fin r) R) :
    φ * GlobalTheory.UnitaryEmbeddingProperties.ex P Q h = φ := by
  simp only [GlobalTheory.UnitaryEmbeddingProperties.ex, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hφ, Matrix.zero_mul, add_zero]

set_option synthInstance.maxHeartbeats 400000 in
theorem incl_vec_mem {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {v : Fin n → D.host.E} (hv : v ∈ L) :
    (fun i => inc (v i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L :=
  Submodule.subset_span ⟨v, hv, rfl⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem mulVec_mem_of {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (S : Submodule (Formalism.L2.Herm.intAf D.host.F D.host.E) (Fin m → Lev.EAf D))
    (hM : ∀ v ∈ L, (fun i => inc ((M *ᵥ v) i)) ∈ S) :
    ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) L, M.map inc *ᵥ z ∈ S := by
  let S' : Submodule (Formalism.L2.Herm.intAf D.host.F D.host.E) (Fin n → Lev.EAf D) :=
    { carrier := {z | M.map inc *ᵥ z ∈ S}
      add_mem' := fun {x y} hx hy => by
        show M.map inc *ᵥ (x + y) ∈ S
        rw [Matrix.mulVec_add]
        exact S.add_mem hx hy
      zero_mem' := by
        show M.map inc *ᵥ (0 : Fin n → Lev.EAf D) ∈ S
        rw [Matrix.mulVec_zero]; exact S.zero_mem
      smul_mem' := fun c x hx => by
        show M.map inc *ᵥ (c • x) ∈ S
        convert S.smul_mem c hx using 1
        funext i
        simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Finset.smul_sum, Subring.smul_def, smul_eq_mul]
        exact Finset.sum_congr rfl fun j _ => by ring }
  have hle : Formalism.L2.Herm.hatL (F := D.host.F) L ≤ S' := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    show M.map inc *ᵥ (fun i => inc (v i)) ∈ S
    convert hM v hv using 1
    funext i
    exact (RingHom.map_mulVec inc M v i).symm
  exact fun z hz => hle hz

end GlobalTheory.UnitaryEmbeddingLattice

namespace GlobalTheory.UnitaryEmbeddingLattice

variable {D : D7} {Y V : HSp D}

local notation "inc" => Formalism.UG.inclE (F := D.host.F) (E := D.host.E) (Formalism.L2.Herm.Af D.host.F)

theorem mulVec_incl {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (v : Fin n → D.host.E) :
    M.map inc *ᵥ (fun i => inc (v i)) = fun i => inc ((M *ᵥ v) i) := by
  funext i
  exact (RingHom.map_mulVec inc M v i).symm

def qLin (d : HermitianOrthogonalExtensionData Y V 1 1) : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin Y.rank → D.host.E) where
  toFun v := GlobalTheory.UnitaryEmbeddingProperties.qM d *ᵥ v
  map_add' := Matrix.mulVec_add _
  map_smul' r v := Matrix.mulVec_smul _ r v

def phiLin (d : HermitianOrthogonalExtensionData Y V 1 1) : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] D.host.E where
  toFun v := (phiRow d *ᵥ v) 0
  map_add' v w := by rw [Matrix.mulVec_add]; rfl
  map_smul' r v := by rw [Matrix.mulVec_smul]; rfl

theorem lat_mem_Q (d : HermitianOrthogonalExtensionData Y V 1 1) (Λ : Lat Y) {v : Fin V.rank → D.host.E} (hv : v ∈ d.lat Λ fun _ => 1) :
    GlobalTheory.UnitaryEmbeddingProperties.qM d *ᵥ v ∈ Λ ∧ ∃ o : 𝓞 D.host.E, (o : D.host.E) = (phiRow d *ᵥ v) 0 := by
  obtain ⟨y, hy, u, hu, rfl⟩ := hv
  have e1 : GlobalTheory.UnitaryEmbeddingProperties.qM d *ᵥ (frameMat V Y d.ι *ᵥ y + d.a *ᵥ u) = y := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, GlobalTheory.UnitaryEmbeddingProperties.qM_mul, qM_mul_a,
      Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]
  have e2 : phiRow d *ᵥ (frameMat V Y d.ι *ᵥ y + d.a *ᵥ u) = u := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, phiRow_mul_P, phiRow_mul_a,
      Matrix.one_mulVec, Matrix.zero_mulVec, zero_add]
  refine ⟨by rw [e1]; exact hy, ?_⟩
  rw [e2]
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 (hu 0)
  exact ⟨o, ho⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem gen_props (d : HermitianOrthogonalExtensionData Y V 1 1) (Λ : Lat Y) (x : GA D Y) (y : Fin V.rank → D.host.E)
    (hy : (Lev.finE V (stabilizerEmbedding d x)⁻¹).1 *ᵥ (fun i => y i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ fun _ => 1)) :
    GlobalTheory.UnitaryEmbeddingProperties.qM d *ᵥ y ∈ latAt Λ x ∧ (phiRow d *ᵥ y) 0 ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  have hQP := GlobalTheory.UnitaryEmbeddingProperties.qM_mul_map inc d
  have hφP : (phiRow d).map inc * (frameMat V Y d.ι).map inc = 0 := by
    rw [← Matrix.map_mul, phiRow_mul_P, Matrix.map_zero _ (map_zero _)]
  have hy' : GlobalTheory.UnitaryEmbeddingProperties.ex ((frameMat V Y d.ι).map inc) ((GlobalTheory.UnitaryEmbeddingProperties.qM d).map inc) (Lev.finE Y x⁻¹).1 *ᵥ
      (fun i => inc (y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ fun _ => 1) := by
    rw [← finiteAdele_unitaryEmbedding, summandEmbedding_inv]
    exact hy
  constructor
  · have h1 := mulVec_mem_of (GlobalTheory.UnitaryEmbeddingProperties.qM d) _ (Formalism.L2.Herm.hatL (F := D.host.F) Λ)
      (fun v hv => incl_vec_mem (lat_mem_Q d Λ hv).1) _ hy'
    rw [Matrix.mulVec_mulVec, Q_ex _ _ hQP, ← Matrix.mulVec_mulVec, mulVec_incl] at h1
    exact Submodule.subset_span h1
  · have h2 := mulVec_mem_of (phiRow d) _ (Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Col.stdLat D.host.E 1))
      (fun v hv => by
        rw [GlobalTheory.CongStdLoc.mem_hatL_std_iff]
        intro i
        obtain ⟨o, ho⟩ := (lat_mem_Q d Λ hv).2
        rw [Subsingleton.elim i 0, ← ho]
        exact (GlobalTheory.NormSum.AdLattice.incl_mem_iff _).2 ⟨o, rfl⟩) _ hy'
    rw [Matrix.mulVec_mulVec, row_ex _ _ _ hφP, mulVec_incl] at h2
    obtain ⟨o, ho⟩ := (GlobalTheory.NormSum.AdLattice.incl_mem_iff _).1 ((GlobalTheory.CongStdLoc.mem_hatL_std_iff _).1 h2 0)
    exact Submodule.mem_one.2 ⟨o, ho⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem mem_smul_lattice_unitaryEmbedding : ∀ (D : D7) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (Λ : Lat Y) (x : GA D Y) (𝔪 : Ideal (𝓞 D.host.E)) (w : Fin V.rank → D.host.E), w ∈ 𝔪 • latAt (d.lat Λ fun _ => 1) (stabilizerEmbedding d x) → ∃ y ∈ 𝔪 • latAt Λ x, ∃ u : 𝓞 D.host.E, u ∈ 𝔪 ∧ w = frameMat V Y d.ι *ᵥ y + (u : D.host.E) • zv d := by
  intro D Y V d Λ x 𝔪 w hw
  have hQ : latAt (d.lat Λ fun _ => 1) (stabilizerEmbedding d x) ≤ (latAt Λ x).comap (qLin d) :=
    Submodule.span_le.2 fun y hy => (gen_props d Λ x y hy).1
  have hφ : latAt (d.lat Λ fun _ => 1) (stabilizerEmbedding d x) ≤ (1 : Submodule (𝓞 D.host.E) D.host.E).comap (phiLin d) :=
    Submodule.span_le.2 fun y hy => (gen_props d Λ x y hy).2
  have hQm : 𝔪 • latAt (d.lat Λ fun _ => 1) (stabilizerEmbedding d x) ≤ (𝔪 • latAt Λ x).comap (qLin d) :=
    Submodule.smul_le.2 fun r hr n hn => by
      rw [Submodule.mem_comap, map_smul]
      exact Submodule.smul_mem_smul hr (hQ hn)
  have hφm : 𝔪 • latAt (d.lat Λ fun _ => 1) (stabilizerEmbedding d x) ≤
      (Submodule.map (Algebra.linearMap (𝓞 D.host.E) D.host.E) 𝔪).comap (phiLin d) :=
    Submodule.smul_le.2 fun r hr n hn => by
      rw [Submodule.mem_comap, map_smul]
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 (hφ hn)
      rw [← ho]
      exact ⟨r * o, Ideal.mul_mem_right o 𝔪 hr, by simp [Algebra.smul_def]⟩
  obtain ⟨u, hu, hu'⟩ := hφm hw
  refine ⟨GlobalTheory.UnitaryEmbeddingProperties.qM d *ᵥ w, hQm hw, u, hu, ?_⟩
  have e : (u : D.host.E) = (phiRow d *ᵥ w) 0 := hu'
  rw [e]
  exact decomp d w

end GlobalTheory.UnitaryEmbeddingLattice
