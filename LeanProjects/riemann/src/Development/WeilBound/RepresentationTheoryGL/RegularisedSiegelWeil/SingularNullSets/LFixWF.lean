import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWE

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open scoped Matrix NNReal TensorProduct
open IsDedekindDomain NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.AdelicU
  GlobalTheory.MixModel GlobalTheory.StdUnn GlobalTheory.Doubling Filter MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L.LFixW

variable {D : D7} {n : ℕ}

def UnitTriv (D : D7) (χ : (AE D)ˣ →* Circle) (S : Finset (Pl D)) : Prop :=
  ∀ u : (AE D)ˣ, (∀ w, compInf D.host.F D.host.E w (u : AE D) = 1) → (∀ v ∈ S, cv D v (u : AE D) = 1) →
    (∀ v ∉ S, cv D v (u : AE D) ∈ intLoc D.host.F D.host.E v ∧
      cv D v ((u⁻¹ : (AE D)ˣ) : AE D) ∈ intLoc D.host.F D.host.E v) → χ u = 1 ∧ absA D u = 1

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  have := congrFun (congrFun (adj_adj (D := D) (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => z)) 0) 0
  simpa [adj] using this

theorem det_mem_intLoc {v : Pl D} {M : Matrix (Fin n) (Fin n) (Fv D.host.F v ⊗[D.host.F] D.host.E)}
    (h : ∀ i j, M i j ∈ intLoc D.host.F D.host.E v) : M.det ∈ intLoc D.host.F D.host.E v := by
  let M' : Matrix (Fin n) (Fin n) (intLoc D.host.F D.host.E v) := fun i j => ⟨M i j, h i j⟩
  have h1 := (intLoc D.host.F D.host.E v).subtype.map_det M'
  have e : (intLoc D.host.F D.host.E v).subtype.mapMatrix M' = M := by ext i j; rfl
  rw [e] at h1
  rw [← h1]
  exact (M'.det).2

theorem map_one_entry {R : Type} [CommRing R] (f : AE D →+* R) (k j : Fin n) :
    f ((1 : Mx D n n) k j) = (1 : Matrix (Fin n) (Fin n) R) k j := by
  by_cases h : k = j
  · subst h; simp
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]

variable {S : Finset (Pl D)} {e : AE D}

theorem fixM (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (he : IsIdem S e) (hU : UnitTriv D χ S) {g : G D n} (hg : g ∈ KOff D n S) (hM : IsM g)
    (Ψ : schwartzA θ V.rank n) (hΨ : Good S e Ψ.1) : ω g Ψ = Ψ := by
  obtain ⟨a, ha⟩ := hM
  have hll : ∀ i j, a.1 i j = mat g (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) := fun i j => by
    rw [ha, block_matrix_apply_inl_inl_alt]
  have hrr : ∀ i j, (a⁻¹).1 i j = cA D (mat g (finSumFinEquiv (Sum.inr j)) (finSumFinEquiv (Sum.inr i))) := fun i j => by
    rw [ha, block_matrix_apply_inr_inr_alt]
    show _ = cA D (cA D ((a⁻¹).1 i j))
    rw [cA_cA]
  have hinf : ∀ w i j, compInf D.host.F D.host.E w (a.1 i j) = (1 : Matrix (Fin n) (Fin n) _) i j := fun w i j => by
    rw [hll, LFixTh.kOff_inf hg, one_ll]
  have hat : ∀ v ∈ S, ∀ i j, cv D v (a.1 i j) = (1 : Matrix (Fin n) (Fin n) _) i j := fun v hv i j => by
    rw [hll, LFixTh.kOff_at hg hv, one_ll]
  have hint : ∀ i j, IntS S (a.1 i j) := fun i j v hv => by rw [hll]; exact (LFixTh.kOff_int hg hv _ _).1
  have hint' : ∀ i j, IntS S ((a⁻¹).1 i j) := fun i j => by
    rw [hrr]
    exact IntS.cA (fun v hv => (LFixTh.kOff_int hg hv _ _).1)
  have hone : ∀ k j, IntS S ((1 : Mx D n n) k j) := fun k j v _ => by
    rw [map_one_entry]
    by_cases h : k = j
    · subst h; rw [Matrix.one_apply_eq]; exact one_mem _
    · rw [Matrix.one_apply_ne h]; exact zero_mem _
  have hoff : ∀ k j, OffS S (a.1 k j - (1 : Mx D n n) k j) := fun k j =>
    ⟨fun w => by rw [RingHom.map_sub, hinf, map_one_entry, sub_self],
      fun v hv => by rw [RingHom.map_sub, hat v hv, map_one_entry, sub_self],
      (hint k j).add (hone k j).neg⟩
  set u := Matrix.GeneralLinearGroup.det a with hudef
  have hu : (u : AE D) = a.1.det := Matrix.GeneralLinearGroup.val_det_apply a
  have hu' : ((u⁻¹ : (AE D)ˣ) : AE D) = (a⁻¹).1.det := by
    rw [hudef, ← map_inv]; exact Matrix.GeneralLinearGroup.val_det_apply _
  have hmap : ∀ {R : Type} [CommRing R] (f : AE D →+* R), (∀ i j, f (a.1 i j) = (1 : Matrix (Fin n) (Fin n) R) i j) →
      f a.1.det = 1 := by
    intro R _ f hf
    rw [RingHom.map_det]
    have : f.mapMatrix a.1 = 1 := by ext i j; exact hf i j
    rw [this, Matrix.det_one]
  obtain ⟨hχu, habs⟩ := hU u (fun w => by rw [hu]; exact hmap _ (hinf w)) (fun v hv => by rw [hu]; exact hmap _ (hat v hv))
    (fun v hv => ⟨by rw [hu, RingHom.map_det]; exact det_mem_intLoc fun i j => hint i j v hv,
      by rw [hu', RingHom.map_det]; exact det_mem_intLoc fun i j => hint' i j v hv⟩)
  have hxa : ∀ x : Mx D V.rank n, IntOff S (x * a.1) ↔ IntOff S x := by
    intro x
    rw [intOff_iff, intOff_iff]
    constructor
    · intro h i j
      have ex : x = (x * a.1) * (a⁻¹).1 := by
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      rw [ex]
      exact intS_mul h hint' i j
    · intro h i j
      exact intS_mul h hint i j
  have hexa : ∀ x : Mx D V.rank n, e • (x * a.1) = e • x := by
    intro x
    ext i j
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
    have : ∀ k, e * (x i k * a.1 k j) = e * (x i k * (1 : Mx D n n) k j) := by
      intro k
      have h0 := idem_mul_offS he (hoff k j)
      linear_combination (x i k) * h0
    simp_rw [this, ← Finset.mul_sum, ← Matrix.mul_apply, Matrix.mul_one]
  refine Subtype.ext (funext fun x => ?_)
  rw [hω.levi g a ha Ψ x]
  change (χ u : ℂ) * npow (absA D u) ((V.rank : ℂ) / 2) * Ψ.1 (x * a.1) = Ψ.1 x
  rw [hχu, habs]
  simp only [npow, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, Circle.coe_one, one_mul]
  rw [hΨ (x * a.1), hΨ x, hxa, hexa]

end PositivityTheory.Rg.Rsw.L.LFixW

end
