import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTorsionCount

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.HtGen GlobalTheory.TrivFlag GlobalTheory.WholeFlag
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj
open scoped TensorProduct NNReal

namespace GlobalTheory.HalfGeo.PointClauses

attribute [local instance] Over.cartesianMonoidalCategory

theorem norm_sum_lt {K I : Type} [NormedField K] [IsUltrametricDist K] (s : Finset I) (f : I → K) {ν : ℝ} (hν : 0 < ν)
    (hf : ∀ i ∈ s, ‖f i‖ < ν) : ‖∑ i ∈ s, f i‖ < ν := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hν
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt (hf a (Finset.mem_insert_self _ _)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem det_comb_rows {C : Type} [CommRing C] {N k : ℕ} (n : Fin k → Fin N → C) (V : Fin N → Fin k → C) :
    (Matrix.of fun r l : Fin k => ∑ m, n r m * V m l).det =
      ∑ s : Fin k → Fin N, (∏ r, n r (s r)) * (Matrix.of fun r l : Fin k => V (s r) l).det := by
  classical
  have hM : (Matrix.of fun r l : Fin k => ∑ m, n r m * V m l) = fun r => ∑ m, n r m • V m := by
    ext r l; simp [Finset.sum_apply]
  rw [hM]
  change Matrix.detRowAlternating.toMultilinearMap _ = _
  rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

theorem val_comb {p : ℕ} [Fact p.Prime] {N g : ℕ} (n : Fin N → ℕ) (h : Fin N → Fin g → ↥(intO ℂ_[p])) (b : Fin g → ℂ_[p]) :
    ∑ i, ((∑ m, (n m : ↥(intO ℂ_[p])) * h m i : ↥(intO ℂ_[p])) : ℂ_[p]) * b i =
      ∑ m, (n m : ℂ_[p]) * ∑ i, (h m i : ℂ_[p]) * b i := by
  have h1 : ∀ i, ((∑ m, (n m : ↥(intO ℂ_[p])) * h m i : ↥(intO ℂ_[p])) : ℂ_[p]) = ∑ m, (n m : ℂ_[p]) * (h m i : ℂ_[p]) := by
    intro i
    push_cast
    rfl
  simp only [h1, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem mulVec_val {C : Type} [CommRing C] {N g m : ℕ} (h : Fin N → Fin g → C) (a : Fin m → Fin g → C) (y : Fin m → C)
    (r : Fin N) : (Matrix.of fun r l => ∑ i, h r i * a l i).mulVec y r = ∑ i, h r i * (∑ l, y l • a l) i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem prod_filter_lt {g k : ℕ} (hk : k ≤ g) (f : Fin g → ℝ) :
    ∏ l ∈ Finset.univ.filter (fun l : Fin g => (l : ℕ) < k), f l = ∏ l : Fin k, f (Fin.castLE hk l) := by
  symm
  refine Finset.prod_bij (fun l _ => Fin.castLE hk l) (fun l _ => by simp) (fun a _ b _ hab => Fin.castLE_injective hk hab)
    (fun b hb => ⟨⟨b, by simpa using hb⟩, Finset.mem_univ _, Fin.ext rfl⟩) (fun _ _ => rfl)

theorem ptSt_of_fullSt : FullSt → PtSt := by
  intro hfull E _ _ _ H X _ t hX p _ x n n' e e' he he' g c J h h' hgen hiso hdl hdl' u a a' ha hu hu'
  obtain ⟨N', c', nn, kk, hall, hkk, hD⟩ := hfull E H X t p x (g + g) c hgen
  have hH := hD n e h he.1 hdl
  have hH' := hD n' e' h' he'.1 hdl'
  have main := fun k hk => GlobalTheory.HtGen.PointDet.pairDet_htLattice E H X t hX p x n n' e e' he he' N' c' _ _ hall hH hH'
    g k hk u a a' ha hu hu' _ rfl
  have hlat := fun b w hw => GlobalTheory.T.tangent_basis_torsion_chars E H X t hX p x n e he N' c' _ hall hH b w hw
  set xC := spMap (intO ℂ_[p]).subtype ≫ x with hxC
  have heC := GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t (intO ℂ_[p]).subtype he
  have heC' := GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t (intO ℂ_[p]).subtype he'
  have hut : ∀ l, IsTanAtG t xC (u l) := fun l => GlobalTheory.LineNorm.Chart.comb_tan heC.1 (hu l)
  have hpos : ∀ k, 0 < wedgeNorm t xC u k := fun k => Finset.prod_pos fun l _ => (main 0 (Nat.zero_le _)).1 l
  have hw : ∀ k (hk : k ≤ g), wedgeNorm t xC u k =
      ∏ l : Fin k, GlobalTheory.ShFam.Pad.grNorm t xC (latHT t p xC) u (Fin.castLE hk l) := fun k hk => prod_filter_lt hk _
  have hpd : ∀ k (hk : k ≤ g) (σ : Fin k → Fin N'),
      pairDet (fun j i => ((∑ m, (nn j m : ↥(intO ℂ_[p])) * h m i : ↥(intO ℂ_[p])) : ℂ_[p])) a hk σ =
      (Matrix.of fun r l : Fin k => ∑ m, (nn (σ r) m : ℂ_[p]) * ∑ i, (h m i : ℂ_[p]) * a (Fin.castLE hk l) i).det := by
    intro k hk σ
    unfold pairDet
    congr 1
    ext r l
    exact val_comb _ _ _
  have hmin : ∀ k (hk : k ≤ g) (σ : Fin k → Fin (g + g)),
      minorAt (Matrix.of fun r l => ∑ i, (h r i : ℂ_[p]) * a l i) k hk σ =
      (Matrix.of fun r l : Fin k => ∑ i, (h (σ r) i : ℂ_[p]) * a (Fin.castLE hk l) i).det := fun _ _ _ => rfl
  have hle : ∀ k (hk : k ≤ g) (σ : Fin k → Fin (g + g)),
      ‖minorAt (Matrix.of fun r l => ∑ i, (h r i : ℂ_[p]) * a l i) k hk σ‖ ≤ wedgeNorm t xC u k := by
    intro k hk σ
    have h1 := (main k hk).2.1 (fun r => kk (σ r))
    rw [hpd, ← hw k hk] at h1
    rw [hmin]
    convert h1 using 3
    ext r l
    simp [hkk, Pi.single_apply]
  have hball : ∀ y : Fin g → ℂ_[p], (∀ r, ‖(Matrix.of fun r l => ∑ i, (h r i : ℂ_[p]) * a l i).mulVec y r‖ ≤ 1) →
      ∃ w, IsCombAtG t xC (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) (∑ l, y l • a l) w ∧
        IsCombAtG t xC (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e' i) (∑ l, y l • a' l) w ∧
        w ∈ latHT t p xC ∧ ∀ i, ‖(p : ℂ_[p]) * (∑ l, y l • a l) i‖ ≤ 1 := by
    intro y hy
    obtain ⟨w, -, hw⟩ := GlobalTheory.LineNorm.WedgeMax.exists_comb t hut y
    have hwe := GlobalTheory.LineNorm.Chart.comb_comb heC.1 hu hw
    have hwe' := GlobalTheory.LineNorm.Chart.comb_comb heC'.1 hu' hw
    have hmem := (hlat _ w hwe).1.2 fun j => by
      rw [val_comb]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun m _ => ?_
      rw [norm_mul, ← mulVec_val (fun r i => (h r i : ℂ_[p]))]
      exact mul_le_one₀ (IsUltrametricDist.norm_natCast_le_one _ _) (norm_nonneg _) (hy m)
    exact ⟨w, hwe, hwe', hmem, (hlat _ w hwe).2 hmem⟩
  refine ⟨hpos, hle, fun k hk => ?_, fun y y' hy hy' => ?_, fun y hy r => ?_⟩
  · obtain ⟨σ, hσ⟩ := (main k hk).2.2.1
    rw [hpd, ← hw k hk, det_comb_rows] at hσ
    by_contra hne
    refine (norm_sum_lt _ _ (hpos k) fun s _ => ?_).ne hσ
    have h1 : ‖minorAt (Matrix.of fun r l => ∑ i, (h r i : ℂ_[p]) * a l i) k hk s‖ < wedgeNorm t xC u k :=
      lt_of_le_of_ne (hle k hk s) fun h2 => hne ⟨s, h2⟩
    rw [hmin] at h1
    rw [norm_mul, ← Nat.cast_prod]
    exact (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)).trans_lt h1
  · obtain ⟨w, -, -, -, hp⟩ := hball y hy
    obtain ⟨w', -, -, -, hp'⟩ := hball y' hy'
    have h1 := hiso n e h he hdl _ _ hp hp'
      (fun m => by rw [← mulVec_val (fun r i => (h r i : ℂ_[p]))]; exact hy m)
      (fun m => by rw [← mulVec_val (fun r i => (h r i : ℂ_[p]))]; exact hy' m)
    simp only [← mulVec_val (fun r i => (h r i : ℂ_[p]))] at h1
    convert h1 using 2
    unfold dotProduct
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Matrix.mulVec.eq_1 (J.map _)]
    unfold dotProduct
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    simp only [Matrix.map_apply, eq_intCast]
    ring
  · obtain ⟨w, hwe, hwe', hmem, -⟩ := hball y hy
    have h1 := GlobalTheory.T.tangent_basis_change_torsion E H X t hX p x n n' e e' he he' (c r) (h r) (h' r) (hdl r) (hdl' r) _ _ w hwe hwe' hmem
    change ‖_‖ < 1
    rw [mulVec_val (fun r i => (h r i : ℂ_[p])), mulVec_val (fun r i => (h' r i : ℂ_[p])), norm_sub_rev]
    exact h1

end GlobalTheory.HalfGeo.PointClauses
