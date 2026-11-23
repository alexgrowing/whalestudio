import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTorsionCharsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisChangeTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantPerturbationBoundStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SuccessiveMinimaPositiveNormsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousPolysTangentBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.HtGen.PointDet

attribute [local instance] Over.cartesianMonoidalCategory

theorem pairDet_eq_sum {C J : Type} [CommRing C] {g m k : ℕ} (h : J → Fin g → C) (a : Fin m → Fin g → C)
    (hk : k ≤ m) (σ : Fin k → J) :
    pairDet h a hk σ = ∑ s : Fin k → Fin g, (∏ i, h (σ i) (s i)) * minor a hk s := by
  classical
  have hM : (Matrix.of fun r l : Fin k => ∑ i, h (σ r) i * a (Fin.castLE hk l) i) =
      fun r => ∑ i, h (σ r) i • (fun l : Fin k => a (Fin.castLE hk l) i) := by
    ext r l; simp [Finset.sum_apply]
  unfold pairDet
  rw [hM]
  change Matrix.detRowAlternating.toMultilinearMap _ = _
  rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  congr 1
  unfold minor
  rw [← Matrix.det_transpose]
  rfl

theorem sum_extend {C : Type} [CommRing C] {m k : ℕ} (hk : k ≤ m) (cf : Fin k → C) (f : Fin m → C) :
    ∑ l', (fun l' : Fin m => if hl : (l' : ℕ) < k then cf ⟨l', hl⟩ else 0) l' * f l' =
      ∑ l : Fin k, cf l * f (Fin.castLE hk l) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ _ (fun l' hl' => ?_) (fun l => ?_)
  · have : ¬ (l' : ℕ) < k := fun hl => hl' ⟨⟨l', hl⟩, Fin.ext rfl⟩
    simp [this]
  · simp

theorem sum_comb_extend {C : Type} [CommRing C] {g m k : ℕ} (hk : k ≤ m) (cf : Fin k → C) (hh : Fin g → C)
    (a : Fin m → Fin g → C) :
    ∑ i, hh i * (∑ l', (fun l' : Fin m => if hl : (l' : ℕ) < k then cf ⟨l', hl⟩ else 0) l' • a l') i =
      ∑ l : Fin k, cf l * ∑ i, hh i * a (Fin.castLE hk l) i := by
  rw [← sum_extend hk cf (fun l' => ∑ i, hh i * a l' i)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l' _ => Finset.sum_congr rfl fun i _ => by ring

theorem pairDet_htLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (p : ℕ) [Fact p.Prime] (x : Sp ↥(intO ℂ_[p]) ⟶ X) (g g' : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)) (e' : Fin g' → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)), IsTanBasis t x e → IsTanBasis t x e' → ∀ (N : ℕ) (c : Fin N → TorsChar t x (p ^ 2)) (h : Fin N → Fin g → ↥(intO ℂ_[p])) (h' : Fin N → Fin g' → ↥(intO ℂ_[p])), (∀ c' : TorsChar t x (p ^ 2), ∃ j, Agree c' (c j)) → (∀ j, DlogIs t p 2 (c j) e (h j)) → (∀ j, DlogIs t p 2 (c j) e' (h' j)) → ∀ (m k : ℕ) (hk : k ≤ m) (u : Fin m → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (a : Fin m → Fin g → ℂ_[p]) (a' : Fin m → Fin g' → ℂ_[p]), LinearIndependent ℂ_[p] a → (∀ l, IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) (a l) (u l)) → (∀ l, IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e' i) (a' l) (u l)) → ∀ ν : ℝ, ν = ∏ l : Fin k, GlobalTheory.ShFam.Pad.grNorm t (spMap (intO ℂ_[p]).subtype ≫ x) (latHT t p (spMap (intO ℂ_[p]).subtype ≫ x)) u (Fin.castLE hk l) → (∀ l, 0 < GlobalTheory.ShFam.Pad.grNorm t (spMap (intO ℂ_[p]).subtype ≫ x) (latHT t p (spMap (intO ℂ_[p]).subtype ≫ x)) u l) ∧ (∀ σ : Fin k → Fin N, ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ‖ ≤ ν) ∧ (∃ σ : Fin k → Fin N, ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ‖ = ν) ∧ ∀ σ : Fin k → Fin N, ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ - pairDet (fun j i => (h' j i : ℂ_[p])) a' hk σ‖ < ν := by
  intro E _ _ _ H X _ t hX p _ x g g' e e' he he' N c h h' hall hdl hdl' m k hk u a a' ha hu hu' ν hν0
  set xC := spMap (intO ℂ_[p]).subtype ≫ x with hxC
  have heC := GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t (intO ℂ_[p]).subtype he
  have hlat := fun b w hw => GlobalTheory.T.tangent_basis_torsion_chars E H X t hX p x g e he N c h hall hdl b w hw
  have hut : ∀ l, IsTanAtG t xC (u l) := fun l => GlobalTheory.LineNorm.Chart.comb_tan heC.1 (hu l)
  have hgr := fun l => GlobalTheory.LineNorm.WedgeMax.grNorm_eq t heC.1
    (P := fun b => ∀ j, ‖∑ i, (h j i : ℂ_[p]) * b i‖ ≤ 1) (fun b w hw => (hlat b w hw).1) hu l
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hker : ∀ cc : Fin g → ℂ_[p], (∀ j, ∑ i, (h j i : ℂ_[p]) * cc i = 0) → cc = 0 := by
    intro cc hcc
    by_contra hne
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    have hi' : cc i ≠ 0 := by simpa using hi
    obtain ⟨y, hy⟩ := NormedField.exists_one_lt_norm ℂ_[p]
    obtain ⟨w, -, hw⟩ := GlobalTheory.LineNorm.WedgeMax.exists_comb t heC.1 ((y / ((p : ℂ_[p]) * cc i)) • cc)
    have hmem := (hlat _ w hw).1.2 fun j => by
      have : ∑ i', (h j i' : ℂ_[p]) * ((y / ((p : ℂ_[p]) * cc i)) • cc) i' =
          (y / ((p : ℂ_[p]) * cc i)) * ∑ i', (h j i' : ℂ_[p]) * cc i' := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
      rw [this, hcc j]; simp
    have h1 := (hlat _ w hw).2 hmem i
    have : (p : ℂ_[p]) * ((y / ((p : ℂ_[p]) * cc i)) • cc) i = y := by
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
      try ring
    rw [this] at h1
    linarith
  obtain ⟨hpos, hprod⟩ := GlobalTheory.T.successive_minima_positive_norms ℂ_[p] g (Fin N) (fun j i => (h j i : ℂ_[p])) hker m a ha _ hgr
  have hν : ν = ⨆ σ : Fin k → Fin N, ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ‖ := by
    rw [hν0, hprod k hk]
    congr 1
    ext σ
    rw [pairDet_eq_sum]
  have hνpos : 0 < ν := hν0 ▸ Finset.prod_pos fun l _ => hpos _
  have hne : Nonempty (Fin k → Fin N) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    rw [Real.iSup_of_isEmpty] at hν
    linarith
  have hle : ∀ σ : Fin k → Fin N, ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ‖ ≤ ν := fun σ =>
    hν ▸ le_ciSup (f := fun σ => ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ‖) (Finite.bddAbove_range _) σ
  have hex : ∃ σ : Fin k → Fin N, ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ‖ = ν := hν ▸ exists_eq_ciSup_of_finite
  refine ⟨hpos, hle, hex, fun σ => ?_⟩
  have hclose : ∀ cf : Fin k → ℂ_[p], (∀ j, ‖∑ l, cf l * ∑ i, (h j i : ℂ_[p]) * a (Fin.castLE hk l) i‖ ≤ 1) →
      ∀ j, ‖∑ l, cf l * ((∑ i, (h j i : ℂ_[p]) * a (Fin.castLE hk l) i) -
        ∑ i, (h' j i : ℂ_[p]) * a' (Fin.castLE hk l) i)‖ < 1 := by
    intro cf hcf j
    obtain ⟨w, -, hw⟩ := GlobalTheory.LineNorm.WedgeMax.exists_comb t hut
      (fun l' : Fin m => if hl : (l' : ℕ) < k then cf ⟨l', hl⟩ else 0)
    have hwe := GlobalTheory.LineNorm.Chart.comb_comb heC.1 hu hw
    have hwe' := GlobalTheory.LineNorm.Chart.comb_comb (GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t (intO ℂ_[p]).subtype he').1 hu' hw
    have hmem := (hlat _ w hwe).1.2 fun j' => by
      rw [sum_comb_extend]; exact hcf j'
    have h1 := GlobalTheory.T.tangent_basis_change_torsion E H X t hX p x g g' e e' he he' (c j) (h j) (h' j) (hdl j) (hdl' j) _ _ w hwe hwe' hmem
    rw [sum_comb_extend, sum_comb_extend, ← Finset.sum_sub_distrib] at h1
    simpa only [mul_sub] using h1
  exact GlobalTheory.T.determinant_perturbation_bound ℂ_[p] (Fin N) k (fun j l => ∑ i, (h j i : ℂ_[p]) * a (Fin.castLE hk l) i)
    (fun j l => ∑ i, (h' j i : ℂ_[p]) * a' (Fin.castLE hk l) i) ν hνpos hle hex hclose σ

end GlobalTheory.HtGen.PointDet
