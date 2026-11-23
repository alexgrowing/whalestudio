import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAdelicVectorDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemBesselExchangeGroupIffRootExchangeStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootExch.Mirror

open GlobalTheory.BesselCompare (mt_mul mt_one hA_add hA_smul hA_smul_right hA_vec cA_inc hD_swap_zero)

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem suppAt_of_isK {ε a : AE D} {v y : Fin B.rank → AE D} {k : GA D B} (hk : IsK B v y k) (hy : a • y = y)
    (h1 : (ε + cA D ε) * a = a) (h2 : (ε + cA D ε) * cA D a = cA D a) : SuppAt ε B k := by
  rw [suppAt_iff_vec]
  intro x
  have e1 : (ε + cA D ε) * hA B x y = hA B x y := by
    rw [← hy, hA_smul_right, ← mul_assoc, h2]
  have e2 : (ε + cA D ε) • y = y := by
    conv_lhs => rw [← hy]
    rw [smul_smul, h1, hy]
  have e : (mt B k).mulVec x - x = hA B x y • v - hA B x v • y := by rw [hk x]; abel
  rw [e, smul_sub, smul_smul, e1, smul_comm, e2]

def fixGrp (B : HSp D) (x : Fin B.rank → AE D) : Subgroup (GA D B) where
  carrier := {g | (mt B g).mulVec x = x}
  one_mem' := by show _ = _; rw [mt_one, Matrix.one_mulVec]
  mul_mem' := fun {g h} hg hh => by
    show _ = _
    rw [mulVec_mul, show (mt B h).mulVec x = x from hh, show (mt B g).mulVec x = x from hg]
  inv_mem' := fun {g} hg => by
    show _ = _
    conv_lhs => rw [← show (mt B g).mulVec x = x from hg]
    rw [mulVec_inv_cancel]

theorem fix_of_isK (d : BesselDatum A B ι) {i l : Fin (d.ρ + 1)} (h : l ≠ i) {t} {g : GA D B}
    (hg : IsK B (vecA B (dual d i)) (iA ι t) g) : g ∈ fixGrp B (vecA B (d.aux l)) := by
  show _ = _
  rw [hg, hA_vec_iA (besselDatum_auxiliaryVector_orthogonal_image d l), hA_vec, (GlobalTheory.T.besselDatum_adelicVector_decomposition D A B ι d).1, if_neg h]
  simp

theorem fix_of_ExGe (d : BesselDatum A B ι) {ε : AE D} (he : IsSplitIdem D ε) {p : ℕ} {l : Fin (d.ρ + 1)} (h : l.1 < p)
    {g : GA D B} (hg : g ∈ ExGe d ε p) : g ∈ fixGrp B (vecA B (d.aux l)) := by
  refine (Subgroup.closure_le _).2 (Set.iUnion_subset fun i => Set.iUnion_subset fun hi u hu => ?_) hg
  obtain ⟨t, -, ht⟩ := (GlobalTheory.T.mem_besselExchangeGroup_iff_rootExchange D A B ι d ε he i u).1 (Subgroup.subset_closure hu)
  exact fix_of_isK d (fun e => by rw [e] at h; omega) ht

theorem basis_castSucc (d : BesselDatum A B ι) (l : Fin d.ρ) : d.aux l.castSucc = d.e l := by
  unfold BesselDatum.aux; rw [Fin.snoc_castSucc]

theorem hD_basis_e (d : BesselDatum A B ι) (m) (j : Fin d.ρ) : B.hD (d.aux m) (d.e j) = 0 := by
  unfold BesselDatum.aux
  refine Fin.lastCases ?_ (fun l => ?_) m
  · rw [Fin.snoc_last]; exact hD_swap_zero (d.ez j)
  · rw [Fin.snoc_castSucc]; exact d.ee l j

theorem hD_basis_succ_f (d : BesselDatum A B ι) (i : Fin d.ρ) : B.hD (d.aux i.succ) (d.f i) = 0 := by
  have key : ∀ m : Fin (d.ρ + 1), m.1 = i.1 + 1 → B.hD (d.aux m) (d.f i) = 0 := by
    intro m
    unfold BesselDatum.aux
    refine Fin.lastCases (fun _ => ?_) (fun l hl => ?_) m
    · rw [Fin.snoc_last]; exact hD_swap_zero (d.fz i)
    · rw [Fin.snoc_castSucc, d.ef, if_neg]
      rintro rfl
      simp at hl
  exact key _ rfl

theorem conj_apply {v y : Fin B.rank → AE D} {k c : GA D B} (hk : IsK B v y k) (hc : c ∈ fixGrp B v)
    {x : Fin B.rank → AE D} (hx : hA B x v = 0) :
    (mt B (c * k * c⁻¹)).mulVec x = x + hA B ((mt B c⁻¹).mulVec x) y • v := by
  have hc' : (mt B c).mulVec v = v := hc
  have h0 : hA B ((mt B c⁻¹).mulVec x) v = 0 := by rw [hA_mt_left, inv_inv, hc', hx]
  rw [mulVec_mul, mulVec_mul, hk, h0, zero_smul, sub_zero, Matrix.mulVec_add, Matrix.mulVec_smul, hc', mulVec_cancel_inv]

theorem sum_single (d : BesselDatum A B ι) (j : Fin d.ρ) (a : AE D) :
    ∑ l, (if l = j then a else 0) • vecA B (d.e l) = a • vecA B (d.e j) := by
  simp [ite_smul]

theorem mirror : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) (ε : AE D), IsSplitIdem D ε → ∀ (j : Fin d.ρ) (t₀ t : Fin A.rank → AE D) (b₀ k : GA D B), ε • t₀ = t₀ → cA D ε • t = t → IsK B (vecA B (dual d j.succ)) (iA ι t₀) b₀ → IsK B (vecA B (d.e j)) (iA ι t) k → SuppAt ε B k ∧ ∀ b ∈ ExGe d ε (j.1 + 2), b * (b₀ * k * b₀⁻¹) * b⁻¹ ∈ d.N ∧ SuppAt ε B (b * (b₀ * k * b₀⁻¹) * b⁻¹) ∧ d.psiN ψ (b * (b₀ * k * b₀⁻¹) * b⁻¹) = ψ (Algebra.trace (AF D.host.F) (AE D) (incA D d.θ * hA A t₀ t)) := by
  intro D A B ι d ψ ε he j t₀ t b₀ k ht₀ ht hb₀ hk
  have h1 : ε * ε = ε := he.1
  have h2 : ε * cA D ε = 0 := he.2.1
  have h3 : cA D ε * cA D ε = cA D ε := by rw [← RingHom.map_mul, h1]
  have a1 : (ε + cA D ε) * ε = ε := by rw [add_mul, h1, mul_comm, h2, add_zero]
  have a2 : (ε + cA D ε) * cA D ε = cA D ε := by rw [add_mul, h2, h3, zero_add]
  have sk : SuppAt ε B k := suppAt_of_isK (a := cA D ε) hk (by rw [← iA_smul, ht]) a2 (by rw [cA_cA, a1])
  have sb : SuppAt ε B b₀ := suppAt_of_isK (a := ε) hb₀ (by rw [← iA_smul, ht₀]) a1 a2
  refine ⟨sk, fun b hb => ?_⟩
  have sb' := suppAt_of_mem_ExGe hb
  have hn : b * (b₀ * k * b₀⁻¹) * b⁻¹ = (b * b₀) * k * (b * b₀)⁻¹ := by group
  have hfix : ∀ l : Fin d.ρ, l ≤ j → b * b₀ ∈ fixGrp B (vecA B (d.e l)) := by
    intro l hl
    have hl' : l.1 ≤ j.1 := hl
    rw [← basis_castSucc]
    refine mul_mem (fix_of_ExGe d he (by simp; omega) hb) (fix_of_isK d (fun e => ?_) hb₀)
    have := congrArg Fin.val e
    simp at this; omega
  have hact : ∀ x : B.V, B.hD x (d.e j) = 0 → actV B (b * (b₀ * k * b₀⁻¹) * b⁻¹) x =
      vecA B x + hA B ((mt B (b * b₀)⁻¹).mulVec (vecA B x)) (iA ι t) • vecA B (d.e j) := by
    intro x hx
    rw [hn]
    exact conj_apply hk (hfix j le_rfl) (by rw [hA_vec, hx, map_zero])
  refine ⟨Subgroup.subset_closure ⟨fun i => ?_, fun x hx => ?_⟩,
    suppAt_mul (suppAt_mul sb' (suppAt_mul (suppAt_mul sb sk) (suppAt_inv sb))) (suppAt_inv sb'), ?_⟩
  · refine ⟨_, fun l hl => ?_, by rw [hact _ (d.ee i j), ← sum_single]⟩
    split_ifs with h
    · subst h
      rw [show (mt B (b * b₀)⁻¹).mulVec (vecA B (d.e i)) = _ from inv_mem (hfix i hl), hA_vec_iA (d.eA i)]
    · rfl
  · exact ⟨_, by rw [hact _ (hx j), ← sum_single]⟩
  · unfold BesselDatum.psiN BesselDatum.simpleSum
    congr 3
    have e : ∀ i : Fin d.ρ, hA B (actV B (b * (b₀ * k * b₀⁻¹) * b⁻¹) (d.aux i.succ)) (vecA B (d.f i)) =
        if j = i then hA B ((mt B (b * b₀)⁻¹).mulVec (vecA B (d.aux i.succ))) (iA ι t) else 0 := by
      intro i
      rw [hact _ (hD_basis_e d _ j), hA_add, hA_smul, hA_vec, hA_vec, hD_basis_succ_f, d.ef]
      split_ifs <;> simp
    simp only [e, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hb' : (mt B b⁻¹).mulVec (vecA B (d.aux j.succ)) = vecA B (d.aux j.succ) :=
      inv_mem (fix_of_ExGe d he (by simp) hb)
    have p1 : hA B (iA ι t) (vecA B (dual d j.succ)) = 0 := by
      rw [← hA_herm, hA_vec_iA (dual_perp d _), map_zero]
    rw [_root_.mul_inv_rev, mulVec_mul, hb', hA_mt_left, inv_inv, hb₀, p1, zero_smul, sub_zero, hA_add_right,
      hA_vec_iA (besselDatum_auxiliaryVector_orthogonal_image d _), zero_add, hA_smul_right, hA_herm, hA_vec, (GlobalTheory.T.besselDatum_adelicVector_decomposition D A B ι d).1, if_pos rfl,
      map_one, mul_one, hA_iA d.isom]

end GlobalTheory.RootExch.Mirror

end
