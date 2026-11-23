import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.JacHom

variable {D : D7}

section Inv

variable {S T : HSp D}

theorem symplOH_mul_mt (a b : WO S T) (g : GA D S) :
    symplOH S T (a ⬝ mt S g) (b ⬝ mt S g) = symplOH S T a b := by
  have h1 : mt S g ⬝ mt S g⁻¹ = 1 := by rw [← mt_mul, mul_inv_cancel, mt_one]
  rw [mt_inv] at h1
  have key : mt S g ⬝ (giA S ⬝ adj (mt S g)) = giA S := by
    have e : mt S g ⬝ (giA S ⬝ adj (mt S g)) = mt S g ⬝ (giA S ⬝ (adj (mt S g) ⬝ gA S)) ⬝ giA S := by
      simp only [Matrix.mul_assoc, gA_mul_giA, Matrix.mul_one]
    rw [e, h1, Matrix.one_mul]
  rw [symplOH_eq, symplOH_eq, hO_eq_trace, hO_eq_trace, adj_mul]
  have e2 : giA S ⬝ (adj (mt S g) ⬝ adj b ⬝ (gA T ⬝ (a ⬝ mt S g))) =
      (giA S ⬝ adj (mt S g) ⬝ adj b ⬝ gA T ⬝ a) ⬝ mt S g := by simp only [Matrix.mul_assoc]
  have e3 : mt S g ⬝ (giA S ⬝ adj (mt S g) ⬝ adj b ⬝ gA T ⬝ a) =
      (mt S g ⬝ (giA S ⬝ adj (mt S g))) ⬝ (adj b ⬝ (gA T ⬝ a)) := by simp only [Matrix.mul_assoc]
  rw [e2, Matrix.trace_mul_comm, e3, key]

theorem symplOH_mul_mt_right (a b : WO S T) (g : GA D S) :
    symplOH S T a (b ⬝ mt S g) = symplOH S T (a ⬝ mt S g⁻¹) b := by
  conv_lhs => rw [← symplOH_mul_mt a (b ⬝ mt S g) g⁻¹]
  rw [Matrix.mul_assoc b, ← mt_mul, mul_inv_cancel, mt_one, Matrix.mul_one]

end Inv

section FinalTheorems

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x : Mx D T.rank ρ)

theorem extX_mul (n : GA D S) : d.extX T x ⬝ mt S n =
    d.extX T (d.extX T x ⬝ mt S n ⬝ d.jX) + d.ext0 T (ptS d T x n) + d.extY T (d.extX T x ⬝ mt S n ⬝ d.jY) := by
  rw [HypDec.extX_apply, HypDec.matrixExtendByZero_apply, HypDec.extY_apply, HypDec.extX_apply, ptS, HypDec.extX_apply]
  conv_lhs => rw [← Matrix.mul_one (x ⬝ d.pX ⬝ mt S n), ← d.sum_eq_one]
  simp only [Matrix.mul_add, Matrix.mul_assoc]

variable {T x}

theorem extX_mul_jX (hx : ∀ u ∈ UX D ρ, x ⬝ u.1 = x) {n : GA D S} (hn : n ∈ flagN d) :
    d.extX T x ⬝ mt S n ⬝ d.jX = x := by
  obtain ⟨M, b, hM, h1, -⟩ := exists_blocks d hn
  have htri : (1 + M).BlockTriangular id := fun i j (h : j < i) => by
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt h), hM i j (le_of_lt h), add_zero]
  have hdiag : ∀ i, (1 + M) i i = 1 := fun i => by rw [Matrix.add_apply, Matrix.one_apply_eq, hM i i le_rfl, add_zero]
  have hu : IsUnit (1 + M) := (Matrix.isUnit_iff_isUnit_det _).2 (by
    rw [Matrix.det_of_upperTriangular htri]; simp only [hdiag, Finset.prod_const_one]; exact isUnit_one)
  have hmem : hu.unit ∈ UX D ρ := fun i j => by
    refine ⟨fun h => ?_, ?_⟩
    · change (1 + M) i j = 0; exact htri h
    · change (1 + M) i i = 1; exact hdiag i
  have e : d.extX T x ⬝ mt S n ⬝ d.jX = x ⬝ (1 + M) := by
    rw [HypDec.extX_apply, Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_add, ← Matrix.mul_assoc d.pX, d.pX_jX,
      Matrix.one_mul]
  rw [e]
  exact hx _ hmem

end FinalTheorems

section Flag

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {T : HSp D} {x : Mx D T.rank ρ}
  (hx : ∀ u ∈ UX D ρ, x ⬝ u.1 = x)
include hx

theorem extX_mul_flag {n : GA D S} (hn : n ∈ flagN d) : d.extX T x ⬝ mt S n =
    d.extX T x + d.ext0 T (ptS d T x n) + d.extY T (d.extX T x ⬝ mt S n ⬝ d.jY) := by
  have h := extX_mul d T x n
  rwa [extX_mul_jX d hx hn] at h

theorem ptS_mul {n n' : GA D S} (hn : n ∈ flagN d) (hn' : n' ∈ flagN d) :
    ptS d T x (n * n') = ptS d T x n + ptS d T x n' := by
  obtain ⟨M, b, -, -, h2⟩ := exists_blocks d hn'
  have e : ptS d T x (n * n') = d.extX T x ⬝ mt S n ⬝ (mt S n' ⬝ d.j0) := by
    rw [ptS, mt_mul, Matrix.mul_assoc (d.extX T x), Matrix.mul_assoc (d.extX T x), Matrix.mul_assoc]
  rw [e, extX_mul_flag d hx hn, h2]
  have e' : ptS d T x n' = d.extX T x ⬝ (d.j0 + d.jX ⬝ b) := by rw [ptS, Matrix.mul_assoc, h2]
  rw [e']
  simp only [HypDec.extX_apply, HypDec.matrixExtendByZero_apply, HypDec.extY_apply, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc,
    d.pX_j0, d.p0_j0, d.pY_j0, d.p0_jX, d.pY_jX, cancel₂ d.p0_jX, cancel₂ d.pY_jX, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, add_zero, zero_add]

end Flag

section Flag2

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {T : HSp D} {x : Mx D T.rank ρ}

theorem symplOH_neg_left' {A B : HSp D} (a b : WO A B) : symplOH A B (-a) b = -symplOH A B a b := by
  rw [eq_neg_iff_add_eq_zero, ← GlobalTheory.OrientedHeis.symplOH_add_left, neg_add_cancel, symplOH_zero_left]

theorem ptS_one : ptS d T x 1 = 0 := by
  rw [ptS, mt_one, Matrix.mul_one, HypDec.extX_apply, Matrix.mul_assoc, d.pX_j0, Matrix.mul_zero]

variable (hx : ∀ u ∈ UX D ρ, x ⬝ u.1 = x)
include hx

theorem ptS_inv {n : GA D S} (hn : n ∈ flagN d) : ptS d T x n⁻¹ = -ptS d T x n := by
  have h := ptS_mul d hx (inv_mem hn) hn
  rw [inv_mul_cancel, ptS_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem cenS_flag {n : GA D S} (hn : n ∈ flagN d) :
    cenS d T x n = symplOH S T (d.extX T x) (d.extY T (d.extX T x ⬝ mt S n ⬝ d.jY)) := by
  conv_lhs => rw [cenS, extX_mul_flag d hx hn]
  rw [GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right,
    GlobalTheory.OrientedHeis.symplOH_self, HypDec.wittDecomp_sympl_extIsotropic_extAnisotropic, zero_add, zero_add]

theorem cenS_mul {n n' : GA D S} (hn : n ∈ flagN d) (hn' : n' ∈ flagN d) :
    cenS d T x (n * n') = cenS d T x n + cenS d T x n' + symplOH S₀ T (ptS d T x n) (ptS d T x n') := by
  have hi : n'⁻¹ ∈ flagN d := inv_mem hn'
  have h0 : symplOH S T (d.extX T x) (d.ext0 T (ptS d T x n) ⬝ mt S n') =
      symplOH S₀ T (ptS d T x n) (ptS d T x n') := by
    rw [symplOH_mul_mt_right, extX_mul_flag d hx hi, GlobalTheory.OrientedHeis.symplOH_add_left,
      GlobalTheory.OrientedHeis.symplOH_add_left, HypDec.wittDecomp_sympl_extIsotropic_extAnisotropic, HypDec.wittDecomp_sympl_extAnisotropic_extAnisotropic, HypDec.wittDecomp_sympl_extDual_extAnisotropic,
      ptS_inv d hx hn', symplOH_neg_left', symplOH_skew S₀ T (ptS d T x n), neg_neg, zero_add, add_zero]
  have hY : symplOH S T (d.extX T x) (d.extY T (d.extX T x ⬝ mt S n ⬝ d.jY) ⬝ mt S n') = cenS d T x n := by
    rw [symplOH_mul_mt_right, extX_mul_flag d hx hi, GlobalTheory.OrientedHeis.symplOH_add_left,
      GlobalTheory.OrientedHeis.symplOH_add_left, symplOH_skew S T (d.extY T _) (d.ext0 T _), HypDec.wittDecomp_sympl_extDual_extAnisotropic,
      HypDec.symplOH_extY_extY, neg_zero, add_zero, add_zero, cenS_flag d hx hn]
  have e : cenS d T x (n * n') = symplOH S T (d.extX T x) (d.extX T x ⬝ mt S n ⬝ mt S n') := by
    rw [cenS, mt_mul, Matrix.mul_assoc]
  rw [e, extX_mul_flag d hx hn, Matrix.add_mul, Matrix.add_mul, GlobalTheory.OrientedHeis.symplOH_add_right,
    GlobalTheory.OrientedHeis.symplOH_add_right, h0, hY, ← cenS]
  ring

variable (ψ : AddChar (AF D.host.F) ℂ)

theorem jacS_mul {n n' : GA D S} (hn : n ∈ flagN d) (hn' : n' ∈ flagN d) (f : WO S₀ T → ℂ) :
    jacS ψ d T x (n * n') f = jacS ψ d T x n (jacS ψ d T x n' f) := by
  funext w
  simp only [jacS, ptS_mul d hx hn hn', cenS_mul d hx hn hn', Pi.smul_apply, smul_eq_mul, heisO,
    GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, AddChar.map_add_eq_mul, add_assoc]
  ring

theorem jacS_mul_levi (n : GA D S) {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ) :
    jacS ψ d T x (n * d.levi u) = jacS ψ d T x n := by
  have hL : d.extX T x ⬝ mt S (d.levi u)⁻¹ = d.extX T x := by
    rw [← map_inv, HypDec.extX_levi, hx _ (inv_mem hu)]
  have hpt : ptS d T x (n * d.levi u) = ptS d T x n := by
    rw [ptS, ptS, mt_mul, ← Matrix.mul_assoc, Matrix.mul_assoc _ (mt S (d.levi u)), d.wittDecomp_levi_inclAnisotropic]
  have hcen : cenS d T x (n * d.levi u) = cenS d T x n := by
    rw [cenS, cenS, mt_mul, ← Matrix.mul_assoc, symplOH_mul_mt_right, hL]
  funext f
  simp only [jacS, hpt, hcen]

end Flag2

section Conj

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {T : HSp D} (x : Mx D T.rank ρ)

theorem witt_extension_hom_mul_embedded_anisotropic (g : GA D S₀) : d.extX T x ⬝ mt S (d.emb0 g) = d.extX T x := by
  rw [HypDec.extX_apply, Matrix.mul_assoc, d.wittDecomp_projX_anisotropicEmbedding]

theorem extX_conj (n : GA D S) (g : GA D S₀) :
    d.extX T x ⬝ mt S (d.emb0 g * n * (d.emb0 g)⁻¹) = d.extX T x ⬝ mt S n ⬝ mt S (d.emb0 g⁻¹) := by
  rw [← map_inv, mt_mul, mt_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, witt_extension_hom_mul_embedded_anisotropic]

theorem ptS_conj (n : GA D S) (g : GA D S₀) :
    ptS d T x (d.emb0 g * n * (d.emb0 g)⁻¹) = actO S₀ T g 1 (ptS d T x n) := by
  rw [ptS, ptS, extX_conj, actO_eq, mt_one, Matrix.one_mul, Matrix.mul_assoc (d.extX T x ⬝ mt S n), d.wittDecomp_anisotropicEmbedding_inclAnisotropic]
  exact (Matrix.mul_assoc _ _ _).symm

theorem cenS_conj (n : GA D S) (g : GA D S₀) :
    cenS d T x (d.emb0 g * n * (d.emb0 g)⁻¹) = cenS d T x n := by
  rw [cenS, cenS, extX_conj, symplOH_mul_mt_right, ← map_inv, inv_inv, witt_extension_hom_mul_embedded_anisotropic]

end Conj

theorem jacS_hom : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ)
    (x : Mx D T.rank ρ), (∀ u ∈ UX D ρ, x ⬝ u.1 = x) → (∀ b c, cenS d T x (d.nB b * d.nC c) = d.qS T c x) ∧
    (∀ n ∈ flagN d, ∀ n' ∈ flagN d, ptS d T x (n * n') = ptS d T x n + ptS d T x n' ∧
      cenS d T x (n * n') = cenS d T x n + cenS d T x n' + symplOH S₀ T (ptS d T x n) (ptS d T x n') ∧
      ∀ f, jacS ψ d T x (n * n') f = jacS ψ d T x n (jacS ψ d T x n' f)) ∧
    (∀ n ∈ flagN d, ∀ u ∈ UX D ρ, jacS ψ d T x (n * d.levi u) = jacS ψ d T x n) ∧
    ∀ n g, ptS d T x (d.emb0 g * n * (d.emb0 g)⁻¹) = actO S₀ T g 1 (ptS d T x n) ∧
      cenS d T x (d.emb0 g * n * (d.emb0 g)⁻¹) = cenS d T x n := by
  intro D ψ S S₀ T ρ d x hx
  refine ⟨fun b c => ?_, fun n hn n' hn' => ⟨ptS_mul d hx hn hn', cenS_mul d hx hn hn', jacS_mul d hx ψ hn hn'⟩,
    fun n _ u hu => jacS_mul_levi d hx ψ n hu, fun n g => ⟨ptS_conj d x n g, cenS_conj d x n g⟩⟩
  have hB : d.nB b ∈ flagN d := d.nB_mem_NFlag b
  have hC : d.nC c ∈ flagN d := d.nC_mem_NFlag c
  have hpC : ptS d T x (d.nC c) = 0 := by
    rw [ptS, Matrix.mul_assoc, d.nC_j0, HypDec.extX_apply, Matrix.mul_assoc, d.pX_j0, Matrix.mul_zero]
  have e : pairS T x (x ⬝ (half D • (b ⬝ plus S₀ b))) = half D * hO S₀ T (x ⬝ b) (x ⬝ b) := by
    rw [← pairS_plus]
    simp only [pairS, Matrix.mul_smul, adj_smul, cA_half, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  have h2 : symplOH S T (d.extX T x) (d.extY T (x ⬝ (half D • (b ⬝ plus S₀ b)))) = 0 := by
    refine eq_of_add_self (F := D.host.F) ?_
    rw [HypDec.symplOH_extX_extY, e, trHalf_half, ← symplOH_eq, GlobalTheory.OrientedHeis.symplOH_self, add_zero]
  have hcB : cenS d T x (d.nB b) = 0 := by
    have h1 : symplOH S T (d.extX T x) (d.extX T x ⬝ mt S (d.nB b)) +
        symplOH S T (d.extX T x) (d.extY T (x ⬝ (half D • (b ⬝ plus S₀ b)))) = 0 := by
      rw [← GlobalTheory.OrientedHeis.symplOH_add_right, HypDec.extX_nB, sub_add_cancel, GlobalTheory.OrientedHeis.symplOH_add_right,
        GlobalTheory.OrientedHeis.symplOH_self, HypDec.wittDecomp_sympl_extIsotropic_extAnisotropic, add_zero]
    rw [h2, add_zero] at h1
    exact h1
  rw [cenS_mul d hx hB hC, hcB, cenS_nC, hpC, symplOH_zero_right, zero_add, add_zero]

end GlobalTheory.JacHom

end
