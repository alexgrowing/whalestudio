import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MixPer.Decomp

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem gram_mt (g : GA D S) {k l : ℕ} (X : Mx D S.rank k) (Y : Mx D S.rank l) :
    adj (mt S g ⬝ X) ⬝ (gA S ⬝ (mt S g ⬝ Y)) = adj X ⬝ (gA S ⬝ Y) := by
  rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) _ Y, ← Matrix.mul_assoc (adj (mt S g)),
    GlobalTheory.MixModel.mt_unitary]

theorem decomp {k : ℕ} (Z : Mx D S.rank k) :
    Z = d.jX ⬝ (d.pX ⬝ Z) + d.j0 ⬝ (d.p0 ⬝ Z) + d.jY ⬝ (d.pY ⬝ Z) := by
  conv_lhs => rw [← Matrix.one_mul Z, ← d.sum_eq_one]
  simp only [Matrix.add_mul, Matrix.mul_assoc]

theorem eq_nC {g : GA D S} (hX : mt S g ⬝ d.jX = d.jX) (h0 : mt S g ⬝ d.j0 = d.j0) :
    ∃ c : skewA D ρ, g = d.nC c := by
  have eY : d.pY ⬝ (mt S g ⬝ d.jY) = 1 := by
    rw [d.pY_eq, Matrix.mul_assoc, ← hX, gram_mt, d.gram_XY]
  have e0 : d.p0 ⬝ (mt S g ⬝ d.jY) = 0 := by
    rw [d.p0_eq, Matrix.mul_assoc, Matrix.mul_assoc, ← h0, gram_mt, d.gram_0Y, Matrix.mul_zero]
  have eM : mt S g ⬝ d.jY = d.jY + d.jX ⬝ (d.pX ⬝ (mt S g ⬝ d.jY)) := by
    conv_lhs => rw [decomp d (mt S g ⬝ d.jY)]
    rw [eY, e0, Matrix.mul_zero, add_zero, Matrix.mul_one, add_comm]
  generalize d.pX ⬝ (mt S g ⬝ d.jY) = c at eM
  have hs := gram_mt g d.jY d.jY
  rw [eM, d.gram_YY] at hs
  simp only [adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, d.gram_YY, d.gram_XY,
    cancel₃ d.gram_XX, cancel₃ d.gram_YX, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add] at hs
  have hc : adj c = -c := eq_neg_of_add_eq_zero_left hs
  refine ⟨⟨_, hc⟩, d.ga_ext ?_ ?_ ?_⟩
  · rw [hX, d.nC_jX]
  · rw [h0, d.nC_j0]
  · rw [eM, d.nC_jY]

theorem fix_of_eq {g n : GA D S} {k : ℕ} {X : Mx D S.rank k} (h : mt S g ⬝ X = mt S n ⬝ X) :
    mt S (g⁻¹ * n) ⬝ X = X := by
  rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, GlobalTheory.MixModel.mt_inv_mul, Matrix.one_mul]

theorem linInd : LinearIndependent D.host.E d.eᵀ := by
  refine Matrix.mulVec_injective_iff.1 fun x y h => ?_
  have := congrArg ((d.e'ᴴ * S.gram).mulVec) h
  simpa [Matrix.mulVec_mulVec, d.e'e] using this
end GlobalTheory.MixPer.Decomp

namespace GlobalTheory.MixPer.Decomp
variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem uc1 {m : ℕ} (u : GL (Fin ρ) (AE D)) (B : Mx D ρ m) : u.1 ⬝ ((u⁻¹).1 ⬝ B) = B := by
  rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem exists_unit {T : Mx D ρ ρ} (hT : GlobalTheory.BesselChar.StrictUp T) : ∃ u ∈ UX D ρ, u.1 = 1 + T := by
  have hU : (1 + T).BlockTriangular id := Matrix.blockTriangular_one.add hT.tri
  have hdet : (1 + T).det = 1 := by
    rw [Matrix.det_of_upperTriangular hU]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [Matrix.add_apply, hT i i le_rfl]; simp
  obtain ⟨u, hu1⟩ : ∃ u : GL (Fin ρ) (AE D), u.1 = 1 + T :=
    ⟨Matrix.nonsingInvUnit (1 + T) (by rw [hdet]; exact isUnit_one), rfl⟩
  refine ⟨u, (GlobalTheory.UniIndexPrime.mem_uniSub u).2 ⟨fun i j h => ?_, fun i => ?_⟩, hu1⟩
  · rw [hu1, Matrix.add_apply, Matrix.one_apply_ne h.ne', hT i j h.le, add_zero]
  · rw [hu1, Matrix.add_apply, Matrix.one_apply_eq, hT i i le_rfl, add_zero]

theorem exists_B {n : GA D S}
    (h2 : ∀ y, (GlobalTheory.BesselChar.perpMat S d.e).map (incA D) *ᵥ y = 0 →
      ∃ a, mt S n *ᵥ y = y + d.e.map (incA D) *ᵥ a) :
    ∃ B : Mx D ρ S₀.rank, mt S n ⬝ d.j0 = d.j0 + d.jX ⬝ B := by
  have hz : ∀ k : Fin S₀.rank, ∃ a : Fin ρ → AE D,
      mt S n *ᵥ (fun i => d.j0 i k) = (fun i => d.j0 i k) + d.jX *ᵥ a := fun k => h2 _ (by
    change d.pY *ᵥ (fun i => d.j0 i k) = 0
    funext r
    have := congrFun (congrFun d.pY_j0 r) k
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this)
  choose a ha using hz
  refine ⟨Matrix.of (fun i k => a k i), ?_⟩
  ext i k
  have := congrFun (ha k) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

theorem k1t (n : GA D S) (u : GL (Fin ρ) (AE D)) (T : Mx D ρ ρ) (hu1 : u.1 = 1 + T)
    (h1 : mt S n ⬝ d.jX = d.jX + d.jX ⬝ T) (B : Mx D ρ S₀.rank) :
    mt S (d.levi u * d.nB ((u⁻¹).1 ⬝ B)) ⬝ d.jX = mt S n ⬝ d.jX := by
  rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, d.nB_jX, d.levi_jX, h1, hu1, Matrix.mul_add, Matrix.mul_one]

theorem k2t (n : GA D S) (u : GL (Fin ρ) (AE D)) (B : Mx D ρ S₀.rank) (hB : mt S n ⬝ d.j0 = d.j0 + d.jX ⬝ B) :
    mt S (d.levi u * d.nB ((u⁻¹).1 ⬝ B)) ⬝ d.j0 = mt S n ⬝ d.j0 := by
  rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, d.nB_j0, hB, Matrix.mul_add, d.wittDecomp_levi_inclAnisotropic, cancel₂ (d.levi_jX u),
      Matrix.mul_assoc d.jX, uc1]

theorem flag_decomp {n : GA D S} (hn : n ∈ flagN d) :
    ∃ u ∈ UX D ρ, ∃ b c, n = d.levi u * (d.nB b * d.nC c) := by
  obtain ⟨⟨T, hT, h1⟩, h2⟩ := (GlobalTheory.BesselChar.mem_NFlag_iff S d.e (linInd d) n).1 hn
  obtain ⟨u, hu, hu1⟩ := exists_unit hT
  obtain ⟨B, hB⟩ := exists_B d h2
  have f1 := fix_of_eq (k1t d n u T hu1 h1 B)
  have f2 := fix_of_eq (k2t d n u B hB)
  refine (eq_nC d f1 f2).elim fun c hc => ⟨u, hu, (u⁻¹).1 ⬝ B, c, ?_⟩
  exact ((mul_inv_cancel_left (d.levi u * d.nB ((u⁻¹).1 ⬝ B)) n).symm.trans
    (congrArg ((d.levi u * d.nB ((u⁻¹).1 ⬝ B)) * ·) hc)).trans (mul_assoc _ _ _)
theorem mt_flag_jX (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    mt S (d.levi u * (d.nB b * d.nC c)) ⬝ d.jX = d.jX ⬝ u.1 := by
  simp only [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, d.nC_jX, d.nB_jX, d.levi_jX]

theorem flag_unipotent_product_anisotropic_action (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    mt S (d.levi u * (d.nB b * d.nC c)) ⬝ d.j0 = d.j0 + d.jX ⬝ (u.1 ⬝ b) := by
  simp only [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, d.nC_j0, d.nB_j0, Matrix.mul_add, d.wittDecomp_levi_inclAnisotropic,
    cancel₂ (d.levi_jX u)]

theorem witt_anisotropic_projection_flag_unipotent_inclusion {n : GA D S} (hn : n ∈ flagN d) {k : ℕ} (X : Mx D S₀.rank k) :
    d.p0 ⬝ (mt S n ⬝ (d.j0 ⬝ X)) = X := by
  obtain ⟨u, -, b, c, rfl⟩ := flag_decomp d hn
  rw [← Matrix.mul_assoc (mt S _), flag_unipotent_product_anisotropic_action, ← Matrix.mul_assoc, Matrix.mul_add, d.p0_j0, cancel₂ d.p0_jX,
    Matrix.zero_mul, add_zero, Matrix.one_mul]

theorem conj_mem {n : GA D S} (hn : n ∈ flagN d) (h : GA D S₀) : d.emb0 h * n * (d.emb0 h)⁻¹ ∈ flagN d := by
  obtain ⟨u, hu, b, c, rfl⟩ := flag_decomp d hn
  have e : d.emb0 h * (d.levi u * (d.nB b * d.nC c)) =
      d.levi u * (d.nB (b ⬝ mt S₀ h⁻¹) * d.nC c) * d.emb0 h := by
    rw [← mul_assoc, d.wittHyperbolic_anisotropic_commute_levi, mul_assoc, ← mul_assoc (d.emb0 h), d.wittHyperbolic_anisotropic_conj_nB, mul_assoc, d.wittHyperbolic_anisotropic_commute_nC]
    simp only [mul_assoc]
  rw [e, mul_inv_cancel_right]
  exact mul_mem (d.levi_mem_NFlag hu) (mul_mem (d.nB_mem_NFlag _) (d.nC_mem_NFlag c))

end GlobalTheory.MixPer.Decomp

namespace GlobalTheory.MixPer.Decomp
variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem mem_flag_iff {n : GA D S} : n ∈ flagN d ↔ ∃ u ∈ UX D ρ, ∃ b c, n = d.levi u * (d.nB b * d.nC c) := by
  refine ⟨flag_decomp d, ?_⟩
  rintro ⟨u, hu, b, c, rfl⟩
  exact mul_mem (d.levi_mem_NFlag hu) (mul_mem (d.nB_mem_NFlag b) (d.nC_mem_NFlag c))

theorem mem_radX_iff {n : GA D S} : n ∈ radX d ↔ ∃ b c, n = d.nB b * d.nC c := by
  change n ∈ flagN d ⊓ fixer S d.jX ↔ _
  constructor
  · intro hn
    obtain ⟨hf, hx⟩ := Subgroup.mem_inf.1 hn
    obtain ⟨u, -, b, c, rfl⟩ := flag_decomp d hf
    have hx' : mt S (d.levi u * (d.nB b * d.nC c)) ⬝ d.jX = d.jX := hx
    rw [mt_flag_jX] at hx'
    have e : u.1 = 1 := by
      have := cancel₂ d.pX_jX u.1
      rw [hx', d.pX_jX, Matrix.one_mul] at this
      exact this.symm
    have : u = 1 := Units.ext e
    subst this
    exact ⟨b, c, by rw [map_one, one_mul]⟩
  · rintro ⟨b, c, rfl⟩
    refine Subgroup.mem_inf.2 ⟨mul_mem (d.nB_mem_NFlag b) (d.nC_mem_NFlag c), ?_⟩
    show mt S (d.nB b * d.nC c) ⬝ d.jX = d.jX
    rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, d.nC_jX, d.nB_jX]

theorem stab_split {g : GA D S} (hg : mt S g ⬝ d.jX = d.jX) :
    ∃ (B : Mx D ρ S₀.rank) (h : GA D S₀), mt S g ⬝ d.j0 = d.jX ⬝ B + d.j0 ⬝ mt S₀ h := by
  have jointCmpEmbeddingY : d.pY ⬝ (mt S g ⬝ d.j0) = 0 := by
    rw [d.pY_eq, Matrix.mul_assoc, ← hg, gram_mt, d.wittDecomp_gram_X_anisotropic]
  have eM : mt S g ⬝ d.j0 = d.jX ⬝ (d.pX ⬝ (mt S g ⬝ d.j0)) + d.j0 ⬝ (d.p0 ⬝ (mt S g ⬝ d.j0)) := by
    conv_lhs => rw [decomp d (mt S g ⬝ d.j0)]
    rw [jointCmpEmbeddingY, Matrix.mul_zero, add_zero]
  generalize d.pX ⬝ (mt S g ⬝ d.j0) = B at eM
  generalize d.p0 ⬝ (mt S g ⬝ d.j0) = Q at eM
  have hs := gram_mt g d.j0 d.j0
  rw [eM, d.gram_00] at hs
  simp only [adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, cancel₃ d.gram_XX,
    cancel₃ d.wittDecomp_gram_X_anisotropic, cancel₃ d.gram_0X, cancel₃ d.gram_00, Matrix.zero_mul, Matrix.mul_zero, add_zero,
    zero_add] at hs
  exact ⟨B, GlobalTheory.MixModel.ofMat S₀ Q hs, eM⟩

theorem mem_stabX_iff {g : GA D S} : g ∈ stabX d ↔ ∃ n ∈ radX d, ∃ h, g = n * d.emb0 h := by
  constructor
  · intro hg
    have hg' : mt S g ⬝ d.jX = d.jX := hg
    obtain ⟨B, h, eM⟩ := stab_split d hg'
    have hX : mt S (g * (d.emb0 h)⁻¹) ⬝ d.jX = d.jX := by
      rw [← map_inv, GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, hg']
    have h0 : mt S (g * (d.emb0 h)⁻¹) ⬝ d.j0 = d.j0 + d.jX ⬝ (B ⬝ mt S₀ h⁻¹) := by
      rw [← map_inv, GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc, eM, Matrix.add_mul,
        Matrix.mul_assoc, Matrix.mul_assoc d.j0, GlobalTheory.MixModel.mt_mul_inv, Matrix.mul_one, add_comm]
    refine ⟨g * (d.emb0 h)⁻¹, Subgroup.mem_inf.2 ⟨d.mem_NFlag HypDec.one_mem_upperUni ?_ h0, hX⟩, h,
      (inv_mul_cancel_right g _).symm⟩
    rw [hX, Units.val_one, Matrix.mul_one]
  · rintro ⟨n, hn, h, rfl⟩
    show mt S (n * d.emb0 h) ⬝ d.jX = d.jX
    rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX]
    exact (Subgroup.mem_inf.1 hn).2

theorem mem_jacGrp_iff {g : GA D S} : g ∈ jacGrp d ↔ ∃ n ∈ flagN d, ∃ h, g = n * d.emb0 h := by
  constructor
  · intro hg
    let K : Subgroup (GA D S) :=
      { carrier := {g | ∃ n ∈ flagN d, ∃ h, g = n * d.emb0 h}
        one_mem' := ⟨1, one_mem _, 1, by rw [map_one, one_mul]⟩
        mul_mem' := by
          rintro _ _ ⟨n, hn, h, rfl⟩ ⟨n', hn', h', rfl⟩
          exact ⟨n * (d.emb0 h * n' * (d.emb0 h)⁻¹), mul_mem hn (conj_mem d hn' h), h * h', by
            rw [map_mul]; group⟩
        inv_mem' := by
          rintro _ ⟨n, hn, h, rfl⟩
          exact ⟨d.emb0 h⁻¹ * n⁻¹ * (d.emb0 h⁻¹)⁻¹, conj_mem d (inv_mem hn) h⁻¹, h⁻¹, by
            rw [map_inv]; group⟩ }
    have hle : jacGrp d ≤ K := sup_le (fun n hn => ⟨n, hn, 1, by rw [map_one, mul_one]⟩)
      (by rintro _ ⟨h, rfl⟩; exact ⟨1, one_mem _, h, (one_mul _).symm⟩)
    exact hle hg
  · rintro ⟨n, hn, h, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)

theorem flag_unipotent_mul_embedded_anisotropic_unique {n n' : GA D S} (hn : n ∈ flagN d) (hn' : n' ∈ flagN d) {h h' : GA D S₀}
    (e : n * d.emb0 h = n' * d.emb0 h') : n = n' ∧ h = h' := by
  have e1 := congrArg (fun g => d.p0 ⬝ (mt S g ⬝ d.j0)) e
  simp only [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic] at e1
  rw [witt_anisotropic_projection_flag_unipotent_inclusion d hn, witt_anisotropic_projection_flag_unipotent_inclusion d hn'] at e1
  have hh : h = h' := GlobalTheory.MixModel.mt_injective S₀ e1
  subst hh
  exact ⟨mul_right_cancel e, rfl⟩

theorem unique_levi {u u' : GL (Fin ρ) (AE D)} {b b' : Mx D ρ S₀.rank} {c c' : skewA D ρ}
    (e : d.levi u * (d.nB b * d.nC c) = d.levi u' * (d.nB b' * d.nC c')) : u = u' ∧ b = b' ∧ c = c' := by
  have e1 := congrArg (fun g => d.pX ⬝ (mt S g ⬝ d.jX)) e
  simp only [mt_flag_jX] at e1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul, Matrix.one_mul] at e1
  have hu : u = u' := Units.ext e1
  subst hu
  have e' := mul_left_cancel e
  have e2 := congrArg (fun g => d.pX ⬝ (mt S g ⬝ d.j0)) e'
  simp only [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, d.nC_j0, d.nB_j0, Matrix.mul_add, d.pX_j0, cancel₂ d.pX_jX,
    Matrix.one_mul, zero_add] at e2
  subst e2
  have e'' := mul_left_cancel e'
  have e3 := congrArg (fun g => d.pX ⬝ (mt S g ⬝ d.jY)) e''
  simp only [d.nC_jY, Matrix.mul_add, d.pX_jY, cancel₂ d.pX_jX, Matrix.one_mul, zero_add] at e3
  exact ⟨rfl, rfl, Subtype.ext e3⟩

end GlobalTheory.MixPer.Decomp

namespace GlobalTheory.MixPer

theorem flag_jacobi_structure : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ),
    (∀ n, n ∈ flagN d ↔ ∃ u ∈ UX D ρ, ∃ b c, n = d.levi u * (d.nB b * d.nC c)) ∧
    (∀ n, n ∈ radX d ↔ ∃ b c, n = d.nB b * d.nC c) ∧
    (∀ g, g ∈ stabX d ↔ ∃ n ∈ radX d, ∃ h, g = n * d.emb0 h) ∧
    (∀ g, g ∈ jacGrp d ↔ ∃ n ∈ flagN d, ∃ h, g = n * d.emb0 h) ∧
    (∀ n ∈ flagN d, ∀ h, d.emb0 h * n * (d.emb0 h)⁻¹ ∈ flagN d) ∧
    (∀ n ∈ flagN d, ∀ n' ∈ flagN d, ∀ h h', n * d.emb0 h = n' * d.emb0 h' → n = n' ∧ h = h') ∧
    ∀ u b c u' b' c', d.levi u * (d.nB b * d.nC c) = d.levi u' * (d.nB b' * d.nC c') → u = u' ∧ b = b' ∧ c = c' :=
  fun _ _ _ _ d => ⟨fun _ => Decomp.mem_flag_iff d, fun _ => Decomp.mem_radX_iff d, fun _ => Decomp.mem_stabX_iff d,
    fun _ => Decomp.mem_jacGrp_iff d, fun _ hn h => Decomp.conj_mem d hn h,
    fun _ hn _ hn' _ _ e => Decomp.flag_unipotent_mul_embedded_anisotropic_unique d hn hn' e, fun _ _ _ _ _ _ e => Decomp.unique_levi d e⟩

end GlobalTheory.MixPer
