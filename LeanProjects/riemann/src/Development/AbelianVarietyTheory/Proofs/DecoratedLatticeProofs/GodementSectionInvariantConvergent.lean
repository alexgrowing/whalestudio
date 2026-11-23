import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizerInductionLaw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SummableOfCount

noncomputable section

open scoped NNReal TensorProduct
open NumberField Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.Eis.Conv GlobalTheory.MixModel GlobalTheory.RegSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GodementSectionReduction

open Formalism.UG (bc)

theorem grp_cover {G : Type} [Group G] {c₀ b₀ B C L e c₁ c₂ y a y' c w w' : G} (h1 : b₀ * B = e * c₁)
    (h2 : c₀ * e = e * c₀) (h3 : c₀ * (c₁ * C) = c₂ * (y' * c)) (h4 : y * a = e * c₂) (h5 : y' * a = a * y')
    (h6 : L * w = a * L) (h7 : L * w' = c * L) : c₀ * b₀ * (B * C * L) = y * y' * L * (w * w') :=
  calc _ = c₀ * (b₀ * B) * C * L := by simp only [mul_assoc]
    _ = e * (c₀ * (c₁ * C)) * L := by rw [h1, ← mul_assoc, h2]; simp only [mul_assoc]
    _ = y * (a * y') * (c * L) := by rw [h3, ← mul_assoc, ← h4]; simp only [mul_assoc]
    _ = y * y' * (a * L) * w' := by rw [← h5, ← h7]; simp only [mul_assoc]
    _ = _ := by rw [← h6]; simp only [mul_assoc]

theorem grp_reduce {G : Type} [Group G] {p u g B B' B'' C C' g' L κ a c : G} (e : p = B * C * g' * L)
    (h1 : g * B = B' * g) (h2 : u * B' = B'' * u) (h3 : g * C = C * g) (h4 : u * C = C' * u) (h5 : g * g' = κ)
    (h6 : κ * L = L * κ) (h7 : u * L = a * c) : u * g * p = B'' * C' * a * (c * κ) :=
  calc _ = u * (g * B) * C * g' * L := by rw [e]; simp only [mul_assoc]
    _ = (u * B') * (g * C) * g' * L := by rw [h1]; simp only [mul_assoc]
    _ = B'' * (u * C) * ((g * g') * L) := by rw [h2, h3]; simp only [mul_assoc]
    _ = B'' * C' * (u * L) * κ := by rw [h4, h5, h6]; simp only [mul_assoc]
    _ = _ := by rw [h7]; simp only [mul_assoc]

theorem add_rearr {A : Type} [AddCommGroup A] {z z' c z'' : A} (e : z - z' = c + z'') : -c + z = z' + z'' := by
  rw [sub_eq_iff_eq_add.1 e]; abel

theorem row_ne_zero {A : Type} [CommRing A] [Nontrivial A] {r n : ℕ} {M : Matrix (Fin r) (Fin n) A}
    {N : Matrix (Fin n) (Fin r) A} (h : M * N = 1) (i : Fin r) : ¬∀ x, M i x = 0 := fun h2 => by
  have h5 := congrFun (congrFun h i) i
  rw [Matrix.mul_apply, one_apply_eq, Finset.sum_eq_zero fun x _ => by rw [h2, zero_mul]] at h5
  exact zero_ne_one h5

variable {D : D7} {T T₀ : HSp D} {r : ℕ}

variable (d : HypDec T T₀ r)

theorem nB_mem (b : Mx D r T₀.rank) : d.nB b ∈ stab d := ⟨1, by rw [d.nB_jX, Units.val_one, Matrix.mul_one]⟩

theorem nC_mem (c : skewA D r) : d.nC c ∈ stab d := ⟨1, by rw [d.nC_jX, Units.val_one, Matrix.mul_one]⟩

theorem wittCoreEmbedding_mem_isotropicStabilizer (g : GA D T₀) : d.emb0 g ∈ stab d := ⟨1, by rw [d.wittDecomp_anisotropicEmbedding_inclX, Units.val_one, Matrix.mul_one]⟩

theorem cover_rad : ∃ (W : Set (GA D T)) (C : ℝ), IsCompact W ∧ ∀ m : Fin r → ℕ, ∃ Y : Finset (GA D T),
    (Y.card : ℝ) ≤ C * ∏ i, bs D ^ ((T₀.rank + r) * m i) ∧ ∀ b c, ∃ γ ∈ stab d ⊓ GQ T, ∃ y ∈ Y, ∃ w ∈ W,
      γ * (d.nB b * d.nC c * d.levi (dg (hf D) fun i => (m i : ℤ))) = y * d.levi (dg (hf D) fun i => (m i : ℤ)) * w := by
  classical
  obtain ⟨K, C, hK, h⟩ := cover_rect D r T₀.rank
  obtain ⟨K', C', hK', h'⟩ := cover_skewA D r
  refine ⟨_, C * C', (hK.prod hK').image ((d.continuous_nB.comp continuous_fst).mul (d.continuous_nC.comp continuous_snd)),
    fun m => ?_⟩
  obtain ⟨Y, hY, h⟩ := h m
  obtain ⟨Y', hY', h'⟩ := h' m
  refine ⟨(Y ×ˢ Y').image fun y => d.nB y.1 * d.nC y.2, ?_, fun b c => ?_⟩
  · refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
    rw [Finset.card_product, Nat.cast_mul]
    refine (mul_le_mul hY hY' (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans hY)).trans (le_of_eq ?_)
    simp only [add_mul, pow_add, Finset.prod_mul_distrib]
    ring
  · generalize (dg (hf D) fun i => (m i : ℤ)) = a at *
    obtain ⟨b₀, hb₀, y, hy, ω, hω, e⟩ := h b
    obtain ⟨c₀, hc₀, y', hy', ω', hω', e'⟩ := h' (cComm T₀ (-b₀) b + c - cComm T₀ y (a.1 ⬝ ω))
    refine ⟨d.nC (-c₀) * d.nB (-b₀), mul_mem ⟨nC_mem d _, d.nC_mem_GQ (neg_mem hc₀)⟩ ⟨nB_mem d _, d.nB_mem_GQ (neg_mem hb₀)⟩,
      _, Finset.mem_image.mpr ⟨(y, y'), Finset.mem_product.2 ⟨hy, hy'⟩, rfl⟩, _, ⟨(ω, ω'), ⟨hω, hω'⟩, rfl⟩, ?_⟩
    have h1 := d.nB_mul_nB (-b₀) b
    rw [show -b₀ + b = y + a.1 ⬝ ω from neg_add_eq_iff_eq_add.2 e] at h1
    have h2 : -c₀ + (cComm T₀ (-b₀) b + c) = cComm T₀ y (a.1 ⬝ ω) + (y' + skewConj a.1 ω') := add_rearr e'
    have h3 := congrArg d.nC h2
    rw [d.nC_add, d.nC_add, d.nC_add, d.nC_add] at h3
    exact grp_cover h1 (d.nC_mul_nB _ _) h3 (d.nB_mul_nB _ _) (d.nC_mul_nB _ _) (d.levi_mul_nB _ _) (d.levi_mul_nC _ _)

theorem exists_decomp (p : stab d) : ∃ b c g, (p : GA D T) = d.nB b * d.nC c * d.emb0 g * d.levi (onX d p) := by
  have h : (p : GA D T) * d.levi (onX d p)⁻¹ ∈ MixPer.stabX d := by
    show mt T (p * d.levi (onX d p)⁻¹) ⬝ d.jX = d.jX
    rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, d.levi_jX, cancel₂ (mul_jX d p), Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
  obtain ⟨n, hn, g, e⟩ := (MixPer.Decomp.mem_stabX_iff d).1 h
  obtain ⟨b, c, rfl⟩ := (MixPer.Decomp.mem_radX_iff d).1 hn
  exact ⟨b, c, g, by rw [← e, map_inv, inv_mul_cancel_right]⟩

theorem reduction_GL_diagonalUnitPowers_compact {E A : Type} [Field E] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    (j : E →+* A) {s : Aˣ} {ν : Aˣ →* ℝ≥0} (hν : Continuous ν) (hj : ∀ u : Eˣ, ν (Units.map j.toMonoidHom u) = 1)
    {b : ℝ} (hb : 0 < b) (hs : (ν s : ℝ) = b⁻¹) {r : ℕ}
    (hR : ∃ Ω : Set A, IsCompact Ω ∧ ∀ β : GL (Fin r) A, ∃ (δ : GL (Fin r) E) (l : Fin r → ℤ) (c : GL (Fin r) A),
      (∀ i k, c.1 i k ∈ Ω ∧ c⁻¹.1 i k ∈ Ω) ∧ δ.1.map j * β.1 = diagonal (fun i => (s ^ l i).1) * c.1) :
    ∃ (L : Set (GL (Fin r) A)) (C : ℝ), IsCompact L ∧ ∀ α : GL (Fin r) A,
    ∃ (δ : GL (Fin r) E) (l : Fin r → ℤ), ∃ c ∈ L, bc j δ * α = dg s l * c ∧
      (ν (GeneralLinearGroup.det α) : ℝ) ≤ C * ∏ i, (b ^ l i)⁻¹ := by
  obtain ⟨Ω, hΩ, hR⟩ := hR
  choose δ l c hcΩ hred using hR
  replace hred : ∀ β, bc j (δ β) * β = dg s (l β) * c β := fun β => Units.ext (hred β)
  obtain ⟨L, hL, hcL⟩ : Bdd c :=
    bdd_units (bdd_matrix hΩ fun q i k => (hcΩ q i k).1) (bdd_matrix hΩ fun q i k => (hcΩ q i k).2)
  have hdet : Continuous (GeneralLinearGroup.det : GL (Fin r) A → Aˣ) := Units.continuous_iff.2
    ⟨Units.continuous_val.matrix_det, Units.continuous_coe_inv.matrix_det⟩
  obtain ⟨B, hB⟩ := (hL.image (NNReal.continuous_coe.comp (hν.comp hdet))).bddAbove
  refine ⟨L, B, hL, fun α => ⟨δ α, l α, c α, hcL α, hred α, ?_⟩⟩
  have h1 : GeneralLinearGroup.det (bc j (δ α)) = Units.map j.toMonoidHom (GeneralLinearGroup.det (δ α)) :=
    Units.ext (j.map_det (δ α).1).symm
  have h3 := congrArg (fun x => (ν (GeneralLinearGroup.det x) : ℝ)) (hred α)
  beta_reduce at h3
  rw [map_mul, map_mul, map_mul, map_mul, h1, hj, one_mul, det_dg, map_prod, NNReal.coe_mul, NNReal.coe_prod] at h3
  have h4 : ∀ i, (ν (s ^ l α i) : ℝ) = (b ^ l α i)⁻¹ := fun i => by
    rw [map_zpow, NNReal.coe_zpow, hs, _root_.inv_zpow]
  rw [h3, mul_comm, Finset.prod_congr rfl fun i _ => h4 i]
  exact mul_le_mul_of_nonneg_right (hB ⟨_, hcL α, rfl⟩) (by positivity)

theorem reduce_gl (D : D7) (r : ℕ) : ∃ (L : Set (GL (Fin r) (AE D))) (C : ℝ), IsCompact L ∧ ∀ α : GL (Fin r) (AE D),
    ∃ (δ : GL (Fin r) D.host.E) (l : Fin r → ℤ), ∃ c ∈ L, bc (incA D) δ * α = dg (hf D) l * c ∧
      (absA D (GeneralLinearGroup.det α) : ℝ) ≤ C * ∏ i, (bs D ^ l i)⁻¹ :=
  haveI := t2Space_adeleRing' (F := D.host.F)
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI := t2Space_tensorProduct_finiteExtension (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hc := AdelicU.isCMExt_host D
  reduction_GL_diagonalUnitPowers_compact (incA D) continuous_absE (fun u => absE_inclR u) (one_pos.trans one_lt_bs)
    (by rw [GlobalTheory.T.tensorIdeleNormalizedAbs_ideleHalfAtInfinity _ _ _ hc]; simp) (red_gl _ _ _ hc r)

theorem reduce (h₀ : IsAniso T₀) : ∃ (W : Set (GA D T)) (C : ℝ), IsCompact W ∧ ∀ p : stab d, ∃ γ ∈ stab d ⊓ GQ T,
    ∃ b c, ∃ l : Fin r → ℤ, ∃ w ∈ W, γ * p = d.nB b * d.nC c * d.levi (dg (hf D) l) * w ∧
      (absDet d p : ℝ) ≤ C * ∏ i, (bs D ^ l i)⁻¹ := by
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact D T₀ h₀
  obtain ⟨L, B, hL, hR⟩ := reduce_gl D r
  have hcont : Continuous fun x : GL (Fin r) (AE D) × GA D T₀ => d.levi x.1 * d.emb0 x.2 :=
    (d.continuous_levi.comp continuous_fst).mul (d.continuous_embed.comp continuous_snd)
  refine ⟨_, B, (hL.prod hK).image hcont, fun p => ?_⟩
  obtain ⟨b, s, g, e⟩ := exists_decomp d p
  obtain ⟨g₀, hg₀, κ, hκ, rfl⟩ := hcov g
  obtain ⟨δ, l, c, hc, hred, hle⟩ := hR (onX d p)
  have h1 : d.levi (bc (incA D) δ) ∈ GQ T := d.levi_mem_GQ (rat_mem δ.1) (rat_mem (δ⁻¹).1)
  generalize bc (incA D) δ = u at h1 hred
  exact ⟨d.levi u * d.emb0 g₀⁻¹, mul_mem ⟨levi_mem d _, h1⟩ ⟨wittCoreEmbedding_mem_isotropicStabilizer d _, d.wittDecomp_anisotropicEmbedding_mem_rationalPoints (inv_mem hg₀)⟩,
    u.1 ⬝ (b ⬝ mt T₀ g₀⁻¹⁻¹), skewConj u.1 s, l, d.levi c * d.emb0 κ, ⟨(c, κ), ⟨hc, hκ⟩, rfl⟩,
    grp_reduce e (d.wittHyperbolic_anisotropic_conj_nB _ _) (d.levi_mul_nB _ _) (d.wittHyperbolic_anisotropic_commute_nC _ _) (d.levi_mul_nC _ _)
      ((map_mul d.emb0 _ _).symm.trans (congrArg d.emb0 (inv_mul_cancel_left g₀ κ))) (d.wittHyperbolic_anisotropic_commute_levi _ _)
      ((map_mul d.levi _ _).symm.trans ((congrArg d.levi hred).trans (map_mul d.levi _ _))), hle⟩

theorem pY_mul (b : Mx D r T₀.rank) (c : skewA D r) (a : GL (Fin r) (AE D)) (w : GA D T) :
    d.pY ⬝ mt T (d.nB b * d.nC c * d.levi a * w) = adj a⁻¹.1 ⬝ (d.pY ⬝ mt T w) := by
  rw [GlobalTheory.MixModel.mt_mul, GlobalTheory.MixModel.mt_mul, GlobalTheory.MixModel.mt_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, d.pY_nB, d.pY_nC, d.pY_levi, Matrix.mul_assoc]

theorem pY_row (g : GA D T) (i : Fin r) : ¬∀ x, (d.pY ⬝ mt T g) i x = 0 :=
  haveI : Nontrivial (AE D) := incA_injective.nontrivial
  have h4 : mt T g ⬝ (mt T g⁻¹ ⬝ d.jY) = d.jY := (cancel₂ (mt_mul_inv T g) d.jY).trans (Matrix.one_mul _)
  row_ne_zero ((Matrix.mul_assoc _ _ _).trans ((congrArg (d.pY ⬝ ·) h4).trans d.pY_jY)) i

theorem bound_aux {E A : Type} [Field E] [CommRing A] (j : E →+* A) {s : Aˣ} {Ω : Set A} {m₀ r n : ℕ}
    (hm₀ : ∀ m, m₀ ≤ m → ∀ ω ∈ Ω, ∀ x : E, j x = s.1 ^ m * ω → x = 0) {l : Fin r → ℤ} {y : Matrix (Fin r) (Fin n) E}
    {w : Matrix (Fin r) (Fin n) A} (hw : ∀ i x, w i x ∈ Ω) (e : y.map j = (dg s l)⁻¹.1 * w) (i : Fin r)
    (h : ¬∀ x, y.map j i x = 0) : -(m₀ : ℤ) ≤ l i := by
  by_contra! hlt
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (a := -l i) (by omega)
  refine h fun x => ?_
  have h3 : j (y i x) = s.1 ^ m * w i x := by
    refine (congrFun (congrFun e i) x).trans ?_
    rw [show (dg s l)⁻¹.1 = diagonal fun i => (s ^ l i)⁻¹.1 from rfl, diagonal_mul, ← _root_.zpow_neg, hm, zpow_natCast,
      Units.val_pow_eq_pow_val]
  rw [map_apply, hm₀ m (by omega) _ (hw i x) _ h3, map_zero]

theorem exists_bound {W : Set (GA D T)} (hW : IsCompact W) : ∃ m₀ : ℕ, ∀ b c (l : Fin r → ℤ), ∀ w ∈ W,
    d.nB b * d.nC c * d.levi (dg (hf D) l) * w ∈ GQ T → ∀ i, -(m₀ : ℤ) ≤ l i := by
  have hc : Continuous fun w : GA D T => d.pY ⬝ mt T w := continuous_const.matrix_mul (continuous_mt T)
  have hb : Bdd fun w : W => (w : GA D T) := ⟨W, hW, fun w => w.2⟩
  obtain ⟨Ω, hΩ, h⟩ := (hb.map hc).entries
  obtain ⟨m₀, hm₀⟩ := (GlobalTheory.T.compact_adeles_rational_points_finite_eventually_zero _ _ Ω hΩ).2
  refine ⟨m₀, fun b c l w hw hg i => ?_⟩
  have h1 := pY_mul d b c (dg (hf D) l) w
  have h2 := pY_row d (d.nB b * d.nC c * d.levi (dg (hf D) l) * w) i
  rw [adj_dg] at h1
  generalize d.nB b * d.nC c * d.levi (dg (hf D) l) * w = g at hg h1 h2
  obtain ⟨y, hy⟩ := mem_ratMx.1 (ratMx_mul (rat_mem d.qY) ((mem_GQ_iff T g).1 hg))
  replace hy : rat y = d.pY ⬝ mt T g := hy
  rw [← hy] at h1 h2
  exact bound_aux (incA D) hm₀ (h ⟨w, hw⟩) h1 i h2

theorem dg_sub (s : (AE D)ˣ) (m : Fin r → ℕ) (m₀ : ℤ) :
    (dg s fun i => (m i : ℤ) + m₀) = (dg s fun i => (m i : ℤ)) * dg s fun _ => m₀ := Units.ext (by
  change diagonal _ = diagonal _ * diagonal _
  rw [diagonal_mul_diagonal]
  exact congrArg diagonal (funext fun i => congrArg Units.val (_root_.zpow_add s _ _)))

theorem grp_count {G : Type} [Group G] {γ' γ x p k n a z w y w' : G} (e : x = p * k) (h1 : γ * p = n * (a * z) * w)
    (h2 : γ' * (n * a) = y * a * w') : γ' * γ * x = y * a * (w' * z * w * k) :=
  calc _ = γ' * (γ * p) * k := by rw [e]; simp only [mul_assoc]
    _ = γ' * (n * a) * (z * w * k) := by rw [h1]; simp only [mul_assoc]
    _ = _ := by rw [h2]; simp only [mul_assoc]

theorem exists_card_le' {Q : Type} {Z w : Q → GA D T} (hZ : ∀ q, Z q ∈ GQ T) (hi : Function.Injective Z) (hw : Bdd w) :
    ∃ N : ℕ, ∀ (z : GA D T) (S : Finset Q), (∀ q ∈ S, Z q = z * w q) → S.card ≤ N := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI : Nontrivial (AE D) := incA_injective.nontrivial
  have he := AdelicU.isEmbedding_matHom (AF D.host.F) D.sp.cm.sig T.gram
  obtain ⟨N, hN⟩ := exists_card_le (incA D) (fun Ω h => (GlobalTheory.T.compact_adeles_rational_points_finite_eventually_zero _ _ Ω h).1)
    (Z := fun q => AdelicU.matHom _ D.sp.cm.sig T.gram (Z q)) (fun q => (mem_rat _).2 fun a b => by
      obtain ⟨y, hy⟩ := mem_ratMx.1 ((mem_GQ_iff T _).1 (hZ q))
      exact ⟨y a b, congrFun (congrFun hy a) b⟩) (he.injective.comp hi) (hw.map he.continuous)
  exact ⟨N, fun z S h => hN (AdelicU.matHom _ D.sp.cm.sig T.gram z) S fun q hq =>
    (congrArg _ (h q hq)).trans (map_mul _ _ _)⟩

theorem summable_absDet (h₀ : IsAniso T₀) {Q : Type} {x k : Q → GA D T} {p : Q → stab d} (hx : ∀ q, x q ∈ GQ T)
    (e : ∀ q, x q = p q * k q) (hk : Bdd k) (hi : ∀ q q', ∀ γ ∈ stab d, x q' = γ * x q → q = q') {t : ℝ}
    (ht : ((T₀.rank + r : ℕ) : ℝ) < t) : Summable fun q => (absDet d (p q) : ℝ) ^ t := by
  classical
  have hb := one_lt_bs (D := D)
  have hb0 := one_pos.trans hb
  obtain ⟨W, B, hW, hR⟩ := reduce d h₀
  choose γ hγ b c l w hw hred hle using fun q => hR (p q)
  have hwb : Bdd w := ⟨W, hW, hw⟩
  obtain ⟨W₁, hW₁, hw₁⟩ := hwb.mul hk
  obtain ⟨m₀, hm₀⟩ := exists_bound d hW₁
  have hl : ∀ q i, -(m₀ : ℤ) ≤ l q i := fun q => hm₀ (b q) (c q) (l q) _ (hw₁ q) (by
    have := mul_mem (hγ q).2 (hx q)
    rwa [e, ← mul_assoc, hred, mul_assoc _ (w q)] at this)
  obtain ⟨m, hm⟩ : ∃ m : Q → Fin r → ℕ, ∀ q, l q = fun i => (m q i : ℤ) + -(m₀ : ℤ) :=
    ⟨fun q i => (l q i + m₀).toNat, fun q => funext fun i => by have := hl q i; beta_reduce; omega⟩
  obtain ⟨W₂, C, hW₂, hC⟩ := cover_rad d
  choose Y hY hC using hC
  choose γ' hγ' y hy w' hw' hcov using fun q => hC (m q) (b q) (c q)
  have hw'b : Bdd w' := ⟨W₂, hW₂, hw'⟩
  have h4 : ∀ q, γ' q * γ q * x q = y q * d.levi (dg (hf D) fun i => (m q i : ℤ)) *
      (w' q * d.levi (dg (hf D) fun _ => -(m₀ : ℤ)) * w q * k q) := fun q =>
    grp_count (e q) (by rw [hred, hm, dg_sub, map_mul]) (hcov q)
  obtain ⟨N, hN⟩ := exists_card_le' (Z := fun q => γ' q * γ q * x q)
    (fun q => mul_mem (mul_mem (hγ' q).2 (hγ q).2) (hx q))
    (fun q q' h => hi q q' ((γ' q' * γ q')⁻¹ * (γ' q * γ q))
      (mul_mem (inv_mem (mul_mem (hγ' q').1 (hγ q').1)) (mul_mem (hγ' q).1 (hγ q).1))
      ((eq_inv_mul_iff_mul_eq.2 h.symm).trans (mul_assoc _ _ _).symm))
    (((hw'b.mul (Bdd.const (d.levi (dg (hf D) fun _ => -(m₀ : ℤ))))).mul hwb).mul hk)
  refine summable_of_count Q r (T₀.rank + r) (bs D) (max (B * bs D ^ (m₀ * r)) (N * C)) t m _ hb ht
    (fun q => ⟨NNReal.coe_nonneg _, ?_⟩) fun μ S hS => ?_
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    refine (hle q).trans (le_of_eq ?_)
    rw [mul_assoc, hm]
    simp only [zpow_add₀ hb0.ne', _root_.zpow_neg, zpow_natCast, mul_inv, inv_inv, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
    rw [mul_comm (∏ _, _)]
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    have h10 : S.card ≤ N * (Y μ).card := Finset.card_le_mul_card_image_of_maps_to
      (fun q hq => hS q hq ▸ hy q) N fun z _ => hN (z * d.levi (dg (hf D) fun i => (μ i : ℤ))) _
        fun q hq => by rw [h4, (Finset.mem_filter.1 hq).2, hS q (Finset.mem_filter.1 hq).1]
    rw [mul_assoc]
    exact (Nat.cast_le.2 h10).trans (by push_cast; exact mul_le_mul_of_nonneg_left (hY μ) (Nat.cast_nonneg _))

end GlobalTheory.GodementSectionReduction

end
