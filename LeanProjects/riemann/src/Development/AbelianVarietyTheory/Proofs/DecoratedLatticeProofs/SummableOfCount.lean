import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizerInductionLaw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary

noncomputable section

open scoped NNReal TensorProduct
open NumberField Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.Eis.Conv GlobalTheory.MixModel GlobalTheory.RegSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GodementSectionReduction

open GlobalTheory.SummCount in

theorem summable_of_count (ι : Type) (n N : ℕ) (b C t : ℝ) (k : ι → Fin n → ℕ)
    (h : ι → ℝ) (hb : 1 < b) (ht : (N : ℝ) < t)
    (hh : ∀ q, 0 ≤ h q ∧ h q ≤ C * ∏ i, (b ^ k q i)⁻¹)
    (hT : ∀ (m : Fin n → ℕ) (T : Finset ι), (∀ q ∈ T, k q = m) →
      (T.card : ℝ) ≤ C * ∏ i, b ^ (N * m i)) :
    Summable fun q => h q ^ t := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg N) ht.le
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨q0⟩⟩
  · exact .of_finite
  have hP : ∀ m : Fin n → ℕ, 0 < ∏ i, (b ^ m i)⁻¹ := fun m => by positivity
  have hC : 0 ≤ C := (mul_nonneg_iff_of_pos_right (hP (k q0))).1 ((hh q0).1.trans (hh q0).2)
  set r := b ^ ((N : ℝ) - t) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hb0.le _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)
  set g : (Fin n → ℕ) → ℝ := fun m => C * C ^ t * ∏ i, r ^ m i with hg_def
  have hg0 : ∀ m, 0 ≤ g m := fun m => by
    simp only [hg_def]; positivity
  have hg : Summable g :=
    (summable_prod_fin_tuple (summable_geometric_of_lt_one hr0 hr1) (fun _ => pow_nonneg hr0 _)
      n).mul_left _
  have key : ∀ q, h q ^ t ≤ C ^ t * ∏ i, ((b ^ k q i)⁻¹) ^ t := fun q => by
    rw [Real.finset_prod_rpow _ _ (fun i _ => by positivity), ← Real.mul_rpow hC (hP _).le]
    exact Real.rpow_le_rpow (hh q).1 (hh q).2 ht0
  refine summable_of_sum_le (c := ∑' m, g m) (fun q => Real.rpow_nonneg (hh q).1 _) fun T => ?_
  rw [← Finset.sum_fiberwise_of_maps_to (g := k) (t := T.image k)
    (fun q hq => Finset.mem_image_of_mem k hq)]
  refine le_trans (Finset.sum_le_sum fun m _ => ?_) (hg.sum_le_tsum _ (fun m _ => hg0 m))
  calc ∑ q ∈ T with k q = m, h q ^ t
      ≤ ∑ q ∈ T with k q = m, C ^ t * ∏ i, ((b ^ m i)⁻¹) ^ t :=
        Finset.sum_le_sum fun q hq => by
          have := key q
          rwa [(Finset.mem_filter.1 hq).2] at this
    _ = ((T.filter (k · = m)).card : ℝ) * (C ^ t * ∏ i, ((b ^ m i)⁻¹) ^ t) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C * ∏ i, b ^ (N * m i)) * (C ^ t * ∏ i, ((b ^ m i)⁻¹) ^ t) :=
        mul_le_mul_of_nonneg_right (hT m _ fun q hq => (Finset.mem_filter.1 hq).2)
          (mul_nonneg (Real.rpow_nonneg hC _)
            (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (by positivity) _))
    _ = g m := by
        simp only [hg_def, hr, ← pow_mul_inv_rpow_eq hb0 N, Finset.prod_mul_distrib]
        ring

open GlobalTheory.Eis.Conv.CovSkew in

theorem cover_adele (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) : ∃ (Ω : Set (AF F ⊗[F] E)) (C : ℝ), IsCompact Ω ∧ ∀ m : ℕ, ∃ Y : Finset (AF F ⊗[F] E),
      (Y.card : ℝ) ≤ C * ((4 : ℝ) ^ Fintype.card (InfinitePlace F)) ^ m ∧ ∀ z : AF F ⊗[F] E, ∃ x : E, ∃ y ∈ Y, ∃ ω ∈ Ω,
        z = inclR (F := F) (AF F) x + y + (halfE F E).1 ^ m * ω := by
  classical
  haveI := hσ.1
  obtain ⟨Ω₀, C₀, hΩ₀, hcov⟩ := GlobalTheory.T.exists_adele_cover_mod_field_shrunk_compact F
  obtain ⟨δ, -, hsp⟩ := exists_delta F E σ hσ
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := isTopologicalRing_tens
  have hcont : Continuous fun p : AF F × AF F => psi (F := F) δ p.1 p.2 := by
    unfold psi
    fun_prop
  refine ⟨_, C₀ ^ 2, (hΩ₀.prod hΩ₀).image hcont, fun m => ?_⟩
  obtain ⟨Y, hY, hYc⟩ := hcov m
  refine ⟨(Y ×ˢ Y).image fun y => psi δ y.1 y.2, ?_, fun z => ?_⟩
  · refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
    rw [Finset.card_product, Nat.cast_mul]
    refine (mul_self_le_mul_self (Nat.cast_nonneg _) hY).trans (le_of_eq ?_)
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, mul_pow]
    ring
  · obtain ⟨u, v, rfl⟩ := exists_coords δ hsp z
    set c : AF F := algebraMap F (AF F) 2⁻¹ with hc
    have h2 : 2 * c = 1 := by
      rw [hc, ← map_ofNat (algebraMap F (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
    obtain ⟨x, y, hy, ω, hω, e⟩ := hYc (c * (u + v))
    obtain ⟨x', y', hy', ω', hω', e'⟩ := hYc (c * (v - u))
    refine ⟨(x - x') • (1 : E) + (x + x') • δ, _, Finset.mem_image.mpr ⟨(y, y'), Finset.mem_product.2 ⟨hy, hy'⟩, rfl⟩,
      _, ⟨(ω, ω'), ⟨hω, hω'⟩, rfl⟩, ?_⟩
    have : (halfE F E).1 = algebraMap (AF F) (AF F ⊗[F] E) (halfInf F).1 := rfl
    rw [this, ← map_pow, ← psi_split, ← e, ← e', psi_eq]
    congr 2
    · linear_combination (-u) * h2
    · linear_combination (-v) * h2

variable {D : D7} {T T₀ : HSp D} {r : ℕ}

abbrev hf (D : D7) : (AE D)ˣ := halfE D.host.F D.host.E

abbrev bs (D : D7) : ℝ := 4 ^ Fintype.card (InfinitePlace D.host.F)

theorem one_lt_bs : 1 < bs D := one_lt_pow₀ (by norm_num) Fintype.card_ne_zero

theorem val_dg (m : Fin r → ℕ) : (dg (hf D) fun i => (m i : ℤ)).1 = diagonal fun i => (hf D).1 ^ m i := by
  simp [dg]

theorem adj_dg (l : Fin r → ℤ) : adj (dg (hf D) l)⁻¹.1 = (dg (hf D) l)⁻¹.1 :=
  congrArg Units.val (cti_dg (σ := cA D) (sigR_halfE D.sp.cm.sig) l)

theorem adj_dg' (l : Fin r → ℤ) : adj (dg (hf D) l).1 = (dg (hf D) l).1 :=
  congrArg Units.inv (cti_dg (σ := cA D) (sigR_halfE D.sp.cm.sig) l)

theorem cover_rect (D : D7) (r n : ℕ) : ∃ (K : Set (Mx D r n)) (C : ℝ), IsCompact K ∧ ∀ m : Fin r → ℕ,
    ∃ Y : Finset (Mx D r n), (Y.card : ℝ) ≤ C * ∏ i, bs D ^ (n * m i) ∧ ∀ x : Mx D r n, ∃ x₀ ∈ ratMx D r n, ∃ y ∈ Y,
      ∃ ω ∈ K, x = x₀ + (y + (dg (hf D) fun i => (m i : ℤ)).1 ⬝ ω) := by
  classical
  obtain ⟨Ω, C, hΩ, h⟩ := cover_adele _ _ _ (AdelicU.isCMExt_host D)
  choose Y hY h using h
  refine ⟨Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Ω, (C ^ n) ^ r,
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hΩ, fun m =>
    ⟨Fintype.piFinset fun i => Fintype.piFinset fun _ => Y (m i), ?_, fun x => ?_⟩⟩
  · have h1 : (Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin n => Y (m i)).card = ∏ i, (Y (m i)).card ^ n := by
      simp only [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (Nat.cast_le.2 h1.le).trans ?_
    push_cast
    refine (Finset.prod_le_prod (fun _ _ => by positivity) fun i _ =>
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hY (m i)) n).trans (le_of_eq ?_)
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul _ (m _),
      mul_comm n]
  · choose x₀ y hy ω hω e using fun i j => h (m i) (x i j)
    refine ⟨_, rat_mem (of x₀), of y, Fintype.mem_piFinset.2 fun i => Fintype.mem_piFinset.2 (hy i), of ω,
      fun i _ j _ => hω i j, ?_⟩
    ext i j
    rw [val_dg, Matrix.add_apply, Matrix.add_apply, diagonal_mul, ← add_assoc]
    exact e i j

def sk (x : Mx D r r) : skewA D r :=
  ⟨half D • (x - adj x), by rw [mem_skewA, adj_smul, cA_half, adj_sub, adj_adj, ← smul_neg, neg_sub]⟩

theorem continuous_sk : Continuous (sk : Mx D r r → _) := by
  have := (lattice_Mx D r r).1
  have : ContinuousSub (Mx D r r) := IsTopologicalAddGroup.to_continuousSub
  exact ((continuous_id.sub continuous_adj).const_smul (half D)).subtype_mk _

theorem sk_add (x y : Mx D r r) : sk (x + y) = sk x + sk y := Subtype.ext (by
  change half D • (x + y - adj (x + y)) = half D • (x - adj x) + half D • (y - adj y)
  rw [adj_add, ← smul_add, add_sub_add_comm])

theorem sk_coe (x : skewA D r) : sk x.1 = x := Subtype.ext (by
  change half D • (x.1 - adj x.1) = x.1
  rw [mem_skewA.1 x.2, sub_neg_eq_add, smul_add, half_smul_add])

theorem sk_conj (a x : Mx D r r) : sk (a ⬝ x ⬝ adj a) = skewConj a (sk x) := Subtype.ext (by
  change half D • (a ⬝ x ⬝ adj a - adj (a ⬝ x ⬝ adj a)) = a ⬝ (half D • (x - adj x)) ⬝ adj a
  rw [adj_mul, adj_mul, adj_adj, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc a (adj x)])

theorem cover_skewA (D : D7) (r : ℕ) : ∃ (K : Set (skewA D r)) (C : ℝ), IsCompact K ∧ ∀ m : Fin r → ℕ,
    ∃ Y : Finset (skewA D r), (Y.card : ℝ) ≤ C * ∏ i, bs D ^ (r * m i) ∧ ∀ x : skewA D r, ∃ x₀ : skewA D r,
      x₀.1 ∈ ratMx D r r ∧ ∃ y ∈ Y, ∃ ω ∈ K, x = x₀ + (y + skewConj (dg (hf D) fun i => (m i : ℤ)).1 ω) := by
  classical
  have hc := AdelicU.isCMExt_host D
  haveI := hc.1
  obtain ⟨Ω₀, C₀, hΩ₀, hcov⟩ := GlobalTheory.T.exists_adele_cover_mod_field_shrunk_compact D.host.F
  obtain ⟨Ω, C, hΩ, h⟩ := GlobalTheory.T.skewHermitian_adelic_cover_of_adele_cover _ _ _ hc _ _ _ hΩ₀ hcov r
  have hK : IsCompact (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Ω : Set (Mx D r r)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hΩ
  refine ⟨_, C, hK.image continuous_sk, fun m => ?_⟩
  obtain ⟨Y, hY, h⟩ := h m
  refine ⟨Finset.image (α := Mx D r r) sk Y, (Nat.cast_le.mpr Finset.card_image_le).trans (hY.trans (le_of_eq ?_)),
    fun x => ?_⟩
  · simp only [bs, ← pow_mul, mul_comm _ 2, show (4 : ℝ) = 2 ^ 2 by norm_num]
  · obtain ⟨S, y, hy, ω, hω, e⟩ := h x.1 x.2
    refine ⟨sk (rat S), ratMx_smul _ (sub_mem (rat_mem _) (ratMx_adj (rat_mem _))), _, Finset.mem_image_of_mem _ hy, _,
      ⟨ω, fun i _ j _ => hω i j, rfl⟩, ?_⟩
    rw [← val_dg] at e
    replace e : x.1 = rat S + y + (dg (hf D) fun i => (m i : ℤ)).1 ⬝ ω ⬝ (dg (hf D) fun i => (m i : ℤ)).1 := e
    rw [← sk_conj, adj_dg', ← sk_add, ← sk_add, ← add_assoc, ← e, sk_coe]

end GlobalTheory.GodementSectionReduction

end
