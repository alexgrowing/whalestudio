import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsRationalDblCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAdeleE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteCompactArchimedeanMaximal
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cont

namespace GlobalTheory.DefiniteStab

open Matrix

theorem hasSig_neg_of_zero {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M 0 n) : HasSig (-M) n 0 := by
  obtain ⟨-, A, hA⟩ := h
  refine ⟨by simp, A.submatrix id (Equiv.sumComm (Fin n) (Fin 0)), ?_⟩
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · have h1 := congrFun (congrFun hA (Sum.inr i)) (Sum.inr j)
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.fromBlocks_apply₂₂,
        Matrix.neg_apply] at h1
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, id,
        Equiv.sumComm_apply, Sum.swap_inl, Matrix.neg_apply, Matrix.fromBlocks_apply₁₁, mul_neg, neg_mul,
        Finset.sum_neg_distrib, h1, neg_neg]
    · exact j.elim0
  · exact i.elim0

theorem eq_neg_one_of_hasSig {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (hM : HasSig M 0 n) (hθ : IsCartan M θ) :
    θ = -1 := by
  obtain ⟨h1, h2, h3⟩ := hθ
  have h : IsCartan (-M) (-θ) := by
    refine ⟨by rw [neg_mul_neg, h1], ?_, fun x hx => ?_⟩
    · rw [Matrix.transpose_neg, Matrix.map_neg _ (fun a => star_neg a)]
      simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, h2]
    · have := h3 x hx
      simpa [Matrix.neg_mulVec, neg_dotProduct] using this
  have := GlobalTheory.DefiniteCartan.eq_one_of_hasSig (hasSig_neg_of_zero hM) h
  rw [← neg_neg θ, this]

end GlobalTheory.DefiniteStab

namespace GlobalTheory.DefiniteStab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_transfer {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.IsLattice E) :
    ∃ c : E, c ≠ 0 ∧ ∀ x ∈ L, ∀ i j, Pi.single i (c * x j) ∈ L := by
  classical
  have hd : ∀ i : Fin n, ∃ z : nonZeroDivisors (𝓞 E), ((z : 𝓞 E) • Pi.single i (1 : E)) ∈ L := by
    intro i
    have hmem : Pi.single i (1 : E) ∈ Submodule.span E (L : Set (Fin n → E)) := by
      rw [hL.span_eq_top]; trivial
    obtain ⟨y, hy, z, hz⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors (𝓞 E))).1 hmem
    refine ⟨z, ?_⟩
    rw [Submodule.span_eq] at hy
    rw [hz, ← smul_assoc, Algebra.smul_def (↑z : 𝓞 E) (IsLocalization.mk' E (1 : 𝓞 E) z), IsLocalization.mk'_spec',
      map_one, one_smul]
    exact hy
  choose z hz using hd
  obtain ⟨s, hs⟩ := hL.fg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E))
    ((s ×ˢ (Finset.univ : Finset (Fin n))).image fun p => p.1 p.2)
  have hint : ∀ x ∈ L, ∀ j, IsLocalization.IsInteger (𝓞 E) ((b : 𝓞 E) • x j) := by
    intro x hx j
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hb _ (Finset.mem_image.2 ⟨(x, j), Finset.mem_product.2 ⟨hx, Finset.mem_univ _⟩, rfl⟩)
    | zero => simpa using IsLocalization.isInteger_zero
    | add x y _ _ hx hy => simpa [smul_add] using IsLocalization.isInteger_add hx hy
    | smul r x _ hx =>
      obtain ⟨o, ho⟩ := hx
      refine ⟨r * o, ?_⟩
      simp only [Pi.smul_apply, map_mul, ho]
      rw [smul_comm (b : 𝓞 E) r (x j)]
      exact (Algebra.smul_def r ((b : 𝓞 E) • x j)).symm
  let d : 𝓞 E := ∏ i, (z i : 𝓞 E)
  have hdmem : ∀ i, d • Pi.single i (1 : E) ∈ L := by
    intro i
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun k => (z k : 𝓞 E)) (Finset.mem_univ i)
    rw [show d = q * z i by rw [mul_comm]; exact hq, mul_smul]
    exact L.smul_mem q (hz i)
  refine ⟨algebraMap (𝓞 E) E (d * b), ?_, fun x hx i j => ?_⟩
  · rw [map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => nonZeroDivisors.coe_ne_zero (z k))
      (nonZeroDivisors.coe_ne_zero b)
  · obtain ⟨o, ho⟩ := hint x hx j
    have e : Pi.single i (algebraMap (𝓞 E) E (d * b) * x j) = o • (d • (Pi.single i (1 : E) : Fin n → E)) := by
      ext k
      by_cases hk : k = i
      · subst hk
        simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, mul_one, Algebra.smul_def]
        rw [map_mul, mul_assoc, ← Algebra.smul_def (b : 𝓞 E) (x j), ← ho]
        ring
      · simp [Pi.single_eq_of_ne hk]
    rw [e]
    exact L.smul_mem o (hdmem i)

end GlobalTheory.DefiniteStab

namespace GlobalTheory.DefiniteStab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (F) in

def intFin : Set (AF F) := {a | ∀ v, evFin F v a ∈ v.adicCompletionIntegers F}

theorem isOpen_intFin : IsOpen (intFin F) := by
  have h := (RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)).preimage
    (show Continuous (fun a : AF F => a.2) from continuous_snd)
  exact h

theorem zero_mem_intFin : (0 : AF F) ∈ intFin F := fun v => by rw [map_zero]; exact zero_mem _

theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem gen_mem {n : ℕ} (X : Spc F E n) {a : AF F} (h0 : evI F a = 0) (ha : a ∈ intFin F) {x : Fin n → E}
    (hx : x ∈ X.L) : a • incV F x ∈ latHat X :=
  AddSubgroup.subset_closure ⟨a, h0, ha, x, hx, rfl⟩

theorem smul_mem_latHat {n : ℕ} {X : Spc F E n} {a : AF F} (ha : a ∈ intFin F) {z : Fin n → AE F E}
    (hz : z ∈ latHat X) : a • z ∈ latHat X := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb0, hb, x, hx, rfl⟩ := hz
    rw [smul_smul]
    refine gen_mem X (by rw [evI_mul, hb0, mul_zero]) (fun v => ?_) hx
    rw [map_mul]; exact mul_mem (ha v) (hb v)
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem inclR_smul_mem {n : ℕ} {X : Spc F E n} (o : 𝓞 E) {z : Fin n → AE F E} (hz : z ∈ latHat X) :
    inclR (F := F) (AF F) (o : E) • z ∈ latHat X := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb0, hb, x, hx, rfl⟩ := hz
    have e : inclR (F := F) (AF F) (o : E) • (b • incV F x) = b • incV F (o • x) := by
      funext i
      simp only [Pi.smul_apply, incV, smul_eq_mul]
      rw [mul_smul_comm, ← map_mul]; rfl
    rw [e]; exact gen_mem X hb0 hb (X.L.smul_mem o hx)
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem single_mem_latHat {n : ℕ} {X : Spc F E n} {c : E} (hc : ∀ x ∈ X.L, ∀ i j, Pi.single i (c * x j) ∈ X.L)
    (i j : Fin n) {z : Fin n → AE F E} (hz : z ∈ latHat X) :
    Pi.single i (inclR (F := F) (AF F) c * z j) ∈ latHat X := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb0, hb, x, hx, rfl⟩ := hz
    have e : (Pi.single i (inclR (F := F) (AF F) c * (b • incV F x) j) : Fin n → AE F E) =
        b • incV F (Pi.single i (c * x j)) := by
      funext k
      by_cases hk : k = i
      · subst hk; simp only [Pi.single_eq_same, Pi.smul_apply, incV, map_mul, mul_smul_comm]
      · simp only [Pi.single_eq_of_ne hk, Pi.smul_apply, incV, map_zero, smul_zero]
    rw [e]; exact gen_mem X hb0 hb (hc x hx i j)
  | zero => simp only [Pi.zero_apply, mul_zero, Pi.single_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, mul_add, Pi.single_add]; exact add_mem hx hy
  | neg x _ hx => simp only [Pi.neg_apply, mul_neg, Pi.single_neg]; exact neg_mem hx

variable (F E) in

noncomputable def basA : Module.Basis (Fin (Module.finrank F E)) (AF F) (AE F E) :=
  Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)

theorem exists_int_scale : ∃ t : E, t ≠ 0 ∧ ∀ k, ∃ o : 𝓞 E, t * Module.finBasis F E k = o := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E))
    (Finset.univ.image (Module.finBasis F E))
  refine ⟨algebraMap (𝓞 E) E b, ?_, fun k => ?_⟩
  · rw [map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]
    exact nonZeroDivisors.coe_ne_zero b
  · obtain ⟨o, ho⟩ := hb _ (Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩)
    exact ⟨o, by rw [← Algebra.smul_def]; exact ho.symm⟩

theorem basis_smul_mem {n : ℕ} {X : Spc F E n} {t : E} (ht : ∀ k, ∃ o : 𝓞 E, t * Module.finBasis F E k = o)
    {u : AE F E} (hu : ∀ k, (basA F E).repr u k ∈ intFin F) {z : Fin n → AE F E} (hz : z ∈ latHat X) :
    (inclR (F := F) (AF F) t * u) • z ∈ latHat X := by
  rw [← (basA F E).sum_repr u, Finset.mul_sum, Finset.sum_smul]
  refine sum_mem fun k _ => ?_
  obtain ⟨o, ho⟩ := ht k
  have e : inclR (F := F) (AF F) t * ((basA F E).repr u k • basA F E k) =
      (basA F E).repr u k • inclR (F := F) (AF F) (o : E) := by
    rw [basA, Algebra.TensorProduct.basis_apply, mul_smul_comm, ← ho, map_mul]; rfl
  rw [e, smul_assoc]
  exact smul_mem_latHat (hu k) (inclR_smul_mem o hz)

theorem mulVec_mem {n : ℕ} {X : Spc F E n} {c t : E} (hc0 : c ≠ 0) (ht0 : t ≠ 0)
    (hc : ∀ x ∈ X.L, ∀ i j, Pi.single i (c * x j) ∈ X.L) (ht : ∀ k, ∃ o : 𝓞 E, t * Module.finBasis F E k = o)
    {N : Matrix (Fin n) (Fin n) (AE F E)}
    (hN : ∀ i j k, (basA F E).repr (inclR (F := F) (AF F) (t * c)⁻¹ * N i j) k ∈ intFin F)
    {z : Fin n → AE F E} (hz : z ∈ latHat X) : N *ᵥ z ∈ latHat X := by
  have h1 : inclR (F := F) (AF F) t * inclR (F := F) (AF F) (t * c)⁻¹ * inclR (F := F) (AF F) c = 1 := by
    rw [← map_mul, ← map_mul, show t * (t * c)⁻¹ * c = 1 by field_simp, map_one]
  have e : N *ᵥ z = ∑ i, ∑ j, (inclR (F := F) (AF F) t * (inclR (F := F) (AF F) (t * c)⁻¹ * N i j)) •
      (Pi.single i (inclR (F := F) (AF F) c * z j) : Fin n → AE F E) := by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    linear_combination (-(N k j * z j)) * h1
  rw [e]
  exact sum_mem fun i _ => sum_mem fun j _ => basis_smul_mem ht (hN i j) (single_mem_latHat hc i j hz)

end GlobalTheory.DefiniteStab

namespace GlobalTheory.DefiniteStab

theorem isOpen_stab_of_definite : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ {B : Base F E} {n : ℕ} {X : Spc F E n},
    (X.IsHerm σ B n 0 ∨ X.IsHerm σ B 0 n) → ∀ {K : Subgroup (UA σ X.J)}, IsStab B K → IsOpen (K : Set (UA σ X.J)) := by
  intro F E _ _ _ _ _ σ _ B n X hX K hK
  have hlat : X.L.IsLattice E := hX.elim (fun h => h.lat) (fun h => h.lat)
  have hθ : ∀ w, X.θ w = 1 ∨ X.θ w = -1 := fun w => hX.elim
    (fun h => Or.inl (GlobalTheory.DefiniteCartan.eq_one_of_hasSig (h.sig w) (h.cartan w)))
    (fun h => Or.inr (eq_neg_one_of_hasSig (h.sig w) (h.cartan w)))
  obtain ⟨c, hc0, hc⟩ := exists_transfer hlat
  obtain ⟨t, ht0, ht⟩ := exists_int_scale (F := F) (E := E)
  let V : Set (AE F E) := {u | ∀ k, (basA F E).repr (inclR (F := F) (AF F) (t * c)⁻¹ * u) k ∈ intFin F}
  have hVo : IsOpen V := by
    have hcont : Continuous fun u : AE F E => (basA F E).equivFun (inclR (F := F) (AF F) (t * c)⁻¹ * u) :=
      (IsModuleTopology.continuous_of_linearMap (basA F E).equivFun.toLinearMap).comp
        (continuous_const.mul continuous_id)
    have e : V = ⋂ k, (fun u => (basA F E).equivFun (inclR (F := F) (AF F) (t * c)⁻¹ * u) k) ⁻¹' intFin F := by
      ext u; simp [V, Module.Basis.equivFun_apply]
    rw [e]
    exact isOpen_iInter_of_finite fun k => isOpen_intFin.preimage ((continuous_apply k).comp hcont)
  have hV0 : (0 : AE F E) ∈ V := fun k => by
    rw [mul_zero, map_zero, Finsupp.zero_apply]; exact zero_mem_intFin
  have hmat : Continuous fun g : UA σ X.J => mat g := Units.continuous_val.comp continuous_subtype_val
  let W : Set (UA σ X.J) := {g | ∀ i j, (mat g - 1) i j ∈ V ∧ (mat g⁻¹ - 1) i j ∈ V}
  have hWo : IsOpen W := by
    have h1 : ∀ i j, Continuous fun g : UA σ X.J => (mat g - 1) i j :=
      fun i j => (hmat.sub continuous_const).matrix_elem i j
    have h2 : ∀ i j, Continuous fun g : UA σ X.J => (mat g⁻¹ - 1) i j :=
      fun i j => ((hmat.comp continuous_inv).sub continuous_const).matrix_elem i j
    simp only [W, Set.setOf_forall, Set.setOf_and]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (hVo.preimage (h1 i j)).inter (hVo.preimage (h2 i j))
  have hW1 : (1 : UA σ X.J) ∈ W := by
    have e : mat (1 : UA σ X.J) = 1 := rfl
    intro i j
    rw [inv_one, e, sub_self]
    exact ⟨hV0, hV0⟩
  have key : ∀ N : Matrix (Fin n) (Fin n) (AE F E), (∀ i j, (N - 1) i j ∈ V) → ∀ z ∈ latHat X, N *ᵥ z ∈ latHat X := by
    intro N hN z hz
    have e : N *ᵥ z = z + (N - 1) *ᵥ z := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [e]
    exact add_mem hz (mulVec_mem hc0 ht0 hc ht (fun i j => hN i j) hz)
  refine Subgroup.isOpen_of_mem_nhds K (g := 1) (Filter.mem_of_superset (hWo.mem_nhds hW1) fun g hg => ?_)
  rw [SetLike.mem_coe, hK]
  refine ⟨fun w => ?_, fun z hz => ⟨key _ (fun i j => (hg i j).1) z hz, key _ (fun i j => (hg i j).2) z hz⟩⟩
  rcases hθ w with h | h <;> rw [h]
  · exact Commute.one_right _
  · exact (Commute.one_right _).neg_right

end GlobalTheory.DefiniteStab
