import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowDef
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport

noncomputable section

namespace PositivityTheory.ThKF0.Grow.Ht

open scoped Matrix NNReal ENNReal Classical TensorProduct
open NumberField IsDedekindDomain Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F : Type} [Field F] [NumberField F]

def evH : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evH_eq (a : AF F) : evI F a = evH a := rfl

def Sz (m : ℕ) (c : ℝ) (a : AF F) : Prop :=
  ‖evH a‖ ≤ c ∧ ∀ v, evFin F v ((m : AF F) * a) ∈ v.adicCompletionIntegers F

theorem Sz.mul {m m' : ℕ} {c c' : ℝ} {a a' : AF F} (h : Sz m c a) (h' : Sz m' c' a') : Sz (m * m') (c * c') (a * a') := by
  refine ⟨?_, fun v => ?_⟩
  · rw [map_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul h.1 h'.1 (norm_nonneg _) ((norm_nonneg _).trans h.1))
  · rw [Nat.cast_mul, mul_mul_mul_comm, map_mul]
    exact mul_mem (h.2 v) (h'.2 v)

theorem Sz.sum {ι : Type} [Fintype ι] {m : ℕ} {c : ℝ} {a : ι → AF F} (h : ∀ i, Sz m c (a i)) :
    Sz m (Fintype.card ι * c) (∑ i, a i) := by
  refine ⟨?_, fun v => ?_⟩
  · rw [map_sum]
    refine (norm_sum_le_of_le _ fun i _ => (h i).1).trans ?_
    simp
  · rw [Finset.mul_sum, map_sum]
    exact sum_mem fun i _ => (h i).2 v

theorem Sz.mono {m m' : ℕ} {c c' : ℝ} {a : AF F} (h : Sz m c a) (hm : m ∣ m') (hc : c ≤ c') : Sz m' c' a := by
  obtain ⟨k, rfl⟩ := hm
  refine ⟨h.1.trans hc, fun v => ?_⟩
  rw [Nat.cast_mul, mul_comm (m : AF F), mul_assoc, map_mul, map_natCast]
  exact mul_mem (natCast_mem _ k) (h.2 v)

theorem exists_den (a : AF F) : ∃ m : ℕ, 1 ≤ m ∧ ∀ v, evFin F v ((m : AF F) * a) ∈ v.adicCompletionIntegers F := by
  obtain ⟨m, hm, -, hv⟩ := GlobalTheory.SmoothForms.denom_global (fun v => max 1 ‖evFin F v a‖₊) (fun v => le_max_left _ _) (by
    refine (Filter.eventually_cofinite.1 a.2.2).subset fun v hv hv' => hv (max_eq_left ?_)
    exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 hv')
  refine ⟨m, hm, fun v => ?_⟩
  rw [map_mul, map_natCast]
  exact Valued.toNormedField.norm_le_one_iff.1 (hv v _ (le_max_right _ _))

theorem exists_sz {ι : Type} [Fintype ι] (a : ι → AF F) : ∃ (m : ℕ) (c : ℝ), 1 ≤ m ∧ 0 ≤ c ∧ ∀ i, Sz m c (a i) := by
  choose m hm hv using fun i => exists_den (a i)
  refine ⟨∏ i, m i, ∑ i, ‖evH (a i)‖, Nat.succ_le_of_lt (Finset.prod_pos fun i _ => hm i), by positivity, fun i =>
    Sz.mono (m := m i) ⟨le_rfl, hv i⟩ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) ?_⟩
  exact Finset.single_le_sum (f := fun i => ‖evH (a i)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)

theorem norm_evH_le {a : AF F} {c : ℝ} (hc : 0 ≤ c) (h : ∀ w, ‖evInf F w a‖ ≤ c) : ‖evH a‖ ≤ c := by
  refine max_le ((pi_norm_le_iff_of_nonneg hc).2 fun w => ?_) ((pi_norm_le_iff_of_nonneg hc).2 fun w => ?_)
  · exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).norm_map_of_map_zero (map_zero _)
      (evInf F w.1 a)).trans_le (h w.1)
  · exact ((InfinitePlace.Completion.isometry_extensionEmbedding w.1).norm_map_of_map_zero (map_zero _)
      (evInf F w.1 a)).trans_le (h w.1)

theorem inf_mul (a : mixedEmbedding.mixedSpace F) (z : AF F) : inf a * z = inf (a * evH z) := by
  refine Prod.ext ?_ (zero_mul _)
  change (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a * z.1 =
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a * InfiniteAdeleRing.ringEquiv_mixedSpace F z.1)
  rw [map_mul, RingEquiv.symm_apply_apply]

theorem inf_sum {ι : Type} [Fintype ι] (a : ι → mixedEmbedding.mixedSpace F) : ∑ i, inf (a i) = inf (∑ i, a i) := by
  let I : mixedEmbedding.mixedSpace F →+ AF F :=
    (AddMonoidHom.inl (Ainf F) (Af F)).comp (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom
  exact (map_sum I a Finset.univ).symm

theorem intF_mul {a z : AF F} (ha : IntF a) (hz : ∀ v, evFin F v z ∈ v.adicCompletionIntegers F) : IntF (a * z) := by
  refine ⟨?_, fun v => ?_⟩
  · change a.1 * z.1 = 0
    rw [ha.1, zero_mul]
  · rw [map_mul]
    exact mul_mem (ha.2 v) (hz v)

theorem intF_sum {ι : Type} [Fintype ι] {a : ι → AF F} (h : ∀ i, IntF (a i)) : IntF (∑ i, a i) := by
  refine ⟨?_, fun v => ?_⟩
  · exact (map_sum (RingHom.fst (Ainf F) (Af F)) a Finset.univ).trans (Finset.sum_eq_zero fun i _ => (h i).1)
  · rw [map_sum]
    exact sum_mem fun i _ => (h i).2 v

variable {κ : Type} [Fintype κ]

variable (F κ) in

def crd : Pt F κ ≃ₗ[AF F] (κ ⊕ κ → AF F) := (LinearEquiv.sumArrowLequivProdArrow κ κ (AF F) (AF F)).symm

theorem crd_apply (s : Pt F κ →ₗ[AF F] Pt F κ) (w : Pt F κ) (i : κ ⊕ κ) :
    crd F κ (s w) i = ∑ j, crd F κ w j * crd F κ (s ((crd F κ).symm (Pi.single j 1))) i := by
  have : w = ∑ j, crd F κ w j • (crd F κ).symm (Pi.single j 1) := by
    apply (crd F κ).injective
    simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [this]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem bd_of_sz {s : Pt F κ →ₗ[AF F] Pt F κ} {m : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, Sz m c (crd F κ (s ((crd F κ).symm (Pi.single j 1))) i)) : Bd s m (Fintype.card (κ ⊕ κ) * c) := by
  refine ⟨fun w hw => ?_, fun w => ?_⟩
  · have hw' : ∀ j, IntF (crd F κ w j) := by
      rintro (j | j)
      exacts [hw.1 j, hw.2 j]
    have : ∀ i, IntF (crd F κ ((m : AF F) • s w) i) := fun i => by
      rw [map_smul, Pi.smul_apply, crd_apply, smul_eq_mul, Finset.mul_sum]
      refine intF_sum fun j => ?_
      rw [mul_left_comm]
      exact intF_mul (hw' j) (h i j).2
    exact ⟨fun i => this (Sum.inl i), fun i => this (Sum.inr i)⟩
  · let z : κ ⊕ κ → mixedEmbedding.mixedSpace F := fun i =>
      ∑ j, Sum.elim w.1 w.2 j * evH (crd F κ (s ((crd F κ).symm (Pi.single j 1))) i)
    have hz : ∀ i, crd F κ (s (emb w)) i = inf (z i) := fun i => by
      rw [crd_apply, ← inf_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← inf_mul]
      rcases j with j | j <;> rfl
    have hn : ∀ i, ‖z i‖ ≤ Fintype.card (κ ⊕ κ) * c * ‖w‖ := fun i => by
      refine (norm_sum_le_of_le (n := fun _ => ‖w‖ * c) _ fun j _ => (norm_mul_le _ _).trans
        (mul_le_mul ?_ (h i j).1 (norm_nonneg _) (norm_nonneg _))).trans (le_of_eq ?_)
      · rcases j with j | j
        exacts [(norm_le_pi_norm w.1 j).trans (norm_fst_le w), (norm_le_pi_norm w.2 j).trans (norm_snd_le w)]
      · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    have h0 : 0 ≤ Fintype.card (κ ⊕ κ) * c * ‖w‖ := by positivity
    exact ⟨(fun i => z (Sum.inl i), fun i => z (Sum.inr i)),
      Prod.ext (funext fun i => hz (Sum.inl i)) (funext fun i => hz (Sum.inr i)),
      max_le ((pi_norm_le_iff_of_nonneg h0).2 fun i => hn _) ((pi_norm_le_iff_of_nonneg h0).2 fun i => hn _)⟩

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem exists_norm_repr_le {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (w : InfinitePlace F) (i : ι) : ∃ B : ℝ, 0 ≤ B ∧ ∀ (c : ℝ) (y : w.Completion ⊗[F] E),
      (∀ τ : EmbOver E w, ‖infEmb τ y‖ ≤ c) →
      ‖(Algebra.TensorProduct.basis w.Completion b.traceDual).repr y i‖ ≤ B * c := by
  letI : Algebra F ℂ := w.embedding.toAlgebra
  let t : (E →ₐ[F] ℂ) → EmbOver E w := fun τ => ⟨τ, RingHom.ext τ.commutes⟩
  have key : ∀ y : w.Completion ⊗[F] E, InfinitePlace.Completion.extensionEmbedding w
      ((Algebra.TensorProduct.basis w.Completion b.traceDual).repr y i) =
      ∑ τ : E →ₐ[F] ℂ, infEmb (t τ) y * τ (b i) := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz, add_mul, Finset.sum_add_distrib]
    | tmul a e =>
      have h : ∀ x : F, InfinitePlace.Completion.extensionEmbedding w (algebraMap F w.Completion x) =
          algebraMap F ℂ x := fun x =>
        InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm x)
      rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul,
        h, Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply,
        trace_eq_sum_embeddings, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [infEmb_tmul, map_mul, mul_assoc]; rfl
  refine ⟨∑ τ : E →ₐ[F] ℂ, ‖τ (b i)‖, by positivity, fun c y hy => ?_⟩
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), key, Finset.sum_mul]
  refine norm_sum_le_of_le _ fun τ _ => ?_
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (hy _) (norm_nonneg _)

variable (F E) in
theorem exists_entries : ∃ (ι : Type) (_ : Fintype ι) (β : Module.Basis ι (AF F) (AE F E)) (C : ℝ), 0 ≤ C ∧
    ∀ (n : ℕ) (g : GL (Fin n) (AE F E)), ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ heightGL F g ∧
      ∀ i j k, Sz m (C * heightGL F g) (β.repr (g.1 i j) k) := by
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral (𝓞 F) F E
  have hb' : ∀ i, IsIntegral ℤ (b i) := fun i => isIntegral_trans _ (hb i)
  choose B hB0 hB using fun (p : s × InfinitePlace F) => exists_norm_repr_le b p.2 p.1
  refine ⟨s, inferInstance, Algebra.TensorProduct.basis (AF F) b.traceDual, ∑ p, B p,
    Finset.sum_nonneg fun p _ => hB0 p, fun n g => ?_⟩
  obtain ⟨d, hd, hdc, hv⟩ := GlobalTheory.SmoothForms.denom_global (fun v => htFin F v (Formalism.UG.bc (compFin F E v) g))
    (fun v => one_le_htOf _ _) (finite_mulSupport_htFin F g)
  refine ⟨d, hd, ?_, fun i j k => ⟨norm_evH_le (mul_nonneg (Finset.sum_nonneg fun p _ => hB0 p) (NNReal.coe_nonneg _))
    fun w => ?_, fun v => ?_⟩⟩
  · exact_mod_cast hdc.trans (le_mul_of_one_le_left' (Finset.one_le_prod' fun _ _ => one_le_htOf _ _))
  · refine (congrArg norm (HeightProper.repr_map b.traceDual (evInf F w) (g.1 i j) k)).symm.trans_le
      ((hB (k, w) (heightGL F g) _ fun τ => ?_).trans (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun p _ => hB0 p) (Finset.mem_univ _)) (NNReal.coe_nonneg _)))
    have h := ((normInf_le_iff F w).1 (le_htOf _ _) τ).trans (GlobalTheory.Grow.htInf_le_heightGL F g w)
    exact (HeightProper.norm_entry_le_opNorm _ i j).trans (NNReal.coe_le_coe.2 h)
  · rw [map_mul, map_natCast]
    refine Valued.toNormedField.norm_le_one_iff.1 (hv v _ ?_)
    refine (congrArg nnnorm (HeightProper.repr_map b.traceDual (evFin F v) (g.1 i j) k)).symm.trans_le
      ((HeightProper.nnnorm_repr_le_absFin b hb' v _ k).trans ?_)
    exact (absFin_le_normFin F v (Formalism.UG.bc (compFin F E v) g).1 i j).trans (le_htOf _ _)

theorem expand {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype ι] (β : Module.Basis ι R A) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) :
    M = ∑ p : Fin n × Fin n × ι, β.repr (M p.1 p.2.1) p.2.2 • Matrix.single p.1 p.2.1 (β p.2.2) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Fintype.sum_prod_type, Matrix.single_apply, smul_ite, smul_zero]
  rw [Finset.sum_eq_single i (fun a _ ha => by simp [ha]) (by simp), Finset.sum_eq_single j (fun a _ ha => by simp [ha]) (by simp)]
  simp

theorem bilin {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype ι] (β : Module.Basis ι R A) {n d : ℕ}
    (l : Matrix (Fin n) (Fin d) A →ₗ[R] R) (u : Matrix (Fin n) (Fin d) A) (M : Matrix (Fin n) (Fin n) A)
    (N : Matrix (Fin d) (Fin d) A) : l (M * u * Nᵀ) = ∑ p : (Fin n × Fin n × ι) × (Fin d × Fin d × ι),
      β.repr (M p.1.1 p.1.2.1) p.1.2.2 * β.repr (N p.2.1 p.2.2.1) p.2.2.2 *
        l (Matrix.single p.1.1 p.1.2.1 (β p.1.2.2) * u * (Matrix.single p.2.1 p.2.2.1 (β p.2.2.2))ᵀ) := by
  refine (congrArg₂ (fun A B => l (A * u * Bᵀ)) (expand β M) (expand β N)).trans ?_
  rw [Fintype.sum_prod_type (α₁ := Fin n × Fin n × ι) (α₂ := Fin d × Fin d × ι), Matrix.sum_mul, Matrix.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.transpose_sum, Matrix.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem bd_bilin {A ι : Type} [CommRing A] [Algebra (AF F) A] [Fintype ι] (β : Module.Basis ι (AF F) A) {n d : ℕ}
    (e : Matrix (Fin n) (Fin d) A ≃ₗ[AF F] Pt F κ) : ∃ (m₀ : ℕ) (K : ℝ), 1 ≤ m₀ ∧ 0 ≤ K ∧
      ∀ (M : Matrix (Fin n) (Fin n) A) (N : Matrix (Fin d) (Fin d) A) (s : Pt F κ →ₗ[AF F] Pt F κ) (a b : ℕ) (x y : ℝ),
        0 ≤ x → 0 ≤ y → (∀ w, s w = e (M * e.symm w * Nᵀ)) → (∀ i j k, Sz a x (β.repr (M i j) k)) →
        (∀ i j k, Sz b y (β.repr (N i j) k)) → Bd s (a * b * m₀) (K * (x * y)) := by
  let l : κ ⊕ κ → Matrix (Fin n) (Fin d) A →ₗ[AF F] AF F := fun i =>
    LinearMap.proj i ∘ₗ (crd F κ).toLinearMap ∘ₗ e.toLinearMap
  let u : κ ⊕ κ → Matrix (Fin n) (Fin d) A := fun j => e.symm ((crd F κ).symm (Pi.single j 1))
  obtain ⟨m₀, c₀, hm₀, hc₀, h₀⟩ := exists_sz (F := F)
    fun q : ((κ ⊕ κ) × (κ ⊕ κ)) × ((Fin n × Fin n × ι) × (Fin d × Fin d × ι)) =>
      l q.1.1 (Matrix.single q.2.1.1 q.2.1.2.1 (β q.2.1.2.2) * u q.1.2 *
        (Matrix.single q.2.2.1 q.2.2.2.1 (β q.2.2.2.2))ᵀ)
  refine ⟨m₀, Fintype.card (κ ⊕ κ) * (Fintype.card ((Fin n × Fin n × ι) × (Fin d × Fin d × ι)) * c₀), hm₀,
    by positivity, fun M N s a b x y hx hy hs hA hB => ?_⟩
  have hbd : Bd s (a * b * m₀) _ := bd_of_sz (c := Fintype.card ((Fin n × Fin n × ι) × (Fin d × Fin d × ι)) *
      (x * y * c₀)) (by positivity) fun i j => by
    have e' : crd F κ (s ((crd F κ).symm (Pi.single j 1))) i = l i (M * u j * Nᵀ) := by rw [hs]; rfl
    rw [e', bilin β (l i) (u j) M N]
    exact Sz.sum fun p => ((hA _ _ _).mul (hB _ _ _)).mul (h₀ ((i, j), p))
  convert hbd using 1
  ring

end PositivityTheory.ThKF0.Grow.Ht

namespace PositivityTheory.ThKF0.Grow

open scoped Matrix NNReal ENNReal Classical TensorProduct
open NumberField IsDedekindDomain Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Ht

theorem htBd : HtBd := by
  intro F E _ _ _ _ _ σ n d X W M
  obtain ⟨ι, _, β, C, hC, hβ⟩ := exists_entries F E
  obtain ⟨m₀, K, hm₀, hK, h₀⟩ := bd_bilin β M.co.e
  refine ⟨m₀ + K * C * C, by positivity, fun g h => ?_⟩
  obtain ⟨a, ha, ha', hA⟩ := hβ n (g⁻¹).1
  obtain ⟨b, hb, hb', hB⟩ := hβ d (h⁻¹).1
  have eg : heightGL F (g⁻¹).1 = ht g := heightGL_inv F g.1
  have eh : heightGL F (h⁻¹).1 = ht h := heightGL_inv F h.1
  rw [eg] at ha' hA
  rw [eh] at hb' hB
  have hbd := h₀ (mat g⁻¹) (mat h⁻¹) (sOf M g h) a b (C * ht g) (C * ht h) (mul_nonneg hC (ht g).2)
    (mul_nonneg hC (ht h).2) (fun _ => rfl) hA hB
  have hx : (0 : ℝ) ≤ ht g := (ht g).2
  have hy : (0 : ℝ) ≤ ht h := (ht h).2
  generalize (ht g : ℝ) = x at *
  generalize (ht h : ℝ) = y at *
  have h0 : 0 ≤ x * y := mul_nonneg hx hy
  have h1 : 0 ≤ K * C * C * (x * y) := by positivity
  refine ⟨a * b * m₀, Nat.mul_pos (Nat.mul_pos ha hb) hm₀, ?_, hbd.fin, fun w => ?_⟩
  · push_cast
    have : (a : ℝ) * b ≤ x * y := mul_le_mul ha' hb' (Nat.cast_nonneg _) hx
    nlinarith [mul_le_mul_of_nonneg_right this (Nat.cast_nonneg (α := ℝ) m₀)]
  · obtain ⟨w', e, hw'⟩ := hbd.inf w
    refine ⟨w', e, hw'.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))⟩
    have : (0 : ℝ) ≤ m₀ * (x * y) := by positivity
    nlinarith

end PositivityTheory.ThKF0.Grow
