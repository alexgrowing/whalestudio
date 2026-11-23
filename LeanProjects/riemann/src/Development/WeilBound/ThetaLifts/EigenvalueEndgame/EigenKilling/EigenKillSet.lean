import Development.WeilBound.ThetaLifts.SmallCones.SoDefs
import Development.WeilBound.ThetaLifts.SmallCones.ExpAlg
import Development.WeilBound.ThetaLifts.SmallCones.FourierUniq
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.SoStatement
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDict
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfSurj
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.ConeIntegralFactorisation

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Comp.SoL

open Filter Topology NumberField IsDedekindDomain Matrix GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.CompanionTheory.Ar.RT.Move GlobalTheory.LatVac PositivityTheory.KCo GlobalTheory.ThK PositivityTheory.ThKCT
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField Classical.propDecidable

section

theorem kill_set {X : Type} [TopologicalSpace X] (N : Submodule ℂ (X → ℂ)) (Z : Set X)
    (h : ∀ Y ∉ Z, ∃ (m : X → ℂ) (c : ℂ), IsLocallyConstant m ∧ m Y ≠ c ∧ ∀ Φ ∈ SB X, (fun y => (m y - c) * Φ y) ∈ N) :
    ∀ Φ ∈ SB X, (∀ Y ∈ Z, Φ Y = 0) → Φ ∈ N := by
  classical
  choose! m c hm hne hN using h
  have key : ∀ s : Finset X, (∀ Y ∈ s, Y ∉ Z) → ∀ Φ ∈ SB X, (∀ y, Φ y ≠ 0 → ∃ Y ∈ s, m Y y = m Y Y) → Φ ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _ Φ _ h0
      have : Φ = 0 := funext fun y => by by_contra e; simpa using h0 y e
      rw [this]; exact zero_mem _
    | insert Y s hY ih =>
      intro hs Φ hΦ h0
      have hY1 := hs Y (Finset.mem_insert_self _ _)
      have hU : IsClopen {y | m Y y = m Y Y} := (hm Y hY1).isClopen_fiber _
      have h1 := hN Y hY1 _ (Submodule.smul_mem _ (m Y Y - c Y)⁻¹ (indicator_mem hU hΦ))
      have h2 := ih (fun Z hZ => hs Z (Finset.mem_insert_of_mem hZ)) _ (indicator_mem hU.compl hΦ) fun y hy => by
        have hy1 : y ∈ {y | m Y y = m Y Y}ᶜ := Set.mem_of_indicator_ne_zero hy
        rw [Set.indicator_of_mem hy1] at hy
        obtain ⟨Z, hZ, e⟩ := h0 y hy
        rcases Finset.mem_insert.1 hZ with rfl | hZ
        · exact (hy1 e).elim
        · exact ⟨Z, hZ, e⟩
      convert add_mem h1 h2 using 1
      funext y
      by_cases hy : y ∈ {y | m Y y = m Y Y}
      · have e : m Y y = m Y Y := hy
        have : y ∉ {y | m Y y = m Y Y}ᶜ := fun h => h hy
        simp only [Pi.add_apply, Pi.smul_apply, Set.indicator_of_mem hy, Set.indicator_of_notMem this, e, smul_eq_mul]
        rw [mul_inv_cancel_left₀ (sub_ne_zero.2 (hne Y hY1)), add_zero]
      · simp [Set.indicator_of_notMem hy, Set.indicator_of_mem (show y ∈ {y | m Y y = m Y Y}ᶜ from hy)]
  intro Φ hΦ h1
  have hK : IsCompact {y | Φ y ≠ 0} :=
    hΦ.2.isCompact.of_isClosed_subset (hΦ.1.isClopen_fiber 0).compl.1 subset_closure
  obtain ⟨s, hs, hc⟩ := hK.elim_nhds_subcover (fun Y => {y | m Y y = m Y Y}) fun Y hY =>
    ((hm Y fun e => hY (h1 Y e)).isOpen_fiber _).mem_nhds rfl
  refine key s (fun Y hY e => hs Y hY (h1 Y e)) Φ hΦ fun y hy => ?_
  simpa using hc hy

theorem rank_ne_iff {k : Type} [Field k] {n d : ℕ} (C : Matrix (Fin n) (Fin d) k) : C.rank ≠ n ↔ ∃ p, p ≠ 0 ∧ p ᵥ* C = 0 := by
  have h := LinearMap.finrank_range_add_finrank_ker Cᵀ.mulVecLin
  rw [Module.finrank_fin_fun, ← Matrix.rank, Matrix.rank_transpose] at h
  have : C.rank ≠ n ↔ LinearMap.ker Cᵀ.mulVecLin ≠ ⊥ := by
    rw [Ne, Ne, ← Submodule.finrank_eq_zero]
    omega
  rw [this, Submodule.ne_bot_iff]
  refine exists_congr fun p => ?_
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose, and_comm]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {ψ : AddChar (AF F) ℂ}

theorem eigen_kill_set (h : IsCMExt F E σ) (hψ : IsStd ψ) (hX : X.J.det ≠ 0) (hW : W.J.det ≠ 0) {t : E →ₐ[F] Fv F v} {ι}
    (hι : M.IsLinBar ψ t 1 1 ι) (l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ)
    (A : Set (Matrix (Fin n) (Fin d) (AE F E) × ℂ)) (hA : ∀ a ∈ A, At (evFin F v) a.1 ∧ a.1.map (piW (t.comp σ)) = 0)
    (hl : ∀ a ∈ A, ∀ φ ∈ SB _, l (locRho M ψ v a.1 φ) = a.2 * l φ) {φ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v))
    (hz : ∀ x, At (evFin F v) x → x.map (piW t) = 0 → (∀ a ∈ A, ψ (sy σ X W x a.1) = a.2) → ι φ (coB σ X W t x) = 0) :
    l φ = 0 := by
  choose xo a1 a2 a3 using exists_coB h t hX hW
  have hb := hι.bij
  have key := kill_set ((SB _ ⊓ LinearMap.ker l).map ι) {Y | ∀ a ∈ A, ψ (sy σ X W (xo Y) a.1) = a.2} (fun Y hY => ?_) _ (hb.1 hφ)
    fun Y hY => by rw [← a3 Y]; exact hz _ (a1 Y) (a2 Y) hY
  · obtain ⟨φ', h', e⟩ := key
    rw [← hb.2.1 h'.1 hφ e]
    exact h'.2
  simp only [Set.mem_setOf_eq, not_forall] at hY
  obtain ⟨⟨u, c⟩, ha, hne⟩ := hY
  obtain ⟨hu, h1⟩ := hA _ ha
  let m : Matrix (Fin n) (Fin d) (Fv F v) → ℂ := fun y => ψ (sy σ X W (xo y) u)
  have hm : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ι (locRho M ψ v u φ) = fun y => m y * ι φ y := fun φ hφ => funext fun y => by
    have := mult' M hψ hι hu h1 (a1 y) (a2 y) hφ
    rwa [a3] at this
  have : T2Space (Matrix (Fin n) (Fin d) (Fv F v)) := inferInstanceAs (T2Space (Fin n → Fin d → Fv F v))
  have : LocallyCompactSpace (Matrix (Fin n) (Fin d) (Fv F v)) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin d → Fv F v))
  have : TotallyDisconnectedSpace (Matrix (Fin n) (Fin d) (Fv F v)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin d → Fv F v))
  refine ⟨m, c, lc_of_mul m fun Φ hΦ => ?_, hne, fun Φ hΦ => ?_⟩
  · obtain ⟨φ', h', rfl⟩ := hb.2.2 hΦ
    rw [← hm φ' h']
    exact hb.1 (locRho_mem M hψ u h')
  · obtain ⟨φ', h', rfl⟩ := hb.2.2 hΦ
    refine ⟨locRho M ψ v u φ' - c • φ', ⟨sub_mem (locRho_mem M hψ u h') (Submodule.smul_mem _ _ h'), ?_⟩, ?_⟩
    · change l _ = 0
      rw [map_sub, map_smul, hl _ ha φ' h', smul_eq_mul, sub_self]
    · rw [map_sub, map_smul, hm φ' h']
      funext y
      simp [sub_mul]

include M in
theorem sy_smul (x u : Matrix (Fin n) (Fin d) (AE F E)) (a : AF F) : sy σ X W x (a • u) = a * sy σ X W x u := by
  simp only [sy, M.co.form, map_smul, Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_dotProduct, smul_eq_mul, mul_sub]

theorem map_vec (π : AE F E →+* Fv F v) (t : E → Fv F v) (ht : ∀ x, π (inclR (F := F) (AF F) x) = t x) (ε : AE F E) (p : Fin n → E)
    (q : Fin d → E) : (ε • incM F (vecMulVec p q)).map π = π ε • vecMulVec (fun i => t (p i)) fun j => t (q j) := by
  ext i j
  simp [incM, vecMulVec_apply, ht]

theorem trace_vec {k : Type} [Field k] (C : Matrix (Fin n) (Fin d) k) (p : Fin n → k) (q : Fin d → k) :
    (Cᵀ * vecMulVec p q).trace = p ⬝ᵥ C *ᵥ q := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem piW_inc (t : E →ₐ[F] Fv F v) (x : E) : piW t (inclR (F := F) (AF F) x) = t x := by
  change evFin F v 1 * t x = t x
  rw [map_one, one_mul]

theorem at_lift (c : Fv F v) (u : Matrix (Fin n) (Fin d) (AE F E)) : At (evFin F v) (liftV v c • u) := fun a ha => by
  rw [smul_smul, ← smul_eq_mul, at_liftV v c a ha, zero_smul]

end

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E}

theorem sig_sig (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

theorem form_swap (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E} (ε : E) (h : ∀ i j, σ (J j i) = ε * J i j) (x y : Fin n → E) :
    σ (form σ J x y) = ε * form σ J y x := by
  simp only [form, dotProduct, mulVec, map_sum, map_mul, hσ, h, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem plane_span {H : Plane E n n₁} {i₀ i₁ : ℕ} (h : H.IsAdapted σ B X X₁ i₀ i₁) (hL : X.L.IsLattice E) (z : Fin n → E) :
    ∃ (s t : E) (u : Fin n₁ → E), z = s • H.x + H.ι *ᵥ u + t • H.y := by
  have hz : z ∈ Submodule.span E (X.L : Set (Fin n → E)) := by rw [hL.span_eq_top]; trivial
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨s, t, u, -, -, -, e⟩ := h.split z hz
    exact ⟨s, t, u, e⟩
  | zero => exact ⟨0, 0, 0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨s, t, u, rfl⟩ := ha
    obtain ⟨s', t', u', rfl⟩ := hb
    exact ⟨s + s', t + t', u + u', by rw [add_smul, add_smul, mulVec_add]; abel⟩
  | smul c a _ ha =>
    obtain ⟨s, t, u, rfl⟩ := ha
    exact ⟨c * s, c * t, c • u, by rw [mulVec_smul, mul_smul, mul_smul, smul_add, smul_add]⟩

theorem incV_mulVec (ι : Matrix (Fin n) (Fin n₁) E) (p : Fin n₁ → E) : incV F (ι *ᵥ p) = incM F ι *ᵥ incV F p := by
  funext i
  simp [incV, incM, mulVec, dotProduct]

theorem vec_right (a : AF F) (ε : AE F E) (ι : Matrix (Fin n) (Fin n₁) E) (p : Fin n₁ → E) (q : Fin d → E) :
    a • ε • incM F (vecMulVec (ι *ᵥ p) q) = vecMulVec (incM F ι *ᵥ (a • ε • incV F p)) (incV F q) := by
  rw [mulVec_smul, mulVec_smul, ← incV_mulVec]
  ext i j
  simp only [incM, incV, Matrix.smul_apply, map_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, map_mul, smul_mul_assoc,
    mul_assoc]

theorem vec_mid (a : AF F) (ε : AE F E) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (p : Fin n₁ → E)
    (q : Fin d₁ → E) : a • ε • incM F (vecMulVec (ι *ᵥ p) (ι' *ᵥ q)) =
      incM F ι * (a • ε • incM F (vecMulVec p q)) * (incM F ι')ᵀ := by
  have e : ∀ {a b : ℕ} (p : Fin a → E) (q : Fin b → E), incM F (vecMulVec p q) = vecMulVec (incV F p) (incV F q) := fun p q => by
    ext i j
    simp [incM, incV, vecMulVec_apply]
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, e, e, incV_mulVec, incV_mulVec, mul_vecMulVec,
    vecMulVec_mul, vecMul_transpose]

theorem map_mulVec' (t : E →ₐ[F] Fv F v) (ι : Matrix (Fin n) (Fin n₁) E) (p : Fin n₁ → E) :
    (fun i => t ((ι *ᵥ p) i)) = ι.map t *ᵥ fun i => t (p i) := by
  funext i
  simp [mulVec, dotProduct]

theorem map_single (t : E →ₐ[F] Fv F v) (j : Fin n) : (fun i => t ((Pi.single j 1 : Fin n → E) i)) = Pi.single j 1 := by
  funext i
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem det_ne_of_map (B : Base F E) (w : InfinitePlace F) {m : ℕ} (J : Matrix (Fin m) (Fin m) E)
    (hJ : (J.map (B.emb w).1).det ≠ 0) : J.det ≠ 0 := fun h0 =>
  hJ (((RingHom.map_det _ J).symm.trans (congrArg _ h0)).trans (map_zero _))

theorem det_herm {B : Base F E} {n r s : ℕ} {X : Spc F E n} (h : X.IsHerm σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact det_ne_of_map B w _ (GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (h.sig w))

theorem det_skew {B : Base F E} {n r s : ℕ} {X : Spc F E n} (h : X.IsSkew σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact det_ne_of_map B w _ fun h0 =>
    GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (h.sig w) (by rw [Matrix.det_smul, h0, mul_zero])

theorem linEx_of : LinEx := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW v t
  obtain ⟨⟨sec, h⟩, -⟩ := section_statement F E σ hB.cm v t
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have uu : ∀ {m : ℕ} {J : Matrix (Fin m) (Fin m) E}, IsUnit J.det → IsUnit ((incM F J).map (piW t)) := fun {m J} hJ => by
    rw [incM_map h]
    exact ((Matrix.isUnit_iff_isUnit_det J).2 hJ).map (t : E →+* Fv F v).mapMatrix
  have hG : Grams σ t (incM F X.J) (incM F W.J) := ⟨uu (det_herm hX).isUnit,
    uu (det_skew hW).isUnit, 1, one_mul _, Matrix.ext fun i j => by
      simp [incM, (h.inc _).1, (h.inc _).2, hX.herm], Matrix.ext fun i j => by simp [incM, (h.inc _).1, (h.inc _).2, hW.skew]⟩
  obtain ⟨ι₀, hι₀⟩ := exists_lm model_existence adjoint_statement hB.std h hG M.co
  refine ⟨⟨_, linBar_of_lm adjoint_statement action_uniqueness h hG hι₀⟩, fun x u hx h0 => ?_⟩
  rw [sy, symp_eq h hG hx, ev_sgl, coord_snd.2 h0, dotProduct_zero, sub_zero]
  simp only [coord, dot_ofM, incM_map h, Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]

end PositivityTheory.ThKEnd.Comp.SoL

namespace PositivityTheory.ThKEnd.Comp.SoL

open GlobalTheory.WeilM GlobalTheory.SplitFlip Matrix ValuativeRel Topology PositivityTheory.KCo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d d₁ : ℕ}

def Sup (S : Finset (Fin n)) (Φ : Matrix (Fin n) (Fin d) k → ℂ) : Prop :=
  Φ ∈ SB (Matrix (Fin n) (Fin d) k) ∧ ∀ Y : Matrix (Fin n) (Fin d) k, ¬ LinearIndepOn k Y S → Φ Y = 0

variable {S : Finset (Fin n)} {i : Fin n}

theorem mv_N (hi : i ∉ S) {ν α : kˣ →* ℂˣ} {N : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ)}
    (hN : ∀ g, ∀ Φ, Sup S Φ → omB ν α g 1 Φ - Φ ∈ N) (x : kˣ) (a : S → k) {Φ : Matrix (Fin n) (Fin d) k → ℂ} (hΦ : Sup S Φ) :
    (((ν x : ℂ) * apow x ((d : ℂ) / 2)) • fun Y => Φ (mv S i x a Y)) ∈ SB (Matrix (Fin n) (Fin d) k) ∧
      (((ν x : ℂ) * apow x ((d : ℂ) / 2)) • fun Y => Φ (mv S i x a Y)) - Φ ∈ N := by
  obtain ⟨g, hg⟩ := exists_gl (d := d) hi ν α x a
  rw [← hg]
  exact ⟨omB_mem_SB ν α g 1 hΦ.1, hN g Φ hΦ⟩

theorem sum_N (hi : i ∉ S) {ν α : kˣ →* ℂˣ} {N : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ)}
    (hN : ∀ g, ∀ Φ, Sup S Φ → omB ν α g 1 Φ - Φ ∈ N) {Q : Type} [Fintype Q] (a : Q → S → k)
    {Φ : Matrix (Fin n) (Fin d) k → ℂ} (hΦ : Sup S Φ) :
    Sup S (fun Y => ∑ q, Φ (mv S i 1 (a q) Y)) ∧ (fun Y => ∑ q, Φ (mv S i 1 (a q) Y)) - (Fintype.card Q : ℂ) • Φ ∈ N := by
  have h := fun q => mv_N hi hN 1 (a q) hΦ
  simp only [map_one, Units.val_one, apow_one, mul_one, one_smul] at h
  have e : (fun Y => ∑ q, Φ (mv S i 1 (a q) Y)) = ∑ q, fun Y => Φ (mv S i 1 (a q) Y) := by
    funext Y
    simp
  refine ⟨⟨e ▸ Submodule.sum_mem _ fun q _ => (h q).1, fun Y hY => Finset.sum_eq_zero fun q _ =>
    hΦ.2 _ fun h => hY (h.congr fun s hs => mv_row hi 1 (a q) Y ⟨s, hs⟩)⟩, ?_⟩
  rw [e]
  convert Submodule.sum_mem _ fun q (_ : q ∈ Finset.univ) => (h q).2 using 1
  simp [Finset.sum_sub_distrib, Nat.cast_smul_eq_nsmul]

theorem stepN (hi : i ∉ S) {ν α : kˣ →* ℂˣ} (hν : USm ν) (h1 : ν ≠ 1) {N : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ)}
    (hN : ∀ g, ∀ Φ, Sup S Φ → omB ν α g 1 Φ - Φ ∈ N) {Φ : Matrix (Fin n) (Fin d) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (Fin n) (Fin d) k)) (h0 : ∀ Y : Matrix (Fin n) (Fin d) k, ¬ LinearIndepOn k Y S → Φ Y = 0) :
    ∃ Ψ ∈ SB (Matrix (Fin n) (Fin d) k), (∀ Y : Matrix (Fin n) (Fin d) k, ¬ LinearIndepOn k Y (insert i S : Finset _) → Ψ Y = 0) ∧ Φ - Ψ ∈ N := by
  obtain ⟨x, hx, hx1⟩ : ∃ x : kˣ, ν x ≠ 1 ∧ valuation k (x : k) ≤ 1 := by
    obtain ⟨x, hx⟩ := DFunLike.ne_iff.1 h1
    rcases le_total (valuation k (x : k)) 1 with h | h
    · exact ⟨x, hx, h⟩
    · exact ⟨x⁻¹, by simpa using hx, by simpa using inv_le_one_of_one_le₀ h⟩
  obtain ⟨c₀, hc₀, hinv⟩ := exists_inv hi hΦ
  have hK : IsCompact (Function.support Φ) := hΦ.2.isCompact.of_isClosed_subset
    (hΦ.1.isOpen_fiber 0).isClosed_compl (subset_tsupport _)
  obtain ⟨L, hL, hLb⟩ := exists_bound (i := i) hK fun Y hY => by_contra fun h => hY (h0 Y h)
  obtain ⟨c, hc, hLc⟩ := bx_large hL
  have := bx_finite (S := S) c hc₀
  have := bx_finite (S := S) ((x⁻¹ : kˣ) * c) hc
  have := Fintype.ofFinite (bx S c ⧸ (bx S c₀).addSubgroupOf (bx S c))
  have := Fintype.ofFinite (bx S ((x⁻¹ : kˣ) * c) ⧸ (bx S c).addSubgroupOf (bx S ((x⁻¹ : kˣ) * c)))
  obtain ⟨s1, a1⟩ := sum_N hi hN (fun q : bx S c ⧸ (bx S c₀).addSubgroupOf (bx S c) => (q.out : S → k)) ⟨hΦ, h0⟩
  set Φ₁ := fun Y => ∑ q : bx S c ⧸ (bx S c₀).addSubgroupOf (bx S c), Φ (mv S i 1 (q.out : S → k) Y) with hΦ₁
  obtain ⟨s2, a2⟩ := sum_N hi hN
    (fun q : bx S ((x⁻¹ : kˣ) * c) ⧸ (bx S c).addSubgroupOf (bx S ((x⁻¹ : kˣ) * c)) => (q.out : S → k)) s1
  obtain ⟨s3, a3⟩ := mv_N hi hN x 0 s1
  set N₁ : ℂ := ((Fintype.card (bx S c ⧸ (bx S c₀).addSubgroupOf (bx S c)) : ℕ) : ℂ) with hN₁
  set N₂ : ℕ := Fintype.card (bx S ((x⁻¹ : kˣ) * c) ⧸ (bx S c).addSubgroupOf (bx S ((x⁻¹ : kˣ) * c))) with hN₂
  set z : ℂ := (ν x : ℂ) * apow x ((d : ℂ) / 2) with hz
  have n1 : N₁ ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have n2 : z * N₂ - 1 ≠ 0 := fun e => hx (by
    have hp : 0 ≤ GlobalTheory.SplitWeil.nabs k x := NNReal.coe_nonneg _
    have e1 : apow x ((d : ℂ) / 2) = ((GlobalTheory.SplitWeil.nabs k x ^ ((d : ℝ) / 2) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hp]; simp [apow]
    set r : ℝ := GlobalTheory.SplitWeil.nabs k x ^ ((d : ℝ) / 2) * N₂ with hr
    have e2 : (ν x : ℂ) * r = 1 := by rw [← sub_eq_zero.1 e, hz, e1, hr]; push_cast; ring
    have e3 : r = 1 := by
      have := congrArg norm e2
      rwa [norm_mul, hν.1, one_mul, norm_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at this
    exact Units.ext (by simpa [e3] using e2))
  refine ⟨((z * N₂ - 1) * N₁)⁻¹ • (z • _ - _), Submodule.smul_mem _ _ (sub_mem (Submodule.smul_mem _ z s2.1) s3), fun Y hY => ?_, ?_⟩
  · rw [Finset.coe_insert] at hY
    replace hY := fun h => hY ((linearIndepOn_insert (K := k) (f := (Y : Fin n → Fin d → k)) (mt Finset.mem_coe.1 hi)).2 h)
    rw [imp_false, not_and_or, not_not] at hY
    suffices h : ∑ q : bx S ((x⁻¹ : kˣ) * c) ⧸ (bx S c).addSubgroupOf (bx S ((x⁻¹ : kˣ) * c)), Φ₁ (mv S i 1 (q.out : S → k) Y) =
        Φ₁ (mv S i x 0 Y) by simp [h]
    rcases hY with hY | hY
    · have z0 : ∀ y a, Φ (mv S i y a Y) = 0 := fun y a => h0 _ fun h => hY (h.congr fun s hs => mv_row hi y a Y ⟨s, hs⟩)
      simp [hΦ₁, mv_mv hi, z0]
    · obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun k).1
        ((congrArg (Submodule.span k) (Set.image_eq_range (Y : Fin n → Fin d → k) S)).le hY)
      have eY : Y = mv S i 0 b Y := by
        rw [mv, zero_smul, zero_add, show cmb S b Y = Y i from hb, updateRow_eq_self]
      let f : (S → k) → ℂ := fun a => Φ (mv S i 0 a Y)
      let f₁ : (S → k) → ℂ := fun a => Φ₁ (mv S i 0 a Y)
      have e1 : ∀ a, f₁ a = ∑ q : bx S c ⧸ (bx S c₀).addSubgroupOf (bx S c), f (a + (q.out : bx S c)) := fun a => by
        simp [f₁, f, hΦ₁, mv_mv hi]
      have i0 : ∀ a ∈ bx S c₀, ∀ b, f (b + a) = f b := fun a ha b => by
        simpa [mv_mv hi] using hinv a ha (mv S i 0 b Y)
      have o0 : ∀ a ∉ bx S c, f a = 0 := fun a ha => by_contra fun h => ha (hLc (hLb _ h a (by
        rw [show cmb S a (mv S i 0 a Y) = cmb S a Y from Finset.sum_congr rfl fun s _ => by rw [mv_row hi]]
        simp [mv])))
      have i1 : ∀ a ∈ bx S c, ∀ b, f₁ (b + a) = f₁ b := fun a ha b => by rw [e1, e1, avg_inv _ _ i0 ha]
      have o1 : ∀ a ∉ bx S c, f₁ a = 0 := fun a ha => by rw [e1, avg_off _ _ o0 ha]
      have hm : ∀ a : S → k, a ∈ bx S ((x⁻¹ : kˣ) * c) ↔ (x : k) • a ∈ bx S c := fun a => forall_congr' fun s => by
        have : 0 < valuation k (x : k) := zero_lt_iff.2 (by simp)
        simp [le_inv_mul_iff₀ this]
      rw [eY]
      simp only [mv_mv hi, one_smul, mul_zero, add_zero]
      change ∑ q : bx S ((x⁻¹ : kˣ) * c) ⧸ (bx S c).addSubgroupOf (bx S ((x⁻¹ : kˣ) * c)), f₁ (b + (q.out : bx S _)) = f₁ ((x : k) • b)
      by_cases hbm : b ∈ bx S ((x⁻¹ : kˣ) * c)
      · have := avg_inv (bx S c) _ i1 hbm 0
        rw [zero_add] at this
        rw [this, avg_zero _ _ i1 o1, ← i1 _ ((hm b).1 hbm) 0, zero_add]
      · rw [o1 _ fun h => hbm ((hm b).2 h)]
        refine avg_off _ _ (fun a ha => o1 a fun h => ha ((hm a).2 fun s => ?_)) hbm
        simpa using (mul_le_of_le_one_left' hx1).trans (h s)
  · have := Submodule.smul_mem _ (-((z * N₂ - 1) * N₁)⁻¹)
      (add_mem (sub_mem (Submodule.smul_mem _ z a2) a3) (Submodule.smul_mem _ (z * N₂ - 1) a1))
    convert this using 1
    ext Y
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

theorem indep_iff (Y : Matrix (Fin n) (Fin d) k) :
    LinearIndepOn k Y S ↔ ∀ p : Fin n → k, (∀ j ∉ S, p j = 0) → p ᵥ* Y = 0 → p = 0 := by
  classical
  refine Iff.trans (linearIndepOn_finset_iff (v := (Y : Fin n → Fin d → k))) ⟨fun h p h0 hp => funext fun j => ?_, fun h f hf j hj => ?_⟩
  · by_cases hj : j ∈ S
    · refine h p ?_ j hj
      exact (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => by rw [h0 j hj, zero_smul]).trans
        ((vecMul_eq_sum p Y).symm.trans hp)
    · exact h0 j hj
  · have := h (fun j => if j ∈ S then f j else 0) (fun j hj => if_neg hj) ((vecMul_eq_sum _ Y).trans (Eq.trans (by
      simp only [ite_smul, zero_smul, Finset.sum_ite_mem, Finset.univ_inter]) hf))
    simpa [hj] using congrFun this j

theorem indep_nhds {Y₀ : Matrix (Fin n) (Fin d) k} (h : LinearIndepOn k Y₀ S) : {Y : Matrix (Fin n) (Fin d) k | LinearIndepOn k Y S} ∈ 𝓝 Y₀ := by
  classical
  let R : Matrix (Fin n) (Fin d) k → Matrix S (Fin d) k := fun Y => Y.submatrix Subtype.val id
  have hR : Continuous R := continuous_id.matrix_submatrix _ _
  have hinj : Function.Injective (R Y₀).vecMulLinear := vecMul_injective_iff.2 h
  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 hinj)
  let B : Matrix (Fin d) S k := (LinearMap.toMatrix' l)ᵀ
  have hB : R Y₀ * B = 1 := by
    ext s s'
    have := congrFun (LinearMap.congr_fun hl (Pi.single s 1)) s'
    rw [LinearMap.comp_apply, ← LinearMap.toMatrix'_mulVec, vecMulLinear_apply, single_one_vecMul] at this
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [mulVec, dotProduct, B, mul_comm, Pi.single_apply, eq_comm] using this
  have hc : Continuous fun Y => (R Y * B).det := (hR.matrix_mul continuous_const).matrix_det
  have hW : {Y | (R Y * B).det ≠ 0} ∈ 𝓝 Y₀ := (isOpen_ne_fun hc continuous_const).mem_nhds (by simp [hB])
  refine Filter.mem_of_superset hW fun Y hY => ?_
  have : Function.Injective (R Y).vecMulLinear := (injective_iff_map_eq_zero _).2 fun p hp =>
    eq_zero_of_vecMul_eq_zero hY (by rw [← vecMul_vecMul, show p ᵥ* R Y = 0 from hp, zero_vecMul])
  exact vecMul_injective_iff.1 this

theorem corank_one {ν α : kˣ →* ℂˣ} (hν : USm ν) (h1 : ν ≠ 1) {N : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ)}
    (hN : ∀ i g, ∀ Φ, Sup (Finset.univ.erase i) Φ → omB ν α g 1 Φ - Φ ∈ N) {Φ : Matrix (Fin n) (Fin d) k → ℂ} (hΦ : Φ ∈ SB _)
    (h0 : ∀ Y : Matrix (Fin n) (Fin d) k, (∀ i, ¬ LinearIndepOn k Y (Finset.univ.erase i : Finset (Fin n))) → Φ Y = 0) :
    ∃ Ψ, Full Ψ ∧ Φ - Ψ ∈ N := by
  classical
  let Fu : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ) :=
    { carrier := {Ψ | Full Ψ}
      zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩
      add_mem' := fun a b => ⟨add_mem a.1 b.1, fun Y hY => by simp [a.2 Y hY, b.2 Y hY]⟩
      smul_mem' := fun c _ a => ⟨Submodule.smul_mem _ c a.1, fun Y hY => by simp [a.2 Y hY]⟩ }
  have : T2Space (Matrix (Fin n) (Fin d) k) := inferInstanceAs (T2Space (Fin n → Fin d → k))
  have : LocallyCompactSpace (Matrix (Fin n) (Fin d) k) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin d → k))
  have : TotallyDisconnectedSpace (Matrix (Fin n) (Fin d) k) := inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin d → k))
  have key := kill_set (Fu ⊔ N) {Y | ∀ i, ¬ LinearIndepOn k Y (Finset.univ.erase i : Finset (Fin n))}
    (fun Y hY => ?_) Φ hΦ h0
  · obtain ⟨Ψ, hΨ, u, hu, rfl⟩ := Submodule.mem_sup.1 key
    exact ⟨Ψ, hΨ, by simpa using hu⟩
  simp only [Set.mem_setOf_eq, not_forall, not_not] at hY
  obtain ⟨i, hi⟩ := hY
  obtain ⟨V, hV, hYV, hVU⟩ := loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 (indep_nhds hi)
  refine ⟨V.indicator 1, 0, (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hV).2, by simp [hYV], fun Ψ hΨ => ?_⟩
  have e : (fun y => (V.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) y - 0) * Ψ y) = V.indicator Ψ := by
    funext y; by_cases hy : y ∈ V <;> simp [hy]
  rw [e]
  obtain ⟨Ψ', a1, a2, a3⟩ := stepN (Finset.notMem_erase i _) hν h1 (hN i) (indicator_mem hV hΨ)
    fun Y hY => Set.indicator_of_notMem (fun h => hY (hVU h)) _
  refine Submodule.mem_sup.2 ⟨Ψ', ⟨a1, fun Y hY => a2 Y fun h => hY ?_⟩, _, a3, by abel⟩
  rw [Finset.insert_erase (Finset.mem_univ i), Finset.coe_univ] at h
  simpa using LinearIndependent.rank_matrix (M := Y) (linearIndepOn_univ_iff.1 h)

theorem rank_ne (hn : 1 ≤ n) {Y₁ : Matrix (Fin n) (Fin d₁) k} (h : ∀ i, ¬ LinearIndepOn k Y₁ (Finset.univ.erase i : Finset (Fin n)))
    (κ : Matrix (Fin d₁) (Fin d) k) (y : Fin n → k) (ρ : Fin d → k) : (Y₁ * κ + vecMulVec y ρ).rank ≠ n := by
  simp only [indep_iff, not_forall] at h
  have e : ∀ p : Fin n → k, p ᵥ* Y₁ = 0 → p ᵥ* (Y₁ * κ + vecMulVec y ρ) = (p ⬝ᵥ y) • ρ := fun p hp => by
    rw [vecMul_add, ← vecMul_vecMul, hp, zero_vecMul, zero_add, vecMul_vecMulVec]
  obtain ⟨p₀, -, a0, b0⟩ := h ⟨0, hn⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.1 b0
  obtain ⟨p₁, c1, a1, b1⟩ := h i
  rw [rank_ne_iff]
  by_cases hy : p₁ ⬝ᵥ y = 0
  · exact ⟨p₁, b1, by rw [e _ a1, hy, zero_smul]⟩
  refine ⟨(p₁ ⬝ᵥ y) • p₀ - (p₀ ⬝ᵥ y) • p₁, fun h0 => ?_, ?_⟩
  · have := congrFun h0 i
    simp only [Pi.sub_apply, Pi.smul_apply, c1 i (Finset.notMem_erase i _), smul_eq_mul, mul_zero, sub_zero] at this
    exact mul_ne_zero hy hi this
  · rw [e _ (by rw [sub_vecMul, smul_vecMul, smul_vecMul, a0, a1]; simp)]
    simp [mul_comm]

theorem sb_shift {Φ : Matrix (Fin n) (Fin d) k → ℂ} (h : Φ ∈ SB _) (Z : Matrix (Fin n) (Fin d) k) : (fun Y => Φ (Y + Z)) ∈ SB _ :=
  ⟨h.1.comp_continuous (continuous_id.add continuous_const), h.2.comp_homeomorph (Homeomorph.addRight Z)⟩

theorem lift {A : Type} [AddCommGroup A] [Module ℂ A] {SA : Submodule ℂ A} {ι : A →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)}
    {τ : A →ₗ[ℂ] (Matrix (Fin n) (Fin d₁) k → ℂ)} (hb : Set.BijOn ι (SA : Set A) (SB (Matrix (Fin n) (Fin d) k) : Set _))
    {κ : Matrix (Fin d₁) (Fin d) k} {ι' : Matrix (Fin d) (Fin d₁) k} {ρ y' : Fin d → k}
    (e1 : κ * ι' = 1) (e2 : ρ ᵥ* ι' = 0) (e3 : κ *ᵥ y' = 0) (e4 : ρ ⬝ᵥ y' = 1)
    (hkill : ∀ φ ∈ SA, ∀ Y₁, (∀ y, ι φ (Y₁ * κ + vecMulVec y ρ) = 0) → τ φ Y₁ = 0)
    (htr : ∀ Z₁ y, ∀ φ ∈ SA, ∀ φ' ∈ SA, (∀ Y, ι φ' Y = ι φ (Y + (Z₁ * κ + vecMulVec y ρ))) → ∀ Y₁, τ φ' Y₁ = τ φ (Y₁ + Z₁))
    (hne : ∃ φ ∈ SA, τ φ ≠ 0) {Ψ : Matrix (Fin n) (Fin d₁) k → ℂ} (hΨ : Sup (Finset.univ.erase i) Ψ) :
    ∃ φ ∈ SA, Full (ι φ) ∧ τ φ = Ψ := by
  classical
  have : T2Space (Matrix (Fin n) (Fin d) k) := inferInstanceAs (T2Space (Fin n → Fin d → k))
  obtain ⟨φ₁, h₁, hc⟩ : ∃ φ ∈ SA, τ φ 0 ≠ 0 := by
    obtain ⟨φ, hφ, h⟩ := hne
    obtain ⟨Y₀, hY₀⟩ := Function.ne_iff.1 h
    obtain ⟨φ', h', e⟩ := hb.2.2 (sb_shift (hb.1 hφ) (Y₀ * κ + vecMulVec 0 ρ))
    exact ⟨φ', h', by rw [htr Y₀ 0 φ hφ φ' h' (congrFun e), zero_add]; exact hY₀⟩
  have hΦ₁ : ι φ₁ ∈ SB _ := hb.1 h₁
  have hK : IsCompact (Function.support Ψ) := hΨ.1.2.isCompact.of_isClosed_subset
    (hΨ.1.1.isOpen_fiber 0).isClosed_compl (subset_tsupport _)
  obtain ⟨L, hL, hLb⟩ := exists_bound (i := i) hK fun Y hY => by_contra fun h => hY (hΨ.2 Y h)
  obtain ⟨c₀, -, hc₀⟩ := bx_large hL
  obtain ⟨c₂, h21, h22⟩ : ∃ c₂ : k, 1 ≤ valuation k c₂ ∧ valuation k c₀ ≤ valuation k c₂ := by
    rcases le_total (valuation k c₀) 1 with h | h
    · exact ⟨1, by simp, by simpa using h⟩
    · exact ⟨c₀, h, le_rfl⟩
  obtain ⟨c₁, hc₁0, hc₁⟩ := bx_large (hΦ₁.2.isCompact.image (f := fun W => W *ᵥ y') (continuous_id.matrix_mulVec continuous_const))
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  set N : k := r⁻¹ * (c₂ * c₁) with hN
  have hNv : valuation k (c₂ * c₁) < valuation k N := by
    have h0 : 0 < valuation k (c₂ * c₁) := by
      rw [map_mul]; exact mul_pos (lt_of_lt_of_le zero_lt_one h21) (zero_lt_iff.2 (by simpa using hc₁0))
    rw [hN, map_mul (valuation k) r⁻¹, map_inv₀]
    exact lt_mul_of_one_lt_left h0 ((one_lt_inv₀ (zero_lt_iff.2 (by simpa using hr))).2 hr1)
  let T : Matrix (Fin n) (Fin d) k → Matrix (Fin n) (Fin d) k := fun Y => Y + (-(Y * ι') * κ + vecMulVec (-Pi.single i N) ρ)
  have hT : Continuous T := continuous_id.add
    (((continuous_id.matrix_mul continuous_const).neg.matrix_mul continuous_const).add continuous_const)
  let Φ : Matrix (Fin n) (Fin d) k → ℂ := fun Y => (τ φ₁ 0)⁻¹ * Ψ (Y * ι') * ι φ₁ (T Y)
  have hΦ : Φ ∈ SB _ := by
    refine ⟨((IsLocallyConstant.const _).mul (hΨ.1.1.comp_continuous (continuous_id.matrix_mul continuous_const))).mul
      (hΦ₁.1.comp_continuous hT), HasCompactSupport.intro
      (K := (fun p : _ × _ => p.2 - (-p.1 * κ + vecMulVec (-Pi.single i N) ρ)) '' (tsupport Ψ ×ˢ tsupport (ι φ₁)))
      ((hΨ.1.2.isCompact.prod hΦ₁.2.isCompact).image (continuous_snd.sub
        ((continuous_fst.neg.matrix_mul continuous_const).add continuous_const))) fun Y hY => by_contra fun h => hY ?_⟩
    refine ⟨(Y * ι', T Y), ⟨subset_tsupport _ fun e => h (by simp [Φ, e]), subset_tsupport _ fun e => h (by simp [Φ, e])⟩, ?_⟩
    simp [T]
  obtain ⟨φ, hφ, eφ⟩ := hb.2.2 hΦ
  refine ⟨φ, hφ, ⟨hb.1 hφ, fun Y hY => by_contra fun h => ?_⟩, funext fun Y₁ => ?_⟩
  · rw [eφ] at h
    have n1 : Ψ (Y * ι') ≠ 0 := fun e => h (by simp [Φ, e])
    have n2 : ι φ₁ (T Y) ≠ 0 := fun e => h (by simp [Φ, e])
    obtain ⟨p, hp, hp0⟩ := (rank_ne_iff Y).1 hY
    have hp1 : p ᵥ* (Y * ι') = 0 := by rw [← vecMul_vecMul, hp0, zero_vecMul]
    have hpi : p i ≠ 0 := fun e => hp ((indep_iff _).1 (by_contra fun h => n1 (hΨ.2 _ h)) p
      (fun j hj => by rw [show j = i by simpa using hj]; exact e) hp1)
    have split : ∀ {M : Type} [AddCommGroup M] (f : Fin n → M), ∑ j, f j = f i + ∑ s : (Finset.univ.erase i : Finset (Fin n)), f s :=
      fun f => by rw [Finset.sum_coe_sort, Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hb' := hc₀ (hLb _ n1 (fun s => -(p s / p i)) (by
      rw [vecMul_eq_sum, split, add_eq_zero_iff_eq_neg] at hp1
      rw [← inv_smul_smul₀ hpi ((Y * ι') i), hp1, cmb, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun s _ => by rw [smul_smul, neg_smul, div_eq_inv_mul]))
    have hw := hc₁ ⟨T Y, subset_tsupport _ n2, rfl⟩
    have ew : T Y *ᵥ y' = Y *ᵥ y' - Pi.single i N := by
      simp only [T, add_mulVec, ← mulVec_mulVec, e3, mulVec_zero, zero_add, vecMulVec_mulVec, e4, op_smul_eq_smul, one_smul,
        sub_eq_add_neg]
    have z : p ⬝ᵥ (T Y *ᵥ y') = -(p i * N) := by
      rw [ew, dotProduct_sub, dotProduct_mulVec, hp0, zero_dotProduct, dotProduct_single, zero_sub]
    have eN : N = -(T Y *ᵥ y') i + ∑ s : (Finset.univ.erase i : Finset (Fin n)), -(p s / p i) * (T Y *ᵥ y') s := by
      rw [dotProduct, split] at z
      have : ∑ s : (Finset.univ.erase i : Finset (Fin n)), -(p s / p i) * (T Y *ᵥ y') s =
          -(p i)⁻¹ * ∑ s : (Finset.univ.erase i : Finset (Fin n)), p s * (T Y *ᵥ y') s := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
      rw [this]
      field_simp
      linear_combination z
    refine absurd hNv (not_lt.2 ?_)
    rw [eN, map_mul]
    refine (valuation k).map_add_le ?_ ((valuation k).map_sum_le fun s _ => ?_)
    · rw [Valuation.map_neg]; exact (hw i).trans (le_mul_of_one_le_left' h21)
    · rw [map_mul]; exact mul_le_mul' ((hb' s).trans h22) (hw s)
  · obtain ⟨φ', h', e'⟩ := hb.2.2 (sb_shift hΦ₁ (-Y₁ * κ + vecMulVec (-Pi.single i N) ρ))
    have t1 := htr _ _ φ₁ h₁ φ' h' (congrFun e') Y₁
    have t2 := hkill (φ - ((τ φ₁ 0)⁻¹ * Ψ Y₁) • φ') (sub_mem hφ (SA.smul_mem _ h')) Y₁ fun y => by
      have e : (Y₁ * κ + vecMulVec y ρ) * ι' = Y₁ := by
        rw [Matrix.add_mul, Matrix.mul_assoc, e1, Matrix.mul_one, vecMulVec_mul, e2]
        exact add_eq_left.2 (Matrix.ext fun _ _ => mul_zero _)
      simp only [map_sub, map_smul, eφ, e', Pi.sub_apply, Pi.smul_apply, Φ, T, e, smul_eq_mul, sub_self]
    rw [add_neg_cancel] at t1
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, t1, smul_eq_mul, sub_eq_zero] at t2
    rw [t2]
    field_simp

end PositivityTheory.ThKEnd.Comp.SoL

namespace PositivityTheory.ThKEnd.Comp.SoL

open Filter Topology NumberField IsDedekindDomain Matrix GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.CompanionTheory.Ar.RT.Move GlobalTheory.LatVac PositivityTheory.KCo GlobalTheory.ThK PositivityTheory.ThKCT PositivityTheory.ThKG.Loc GlobalTheory.LFun

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField Classical.propDecidable

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F} {n d d₁ : ℕ}
  {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁} {B : Base F E} {M : Model σ X W} {M₁ : Model σ X W₁}

theorem upd_sb {κ : Type} [Fintype κ] {φ : ∀ u : Pl F, (κ → Fv F u) → ℂ} (h : ∀ u, φ u ∈ SB _) {z} (hz : z ∈ SB _) (u : Pl F) :
    Function.update φ v z u ∈ SB _ := by
  by_cases e : u = v
  · subst e; rwa [Function.update_self]
  · rw [Function.update_of_ne e]; exact h u

theorem upd_cof {κ : Type} {φ : ∀ u : Pl F, (κ → Fv F u) → ℂ} (z) : ∀ᶠ u in cofinite, Function.update φ v z u = φ u :=
  (eventually_cofinite_ne v).mono fun _ e => Function.update_of_ne e _ _

theorem position_inj (hM : M.IsGood B.ψ) {f : SInf F (Fin n × Fin d)} (hf : f ≠ 0) {a b}
    (h : pure f (Function.update M.vac v a) = pure f (Function.update M.vac v b)) : a = b := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 (pure_ne_zero f hf M.vac (fun u => (hM.vac u).2.1) hM.std)
  have u := fun z y => pure_update hM.std (φ := M.vac) (Eventually.of_forall fun _ => rfl) v z f y
  have h1 := u (M.vac v) x
  rw [Function.update_eq_self] at h1
  have h2 := right_ne_zero_of_mul (fun e => hx (h1.trans e))
  funext y
  have := (u a (repl v x y)).symm.trans ((congrFun h _).trans (u b (repl v x y)))
  rw [piK_repl, pure_repl] at this
  exact mul_right_cancel₀ h2 this

theorem exists_continuousLinearMap_tens_update (hM : M.IsGood B.ψ) (f : SInf F (Fin n × Fin d)) (v : Pl F) : ∃ r, (∀ φ, pure f (Function.update M.vac v φ) =
    tens (evFin F v) φ r) ∧ ∀ φ ∈ SB _, Rest (evFin F v) φ r := by
  obtain ⟨r, hr, er⟩ := GlobalTheory.CompanionTheory.Ar.RT.Inj.pure_at M B.ψ hM M.vac (Eventually.of_forall fun _ => rfl) f v
  have e : ∀ φ, pure f (Function.update M.vac v φ) = tens (evFin F v) φ r := fun φ => by
    rw [er _ fun w hw => Function.update_of_ne hw _ _, Function.update_self]
  refine ⟨r, e, fun φ hφ => ⟨hr, ?_⟩⟩
  obtain ⟨g, hg, e'⟩ := GlobalTheory.CompanionTheory.Ar.RT.Inj.pure_eq_pureA M B.ψ hM _ (upd_sb (fun u => (hM.vac u).1) hφ) (upd_cof φ)
  rw [← e, e' f]
  exact Submodule.subset_span ⟨f, g, hg, rfl⟩

theorem ev_loc (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) {e ei ev} (he : IsEvLoc M M₁ e ei ev) {S : Fn F n d → Fn F n d}
    {S₁ : Fn F n d₁ → Fn F n d₁} (h : ∀ Φ ∈ schA F _, e (S Φ) = S₁ (e Φ)) {φ φ' φ₂} (hφ : φ ∈ SB _) (hφ' : φ' ∈ SB _)
    (a : Acts (evFin F v) S φ φ') (a₁ : Acts (evFin F v) S₁ (ev v φ) φ₂) : ev v φ' = φ₂ := by
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    by_contra h
    push Not at h
    exact he.ne (ContinuousLinearMap.ext h)
  obtain ⟨r, er, hr⟩ := exists_continuousLinearMap_tens_update hM f v
  obtain ⟨r₁, er₁, hr₁⟩ := exists_continuousLinearMap_tens_update hM₁ (ei f) v
  have key : ∀ z ∈ SB _, e (tens (evFin F v) z r) = tens (evFin F v) (ev v z) r₁ := fun z hz => by
    rw [← er, ← er₁, he.pure f _ (upd_sb (fun u => (hM.vac u).1) hz) (upd_cof z)]
    congr 1
    funext w
    by_cases hw : w = v
    · subst hw; simp
    · simp [Function.update_of_ne hw, (he.vac w).1]
  have := h _ (hr φ hφ).2
  rw [a r (hr φ hφ), key _ hφ', key _ hφ, a₁ r₁ (hr₁ _ ((he.vac v).2 ▸ Submodule.mem_map_of_mem hφ)), ← er₁, ← er₁] at this
  exact position_inj hM₁ hf this

theorem acts_rho (M : Model σ X W) (ψ) {u} (hu : At (evFin F v) u) (φ) : Acts (evFin F v) (M.co.rho ψ u) φ (locRho M ψ v u φ) :=
  fun _ hr => rho_tens M ψ hu φ hr.1

theorem sep {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {s s' : Fv F v} (h : ∀ c, ψ (liftV v (s * c)) = ψ (liftV v (s' * c))) : s = s' := by
  by_contra hne
  refine GlobalTheory.PsiNontriv.psiV_ne_one ψ hψ v (AddChar.ext _ _ fun y => ?_)
  have h1 := h ((s - s')⁻¹ * y)
  have h2 : s * ((s - s')⁻¹ * y) = y + s' * ((s - s')⁻¹ * y) := by
    have := sub_ne_zero.2 hne
    field_simp
    ring
  rw [h2, map_add, AddChar.map_add_eq_mul] at h1
  exact (mul_eq_right₀ (std_ne_zero hψ _)).1 h1

theorem map_form (t : E →ₐ[F] Fv F v) (J : Matrix (Fin d) (Fin d) E) (x y : Fin d → E) :
    t (form σ J x y) = (fun i => t (x i)) ⬝ᵥ J.map t *ᵥ fun i => (t.comp σ) (y i) := by
  simp [form, dotProduct, mulVec]

theorem map_inc {m m' : ℕ} (t : E →ₐ[F] Fv F v) (A : Matrix (Fin m) (Fin m') E) : (incM F A).map (piW t) = A.map t :=
  Matrix.ext fun i j => by rw [incM, map_apply, map_apply, map_apply]; exact piW_inc t (A i j)

theorem mid_eq (z : Matrix (Fin n) (Fin d₁) (AE F E)) (A : Matrix (Fin d) (Fin d₁) E) :
    incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F A)ᵀ = z * (incM F A)ᵀ := by
  rw [show incM F (1 : Matrix (Fin n) (Fin n) E) = 1 from Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem map_mid (t : E →ₐ[F] Fv F v) (z : Matrix (Fin n) (Fin d₁) (AE F E)) (A : Matrix (Fin d) (Fin d₁) E) :
    (z * (incM F A)ᵀ).map (piW t) = z.map (piW t) * (A.map t)ᵀ := by
  rw [Matrix.map_mul, Matrix.transpose_map, map_inc]

theorem map_vv (t : E →ₐ[F] Fv F v) (a : Fin n → AE F E) (x : Fin d → E) :
    (vecMulVec a (incV F x)).map (piW t) = vecMulVec (fun i => piW t (a i)) fun j => t (x j) := by
  ext i j
  simp [vecMulVec_apply, incV, piW_inc]

theorem soLower_of (hMx : PositivityTheory.ThKG.MixW) : SoLower := by
  intro F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ χX χW om om₁ r s r' s' r₁ s₁ H i₀ i₁ hp hp₁ hH hn hd hν e ei ev he hl φ hφ
  have hB := hp.base
  have hσ : ∀ x, σ (σ x) = x := sig_sig hB.cm
  have dX := det_herm hp.herm
  have dW := det_skew hp.skew
  have dW₁ := det_skew hp₁.skew
  obtain ⟨⟨ι, hι⟩, ν, α, -, -, -, hD⟩ := dictionary_statement F E σ n d B X W M om χX χW hB ⟨_, _, hp.herm⟩ ⟨_, _, hp.skew⟩ hp.good hp.weil
    hp.hX hp.hW B.v₁ B.τ₁
  obtain ⟨⟨ι₁, hι₁⟩, ν₁, α₁, hν₁, -, h1, hD₁⟩ := dictionary_statement F E σ n d₁ B X W₁ M₁ om₁ χX χW hB ⟨_, _, hp.herm⟩ ⟨_, _, hp₁.skew⟩
    hp₁.good hp₁.weil hp.hX hp.hW B.v₁ B.τ₁
  replace hD := hD ι hι
  replace hD₁ := hD₁ ι₁ hι₁
  have hν1 : ν₁ ≠ 1 := fun e => (h1 hn hd e).elim (hν _) (hν _)
  obtain ⟨-, hf⟩ := linEx_of F E σ B n d X W M _ _ _ _ hB hp.herm hp.skew B.v₁ B.τ₁
  obtain ⟨-, hf₁⟩ := linEx_of F E σ B n d₁ X W₁ M₁ _ _ _ _ hB hp.herm hp₁.skew B.v₁ B.τ₁
  generalize B.τ₁ = t at *
  have hb := hι.bij
  have hb₁ := hι₁.bij
  have evsb : ∀ φ ∈ SB _, ev B.v₁ φ ∈ SB _ := fun φ h => (hl.vac B.v₁).2 ▸ Submodule.mem_map_of_mem h
  have so_iff : ∀ φ ∈ SB _, φ ∈ M.SoLoc B.ψ t ↔ Full (ι φ) := fun φ h => ⟨fun hs => ⟨hb.1 h, fun Y hY => by
    obtain ⟨h1, ι', hι', h2⟩ := hs
    obtain ⟨x, hx, h0, rfl⟩ := exists_coB (X := X) (W := W) hB.cm t dX dW Y
    exact eigen_kill M hB.cm hB.std dX dW hι' ((LinearMap.proj (coB σ X W t x)).comp ι) hx h0
      (fun u hu hu1 φ' h' => mult' M hB.std hι hu hu1 hx h0 h') h1 (h2 _ hY)⟩, fun h' => ⟨h, ι, hι, h'.2⟩⟩
  have lmid : ∀ z, At (evFin F B.v₁) z → ∀ φ ∈ SB _, ev B.v₁ (locRho M B.ψ B.v₁ (z * (incM F H.ι)ᵀ) φ) =
      locRho M₁ B.ψ B.v₁ z (ev B.v₁ φ) := fun z hz φ h =>
    ev_loc hp.good hp₁.good hl (fun Φ hΦ => by rw [← he.Heisenberg₂ z Φ hΦ, mid_eq]) h (locRho_mem M hB.std _ h)
      (acts_rho M _ (fun a ha => by rw [← Matrix.smul_mul, hz a ha, Matrix.zero_mul]) φ) (acts_rho M₁ _ hz _)
  have avv : ∀ a : Fin n → AE F E, At (evFin F B.v₁) a → At (evFin F B.v₁) (vecMulVec a (incV F H.x)) := fun a ha c hc => by
    rw [← smul_vecMulVec, ha c hc, zero_vecMulVec]
  have linv : ∀ a, At (evFin F B.v₁) a → ∀ φ ∈ SB _, ev B.v₁ (locRho M B.ψ B.v₁ (vecMulVec a (incV F H.x)) φ) = ev B.v₁ φ :=
    fun a ha φ h => ev_loc (S₁ := id) hp.good hp₁.good hl (fun Φ hΦ => he.inv _ ⟨a, rfl⟩ Φ hΦ) h (locRho_mem M hB.std _ h)
      (acts_rho M _ (avv a ha) φ) fun _ _ => rfl
  set J := W.J.map t with hJ
  set J₁ := W₁.J.map t with hJ₁
  set ι' := H.ι.map t with hι'
  set ιb := H.ι.map (t.comp σ) with hιb
  have uJ₁ : IsUnit J₁ᵀ.det := by rw [det_transpose]; exact unit_map t dW₁
  have uX : IsUnit (-X.J.map t).det := by rw [Matrix.det_neg]; exact (isUnit_one.neg.pow _).mul (unit_map t dX)
  have gram : ιbᵀ * Jᵀ * ι' = J₁ᵀ := by
    have h1 : ι'ᵀ * J * ιb = J₁ := by
      rw [hJ₁, ← hH.gram, hι', hJ, hιb]
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.mul_apply, map_apply, transpose_apply, map_sum, map_mul, AlgHom.comp_apply]
    rw [← h1, transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_assoc]
  let κ : Matrix (Fin d₁) (Fin d) (Fv F B.v₁) := J₁ᵀ⁻¹ * (ιbᵀ * Jᵀ)
  let ρ : Fin d → Fv F B.v₁ := J *ᵥ fun i => (t.comp σ) (H.x i)
  let y' : Fin d → Fv F B.v₁ := -fun i => t (H.y i)
  have sw : ∀ a b, σ (form σ W.J a b) = -1 * form σ W.J b a := form_swap hσ (-1) fun i j => by rw [hp.skew.skew, neg_one_mul]
  have hκ : ∀ w : Fin d → E, (∀ u, form σ W.J (H.ι *ᵥ u) w = 0) → κ *ᵥ (fun i => t (w i)) = 0 := fun w hw => by
    have : (ιbᵀ * Jᵀ) *ᵥ (fun i => t (w i)) = 0 := by
      funext j
      have h2 := sw (H.ι *ᵥ Pi.single j 1) w
      rw [hw, map_zero] at h2
      have h0 : form σ W.J w (H.ι *ᵥ Pi.single j 1) = 0 := by simpa using h2.symm
      have h1 := map_form (σ := σ) t W.J w (H.ι *ᵥ Pi.single j 1)
      have h3 := map_mulVec' (t.comp σ) H.ι (Pi.single j 1)
      rw [SoL.map_single] at h3
      rw [h0, map_zero, h3] at h1
      have h4 : ((ιbᵀ * Jᵀ) *ᵥ fun i => t (w i)) j = (fun i => t (w i)) ⬝ᵥ J *ᵥ ιb *ᵥ Pi.single j 1 := by
        rw [mulVec_mulVec, dotProduct_mulVec, dotProduct_single, mul_one, ← mulVec_transpose, transpose_mul]
      exact h4.trans h1.symm
    rw [← mulVec_mulVec, this, mulVec_zero]
  have hρ : ∀ w : Fin d → E, ρ ⬝ᵥ (fun i => t (w i)) = t (form σ W.J w H.x) := fun w => by rw [map_form, dotProduct_comm]
  have e1 : κ * ι' = 1 := by rw [Matrix.mul_assoc, gram, nonsing_inv_mul _ uJ₁]
  have e2' : ∀ u : Fin d₁ → E, ρ ⬝ᵥ ι' *ᵥ (fun i => t (u i)) = 0 := fun u => by
    rw [← map_mulVec', hρ, (hH.orth u).1, map_zero]
  have e2 : ρ ᵥ* ι' = 0 := funext fun j => by
    have := e2' (Pi.single j 1)
    rwa [map_single, dotProduct_mulVec, dotProduct_single, mul_one] at this
  have e3 : κ *ᵥ y' = 0 := by rw [mulVec_neg, hκ _ fun u => (hH.orth u).2, neg_zero]
  have e4 : ρ ⬝ᵥ y' = 1 := by
    have := sw H.x H.y
    rw [hH.xy, map_one] at this
    rw [dotProduct_neg, hρ, ← map_neg, ← neg_one_mul, ← this, map_one]
  have cmid : ∀ z, coB σ X W t (z * (incM F H.ι)ᵀ) = coB σ X W₁ t z * κ := fun z => by
    rw [coB_eq, coB_eq, map_mid]
    simp only [κ, Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ uJ₁]
  have cvv : ∀ a, coB σ X W t (vecMulVec a (incV F H.x)) = vecMulVec ((-X.J.map t) *ᵥ fun i => piW (t.comp σ) (a i)) ρ := fun a => by
    rw [coB_eq, map_vv, mul_vecMulVec, vecMulVec_mul, vecMul_transpose]
  have htr : ∀ Z₁ y, ∀ φ ∈ SB _, ∀ φ' ∈ SB _, (∀ Y, ι φ' Y = ι φ (Y + (Z₁ * κ + vecMulVec y ρ))) →
      ∀ Y₁, (ι₁ ∘ₗ ev B.v₁) φ' Y₁ = (ι₁ ∘ₗ ev B.v₁) φ (Y₁ + Z₁) := fun Z₁ y φ h φ' h' hY Y₁ => by
    obtain ⟨z, hz, z0, rfl⟩ := exists_coB (X := X) (W := W₁) hB.cm t dX dW₁ Z₁
    choose a a1 a2 a3 using fun i => exists_pair hB.cm t 0 (((-X.J.map t)⁻¹ *ᵥ y) i)
    have ha : At (evFin F B.v₁) a := fun c hc => funext fun i => a1 i c hc
    have s1 := locRho_mem M hB.std (vecMulVec a (incV F H.x)) h
    have s2 := locRho_mem M hB.std (z * (incM F H.ι)ᵀ) s1
    have hz' : At (evFin F B.v₁) (z * (incM F H.ι)ᵀ) := fun a ha => by rw [← Matrix.smul_mul, hz a ha, Matrix.zero_mul]
    have e : φ' = locRho M B.ψ B.v₁ (z * (incM F H.ι)ᵀ) (locRho M B.ψ B.v₁ (vecMulVec a (incV F H.x)) φ) :=
      hb.2.1 h' s2 (funext fun Y => by
        rw [hι.trans _ hz' (by rw [map_mid, z0, Matrix.zero_mul]) _ s1 _ s2 (acts_rho M _ hz' _),
          hι.trans _ (avv a ha) (by rw [map_vv, funext a2]; exact zero_vecMulVec _) _ h _ s1 (acts_rho M _ (avv a ha) _), hY]
        change _ = ι φ (Y + coB σ X W t _ + coB σ X W t _)
        rw [cmid, cvv, funext a3, mulVec_mulVec, mul_nonsing_inv _ uX, one_mulVec, add_assoc])
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e, lmid z hz _ s1, linv a ha φ h]
    exact hι₁.trans z hz z0 _ (evsb φ h) _ (locRho_mem M₁ hB.std _ (evsb φ h)) (acts_rho M₁ _ hz _) Y₁
  have hkill : ∀ φ ∈ SB _, ∀ Y₁, (∀ y, ι φ (Y₁ * κ + vecMulVec y ρ) = 0) → (ι₁ ∘ₗ ev B.v₁) φ Y₁ = 0 := fun φ h Y₁ hY => by
    obtain ⟨x₁, hx₁, x0, rfl⟩ := exists_coB (X := X) (W := W₁) hB.cm t dX dW₁ Y₁
    obtain ⟨ε, ε0, ε1, ε2⟩ := exists_pair hB.cm t 1 0
    have z2 : ∀ {m : ℕ} (c : Fv F B.v₁) (p : Fin n → E) (q : Fin m → E),
        (liftV B.v₁ c • ε • incM F (vecMulVec p q)).map (piW (t.comp σ)) = 0 := fun c p q => by
      rw [← smul_assoc, map_vec _ _ (piW_inc _), Algebra.smul_def, map_mul, ε2, mul_zero, zero_smul]
    have ev1 : ∀ {m : ℕ} {Z : Spc F E m} (N : Model σ X Z), (∀ x u : Matrix (Fin n) (Fin m) (AE F E), At (evFin F B.v₁) x →
        x.map (piW t) = 0 → evFin F B.v₁ (sy σ X Z x u) =
          ((X.J.map t * x.map (piW (t.comp σ)) * (Z.J.map t)ᵀ)ᵀ * u.map (piW t)).trace) → ∀ x, At (evFin F B.v₁) x →
        x.map (piW t) = 0 → ∀ c p q, sy σ X Z x (liftV B.v₁ c • ε • incM F (vecMulVec p q)) =
          liftV B.v₁ (-((fun i => t (p i)) ⬝ᵥ coB σ X Z t x *ᵥ fun j => t (q j)) * c) := fun N hN x hx h0 c p q => by
      have k1 := hN x (ε • incM F (vecMulVec p q)) hx h0
      rw [map_vec _ _ (piW_inc _), ε1, one_smul, trace_vec] at k1
      rw [sy_smul N, mul_comm (liftV _ _), mul_liftV, k1, coB_eq, Matrix.neg_mul, Matrix.neg_mul, neg_mulVec, dotProduct_neg, neg_neg]
    refine eigen_kill_set M hB.cm hB.std dX dW hι ((LinearMap.proj (coB σ X W₁ t x₁)).comp (ι₁ ∘ₗ ev B.v₁))
      {b | (∃ c p q, b = (liftV B.v₁ c • ε • incM F (vecMulVec p (H.ι *ᵥ q)),
        B.ψ (sy σ X W₁ x₁ (liftV B.v₁ c • ε • incM F (vecMulVec p q))))) ∨
        ∃ c p, b = (liftV B.v₁ c • ε • incM F (vecMulVec p H.x), 1)} ?_ ?_ h fun x hx h0 hc => ?_
    · rintro _ (⟨c, p, q, rfl⟩ | ⟨c, p, rfl⟩) <;> exact ⟨at_lift _ _, z2 _ _ _⟩
    · rintro _ (⟨c, p, q, rfl⟩ | ⟨c, p, rfl⟩) φ' h'
      · have := vec_mid (liftV B.v₁ c) ε (1 : Matrix (Fin n) (Fin n) E) H.ι p q
        rw [one_mulVec, mid_eq] at this
        change ι₁ (ev _ _) _ = _ * ι₁ (ev _ _) _
        dsimp only
        rw [this, lmid _ (at_lift _ _) _ h']
        exact mult' M₁ hB.std hι₁ (at_lift _ _) (z2 _ _ _) hx₁ x0 (evsb _ h')
      · have := vec_right (liftV B.v₁ c) ε (1 : Matrix (Fin n) (Fin n) E) p H.x
        rw [one_mulVec] at this
        change ι₁ (ev _ _) _ = _ * ι₁ (ev _ _) _
        dsimp only
        rw [this, linv _ (fun a ha => by rw [← mulVec_smul, smul_smul, ← smul_eq_mul, at_liftV _ c a ha, zero_smul, mulVec_zero])
          _ h', one_mul]
    · set C := coB σ X W t x with hC
      have c1 : C * ι' = coB σ X W₁ t x₁ := Matrix.ext fun i j => by
        have h5 := fun c => hc _ (Or.inl ⟨c, Pi.single i 1, Pi.single j 1, rfl⟩)
        have h6 := sep hB.std fun c => (congrArg B.ψ (ev1 M hf x hx h0 c _ _)).symm.trans
          ((h5 c).trans (congrArg B.ψ (ev1 M₁ hf₁ x₁ hx₁ x0 c _ _)))
        rw [neg_inj, map_mulVec', SoL.map_single, SoL.map_single, mulVec_mulVec, single_dotProduct, single_dotProduct, one_mul,
          one_mul, mulVec_single_one, mulVec_single_one] at h6
        exact h6
      have c2 : C *ᵥ (fun j => t (H.x j)) = 0 := funext fun i => by
        have h5 := fun c => hc _ (Or.inr ⟨c, Pi.single i 1, rfl⟩)
        have h6 := sep hB.std (s' := 0) fun c => (congrArg B.ψ (ev1 M hf x hx h0 c _ _)).symm.trans
          ((h5 c).trans (by rw [zero_mul, map_zero, AddChar.map_zero_eq_one]))
        rw [neg_eq_zero, SoL.map_single, single_dotProduct, one_mul] at h6
        exact h6
      have c3 : C = coB σ X W₁ t x₁ * κ + vecMulVec (C *ᵥ y') ρ := by
        have : ∀ w : Fin d → E, C *ᵥ (fun j => t (w j)) = (C * ι' * κ + vecMulVec (C *ᵥ y') ρ) *ᵥ fun j => t (w j) := fun w => by
          obtain ⟨a, b, u, rfl⟩ := plane_span hH hp.skew.lat w
          have e : (fun j => t ((a • H.x + H.ι *ᵥ u + b • H.y) j)) =
              t a • (fun j => t (H.x j)) + ι' *ᵥ (fun j => t (u j)) + (-t b) • y' := by
            rw [← map_mulVec']; funext j; simp [y']
          have k1 := hκ _ fun u => (hH.orth u).1
          have k2 := hρ H.x
          rw [hH.xx, map_zero] at k2
          have k3 : κ *ᵥ (ι' *ᵥ fun j => t (u j)) = fun j => t (u j) := by rw [mulVec_mulVec, e1, one_mulVec]
          rw [e]
          simp only [mulVec_add, add_mulVec, mulVec_smul, ← mulVec_mulVec, vecMulVec_mulVec, c2, k1, k2, k3, e2', e3, e4,
            mulVec_zero, op_smul_eq_smul, zero_smul, one_smul, smul_zero, add_zero, zero_add]
        rw [← c1]
        refine Matrix.ext fun i j => ?_
        have := congrFun (this (Pi.single j 1)) i
        rw [SoL.map_single, mulVec_single_one, mulVec_single_one] at this
        exact this
      rw [c3]
      exact hY _
  let Fu : Submodule ℂ ((Fin n × Fin d → Fv F B.v₁) → ℂ) :=
    { carrier := {φ | φ ∈ SB _ ∧ Full (ι φ)}
      zero_mem' := ⟨zero_mem _, by rw [map_zero]; exact ⟨zero_mem _, fun _ _ => rfl⟩⟩
      add_mem' := fun a b => ⟨add_mem a.1 b.1, by
        rw [map_add]; exact ⟨add_mem a.2.1 b.2.1, fun Y hY => by simp [a.2.2 Y hY, b.2.2 Y hY]⟩⟩
      smul_mem' := fun c _ a => ⟨Submodule.smul_mem _ c a.1, by
        rw [map_smul]; exact ⟨Submodule.smul_mem _ c a.2.1, fun Y hY => by simp [a.2.2 Y hY]⟩⟩ }
  have hne : ∃ φ ∈ SB (Fin n × Fin d → Fv F B.v₁), (ι₁ ∘ₗ ev B.v₁) φ ≠ 0 := ⟨_, (hp.good.vac _).1, fun h0 => by
    rw [LinearMap.comp_apply, (hl.vac _).1] at h0
    exact (hp₁.good.vac _).2.1 (hb₁.2.1 (hp₁.good.vac _).1 (zero_mem _) (h0.trans (map_zero _).symm))⟩
  have hs := hφ.1
  have hfull := (so_iff φ hs).1 hφ
  obtain ⟨Ψ, hΨ, η, hη, eη⟩ := corank_one (α := α₁) hν₁ hν1
    (N := (Fu ⊓ PositivityTheory.ThKF.augOn om B.v₁ (M.SoLoc B.ψ t)).map (ι₁ ∘ₗ ev B.v₁)) (fun i g₀ Ψ hΨ => by
      obtain ⟨χ, hχ, hχf, rfl⟩ := lift hb e1 e2 e3 e4 hkill htr hne hΨ
      obtain ⟨g, hg, hr₁⟩ := hD₁.leftOnto g₀
      obtain ⟨g₁, hr⟩ := hD.left g hg
      obtain ⟨χ₁, s1, a1, b1⟩ := hr χ hχ
      obtain ⟨χ₂, -, a2, b2⟩ := hr₁ _ (evsb χ hχ)
      have e2 : ev B.v₁ χ₁ = χ₂ := ev_loc hp.good hp₁.good hl (fun Φ hΦ => by
        have := hMx F E σ B n d X W M χX χW om _ _ _ _ hp d₁ W₁ H i₀ i₁ M₁ om₁ _ _ hH hp₁ e he g 1 1 1
          (by simp [IsLevi, mat]) 1 (one_mem _) Φ hΦ
        simpa using this) hχ s1 a1 a2
      refine ⟨χ₁ - χ, ⟨sub_mem (show χ₁ ∈ Fu from ⟨s1, hb.1 s1, fun Y hY => ?_⟩) ⟨hχ, hχf⟩,
        Submodule.subset_span ⟨g, hg, χ, (so_iff χ hχ).2 hχf, χ₁, s1, a1, rfl⟩⟩, ?_⟩
      · rw [b1, GlobalTheory.SplitFlip.omB, hχf.2 _ ?_, mul_zero]
        rwa [Units.val_one, Matrix.mul_one, Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by
          rw [det_transpose]; exact (Matrix.isUnit_iff_isUnit_det _).1 g₁.isUnit)]
      · rw [map_sub, LinearMap.comp_apply, e2, b2]; rfl)
    (Φ := (ι₁ ∘ₗ ev B.v₁) φ) (hb₁.1 (evsb φ hs)) fun Y₁ hY₁ => hkill φ hs Y₁ fun y => hfull.2 _ (rank_ne hn hY₁ κ y ρ)
  have hF : φ - η ∈ Fu := sub_mem ⟨hs, hfull⟩ hη.1
  refine ⟨φ - η, (so_iff _ hF.1).2 hF.2, by simpa using hη.2, evsb _ hF.1, ι₁, hι₁, fun Y hY => ?_⟩
  have : ι₁ (ev B.v₁ (φ - η)) = Ψ := by
    rw [← LinearMap.comp_apply, map_sub, eη]; abel
  rw [this]
  exact hΨ.2 Y hY

end PositivityTheory.ThKEnd.Comp.SoL

end
