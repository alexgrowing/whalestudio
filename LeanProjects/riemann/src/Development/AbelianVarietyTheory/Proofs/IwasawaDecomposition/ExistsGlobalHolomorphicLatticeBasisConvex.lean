import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement

set_option autoImplicit false

noncomputable section

open Topology

namespace GlobalTheory.ShFam.Hor.LogCh.Glob

variable {g r : ℕ}

def rip (w : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℝ] ℝ where
  toFun v := ∑ k, (v k * (starRingEnd ℂ) (w k)).re
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.mul_sum, mul_assoc]

theorem rip_apply (w v : Fin g → ℂ) : rip w v = ∑ k, (v k * (starRingEnd ℂ) (w k)).re := rfl

theorem rip_comm (w v : Fin g → ℂ) : rip w v = rip v w := by
  simp only [rip_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Complex.mul_re]
  ring

theorem eq_zero_of_rip_self {v : Fin g → ℂ} (h : rip v v = 0) : v = 0 := by
  have h' : ∑ k, Complex.normSq (v k) = 0 := by
    rw [← h, rip_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.mul_conj, Complex.ofReal_re]
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg (v k))).1 h'
  funext k
  exact Complex.normSq_eq_zero.1 (this k (Finset.mem_univ k))

theorem continuous_rip : Continuous fun q : (Fin g → ℂ) × (Fin g → ℂ) => rip q.1 q.2 := by
  simp only [rip_apply]
  refine continuous_finset_sum _ fun k _ => Complex.continuous_re.comp ?_
  exact ((continuous_apply k).comp continuous_snd).mul
    (Complex.continuous_conj.comp ((continuous_apply k).comp continuous_fst))

def gram (l : Fin r → Fin g → ℂ) : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun i a => rip (l a) (l i)

def pair (l y : Fin r → Fin g → ℂ) : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun j a => rip (l a) (y j)

theorem det_gram_ne_zero {l : Fin r → Fin g → ℂ} (hl : LinearIndependent ℝ l) : (gram l).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
  apply hv
  have hs : ∀ a, rip (l a) (∑ i, v i • l i) = 0 := by
    intro a
    have := congrFun hv0 a
    simpa [Matrix.vecMul, dotProduct, gram, map_sum] using this
  have hz : (∑ i, v i • l i) = 0 := by
    apply eq_zero_of_rip_self
    calc rip (∑ i, v i • l i) (∑ i, v i • l i) = ∑ a, rip (∑ i, v i • l i) (v a • l a) := map_sum _ _ _
      _ = ∑ a, v a * rip (l a) (∑ i, v i • l i) :=
        Finset.sum_congr rfl fun a _ => by rw [map_smul, smul_eq_mul, rip_comm]
      _ = 0 := by simp [hs]
  exact funext fun i => Fintype.linearIndependent_iff.1 hl v hz i

def coord (l y : Fin r → Fin g → ℂ) : Matrix (Fin r) (Fin r) ℝ := pair l y * (gram l)⁻¹

theorem coord_eq {l y : Fin r → Fin g → ℂ} (hl : LinearIndependent ℝ l) (c : Matrix (Fin r) (Fin r) ℝ)
    (hy : ∀ j, y j = ∑ i, c j i • l i) : coord l y = c := by
  have : pair l y = c * gram l := by
    ext j a
    simp [pair, gram, Matrix.mul_apply, hy j, map_sum]
  rw [coord, this]
  exact Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_iff_ne_zero.2 (det_gram_ne_zero hl))

theorem continuous_coord {T : Type*} [TopologicalSpace T] {l y : T → Fin r → Fin g → ℂ} (hl : Continuous l)
    (hy : Continuous y) (hi : ∀ t, LinearIndependent ℝ (l t)) : Continuous fun t => coord (l t) (y t) := by
  have hg : Continuous fun t => gram (l t) := continuous_matrix fun i a =>
    continuous_rip.comp (((continuous_apply a).comp hl).prodMk ((continuous_apply i).comp hl))
  have hp : Continuous fun t => pair (l t) (y t) := continuous_matrix fun j a =>
    continuous_rip.comp (((continuous_apply a).comp hl).prodMk ((continuous_apply j).comp hy))
  have hinv : Continuous fun t => (gram (l t))⁻¹ := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv']
    exact (hg.matrix_det.inv₀ fun t => det_gram_ne_zero (hi t)).smul hg.matrix_adjugate
  exact hp.matrix_mul hinv

def act (m : Matrix (Fin r) (Fin r) ℤ) (l : Fin r → Fin g → ℂ) : Fin r → Fin g → ℂ := fun j => ∑ i, m j i • l i

theorem act_real (m : Matrix (Fin r) (Fin r) ℤ) (l : Fin r → Fin g → ℂ) (j : Fin r) :
    act m l j = ∑ i, (m.map (Int.cast : ℤ → ℝ)) j i • l i := by
  simp only [act, Matrix.map_apply, Int.cast_smul_eq_zsmul]

theorem coord_act {l : Fin r → Fin g → ℂ} (hl : LinearIndependent ℝ l) (m : Matrix (Fin r) (Fin r) ℤ) :
    coord l (act m l) = m.map (Int.cast : ℤ → ℝ) :=
  coord_eq hl _ (act_real m l)

theorem act_injective {l : Fin r → Fin g → ℂ} (hl : LinearIndependent ℝ l) {m m' : Matrix (Fin r) (Fin r) ℤ}
    (h : act m l = act m' l) : m = m' := by
  have := (coord_act hl m).symm.trans ((congrArg (coord l) h).trans (coord_act hl m'))
  ext j i
  simpa using congrFun (congrFun this j) i

theorem act_one (l : Fin r → Fin g → ℂ) : act 1 l = l := by
  funext j
  simp [act, Matrix.one_apply]

theorem act_act (m n : Matrix (Fin r) (Fin r) ℤ) (l : Fin r → Fin g → ℂ) : act m (act n l) = act (m * n) l := by
  funext j
  simp only [act, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem sum_act_int (a : Fin r → ℤ) (m : Matrix (Fin r) (Fin r) ℤ) (l : Fin r → Fin g → ℂ) :
    ∑ j, a j • act m l j = ∑ i, (Matrix.vecMul a m) i • l i := by
  simp only [act, Matrix.vecMul, dotProduct, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem sum_act_real (c : Fin r → ℝ) (m : Matrix (Fin r) (Fin r) ℤ) (l : Fin r → Fin g → ℂ) :
    ∑ j, c j • act m l j = ∑ i, (Matrix.vecMul c (m.map (Int.cast : ℤ → ℝ))) i • l i := by
  simp only [act_real, Matrix.vecMul, dotProduct, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

def GLZ (r : ℕ) : Type := (Matrix (Fin r) (Fin r) ℤ)ˣ

instance : TopologicalSpace (GLZ r) := ⊥

instance : DiscreteTopology (GLZ r) := ⟨rfl⟩

def GLZ.mat (M : GLZ r) : Matrix (Fin r) (Fin r) ℤ := Units.val M

theorem GLZ.mat_injective : Function.Injective (GLZ.mat : GLZ r → _) := Units.val_injective

theorem exists_glz {S : Set (Fin g → ℂ)} {l l' : Fin r → Fin g → ℂ} (hl : IsLatBasis S l) (hl' : IsLatBasis S l') :
    ∃ M : GLZ r, l' = act M.mat l := by
  have mem : ∀ {q : Fin r → Fin g → ℂ}, IsLatBasis S q → ∀ j, q j ∈ S := fun {q} hq j =>
    (hq.2 _).2 ⟨Pi.single j 1, by simp [Pi.single_apply, ite_smul]⟩
  choose m hm using fun j => (hl.2 _).1 (mem hl' j)
  choose n hn using fun j => (hl'.2 _).1 (mem hl j)
  have e1 : l' = act (Matrix.of m) l := funext hm
  have e2 : l = act (Matrix.of n) l' := funext hn
  have h1 : Matrix.of m * Matrix.of n = 1 := by
    refine act_injective hl'.1 ?_
    rw [← act_act, ← e2, ← e1, act_one]
  have h2 : Matrix.of n * Matrix.of m = 1 := by
    refine act_injective hl.1 ?_
    rw [← act_act, ← e1, ← e2, act_one]
  exact ⟨⟨Matrix.of m, Matrix.of n, h1, h2⟩, e1⟩

theorem isLatBasis_act {S : Set (Fin g → ℂ)} {l : Fin r → Fin g → ℂ} (hl : IsLatBasis S l) (M : GLZ r) :
    IsLatBasis S (act M.mat l) := by
  obtain ⟨m, n, hM, h1, h2⟩ : ∃ m n : Matrix (Fin r) (Fin r) ℤ, M.mat = m ∧ m * n = 1 ∧ n * m = 1 :=
    ⟨M.mat, Units.inv M, rfl, Units.mul_inv M, Units.inv_mul M⟩
  rw [hM]
  have hr : m.map (Int.cast : ℤ → ℝ) * n.map (Int.cast : ℤ → ℝ) = 1 := by
    have h : (m * n).map (Int.castRingHom ℝ) = 1 := by rw [h1]; simp
    rw [Matrix.map_mul] at h
    exact h
  refine ⟨Fintype.linearIndependent_iff.2 fun c hc j => ?_, fun w => ?_⟩
  · rw [sum_act_real] at hc
    have h0 := Fintype.linearIndependent_iff.1 hl.1 _ hc
    have h0' : Matrix.vecMul c (m.map (Int.cast : ℤ → ℝ)) = 0 := funext h0
    have : c = Matrix.vecMul (Matrix.vecMul c (m.map (Int.cast : ℤ → ℝ))) (n.map (Int.cast : ℤ → ℝ)) := by
      rw [Matrix.vecMul_vecMul, hr, Matrix.vecMul_one]
    rw [this, h0']
    simp
  · constructor
    · intro hw
      obtain ⟨b, rfl⟩ := (hl.2 _).1 hw
      refine ⟨Matrix.vecMul b n, ?_⟩
      rw [sum_act_int, Matrix.vecMul_vecMul, h2, Matrix.vecMul_one]
    · rintro ⟨a, rfl⟩
      exact (hl.2 _).2 ⟨Matrix.vecMul a m, sum_act_int a m l⟩

theorem continuous_of_act {T : Type*} [TopologicalSpace T] {l y : T → Fin r → Fin g → ℂ} (hl : Continuous l)
    (hy : Continuous y) (hi : ∀ t, LinearIndependent ℝ (l t)) (M : T → GLZ r)
    (h : ∀ t, y t = act (M t).mat (l t)) : Continuous M := by
  have hc := continuous_coord hl hy hi
  have he : ∀ t, coord (l t) (y t) = (M t).mat.map (Int.cast : ℤ → ℝ) := fun t => by
    rw [h t, coord_act (hi t)]
  have hp : Continuous fun t => ((M t).mat : Fin r → Fin r → ℤ) := by
    refine continuous_pi fun j => continuous_pi fun i => ?_
    rw [Int.isClosedEmbedding_coe_real.isEmbedding.continuous_iff]
    have : Continuous fun t => coord (l t) (y t) j i :=
      hc.matrix_elem j i
    refine this.congr fun t => ?_
    rw [he t]
    rfl
  have hlc : IsLocallyConstant (fun t => ((M t).mat : Fin r → Fin r → ℤ)) :=
    (IsLocallyConstant.iff_continuous _).2 hp
  exact ((IsLocallyConstant.desc M GLZ.mat hlc GLZ.mat_injective)).continuous

theorem continuous_act (m : Matrix (Fin r) (Fin r) ℤ) : Continuous (act m : (Fin r → Fin g → ℂ) → _) :=
  continuous_pi fun j => continuous_finset_sum _ fun i _ => (continuous_apply i).const_smul (m j i)

variable {n : ℕ}

abbrev Frames (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (r : ℕ) : Type :=
  {p : ↥B × (Fin r → Fin g → ℂ) // IsLatBasis (K p.1) p.2}

def proj (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (r : ℕ) : Frames B K r → ↥B := fun e => e.1.1

theorem continuous_proj (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (r : ℕ) :
    Continuous (proj B K r) := continuous_fst.comp continuous_subtype_val

theorem local_data {B : Set (Fin n → ℂ)} {K : (Fin n → ℂ) → Set (Fin g → ℂ)} (hB : IsOpen B)
    (hloc : ∀ b₀ ∈ B, ∃ lam : (Fin n → ℂ) → Fin r → Fin g → ℂ, AnalyticAt ℂ lam b₀ ∧
      ∀ᶠ b in 𝓝 b₀, IsLatBasis (K b) (lam b)) {b₀ : Fin n → ℂ} (hb : b₀ ∈ B) :
    ∃ (V : Set (Fin n → ℂ)) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ), IsOpen V ∧ b₀ ∈ V ∧ V ⊆ B ∧
      AnalyticAt ℂ lam b₀ ∧ ContinuousOn lam V ∧ ∀ b ∈ V, IsLatBasis (K b) (lam b) := by
  obtain ⟨lam, han, hev⟩ := hloc b₀ hb
  have h := (han.eventually_analyticAt.and hev).and (hB.mem_nhds hb)
  obtain ⟨V, hVs, hV, hbV⟩ := eventually_nhds_iff.1 h
  exact ⟨V, lam, hV, hbV, fun x hx => (hVs x hx).2, han,
    fun x hx => (hVs x hx).1.1.continuousAt.continuousWithinAt, fun x hx => (hVs x hx).1.2⟩

theorem isCoveringMap_proj {B : Set (Fin n → ℂ)} {K : (Fin n → ℂ) → Set (Fin g → ℂ)} (hB : IsOpen B)
    (hloc : ∀ b₀ ∈ B, ∃ lam : (Fin n → ℂ) → Fin r → Fin g → ℂ, AnalyticAt ℂ lam b₀ ∧
      ∀ᶠ b in 𝓝 b₀, IsLatBasis (K b) (lam b)) : IsCoveringMap (proj B K r) := by
  intro x₀
  obtain ⟨V, lam, hV, hxV, hVB, -, hc, hbas⟩ := local_data hB hloc x₀.2
  apply IsEvenlyCovered.to_isEvenlyCovered_preimage (I := GLZ r)
  have hU : IsOpen (Subtype.val ⁻¹' V : Set ↥B) := hV.preimage continuous_subtype_val
  have hM : ∀ e : proj B K r ⁻¹' (Subtype.val ⁻¹' V : Set ↥B), ∃ M : GLZ r,
      e.1.1.2 = act M.mat (lam e.1.1.1.1) := fun e => exists_glz (hbas _ e.2) e.1.2
  choose M hM using hM
  have hcl : Continuous fun e : proj B K r ⁻¹' (Subtype.val ⁻¹' V : Set ↥B) => lam e.1.1.1.1 :=
    hc.comp_continuous (by fun_prop) fun e => e.2
  have hMc : Continuous M :=
    continuous_of_act hcl (by fun_prop) (fun e => (hbas _ e.2).1) M hM
  refine ⟨inferInstance, _, hxV, hU, hU.preimage (continuous_proj B K r), ?_⟩
  refine ⟨{ toFun := fun e => (⟨proj B K r e.1, e.2⟩, M e)
            invFun := fun q => ⟨⟨⟨q.1.1, act q.2.mat (lam q.1.1.1)⟩, isLatBasis_act (hbas _ q.1.2) q.2⟩, q.1.2⟩
            left_inv := fun e => ?_
            right_inv := fun q => ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun e => rfl⟩
  · apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl (hM e).symm
  · refine Prod.ext rfl ?_
    apply GLZ.mat_injective
    exact act_injective (hbas _ q.1.2).1 (hM _).symm
  · exact (Continuous.subtype_mk ((continuous_proj B K r).comp continuous_subtype_val) _).prodMk hMc
  · refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    refine (continuous_subtype_val.comp continuous_fst).prodMk ?_
    rw [continuous_prod_of_discrete_right]
    intro m
    have hlu : Continuous fun u : ↥(Subtype.val ⁻¹' V : Set ↥B) => lam u.1.1 :=
      hc.comp_continuous (by fun_prop) fun u => u.2
    exact (continuous_act m.mat).comp hlu

theorem exists_global (n g r : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (hB : IsOpen B)
    (hconv : Convex ℝ B)
    (hloc : ∀ b₀ ∈ B, ∃ lam : (Fin n → ℂ) → Fin r → Fin g → ℂ, AnalyticAt ℂ lam b₀ ∧
      ∀ᶠ b in 𝓝 b₀, IsLatBasis (K b) (lam b)) :
    ∃ lam : (Fin n → ℂ) → Fin r → Fin g → ℂ, DifferentiableOn ℂ lam B ∧ ∀ b ∈ B, IsLatBasis (K b) (lam b) := by
  rcases B.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, by simp, by simp⟩
  obtain ⟨a₀, ha₀⟩ := hne
  have hcs : ContractibleSpace ↥B := hconv.contractibleSpace ⟨a₀, ha₀⟩
  have hlp : LocallyPathConnectedSpace ↥B := hB.locallyPathConnectedSpace
  obtain ⟨l₀, -, hl₀⟩ := hloc a₀ ha₀
  have cov := isCoveringMap_proj (r := r) hB hloc
  obtain ⟨F, ⟨-, hF⟩, -⟩ := cov.existsUnique_continuousMap_lifts (ContinuousMap.id ↥B) ⟨a₀, ha₀⟩
    ⟨⟨⟨a₀, ha₀⟩, l₀ a₀⟩, hl₀.self_of_nhds⟩ rfl
  have hFb : ∀ x : ↥B, (F x).1.1 = x := fun x => congrFun hF x
  have hbas : ∀ x : ↥B, IsLatBasis (K x) (F x).1.2 := fun x => by
    have := (F x).2
    rwa [hFb x] at this
  classical
  let lamG : (Fin n → ℂ) → Fin r → Fin g → ℂ := fun b => if h : b ∈ B then (F ⟨b, h⟩).1.2 else 0
  have hlamG : ∀ x : ↥B, lamG x = (F x).1.2 := fun x => by simp [lamG, x.2]
  refine ⟨lamG, fun b₀ hb₀ => ?_, fun b hb => hlamG ⟨b, hb⟩ ▸ hbas ⟨b, hb⟩⟩
  obtain ⟨V, lam, hV, hbV, hVB, han, hc, hlat⟩ := local_data hB hloc hb₀
  have hM : ∀ t : ↥V, ∃ M : GLZ r, (F ⟨t, hVB t.2⟩).1.2 = act M.mat (lam t) :=
    fun t => exists_glz (hlat _ t.2) (hbas ⟨t, hVB t.2⟩)
  choose M hM using hM
  have hMc : Continuous M := continuous_of_act (hc.comp_continuous continuous_subtype_val fun t => t.2)
    (by fun_prop) (fun t => (hlat _ t.2).1) M hM
  have hopen : IsOpen (Subtype.val '' (M ⁻¹' {M ⟨b₀, hbV⟩}) : Set (Fin n → ℂ)) :=
    hV.isOpenMap_subtype_val _ ((isOpen_discrete _).preimage hMc)
  have hev : lamG =ᶠ[𝓝 b₀] fun b => act (M ⟨b₀, hbV⟩).mat (lam b) := by
    filter_upwards [hopen.mem_nhds ⟨⟨b₀, hbV⟩, rfl, rfl⟩] with b hb
    obtain ⟨t, ht, rfl⟩ := hb
    rw [show lamG t = (F ⟨t, hVB t.2⟩).1.2 from hlamG ⟨t, hVB t.2⟩, hM t, show M t = M ⟨b₀, hbV⟩ from ht]
  have hd : DifferentiableAt ℂ (fun b => act (M ⟨b₀, hbV⟩).mat (lam b)) b₀ := by
    have hda := han.differentiableAt
    refine differentiableAt_pi.2 fun j => ?_
    simp only [act, ← Int.cast_smul_eq_zsmul ℂ]
    exact DifferentiableAt.fun_sum fun i _ => (differentiableAt_pi.1 hda i).fun_const_smul _
  exact (hev.differentiableAt_iff.2 hd).differentiableWithinAt

end GlobalTheory.ShFam.Hor.LogCh.Glob
