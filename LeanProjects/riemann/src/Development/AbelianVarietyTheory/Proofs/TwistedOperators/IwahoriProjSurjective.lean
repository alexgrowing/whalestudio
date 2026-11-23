import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel Matrix Topology Filter

namespace GlobalTheory.SmGL.IwahoriOnto

section Abstract

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

theorem exists_fixed_map_eq {π : Representation ℂ G V} (hπ : IsSmooth π) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) (f : V →ₗ[ℂ] W) (u : V) (hu : ∀ h ∈ H, f (π h u) = f u) :
    ∃ v ∈ fixed π H, f v = f u := by
  classical
  have hlc : IsLocallyConstant fun g : G => π g u := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
    have ho : IsOpen ((fun x => g⁻¹ * x) ⁻¹' {x : G | π x u = u}) := (hπ u).preimage (by fun_prop)
    filter_upwards [ho.mem_nhds (by simp)] with x hx
    have hx' : π (g⁻¹ * x) u = u := hx
    conv_rhs => rw [← hx']
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hH
  have hfin : (Set.range fun h : H => π h u).Finite :=
    (hlc.comp_continuous continuous_subtype_val).range_finite
  set S := hfin.toFinset with hS
  have hmem : ∀ w, w ∈ S ↔ ∃ h : H, π h u = w := fun w => by simp [hS]
  have hne : (S.card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨u, (hmem u).2 ⟨1, by simp⟩⟩)
  have hst : ∀ (h : H) w, w ∈ S → π h w ∈ S := by
    intro h w hw
    obtain ⟨h', rfl⟩ := (hmem w).1 hw
    exact (hmem _).2 ⟨h * h', by simp⟩
  have hc : ∀ (g : G) w, π g⁻¹ (π g w) = w := fun g w => by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  refine ⟨(S.card : ℂ)⁻¹ • ∑ w ∈ S, w, fun h => ?_, ?_⟩
  · simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_smul, map_sum]
    congr 1
    refine Finset.sum_nbij' (π h) (π (h⁻¹ : H)) (hst h) (hst h⁻¹) (fun w _ => hc _ w)
      (fun w _ => ?_) fun _ _ => rfl
    simpa using hc (h : G)⁻¹ w
  · rw [map_smul, map_sum, Finset.sum_congr rfl (g := fun _ => f u), Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hne, one_smul]
    intro w hw
    obtain ⟨h, rfl⟩ := (hmem w).1 hw
    exact hu h h.2

theorem exists_fixed_mk_eq {π : Representation ℂ G V} (hπ : IsAdmissible π) {I N : Subgroup G}
    (ho : IsOpen (I : Set G)) (hc : IsCompact (I : Set G)) {M : Type} [CommGroup M] (s : M →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G)) (M₀ : Subgroup M) (hM₀ : ∀ d ∈ M₀, s d ∈ I)
    (C : Set G) (hfac : ∀ g ∈ I, ∃ d ∈ M₀, ∃ x ∈ N, ∃ c ∈ C, g = s d * x * c)
    (hcon : ∀ U ∈ 𝓝 (1 : G), ∃ t : M, ∀ c ∈ C, (s t)⁻¹ * c * s t ∈ U)
    (y : Jacquet π N) (hy : y ∈ fixed (jacquet π N s hs) M₀) :
    ∃ v ∈ fixed π I, (twKer π N 1).mkQ v = y := by
  set p := (twKer π N 1).mkQ with hp
  set σ := jacquet π N s hs with hσ
  have hps : ∀ m v, p (π (s m) v) = σ m (p v) := fun _ _ => rfl
  have hpN : ∀ x ∈ N, ∀ v, p (π x v) = p v := fun x hx v =>
    (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨x, hx⟩, v, by simp⟩)
  obtain ⟨u, rfl⟩ : ∃ u, p u = y := Submodule.mkQ_surjective _ y
  obtain ⟨t, ht⟩ := hcon _ ((ho.inter (hπ.1 u)).mem_nhds ⟨one_mem I, by simp⟩)
  set Y := (fixed π I).map p with hY
  haveI := hπ.2 I ho hc
  have key : ∀ w, (∀ c ∈ C, π ((s t)⁻¹ * c * s t) w = w) → (∀ d ∈ M₀, σ d (p w) = p w) →
      σ t (p w) ∈ Y := by
    intro w h1 h2
    refine exists_fixed_map_eq hπ.1 hc p (π (s t) w) fun g hg => ?_
    obtain ⟨d, hd, x, hx, c, hcC, rfl⟩ := hfac g hg
    have h3 : π c (π (s t) w) = π (s t) w := by
      conv_rhs => rw [← h1 c hcC]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h3, hps, hpN x hx, hps,
      ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply, h2 d hd]
  have hinj : Function.Injective (σ t) := by
    intro a b hab
    have := congrArg (σ t⁻¹) hab
    simpa [← Module.End.mul_apply, ← map_mul] using this
  have hst : ∀ z ∈ Y, σ t z ∈ Y := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : ∀ g ∈ I, π g w = w := fun g hg => by simpa using hw ⟨g, hg⟩
    exact key w (fun c hcC => hw' _ (ht c hcC).1) fun d hd => by rw [← hps, hw' _ (hM₀ d hd)]
  have hsurj : Function.Surjective ((σ t).restrict hst) :=
    LinearMap.surjective_of_injective fun a b hab => Subtype.ext (hinj (congrArg Subtype.val hab))
  obtain ⟨z, hz⟩ := hsurj ⟨_, key u (fun c hcC => (ht c hcC).2) fun d hd => by simpa using hy ⟨d, hd⟩⟩
  have : (z : Jacquet π N) = p u := hinj (congrArg Subtype.val hz)
  exact this ▸ z.2

end Abstract

section Factor

variable {R n : Type} [CommRing R] [IsLocalRing R] [Fintype n] [DecidableEq n] [LinearOrder n]

theorem exists_mul_mem_borel (h : GL n R)
    (hh : GeneralLinearGroup.map (IsLocalRing.residue R) h ∈ borel (IsLocalRing.ResidueField R) n) :
    ∃ L : GL n R, (∀ i j, i < j → (L : Matrix n n R) i j = 0) ∧ (∀ i, (L : Matrix n n R) i i = 1) ∧
      h * L ∈ borel R n := by
  have hup : ∀ i j, j < i → IsLocalRing.residue R ((h : Matrix n n R) i j) = 0 := hh
  have hdiag : ∀ i, IsLocalRing.residue R ((h : Matrix n n R) i i) ≠ 0 := by
    intro i
    have h1 := (GeneralLinearGroup.det (GeneralLinearGroup.map (IsLocalRing.residue R) h)).ne_zero
    rw [GeneralLinearGroup.val_det_apply, det_of_upperTriangular (mem_borel _ |>.1 hh)] at h1
    exact Finset.prod_ne_zero_iff.1 h1 i (Finset.mem_univ i)
  let A : n → Matrix n n R := fun j => Matrix.of fun i l =>
    if j < i then (h : Matrix n n R) i l else (1 : Matrix n n R) i l
  have hA : ∀ j, IsUnit (A j).det := by
    intro j
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, det_of_upperTriangular]
    · refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
      by_cases hji : j < i
      · simpa [A, hji] using hdiag i
      · simp [A, hji]
    · intro i l hl
      have hl' : l < i := hl
      by_cases hji : j < i
      · simpa [A, hji] using hup i l hl'
      · simp [A, hji, one_apply_ne hl'.ne']
  let L : Matrix n n R := Matrix.of fun i j => (A j)⁻¹ i j
  have hAL : ∀ i j, ∑ l, A j i l * L l j = (1 : Matrix n n R) i j := fun i j =>
    congrFun (congrFun (mul_nonsing_inv (A j) (hA j)) i) j
  have hL : ∀ i j, i ≤ j → L i j = (1 : Matrix n n R) i j := by
    intro i j hij
    have := hAL i j
    simpa [A, hij.not_gt, ← Matrix.mul_apply] using this
  have hL0 : ∀ i j, i < j → L i j = 0 := fun i j hij => by rw [hL i j hij.le, one_apply_ne hij.ne]
  have hL1 : ∀ i, L i i = 1 := fun i => by rw [hL i i le_rfl, one_apply_eq]
  have hdet : L.det = 1 := by
    rw [det_of_lowerTriangular L fun i j hij => hL0 i j hij]
    simp [hL1]
  refine ⟨GeneralLinearGroup.mk'' L (by rw [hdet]; exact isUnit_one), hL0, hL1, fun i j hij => ?_⟩
  have hij' : j < i := hij
  have := hAL i j
  rw [one_apply_ne hij'.ne'] at this
  simpa [A, hij', Matrix.mul_apply] using this

end Factor

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]

def lowerInt : Set (GL n k) :=
  {c | (∀ i j, valuation k ((c : Matrix n n k) i j) ≤ 1) ∧ (∀ i j, i < j → (c : Matrix n n k) i j = 0) ∧
    ∀ i, (c : Matrix n n k) i i = 1}

theorem isOpen_iwahori : IsOpen (iwahori k n : Set (GL n k)) := by
  have e : (iwahori k n : Set (GL n k)) = (KO k n : Set (GL n k)) ∩ ⋂ i, ⋂ j, ⋂ _ : j < i,
      (fun g : GL n k => g.val i j) ⁻¹' {x | valuation k x < 1} := by
    ext g; simp only [SetLike.mem_coe, mem_iwahori, Set.mem_inter_iff, Set.mem_iInter]; rfl
  rw [e]
  refine SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_iInter_of_finite fun _ => IsOpen.preimage ?_ ?_)
  · exact Units.continuous_val.matrix_elem i j
  · simpa using (valuation k).isOpen_ball 1

theorem isCompact_iwahori : IsCompact (iwahori k n : Set (GL n k)) :=
  SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ (isOpen_iwahori k n))
    (iwahori_le_KO k n)

theorem iwahori_factor : ∀ g ∈ iwahori k n, ∃ d ∈ torusO k n, ∃ x ∈ unipB k n, ∃ c ∈ lowerInt k n,
    g = diagT k n d * x * c := by
  rintro _ ⟨h, hh, rfl⟩
  obtain ⟨L, hL0, hL1, hb⟩ := exists_mul_mem_borel h hh
  obtain ⟨u, hu, e⟩ := exists_levi_mul_unip 𝒪[k] (points n) ⟨_, hb⟩
  obtain ⟨d, hd⟩ := (leviTorus 𝒪[k] n).surjective (leviProj 𝒪[k] (points n) ⟨_, hb⟩)
  rw [← hd] at e
  have e' : h * L = diagT 𝒪[k] n d * u := e
  have hLl : L ∈ unipBLower 𝒪[k] n :=
    (mem_unipB (n := nᵒᵈ) 𝒪[k]).2 ⟨fun i j hij => hL0 i j hij, hL1⟩
  have hLi := (mem_unipB (n := nᵒᵈ) 𝒪[k]).1 (inv_mem hLl)
  have hu' := (mem_unipB 𝒪[k]).1 hu
  let f := GeneralLinearGroup.map (n := n) (algebraMap 𝒪[k] k)
  have hf : ∀ (g : GL n 𝒪[k]) i j, (f g : Matrix n n k) i j = algebraMap 𝒪[k] k ((g : Matrix n n 𝒪[k]) i j) :=
    fun _ _ _ => rfl
  refine ⟨fun i => Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) (d i), fun i =>
    (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _), f u,
    (mem_unipB k).2 ⟨fun i j hij => by rw [hf, hu'.1 i j hij, map_zero], fun i => by rw [hf, hu'.2 i, map_one]⟩,
    f L⁻¹, ⟨fun i j => ((L⁻¹ : GL n 𝒪[k]).val i j).2, fun i j hij => ?_, fun i => ?_⟩, ?_⟩
  · rw [hf]; exact (congrArg _ (hLi.1 i j hij)).trans (map_zero _)
  · rw [hf]; exact (congrArg _ (hLi.2 i)).trans (map_one _)
  · have : diagT k n (fun i => Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) (d i)) = f (diagT 𝒪[k] n d) := by
      ext i j
      rw [hf, val_diagT, val_diagT, diagonal_apply, diagonal_apply]
      split_ifs
      · rfl
      · simp
    rw [this, ← map_mul, ← map_mul, ← e', mul_inv_cancel_right]

theorem lowerInt_contract : ∀ U ∈ 𝓝 (1 : GL n k), ∃ t : n → kˣ, ∀ c ∈ lowerInt k n,
    (diagT k n t)⁻¹ * c * diagT k n t ∈ U := by
  intro U hU
  let r : n → ℕ := fun i => (Finset.univ.filter fun j => j < i).card
  have hr : ∀ i j, j < i → r j < r i := fun i j hij =>
    Finset.card_lt_card ⟨fun l hl => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
      exact hl.trans hij, fun hs => by simpa using hs (show j ∈ _ by simpa using hij)⟩
  let T : kˣ → n → kˣ := fun x i => (x ^ r i)⁻¹
  let F : Filter (kˣ × lowerInt k n) := (comap (fun x : kˣ => (x : k)) (𝓝 0)) ×ˢ ⊤
  have hent : ∀ (x : kˣ) (c : GL n k) i j, ((diagT k n (T x))⁻¹ * c * diagT k n (T x)).val i j =
      (x : k) ^ r i * c.val i j * ((x : k) ^ r j)⁻¹ := by
    intro x c i j
    rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, mul_diagonal, diagonal_mul]
    simp [T]
  have hT : Tendsto (fun p : kˣ × lowerInt k n => (diagT k n (T p.1))⁻¹ * p.2.1 * diagT k n (T p.1)) F
      (𝓝 1) := by
    rw [SplitFlip.isEmbedding_val_GL.tendsto_nhds_iff]
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    simp only [Function.comp_def, hent]
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp [fun p : kˣ × lowerInt k n => p.2.2.2.1 i j hij, one_apply_ne hij.ne, tendsto_const_nhds]
    · simp [fun p : kˣ × lowerInt k n => p.2.2.2.2 i, tendsto_const_nhds]
    · rw [Units.val_one, one_apply_ne hij.ne', (IsValuativeTopology.hasBasis_nhds_zero k).tendsto_right_iff]
      intro γ _
      have h1 : {x : k | valuation k x < γ} ∈ 𝓝 (0 : k) :=
        (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨γ, fun _ h => h⟩
      have h2 : {x : k | valuation k x < 1} ∈ 𝓝 (0 : k) :=
        (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, fun _ h => h⟩
      filter_upwards [prod_mem_prod (preimage_mem_comap (inter_mem h1 h2)) univ_mem] with p hp
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt (hr i j hij)
      have : (p.1 : k) ^ r i * p.2.1.val i j * ((p.1 : k) ^ r j)⁻¹ = p.1 * (p.1 ^ m * p.2.1.val i j) := by
        rw [hm]; field_simp; ring
      show valuation k _ < _
      rw [this, map_mul, map_mul, map_pow]
      exact (mul_le_of_le_one_right' (mul_le_one' (pow_le_one' hp.1.2.le _) (p.2.2.1 i j))).trans_lt hp.1.1
  haveI : (comap (fun x : kˣ => (x : k)) (𝓝 0)).NeBot := by
    refine comap_neBot fun s hs => ?_
    obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff s).1 hs
    obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ValueGroupWithZero k, δ ≠ 0 ∧ δ < γ :=
      ⟨uniformizer k * γ, by simp, mul_lt_of_lt_one_left γ.zero_lt uniformizer_lt_one⟩
    obtain ⟨x, rfl⟩ := valuation_surjective δ
    exact ⟨Units.mk0 x (by simpa using hδ0), hγ hδ⟩
  obtain ⟨x, hx⟩ := Filter.nonempty_of_mem (mem_prod_top.1 (hT hU))
  exact ⟨T x, fun c hc => hx ⟨c, hc⟩⟩

end Local

theorem iwahoriProj_surjective (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] (V : Type)
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V) (hπ : IsAdmissible π) :
    Function.Surjective (iwahoriProj π) := by
  rintro ⟨y, hy⟩
  obtain ⟨v, hv, e⟩ := exists_fixed_mk_eq hπ (isOpen_iwahori k n) (isCompact_iwahori k n) (diagT k n)
    (N := unipB k n) (fun _ => leviEmb_mem_normalizer k (points n) _) (torusO k n)
    (fun _ => diagT_mem_iwahori) (lowerInt k n) (iwahori_factor k n) (lowerInt_contract k n) y hy
  exact ⟨⟨v, hv⟩, Subtype.ext e⟩

end GlobalTheory.SmGL.IwahoriOnto
