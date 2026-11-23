import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.WTrans
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.GConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FzkLaw

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc Matrix

noncomputable section

section Mat

variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]

variable (O) in
private def Ent (g : GL (Fin 2) K) : Prop := ∀ s t, (g : Matrix (Fin 2) (Fin 2) K) s t ∈ Set.range (algebraMap O K)

private abbrev sc (s : Kˣ) : GL (Fin 2) K := GeneralLinearGroup.scalar (Fin 2) s

private theorem sc_val (s : Kˣ) : ((sc s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = (s : K) • 1 := by
  ext i j
  by_cases h : i = j <;> simp [sc, GeneralLinearGroup.scalar, h]

private theorem sc_comm (s : Kˣ) (g : GL (Fin 2) K) : sc s * g = g * sc s := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, sc_val, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

private theorem kg_ent {g : GL (Fin 2) K} (h : g ∈ KG O K) : Ent O g := by
  obtain ⟨a, rfl⟩ := h
  exact fun s t => ⟨(a : Matrix (Fin 2) (Fin 2) O) s t, rfl⟩

private theorem kg_det {g : GL (Fin 2) K} (h : g ∈ KG O K) :
    ∃ u : Oˣ, (g : Matrix (Fin 2) (Fin 2) K).det = algebraMap O K u := by
  obtain ⟨a, rfl⟩ := h
  refine ⟨GeneralLinearGroup.det a, ?_⟩
  simp [RingHom.map_det]

private theorem kg_of_det [IsFractionRing O K] {g : GL (Fin 2) K} (h : Ent O g) (u : Oˣ)
    (hu : (g : Matrix (Fin 2) (Fin 2) K).det = algebraMap O K u) : g ∈ KG O K := by
  choose a ha using h
  have hg : (g : Matrix (Fin 2) (Fin 2) K) = (algebraMap O K).mapMatrix (Matrix.of a) := by
    ext s t
    simp [ha]
  have hd : (Matrix.of a).det = u := by
    apply IsFractionRing.injective O K
    rw [RingHom.map_det, ← hg, hu]
  refine ⟨GeneralLinearGroup.mk'' (Matrix.of a) (hd ▸ u.isUnit), Units.ext ?_⟩
  rw [hg]
  rfl

private theorem ent_det {g : GL (Fin 2) K} (h : Ent O g) : ∃ r : O, (g : Matrix (Fin 2) (Fin 2) K).det = algebraMap O K r := by
  choose a ha using h
  exact ⟨a 0 0 * a 1 1 - a 0 1 * a 1 0, by simp [det_fin_two, ha]⟩

private theorem kg_of_inv [IsFractionRing O K] {g : GL (Fin 2) K} (h : Ent O g) (h' : Ent O g⁻¹) : g ∈ KG O K := by
  obtain ⟨r, hr⟩ := ent_det h
  obtain ⟨r', hr'⟩ := ent_det h'
  have : r * r' = 1 := by
    apply IsFractionRing.injective O K
    rw [map_mul, ← hr, ← hr', ← det_mul, ← Units.val_mul, mul_inv_cancel, map_one]
    simp
  exact kg_of_det h (Units.mkOfMulEqOne r r' this) hr

private theorem zk_iff {g : GL (Fin 2) K} : g ∈ ZK O K ↔ ∃ s : Kˣ, ∃ k ∈ KG O K, g = sc s * k := by
  constructor
  · intro h
    haveI : (GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K).range.Normal := ⟨by
      rintro _ ⟨s, rfl⟩ g
      exact ⟨s, by rw [← sc_comm s g, mul_inv_cancel_right]⟩⟩
    have h' : g ∈ ((ZK O K : Subgroup _) : Set (GL (Fin 2) K)) := h
    rw [ZK, Subgroup.normal_mul] at h'
    obtain ⟨_, ⟨s, rfl⟩, k, hk, rfl⟩ := h'
    exact ⟨s, k, hk, rfl⟩
  · rintro ⟨s, k, hk, rfl⟩
    exact Subgroup.mul_mem_sup ⟨s, rfl⟩ hk

private theorem ent_of_zk [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] {g : GL (Fin 2) K} (u : Oˣ)
    (hu : (g : Matrix (Fin 2) (Fin 2) K).det = algebraMap O K u) (h : g ∈ ZK O K) : Ent O g := by
  obtain ⟨w, k, hk, rfl⟩ := zk_iff.1 h
  obtain ⟨v, hv⟩ := kg_det hk
  have hw : ∃ r : O, algebraMap O K r = w := by
    rcases ValuationRing.isInteger_or_isInteger O (w : K) with h | ⟨r, hr⟩
    · exact h
    · rw [Units.val_mul, sc_val, det_mul, det_smul, hv] at hu
      have : r * (r * u) = v := by
        apply IsFractionRing.injective O K
        rw [map_mul, map_mul, hr, ← hu]
        simp
        field_simp
      have hr' : IsUnit r := isUnit_of_mul_isUnit_left (this ▸ v.isUnit)
      obtain ⟨r', hr''⟩ := hr'.exists_right_inv
      refine ⟨r', ?_⟩
      have := congrArg (algebraMap O K) hr''
      rw [map_mul, hr, map_one] at this
      field_simp at this
      exact this
  obtain ⟨r, hr⟩ := hw
  intro s t
  obtain ⟨a, ha⟩ := kg_ent hk s t
  exact ⟨r * a, by simp [sc_val, hr, ha]⟩

end Mat

section LL

variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {τ : K}

variable (τ) in
private abbrev b0 : Module.Basis (Fin 2) K (Etau K τ) := QuadraticAlgebra.basis (-1) τ

variable (τ) in
private abbrev j0 : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K := Algebra.leftMulMatrix (b0 τ)

private theorem leftMulMatrixEmbedding_omega_trace : (j0 τ ω).trace = τ := by
  simp [Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis]

private theorem leftMulMatrixEmbedding_det_eq_norm (x : Etau K τ) : (j0 τ x).det = QuadraticAlgebra.norm x := by
  simp [Matrix.det_fin_two, Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis, QuadraticAlgebra.norm_def]
  ring

variable (τ) in
private def su (s : Kˣ) : (Etau K τ)ˣ := Units.map (algebraMap K (Etau K τ) : K →* Etau K τ) s

private theorem su_mul (s : Kˣ) (x : Etau K τ) : (su τ s : Etau K τ) * x = (s : K) • x := by
  simp [su, Algebra.smul_def]

private theorem jU_su (s : Kˣ) : jU (j0 τ) (su τ s) = sc s := by
  apply Units.ext
  rw [sc_val]
  change j0 τ (algebraMap K _ (s : K)) = _
  rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]

variable (O τ) in
private def LL (g : GL (Fin 2) K) : Set (Etau K τ) :=
  {x | ∀ i, (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (b0 τ).repr x) i ∈ Set.range (algebraMap O K)}

private theorem lat_mul (t : (Etau K τ)ˣ) (g : GL (Fin 2) K) :
    LL O τ (jU (j0 τ) t * g) = ((t : Etau K τ) * ·) '' LL O τ g := by
  have h : ∀ x, x ∈ LL O τ (jU (j0 τ) t * g) ↔ ((t⁻¹ : (Etau K τ)ˣ) : Etau K τ) * x ∈ LL O τ g := by
    intro x
    simp only [LL, Set.mem_setOf_eq]
    rw [_root_.mul_inv_rev, ← map_inv, Units.val_mul, ← mulVec_mulVec, ← Algebra.leftMulMatrix_mulVec_repr]
    rfl
  ext x
  rw [h]
  constructor
  · exact fun hx => ⟨_, hx, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

private theorem lat_sc (s : Kˣ) (g : GL (Fin 2) K) : LL O τ (sc s * g) = ((s : K) • ·) '' LL O τ g := by
  rw [← jU_su (τ := τ), lat_mul]
  simp only [su_mul]

private theorem lat_le {g g' : GL (Fin 2) K} : LL O τ g ⊆ LL O τ g' ↔ Ent O (g'⁻¹ * g) := by
  constructor
  · intro h s t
    have := h (a := (b0 τ).equivFun.symm ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ Pi.single t 1)) (by
      intro i
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, one_mulVec]
      by_cases h : i = t
      · exact ⟨1, by simp [h]⟩
      · exact ⟨0, by simp [h]⟩) s
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, mulVec_mulVec, ← Units.val_mul] at this
    simpa using this
  · intro h x hx i
    have e : ((g'⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (b0 τ).repr x =
        ((g'⁻¹ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
          (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (b0 τ).repr x) := by
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right]
    rw [e]
    choose a ha using h
    choose v hv using hx
    refine ⟨a i 0 * v 0 + a i 1 * v 1, ?_⟩
    rw [map_add, map_mul, map_mul, ha, ha, hv, hv]
    generalize ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (b0 τ).repr x = w
    simp [mulVec, dotProduct]

private theorem lat_basis [IsDomain O] [IsFractionRing O K] (B : Module.Basis (Fin 2) K (Etau K τ)) (g : GL (Fin 2) K)
    (h : ∀ x, ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (b0 τ).repr x = B.repr x) :
    LL O τ g = Submodule.span O (Set.range B) := by
  ext x
  rw [SetLike.mem_coe, B.mem_span_iff_repr_mem O, ← h]
  rfl

private theorem lat_isLat [IsDomain O] [IsFractionRing O K] (g : GL (Fin 2) K) : IsLat O τ (LL O τ g) := by
  classical
  let B : Module.Basis (Fin 2) K (Etau K τ) :=
    Module.Basis.ofEquivFun ((b0 τ).equivFun ≪≫ₗ (GeneralLinearGroup.toLin g⁻¹).toLinearEquiv)
  have h := lat_basis (O := O) B g fun x => rfl
  refine ⟨⟨Finset.univ.image B, by rw [h]; simp⟩, ?_⟩
  rw [h, Submodule.span_span_of_tower, B.span_eq]

private theorem isLat_lat [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] {S : Set (Etau K τ)}
    (hS : IsLat O τ S) : ∃ g, S = LL O τ g := by
  obtain ⟨⟨s, rfl⟩, hsp⟩ := hS
  set M : Submodule O (Etau K τ) := Submodule.span O (s : Set (Etau K τ)) with hM
  haveI : Submodule.IsLattice K M := ⟨⟨s, rfl⟩, hsp⟩
  have hr : Module.finrank O M = 2 := by
    apply Module.finrank_eq_of_rank_eq
    rw [Submodule.IsLattice.rank' K M, ← Module.finrank_eq_rank, QuadraticAlgebra.finrank_eq_two]
  let b := Module.finBasisOfFinrankEq O M hr
  let B := b.extendOfIsLattice K
  refine ⟨⟨(b0 τ).toMatrix B, B.toMatrix (b0 τ), by simp, by simp⟩, ?_⟩
  rw [lat_basis B _ fun x => (b0 τ).toMatrix_mulVec_repr B x]
  have : Set.range B = M.subtype '' Set.range b := by
    rw [← Set.range_comp]
    congr 1
    funext i
    simp [B]
  rw [this, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]

private theorem cls_self (S : Set (Etau K τ)) : S ∈ cls τ S := ⟨1, by simp⟩

private theorem cls_smul (s : Kˣ) (S : Set (Etau K τ)) : cls τ (((s : K) • ·) '' S) = cls τ S := by
  ext T
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r * s, by simp [← Set.image_comp, Function.comp_def, mul_smul]⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r * s⁻¹, by simp [← Set.image_comp, Function.comp_def, smul_smul]⟩

private theorem cls_mul (t : Etau K τ) (S : Set (Etau K τ)) :
    cls τ ((t * ·) '' S) = (fun S => (t * ·) '' S) '' cls τ S := by
  ext T
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨_, ⟨r, rfl⟩, by simp [← Set.image_comp, Function.comp_def]⟩
  · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
    exact ⟨r, by simp [← Set.image_comp, Function.comp_def]⟩

private theorem cls_lat [IsFractionRing O K] {g g' : GL (Fin 2) K} :
    cls τ (LL O τ g) = cls τ (LL O τ g') ↔ g⁻¹ * g' ∈ ZK O K := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ : LL O τ g' ∈ cls τ (LL O τ g) := h ▸ cls_self _
    rw [← lat_sc] at hs
    refine zk_iff.2 ⟨s, (sc s * g)⁻¹ * g', kg_of_inv (lat_le.1 hs.subset) ?_, ?_⟩
    · have := lat_le.1 hs.superset
      rwa [_root_.mul_inv_rev, inv_inv]
    · rw [← mul_assoc, sc_comm s (sc s * g)⁻¹]
      group
  · intro h
    obtain ⟨s, k, hk, e⟩ := zk_iff.1 h
    have e' : (sc s * g)⁻¹ * g' = k := by
      rw [sc_comm, _root_.mul_inv_rev, mul_assoc, e, inv_mul_cancel_left]
    have : LL O τ g' = LL O τ (sc s * g) := by
      refine Set.Subset.antisymm (lat_le.2 (e' ▸ kg_ent hk)) (lat_le.2 ?_)
      have := kg_ent ((KG O K).inv_mem hk)
      rwa [← e', _root_.mul_inv_rev, inv_inv] at this
    rw [this, lat_sc, cls_smul]

end LL

section Main

variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {τ : K}

private theorem stab_iff (u : (Etau K τ)ˣ) (g : GL (Fin 2) K) :
    (∃ S, IsLat O τ S ∧ (∀ y ∈ S, (u : Etau K τ) * y ∈ S) ∧ cls τ (LL O τ g) = cls τ S) →
      Ent O (g⁻¹ * (jU (j0 τ) u * g)) := by
  rintro ⟨S, -, hs, e⟩
  obtain ⟨s, hs'⟩ : LL O τ g ∈ cls τ S := e ▸ cls_self _
  rw [← lat_le (τ := τ), lat_mul, hs']
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  exact ⟨_, hs y hy, by simp⟩

open Classical in
private theorem val_eq [IsDomain O] [IsDiscreteValuationRing O] {Δ : K} (hL : IsLoc O Δ) (χ : Kˣ →* ℂˣ) (hχ : Unr O χ)
    (u : (Etau K τ)ˣ) (s : Kˣ) (ε : Oˣ) (hu : QuadraticAlgebra.norm (u : Etau K τ) = algebraMap O K ε) (g : GL (Fin 2) K) :
    fZK O χ (g⁻¹ * jU (j0 τ) (su τ s * u) * g) = (((χ s)⁻¹ : ℂˣ) : ℂ) *
      if ∃ S, IsLat O τ S ∧ (∀ y ∈ S, (u : Etau K τ) * y ∈ S) ∧ cls τ (LL O τ g) = cls τ S then 1 else 0 := by
  haveI := hL.frac
  obtain ⟨h0, h1⟩ := fzkLaw O K Δ hL χ hχ
  have e : g⁻¹ * jU (j0 τ) (su τ s * u) * g = sc s * (g⁻¹ * (jU (j0 τ) u * g)) := by
    rw [map_mul, jU_su, ← mul_assoc, ← sc_comm]
    group
  have hd : ((g⁻¹ * (jU (j0 τ) u * g) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = algebraMap O K ε := by
    rw [Units.val_mul, Units.val_mul, ← mul_assoc, det_units_conj', ← hu, ← leftMulMatrixEmbedding_det_eq_norm]
    rfl
  rw [e]
  split_ifs with h
  · rw [h1 s _ (kg_of_det (stab_iff u g h) ε hd), mul_one]
  · rw [mul_zero]
    refine h0 _ fun hz => h ⟨_, lat_isLat g, fun y hy => ?_, rfl⟩
    have hz' : g⁻¹ * (jU (j0 τ) u * g) ∈ ZK O K :=
      ((ZK O K).mul_mem_cancel_left (zk_iff.2 ⟨s, 1, one_mem _, (mul_one _).symm⟩)).1 hz
    have := (lat_le (τ := τ)).2 (ent_of_zk ε hd hz')
    rw [lat_mul] at this
    exact this ⟨y, hy, rfl⟩

private theorem wcount_mul {T Y : Type} [Group T] [MulAction T Y] (C : Subgroup T) (c : ℂ) (k : Y → ℂ) :
    c * wcount C k = wcount C fun y => c * k y := by
  unfold wcount
  rw [mul_finsum]
  exact finsum_congr fun o => by ring

private theorem q_mul (t : (Etau K τ)ˣ) (x : Etau K τ) [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K]
    (X : Set (Set (Etau K τ))) (h : ∃ S, IsLat O τ S ∧ (∀ y ∈ S, x * y ∈ S) ∧ X = cls τ S) :
    ∃ S, IsLat O τ S ∧ (∀ y ∈ S, x * y ∈ S) ∧ (fun S => ((t : Etau K τ) * ·) '' S) '' X = cls τ S := by
  obtain ⟨S, hS, hs, rfl⟩ := h
  refine ⟨_, ?_, ?_, (cls_mul _ S).symm⟩
  · obtain ⟨g, rfl⟩ := isLat_lat hS
    rw [← lat_mul]
    exact lat_isLat _
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨_, hs y hy, mul_left_comm _ _ _⟩

end Main

end

theorem UpperTheory.V.Z.Sym.Loc.gLat :
    UpperTheory.V.Z.Sym.Loc.GLat := by
  classical
  intro O K _ _ _ _ _ Δ τ hL hτ j χ hj hχ z s ε hz
  haveI := hL.frac
  rw [(gConj O K Δ τ hL hτ j (j0 τ) hj leftMulMatrixEmbedding_omega_trace).2 χ hχ z]
  obtain ⟨u, rfl⟩ : ∃ u, z = su τ s * u := ⟨(su τ s)⁻¹ * z, by simp⟩
  have hx : ((s⁻¹ : Kˣ) : K) • ((su τ s * u : (Etau K τ)ˣ) : Etau K τ) = u := by
    rw [Units.val_mul, su_mul, smul_smul, Units.inv_mul, one_smul]
  have hu : QuadraticAlgebra.norm (u : Etau K τ) = algebraMap O K ε := by
    rw [Units.val_mul, su_mul, ← leftMulMatrixEmbedding_det_eq_norm, map_smul, det_smul, leftMulMatrixEmbedding_det_eq_norm, Fintype.card_fin, mul_comm] at hz
    exact mul_right_cancel₀ (pow_ne_zero 2 s.ne_zero) hz
  rw [hx]
  unfold gOrb orb vcount
  letI := mulAct (K := K) τ
  letI : MulAction (Etau K τ)ˣ (GL (Fin 2) K ⧸ ZK O K) := MulAction.compHom _ (jU (j0 τ))
  rw [wcount_mul]
  have hmk : ∀ g : GL (Fin 2) K, cls τ (LL O τ (QuotientGroup.mk g : GL (Fin 2) K ⧸ ZK O K).out) = cls τ (LL O τ g) :=
    fun g => cls_lat.2 (QuotientGroup.eq.1 (QuotientGroup.out_eq' _))
  have heq : ∀ (t : (Etau K τ)ˣ) (y : GL (Fin 2) K ⧸ ZK O K), cls τ (LL O τ (t • y).out) = t • cls τ (LL O τ y.out) := by
    intro t y
    have : t • y = QuotientGroup.mk (jU (j0 τ) t * y.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' y]
      rfl
    rw [this, hmk, lat_mul, cls_mul]
    rfl
  have hq : ∀ (t : (Etau K τ)ˣ) (X : Set (Set (Etau K τ))),
      (∃ S, IsLat O τ S ∧ (∀ y ∈ S, (u : Etau K τ) * y ∈ S) ∧ t • X = cls τ S) ↔
        ∃ S, IsLat O τ S ∧ (∀ y ∈ S, (u : Etau K τ) * y ∈ S) ∧ X = cls τ S := by
    intro t X
    refine ⟨fun h => ?_, q_mul t _ X⟩
    have := q_mul t⁻¹ _ _ h
    change ∃ S, _ ∧ _ ∧ t⁻¹ • t • X = _ at this
    rwa [inv_smul_smul] at this
  simp only [MonoidHom.id_apply]
  refine wTrans _ _ _ _ _ _ (fun y X => X = cls τ (LL O τ y.out)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro t y
    rw [val_eq hL χ hχ u s ε hu, val_eq hL χ hχ u s ε hu, heq, if_congr (hq _ _) rfl rfl]
  · intro t X
    rw [if_congr (hq _ _) rfl rfl]
  · rintro t y _ rfl
    exact (heq t y).symm
  · rintro y _ rfl
    exact val_eq hL χ hχ u s ε hu _
  · exact fun y _ => ⟨_, rfl, fun _ h => h⟩
  · intro X hX
    have h : ∃ S, IsLat O τ S ∧ (∀ y ∈ S, (u : Etau K τ) * y ∈ S) ∧ X = cls τ S := by
      by_contra h
      exact hX (by rw [if_neg h, mul_zero])
    obtain ⟨S, hS, -, rfl⟩ := h
    obtain ⟨g, rfl⟩ := isLat_lat hS
    refine ⟨QuotientGroup.mk g, (hmk g).symm, fun y hy => ?_⟩
    rw [← QuotientGroup.out_eq' y]
    exact QuotientGroup.eq.2 (cls_lat.1 hy.symm)
