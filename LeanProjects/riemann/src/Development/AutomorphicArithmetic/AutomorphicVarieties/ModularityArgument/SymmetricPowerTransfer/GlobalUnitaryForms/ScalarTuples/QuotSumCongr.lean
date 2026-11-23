import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.ResidualAutomorphyOfLinkedEnds
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.EmbAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.GlobNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.IsScal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.CommOfConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FzdLaw

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc MulAction

private theorem quot_sum_congr {Y : Type} (s s' : Setoid Y) (h : s = s') (k k' : Y → ℂ) (hk : k = k') :
    (∑ᶠ o : Quotient s, k o.out) = ∑ᶠ o : Quotient s', k' o.out := by
  subst h; subst hk; rfl

private theorem gqOn_surj {H' H G : Type} [Group H'] [Group H] [Group G] (e : H' →* H) (he : Function.Surjective e)
    (j : H →* G) (H₀ : Subgroup H) (U : Subgroup G) (k : G ⧸ U → ℂ) :
    gqOn (j.comp e) (H₀.comap e) U k = gqOn j H₀ U k := by
  letI a : MulAction H (G ⧸ U) := MulAction.compHom _ j
  letI a' : MulAction H' (G ⧸ U) := MulAction.compHom _ (j.comp e)
  have hs : ∀ (x : H') (y : G ⧸ U), x • y = e x • y := fun _ _ => rfl
  refine quot_sum_congr (orbitRel H' (G ⧸ U)) (orbitRel H (G ⧸ U)) ?_
    (fun y => k y / ((H₀.comap e).relIndex (stabilizer H' y) : ℂ)) (fun y => k y / (H₀.relIndex (stabilizer H y) : ℂ)) ?_
  · ext x y
    rw [orbitRel_apply, orbitRel_apply, mem_orbit_iff, mem_orbit_iff]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨e g, hg⟩
    · rintro ⟨g, hg⟩
      obtain ⟨g', rfl⟩ := he g
      exact ⟨g', hg⟩
  · funext y
    have : stabilizer H' y = (stabilizer H y).comap e := by
      ext x; simp only [mem_stabilizer_iff, Subgroup.mem_comap, hs]
    rw [this, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective he]

section Field

variable {K : Type} [Field K] {Δ : K}

private theorem mem_DX_k (g : GL (Fin 2) (Lsq K Δ)) : g ∈ DX Δ ↔
    ((g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 1 1 = star ((g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 0) ∧
    (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 1 0 = - star ((g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 1)) := by
  have e : g ∈ DX Δ ↔ (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map (starRingEnd _) =
      !![0, -1; 1, 0] * (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * !![0, 1; -1, 0] := by
    unfold DX
    exact Units.ext_iff
  rw [e]
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, starRingEnd_apply] at h00 h01
    exact ⟨h00.symm, by rw [h01, neg_neg]⟩
  · rintro ⟨h1, h2⟩
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [starRingEnd_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, h1, h2]

private theorem tr_det_rat (g : DX Δ) : ∃ a b : K, (mt g).trace = algebraMap K _ a ∧ (mt g).det = algebraMap K _ b ∧ b ≠ 0 := by
  obtain ⟨h1, h2⟩ : mt g 1 1 = star (mt g 0 0) ∧ mt g 1 0 = - star (mt g 0 1) := (mem_DX_k _).1 g.2
  have hd : (mt g).det = algebraMap K _ (QuadraticAlgebra.norm (mt g 0 0) + QuadraticAlgebra.norm (mt g 0 1)) := by
    rw [Matrix.det_fin_two, h1, h2, map_add, QuadraticAlgebra.algebraMap_norm_eq_mul_star, QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    ring
  refine ⟨2 * (mt g 0 0).re, _, ?_, hd, ?_⟩
  · rw [Matrix.trace_fin_two, h1]
    ext <;> simp [two_mul]
  · intro h
    rw [h, map_zero] at hd
    exact (Matrix.isUnits_det_units (g : GL (Fin 2) (Lsq K Δ))).ne_zero hd

private theorem mt_mul (a b : DX Δ) : mt (a * b) = mt a * mt b := rfl

private theorem mt_inj {a b : DX Δ} (h : mt a = mt b) : a = b := Subtype.ext (Units.ext h)

private theorem tr_conj (x g : DX Δ) : (mt (x⁻¹ * g * x)).trace = (mt g).trace := by
  rw [mt_mul, Matrix.trace_mul_comm, ← mt_mul, ← mul_assoc, mul_inv_cancel, one_mul]

private theorem det_conj (x g : DX Δ) : (mt (x⁻¹ * g * x)).det = (mt g).det := by
  rw [mt_mul, Matrix.det_mul_comm, ← mt_mul, ← mul_assoc, mul_inv_cancel, one_mul]

private theorem mem_ZD (z : DX Δ) : z ∈ ZD Δ ↔ ∃ s : Kˣ, mt z = algebraMap K (Lsq K Δ) s • 1 := by
  unfold ZD
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  refine exists_congr fun s => ?_
  rw [← Units.val_inj, eq_comm]
  have : ((((GeneralLinearGroup.scalar (Fin 2)).comp (Units.map (algebraMap K (Lsq K Δ) : K →* Lsq K Δ))) s : GL (Fin 2) (Lsq K Δ)) :
      Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = algebraMap K (Lsq K Δ) s • 1 := by
    ext i j : 1
    simp [Matrix.diagonal_apply, Matrix.one_apply]
  rw [this]

private theorem alg_inj : Function.Injective (algebraMap K (Lsq K Δ)) := (algebraMap K (Lsq K Δ)).injective

private theorem one_add {τ : K} {γ : DX Δ} {j : (Etau K τ)ˣ →* DX Δ} (hj : IsEmb τ γ j) {z : (Etau K τ)ˣ}
    (hz : (z : Etau K τ) = 1 + QuadraticAlgebra.omega) : mt (j z) = 1 + mt γ := by
  rw [hj z, hz]
  simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem det_one_add (M : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) : (1 + M).det = 1 + M.trace + M.det := by
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.add_apply, Matrix.one_apply]
  simp
  ring

private theorem tr_det_one_add {τ : K} {γ δ : DX Δ} (hγ : HasTr γ τ) (h : mt δ = 1 + mt γ) :
    (mt δ).trace = algebraMap K _ (2 + τ) ∧ (mt δ).det = algebraMap K _ (2 + τ) := by
  rw [h, det_one_add, Matrix.trace_add, hγ.1, hγ.2, Matrix.trace_one, map_add, map_ofNat]
  refine ⟨by simp, by ring⟩

private theorem rel_inj {a b : K} (hb : b ≠ 0) {δ δ' x z : DX Δ} (hz : z ∈ ZD Δ)
    (h1 : (mt δ).trace = algebraMap K _ a) (h2 : (mt δ).det = algebraMap K _ a)
    (h1' : (mt δ').trace = algebraMap K _ b) (h2' : (mt δ').det = algebraMap K _ b)
    (h : δ' = x⁻¹ * δ * x * z) : a = b ∧ z = 1 := by
  obtain ⟨s, hs⟩ := (mem_ZD z).1 hz
  have e : mt δ' = algebraMap K (Lsq K Δ) s • mt (x⁻¹ * δ * x) := by
    rw [h, mt_mul, hs, Matrix.mul_smul, Matrix.mul_one]
  rw [e, Matrix.trace_smul, tr_conj, h1, smul_eq_mul, ← map_mul] at h1'
  rw [e, Matrix.det_smul, det_conj, h2, Fintype.card_fin, ← map_pow, ← map_mul] at h2'
  have e1 := alg_inj h1'
  have e2 := alg_inj h2'
  have hs1 : (s : K) = 1 := by
    apply mul_right_cancel₀ hb
    rw [one_mul]
    calc (s : K) * b = s * (s * a) := by rw [e1]
      _ = b := by rw [← e2]; ring
  refine ⟨by rw [← e1, hs1, one_mul], mt_inj ?_⟩
  rw [hs, hs1, map_one, one_smul]
  rfl

private theorem scal_ex (s : Kˣ) : ∃ z ∈ ZD Δ, mt z = algebraMap K (Lsq K Δ) s • 1 := by
  have hd : IsUnit (algebraMap K (Lsq K Δ) s • (1 : Matrix (Fin 2) (Fin 2) (Lsq K Δ))) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, Matrix.det_one, mul_one]
    exact (s.isUnit.map _).pow _
  have hm : hd.unit ∈ DX Δ := by
    rw [mem_DX_k, IsUnit.unit_spec]
    constructor
    · ext <;> simp
    · simp
  exact ⟨⟨hd.unit, hm⟩, (mem_ZD _).2 ⟨s, rfl⟩, rfl⟩

private theorem cover {τ a b : K} {g : DX Δ} (h1 : (mt g).trace = algebraMap K _ a) (h2 : (mt g).det = algebraMap K _ b)
    (hb : b ≠ 0) (hτ : 2 + τ ≠ 0) (h : a ^ 2 = (2 + τ) * b) :
    ∃ γ : DX Δ, HasTr γ τ ∧ ∃ z ∈ ZD Δ, mt g = (1 + mt γ) * mt z := by
  have ha : a ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hτ hb (by rw [← h]; ring)
  have hs : a / (2 + τ) ≠ 0 := div_ne_zero ha hτ
  obtain ⟨z, hz, hz'⟩ := scal_ex (Δ := Δ) (Units.mk0 _ hs)
  set r : K := (2 + τ) / a with hr
  have hra : r * a = 2 + τ := by rw [hr]; field_simp
  have hrb : r ^ 2 * b = 2 + τ := by
    rw [hr, div_pow, h]; field_simp
  set M : Matrix (Fin 2) (Fin 2) (Lsq K Δ) := algebraMap K (Lsq K Δ) r • mt g - 1 with hM
  have hM1 : 1 + M = algebraMap K (Lsq K Δ) r • mt g := by rw [hM]; abel
  have htr : M.trace = algebraMap K _ τ := by
    rw [hM, Matrix.trace_sub, Matrix.trace_smul, h1, smul_eq_mul, ← map_mul, hra, Matrix.trace_one, map_add, map_ofNat]
    simp
  have hdet : M.det = 1 := by
    have := det_one_add M
    rw [hM1, Matrix.det_smul, h2, Fintype.card_fin, ← map_pow, ← map_mul, hrb, htr, map_add, map_ofNat] at this
    linear_combination -this
  have hd : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet]
    exact isUnit_one
  obtain ⟨k1, k2⟩ : mt g 1 1 = star (mt g 0 0) ∧ mt g 1 0 = - star (mt g 0 1) := (mem_DX_k _).1 g.2
  have hst : star (algebraMap K (Lsq K Δ) r) = algebraMap K (Lsq K Δ) r := by ext <;> simp
  have hm : hd.unit ∈ DX Δ := by
    rw [mem_DX_k, IsUnit.unit_spec, hM]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, k1, k2, star_sub, star_mul', hst]
    simp
  refine ⟨⟨hd.unit, hm⟩, ⟨hdet, htr⟩, z, hz, ?_⟩
  change mt g = (1 + M) * mt z
  rw [hM1, hz', Matrix.mul_smul, Matrix.mul_one, smul_smul, ← map_mul, Units.val_mk0]
  have : a / (2 + τ) * r = 1 := by rw [hr]; field_simp
  rw [this, map_one, one_smul]

private theorem unit_ex {τ : K} (hτ : 2 + τ ≠ 0) : ∃ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + QuadraticAlgebra.omega := by
  have : (1 + QuadraticAlgebra.omega : Etau K τ) * ⟨(1 + τ) / (2 + τ), -1 / (2 + τ)⟩ = 1 := by
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring
  exact ⟨Units.mkOfMulEqOne _ _ this, rfl⟩

private theorem two_add_ne {τ : K} (h : τ ^ 2 - 4 ≠ 0) : 2 + τ ≠ 0 := fun e => h (by linear_combination (τ - 2) * e)

private theorem reg_of_not_int {O : Type} [CommRing O] [Algebra O K] {τ : K} (h : ¬ IsIntegral O τ) : τ ^ 2 - 4 ≠ 0 := by
  intro e
  have h2 : IsIntegral O (2 : K) := by
    have := (isIntegral_one (R := O) (B := K)).add (isIntegral_one (R := O) (B := K))
    rwa [one_add_one_eq_two] at this
  have : (τ - 2) * (τ + 2) = 0 := by linear_combination e
  rcases mul_eq_zero.1 this with e | e
  · exact h (by rw [sub_eq_zero.1 e]; exact h2)
  · exact h (by rw [eq_neg_of_add_eq_zero_left e]; exact h2.neg)

private theorem lmap_alg {K' : Type} [Field K'] (f : K →+* K') (a : K) :
    lmap f Δ (algebraMap K (Lsq K Δ) a) = algebraMap K' (Lsq K' (f Δ)) (f a) := by
  ext <;> simp [lmap]

private theorem local_tau {K' : Type} [Field K'] (f : K →+* K') {g : DX Δ} {g' y : DX (f Δ)} (hg : mt g' = (mt g).map (lmap f Δ))
    {a b : K} (h1 : (mt g).trace = algebraMap K _ a) (h2 : (mt g).det = algebraMap K _ b) (hb : b ≠ 0) {τ : K'}
    (h : (mt (y⁻¹ * g' * y)).trace ^ 2 = algebraMap K' _ (2 + τ) * (mt (y⁻¹ * g' * y)).det) : f (a ^ 2 / b - 2) = τ := by
  have e1 : (mt g').trace = algebraMap K' _ (f a) := by
    rw [hg, ← lmap_alg, ← h1]
    simp [Matrix.trace_fin_two]
  have e2 : (mt g').det = algebraMap K' _ (f b) := by
    rw [hg, ← lmap_alg, ← h2]
    simp [Matrix.det_fin_two]
  rw [tr_conj, det_conj, e1, e2, ← map_pow, ← map_mul] at h
  have e := alg_inj h
  have hb' : f b ≠ 0 := (map_ne_zero f).2 hb
  rw [map_sub, map_div₀, map_pow, map_ofNat, e]
  field_simp
  ring

private theorem term_eq [CharZero K] {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (B : Base (DX Δ) G V) (hΓ : B.Γ₀ = ZD Δ)
    (hΔ : Δ ≠ 0) {τ : K} (hτ : τ ^ 2 - 4 ≠ 0) {γ : DX Δ} (hγ : HasTr γ τ) {j : (Etau K τ)ˣ →* DX Δ} (hj : IsEmb τ γ j)
    {z : (Etau K τ)ˣ} (hz : (z : Etau K τ) = 1 + QuadraticAlgebra.omega) (f : G → ℂ) :
    (Base.Tw.one B).term f (j z) = LinearMap.trace ℂ V (B.W (j z)) *
      gqOn (B.ι.comp j) (scalE τ) B.U (fun y => f (y.out⁻¹ * B.ι (j z) * y.out)) := by
  obtain ⟨-, h2, h3⟩ := (embAlg K Δ τ hΔ hτ γ hγ).2.1 j hj
  have hδ := one_add hj hz
  obtain ⟨t1, t2⟩ := tr_det_one_add hγ hδ
  have hc : ∀ x, x ∈ (Base.Tw.one B).Cent (j z) ↔ x ∈ j.range := fun x => by
    constructor
    · rintro ⟨w, hw, e⟩
      change x⁻¹ * j z * x = j z * w at e
      rw [hΓ] at hw
      have e' : j z = x⁻¹ * j z * x * w⁻¹ := by rw [e, mul_inv_cancel_right]
      have hw1 := (rel_inj (two_add_ne hτ) (inv_mem hw) t1 t2 t1 t2 e').2
      rw [hw1, mul_one, mul_assoc, eq_inv_mul_iff_mul_eq] at e'
      have e2 := congrArg mt e'
      rw [mt_mul, mt_mul, hδ, mul_add, add_mul, mul_one, one_mul, add_right_inj] at e2
      exact (h2 x).2 (mt_inj e2)
    · rintro ⟨w, rfl⟩
      refine ⟨1, one_mem _, ?_⟩
      change (j w)⁻¹ * j z * j w = j z * 1
      rw [← map_inv, ← map_mul, ← map_mul, mul_one, mul_right_comm, inv_mul_cancel, one_mul]
  let e : (Etau K τ)ˣ →* (Base.Tw.one B).Cent (j z) := j.codRestrict _ fun w => (hc _).2 ⟨w, rfl⟩
  have he : Function.Surjective e := fun x => by
    obtain ⟨w, hw⟩ := (hc x).1 x.2
    exact ⟨w, Subtype.ext hw⟩
  have key := gqOn_surj e he (B.ι.comp ((Base.Tw.one B).Cent (j z)).subtype) (B.Γ₀.subgroupOf _) B.U ((Base.Tw.one B).ker f (j z))
  have k2 : (B.Γ₀.subgroupOf ((Base.Tw.one B).Cent (j z))).comap e = scalE τ := by
    rw [← h3, hΓ]
    rfl
  rw [k2] at key
  unfold Base.Tw.term
  rw [← key]
  rfl

end Field

section Global

variable {F : Type} [Field F] [NumberField F] {Δ : F} {D : Dat Δ}

private theorem supp (hD : D.Ok) (t : Dat.Par F) (g : DA Δ) (h : D.FK t g ≠ 0) (v : Pl F) (hv : v ∈ D.Sg) :
    (D.S v).fK (t v) (g.1 v) ≠ 0 := by
  classical
  have hfin : (Function.mulSupport fun v => D.fKv t v (g.1 v)).Finite := by
    refine (D.Sg.finite_toSet.union (Filter.eventually_cofinite.1 ((rpg _ _).ae g))).subset fun w hw => ?_
    by_contra hn
    rw [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hn
    apply hw
    have := (fzdLaw (Ov w) (Kv w) (cv w Δ) (hD.off w hn.1) (D.χ w) (hD.chi w).1).2 1 1 (g.1 w) (by simp [IsScal]) hn.2
    have hw' : w ∉ D.Sg := hn.1
    rw [one_mul] at this
    simp only [Dat.fKv, if_neg hw', this, map_one, inv_one, Units.val_one]
  intro h0
  apply h
  unfold Dat.FK
  refine finprod_eq_zero _ v ?_ hfin
  simp only [Dat.fKv, if_pos hv, h0]

private theorem real_emb (hD : D.Ok) : Nonempty (F →+* ℝ) := by
  have := hD.real
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact ⟨InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)⟩

private theorem cover_glob (hD : D.Ok) {ι : DX Δ →* DA Δ} (hι : IsIotaD ι) {t : Dat.Par F} (ht : D.Cone t) (g : DX Δ) (y : DA Δ)
    (h : D.FK t (y⁻¹ * ι g * y) ≠ 0) :
    ∃ τ, D.Good t τ ∧ ∃ γ : DX Δ, HasTr γ τ ∧ ∃ z ∈ ZD Δ, mt g = (1 + mt γ) * mt z := by
  obtain ⟨a, b, h1, h2, hb⟩ := tr_det_rat g
  have hadm : ∀ v ∈ D.Sg, Ind (D.S v).H (cv v (a ^ 2 / b - 2)) (t v) := fun v hv => by
    obtain ⟨τ, hτ, e⟩ := (hD.sig v hv).K_supp (t v) (ht v hv) _ (supp hD t _ h v hv)
    have e' : (y⁻¹ * ι g * y).1 v = (y.1 v)⁻¹ * (ι g).1 v * y.1 v := rfl
    rw [e'] at e
    rw [local_tau (cv v) (hι g v) h1 h2 hb e]
    exact hτ
  have hreg : (a ^ 2 / b - 2) ^ 2 - 4 ≠ 0 := by
    obtain ⟨v, hv⟩ := hD.ne
    have := reg_of_not_int ((hD.sig v hv).reg (t v) (ht v hv) _ (hadm v hv)).2
    intro e
    apply this
    have e2 := congrArg (cv v) e
    rwa [map_sub, map_pow, map_ofNat, map_zero] at e2
  obtain ⟨γ, hγ, r⟩ := cover h1 h2 hb (two_add_ne hreg) (by field_simp; ring)
  exact ⟨_, ⟨(embEx F Δ D hD _).2 γ hγ hreg, hadm⟩, γ, hγ, r⟩

end Global

end UpperTheory.V.Z.Sym.Glob

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob in
theorem UpperTheory.V.Z.Sym.Glob.sideK :
    UpperTheory.V.Z.Sym.Glob.SideK := by
  classical
  intro F _ _ Δ D hD
  refine ⟨∏ v ∈ D.Sg, (D.S v).cK, Finset.prod_pos fun v hv => (hD.sig v hv).cK, ?_⟩
  intro V _ _ _ ch B hB t ht
  obtain ⟨σ⟩ := real_emb hD
  have hΔ : Δ ≠ 0 := fun e => by
    have := hD.neg σ
    rw [e, map_zero] at this
    exact lt_irrefl _ this
  have hreg : ∀ i : {τ // D.Good t τ}, i.1 ^ 2 - 4 ≠ 0 := fun i e => by
    have := i.2.1 σ
    rw [e, map_zero] at this
    exact lt_irrefl _ this
  choose γ hγ using fun i : {τ // D.Good t τ} => (embEx F Δ D hD i.1).1 i.2.1
  choose j hj using fun i : {τ // D.Good t τ} => (embAlg F Δ i.1 hΔ (hreg i) (γ i) (hγ i)).1
  choose z hz using fun i : {τ // D.Good t τ} => unit_ex (two_add_ne (hreg i))
  have hδ := fun i => one_add (hj i) (hz i)
  have htd := fun i => tr_det_one_add (hγ i) (hδ i)
  obtain ⟨hfin, htest⟩ := finK F Δ D hD V ch B hB
  have hι : IsIotaD B.ι := hB.ι
  have key := (Tf.trace _ _ V B hfin (Base.Tw.one B) (D.FK t) (htest t ht) {τ // D.Good t τ} (fun i => j i (z i)) ?_ ?_).2
  · rw [key]
    have e : ∀ i : {τ // D.Good t τ}, (Base.Tw.one B).term (D.FK t) (j i (z i)) =
        ((∏ v ∈ D.Sg, (D.S v).cK : ℝ) : ℂ) * (ch i.1 * ms i.1 * D.nK i.1) := fun i => by
      rw [term_eq B hB.Γ₀ hΔ (hreg i) (hγ i) (hj i) (hz i), hB.tr _ _ (htd i).1 (htd i).2, hB.U,
        gqK F Δ D hD B.ι hι t ht i.1 i.2.1 (γ i) (j i) (hγ i) (hj i) (z i) (hz i)]
      have : one (D.admitted t i.1) = 1 := if_pos i.2.2
      rw [this]
      push_cast
      ring
    rw [finsum_congr e, ← mul_finsum, Dat.sumK,
      finsum_subtype_eq_finsum_cond (f := fun τ => ch τ * ms τ * D.nK τ) (p := D.Good t)]
    congr 1
    refine finsum_congr fun τ => ?_
    rw [finsum_eq_if, one]
    split_ifs <;> simp
  · rintro i i' ⟨x, w, hw, e⟩
    rw [hB.Γ₀] at hw
    have := (rel_inj (two_add_ne (hreg i')) hw (htd i).1 (htd i).2 (htd i').1 (htd i').2 e).1
    exact Subtype.ext (add_left_cancel this)
  · rintro g ⟨y, hy⟩
    obtain ⟨τ, hτ, γ', hγ', w, hw, e⟩ := cover_glob hD hι ht g y.out hy
    obtain ⟨x, hx⟩ := (embAlg F Δ τ hΔ (hreg ⟨τ, hτ⟩) (γ ⟨τ, hτ⟩) (hγ ⟨τ, hτ⟩)).2.2 γ' hγ'
    refine ⟨⟨τ, hτ⟩, x, w, hB.Γ₀ ▸ hw, mt_inj ?_⟩
    change mt g = mt (x⁻¹ * j ⟨τ, hτ⟩ (z ⟨τ, hτ⟩) * x * w)
    have hx1 : mt x⁻¹ * mt x = 1 := by rw [← mt_mul, inv_mul_cancel]; rfl
    rw [e, hx, mt_mul, mt_mul, mt_mul, mt_mul, mt_mul, hδ, mul_add (mt x⁻¹), add_mul _ _ (mt x), mul_one, hx1]
