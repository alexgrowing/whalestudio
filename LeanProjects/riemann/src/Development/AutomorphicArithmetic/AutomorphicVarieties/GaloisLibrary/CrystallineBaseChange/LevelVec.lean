import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.MemMirabIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.DirChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosNatMemOpenAdeleSubgroup

open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd UpperTheory.V.Af UpperTheory.V.Af.Nf Filter Topology

namespace UpperTheory.V.Br

private theorem lv_zero {x : Af ℚ} (h : ∀ n : ℕ, ∃ y ∈ Ohat ℚ, x = (n.factorial : ℕ) * y) : x = 0 := by
  by_contra hx
  have hc : IsCompact (Ohat ℚ : Set (Af ℚ)) := by
    convert GroundTheory.Global.isCompact_integralFiniteAdeles ℚ using 1
    exact Set.ext fun _ => mem_Ohat
  have key : ∀ᶠ d in 𝓝 (0 : Af ℚ), ∀ z ∈ (Ohat ℚ : Set (Af ℚ)), x ≠ d * z :=
    hc.eventually_forall_of_forall_eventually fun z _ =>
      (isOpen_ne_fun continuous_const (continuous_fst.mul continuous_snd)).mem_nhds (by simpa using hx)
  obtain ⟨n, hn⟩ := ((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele ℚ).eventually key).exists
  obtain ⟨y, hy, e⟩ := h n
  exact hn y hy e

private theorem lv_KLev {U : Set (GL (Fin 2) (Af ℚ))} (hU : IsOpen U) (h1 : 1 ∈ U) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ g ∈ KLev ℚ 2 M, g ∈ U := by
  by_contra h
  push Not at h
  have hcl : ∀ n : ℕ, IsClosed ((KLev ℚ 2 n.factorial : Set (GL (Fin 2) (Af ℚ))) ∩ Uᶜ) := fun n =>
    (Subgroup.isClosed_of_isOpen _ (isOpen_KLev n.factorial_pos)).inter hU.isClosed_compl
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n : ℕ => (KLev ℚ 2 n.factorial : Set (GL (Fin 2) (Af ℚ))) ∩ Uᶜ)
    (fun n => Set.inter_subset_inter_left _ (KLev_le_of_dvd (Nat.factorial_dvd_factorial n.le_succ)))
    (fun n => h _ n.factorial_pos) ((isCompact_KLev (Nat.factorial_pos 0)).inter_right hU.isClosed_compl) hcl
  rw [Set.mem_iInter] at hg
  refine (hg 0).2 ?_
  rwa [show g = 1 from Units.ext (Matrix.ext fun a b => sub_eq_zero.1 (lv_zero fun n => (mem_KLev.1 (hg n).1).2.2 a b))]

private theorem lv_eig {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : G →* Module.End ℂ V) {N : ℕ} [NeZero N]
    (δ : G →* ZMod N) (W : Submodule ℂ V) (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) {v : V} (hv : v ∈ W) (h0 : v ≠ 0)
    (hk : ∀ g, δ g = 1 → ρ g v = v) :
    ∃ (χ : DirichletCharacter ℂ N), ∃ w ∈ W, w ≠ 0 ∧ ∀ g, χ (δ g) • ρ g w = w := by
  classical
  let f : ZMod N → V := fun a => if h : ∃ g, δ g = a then ρ h.choose v else 0
  have hf : ∀ g, f (δ g) = ρ g v := fun g => by
    have h : ∃ g', δ g' = δ g := ⟨g, rfl⟩
    have := hk (g⁻¹ * h.choose) (by rw [map_mul, h.choose_spec, ← map_mul, inv_mul_cancel, map_one])
    simp only [f, dif_pos h]
    conv_rhs => rw [← this]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have hm : ∀ g a, ρ g (f a) = f (δ g * a) := fun g a => by
    by_cases h : ∃ g, δ g = a
    · obtain ⟨g', rfl⟩ := h
      rw [← map_mul, hf, hf, map_mul, Module.End.mul_apply]
    · have h' : ¬ ∃ g', δ g' = δ g * a := fun ⟨g', e⟩ => h ⟨g⁻¹ * g', by
        rw [map_mul, e, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]⟩
      simp only [f, dif_neg h, dif_neg h', map_zero]
  have hfW : ∀ a, f a ∈ W := fun a => by
    simp only [f]; split_ifs
    · exact hW _ _ hv
    · exact W.zero_mem
  have hs : ∑ χ : DirichletCharacter ℂ N, ∑ a, χ a • f a ≠ 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, DirichletCharacter.sum_characters_eq, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [← map_one δ, hf, map_one]
    exact smul_ne_zero (Nat.cast_ne_zero.2 (Nat.totient_pos.2 (NeZero.pos N)).ne') h0
  obtain ⟨χ, -, hχ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  refine ⟨χ, _, W.sum_mem fun a _ => W.smul_mem _ (hfW a), hχ, fun g => ?_⟩
  rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (δ.toHomUnits g).mulLeft _ _ fun a => ?_
  rw [map_smul, hm, smul_smul, ← map_mul]
  rfl

private theorem lv_red {M : ℕ} (hM : 1 ≤ M) : ∃ r : ↥(Ohat ℚ) →* ZMod M,
    ∀ (x : ↥(Ohat ℚ)) (d : ℤ), r x = d ↔ ∃ y ∈ Ohat ℚ, (x : Af ℚ) - d = M * y := by
  have hM' : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hi : algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * M = 1 := by
    rw [← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, inv_mul_cancel₀ hM', map_one]
  have uq : ∀ {x : Af ℚ} {d e : ℤ}, (∃ y ∈ Ohat ℚ, x - d = M * y) → (∃ y ∈ Ohat ℚ, x - e = M * y) → (d : ZMod M) = e := by
    rintro x d e ⟨y, hy, hd⟩ ⟨z, hz, he⟩
    have h1 : algebraMap ℚ (Af ℚ) ((M : ℚ)⁻¹ * ((e : ℚ) - d)) = y - z := by
      rw [map_mul, map_sub, map_intCast, map_intCast]
      linear_combination algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * (hd - he) + (y - z) * hi
    obtain ⟨n, hn⟩ := ratAd.2.2 _ (h1 ▸ sub_mem hy hz)
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    refine ⟨n, ?_⟩
    rw [inv_mul_eq_iff_eq_mul₀ hM'] at hn
    exact_mod_cast hn
  choose f hf using fun x : ↥(Ohat ℚ) => ratAd.2.1 M hM x x.2
  refine ⟨⟨⟨fun x => f x, ?_⟩, fun a b => ?_⟩, fun x d => ⟨fun h => ?_, uq (hf x)⟩⟩
  · simpa using uq (e := 1) (hf 1) ⟨0, zero_mem _, by simp⟩
  · obtain ⟨y, hy, h1⟩ := hf a
    obtain ⟨z, hz, h2⟩ := hf b
    have := uq (e := f a * f b) (hf (a * b)) ⟨a * z + f b * y,
      add_mem (mul_mem a.2 hz) (mul_mem (intCast_mem _ _) hy), by
        rw [Subring.coe_mul, Int.cast_mul]
        linear_combination (a : Af ℚ) * h2 + (f b : Af ℚ) * h1⟩
    simpa using this
  · obtain ⟨n, hn⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h
    obtain ⟨y, hy, h1⟩ := hf x
    have hn' : (d : Af ℚ) - f x = M * n := by exact_mod_cast congrArg (Int.cast : ℤ → Af ℚ) hn
    exact ⟨y - n, sub_mem hy (intCast_mem _ _), by linear_combination h1 - hn'⟩

private theorem lv_det {N : ℕ} {g : GL (Fin 2) (Af ℚ)} (hg : g ∈ K1G N) :
    ((Matrix.GeneralLinearGroup.det g : (Af ℚ)ˣ) : Af ℚ) ∈ Ohat ℚ := by
  have h := ((memK N g).1 hg).1
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  exact sub_mem (mul_mem (h 0 0) (h 1 1)) (mul_mem (h 0 1) (h 1 0))

private theorem lv_conj {R : Type} [CommRing R] (m : Rˣ) (g : GL (Fin 2) R) :
    (aff m 0 * g * (aff m 0)⁻¹).val = !![g 0 0, m * g 0 1; g 1 0 * (m⁻¹ : Rˣ), g 1 1] := by
  change (aff m 0).val * g.val * (aff m 0).inv = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  rw [mul_right_comm, Units.mul_inv, one_mul]

private theorem lv_int {M : ℕ} {m : (Af ℚ)ˣ} (hm : (m : Af ℚ) = M) {g : GL (Fin 2) (Af ℚ)} (hg : g ∈ K1G (M * M)) (a b : Fin 2) :
    (aff m 0 * g * (aff m 0)⁻¹ : GL (Fin 2) (Af ℚ)) a b ∈ Ohat ℚ := by
  obtain ⟨h, -, ⟨y, hy, e⟩, -⟩ := (memK _ g).1 hg
  revert a b
  rw [lv_conj]
  refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨h 0 0, mul_mem (hm ▸ natCast_mem _ M) (h 0 1)⟩,
    Fin.forall_fin_two.2 ⟨?_, h 1 1⟩⟩
  change g 1 0 * (m⁻¹ : (Af ℚ)ˣ) ∈ _
  rw [e, Nat.cast_mul, ← hm, mul_assoc, mul_assoc, mul_comm, mul_assoc, mul_assoc, Units.inv_mul, mul_one]
  exact mul_mem (hm ▸ natCast_mem _ M) hy

private theorem lv_mem {M : ℕ} {m : (Af ℚ)ˣ} (hm : (m : Af ℚ) = M) {g : GL (Fin 2) (Af ℚ)} (hg : g ∈ K1G (M * M))
    (hd : ∃ y ∈ Ohat ℚ, ((Matrix.GeneralLinearGroup.det g : (Af ℚ)ˣ) : Af ℚ) - (1 : ℤ) = (M * M : ℕ) * y) :
    aff m 0 * g * (aff m 0)⁻¹ ∈ KLev ℚ 2 M := by
  refine mem_KLev.2 ⟨lv_int hm hg, fun a b => ?_, ?_⟩
  · have := lv_int hm (inv_mem hg) a b
    rwa [show aff m 0 * g⁻¹ * (aff m 0)⁻¹ = (aff m 0 * g * (aff m 0)⁻¹)⁻¹ by group] at this
  obtain ⟨h, -, ⟨w, hw, e1⟩, z, hz, e2⟩ := (memK _ g).1 hg
  obtain ⟨y, hy, e3⟩ := hd
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Int.cast_one] at e3
  rw [Nat.cast_mul] at e1 e2 e3
  have hM := natCast_mem (Ohat ℚ) M
  rw [lv_conj]
  refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨⟨M * (y - g 0 0 * z + g 0 1 * w),
    mul_mem hM (add_mem (sub_mem hy (mul_mem (h 0 0) hz)) (mul_mem (h 0 1) hw)), ?_⟩, ⟨_, h 0 1, ?_⟩⟩,
    Fin.forall_fin_two.2 ⟨⟨w, hw, ?_⟩, ⟨M * z, mul_mem hM hz, ?_⟩⟩⟩
  · change g 0 0 - 1 = _
    linear_combination e3 - g 0 0 * e2 + g 0 1 * e1
  · change m * g 0 1 - 0 = _
    rw [hm, sub_zero]
  · change g 1 0 * (m⁻¹ : (Af ℚ)ˣ) - 0 = _
    rw [e1, ← hm]
    linear_combination (m : Af ℚ) * w * m.mul_inv
  · change g 1 1 - 1 = _
    rw [e2, mul_assoc]

private noncomputable def lowSub (k : ℕ) : Submodule ℂ (TR.Sm ℚ 2) where
  carrier := {φ | IsLow k φ}
  zero_mem' := ⟨fun _ => by simp, fun _ => by simp, fun _ => by simp⟩
  add_mem' {a b} ha hb :=
    ⟨fun v => by simp only [map_add]; linear_combination (norm := module) ha.wt v + hb.wt v,
      fun v => by simp only [map_add]; linear_combination (norm := module) ha.low v + hb.low v,
      fun v => by simp only [map_add]; linear_combination (norm := module) ha.one v + hb.one v⟩
  smul_mem' c a ha :=
    ⟨fun v => by simp only [map_smul]; linear_combination (norm := module) c • ha.wt v,
      fun v => by simp only [map_smul]; linear_combination (norm := module) c • ha.low v,
      fun v => by simp only [map_smul]; linear_combination (norm := module) c • ha.one v⟩

private theorem lv_map {k : ℕ} (T : TR.Sm ℚ 2 →ₗ[ℂ] TR.Sm ℚ 2) (hT : ∀ v i j φ, TR.Eop v i j (T φ) = T (TR.Eop v i j φ))
    {φ : TR.Sm ℚ 2} (h : IsLow k φ) : IsLow k (T φ) :=
  ⟨fun v => by rw [hT, hT, ← map_sub, h.wt, map_smul],
    fun v => by rw [hT, hT, hT, hT, ← map_sub, h.low, map_smul, map_add],
    fun v => by rw [hT, hT, ← map_add, h.one, map_zero]⟩

end UpperTheory.V.Br

open UpperTheory.V.Br in
theorem UpperTheory.V.Br.levelVec :
    UpperTheory.V.Br.LevelVec := by
  rintro k π ⟨φ, hφ, h0, hl⟩
  obtain ⟨M, hM, hK⟩ := lv_KLev (π.cusp φ hφ).1.level (by simp)
  have hN : 1 ≤ M * M := Nat.mul_pos hM hM
  haveI : NeZero (M * M) := ⟨by omega⟩
  obtain ⟨m, hm⟩ : IsUnit (M : Af ℚ) := by
    rw [← map_natCast (algebraMap ℚ (Af ℚ))]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (by omega))).map _
  obtain ⟨r, hr⟩ := lv_red hN
  let j : ↥(K1G (M * M)) →* ↥(Ohat ℚ) :=
    { toFun := fun g => ⟨_, lv_det g.2⟩
      map_one' := Subtype.ext (congrArg Units.val (map_one Matrix.GeneralLinearGroup.det))
      map_mul' := fun a b => Subtype.ext (congrArg Units.val (map_mul Matrix.GeneralLinearGroup.det a.1 b.1)) }
  have hW : ∀ g, ∀ w ∈ π.V ⊓ lowSub k, TR.finRep ℚ 2 g w ∈ π.V ⊓ lowSub k := fun g w hw =>
    ⟨π.stable (.fin g) w hw.1, lv_map _ (fun v a b ψ => LinearMap.congr_fun (TR.lie_rt_fin _ g) ψ) hw.2⟩
  obtain ⟨χ, w, hw, hw0, hχ⟩ := lv_eig ((TR.finRep ℚ 2).comp (K1G (M * M)).subtype) (r.comp j) (π.V ⊓ lowSub k)
    (fun g => hW g.1) (hW (aff m 0)⁻¹ φ ⟨hφ, hl⟩)
    (fun h => h0 (by
      have := congrArg (TR.finRep ℚ 2 (aff m 0)) h
      rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, map_zero] at this))
    (fun g hg => by
      have h1 : TR.finRep ℚ 2 _ φ = φ := hK _ (lv_mem hm g.2 ((hr (j g) 1).1 (by rw [Int.cast_one]; exact hg)))
      change TR.finRep ℚ 2 g.1 (TR.finRep ℚ 2 _ φ) = _
      conv_rhs => rw [← h1]
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← mul_assoc, inv_mul_cancel_left])
  obtain ⟨ν, hν⟩ := dirChar (M * M) hN χ⁻¹
  have he : ∀ v, TR.expo ν v = 0 := fun v => TR.expo_eq_of_exp ν v 0 fun t => by
    rw [zero_mul, Complex.exp_zero]
    exact congrArg Units.val (hν.pos _ fun _ => Real.exp_pos _)
  refine ⟨M * M, χ⁻¹, ν, hN, hν, TR.mulChi 2 ν w, ⟨w, hw.1, rfl⟩, (TR.mulChi 2 ν).map_ne_zero_iff.2 hw0,
    lv_map (TR.mulChi 2 ν).toLinearMap (fun v a b ψ => ?_) hw.2, fun u hu => ?_⟩
  · refine (TR.Eop_mulChi ν v a b ψ).trans ?_
    rw [he, ite_self, zero_smul, add_zero]
    rfl
  · refine (TR.rt_mulChi ν (finGL ℚ 2 u) w).trans (congrArg _ ?_)
    obtain ⟨d, hd⟩ := ratAd.2.1 _ hN _ (lv_det hu)
    have h1 := hν.unit (Matrix.GeneralLinearGroup.det u) ⟨lv_det hu, by rw [← map_inv]; exact lv_det (inv_mem hu)⟩ d hd
    have h2 : chiDet 2 ν (finGL ℚ 2 u) = ν.1 (finId ℚ (Matrix.GeneralLinearGroup.det u)) := congrArg ν.1 (TR.det_finGL u)
    rw [MulChar.inv_apply_eq_inv', ← div_eq_mul_inv] at h1
    rw [h2, eq_of_div_eq_one h1, ← (hr (j ⟨u, hu⟩) d).2 hd]
    exact hχ ⟨u, hu⟩
