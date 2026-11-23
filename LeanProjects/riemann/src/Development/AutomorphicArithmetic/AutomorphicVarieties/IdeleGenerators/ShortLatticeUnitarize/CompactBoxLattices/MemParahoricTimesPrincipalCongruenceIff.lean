import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.Unitarize
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop

open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Af Matrix

namespace UpperTheory.V.Sd.Wc

variable {F : Type} [Field F] [NumberField F]

private noncomputable def mP (w : Pl F) (c : ℕ) : AddSubgroup (w.adicCompletion F) :=
  (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c).toAddSubgroup.map
    (w.adicCompletionIntegers F).subtype.toAddMonoidHom

private theorem isOpen_mP (w : Pl F) (c : ℕ) : IsOpen (mP w c : Set (w.adicCompletion F)) := by
  have h0 : IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c ≠ ⊥ :=
    pow_ne_zero c (IsDiscreteValuationRing.not_a_field _)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have ha1 : (a : w.adicCompletion F) ≠ 0 := fun e => ha0 (Subtype.ext e)
  have ho : IsOpen ((fun x : w.adicCompletion F => (a : w.adicCompletion F)⁻¹ * x) ⁻¹'
      (w.adicCompletionIntegers F : Set (w.adicCompletion F))) :=
    (Valued.isOpen_valuationSubring _).preimage (continuous_const.mul continuous_id)
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (Filter.mem_of_superset (ho.mem_nhds (by simp)) fun x hx => ?_)
  refine ⟨a * ⟨_, hx⟩, Ideal.mul_mem_right _ _ ha, ?_⟩
  change (a : w.adicCompletion F) * ((a : w.adicCompletion F)⁻¹ * x) = x
  rw [mul_inv_cancel_left₀ ha1]

private theorem mem_parahoricTimesPrincipalCongruence_iff {w : Pl F} {c : ℕ} {g : GL (Fin 2) (w.adicCompletion F)} :
    g ∈ K1 w c ↔ (∀ a b, g a b ∈ w.adicCompletionIntegers F) ∧
      (∀ a b, (g⁻¹ : GL (Fin 2) (w.adicCompletion F)) a b ∈ w.adicCompletionIntegers F) ∧
      g 1 0 ∈ mP w c ∧ g 1 1 - 1 ∈ mP w c := by
  have key : ∀ k : GL (Fin 2) (w.adicCompletionIntegers F),
      k ∈ ((mirab _).comap (Matrix.GeneralLinearGroup.map (n := Fin 2)
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)))) ↔
      k 1 0 ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c ∧
        k 1 1 - 1 ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c := fun k => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq, map_one]
    change ![0, 1] ᵥ* _ = ![0, 1] ↔ _
    rw [funext_iff, Fin.forall_fin_two]
    simp [Matrix.vecMul, dotProduct]
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨h1, h2⟩ := (key k).1 hk
    refine ⟨fun a b => (k a b).2, fun a b => ?_, ⟨_, h1, rfl⟩, ⟨_, h2, rfl⟩⟩
    rw [← map_inv]; exact ((k⁻¹ : GL (Fin 2) (w.adicCompletionIntegers F)) a b).2
  · rintro ⟨ha, hb, ⟨y, hy, e⟩, ⟨y', hy', e'⟩⟩
    have inj : Function.Injective (RingHom.mapMatrix (m := Fin 2) (w.adicCompletionIntegers F).subtype) := fun x y h =>
      Matrix.ext fun a b => Subtype.ext (congrFun (congrFun h a) b)
    let k : GL (Fin 2) (w.adicCompletionIntegers F) :=
      ⟨Matrix.of fun a b => ⟨g a b, ha a b⟩, Matrix.of fun a b => ⟨(g⁻¹ : GL (Fin 2) (w.adicCompletion F)) a b, hb a b⟩,
        inj (by rw [map_mul, map_one]; exact g.mul_inv), inj (by rw [map_mul, map_one]; exact g.inv_mul)⟩
    refine ⟨k, (key k).2 ⟨?_, ?_⟩, Units.ext rfl⟩
    · rw [show k 1 0 = y from Subtype.ext e.symm]; exact hy
    · rw [show k 1 1 - 1 = y' from Subtype.ext e'.symm]; exact hy'

private theorem mem_mP_zero {w : Pl F} {x : w.adicCompletion F} (hx : x ∈ w.adicCompletionIntegers F) : x ∈ mP w 0 :=
  ⟨⟨x, hx⟩, by simp, rfl⟩

private theorem mem_Oh {x : Af F} :
    x ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F ↔ ∀ w : Pl F, pLoc F w x ∈ w.adicCompletionIntegers F := by
  rw [← mem_Ohat]; simp [Ohat, Subring.mem_iInf]

private theorem mem_Kc {c : Pl F → ℕ} {g : GF F} :
    g ∈ Kc c ↔ g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL F 2 ∧
      ∀ w, c w ≠ 0 → pLoc F w (g 1 0) ∈ mP w (c w) ∧ pLoc F w (g 1 1) - 1 ∈ mP w (c w) := by
  simp only [Kc, Subgroup.mem_iInf, Subgroup.mem_comap, mem_parahoricTimesPrincipalCongruence_iff, ← map_inv,
    GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff, mem_Oh]
  constructor
  · exact fun h => ⟨⟨fun a b w => (h w).1 a b, fun a b w => (h w).2.1 a b⟩, fun w _ => (h w).2.2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩ w
    refine ⟨fun a b => h1 a b w, fun a b => h2 a b w, ?_⟩
    by_cases hw : c w = 0
    · rw [hw]
      exact ⟨mem_mP_zero (h1 1 0 w), mem_mP_zero (sub_mem (h1 1 1 w) (one_mem _))⟩
    · exact h3 w hw

private theorem isOpen_Kc {c : Pl F → ℕ} (hc : {w | c w ≠ 0}.Finite) : IsOpen (Kc c : Set (GF F)) := by
  have e : (Kc c : Set (GF F)) = (GroundTheory.Automorphic.AdelicGLn.integralFiniteGL F 2 : Set (GF F)) ∩
      ⋂ w ∈ {w | c w ≠ 0}, ((fun g : GF F => pLoc F w (g 1 0)) ⁻¹' mP w (c w) ∩
        (fun g : GF F => pLoc F w (g 1 1) - 1) ⁻¹' mP w (c w)) := by
    ext g
    simp only [SetLike.mem_coe, mem_Kc, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
  have ct : ∀ w a b, Continuous fun g : GF F => pLoc F w (g a b) := fun w a b =>
    (show Continuous (pLoc F w) from RestrictedProduct.continuous_eval w).comp
      (Continuous.matrix_elem Units.continuous_val a b)
  rw [e]
  exact (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL F 2).inter (hc.isOpen_biInter fun w _ =>
    ((isOpen_mP w _).preimage (ct w 1 0)).inter ((isOpen_mP w _).preimage ((ct w 1 1).sub continuous_const)))

private theorem range_zc : ((zc F).range : Set (GF F)) =
    {g : GF F | g 0 1 = 0} ∩ {g : GF F | g 1 0 = 0} ∩ {g : GF F | g 0 0 = g 1 1} := by
  ext g
  constructor
  · rintro ⟨z, rfl⟩
    simp [zc]
  · rintro ⟨⟨h1, h2⟩, h3⟩
    simp only [Set.mem_setOf_eq] at h1 h2 h3
    have hm : g 0 0 * (g⁻¹ : GF F) 0 0 = 1 := by
      have := congrFun (congrFun g.mul_inv 0) 0
      rw [Matrix.mul_apply, Fin.sum_univ_two, h1, zero_mul, add_zero] at this
      exact this
    refine ⟨Units.mkOfMulEqOne _ _ hm, Units.ext (Matrix.ext fun i j => ?_)⟩
    fin_cases i <;> fin_cases j <;> simp [zc, h1, h2, h3]

end UpperTheory.V.Sd.Wc

open UpperTheory.V.Sd.Wc in
theorem UpperTheory.V.Sd.Wc.kcTop :
    UpperTheory.V.Sd.Wc.KcTop := by
  intro F _ _
  have ct : ∀ a b, Continuous fun g : GF F => g a b := fun a b => Continuous.matrix_elem Units.continuous_val a b
  refine ⟨fun c hc => ⟨isOpen_Kc hc, ?_⟩, fun U hU => ?_, fun z => ?_, ?_, ?_, fun c w k hk => ?_⟩
  · exact (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL F 2).of_isClosed_subset
      (Subgroup.isClosed_of_isOpen _ (isOpen_Kc hc)) fun g hg => (mem_Kc.1 hg).1
  · obtain ⟨H, -, hH⟩ := (GroundTheory.Automorphic.AdelicGLn.finite_hasBasis_nhds_one F 2).mem_iff.1 hU
    exact ⟨H.toSubgroup, H.isOpen, hH⟩
  · refine Subgroup.mem_center_iff.2 fun g => Units.ext ?_
    exact ((Matrix.scalar_commute (z : Af F) (fun _ => Commute.all _ _) g.val).eq).symm
  · rw [range_zc]
    exact ((isClosed_eq (ct 0 1) continuous_const).inter (isClosed_eq (ct 1 0) continuous_const)).inter
      (isClosed_eq (ct 0 0) (ct 1 1))
  · refine Continuous.units_map _ ?_
    exact (continuous_pi fun _ => continuous_id : Continuous fun x : Af F => fun _ : Fin 2 => x).matrix_diagonal
  · refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_comap.2 ?_
    by_cases h : v = w
    · subst h; rwa [pLoc_locGL]
    · rw [pLoc_locGL_of_ne h]; exact one_mem _
