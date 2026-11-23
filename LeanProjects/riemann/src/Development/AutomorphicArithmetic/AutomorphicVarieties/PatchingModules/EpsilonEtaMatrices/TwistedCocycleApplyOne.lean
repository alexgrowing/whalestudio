import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.FinTwLc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.LcOfOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.DdSumZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.AdicLC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlProps

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section Abs

variable {K R M : Type} [Group K] [CommRing R] [Ring M] [Module R M] (ρ z : K → M) (χ : K → R)
  (h1 : ρ 1 = 1) (hm : ∀ g h, ρ (g * h) = ρ g * ρ h) (c1 : χ 1 = 1) (cm : ∀ g h, χ (g * h) = χ g * χ h)
  (hz : ∀ g h, z (g * h) = z g + χ g • (ρ g * z h * ρ g⁻¹))

include h1 c1 hz in
private theorem twisted_cocycle_apply_one : z 1 = 0 := by
  have h := hz 1 1
  simp only [mul_one, inv_one, h1, c1, one_smul, one_mul] at h
  simpa using h

private theorem tw_inv {N : Type} [Monoid N] (ρ : K → N) (h1 : ρ 1 = 1) (hm : ∀ g h, ρ (g * h) = ρ g * ρ h)
    {g : K} (hg : ρ g = 1) : ρ g⁻¹ = 1 := by
  have := hm g g⁻¹
  rw [mul_inv_cancel, h1, hg, one_mul] at this
  exact this.symm

include h1 hm hz in
private theorem tw_add {g : K} (hg : ρ g = 1) (hc : χ g = 1) (h : K) : z (g * h) = z g + z h := by
  rw [hz, hg, hc, tw_inv ρ h1 hm hg, one_smul, one_mul, mul_one]

include h1 hm c1 hz in
private theorem tw_pow {g : K} (hg : ρ g = 1) (hc : χ g = 1) (k : ℕ) : ρ (g ^ k) = 1 ∧ z (g ^ k) = k • z g := by
  induction k with
  | zero => exact ⟨by simpa using h1, by simpa using twisted_cocycle_apply_one (ρ := ρ) (z := z) (χ := χ) h1 c1 hz⟩
  | succ k ih =>
    obtain ⟨h1', h2'⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [pow_succ, hm, h1', hg, one_mul]
    · rw [pow_succ', tw_add (ρ := ρ) (z := z) (χ := χ) h1 hm hz hg hc, h2', succ_nsmul, add_comm]

include h1 hm c1 cm hz in
private theorem tw_U [TopologicalSpace K] (cρ : IsLocallyConstant ρ) (cχ : IsLocallyConstant χ)
    (cz : IsLocallyConstant z) :
    ∃ U : OpenNormalSubgroup K, ∀ g, g ∈ U ↔ ρ g = 1 ∧ χ g = 1 ∧ z g = 0 := by
  let S : Subgroup K :=
    { carrier := {g | ρ g = 1 ∧ χ g = 1 ∧ z g = 0}
      mul_mem' := by
        intro a b ha hb
        obtain ⟨ha1, ha2, ha3⟩ := ha
        obtain ⟨hb1, hb2, hb3⟩ := hb
        refine ⟨by rw [hm, ha1, hb1, one_mul], by rw [cm, ha2, hb2, one_mul], ?_⟩
        rw [tw_add (ρ := ρ) (z := z) (χ := χ) h1 hm hz ha1 ha2, ha3, hb3, add_zero]
      one_mem' := ⟨h1, c1, twisted_cocycle_apply_one (ρ := ρ) (z := z) (χ := χ) h1 c1 hz⟩
      inv_mem' := by
        intro a ha
        obtain ⟨ha1, ha2, ha3⟩ := ha
        refine ⟨tw_inv ρ h1 hm ha1, tw_inv χ c1 cm ha2, ?_⟩
        have e := tw_add (ρ := ρ) (z := z) (χ := χ) h1 hm hz ha1 ha2 a⁻¹
        rw [mul_inv_cancel, twisted_cocycle_apply_one (ρ := ρ) (z := z) (χ := χ) h1 c1 hz, ha3, zero_add] at e
        exact e.symm }
  have hSo : IsOpen (S : Set K) :=
    (cρ.isOpen_fiber 1).inter ((cχ.isOpen_fiber 1).inter (cz.isOpen_fiber 0))
  have hSn : S.Normal := by
    refine ⟨fun a ha b => ?_⟩
    obtain ⟨ha1, ha2, ha3⟩ := ha
    have r1 : ρ (b * a * b⁻¹) = 1 := by rw [hm, hm, ha1, mul_one, ← hm, mul_inv_cancel, h1]
    have r2 : χ (b * a * b⁻¹) = 1 := by rw [cm, cm, ha2, mul_one, ← cm, mul_inv_cancel, c1]
    refine ⟨r1, r2, ?_⟩
    have e1 : z (a * b⁻¹) = z b⁻¹ := by
      rw [tw_add (ρ := ρ) (z := z) (χ := χ) h1 hm hz ha1 ha2, ha3, zero_add]
    rw [mul_assoc, hz, e1, ← hz, mul_inv_cancel, twisted_cocycle_apply_one (ρ := ρ) (z := z) (χ := χ) h1 c1 hz]
  exact ⟨⟨⟨S, hSo⟩, hSn⟩, fun g => Iff.rfl⟩

end Abs

private theorem tw_lc {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hx : ∀ᶠ y in nhds x, ∀ i j, f y i j = f x i j := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact (IsLocallyConstant.iff_eventually_eq _).mp (h i j) x
  filter_upwards [hx] with y hy
  exact Matrix.ext hy

private theorem tw_core {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (K P : Subgroup Γ) [P.Normal] (hK : IsOpen (K : Set Γ)) (hP : P ≤ K) :
    ∃ U : OpenNormalSubgroup Γ, P ≤ U.toSubgroup ∧ U.toSubgroup ≤ K := by
  have hKc : IsClosed (K : Set Γ) := K.isClosed_of_isOpen hK
  haveI : Finite (Γ ⧸ K) := K.quotient_finite_of_isOpen hK
  haveI : K.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hNo : IsOpen (K.normalCore : Set Γ) :=
    K.normalCore.isOpen_of_isClosed_of_finiteIndex (K.normalCore_isClosed hKc)
  refine ⟨⟨⟨K.normalCore, hNo⟩, inferInstance⟩, ?_, ?_⟩
  · exact Subgroup.normal_le_normalCore.mpr hP
  · exact K.normalCore_le

private theorem pow_mem_of_PL (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (H : Subgroup Γ) (V : Set Γ) (hV : IsOpen V) (hle : (PL l H : Set Γ) ⊆ V) : ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ V := by
  classical
  intro h hh
  have hc : IsCompact (Vᶜ) := hV.isClosed_compl.isCompact
  obtain ⟨u, hu⟩ := hc.elim_finite_subfamily_closed
    (fun i : {U : OpenNormalSubgroup Γ // ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U} => (i.1.toSubgroup : Set Γ))
    (fun i => Subgroup.isClosed_of_isOpen _ i.1.isOpen') (by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_iInter, Set.mem_empty_iff_false, iff_false,
        not_and]
      intro hy hall
      apply hy
      apply hle
      simp only [PL, SetLike.mem_coe, Subgroup.mem_iInf]
      intro U hU
      exact hall ⟨U, hU⟩)
  let e : {U : OpenNormalSubgroup Γ // ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U} → ℕ := fun i => (i.2 h hh).choose
  refine ⟨u.sup e, ?_⟩
  by_contra hn
  have hmem : h ^ l ^ u.sup e ∈ Vᶜ ∩ ⋂ i ∈ u, (i.1.toSubgroup : Set Γ) := by
    refine ⟨hn, ?_⟩
    simp only [Set.mem_iInter]
    intro i hi
    have hle' : e i ≤ u.sup e := Finset.le_sup hi
    have hpow : l ^ u.sup e = l ^ e i * l ^ (u.sup e - e i) := by rw [← pow_add, Nat.add_sub_cancel' hle']
    rw [SetLike.mem_coe, hpow, pow_mul]
    exact Subgroup.pow_mem _ (i.2 h hh).choose_spec _
  rw [hu] at hmem
  exact hmem

private theorem epM_mul {X : Type} [CommRing X] {g n : ℕ} (Z : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM Z * DD.epM Z = 0 := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  ext <;> simp [DD.epM]

private theorem one_add_pow {S : Type} [Ring S] (E : S) (h : E * E = 0) (k : ℕ) : (1 + E) ^ k = 1 + k • E := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, add_mul, mul_add, mul_add]
    simp only [smul_mul_assoc, h, smul_zero, mul_one, one_mul, add_zero, succ_nsmul]
    abel

private theorem rho1_pow_eq_one_pro_l (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (x : NP G0.frame n)
    (k : Kap x) (m : ℕ) (hPL : ∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → x.ρ g = 1) (g : G0.G₀)
    (hg : (g : G0.Γ) ∈ T.H) : ∃ e : ℕ, k.ρ1 (x.Am m) (g ^ l ^ e) = 1 := by
  have hlc : IsLocallyConstant fun g : G0.G₀ => k.ρ1 (x.Am m) g := (lc1 l L G0 G0 (Glob.Hom.refl G0) n x k m).1
  have hr := rho1 l G0.frame n x k (x.Am m)
  have hpow : ∀ (g : G0.G₀) (j : ℕ), k.ρ1 (x.Am m) (g ^ j) = k.ρ1 (x.Am m) g ^ j := by
    intro g j
    induction j with
    | zero => simpa using hr.1
    | succ j ih => rw [pow_succ, hr.2.1, ih, pow_succ]
  have hlD : ∀ w : DD (x.Am m) k.g, l • w = 0 := (finAm l G0.frame n x m k.g).2.2.2.2.1
  have hkey : ∀ g0 : G0.G₀, x.ρ g0 = 1 → k.ρ1 (x.Am m) (g0 ^ l) = 1 := by
    intro g0 hρ
    have hρ1 : k.ρ1 (x.Am m) g0 = 1 + DD.epM (fun j => (k.κ j g0).map ⇑(algebraMap x.A (x.Am m))) := by
      simp [Kap.ρ1, NP.ρX, mat, hρ]
    rw [hpow, hρ1, one_add_pow _ (epM_mul _) l]
    have hz : l • DD.epM (fun j => (k.κ j g0).map ⇑(algebraMap x.A (x.Am m))) = 0 := by
      refine Matrix.ext fun a b => ?_
      rw [Matrix.smul_apply, hlD, Matrix.zero_apply]
    rw [hz, add_zero]
  let V : Set G0.Γ := Subtype.val '' {g : G0.G₀ | k.ρ1 (x.Am m) (g ^ l) = 1}
  have hVo : IsOpen V := G0.η_open.isOpenMap_subtype_val _
    ((hlc.comp_continuous (continuous_pow l)).isOpen_fiber 1)
  have hsub : (PL l T.H.toSubgroup : Set G0.Γ) ⊆ V := by
    intro γ hγ
    have hγH : γ ∈ T.H := (pl_props l G0.Γ T.H.toSubgroup T.H.isOpen').2.2.1 hγ
    have hγ0 : γ ∈ G0.η.ker := by rw [MonoidHom.mem_ker]; exact T.H_η γ hγH
    exact ⟨⟨γ, hγ0⟩, hkey _ (hPL ⟨γ, hγ0⟩ hγ), rfl⟩
  obtain ⟨e, he⟩ := pow_mem_of_PL l T.H.toSubgroup V hVo hsub g hg
  obtain ⟨g', hg'1, hg'2⟩ := he
  have hgg : g' = g ^ l ^ e := Subtype.ext (by rw [hg'2]; simp)
  refine ⟨e + 1, ?_⟩
  rw [pow_succ, pow_mul, ← hgg]
  exact hg'1

private theorem epsD_one (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n)
    (k : Kap x) (m : ℕ) (g : F.Γ) (hg : PadicInt.toZMod ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) = 1) : epsD k (x.Am m) g = 1 := by
  set y : ℤ_[l] := ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) with hyd
  have hy : y - 1 ∈ RingHom.ker (PadicInt.toZMod (p := l)) := by
    rw [RingHom.mem_ker, map_sub, hg, map_one, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hy
  obtain ⟨u, hu⟩ := hy
  have hl : ∀ w : DD (x.Am m) k.g, l • w = 0 := (finAm l F n x m k.g).2.2.2.2.1
  have hy1 : y = 1 + u * l := by rw [hu]; ring
  unfold epsD
  rw [← hyd, hy1, map_add, map_one, map_add, map_one, map_mul, map_mul, map_natCast, map_natCast,
    ← nsmul_eq_mul', hl, add_zero]

private theorem epsD_am_eq_one_of_mem_frame_g' (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (x : NP G0.frame n)
    (k : Kap x) (m : ℕ) (s : G0.G₀) (hs : s ∈ G0.frame.G') : epsD k (x.Am m) (s : G0.Γ) = 1 := by
  have hs' : G0.frame.ε (s : G0.Γ) = 1 := MonoidHom.mem_ker.mp hs
  exact epsD_one l G0.frame n x k m (s : G0.Γ) (by rw [hs']; simp)

private theorem phEq_one (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (x : NP G0.frame n)
    (k : Kap x) (m : ℕ) (hPL : ∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → x.ρ g = 1)
    (z : G0.G₀ → Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) (cz : IsLocallyConstant z)
    (hz : ∀ g h : G0.G₀, z (g * h) = z g + epsD k (x.Am m) g • (k.ρ1 (x.Am m) g * z h * k.ρ1 (x.Am m) g⁻¹))
    (j : Fin T.q) : ∀ᶠ N in atTop, k.ρ1 (x.Am m) ((T.h N).p₀ (T.ph N j)) = k.ρ1 (x.Am m) (T.sg j) ∧
      epsD k (x.Am m) ((T.h N).p (T.ph N j)) = 1 ∧ z ((T.h N).p₀ (T.ph N j)) = z (T.sg j) := by
  have hr := rho1 l G0.frame n x k (x.Am m)
  have hlD : ∀ w : DD (x.Am m) k.g, l • w = 0 := (finAm l G0.frame n x m k.g).2.2.2.2.1
  let ρ' : G0.G₀ → Matrix (Fin n) (Fin n) (DD (x.Am m) k.g) := fun g => k.ρ1 (x.Am m) g
  let χ : G0.G₀ → DD (x.Am m) k.g := fun g => epsD k (x.Am m) (g : G0.Γ)
  have h1 : ρ' 1 = 1 := hr.1
  have hm : ∀ g h, ρ' (g * h) = ρ' g * ρ' h := hr.2.1
  have c1 : χ 1 = 1 := by simp [χ, epsD]
  have cm : ∀ g h, χ (g * h) = χ g * χ h := by
    intro g h
    simp [χ, epsD, map_mul]
  have cρ : IsLocallyConstant ρ' := (lc1 l L G0 G0 (Glob.Hom.refl G0) n x k m).1
  have cχ : IsLocallyConstant χ :=
    ((lc1 l L G0 G0 (Glob.Hom.refl G0) n x k m).2.1).comp_continuous continuous_subtype_val
  obtain ⟨U, hU⟩ := tw_U (ρ := ρ') (z := z) (χ := χ) h1 hm c1 cm hz cρ cχ cz
  have hHk : T.H.toSubgroup ≤ G0.η.ker := fun g hg => T.H_η g hg
  have hχH : ∀ h : G0.G₀, (h : G0.Γ) ∈ T.H → χ h = 1 := fun h hh =>
    epsD_one l G0.frame n x k m (h : G0.Γ) (T.H_ε _ hh)
  have hcond : ∀ h : G0.G₀, (h : G0.Γ) ∈ T.H → ∃ e : ℕ, h ^ l ^ e ∈ U := by
    intro h hh
    obtain ⟨e, he⟩ := rho1_pow_eq_one_pro_l l L G0 T n x k m hPL h hh
    have hmem : ∀ j : ℕ, ((h ^ j : G0.G₀) : G0.Γ) ∈ T.H := fun j => by
      rw [Subgroup.coe_pow]
      exact Subgroup.pow_mem _ hh j
    have hc1 : χ (h ^ l ^ e) = 1 := hχH _ (hmem _)
    obtain ⟨hp1, hp2⟩ := tw_pow (ρ := ρ') (z := z) (χ := χ) h1 hm c1 hz he hc1 l
    refine ⟨e + 1, (hU _).mpr ⟨?_, hχH _ (hmem _), ?_⟩⟩
    · rw [pow_succ, pow_mul]
      exact hp1
    · rw [pow_succ, pow_mul, hp2]
      exact Matrix.ext fun a b => by rw [Matrix.smul_apply, hlD, Matrix.zero_apply]
  haveI hPn : (PL l T.H.toSubgroup).Normal := (pl_props l G0.Γ T.H.toSubgroup T.H.isOpen').1
  let K' : Subgroup G0.Γ := U.toSubgroup.map G0.η.ker.subtype
  have hK'o : IsOpen (K' : Set G0.Γ) := by
    rw [Subgroup.coe_map]
    exact G0.η_open.isOpenMap_subtype_val _ U.isOpen'
  have hPK : PL l T.H.toSubgroup ≤ K' := by
    intro γ hγ
    have hγH : γ ∈ T.H := (pl_props l G0.Γ T.H.toSubgroup T.H.isOpen').2.2.1 hγ
    have hγ0 : γ ∈ G0.η.ker := hHk hγH
    have hu : (⟨γ, hγ0⟩ : G0.G₀) ∈ U :=
      pl_sub l G0.Γ T.H.toSubgroup G0.η.ker G0.η_open hHk U hcond ⟨γ, hγ0⟩ hγ
    exact Subgroup.mem_map.mpr ⟨_, hu, rfl⟩
  obtain ⟨W, hPW, hWK⟩ := tw_core K' (PL l T.H.toSubgroup) hK'o hPK
  have hsg : χ (T.sg j) = 1 := epsD_am_eq_one_of_mem_frame_g' l L G0 n x k m (T.sg j) (T.sg_mem j)
  filter_upwards [T.ph_lim W j hPW] with N hN
  obtain ⟨u, huU, hu⟩ := Subgroup.mem_map.mp (hWK hN)
  obtain ⟨hu1, hu2, hu3⟩ := (hU u).mp huU
  have ha : (T.h N).p₀ (T.ph N j) = u * T.sg j := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    change (T.h N).p (T.ph N j) = (u : G0.Γ) * (T.sg j : G0.Γ)
    change (u : G0.Γ) = _ at hu
    rw [hu, inv_mul_cancel_right]
  have hpa : (T.h N).p (T.ph N j) = (((T.h N).p₀ (T.ph N j) : G0.G₀) : G0.Γ) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [ha]
    change ρ' (u * T.sg j) = ρ' (T.sg j)
    rw [hm, hu1, one_mul]
  · rw [hpa, ha]
    change χ (u * T.sg j) = 1
    rw [cm, hu2, one_mul, hsg]
  · rw [ha, tw_add (ρ := ρ') (z := z) (χ := χ) h1 hm hz hu1 hu2, hu3, zero_add]

theorem UpperTheory.V.Pa.phEq :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (m : ℕ), PhiCond G0.Γ l → (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → x.ρ g = 1) → ∀ᶠ N in atTop, ∀ j, k.ρ1 (x.Am m) ((T.h N).p₀ (T.ph N j)) = k.ρ1 (x.Am m) (T.sg j) ∧ epsD k (x.Am m) ((T.h N).p (T.ph N j)) = 1 ∧ ∀ z ∈ TwZ k (x.Am m), z ((T.h N).p₀ (T.ph N j)) = z (T.sg j) := by
  intro l _ L G0 T n x k m hphi hPL
  have hfin := finTw l L G0 n x k m hphi
  have ht : (algebraMap x.A (DD (x.Am m) k.g)) x.t ^ m = 0 := (finAm l G0.frame n x m k.g).2.2.2.2.2.2.1
  have hz0 := phEq_one l L G0 T n x k m hPL (fun _ => 0) (IsLocallyConstant.const 0) (by intro g h; simp)
  have hzs : ∀ z ∈ TwZ k (x.Am m), ∀ j, ∀ᶠ N in atTop, z ((T.h N).p₀ (T.ph N j)) = z (T.sg j) := by
    intro z hz j
    obtain ⟨_, hcont, hcoc, _⟩ := hz
    have cz : IsLocallyConstant z := tw_lc z (fun i j' => (adicLC _ _ _ m _ ht).mp (hcont i j'))
    exact (phEq_one l L G0 T n x k m hPL z cz hcoc j).mono fun N h => h.2.2
  have e1 : ∀ᶠ N in atTop, ∀ j, k.ρ1 (x.Am m) ((T.h N).p₀ (T.ph N j)) = k.ρ1 (x.Am m) (T.sg j) ∧
      epsD k (x.Am m) ((T.h N).p (T.ph N j)) = 1 :=
    Filter.eventually_all.mpr fun j => (hz0 j).mono fun N h => ⟨h.1, h.2.1⟩
  have e2 : ∀ᶠ N in atTop, ∀ j, ∀ z ∈ TwZ k (x.Am m), z ((T.h N).p₀ (T.ph N j)) = z (T.sg j) :=
    Filter.eventually_all.mpr fun j => (Filter.eventually_all_finite hfin).mpr fun z hz => hzs z hz j
  filter_upwards [e1, e2] with N h1 h2 j
  exact ⟨(h1 j).1, (h1 j).2, h2 j⟩
