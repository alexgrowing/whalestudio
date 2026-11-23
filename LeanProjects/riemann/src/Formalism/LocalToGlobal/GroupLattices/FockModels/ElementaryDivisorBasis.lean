import Formalism.LocalToGlobal.GroupLattices.FockModels.MkP

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems

theorem pos_basis (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m r : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det) :
    ∃ (X : ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)
      (π : ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) → ℤ),
      LinearIndependent Kf X ∧ Submodule.span Kf (Set.range X) = dualWeyl Kf (m + 1) (m + 1) (nuOf lam) ∧
      (∀ i, π i ≤ ∑ a : Fin (m + 1) with a.val < r, lam a) ∧
      ∀ c : Kf, c ≠ 0 → Submodule.span O (Set.range fun i => c ^ π i • X i) =
        nablaLTw O Kf m lam (g * lb_D (m + 1) r c) := by
  classical
  set e : ℤ := lam (Fin.last m) with he
  obtain ⟨b, hb, hwt⟩ := lb_basis O (m + 1) (m + 1) (nuOf lam)
  obtain ⟨k1, k2⟩ := nablaLKBasis O Kf hinj (m + 1) (m + 1) (nuOf lam) b _ hb g hg
  set ρ : ℕ := (Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card with hρ
  have hd : g.det ^ (-e) ≠ 0 := zpow_ne_zero _ hg.ne_zero
  set T : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf :=
    LinearMap.lsmul Kf _ (g.det ^ (-e)) with hT
  have hTinj : Function.Injective T := fun x y hxy => smul_right_injective _ hd hxy
  refine ⟨fun i => T (rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i))),
    fun i => ((∑ a : Fin (m + 1) with a.val < r, rowWt i.1 a : ℕ) : ℤ) + ρ * e, ?_, ?_, ?_, ?_⟩
  · exact k1.map' T (LinearMap.ker_eq_bot.2 hTinj)
  · have : (Set.range fun i => T (rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i)))) =
        T '' (Set.range fun i => rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i))) := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, k2]
    have hT2 : T = (g.det ^ (-e)) • LinearMap.id := by
      ext x; simp [hT]
    rw [hT2, Submodule.map_smul _ _ _ hd, Submodule.map_id]
  · intro i
    have hle := hwt i r
    have h3 : (∑ a : Fin (m + 1) with a.val < r, lam a) =
        ((∑ t : Fin (m + 1) with t.val < r, nuOf lam t : ℕ) : ℤ) + ρ * e := by
      rw [hρ]
      push_cast
      rw [Finset.card_eq_sum_ones]
      push_cast
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      have : 0 ≤ lam a - lam (Fin.last m) := sub_nonneg.2 (hlam (Fin.le_last a))
      simp only [nuOf, Int.toNat_of_nonneg this, he]
      ring
    rw [h3]
    have : ((∑ a : Fin (m + 1) with a.val < r, rowWt i.1 a : ℕ) : ℤ) ≤
        ((∑ t : Fin (m + 1) with t.val < r, nuOf lam t : ℕ) : ℤ) := by exact_mod_cast hle
    linarith
  · intro c hc
    set t : Fin (m + 1) → Kf := fun a => if a.val < r then c⁻¹ else 1 with ht
    have ht0 : ∀ a, t a ≠ 0 := by
      intro a
      simp only [ht]
      split_ifs
      · exact inv_ne_zero hc
      · exact one_ne_zero
    have hD : Submodule.span O (Set.range fun i => (∏ a, t a ^ rowWt i.1 a)⁻¹ •
        rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i))) =
        nablaL O Kf (m + 1) (m + 1) (fun t => (lam t - lam (Fin.last m)).toNat) (g * lb_D (m + 1) r c) :=
      (nablaLDiag O Kf hinj (m + 1) (m + 1) (nuOf lam) b _ hb g t hg ht0).2
    unfold nablaLTw
    rw [← hD, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext i
    show c ^ (((∑ a : Fin (m + 1) with a.val < r, rowWt i.1 a : ℕ) : ℤ) + ρ * e) •
        (g.det ^ (-e) • rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i))) =
      (g * lb_D (m + 1) r c).det ^ (-e) • ((∏ a, t a ^ rowWt i.1 a)⁻¹ •
        rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i)))
    rw [smul_smul, smul_smul]
    congr 1
    set π' : ℕ := ∑ a : Fin (m + 1) with a.val < r, rowWt i.1 a with hπ
    have h1 : (g * lb_D (m + 1) r c).det = g.det * (c⁻¹) ^ ρ := by
      rw [Matrix.det_mul, lb_D, Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const,
        Finset.prod_const_one, mul_one]
    have h2 : ∏ a, t a ^ rowWt i.1 a = (c⁻¹) ^ π' := by
      rw [hπ, ← Finset.prod_pow_eq_pow_sum, Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro a _
      simp only [ht]
      split_ifs <;> simp
    have h5 : ((c⁻¹) ^ ρ) ^ (-e) = c ^ ((ρ : ℤ) * e) := by
      rw [inv_pow, inv_zpow, zpow_neg, inv_inv, ← zpow_natCast c ρ, ← zpow_mul]
    have h6 : ((c⁻¹) ^ π')⁻¹ = c ^ π' := by rw [inv_pow, inv_inv]
    rw [h1, h2, mul_zpow, h5, h6, zpow_add₀ hc, zpow_natCast]
    ring

theorem comap_span_coe {O Kf X : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X]
    [Module O X] [IsScalarTower O Kf X] {I : Type} (Vs : Submodule Kf X) (f : I → Vs) :
    (Submodule.span O (Set.range fun i => (f i : X))).comap (Vs.subtype.restrictScalars O) =
      Submodule.span O (Set.range f) := by
  have h : (Set.range fun i => (f i : X)) = (Vs.subtype.restrictScalars O) '' Set.range f := by
    ext y
    simp
  rw [h, ← Submodule.map_span, Submodule.comap_map_eq_of_injective]
  exact Subtype.val_injective

theorem scale_span {O Kf X : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X]
    [Module O X] [IsScalarTower O Kf X] {I : Type} (c : Kf) (f : I → X) :
    scale c (Submodule.span O (Set.range f)) = Submodule.span O (Set.range fun i => c • f i) := by
  unfold scale
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem dualLat_span {O Kf V : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V] [Module Kf V]
    [Module O V] [IsScalarTower O Kf V] {I : Type} [Finite I] (x : Module.Basis I Kf V) (a : I → Kf)
    (ha : ∀ i, a i ≠ 0) :
    dualLat O Kf (Submodule.span O (Set.range fun i => a i • x i)) =
      Submodule.span O (Set.range fun i => (a i)⁻¹ • x.coord i) := by
  classical
  cases nonempty_fintype I
  apply le_antisymm
  · intro φ hφ
    have h1 : ∀ i, ∃ o : O, algebraMap O Kf o = φ (a i • x i) :=
      fun i => hφ _ (Submodule.subset_span ⟨i, rfl⟩)
    choose o ho using h1
    have h2 : φ = ∑ i, o i • ((a i)⁻¹ • x.coord i) := by
      apply x.ext
      intro k
      rw [LinearMap.sum_apply, Finset.sum_eq_single k]
      · rw [LinearMap.smul_apply, LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
          Finsupp.single_eq_same, ← algebraMap_smul Kf (o k), ho, map_smul, smul_eq_mul, smul_eq_mul,
          smul_eq_mul, mul_one]
        field_simp [ha k]
      · intro i _ hik
        rw [LinearMap.smul_apply, LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
          Finsupp.single_eq_of_ne (Ne.symm hik |>.symm), smul_zero, smul_zero]
      · intro h; exact absurd (Finset.mem_univ k) h
    rw [h2]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k, rfl⟩ := hv
      by_cases hik : k = i
      · subst hik
        refine ⟨1, ?_⟩
        rw [LinearMap.smul_apply, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
          Finsupp.single_eq_same, map_one, smul_eq_mul, smul_eq_mul, mul_one, inv_mul_cancel₀ (ha k)]
      · refine ⟨0, ?_⟩
        rw [LinearMap.smul_apply, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
          Finsupp.single_eq_of_ne (by first | exact hik | exact Ne.symm hik), map_zero, smul_zero, smul_zero]
    | zero => exact ⟨0, by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨a1, h1⟩ := hu
      obtain ⟨a2, h2⟩ := hv
      exact ⟨a1 + a2, by rw [map_add, map_add, h1, h2]⟩
    | smul c v _ hv =>
      obtain ⟨a1, h1⟩ := hv
      refine ⟨c * a1, ?_⟩
      rw [map_mul, h1, ← Algebra.smul_def, LinearMap.map_smul_of_tower]

theorem ten_basis (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [IsFractionRing O Kf]
    {n' m : ℕ} (r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (hd : IsDominant lam0)
    (gs : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hgs : ∀ s, IsUnit (gs s).det) :
    ∃ (I : Type) (_ : Finite I) (x : Module.Basis I Kf (Vsp Kf lam0)) (π : I → ℤ),
      (∀ i, π i ≤ Ar r lam0) ∧
      ∀ c : Kf, c ≠ 0 → Submodule.span O (Set.range fun i => c ^ π i • x i) =
        toV lam0 (Hten O lam0 fun s => colSpan O (gs s * lb_D (m + 1) r c)) := by
  classical
  have hinj : Function.Injective (algebraMap O Kf) := IsFractionRing.injective O Kf
  have hanti := kp_lamAt_antitone lam0 hd
  have hB := fun s : Fin n' => pos_basis O Kf hinj m r (lamAt lam0 s) (hanti s) (gs s) (hgs s)
  choose X π b1 b2 b3 b4 using hB
  have hV : Vsp Kf lam0 = tensorLat Kf Kf
      (fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s))) := by
    unfold Vsp
    congr 1
    funext s
    rw [if_pos (hanti s)]
  have hKK : IsFractionRing Kf Kf := jr_KK Kf
  obtain ⟨kL, kS⟩ := tensorBasis Kf Kf (Fin n') (m + 1) (m + 1) _ _ X b1 b2
  have hfin : ∀ s : Fin n', Finite ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s))) :=
    fun s => (sSIdxFinite (m + 1) (m + 1) (nuOf (lamAt lam0 s))).to_subtype
  let x : Module.Basis (∀ s, ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s)))) Kf (Vsp Kf lam0) :=
    (Module.Basis.span kL).map (LinearEquiv.ofEq _ _ (kS.trans hV.symm))
  have hx : ∀ i, ((x i : Vsp Kf lam0) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
      ∏ s, blockEmb Kf s (X s (i s)) := by
    intro i
    show (((LinearEquiv.ofEq _ _ (kS.trans hV.symm)) (Module.Basis.span kL i) : Vsp Kf lam0) :
      MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = _
    rw [LinearEquiv.coe_ofEq_apply]
    exact congrArg Subtype.val (Module.Basis.span_apply kL i)
  refine ⟨_, inferInstance, x, fun i => ∑ s, π s (i s), ?_, ?_⟩
  · intro i
    unfold Ar
    exact Finset.sum_le_sum fun s _ => b3 s (i s)
  · intro c hc
    have hLI : ∀ s, LinearIndependent O (fun i => c ^ π s i • X s i) := by
      intro s
      have h1 : LinearIndependent Kf (fun i => c ^ π s i • X s i) :=
        (b1 s).units_smul (fun i => Units.mk0 (c ^ π s i) (zpow_ne_zero _ hc))
      exact h1.restrict_scalars (by
        intro a b hab
        apply hinj
        simpa [Algebra.smul_def] using hab)
    obtain ⟨-, oS⟩ := tensorBasis O Kf (Fin n') (m + 1) (m + 1) _ _ (fun s i => c ^ π s i • X s i) hLI
      (fun s => b4 s c hc)
    have hH : Hten O lam0 (fun s => colSpan O (gs s * lb_D (m + 1) r c)) =
        tensorLat O Kf (fun s => nablaLTw O Kf m (lamAt lam0 s) (gs s * lb_D (m + 1) r c)) := by
      unfold Hten
      congr 1
      funext s
      rw [H0_eq_twisted_nabla (la_indep hinj) _ _ (hanti s) _
        (by rw [Matrix.det_mul]; exact (hgs s).mul (lb_D_det _ _ _ hc))]
    unfold toV
    rw [hH, ← oS, ← comap_span_coe]
    congr 3
    funext i
    show c ^ (∑ s, π s (i s)) • ((x i : Vsp Kf lam0) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = _
    rw [hx]
    simp only [map_smul]
    rw [Finset.prod_smul, lb_zpow_sum _ hc]

section
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem w_ne (h : HidaSetting p n' W Qq O Kf ι σ j w) : algebraMap O Kf w ≠ 0 := by
  intro h0
  have hpK : (p : Kf) = algebraMap O Kf w ^ 2 := by rw [← map_pow, h.w_sq, map_natCast]
  have hpW : (p : W) ≠ 0 := h.p_unif.ne_zero
  haveI := h.frac_alt
  have hpQ : (p : Qq) ≠ 0 := by
    rw [← map_natCast (algebraMap W Qq)]
    exact (map_ne_zero_iff _ (IsFractionRing.injective W Qq)).2 hpW
  have hpK' : (p : Kf) ≠ 0 := by
    rw [← map_natCast ι]
    exact (map_ne_zero ι).2 hpQ
  exact hpK' (by rw [hpK, h0]; simp)

theorem p_eq (h : HidaSetting p n' W Qq O Kf ι σ j w) : (p : Kf) = algebraMap O Kf w ^ 2 := by
  rw [← map_pow, h.w_sq, map_natCast]

theorem edgeLat (h : HidaSetting p n' W Qq O Kf ι σ j w) (m r : ℕ) (e : Edge W Qq (m + 1))
    (he : IsEdge p n' r e) :
    ∃ gs : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, (∀ s, IsUnit (gs s).det) ∧
      (∀ s, extO O ι σ s e.src = colSpan O (gs s)) ∧
      (∀ s, LeAt p ι σ w s e = colSpan O (gs s * lb_D (m + 1) r (algebraMap O Kf w))) ∧
      (∀ s, extO O ι σ s e.tgt = colSpan O (gs s * lb_D (m + 1) r (algebraMap O Kf w) *
          lb_D (m + 1) r (algebraMap O Kf w))) :=
  lb_edgeLat_of_basis (mkG h m r (fun _ _ => 0) (fun _ _ _ _ => le_rfl)) (0 : Fin 1) (restEdgeBasis _ _) e he

theorem lb_D_one {K : Type} [Field K] (k r : ℕ) : lb_D k r (1 : K) = 1 := by
  unfold lb_D
  simp

theorem lb_D_sq {K : Type} [Field K] (k r : ℕ) (c : K) : lb_D k r c * lb_D k r c = lb_D k r (c ^ 2) := by
  unfold lb_D
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  split_ifs <;> simp [sq, mul_inv]

theorem elementary_divisor_basis (h : HidaSetting p n' W Qq O Kf ι σ j w) (m r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (hd : IsDominant lam0) (e : Edge W Qq (m + 1)) (he : IsEdge p n' r e) :
    ∃ (I : Type) (_ : Finite I) (x : Module.Basis I Kf ↥(Vsp Kf lam0)) (π : I → ℤ),
      Submodule.span O (Set.range x) = HL ι σ lam0 e.src ∧
      Submodule.span O (Set.range fun i => ((p : Kf) ^ π i) • x i) = HL ι σ lam0 e.tgt ∧
      Submodule.span O (Set.range fun i => (algebraMap O Kf w ^ π i) • x i) = HLe p ι σ w lam0 e ∧
      (∀ i, 0 ≤ order r lam0 (π i)) ∧
      Submodule.span O (Set.range fun i => (algebraMap O Kf w ^ (-order r lam0 (π i))) • x i) =
        Re p ι σ w r lam0 e ∧
      Submodule.span O (Set.range fun i =>
          (algebraMap O Kf w ^ (-order r lam0 (π i)) * (p : Kf) ^ (-π i)) • x.coord i) =
        Re' p ι σ w r lam0 e := by
  have := h.frac_O
  obtain ⟨gs, hgs, h1, h2, h3⟩ := edgeLat h m r e he
  obtain ⟨I, hI, x, π, hπ, hx⟩ := ten_basis O Kf r lam0 hd (fun s : Fin n' => gs s.val) (fun s => hgs _)
  have hw := w_ne h
  have hp := p_eq h
  have hp0 : (p : Kf) ≠ 0 := by rw [hp]; exact pow_ne_zero _ hw
  have hLe : Submodule.span O (Set.range fun i => (algebraMap O Kf w ^ π i) • x i) = HLe p ι σ w lam0 e := by
    rw [hx _ hw]
    unfold HLe
    simp only [h2]
  refine ⟨I, hI, x, π, ?_, ?_, hLe, fun i => sub_nonneg.2 (hπ i), ?_, ?_⟩
  · have := hx 1 one_ne_zero
    simp only [one_zpow, one_smul, lb_D_one, Matrix.mul_one] at this
    unfold HL
    simp only [h1]
    exact this
  · rw [hx _ hp0]
    unfold HL
    simp only [h3, Matrix.mul_assoc, lb_D_sq, ← hp]
  · unfold Re
    rw [← hLe, scale_span]
    congr 2
    funext i
    rw [smul_smul, ← zpow_add₀ hw]
    congr 2
    unfold order
    ring
  · unfold Re'
    rw [← hLe, dualLat_span x _ (fun i => zpow_ne_zero _ hw), scale_span]
    congr 2
    funext i
    rw [smul_smul]
    congr 1
    rw [hp, ← zpow_natCast (algebraMap O Kf w) 2, ← zpow_mul, ← zpow_neg, ← zpow_add₀ hw, ← zpow_add₀ hw]
    congr 1
    unfold order
    push_cast
    ring

end

theorem dualHeightBasis : DualHeightBasis := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w h m r lam0 hd e he
  classical
  obtain ⟨I, hI, x, π, c1, c2, c3, c4, c5, c6⟩ := elementary_divisor_basis h m r lam0 hd e he
  cases nonempty_fintype I
  have hcard : Fintype.card I = dimV Kf lam0 := (Module.finrank_eq_card_basis x).symm
  let E : I ≃ Fin (dimV Kf lam0) := Fintype.equivFinOfCardEq hcard
  have hr : ∀ {Y : Type} (F : I → Y), (Set.range fun a => F (E.symm a)) = Set.range F :=
    fun F => E.symm.surjective.range_comp F
  have hcoord : ∀ a, (x.reindex E).coord a = x.coord (E.symm a) := by
    intro a
    ext v
    simp [Module.Basis.coord_apply]
  refine ⟨x.reindex E, fun a => π (E.symm a), ?_, ?_, ?_, fun a => c4 _, ?_, ?_⟩
  · rw [← c1]
    congr 1
    simp
  · rw [← c2]
    congr 1
    simpa using hr (fun i => ((p : Kf) ^ π i) • x i)
  · rw [← c3]
    congr 1
    simpa using hr (fun i => (algebraMap O Kf w ^ π i) • x i)
  · rw [← c5]
    congr 1
    simpa using hr (fun i => (algebraMap O Kf w ^ (-order r lam0 (π i))) • x i)
  · rw [← c6]
    congr 1
    simp only [hcoord]
    exact hr (fun i => (algebraMap O Kf w ^ (-order r lam0 (π i)) * (p : Kf) ^ (-π i)) • x.coord i)

end Formalism.L2.G.Model
