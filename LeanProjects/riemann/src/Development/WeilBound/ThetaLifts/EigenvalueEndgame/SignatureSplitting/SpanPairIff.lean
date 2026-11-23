import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.Emb2DiaMulVecIncVY
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.AeFacts

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Two

open scoped TensorProduct NNReal Matrix MatrixGroups Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEnd.Grp PositivityTheory.ThKG.Tow.Levi
open GlobalTheory.Eis.Conv (halfE)

theorem uniq_sub {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] {Γ S : Subgroup G} (hS : IsClosed (S : Set G))
    (L : Lat (Γ.subgroupOf S)) {f c c' : G → ℂ} (h : IsAv (Γ.subgroupOf S) Subtype.val f c)
    (h' : IsAv (Γ.subgroupOf S) Subtype.val f c') : c = c' := by
  have : LocallyCompactSpace S := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  exact L.isAv_uniq h h'

theorem first_of (G : Type) [TopologicalSpace G] [SecondCountableTopology G] : FirstCountableTopology G := inferInstance

theorem uni_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (ξ : R) :
    uni (.ofAdd (f ξ)) = Matrix.SpecialLinearGroup.map f (uni (.ofAdd ξ)) :=
  Subtype.ext (Matrix.ext fun i j => by
    fin_cases i <;> fin_cases j
    exacts [(map_one f).symm, rfl, (map_zero f).symm, (map_one f).symm])

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {d d₁ d₂ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {W₂ : Spc F E d₂} {H : Plane E d d₁} {H₁ : Plane E d₁ d₂}

theorem fa_add (J : Matrix (Fin d) (Fin d) E) (w w' z : Fin d → AE F E) (a : AE F E) :
    fa σ J (w + a • w') z = fa σ J w z + a * fa σ J w' z := by
  rw [fa, add_dotProduct, smul_dotProduct]; rfl

theorem incV_lin (x y : Fin d → E) (a b : E) :
    incV F (a • x + b • y) = inclR (F := F) (AF F) a • incV F x + inclR (F := F) (AF F) b • incV F y :=
  funext fun i => by simp [incV]

theorem span_pair_iff {x y : Fin d → E} {z : Fin d → AE F E} : z ∈ Submodule.span (AE F E) (incV F '' (Submodule.span E {x, y} : Set (Fin d → E))) ↔
    ∃ a b : AE F E, a • incV F x + b • incV F y = z := by
  rw [← Submodule.mem_span_pair]
  refine ⟨fun k => Submodule.span_le.2 ?_ k, fun k => Submodule.span_mono ?_ k⟩
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hu
    exact Submodule.mem_span_pair.2 ⟨_, _, (incV_lin x y a b).symm⟩
  · rintro _ (rfl | rfl)
    exacts [⟨x, Submodule.subset_span (by simp), rfl⟩, ⟨y, Submodule.subset_span (by simp), rfl⟩]

variable (h : IsCMExt F E σ) (hJ : ∀ i j, σ (W.J j i) = -W.J i j) (hH : IsPlane σ H W W₁) (hH₁ : IsPlane σ H₁ W₁ W₂)

include h hJ hH hH₁

theorem emb2_norm (g : SL(2, E)) : ∀ u ∈ Submodule.span E {H.x, H.ι *ᵥ H₁.x}, ∃ u' ∈ Submodule.span E {H.x, H.ι *ᵥ H₁.x},
    mat (emb2 h hJ hH hH₁ (Matrix.SpecialLinearGroup.map (inclR (F := F) (AF F)) g)) *ᵥ incV F u = incV F u' := fun u hu => by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hu
  refine ⟨_, Submodule.mem_span_pair.2 ⟨a * g.1 0 0 + b * g.1 0 1, a * g.1 1 0 + b * g.1 1 1, rfl⟩, ?_⟩
  rw [incV_lin, incV_lin, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, (emb2_mulVec_incV_x_and_complement_x h hJ hH hH₁ _).1, (emb2_mulVec_incV_x_and_complement_x h hJ hH hH₁ _).2]
  simp only [map_add, map_mul, smul_add, add_smul, smul_smul]
  exact add_add_add_comm _ _ _ _

theorem mem_pair (hJ₁ : ∀ i j, σ (W₁.J j i) = -W₁.J i j) {u : UA σ W.J} {y : UA σ W₁.J} (hx : mat u *ᵥ incV F H.x = incV F H.x)
    (hy : ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat y *ᵥ z) + a • incV F H.x) :
    u ∈ unipU σ W (Submodule.span E {H.x, H.ι *ᵥ H₁.x}) ↔
      y ∈ unip σ W₁ H₁ ∧ mat u *ᵥ incV F (H.ι *ᵥ H₁.x) = incV F (H.ι *ᵥ H₁.x) := by
  have m0 : H.x ∈ Submodule.span E {H.x, H.ι *ᵥ H₁.x} := Submodule.subset_span (by simp)
  have m1 : H.ι *ᵥ H₁.x ∈ Submodule.span E {H.x, H.ι *ᵥ H₁.x} := Submodule.subset_span (by simp)
  rw [unipLine F E σ h _ _ _ _ H₁ (Or.inr hJ₁) hH₁, (unipU_eq _).choose_spec.choose_spec.2, (unipU_eq _).choose_spec.choose_spec.2]
  constructor
  · rintro ⟨k1, k2⟩
    have e1 : mat y *ᵥ incV F H₁.x = incV F H₁.x := by
      obtain ⟨a, ha⟩ := hy (incV F H₁.x)
      rw [incM_mulVec H.ι H₁.x, k1 _ m1, ← incM_mulVec] at ha
      exact (iota_inj h hJ hH (a := 0) ((congrArg _ (zero_smul _ _)).trans ((add_zero _).trans ha))).symm
    refine ⟨⟨fun v hv => ?_, fun z hz => ?_⟩, k1 _ m1⟩
    · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
      have : incV F (a • H₁.x) = inclR (F := F) (AF F) a • incV F H₁.x := funext fun i => map_mul _ _ _
      rw [this, Matrix.mulVec_smul, e1]
    · obtain ⟨a, b, hab⟩ := span_pair_iff.1 (k2 (H.ι *ᵥ z) fun v hv => by
        obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hv
        refine inc_inj (F := F) ?_
        have z1 := congrArg (inclR (F := F) (AF F)) (hz _ (Submodule.mem_span_singleton_self _))
        rw [← fa_inc, map_zero] at z1
        have : ∀ w p q : Fin d → AE F E, fa σ W.J w (p + q) = fa σ W.J w p + fa σ W.J w q := fun w p q => by
          simp only [fa, Pi.add_apply, map_add]
          rw [← dotProduct_add, ← Matrix.mulVec_add]; rfl
        rw [← fa_inc, incV_lin, this, fa_smul, fa_smul, ← incM_mulVec, ← incM_mulVec, fa_iota hH, fa_iota2 hH, z1]
        simp)
      obtain ⟨c, hc⟩ := hy (incV F z)
      rw [← incM_mulVec, ← incM_mulVec, hc] at hab
      have := iota_inj h hJ hH (z := mat y *ᵥ incV F z - incV F z) (z' := b • incV F H₁.x) (a := c) (a' := a) (by
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, add_comm (b • _), hab]; abel)
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, Submodule.mem_span_singleton_self _, rfl⟩)
  · rintro ⟨k, k3⟩
    rw [← (unipU_eq _).choose_spec.choose_spec.2, ← unipLine F E σ h _ _ _ _ H₁ (Or.inr hJ₁) hH₁, mem_unip h (Or.inr hJ₁) hH₁] at k
    refine ⟨fun v hv => ?_, fun z hz => ?_⟩
    · obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hv
      rw [incV_lin, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hx, k3]
    · obtain ⟨w, a, e⟩ := exists_decomp_of_fa_incV_x_eq_zero (form_yx h (Or.inr hJ) hH) hH (w := incV F z) (by rw [fa_inc, hz _ m0, map_zero])
      have z1 : fa σ W₁.J w (incV F H₁.x) = 0 := by
        have := congrArg (inclR (F := F) (AF F)) (hz _ m1)
        rwa [← fa_inc, e, fa_add, fa_inc, form_skew (sig_sig h) hJ, (hH.orth _).1, ← incM_mulVec, fa_iota2 hH, map_zero, neg_zero,
          map_zero, mul_zero, add_zero] at this
      obtain ⟨b, hb⟩ := k.2 w z1
      obtain ⟨c, hc⟩ := hy w
      refine span_pair_iff.2 ⟨c, b, ?_⟩
      rw [e, Matrix.mulVec_add, hc, hb, Matrix.mulVec_smul, hx, Matrix.mulVec_add, Matrix.mulVec_smul, incM_mulVec]
      abel

set_option maxHeartbeats 800000 in

theorem two_orders [MeasurableSpace (Multiplicative (AE F E))] [BorelSpace (Multiplicative (AE F E))] (hd : W.J.det ≠ 0)
    (hJ₁ : ∀ i j, σ (W₁.J j i) = -W₁.J i j) {f c₀ c φ c' : UA σ W.J → ℂ} (hf : IsAut f)
    (h0 : IsCT H f c₀) (h1 : ∀ lev : UA σ W₁.J → UA σ W.J, (∀ y, IsLevi H 1 y (lev y)) →
      IsAv ((ratU σ W₁.J).subgroupOf (unip σ W₁ H₁)) (fun u => lev u.1) c₀ c)
    (hφ : IsAv ((ratU σ W.J).subgroupOf (unipU σ W (Submodule.span E {H.x, H.ι *ᵥ H₁.x}))) Subtype.val f φ)
    (hc' : IsAv ((inclR (F := F) (E := E) (AF F)).toAddMonoidHom.toMultiplicative).range ((emb2 h hJ hH hH₁).comp uni) φ c') :
    c = c' := by
  obtain ⟨-, i1, i2, i3⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ d W.J
  obtain ⟨-, j1, j2, j3⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ d₁ W₁.J
  obtain ⟨k1, k2, hC, LR⟩ := ae_facts h
  have := PositivityTheory.ThKF.countable_ratU σ W.J
  have : DiscreteTopology (ratU σ W.J) := PositivityTheory.ThKF.discrete_ratU h (ε := -1) (fun i j => by simp [hJ]) hd
  have : DiscreteTopology (ratU σ W₁.J) := PositivityTheory.ThKF.discrete_ratU h (ε := -1) (fun i j => by simp [hJ₁]) hH.nondeg
  have G0 := unipGood h (Or.inr hJ) hd hH
  have G1 := unipGood h (Or.inr hJ₁) hH.nondeg hH₁
  have G2 := (unipUGood F E σ h d W (Or.inr hJ) hd (Submodule.span E {H.x, H.ι *ᵥ H₁.x})).1
  have := G1.lc
  have := G1.sc
  have : SecondCountableTopology (Multiplicative (AE F E)) := k2
  have : T2Space (Multiplicative (AE F E)) := t2AE
  obtain ⟨lev, ρ, c1, c2, v1, v2, v3, v4⟩ := levi_data h hJ hH
  have ρeq : ∀ u y, (∀ z, ∃ a : AE F E, mat u.1 *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat y *ᵥ z) + a • incV F H.x) → ρ u = y :=
    fun u y k => mat_inj (Matrix.ext_iff_mulVec.2 fun z => by
      obtain ⟨a, ha⟩ := v4 u z
      obtain ⟨b, hb⟩ := k z
      exact iota_inj h hJ hH (ha.symm.trans hb))
  let S : Subgroup (UA σ W.J) := ((unip σ W₁ H₁).comap ρ).map (stab σ W H.x).subtype
  have mS : ∀ u (hu : u ∈ stab σ W H.x), ρ ⟨u, hu⟩ ∈ unip σ W₁ H₁ → u ∈ S := fun u hu k => ⟨⟨u, hu⟩, k, rfl⟩
  have sS : S ≤ stab σ W H.x := Subgroup.map_subtype_le _
  have rS : ∀ u : S, ρ (Subgroup.inclusion sS u) ∈ unip σ W₁ H₁ := by
    rintro ⟨_, u, hu, rfl⟩
    exact hu
  have cS : IsClosed (S : Set (UA σ W.J)) := (stab_closed H.x).isClosedEmbedding_subtypeVal.isClosedMap _ (G1.closed.preimage c2)
  have cI : Continuous (Subgroup.inclusion sS) := continuous_subtype_val.subtype_mk _
  have k0 : ∀ u (hu : u ∈ stab σ W H.x), ρ ⟨u, hu⟩ = 1 ↔ u ∈ unip σ W H := fun u hu => by
    refine ⟨fun k => Subgroup.subset_closure ⟨hu, fun z => ?_⟩, fun k => ρeq _ _ fun z => ?_⟩
    · simpa only [k, mat_one, Matrix.one_mulVec] using v4 ⟨u, hu⟩ z
    · rw [mat_one, Matrix.one_mulVec]
      exact ((mem_unip h (Or.inr hJ) hH).1 k).2 _ (fa_iota hH z)
  have ls : ∀ y, lev y ∈ stab σ W H.x := fun y => (v1 y).1.trans (one_smul _ _)
  have lρ : ∀ y, ρ ⟨lev y, ls y⟩ = y := fun y => ρeq _ _ fun z =>
    ⟨0, by rw [zero_smul, add_zero, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, (v1 y).2.2]⟩
  obtain ⟨LS, st1⟩ := stage_sub (Γ := ratU σ W.J) (ΓB := (ratU σ W₁.J).subgroupOf (unip σ W₁ H₁)) cS G0.closed
    (fun u hu => mS u (((mem_unip h (Or.inr hJ) hH).1 hu).1.trans (one_smul _ _)) ((k0 _ _).2 hu ▸ one_mem _))
    (ι := lev.comp (unip σ W₁ H₁).subtype) (c1.comp continuous_subtype_val) (fun b => mS _ (ls b) ((lρ b).symm ▸ b.2))
    (π := (ρ.comp (Subgroup.inclusion sS)).codRestrict _ rS) ((c2.comp cI).subtype_mk _) (fun b => Subtype.ext (lρ b))
    (fun s => Subtype.ext_iff.trans (k0 _ _)) (fun b hb => v2 _ hb) (fun s hs => v3 _ hs) (lat_of_good G0) (lat_of_good G1)
  have A1 := st1 f c₀ c hf.1 hf.2 h0 (h1 lev v1)
  let m := emb2 h hJ hH hH₁
  have mc : Continuous m := continuous_SL2_embedding h hJ hH hH₁
  let x₁ := incV F (H.ι *ᵥ H₁.x)
  have xy : fa σ W.J (incV F H.x) (incV F H.y) = 1 := by rw [fa_inc, hH.xy, map_one]
  have x1y : fa σ W.J x₁ (incV F H.y) = 0 := by rw [fa_inc, (hH.orth _).2, map_zero]
  have act : ∀ s : S, mat s.1 *ᵥ x₁ = x₁ + fa σ W.J (mat s.1 *ᵥ x₁) (incV F H.y) • incV F H.x := fun s => by
    obtain ⟨a, ha⟩ := v4 (Subgroup.inclusion sS s) (incV F H₁.x)
    rw [((mem_unip h (Or.inr hJ₁) hH₁).1 (rS s)).1, Units.val_one, one_smul, incM_mulVec] at ha
    change mat s.1 *ᵥ x₁ = x₁ + _ at ha
    rw [ha, fa_add, x1y, xy, zero_add, mul_one]
  let π : S →* Multiplicative (AE F E) := MonoidHom.mk' (fun s => .ofAdd (fa σ W.J (mat s.1 *ᵥ x₁) (incV F H.y))) fun s t => by
    rw [← ofAdd_add, Subgroup.coe_mul, mat_mul, ← Matrix.mulVec_mulVec]
    conv_lhs => rw [act t, Matrix.mulVec_add, Matrix.mulVec_smul, sS s.2, fa_add, xy, mul_one]
  have ns : ∀ b, m (uni b) ∈ stab σ W H.x := fun b => (emb2_mulVec_incV_x_and_complement_x h hJ hH hH₁ (uni b)).1.trans (by simp [uni_val])
  have nρ : ∀ b, ρ ⟨m (uni b), ns b⟩ = 1 := fun b => ρeq _ _ fun z => ⟨b.toAdd * fa σ W₁.J z (incV F H₁.y), by
    change mat (emb2 h hJ hH hH₁ _) *ᵥ _ = _
    rw [emb2_mulVec_complement_eq, ← map_inv, uni_val, uni_val]; simp [mat_one]⟩
  have ur := uni_map (inclR (F := F) (E := E) (AF F))
  obtain ⟨-, st2⟩ := stage_sub (Γ := ratU σ W.J) (ΓB := ((inclR (F := F) (E := E) (AF F)).toAddMonoidHom.toMultiplicative).range) cS
    G2.closed (fun u hu => by
      have hx : u ∈ stab σ W H.x := ((unipU_eq _).choose_spec.choose_spec.2 u).1 hu |>.1 _ (Submodule.subset_span (by simp))
      exact mS u hx ((mem_pair h hJ hH hH₁ hJ₁ hx (v4 ⟨u, hx⟩)).1 hu).1)
    (ι := m.comp uni) (mc.comp continuous_uni) (fun b => mS _ (ns b) (nρ b ▸ one_mem _)) (π := π)
    (continuous_ofAdd.comp (((continuous_mat.comp continuous_subtype_val).matrix_mulVec continuous_const).dotProduct continuous_const))
    (fun b => by
      change Multiplicative.ofAdd (fa σ W.J (mat (emb2 h hJ hH hH₁ (uni b)) *ᵥ x₁) _) = b
      rw [(emb2_mulVec_incV_x_and_complement_x h hJ hH hH₁ _).2, add_comm, uni_val]
      simp [fa_add, xy, x1y, x₁])
    (fun s => by
      rw [mem_pair h hJ hH hH₁ hJ₁ (sS s.2) (v4 (Subgroup.inclusion sS s)), and_iff_right (rS s)]
      refine ⟨fun k => ?_, fun k => congrArg Multiplicative.ofAdd ((congrArg (fa σ W.J · _) k).trans x1y)⟩
      have := act s
      rwa [show fa σ W.J (mat s.1 *ᵥ x₁) (incV F H.y) = 0 from k, zero_smul, add_zero] at this)
    (by
      rintro _ ⟨ξ, rfl⟩
      exact (congrArg m (ur ξ.toAdd)).symm ▸ emb2_map_inclR h hJ hH hH₁ _)
    (fun s hs => by
      obtain ⟨A, hA⟩ := (rat_iff _).1 hs
      refine ⟨.ofAdd (form σ W.J (A *ᵥ (H.ι *ᵥ H₁.x)) H.y), congrArg Multiplicative.ofAdd ?_⟩
      rw [hA, incM_mulVec, fa_inc]; rfl) (lat_of_good G2) LR
  exact uniq_sub cS LS A1 (st2 f φ c' hf.1 hf.2 hφ hc')

set_option maxHeartbeats 800000 in

theorem two_kill (hd : W.J.det ≠ 0) (hJ₁ : ∀ i j, σ (W₁.J j i) = -W₁.J i j) {f c₀ c : UA σ W.J → ℂ} (hf : IsAut f) (hm : Mod f)
    (h0 : IsCT H f c₀) (h1 : ∀ lev : UA σ W₁.J → UA σ W.J, (∀ y, IsLevi H 1 y (lev y)) →
      IsAv ((ratU σ W₁.J).subgroupOf (unip σ W₁ H₁)) (fun u => lev u.1) c₀ c) {l : ℂ} (hl : ‖l‖ < 1) {a : UA σ W.J}
    (ha : a = emb2 h hJ hH hH₁ (dia (halfE F E)⁻¹)) (law : ∀ x, c (a * (a * x)) - c (a * x) = l * (c (a * x) - c x)) (x : UA σ W.J) :
    c (a * x) = c x := by
  obtain ⟨-, i1, i2, i3⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ d W.J
  obtain ⟨k1, k2, hC, LR⟩ := ae_facts h
  obtain ⟨l1, l2, l3⟩ := sl_facts (R := AE F E)
  have := PositivityTheory.ThKF.countable_ratU σ W.J
  have : DiscreteTopology (ratU σ W.J) := PositivityTheory.ThKF.discrete_ratU h (ε := -1) (fun i j => by simp [hJ]) hd
  have G2 := (unipUGood F E σ h d W (Or.inr hJ) hd (Submodule.span E {H.x, H.ι *ᵥ H₁.x})).1
  have := G2.lc
  have := G2.sc
  letI : MeasurableSpace (Multiplicative (AE F E)) := borel _
  have : BorelSpace (Multiplicative (AE F E)) := ⟨rfl⟩
  have : SecondCountableTopology (Multiplicative (AE F E)) := k2
  have : T2Space (Multiplicative (AE F E)) := t2AE
  letI : MeasurableSpace SL(2, AE F E) := borel _
  have : BorelSpace SL(2, AE F E) := ⟨rfl⟩
  have := first_of (UA σ W.J)
  let m := emb2 h hJ hH hH₁
  have mc : Continuous m := continuous_SL2_embedding h hJ hH hH₁
  have ur := uni_map (inclR (F := F) (E := E) (AF F))
  obtain ⟨φ, hφ⟩ := (lat_of_good G2).isAv_ex (ι := Subgroup.subtype _) (f := f) fun γ hγ => hf.2 _ hγ
  have φc : Continuous φ := hφ.cont (lat_of_good G2) continuous_subtype_val hf.1 fun γ hγ => hf.2 _ hγ
  have φi : ∀ γ ∈ (Matrix.SpecialLinearGroup.map (n := Fin 2) (inclR (F := F) (E := E) (AF F))).range, ∀ x, φ (m γ * x) = φ x := by
    rintro _ ⟨g, rfl⟩
    have r := emb2_map_inclR h hJ hH hH₁ g
    have n1 := emb2_norm h hJ hH hH₁ g
    have n2 := emb2_norm h hJ hH hH₁ g⁻¹
    rw [map_inv, map_inv] at n2
    exact IsAv.conj_sub G2.closed (lat_of_good G2) hφ r (fun u => conj_unipU r n1 n2)
      (fun u hu => by simpa using conj_unipU (inv_mem r) n2 (by simpa using n1) hu) (hf.2 _ r)
  have φu : ∀ γ ∈ ((inclR (F := F) (E := E) (AF F)).toAddMonoidHom.toMultiplicative).range, ∀ x, φ ((m.comp uni) γ * x) = φ x := by
    rintro _ ⟨ξ, rfl⟩
    exact φi _ ⟨_, (ur ξ.toAdd).symm⟩
  obtain ⟨c', hc'⟩ := LR.isAv_ex φu
  obtain rfl : c = c' := two_orders h hJ hH hH₁ hd hJ₁ hf h0 h1 hφ hc'
  have cc := hc'.cont LR (mc.comp continuous_uni) φc φu
  obtain ⟨lam, _, hlam⟩ := LR.isAv_prob (H := UA σ W.J)
  obtain ⟨k, hk⟩ := (hm.av G2 hf.2 hφ).gr mc (dia (halfE F E)⁻¹) x
  have D : Dat _ uni (dia (halfE F E)⁻¹) lam l (fun g => φ (m g * x)) fun g => c (m g * x) :=
    ⟨by fun_prop, fun γ hγ g => by rw [map_mul, mul_assoc, φi γ hγ], by fun_prop,
      fun g => by simp only [hlam _ φ c hc', map_mul, mul_assoc]; rfl,
      fun g => by simpa only [map_mul, mul_assoc, ha] using law (m g * x)⟩
  simpa [ha] using kill hC continuous_uni hl D hk 1

end PositivityTheory.ThKEnd.Two

end
