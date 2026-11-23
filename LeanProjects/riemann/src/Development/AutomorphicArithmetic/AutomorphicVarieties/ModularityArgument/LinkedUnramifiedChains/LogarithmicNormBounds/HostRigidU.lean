import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.IsIrrOfMatIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostOk
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CzBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigDiag
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LevelAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.GaussianFieldRangeEqKerQuarticChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.BkAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RestrictionToDecompositionGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.LkHost
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HostEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.LogarithmicNormBounds.HostUnl
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.FreeCU
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.IsIrrOfMatIrr

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete
  UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section Local

open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  by_contra hx
  have hx' : x ∉ N := fun h => hx ((QuotientGroup.eq_one_iff x).2 h)
  have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
  let V : Subgroup (G ⧸ N) := U.toSubgroup.map (QuotientGroup.mk' N)
  have hVo : IsOpen (V : Set (G ⧸ N)) := QuotientGroup.isOpenMap_coe _ U.isOpen'
  have hV : IsClopen (V : Set (G ⧸ N)) := ⟨V.isClosed_of_isOpen hVo, hVo⟩
  obtain ⟨u, hu, hux⟩ := hV.connectedComponent_subset V.one_mem hy
  exact hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)

private theorem cocycle_coboundary_of_finite_index {k G W : Type} [Field k] [CharZero k] [Group G] [AddCommGroup W] [Module k W]
    (a : G → W →ₗ[k] W) (hmul : ∀ g h w, a (g * h) w = a g (a h w)) (f : G → W)
    (hf : ∀ g h, f (g * h) = f g + a g (f h)) (H : Subgroup G) [H.FiniteIndex] (x : W)
    (hx : ∀ h ∈ H, f h = a h x - x) : ∃ y, ∀ g, f g = a g y - y := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set f' : G → W := fun g => f g - (a g x - x) with hf'
  have hc : ∀ g h, f' (g * h) = f' g + a g (f' h) := by
    intro g h
    simp only [hf', hf, hmul, map_sub]
    abel
  have hH : ∀ g h, h ∈ H → f' (g * h) = f' g := by
    intro g h hh
    rw [hc]
    have : f' h = 0 := by simp only [hf', hx h hh, sub_self]
    rw [this, map_zero, add_zero]
  let F : G ⧸ H → W := Quotient.lift f' (by
    intro g g' hgg
    have h1 : g⁻¹ * g' ∈ H := QuotientGroup.leftRel_apply.1 hgg
    have := hH g _ h1
    rw [mul_inv_cancel_left] at this
    exact this.symm)
  have hF : ∀ (g : G) (q : G ⧸ H), F (g • q) = f' g + a g (F q) := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H z => exact hc g z
  set S : W := ∑ q, F q with hS
  have hsum : ∀ g, S = (Fintype.card (G ⧸ H) : k) • f' g + a g S := by
    intro g
    have e1 : ∑ q, F (g • q) = S := Equiv.sum_comp (MulAction.toPerm g) F
    refine e1.symm.trans ?_
    simp only [hF, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← map_sum,
      Nat.cast_smul_eq_nsmul, ← hS]
  have hn : (Fintype.card (G ⧸ H) : k) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨x - (Fintype.card (G ⧸ H) : k)⁻¹ • S, fun g => ?_⟩
  have e : f' g = (Fintype.card (G ⧸ H) : k)⁻¹ • (S - a g S) := by
    rw [eq_inv_smul_iff₀ hn, eq_sub_iff_add_eq]
    exact (hsum g).symm
  have e2 : f g = f' g + (a g x - x) := by simp only [hf', sub_add_cancel]
  rw [e2, e, map_sub, map_smul, smul_sub]
  abel

private theorem rig_avg {K D V : Type} [Field K] [CharZero K] [Group D] [AddCommGroup V] [Module K V]
    (ρ : Representation K D V) (y : D → V) (hy : ∀ g h, y (g * h) = y g + ρ g (y h)) (I N : Subgroup D) [N.FiniteIndex]
    (h : ∀ s ∈ I, s ∈ N → y s = 0) : ∃ x, ∀ s ∈ I, y s = ρ s x - x := by
  obtain ⟨x, hx⟩ := cocycle_coboundary_of_finite_index (k := K) (G := I) (fun g => ρ g) (fun g h w => by simp) (fun g => y g)
    (fun g h => hy g h) (N.subgroupOf I) 0 (fun s hs => by simp [h s s.2 hs])
  exact ⟨x, fun s hs => hx ⟨s, hs⟩⟩

private theorem rig_away {O K G' Γ ι : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [Field K] [CharZero K]
    [Algebra O K] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [Group Γ] [TopologicalSpace Γ]
    (F : Frame O G' Γ ι) (hF : F.Ok) (r : Γ →* GG 3 K) (hm : HasMult F.η r) (y : Γ → Matrix (Fin 3) (Fin 3) K)
    (r' : Γ →* GG 3 (DualNumber K)) (hy : IsCoc r y)
    (hd : IsDeform ((GG.map (algebraMap K (DualNumber K))).comp r)
      (fun g => (y g).map (TrivSqZeroExt.inr : K → DualNumber K)) r')
    (hN : ∀ v ∉ F.Tb, ∀ s ∈ F.Nv v, y (F.loc v s) = 0)
    (hD : ∀ v ∈ F.Sb, ∃ h, DiagIn (F.ηv v) (F.Ψv v) (F.Iv v) (r'.comp (F.loc v)) h) (v : ι) (hv : v ≠ F.vl) :
    ∃ X, ∀ s ∈ F.I v, y (F.π s) = adRep r (F.π s) X - X := by
  suffices h : ∃ X, ∀ s ∈ F.Iv v, y (F.loc v s) = adRep (r.comp (F.loc v)) s X - X by
    obtain ⟨X, hX⟩ := h
    exact ⟨X, fun s hs => hX ⟨s, hF.I_le v hs⟩ hs⟩
  by_cases hb : v ∈ F.Sb
  · obtain ⟨h, hh⟩ := hD v hb
    exact rig_diag (F.ηv v) (F.Ψv v) (F.Iv v) (r.comp (F.loc v)) (fun s => y (F.loc v s)) (r'.comp (F.loc v)) h
      (hF.η_I v (Or.inr hb)) (fun g => hm _) (fun g => hd _) hh
  · have hT : v ∉ F.Tb := fun h => h.elim hv hb
    refine rig_avg (adRep (r.comp (F.loc v))) (fun s => y (F.loc v s)) (fun g h => ?_) (F.Iv v)
      ((F.ηv v).ker ⊓ ((Units.map (residue O).toMonoidHom).comp (F.Ψv v)).ker) fun s hs hs' => hN v hT s ⟨⟨hs, hs'.1⟩, hs'.2⟩
    rw [map_mul]
    exact hy _ _

private theorem rig_fst {K D : Type} [Field K] [Group D] (r : D →* GG 3 K) (y : D → Matrix (Fin 3) (Fin 3) K)
    (r' : D →* GG 3 (DualNumber K))
    (hd : IsDeform ((GG.map (algebraMap K (DualNumber K))).comp r)
      (fun g => (y g).map (TrivSqZeroExt.inr : K → DualNumber K)) r') (h : GL (Fin 3) (DualNumber K)) (g : D) (i j : Fin 3) :
    ((conjBy h⁻¹ r' g).mat i j).fst =
      (conjBy (GeneralLinearGroup.map (TrivSqZeroExt.fstHom K K K).toRingHom h)⁻¹ r g).mat i j := by
  have e : GG.map (TrivSqZeroExt.fstHom K K K).toRingHom (r' g) = r g := by
    refine SemidirectProduct.ext (Units.ext ?_) (hd g).1
    ext a b
    show ((r' g).mat a b).fst = (r g).mat a b
    rw [(hd g).2, Matrix.add_mul, Matrix.one_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_three, TrivSqZeroExt.algebraMap_eq_inl]
  have e2 : GG.map (TrivSqZeroExt.fstHom K K K).toRingHom (conjBy h⁻¹ r' g) =
      conjBy (GeneralLinearGroup.map (TrivSqZeroExt.fstHom K K K).toRingHom h)⁻¹ r g := by
    show GG.map _ (GG.ofGL h⁻¹ * r' g * (GG.ofGL h⁻¹)⁻¹) = GG.ofGL _ * r g * (GG.ofGL _)⁻¹
    rw [map_mul, map_mul, map_inv, e, ← map_inv (GeneralLinearGroup.map _)]
    rfl
  rw [← e2]
  rfl

private theorem rig_char {l : ℕ} [Fact l.Prime] (c : Coef l) (u : ℤ_[l]ˣ) (e : ℕ) (a : Fin 3) :
    algebraMap c.O (DualNumber (PadicAlgCl l))
      (((Units.map (algebraMap ℤ_[l] c.O).toMonoidHom u ^ (e : ℤ)) ^ wt1 a : c.Oˣ) : c.O) =
      ((Units.map (algebraMap ℤ_[l] (DualNumber (PadicAlgCl l)) : ℤ_[l] →* _) u ^ ((e : ℤ) * wt1 a) :
        (DualNumber (PadicAlgCl l))ˣ) : DualNumber (PadicAlgCl l)) := by
  have h : Units.map (algebraMap ℤ_[l] (DualNumber (PadicAlgCl l)) : ℤ_[l] →* _) u =
      Units.map (algebraMap c.O (DualNumber (PadicAlgCl l))).toMonoidHom
        (Units.map (algebraMap ℤ_[l] c.O).toMonoidHom u) := Units.ext rfl
  rw [h, ← map_zpow (Units.map (algebraMap c.O (DualNumber (PadicAlgCl l))).toMonoidHom), _root_.zpow_mul]
  rfl

private theorem rig_above (hP : UpperTheory.V.Loc.LocalPublishedTheorems) (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ) (hD : HostData l e ψ o₁)
    (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S)
    (hF : IsHostFrame Ω c e ψ S A F) (g₁ : Gam Ω S) (r : Gam Ω S →* GG 3 (PadicAlgCl l)) (hr : F.IsCharZeroPt g₁ r)
    (hm : HasMult F.η r) (hc : Continuous (mats r)) (y : Gam Ω S → Matrix (Fin 3) (Fin 3) (PadicAlgCl l))
    (r' : Gam Ω S →* GG 3 (DualNumber (PadicAlgCl l))) (hyc : Continuous y) (hy : IsCoc r y)
    (hd : IsDeform ((GG.map (algebraMap (PadicAlgCl l) (DualNumber (PadicAlgCl l)))).comp r)
      (fun g => (y g).map (TrivSqZeroExt.inr : PadicAlgCl l → DualNumber (PadicAlgCl l))) r')
    (h : GL (Fin 3) (DualNumber (PadicAlgCl l)))
    (hh : TriIn (F.ηv F.vl) (F.Ψv F.vl) (F.Iv F.vl) (r'.comp (F.loc F.vl)) h)
    (φ : F.D F.vl →* Formalism.BasicNotions.Loc.GQ l) (hφ : Topology.IsOpenEmbedding φ)
    (hI : ∀ g, φ g ∈ UpperTheory.V.Loc.Iq l → g ∈ F.Iv F.vl)
    (hcy : ∀ g, UpperTheory.V.Loc.cyc l l (φ g) = cycZ ℚ Ω l (g : G ℚ Ω)) :
    (fun g => y (F.loc F.vl g)) ∈ UpperTheory.V.Loc.finiteCocycles φ (adRep (r.comp (F.loc F.vl))) := by
  have ok := hostFrame_ok Ω c e ψ o₁ hD S A F hF
  obtain ⟨H, hn, ho, hle, hΨ, g, hg, hu, hg1⟩ := rig_sub Ω c e ψ o₁ hD S A F hF
  have hl : Continuous (F.loc F.vl) := ok.π_cont.comp continuous_subtype_val
  refine rig_loc hP φ hφ (F.ηv F.vl) (ok.η_cont.comp_continuous hl) (r.comp (F.loc F.vl)) _ (r'.comp (F.loc F.vl)) h
    (fun g => hm _) (hc.comp hl) (hyc.comp hl) (fun g k => ?_) (fun g => hd _) H ho hle hh.tri
    (fun a => (e : ℤ) * wt1 a) ?_ (fun s hs hs' a => ?_) (fun i j hij => ⟨g, hg, ?_⟩)
  · simp only [map_mul]
    exact hy _ _
  · have he : (0 : ℤ) < e := by exact_mod_cast hD.e_pos
    intro a b hab
    refine mul_lt_mul_of_pos_left ?_ he
    have : (a : ℕ) < b := hab
    simp only [wt1]
    omega
  · rw [hh.ine s (hI s hs') (hle hs) a, psi, hΨ s hs (hI s hs')]
    have := rig_char c (cycZ ℚ Ω l (s : G ℚ Ω)) e a
    rw [← hcy] at this
    rw [UpperTheory.V.Base.chiO, MonoidHom.comp_apply, ← hcy]
    exact this
  · have hf := rig_fst (r.comp (F.loc F.vl)) (fun g => y (F.loc F.vl g)) (r'.comp (F.loc F.vl)) (fun g => hd _) h g
    rw [hf, hf]
    refine rig_eig c F g₁ r hr (F.loc F.vl g) (hle hg) hu _ (fun a b hab => ?_) i j hij.ne _ ?_
    · refine (hf a b).symm.trans ?_
      rw [hh.tri g (hle hg) a b (by
        have : (b : ℕ) < a := hab
        simp only [wt, wt1]
        omega)]
      rfl
    · have e1 : ((UpperTheory.V.Loc.cycA l l (PadicAlgCl l) (φ g) : (PadicAlgCl l)ˣ) : PadicAlgCl l) - 1 =
          algebraMap ℚ_[l] (PadicAlgCl l)
            ((((cycZ ℚ Ω l (g : G ℚ Ω) : ℤ_[l]ˣ) : ℤ_[l]) - 1 : ℤ_[l]) : ℚ_[l]) := by
        rw [← hcy, PadicInt.coe_sub, map_sub, PadicInt.coe_one, map_one]
        rfl
      rw [e1, norm_algebraMap']
      exact hg1

end Local

section Glob

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

open Matrix Formalism.MainNotions.N in
private theorem ss_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {ρ ρ' : Γ →* GL (Fin n) k} (h : GL (Fin n) k)
    (hh : ∀ g, ρ' g = h * ρ g * h⁻¹) (hρ : IsSSRep ρ) : IsSSRep ρ' := by
  let e : (Fin n → k) ≃ₗ[k] (Fin n → k) := Matrix.toLin'OfInv (M := (h : Matrix (Fin n) (Fin n) k))
    (M' := ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (Units.mul_inv h) (Units.inv_mul h)
  have he : ∀ v, e v = ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ v := fun v => rfl
  have key : ∀ g v, e ((ρ' g : Matrix (Fin n) (Fin n) k) *ᵥ v) = (ρ g : Matrix (Fin n) (Fin n) k) *ᵥ e v := by
    intro g v
    rw [he, he, hh, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  intro W hW
  obtain ⟨W', hW', hc⟩ := hρ (W.map (e : (Fin n → k) →ₗ[k] (Fin n → k))) (by
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨_, hW g v hv, key g v⟩)
  refine ⟨W'.comap (e : (Fin n → k) →ₗ[k] (Fin n → k)), fun g v hv => ?_, ?_⟩
  · show e _ ∈ W'
    rw [key]
    exact hW' g _ hv
  · have := (Submodule.orderIsoMapComap e).symm.isCompl hc
    have h2 : IsCompl ((W.map (e : (Fin n → k) →ₗ[k] (Fin n → k))).comap (e : (Fin n → k) →ₗ[k] (Fin n → k)))
      (W'.comap (e : (Fin n → k) →ₗ[k] (Fin n → k))) := this
    rwa [Submodule.comap_map_eq_of_injective e.injective] at h2

private theorem autCsd_iso {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} (h : Af.RepIso r r')
    (H : Af.IsAutCsd ι r) : Af.IsAutCsd ι r' := by
  obtain ⟨π, h1, h2, h3, h4⟩ := H
  refine ⟨π, h1, h2, ss_conj h.choose h.choose_spec h3, h4.mono fun w ⟨B, hB, hB'⟩ => ⟨B, hB, hB'.of_iso h⟩⟩

private theorem tw_iso {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (χ : Γ →* kˣ)
    (h : Af.RepIso r r') : Af.RepIso (Af.tw r χ) (Af.tw r' χ) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s => Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, Af.tw_val, Af.tw_val, hg, Units.val_mul, Units.val_mul, Matrix.mul_smul,
    Matrix.smul_mul]

private theorem conj_left {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (h : GL (Fin 3) R) (g : G)
    (hg : (r g).right = 1) : (conjBy h r g).left = h * (r g).left * h⁻¹ := by
  have e : conjBy h r g = GG.ofGL h * r g * GG.ofGL h⁻¹ := by
    rw [map_inv]; rfl
  rw [e, SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
    SemidirectProduct.left_inl, SemidirectProduct.right_inl, sgnAct_one, SemidirectProduct.mul_right,
    SemidirectProduct.right_inl, hg, mul_one, sgnAct_one]

open Matrix in
private theorem matIrr_conj {G R : Type} [Group G] [CommRing R] {m : ℕ} {U : Subgroup G}
    {a a' : G → Matrix (Fin m) (Fin m) R} (h : GL (Fin m) R)
    (e : ∀ g ∈ U, a g = ((h⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * a' g * h) (H : MatIrr U a) :
    MatIrr U a' := by
  intro W hW
  have hv : ∀ v : Fin m → R, (h : Matrix (Fin m) (Fin m) R) *ᵥ
      (((h⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rcases H (W.comap (Matrix.toLin' (h : Matrix (Fin m) (Fin m) R))) (fun g hg v hv' => by
    rw [Submodule.mem_comap, Matrix.toLin'_apply] at hv' ⊢
    rw [e g hg, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv]
    exact hW g hg _ hv') with h0 | h0
  · refine Or.inl (eq_bot_iff.2 fun v hv' => ?_)
    have : ((h⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) *ᵥ v ∈
        W.comap (Matrix.toLin' (h : Matrix (Fin m) (Fin m) R)) := by
      rwa [Submodule.mem_comap, Matrix.toLin'_apply, hv]
    rw [h0, Submodule.mem_bot] at this
    rw [Submodule.mem_bot, ← hv v, this, Matrix.mulVec_zero]
  · refine Or.inr (eq_top_iff.2 fun v _ => ?_)
    have : ((h⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) *ᵥ v ∈
        W.comap (Matrix.toLin' (h : Matrix (Fin m) (Fin m) R)) := h0 ▸ Submodule.mem_top
    rwa [Submodule.mem_comap, Matrix.toLin'_apply, hv] at this

open TensorProduct in
private theorem h1f_equiv_of_intertwiner {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
    {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V]
    (ρ ρ' : Representation C (G F Ω) V) (f f' : V →ₗ[C] V) (hc : Continuous f) (hff : ∀ x, f' (f x) = x)
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (hf' : ∀ g x, f' (ρ' g x) = ρ g (f' x)) (H : Af.BlochKatoSelmerVanishes l ρ') :
    Af.BlochKatoSelmerVanishes l ρ := by
  intro c hZ hb
  have h := H (fun g => f (c g)) ⟨hc.comp hZ.1, fun g h => by simp only [hZ.2 g h, map_add, hf]⟩ ⟨fun w hw => ?_, fun τ => ?_⟩
  · obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 h
    refine (mem_coboundaries1 _ _).2 ⟨f' m, fun g => ?_⟩
    rw [← hff (c g), hm g, map_sub, hf']
  · obtain ⟨A, hA, x, hx⟩ := hb.away w hw
    exact ⟨A, hA, f x, fun s hs => by rw [hx s hs, map_sub, hf]⟩
  · obtain ⟨j, hj, ⟨h1, h2⟩, x, hx⟩ := hb.above τ
    refine ⟨j, hj, ⟨hc.comp h1, fun g h => ?_⟩, LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l]) x, fun g => ?_⟩
    · refine (congrArg f (h2 g h)).trans ?_
      rw [map_add]
      exact congrArg _ (hf _ _)
    · have key : ∀ y : V ⊗[ℚ_[l]] Loc.Bcr l, LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l])
          (Loc.actC ((MonoidHom.snd _ _).comp (Af.decJ F j).subtype)
            (ρ.comp ((MonoidHom.fst _ _).comp (Af.decJ F j).subtype)) g y) =
          Loc.actC ((MonoidHom.snd _ _).comp (Af.decJ F j).subtype)
            (ρ'.comp ((MonoidHom.fst _ _).comp (Af.decJ F j).subtype)) g
            (LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l]) y) := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp [Loc.actC, hf]
        | add a b ha hb => simp only [map_add, ha, hb]
      rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
      rfl

private theorem h1f_vanishing_conj_invariant {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [Fact l.Prime] (R : G ℚ Ω →* GG 3 (PadicAlgCl l))
    (h : GL (Fin 3) (PadicAlgCl l)) (H : Af.BlochKatoSelmerVanishes l (adRep (conjBy h R))) : Af.BlochKatoSelmerVanishes l (adRep R) := by
  have e : ∀ g, conjBy h R g = GG.ofGL h * R g * (GG.ofGL h)⁻¹ := fun g => rfl
  refine h1f_equiv_of_intertwiner _ _ (GG.ad 3 _ (GG.ofGL h)) (GG.ad 3 _ (GG.ofGL h)⁻¹) ?_ (fun x => ?_) (fun g x => ?_) (fun g x => ?_) H
  · have : ⇑(GG.ad 3 _ (GG.ofGL h)) = fun X => (GG.ofGL h).mat * X *
        (((GG.ofGL h).left⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) := by
      funext X
      rw [GG.ad_apply, GG.adFun, if_pos (SemidirectProduct.right_inl _)]
    rw [this]
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  · rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  · show GG.ad 3 _ _ (GG.ad 3 _ (R g) x) = GG.ad 3 _ (conjBy h R g) _
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, e, inv_mul_cancel_right]
  · show GG.ad 3 _ _ (GG.ad 3 _ (conjBy h R g) x) = GG.ad 3 _ (R g) _
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, e, mul_assoc, inv_mul_cancel_left]

private theorem val_of_even {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {M : ℕ} (hM : Even M)
    (h : B.valuation ((4 : ℕ) : Ω) < 1) : B.valuation (M : Ω) < 1 := by
  obtain ⟨m, rfl⟩ := hM.two_dvd
  have h2 : B.valuation ((2 : ℕ) : Ω) < 1 := by
    by_contra h2
    rw [not_lt] at h2
    rw [show (4 : ℕ) = 2 * 2 from rfl, Nat.cast_mul, map_mul] at h
    exact absurd h (not_lt.2 (one_le_mul h2 h2))
  have hm : B.valuation (m : Ω) ≤ 1 := (B.valuation_le_one_iff _).2 (natCast_mem B m)
  rw [Nat.cast_mul, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' hm) h2

private theorem unl_iso {l : ℕ} [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {n M : ℕ} {m : Fin n → ℤ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} (H : Th.Unl l M m r) (h : Af.RepIso r r') :
    Th.Unl l M m r' := fun w hw => by
  obtain ⟨A, hA, κ, ⟨χ, h1, h2, h3⟩, h4⟩ := H w hw
  exact ⟨A, hA, κ, ⟨χ, h1, h2.of_iso h, h3⟩, h4⟩

private theorem cont_hom {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ] [Monoid M] [TopologicalSpace M]
    (f : Γ →* Mˣ) (h : Continuous fun g => (f g : M)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

open Formalism.GaloisCohomology UpperTheory.V.Base in
private theorem selmer_h1_vanishes_at_rigid_point (hH : Af.HypothesesH) (hL : Th.AdL) (hU : Z.J.UnlEndLogNorm) (K : Type) [Field K] [NumberField K] [IsCMField K] (hK : IsQi K)
    (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ)
    (ψ : DirichletCharacter c.O N) (o₁ : ℕ) (hd : UnitaryThreeInertia.HostData l e ψ o₁) (S : Finset UnitaryThreeInertia.Pl) (A : S → ValuationSubring Ω)
    (F : UnitaryThreeInertia.Frame c.O (G ℚ Ω) (UnitaryThreeInertia.Gam Ω S) S) (hF : UnitaryThreeInertia.IsHostFrame Ω c e ψ S A F) (ι : Qbar l ≃+* ℂ)
    (g₁ : UnitaryThreeInertia.Gam Ω S) (hg : F.Marked g₁) (r : UnitaryThreeInertia.Gam Ω S →* GG 3 (PadicAlgCl l)) (hr : F.IsCharZeroPt g₁ r)
    (hmu : HasMult F.η r) (hc : Continuous (mats r)) (hB : BPrime K ι fun s => (r (toGS Ω _ s)).mat) :
    Af.BlochKatoSelmerVanishes l (adRep (r.comp F.π)) := by
  have hN := hH.litN
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (dvrFacts l c.O).2.2.1
  haveI : CharP (ResidueField c.O) l := by
    rw [CharP.charP_iff_prime_eq_zero hl.out, ← map_natCast (residue c.O), residue_eq_zero_iff,
      mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O)]
    intro hu
    exact PadicInt.prime_p.not_unit (isUnit_of_map_unit _ _ hu)
  obtain ⟨σ, hσ, hσc⟩ := hF.cc
  have hv : (A F.vl).valuation (l : Ω) < 1 := by simpa using (hF.isOver F.vl (l : 𝓞 ℚ)).2 hF.vl
  have hfr := Fr.host_ex ⟨⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.pt⟩, hN.coh.uo, hN.coh.gw⟩
    Ω l c N e ψ o₁ hd σ hσ _ hv
  have hσ' : IsConjOm σ.toRingEquiv := hσ
  have hΨ : Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1 := by
    have h1 : cycZ ℚ Ω l σ = -1 := hσ'.cyc (E := ℚ)
    have h2 : chiO ℚ Ω l c.O σ = -1 := by
      show Units.map (algebraMap ℤ_[l] c.O).toMonoidHom (cycZ ℚ Ω l σ) = -1
      rw [h1]
      apply Units.ext
      simp
    have h3 : (Chr.dirG ℚ Ω ψ σ : c.O) = (-1) ^ e := by
      rw [Chr.dirG, MonoidHom.comp_apply, (Chr.clsFacts ℚ Ω N).2.2.2.1 σ hσ', MulChar.coe_toUnitHom]
      exact hd.par
    apply Units.ext
    show ((chiO ℚ Ω l c.O σ ^ (e : ℤ) * Chr.dirG ℚ Ω ψ σ : c.Oˣ) : c.O) = 1
    rw [h2, zpow_natCast, Units.val_mul, h3, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, ← mul_pow]
    simp
  have hram : ∀ B' : ValuationSubring Ω, ¬ Ine (F := ℚ) B' ≤ (UnitaryThreeInertia.eta4 Ω).ker →
      B'.valuation ((l * N : ℕ) : Ω) < 1 := by
    intro B' h
    refine val_of_even B' (hd.N_even.mul_left l) ?_
    by_contra h4
    refine h fun s hs => ?_
    have h5 : Chr.cls ℚ Ω 4 s = 1 := (Chr.clsFacts ℚ Ω 4).2.2.2.2 B' h4 hs
    rw [MonoidHom.mem_ker, UnitaryThreeInertia.eta4, Chr.dirG, MonoidHom.comp_apply, h5, map_one]
  have hk : LinkHyp c N e (UnitaryThreeInertia.eta4 Ω) σ (A F.vl) (l * N) :=
    ⟨hd.e_pos, dvd_rfl, mul_ne_zero hl.out.ne_zero (NeZero.ne N), hram, hv, hσ⟩
  obtain ⟨_, _, ρ, hρ, hAut⟩ := hB.aut
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  have hopen : IsOpen ((UnitaryThreeInertia.eta4 Ω).ker : Set (G ℚ Ω)) := by
    rw [← (UnitaryThreeInertia.gaussian_field_range_eq_ker_quartic_char.2 Ω K hK).1, Base.range_galEmb]
    exact (Base.galEmbTop ℚ K Ω).2.1
  have hη₀ : ∀ g, F.η (toGS Ω _ g) = UnitaryThreeInertia.eta4 Ω g := fun g => by rw [← hF.η, hF.π]; rfl
  have hTI : U3.TypeI F.η r := fun W hW => hB.opens _ hopen le_rfl W fun s hs v hv =>
    hW (toGS Ω _ s) (by
      rw [MonoidHom.mem_ker, hη₀]
      exact hs) v hv
  have hunl := Z.J.hostUnlE hH hU K hK Ω l c N e ψ o₁ hd S A F hF g₁ hg r hr hTI ρ hρ
  have hρc : Continuous ρ := by
    refine cont_hom _ ?_
    simp only [hρ]
    exact (hc.comp (continuous_toGS Ω _)).comp (Base.galEmbTop ℚ K Ω).1.continuous
  obtain ⟨B, _, _, t, r', hr', ht⟩ := hr
  obtain ⟨g, rfl⟩ : ∃ g, toGS Ω _ g = g₁ := QuotientGroup.mk_surjective g₁
  rw [hF.π] at hσc ⊢
  have ho := ordPt_of_isPt Ω c e ψ o₁ hd S A F hF σ g hσc r' hr'
  have hη : ∀ g, F.η (toGS Ω _ g) = UnitaryThreeInertia.eta4 Ω g := fun g => by rw [← hF.η, hF.π]; rfl
  have hm : ∀ s, (r (toGS Ω _ s)).right = UnitaryThreeInertia.eta4 Ω s := fun s => (hmu _).trans (hη s)
  have hle : ∀ s ∈ (UnitaryThreeInertia.eta4 Ω).ker, (UnitaryThreeInertia.push B.val (r'.comp (toGS Ω _)) s).left =
      tor _ t * (r (toGS Ω _ s)).left * (tor _ t)⁻¹ := fun s hs => by
    rw [← conj_left r _ _ ((hm s).trans hs), ← ht]
    rfl
  have hrg := (UnitaryThreeInertia.gaussian_field_range_eq_ker_quartic_char.2 Ω K hK).1
  have hker : ∀ s : G K Ω, Base.galEmb ℚ K Ω s ∈ (UnitaryThreeInertia.eta4 Ω).ker := fun s => by
    rw [← hrg]
    exact ⟨s, rfl⟩
  let j : G K Ω →* (UnitaryThreeInertia.eta4 Ω).ker := (Base.galEmb ℚ K Ω).codRestrict _ hker
  let ρ' : G K Ω →* GL (Fin 3) (Qbar l) :=
    (glPart (UnitaryThreeInertia.eta4 Ω) (UnitaryThreeInertia.push B.val (r'.comp (toGS Ω _))) ho.red.mult).comp j
  have hiso : Af.RepIso ρ ρ' := ⟨tor _ t, fun s => by
    rw [show ρ s = (r (toGS Ω _ (Base.galEmb ℚ K Ω s))).left from Units.ext (hρ s)]
    exact hle _ (hker s)⟩
  have hAut' := autCsd_iso (tw_iso _ hiso) hAut
  have he := hd.e_pos
  have hfree : Th.FreeAt l ρ' :=
    Z.J.freeCU hH K Ω l hd.l_odd ι 3 (by decide) ρ' (-1) N _ (Af.continuous_of_iso hρc hiso) hAut' NeZero.one_le (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega) (unl_iso hunl hiso)
  rw [zpow_neg_one] at hAut'
  have key := Th.rigEnd3 hH hL Ω l ι c N e ψ (UnitaryThreeInertia.eta4 Ω) σ g (A F.vl) _ hk hΨ hfr B _ ho
    (fun V hV hVη => matIrr_conj (tor _ t) (fun s hs => by
      rw [mats, GG.mat, GG.mat, hle s (hVη hs), ← Units.val_mul, ← Units.val_mul]
      congr 1
      group) (hB.opens V hV hVη)) K hK.1 (by rw [← Base.range_galEmb]; exact hrg.symm) ρ' (fun s => rfl) hAut' hfree
  refine h1f_vanishing_conj_invariant _ (tor _ t) ?_
  have e1 : conjBy (tor _ t) (r.comp (toGS Ω _)) = UnitaryThreeInertia.push B.val (r'.comp (toGS Ω _)) :=
    MonoidHom.ext fun s => (DFunLike.congr_fun ht (toGS Ω _ s)).symm
  rwa [e1]

end Glob

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th UpperTheory.V.Z.J
open Matrix UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.V.Z.J.hostRigidUE :
    Af.HypothesesH → Th.AdL → UnlEndLogNorm → UnitaryThreeInertia.HostRigid := by
  intro hH hL hU K _ _ _ hK Ω _ _ _ l _ c N _ e ψ o₁ hD S A F hF ι g₁ hg r hr hB y r' hyc hy hd hN ⟨h, hh⟩ hSb
  have hN' := hH.litN
  have hP : Loc.LocalPublishedTheorems :=
    ⟨hN'.coh.lfK, hN'.coh.ltK, hN'.coh.leK, hN'.coh.lf, hN'.coh.lt, hN'.coh.le, hN'.coh.bk⟩
  have ok := hostFrame_ok Ω c e ψ o₁ hD S A F hF
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI hcl := isClosed_NS Ω (S : Set Pl)
  haveI : TotallyDisconnectedSpace (Gam Ω S) := totDisc_quot _ hcl
  obtain ⟨hm, -, hc, -⟩ := isCharZeroPt_basic F ok g₁ hg r hr
  have hz := selmer_h1_vanishes_at_rigid_point hH hL hU K hK Ω l c N e ψ o₁ hD S A F hF ι g₁ hg r hr hm hc hB
  have hZ : (fun s => y (F.π s)) ∈ Z1 (adRep (r.comp F.π)) := ⟨hyc.comp ok.π_cont, fun g k => by
    simp only [map_mul]
    exact hy _ _⟩
  have hsurj : Function.Surjective F.π := by
    rw [hF.π]
    exact QuotientGroup.mk_surjective
  have hb := hz _ hZ ⟨fun w hw => ?_, fun τ => ?_⟩
  · obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hb
    refine ⟨-m, fun g => ?_⟩
    obtain ⟨s, rfl⟩ := hsurj g
    rw [hm s, cob, map_neg, neg_sub_neg]
    rfl
  · by_cases hS : w ∈ S
    · refine ⟨A ⟨w, hS⟩, hF.isOver _, ?_⟩
      rw [← hF.I]
      exact rig_away F ok r hm y r' hy hd hN hSb ⟨w, hS⟩ fun h => hw (by
        have := hF.vl
        rwa [← h] at this)
    · obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w
      refine ⟨B, hB, 0, fun s hs => ?_⟩
      have h1 : F.π s = 1 := by
        rw [hF.π]
        refine (QuotientGroup.eq_one_iff s).2 ?_
        refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
        simp only [Set.mem_iUnion]
        exact ⟨w, hS, B, hB, hs⟩
      have h2 := hy 1 1
      rw [mul_one, map_one, Module.End.one_apply, left_eq_add] at h2
      simp only [h1, h2, map_zero, sub_zero]
  · obtain ⟨j, hj⟩ := (Loc.decEmb (F := ℚ) (Ω := Ω) (v := l)).1 _ _ (hF.isOver F.vl) hF.vl
    refine ⟨j, Subsingleton.elim _ _, ?_⟩
    obtain ⟨φ, h1, h2, h3, h4⟩ : ∃ φ : F.D F.vl →* Formalism.BasicNotions.Loc.GQ l, Topology.IsOpenEmbedding φ ∧
        (∀ g x, φ g (j x) = j ((g : G ℚ Ω) x)) ∧ (∀ g, φ g ∈ Loc.Iq l → (g : G ℚ Ω) ∈ F.I F.vl) ∧
        ∀ g, Loc.cyc l l (φ g) = cycZ ℚ Ω l (g : G ℚ Ω) := by
      rw [hF.D, hF.I, ← hj]
      obtain ⟨-, φ, a1, a2, -, a3, a4, -⟩ := (Loc.decEmb (F := ℚ) (Ω := Ω) (v := l)).2 j
      exact ⟨φ, a1, a2, fun g => (a3 g).1, a4 l⟩
    exact (Loc.bkAbove j φ (F.D F.vl).subtype h1 h2 _ _ hZ).1
      (rig_above hP Ω c e ψ o₁ hD S A F hF g₁ r hr hm hc y r' hyc hy hd h hh φ h1 h3 h4)
