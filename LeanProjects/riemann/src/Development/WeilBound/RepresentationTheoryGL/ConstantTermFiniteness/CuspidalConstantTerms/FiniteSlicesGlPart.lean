import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfIsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbNormalises
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactBlockLeviSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormBlockEmbLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfIsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KinfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspBlockConstantTermVanishing
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.IsCuspidalCompBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecInv
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.EnvRepAllInjective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMaxCompactRealPointsOfOrthonormalFramesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieOneParameterIsRealOneParamSubgroupAdelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameFamilyCompactRepresentation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantOfLieOneLEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CofiniteOfCapelliMonicStatement
import Development.WeilBound.HeckeVectors.SmoothVectors.ContinuousUnits.LocInCompT
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsBlockPointStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnitaryAdelicUnipotentLiftStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerEndMemLeftInv
import GroundTheory.PAdicHodge.NormalizedTrace

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.CoreGL.Rg

open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

theorem exists_block {m : ℕ} (T : Finset (Fin m)) (k : Fin m) (hk : k ∈ T) :
    ∃ l d : ℕ, ∃ h : l + d ≤ m, 1 ≤ d ∧ k.val + 1 = l + d ∧ (∀ j : Fin m, l ≤ j.val → j.val + 1 < l + d → j ∉ T) ∧
      (l = 0 ∨ ∃ p ∈ T, p.val + 1 = l) := by
  classical
  by_cases hs : (T.filter (· < k)).Nonempty
  · set p := (T.filter (· < k)).max' hs with hp
    have hpm := Finset.mem_filter.1 ((T.filter (· < k)).max'_mem hs)
    have hpk : p.val < k.val := hpm.2
    refine ⟨p.val + 1, k.val - p.val, by have := k.2; omega, by omega, by omega, fun j h1 h2 hj => ?_, Or.inr ⟨p, hpm.1, rfl⟩⟩
    have hjk : j < k := by rw [Fin.lt_def]; omega
    have := (T.filter (· < k)).le_max' j (Finset.mem_filter.2 ⟨hj, hjk⟩)
    rw [← hp, Fin.le_def] at this
    omega
  · refine ⟨0, k.val + 1, by have := k.2; omega, by omega, by omega, fun j _ h2 hj => hs ⟨j, Finset.mem_filter.2 ⟨hj, ?_⟩⟩, Or.inl rfl⟩
    rw [Fin.lt_def]; omega

theorem levi_keeps {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} {T : Finset (Fin r)} {m : GAd σ J}
    (hm : m ∈ levi σ J X Y T) (k : Fin r) (hk : k ∈ T) (y : Fin n → AF F ⊗[F] E) :
    y ∈ colSpan F X {i | i ≤ k} ↔ (matHom _ σ J m).1 *ᵥ y ∈ colSpan F X {i | i ≤ k} := by
  have fwd : ∀ m ∈ levi σ J X Y T, ∀ y, y ∈ colSpan F X {i | i ≤ k} → (matHom _ σ J m).1 *ᵥ y ∈ colSpan F X {i | i ≤ k} := by
    intro m hm y hy
    have h1 := (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hm k) hk).1
    obtain ⟨B, -, e⟩ := h1
    obtain ⟨a, rfl⟩ := mem_colSpan_iff.1 hy
    refine mem_colSpan_iff.2 ⟨B.1 *ᵥ a, ?_⟩
    rw [mulVec_mulVec, mulVec_mulVec, e]
  refine ⟨fwd m hm y, fun h => ?_⟩
  have := fwd m⁻¹ (inv_mem hm) _ h
  rwa [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec] at this

section Rep

variable {G K : Type} [Group G] [Group K]

def repOf (S : Submodule ℂ (K → ℂ)) (hS : ∀ f ∈ S, ∀ k, (fun x => f (x * k)) ∈ S) (α : G →* K) : Representation ℂ G S where
  toFun g :=
    { toFun := fun f => ⟨fun x => f.1 (x * α g), hS f.1 f.2 _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext f x
    simp
  map_mul' a b := by
    ext f x
    simp [mul_assoc]

theorem coeff_repOf (S : Submodule ℂ (K → ℂ)) (hS : ∀ f ∈ S, ∀ k, (fun x => f (x * k)) ∈ S) (α : G →* K) {s : K → ℂ}
    (hs : s ∈ S) : (fun g => s (α g)) ∈ GlobalTheory.Published.AutFin.coeffSpan (repOf S hS α) :=
  Submodule.subset_span ⟨(LinearMap.proj (1 : K)).comp S.subtype, ⟨s, hs⟩, funext fun g => by
    change s (α g) = s (1 * α g)
    rw [one_mul]⟩

theorem isContRep_repOf [TopologicalSpace G] [TopologicalSpace K] [ContinuousMul K] (S : Submodule ℂ (K → ℂ))
    [FiniteDimensional ℂ S] (hS : ∀ f ∈ S, ∀ k, (fun x => f (x * k)) ∈ S) (hc : ∀ f ∈ S, Continuous f) (α : G →* K)
    (hα : Continuous α) : IsContRep (repOf S hS α) := by
  classical
  intro ℓ w
  obtain ⟨P, hP⟩ := exists_finset_sep S
  let ev : S →ₗ[ℂ] (P → ℂ) :=
    { toFun := fun f p => f.1 p.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : LinearMap.ker ev = ⊥ := LinearMap.ker_eq_bot.2 ((injective_iff_map_eq_zero ev).2 fun f hf => Subtype.ext
    (hP f.1 f.2 fun x hx => congrFun hf ⟨x, hx⟩))
  obtain ⟨Lf, hL⟩ := LinearMap.exists_leftInverse_of_injective ev hinj
  have e : ∀ f : S, ℓ f = ∑ p : P, ℓ (Lf (Pi.single p 1)) * f.1 p.1 := fun f => by
    have h1 : f = Lf (ev f) := (LinearMap.congr_fun hL f).symm
    have h2 : ev f = ∑ p : P, f.1 p.1 • (Pi.single p 1 : P → ℂ) := by
      funext p
      simp [ev, Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [h1, h2, map_sum, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, map_smul, smul_eq_mul, mul_comm]
  have : (fun g => ℓ (repOf S hS α g w)) = fun g => ∑ p : P, ℓ (Lf (Pi.single p 1)) * w.1 (p.1 * α g) := by
    funext g
    rw [e]
    rfl
  rw [this]
  exact continuous_finset_sum _ fun p _ => continuous_const.mul
    ((hc w.1 w.2).comp (continuous_const.mul hα))

theorem kfin_of_space {S : Submodule ℂ (K → ℂ)} [FiniteDimensional ℂ S] {H : Type} [Mul H] {i : K → H} {φ : H → ℂ}
    (h : ∀ g, (fun k => φ (g * i k)) ∈ S) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun g => φ (g * i k))) := by
  let B := Module.finBasis ℂ S
  let c : Fin (Module.finrank ℂ S) → H → ℂ := fun a g => B.repr ⟨_, h g⟩ a
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range c)) := FiniteDimensional.span_of_finite ℂ (Set.finite_range c)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range c)) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  have e : (fun g => φ (g * i k)) = ∑ a, (B a).1 k • c a := by
    funext g
    have h1 := congrFun (congrArg Subtype.val (B.sum_repr ⟨_, h g⟩)) k
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← h1]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  change (fun g => φ (g * i k)) ∈ _
  rw [e]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end Rep

section Centre

open PositivityTheory.Affgl GlobalTheory.CuspRep

theorem zfin_of_cofin {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {J : Set (Module.End ℂ (Sm E a))}
    (hJ : Cofin J) {f : Sm E a} (hf : ∀ z ∈ J, z f = 0) :
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z f) '' Zalg E a)) := by
  obtain ⟨-, V, hV, h⟩ := hJ
  let ev : Module.End ℂ (Sm E a) →ₗ[ℂ] Sm E a := LinearMap.applyₗ f
  have key : ∀ w ∈ Submodule.span ℂ {y | ∃ x ∈ Zalg E a, ∃ j ∈ J, y = x * j}, w f = 0 := fun w hw => by
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, -, j, hj, rfl⟩ := hx
      rw [Module.End.mul_apply, hf j hj, map_zero]
    | zero => rfl
    | add x y _ _ hx hy => rw [LinearMap.add_apply, hx, hy, add_zero]
    | smul a x _ hx => rw [LinearMap.smul_apply, hx, smul_zero]
  refine Submodule.finiteDimensional_of_le (S₂ := V.map ev) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨v, hv, w, hw, e⟩ := Submodule.mem_sup.1 (h z hz)
  refine ⟨v, hv, ?_⟩
  change v f = z f
  rw [← e, LinearMap.add_apply, key w hw, add_zero]

end Centre

section Gelf

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem zfin_of_gelf (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hs : IsSm D.sp.cm.sig V.gram φ) {c : D.what₂.Tau → ℕ → ℂ}
    (hg : ∀ τ k, gelf θ V τ k φ = c τ k • φ) :
    FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z, IsCentral D.sp.cm.sig V.gram z ∧ f = dop z φ}) := by
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  have hW : ∀ τ k, ∀ f ∈ Submodule.span ℂ {φ}, gelf θ V τ k f ∈ Submodule.span ℂ {φ} := by
    intro τ k f hf
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hf
    rw [(GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) τ k).smul, hg, smul_comm]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ}) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨u, hu, e⟩ := GlobalTheory.CentralOps.Rg.exists_center hθ R hz
  let ψ : GlobalTheory.SmoothForms.SmF θ V := ⟨φ, (GlobalTheory.SmoothForms.smooth_iff R φ).1 fun k τs Xs hX g =>
    hs k (fun i => oneP θ V (τs i) (Xs i)) (fun i => GlobalTheory.T.unitary_lie_one_parameter_isRealOneParamSubgroupAdelic D θ hθ V _ _ (hX i)) g⟩
  exact (e ψ).symm ▸ GlobalTheory.CentralOps.mem_of_mem_center R hW hu ψ (Submodule.mem_span_singleton_self φ)

end Gelf

section Main

open GlobalTheory.CuspRep in

theorem finite_slices_glPart : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), (∀ τ, IsContRep (ρ τ)) → ∀ (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), T.Nonempty → ∀ k ∈ T, ∀ b : GA D V, FiniteDimensional ℂ (Submodule.span ℂ (sliceSet (cuspOn θ V X Y T U ε fr ρ c) (glPart D.sp.cm.sig V.gram X Y T k) (levi D.sp.cm.sig V.gram X Y T) b)) := by
  intro D θ hθ V U hU ε fr hfr W _ _ _ ρ hρ c m X Y hW T hT k hk b
  classical
  have hcm := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm).1
  have hJ := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm).2 V
  haveI := GlobalTheory.CuspRep.host_isCMField D.host
  haveI : IsTotallyComplex D.host.E := inferInstance
  obtain ⟨l, d, hl, hd, hkl, hblk, hprev⟩ := exists_block T k hk
  have hend : ∃ k' ∈ T, k'.val + 1 = l + d := ⟨k, hk, hkl⟩
  obtain ⟨ι, hι⟩ := GlobalTheory.BlockFormsEmb.exists_blockEmb _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW l d hl
  have hrange := GlobalTheory.T.block_embedding_parabolic_compatibility _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW T k hk l d hl ι hι hkl hd hblk hprev
  have hιH : ∀ x, ι x ∈ glPart D.sp.cm.sig V.gram X Y T k := fun x => hrange ▸ ⟨x, rfl⟩
  obtain ⟨K, hKm, j, hjs, hj⟩ := GlobalTheory.T.exists_maxCompact_realPoints_of_orthonormalFrames D θ hθ V ε fr hfr
  have hK : IsMaxCpt D.sp.cm.sig V.gram K :=
    ⟨⟨fun x hx => hKm.1 x hx, hKm.2.1⟩, fun K' hK' hle => (hKm.2.2 K' (fun x hx => hK'.1 hx) hK'.2 hle).le⟩
  obtain ⟨u, hu, -, y₁, g₀, hb, hg₀⟩ := GlobalTheory.T.parabolic_block_embedding_compact _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW K hK T l d hl ι hι hd hblk hend hprev b
  obtain ⟨S, hSf, hSc, hSt, hSφ⟩ := GlobalTheory.typesFiniteSpace D θ hθ V ε fr hfr K ⟨j, hjs, hj⟩ W ρ
  haveI := hSf
  let α : Kinf D.host.E d →* K :=
    { toFun := fun κ => ⟨g₀⁻¹ * ι (infGL D.host.E d (Unitary.toUnits κ)) * g₀, hg₀ κ⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hιc := GlobalTheory.BlockLevel.continuous_of_isBlockEmb hι
  have hα : Continuous α := Continuous.subtype_mk
    ((continuous_const.mul (hιc.comp CompanionTheory.D.gk.Br.LIC.continuous_infGL_toUnits)).mul continuous_const) _
  let ρ' := repOf S hSt α
  have hρ' : IsContRep ρ' := isContRep_repOf S hSt hSc α hα
  let L : Subgroup (GL (Fin d) (GlobalTheory.CuspRep.Af D.host.E)) :=
    U.comap ((MulAut.conj g₀⁻¹).toMonoidHom.comp (ι.comp (finGL D.host.E d)))
  have hL : IsOpen (L : Set (GL (Fin d) (GlobalTheory.CuspRep.Af D.host.E))) := by
    refine hU.preimage ?_
    have : Continuous fun k : GL (Fin d) (GlobalTheory.CuspRep.Af D.host.E) => g₀⁻¹ * ι (finGL D.host.E d k) * g₀⁻¹⁻¹ :=
      (continuous_const.mul (hιc.comp CompanionTheory.D.gk.Br.LIC.continuous_finGL)).mul continuous_const
    exact this
  choose q hq hq0 using GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.MonicBlock.monic_block D θ hθ V c m X Y hW T l d hl ι hι hd hblk hend hprev
  let Js : Set (Module.End ℂ (Sm D.host.E d)) :=
    Set.range fun p : (D.host.E →+* ℂ) × ℂ => Polynomial.aeval (cap (a := d) p.1 p.2) (q p.1 p.2)
  have hJs : Js ⊆ Zalg D.host.E d := by
    rintro _ ⟨p, rfl⟩
    have h : cap (a := d) p.1 p.2 ∈ Zalg D.host.E d := Algebra.subset_adjoin ⟨p.1, p.2, rfl⟩
    change Polynomial.aeval _ _ ∈ Zalg D.host.E d
    rw [Polynomial.aeval_eq_sum_range]
    exact Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (pow_mem h i) _
  have hCof := GlobalTheory.T.cofinite_of_capelli_monic D.host.E d Js hJs fun τ v => ⟨q τ v, hq τ v, ⟨(τ, v), rfl⟩⟩
  have hfin := GlobalTheory.CompanionTheory.CuspFinGL.Split.cuspFin D.host.E d L hL S ρ' hρ' Js hCof
  have hnorm : (finPts D.sp.cm.sig V.gram).Normal := by
    unfold finPts
    infer_instance
  have key : ∀ φ ∈ cuspOn θ V X Y T U ε fr ρ c, ∀ y : GA D V,
      (∀ t ∈ glPart D.sp.cm.sig V.gram X Y T k, t * y = y * t) →
      ∃ F : Sm D.host.E d, (∀ x, F.1 x = φ (ι x * (y * g₀))) ∧
        F ∈ {F | F ∈ PositivityTheory.Affgl.genSpace L ρ' Js ∧ IsCuspidal F.1} := by
    intro φ hφ y hy
    obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := hφ
    have hc : GlobalTheory.StdPar.IsCuspOn D.sp.cm.sig V.gram X Y T K φ :=
      ⟨⟨fun u hu g => h1.left u (Subgroup.mem_sup_left hu) g,
        fun γ a b g => h1.left γ (Subgroup.mem_sup_right ⟨a, b⟩) g, h1.level, h1.cont, h1.smooth, h1.growth,
        kfin_of_space (S := S) (i := Subtype.val) (hSφ φ h1.cont h3), zfin_of_gelf hθ h1.smooth h4⟩, h5⟩
    have hcj : ∀ x, (y * g₀)⁻¹ * ι x * (y * g₀) = g₀⁻¹ * ι x * g₀ := fun x => by
      have e := hy (ι x) (hιH x)
      calc (y * g₀)⁻¹ * ι x * (y * g₀) = g₀⁻¹ * y⁻¹ * (ι x * y) * g₀ := by group
        _ = g₀⁻¹ * ι x * g₀ := by rw [e]; group
    have hg₁ : ∀ κ : Kinf D.host.E d, (y * g₀)⁻¹ * ι (infGL D.host.E d (Unitary.toUnits κ)) * (y * g₀) ∈ K := fun κ => by
      rw [hcj]; exact hg₀ κ
    have hmv : ∀ x a, ι (x * a) * (y * g₀) = ι x * (y * g₀) * (g₀⁻¹ * ι a * g₀) := fun x a => by
      rw [← hcj, map_mul]; group
    let F : Sm D.host.E d := ⟨fun x => φ (ι x * (y * g₀)), GlobalTheory.CuspSmooth.mem_Sm_blockEmb _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW K hK T l d hl ι hι hd hblk hend hprev φ hc _ hg₁⟩
    have hkill : ∀ z ∈ Js, z F = 0 := by
      rintro _ ⟨p, rfl⟩
      exact hq0 p.1 p.2 φ h1 h4 _ F fun _ => rfl
    have hlev : ∀ a ∈ L, finRep D.host.E d a F = F := by
      intro a ha
      refine Subtype.ext (funext fun x => ?_)
      change φ (ι (x * finGL D.host.E d a) * (y * g₀)) = φ (ι x * (y * g₀))
      have hU' : g₀⁻¹ * ι (finGL D.host.E d a) * g₀ ∈ U := by simpa [L, MulAut.conj_apply] using ha
      have hf' : g₀⁻¹ * ι (finGL D.host.E d a) * g₀ ∈ finPts D.sp.cm.sig V.gram := by
        simpa using hnorm.conj_mem _ (GlobalTheory.BlockLevel.finGL_mem_finPts hι a) g₀⁻¹
      rw [hmv]
      exact h2 _ hU' hf' _
    have hcoef : ∀ g : GlobalTheory.CuspRep.GA D.host.E d, (fun κ : Kinf D.host.E d => (cptRep D.host.E d κ F).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ' := by
      intro g
      have e : (fun κ : Kinf D.host.E d => (cptRep D.host.E d κ F).1 g) =
          fun κ => (fun k : K => φ (ι g * (y * g₀) * k)) (α κ) := funext fun κ => by
        change φ (ι (g * infGL D.host.E d (Unitary.toUnits κ)) * (y * g₀)) = _
        rw [hmv]
        rfl
      rw [e]
      exact coeff_repOf S hSt α (hSφ φ h1.cont h3 _)
    have haut : IsAutForm F := by
      refine ⟨GlobalTheory.CuspBlockLeft.cuspForm_blockEmb_left_invariant _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW K hK T l d hl ι hι hd hblk hend hprev φ hc _ hg₁, ?_, ?_, zfin_of_cofin hCof hkill, GlobalTheory.BlockForms.growth_comp_blockEmb _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW K hK T l d hl ι hι hd hblk hend hprev φ hc _ hg₁⟩
      · have e : {a | finRep D.host.E d a F = F} = {a : GL (Fin d) (GlobalTheory.CuspRep.Af D.host.E) | ∀ g, φ (ι (g * finGL D.host.E d a) * (y * g₀)) = φ (ι g * (y * g₀))} :=
          Set.ext fun a => ⟨fun e g => congrFun (congrArg Subtype.val e) g, fun e => Subtype.ext (funext e)⟩
        rw [e]
        exact GlobalTheory.BlockLevel.isOpen_rightInv_finGL _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW K hK T l d hl ι hι hd hblk hend hprev φ hc _ hg₁
      · have e : (Submodule.span ℂ (Set.range fun a => cptRep D.host.E d a F)).map (Sm D.host.E d).subtype =
            Submodule.span ℂ (Set.range fun a : Kinf D.host.E d => fun g : GlobalTheory.CuspRep.GA D.host.E d => φ (ι (g * infGL D.host.E d (Unitary.toUnits a)) * (y * g₀))) := by
          rw [Submodule.map_span, ← Set.range_comp]
          rfl
        have := GlobalTheory.CuspKinfFin.kinf_finite _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW K hK T l d hl ι hι hd hblk hend hprev φ hc _ hg₁
        rw [← e] at this
        exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective (Sm D.host.E d).subtype Subtype.val_injective
          (Submodule.span ℂ (Set.range fun a => cptRep D.host.E d a F))).symm
    exact ⟨F, fun _ => rfl, ⟨haut, hlev, hcoef, hkill⟩,
      GlobalTheory.BlockForms.CuspConst.Rg.isCuspidal_comp_blockEmb _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW K hK T l d hl ι hι hd hblk hend hprev φ hc _ hg₁⟩
  have hmem : ∀ t : glPart D.sp.cm.sig V.gram X Y T k, t.1 ∈ ι.range := fun t => hrange ▸ t.2
  let pre : glPart D.sp.cm.sig V.gram X Y T k → GlobalTheory.CuspRep.GA D.host.E d := fun t => Classical.choose (hmem t)
  have hpre : ∀ t, ι (pre t) = t.1 := fun t => Classical.choose_spec (hmem t)
  let Λ : Sm D.host.E d →ₗ[ℂ] (glPart D.sp.cm.sig V.gram X Y T k → ℂ) :=
    { toFun := fun F t => F.1 (pre t * infGL D.host.E d y₁)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI := hfin
  refine Submodule.finiteDimensional_of_le
    (S₂ := (Submodule.span ℂ {F | F ∈ PositivityTheory.Affgl.genSpace L ρ' Js ∧ IsCuspidal F.1}).map Λ) (Submodule.span_le.2 ?_)
  rintro f ⟨φ, hφ, y, hy, hyc, rfl⟩
  obtain ⟨F, hF, hFm⟩ := key φ hφ y hyc
  refine ⟨F, Submodule.subset_span hFm, funext fun t => ?_⟩
  change F.1 (pre t * infGL D.host.E d y₁) = φ (t.1 * y * b)
  rw [hF, map_mul, hpre, hb]
  have hy1 := hyc _ (hιH (infGL D.host.E d y₁))
  have hty : t.1 * y ∈ levi D.sp.cm.sig V.gram X Y T := mul_mem t.2.1 hy
  have hu' := GlobalTheory.FlagNorm.conj_mem_unip _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW T (t.1 * y)
    (fun k' hk' v => levi_keeps hty k' hk' v) u hu
  have e1 : t.1 * ι (infGL D.host.E d y₁) * (y * g₀) = t.1 * y * ι (infGL D.host.E d y₁) * g₀ := by
    rw [mul_assoc t.1, ← mul_assoc (ι _), hy1]
    simp only [mul_assoc]
  have e2 : t.1 * y * (u * ι (infGL D.host.E d y₁) * g₀) =
      (t.1 * y * u * (t.1 * y)⁻¹) * (t.1 * ι (infGL D.host.E d y₁) * (y * g₀)) := by
    rw [e1]; group
  rw [e2]
  exact (hφ.1.1.left _ (Subgroup.mem_sup_left hu') _).symm

end Main

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.CoreGL.Rg
