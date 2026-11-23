import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsStableSquareIntegrableForms
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableLevelDecomposition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import GroundTheory.PAdicHodge.NormalizedTrace

noncomputable section

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CapOrth
  GlobalTheory.LevelTypeProj GlobalTheory.PRep GlobalTheory.CuspRep.LocEx

namespace PositivityTheory.Rg.Rs.PrAdm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

def annZ (ψ : Sm E N) : Set (Module.End ℂ (Sm E N)) := {z | z ∈ Zalg E N ∧ z ψ = 0}

theorem cofin_annZ {ψ : Sm E N} (hψ : IsAutForm ψ) : PositivityTheory.Affgl.Cofin (annZ ψ) := by
  refine ⟨fun z hz => hz.1, ?_⟩
  let Z : Submodule ℂ (Module.End ℂ (Sm E N)) := Subalgebra.toSubmodule (Zalg E N)
  let ev : Module.End ℂ (Sm E N) →ₗ[ℂ] Sm E N := LinearMap.applyₗ ψ
  let M := Z.map ev
  have : FiniteDimensional ℂ M := by
    have := hψ.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E N) => z ψ) '' Zalg E N)) ?_
    rintro _ ⟨z, hz, rfl⟩
    exact Submodule.subset_span ⟨z, hz, rfl⟩
  let f : Z →ₗ[ℂ] M := (ev.comp Z.subtype).codRestrict M (fun z => ⟨z.1, z.2, rfl⟩)
  have hf : LinearMap.range f = ⊤ := LinearMap.range_eq_top.2 (by
    rintro ⟨_, z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩)
  obtain ⟨g, hg⟩ := f.exists_rightInverse_of_surjective hf
  refine ⟨(LinearMap.range g).map Z.subtype, inferInstance, fun z hz => ?_⟩
  let zz : Z := ⟨z, hz⟩
  set v : Z := g (f zz) with hv
  have hfg : f v = f zz := LinearMap.congr_fun hg (f zz)
  have hk : (z - v.1) ψ = 0 := by
    have := congrArg Subtype.val hfg
    change v.1 ψ = z ψ at this
    rw [LinearMap.sub_apply, this, sub_self]
  have hmem : z - v.1 ∈ annZ ψ := ⟨(Zalg E N).sub_mem hz v.2, hk⟩
  refine Submodule.mem_sup.2 ⟨v.1, ⟨v, ⟨f zz, hv.symm⟩, rfl⟩, 1 * (z - v.1),
    Submodule.subset_span ⟨1, (Zalg E N).one_mem, z - v.1, hmem, rfl⟩, by rw [one_mul, add_sub_cancel]⟩

theorem zalg_comm_act {z : Module.End ℂ (Sm E N)} (hz : z ∈ Zalg E N) (o : Op E N) : z * act o = act o * z := by
  cases o with
  | fin k => exact GlobalTheory.CuspStab.zalg_comm_fin k hz
  | cpt k => exact GlobalTheory.ZalgCpt.zalg_comm_cptRep E N k z hz
  | lie X => exact GlobalTheory.CuspRep.Zalg_mul_lie E N X z hz

def SupSpansPsiPart (W : Submodule ℂ (Sm E N)) (ψ : Sm E N) : Submodule ℂ (Sm E N) where
  carrier := {φ | φ ∈ W ∧ ∀ z ∈ annZ ψ, z φ = 0}
  add_mem' := fun {φ φ'} h h' => ⟨W.add_mem h.1 h'.1, fun z hz => by rw [map_add, h.2 z hz, h'.2 z hz, add_zero]⟩
  zero_mem' := ⟨W.zero_mem, fun z _ => map_zero z⟩
  smul_mem' := fun c φ h => ⟨W.smul_mem c h.1, fun z hz => by rw [map_smul, h.2 z hz, smul_zero]⟩

theorem admissible_span_le (W : Submodule ℂ (Sm E N)) (ψ : Sm E N) : SupSpansPsiPart W ψ ≤ W := fun _ h => h.1

theorem mem_admissible_span_self {W : Submodule ℂ (Sm E N)} {ψ : Sm E N} (h : ψ ∈ W) : ψ ∈ SupSpansPsiPart W ψ := ⟨h, fun _ hz => hz.2⟩

theorem isStable_admissible_span {W : Submodule ℂ (Sm E N)} (hW : IsStable W) (ψ : Sm E N) : IsStable (SupSpansPsiPart W ψ) := by
  intro o φ hφ
  refine ⟨hW o φ hφ.1, fun z hz => ?_⟩
  rw [← Module.End.mul_apply, zalg_comm_act hz.1 o, Module.End.mul_apply, hφ.2 z hz, map_zero]

theorem finiteDimensional_admissible_isotypic {W : Submodule ℂ (Sm E N)} (hA : ∀ φ ∈ W, IsAutForm φ) {ψ : Sm E N} (hψ : IsAutForm ψ)
    {L : Subgroup (GL (Fin N) (Af E))} (hL : IsOpen (L : Set (GL (Fin N) (Af E)))) {U : Type} [AddCommGroup U]
    [Module ℂ U] [FiniteDimensional ℂ U] (ρ : Representation ℂ (Kinf E N) U) (hρ : GlobalTheory.Published.AutFin.IsContRep ρ) :
    FiniteDimensional ℂ (SupSpansPsiPart W ψ ⊓ typePart L ρ : Submodule ℂ (Sm E N)) := by
  have := PositivityTheory.Rg.HF.GL.genFin E N L hL U ρ hρ (annZ ψ) (cofin_annZ hψ)
  exact Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (PositivityTheory.Affgl.genSpace L ρ (annZ ψ)))
    fun φ hφ => Submodule.subset_span
      (show φ ∈ PositivityTheory.Affgl.genSpace L ρ (annZ ψ) from ⟨hA φ hφ.1.1, hφ.2.1, hφ.2.2, hφ.1.2⟩)

theorem exists_type {χ : Sm E N} (hχ : IsAutForm χ) : ∃ L : Subgroup (GL (Fin N) (Af E)),
    IsOpen (L : Set (GL (Fin N) (Af E))) ∧ IsCompact (L : Set (GL (Fin N) (Af E))) ∧
      χ ∈ typePart L (sub (cptRep E N) (orbSpan χ) (orbSpan_stable χ)) := by
  obtain ⟨U0, hU0o, hU0c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E N
  let L : Subgroup (GL (Fin N) (Af E)) := U0 ⊓ GlobalTheory.DiscClosure.stabSub χ
  have hLo : IsOpen (L : Set (GL (Fin N) (Af E))) := hU0o.inter hχ.level
  refine ⟨L, hLo, hU0c.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hLo) Set.inter_subset_left,
    fun k hk => hk.2, fun g => ?_⟩
  exact GlobalTheory.Published.AutFinGL.type_of_map _ (orbSpan χ).subtype (fun _ _ => rfl)
    ⟨χ, Submodule.subset_span ⟨1, by simp⟩⟩ g

section Proj

variable {μ : Measure (GA E N)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {W : Submodule ℂ (Sm E N)}
  (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1)

theorem exists_orth (hW : IsStable W) (hA : ∀ φ ∈ W, IsAutForm φ) (hinj : ∀ x ∈ W, cls h x = 0 → x = 0)
    {V : Submodule ℂ (Sm E N)} (hV : IsStable V) (hVW : V ≤ W) {χ : Sm E N} (hχ : χ ∈ W)
    {L : Subgroup (GL (Fin N) (Af E))} (hLo : IsOpen (L : Set (GL (Fin N) (Af E))))
    (hLc : IsCompact (L : Set (GL (Fin N) (Af E)))) {U : Type} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    (ρ : Representation ℂ (Kinf E N) U) (hρ : GlobalTheory.Published.AutFin.IsContRep ρ) (hχT : χ ∈ typePart L ρ)
    [FiniteDimensional ℂ (V ⊓ typePart L ρ : Submodule ℂ (Sm E N))] :
    ∃ v ∈ V ⊓ typePart L ρ, ∀ w ∈ V, inner ℂ (cls h (χ - v)) (cls h w) = 0 := by
  have hF : Function.Injective (toL2ₗ μ W h) := (injective_iff_map_eq_zero _).2 fun x e =>
    Subtype.ext (hinj x.1 x.2 (by rw [cls_mk h x.2]; exact e))
  obtain ⟨p, hpS, hp⟩ := exists_proj h hF (V ⊓ typePart L ρ) (inf_le_left.trans hVW)
  let χW : W := ⟨χ, hχ⟩
  refine ⟨(p χW).1, hpS χW, fun w hw => ?_⟩
  obtain ⟨w', hw'V, hw'L, hw'T, hinner⟩ :=
    exists_levelType_part E N μ W V h hW hA hV hVW L hLo hLc U ρ hρ ⟨w, hVW hw⟩ hw
  have hdT : (χW - p χW).1 ∈ typePart L ρ := sub_mem hχT (hpS χW).2
  have e := hinner (χW - p χW) hdT.1 hdT.2
  rw [cls_sub h hχ (p χW).2, cls_mk h hχ, cls_mk h (p χW).2, cls_mk h (hVW hw)]
  change inner ℂ (toL2ₗ μ W h χW - toL2ₗ μ W h (p χW)) (toL2ₗ μ W h ⟨w, hVW hw⟩) = 0
  rw [← map_sub, e, map_sub]
  exact hp χW w' ⟨hw'V, hw'L, hw'T⟩

omit [μ.IsHaarMeasure] [μ.IsMulRightInvariant] in

theorem orth_unique (hinj : ∀ x ∈ W, cls h x = 0 → x = 0) {V : Submodule ℂ (Sm E N)} (hVW : V ≤ W)
    {χ v v' : Sm E N} (hχ : χ ∈ W) (hv : v ∈ V) (hv' : v' ∈ V)
    (h1 : ∀ w ∈ V, inner ℂ (cls h (χ - v)) (cls h w) = 0) (h2 : ∀ w ∈ V, inner ℂ (cls h (χ - v')) (cls h w) = 0) :
    v = v' := by
  have hm : v' - v ∈ V := V.sub_mem hv' hv
  have e : cls h (v' - v) = cls h (χ - v) - cls h (χ - v') := by
    rw [cls_sub h (hVW hv') (hVW hv), cls_sub h hχ (hVW hv), cls_sub h hχ (hVW hv')]
    abel
  have h0 : inner ℂ (cls h (v' - v)) (cls h (v' - v)) = 0 := by
    rw [e, inner_sub_left, ← e, h1 _ hm, h2 _ hm, sub_zero]
  exact (sub_eq_zero.1 (hinj _ (hVW hm) (inner_self_eq_zero.1 h0))).symm

end Proj

end PositivityTheory.Rg.Rs.PrAdm

end
