import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValQOfValQr
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLocalGroupsNormalFramesSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalInvariantIntegralsSymmetricHaarSubgroupsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqIntegralFactorQuotient
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceCmHostAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentAnisotropicProjectionEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.QRed

section Abstract
variable {A B P : Type} [Group A] [TopologicalSpace A] [Group B] [TopologicalSpace B] [Group P] [TopologicalSpace P]

def resEquiv (e : (A × B) ≃ₜ* P) {RA : Subgroup A} {RB : Subgroup B} {RP : Subgroup P}
    (h : ∀ a b, e (a, b) ∈ RP ↔ a ∈ RA ∧ b ∈ RB) : (RA × RB) ≃ₜ* RP where
  toFun p := ⟨e (p.1.1, p.2.1), (h _ _).2 ⟨p.1.2, p.2.2⟩⟩
  invFun g := (⟨(e.symm g.1).1, ((h _ (e.symm g.1).2).1 (by simp)).1⟩, ⟨(e.symm g.1).2, ((h (e.symm g.1).1 _).1 (by simp)).2⟩)
  left_inv p := by ext <;> simp
  right_inv g := by ext : 1; simp
  map_mul' p q := by ext : 1; exact map_mul e (p.1.1, p.2.1) (q.1.1, q.2.1)
  continuous_toFun := by
    refine Continuous.subtype_mk (e.continuous.comp ?_) _
    exact (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (Continuous.subtype_mk ?_ _)
    · exact continuous_fst.comp (e.symm.continuous.comp continuous_subtype_val)
    · exact continuous_snd.comp (e.symm.continuous.comp continuous_subtype_val)

variable [IsTopologicalGroup A] [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
  [IsTopologicalGroup B] [LocallyCompactSpace B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
  [IsTopologicalGroup P] [MeasurableSpace P] [BorelSpace P]

theorem exists_prod (e : (A × B) ≃ₜ* P) (μ : Measure P) (m : Measure B) [μ.IsHaarMeasure] [m.IsHaarMeasure] :
    ∃ μ' : Measure A, μ'.IsHaarMeasure ∧ μ = (μ'.prod m).map e.toHomeomorph.toMeasurableEquiv := by
  obtain ⟨c, hc, h⟩ := GlobalTheory.CollapseFactor.exists_eq_map_smul_prod e μ Measure.haar m
  refine ⟨c • Measure.haar, Measure.IsHaarMeasure.nnreal_smul _ hc.ne', ?_⟩
  rw [h, Measure.prod_smul_left]
  rfl

theorem exists_prod_norm (e : (A × B) ≃ₜ* P) (μ : Measure P) (m : Measure B) [μ.IsHaarMeasure] [m.IsHaarMeasure]
    {UA : Set A} {UB : Set B} {UP : Set P} (hU : ∀ a b, e (a, b) ∈ UP ↔ a ∈ UA ∧ b ∈ UB) (h1 : μ UP = 1) (h2 : m UB = 1) :
    ∃ μ' : Measure A, μ'.IsHaarMeasure ∧ μ' UA = 1 ∧ μ = (μ'.prod m).map e.toHomeomorph.toMeasurableEquiv := by
  obtain ⟨μ', h, hμ⟩ := exists_prod e μ m
  refine ⟨μ', h, ?_, hμ⟩
  have hp : e.toHomeomorph.toMeasurableEquiv ⁻¹' UP = UA ×ˢ UB := Set.ext fun p => hU p.1 p.2
  rwa [hμ, MeasurableEquiv.map_apply, hp, Measure.prod_prod, h2, mul_one] at h1

theorem inv_of_prod (e : (A × B) ≃ₜ* P) (μ : Measure P) (m : Measure B) [μ.IsHaarMeasure] [m.IsHaarMeasure]
    [m.IsInvInvariant] (hA : ∀ μ' : Measure A, μ'.IsHaarMeasure → μ'.IsInvInvariant) : μ.IsInvInvariant := by
  obtain ⟨μ', h, hμ⟩ := exists_prod e μ m
  haveI := hA μ' h
  have h1 : (μ'.prod m).map Inv.inv = μ'.prod m := by
    have := Measure.map_prod_map μ' m (measurable_inv (G := A)) (measurable_inv (G := B))
    rw [Measure.map_inv_eq_self, Measure.map_inv_eq_self] at this
    exact this.symm
  constructor
  rw [Measure.inv_def, hμ, Measure.map_map measurable_inv (MeasurableEquiv.measurable _)]
  conv_rhs => rw [← h1, Measure.map_map (MeasurableEquiv.measurable _) measurable_inv]
  congr 1
  funext p
  exact (map_inv e p).symm

end Abstract

theorem quot_transport {G G' : Type} [Group G] [MeasurableSpace G] [Group G'] [MeasurableSpace G'] {R : Subgroup G}
    {R' : Subgroup G'} (E : G' ≃ᵐ G) (hE : ∀ a b, E (a * b) = E a * E b) (ER : R' ≃ᵐ R) (hR : ∀ r, (ER r : G) = E r)
    (μ' : Measure G') (ρ' : Measure R') (f : G → ℂ) (z : ℂ) (h : IsQuotIntL1 ρ' μ' (fun x => f (E x)) z) :
    IsQuotIntL1 (ρ'.map ER) (μ'.map E) f z := by
  obtain ⟨F, h1, h2, h3, h4⟩ := h
  have key : ∀ (x : G) (r : R'), E.symm ((ER r : G) * x) = r * E.symm x := fun x r => by
    apply E.injective
    rw [hE, E.apply_symm_apply, E.apply_symm_apply, hR]
  refine ⟨fun x => F (E.symm x), ?_, fun x => ?_, fun x => ?_, ?_⟩
  · rw [integrable_map_equiv]
    simpa [Function.comp_def] using h1
  · rw [integrable_map_equiv]
    simpa only [Function.comp_def, key] using h2 (E.symm x)
  · rw [integral_map_equiv]
    simpa only [key, E.apply_symm_apply] using h3 (E.symm x)
  · rw [integral_map_equiv]
    simpa using h4

def prodMeas {A B : Type} [Group A] [Group B] [MeasurableSpace A] [MeasurableSpace B] (RA : Subgroup A) (RB : Subgroup B) :
    RA.prod RB ≃ᵐ RA × RB where
  toEquiv := (Subgroup.prodEquiv RA RB).toEquiv
  measurable_toFun := ((measurable_fst.comp measurable_subtype_coe).subtype_mk).prodMk
    ((measurable_snd.comp measurable_subtype_coe).subtype_mk)
  measurable_invFun := ((measurable_subtype_coe.comp measurable_fst).prodMk
    (measurable_subtype_coe.comp measurable_snd)).subtype_mk

theorem side_abs {A B P : Type} [Group A] [TopologicalSpace A] [Group B] [TopologicalSpace B] [Group P] [TopologicalSpace P]
    [IsTopologicalGroup A] [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
    [IsTopologicalGroup B] [LocallyCompactSpace B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
    [IsTopologicalGroup P] [MeasurableSpace P] [BorelSpace P] (e : (A × B) ≃ₜ* P) {RA : Subgroup A} {RB : Subgroup B}
    {RP : Subgroup P} (cA : IsClosed (RA : Set A)) (cB : IsClosed (RB : Set B))
    (hm : ∀ a b, e (a, b) ∈ RP ↔ a ∈ RA ∧ b ∈ RB) {UA : Set A} {UB : Set B} {UP : Set P}
    (hU : ∀ a b, e (a, b) ∈ UP ↔ a ∈ UA ∧ b ∈ UB) (μ : Measure P) (ρ : Measure RP) (m : Measure B) (s : Measure RB)
    (hμ : μ.IsHaarMeasure) (hρ : ρ.IsHaarMeasure) (hm' : m.IsHaarMeasure) (hs : s.IsHaarMeasure) (h1 : μ UP = 1)
    (h2 : ρ {x | x.1 ∈ UP} = 1) (h3 : m UB = 1) (h4 : s {x | x.1 ∈ UB} = 1) :
    ∃ (μ' : Measure A) (ρ' : Measure RA) (p : Measure (RA.prod RB)), μ'.IsHaarMeasure ∧ ρ'.IsHaarMeasure ∧ μ' UA = 1 ∧
      ρ' {x | x.1 ∈ UA} = 1 ∧ p.map (Subgroup.prodEquiv RA RB) = ρ'.prod s ∧
      ∀ (f : P → ℂ) (z : ℂ), IsQuotIntL1 p (μ'.prod m) (fun x => f (e x)) z → IsQuotIntL1 ρ μ f z := by
  haveI := cA.locallyCompactSpace
  haveI := cB.locallyCompactSpace
  obtain ⟨μ', a1, a2, a3⟩ := exists_prod_norm e μ m hU h1 h3
  obtain ⟨ρ', b1, b2, b3⟩ := exists_prod_norm (resEquiv e hm) ρ s (UA := {x | x.1 ∈ UA}) (fun a b => hU a.1 b.1) h2 h4
  let pe := prodMeas RA RB
  refine ⟨μ', ρ', (ρ'.prod s).map pe.symm, a1, b1, a2, b2, pe.map_map_symm, fun f z hq => ?_⟩
  have := quot_transport e.toHomeomorph.toMeasurableEquiv (map_mul e)
    (pe.trans (resEquiv e hm).toHomeomorph.toMeasurableEquiv) (fun r => rfl) _ _ f z hq
  rwa [← a3, MeasurableEquiv.coe_trans, ← Measure.map_map (MeasurableEquiv.measurable _) pe.measurable, pe.map_map_symm,
    ← b3] at this

section Concrete
variable {D : D7}

theorem mem_congGrp {V : HSp D} {I : Ideal (AE D)} {g : GA D V} :
    g ∈ congGrp V I ↔ ∀ i j, mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  constructor
  · intro h i j
    have := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ I) => x.1 i j) h
    rw [← Ideal.Quotient.eq]
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this
  · intro h
    ext i j
    have := h i j
    rw [← Ideal.Quotient.eq] at this
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this

theorem grpAt_mono {V : HSp D} {P R : Pl D → Prop} (h : ∀ p, P p → R p) {g : GA D V}
    (hg : g ∈ grpAt V P) : g ∈ grpAt V R := by
  rw [grpAt, mem_congGrp] at hg ⊢
  intro i j
  have h1 := hg i j
  simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf] at h1 ⊢
  exact ⟨h1.1, fun u => h1.2 ⟨u.1, fun hp => u.2 (h _ hp)⟩⟩

theorem grpAt_off {V : HSp D} {P R : Pl D → Prop} (h : ∀ p, P p → ¬ R p) {g : GA D V}
    (hg : g ∈ grpAt V P) : g ∈ grpOff V R := by
  rw [grpAt, mem_congGrp] at hg
  rw [grpOff, mem_congGrp]
  intro i j
  have h1 := hg i j
  simp only [idAt, idOff, Submodule.mem_inf, Submodule.mem_iInf] at h1 ⊢
  exact fun u => h1.2 ⟨u.1, fun hp => h _ hp u.2⟩

theorem grpAt_of_off {V : HSp D} {P P' : Pl D → Prop} {w : Pl D} (h : ∀ v, P v → w = v ∨ P' v) {g : GA D V}
    (hg : g ∈ grpAt V P) (hg' : g ∈ grpOff V (· = w)) : g ∈ grpAt V P' := by
  rw [grpAt, mem_congGrp] at hg ⊢
  rw [grpOff, mem_congGrp] at hg'
  intro i j
  have h1 := hg i j
  have h2 := hg' i j
  simp only [idAt, idOff, Submodule.mem_inf, Submodule.mem_iInf] at h1 h2 ⊢
  refine ⟨h1.1, fun u => ?_⟩
  by_cases hp : P u.1
  · exact h2 ⟨u.1, ((h _ hp).resolve_right u.2).symm⟩
  · exact h1.2 ⟨u.1, hp⟩

theorem grpAt_eq_one {V : HSp D} {P : Pl D → Prop} (hP : ∀ v, ¬ P v) {g : GA D V} (hg : g ∈ grpAt V P) : g = 1 := by
  have h := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2 V).2.2.1
  have : g ∈ grpAt V P ⊓ grpOff V P := ⟨hg, grpAt_off (fun p hp _ => hP p hp) hg⟩
  rwa [h, Subgroup.mem_bot] at this

variable {k Y : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype Y] [DecidableEq Y]

def IsLocGrp (V : HSp D) (w : Pl D) (gl : GL Y k →* GA D V) : Prop :=
  Continuous gl ∧ (∀ g, gl g ∈ grpAt V (· = w)) ∧ (∀ x : GA D V, ∃! g, x * (gl g)⁻¹ ∈ grpOff V (· = w)) ∧
    ∀ g, ∀ y ∈ grpOff V (· = w), gl g * y = y * gl g

theorem isLocGrp (q : SplitPt D k) (V : HSp D) (F : GlobalTheory.LocMod.Frame k V.rank Y) (gl : GL Y k →* GA D V)
    (h : ∀ g, (ofSplit q).IsLoc F (gl g) g) : IsLocGrp V q.v gl := by
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D k q V Y F gl h
  exact ⟨h1.continuous, fun g => h2 ▸ ⟨g, rfl⟩, h3, h4⟩

variable {V : HSp D} {w : Pl D} {gl : GL Y k →* GA D V}

theorem IsLocGrp.eq_one (h : IsLocGrp V w gl) {g : GL Y k} (hg : gl g ∈ grpOff V (· = w)) : g = 1 :=
  (h.2.2.1 (gl g)).unique (by simp) (by simpa using hg)

theorem off_of_not {P' : Pl D → Prop} (hw : ¬ P' w) {x : GA D V} (hx : x ∈ grpAt V P') : x ∈ grpOff V (· = w) :=
  grpAt_off (R := (· = w)) (fun _ hp e => hw (e ▸ hp)) hx

theorem IsLocGrp.exists_equiv (h : IsLocGrp V w gl) {P P' : Pl D → Prop} (hP : ∀ v, P v ↔ w = v ∨ P' v) (hw : ¬ P' w) :
    ∃ e : (grpAt V P' × GL Y k) ≃ₜ* grpAt V P, ∀ x, (e x : GA D V) = x.1.1 * gl x.2 := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := (GlobalTheory.FinPl.KOpen.isClosed_grpAt V P).locallyCompactSpace
  haveI := (GlobalTheory.FinPl.KOpen.isClosed_grpAt V P').locallyCompactSpace
  let f : (grpAt V P' × GL Y k) →* grpAt V P :=
    { toFun := fun x => ⟨x.1.1 * gl x.2, mul_mem (grpAt_mono (fun p hp => (hP p).2 (Or.inr hp)) x.1.2)
        (grpAt_mono (fun p hp => (hP p).2 (Or.inl hp.symm)) (h.2.1 x.2))⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, map_mul, mul_assoc]
        rw [← mul_assoc (gl x.2), h.2.2.2 _ _ (off_of_not hw y.1.2), mul_assoc]) }
  have hc : Continuous f :=
    ((continuous_subtype_val.comp continuous_fst).mul (h.1.comp continuous_snd)).subtype_mk _
  have hs : Function.Surjective f := fun y => by
    obtain ⟨g, hg, -⟩ := h.2.2.1 y.1
    refine ⟨(⟨y.1 * (gl g)⁻¹, grpAt_of_off (fun v hv => (hP v).1 hv) (mul_mem y.2 (inv_mem
      (grpAt_mono (fun p hp => (hP p).2 (Or.inl hp.symm)) (h.2.1 g)))) hg⟩, g), Subtype.ext ?_⟩
    show y.1 * (gl g)⁻¹ * gl g = y.1
    simp
  have hi : Function.Injective f := (injective_iff_map_eq_one f).2 fun x hx => by
    have h1 : x.1.1 * gl x.2 = 1 := congrArg Subtype.val hx
    have h2 : x.2 = 1 := h.eq_one (by
      rw [← inv_eq_of_mul_eq_one_right h1]; exact inv_mem (off_of_not hw x.1.2))
    rw [h2, map_one, mul_one] at h1
    exact Prod.ext (Subtype.ext h1) h2
  have ho : IsOpenMap f := MonoidHom.isOpenMap_of_sigmaCompact f hs hc
  let E := MulEquiv.ofBijective f ⟨hi, hs⟩
  exact ⟨{ E with
    continuous_toFun := hc
    continuous_invFun := (E.toEquiv.toHomeomorphOfContinuousOpen hc ho).symm.continuous }, fun x => rfl⟩

theorem IsLocGrp.intAt_self (h : IsLocGrp V w gl) {x : GA D V} (hx : x ∈ grpOff V (· = w)) (g : GL Y k) :
    IntAt w gl (x * gl g) ↔ g ∈ KO k Y := by
  constructor
  · rintro ⟨κ, hκ, h1⟩
    rw [mul_assoc, Subgroup.mul_mem_cancel_left _ hx, ← map_inv, ← map_mul] at h1
    rw [mul_inv_eq_one.1 (h.eq_one h1)]
    exact hκ
  · exact fun hg => ⟨g, hg, by simpa using hx⟩

theorem IsLocGrp.intAt_mul (h : IsLocGrp V w gl) (x : GA D V) {y : GA D V} (hy : y ∈ grpOff V (· = w)) :
    IntAt w gl (x * y) ↔ IntAt w gl x := by
  refine exists_congr fun κ => and_congr_right fun _ => ?_
  rw [← map_inv, mul_assoc, ← h.2.2.2 _ _ hy, ← mul_assoc, Subgroup.mul_mem_cancel_right _ hy]

variable [MeasurableSpace k] [BorelSpace k]

def IsLocSub (w : Pl D) (gl : GL Y k →* GA D V) (R : Subgroup (GA D V)) (R₀ : Subgroup (GL Y k)) : Prop :=
  IsClosed (R : Set (GA D V)) ∧ (∀ g, gl g ∈ R ↔ g ∈ R₀) ∧ (∀ g, ∀ y ∈ grpOff V (· = w), gl g * y ∈ R → gl g ∈ R) ∧
    ∀ s : Measure R₀, s.IsHaarMeasure → s {x | x.1 ∈ KO k Y} = 1 → s.IsInvInvariant

variable {R : Subgroup (GA D V)} {R₀ : Subgroup (GL Y k)}

theorem IsLocSub.closed (h : IsLocGrp V w gl) (hR : IsLocSub w gl R R₀) : IsClosed (R₀ : Set (GL Y k)) := by
  have e : (R₀ : Set (GL Y k)) = gl ⁻¹' R := Set.ext fun g => (hR.2.1 g).symm
  rw [e]
  exact hR.1.preimage h.1

theorem IsLocSub.mul_mem_iff (h : IsLocGrp V w gl) (hR : IsLocSub w gl R R₀) {x : GA D V} (hx : x ∈ grpOff V (· = w))
    (g : GL Y k) : x * gl g ∈ R ↔ x ∈ R ∧ g ∈ R₀ := by
  constructor
  · intro h1
    have h2 := hR.2.2.1 g x hx (by rwa [h.2.2.2 g x hx])
    exact ⟨(Subgroup.mul_mem_cancel_right _ h2).1 h1, (hR.2.1 g).1 h2⟩
  · exact fun h1 => mul_mem h1.1 ((hR.2.1 g).2 h1.2)

theorem exists_haar_sub (hc : IsClosed (R₀ : Set (GL Y k))) :
    ∃ s : Measure R₀, s.IsHaarMeasure ∧ s {x | x.1 ∈ KO k Y} = 1 := by
  haveI : BorelSpace (GL Y k) := GlobalTheory.SplitFlip.borel_GL
  have ho : IsOpen {x : R₀ | x.1 ∈ KO k Y} := GlobalTheory.SplitFlip.isOpen_KO.preimage continuous_subtype_val
  have hk : IsCompact {x : R₀ | x.1 ∈ KO k Y} := GlobalTheory.CollapseFactor.isCompact_setOf_val GlobalTheory.SplitFlip.isCompact_KO hc
  let K : TopologicalSpace.PositiveCompacts R₀ := ⟨⟨_, hk⟩, ⟨1, by rw [ho.interior_eq]; exact (KO k Y).one_mem⟩⟩
  exact ⟨Measure.haarMeasure K, inferInstance, Measure.haarMeasure_self (K₀ := K)⟩

theorem inv_step (h : IsLocGrp V w gl) (hR : IsLocSub w gl R R₀) {P P' : Pl D → Prop} (hP : ∀ v, P v ↔ w = v ∨ P' v)
    (hw : ¬ P' w) (ih : ∀ ρ : Measure (R.subgroupOf (grpAt V P')), ρ.IsHaarMeasure → ρ.IsInvInvariant)
    (ρ : Measure (R.subgroupOf (grpAt V P))) (hρ : ρ.IsHaarMeasure) : ρ.IsInvInvariant := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := (GlobalTheory.FinPl.KOpen.isClosed_grpAt V P').locallyCompactSpace
  haveI : BorelSpace (GL Y k) := GlobalTheory.SplitFlip.borel_GL
  have c1 : IsClosed ((R.subgroupOf (grpAt V P') : Subgroup _) : Set (grpAt V P')) := hR.1.preimage continuous_subtype_val
  haveI := c1.locallyCompactSpace
  haveI := (hR.closed h).locallyCompactSpace
  obtain ⟨e, he⟩ := h.exists_equiv hP hw
  have hm : ∀ a b, e (a, b) ∈ R.subgroupOf (grpAt V P) ↔ a ∈ R.subgroupOf (grpAt V P') ∧ b ∈ R₀ := fun a b => by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, he]
    exact hR.mul_mem_iff h (off_of_not hw a.2) b
  obtain ⟨s, hs, hs1⟩ := exists_haar_sub (hR.closed h)
  haveI := hR.2.2.2 s hs hs1
  exact inv_of_prod (resEquiv e hm) ρ s ih

theorem inv_base {P : Pl D → Prop} (hP : ∀ v, ¬ P v) (ρ : Measure (R.subgroupOf (grpAt V P))) : ρ.IsInvInvariant := by
  constructor
  have e : (Inv.inv : R.subgroupOf (grpAt V P) → _) = id :=
    funext fun x => Subtype.ext (Subtype.ext ((grpAt_eq_one hP (x⁻¹).1.2).trans (grpAt_eq_one hP x.1.2).symm))
  rw [Measure.inv_def, e, Measure.map_id]

theorem side_step (h : IsLocGrp V w gl) (hR : IsLocSub w gl R R₀) {P P' : Pl D → Prop} (hP : ∀ v, P v ↔ w = v ∨ P' v)
    (hw : ¬ P' w) (U U' : GA D V → Prop) (hU : ∀ x ∈ grpAt V P', ∀ g, U (x * gl g) ↔ U' x ∧ g ∈ KO k Y)
    (μ : Measure (grpAt V P)) (ρ : Measure (R.subgroupOf (grpAt V P))) (hμ : μ.IsHaarMeasure) (hρ : ρ.IsHaarMeasure)
    (h1 : μ {x | U x.1} = 1) (h2 : ρ {x | U x.1.1} = 1) :
    ∃ (μ' : Measure (grpAt V P')) (ρ' : Measure (R.subgroupOf (grpAt V P'))) (m : Measure (GL Y k)) (s : Measure R₀)
      (p : Measure ((R.subgroupOf (grpAt V P')).prod R₀)) (e : (grpAt V P' × GL Y k) ≃ grpAt V P),
      μ'.IsHaarMeasure ∧ ρ'.IsHaarMeasure ∧ μ' {x | U' x.1} = 1 ∧ ρ' {x | U' x.1.1} = 1 ∧ m.IsHaarMeasure ∧ m (KO k Y) = 1 ∧
      s.IsHaarMeasure ∧ s {x | x.1 ∈ KO k Y} = 1 ∧ s.IsInvInvariant ∧ p.map (Subgroup.prodEquiv _ _) = ρ'.prod s ∧
      (∀ x, (e x : GA D V) = x.1.1 * gl x.2) ∧
      ∀ (f : grpAt V P → ℂ) (z : ℂ), IsQuotIntL1 p (μ'.prod m) (fun x => f (e x)) z → IsQuotIntL1 ρ μ f z := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := (GlobalTheory.FinPl.KOpen.isClosed_grpAt V P').locallyCompactSpace
  haveI : BorelSpace (GL Y k) := GlobalTheory.SplitFlip.borel_GL
  have c1 : IsClosed ((R.subgroupOf (grpAt V P') : Subgroup _) : Set (grpAt V P')) := hR.1.preimage continuous_subtype_val
  haveI := c1.locallyCompactSpace
  haveI := (hR.closed h).locallyCompactSpace
  obtain ⟨e, he⟩ := h.exists_equiv hP hw
  have hm : ∀ a b, e (a, b) ∈ R.subgroupOf (grpAt V P) ↔ a ∈ R.subgroupOf (grpAt V P') ∧ b ∈ R₀ := fun a b => by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, he]
    exact hR.mul_mem_iff h (off_of_not hw a.2) b
  obtain ⟨s, hs, hs1⟩ := exists_haar_sub (hR.closed h)
  have hm1 : GlobalTheory.SplitFlip.haarVol (KO k Y) (KO k Y) = 1 := GlobalTheory.SplitFlip.haarVol_self GlobalTheory.SplitFlip.isOpen_KO le_rfl
  have hU' : ∀ a b, U (e (a, b)).1 ↔ U' a.1 ∧ b ∈ KO k Y := fun a b => by rw [he]; exact hU a.1 a.2 b
  obtain ⟨μ', ρ', p, a1, a2, a3, a4, a5, a6⟩ := side_abs e c1 (hR.closed h) hm (UA := {x | U' x.1}) (UB := KO k Y)
    (UP := {x | U x.1}) hU' μ ρ _ s hμ hρ GlobalTheory.SplitFlip.isHaarMeasure_haarVol_KO hs h1 h2 hm1 hs1
  exact ⟨μ', ρ', _, s, p, e.toEquiv, a1, a2, a3, a4, GlobalTheory.SplitFlip.isHaarMeasure_haarVol_KO, hm1, hs, hs1, hR.2.2.2 s hs hs1, a5, he, a6⟩

end Concrete

section Steps
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

theorem hz_div_xi_ne (Q : QStep S) : (ofSplit Q.q).hz S.B / (ofSplit Q.q).xi ≠ 0 := by
  intro h0
  obtain ⟨hc, -, -, h⟩ := Q.F.jac
  have h1 := h ⟨0, by omega⟩ ⟨2 * σ + 1, by omega⟩ (by simp; omega)
  have h2 := congrFun (congrFun Q.F.G₁.γβ (Sum.inr ⟨2 * σ + 1, by omega⟩)) (Sum.inr ⟨2 * σ + 1, by omega⟩)
  simp [Matrix.mul_apply, h1, h0] at h2

theorem loc₁ (Q : QStep S) : IsLocGrp S.J.W Q.q.v Q.gl₁ := isLocGrp Q.q _ Q.F.G₁ _ Q.loc₁

theorem loc₂ (Q : QStep S) : IsLocGrp S.B'.V Q.q.v Q.gl₂ := isLocGrp Q.q _ Q.F.G₂ _ Q.loc₂

theorem sub₁ (Q : QStep S) : IsLocSub Q.q.v Q.gl₁ (jacGrp S.J.d) (RFJ Q.k Q.n₁ (Q.c + 1 + 1) (σ + 1)) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.T.periodLocalGroups_normalFrames_splitPlace D Q.k Q.q Q.n₁ (Q.c + 1 + 1) (σ + 1)).1 S.J _ _ Q.F.F₁ Q.F.G₁ Q.gl₁ (by omega) Q.F.s_ne
    (div_ne_zero_iff.1 (hz_div_xi_ne Q)).1 Q.F.jac Q.loc₁
  refine ⟨GlobalTheory.jacGrp_isClosed D _ _ _ S.J.d, h1, h2, fun s hs hs1 => ?_⟩
  exact ((GlobalTheory.T.localInvariantIntegrals_symmetric_haarSubgroups Q.k Q.ν Q.unitVol Q.n₁ (Q.c + 1 + 1) (σ + 1) Q.m₁ (GlobalTheory.SplitFlip.haarVol (KO _ _)) Q.haar₁
    GlobalTheory.SplitFlip.isHaarMeasure_haarVol_KO Q.vol₁).2 (by omega) Q.F.jac.1 s hs hs1).1

theorem sub₂ (Q : QStep S) : IsLocSub Q.q.v Q.gl₂ (besGrp S.B'.d S.B'.o) (R Q.k Q.n₂ (Q.c + 1) (σ + 1)) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.T.periodLocalGroups_normalFrames_splitPlace D Q.k Q.q Q.n₂ (Q.c + 1) σ).2 S.B' _ Q.F.F₂ Q.F.G₂ Q.gl₂
    (mul_ne_zero Q.F.s_ne (div_ne_zero_iff.1 (hz_div_xi_ne Q)).2) Q.F.bes' Q.loc₂
  refine ⟨GlobalTheory.BesClosed.besGrp_isClosed _ _ _ _ _ _ S.B'.d S.B'.o, h1, h2, fun s hs hs1 => ?_⟩
  exact ((GlobalTheory.T.localInvariantIntegrals_symmetric_haarSubgroups Q.k Q.ν Q.unitVol Q.n₂ (Q.c + 1) (σ + 1) Q.m₂ (GlobalTheory.SplitFlip.haarVol (KO _ _)) Q.haar₂
    GlobalTheory.SplitFlip.isHaarMeasure_haarVol_KO Q.vol₂).1 Q.F.jac.1 s hs hs1).1

theorem places_succ {r : ℕ} (Q : Fin (r + 1) → QStep S) (v : Pl D) :
    places Q v ↔ (Q 0).q.v = v ∨ places (fun i => Q i.succ) v := Fin.exists_fin_succ

theorem not_places {r : ℕ} {Q : Fin (r + 1) → QStep S} (h : Function.Injective fun i => (Q i).q.v) :
    ¬ places (fun i => Q i.succ) (Q 0).q.v := fun ⟨j, hj⟩ => Fin.succ_ne_zero j (h hj)

theorem inv_places : ∀ (r : ℕ) (Q : Fin r → QStep S), (Function.Injective fun i => (Q i).q.v) →
    (∀ ρ : Measure ((jacGrp S.J.d).subgroupOf (grpAt S.J.W (places Q))), ρ.IsHaarMeasure → ρ.IsInvInvariant) ∧
      ∀ ρ : Measure ((besGrp S.B'.d S.B'.o).subgroupOf (grpAt S.B'.V (places Q))), ρ.IsHaarMeasure → ρ.IsInvInvariant := by
  intro r
  induction r with
  | zero => exact fun Q _ => ⟨fun ρ _ => inv_base (fun _ ⟨i, _⟩ => i.elim0) ρ, fun ρ _ => inv_base (fun _ ⟨i, _⟩ => i.elim0) ρ⟩
  | succ r ih =>
    intro Q h
    obtain ⟨h1, h2⟩ := ih (fun i => Q i.succ) (h.comp (Fin.succ_injective _))
    exact ⟨inv_step (loc₁ (Q 0)) (sub₁ (Q 0)) (places_succ Q) (not_places h) h1,
      inv_step (loc₂ (Q 0)) (sub₂ (Q 0)) (places_succ Q) (not_places h) h2⟩

theorem int₁ {r : ℕ} {Q : Fin (r + 1) → QStep S} (h : Function.Injective fun i => (Q i).q.v) :
    ∀ x ∈ grpAt S.J.W (places fun i => Q i.succ), ∀ g, (∀ i, IntAt (Q i).q.v (Q i).gl₁ (x * (Q 0).gl₁ g)) ↔
      (∀ i : Fin r, IntAt (Q i.succ).q.v (Q i.succ).gl₁ x) ∧ g ∈ KO _ _ := fun x hx g => by
  rw [Fin.forall_fin_succ, (loc₁ (Q 0)).intAt_self (off_of_not (not_places h) hx), and_comm]
  refine and_congr_left fun _ => forall_congr' fun i => (loc₁ (Q i.succ)).intAt_mul x
    (off_of_not (P' := (· = (Q 0).q.v)) (fun e => Fin.succ_ne_zero i (h e)) ((loc₁ (Q 0)).2.1 g))

theorem int₂ {r : ℕ} {Q : Fin (r + 1) → QStep S} (h : Function.Injective fun i => (Q i).q.v) :
    ∀ x ∈ grpAt S.B'.V (places fun i => Q i.succ), ∀ g, (∀ i, IntAt (Q i).q.v (Q i).gl₂ (x * (Q 0).gl₂ g)) ↔
      (∀ i : Fin r, IntAt (Q i.succ).q.v (Q i.succ).gl₂ x) ∧ g ∈ KO _ _ := fun x hx g => by
  rw [Fin.forall_fin_succ, (loc₂ (Q 0)).intAt_self (off_of_not (not_places h) hx), and_comm]
  refine and_congr_left fun _ => forall_congr' fun i => (loc₂ (Q i.succ)).intAt_mul x
    (off_of_not (P' := (· = (Q 0).q.v)) (fun e => Fin.succ_ne_zero i (h e)) ((loc₂ (Q 0)).2.1 g))

end Steps

set_option maxHeartbeats 1000000 in

theorem reduce : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin (r + 1) → QStep S), Function.Injective (fun i => (Q i).q.v) → ∀ (μ₁ : Measure (grpAt S.J.W (places Q))) (ρ₁ : Measure ((jacGrp S.J.d).subgroupOf (grpAt S.J.W (places Q)))) (μ₂ : Measure (grpAt S.B'.V (places Q))) (ρ₂ : Measure ((besGrp S.B'.d S.B'.o).subgroupOf (grpAt S.B'.V (places Q)))), Norm Q μ₁ ρ₁ μ₂ ρ₂ → LocallyCompactSpace (grpAt S.J.W (places fun i => Q i.succ)) ∧ LocallyCompactSpace (grpAt S.B'.V (places fun i => Q i.succ)) ∧ IsClosed (((jacGrp S.J.d).subgroupOf (grpAt S.J.W (places fun i => Q i.succ)) : Set (grpAt S.J.W (places fun i => Q i.succ)))) ∧ IsClosed (((besGrp S.B'.d S.B'.o).subgroupOf (grpAt S.B'.V (places fun i => Q i.succ)) : Set (grpAt S.B'.V (places fun i => Q i.succ)))) ∧ IsClosed ((RFJ (Q 0).k (Q 0).n₁ ((Q 0).c + 1 + 1) (σ + 1) : Set (GL ((Q 0).n₁ ⊕ Fin ((Q 0).c + 1 + 1)) (Q 0).k))) ∧ IsClosed ((R (Q 0).k (Q 0).n₂ ((Q 0).c + 1) (σ + 1) : Set (GL ((Q 0).n₂ ⊕ Fin ((Q 0).c + 1)) (Q 0).k))) ∧ ∃ (μ₁' : Measure (grpAt S.J.W (places fun i => Q i.succ))) (ρ₁' : Measure ((jacGrp S.J.d).subgroupOf (grpAt S.J.W (places fun i => Q i.succ)))) (μ₂' : Measure (grpAt S.B'.V (places fun i => Q i.succ))) (ρ₂' : Measure ((besGrp S.B'.d S.B'.o).subgroupOf (grpAt S.B'.V (places fun i => Q i.succ)))) (m₁ : Measure (GL ((Q 0).n₁ ⊕ Fin ((Q 0).c + 1 + 1)) (Q 0).k)) (s₁ : Measure (RFJ (Q 0).k (Q 0).n₁ ((Q 0).c + 1 + 1) (σ + 1))) (m₂ : Measure (GL ((Q 0).n₂ ⊕ Fin ((Q 0).c + 1)) (Q 0).k)) (s₂ : Measure (R (Q 0).k (Q 0).n₂ ((Q 0).c + 1) (σ + 1))) (p₁ : Measure (((jacGrp S.J.d).subgroupOf (grpAt S.J.W (places fun i => Q i.succ))).prod (RFJ (Q 0).k (Q 0).n₁ ((Q 0).c + 1 + 1) (σ + 1)))) (p₂ : Measure (((besGrp S.B'.d S.B'.o).subgroupOf (grpAt S.B'.V (places fun i => Q i.succ))).prod (R (Q 0).k (Q 0).n₂ ((Q 0).c + 1) (σ + 1)))), Norm (fun i => Q i.succ) μ₁' ρ₁' μ₂' ρ₂' ∧ LocNorm (Q 0) m₁ s₁ m₂ s₂ ∧ ρ₁'.IsInvInvariant ∧ ρ₂'.IsInvInvariant ∧ s₁.IsInvInvariant ∧ s₂.IsInvInvariant ∧ p₁.map (Subgroup.prodEquiv _ _) = ρ₁'.prod s₁ ∧ p₂.map (Subgroup.prodEquiv _ _) = ρ₂'.prod s₂ ∧ ∀ (F : GA D S.J.W → GA D S.B'.V → ℂ) (z : ℂ), Iter2 p₁ (μ₁'.prod m₁) p₂ (μ₂'.prod m₂) (fun x y => F (x.1.1 * (Q 0).gl₁ x.2) (y.1.1 * (Q 0).gl₂ y.2)) z → Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun x y => F x.1 y.1) z := by
  intro D ψ σ S r Q h μ₁ ρ₁ μ₂ ρ₂ ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩
  obtain ⟨μ₁', ρ₁', m₁, s₁, p₁, e₁, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ :=
    side_step (loc₁ (Q 0)) (sub₁ (Q 0)) (places_succ Q) (not_places h) (fun x => ∀ i, IntAt (Q i).q.v (Q i).gl₁ x)
      (fun x => ∀ i : Fin r, IntAt (Q i.succ).q.v (Q i.succ).gl₁ x) (int₁ h) μ₁ ρ₁ a1 a2 a5 a6
  obtain ⟨μ₂', ρ₂', m₂, s₂, p₂, e₂, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ :=
    side_step (loc₂ (Q 0)) (sub₂ (Q 0)) (places_succ Q) (not_places h) (fun x => ∀ i, IntAt (Q i).q.v (Q i).gl₂ x)
      (fun x => ∀ i : Fin r, IntAt (Q i.succ).q.v (Q i.succ).gl₂ x) (int₂ h) μ₂ ρ₂ a3 a4 a7 a8
  obtain ⟨i₁, i₂⟩ := inv_places r (fun i => Q i.succ) (h.comp (Fin.succ_injective _))
  haveI := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S.J.W).1
  haveI := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S.B'.V).1
  refine ⟨(GlobalTheory.FinPl.KOpen.isClosed_grpAt _ _).locallyCompactSpace, (GlobalTheory.FinPl.KOpen.isClosed_grpAt _ _).locallyCompactSpace,
    (sub₁ (Q 0)).1.preimage continuous_subtype_val, (sub₂ (Q 0)).1.preimage continuous_subtype_val,
    (sub₁ (Q 0)).closed (loc₁ (Q 0)), (sub₂ (Q 0)).closed (loc₂ (Q 0)), μ₁', ρ₁', μ₂', ρ₂', m₁, s₁, m₂, s₂, p₁, p₂,
    ⟨b1, b2, c1, c2, b3, b4, c3, c4⟩, ⟨b5, b6, b7, b8, c5, c6, c7, c8⟩, i₁ _ b2, i₂ _ c2, b9, c9, b10, c10, ?_⟩
  rintro F z ⟨f₁, hf, hf'⟩
  refine ⟨fun q => f₁ (e₁.symm q), b12 _ z (by simpa only [Equiv.symm_apply_apply] using hf), fun q => c12 _ _ ?_⟩
  have := hf' (e₁.symm q)
  simpa only [← b11, ← c11, Equiv.apply_symm_apply] using this

end GlobalTheory.QRed

end
