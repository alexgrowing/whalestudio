import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityInnerProductUnitTwistedRightTranslat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLevChiFlagLEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMapMulRightOfMemCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockDetSingleBlockSecondEqOneOfLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeInnerProductModel

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainScalar

section General

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem topGroup (V : HSp D) : IsTopologicalGroup (GA D V) := by
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  exact inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))

theorem isMeasLev_unique {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))} {μ μ' : Measure (GA D V)}
    (h : IsMeasLev V K μ) (h' : IsMeasLev V K μ') : μ' = μ := by
  obtain ⟨hlc, hsc, hbo, hcount⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  have htg := topGroup V
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨hμ, ⟨θ, hθ⟩, h1⟩ := h
  obtain ⟨⟨A, hA⟩, h2⟩ := h1 θ hθ
  obtain ⟨⟨m, hm⟩, h3⟩ := h2 A hA
  obtain ⟨hμ', -, h1'⟩ := h'
  let B : ∀ ρ : D.what₂.Tau, TopologicalSpace.PositiveCompacts (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) :=
    fun ρ => Classical.arbitrary _
  have hB : ∀ ρ, MeasurableSet (B ρ : Set (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2)) := fun ρ =>
    (B ρ).isCompact.measurableSet
  have e1 := h3 m hm (fun ρ => B ρ) hB
  have e2 := ((h1' θ hθ).2 A hA).2 m hm (fun ρ => B ρ) hB
  have h0 : ∏ ρ, m ρ (B ρ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun ρ _ => by
    have := (hm ρ).1
    exact ((Measure.measure_pos_of_nonempty_interior (m ρ) (B ρ).interior_nonempty)).ne'
  have ht : ∏ ρ, m ρ (B ρ) ≠ ⊤ := ENNReal.prod_ne_top fun ρ _ => by
    have := (hm ρ).1
    exact (B ρ).isCompact.measure_lt_top.ne
  have e : μ' = ((Measure.haarScalarFactor μ' μ : NNReal) : ENNReal) • μ := Measure.isMulLeftInvariant_eq_smul μ' μ
  rw [e, Measure.smul_apply, e1, smul_eq_mul] at e2
  have hc : ((Measure.haarScalarFactor μ' μ : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj h0 ht).1 (e2.trans (one_mul _).symm)
  rw [e, hc, one_smul]

theorem isMultiplicityInner_of_fundamentalDomain (θ : InfFam D) (M : DSModel V S) {J χ} {μ : Measure (GA D V)} {𝓕 𝓕' : Set (GA D V)}
    (hμ : μ.IsHaarMeasure) (h : IsFundamentalDomain (GQ V) 𝓕 μ) (h' : IsFundamentalDomain (GQ V) 𝓕' μ)
    {T T' : MMap M} (hT : T ∈ Mult θ M J χ) (hT' : T' ∈ Mult θ M J χ) {c : ℂ} (hc : IsMultIP M μ 𝓕 T T' c) :
    IsMultIP M μ 𝓕' T T' c := by
  obtain ⟨hlc, hsc, hbo, hcount⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  have htg := topGroup V
  intro v v'
  have hinv : ∀ (γ : GQ V) (g : GA D V), star (T v (γ • g)) * T' v' (γ • g) = star (T v g) * T' v' g := fun γ g => by
    show star (T v (γ.1 * g)) * T' v' (γ.1 * g) = _
    rw [(GlobalTheory.mult_value_left_cont_level θ M J χ T hT v).1 γ γ.2 g, (GlobalTheory.mult_value_left_cont_level θ M J χ T' hT' v').1 γ γ.2 g]
  exact ⟨(h.integrableOn_iff h' hinv).1 (hc v v').1, (h'.setIntegral_eq h hinv).trans (hc v v').2⟩

theorem ip_unique (M : DSModel V S) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {T T' : MMap M} {c c' : ℂ}
    (h : IsMultIP M μ 𝓕 T T' c) (h' : IsMultIP M μ 𝓕 T T' c') : c = c' := by
  have hv : ∀ τ, ∃ v : M.sm τ, v ≠ 0 := fun τ => by
    obtain ⟨v, hv, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (GlobalTheory.GardingVec.sm_ne_bot D V S M τ)
    exact ⟨⟨v, hv⟩, fun h => h0 (congrArg Subtype.val h)⟩
  choose v hv using hv
  exact hasPeterssonInner_unique M μ 𝓕 T T' v
    (Finset.prod_ne_zero_iff.2 fun τ _ h => hv τ (Subtype.ext (inner_self_eq_zero.1 h))) h h'

theorem ip_sum (M : DSModel V S) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {ι : Type} [Fintype ι] {T T' : ι → MMap M}
    {U U' : MMap M} (z a : ι → ℂ) (h : ∀ i, IsMultIP M μ 𝓕 (T i) (T' i) (a i))
    (hU : ∀ v v' g, star (U v g) * U' v' g = ∑ i, z i * (star (T i v g) * T' i v' g)) :
    IsMultIP M μ 𝓕 U U' (∑ i, z i * a i) := by
  intro v v'
  simp only [hU]
  refine ⟨integrable_finset_sum _ fun i _ => (h i v v').1.const_mul _, ?_⟩
  rw [integral_finset_sum _ fun i _ => (h i v v').1.const_mul _, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, (h i v v').2, mul_assoc]

theorem levelGroupAction_apply_of_exists_lift {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {g : G0 L.Pg L.r}
    (hk : ∃ κ, IsLevelLift V β L g κ) (f : GA D V → ℂ) (h : GA D V) :
    actG0 V β L g f h = (levChi V β (flagL L) hk.choose)⁻¹ * f (h * hk.choose) := by
  rw [actG0, dif_pos hk]

theorem levelGroupActionOnAdelicFunctions_eq_zero_of_no_lift {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {g : G0 L.Pg L.r}
    (hk : ¬ ∃ κ, IsLevelLift V β L g κ) (f : GA D V → ℂ) : actG0 V β L g f = 0 := by
  rw [actG0, dif_neg hk]

end General

theorem eq_adjoint_of_inner {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (f : X →ₗ[ℂ] Y) (u : Y) (x : X)
    (h : ∀ y, ⟪x, y⟫_ℂ = ⟪u, f y⟫_ℂ) : x = LinearMap.adjoint f u :=
  ext_inner_right ℂ fun y => (h y).trans (LinearMap.adjoint_inner_left f y u).symm

theorem eq_smul_of_inner {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (f : X →ₗ[ℂ] Y) (P : Submodule ℂ Y) (l : ℂ)
    (h : ∀ u₁ ∈ P, ∀ u₂ ∈ P, u₁ ≠ 0 → u₂ ≠ 0 → ⟪LinearMap.adjoint f u₁, LinearMap.adjoint f u₂⟫_ℂ = l * ⟪u₁, u₂⟫_ℂ)
    {x : Y} (hx : x ∈ P) (h0 : x ≠ 0) (hK : f (LinearMap.adjoint f x) ∈ P) : f (LinearMap.adjoint f x) = l • x := by
  by_contra hne
  have h1 := h _ (P.sub_mem hK (P.smul_mem l hx)) x hx (sub_ne_zero.2 hne) h0
  rw [LinearMap.adjoint_inner_left] at h1
  apply hne
  rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℂ)]
  conv_lhs => rw [inner_sub_right, inner_smul_right, h1, sub_self]

theorem sum_adjoint_eq {G H : Type} [Group G] [Fintype G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Representation ℂ G H) (hπ : ∀ g x, ‖π g x‖ = ‖x‖) (c : G → ℂ) (hc : ∀ x, ∑ g, c g • π g x = x) (x : H) :
    ∑ g, star (c g) • π g⁻¹ x = x := by
  refine ext_inner_right ℂ fun y => ?_
  conv_rhs => rw [← hc y]
  rw [sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [inner_smul_left, inner_smul_right]
  have h1 := (LinearIsometry.mk (π g) (hπ g)).inner_map_map (π g⁻¹ x) y
  have h2 : π g (π g⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  change ⟪π g (π g⁻¹ x), π g y⟫_ℂ = _ at h1
  rw [h2] at h1
  rw [h1]
  simp

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

variable (R) in

abbrev Mult0 : Submodule ℂ (MMap (R.MY 0)) :=
  Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv))

theorem e_mem_EE (hE : R.models_HE) (x : R.HE.H) : R.HE.e x ∈ R.EEat R.triv :=
  hE.2.1 ▸ LinearMap.mem_range_self _ x

theorem goodRowsProjector_apply_eq_sum (f : GA D (Yc D 0) → ℂ) :
    R.e0 f = ∑ g, RealDat.eC (A := A) D.what₂.embLL g • actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) f := by
  unfold RealDat.e0 gaL
  rw [LinearMap.sum_apply]
  rfl

theorem e_gE (hg : R.models_gE) (g : G) (x : R.HE.H) (v : (R.MY 0).Vec) :
    R.HE.e (R.gE g x) v = actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (R.HE.e x v) := by
  rw [hg g x]
  rfl

theorem sum_gE (hE : R.models_HE) (hg : R.models_gE) (x : R.HE.H) :
    ∑ g, RealDat.eC (A := A) D.what₂.embLL g • R.gE g x = x := by
  refine hE.1 (MultilinearMap.ext fun v => ?_)
  have h := ((mem_goodPart R.θ (R.MY 0) _ _ R.e0 _).1 (e_mem_EE hE x)).2 v
  rw [← h, goodRowsProjector_apply_eq_sum, map_sum, MultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, MultilinearMap.smul_apply, e_gE hg]

theorem gE_gE_inv (g : G) (x : R.HE.H) : R.gE g (R.gE g⁻¹ x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem ip_act (hM : R.IsModels) {x : R.HE.H} (hx : x ≠ 0) (g : G) {U U' W W' : MMap (R.MY 0)} (hU : U ∈ Mult0 R)
    (hU' : U' ∈ Mult0 R) (hW : ∀ v, W v = actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (U v))
    (hW' : ∀ v, W' v = actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (U' v)) {a : ℂ}
    (ha : IsMultIP (R.MY 0) R.ν0 R.fd0 U U' a) : IsMultIP (R.MY 0) R.ν0 R.fd0 W W' a := by
  obtain ⟨hlc, hsc, hbo, hcount⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable (Yc D 0)
  have htg := topGroup (Yc D 0)
  have hμ := hM.ν0.1.1
  have hk : ∃ κ, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) κ := by
    by_contra hk
    refine hx (hM.HE.1 (MultilinearMap.ext fun v => ?_))
    rw [← gE_gE_inv g x, e_gE hM.gE, map_zero]
    exact levelGroupActionOnAdelicFunctions_eq_zero_of_no_lift hk _
  obtain ⟨hcpt, hlift⟩ := GlobalTheory.ParahoricCompact.isCompact_flag_and_lift (Yc D 0) (R.βY 0) (R.dat0 R.triv)
  have hκ := hlift _ _ hk.choose_spec
  exact GlobalTheory.isMultiplicityInner_of_unit_twist_shift R.θ (R.MY 0) _ _ R.ν0 R.fd0 hμ hM.ν0.2 hk.choose
    (levChi (Yc D 0) (R.βY 0) (flagL (R.dat0 R.triv)) hk.choose)⁻¹
    (by rw [norm_inv, GlobalTheory.norm_levChi_flagL_eq_one _ _ _ _ hκ, inv_one])
    (GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup R.ν0 _ hcpt _ hκ) _ hU _ hU' _ _
    (fun v h => (congrFun (hW v) h).trans (levelGroupAction_apply_of_exists_lift hk _ _)) (fun v h => (congrFun (hW' v) h).trans (levelGroupAction_apply_of_exists_lift hk _ _)) _ ha

theorem norm_gE (hM : R.IsModels) (g : G) (x : R.HE.H) : ‖R.gE g x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · rw [hx, map_zero]
  have hip := GlobalTheory.SchurPolar.isMultiplicityInner_inner (R.MY 0) R.ν0 R.fd0 R.HE _ hM.HE
  have h := ip_unique _ (hip (R.gE g x) (R.gE g x))
    (ip_act hM hx g (e_mem_EE hM.HE x).1 (e_mem_EE hM.HE x).1 (e_gE hM.gE g x) (e_gE hM.gE g x) (hip x x))
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ x, h]

theorem schurConstant_goodRow_projector_invariant (hM : R.IsModels) (hS : GlobalTheory.Hk3.SchurAll R) {x : R.HE.H} (hx : x ≠ 0) {U : MMap (R.MY 0)} (hU : U ∈ Mult0 R) {a : ℂ}
    (ha : IsMultIP (R.MY 0) R.ν0 R.fd0 (R.HE.e x) U a) :
    IsMultIP (R.MY 0) R.ν0 R.fd0 (R.HE.e x) (postOn (R.MY 0) R.e0 U) a := by
  have hmem : ∀ y, R.HE.e y ∈ Mult0 R := fun y => (e_mem_EE hM.HE y).1
  choose b hb using fun g => hS.2.1 hM.inf hM.ν0.1.1 hM.ν0.2 _ (hmem (R.gE g⁻¹ x)) _ hU
  have hb' : ∀ g, IsMultIP (R.MY 0) R.ν0 R.fd0 (R.HE.e x)
      (postOn (R.MY 0) (actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g)) U) (b g) := fun g =>
    ip_act hM hx g (hmem (R.gE g⁻¹ x)) hU (fun v => by rw [← e_gE hM.gE, gE_gE_inv]) (fun _ => rfl) (hb g)
  have h1 : IsMultIP (R.MY 0) R.ν0 R.fd0 (R.HE.e x) U (∑ g, RealDat.eC (A := A) D.what₂.embLL g * b g) := by
    refine ip_sum _ _ _ hb fun v v' h => ?_
    conv_lhs => rw [← sum_adjoint_eq R.gE (norm_gE hM) _ (sum_gE hM.HE hM.gE) x]
    rw [map_sum, MultilinearMap.sum_apply, Finset.sum_apply, star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, star_mul', star_star, mul_assoc]
  rw [ip_unique _ ha h1]
  refine ip_sum _ _ _ hb' fun v v' h => ?_
  rw [postOn_apply, goodRowsProjector_apply_eq_sum, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_left_comm]
  rfl

theorem rank_zeroth_component_eq : (Yc D 0).rank = D.R.r := by
  rw [D.sp.Y_rank _ (min_le_right _ _)]; simp [Ranks.rankY]

theorem lev_zero (t : T) : lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.datYt t 0 R.triv) =
    lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv) := by
  ext x
  rw [Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev, Formalism.L2.DIV.mem_parLev]
  constructor
  · rintro ⟨⟨h1, h2, h3, _⟩, h5⟩
    exact ⟨⟨h1, h2, h3, fun PP _ => mem_blockTriangular_singleBlock_of_le (r := D.R.r) rank_zeroth_component_eq.le _⟩, h5⟩
  · rintro ⟨⟨h1, h2, h3, _⟩, h5⟩
    exact ⟨⟨h1, h2, h3, fun PP _ => mem_blockTriangular_singleBlock_of_le (r := D.R.r) rank_zeroth_component_eq.le _⟩, h5⟩

theorem nu_zero (hM : R.IsModels) (t : T) : R.νY t 0 = R.ν0 :=
  isMeasLev_unique hM.ν0.1 (lev_zero (R := R) t ▸ (hM.νY t 0 D.R.two_le_m).1)

theorem isInnerProduct_zero_iff_isMultiplicityInner (hM : R.IsModels) (t : T) {U U' : MMap (R.MY 0)} (hU : U ∈ Mult0 R) (hU' : U' ∈ Mult0 R) (a : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.IsIP R t 0 U U' a ↔ IsMultIP (R.MY 0) R.ν0 R.fd0 U U' a := by
  have h := (hM.νY t 0 D.R.two_le_m).2
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.IsIP
  rw [nu_zero hM t] at h ⊢
  exact ⟨isMultiplicityInner_of_fundamentalDomain R.θ _ hM.ν0.1.1 h hM.ν0.2 hU hU', isMultiplicityInner_of_fundamentalDomain R.θ _ hM.ν0.1.1 hM.ν0.2 h hU hU'⟩

theorem mem_mult0 (t : T) (y : R.CC t 0) : PiTensorProduct.lift.symm y.1 ∈ Mult0 R := by
  obtain ⟨h2, h3⟩ := GlobalTheory.levG_twist_trivial_of_rank_eq (Yc D 0) (R.βY 0) D.R.r D.R.t (r_le_Y 0) rank_zeroth_component_eq R.Pg (R.Q t) R.triv
    R.chi (R.xiR t)
  have h2' : levS _ (R.βY 0) (R.datYt t 0 R.triv) = levS _ (R.βY 0) (R.dat0 R.triv) := congrArg SetLike.coe h2
  refine Submodule.span_mono (fun U h => ?_) ((mem_multT R.θ (R.MY 0) _ _ _).1 y.2)
  exact ⟨h.aut, h.cusp, fun v k hk g => (h.lev v k (h2' ▸ hk) g).trans (congrArg (· * U v g) (h3 k (h2 ▸ hk))), h.equiv, h.cont⟩

open GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars

def Lifts (t : T) (u : MMap (R.MY 0)) (k : ℕ) (x : MMap (R.MY k)) : Prop :=
  ∀ (y : R.CC t k) (a : ℂ), IsIP R t k x (PiTensorProduct.lift.symm y.1) a →
    IsIP R t 0 u (PiTensorProduct.lift.symm (Lift.dnFrom (R.CC t) (R.ioY t) k y).1) a

theorem exists_lifts (t : T) (c : EigSys D) (Λ : ℕ → ℝ) {u₁ u₂ : MMap (R.MY 0)} (h₁ : u₁ ∈ rowPart R (badPl R t) c)
    (h₂ : u₂ ∈ rowPart R (badPl R t) c) {a : ℂ} (ha : IsIP R t 0 u₁ u₂ a) (k : ℕ) (hΛ : ∀ j, j < k → StepScalar R t c j (Λ j)) :
    ∃ x₁ ∈ reached R t c k, ∃ x₂ ∈ reached R t c k, Lifts t u₁ k x₁ ∧ Lifts t u₂ k x₂ ∧
      IsIP R t k x₁ x₂ (((∏ j ∈ Finset.range k, Λ j : ℝ) : ℂ) * a) := by
  induction k with
  | zero => exact ⟨u₁, h₁, u₂, h₂, fun _ _ h => h, fun _ _ h => h, by simpa using ha⟩
  | succ k ih =>
    obtain ⟨x₁, m₁, x₂, m₂, l₁, l₂, hip⟩ := ih fun j hj => hΛ j (hj.trans (Nat.lt_succ_self k))
    obtain ⟨hex, hsc⟩ := hΛ k (Nat.lt_succ_self k)
    obtain ⟨y₁, hy₁⟩ := hex x₁ m₁
    obtain ⟨y₂, hy₂⟩ := hex x₂ m₂
    have step : ∀ {u x y}, Lifts t u k x → IsUp R t k x y → Lifts t u (k + 1) y := by
      intro u x y l hy z b hb
      obtain ⟨b', hb1, hb2⟩ := hy.2 z
      obtain rfl : b = b' := ip_unique _ hb hb1
      exact l _ _ hb2
    refine ⟨y₁, ⟨x₁, m₁, hy₁⟩, y₂, ⟨x₂, m₂, hy₂⟩, step l₁ hy₁, step l₂ hy₂, ?_⟩
    obtain ⟨b, hb1, hb2⟩ := hsc x₁ m₁ x₂ m₂ y₁ y₂ hy₁ hy₂
    rw [ip_unique _ hb1 hip] at hb2
    rw [Finset.prod_range_succ, Complex.ofReal_mul, mul_comm _ (Λ k : ℂ), mul_assoc]
    exact hb2

theorem top_dn (t : T) {u : MMap (R.MY 0)} {x : MMap (R.MY (D.R.m - 1))} (l : Lifts t u (D.R.m - 1) x) {X : (R.HX t).H}
    (hX : IsUpTop R t x X) (y : (R.HX t).H) :
    ∃ z : R.CC t 0, z.1 = R.thDn t y ∧ IsIP R t 0 u (PiTensorProduct.lift.symm z.1) ⟪X, y⟫_ℂ := by
  have h0 := hX y
  unfold topStep at h0
  refine ⟨_, ?_, l _ _ h0⟩
  unfold RealDat.thDn Lift.thetaDn
  simp only [LinearMap.comp_apply, Submodule.subtype_apply]

theorem top_eq_adjoint (hM : R.IsModels) (hT : R.chain_Th) (hS : GlobalTheory.Hk3.SchurAll R) (t : T) {u : R.HE.H} (hu : u ≠ 0)
    {x : MMap (R.MY (D.R.m - 1))} (l : Lifts (R := R) t (R.HE.e u) (D.R.m - 1) x) {X : (R.HX t).H} (hX : IsUpTop R t x X) :
    X = LinearMap.adjoint (R.Th t) u := by
  refine eq_adjoint_of_inner _ _ _ fun y => ?_
  have h0 := top_dn (R := R) t l hX y
  obtain ⟨z, hz, h1⟩ := h0
  have hz0 := mem_mult0 (R := R) t z
  have h2 := schurConstant_goodRow_projector_invariant (R := R) hM hS hu hz0 ((isInnerProduct_zero_iff_isMultiplicityInner (R := R) hM t (e_mem_EE (R := R) hM.HE u).1 hz0 _).1 h1)
  have h3 := GlobalTheory.SchurPolar.isMultiplicityInner_inner (R.MY 0) R.ν0 R.fd0 R.HE _ hM.HE u (R.Th t y)
  have e : R.HE.e (R.Th t y) = postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm z.1) :=
    (hT t y).trans (congrArg (fun w : SmT (R.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ) =>
      postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm w)) hz.symm)
  exact ip_unique _ ((congrArg (fun w => IsMultIP (R.MY 0) R.ν0 R.fd0 (R.HE.e u) w ⟪X, y⟫_ℂ) e).mpr h2) h3

theorem mem_rowPart (hE : R.models_HE) {SF} {c : EigSys D} {x : R.HE.H} :
    x ∈ GlobalTheory.Hk3.EEc R SF c ↔ R.HE.e x ∈ rowPart R SF c := by
  unfold GlobalTheory.Hk3.EEc rowPart
  rw [Submodule.mem_comap, Submodule.mem_inf]
  exact ⟨fun h => ⟨h, e_mem_EE hE x⟩, fun h => h.1⟩

theorem inner_adjoint (hM : R.IsModels) (hT : R.chain_Th) (hS : GlobalTheory.Hk3.SchurAll R) (t : T) (c : EigSys D) (Λ : ℕ → ℝ)
    (hΛ : ∀ j, j < D.R.m - 1 → StepScalar R t c j (Λ j)) (hΛ' : TopScalar R t c (Λ (D.R.m - 1)))
    {u₁ u₂ : R.HE.H} (h₁ : u₁ ∈ GlobalTheory.Hk3.EEc R (badPl R t) c) (h₂ : u₂ ∈ GlobalTheory.Hk3.EEc R (badPl R t) c)
    (z₁ : u₁ ≠ 0) (z₂ : u₂ ≠ 0) :
    ⟪LinearMap.adjoint (R.Th t) u₁, LinearMap.adjoint (R.Th t) u₂⟫_ℂ =
      ((∏ j ∈ Finset.range (D.R.m - 1 + 1), Λ j : ℝ) : ℂ) * ⟪u₁, u₂⟫_ℂ := by
  have ha := (isInnerProduct_zero_iff_isMultiplicityInner (R := R) hM t (e_mem_EE (R := R) hM.HE u₁).1 (e_mem_EE (R := R) hM.HE u₂).1 _).2
    (GlobalTheory.SchurPolar.isMultiplicityInner_inner (R.MY 0) R.ν0 R.fd0 R.HE _ hM.HE u₁ u₂)
  have h0 := exists_lifts (R := R) t c Λ ((mem_rowPart (R := R) hM.HE).1 h₁)
    ((mem_rowPart (R := R) hM.HE).1 h₂) ha _ hΛ
  obtain ⟨x₁, m₁, x₂, m₂, l₁, l₂, hip⟩ := h0
  obtain ⟨hex, hsc⟩ := hΛ'
  have h0 := hex x₁ m₁
  obtain ⟨X₁, hX₁⟩ := h0
  have h0 := hex x₂ m₂
  obtain ⟨X₂, hX₂⟩ := h0
  have h0 := hsc x₁ m₁ x₂ m₂ X₁ X₂ hX₁ hX₂
  obtain ⟨b, hb1, hb2⟩ := h0
  have e₁ := top_eq_adjoint (R := R) hM hT hS t z₁ l₁ hX₁
  have e₂ := top_eq_adjoint (R := R) hM hT hS t z₂ l₂ hX₂
  have e₃ := ip_unique _ hb1 hip
  refine ((congrArg₂ (fun a b : (R.HX t).H => ⟪a, b⟫_ℂ) e₁ e₂).symm.trans hb2).trans ?_
  generalize ⟪u₁, u₂⟫_ℂ = a at e₃ ⊢
  rw [e₃, Finset.prod_range_succ, Complex.ofReal_mul]
  ring

theorem eec_le {SF} (hSF : GlobalTheory.Hk3.IsSF R SF) (t : T) (c : EigSys D) {x : R.HE.H} (hE : R.models_HE)
    (hx : x ∈ GlobalTheory.Hk3.EEc R SF c) : x ∈ GlobalTheory.Hk3.EEc R (badPl R t) c := by
  classical
  have h : SF ⊆ badPl R t := fun v hv => by
    obtain ⟨PP, h1, h2⟩ := (hSF v).1 hv
    unfold badPl
    simp only [Finset.mem_image, Finset.mem_union]
    exact ⟨PP, Or.inl h1, HeightOneSpectrum.ext h2⟩
  exact (mem_rowPart (R := R) hE).2 (rowPart_mono R h c ((mem_rowPart (R := R) hE).1 hx))

end Real

theorem bForm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R → Kept R → ∀ SF, GlobalTheory.Hk3.IsSF R SF → BForm R SF := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS ⟨κ, hκ, hsc⟩ hK SF hSF
  have hM := hC.models
  have hm : D.R.m - 1 + 1 = D.R.m := Nat.sub_add_cancel (le_trans one_le_two D.R.two_le_m)
  refine ⟨∏ i : Fin D.R.m, κ ((i : ℕ) + 1), Finset.prod_pos fun i _ => hκ _ (Nat.le_add_left _ _) i.2, fun t c z hz x hx => ?_⟩
  by_cases hx0 : x = 0
  · subst hx0
    exact ((congrArg (R.Th t) (LinearMap.map_zero _)).trans (LinearMap.map_zero _)).trans (smul_zero _).symm
  have hx' := eec_le (R := R) hSF t c hM.HE hx
  have hne : GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c ≠ ⊥ := fun h => by
    have h1 : R.HE.e x ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c :=
      (mem_rowPart (R := R) hM.HE).1 hx'
    rw [h, Submodule.mem_bot] at h1
    exact hx0 (hM.HE.1 (h1.trans (LinearMap.map_zero _).symm))
  have hall := (hsc t c hne).2
  let Λ : ℕ → ℝ := fun j => if h : j < D.R.m then κ (j + 1) * z ⟨j, h⟩ else 0
  have hΛ : ∀ j, j < D.R.m - 1 → GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.StepScalar R t c j (Λ j) := by
    intro j hj
    have hj' : j < D.R.m := by omega
    obtain ⟨B, hB, hL⟩ := hz ⟨j, hj'⟩
    obtain ⟨l, hl, hs⟩ := (hall B hB).1 j (by omega)
    rw [hl.unique hL] at hs
    simpa only [Λ, dif_pos hj'] using hs
  have hΛ' : GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.TopScalar R t c (Λ (D.R.m - 1)) := by
    have hj' : D.R.m - 1 < D.R.m := by omega
    obtain ⟨B, hB, hL⟩ := hz ⟨_, hj'⟩
    obtain ⟨l, hl, hs⟩ := (hall B hB).2
    simp only [hm] at hL
    rw [hl.unique hL] at hs
    simpa only [Λ, dif_pos hj', hm] using hs
  have hp : ∏ j ∈ Finset.range (D.R.m - 1 + 1), Λ j = (∏ i : Fin D.R.m, κ ((i : ℕ) + 1)) * ∏ i, z i := by
    rw [hm, ← Fin.prod_univ_eq_prod_range, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => dif_pos i.2
  refine eq_smul_of_inner (R.Th t) _ _ (fun u₁ h₁ u₂ h₂ z₁ z₂ => ?_) hx' hx0 (hK t c x hx')
  exact (inner_adjoint (R := R) hM hC.chain.Th hS t c Λ hΛ hΛ' h₁ h₂ z₁ z₂).trans (by rw [hp])

end GlobalTheory.ChainScalar

end
