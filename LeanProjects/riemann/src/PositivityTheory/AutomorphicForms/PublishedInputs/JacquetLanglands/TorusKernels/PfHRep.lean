import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolCap
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.UopSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RDual2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Polynomial UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd Matrix
open GlobalTheory.CuspRep (SmIrr Af invT finId pFin locGL finGL GA chiDet)

namespace UpperTheory.Esk.HeckeRepresentationSatake

section Proj
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}

theorem stable_iSup (S : Set (TR.CuspSub F a)) : TR.IsStable (⨆ π ∈ S, π.V) := fun o φ hφ => by
  refine Submodule.mem_comap.1 ((iSup₂_le (a := Submodule.comap (TR.act o) _) fun π hπ x hx => ?_) hφ)
  exact Submodule.mem_iSup_of_mem π (Submodule.mem_iSup_of_mem hπ (π.stable o x hx))

theorem proj {φ : TR.Sm F a} (h0 : φ ≠ 0) (h : φ ∈ ⨆ π : TR.CuspSub F a, π.V) :
    ∃ (π : TR.CuspSub F a) (ψ : TR.Sm F a), ψ ∈ π.V ∧ ψ ≠ 0 ∧ ∀ z : Module.End ℂ (TR.Sm F a),
      (∀ V, TR.IsStable V → ∀ x ∈ V, z x ∈ V) → ∀ c : ℂ, z φ = c • φ → z ψ = c • ψ := by
  classical
  obtain ⟨S, hS⟩ := Submodule.mem_iSup_iff_exists_finset.1 h
  induction S using Finset.induction_on with
  | empty => exact absurd (by simpa using hS) h0
  | insert π S hπ ih =>
    rw [Finset.iSup_insert] at hS
    have hs : TR.IsStable (⨆ π ∈ S, π.V) := stable_iSup (S : Set (TR.CuspSub F a))
    rcases π.irred (π.V ⊓ ⨆ π ∈ S, π.V) inf_le_left (fun o x hx => ⟨π.stable o x hx.1, hs o x hx.2⟩) with e | e
    · obtain ⟨ψ, h1, ψ', h2, e2⟩ := Submodule.mem_sup.1 hS
      by_cases h3 : ψ = 0
      · exact ih (by rw [← e2, h3, zero_add]; exact h2)
      refine ⟨π, ψ, h1, h3, fun z hz c hc => ?_⟩
      rw [← e2, map_add, smul_add] at hc
      have h4 : z ψ - c • ψ ∈ π.V ⊓ ⨆ π ∈ S, π.V := by
        refine ⟨sub_mem (hz _ π.stable _ h1) (π.V.smul_mem c h1), ?_⟩
        have : z ψ - c • ψ = c • ψ' - z ψ' := by linear_combination (norm := module) hc
        rw [this]
        exact sub_mem (Submodule.smul_mem _ c h2) (hz _ hs _ h2)
      rw [e, Submodule.mem_bot] at h4
      exact sub_eq_zero.1 h4
    · exact ih ((sup_le (inf_eq_left.1 e) le_rfl) hS)

theorem rt_lie (y : GL (Fin a) (TR.Rinf F)) (X : Matrix (Fin a) (Fin a) (TR.Rinf F)) :
    TR.rt F a (TR.infGL F a y) * TR.lie F a (TR.toL X) =
      TR.lie F a (TR.toL (y.val * X * (y⁻¹).val)) * TR.rt F a (TR.infGL F a y) := by
  refine LinearMap.ext fun φ => Subtype.ext <| funext fun g => ?_
  change fderiv ℝ (TR.chart φ.1 (g * TR.infGL F a y)) (TR.oneL F a) (TR.toL X) =
    fderiv ℝ (TR.chart (fun x => φ.1 (x * TR.infGL F a y)) g) (TR.oneL F a) (TR.toL (y.val * X * (y⁻¹).val))
  have hd : DifferentiableAt ℝ (TR.chart φ.1 g) (TR.toL y.val) :=
    (TR.contDiffAt_chart φ.2 g (TR.val_mem_invSet y)).differentiableAt (by simp)
  have e1 : TR.lmul (TR.toL y.val) (TR.oneL F a) = TR.toL y.val := mul_one y.val
  have e2 : TR.rmul (TR.toL y.val) (TR.oneL F a) = TR.toL y.val := one_mul y.val
  rw [TR.chart_mul, TR.chart_rt_inf, fderiv_comp _ (by rw [e1]; exact hd) (TR.lmul (TR.toL y.val)).differentiableAt,
    fderiv_comp _ (by rw [e2]; exact hd) (TR.rmul (TR.toL y.val)).differentiableAt, e1, e2,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  exact congrArg (fun Z => fderiv ℝ (TR.chart φ.1 g) (TR.toL y.val) (TR.toL Z)) (Units.inv_mul_cancel_right (y.val * X) y).symm

open Classical in
theorem lie_eq_sum (X : Matrix (Fin a) (Fin a) (TR.Rinf F)) :
    TR.lie F a (TR.toL X) = ∑ v, ∑ i, ∑ j, ((X i j v : ℝ) : ℂ) • TR.Eop v i j := by
  let L : Matrix (Fin a) (Fin a) (TR.Rinf F) →ₗ[ℝ] Module.End ℂ (TR.Sm F a) := TR.lie F a
  have e : X = ∑ v, ∑ i, ∑ j, X i j v • Matrix.single i j (Pi.single v 1 : TR.Rinf F) := by
    ext i j v
    simp [Matrix.sum_apply, Matrix.single_apply, ite_and, Pi.single_apply, ite_apply]
  change L X = _
  conv_lhs => rw [e]
  simp only [map_sum, map_smul]
  rfl

theorem rt_Eop (y : GL (Fin a) (TR.Rinf F)) (v : InfinitePlace F) (i j : Fin a) :
    TR.rt F a (TR.infGL F a y) * TR.Eop v i j =
      (∑ k, ∑ l, (((y.val k i v : ℝ) : ℂ) * (((y⁻¹).val j l v : ℝ) : ℂ)) • TR.Eop v k l) * TR.rt F a (TR.infGL F a y) := by
  classical
  rw [TR.Eop, rt_lie, lie_eq_sum, Finset.sum_eq_single v]
  · simp [Matrix.mul_apply, Matrix.single_apply, ite_and, ite_apply]
  · intro v' _ h
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, ite_apply, h]
  · simp

theorem cap_act (v : InfinitePlace F) (u : ℂ) (o : TR.Op F a) : TR.act o * TR.cap v u = TR.cap v u * TR.act o := by
  cases o with
  | fin k => exact GlobalTheory.CapAdInv.qdet_semiconj _ _ _ (fun i j => (TR.lie_rt_fin _ k).symm) _
  | cpt k =>
    set y := Unitary.toUnits k
    let f : TR.Rinf F →+* ℂ := Complex.ofRealHom.comp (Pi.evalRingHom _ v)
    have h := GlobalTheory.CapAdInv.qdet_semiconj _ _ _ (rt_Eop y v) (u + ((a : ℂ) - 1) / 2)
    have hQP : ((y⁻¹).val.map f) * (y.val.map f) = 1 := by
      rw [← Matrix.map_mul, Units.inv_mul]; simp
    exact h.trans (congrArg (· * _) (GlobalTheory.CapAdInv.qdet_ad _ (TR.glRel_Eop v) _ _ hQP (u + ((a : ℂ) - 1) / 2)))
  | lie X =>
    have h : ∀ v' i j, Commute (TR.Eop (a := a) v' i j) (TR.cap v u) := fun v' i j => by
      by_cases e : v' = v
      · subst e; exact (TR.cap_comm _ _ _ _).symm
      · exact GlobalTheory.CapAdInv.qdet_semiconj _ _ _ (fun k l => TR.Eop_comm e _ _ _ _) _
    change Commute (TR.lie F a (TR.toL (Matrix.of X))) _
    rw [lie_eq_sum]
    exact Commute.sum_left _ _ _ fun v' _ => Commute.sum_left _ _ _ fun i _ => Commute.sum_left _ _ _ fun j _ =>
      (h v' i j).smul_left _

theorem cap_all (π : TR.CuspSub F a) {ψ : TR.Sm F a} (h : ψ ∈ π.V) (h0 : ψ ≠ 0) (v : InfinitePlace F) (u c : ℂ)
    (hc : TR.cap v u ψ = c • ψ) : ∀ x ∈ π.V, TR.cap v u x = c • x := by
  rcases π.irred (π.V ⊓ Module.End.eigenspace (TR.cap v u) c) inf_le_left (fun o x hx => ⟨π.stable o x hx.1, by
    have := Module.End.mem_eigenspace_iff.1 hx.2
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [← Module.End.mul_apply, ← cap_act, Module.End.mul_apply, this, map_smul]⟩) with e | e
  · exact absurd (e.le ⟨h, Module.End.mem_eigenspace_iff.2 hc⟩) h0
  · exact fun x hx => Module.End.mem_eigenspace_iff.1 (e.ge hx).2

end Proj

section Loc
open GlobalTheory.LFun Formalism.UG

theorem hecke_eq_dc {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (a : G) (h : G → ℂ) (h1 : ∀ g : G, (g : G ⧸ K) ∈ MulAction.orbit K (a : G ⧸ K) → h g = 1)
    (h2 : ∀ g : G, (g : G ⧸ K) ∉ MulAction.orbit K (a : G ⧸ K) → h g = 0) (hf : {c : G ⧸ K | h c.out ≠ 0}.Finite) (x : V) :
    heckeVec ρ K h x = Hi.dc ρ K K a x := by
  classical
  have hfin : (MulAction.orbit K (a : G ⧸ K)).Finite := hf.subset fun c hc => by
    rw [Set.mem_setOf_eq, h1 _ (by rwa [QuotientGroup.out_eq'])]; exact one_ne_zero
  letI := hfin.fintype
  rw [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, ← finsum_eq_sum_of_fintype,
    finsum_set_coe_eq_finsum_mem (f := fun c : G ⧸ K => ρ c.out x), heckeVec]
  refine finsum_congr fun c => ?_
  by_cases hc : c ∈ MulAction.orbit K (a : G ⧸ K)
  · rw [h1 _ (by rwa [QuotientGroup.out_eq'])]; simp [hc]
  · rw [h2 _ (by rwa [QuotientGroup.out_eq'])]; simp [hc]

variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))

theorem iwahori_level_zero_eq : K1 w 0 = KGL w 2 := by
  ext g
  refine ⟨fun ⟨k, _, e⟩ => ⟨k, e⟩, fun ⟨k, e⟩ => ⟨k, ?_, e⟩⟩
  haveI : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) :=
    Ideal.Quotient.subsingleton_iff.2 (by simp)
  exact Subsingleton.elim _ _

theorem hecke_Tj {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V)
    (j : ℕ) (a : GL (Fin 2) (w.adicCompletion F)) (ha : a.val = diagJ 2 (atFin w (unif w) : w.adicCompletion F) j) (x : V) :
    heckeVec ρ (KGL w 2) (Tj ℂ 2 (Ov F w) (atFin w (unif w) : w.adicCompletion F) j) x = Hi.dc ρ (KGL w 2) (KGL w 2) a x := by
  refine hecke_eq_dc ρ _ a _ (fun g hg => ?_) (fun g hg => ?_)
    (Formalism.UG.P.finite_support_cosets (Final.GLintComm F w 2) (Tj_mem_hecke (unif_spec w) j).2) x
  · obtain ⟨k, hk⟩ := hg
    have h : ((k : GL (Fin 2) (w.adicCompletion F)) * a)⁻¹ * g ∈ KGL w 2 := QuotientGroup.eq.1 hk
    rw [Tj, Set.indicator_of_mem, Pi.one_apply]
    refine ⟨k, k.2, _, h, ?_⟩
    rw [← ha, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel_left]
  · rw [Tj, Set.indicator_of_notMem]
    rintro ⟨k, hk, k', hk', e⟩
    refine hg ⟨⟨k, hk⟩, ?_⟩
    rw [← ha, ← Units.val_mul, ← Units.val_mul] at e
    rw [Units.ext e]
    exact (QuotientGroup.mk_mul_of_mem (k * a) hk').symm

theorem sat_two {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V}
    {x : V} {B : Multiset ℂˣ} (h : IsSatVecGL w ρ x B) : ∃ α β : ℂˣ, B = {α, β} ∧
      Uop w ρ 0 x = ((((normV w : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (α + β)) • x ∧
      ρ (GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) x = ((α * β : ℂˣ) : ℂ) • x := by
  obtain ⟨α, β, rfl⟩ := Multiset.card_eq_two.1 h.2.2.1
  refine ⟨α, β, rfl, ?_, ?_⟩
  · rw [Uop, iwahori_level_zero_eq, ← hecke_Tj w ρ 1 _ (by ext i j; fin_cases i <;> fin_cases j <;> simp [aff, diagJ]),
      h.2.2.2 _ (unif_spec w) 1 (by norm_num)]
    congr 1
    rw [Complex.ofReal_cpow (by positivity)]
    have : qV F w = normV w := rfl
    simp [satEig, Multiset.esymm, Multiset.powersetCard_one, this]
    norm_num [add_comm]
  · have h2 := h.2.2.2 _ (unif_spec w) 2 le_rfl
    set z := GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))
    rw [hecke_Tj w ρ 2 z (by ext i j; fin_cases i <;> fin_cases j <;> simp [z, diagJ])] at h2
    have ho : ∀ q ∈ MulAction.orbit (KGL w 2) (z : _ ⧸ KGL w 2), q = z := by
      rintro _ ⟨k, rfl⟩
      change (((k : GL (Fin 2) (w.adicCompletion F)) * z : GL (Fin 2) (w.adicCompletion F)) : _ ⧸ KGL w 2) = _
      rw [← GlobalTheory.CuspRep.scalar_comm]
      exact QuotientGroup.mk_mul_of_mem _ k.2
    rw [(Hi.dcSum ℂ _ V ρ _ _ z ((Set.finite_singleton _).subset ho)).1 {z}
      (fun y hy => by rw [Finset.mem_singleton.1 hy]; exact MulAction.mem_orbit_self _)
      (fun q hq => ⟨z, ⟨Finset.mem_singleton_self _, (ho q hq).symm⟩, fun y hy => Finset.mem_singleton.1 hy.1⟩) x
      (GlobalTheory.LGrp.mem_fixed.1 h.2.1), Finset.sum_singleton] at h2
    rw [h2]
    simp [satEig, Multiset.esymm, Multiset.powersetCard_cons, Multiset.powersetCard_one]

theorem uop_map {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V} {ρ' : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) W}
    (f : V →ₗ[ℂ] W) (χ : (w.adicCompletion F)ˣ →* ℂˣ)
    (hf : ∀ g x, ρ' g (f x) = ((χ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • f (ρ g x)) (c : ℕ) (x : V)
    (hx : x ∈ Hi.fixd ρ (K1 w c)) (hx' : f x ∈ Hi.fixd ρ' (K1 w c)) :
    Uop w ρ' c (f x) = ((χ (atFin w (unif w)) : ℂˣ) : ℂ) • f (Uop w ρ c x) := by
  classical
  haveI := Formalism.UG.P.glint_finite_residueField w
  letI := Fintype.ofFinite (IsLocalRing.ResidueField (w.adicCompletionIntegers F))
  choose s hs using (IsLocalRing.residue_surjective (R := w.adicCompletionIntegers F))
  have hS : Set.BijOn (IsLocalRing.residue _) ((Finset.univ.image s : Finset _) : Set (w.adicCompletionIntegers F)) Set.univ := by
    refine ⟨fun _ _ => trivial, fun u hu u' hu' e => ?_, fun r _ => ⟨s r, by simp, hs r⟩⟩
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨r', -, rfl⟩ := Finset.mem_image.1 hu'
    rw [hs, hs] at e
    rw [e]
  have hd : ∀ u, GeneralLinearGroup.det (aff (atFin w (unif w)) u) = atFin w (unif w) := fun u =>
    Units.ext (by simp [aff, Matrix.det_fin_two])
  rw [(uopSum F w V ρ c x hx).2 _ hS, (uopSum F w W ρ' c _ hx').2 _ hS, map_add, map_sum, smul_add, Finset.smul_sum]
  simp only [hf, hd]
  congr 1
  split_ifs
  · rw [map_mul GeneralLinearGroup.det, map_inv, hd]
    congr 3
    exact Units.ext (by simp [sq])
  · simp

theorem fin_scalar (x : (w.adicCompletion F)ˣ) :
    finGL F 2 (locGL F 2 w (GeneralLinearGroup.scalar (Fin 2) x)) = GeneralLinearGroup.scalar (Fin 2) (localIdele F w x) := by
  have h := GlobalTheory.CuspRep.finId_det_locGL w (GeneralLinearGroup.scalar (Fin 1) x)
  rw [locGL, GlobalTheory.CuspRep.cornerGL_scalar] at h ⊢
  rw [finGL, GlobalTheory.CuspRep.cornerGL_scalar]
  congr 1
  exact (congrArg (finId F) (GlobalTheory.CuspRep.CG.det_oneByOne _)).symm.trans
    (h.trans (congrArg (localIdele F w) (GlobalTheory.CuspRep.CG.det_oneByOne _)))

theorem unit_det {c : ℕ} {k : GL (Fin 2) (w.adicCompletion F)} (hk : k ∈ K1 w c) :
    IsUnitAt w (GeneralLinearGroup.det k) := by
  obtain ⟨k, -, rfl⟩ := hk
  rw [IsUnitAt, GlobalTheory.CuspRep.det_map]
  exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 (Units.isUnit _)

end Loc

section Inf
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
open GlobalTheory.HeckeGal.Model GlobalTheory.Mem.Chr.CharModel

theorem expo_abs (s : ℝ) (v : InfinitePlace F) : TR.expo (absPow F s) v = s := by
  classical
  refine TR.expo_eq_of_exp _ v s fun t => ?_
  change Complex.exp (s * logNorm F (TR.infId F (TR.expU (Pi.single v t)))) = _
  have h1 : finPart F (TR.infId F (TR.expU (Pi.single v t))) = 1 := Units.ext (by
    change (1 : Af F) - 0 + 0 = 1
    simp)
  have h2 : ∀ u, ‖(infPart F (TR.infId F (TR.expU (Pi.single v t)))).val u‖ = Real.exp ((Pi.single v t : TR.Rinf F) u) := fun u => by
    have e : (infPart F (TR.infId F (TR.expU (Pi.single v t)))).val = TR.infEq F (TR.expU (Pi.single v t)).val := by
      change 1 - TR.infEq F 1 + TR.infEq F _ = _
      simp
    rw [e]
    exact (((InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal u)).symm.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal u)).symm)) _).trans
      (Real.norm_of_nonneg (Real.exp_pos _).le)
  rw [logNorm, h1, logFin_one, logInf]
  simp [h2, Pi.single_apply, InfinitePlace.mult, IsTotallyReal.isReal]

omit [IsTotallyReal F] in
theorem sign_abs (s : ℝ) (v : InfinitePlace F) : (absPow F s).locInf v (-1) = 1 := by
  refine Units.ext ?_
  set x := ReciprocityTheory.Neutral.Bridge.HCFR.infIdele F v (-1)
  have h0 : logNorm F 1 = 0 := by have := logNorm_mul F 1 1; rw [mul_one] at this; linarith
  have h := logNorm_mul F x x
  rw [← map_mul, neg_mul_neg, mul_one, map_one, h0] at h
  change Complex.exp (s * logNorm F x) = 1
  rw [show logNorm F x = 0 by linarith]
  simp

end Inf

section Sign
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def rot (θ : TR.Rinf F) : GL (Fin 2) (TR.Rinf F) where
  val := !![fun v => Real.cos (θ v), fun v => Real.sin (θ v); fun v => -Real.sin (θ v), fun v => Real.cos (θ v)]
  inv := !![fun v => Real.cos (θ v), fun v => -Real.sin (θ v); fun v => Real.sin (θ v), fun v => Real.cos (θ v)]
  val_inv := by
    ext i j v
    have := Real.sin_sq_add_cos_sq (θ v)
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> linarith
  inv_val := by
    ext i j v
    have := Real.sin_sq_add_cos_sq (θ v)
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> linarith

omit [NumberField F] [IsTotallyReal F] in
theorem rot_add (θ θ' : TR.Rinf F) : rot (θ + θ') = rot θ * rot θ' := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot, Matrix.mul_apply, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring

theorem sign_hol {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} {ω : HChar F} {φ : TR.Sm F 2} (hφ : IsHolV k c ω φ) (h0 : φ ≠ 0) (v : InfinitePlace F) :
    ((ω.locInf v (-1) : ℂˣ) : ℂ) = Complex.exp (Complex.I * (k v : ℂ) * Real.pi) := by
  classical
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (Subtype.ext (funext h))
  set e : TR.Rinf F := Pi.single v 1 with he
  have hr0 : rot ((0 : ℝ) • e) = 1 := by
    ext i j u
    fin_cases i <;> fin_cases j <;> simp [rot]
  have hd0 : ∀ g, HasDerivAt (fun t : ℝ => φ.1 (g * TR.infGL F 2 (rot (t • e)))) (Complex.I * (k v : ℂ) * φ.1 g) 0 := fun g => by
    have h1 := TR.hasDerivAt_curve φ g (fun t : ℝ => rot (t • e))
      (TR.toL (Matrix.single 0 1 e) - TR.toL (Matrix.single 1 0 e)) hr0 (by
        refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun u => ?_
        have hc := ((hasDerivAt_id (0 : ℝ)).mul_const (e u)).cos
        have hs := ((hasDerivAt_id (0 : ℝ)).mul_const (e u)).sin
        fin_cases i <;> fin_cases j
        · simpa [rot] using hc
        · simpa [rot] using hs
        · simpa [rot] using hs.fun_neg
        · simpa [rot] using hc)
    rw [← TR.lie_apply, map_sub] at h1
    exact h1.congr_deriv (congrArg (fun x : TR.Sm F 2 => x.1 g) (hφ.wt v))
  set f : ℝ → ℂ := fun t => φ.1 (g * TR.infGL F 2 (rot (t • e))) with hf
  have hd : ∀ t, HasDerivAt f (Complex.I * (k v : ℂ) * f t) t := fun t => by
    have h1 := HasDerivAt.comp_sub_const t t ((sub_self t).symm ▸ hd0 (g * TR.infGL F 2 (rot (t • e))))
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [hf]
    rw [mul_assoc, ← map_mul, ← rot_add, ← add_smul, add_sub_cancel]
  have hc : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f t * Complex.exp (-(Complex.I * (k v : ℂ) * t))) 0 t := fun t => by
    have h1 := (hd t).mul (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (Complex.I * (k v : ℂ))).fun_neg.cexp)
    exact h1.congr_deriv (by simp; ring)
  have h2 := is_const_of_deriv_eq_zero (fun t => (hc t).differentiableAt) (fun t => (hc t).deriv) Real.pi 0
  have hu : (1 - 2 * e) * (1 - 2 * e) = 1 := by
    funext w
    by_cases h : w = v
    · subst h; simp [he]; norm_num
    · simp [he, h]
  let u : (TR.Rinf F)ˣ := ⟨1 - 2 * e, 1 - 2 * e, hu, hu⟩
  have h3 : rot (Real.pi • e) = GeneralLinearGroup.scalar (Fin 2) u := by
    ext i j w
    by_cases h : w = v
    · subst h
      fin_cases i <;> fin_cases j <;> simp [rot, u, he] <;> norm_num
    · fin_cases i <;> fin_cases j <;> simp [rot, u, he, h]
  have h4 : Units.map (GlobalTheory.CuspRep.corner (TR.sInf F)) u = ReciprocityTheory.Neutral.Bridge.HCFR.infIdele F v (-1) := by
    refine Units.ext (Prod.ext (funext fun w => ?_) ?_)
    · change (1 - TR.infEq F 1 + TR.infEq F (1 - 2 * e)) w = Pi.mulSingle (M := fun w : InfinitePlace F => w.Completion) v (-1) w
      rw [map_one, sub_self, zero_add]
      change (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm ((1 - 2 * e) w) = _
      by_cases h : w = v
      · subst h
        rw [show (1 - 2 * e) w = -1 by simp [he]; norm_num]
        simp
      · simp [he, h]
    · change (1 : Af F) - 0 + 0 = 1
      simp
  simp only [hf, hr0, h3, TR.infGL, map_one, mul_one] at h2
  rw [GlobalTheory.CuspRep.cornerGL_scalar, h4, ← GlobalTheory.CuspRep.scalar_comm, hφ.cent] at h2
  rw [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one, Complex.exp_neg, mul_right_comm,
    mul_eq_right₀ hg, mul_inv_eq_one₀ (Complex.exp_ne_zero _)] at h2
  exact h2

end Sign

theorem sign_eq (k m : ℕ) : Complex.exp (Complex.I * ((k + 2 * m : ℕ) : ℂ) * Real.pi) = Complex.exp (Complex.I * (k : ℂ) * Real.pi) := by
  have e : Complex.I * ((k + 2 * m : ℕ) : ℂ) * Real.pi = Complex.I * (k : ℂ) * Real.pi + (m : ℕ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

end UpperTheory.Esk.HeckeRepresentationSatake
