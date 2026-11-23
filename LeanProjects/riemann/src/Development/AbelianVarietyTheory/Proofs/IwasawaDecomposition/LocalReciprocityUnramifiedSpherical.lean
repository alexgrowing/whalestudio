import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfOfNodupAlg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClassStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicPartSpannedBySplitPlaceLocalComponentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedVectorsNeBotOfMemSumIntertwiningRangesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.SphLoc

section Alg
variable {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]

theorem fixed_ne_bot_of_mem_iSup {ι : Type} [Finite ι] {σ : Representation ℂ G V} (hσ : σ.IsIrreducible)
    {ρ : Representation ℂ G X} (T : ι → σ.IntertwiningMap ρ) (K : Subgroup G) {f : X}
    (hf : f ∈ ⨆ j, LinearMap.range (T j).toLinearMap) (hf0 : f ≠ 0) (hK : ∀ k ∈ K, ρ k f = f) :
    GlobalTheory.PRep.fixed σ K ≠ ⊥ :=
  GlobalTheory.T.fixedVectors_ne_bot_of_mem_sum_intertwining_ranges hσ T K hf hf0 hK

end Alg

section Val
open ValuativeRel Filter Topology

variable {K K' : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']

theorem tendsto_pow_zero {x : K} (h : valuation K x < 1) : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' K).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero K) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_mem_nhds : {y : K' | valuation K' y < 1} ∈ 𝓝 (0 : K') := by
  refine (IsValuativeTopology.hasBasis_nhds_zero' K').mem_iff.2 ⟨1, one_ne_zero, fun y hy => hy⟩

theorem lt_one_of_map (i : K →+* K') (hi : Continuous i) {x : K} (h : valuation K x < 1) :
    valuation K' (i x) < 1 := by
  have h1 : Tendsto (fun n : ℕ => i x ^ n) atTop (𝓝 0) := by
    have := (hi.tendsto 0).comp (tendsto_pow_zero h)
    simpa [Function.comp_def, map_pow] using this
  obtain ⟨N, hN⟩ := (h1.eventually lt_one_mem_nhds).exists
  by_contra hc
  push Not at hc
  have : 1 ≤ valuation K' (i x ^ N) := by rw [map_pow]; exact one_le_pow₀ hc
  exact absurd hN (not_lt.2 this)

theorem le_one_of_map (i : K →+* K') (hi : Continuous i) {y : K} (h : valuation K' (i y) ≤ 1) :
    valuation K y ≤ 1 := by
  by_contra hc
  push Not at hc
  have hy : y ≠ 0 := fun h0 => by simp [h0] at hc
  have h1 : valuation K y⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hc
  have h2 := lt_one_of_map i hi h1
  rw [map_inv₀, map_inv₀] at h2
  have h0 : (0 : ValueGroupWithZero K') < valuation K' (i y) := by
    rw [zero_lt_iff, Valuation.ne_zero_iff]
    exact (map_ne_zero i).2 hy
  exact absurd h (not_le.2 ((inv_lt_one₀ h0).1 h2))

end Val

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem mem_Umax_of_mem_KO (s : SplitPlace L)
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hi : Continuous i) (x : GAf L n)
    (hx : TrivOutside {s.v} x)
    (hk : Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x) ∈ GlobalTheory.SplitWeil.KO (s.w.adicCompletion L) (Fin n)) :
    x ∈ Umax L n := by
  have key : ∀ y, ValuativeRel.valuation _ (i y) ≤ 1 → Valued.v y ≤ 1 := fun y hy =>
    (GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff s.v y).1 (le_one_of_map i.toRingHom hi hy)
  rw [GlobalTheory.SplitFlip.mem_KO_iff] at hk
  refine GlobalTheory.TSetFin.mem_Umax_of_loc s x hx (fun a b => key _ (hk.1 a b)) (fun a b => key _ ?_)
  have h2 := hk.2 a b
  rw [← map_inv, ← map_inv] at h2
  exact h2

theorem isSpherical_of_sphAt (π : NG.AutRep L n) (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (hσ : IsLocS π.S s σ) (hs : π.SphAt s.v) :
    GlobalTheory.SmGL.IsSpherical σ.ρ := by
  classical
  obtain ⟨i, T₀, hi, hic, -, -, -⟩ := id hσ
  obtain ⟨f, hf, hf0, hfix⟩ := hs
  have hI := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  choose lift hlift using fun A => (hI.2.2 A).exists
  have huniq : ∀ A x, TrivOutside {s.v} x → s.loc n x = A → x = lift A := fun A x hx e =>
    (hI.2.2 A).unique ⟨hx, e⟩ (hlift A)
  have hmul : ∀ A B, lift (A * B) = lift A * lift B := fun A B =>
    (huniq _ _ (GlobalTheory.TSetFin.triv_mul (hlift A).1 (hlift B).1) (by rw [map_mul, (hlift A).2, (hlift B).2])).symm
  have htriv1 : TrivOutside {s.v} (1 : GAf L n) := by
    intro v _
    show ((1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = 1
    rw [Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hone : lift 1 = 1 := (huniq _ _ htriv1 (map_one _)).symm
  let e : GL (Fin n) (s.w.adicCompletion L) →* GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) :=
    Matrix.GeneralLinearGroup.map i.symm.toRingHom
  have hloc : ∀ g, Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n (lift (e g))) = g := fun g => by
    rw [(hlift _).2]
    exact Units.ext (Matrix.ext fun a b => i.apply_symm_apply _)
  let ρX : Representation ℂ (GL (Fin n) (s.w.adicCompletion L)) (GAf L n → π.W) :=
    { toFun := fun g => NG.rt L n (lift (e g))
      map_one' := by
        simp only [map_one, hone]
        ext φ x
        simp [NG.rt]
      map_mul' := fun g h => by
        simp only [map_mul, hmul]
        ext φ x
        simp [NG.rt, mul_assoc] }
  have hiso : f ∈ NG.isoTyp π.ρ π.S := by
    unfold NG.isoTyp
    exact Submodule.mem_sSup_of_mem (show π.S ∈ {S' | NG.IsIrrRep π.ρ S' ∧ NG.IsoRep π.S S'} from
      ⟨π.irrS, LinearEquiv.refl ℂ _, fun _ _ _ e => e⟩) hf
  have h1 := GlobalTheory.T.isotypicPart_spanned_by_splitPlace_localComponent L n π.toAlgWt π.S π.irrS s σ hσ i hi hic hiso
  rw [iSup_subtype', Submodule.mem_iSup_iff_exists_finset] at h1
  obtain ⟨t, ht⟩ := h1
  rw [iSup_subtype'] at ht
  let Tm : {j // j ∈ t} → σ.ρ.IntertwiningMap ρX := fun j =>
    ⟨j.1.1, fun g => LinearMap.ext fun a => by
      have := j.1.2.2 (lift (e g)) (hlift _).1 a
      rw [hloc] at this
      exact this⟩
  refine fixed_ne_bot_of_mem_iSup σ.irr Tm (GlobalTheory.SplitWeil.KO _ (Fin n)) ht hf0 fun k hk => ?_
  show NG.rt L n (lift (e k)) f = f
  exact hfix _ (mem_Umax_of_mem_KO s i hi _ (hlift _).1 (by rw [hloc]; exact hk)) (hlift _).1

end

end GlobalTheory.SphLoc

end

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.SphLoc.main : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E) x,
    GlobalTheory.AutQuot.LocAt π s.w x → π.SphAt s.v → (GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 s.w) x).unr := by
  intro hL D π s x hx hs
  obtain ⟨s', σ, h, hσ, e⟩ := hx
  have hv : s'.v = s.v := HeightOneSpectrum.ext (by rw [← s'.w_under, ← s.w_under, h])
  have hsph := GlobalTheory.SphLoc.isSpherical_of_sphAt π s' σ hσ (hv ▸ hs)
  have hu := (GlobalTheory.CuspRep.ParLaws.unr_iff (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 s'.w)) σ).2 hsph
  have key : ∀ (u u' : HeightOneSpectrum (𝓞 D.host.E)) (_ : u = u') (a : GlobalTheory.LocGL.IrrGL (u.adicCompletion D.host.E))
      (b : GlobalTheory.LocGL.IrrGL (u'.adicCompletion D.host.E)), HEq a b →
      (GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 u) a).unr → (GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 u') b).unr := by
    intro u u' hu a b hab
    subst hu
    cases eq_of_heq hab
    exact id
  exact key _ _ h _ _ e hu

end
