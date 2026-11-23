import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsClassificationCuspidalSupport
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsDistinctCuspidalPairEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalMultiplicityProductZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsEmbeddingParIndOfJacquetNontrivial
import GroundTheory.AutomorphicForms.CuspidalSplittingIsotypic

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

namespace UpperTheory.Lit.Full.EmbCusp

section Abstract

variable {G H V Y : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]

def NoProper (τ : Representation ℂ G Y) (μ : Representation ℂ G V) : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module ℂ U] (ν : Representation ℂ G U) (f : μ.IntertwiningMap ν),
    Function.Surjective f → ¬ Function.Injective f → ¬ IsSubquotient τ ν

theorem exists_mk {μ : Representation ℂ G V} (K : Subrepresentation μ) :
    ∃ q : μ.IntertwiningMap (subQuot ⊤ K), Function.Surjective q ∧ ∀ v, q v = 0 ↔ v ∈ K.toSubmodule :=
  GlobalTheory.CompanionTheory.Hypotheses₂.TDSwap.exists_quot_map K ⊤ rfl (.refl _)

theorem exists_minimal {τ : Representation ℂ G Y} {μ : Representation ℂ G V} (hl : HasFiniteLength μ)
    (h : IsSubquotient τ μ) :
    ∃ K : Subrepresentation μ, IsSubquotient τ (subQuot ⊤ K) ∧ NoProper τ (subQuot ⊤ K) := by
  haveI := ((hasFiniteLength_iff_wellFounded μ).1 hl).1
  have h0 : IsSubquotient τ (subQuot ⊤ (⊥ : Subrepresentation μ)) := by
    obtain ⟨q, -, hq⟩ := exists_mk (⊥ : Subrepresentation μ)
    exact h.trans (.of_injective q ((injective_iff_map_eq_zero _).2 fun v hv => (hq v).1 hv))
  obtain ⟨K, hK, hmax⟩ := (wellFounded_gt (α := Subrepresentation μ)).has_min
    {K | IsSubquotient τ (subQuot ⊤ K)} ⟨⊥, h0⟩
  refine ⟨K, hK, fun U _ _ ν f hf hni hs => ?_⟩
  obtain ⟨p, hp, hpK⟩ := exists_mk K
  obtain ⟨p', hp', hpK'⟩ := exists_mk (f.comp p).ker
  obtain ⟨l, hl⟩ := exists_factor p'.toLinearMap (f.comp p).toLinearMap fun v hv => (hpK' v).1 hv
  have hl' : ∀ v, l (p' v) = f (p v) := hl
  let L : (subQuot ⊤ (f.comp p).ker).IntertwiningMap ν := ⟨l, fun g => LinearMap.ext fun x => by
    obtain ⟨v, rfl⟩ := hp' x
    show l (subQuot ⊤ (f.comp p).ker g (p' v)) = ν g (l (p' v))
    rw [← p'.isIntertwining, hl', hl', p.isIntertwining, f.isIntertwining]⟩
  have hL : Function.Surjective L := fun u => by
    obtain ⟨x, rfl⟩ := hf u
    obtain ⟨v, rfl⟩ := hp x
    exact ⟨p' v, hl' v⟩
  refine hmax _ (hs.trans (.of_surjective L hL)) (lt_of_le_not_ge (fun v hv => ?_) fun hle => hni ?_)
  · show f (p v) = 0
    rw [(hpK v).2 hv, map_zero]
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨v, rfl⟩ := hp x
    exact (hpK v).2 (hle (show v ∈ (f.comp p).ker from hx))

theorem NoProper.sub {τ : Representation ℂ G Y} {μ : Representation ℂ G V} (hτ : τ.IsIrreducible)
    (h : IsSubquotient τ μ) (hn : NoProper τ μ) (X : Subrepresentation μ) (hX : X ≠ ⊥) :
    IsSubquotient τ X.toRepresentation := by
  obtain ⟨q, hq, hqX⟩ := exists_mk X
  have h1 := hn _ _ q hq fun hi => hX (le_bot_iff.1 fun v hv =>
    (injective_iff_map_eq_zero _).1 hi v ((hqX v).2 hv))
  have h2 := jhMult_ne_zero_iff.2 h
  rw [jhMult_sub_add_quot hτ X, not_not.1 (mt jhMult_ne_zero_iff.1 h1), add_zero] at h2
  exact jhMult_ne_zero_iff.1 h2

theorem NoProper.central {τ : Representation ℂ G Y} {μ : Representation ℂ G V} (hτ : τ.IsIrreducible)
    (hl : HasFiniteLength μ) (h : IsSubquotient τ μ) (hn : NoProper τ μ) (z : G) (hz : ∀ g, g * z = z * g)
    (c : ℂ) (hc : ∀ y, τ z y = c • y) (v : V) : μ z v = c • v := by
  haveI := ((hasFiniteLength_iff_wellFounded μ).1 hl).2
  have hzg : ∀ g v, μ z (μ g v) = μ g (μ z v) := fun g v => by
    rw [← Module.End.mul_apply, ← map_mul, ← hz, map_mul, Module.End.mul_apply]
  let T : V →ₗ[ℂ] V := μ z - c • LinearMap.id
  have hT : ∀ v, T v = μ z v - c • v := fun v => rfl
  have hTg : ∀ g v, T (μ g v) = μ g (T v) := fun g v => by rw [hT, hT, hzg, map_sub, map_smul]
  let R : Subrepresentation μ := ⟨LinearMap.range T, by
    rintro g _ ⟨v, rfl⟩
    exact ⟨μ g v, hTg g v⟩⟩
  let f : μ.IntertwiningMap R.toRepresentation :=
    ⟨T.rangeRestrict, fun g => LinearMap.ext fun v => Subtype.ext (hTg g v)⟩
  by_cases hR : R = ⊥
  · have h1 : T v ∈ R.toSubmodule := ⟨v, rfl⟩
    rw [hR] at h1
    exact sub_eq_zero.1 h1
  exfalso
  refine hn _ _ f T.surjective_rangeRestrict (fun hi => ?_) (hn.sub hτ h R hR)
  obtain ⟨X, hX, -⟩ := (eq_bot_or_exists_atom_le R).resolve_left hR
  obtain ⟨a⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TDSwap.exists_sub_equiv X ⊥ rfl (.refl _)
  have hXi : X.toRepresentation.IsIrreducible :=
    GlobalTheory.Parabolic.isIrreducible_of_equiv a.symm (isIrreducible_subQuot hX.bot_covBy)
  obtain ⟨b⟩ := (hn.sub hτ h X hX.1).nonempty_equiv hτ hXi
  haveI := nontrivial_of_irreducible hXi
  obtain ⟨x, hx⟩ := exists_ne (0 : X.toSubmodule)
  have h1 : b.toLinearEquiv (X.toRepresentation z x) = τ z (b.toLinearEquiv x) :=
    Representation.IntertwiningMap.isIntertwining _ _ b.toIntertwiningMap z x
  rw [hc, ← map_smul] at h1
  have h2 : μ z x = c • (x : V) := congrArg Subtype.val (b.toLinearEquiv.injective h1)
  refine hx (Subtype.ext ((injective_iff_map_eq_zero _).1 hi x (Subtype.ext ?_)))
  exact sub_eq_zero.2 h2

end Abstract

theorem exists_sub_le {G V U W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    [AddCommGroup W] [Module ℂ W] {A : Representation ℂ G W} {ρ₁ : Representation ℂ G U}
    {ρ : Representation ℂ G V} (ι : ρ₁.IntertwiningMap ρ) (hι : Function.Injective ι) (h : IsSubquotient A ρ₁) :
    ∃ (S : Subrepresentation ρ) (f : S.toRepresentation.IntertwiningMap A), Function.Surjective f ∧
      ∀ v ∈ S.toSubmodule, ∃ u, ι u = v := by
  obtain ⟨S, f, hf⟩ := h
  let e := Submodule.equivMapOfInjective ι.toLinearMap hι S.toSubmodule
  refine ⟨subMap ι S, ⟨f.toLinearMap ∘ₗ e.symm.toLinearMap, fun g => LinearMap.ext fun v => ?_⟩,
    hf.comp e.symm.surjective, ?_⟩
  · obtain ⟨w, rfl⟩ := e.surjective v
    show f (e.symm _) = A g (f (e.symm (e w)))
    rw [e.symm_apply_apply, ← f.isIntertwining]
    congr 1
    refine e.symm_apply_eq.2 ?_
    exact Subtype.ext (ι.isIntertwining _ _ g w).symm
  · rintro _ ⟨v, -, rfl⟩
    exact ⟨v, rfl⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open GroundTheory.Automorphic.Parabolic (isotypicKernel isotypicPart mem_isotypicKernel) in

theorem exists_quot {G V Y W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup W] [Module ℂ W] {d : ℕ}
    (ψ : GL (Fin d) k →* G) (hψ : Continuous ψ)
    (hdec : ∀ g, ∃ (h : GL (Fin d) k) (g' : G), g = ψ h * g' ∧ ∀ x, ψ x * g' = g' * ψ x)
    {A : Representation ℂ (GL (Fin d) k) W} (hA : A.IsIrreducible) (hAc : IsCuspidal A)
    {ω : GL (Fin d) k → ℂ} (hω : GroundTheory.Automorphic.Parabolic.HasCentralChar A ω)
    {τ : Representation ℂ G Y} (hτ : τ.IsIrreducible)
    (hτω : ∀ z ∈ Subgroup.center (GL (Fin d) k), ∀ y, τ (ψ z) y = ω z • y)
    (hAτ : IsSubquotient A (τ.comp ψ : Representation ℂ (GL (Fin d) k) Y))
    {μ : Representation ℂ G V} (hμ : IsSmooth μ) (hl : HasFiniteLength μ) (h : IsSubquotient τ μ) :
    ∃ (U : Type) (_ : AddCommGroup U) (_ : Module ℂ U) (ν : Representation ℂ G U) (f : μ.IntertwiningMap ν),
      ν.IsIrreducible ∧ Function.Surjective f ∧
        IsSubquotient A (ν.comp ψ : Representation ℂ (GL (Fin d) k) U) := by
  obtain ⟨K, hK, hn⟩ := exists_minimal hl h
  obtain ⟨p, hp, -⟩ := exists_mk K
  generalize subQuot ⊤ K = μ' at hK hn p hp
  generalize_proofs at *
  have hl' : HasFiniteLength μ' := IsFiniteLength.of_surjective hl
    (f := Representation.IntertwiningMap.equivLinearMapAsModule μ μ' p) hp
  have hs' : IsSmooth (μ'.comp ψ : Representation ℂ (GL (Fin d) k) _) :=
    isSmooth_comp ((IsSubquotient.of_surjective p hp).isSmooth hμ) ψ hψ
  have hω' : GroundTheory.Automorphic.Parabolic.HasCentralChar (μ'.comp ψ : Representation ℂ (GL (Fin d) k) _) ω := by
    intro z hz v
    refine hn.central hτ hl' hK (ψ z) (fun g => ?_) _ (hτω z hz) v
    obtain ⟨x, g', rfl, hg'⟩ := hdec g
    rw [mul_assoc, ← hg', ← mul_assoc, ← map_mul, Subgroup.mem_center_iff.1 hz x, map_mul, mul_assoc]
  haveI := hA
  have hsc := GlobalTheory.CompanionTheory.CuspNotInd.isSupercuspidal_of_isCuspidal hAc
  let N : Subrepresentation μ' := ⟨isotypicKernel A (μ'.comp ψ), fun g v hv => by
    obtain ⟨x, g', rfl, hg'⟩ := hdec g
    rw [map_mul, Module.End.mul_apply]
    refine GroundTheory.Automorphic.Parabolic.isotypicKernel_stable (ρ := μ'.comp ψ) x (mem_isotypicKernel.2 fun F => ?_)
    let T : Representation.IntertwiningMap (μ'.comp ψ) (μ'.comp ψ) := ⟨μ' g', fun y => by
      show μ' g' * μ' (ψ y) = μ' (ψ y) * μ' g'
      rw [← map_mul, ← map_mul, hg']⟩
    exact mem_isotypicKernel.1 hv (F.comp T)⟩
  have hN : N = ⊥ := by
    by_contra hN
    let ι : Representation.IntertwiningMap (N.toRepresentation.comp ψ) (μ'.comp ψ) :=
      ⟨N.toSubmodule.subtype, fun _ => rfl⟩
    obtain ⟨S, f, hf, hS⟩ := exists_sub_le ι N.toSubmodule.injective_subtype
      (hAτ.trans (SupportUnique.isSubquotient_comp (hn.sub hτ hK N hN) ψ))
    refine GroundTheory.Automorphic.Parabolic.not_surjective_of_le_isotypicKernel hAc.1 hsc hω hs' hω' S
      (fun v hv => ?_) f hf
    obtain ⟨u, rfl⟩ := hS v hv
    exact u.2
  have hE : isotypicPart A (μ'.comp ψ) = ⊤ := by
    have h1 := GroundTheory.Automorphic.Parabolic.isCompl_isotypicPart_isotypicKernel hAc.1 hsc hω hs' hω'
    have h2 : isotypicKernel A (μ'.comp ψ) = ⊥ := congrArg Subrepresentation.toSubmodule hN
    rw [h2] at h1
    exact eq_top_of_isCompl_bot h1
  haveI := ((hasFiniteLength_iff_wellFounded μ').1 hl').1
  have hne : (⊥ : Subrepresentation μ') ≠ ⊤ := by
    intro hbt
    obtain ⟨S, f, hf⟩ := hK
    haveI := nontrivial_of_irreducible hτ
    obtain ⟨y, hy⟩ := exists_ne (0 : Y)
    obtain ⟨v, rfl⟩ := hf y
    have h1 : v.1 ∈ (⊥ : Subrepresentation μ').toSubmodule := by rw [hbt]; trivial
    exact hy (by rw [show v = 0 from Subtype.ext h1, map_zero])
  obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subrepresentation μ')).resolve_left hne
  obtain ⟨q, hq, hqM⟩ := exists_mk M
  refine ⟨_, _, _, subQuot ⊤ M, q.comp p, isIrreducible_subQuot hM.covBy_top, hq.comp hp, ?_⟩
  by_contra hcon
  refine hM.1 (top_le_iff.1 fun v _ => ?_)
  have h1 : isotypicPart A (μ'.comp ψ) ≤ M.toSubmodule := by
    refine iSup_le fun t => ?_
    rintro _ ⟨w, rfl⟩
    rcases Representation.IsIrreducible.injective_or_eq_zero ((compMap q ψ).comp t) with h2 | h2
    · exact absurd (.of_injective _ h2) hcon
    · exact (hqM _).1 (congrArg (fun F : A.IntertwiningMap ((subQuot ⊤ M).comp ψ) => F w) h2)
  exact h1 (hE ▸ Submodule.mem_top)

theorem exists_central (y : IrrGL k) :
    ∃ c : GL (Fin y.1) k → ℂ, GroundTheory.Automorphic.Parabolic.HasCentralChar y.rep c := by
  have h := exists_smooth_hasCentralChar (k := k) (n := Fin y.1) (π := y.rep) y.2.rep.smooth y.2.rep.irr
  obtain ⟨ω, -, hω⟩ := h
  have hex : ∀ z : GL (Fin y.1) k, ∃ c : ℂ, z ∈ Subgroup.center (GL (Fin y.1) k) →
      ∀ v, y.rep z v = c • v := by
    intro z
    by_cases hz : z ∈ Subgroup.center (GL (Fin y.1) k)
    · have hz' := hz
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz'
      obtain ⟨t, rfl⟩ := hz'
      exact ⟨ω t, fun _ => hω t⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose c hc using hex
  exact ⟨c, hc⟩

theorem exists_jac_quot (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (x : IrrGL k)
    {s : ℕ} (q : Fin s → IrrGL k) (hq : ∑ a, (q a).1 = x.1) (i : Fin s) (hi : (q i).IsCusp)
    (h : jm q hq x.rep ≠ 0) :
    ∃ (U : Type) (_ : AddCommGroup U) (_ : Module ℂ U) (ν : Representation ℂ (Levi k fun a => Fin (q a).1) U)
      (f : (jac (stdBlocks (fun a => (q a).1) hq) x.rep).IntertwiningMap ν),
      ν.IsIrreducible ∧ Function.Surjective f ∧
        IsSubquotient (q i).rep (ν.comp (MonoidHom.mulSingle (fun a => GL (Fin (q a).1) k) i) :
          Representation ℂ (GL (Fin (q i).1) k) U) := by
  refine (exists_central (q i)).elim fun c hc => ?_
  let e := stdBlocks (fun a => (q a).1) hq
  let ψ : GL (Fin (q i).1) k →* Levi k (fun a => Fin (q a).1) :=
    MonoidHom.mulSingle (fun a => GL (Fin (q a).1) k) i
  have h1 : Continuous ψ := by
    refine continuous_pi fun a => ?_
    by_cases ha : a = i
    · subst ha
      simpa [ψ] using continuous_id'
    · simpa [ψ, Pi.mulSingle_eq_of_ne ha] using continuous_const
  have h2 : ∀ g : Levi k (fun a => Fin (q a).1), ∃ (h : GL (Fin (q i).1) k) (g' : Levi k (fun a => Fin (q a).1)),
      g = ψ h * g' ∧ ∀ t, ψ t * g' = g' * ψ t := fun g => ⟨g i, Function.update g i 1, by
      funext a
      by_cases ha : a = i
      · subst ha
        simp [ψ]
      · simp [ψ, Pi.mulSingle_eq_of_ne ha, Function.update_of_ne ha], fun t => by
      funext a
      by_cases ha : a = i
      · subst ha
        simp [ψ]
      · simp [ψ, Pi.mulSingle_eq_of_ne ha]⟩
  have h3 : (piTensor fun a => (q a).rep).IsIrreducible :=
    GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k (Fin s) (fun a => Fin (q a).1) fun a => (q a).2.rep
  have h4 : ∀ z ∈ Subgroup.center (GL (Fin (q i).1) k), ∀ y, (piTensor fun a => (q a).rep) (ψ z) y = c z • y := by
    intro z hz y
    have h1 := GlobalTheory.CompanionTheory.Hypotheses₂.TDSwap.piTensor_scalar (fun a => (q a).rep) (ψ z)
      (fun a => if a = i then c z else 1) (fun a v => by
        by_cases ha : a = i
        · subst ha
          simpa [ψ] using hc z hz v
        · simp [ψ, Pi.mulSingle_eq_of_ne ha, ha]) y
    simpa using h1
  have h5 : IsSubquotient (q i).rep ((piTensor fun a => (q a).rep).comp ψ : Representation ℂ _ _) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun a => (q a).rep) (fun a => (q a).2.rep.irr) i
  have h6 : IsSmooth (jac e x.rep) := isSmooth_jac e x.2.rep.smooth
  have h7 : HasFiniteLength (jac e x.rep) :=
    (hBZ k).2.1 _ _ _ e _ x.rep x.2.rep.smooth (hasFiniteLength_of_isIrreducible x.2.rep.irr)
  have h8 : IsSubquotient (piTensor fun a => (q a).rep) (jac e x.rep) := jhMult_ne_zero_iff.1 h
  have h9 : GroundTheory.Automorphic.Parabolic.HasCentralChar (q i).rep c := hc
  exact exists_quot ψ h1 h2 (A := (q i).rep) (q i).2.rep.irr hi.2 h9 h3 h4 h5 h6 h7 h8

def EmbIn (x : IrrGL k) {s : ℕ} (y : Fin s → IrrGL k) : Prop :=
  ∃ (hd : ∑ a, (y a).1 = x.1) (f : x.rep.IntertwiningMap (prodIrr y hd)), Function.Injective f

theorem exists_emb (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (x : IrrGL k)
    {s : ℕ} (q : Fin s → IrrGL k) (hq : ∑ a, (q a).1 = x.1) (i : Fin s) (hi : (q i).IsCusp)
    (h : jm q hq x.rep ≠ 0) :
    ∃ y : Fin s → IrrGL k, y i = q i ∧ EmbIn x y := by
  let e := stdBlocks (fun a => (q a).1) hq
  let π : GlobalTheory.SplitRead.Irr k x.1 := { V := x.2.rep.V, π := x.rep, smooth := x.2.rep.smooth, irr := x.2.rep.irr }
  obtain ⟨U, _, _, ν, f, hν, hf, hsub⟩ := exists_jac_quot hBZ x q hq i hi h
  have h1 := GlobalTheory.injective_of_jacquet_surjective π e hν f hf
  have h2 := GlobalTheory.CuspSupportExist.L_tens hG k _ π s _ e U ν hν (.of_surjective f hf)
  obtain ⟨φ, hφ⟩ := h1
  obtain ⟨σ, hσ⟩ := h2
  have hirr : (piTensor fun a => (σ a).π).IsIrreducible :=
    GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k (Fin s) (fun a => Fin (q a).1) fun a => (σ a).toIrrRep
  have h3 := hσ.nonempty_equiv hν hirr
  obtain ⟨ε⟩ := h3
  have h4 : IsSubquotient (q i).rep (σ i).π :=
    SupportUnique.isSubquotient_factor (fun a => (σ a).π) i (q i).2.rep.irr
      (hsub.trans (SupportUnique.isSubquotient_comp hσ _))
  have h5 : IrrGL.of (σ i).π (σ i).smooth (σ i).irr = IrrGL.of (q i).rep (q i).2.rep.smooth (q i).2.rep.irr :=
    IrrGL.of_eq_of.2 (h4.nonempty_equiv (q i).2.rep.irr (σ i).irr)
  rw [IrrGL.of_rep] at h5
  let χ₁ : (parInd e ν).Equiv (multiProd e fun a => (σ a).π) := parIndEquiv e ε.symm
  let χ := χ₁.trans (prodIrrEquiv hq (fun a => (σ a).π) (fun a => (σ a).smooth) fun a => (σ a).irr)
  refine ⟨fun a => IrrGL.of (σ a).π (σ a).smooth (σ a).irr, h5, hq, ?_⟩
  exact ⟨χ.toIntertwiningMap.comp φ, χ.toLinearEquiv.injective.comp hφ⟩

end UpperTheory.Lit.Full.EmbCusp

theorem UpperTheory.Lit.Full.embL :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL k) (q : Fin 2 → IrrGL k) (hq : ∑ a, (q a).1 = x.1), (q 0).IsCusp → jm q hq x.rep ≠ 0 → ∃ z, Emb x (q 0) z := by
  intro hG hBZ k _ _ _ _ x q hq hc h
  obtain ⟨y, hy, hf⟩ := UpperTheory.Lit.Full.EmbCusp.exists_emb hG hBZ x q hq 0 hc h
  obtain ⟨a, b, rfl⟩ : ∃ a b, y = ![a, b] := ⟨y 0, y 1, by
    funext j
    fin_cases j <;> rfl⟩
  obtain rfl : a = q 0 := hy
  exact ⟨b, hf⟩
