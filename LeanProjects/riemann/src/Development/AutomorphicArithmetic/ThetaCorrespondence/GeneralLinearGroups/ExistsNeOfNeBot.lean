import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsDistinctCuspidalPairEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalMultiplicityProductZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsEmbeddingParIndOfJacquetNontrivial
import GroundTheory.AutomorphicForms.CuspidalSplittingIsotypic

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

namespace UpperTheory.Lit.Full.EmbR

section Abstract

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

private def quo (ν : Representation ℂ G V) (X : Subrepresentation ν) : Representation ℂ G (V ⧸ X.toSubmodule) :=
  ν.quotient X.toSubmodule fun g _ hv => X.apply_mem_toSubmodule g hv

private def quoMap (ν : Representation ℂ G V) (X : Subrepresentation ν) : ν.IntertwiningMap (quo ν X) :=
  ⟨X.toSubmodule.mkQ, fun _ => rfl⟩

private theorem quoMap_surj (ν : Representation ℂ G V) (X : Subrepresentation ν) :
    Function.Surjective (quoMap ν X) := Submodule.mkQ_surjective _

private theorem quoMap_eq_zero (ν : Representation ℂ G V) (X : Subrepresentation ν) (v : V) :
    quoMap ν X v = 0 ↔ v ∈ X.toSubmodule := Submodule.Quotient.mk_eq_zero _

private theorem exists_ne_of_ne_bot {ν : Representation ℂ G V} {X : Subrepresentation ν} (h : X ≠ ⊥) :
    ∃ v ∈ X.toSubmodule, v ≠ 0 :=
  (Submodule.ne_bot_iff _).1 fun e => h (Subrepresentation.toSubmodule_injective e)

private theorem quoMap_not_inj {ν : Representation ℂ G V} {X : Subrepresentation ν} (h : X ≠ ⊥) :
    ¬ Function.Injective (quoMap ν X) := fun hi => by
  obtain ⟨v, hv, h0⟩ := exists_ne_of_ne_bot h
  exact h0 ((injective_iff_map_eq_zero _).1 hi v ((quoMap_eq_zero ν X v).2 hv))

private theorem irr_of_atom {ν : Representation ℂ G V} {X : Subrepresentation ν} (h : IsAtom X) :
    X.toRepresentation.IsIrreducible := by
  obtain ⟨v, hv, h0⟩ := exists_ne_of_ne_bot h.1
  haveI : Nontrivial (Subrepresentation X.toRepresentation) := ⟨⊥, ⊤, fun e => by
    have h1 : (⟨v, hv⟩ : X.toSubmodule) ∈ (⊥ : Subrepresentation X.toRepresentation).toSubmodule := e ▸ trivial
    exact h0 (congrArg Subtype.val (show (⟨v, hv⟩ : X.toSubmodule) = 0 from h1))⟩
  refine ⟨fun S => ?_⟩
  let T : Subrepresentation ν := ⟨S.toSubmodule.map X.toSubmodule.subtype, by
    rintro g _ ⟨w, hw, rfl⟩
    exact ⟨X.toRepresentation g w, S.apply_mem_toSubmodule g hw, rfl⟩⟩
  have hT : T ≤ X := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  rcases h.le_iff.1 hT with e | e
  · refine Or.inl (le_bot_iff.1 fun w hw => ?_)
    have h1 : (w : V) ∈ T.toSubmodule := ⟨w, hw, rfl⟩
    rw [e] at h1
    exact Subtype.ext h1
  · refine Or.inr (top_le_iff.1 fun w _ => ?_)
    obtain ⟨u, hu, h1⟩ : (w : V) ∈ T.toSubmodule := by rw [e]; exact w.2
    rwa [← Subtype.ext h1]

private theorem scalar_of_subquot {σ : Representation ℂ G W} {ν : Representation ℂ G V} (h : IsSubquotient σ ν)
    {g : G} {c : ℂ} (hc : ∀ v, ν g v = c • v) (w : W) : σ g w = c • w := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨s, rfl⟩ := hf w
  rw [← f.isIntertwining, ← map_smul]
  exact congrArg f (Subtype.ext (hc s))

private theorem exists_min_quot (ψ : H →* G) (A : Representation ℂ H W) {μ : Representation ℂ G V}
    (hl : HasFiniteLength μ) (hA : IsSubquotient A (μ.comp ψ : Representation ℂ H V)) :
    ∃ (U : Type) (_ : AddCommGroup U) (_ : Module ℂ U) (ν : Representation ℂ G U) (q : μ.IntertwiningMap ν),
      Function.Surjective q ∧ IsSubquotient A (ν.comp ψ : Representation ℂ H U) ∧
      ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ G Y) (f : ν.IntertwiningMap τ),
        Function.Surjective f → IsSubquotient A (τ.comp ψ : Representation ℂ H Y) → Function.Injective f := by
  haveI := ((hasFiniteLength_iff_wellFounded μ).1 hl).1
  let P : Subrepresentation μ → Prop := fun K => ∃ (U : Type) (_ : AddCommGroup U) (_ : Module ℂ U)
    (ν : Representation ℂ G U) (q : μ.IntertwiningMap ν), Function.Surjective q ∧
      IsSubquotient A (ν.comp ψ : Representation ℂ H U) ∧ q.ker = K
  obtain ⟨K, ⟨U, _, _, ν, q, hq, hν, rfl⟩, hmax⟩ := exists_maximal_of_wellFoundedGT P
    ⟨_, V, _, _, μ, .id μ, Function.surjective_id, hA, rfl⟩
  refine ⟨U, _, _, ν, q, hq, hν, fun Y _ _ τ f hf hτ => (injective_iff_map_eq_zero _).2 fun u hu => ?_⟩
  obtain ⟨v, rfl⟩ := hq u
  have h1 : (f.comp q).ker ≤ q.ker := hmax ⟨Y, _, _, τ, f.comp q, hf.comp hq, hτ, rfl⟩ fun w hw => by
    show f (q w) = 0
    rw [show q w = 0 from hw, map_zero]
  exact h1 (show v ∈ (f.comp q).ker from hu)

private theorem wf_of_surj {μ : Representation ℂ G V} {ν : Representation ℂ G W} (hl : HasFiniteLength μ)
    (q : μ.IntertwiningMap ν) (hq : Function.Surjective q) : WellFoundedLT (Subrepresentation ν) := by
  haveI := ((hasFiniteLength_iff_wellFounded μ).1 hl).2
  refine StrictMono.wellFoundedLT (f := subComap q) fun S T h => lt_of_le_of_ne (subComap_mono q h.le) fun e => ?_
  refine h.not_ge fun w hw => ?_
  obtain ⟨v, rfl⟩ := hq w
  have h1 : v ∈ (subComap q T).toSubmodule := hw
  rw [← e] at h1
  exact h1

section Min

variable {ψ : H →* G} {A : Representation ℂ H W} {ν : Representation ℂ G V} (hAi : A.IsIrreducible)
  (hA : IsSubquotient A (ν.comp ψ : Representation ℂ H V))
  (hmin : ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ G Y) (f : ν.IntertwiningMap τ),
    Function.Surjective f → IsSubquotient A (τ.comp ψ : Representation ℂ H Y) → Function.Injective f)

include hAi hA hmin in
private theorem sub_has {X : Subrepresentation ν} (hX : X ≠ ⊥) :
    IsSubquotient A (X.toRepresentation.comp ψ : Representation ℂ H _) := by
  have h := jhMult_exact (σ := A)
    (compMap (⟨X.toSubmodule.subtype, fun _ => rfl⟩ : X.toRepresentation.IntertwiningMap ν) ψ)
    (compMap (quoMap ν X) ψ) hAi Subtype.val_injective (quoMap_surj ν X)
    (fun u => (quoMap_eq_zero ν X _).2 u.2) fun v hv => ⟨⟨v, (quoMap_eq_zero ν X _).1 hv⟩, rfl⟩
  have h2 : jhMult A ((quo ν X).comp ψ : Representation ℂ H _) = 0 := by
    by_contra h3
    exact quoMap_not_inj hX (hmin _ _ _ (quoMap_surj ν X) (jhMult_ne_zero_iff.1 h3))
  rw [h2, add_zero] at h
  exact jhMult_ne_zero_iff.1 (h ▸ jhMult_ne_zero_iff.2 hA)

include hAi hA hmin in
private theorem scalar_all {z : G} (hz : ∀ g, g * z = z * g) {c : ℂ} {v₀ : V} (h0 : v₀ ≠ 0)
    (hv₀ : ν z v₀ = c • v₀) (v : V) : ν z v = c • v := by
  have hzg : ∀ g v, ν z (ν g v) = ν g (ν z v) := fun g v => by
    rw [← Module.End.mul_apply, ← map_mul, ← hz, map_mul, Module.End.mul_apply]
  let T₀ : V →ₗ[ℂ] V := ν z - c • LinearMap.id
  have hT₀ : ∀ v, T₀ v = ν z v - c • v := fun v => rfl
  have hTg : ∀ g v, T₀ (ν g v) = ν g (T₀ v) := fun g v => by rw [hT₀, hT₀, hzg, map_sub, map_smul]
  let R : Subrepresentation ν := ⟨LinearMap.range T₀, by
    rintro g _ ⟨w, rfl⟩
    exact ⟨ν g w, hTg g w⟩⟩
  let T : ν.IntertwiningMap R.toRepresentation :=
    ⟨T₀.rangeRestrict, fun g => LinearMap.ext fun w => Subtype.ext (hTg g w)⟩
  by_cases hR : R = ⊥
  · have h1 : T₀ v ∈ R.toSubmodule := ⟨v, rfl⟩
    rw [hR] at h1
    exact sub_eq_zero.1 h1
  · have hi := hmin _ _ T T₀.surjective_rangeRestrict (sub_has hAi hA hmin hR)
    exact absurd ((injective_iff_map_eq_zero _).1 hi v₀ (Subtype.ext (sub_eq_zero.2 hv₀))) h0

include hAi hmin in
private theorem range_le {X : Subrepresentation ν} (hX : X ≠ ⊥)
    (ι : A.IntertwiningMap (ν.comp ψ : Representation ℂ H V)) (w : W) : ι w ∈ X.toSubmodule := by
  rcases Representation.IsIrreducible.injective_or_eq_zero ((compMap (quoMap ν X) ψ).comp ι) with h | h
  · exact absurd (hmin _ _ _ (quoMap_surj ν X) (.of_injective _ h)) (quoMap_not_inj hX)
  · exact (quoMap_eq_zero ν X _).1 (congrArg (fun F => F w) h)

include hAi hmin in
private theorem map_eq_zero' {X : Subrepresentation ν} (hX : X ≠ ⊥)
    (F : Representation.IntertwiningMap (ν.comp ψ : Representation ℂ H V) A) (hF : ∀ v ∈ X.toSubmodule, F v = 0)
    (v : V) : F v = 0 := by
  let F' : Representation.IntertwiningMap ((quo ν X).comp ψ : Representation ℂ H _) A :=
    ⟨X.toSubmodule.liftQ F.toLinearMap hF, fun h => Submodule.linearMap_qext _ (LinearMap.ext fun u =>
      F.isIntertwining _ _ h u)⟩
  rcases Representation.IsIrreducible.surjective_or_eq_zero F' with h | h
  · exact absurd (hmin _ _ _ (quoMap_surj ν X) (.of_surjective _ h)) (quoMap_not_inj hX)
  · exact congrArg (fun F => F (Submodule.Quotient.mk v)) h

end Min

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open GroundTheory.Automorphic.Parabolic (isotypicPart isotypicKernel) in

private theorem exists_irr_quot {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] {b : ℕ} (ψ : GL (Fin b) k →* G) (hψ : Continuous ψ)
    (hdec : ∀ g, ∃ (h : GL (Fin b) k) (g' : G), g = ψ h * g' ∧ ∀ x, ψ x * g' = g' * ψ x)
    {A : Representation ℂ (GL (Fin b) k) W} (hAi : A.IsIrreducible) (hAc : IsCuspidal A)
    {μ : Representation ℂ G V} (hs : IsSmooth μ) (hl : HasFiniteLength μ)
    (hA : IsSubquotient A (μ.comp ψ : Representation ℂ _ V))
    (hsc : ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ G Y), τ.IsIrreducible →
      IsSubquotient τ μ → ∀ z ∈ Subgroup.center (GL (Fin b) k), ∃ c : ℂ, ∀ y, τ (ψ z) y = c • y) :
    ∃ (U : Type) (_ : AddCommGroup U) (_ : Module ℂ U) (ν : Representation ℂ G U) (q : μ.IntertwiningMap ν),
      Function.Surjective q ∧ IsSubquotient A (ν.comp ψ : Representation ℂ _ U) ∧ ν.IsIrreducible := by
  classical
  obtain ⟨U, _, _, ν, q, hq, hν, hmin⟩ := exists_min_quot ψ A hl hA
  refine ⟨U, _, _, ν, q, hq, hν, ?_⟩
  haveI := wf_of_surj hl q hq
  haveI := Model.nontrivial_of_isIrreducible hAi
  have hνs : IsSmooth ν := (IsSubquotient.of_surjective q hq).isSmooth hs
  have hbt : (⊤ : Subrepresentation ν) ≠ ⊥ := by
    intro e
    obtain ⟨S, f, hf⟩ := hν
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    obtain ⟨s, rfl⟩ := hf w
    have h1 : (s : U) ∈ (⊤ : Subrepresentation ν).toSubmodule := trivial
    rw [e] at h1
    exact hw (by rw [show s = 0 from Subtype.ext h1, map_zero])
  obtain ⟨X, hX, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation ν)).resolve_left hbt
  have hXμ : IsSubquotient X.toRepresentation μ :=
    (IsSubquotient.of_injective (⟨X.toSubmodule.subtype, fun _ => rfl⟩ : X.toRepresentation.IntertwiningMap ν)
      Subtype.val_injective).trans (.of_surjective q hq)
  have hcen : ∀ z ∈ Subgroup.center (GL (Fin b) k), ∃ c : ℂ, ∀ u, ν (ψ z) u = c • u := by
    intro z hz
    obtain ⟨c, hc⟩ := hsc _ _ (irr_of_atom hX) hXμ z hz
    obtain ⟨v, hv, h0⟩ := exists_ne_of_ne_bot hX.1
    refine ⟨c, scalar_all hAi hν hmin (fun g => ?_) h0 (congrArg Subtype.val (hc ⟨v, hv⟩))⟩
    obtain ⟨h, g', rfl, hg'⟩ := hdec g
    rw [mul_assoc, ← hg', ← mul_assoc, ← map_mul, Subgroup.mem_center_iff.1 hz h, map_mul, mul_assoc]
  choose c hc using hcen
  let ω : GL (Fin b) k → ℂ := fun z => if h : z ∈ Subgroup.center (GL (Fin b) k) then c z h else 0
  have hων : GroundTheory.Automorphic.Parabolic.HasCentralChar (ν.comp ψ : Representation ℂ _ U) ω := fun z hz u => by
    simp only [ω, dif_pos hz]
    exact hc z hz u
  have hωA : GroundTheory.Automorphic.Parabolic.HasCentralChar A ω := fun z hz =>
    scalar_of_subquot hν (hων z hz)
  have hsup := GlobalTheory.CompanionTheory.CuspNotInd.isSupercuspidal_of_isCuspidal hAc
  have hsm : IsSmooth (ν.comp ψ : Representation ℂ _ U) := isSmooth_comp hνs ψ hψ
  haveI := hAi
  have hco := GroundTheory.Automorphic.Parabolic.isCompl_isotypicPart_isotypicKernel hAc.1 hsup hωA hsm hων
  let K : Subrepresentation ν := ⟨isotypicKernel A (ν.comp ψ : Representation ℂ _ U), fun g u hu => by
    obtain ⟨h, g', rfl, hg'⟩ := hdec g
    rw [map_mul, Module.End.mul_apply]
    refine GroundTheory.Automorphic.Parabolic.isotypicKernel_stable (ρ := (ν.comp ψ : Representation ℂ _ U)) h ?_
    rw [GroundTheory.Automorphic.Parabolic.mem_isotypicKernel] at hu ⊢
    intro F
    refine hu ⟨F.toLinearMap ∘ₗ ν g', fun x => LinearMap.ext fun w => ?_⟩
    show F (ν g' (ν (ψ x) w)) = A x (F (ν g' w))
    rw [← F.isIntertwining, ← Module.End.mul_apply, ← map_mul, ← hg', map_mul, Module.End.mul_apply]
    rfl⟩
  have hK : K = ⊥ := by
    by_contra hK
    obtain ⟨S, f, hf⟩ := hν
    refine GroundTheory.Automorphic.Parabolic.not_surjective_of_le_isotypicKernel hAc.1 hsup hωA hsm hων S
      (fun u _ => GroundTheory.Automorphic.Parabolic.mem_isotypicKernel.2 fun F => ?_) f hf
    exact map_eq_zero' hAi hmin hK F (fun v hv => GroundTheory.Automorphic.Parabolic.mem_isotypicKernel.1 hv F) u
  have hK' : isotypicKernel A (ν.comp ψ : Representation ℂ _ U) = ⊥ := congrArg Subrepresentation.toSubmodule hK
  rw [hK'] at hco
  have hle : isotypicPart A (ν.comp ψ : Representation ℂ _ U) ≤ X.toSubmodule := iSup_le fun ι => by
    rintro _ ⟨w, rfl⟩
    exact range_le hAi hmin hX.1 ι w
  rw [eq_top_of_isCompl_bot hco] at hle
  obtain rfl : X = ⊤ := top_le_iff.1 hle
  exact isSimpleOrder_iff_isAtom_top.2 hX

set_option maxHeartbeats 1600000 in

theorem exists_emb (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (x : IrrGL k)
    {h : ℕ} (q : Fin h → IrrGL k) (hq : ∑ a, (q a).1 = x.1) (c : Fin h) (hc : (q c).IsCusp)
    (hj : jm q hq x.rep ≠ 0) :
    ∃ (r : Fin h → IrrGL k) (hr : ∑ a, (r a).1 = x.1) (f : x.rep.IntertwiningMap (prodIrr r hr)),
      r c = q c ∧ Function.Injective f := by
  classical
  let π : GlobalTheory.SplitRead.Irr k x.1 := ⟨x.2.rep.V, x.rep, x.2.rep.smooth, x.2.rep.irr⟩
  let e := stdBlocks (fun a => (q a).1) hq
  let ψ : GL (Fin (q c).1) k →* Levi k (fun a => Fin (q a).1) :=
    MonoidHom.mulSingle (fun a => GL (Fin (q a).1) k) c
  have hfl : HasFiniteLength (jac e π.π) :=
    (hBZ k).2.1 _ _ _ e π.V π.π π.smooth (hasFiniteLength_of_isIrreducible π.irr)
  have hsub : IsSubquotient (q c).rep ((jac e π.π).comp ψ : Representation ℂ _ _) :=
    (GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun a => (q a).rep) (fun a => (q a).2.rep.irr) c).trans
      (SupportUnique.isSubquotient_comp (jhMult_ne_zero_iff.1 hj) ψ)
  obtain ⟨U, _, _, ν, p, hp, hν, hνi⟩ := exists_irr_quot ψ
    (continuous_mulSingle (A := fun a => GL (Fin (q a).1) k) c) (fun g => by
      refine ⟨g c, Function.update g c 1, ?_, fun y => ?_⟩
      · funext a
        by_cases ha : a = c
        · subst ha
          simp [ψ]
        · simp [ψ, Pi.mulSingle_eq_of_ne ha, Function.update_of_ne ha]
      · funext a
        by_cases ha : a = c
        · subst ha
          simp [ψ]
        · simp [ψ, Pi.mulSingle_eq_of_ne ha, Function.update_of_ne ha])
    (q c).2.rep.irr hc.2 (isSmooth_jac e π.smooth) hfl hsub (by
      intro Y _ _ τ hτ hτs z hz
      obtain ⟨σ, hσ⟩ := GlobalTheory.CuspSupportExist.L_tens hG k _ π _ _ e Y τ hτ hτs
      obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar (σ c).smooth (σ c).irr
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
      obtain ⟨z, rfl⟩ := hz
      refine ⟨_, scalar_of_subquot hσ (GlobalTheory.CompanionTheory.Hypotheses₂.TDSwap.piTensor_scalar (fun a => (σ a).π) _
        (fun a => if a = c then (ω z : ℂ) else 1) fun a v => ?_)⟩
      by_cases ha : a = c
      · subst ha
        simpa [ψ] using hω z v
      · simp [ψ, Pi.mulSingle_eq_of_ne ha, ha])
  obtain ⟨σ, hσ⟩ := GlobalTheory.CuspSupportExist.L_tens hG k _ π _ _ e U ν hνi (.of_surjective p hp)
  obtain ⟨φ, hφ⟩ := GlobalTheory.injective_of_jacquet_surjective π e hνi p hp
  have hirr : (piTensor fun a => (σ a).π).IsIrreducible :=
    GlobalTheory.ExtTensorIrr.piTensor_isIrreducible hBZ k (Fin h) (fun a => Fin (q a).1)
      (fun j => ⟨(σ j).V, (σ j).π, (σ j).smooth, (σ j).irr⟩)
  obtain ⟨ε⟩ := SupportUnique.nonempty_equiv_of_isSubquotient hνi hirr hσ
  obtain ⟨η⟩ := SupportUnique.nonempty_equiv_of_isSubquotient (q c).2.rep.irr (σ c).irr
    (SupportUnique.isSubquotient_factor (fun a => (σ a).π) c (q c).2.rep.irr
      (hν.trans (SupportUnique.isSubquotient_comp hσ ψ)))
  let Ψ := (parIndEquiv e ε.symm).trans
    (prodIrrEquiv hq (fun a => (σ a).π) (fun a => (σ a).smooth) fun a => (σ a).irr)
  exact ⟨fun a => IrrGL.of (σ a).π (σ a).smooth (σ a).irr, hq, Ψ.toIntertwiningMap.comp φ,
    (IrrGL.of_eq_of.2 ⟨η⟩).trans (IrrGL.of_rep (q c)), Ψ.toLinearEquiv.injective.comp hφ⟩

theorem emb_of (x : IrrGL k) (r : Fin 2 → IrrGL k) (hr : ∑ a, (r a).1 = x.1)
    (f : x.rep.IntertwiningMap (prodIrr r hr)) (hf : Function.Injective f) : Emb x (r 0) (r 1) := by
  have key : ∀ y z : IrrGL k, r = ![y, z] → Emb x y z := by
    rintro y z rfl
    exact ⟨hr, f, hf⟩
  refine key _ _ (funext fun a => ?_)
  fin_cases a <;> rfl

end UpperTheory.Lit.Full.EmbR

theorem UpperTheory.Lit.Full.embR :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL k) (q : Fin 2 → IrrGL k) (hq : ∑ a, (q a).1 = x.1), (q 1).IsCusp → jm q hq x.rep ≠ 0 → ∃ y, Emb x y (q 1) := by
  intro hG hBZ k _ _ _ _ x q hq hc hj
  obtain ⟨r, hr, f, h1, hf⟩ := EmbR.exists_emb hG hBZ x q hq 1 hc hj
  exact ⟨r 0, h1 ▸ EmbR.emb_of x r hr f hf⟩
