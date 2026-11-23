import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteMapsSplitPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweDualityOfMinguezStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShellSumEquivariantNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterNormalizedEquivariantFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwiningMapIntoInducedLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedRepresentationIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearWittModelLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWittModelUnitaryActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryMatrixSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConduct

noncomputable section

namespace GlobalTheory.KSplitIdent

section Local

open Filter Topology Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit GlobalTheory.PRep GlobalTheory.ThetaGL
open scoped TensorProduct

theorem exists_rep_of_surj {G S P : Type} [Group G] [AddCommGroup S] [Module ℂ S] [AddCommGroup P] [Module ℂ P]
    (ρ : Representation ℂ G S) (q : S →ₗ[ℂ] P) (hq : Function.Surjective q) (hk : ∀ g x, q x = 0 → q (ρ g x) = 0) :
    ∃ τ : Representation ℂ G P, ∀ g x, τ g (q x) = q (ρ g x) := by
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hq)
  have key : ∀ g x, q (ρ g (s (q x))) = q (ρ g x) := fun g x => by
    rw [← sub_eq_zero, ← map_sub, ← map_sub]
    refine hk g _ ?_
    rw [map_sub, sub_eq_zero]
    exact LinearMap.congr_fun hs (q x)
  refine ⟨{ toFun := fun g => q ∘ₗ ρ g ∘ₗ s, map_one' := ?_, map_mul' := fun g h => ?_ }, key⟩
  · ext y
    obtain ⟨x, rfl⟩ := hq y
    simpa using key 1 x
  · ext y
    obtain ⟨x, rfl⟩ := hq y
    simp only [LinearMap.comp_apply, Module.End.mul_apply, key]
    rw [map_mul, Module.End.mul_apply]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a d : ℕ}

theorem eventually_comp_mul {Φ : Matrix (Fin a) (Fin d) k → ℂ} (hΦ : Φ ∈ SB (Matrix (Fin a) (Fin d) k)) :
    ∀ᶠ g in 𝓝 (1 : GL (Fin d) k), ∀ X, Φ (X * g.val) = Φ X := by
  have h1 : ∀ᶠ g in 𝓝 (1 : GL (Fin d) k), ∀ X ∈ tsupport Φ, Φ (X * g.val) = Φ X := by
    refine hΦ.2.isCompact.eventually_forall_of_forall_eventually fun X _ => ?_
    have c1 : Continuous fun z : GL (Fin d) k × Matrix (Fin a) (Fin d) k => z.2 * z.1.val :=
      continuous_snd.matrix_mul (Units.continuous_val.comp continuous_fst)
    filter_upwards [(hΦ.1.comp_continuous c1).eventually_eq (1, X),
      (hΦ.1.comp_continuous continuous_snd).eventually_eq ((1 : GL (Fin d) k), X)] with z h h'
    simp only [Function.comp_apply, Units.val_one, Matrix.mul_one] at h h'
    rw [h, h']
  have h2 := (continuous_inv.tendsto' (1 : GL (Fin d) k) 1 inv_one).eventually h1
  filter_upwards [h1, h2] with g hg hg' X
  by_cases hX : X ∈ tsupport Φ
  · exact hg X hX
  by_cases hX' : X * g.val ∈ tsupport Φ
  · rw [← hg' _ hX', Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  · rw [image_eq_zero_of_notMem_tsupport hX, image_eq_zero_of_notMem_tsupport hX']

theorem om_eq (ν β : kˣ →* ℂˣ) (g : GL (Fin d) k) (h : GL (Fin a) k) (Φ : Matrix (Fin a) (Fin d) k → ℂ) :
    om ν g h Φ = (((ν * β) (gdet g) : ℂˣ) : ℂ) • omA ν β h (invT g) Φ := by
  funext X
  have e : ∀ (x : kˣ) (r : ℝ), ((nabs k x ^ r : ℝ) : ℂ) = apow x (r : ℂ) := fun x r =>
    Complex.ofReal_cpow (GlobalTheory.SplitWeil.Model.nabs_pos x).le r
  have hβ : (β (gdet g) : ℂ) ≠ 0 := Units.ne_zero _
  simp only [om, omA, e, Pi.smul_apply, smul_eq_mul, gdet_invT, apow_inv, invT_invT, map_inv, MonoidHom.mul_apply,
    Units.val_mul, Units.val_inv_eq_inv_val, neg_div, neg_neg]
  push_cast
  field_simp

def repS (ν β : kˣ →* ℂˣ) : Representation ℂ (GL (Fin a) k × GL (Fin d) k) (SB (Matrix (Fin a) (Fin d) k)) :=
  (repA ν β).subrepresentation _ fun x _ h => omA_mem_SB ν β x.1 x.2 h

theorem repS_val (ν β : kˣ →* ℂˣ) (g : GL (Fin a) k) (h : GL (Fin d) k) (Φ : SB (Matrix (Fin a) (Fin d) k)) :
    (repS ν β (g, h) Φ : Matrix (Fin a) (Fin d) k → ℂ) = omA ν β g h Φ := rfl

def repD (ν β : kˣ →* ℂˣ) : Representation ℂ (GL (Fin d) k) (SB (Matrix (Fin a) (Fin d) k)) where
  toFun g := (((ν * β) (gdet g) : ℂˣ) : ℂ) • repS ν β ((1 : GL (Fin a) k), invT g)
  map_one' := by
    rw [show gdet (1 : GL (Fin d) k) = 1 from map_one _, map_one, map_one, Prod.mk_one_one, map_one, Units.val_one]
    exact one_smul ℂ (1 : Module.End ℂ (SB (Matrix (Fin a) (Fin d) k)))
  map_mul' g h := by
    rw [smul_mul_smul_comm, ← map_mul (repS ν β), Prod.mk_mul_mk, one_mul, map_mul, gdet_mul, map_mul, Units.val_mul]

theorem repD_apply (ν β : kˣ →* ℂˣ) (g : GL (Fin d) k) (Φ : SB (Matrix (Fin a) (Fin d) k)) :
    repD ν β g Φ = (((ν * β) (gdet g) : ℂˣ) : ℂ) • repS ν β (1, invT g) Φ := rfl

structure IsQuot (ν β : kˣ →* ℂˣ) {P : Type} [AddCommGroup P] [Module ℂ P]
    (q : SB (Matrix (Fin a) (Fin d) k) →ₗ[ℂ] P) : Prop where
  onto : Function.Surjective q
  inv : ∀ g Φ, q (repS ν β (g, 1) Φ) = q Φ
  ker : ∀ h Φ, q Φ = 0 → q (repS ν β (1, h) Φ) = 0
  nontriv : Nontrivial P
  irred : ∀ N : Submodule ℂ P, (∀ h Φ, q Φ ∈ N → q (repS ν β (1, h) Φ) ∈ N) → N = ⊥ ∨ N = ⊤

theorem exists_quot_ind (HB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) (a a' : ℕ) {α β : kˣ →* ℂˣ} (hα : IsSmU α)
    (hβ : IsSmU β) {ϖ : kˣ} (hϖ : IsUnif ϖ) {e : ℕ} (he : CondLE ϖ e (α / β)) :
    ∃ q : SB (Matrix (Fin a) (Fin (a + a')) k) →ₗ[ℂ] indSp a a' α β, IsQuot (α / β) β q ∧
      ∀ h Φ g, (q (repS (α / β) β (1, h) Φ) : GL (Fin (a + a')) k → ℂ) g = (q Φ : GL (Fin (a + a')) k → ℂ) (g * h) := by
  obtain ⟨l, hl, hl0⟩ : ∃ l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ, IsEqv (α / β) (((a + a' : ℕ) : ℂ) / 2) l ∧
      ∃ φ ∈ SB _, l φ ≠ 0 := by
    by_cases hu : IsUnram (α / β)
    · obtain ⟨l, hl, hl1⟩ := GlobalTheory.T.unramified_character_normalized_equivariant_functional k a _ (((a + a' : ℕ) : ℂ) / 2) (hα.div hβ) hu
      exact ⟨l, hl, _, indicator_intM_mem_SB, hl1 ▸ one_ne_zero⟩
    · borelize k
      exact ⟨_, GlobalTheory.T.shell_sum_equivariant_nonzero k ϖ a e _ (((a + a' : ℕ) : ℂ) / 2) hϖ (hα.div hβ) hu he⟩
  have hI := GlobalTheory.KSplit.indSp_irreducible HB k a a' α β hα hβ
  let q : SB (Matrix (Fin a) (Fin (a + a')) k) →ₗ[ℂ] indSp a a' α β :=
    { toFun := fun Φ => ⟨mapA a' l (α / β) β Φ, GlobalTheory.KSplitInd.mapA_mem_indSp k a a' α β l hβ hl _ Φ.2⟩
      map_add' := fun Φ Φ' => Subtype.ext (mapA_add hl Φ.2 Φ'.2)
      map_smul' := fun c Φ => Subtype.ext (mapA_smul hl c Φ.2) }
  have tr : ∀ h Φ g, (q (repS (α / β) β (1, h) Φ) : GL (Fin (a + a')) k → ℂ) g =
      (q Φ : GL (Fin (a + a')) k → ℂ) (g * h) := fun h Φ g => mapA_omA_right l _ h g
  have ne : ∃ Φ, q Φ ≠ 0 := by
    obtain ⟨Φ, hΦ, h0⟩ := mapA_ne_zero (a' := a') (ν := α / β) (β := β) hl0
    exact ⟨⟨Φ, hΦ⟩, fun h => h0 (congrFun (congrArg Subtype.val h) 1)⟩
  have onto : Function.Surjective q := by
    obtain ⟨Φ, h0⟩ := ne
    rw [← LinearMap.range_eq_top, ← Submodule.map_top]
    exact map_eq_top ⊤ _ hI q (fun φ _ x => ⟨_, trivial, funext (tr x φ)⟩) ⟨Φ, trivial, h0⟩
  refine ⟨q, ⟨onto, fun g Φ => Subtype.ext (mapA_omA_left hl g Φ.2), fun h Φ H => ?_, ?_, fun N hN => ?_⟩, tr⟩
  · refine Subtype.ext (funext fun g => ?_)
    rw [tr, H]
    rfl
  · obtain ⟨Φ, h0⟩ := ne
    exact ⟨⟨_, _, h0⟩⟩
  · rcases hI (Submodule.map (indSp a a' α β).subtype N) (Submodule.map_subtype_le _ _) (by
      rintro _ ⟨f, hf, rfl⟩ x
      obtain ⟨Φ, rfl⟩ := onto f
      exact ⟨_, hN x Φ hf, funext (tr x Φ)⟩) with h | h
    · exact Or.inl (Submodule.map_injective_of_injective (indSp a a' α β).injective_subtype
        (h.trans (Submodule.map_bot _).symm))
    · exact Or.inr (Submodule.map_injective_of_injective (indSp a a' α β).injective_subtype
        (h.trans (Submodule.map_subtype_top _).symm))

theorem trivial_isIrreducible (G : Type) [Group G] : (Representation.trivial ℂ G ℂ).IsIrreducible := by
  haveI : Nontrivial (Subrepresentation (Representation.trivial ℂ G ℂ)) :=
    ⟨⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩⟩
  refine ⟨fun N => (eq_bot_or_eq_top N.toSubmodule).imp (fun h => ?_) fun h => ?_⟩
  · exact Subrepresentation.toSubmodule_injective h
  · exact Subrepresentation.toSubmodule_injective h

theorem IsQuot.exists_rep {ν β : kˣ →* ℂˣ} (hν : IsSmU ν) {P : Type} [AddCommGroup P] [Module ℂ P]
    {q : SB (Matrix (Fin a) (Fin d) k) →ₗ[ℂ] P} (hq : IsQuot ν β q) :
    ∃ τ : Representation ℂ (GL (Fin d) k) P, IsSmooth τ ∧ τ.IsIrreducible ∧
      OmQuot ν τ (Representation.trivial ℂ (GL (Fin a) k) ℂ) ∧ ∀ g Φ, τ g (q Φ) = q (repD ν β g Φ) := by
  obtain ⟨τ, hτ⟩ := exists_rep_of_surj (repD ν β) q hq.onto fun g x h => by
    rw [repD_apply, map_smul, hq.ker _ _ h, smul_zero]
  have hD : ∀ g (Φ : SB (Matrix (Fin a) (Fin d) k)), (repD ν β g Φ : Matrix (Fin a) (Fin d) k → ℂ) = om ν g 1 Φ :=
    fun g Φ => by rw [om_eq ν β, repD_apply, Submodule.coe_smul, repS_val]
  haveI := hq.nontriv
  refine ⟨τ, fun x => ?_, ?_, ?_, hτ⟩
  · obtain ⟨Φ, rfl⟩ := hq.onto x
    let K : Subgroup (GL (Fin d) k) :=
      { carrier := {g | τ g (q Φ) = q Φ}
        one_mem' := by simp
        mul_mem' := fun {g h} hg hh => by
          simp only [Set.mem_ofPred_eq] at hg hh ⊢
          rw [map_mul, Module.End.mul_apply, hh, hg]
        inv_mem' := fun {g} hg => by
          simp only [Set.mem_ofPred_eq] at hg ⊢
          nth_rewrite 1 [← hg]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    refine K.isOpen_of_mem_nhds (g := 1) ?_
    have c : Continuous fun g : GL (Fin d) k => gdet g := Matrix.GeneralLinearGroup.continuous_det
    have h1 : ∀ᶠ g in 𝓝 (1 : GL (Fin d) k), gdet g ∈ ν.ker :=
      (hν.1.preimage c).mem_nhds (by simp)
    have h2 : ∀ᶠ g in 𝓝 (1 : GL (Fin d) k), g ∈ KO k (Fin d) := (GlobalTheory.SplitFlip.isOpen_KO).mem_nhds (one_mem _)
    filter_upwards [h1, h2, eventually_comp_mul Φ.2] with g hg hg' hg''
    show τ g (q Φ) = q Φ
    rw [hτ]
    congr 1
    refine Subtype.ext ?_
    rw [hD]
    funext X
    have e1 : ν (Matrix.GeneralLinearGroup.det g) = 1 := hg
    have e2 : nabs k (Matrix.GeneralLinearGroup.det g) = 1 := nabs_of_valuation_eq_one (valuation_gdet_of_mem_KO hg')
    simp [om, e1, e2, hg'', GlobalTheory.SplitWeil.Model.nabs_one]
  · haveI : Nontrivial (Subrepresentation τ) :=
      ⟨⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩⟩
    refine ⟨fun N => (hq.irred N.toSubmodule fun h Φ hΦ => ?_).imp (fun h => ?_) fun h => ?_⟩
    · have := N.apply_mem_toSubmodule (invT h) hΦ
      rw [hτ] at this
      rwa [repD_apply, map_smul, invT_invT, Submodule.smul_mem_iff _ (Units.ne_zero _)] at this
    · exact Subrepresentation.toSubmodule_injective h
    · exact Subrepresentation.toSubmodule_injective h
  · refine ⟨(TensorProduct.rid ℂ P).symm.toLinearMap ∘ₗ q, fun h => ?_, fun g h Φ Φ' H => ?_⟩
    · obtain ⟨x, hx⟩ := exists_ne (0 : P)
      obtain ⟨Φ, rfl⟩ := hq.onto x
      exact hx ((TensorProduct.rid ℂ P).symm.map_eq_zero_iff.1 (LinearMap.congr_fun h Φ))
    · have e : Φ' = repS ν β (h, 1) (repD ν β g Φ) := by
        refine Subtype.ext ?_
        rw [H, om_eq ν β, repD_apply, map_smul, Submodule.coe_smul, repS_val, repS_val, ← omA_mul, mul_one, one_mul]
      simp [e, hq.inv, hτ]

theorem IsQuot.exists_equiv (HD : GlobalTheory.Published.HoweDualityGL) {ν β : kˣ →* ℂˣ} (hν : IsSmU ν)
    {P P' : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P']
    {q : SB (Matrix (Fin a) (Fin d) k) →ₗ[ℂ] P} {q' : SB (Matrix (Fin a) (Fin d) k) →ₗ[ℂ] P'}
    (hq : IsQuot ν β q) (hq' : IsQuot ν β q') :
    ∃ e : P ≃ₗ[ℂ] P', ∀ h Φ Φ', e (q Φ) = q' Φ' → e (q (repS ν β (1, h) Φ)) = q' (repS ν β (1, h) Φ') := by
  obtain ⟨τ, h1, h2, h3, h4⟩ := hq.exists_rep hν
  obtain ⟨τ', h1', h2', h3', h4'⟩ := hq'.exists_rep hν
  obtain ⟨e⟩ := (HD k d a ν hν.1).2 P P' ℂ τ τ' _ h1 h2 h1' h2' (fun _ => by simp) (trivial_isIrreducible _) h3 h3'
  refine ⟨e.toLinearEquiv, fun h Φ Φ' H => ?_⟩
  have key : e.toLinearEquiv (τ (invT h) (q Φ)) = τ' (invT h) (e.toLinearEquiv (q Φ)) :=
    LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' (invT h)) (q Φ)
  rw [H, h4, h4'] at key
  rw [repD_apply, repD_apply, map_smul, map_smul, map_smul, invT_invT] at key
  exact smul_right_injective _ (Units.ne_zero _) key

end Local

section Adelic

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem surj_herm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {n r s : ℕ} {X : Spc F E n} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) {v : Pl F}
    (t : E →ₐ[F] Fv F v) (g : GL (Fin n) (Fv F v)) : ∃ x ∈ UAt σ X (evFin F v), locMat t 1 x = g := by
  have hJ : IsUnit (X.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := GlobalTheory.LeviAtPlace.det_ne_zero_of_sig (hX.sig (InfinitePlace.mk φ))
    have h1 : X.J.det ≠ 0 := fun e => h0 (by
      rw [show X.J.map _ = RingHom.mapMatrix _ X.J from rfl, ← RingHom.map_det, e, map_zero])
    rw [show X.J.map t = (t : E →+* Fv F v).mapMatrix X.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  refine ⟨GlobalTheory.LeviAtPlace.leviHom hB.cm t X.J hJ hX.herm g, GlobalTheory.LeviAtPlace.lift_sub_one_at v _, Units.ext ?_⟩
  rw [locMat_val, GlobalTheory.LeviAtPlace.leviHom_map_piW, GlobalTheory.LeviAtPlace.locMat, GlobalTheory.LeviAtPlace.pairMat_fst]
  simp

theorem acts_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl F)
    (T : Module.End ℂ ((κ → AF F) → ℂ)) : Acts (evFin F v) T 0 0 := fun r _ => by
  have e : tens (evFin F v) (0 : (κ → Fv F v) → ℂ) r = 0 := funext fun x => zero_mul _
  rw [e, map_zero]

theorem exists_equiv_indSp : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (c : GL (Fin (a + a')) (Fv F v)),
      ∃ e : Rf.Pi v ≃ₗ[ℂ] GlobalTheory.KSplit.indSp a a' (chrW X.α t) (chrW X.β t),
        ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
          Acts (evFin F v) (om (1, h)) φ φ₁ → ∀ g : GL (Fin (a + a')) (Fv F v),
            (e (Rf.p v φ₁) : GL (Fin (a + a')) (Fv F v) → ℂ) g =
              (e (Rf.p v φ) : GL (Fin (a + a')) (Fv F v) → ℂ) (g * GlobalTheory.KSplit.locMat t c h) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM v t c
  have hT := hM.triple
  have hF := hM.fin
  have hP := hK.base
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_linear_witt_model_local hP F E σ B _ _ _ _ _ _ _ om _ _ _ _ (isPair_big hT) v t 1 c
  have act := GlobalTheory.T.linear_witt_model_unitary_action hP F E σ B _ _ _ _ _ _ _ om _ _ _ _ (isPair_big hT) v t 1 c ι hι
  have hex := (GlobalTheory.T.theta_action_exists hP F E σ B _ _ _ _ _ _ _ om _ _ _ _ (isPair_big hT) v).1
  have hb := Model.IsLin.bij hι
  have hα := (GlobalTheory.ChrWLocal.chrW_local F E X.α hT.chars.heckeα v t).1
  have hβ := (GlobalTheory.ChrWLocal.chrW_local F E X.β hT.chars.heckeβ v t).1
  obtain ⟨n, hn⟩ := (GlobalTheory.ChrWLocal.chrW_local F E _ (isHecke_div hT.chars.heckeα hT.chars.heckeβ) v t).2.1
  rw [chrW_div, inv_div] at act
  rw [chrW_div] at hn
  set α := chrW X.α t
  set β := chrW X.β t
  let j : SB (Fin a × Fin (a + a') → Fv F v) ≃ₗ[ℂ] GlobalTheory.SplitWeil.SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) :=
    LinearEquiv.ofBijective (ι.restrict fun φ h => hb.mapsTo h)
      ⟨fun φ φ' h => Subtype.ext (hb.injOn φ.2 φ'.2 (congrArg Subtype.val h)), fun Φ => by
        obtain ⟨φ, hφ, h⟩ := hb.surjOn Φ.2
        exact ⟨⟨φ, hφ⟩, Subtype.ext h⟩⟩
  let q : GlobalTheory.SplitWeil.SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) →ₗ[ℂ] Rf.Pi v :=
    Rf.p v ∘ₗ (SB _).subtype ∘ₗ j.symm.toLinearMap
  have hq : ∀ φ, q (j φ) = Rf.p v φ := fun φ => by simp [q]
  have hj : ∀ g ∈ UAt σ G.V (evFin F v), ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ φ₁ : SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (g, h)) φ φ₁ → repS (α / β) β (locMat t 1 g, locMat t c h) (j φ) = j φ₁ :=
    fun g hg h hh φ φ₁ H => Subtype.ext (act g hg h hh φ φ.2 φ₁ φ₁.2 H).symm
  have hW : ∀ x (φ : SB (Fin a × Fin (a + a') → Fv F v)), ∃ h ∈ UAt σ G.W (evFin F v), ∃ φ₁ ∈ SB _,
      Acts (evFin F v) (om (1, h)) φ φ₁ ∧ q (repS (α / β) β (1, x) (j φ)) = Rf.p v φ₁ := fun x φ => by
    obtain ⟨h, hh, rfl⟩ := GlobalTheory.T.local_unitary_matrix_surjective F E σ B _ G.W _ _ hT.base hT.geo.hW v t c x
    obtain ⟨φ₁, ⟨h1, H⟩, -⟩ := hex 1 (one_mem_UAt _ v) h hh φ φ.2
    refine ⟨h, hh, φ₁, h1, H, ?_⟩
    have := hj 1 (one_mem_UAt _ v) h hh φ ⟨φ₁, h1⟩ H
    rw [map_one] at this
    rw [this, hq]
  have hQ : IsQuot (α / β) β q := by
    refine ⟨fun y => ?_, fun g Φ => ?_, fun x Φ H => ?_, hF.nontriv v, fun N hN => hF.irred v N ?_⟩
    · obtain ⟨φ, hφ, rfl⟩ : y ∈ (SB _).map (Rf.p v) := hF.onto v ▸ Submodule.mem_top
      exact ⟨j ⟨φ, hφ⟩, hq _⟩
    · obtain ⟨φ, rfl⟩ := j.surjective Φ
      obtain ⟨x, hx, rfl⟩ := surj_herm hT.base hT.geo.hV t g
      obtain ⟨φ₁, ⟨h1, H⟩, -⟩ := hex x hx 1 (one_mem_UAt _ v) φ φ.2
      have := hj x hx 1 (one_mem_UAt _ v) φ ⟨φ₁, h1⟩ H
      rw [map_one] at this
      rw [this, hq, hq, ← sub_eq_zero, ← map_sub]
      exact hF.inv v (Submodule.subset_span ⟨x, hx, φ, φ.2, φ₁, h1, H, rfl⟩)
    · obtain ⟨φ, rfl⟩ := j.surjective Φ
      obtain ⟨h, hh, φ₁, h1, H1, e⟩ := hW x φ
      rw [hq] at H
      rw [e, hF.equiv v h hh φ φ.2 0 (zero_mem _) φ₁ h1 0 (zero_mem _) H1 (acts_zero v _) (by rw [H, map_zero]), map_zero]
    · intro h hh φ hφ φ₁ h1 H hm
      have := hj 1 (one_mem_UAt _ v) h hh ⟨φ, hφ⟩ ⟨φ₁, h1⟩ H
      rw [map_one] at this
      have h2 := hN (locMat t c h) (j ⟨φ, hφ⟩) (by rw [hq]; exact hm)
      rwa [this, hq] at h2
  obtain ⟨q', hQ', tr⟩ := exists_quot_ind hP.bernsteinUnitaryProductIrreducible a a' hα hβ
    (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec hn
  obtain ⟨e, he⟩ := hQ.exists_equiv (GlobalTheory.T.howe_duality_of_minguez hK.minguezThetaGL) (hα.div hβ) hQ'
  refine ⟨e, fun h hh φ hφ φ₁ h1 H g => ?_⟩
  have h2 := hj 1 (one_mem_UAt _ v) h hh ⟨φ, hφ⟩ ⟨φ₁, h1⟩ H
  rw [map_one] at h2
  obtain ⟨Φ', h3⟩ := hQ'.onto (e (q (j ⟨φ, hφ⟩)))
  have h4 := he (locMat t c h) _ Φ' h3.symm
  rw [h2, hq] at h4
  rw [hq] at h3
  rw [h4, tr, h3]

end Adelic

end GlobalTheory.KSplitIdent

end
