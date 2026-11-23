import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RationalUnipotentLeParabolicStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermModerateGrowthInheritedStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermParabolicKFiniteStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermSmoothModerateGrowthStatement
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.FiniteDimensionalOfParts
import GroundTheory.PAdicHodge.NormalizedTrace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.Rg

open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev

section Main

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {m : ℕ}
  {X Y : Matrix (Fin V.rank) (Fin m) D.host.E} {U : Subgroup (GA D V)}
  {ε : D.what₂.Tau → Fin V.rank → Bool} {fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
  {W : D.what₂.Tau → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]
  {ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)} {c : D.what₂.Tau → ℕ → ℂ}

theorem host_facts (D : D7) (V : HSp D) : IsCMExt D.host.F D.host.E D.sp.cm.sig ∧ IsHermND D.sp.cm.sig V.gram :=
  let h := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  ⟨h.1, h.2 V⟩

theorem forms_subset_formsOn_empty (hθ : IsInfFam θ) :
    forms θ V U ε fr ρ c ⊆ formsOn θ V X Y ∅ U ε fr ρ c := by
  rintro φ ⟨h1, h2, h3, h4⟩
  have hle : (leftSub V X Y ∅ : Set (GA D V)) ⊆ GlobalTheory.AdelicU.ratPts D.sp.cm.sig V.gram := by
    have : leftSub V X Y ∅ ≤ GQ V := by
      refine sup_le ?_ inf_le_left
      rw [unip_empty]
      exact bot_le
    exact this
  exact ⟨IsSmModOn.of_isSmoothModerate (GlobalTheory.SiegelSet.isSmoothModerate_of_isAutFunSm hθ h1) hle, h2, h3, h4⟩

theorem constAlong_mem_formsOn [∀ τ, FiniteDimensional ℂ (W τ)] (hθ : IsInfFam θ)
    (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y) {S T : Finset (Fin m)} (hST : S ⊆ T) (hT : T.Nonempty)
    {φ a : GA D V → ℂ} (hφ : φ ∈ formsOn θ V X Y S U ε fr ρ c) (ha : IsConstAlong D.sp.cm.sig V.gram X T φ a) :
    a ∈ formsOn θ V X Y T U ε fr ρ c := by
  obtain ⟨h1, h2, h3, h4⟩ := hφ
  obtain ⟨hcm, hJ⟩ := host_facts D V
  have st := constAlong_cocompact_unique_stages hcm hJ hW
  obtain ⟨m1, m2⟩ := GlobalTheory.T.constant_term_moderate_growth_inherited D V m X Y hW S T hST hT φ a h1 ha
  obtain ⟨-, μ, 𝓕, b1, b2, b3⟩ := st.1 T
  have hleft : IsSmModOn D.sp.cm.sig V.gram ((GQ V ⊓ unip D.sp.cm.sig V.gram X T : Subgroup (GA D V)) : Set (GA D V)) φ :=
    ⟨fun γ hγ g => h1.left γ (GlobalTheory.T.rational_unipotent_le_parabolic D V m X Y hW S T hST hγ) g, h1.level, h1.cont, h1.smooth, h1.growth⟩
  refine ⟨m1, fun u hu hu' g => ?_, fun τ => GlobalTheory.T.constant_term_parabolic_K_finite D θ V m X Y hW S T hST τ (ε τ) (fr τ) (W τ) (ρ τ) φ a h1 (h3 τ) ha,
    fun τ k => ?_⟩
  · rw [ha μ 𝓕 b1 b2 b3 (g * u), ha μ 𝓕 b1 b2 b3 g]
    refine MeasureTheory.integral_congr_ae (.of_forall fun x => ?_)
    change φ (_ * (g * u)) = φ (_ * g)
    rw [← mul_assoc, h2 u hu hu']
  · have g1 := GlobalTheory.T.constant_term_smooth_moderate_growth D θ hθ V m X Y hW T φ a hleft m1.smooth m2 τ k
    rw [h4 τ k] at g1
    have g2 : IsConstAlong D.sp.cm.sig V.gram X T (c τ k • φ) (c τ k • a) := fun μ 𝓕 b1 b2 b3 g => by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [ha μ 𝓕 b1 b2 b3 g, MeasureTheory.integral_const_mul]
    exact st.2.2.1 T _ _ _ g1 g2

theorem finite_formsOn [∀ τ, FiniteDimensional ℂ (W τ)] (hθ : IsInfFam θ) (hU : IsOpen (U : Set (GA D V)))
    (hfr : IsFrameFam V ε fr) (hρ : ∀ τ, IsContRep (ρ τ)) (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y) :
    ∀ (j : ℕ) (T : Finset (Fin m)), T.Nonempty → Tᶜ.card = j →
      FiniteDimensional ℂ (Submodule.span ℂ (formsOn θ V X Y T U ε fr ρ c)) := by
  classical
  obtain ⟨hcm, hJ⟩ := host_facts D V
  have st := constAlong_cocompact_unique_stages hcm hJ hW
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro T hT hj
  set A := Submodule.span ℂ (formsOn θ V X Y T U ε fr ρ c) with hA
  have hmem : ∀ f : A, f.1 ∈ formsOn θ V X Y T U ε fr ρ c := fun f => mem_formsOn_of_mem_span hθ f.2
  have hl : ∀ f : A, ∀ T' : Finset (Fin m), T ⊆ T' → GlobalTheory.AutomorphicL2Unitary.LeftInv
      (GlobalTheory.AdelicU.ratPts D.sp.cm.sig V.gram ⊓ unip D.sp.cm.sig V.gram X T') f.1 := fun f T' h γ hγ g =>
    (hmem f).1.left γ (GlobalTheory.T.rational_unipotent_le_parabolic D V m X Y hW T T' h hγ) g

  have key : ∀ k : {k // k ∉ T}, ∃ L : A →ₗ[ℂ] Submodule.span ℂ (formsOn θ V X Y (insert k.1 T) U ε fr ρ c),
      ∀ f : A, IsConstAlong D.sp.cm.sig V.gram X (insert k.1 T) f.1 (L f).1 := by
    intro k
    have hsub : T ⊆ insert k.1 T := Finset.subset_insert _ _
    haveI := locallyCompact_unip hcm hJ hW (insert k.1 T)
    have cS := cocompact_unip_std hcm hJ hW (insert k.1 T)
    have cS' := cocompact_ratPts_inf le_rfl cS
    have hc : ∀ f : A, IsConstAlong D.sp.cm.sig V.gram X (insert k.1 T) f.1
        (GlobalTheory.Cusp.constTermOn (GlobalTheory.AdelicU.ratPts D.sp.cm.sig V.gram ⊓ unip D.sp.cm.sig V.gram X (insert k.1 T))
          (unip D.sp.cm.sig V.gram X (insert k.1 T)) f.1) := fun f =>
      (isConstTermOn_iff_ratPts_inf le_rfl cS (hl f _ hsub)).2 rfl
    refine ⟨{ toFun := fun f => ⟨_, Submodule.subset_span
                (constAlong_mem_formsOn hθ hW hsub (Finset.insert_nonempty _ _) (hmem f) (hc f))⟩
              map_add' := fun a b => Subtype.ext (funext fun x =>
                cS'.constTermOn_add (hl a _ hsub) (hmem a).1.cont (hl b _ hsub) (hmem b).1.cont x)
              map_smul' := fun a f => Subtype.ext (funext fun x => GlobalTheory.Cusp.constTermOn_smul a f.1 x) }, hc⟩
  choose L hL using key
  have hfin : ∀ k : {k // k ∉ T},
      FiniteDimensional ℂ (Submodule.span ℂ (formsOn θ V X Y (insert k.1 T) U ε fr ρ c)) := fun k => by
    have hlt : (insert k.1 T)ᶜ.card < j := by
      rw [← hj]
      refine Finset.card_lt_card ⟨fun x hx => ?_, fun h => ?_⟩
      · simp only [Finset.mem_compl, Finset.mem_insert, not_or] at hx ⊢
        exact hx.2
      · have := h (Finset.mem_compl.2 k.2)
        simp at this
    exact ih _ hlt _ (Finset.insert_nonempty _ _) rfl
  let Ψ : A →ₗ[ℂ] (∀ k : {k // k ∉ T}, Submodule.span ℂ (formsOn θ V X Y (insert k.1 T) U ε fr ρ c)) := LinearMap.pi L
  have hker : ∀ f : A, Ψ f = 0 → ∀ T' : Finset (Fin m), T ⊂ T' → IsConstAlong D.sp.cm.sig V.gram X T' f.1 0 := by
    intro f hf T' hT'
    obtain ⟨k, hk, hkT⟩ := Finset.exists_of_ssubset hT'
    have h0 : (L ⟨k, hkT⟩ f).1 = 0 := congrArg Subtype.val (congrFun hf ⟨k, hkT⟩)
    have h1 := hL ⟨k, hkT⟩ f
    rw [h0] at h1
    exact st.2.2.2.2 T' (insert k T) f.1 0 0 (Finset.insert_subset hk hT'.1) (hmem f).1.cont
      (fun γ hγ hγ' g => hl f T' hT'.1 γ ⟨hγ, hγ'⟩ g) h1 (isConstAlong_const _ _ _ _ 0)
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Rg.finite_cuspOn D θ hθ V U hU ε fr hfr W ρ hρ c m X Y hW T hT
  haveI : FiniteDimensional ℂ (LinearMap.ker Ψ) := by
    let ι : LinearMap.ker Ψ →ₗ[ℂ] Submodule.span ℂ {φ | φ ∈ formsOn θ V X Y T U ε fr ρ c ∧
        ∀ T' : Finset (Fin m), T ⊂ T' → IsConstAlong D.sp.cm.sig V.gram X T' φ 0} :=
      { toFun := fun f => ⟨f.1.1, Submodule.subset_span ⟨hmem f.1, hker f.1 f.2⟩⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact FiniteDimensional.of_injective ι fun a b h =>
      Subtype.ext (Subtype.ext (congrArg (fun z => z.1) h))
  haveI := hfin
  haveI : FiniteDimensional ℂ (LinearMap.range Ψ) := inferInstance
  haveI : FiniteDimensional ℂ (A ⧸ LinearMap.ker Ψ) := Module.Finite.equiv Ψ.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker Ψ)

end Main

theorem finite_constTerm : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), GlobalTheory.Published.AutFin.IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), (∀ τ, GlobalTheory.Published.AutFin.IsContRep (ρ τ)) → ∀ c : D.what₂.Tau → ℕ → ℂ, ∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (hC : IsIsoFrame V C), FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag hC) '' GlobalTheory.Published.AutFin.forms θ V U ε fr ρ c)) := by
  intro D θ hθ V U hU ε fr hfr W _ _ _ ρ hρ c r C hC
  obtain ⟨hcm, hJ⟩ := host_facts D V
  obtain ⟨hr, hi, hg⟩ := id hC
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨m, hm, X, Y, hW, hX⟩ := GlobalTheory.WittExt.exists_isWittFrame_initCols D.host.F D.host.E D.sp.cm.sig hcm V.rank V.gram hJ r C hi hg
  have hfin := finite_formsOn (c := c) (U := U) hθ hU hfr hρ hW _ {(⟨r, hm⟩ : Fin m)} (Finset.singleton_nonempty _) rfl
  haveI := hfin
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (formsOn θ V X Y {(⟨r, hm⟩ : Fin m)} U ε fr ρ c))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨φ, hφ, rfl⟩
  refine Submodule.subset_span ?_
  have h0 := forms_subset_formsOn_empty (X := X) (Y := Y) hθ hφ
  refine constAlong_mem_formsOn hθ hW (Finset.empty_subset _) (Finset.singleton_nonempty _) h0 ?_
  rw [isConstAlong_singleton hW, hX, GlobalTheory.UAut.isConstTerm_iff]
  have e : GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC) = GlobalTheory.SiegelSet.unipRad D.sp.cm.sig V.gram C := GlobalTheory.Cusp.NA_frameFlag hC
  have h1 : GlobalTheory.UAut.IsConstTermOn D.sp.cm.sig V.gram (GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC)) φ
      (GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag hC) φ) := fun μ 𝓕 b1 b2 b3 g => by
    rw [GlobalTheory.Cusp.constTerm_eq b2 hφ.1.left g, MeasureTheory.Measure.real, b3]
    simp
  exact e ▸ h1

end GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.Rg
