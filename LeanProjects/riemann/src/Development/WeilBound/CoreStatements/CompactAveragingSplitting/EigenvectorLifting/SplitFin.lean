import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitAsm

noncomputable section

namespace PositivityTheory.ThK.SplitAsm

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip
open PositivityTheory.KCo PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitDict PositivityTheory.ThK ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

local instance measFv (v : Pl F) : MeasurableSpace (Fv F v) := borel _

local instance borelFv (v : Pl F) : BorelSpace (Fv F v) := ⟨rfl⟩

open Classical in

def oneMaps (v : Pl F) (P : Type) [AddCommGroup P] [Module ℂ P]
    (p : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] P) (p' : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] P) :
    FinMaps F a a' where
  Pi := fun _ => P
  p := fun v' => if h : v' = v then h ▸ p else 0
  p' := fun v' => if h : v' = v then h ▸ p' else 0

theorem oneMaps_p (v : Pl F) (P : Type) [AddCommGroup P] [Module ℂ P] p p' :
    (oneMaps (a := a) (a' := a') v P p p').p v = p := by simp [oneMaps]; rfl

theorem oneMaps_p' (v : Pl F) (P : Type) [AddCommGroup P] [Module ℂ P] p p' :
    (oneMaps (a := a) (a' := a') v P p p').p' v = p' := by simp [oneMaps]; rfl

theorem core (hAU : ActsUniq) (v : Pl F) (G : Geo σ a a') (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (ν α β : (Fv F v)ˣ →* ℂˣ) (I : Submodule ℂ (GL (Fin (a + a')) (Fv F v) → ℂ))
    (f : (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ) → GL (Fin (a + a')) (Fv F v) → ℂ)
    (f' : (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ) → GL (Fin (a + a')) (Fv F v) → ℂ)
    (hlin : ∀ Φ ∈ SB _, ∀ Φ₁ ∈ SB _, ∀ c : ℂ, f (Φ + c • Φ₁) = f Φ + c • f Φ₁)
    (hlin' : ∀ Φ ∈ SB _, ∀ Φ₁ ∈ SB _, ∀ c : ℂ, f' (Φ + c • Φ₁) = f' Φ + c • f' Φ₁)
    (hmem : ∀ Φ ∈ SB _, f Φ ∈ I) (hmem' : ∀ Φ ∈ SB _, f' Φ ∈ I)
    (hinv : ∀ Φ ∈ SB _, ∀ g, f (omA ν β g 1 Φ) = f Φ) (hinv' : ∀ Φ ∈ SB _, ∀ g, f' (omB ν α g 1 Φ) = f' Φ)
    (heq : ∀ Φ ∈ SB _, ∀ h₁, f (omA ν β 1 h₁ Φ) = rtr h₁ (f Φ))
    (heq' : ∀ Φ ∈ SB _, ∀ h₁, f' (omB ν α 1 h₁ Φ) = rtr h₁ (f' Φ))
    (hon : ∀ y ∈ I, ∃ Φ ∈ SB _, f Φ = y) (hon' : ∀ y ∈ I, ∃ Φ ∈ SB _, f' Φ = y) (hnz : ∃ Φ ∈ SB _, f Φ ≠ 0)
    (hirr : ∀ N : Submodule ℂ (GL (Fin (a + a')) (Fv F v) → ℂ), N ≤ I → (∀ h₁, ∀ y ∈ N, rtr h₁ y ∈ N) → N = ⊥ ∨ N = I)
    (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ))
    (ι' : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ))
    (hι : Set.BijOn ι (SB (Fin a × Fin (a + a') → Fv F v) : Set _) (SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) : Set _))
    (hι' : Set.BijOn ι' (SB (Fin a' × Fin (a + a') → Fv F v) : Set _) (SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) : Set _))
    (gl : UA σ G.V.J → GL (Fin a) (Fv F v)) (gl' : UA σ G.V'.J → GL (Fin a') (Fv F v))
    (hl : UA σ G.W.J → GL (Fin (a + a')) (Fv F v))
    (hRg : ∀ g ∈ UAt σ G.V (evFin F v), Reads v ι (om (g, 1)) (omA ν β (gl g) 1))
    (hRh : ∀ h ∈ UAt σ G.W (evFin F v), Reads v ι (om (1, h)) (omA ν β 1 (hl h)))
    (hRg' : ∀ g ∈ UAt σ G.V' (evFin F v), Reads v ι' (om' (g, 1)) (omB ν α (gl' g) 1))
    (hRh' : ∀ h ∈ UAt σ G.W (evFin F v), Reads v ι' (om' (1, h)) (omB ν α 1 (hl h)))
    (hhl : ∀ x, ∃ h ∈ UAt σ G.W (evFin F v), hl h = x) :
    ∃ (p : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] I) (p' : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] I),
      (∀ φ ∈ SB _, (p φ : GL (Fin (a + a')) (Fv F v) → ℂ) = f (ι φ)) ∧
      (∀ φ ∈ SB _, (p' φ : GL (Fin (a + a')) (Fv F v) → ℂ) = f' (ι' φ)) ∧
      (SB _).map p = ⊤ ∧ (SB _).map p' = ⊤ ∧ augAt om v ≤ LinearMap.ker p ∧ augAt om' v ≤ LinearMap.ker p' ∧
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ φ₁ ∈ SB _, ∀ φ₁' ∈ SB _,
        Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' → p φ = p' φ' → p φ₁ = p' φ₁') ∧
      Nontrivial I ∧
      (∀ N : Submodule ℂ I, (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _,
        Acts (evFin F v) (om (1, h)) φ φ₁ → p φ ∈ N → p φ₁ ∈ N) → N = ⊥ ∨ N = ⊤) := by
  obtain ⟨p, hp, hpon⟩ := mk_p _ _ ι hι I f hlin hmem hon
  obtain ⟨p', hp', hpon'⟩ := mk_p _ _ ι' hι' I f' hlin' hmem' hon'

  have actA : ∀ (T : ((Fin a × Fin (a + a') → AF F) → ℂ) → _) (S : (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ) → _),
      Reads v ι T S → ∀ φ ∈ SB _, ∀ φ₁, Acts (evFin F v) T φ φ₁ → φ₁ ∈ SB _ → ι φ₁ = S (ι φ) := by
    intro T S hR φ hφ φ₁ h₁ _
    obtain ⟨φ₂, _, h₂, e⟩ := hR φ hφ
    rw [hAU F _ v T φ hφ φ₁ φ₂ h₁ h₂, e]
  have actB : ∀ (T : ((Fin a' × Fin (a + a') → AF F) → ℂ) → _) (S : (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ) → _),
      Reads v ι' T S → ∀ φ ∈ SB _, ∀ φ₁, Acts (evFin F v) T φ φ₁ → φ₁ ∈ SB _ → ι' φ₁ = S (ι' φ) := by
    intro T S hR φ hφ φ₁ h₁ _
    obtain ⟨φ₂, _, h₂, e⟩ := hR φ hφ
    rw [hAU F _ v T φ hφ φ₁ φ₂ h₁ h₂, e]
  refine ⟨p, p', hp, hp', hpon, hpon', ?_, ?_, ?_, ?_, ?_⟩
  · rw [augAt, Submodule.span_le]
    rintro z ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩
    show p (φ₁ - φ) = 0
    rw [map_sub, sub_eq_zero]
    apply Subtype.ext
    rw [hp φ₁ hφ₁, hp φ hφ, actA _ _ (hRg g hg) φ hφ φ₁ hA hφ₁, hinv _ (hι.mapsTo hφ)]
  · rw [augAt, Submodule.span_le]
    rintro z ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩
    show p' (φ₁ - φ) = 0
    rw [map_sub, sub_eq_zero]
    apply Subtype.ext
    rw [hp' φ₁ hφ₁, hp' φ hφ, actB _ _ (hRg' g hg) φ hφ φ₁ hA hφ₁, hinv' _ (hι'.mapsTo hφ)]
  · intro h hh φ hφ φ' hφ' φ₁ hφ₁ φ₁' hφ₁' hA hA' e
    apply Subtype.ext
    have e' := congrArg Subtype.val e
    rw [hp φ hφ, hp' φ' hφ'] at e'
    rw [hp φ₁ hφ₁, hp' φ₁' hφ₁', actA _ _ (hRh h hh) φ hφ φ₁ hA hφ₁, actB _ _ (hRh' h hh) φ' hφ' φ₁' hA' hφ₁',
      heq _ (hι.mapsTo hφ), heq' _ (hι'.mapsTo hφ'), e']
  · obtain ⟨Φ, hΦ, hne⟩ := hnz
    exact ⟨⟨⟨f Φ, hmem Φ hΦ⟩, 0, fun h => hne (congrArg Subtype.val h)⟩⟩
  · intro N hN
    have hst : ∀ h₁, ∀ y ∈ N.map I.subtype, rtr h₁ y ∈ N.map I.subtype := by
      rintro h₁ _ ⟨y, hy, rfl⟩
      obtain ⟨φ, hφ, rfl⟩ : ∃ φ ∈ SB _, p φ = y := by
        have : y ∈ (SB _).map p := hpon ▸ Submodule.mem_top
        obtain ⟨φ, hφ, e⟩ := this
        exact ⟨φ, hφ, e⟩
      obtain ⟨h, hh, rfl⟩ := hhl h₁
      obtain ⟨φ₁, hφ₁, hA, e⟩ := hRh h hh φ hφ
      refine ⟨p φ₁, hN h hh φ hφ φ₁ hφ₁ hA hy, ?_⟩
      show (p φ₁ : GL (Fin (a + a')) (Fv F v) → ℂ) = rtr (hl h) (p φ : GL (Fin (a + a')) (Fv F v) → ℂ)
      rw [hp φ₁ hφ₁, hp φ hφ, e, heq _ (hι.mapsTo hφ)]
    rcases hirr (N.map I.subtype) (by rintro _ ⟨y, -, rfl⟩; exact y.2) hst with h0 | h1
    · left
      rw [eq_bot_iff]
      intro y hy
      have : (y : GL (Fin (a + a')) (Fv F v) → ℂ) ∈ N.map I.subtype := ⟨y, hy, rfl⟩
      rw [h0] at this
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext ((Submodule.mem_bot ℂ).1 this))
    · right
      rw [eq_top_iff]
      intro y _
      have : (y : GL (Fin (a + a')) (Fv F v) → ℂ) ∈ N.map I.subtype := by rw [h1]; exact y.2
      obtain ⟨z, hz, e⟩ := this
      exact (Subtype.ext e : z = y) ▸ hz

theorem finRam_of (hR : RamMaps) (hRN : RamNonzero) (hI : IndIrred) (hD : Dict) (hAU : ActsUniq) (hC : ChrFacts) :
    FinRam := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv
  have hP : v ∈ B.P := hT.chars.sub hv
  obtain ⟨hα, hβ, hν, hcond, hram, -⟩ := hC F E B X a a' v (B.τ ⟨v, hP⟩) hT.chars
  have hS : HidaSetting a a' (unifAt v) (chrW X.α (B.τ ⟨v, hP⟩)) (chrW X.β (B.τ ⟨v, hP⟩)) (chrW X.ν (B.τ ⟨v, hP⟩)) :=
    ⟨GlobalTheory.SplitFlip.exists_isUnif.choose_spec, hα, hβ, hν, hT.geo.lt, hT.geo.even, hcond⟩
  obtain ⟨hlin, hlin', hmem, hmem', hinv, hinv', heq, heq', hon, hon'⟩ := hR (Fv F v) a a' _ _ _ _ hS (hram hv)
  obtain ⟨Φ0, hΦ0, hnz⟩ := hRN (Fv F v) a a' _ _ _ _ hS (hram hv)
  obtain ⟨b, b', c, ι, ι', gl, gl', hl, hW, hB, hbas, hvac, hvac', hRg, hRh, hRg', hRh', hhl⟩ :=
    hD F E σ B a a' G X om om' hT v (B.τ ⟨v, hP⟩)
  obtain ⟨rfl, rfl, rfl⟩ := hbas hP rfl
  obtain ⟨p, p', hp, hp', hon1, hon1', hinv1, hinv1', heq1, hnt, hirr1⟩ := core hAU v G om om' _ _ _ (indSp a a' _ _)
    (pRam a a' (unifAt v) (chrW X.ν (B.τ ⟨v, hP⟩)) (chrW X.β (B.τ ⟨v, hP⟩)))
    (pRam' a a' (chrW X.ν (B.τ ⟨v, hP⟩)) (chrW X.α (B.τ ⟨v, hP⟩)))
    (fun Φ h Φ₁ h₁ => hlin Φ h Φ₁ h₁) (fun Φ h Φ₁ h₁ => hlin' Φ h Φ₁ h₁)
    (fun Φ h => hmem Φ h) (fun Φ h => hmem' Φ h) (fun Φ h => hinv Φ h)
    (fun Φ h => hinv' Φ h) (fun Φ h => heq Φ h) (fun Φ h => heq' Φ h)
    (fun y hy => by obtain ⟨Φ, h, r⟩ := hon y hy; exact ⟨Φ, h, r⟩)
    (fun y hy => by obtain ⟨Φ, h, r⟩ := hon' y hy; exact ⟨Φ, h, r⟩) ⟨Φ0, hΦ0, hnz⟩
    (fun N hN hst => hI (Fv F v) a a' _ _ hα hβ N hN hst) ι ι' hW.bij hB.bij gl gl' hl hRg hRh hRg' hRh' hhl
  refine ⟨oneMaps v _ p p', ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [oneMaps_p]; exact hon1
  · rw [oneMaps_p']; exact hon1'
  · rw [oneMaps_p]; exact hinv1
  · rw [oneMaps_p']; exact hinv1'
  · rw [oneMaps_p, oneMaps_p']; exact heq1
  · exact hnt
  · rw [oneMaps_p]; exact hirr1
  · intro hv'; exact absurd hv hv'
  · intro hv' _
    refine ⟨ι, ι', hW, hB, hvac, hvac', fun φ hφ φ' hφ' => ?_⟩
    rw [oneMaps_p, oneMaps_p']
    refine ⟨fun h => ?_, fun h => Subtype.ext ?_⟩
    · have := congrArg Subtype.val h
      erw [hp φ hφ, hp' φ' hφ'] at this
      exact this
    · erw [hp φ hφ, hp' φ' hφ']
      exact h

def IntEq : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (x : Fv F v), x ∈ 𝒪[Fv F v] ↔ x ∈ v.adicCompletionIntegers F

theorem finSplit_of (hU : UnrMaps) (hI : IndIrred) (hIw : IndIwasawa) (hD : Dict) (hAU : ActsUniq) (hC : ChrFacts)
    (hZ : IntEq) : FinSplit := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v ⟨hv, ⟨τ⟩⟩
  obtain ⟨hα, hβ, hν, hcond, -, hunr⟩ := hC F E B X a a' v τ hT.chars
  obtain ⟨hαu, hβu⟩ := hunr hv
  have hS : HidaSetting a a' (unifAt v) (chrW X.α τ) (chrW X.β τ) (chrW X.ν τ) :=
    ⟨GlobalTheory.SplitFlip.exists_isUnif.choose_spec, hα, hβ, hν, hT.geo.lt, hT.geo.even, hcond⟩
  obtain ⟨hlin, hlin', hmem, hmem', hinv, hinv', heq, heq', hon, hon', hsph, hsph'⟩ :=
    hU (Fv F v) a a' _ _ _ _ hS hαu hβu
  obtain ⟨b, b', c, ι, ι', gl, gl', hl, hW, hB, -, hvac, hvac', hRg, hRh, hRg', hRh', hhl⟩ :=
    hD F E σ B a a' G X om om' hT v τ
  have hind : ∀ m n : ℕ, (intInd v : Matrix (Fin m) (Fin n) (Fv F v) → ℂ) =
      Set.indicator {Y | ∀ i j, Y i j ∈ 𝒪[Fv F v]} 1 := by
    intro m n
    unfold intInd
    congr 1
    ext Y
    simp only [Set.mem_setOf_eq, hZ F v]
  have h1 : ∀ h ∈ GlobalTheory.SplitWeil.KO (Fv F v) (Fin (a + a')), pUnr a a' (unifAt v) (chrW X.ν τ) (chrW X.β τ) (intInd v) h = 1 :=
    fun h hh => by rw [hind]; exact hsph h hh
  have h1' : ∀ h ∈ GlobalTheory.SplitWeil.KO (Fv F v) (Fin (a + a')), pUnr' a a' (unifAt v) (chrW X.ν τ) (chrW X.α τ) (intInd v) h = 1 :=
    fun h hh => by rw [hind]; exact hsph' h hh
  have hiSB : intInd v ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) := by
    rw [← hvac]; exact hW.bij.mapsTo (hT.geo.hM.vac v).1
  have hnz : pUnr a a' (unifAt v) (chrW X.ν τ) (chrW X.β τ) (intInd v) ≠ 0 := fun h0 => by
    have := h1 1 (one_mem _)
    rw [h0] at this
    exact zero_ne_one this
  obtain ⟨p, p', hp, hp', hon1, hon1', hinv1, hinv1', heq1, hnt, hirr1⟩ := core hAU v G om om' _ _ _ (indSp a a' _ _)
    (pUnr a a' (unifAt v) (chrW X.ν τ) (chrW X.β τ)) (pUnr' a a' (unifAt v) (chrW X.ν τ) (chrW X.α τ))
    (fun Φ h Φ₁ h₁ => hlin Φ h Φ₁ h₁) (fun Φ h Φ₁ h₁ => hlin' Φ h Φ₁ h₁)
    (fun Φ h => hmem Φ h) (fun Φ h => hmem' Φ h) (fun Φ h => hinv Φ h)
    (fun Φ h => hinv' Φ h) (fun Φ h => heq Φ h) (fun Φ h => heq' Φ h)
    (fun y hy => by obtain ⟨Φ, h, r⟩ := hon y hy; exact ⟨Φ, h, r⟩)
    (fun y hy => by obtain ⟨Φ, h, r⟩ := hon' y hy; exact ⟨Φ, h, r⟩) ⟨_, hiSB, hnz⟩
    (fun N hN hst => hI (Fv F v) a a' _ _ hα hβ N hN hst) ι ι' hW.bij hB.bij gl gl' hl hRg hRh hRg' hRh' hhl
  refine ⟨oneMaps v _ p p', ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [oneMaps_p]; exact hon1
  · rw [oneMaps_p']; exact hon1'
  · rw [oneMaps_p]; exact hinv1
  · rw [oneMaps_p']; exact hinv1'
  · rw [oneMaps_p, oneMaps_p']; exact heq1
  · exact hnt
  · rw [oneMaps_p]; exact hirr1
  · intro _
    rw [oneMaps_p, oneMaps_p']
    have e1 := hp _ (hT.geo.hM.vac v).1
    have e2 := hp' _ (hT.geo.hM'.vac v).1
    rw [hvac] at e1
    rw [hvac'] at e2
    have hm1 := hmem _ hiSB
    have hm2 : pUnr' a a' (unifAt v) (chrW X.ν τ) (chrW X.α τ) (intInd v) ∈ indSp a a' (chrW X.α τ) (chrW X.β τ) := by
      rw [← e2]; exact (p' (G.M'.vac v)).2
    have hd : pUnr a a' (unifAt v) (chrW X.ν τ) (chrW X.β τ) (intInd v) -
        pUnr' a a' (unifAt v) (chrW X.ν τ) (chrW X.α τ) (intInd v) = 0 :=
      hIw (Fv F v) a a' _ _ _ (Submodule.sub_mem _ hm1 hm2) fun h hh => by
        simp only [Pi.sub_apply, h1 h hh, h1' h hh, sub_self]
    refine ⟨Subtype.ext ?_, fun h0 => hnz ?_⟩
    · erw [e1, e2]; exact sub_eq_zero.1 hd
    · have := congrArg Subtype.val h0
      erw [e1] at this
      exact this
  · intro _ hvT; exact absurd hvT hv

end PositivityTheory.ThK.SplitAsm
