import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbeddingAtEveryPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSubmoduleChainBoundedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSubmoduleSupNeTopStatement

open NumberField IsDedekindDomain

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HoweSplitPlace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

theorem ker_thetaSub {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {Bs : Base F E} {a a' : ℕ} {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    {R : RealMaps F a a'} {Rf : FinMaps F a a'} (hm : IsMatched Bs G Xc om om' R Rf) (v : Pl F) :
    GlobalTheory.Published.ThetaSub om v (LinearMap.ker (Rf.p v) ⊓ GlobalTheory.WeilM.SB _) := by
  refine ⟨le_inf (hm.fin.inv v) ?_, inf_le_right, ?_⟩
  · rw [augAt, Submodule.span_le]
    rintro _ ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact Submodule.sub_mem _ hφ₁ hφ
  · intro h hh φ hφ φ₁ hφ₁ hact
    refine ⟨?_, hφ₁⟩
    have h0 : Acts (evFin F v) (om' (1, h)) 0 0 := by
      intro r _
      have : tens (evFin F v) (0 : (Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) r = 0 :=
        funext fun x => by simp [tens]
      rw [this, map_zero]
    have := hm.fin.equiv v h hh φ hφ.2 0 (Submodule.zero_mem _) φ₁ hφ₁ 0 (Submodule.zero_mem _) hact h0
      (by rw [map_zero]; exact hφ.1)
    rw [map_zero] at this
    exact this

theorem main : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.MinguezThetaGL → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, Nonempty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p v φ = 0 := by
  intro hP hMin F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hm v hv
  obtain ⟨χ, ι, hχ, hbij, htr⟩ := GlobalTheory.T.exists_embedding_at_every_place hP F E σ Bs a a' G Xc om om' hm.triple v hv
  have ha : 1 ≤ a := by have := hm.triple.geo.lt; omega
  have hd : 1 ≤ a + a' := by omega
  have hSB : (GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)).map ι = GlobalTheory.SplitWeil.SB _ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hbij.mapsTo hx
    · intro hy
      obtain ⟨x, hx, rfl⟩ := hbij.surjOn hy
      exact ⟨x, hx, rfl⟩
  have hinj : ∀ N N' : Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
      N ≤ GlobalTheory.WeilM.SB _ → N' ≤ GlobalTheory.WeilM.SB _ → N.map ι ≤ N'.map ι → N ≤ N' := by
    intro N N' hN hN' hle x hx
    obtain ⟨y, hy, hyx⟩ := hle ⟨x, hx, rfl⟩
    rw [hbij.injOn (hN' hy) (hN hx) hyx] at hy
    exact hy
  have hne : ∀ N : Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
      N ≤ GlobalTheory.WeilM.SB _ → N ≠ GlobalTheory.WeilM.SB _ → N.map ι ≠ GlobalTheory.SplitWeil.SB _ := by
    intro N hN hN' he
    exact hN' (le_antisymm hN (hinj _ _ le_rfl hN (by rw [hSB, he])))
  refine ⟨?_, ?_⟩
  · obtain ⟨L, hL⟩ := GlobalTheory.T.theta_submodule_chain_bounded hP _ a (a + a') χ hχ
    refine ⟨L, fun r N hN hT => hL r (fun i => (N i).map ι) ?_ fun i => (htr _ (hT i).2.1).1 (hT i)⟩
    intro i j hij
    refine lt_of_le_of_ne (Submodule.map_mono (hN hij).le) fun heq => (hN hij).ne ?_
    exact le_antisymm (hN hij).le (hinj _ _ (hT j).2.1 (hT i).2.1 heq.ge)
  · intro N hN hNne φ hφ
    set K := LinearMap.ker (Rf.p v) ⊓ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) with hKdef
    have hK : GlobalTheory.Published.ThetaSub om v K := ker_thetaSub hm v
    have hKne : K ≠ GlobalTheory.WeilM.SB _ := by
      intro he
      haveI := hm.fin.nontriv v
      obtain ⟨y, hy⟩ := exists_ne (0 : Rf.Pi v)
      have hy' : y ∈ (GlobalTheory.WeilM.SB _).map (Rf.p v) := by rw [hm.fin.onto v]; trivial
      obtain ⟨x, hx, rfl⟩ := hy'
      rw [← he] at hx
      exact hy hx.1
    have hNK : N ⊔ K ≤ GlobalTheory.WeilM.SB _ := sup_le hN.2.1 inf_le_right
    have hsub : GlobalTheory.Published.ThetaSub om v (N ⊔ K) := by
      refine (htr _ hNK).2 ?_
      rw [Submodule.map_sup]
      exact ((htr _ hN.2.1).1 hN).sup ((htr _ inf_le_right).1 hK)
    have hNKne : N ⊔ K ≠ GlobalTheory.WeilM.SB _ := by
      intro he
      have := GlobalTheory.T.theta_submodule_sup_ne_top hP hMin _ a (a + a') ha hd χ hχ _ _ ((htr _ hN.2.1).1 hN) ((htr _ inf_le_right).1 hK)
        (hne _ hN.2.1 hNne) (hne _ inf_le_right hKne)
      apply this
      rw [← Submodule.map_sup, he, hSB]
    have hmem : ∀ x ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v),
        Rf.p v x ∈ (N ⊔ K).map (Rf.p v) → x ∈ N ⊔ K := by
      intro x hx hpx
      obtain ⟨y, hy, hyx⟩ := hpx
      have hxy : x - y ∈ K := ⟨by simp [LinearMap.mem_ker, map_sub, hyx], Submodule.sub_mem _ hx (hNK hy)⟩
      have : x = y + (x - y) := by abel
      rw [this]
      exact Submodule.add_mem _ hy (Submodule.mem_sup_right hxy)
    rcases hm.fin.irred v ((N ⊔ K).map (Rf.p v)) (fun h hh x hx x₁ hx₁ hact hpx =>
        ⟨x₁, hsub.2.2 h hh x (hmem x hx hpx) x₁ hx₁ hact, rfl⟩) with hbot | htop
    · have : Rf.p v φ ∈ (N ⊔ K).map (Rf.p v) := ⟨φ, Submodule.mem_sup_left hφ, rfl⟩
      rw [hbot] at this
      exact this
    · exfalso
      apply hNKne
      refine le_antisymm hNK fun x hx => hmem x hx ?_
      rw [htop]
      trivial

end GlobalTheory.HoweSplitPlace
