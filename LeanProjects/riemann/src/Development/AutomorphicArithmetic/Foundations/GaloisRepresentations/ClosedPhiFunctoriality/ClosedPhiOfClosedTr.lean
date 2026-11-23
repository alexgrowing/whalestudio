import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IsOp2One
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClosedAtL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSstAtOfIsCrysAt

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem closedTr_of (h1 : CoverJ) (h2 : FrEx) (h3 : OpEx2) (h4 : FixOf) (h5 : Tie2) (h6 : TrLim) : ClosedTr := by
  intro E Ω _ _ _ _ _ l _ ι a ha P AI hT w A h O _ _ _ Bw hj J r hr hss C g θ hC hρ
  classical
  have hcrr : IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype) :=
    (GlobalTheory.LimitTop.closedAtL E Ω l a ha P AI hT w A h O Bw hj J r hr hss C hC.lin
      fun ρ hm => ⟨(hρ ρ hm).1, (hρ ρ hm).2.1, (hρ ρ hm).2.2.2⟩).2 fun ρ hm => (hρ ρ hm).2.2.1
  obtain ⟨T⟩ := hT
  let jl : ↥(GK Bw.Kw) →* Formalism.ConjugateSelfDual.G E Ω := (ReciprocityTheory.Gal.Dec (F := E) A).subtype.comp Bw.e.symm.toMonoidHom
  have hjl : Continuous jl := continuous_subtype_val.comp Bw.e_symm_cont
  let jE : E →+* ↥Bw.Kw.1 := (Bw.j.comp (algebraMap E Ω)).codRestrict Bw.Kw.1 Bw.j_E
  let J' : (↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l) → Multiset ℤ := fun τ'' => J (τ''.toRingHom.comp jE)
  obtain ⟨Cv, hCv⟩ := h1 l (Formalism.ConjugateSelfDual.G E Ω) a Bw.LL r hr hss C (fun ρ hm => (hρ ρ hm).1) _ θ hC
  have tr : ∀ (ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Om l)) (L : FinExt l) (r' : ↥(GK Bw.Kw) →* GL (Fin a) ↥L.1)
      (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)), Bw.LL.1 ≤ L.1 →
      (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i k, (((r' g).val i k : ↥L.1) : Om l) = ((ρ.comp jl) g).val i k) →
      IsModel Bw (ρ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) L (r'.comp Bw.e.toMonoidHom) ∧
        Bw.repE L (r'.comp Bw.e.toMonoidHom) = R := by
    intro ρ L r' R hle hR he
    refine ⟨⟨hle, ?_⟩, ?_⟩
    · ext g i k
      have := he (Bw.e g) i k
      simpa [jl, mapRep] using this
    · refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
      rw [hR]
      simp [LocBridge.repE, Matrix.toLin'_apply]
  obtain ⟨bk⟩ := GlobalTheory.BSP.nonempty_bk_of_finExt l Bw.Kw
  obtain ⟨τp, hτp⟩ := GlobalTheory.BSP.exists_isPer l Bw.Kw bk
  obtain ⟨N, F, F₀, rr, hF, hF₀, hlink⟩ := h2 l Bw.Kw Bw.LL bk τp hτp P AI T a Bw.LL_split (r.comp jl) _ (Cv.pull jl hjl) J'
    (by
      rintro _ ⟨ρ, hm, rfl⟩ L r' R hle hR he
      obtain ⟨hmod, hrep⟩ := tr ρ L r' R hle hR he
      refine ⟨hrep ▸ GlobalTheory.SstModel.main l P AI ⟨T⟩ E Ω (ReciprocityTheory.Gal.Dec (F := E) A) O Bw a _ L _ hmod (hρ ρ hm).2.1, fun τ n => ?_⟩
      have hi : IsInduced Bw ((L.1.val.comp τ).toRingHom.comp jE) τ := fun x => rfl
      have := IsJumpsAt.count_eq P hmod hi ((hρ ρ hm).2.2.2 _ L τ hi) n
      rw [← hrep]
      exact this.symm)
    (by
      rintro _ ⟨ρ, hm, rfl⟩ L r' R hle hR he
      obtain ⟨hmod, hrep⟩ := tr ρ L r' R hle hR he
      rw [← hrep]
      exact (hmod.isCrysAt_iff P).1 (hρ ρ hm).2.2.1)
  have hfix := h4 l E Ω w A h O Bw hj g
  have hfix0 : FixUr Bw.Kw 0 := fun c _ => by simp
  have hf1 : FixUr Bw.Kw (-alpha l g).toNat := by
    rcases le_total (alpha l g) 0 with h0 | h0
    · rwa [show (-alpha l g).toNat = (alpha l g).natAbs by omega]
    · rwa [show (-alpha l g).toNat = 0 by omega]
  have hf2 : FixUr Bw.Kw (alpha l g).toNat := by
    rcases le_total (alpha l g) 0 with h0 | h0
    · rwa [show (alpha l g).toNat = 0 by omega]
    · rwa [show (alpha l g).toNat = (alpha l g).natAbs by omega]
  have hα : alpha l g = (((alpha l g).toNat : ℕ) : ℤ) - (((-alpha l g).toNat : ℕ) : ℤ) := by omega
  obtain ⟨s, V, V', hs, hV, hV', hl⟩ := h3 l Bw.Kw bk τp hτp P AI T _ _ hf1 hf2 _ N _ (Cv.pull jl hjl).tw F F₀ rr hF hF₀ hlink
  refine h6 l P AI T Bw.Kw bk _ Bw.LL a r C Cv s V V' _ θ
    (fun m k => wdTr P ι Bw h hj (((Cv.lay m).rep k).comp (Dec (F := E) A).subtype) g) hs ?_ (fun m k => ?_) hl hCv
  · exact h5 l ι P AI T E Ω w A h O Bw hj g _ _ hα a _ _ hcrr _ Cv.b Cv.e (Cv.pull jl hjl).reads _ _ hV
  · exact h5 l ι P AI T E Ω w A h O Bw hj g _ _ hα a _ _ (hρ _ ((Cv.lay m).mem k)).2.2.1 _ (fun j => (Cv.lay m).b j k) (Cv.lay m).e
      (((Cv.pull jl hjl).lay m).reads k) _ _ (hV' m)

theorem congPhi_of_closedTr (H : ClosedTr) (hp : PowTr) : GlobalTheory.CongPhi.ClosedPhi := by
  intro E Ω _ _ _ _ _ l _ ι a ha P AI hT w A h O _ _ _ Bw hj J r hr hss C hρ σ S hC n
  have key := H E Ω l ι a ha P AI hT w A h O Bw hj J r hr hss C (σ ^ n) (S n)
    (fun ε hε => by
      obtain ⟨t, c, ht, h1, h2⟩ := hC n ε hε
      refine ⟨t, c, ht, h1, ?_⟩
      have := h2 n le_rfl
      simpa only [hp E Ω w A h _ σ n, wdTr] using this)
    (fun ρ hm => ⟨(hρ ρ hm).1, GlobalTheory.CrysSst.isSstAt_of_isCrysAt l P AI hT E Ω _ O Bw a _ (hρ ρ hm).2.1, (hρ ρ hm).2.1, (hρ ρ hm).2.2⟩)
  rw [hp E Ω w A h _ σ n, ← key, wdTr, RingEquiv.apply_symm_apply]

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
