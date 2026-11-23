import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslationLiftEqLevelMoveUnitConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActLevMemCuspA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSectionReadingEqMovedFrameReadingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTraceFormLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchingDeterminantRootOfUnity

noncomputable section

namespace GlobalTheory.StabMove

section Adelic

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.LevelCusp GlobalTheory.DictMove
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

set_option maxHeartbeats 1000000 in

theorem exists_carries {V W : HSp D} (hV : V = W) {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (hr : V.rank = r) (hr' : W.rank = r) {U : Unf Xo c σ r}
    {dict : GA D V → Σ k, Frame (U.X k).Ψ r} (io : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) {g : ℕ}
    {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ}
    {th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
    (hU : IsUnf U) (hW : ∀ k, ModelW V hr (U.X k))
    (hL : DictLat U V hr dict (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ io) e F ik φ th x₀)
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hdom : ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom)
    {s : Dw.La →ₗ[𝓞 D.host.E] Dw.La} {κ : GA D W}
    (hκ : Induces W l (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr') ∘ₗ io) s κ) (h : GA D W) :
    (Formalism.IndefR.FWT.castDict hV dict h).2 ∈ (U.X (Formalism.IndefR.FWT.castDict hV dict h).1).dom ∧
      ∃ δ, ∃ hc : Carries φ s (Formalism.IndefR.FWT.castDict hV dict h).1 (Formalism.IndefR.FWT.castDict hV dict (h * κ)).1 δ,
        (Formalism.IndefR.FWT.castDict hV dict (h * κ)).2 =
          lact δ (castFr hc.mt.psi (Formalism.IndefR.FWT.castDict hV dict h).2) := by
  subst hV
  subst hr
  change DictLat U V rfl dict io e F ik φ th x₀ at hL
  change Induces V l io s κ at hκ
  refine ⟨hdom h, ?_⟩
  change ∃ δ, ∃ hc : Carries φ s (dict h).1 (dict (h * κ)).1 δ,
      (dict (h * κ)).2 = lact δ (castFr hc.mt.psi (dict h).2)
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have hxi : ∀ k k', (U.X k).ξ0 = (U.X k').ξ0 := fun k k' => (hW k).2.trans (hW k').2.symm
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  obtain ⟨hAr, -, -⟩ := GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V θ hθ
  obtain ⟨γ₁, hγ₁, hΛ₁, hm₁, hf₁⟩ := hL.2 h
  obtain ⟨γ₂, hγ₂, hΛ₂, hm₂, hf₂⟩ := hL.2 (h * κ)
  have e₀ : γ₂ * (h * κ) = γ₂ * γ₁⁻¹ * (γ₁ * h) * κ := by group
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix V (γ₂ * γ₁⁻¹) (mul_mem hγ₂ (inv_mem hγ₁))
  obtain ⟨gam, e₁, t₁, hgam⟩ := GlobalTheory.TwistTie.marked_isometry_half V l io (U.X (dict h).1) (U.X (dict (h * κ)).1) _ _
    (φ _) (φ _) (F.t _) (F.t _) s (γ₁ * h) (γ₂ * γ₁⁻¹) κ (hW _) (hW _) (hL.1.1 _) (hL.1.1 _) δ hδu hδf hκ.2.1 hκ.2.2
    ⟨hΛ₁, hm₁⟩ (by rw [← e₀]; exact ⟨hΛ₂, hm₂⟩)
  have hmt : IsMatch (U.X (dict h).1) (U.X (dict (h * κ)).1) δ := by
    refine ⟨Finset.ext fun τ => ((hU.2.1 _).2 τ).trans ((hU.2.1 _).2 τ).symm, (hU.2.1 _).1.trans (hU.2.1 _).1.symm,
      hxi _ _, fun u v => by rw [hG, hG]; exact hδu u v, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · obtain ⟨a, ha⟩ := (φ _).surjective ⟨v, hv⟩
      rw [show v = (φ (dict h).1 a : Fin V.rank → D.host.E) by rw [ha], ← hgam]
      exact (φ _ _).2
    · obtain ⟨a, ha⟩ := (φ _).surjective ⟨_, hv⟩
      obtain ⟨b, rfl⟩ := gam.surjective a
      have h1 := congrArg (fun u => (δ⁻¹).1 *ᵥ u) ((hgam b).symm.trans (congrArg Subtype.val ha))
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h1
      rw [← h1]
      exact (φ _ _).2
  refine ⟨δ, ⟨hmt, by rw [hG, hG], gam, e₁, t₁, hgam⟩, funext fun τ => ?_⟩
  change mat (dict (h * κ)).2 τ = δ.1.map τ.1 * mat (dict h).2 ⟨τ.1, hmt.mem τ⟩
  rw [hf₁, hf₂, GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth _ τ) (hθ τ.1),
    GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth _ ⟨τ.1, hmt.mem τ⟩) (hθ τ.1), e₀, (hAr τ.1).2.1, (hAr τ.1).2.1,
    (hAr τ.1).2.2.1 κ hκ.1, hδa τ.1 _ (hθ τ.1), Matrix.mul_one, ← Matrix.mul_assoc]
  rfl

set_option maxHeartbeats 1000000 in

theorem rdU_eq_of_carries_self (T : CoreJ D) (hT : LawsJ T) {j : ℕ} (hj : InR D j) {σ : T.Q.c.F →+* ℂ}
    (hσ : GoodEmb T.Q.c σ) {g : ℕ} {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ)}
    {F : FamilyUnif (T.Q.Xo j) (σ.comp (IntermediateField.inclusion T.Q.c.le).toRingHom)
      (fun i => relab T.Q.c σ (e i).1)}
    {ik : (T.U j σ).Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] ((T.U j σ).X k).Λ}
    (hP : HasPeriods φ) {G : Type} [Group G]
    {lev : G → ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) × ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La)}
    (hact : ActLev (Xo := T.Q.Xo j) T.Q.c lev) (a : G) {w : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hD : Dom w n)
    {f : Rul (T.Q.Xo j) T.Q.c} (hf : f ∈ sec (T.Q.Xo j) T.Q.c w n)
    (p q : Σ k, Frame ((T.U j σ).X k).Ψ D.R.r) (hp : p.2 ∈ ((T.U j σ).X p.1).dom) {δ : GL (Fin D.R.r) D.host.E}
    (hc : Carries φ (lev a).1 p.1 q.1 δ) (hq : q.2 = lact δ (castFr hc.mt.psi p.2)) (hpq : q.1 = p.1) :
    rdU (T.U j σ) (actLev T.Q.c lev a f) p.1 p.2 = rdU (T.U j σ) f q.1 q.2 := by
  obtain ⟨k, x⟩ := p
  obtain ⟨k', x'⟩ := q
  dsimp only at hp hc hq hpq ⊢
  subst hpq
  rw [hq]
  obtain ⟨-, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hT.pins
  have hU := hT.unf _ hj σ hσ
  have hr := hU.1 ▸ (show 1 ≤ D.R.r from (hnum _ hj).2.1)
  obtain ⟨hneg, φD, h1, h2, h3⟩ := GlobalTheory.GeoLevel.model_space_of_lawsJ D T hT j hj σ hσ k'
  obtain ⟨h4, hdet⟩ := GlobalTheory.GeoLevel.four_dvd_finrank_and_det_eq_pm_one D
  obtain ⟨ρ, ν, hρ, hν, -⟩ := mvPt_spec hact.total a ((T.U j σ).un k' ⟨x, hp⟩)
  refine GlobalTheory.T.movedSection_reading_eq_movedFrame_reading D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c σ D.R.r (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hσ hU
    k' φD h1 h2 h3 hneg δ hc.mt ((hdet _ _ δ hc.mt).imp_right fun h => ⟨h, h4⟩) ρ ν hν.1
    (fun z y' hm => move_eq hσ hr hA hP hc hν z hm) w n hD f hf _
    (actL_mem _ _ _ _ hact.total hact.nat hact.bor _ a hf) (fun y y' hm => ?_) x hp
  have m1 := mvPt_spec hact.total a y
  have m2 : levActR (Xo := T.Q.Xo j) (c := T.Q.c) lev a y y' := ⟨ρ, ν, hρ, hν, hm⟩
  exact (evalAt_actL hact (hT.evalWD _ hj) frMap_trans_id a hf.1 y).trans
    (evalAt_congr_id (hT.evalWD _ hj) frMap_trans_id hf.1 (hact.func a _ y _ _ m1 m2) (hact.func a _ y _ _ m2 m1))

end Adelic

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem phiAt_actLev_of_comp_eq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, OMPins T R κ v₀ O i) → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, ∀ g k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k → ∀ y : T.Q.c.F, D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) = ((chiC R i g : ℂˣ) : ℂ) → ∀ h, (castDict hV (T.dict ((i : ℕ) + 1) σ) (h * k)).1 = (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 → ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, phiAt T i σ hV (fun _ => 1) (actLev T.Q.c (O i).lev2 g f) h = σ y * phiAt T i σ hV (fun _ => 1) f (h * k) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hR ht hpb hO i σ hσ hV g k hk y hy p hp f hf
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have h := ht.laws
  obtain ⟨_, _, -, hd⟩ := h.dictU _ hj σ hσ
  obtain ⟨hr, g₀, e, F, ik, φ, th, hio, -, hth, hL⟩ := h.adPin _ hj σ hσ
  obtain ⟨_, hW⟩ := h.modelW _ hj σ hσ
  have hU := h.unf _ hj σ hσ
  have hK := h.levelK _ hj σ hσ
  rw [← h.pins.2.1.1] at hK
  obtain ⟨hio', hK'⟩ := GlobalTheory.DictMove.cast_level hV hK (T.iota _) hr (rank_Wc i) hio
  obtain ⟨k₀, hk₀, hs⟩ := (hO i).2.lift.lev g
  have hI := GlobalTheory.DictMove.induces_of_lift hio' (hR.βW i)
    (fun k hk => hK' k ((GlobalTheory.LiftLevel.isLift_one_iff_mem_level T R κ v₀ hR ht hpb i σ hσ hV k).1 hk)) hk₀ hk hs
  obtain ⟨hdom, δ, hc, hq⟩ := exists_carries hV hr (rank_Wc i) (T.iota _) hU hW hL hth hd.2.2.2.1 hI p
  have key := rdU_eq_of_carries_self T h hj hσ hL.1.2 (hO i).2.act.1 g (dom_wtA (κ i))
    ((mem_cusp _ _ _ _ _ _).1 hf).1 _ _ hdom hc hq hp
  obtain ⟨y', hy', hy1⟩ := GlobalTheory.GeoLevel.mu_lift hR ht hpb i hσ hV hk
  obtain rfl : y = y' := (algebraMap T.Q.c.F D.what₂.LL).injective (D.what₂.embLL.injective (hy.trans hy'.symm))
  have hmu := h.muUnit _ hj σ hσ
  rw [GlobalTheory.GeoLevel.phiAt_eq, GlobalTheory.GeoLevel.phiAt_eq, GlobalTheory.GeoLevel.castDict_mu_mul hmu.1, ← mul_assoc,
    mul_left_comm (σ y), hy1, mul_one]
  unfold GlobalTheory.GeoLevel.frameRead
  rw [key]

end GlobalTheory.StabMove
