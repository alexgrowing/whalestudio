import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdeleSupportedAtFinitePlaceOfSupportedAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNatDatumSquareFlip
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunOMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerFixedFunctionsProportionalOfSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzEqPureTensorOfFiniteSlices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemScLatOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatPtLeClosureAndSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewGramInrInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtThetaTransformHeisenbergRealLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumThetaFunctionDerivativeComplexStructur
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransposeMapConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesSplitIdempotentSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtWAtPlSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartAlgebraMapLiftV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxGraphGraphHeis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergStableRelationOfVacua

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BigDat

section Generic

open GlobalTheory.LatVac (liftV psiAt locCo)

variable {F : Type} [Field F] [NumberField F] {U : Type} [AddCommGroup U] [Module (AF F) U] {B : U → U → AF F}
  {κ : Type} [Fintype κ]

theorem schr_eq_of_acts (co : Darboux B κ) (ψ : AddChar (AF F) ℂ) {v : HeightOneSpectrum (𝓞 F)} {γ : U}
    (hγ : At (evFin F v) γ) {φ : (κ → Fv F v) → ℂ} (hφ : φ ∈ GlobalTheory.WeilM.SB _) (h : Acts (evFin F v) (co.rho ψ γ) φ φ) :
    schr (psiAt ψ v) (locCo co v γ) φ = φ :=
  GlobalTheory.TensUniq.eq_of_tens_eq v φ _ _ hφ fun r hr => (GlobalTheory.VacBridge.rho_acts_locCo co ψ v γ hγ φ r hr).symm.trans (h r hr)

theorem schr_slice (co : Darboux B κ) (ψ : AddChar (AF F) ℂ) {v : HeightOneSpectrum (𝓞 F)} {γ : U}
    (hγ : At (evFin F v) γ) {Φ : (κ → AF F) → ℂ} (h : co.rho ψ γ Φ = Φ) {y : κ → AF F} (hy : ∀ k, evFin F v (y k) = 0) :
    schr (psiAt ψ v) (locCo co v γ) (fun ξ => Φ (y + fun k => liftV v (ξ k))) = fun ξ => Φ (y + fun k => liftV v (ξ k)) := by
  funext ξ
  have hc : ∀ u : AF F, evFin F v u = 0 → u • co.e γ = 0 := fun u hu => by rw [← map_smul, hγ u hu, map_zero]
  have h1 : ∀ k, At (evFin F v) ((co.e γ).1 k) := fun k u hu => congrArg (fun z => z.1 k) (hc u hu)
  have h2 : ∀ k, At (evFin F v) ((co.e γ).2 k) := fun k u hu => congrArg (fun z => z.2 k) (hc u hu)
  have hl : ∀ z : AF F, At (evFin F v) z → liftV v (evFin F v z) = z := fun z hz => (GlobalTheory.VacAny.eq_atPlace_of_at v z hz).symm
  conv_rhs => rw [← h]
  simp only [Darboux.rho, schr]
  congr 1
  · have hat : At (evFin F v) ((y + fun k => liftV v (ξ k)) ⬝ᵥ (co.e γ).2 + ⅟(2 : AF F) * ((co.e γ).1 ⬝ᵥ (co.e γ).2)) :=
      GlobalTheory.VacAny.at_add (GlobalTheory.VacAny.at_sum _ fun k _ => GlobalTheory.VacAny.at_mul_left _ (h2 k))
        (GlobalTheory.VacAny.at_mul_left _ (GlobalTheory.VacAny.at_sum _ fun k _ => GlobalTheory.VacAny.at_mul_left _ (h2 k)))
    rw [← hl _ hat]
    refine congrArg (fun z => ψ (liftV v z)) ?_
    simp only [dotProduct, map_add, map_sum, map_mul, GlobalTheory.VacAny.evFin_invOf_two, Pi.add_apply, hy, zero_add,
      GlobalTheory.LatVac.evFin_liftV]
    rfl
  · congr 1
    funext k
    simp only [Pi.add_apply, map_add, add_assoc]
    congr 2
    exact hl _ (h1 k)

end Generic

theorem lagr_vac {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {Y : Spc F E d} {M : Model σ X Y} {ψ : AddChar (AF F) ℂ} {v : HeightOneSpectrum (𝓞 F)} {A A' : Set _}
    {Z : Type} [TopologicalSpace Z] [AddGroup Z] {co ι} (h : IsLagrModel (Z := Z) M ψ v A A' co ι)
    {φ : (Fin n × Fin d → Fv F v) → ℂ} (hφ : φ ∈ GlobalTheory.WeilM.SB _) (h0 : φ ≠ 0) (Λ : Set _)
    (hfix : ∀ γ ∈ Λ, γ ∈ A ∨ γ ∈ A' → Acts (evFin F v) (M.co.rho ψ γ) φ φ) (hon : ∀ z, ∃ x ∈ A, co x = z)
    (hd : ∀ x ∈ A, (∀ y ∈ Λ, y ∈ A' → ψ (symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) x y) = 1) → x ∈ Λ) :
    ι φ 0 ≠ 0 ∧ ∀ x ∈ A, ι φ (co x) = Λ.indicator (fun _ => ι φ 0) x := by
  have key : ∀ x ∈ A, ι φ (co x) = Λ.indicator (fun _ => ι φ 0) x := fun x hx => by
    by_cases hΛ : x ∈ Λ
    · rw [Set.indicator_of_mem hΛ, h.2.1 x hx φ hφ φ hφ (hfix x hΛ (.inl hx)) 0, zero_add]
    · rw [Set.indicator_of_notMem hΛ]
      by_contra hne
      exact hΛ (hd x hx fun y hy hy' =>
        mul_right_cancel₀ hne ((h.2.2 y hy' φ hφ φ hφ (hfix y hy (.inr hy')) x hx).symm.trans (one_mul _).symm))
  refine ⟨fun h1 => h0 (h.1.injOn hφ (zero_mem _) (funext fun z => ?_)), key⟩
  obtain ⟨x, hx, rfl⟩ := hon z
  rw [key x hx, h1, map_zero]
  exact congrFun (Set.indicator_zero _ _) x

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}

theorem heisPt_box_gen {i j : ℕ} {e : Num G i j} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    (hW : Γ.V.J = (1 : D.host.E) • (spW G i j).gram) (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e)
    {ψ : AddChar (AF D.host.F) ℂ} {f₁ : HomV G i j → ℂ} {f₂ : HomW G i j → ℂ}
    (h₁ : IsLatVac (heisO ψ _ _) (latV G i j) f₁) (h₂ : IsLatVac (heisO ψ _ _) (latW G i j) f₂) {v : Pl D.host.F}
    {γ : Pt G i j} (hγ : γ ∈ genPt e v) : heisPt Γ ψ γ (box e f₁ f₂) = box e f₁ f₂ := by
  rw [heisPt_box e Γ hW hWW]
  rcases hγ with ⟨γ', h, rfl⟩ | ⟨h, ε, hε, hh⟩
  · rw [two_nsmul, mapV_add, mapW_add, ← two_nsmul, ← two_nsmul, h₁.1 _ h.2.1, h₂.1 _ h.2.2]
  · rw [h₁.2 ε hε _ h.2.1 hh.1, h₂.2 ε hε _ h.2.2 hh.2]

theorem thetaPt_smul {i j : ℕ} (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (c : ℂ)
    (Φ : (Ix G i j → AF D.host.F) → ℂ) (u : Pt G i j) : thetaPt Γ ψ (c • Φ) u = c * thetaPt Γ ψ Φ u :=
  (tsum_congr fun _ => mul_left_comm _ _ _).trans tsum_mul_left

theorem splitIdem_conj {a : AE D} (h : IsSplitIdem D a) : IsSplitIdem D (cA D a) := by
  obtain ⟨h1, h2, v, ε, h3, h4⟩ := h
  refine ⟨by rw [← RingHom.map_mul, h1], ?_, v, ε, h3, ?_⟩
  · rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, h2]
  · rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, h4]

theorem vac_ne_zero {S T : HSp D} {ψ θ sS sT LS LT} {f : WO S T → ℂ} (h : IsVacO ψ θ S T sS sT LS LT f) : f ≠ 0 := by
  rintro rfl
  obtain ⟨⟨p, hp⟩, hn⟩ := h.2.norm
  simpa [nrm2] using hn p hp

section Square

variable {W : G.Weil} {t : T} {i j : Fin D.R.m} {M : Vol G} {e : Num G i j} {Bs : Base D.host.F D.host.E}
  {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j} {X : Chars D.host.F D.host.E} {om : Rep D.sp.cm.sig Γ.V Γ.W} {om' : Rep D.sp.cm.sig Γ.V' Γ.W}

theorem exists_vac (hL : L.Is μ₀) (h : IsTripleOf W M t i j e Bs Γ X) (hT : IsTriple Bs Γ X om om')
    (hti : IsTied t i j e Bs Γ X) {f₁ : HomV G i j → ℂ} {f₂ : HomW G i j → ℂ} (h₁ : W.IsVac (.chi i (j + 1)) f₁)
    (h₂ : W.IsVac (.mu t (i + 1) j) f₂) :
    ∃ f, thetaPt Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f Γ.M.vac) = box e f₁ f₂ := by
  obtain ⟨-, hinj, hon⟩ := GlobalTheory.BigDat.ThBox.thetaPt_box W M t i j e Bs Γ X om om' h hT
  obtain ⟨Φ, hΦ, hb⟩ := hon f₁ f₂ h₁.2.theta h₂.2.theta
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := h.ψ ▸ hT.base.std
  have hG : Γ.M.IsGood W.ψ := h.ψ ▸ hT.geo.hM
  obtain ⟨f, hf⟩ := GlobalTheory.PureGlue.eq_pure_of_slices Γ.M.vac (fun v => (hG.vac v).2.1) hG.std Φ hΦ fun v y hy => by
    have hle := GlobalTheory.BigDat.latPt_le_latAtV t i j e Bs Γ X hti v
    obtain ⟨hgen, hsd⟩ := GlobalTheory.BigDatLat.latPt_le_closure_and_selfDual hL W i j e Γ h.JW h.JWW v
    obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded Γ.V Γ.W v Γ.M.co hT.geo.hV.lat hT.geo.hW.lat
    obtain ⟨a, ha⟩ := GlobalTheory.SchrFixUniq.proportional_of_fixed v (GlobalTheory.LatVac.psiAt W.ψ v) (GlobalTheory.VacAny.continuous_psiV hstd.1 v)
      (GlobalTheory.PsiNontriv.psiAt_ne_one W.ψ hstd v) (GlobalTheory.LatVac.locCo Γ.M.co v '' genPt e v)
      ((latPt e v).map (GlobalTheory.LatVac.locCo Γ.M.co v)) c
      (by rw [← AddMonoidHom.map_closure]; exact AddSubgroup.map_mono hgen) hc0
      (GlobalTheory.LatVac.DualLoc.map_selfDual v Γ.M.co W.ψ _ (fun γ hγ => hγ.1) hsd)
      (by rintro _ ⟨γ, hγ, rfl⟩; exact hc γ (hle γ hγ)) (Γ.M.vac v)
      (fun ξ => Φ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k)))
      (by
        rintro _ ⟨γ, hγ, rfl⟩
        exact schr_eq_of_acts _ _ (genPt_subset e v hγ).1 (hG.vac v).1 (GlobalTheory.BigDat.VacFix.vac_fixed W M t i j e Bs Γ X om om' h hT v hle γ hγ))
      (by
        rintro _ ⟨γ, hγ, rfl⟩
        refine schr_slice _ _ (genPt_subset e v hγ).1 (hinj _ (GlobalTheory.HeisSchA.rho_mem_schA Γ.M W.ψ hstd γ Φ hΦ) _ hΦ ?_) hy
        rw [thetaPt_rho, hb, heisPt_box_gen h.JW h.JWW h₁.2.lat h₂.2.lat hγ]) (hG.vac v).2.1
    exact ⟨a, congrFun ha⟩
  exact ⟨f, hf ▸ hb⟩

theorem pure_vac_inj {ψ} (hG : Γ.M.IsGood ψ) {f f' : SInf D.host.F (Ix G i j)}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f Γ.M.vac = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' Γ.M.vac) : f = f' := by
  classical
  choose ξ hξ using fun v => Function.ne_iff.1 (hG.vac v).2.1
  have hS := Filter.eventually_cofinite.1 hG.std
  let y : Ix G i j → Af D.host.F := fun k => ∑ v ∈ hS.toFinset, singleFin v (ξ v k)
  have hy : finPartFn Γ.M.vac y ≠ 0 := by
    refine finprod_induction (· ≠ (0 : ℂ)) one_ne_zero (fun _ _ => mul_ne_zero) fun v => ?_
    by_cases hv : v ∈ hS.toFinset
    · have : (fun k => evalV D.host.F v (y k)) = ξ v := funext fun k => by
        rw [map_sum, Finset.sum_eq_single_of_mem v hv fun v' _ h => evalV_singleFin_ne h.symm _, evalV_singleFin_self]
      rw [this]
      exact hξ v
    · have : (fun k => evalV D.host.F v (y k)) = 0 := funext fun k => by
        rw [map_sum]
        exact Finset.sum_eq_zero fun v' h => evalV_singleFin_ne (fun e : v = v' => hv (e ▸ h)) _
      rw [this, of_not_not (mt hS.mem_toFinset.2 hv), Set.indicator_of_mem (by exact fun _ => zero_mem _)]
      exact one_ne_zero
  ext z
  have := congrFun h fun k => pairA D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace _).symm (z k)) (y k)
  simp only [pure_eq, pureA, pairA, RingEquiv.apply_symm_apply] at this
  exact mul_right_cancel₀ hy this

theorem isGauss (h : IsTripleOf W M t i j e Bs Γ X) (hT : IsTriple Bs Γ X om om') {f₁ : HomV G i j → ℂ} {f₂ : HomW G i j → ℂ}
    (h₁ : W.IsVac (.chi i (j + 1)) f₁) (h₂ : W.IsVac (.mu t (i + 1) j) f₂) {c : ℂ} {f₀}
    (hb : thetaPt Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M.vac) = c • box e f₁ f₂) : Γ.M.IsGauss Bs.ψ Bs.emb f₀ := by
  obtain ⟨-, hinj, -⟩ := GlobalTheory.BigDat.ThBox.thetaPt_box W M t i j e Bs Γ X om om' h hT
  have hG : Γ.M.IsGood W.ψ := h.ψ ▸ hT.geo.hM
  have hm := fun f => (isFinPart_vac hG ∅).fam.mem hG f
  rw [h.ψ]
  refine ⟨1, fun u u' _ _ hJ f f' hf hf' => pure_vac_inj hG (hinj _ (hm _) _ (hm _) (funext fun x => ?_))⟩
  have hc := GlobalTheory.TripleCplxAt.cplx_pair W M t i j e Bs Γ X h u u' fun w => by simpa using hJ w
  obtain ⟨a, ha, ha'⟩ := GlobalTheory.FockLineJ.fock_line_J W.ψ W.θ _ _ _ _ f₁ W.ψ_std W.θ_is h₁.2.theta h₁.2.fock _ _ (fun τ => (hc τ).1) (mapV e x)
  obtain ⟨b, hb₁, hb'⟩ := GlobalTheory.FockLineJ.fock_line_J W.ψ W.θ _ _ _ _ f₂ W.ψ_std W.θ_is h₂.2.theta h₂.2.fock _ _ (fun τ => (hc τ).2) (mapW e x)
  have hr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evI D.host.F) f₀ fun y : Ix G i j → AF D.host.F => finPartFn Γ.M.vac fun k => (y k).2 := by
    refine ⟨fun y z hz => ?_, hm f₀⟩
    refine congrArg (finPartFn Γ.M.vac) (funext fun k => ?_)
    have : (pairA D.host.F 0 1 * z k).2 = 0 :=
      congrArg (fun q => (q k).2) (hz (pairA D.host.F 0 1) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace _)))
    exact (add_eq_left (a := (y k).2)).2 ((one_mul (z k).2).symm.trans this)
  have key : ∀ u (g : SInf D.host.F (Ix G i j)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (evI D.host.F) (Γ.M.heisLine W.ψ u) f₀ g →
      HasDerivAt (fun s : ℝ => c * (heisO W.ψ _ _ (realAd D.host.F s • mapV e u) f₁ (mapV e x) *
        heisO W.ψ _ _ (realAd D.host.F s • mapW e u) f₂ (mapW e x))) (thetaPt Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g Γ.M.vac) x) 0 := by
    intro u g hg
    have := GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_rho Γ.M.co W.ψ inferInstance W.ψ_std.1 u _ (hm f₀) _ (hm g) (hg _ hr) x
    convert this using 2 with s
    refine Eq.trans ?_ (congrFun (thetaPt_rho Γ W.ψ _ (realAd D.host.F s • u)) x).symm
    rw [hb, ← mapV_smul, ← mapW_smul]
    refine Eq.trans (congrArg (c * ·) (congrFun (heisPt_box e Γ h.JW h.JWW W.ψ _ f₁ f₂) x).symm) ?_
    simp only [heisPt, Pi.smul_apply, smul_eq_mul]
    ring
  have e1 := (key u f hf).unique ((ha.mul hb₁).const_mul c)
  have e2 := (key u' f' hf').unique ((ha'.mul hb').const_mul c)
  have e3 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Complex.I • f) Γ.M.vac = Complex.I • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f Γ.M.vac :=
    funext fun _ => mul_assoc _ _ _
  have e4 : realAd D.host.F 0 = 0 := by
    unfold realAd
    rw [map_zero (algebraMap ℝ _), map_zero (RingEquiv.symm _)]
    rfl
  have e5 : thetaPt Γ W.ψ (Complex.I • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f Γ.M.vac) x =
      Complex.I * thetaPt Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f Γ.M.vac) x := thetaPt_smul _ _ _ _ _
  rw [e3, e5, e1, e2]
  simp only [e4, zero_smul]
  ring

end Square

def halfPt {i j : ℕ} (e : Num G i j) (ε : AE D) : AddSubgroup (Pt G i j) :=
  ((GlobalTheory.PlaceModel.half _ _ ε).prod (GlobalTheory.PlaceModel.half _ _ ε)).comap (maps e).toLinearMap.toAddMonoidHom

theorem mem_halfPt {i j : ℕ} {e : Num G i j} {ε : AE D} {u : Pt G i j} : u ∈ halfPt e ε ↔ u ∈ mixHalf e ε :=
  and_congr (GlobalTheory.PlaceModel.isHalf_iff _ _).symm (GlobalTheory.PlaceModel.isHalf_iff _ _).symm

theorem isHalf_mono {m n : ℕ} {a ε : AE D} (h : ε * a = a) {x : Mx D m n} (hx : IsHalf a x) : IsHalf ε x := fun p q => by
  rw [← hx p q, ← mul_assoc, h]

theorem mem_of_sum_smul {m n : ℕ} {ι : Type} {P : Finset ι} {a : ι → AE D} {x : Mx D m n} (hx : IsHalf (∑ w ∈ P, a w) x)
    {Λ : AddSubgroup (Mx D m n)} (h : ∀ w ∈ P, a w • x ∈ Λ) : x ∈ Λ := by
  have : x = ∑ w ∈ P, a w • x := by
    rw [← Finset.sum_smul]
    exact Matrix.ext fun p q => (hx p q).symm
  rw [this]
  exact sum_mem h

set_option maxHeartbeats 1600000 in

theorem exists_gauss_datum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t)
    (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X → ∀ n Φ τ τ',
    (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) → HasFlip B t ρ i j n Φ τ τ' →
    ∀ φ, IsFinPart Γ.M X.T φ →
    (∀ w ∈ locPl G t, IsLocFn W B t e Γ w (w.under (𝓞 D.host.F)) (flipAt W t i j w (n w) (Φ w)) (φ (w.under (𝓞 D.host.F)))) →
    ∃ f₀, f₀ ≠ 0 ∧ Γ.M.IsGauss Bs.ψ Bs.emb f₀ ∧ IsDatumA W e Γ τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) := by
  intro D T L sc G μ₀ hL W B ρ t i j M _ e Bs Γ X om om' h hT hti n Φ τ τ' _ hfl φ hφ hloc
  classical
  obtain ⟨ε, hε, -, φ₁, φ₂, hmem, hsum⟩ := hfl
  have h₁ := ρ.vX_is i (j + 1) i.2 j.2
  have h₂ := ρ.vT_is t (i + 1) j i.2 j.2
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := h.ψ ▸ hT.base.std
  have hG : Γ.M.IsGood W.ψ := h.ψ ▸ hT.geo.hM
  obtain ⟨hadd, -, -⟩ := GlobalTheory.BigDat.ThBox.thetaPt_box W M t i j e Bs Γ X om om' h hT
  obtain ⟨f, hf⟩ := exists_vac hL h hT hti h₁ h₂
  have sW := (node_isV G hL (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).sd
  obtain ⟨T₁, hT₁⟩ := (GlobalTheory.PlaceModelSum.placeModelExistsSum D W.ψ W.ψ_std _ _ _ _ (isSelfDualC_neg sW)
    (node_isV G hL (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩).sd _ ε hε _ h₁.2.theta h₁.2.lat).1
  obtain ⟨T₂, hT₂⟩ := (GlobalTheory.PlaceModelSum.placeModelExistsSum D W.ψ W.ψ_std _ _ _ _
    (node_isV G hL (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩).sd sW _ ε hε _ h₂.2.theta h₂.2.lat).1
  obtain ⟨g0, g1, g2⟩ := GlobalTheory.BigDat.boxGraph_graph_heis hL W i j e Γ h.JW h.JWW ε _ hε _ _ T₁ T₂ hT₁ hT₂
  obtain ⟨hid, hsumid⟩ := GlobalTheory.IdemAtPl.main hL (G := G) t
  obtain ⟨hεs, hεw⟩ := hsumid ε hε
  have hh := fun w hw => GlobalTheory.BigDat.halves_split hL W i j e Γ h.JW h.JWW _ _ (hid w hw).1 (hid w hw).2
  have hco := GlobalTheory.BigDat.mixCo_spec B t i j e
  have hI : ∀ w, ∃ ι : ((Ix G i j → Fv D.host.F (w.under (𝓞 D.host.F))) → ℂ) →ₗ[ℂ] (_ → ℂ), w ∈ locPl G t →
      IsLagrModel Γ.M W.ψ _ (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w) ι ∧
        ι (φ _) = flipAt W t i j w (n w) (Φ w) := fun w => by
    by_cases hw : w ∈ locPl G t
    · exact (hloc w hw).2.imp fun _ h _ => h
    · exact ⟨0, fun h => absurd h hw⟩
  choose I hI using hI
  have hv := fun w hw => lagr_vac (hI w hw).1 (hG.vac _).1 (hG.vac _).2.1 (latPt e (w.under (𝓞 D.host.F)) : Set _)
    (fun γ hγ hγ' => GlobalTheory.BigDat.VacFix.vac_fixed W M t i j e Bs Γ X om om' h hT _ (GlobalTheory.BigDat.latPt_le_latAtV t i j e Bs Γ X hti _) γ (.inr ⟨hγ, hγ'.elim
      (fun h => ⟨_, (hid w hw).1, h⟩) fun h => ⟨_, splitIdem_conj (hid w hw).1, h⟩⟩)) (hco w).2.1 (hh w hw).2.2.2.1
  set c := ∏ w ∈ locPl G t, I w (Γ.M.vac _) 0 with hc
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun w hw => (hv w hw).1
  have hb : thetaPt Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) Γ.M.vac) = c • box e (ρ.vX i (j + 1)) (ρ.vT (i + 1) j) := by
    rw [← hf]
    exact funext fun u => (congrArg (thetaPt Γ W.ψ · u) (funext fun _ => mul_assoc _ _ _)).trans (thetaPt_smul _ _ _ _ u)
  let R : Submodule ℂ ((Pt G i j → ℂ) × ((Ix G i j → AF D.host.F) → ℂ)) :=
    { carrier := {p | p.2 ∈ schA D.host.F _ ∧ (p.1, thetaPt Γ W.ψ p.2) ∈ boxGraph e ε T₁ T₂}
      zero_mem' := ⟨zero_mem _, by
        have : thetaPt Γ W.ψ 0 = 0 := funext fun u => by simpa using thetaPt_smul Γ W.ψ 0 0 u
        rw [Prod.snd_zero, this]; exact zero_mem _⟩
      add_mem' := fun {p q} hp hq => ⟨add_mem hp.1 hq.1, by
        rw [Prod.snd_add, hadd _ hp.1 _ hq.1]; exact add_mem hp.2 hq.2⟩
      smul_mem' := fun a p hp => ⟨Submodule.smul_mem _ a hp.1, by
        rw [Prod.smul_snd, show thetaPt Γ W.ψ (a • p.2) = a • thetaPt Γ W.ψ p.2 from funext (thetaPt_smul _ _ _ _)]
        exact Submodule.smul_mem _ a hp.2⟩ }
  have hA : ∀ w ∈ locPl G t, ∀ x ∈ mixHalf e (atPl w 1), x ∈ mixHalf e ε := fun w hw x hx =>
    ⟨isHalf_mono (hεw w hw) hx.1, isHalf_mono (hεw w hw) hx.2⟩
  have hA' : ∀ w ∈ locPl G t, ∀ x ∈ mixHalf e (cA D (atPl w 1)), x ∈ mixHalf e (cA D ε) := fun w hw x hx =>
    have : cA D ε * cA D (atPl w 1) = cA D (atPl w 1) := by rw [← RingHom.map_mul, hεw w hw]
    ⟨isHalf_mono this hx.1, isHalf_mono this hx.2⟩
  have hbase : (Set.indicator (halfPt e ε : Set _) fun u => ∏ w ∈ locPl G t, I w (Γ.M.vac _) (mixCo B t e w u)) =
      c • box e (halfInd ε (latV G i j)) (halfInd ε (latW G i j)) := by
    funext u
    rw [Pi.smul_apply, smul_eq_mul, box, halfInd, halfInd]
    by_cases hu : u ∈ mixHalf e ε
    · rw [Set.indicator_of_mem (mem_halfPt.2 hu), Finset.prod_congr rfl fun w hw =>
        (congrArg _ ((hco w).2.2.1 u).symm).trans ((hv w hw).2 _ ((hh w hw).2.2.2.2 u).1)]
      by_cases hl : mapV e u ∈ latV G i j ∧ mapW e u ∈ latW G i j
      · rw [if_pos ⟨hl.1, hu.1⟩, if_pos ⟨hl.2, hu.2⟩, mul_one, mul_one]
        exact Finset.prod_congr rfl fun w hw => Set.indicator_of_mem (((hh w hw).2.2.2.2 u).2.2 hl.1 hl.2) _
      · have : ∃ w ∈ locPl G t, ofMaps e (atPl w 1 • mapV e u, atPl w 1 • mapW e u) ∉ latPt e (w.under (𝓞 D.host.F)) := by
          by_contra! hall
          exact hl ⟨mem_of_sum_smul (hεs ▸ hu.1) fun w hw => (mapV_ofMaps e _ ▸ (hall w hw).2.1 :),
            mem_of_sum_smul (hεs ▸ hu.2) fun w hw => (mapW_ofMaps e _ ▸ (hall w hw).2.2 :)⟩
        obtain ⟨w, hw, hn⟩ := this
        rw [Finset.prod_eq_zero hw (Set.indicator_of_notMem hn _)]
        rcases not_and_or.1 hl with hl | hl
        · rw [if_neg fun h => hl h.1, zero_mul, mul_zero]
        · rw [if_neg fun h : _ ∧ IsHalf ε (mapW e u) => hl h.1, mul_zero, mul_zero]
    · rw [Set.indicator_of_notMem (mt mem_halfPt.1 hu)]
      rcases not_and_or.1 hu with hl | hl
      · rw [if_neg fun h => hl h.2, zero_mul, mul_zero]
      · rw [if_neg fun h : _ ∧ IsHalf ε (mapW e u) => hl h.2, mul_zero, mul_zero]
  have hR := GlobalTheory.InductLagr.rel_of_vac Γ.M W.ψ hstd hG (locPl G t) (fun w => w.under (𝓞 D.host.F)) (Good.under_injOn hL G t) _
    (fun w => mixHalf e (atPl w 1)) (fun w => mixHalf e (cA D (atPl w 1))) (mixCo B t e) I (halfPt e ε) R (c • f)
    (fun w hw => (hI w hw).1) (fun w hw u hu => ⟨(hh w hw).1 u hu, mem_halfPt.2 (hA w hw u hu)⟩) (fun w hw => (hh w hw).2.1)
    (fun w hw => (hh w hw).2.2.1) (fun w _ x _ u => (hco w).1 u x)
    (fun w _ w' _ hne x hx u => by rw [(hco w').1, (hco w').2.2.2 w hne.symm x hx, add_zero])
    (fun w hw u => ⟨_, ((hh w hw).2.2.2.2 u).1, (hco w).2.2.1 u, ((hh w hw).2.2.2.2 u).2.1⟩)
    (fun w hw x hx p hp => ⟨GlobalTheory.HeisSchA.rho_mem_schA Γ.M W.ψ hstd x _ hp.1, by
      have := g1 x (hA w hw x hx) _ hp.2
      rwa [← thetaPt_rho] at this⟩)
    (fun w hw x hx p hp => ⟨GlobalTheory.HeisSchA.rho_mem_schA Γ.M W.ψ hstd x _ hp.1, by
      have := g2 x (hA' w hw x hx) _ hp.2
      rwa [← thetaPt_rho] at this⟩)
    ⟨(isFinPart_vac hG ∅).fam.mem hG _, by
      have := (boxGraph e ε T₁ T₂).smul_mem c (Submodule.subset_span
        ⟨_, _, GlobalTheory.isSBHalf_halfInd ε _, GlobalTheory.isSBHalf_halfInd ε _, rfl⟩)
      rw [(congrArg T₁ (one_smul ℂ _).symm).trans hT₁.vac, (congrArg T₂ (one_smul ℂ _).symm).trans hT₂.vac] at this
      show (_, thetaPt Γ W.ψ _) ∈ _
      rw [hbase, hb]
      exact this⟩
    φ hφ.1 fun v hv => hφ.2 v fun hm => let ⟨w, hw, e⟩ := (hti.2.2.1 v).1 hm; hv w hw e
  have hτ : (∑ d ∈ τ.support, τ d • (box e (φ₁ d) (φ₂ d), box e d.1.2 d.2)) ∈ boxGraph e ε T₁ T₂ :=
    sum_mem fun d hd => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, (hmem d hd).1.1, (hmem d hd).2.1, by
      rw [← (hmem d hd).1.2.2 T₁ hT₁, ← (hmem d hd).2.2.2 T₂ hT₂]⟩)
  have hfst : (Set.indicator (halfPt e ε : Set _) fun u => ∏ w ∈ locPl G t, I w (φ _) (mixCo B t e w u)) =
      (∑ d ∈ τ.support, τ d • (box e (φ₁ d) (φ₂ d), box e d.1.2 d.2)).1 := by
    funext u
    rw [Prod.fst_sum, Finset.sum_apply]
    by_cases hu : u ∈ mixHalf e ε
    · rw [Set.indicator_of_mem (mem_halfPt.2 hu), Finset.prod_congr rfl fun w hw => congrFun (hI w hw).2 _]
      exact (hsum _ _ hu.1 hu.2).symm
    · rw [Set.indicator_of_notMem (mt mem_halfPt.1 hu)]
      refine (Finset.sum_eq_zero fun d hd => mul_eq_zero_of_right _ ?_).symm
      by_contra hne
      exact hu ⟨(hmem d hd).1.1.1 _ (left_ne_zero_of_mul hne), (hmem d hd).2.1.1 _ (right_ne_zero_of_mul hne)⟩
  refine ⟨c • f, fun h0 => ?_, isGauss h hT h₁ h₂ hb, hR.1, fun u => ?_⟩
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 (vac_ne_zero h₁)
    obtain ⟨y, hy⟩ := Function.ne_iff.1 (vac_ne_zero h₂)
    have := congrFun hb (ofMaps e (x, y))
    rw [h0, show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : SInf D.host.F (Ix G i j)) Γ.M.vac = (0 : ℂ) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure 0 Γ.M.vac from
      funext fun _ => (zero_mul _).trans (zero_mul _).symm, thetaPt_smul, zero_mul, Pi.smul_apply, box, mapV_ofMaps,
      mapW_ofMaps] at this
    exact mul_ne_zero hc0 (mul_ne_zero hx hy) this.symm
  · have := g0 _ (by
      have := sub_mem hR.2 hτ
      rwa [← Prod.mk.eta (p := Finset.sum _ _), Prod.mk_sub_mk, ← hfst, sub_self] at this)
    have := congrFun (sub_eq_zero.1 this) u
    rw [Prod.snd_sum, Finset.sum_apply] at this
    exact this

end GlobalTheory.BigDat

end
