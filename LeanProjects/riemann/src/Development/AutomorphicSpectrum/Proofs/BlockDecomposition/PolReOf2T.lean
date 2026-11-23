import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HoweMaximalTori.MaxSplit
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Inertof
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Vaceigen
import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasMain
import Development.WeilBound.CoreStatements.LocalThetaKernels.EvlMain
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SiegelTransport
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LinearAct
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.HypothesesAtTriple
import Development.WeilBound.CoreStatements.LocalThetaKernels.Locpair
import Development.WeilBound.CoreStatements.LocalThetaKernels.LocpairU
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDict
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ExistsFull
import Development.WeilBound.ThetaLifts.CartanFactorisation.Kills0Of
import Development.WeilBound.ThetaLifts.CartanFactorisation.KillInf
import Development.WeilBound.ThetaLifts.Reductions.ArchimedeanMatchedMapsCompare

noncomputable section

namespace GlobalTheory.CompanionTheory.ThetaK

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKG PositivityTheory.ThKF PositivityTheory.HoweDualityUnitaryAlt
open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem cmp_finT (hM : MaxFinT) {R R₂ : RealMaps F a a'} {Rf Rf₂ : FinMaps F a a'} (m : IsMatched B G X om om' R Rf)
    (v : Pl F) (n₂ : Nontrivial (Rf₂.Pi v)) (o : (SB _).map (Rf₂.p v) = ⊤) (o' : (SB _).map (Rf₂.p' v) = ⊤)
    (x₁ : Maximal (fun P => GlobalTheory.Published.ThetaSub om v P ∧ P ≠ SB _) (LinearMap.ker (Rf₂.p v) ⊓ SB _))
    (x₂ : Maximal (fun P => GlobalTheory.Published.ThetaSub om' v P ∧ P ≠ SB _) (LinearMap.ker (Rf₂.p' v) ⊓ SB _))
    (eq₂ : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ φ₁ ∈ SB _, ∀ φ₁' ∈ SB _,
      Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' →
      Rf₂.p v φ = Rf₂.p' v φ' → Rf₂.p v φ₁ = Rf₂.p' v φ₁') :
    ∃ (e : Rf.Pi v →ₗ[ℂ] Rf₂.Pi v) (c : ℂ), c ≠ 0 ∧ (∀ x ∈ SB _, e (Rf.p v x) = Rf₂.p v x) ∧
      ∀ x ∈ SB _, e (Rf.p' v x) = c • Rf₂.p' v x := by
  have p1 := pairV m.triple
  have p2 := pairV' m.triple
  obtain ⟨ω, ρ, hω⟩ := PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B _ _ G.M om
    ⟨p1.base, ⟨_, _, p1.herm⟩, ⟨_, _, p1.skew⟩, p1.good, ⟨_, _, p1.weil⟩⟩ v
  choose A' hA' hA'' using fun (i : UAt σ G.W (evFin F v)) (x : SB (Fin a' × Fin (a + a') → Fv F v)) => ex_fin p2 v i x x.2
  have ac : ∀ (i : UAt σ G.W (evFin F v)) (x : SB (Fin a × Fin (a + a') → Fv F v)),
      Acts (evFin F v) (om (1, i.1)) x (ω (1, i.1) x) := fun i x => (hω.acts 1 (one_at _) i i.2 x x.2 _).2 rfl
  have pr : ∀ (i : UAt σ G.W (evFin F v)) (x : SB (Fin a × Fin (a + a') → Fv F v)), ω (1, i.1) x ∈ SB _ :=
    fun i x => hω.pres 1 (one_at _) i i.2 x x.2
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  exact schur_match (SB _) (SB _) (Rf.p v) (Rf.p' v) (Rf₂.p v) (Rf₂.p' v) (m.fin.onto v) (m.fin.onto' v) o o'
    (fun x hx => (ker_of_eq ((hM F E σ B _ _ G X om om' m.triple v trivial).1 _ _ (maxFinP m v).1 x₁) x hx).1)
    (ker_of_eq ((hM F E σ B _ _ G X om om' m.triple v trivial).2 _ _ (maxFinP m v).2 x₂))
    (fun i : UAt σ G.W (evFin F v) => ω (1, i.1) ∘ₗ Submodule.subtype _) A' pr hA'
    (fun i x x' => m.fin.equiv v i i.2 x x.2 x' x'.2 _ (pr i x) _ (hA' i x') (ac i x) (hA'' i x'))
    (fun i x x' => eq₂ i i.2 x x.2 x' x'.2 _ (pr i x) _ (hA' i x') (ac i x) (hA'' i x'))
    (fun N hN => m.fin.irred v N fun h hh x hx y _ e hp => by
      rw [(hω.acts 1 (one_at _) h hh x hx y).1 e]; exact hN ⟨h, hh⟩ ⟨x, hx⟩ hp)
    (rank_SB _)

theorem polRe_of2T (hH : PositivityTheory.ThKR.JoinTri) (hM : MaxFinT) (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hC : PolCount)
    (hJ : CartanConj) (hV : CartanMove) (hK : KCoinv) (hI : ILeft) : PolRe := by
  rintro F E _ _ _ _ _ σ B a a' G X om om' R Rf m V V' W R₂ Rf₂ m₂ ⟨c₂, hc₂, hc⟩
  have p1 := pairV m.triple
  have p2 := pairV' m.triple
  obtain ⟨h, hh, hh'⟩ := hJ F E σ B _ G.W W _ _ p1.base p1.skew m₂.triple.geo.hW
  obtain ⟨g, hg, hg', hP⟩ := hV F E σ B _ _ _ _ _ _ _ om _ _ _ _ p1 V W (reG G V V' W).M rfl (pairV m₂.triple) h hh hh'
  obtain ⟨g', hk, hk', hP'⟩ := hV F E σ B _ _ _ _ _ _ _ om' _ _ _ _ p2 V' W (reG G V V' W).M' rfl (pairV' m₂.triple) h hh hh'
  obtain ⟨T, hT, -⟩ := hO F E σ B _ _ _ _ _ _ _ om _ _ _ _ p1 g hg h hh
  obtain ⟨T', hT', -⟩ := hO F E σ B _ _ _ _ _ _ _ om' _ _ _ _ p2 g' hk h hh
  obtain ⟨e, c, c0, he, he'⟩ := archimedean_matched_maps_compare hH hO hL hQ hC ⟨m₂.triple, real_trans hO hL hQ m.triple m₂.triple m.real ⟨hg, hg'⟩ ⟨hk, hk'⟩
    ⟨hh, hh'⟩ hT hT' (hP T hT) (hP' T' hT'), m₂.fin⟩ m₂
  choose ef cf cf0 hef hef' using fun v => cmp_finT (R₂ := R₂) hM m v (m₂.fin.nontriv v) (m₂.fin.onto v) (m₂.fin.onto' v)
    (maxFinP m₂ v).1 (maxFinP m₂ v).2 (m₂.fin.equiv v)
  have cf1 : ∀ v ∉ X.T, cf v = 1 := fun v hv => by
    obtain ⟨s1, s2⟩ := m₂.fin.sph v hv
    have x1 := hef v _ (p1.good.vac v).1
    rw [(m.fin.sph v hv).1, hef' v _ (p2.good.vac v).1] at x1
    have x2 : cf v • Rf₂.p v (G.M.vac v) = (1 : ℂ) • Rf₂.p v (G.M.vac v) := by
      rw [one_smul]; exact (congrArg (cf v • ·) s1).trans x1
    exact smul_left_injective ℂ s2 x2
  let Λ : ℂ := c * ∏ v ∈ X.T, cf v
  refine ⟨c₂ * Λ, mul_ne_zero hc₂ (mul_ne_zero c0 (Finset.prod_ne_zero_iff.2 fun v _ => cf0 v)), ?_⟩
  rintro Φ Φ' hΦ' ⟨S, hS, k, k', f, φ, f', φ', h1, h2, rfl, rfl, eq⟩ x
  choose u hu hu' using fun i => (show f i ∈ ((reG G V V' W).M.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) from hP T hT ▸ (h1 i).1)
  choose u' hw hw' using fun i => (show f' i ∈ ((reG G V V' W).M'.Pol B.ψ B.emb).map (T' : _ →ₗ[ℂ] _) from hP' T' hT' ▸ (h2 i).1)
  have e1 := move_sum p1.good hT u φ (fun i => (h1 i).2.1) fun i => ev_of_off (h1 i).2.2
  have e2 := move_sum p2.good hT' u' φ' (fun i => (h2 i).2.1) fun i => ev_of_off (h2 i).2.2
  have fu : ∀ i, T (u i) = f i := hu'
  have fu' : ∀ i, T' (u' i) = f' i := hw'
  simp only [fu] at e1
  simp only [fu'] at e2
  have s1 : ∑ i, pure (u i) (φ i) ∈ schA F _ := sum_mem fun i _ =>
    GlobalTheory.TensUniq.pure_mem_schA _ _ (h1 i).2.1 ((good_std p1.good).congr (ev_of_off (h1 i).2.2))
  have so : ∑ i, pure (u' i) (φ' i) ∈ G.M'.So B.ψ B.τ₁ := by
    have := (hK F E σ B a a' G X om om' R Rf m).2 (g', h)⁻¹ _ hΦ'
    rwa [← e2, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
  have e3 : Λ • ∑ i, pure (u' i) (φ' i) = ∑ i, pure (Λ • u' i) (φ' i) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => funext fun y => (mul_assoc _ _ _).symm
  have pm : PolMatch B (reG G V V' W) X R₂ Rf₂ (∑ i, pure (u i) (φ i)) (Λ • ∑ i, pure (u' i) (φ' i)) := by
    refine ⟨S, hS, k, k', u, φ, fun i => Λ • u' i, φ', fun i => ⟨hu i, (h1 i).2⟩,
      fun i => ⟨Submodule.smul_mem _ _ (hw i), (h2 i).2⟩, rfl, e3, ?_⟩
    have := congrArg (TensorProduct.map e (PiTensorProduct.map fun v : S => ef v)) eq
    simp only [map_sum, TensorProduct.map_tmul, PiTensorProduct.map_tprod] at this
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (this.trans (Finset.sum_congr rfl fun j _ => ?_))
    · rw [← fu i, show e (R.p (T (u i))) = R₂.p (u i) from he _ (hu i)]
      simp only [hef _ _ ((h1 i).2.1 _)]
    · rw [← fu' j, show e (R.p' (T' (u' j))) = c • R₂.p' (u' j) from he' _ (hw j)]
      simp only [hef' _ _ ((h2 j).2.1 _)]
      rw [MultilinearMap.map_smul_univ, TensorProduct.smul_tmul_smul, map_smul, TensorProduct.smul_tmul',
        Finset.prod_coe_sort S cf, ← Finset.prod_subset hS fun v _ hv => cf1 v hv]
  have := hc _ _ (Submodule.smul_mem _ Λ (so_re V V' W so)) pm (x * h)
  rw [← e1, ← e2, I_move hI p1 s1, I_move hI p2 (so_le p2.good _ so), mul_assoc, ← I_smul]
  exact this

end GlobalTheory.CompanionTheory.ThetaK

end
