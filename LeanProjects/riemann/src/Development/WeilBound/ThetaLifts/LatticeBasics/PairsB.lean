import Development.WeilBound.ThetaLifts.LatticeBasics.PairsL
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.PlaneRemovalConfiguration

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct Classical
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dens
open PositivityTheory.ThKF (ArchOp PureAct)
open PositivityTheory.ThK (LocRepEx)

def PolFin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ U : Submodule ℂ (SInf F (Fin a × Fin (a + a'))), FiniteDimensional ℂ U ∧
      ∀ k ∈ KInf σ G.W B.emb, ∀ f₁ : SInf F _, Acts (evI F) (om (1, k)) f f₁ → f₁ ∈ U

namespace Prs

theorem countable_compactOpen (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    {U : Set X | IsOpen U ∧ IsCompact U}.Countable := by
  have hb := TopologicalSpace.isBasis_countableBasis X
  have hc := TopologicalSpace.countable_countableBasis X
  have hfin : {t : Set (Set X) | t.Finite ∧ t ⊆ TopologicalSpace.countableBasis X}.Countable :=
    Set.countable_setOf_finite_subset hc
  refine (hfin.image fun t => ⋃₀ t).mono ?_
  rintro U ⟨hU, hK⟩
  obtain ⟨S, hS, rfl⟩ := hb.open_eq_sUnion hU
  obtain ⟨t, htS, htf, hcov⟩ := hK.elim_finite_subcover_image (b := S) (c := fun s => s)
    (fun s hs => hb.isOpen (hS hs)) Set.sUnion_eq_biUnion.subset
  refine ⟨t, ⟨htf, htS.trans hS⟩, Set.Subset.antisymm ?_ ?_⟩
  · exact Set.sUnion_subset_sUnion htS
  · simpa [Set.sUnion_eq_biUnion] using hcov

theorem mem_span_indicator {X : Type} [TopologicalSpace X] {f : X → ℂ}
    (hf : f ∈ GlobalTheory.WeilM.SB X) :
    f ∈ Submodule.span ℂ
      ((fun U : Set X => U.indicator (1 : X → ℂ)) '' {U : Set X | IsOpen U ∧ IsCompact U}) := by
  classical
  obtain ⟨hl, hK⟩ := hf
  have hK' : IsCompact (tsupport f) := hK
  obtain ⟨t, ht⟩ := hK'.elim_finite_subcover (fun c : ℂ => f ⁻¹' {c})
    (fun c => hl.isOpen_fiber c) (fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩)
  have hsum : f = ∑ c ∈ t, c • (f ⁻¹' {c}).indicator (1 : X → ℂ) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, Set.indicator_apply, Set.mem_preimage,
      Set.mem_singleton_iff, Pi.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · by_contra hne
      have hx : x ∈ tsupport f := subset_tsupport f (fun h0 => hne (by simpa using h0))
      obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 (ht hx)
      have : f x = c := hxc
      exact h (this ▸ hc)
  rw [hsum]
  refine Submodule.sum_mem _ fun c _ => ?_
  by_cases hc : c = 0
  · simp [hc]
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨hl.isOpen_fiber c, ?_⟩, rfl⟩)
    refine hK'.of_isClosed_subset (hl.isClosed_fiber c) fun x hx => subset_tsupport f ?_
    have : f x = c := hx
    simpa [Function.mem_support, this] using hc

theorem rank_SB_le (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    Module.rank ℂ (GlobalTheory.WeilM.SB X) ≤ Cardinal.aleph0 := by
  have hle : GlobalTheory.WeilM.SB X ≤ Submodule.span ℂ
      ((fun U : Set X => U.indicator (1 : X → ℂ)) '' {U : Set X | IsOpen U ∧ IsCompact U}) :=
    fun f hf => mem_span_indicator hf
  refine (Submodule.rank_mono hle).trans ((rank_span_le _).trans ?_)
  exact Cardinal.le_aleph0_iff_set_countable.2 ((countable_compactOpen X).image _)

theorem rank_SB_Fv : ∀ {F : Type} [Field F] [NumberField F] (v : Pl F) (κ : Type) [Finite κ],
    Module.rank ℂ (GlobalTheory.WeilM.SB (κ → Fv F v)) ≤ Cardinal.aleph0 := by
  intro F _ _ v κ _
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : SecondCountableTopology (Fv F v) := secondCountable_of_proper
  exact rank_SB_le _

theorem cartan_one {n r : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (hs : HasSig M r 0) (h : IsCartan M θ) : θ = 1 := by
  obtain ⟨rfl, A, hA⟩ := hs
  let P : Matrix (Fin r) (Fin r) ℂ := A.submatrix id Sum.inl
  have e : Pᵀ * (M * P.map star) = 1 := by
    rw [← Matrix.mul_assoc]
    exact Matrix.ext fun i j => congrFun (congrFun hA (Sum.inl i)) (Sum.inl j)
  have e' : P * (M * P.map star)ᵀ = 1 := by
    rw [mul_eq_one_comm, ← transpose_transpose P, ← transpose_mul, transpose_transpose, e, transpose_one]
  have pos : ∀ x : Fin r → ℂ, 0 ≤ (x ⬝ᵥ M *ᵥ star x).re := fun x => by
    obtain ⟨y, rfl⟩ : ∃ y, x = P *ᵥ y := ⟨(M * P.map star)ᵀ *ᵥ x, by rw [mulVec_mulVec, e', one_mulVec]⟩
    have : star (P *ᵥ y) = P.map star *ᵥ star y := funext fun i => by simp [Matrix.mulVec, dotProduct]
    rw [this, mulVec_mulVec, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, e, one_mulVec]
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.re_sum, Complex.ofReal_re]
    exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  refine Matrix.ext_iff_mulVec.2 fun u => ?_
  by_contra hu
  rw [one_mulVec] at hu
  have h1 := h.2.2 (θ *ᵥ u - u) (sub_ne_zero.2 hu)
  rw [mulVec_sub, mulVec_mulVec, h.1, one_mulVec, ← neg_sub, neg_dotProduct, Complex.neg_re] at h1
  linarith [pos (θ *ᵥ u - u)]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
  {B : Base F E} {R : RealMaps F a a'} {Rf : FinMaps F a a'} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
  {om' : Rep σ G.V' G.W}

theorem comm_theta (ht : IsTriple B G X om om') (hp : G.p = 0) (hq : G.q = 0) (w) (A) : Commute A (G.W.θ w) := by
  have h := ht.geo.hW.sig w
  rw [hp, hq] at h
  rw [cartan_one h (ht.geo.hW.cartan w)]
  exact Commute.one_right _

theorem deriv_mem {κ : Type} [Fintype κ] (U : Submodule ℂ (SInf F κ)) [FiniteDimensional ℂ U] (u : ℝ → SInf F κ)
    (hu : ∀ t, u t ∈ U) (f : SInf F κ) (h : ∀ x, HasDerivAt (fun t => u t x) (f x) 0) : f ∈ U := by
  let c : SInf F κ →ₗ[ℂ] (κ → mixedEmbedding.mixedSpace F) → ℂ := ⟨⟨fun g => g, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  have h1 : Tendsto (fun t : ℝ => c (((t : ℂ)⁻¹) • (u t - u 0))) (𝓝[≠] 0) (𝓝 (c f)) := tendsto_pi_nhds.2 fun x => by
    refine (h x).tendsto_slope_zero.congr fun t => ?_
    show _ = (t : ℂ)⁻¹ * (u t x - u 0 x)
    rw [zero_add, Complex.real_smul, Complex.ofReal_inv]
  obtain ⟨g, hg, e⟩ := (U.map c).closed_of_finiteDimensional.mem_of_tendsto h1
    (Eventually.of_forall fun t => ⟨_, U.smul_mem _ (sub_mem (hu t) (hu 0)), rfl⟩)
  exact (DFunLike.coe_injective e : g = f) ▸ hg

theorem rank_pi (hm : IsMatched B G X om om' R Rf) (v : Pl F) : Module.rank ℂ (Rf.Pi v) ≤ Cardinal.aleph0 := by
  rw [← rank_top, ← hm.fin.onto v]
  exact (rank_map_le _ _).trans (rank_SB_Fv _ _)

theorem irr_inf (hO : ArchOp) (hF : PolFin) (hm : IsMatched B G X om om' R Rf) (hp : G.p = 0) (hq : G.q = 0) (N : Submodule ℂ R.Pi)
    (h : ∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F _,
      Acts (evI F) (om (1, k)) f f₁ → R.p f ∈ N → R.p f₁ ∈ N) : N = ⊥ ∨ N = ⊤ := by
  refine hm.real.irred N (fun γ hγ f hf f₁ hd hN => ?_) h
  obtain ⟨U, hU, H⟩ := hF F E σ B a a' G X om om' hm.triple f hf
  have hk : ∀ t : ℝ, γ (Multiplicative.ofAdd t) ∈ KInf σ G.W B.emb := fun t => ⟨hγ.2 _, fun w => comm_theta hm.triple hp hq w _⟩
  choose A hA using fun t : ℝ => inf_op hO (PositivityTheory.ThKG.pairV hm.triple) (hk t)
  have hM := hm.triple.geo.hM
  have hr := Dat.rest (T := ∅) hM ⟨hf, fun v => (hM.vac v).1, fun _ _ => rfl⟩
  have : ∀ v, ∃ b, G.M.vac v b ≠ 0 ∧
      (G.M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 → ∀ i, b i ∈ v.adicCompletionIntegers F) := fun v => by
    obtain ⟨b, hb⟩ := Function.ne_iff.1 (hM.vac v).2.1
    exact ⟨b, hb, fun e => by rw [e] at hb; exact Set.mem_of_indicator_ne_zero hb⟩
  choose b hb hb' using this
  let y : Fin a × Fin (a + a') → Af F := fun i => ⟨fun v => b v i, hM.std.mono fun v e => hb' v e i⟩
  have hc : (∏ᶠ v, G.M.vac v (b v)) ≠ 0 := finprod_induction (· ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) hb
  haveI : FiniteDimensional ℂ ↥(U ⊓ N.comap R.p) := Submodule.finiteDimensional_inf_left _ _
  refine (deriv_mem (U ⊓ N.comap R.p) (fun t => A t f) (fun t => ⟨H _ (hk t) _ (hA t f hf).2,
    h _ (hk t) f hf _ (hA t f hf).2 hN⟩) f₁ fun x => ?_).2
  let z : Fin a × Fin (a + a') → AF F := fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i) : Ainf F × Af F)
  have e : ∀ g : SInf F (Fin a × Fin (a + a')), tens (evI F) g (finPart G.M.vac) z = g x * ∏ᶠ v, G.M.vac v (b v) := fun g =>
    congrArg (fun u => g u * _) (funext fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _)
  have := (hd _ hr z).div_const (∏ᶠ v, G.M.vac v (b v))
  simpa only [fun t => (hA t f hf).2 _ hr, e, mul_div_cancel_right₀ _ hc] using this

theorem fill (hL : LocRepEx) (hP : PureAct) (hO : ArchOp) (hF : PolFin) (hm : IsMatched B G X om om' R Rf) (hp : G.p = 0) (hq : G.q = 0) (T : Finset (Pl F))
    (N : Submodule ℂ (Fn F a (a + a'))) (hN : ∀ h, ∀ Φ ∈ N, om (1, h) Φ ∈ N) {Φ₀ ξ₀} (h0 : Φ₀ ∈ N)
    (c0 : (Φ₀, ξ₀) ∈ Cl B G.M R.p Rf.p T) (n0 : ξ₀ ≠ 0) (ξ) : ∃ Φ ∈ N, (Φ, ξ) ∈ Cl B G.M R.p Rf.p T := by
  let S : Submodule ℂ (PiT R Rf T) := (Cl B G.M R.p Rf.p T ⊓ N.prod ⊤).map (LinearMap.snd _ _ _)
  have mS : ∀ η, η ∈ S ↔ ∃ Φ ∈ N, (Φ, η) ∈ Cl B G.M R.p Rf.p T := fun η =>
    ⟨by rintro ⟨z, ⟨h1, h2, -⟩, rfl⟩; exact ⟨z.1, h2, h1⟩, fun ⟨Φ, h1, h2⟩ => ⟨(Φ, η), ⟨h2, h1, trivial⟩, rfl⟩⟩
  obtain ⟨a₀, ha₀, hy⟩ := exists_tmul_mem (A := R.Pi) (X := fun v : T => Rf.Pi v)
    (fun v => {Op | ∃ h, ∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ ∧ Op (Rf.p v φ) = Rf.p v φ₁})
    (fun v => rank_pi hm v) (fun v => hm.fin.nontriv v)
    (fun v P hs => hm.fin.irred v P fun h hh φ hφ φ₁ h₁ hact hφP => by
      obtain ⟨Op, o1, o2, -⟩ := fin_ops hL hm hh
      rw [← o2 φ hφ φ₁ h₁ hact]
      exact hs Op ⟨h, o1⟩ _ hφP) S
    (by
      rintro v Op ⟨h, o⟩ η hη
      obtain ⟨Φ, h1, h2⟩ := (mS η).1 hη
      exact (mS _).2 ⟨_, hN h Φ h1, cl_fin hP hm.triple.geo.hM v _ Op o h2⟩) ξ₀ ((mS _).2 ⟨_, h0, c0⟩) n0
  let Ni : Submodule ℂ R.Pi := ⨅ y, S.comap ((TensorProduct.mk ℂ R.Pi _).flip y)
  have mN : ∀ u, u ∈ Ni ↔ ∀ y, u ⊗ₜ[ℂ] y ∈ S := fun u => Submodule.mem_iInf _
  rcases irr_inf hO hF hm hp hq Ni (fun k hk f hf f₁ hact hmem => (mN _).2 fun y => by
    obtain ⟨Op, o1, o2, -⟩ := inf_ops hO hm hk
    obtain ⟨Φ, h1, h2⟩ := (mS _).1 ((mN _).1 hmem y)
    have := cl_inf hm.triple.geo.hM _ Op o1 h2
    rw [LinearMap.rTensor_tmul, o2 f hf f₁ hact] at this
    exact (mS _).2 ⟨_, hN k Φ h1, this⟩) with hb | ht
  · exact absurd ((Submodule.mem_bot ℂ).1 (hb ▸ (mN _).2 hy)) ha₀
  · refine (mS ξ).1 ?_
    induction ξ using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul u y => exact (mN u).1 (ht ▸ Submodule.mem_top) y

theorem pairs_lin (hm : IsMatched B G X om om' R Rf) {y y'} (h : y ∈ pairs B G X R Rf) (h' : y' ∈ pairs B G X R Rf) (c : ℂ) :
    y + c • y' ∈ pairs B G X R Rf :=
  ⟨add_mem h.1 (Submodule.smul_mem _ c h'.1), polMatch_add_smul hm h.2 h'.2 c⟩

end Prs

open Prs

theorem pairsStable_of (hS : PositivityTheory.ThKEnd.MatchStab) : PairsStable := fun F E _ _ _ _ _ σ B a a' G X om om' R Rf hm hp hq =>
  ⟨fun _ h _ h' c => pairs_lin hm h h' c, fun y hy h =>
    hS F E σ B a a' G X om om' R Rf hm h (fun w => comm_theta hm.triple hp hq w _) y.1 y.2 hy.1 hy.2⟩

theorem pairsIrr_of (hL : LocRepEx) (hP : PureAct) (hO : ArchOp) (hF : PolFin) : PairsIrr := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hm hp hq N hsub hnull hst
  refine or_iff_not_imp_left.2 fun hn y hy => ?_
  push Not at hn
  obtain ⟨y₀, h0, n0⟩ := hn
  obtain ⟨T₀, hT₀, H₀⟩ := polMatch_big hm (hsub h0).2
  obtain ⟨T₁, -, H₁⟩ := polMatch_big hm hy.2
  have hT : X.T ⊆ T₀ ∪ T₁ := hT₀.trans Finset.subset_union_left
  obtain ⟨ξ₀, c0, -⟩ := H₀ _ (Finset.subset_union_left (s₂ := T₁))
  obtain ⟨ξ, c1, -⟩ := H₁ _ (Finset.subset_union_right (s₁ := T₀))
  obtain ⟨_, ⟨z, hz, rfl⟩, c2⟩ := fill hL hP hO hF hm hp hq _ (N.map (LinearMap.fst _ _ _))
    (by rintro h _ ⟨z, hz, rfl⟩; exact ⟨_, hst z hz h, rfl⟩) ⟨y₀, h0, rfl⟩ c0
    (fun e => n0 (polMatch_iff.2 ⟨_, hT, ξ₀, c0, e ▸ zero_mem _⟩)) ξ
  have h1 := hnull _ (pairs_lin hm hy (hsub hz) (-1))
    (polMatch_iff.2 ⟨_, hT, 0, by simpa [sub_eq_add_neg] using sub_mem c1 c2, zero_mem _⟩)
  simpa using N.add_mem h1 hz

end GlobalTheory.ThK.Dbl

end
