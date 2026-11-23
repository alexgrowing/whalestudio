import Development.WeilBound.ThetaLifts.FrameEstimates.TowerRallisLemma
import Development.WeilBound.ThetaLifts.FrameEstimates.ThickFrames
import Development.WeilBound.ThetaLifts.FrameEstimates.IsCompactIntV
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.SigThConst

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem exists_soFin (hF : SoFin) (hp : IsPair B M χX χW om r s r' s') {m : ℕ} (φ : Fin m → (Fin n × Fin d → Af F) → ℂ)
    (hφ : ∀ j, φ j ∈ SB _) : ∃ ψ : Fin m → (Fin n × Fin d → Af F) → ℂ, (∀ j, ψ j ∈ soFin B M) ∧
      ∀ w : Fin m → SInf F (Fin n × Fin d), ∑ j, pureA F (w j) (φ j) ∈ M.So B.ψ B.τ₁ →
        ∑ j, pureA F (w j) (φ j) = ∑ j, pureA F (w j) (ψ j) := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (soCoeff (B := B) M φ)
  let P := Submodule.linearProjOfIsCompl _ _ hQ
  let ψ : Fin m → (Fin n × Fin d → Af F) → ℂ := fun j => ∑ i, (P (Pi.single j 1) : Fin m → ℂ) i • φ i
  have hψ : ∀ j, ψ j ∈ soFin B M := fun j =>
    ⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hφ i), (P (Pi.single j 1)).2⟩
  have key : ∀ w : Fin m → SInf F (Fin n × Fin d), ∑ j, pureA F (w j) (φ j) ∈ M.So B.ψ B.τ₁ →
      ∑ j, pureA F (w j) (φ j) = ∑ j, pureA F (w j) (ψ j) := fun w hw => by
    obtain ⟨m', f', χ, hχ, e⟩ := (hF F E σ B n d X W M χX χW om r s r' s' hp).1 _ hw
    have hmem : ∀ x, (fun j => w j x) ∈ soCoeff (B := B) M φ := fun x f₀ => by
      have e2 : ∑ j, w j x • φ j = ∑ i, f' i x • χ i := by
        funext y
        obtain ⟨z, hz1, hz2⟩ : ∃ z : Fin n × Fin d → AdeleRing (𝓞 F) F,
            (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) = x ∧ (fun i => (z i).2) = y :=
          ⟨fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i),
            funext fun i => RingEquiv.apply_symm_apply _ _, rfl⟩
        have := congrFun e z
        simp only [Finset.sum_apply, pureA, hz1, hz2] at this
        simpa [Finset.sum_apply] using this
      have e3 : pureA F f₀ (∑ i, f' i x • χ i) = ∑ i, f' i x • pureA F f₀ (χ i) := by
        funext z; simp [pureA, Finset.mul_sum, Finset.sum_apply]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [e2, e3]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ((hχ i).2 f₀)
    funext z
    set x : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1
    have e4 : (fun j => w j x) = ∑ j, w j x • (P (Pi.single j 1) : Fin m → ℂ) := by
      have a1 : (P (fun j => w j x) : Fin m → ℂ) = fun j => w j x :=
        congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hQ ⟨_, hmem x⟩)
      have a2 : (fun j => w j x) = ∑ j, w j x • (Pi.single j 1 : Fin m → ℂ) := by
        funext i; simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [← a1, a2]
      simp
    have e5 : ∀ i, w i x = ∑ j, w j x * (P (Pi.single j 1) : Fin m → ℂ) i := fun i => by
      simpa [Finset.sum_apply] using congrFun e4 i
    simp only [Finset.sum_apply, pureA, ψ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show w i (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) = _ from e5 i, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
  exact ⟨ψ, hψ, key⟩

theorem polData_sum (hp : IsPair B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ PolData B M) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → (Fin n × Fin d → Af F) → ℂ),
      (∀ i, f i ∈ M.Pol B.ψ B.emb) ∧ (∀ i, φ i ∈ SB _) ∧ Φ = ∑ i, pureA F (f i) (φ i) := by
  obtain ⟨m, c, x, rfl⟩ := Submodule.mem_span_set'.1 hΦ
  choose f hf χ h1 h2 h3 using fun i => (x i).2
  refine ⟨m, fun i => c i • f i, fun i => FiniteAdelicSupportCompactness.pf (χ i), fun i => Submodule.smul_mem _ _ (hf i),
    fun i => FiniteAdelicSupportCompactness.pf_mem ⟨h1 i, ((h2 i).and hp.good.std).mono fun v hv => hv.1.trans hv.2⟩,
    Finset.sum_congr rfl fun i _ => ?_⟩
  rw [h3 i, FiniteAdelicSupportCompactness.pure_eq]
  funext z
  simp [pureA, mul_assoc]

variable (B W) in

def Nice (f : UA σ W.J → ℂ) : Prop := LeftInv f ∧ UMG W f ∧ SmoothFin W B.emb f

theorem nice_zero : Nice B W (0 : UA σ W.J → ℂ) :=
  ⟨fun _ _ _ => rfl, ⟨0, {0}, rfl, by
    rintro _ rfl
    exact ⟨continuous_const, ⟨0, fun h => by simp⟩, fun γ _ => ⟨0, rfl, fun h => hasDerivAt_const _ _⟩⟩⟩,
    Set.univ, univ_mem, fun _ _ _ _ => rfl⟩

theorem Nice.lin (hU : UMGLin) (hc : IsCMExt F E σ) (hJ : EpsHerm σ W.J) {f f' : UA σ W.J → ℂ} (h : Nice B W f)
    (h' : Nice B W f') (a b : ℂ) : Nice B W (a • f + b • f') := by
  refine ⟨fun γ hγ x => ?_, hU F E σ hc B.emb d W hJ f f' h.2.1 h'.2.1 a b, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, h.1 γ hγ x, h'.1 γ hγ x]
  · obtain ⟨U, hU1, hu⟩ := h.2.2
    obtain ⟨U', hU1', hu'⟩ := h'.2.2
    refine ⟨U ∩ U', inter_mem hU1 hU1', fun u hm h1 x => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, hu u hm.1 h1 x, hu' u hm.2 h1 x]

theorem nice_sum (hB : ThetaBasic) (hU : UMGLin) (hE : EpsOf) (hG : IUMG) (hI : IInv) (hp : IsPair B M χX χW om r s r' s')
    {𝓕} (hD : Dom M om 𝓕) {m : ℕ} (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → (Fin n × Fin d → Af F) → ℂ)
    (hf : ∀ i, f i ∈ M.Pol B.ψ B.emb) (hφ : ∀ i, φ i ∈ 𝓕) (hsb : ∀ i, φ i ∈ SB _) :
    Nice B W (M.I om (∑ i, pureA F (f i) (φ i))) := by
  obtain ⟨hJ, -, -⟩ := hE F E σ B hp.base d W r' s' (Or.inr hp.skew)
  have e : M.I om (∑ i, pureA F (f i) (φ i)) = ∑ i, M.I om (pureA F (f i) (φ i)) :=
    funext fun h => ((dom_sum hB hp hD f φ hφ hsb).2.2 h).trans (Finset.sum_apply _ _ _).symm
  rw [e]
  refine Finset.sum_induction _ _ (fun a b ha hb => by simpa using ha.lin hU hp.base.cm hJ hb 1 1) nice_zero fun i _ => ?_
  exact ⟨(hI F E σ B n d X W M χX χW om r s r' s' hp _ (pureA_mem _ (hsb i))).1,
    hG F E σ B n d X W M χX χW om r s r' s' hp 𝓕 hD _ (hφ i) (hsb i) _ (hf i)⟩

end

theorem sig_nice (hB : ThetaBasic) (hU : UMGLin) (hE : EpsOf) (hG : IUMG) (hI : IInv) (hT : TriplePair) (hW : DomWeil)
    (hS : DomSoU) (hF : SoFin) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (ht' : IsTriple B G X om om') {f : UA σ G.W.J → ℂ} (hf : f ∈ PositivityTheory.ThKEnd.Sig B G om om') :
    Nice B G.W f := by
  obtain ⟨h1, h2, h3⟩ := hT F E σ B a a' G X om om' ht'
  obtain ⟨Φ, hΦ, Φ', hΦ', rfl⟩ := hf
  obtain ⟨hJ, -, -⟩ := hE F E σ B h1.base _ G.W _ _ (Or.inr h1.skew)
  obtain ⟨m, f, φ, c1, c2, rfl⟩ := polData_sum h1 hΦ
  obtain ⟨m', f', φ', c1', c2', rfl⟩ := polData_sum h2 hΦ'.1
  obtain ⟨ψ, hψ, hk⟩ := exists_soFin hF h2 φ' c2'
  rw [hk f' hΦ'.2]
  have n1 := nice_sum hB hU hE hG hI h1 (hW F E σ B _ _ _ _ _ _ _ om _ _ _ _ h1 (Or.inl h3)) f φ c1 c2 c2
  have n2 := nice_sum hB hU hE hG hI h2 (dom_of_domSoU hS h2) f' ψ c1' hψ fun i => (hψ i).1
  simpa [sub_eq_add_neg] using n1.lin hU h1.base.cm hJ n2 1 (-1)

theorem sigRapid_of (hB : ThetaBasic) (hU : UMGLin) (hE : EpsOf) (hG : IUMG) (hI : IInv) (hT : TriplePair) (hW : DomWeil)
    (hS : DomSoU) (hF : SoFin) (hC : CuspRapid) : PositivityTheory.ThKEnd.Orth.SigRapid := by
  intro F E _ _ _ _ _ σ B a a' G X om om' ht' f hf hc
  obtain ⟨n1, n2, n3⟩ := sig_nice hB hU hE hG hI hT hW hS hF ht' hf
  obtain ⟨h1, -, -⟩ := hT F E σ B a a' G X om om' ht'
  obtain ⟨hJ, -, -⟩ := hE F E σ B h1.base _ G.W _ _ (Or.inr h1.skew)
  refine ⟨?_, n1, hC F E σ h1.base.cm B.emb _ G.W hJ f n1 n2 n3 hc⟩
  obtain ⟨k, S, hS1, hS2⟩ := n2
  exact (hS2 f hS1).1

end PositivityTheory.ThKEst

end
