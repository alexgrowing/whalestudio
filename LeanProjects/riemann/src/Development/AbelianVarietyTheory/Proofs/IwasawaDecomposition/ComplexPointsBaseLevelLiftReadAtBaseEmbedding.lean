import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.LiftForms

theorem exists_mat {K K' : Type} [Field K] [Field K'] (φ : K →+* K') {n n' : ℕ} (hn : n = n')
    (V : Submodule K (Fin n → K)) (V' : Submodule K' (Fin n' → K'))
    (hV : V' = Submodule.span K' {x' | ∃ x ∈ V, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)}) :
    ∃ G : Matrix (Fin (Module.finrank K' V')) (Fin (Module.finrank K V)) K', Function.Bijective G.mulVec ∧
      ∀ y : Fin (Module.finrank K V) → K, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' →
        (∑ l, (G.mulVec (fun i => φ (y i))) l • (Module.finBasis K' V' l : Fin n' → K')) k' =
          φ ((∑ i, y i • (Module.finBasis K V i : Fin n → K)) k) := by
  subst hn
  classical
  set b := Module.finBasis K V
  set Φ : (Fin n → K) → (Fin n → K') := fun x k => φ (x k) with hΦ
  have hrel : ∀ x' : Fin n → K', ∀ x : Fin n → K, (∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)) ↔ x' = Φ x := by
    intro x' x
    constructor
    · intro h; funext k; exact h k k rfl
    · rintro rfl k k' hk; rw [Fin.ext hk]
  have hS : {x' | ∃ x ∈ V, ∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)} = Φ '' V := by
    ext x'; simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨x, hx, h⟩; exact ⟨x, hx, ((hrel x' x).1 h).symm⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, (hrel _ x).2 rfl⟩
  rw [hS] at hV
  have hΦadd : ∀ x y, Φ (x + y) = Φ x + Φ y := fun x y => by funext k; simp [hΦ]
  have hΦsmul : ∀ (a : K) x, Φ (a • x) = φ a • Φ x := fun a x => by funext k; simp [hΦ]
  have hΦsum : ∀ y : Fin (Module.finrank K V) → K, Φ (∑ i, y i • (b i : Fin n → K)) = ∑ i, φ (y i) • Φ (b i) := by
    intro y
    funext k
    simp [hΦ, Finset.sum_apply, map_sum]
  let c : Fin (Module.finrank K V) → Fin n → K' := fun i => Φ (b i)
  have hc_mem : ∀ i, c i ∈ V' := fun i => hV ▸ Submodule.subset_span ⟨b i, (b i).2, rfl⟩
  have hli : LinearIndependent K' c := by
    letI := φ.toAlgebra
    have h0 : LinearIndependent K (fun i => (b i : Fin n → K)) := b.linearIndependent.map' V.subtype V.ker_subtype
    exact (linearIndependent_algebraMap_comp_iff).2 h0
  have hspan : Submodule.span K' (Set.range c) = V' := by
    apply le_antisymm
    · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hc_mem i
    · rw [hV, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : (⟨x, hx⟩ : V) = ∑ i, (b.repr ⟨x, hx⟩ i) • b i := (b.sum_repr _).symm
      have hx2 : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : Fin n → K) := by
        have := congrArg Subtype.val hx'
        rw [Submodule.coe_sum] at this
        simpa only [Submodule.coe_smul] using this
      rw [hx2, hΦsum]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let cV : Fin (Module.finrank K V) → V' := fun i => ⟨c i, hc_mem i⟩
  have hliV : LinearIndependent K' cV := LinearIndependent.of_comp V'.subtype hli
  have hspV : ⊤ ≤ Submodule.span K' (Set.range cV) := by
    rintro ⟨x, hx⟩ _
    rw [← hspan] at hx
    have : Set.range c = V'.subtype '' Set.range cV := by
      ext z; simp [cV, c]
    rw [this, ← Submodule.map_span] at hx
    obtain ⟨w, hw, hwx⟩ := hx
    have : w = ⟨x, hspan ▸ (by rw [this, ← Submodule.map_span]; exact ⟨w, hw, hwx⟩)⟩ := Subtype.ext hwx
    rw [← this]; exact hw
  let bc : Module.Basis (Fin (Module.finrank K V)) K' V' := Module.Basis.mk hliV hspV
  set b' := Module.finBasis K' V'
  refine ⟨Matrix.of fun l i => b'.repr (bc i) l, ?_, ?_⟩
  · have hG : (Matrix.of fun l i => b'.repr (bc i) l).mulVec = fun y => b'.equivFun (bc.equivFun.symm y) := by
      funext y l
      simp [Matrix.mulVec, dotProduct, Module.Basis.equivFun_symm_apply, map_sum, mul_comm]
    rw [hG]
    exact b'.equivFun.bijective.comp bc.equivFun.symm.bijective
  · intro y k k' hk
    rw [← Fin.ext hk]
    have e1 : (∑ l, ((Matrix.of fun l i => b'.repr (bc i) l).mulVec (fun i => φ (y i))) l • (b' l : Fin n → K')) =
        ((∑ i, φ (y i) • bc i : V') : Fin n → K') := by
      have : ∑ l, ((Matrix.of fun l i => b'.repr (bc i) l).mulVec (fun i => φ (y i))) l • b' l = ∑ i, φ (y i) • bc i := by
        rw [← b'.sum_repr (∑ i, φ (y i) • bc i)]
        congr 1; funext l; congr 1
        simp [Matrix.mulVec, dotProduct, map_sum, mul_comm]
      have := congrArg Subtype.val this
      simpa [Submodule.coe_sum] using this
    rw [e1]
    have e2 : ((∑ i, φ (y i) • bc i : V') : Fin n → K') = ∑ i, φ (y i) • c i := by
      simp [Submodule.coe_sum, bc, cV]
    rw [e2, ← hΦsum]

theorem lat_coords {K K' : Type} [Field K] [Field K'] [NumberField K] [NumberField K'] (φ : K →+* K') {n n' d d' : ℕ}
    (hn : n = n') (b : Fin d → Fin n → K) (b' : Fin d' → Fin n' → K') (hb' : LinearIndependent K' b')
    (G : Matrix (Fin d') (Fin d) K')
    (hG : ∀ y : Fin d → K, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' →
        (∑ l, (G.mulVec (fun i => φ (y i))) l • b' l) k' = φ ((∑ i, y i • b i) k))
    (M : Submodule (𝓞 K) (Fin n → K)) (hM : ∀ x ∈ M, x ∈ Submodule.span K (Set.range b))
    (M' : Submodule (𝓞 K') (Fin n' → K'))
    (hM' : M' = Submodule.span (𝓞 K') {x' | ∃ x ∈ M, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)}) :
    M'.comap ((Fintype.linearCombination K' b').restrictScalars (𝓞 K')) =
      Submodule.span (𝓞 K') ((fun y : Fin d → K => G.mulVec fun i => φ (y i)) ''
        (M.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K)) : Set (Fin d → K))) := by
  subst hn
  set L' := (Fintype.linearCombination K' b').restrictScalars (𝓞 K') with hL'
  have hL'apply : ∀ c, L' c = ∑ l, c l • b' l := fun c => by
    simp [hL', Fintype.linearCombination_apply]
  have key : ∀ y : Fin d → K, L' (G.mulVec fun i => φ (y i)) = fun k => φ ((∑ i, y i • b i) k) := by
    intro y; funext k; rw [hL'apply]; exact hG y k k rfl
  have hinj : Function.Injective L' := by
    intro c₁ c₂ h
    rw [hL'apply, hL'apply] at h
    have h0 : ∑ l, (c₁ - c₂) l • b' l = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self]
    funext l
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hb' _ h0 l)
  apply le_antisymm
  · intro c hc
    have hc' : L' c ∈ M' := hc
    have hle : M' ≤ (Submodule.span (𝓞 K') ((fun y : Fin d → K => G.mulVec fun i => φ (y i)) ''
        (M.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K)) : Set (Fin d → K)))).map L' := by
      rw [hM', Submodule.span_le]
      rintro x' ⟨x, hx, hrel⟩
      obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hM x hx)
      have hyM : y ∈ M.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K)) := by
        show (Fintype.linearCombination K b) y ∈ M
        rw [Fintype.linearCombination_apply, hy]; exact hx
      have : x' = L' (G.mulVec fun i => φ (y i)) := by
        rw [key y, hy]; funext k; exact hrel k k rfl
      rw [this]
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨y, hyM, rfl⟩)
    obtain ⟨e, he, hec⟩ := hle hc'
    rw [← hinj hec]; exact he
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    show L' (G.mulVec fun i => φ (y i)) ∈ M'
    rw [hM', key y]
    refine Submodule.subset_span ⟨∑ i, y i • b i, ?_, fun k k' hk => by rw [Fin.ext hk]⟩
    have : (Fintype.linearCombination K b) y ∈ M := hy
    rwa [Fintype.linearCombination_apply] at this

theorem complexPoints_baseLevelLift_readAtBaseEmbedding {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (i : Fin D.R.m)
    (y : Fin ((R.toCx3 F).dW false i) → D.what₂.LL) :
    @Tw.out (twAt D.what₂.embLL A3.A.v0) _ ((R.toCx3 F).w0C false i (cpt A3.fam3.base3.v0.embedding y)) =
      (R.FW i).j (sg0 D A3.A) (∑ k, y k • R.toRealDat.bL F.lv2 false i k) := by
  have hpos : (0:ℝ) < RealDat.nP F.lv2 false := by
    unfold RealDat.nP; exact_mod_cast Nat.card_pos
  set s := twAt D.what₂.embLL A3.A.v0
  set WS := R.toRealDat.WS F.lv2 false i (sg0 D A3.A)
  have h2 : (@Tw.out s WS ((R.toCx3 F).wC false i A3.fam3.base3.v0 (cpt A3.fam3.base3.v0.embedding y))) =
      ∑ k, cj s (cpt A3.fam3.base3.v0.embedding y k) • (⟨R.toRealDat.bC F.lv2 false i (sg0 D A3.A) k, Submodule.subset_span ⟨k, rfl⟩⟩ : WS) := by
    simp only [CxData.wC, lin, Fintype.linearCombination_apply]
    rfl
  have h1 : ∀ x : Tw s WS, @Tw.out s _ ((R.toCx3 F).eW false i x) = (((Real.sqrt (RealDat.nP F.lv2 false) : ℝ) : ℂ)) • ((Tw.out x : WS) : (R.HW i (sg0 D A3.A)).H) := fun x => rfl
  refine Eq.trans (h1 ((R.toCx3 F).wC false i A3.fam3.base3.v0 (cpt A3.fam3.base3.v0.embedding y))) ?_
  rw [h2, Submodule.coe_sum, Finset.smul_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Submodule.coe_smul, map_smulₛₗ, smul_comm]
  have he : cj s (cpt A3.fam3.base3.v0.embedding y k) = sg0 D A3.A (y k) := by
    show cj s (A3.A.v0.embedding (y k)) = _
    rw [emb_eq D.what₂.embLL A3.A.v0 (y k), cj_cj]
  rw [he]
  congr 1
  show ((Real.sqrt (RealDat.nP F.lv2 false) : ℝ) : ℂ) • ((((Real.sqrt (RealDat.nP F.lv2 false))⁻¹ : ℝ) : ℂ) • (R.FW i).j (sg0 D A3.A) (R.toRealDat.bL F.lv2 false i k)) = _
  rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.2 hpos).ne', Complex.ofReal_one, one_smul]

theorem liftWeight_complexPoint_eq_twist {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (i : Fin D.R.m)
    (y : Fin ((R.toCx3 F).dW false i) → D.what₂.LL) :
    HEq ((R.toCx3 F).w0C false i (cpt A3.fam3.base3.v0.embedding y))
      ((R.FW i).j D.what₂.embLL (∑ k, y k • R.toRealDat.bL F.lv2 false i k)) := by
  have e := complexPoints_baseLevelLift_readAtBaseEmbedding R F i y
  have hs : sg0 D A3.A = D.what₂.embLL := sgAt_mk _ R.hv0
  have key : ∀ (σ σ' : D.what₂.LL →+* ℂ), σ = σ' → ∀ v, HEq ((R.FW i).j σ v) ((R.FW i).j σ' v) := by
    intro σ σ' h v; subst h; rfl
  show HEq (@Tw.out (twAt D.what₂.embLL A3.A.v0) _ ((R.toCx3 F).w0C false i (cpt A3.fam3.base3.v0.embedding y))) _
  rw [e]
  exact key _ _ hs _

theorem nat_eq_of_heq {m m' : ℕ} (hm : m' = m) {f : Fin m → ℕ} {f' : Fin m' → ℕ} (h : HEq f' f) (i : Fin m) (i' : Fin m')
    (hi : (i : ℕ) = i') : f i = f' i' := by
  subst hm
  have := eq_of_heq h
  subst this
  rw [Fin.ext hi]

theorem mem_span_basis {K : Type} [Field K] {n : ℕ} (V : Submodule K (Fin n → K)) [Module.Finite K V] {x : Fin n → K}
    (hx : x ∈ V) : x ∈ Submodule.span K (Set.range fun k => (Module.finBasis K V k : Fin n → K)) := by
  have hx' : (⟨x, hx⟩ : V) = ∑ i, ((Module.finBasis K V).repr ⟨x, hx⟩ i) • Module.finBasis K V i := ((Module.finBasis K V).sum_repr _).symm
  have hx2 : x = ∑ i, ((Module.finBasis K V).repr ⟨x, hx⟩ i) • (Module.finBasis K V i : Fin n → K) := by
    have := congrArg Subtype.val hx'
    rw [Submodule.coe_sum] at this
    simpa only [Submodule.coe_smul] using this
  rw [hx2]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.Mem.R3.LiftForms

end
