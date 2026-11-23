import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeAlgebraMap

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing

namespace GlobalTheory.Vanishing

open H0

variable {Y T : Scheme.{0}} {k k' : Type} [CommRing k] [CommRing k'] {p : Y ⟶ Sp k} {q : T ⟶ Sp k'} {φ : k →+* k'}
  {r : T ⟶ Y} {P B N : LB Y} {P' B' N' : LB T} {O : Y.Opens} {W : T.Opens}

theorem pullChart_ofSec (a : ChartPull B' B r) (hq : r ≫ p = q ≫ spMap φ) (h : W ≤ r ⁻¹ᵁ O) (s : B.Sec) :
    pullChart a hq h (H0.ofSec p O s) = H0.ofSec q W (GlobalTheory.chartSec a s) :=
  LB.sec_ext fun i => fun_ext_ger fun z hz => by
    change germ i z hz.1 hz.2 _ = germ i z hz.1 hz.2 _
    rw [germ_pullChart, germ_ofSec]
    exact (congrArg _ (germ_ofSec _ _ _ _ s)).trans (ger_appLE r _ z hz.2 _).symm

theorem pullChart_mul (C : ProdChart P B N) (C' : ProdChart P' B' N') (a : ChartPull P' P r) (b : ChartPull B' B r)
    (c : ChartPull N' N r) (hC : ∀ t, ∃ s, a.idx (C'.a t) = C.a s ∧ b.idx (C'.b t) = C.b s ∧ c.idx (C'.c t) = C.c s)
    (hq : r ≫ p = q ≫ spMap φ) (h : W ≤ r ⁻¹ᵁ O) (σ : H0 p P O) (f : H0 p B O) :
    pullChart c hq h (C.mul σ f) = C'.mul (pullChart a hq h σ) (pullChart b hq h f) :=
  C'.sec_ext fun t z hz ha hb hc => by
    obtain ⟨s, e₁, e₂, e₃⟩ := hC t
    have key (y hy i j l) (e₁ : i = C.a s) (e₂ : j = C.b s) (e₃ : l = C.c s) (hi hj hl) :
        germ l y hy hl (C.mul σ f) = germ i y hy hi σ * germ j y hy hj f := by
      subst e₁ e₂ e₃
      exact C.germ_mul σ f s y hy hi hj hl
    rw [C'.germ_mul _ _ t z hz ha hb hc, germ_pullChart, germ_pullChart, germ_pullChart, ← map_mul]
    exact congrArg _ (key _ _ _ _ _ e₁ e₂ e₃ _ _ _)

end GlobalTheory.Vanishing

namespace GlobalTheory.HermTools

theorem csq_extend {K E V V' : Type*} [Field K] [Field E] [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module E V'] {j : K →+* E} {ι : V →ₛₗ[j] V'} (hι : IsExtension ι) [FiniteDimensional K V] (h : HermFam K V)
    (τ : E →+* ℂ) {κ : Type*} [Fintype κ] (c : κ → ℂ) (v : κ → V) :
    csq (extend hι h) τ c (fun i => ι (v i)) = csq h (τ.comp j) c v := by
  simp only [csq, form_extend]

theorem cnrm_extend_comb {K E V V' : Type*} [Field K] [Field E] [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module E V'] {j : K →+* E} {ι : V →ₛₗ[j] V'} (hι : IsExtension ι) [FiniteDimensional K V] (h : HermFam K V)
    (τ : E →+* ℂ) {κ μ : Type*} [Fintype κ] [Fintype μ] (c : κ → ℂ) (a : κ → μ → E) (v : μ → V) :
    cnrm (extend hι h) τ c (fun i => ∑ l, a i l • ι (v l)) =
      cnrm h (τ.comp j) (fun l => ∑ i, c i * τ (a i l)) v :=
  congrArg Real.sqrt ((csq_comb _ _ _ _ _).trans (csq_extend hι h τ _ v))

end GlobalTheory.HermTools

namespace GlobalTheory.Adelic.HermSys

variable {F : Type} [Field F] [NumberField F] {T : HermSys F} (E : Type) [Field E] [NumberField E] [Algebra F E]

theorem normAt_baseChange (τ : E →+* ℂ) (u : Fin T.N → F) :
    (T.baseChange E).normAt τ (fun j => algebraMap F E (u j)) = T.normAt (τ.comp (algebraMap F E)) u := rfl

theorem NormsLe.baseChange (h : T.NormsLe) : (T.baseChange E).NormsLe :=
  fun k τ => (normAt_baseChange E τ (T.w.col k)).trans_le (h k _)

end GlobalTheory.Adelic.HermSys

namespace GlobalTheory.HilbertSamuel

variable {F : Type} [Field F] [NumberField F]

theorem meanLog_baseChange (E : Type) [Field E] [NumberField E] [Algebra F E] (β : (F →+* ℂ) → ℝ) :
    meanLog E (fun τ => β (τ.comp (algebraMap F E))) = meanLog F β := by
  have h₁ : (Module.finrank F E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [meanLog, meanLog, ← Module.finrank_mul_finrank ℚ F E, Nat.cast_mul,
    Adelic.HeightExt.sum_comp_algebraMap fun σ => Real.log (β σ), mul_comm (Module.finrank ℚ F : ℝ),
    mul_div_mul_left _ _ h₁]

namespace Geo

variable (G : Geo F) (E : Type) [Field E] [NumberField E] [Algebra F E]

theorem toExt_mulW (j : ℕ) (u : Fin G.N → F) (f : G.Sec j) :
    G.toExt E (j + 1) (G.mulW j u f) = (G.baseChange E).mulW j (algebraMap F E ∘ u) (G.toExt E j f) := by
  refine (pullChart_mul _ (oneChart (isLB_tens (G.baseChange E).K.isLB (G.baseChange E).isLBA) (G.baseChange E).isLB
    (Nat.cast_succ j).symm) (GlobalTheory.chartPullPull G.L (G.fst E)) (G.chartAdj E j) (G.chartAdj E (j + 1))
    (fun t => ⟨((t.1.1 PUnit.unit, t.1.2 PUnit.unit), t.2 PUnit.unit), rfl, rfl, rfl⟩) _ le_rfl _ f).trans ?_
  refine congrArg (fun s => ProdChart.mul _ s _) ?_
  rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (map_smulₛₗ _ _ _).trans (congrArg _ (pullChart_ofSec _ _ _ (G.b k)))

def chartAdj₂ (j : ℕ) : ChartPull ((G.baseChange E).adj₂ j) (G.adj₂ j) (G.fst E) :=
  chartPullTwist (chartPullTens (GlobalTheory.chartPullPull G.K.bundle _) (GlobalTheory.chartPullPull G.L₂ _))
    (GlobalTheory.chartPullPull G.L _) (j + G.D)

def toExt₂ (j : ℕ) : H0 G.str (G.adj₂ j) ⊤ →ₛₗ[algebraMap F E]
    H0 (G.baseChange E).str ((G.baseChange E).adj₂ j) ⊤ :=
  pullChart (G.chartAdj₂ E j) (G.isPullback_fst E).w le_top

theorem isExtension_toExt₂ (j : ℕ) : IsExtension (G.toExt₂ E j) :=
  isExtension_pullChart_top (G.isPullback_fst E) (isLB_tw (isLB_tens G.K.isLB G.isLB₂) G.isLB _)
    (isLB_tw (isLB_tens (G.baseChange E).K.isLB (G.baseChange E).isLB₂) (G.baseChange E).isLB _)
    (G.chartAdj₂ E j) G.geom.alg.variety.proj (G.baseChange E).geom.alg.variety.proj

theorem toExt_mulE (j : ℕ) (f : H0 G.str (G.adj₂ j) ⊤) :
    G.toExt E j (G.mulE j f) = (G.baseChange E).mulE j (G.toExt₂ E j f) := by
  refine (restr_pullChart (G.chartAdj E j) (G.isPullback_fst E).w (W := ⊤) le_top le_rfl le_top le_top _).symm.trans
    (congrArg _ ?_)
  refine (pullChart_mul _ (quotChart (G.baseChange E).K.isLB (G.baseChange E).isLBA (G.baseChange E).isLB₂
    (G.baseChange E).isLB rfl) (chartPullQuot (GlobalTheory.chartPullPull G.LA (G.fst E))
    (chartPullTwist (GlobalTheory.chartPullPull G.L₂ _) (GlobalTheory.chartPullPull G.L _) _)) (G.chartAdj₂ E j) (G.chartAdj E j)
    (fun t => ⟨(t.1 PUnit.unit, t.2.1 PUnit.unit, t.2.2.1 PUnit.unit, t.2.2.2 PUnit.unit), rfl, rfl, rfl⟩)
    _ le_top _ f).trans ?_
  exact congrArg (fun s => ProdChart.mul _ s _) (pullChart_ofSec _ _ _ G.e)

end Geo

namespace Data

variable {X : Data F} (E : Type) [Field E] [NumberField E] [Algebra F E]

variable (X) in

theorem toExtV_inclE {j : ℕ} (hj : j ≤ X.T) (f : H0 X.str (X.adj₂ j) ⊤) :
    X.toExtV E j (X.inclE hj f) = (X.baseChange E).inclE hj (X.toExt₂ E j f) :=
  Subtype.ext (X.toExt_mulE E j f)

variable (X) in

theorem toExtV_mem {j : ℕ} {x : X.V j} (hx : x ∈ X.M j) : X.toExtV E j x ∈ (X.baseChange E).M j :=
  (Submodule.subset_span ⟨x, hx, rfl⟩ : extMap (X.toExt E j) (X.V j) x ∈
    Submodule.span (𝓞 E) (extMap (X.toExt E j) (X.V j) '' X.M j))

theorem MulStable.baseChange (h : X.MulStable) : (X.baseChange E).MulStable := fun j hj w hw f hf => by
  let X' := X.baseChange E
  let S := (X'.M (j + 1)).map ((X'.V (j + 1)).subtype.restrictScalars (𝓞 E))
  change X'.mulW j w f ∈ S
  induction hw using Submodule.span_induction with
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [← algebraMap_smul E, map_smul, LinearMap.smul_apply, algebraMap_smul]; exact S.smul_mem _ ha
  | mem w hw =>
    obtain ⟨k, rfl⟩ := hw
    induction hf using Submodule.span_induction with
    | zero => exact (map_zero (X'.mulW j _)).symm ▸ zero_mem _
    | add a b _ _ ha hb => exact (map_add (X'.mulW j _) _ _).symm ▸ add_mem ha hb
    | smul c a _ ha =>
      exact (map_smul (X'.mulW j _) (algebraMap _ E c) _).symm ▸ S.smul_mem c ha
    | mem f hf =>
      obtain ⟨f, hf, rfl⟩ := hf
      obtain ⟨g, hg, e⟩ := h j hj _ (Submodule.subset_span ⟨k, rfl⟩) f hf
      exact ⟨_, X.toExtV_mem E hg, (congrArg (X.toExt E (j + 1)) e).trans (X.toExt_mulW E j _ _)⟩

variable {E} in

theorem MulStable.mulBoundAt_baseChange (h : X.MulStable) {τ : E →+* ℂ} {β : ℝ}
    (hb : X.MulBoundAt (τ.comp (algebraMap F E)) β) : (X.baseChange E).MulBoundAt τ β := by
  intro j hj u m c f g e
  let b := Module.finBasis F (X.V j)
  let b' := (X.isExtension_extMap E j).basis b
  let G : Fin X.N × Fin _ → X.V (j + 1) := fun t => ⟨_, h.mem hj (Pi.single t.1 1) (b t.2)⟩
  obtain ⟨a, rfl⟩ : ∃ a : Fin m → Fin _ → E, f = fun i => ∑ l, a i l • X.toExtV E j (b l) :=
    ⟨fun i l => b'.repr (f i) l, funext fun i => (b'.sum_repr (f i)).symm.trans
      (Finset.sum_congr rfl fun l _ => congrArg _ (IsExtension.basis_apply _ _ _))⟩
  have hG (t) : (X.toExtV E (j + 1) (G t) : (X.baseChange E).Sec (j + 1)) =
      (X.baseChange E).mulW j (Pi.single t.1 1) (X.toExtV E j (b t.2)) :=
    (X.toExt_mulW E j _ _).trans (congrArg (fun w => (X.baseChange E).mulW j w _)
      (funext fun l : Fin X.N => (by simp [Pi.single_apply] :
        algebraMap F E (Pi.single (M := fun _ => F) t.1 1 l) = Pi.single (M := fun _ => E) t.1 1 l)))
  change Fin X.N → ℂ at u
  obtain rfl : g = fun t : Fin X.N × Fin m => ∑ s, (if s.1 = t.1 then a t.2 s.2 else 0) • X.toExtV E (j + 1) (G s) :=
    funext fun t : Fin X.N × Fin m => Subtype.ext <| (e t.1 t.2).trans <| by
      simp only [Fintype.sum_prod_type, ite_smul, zero_smul, Finset.sum_ite_irrel, Finset.sum_const_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, hG]
  refine (cnrm_extend_comb (X.isExtension_extMap E (j + 1)) _ τ _ _ G).trans_le
    (le_of_eq_of_le (congrArg (cnrm _ _ · G) (funext fun s => ?_))
    ((hb j hj u _ (fun l => ∑ i, c i * τ (a i l)) b G fun _ _ => rfl).trans_eq
      (congrArg _ (cnrm_extend_comb (X.isExtension_extMap E j) _ τ c a b).symm)))
  change ∑ t : Fin X.N × Fin m, u t.1 * c t.2 * τ (if s.1 = t.1 then a t.2 s.2 else 0) = _
  simp [Fintype.sum_prod_type, apply_ite τ, Finset.mul_sum, mul_assoc]

theorem MulStable.mulBound_baseChange (h : X.MulStable) {β : (F →+* ℂ) → ℝ} (hb : ∀ σ, X.MulBoundAt σ (β σ)) :
    (X.baseChange E).MulBound fun τ => β (τ.comp (algebraMap F E)) :=
  (h.baseChange E).mulBound fun _ => h.mulBoundAt_baseChange (hb _)

variable (X) in

theorem latRank_M_baseChange (j : ℕ) : latRank E ((X.baseChange E).M j) = latRank F (X.M j) := by
  rw [latRank_M, latRank_M, finrank_V_baseChange]

theorem ShortFamily.baseChange {j : ℕ} {Λ : ℝ} (h : X.ShortFamily j Λ) : (X.baseChange E).ShortFamily j Λ := by
  obtain ⟨v, h₁, h₂, h₃⟩ := h
  have e := X.latRank_M_baseChange E j
  exact ⟨fun i => X.toExtV E j (v (i.cast e)), fun i => X.toExtV_mem E (h₁ _),
    ((X.isExtension_extMap E j).indep _ v h₂).comp _ (Fin.cast_injective e),
    fun i τ => (X.nrm_toExtV E j τ _).trans_le (h₃ _ _)⟩

theorem ShortFamilyMean.baseChange {j : ℕ} {Λ : ℝ} (h : X.ShortFamilyMean j Λ) :
    (X.baseChange E).ShortFamilyMean j Λ := by
  obtain ⟨v, h₁, h₂, h₃⟩ := h
  have e := X.latRank_M_baseChange E j
  refine ⟨fun i => X.toExtV E j (v (i.cast e)), fun i => X.toExtV_mem E (h₁ _),
    ((X.isExtension_extMap E j).indep _ v h₂).comp _ (Fin.cast_injective e), fun i => le_of_eq_of_le ?_ (h₃ (i.cast e))⟩
  exact (congrArg _ (funext fun τ => X.nrm_toExtV E j τ _)).trans
    (meanLog_baseChange E fun σ => (X.nm j).nrm σ (v (i.cast e)))

variable (X) in

theorem baseChange_mul_short :
    (∀ j u f, X.toExt E (j + 1) (X.mulW j u f) =
      (X.baseChange E).mulW j (algebraMap F E ∘ u) (X.toExt E j f)) ∧
    (∀ j f, X.toExt E j (X.mulE j f) = (X.baseChange E).mulE j (X.toExt₂ E j f)) ∧
    (X.MulStable → (X.baseChange E).MulStable) ∧
    (X.MulStable → ∀ (τ : E →+* ℂ) β, X.MulBoundAt (τ.comp (algebraMap F E)) β → (X.baseChange E).MulBoundAt τ β) ∧
    (X.MulStable → ∀ β : (F →+* ℂ) → ℝ, (∀ σ, X.MulBoundAt σ (β σ)) →
      (X.baseChange E).MulBound fun τ => β (τ.comp (algebraMap F E))) ∧
    (∀ j Λ, X.ShortFamily j Λ → (X.baseChange E).ShortFamily j Λ) ∧
    (∀ j Λ, X.ShortFamilyMean j Λ → (X.baseChange E).ShortFamilyMean j Λ) ∧
    (X.NormsLe → (X.baseChange E).NormsLe) ∧
    ∀ β : (F →+* ℂ) → ℝ, meanLog E (fun τ => β (τ.comp (algebraMap F E))) = meanLog F β :=
  ⟨X.toExt_mulW E, X.toExt_mulE E, fun h => h.baseChange E, fun h _ _ => h.mulBoundAt_baseChange,
    fun h _ => h.mulBound_baseChange E, fun _ _ h => h.baseChange E, fun _ _ h => h.baseChange E,
    fun h => h.baseChange E, meanLog_baseChange E⟩

end Data

end GlobalTheory.HilbertSamuel
