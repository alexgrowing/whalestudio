import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentPullChart
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing
open scoped ENNReal

namespace GlobalTheory.Adelic

variable {F : Type} [Field F] [NumberField F]

theorem LinSys.IsVariety.isIntegral {k : Type} [Field k] {S : LinSys k} (h : S.IsVariety) : IsIntegral S.Y :=
  have := h.smooth
  have := h.conn
  have : Smooth S.str := SmoothOfRelativeDimension.smooth S.D _
  isIntegral_of_smooth_of_geometricallyConnected S.str

theorem LinSys.ofSec_comb {k : Type} [Field k] (S : LinSys k) (O : S.Y.Opens) (u : Fin S.N → k) :
    H0.ofSec S.str O (S.comb u) = ∑ j, u j • H0.ofSec S.str O (S.b j) := by
  refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun j _ => Eq.trans
    (congrArg (fun a => H0.ofSec S.str O (a • S.b j)) (?_ : _ = algX S.str ⊤ (u j))) (H0.ofSec_smul _ _))
  change S.str.appTop _ = _
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

namespace HermSys

variable (T : HermSys F)

def weight (hb : T.BasePointFree) (hh : T.Hermitian) (σ : F →+* ℂ) : Weight T.str σ T.L :=
  Weight.fsBasis T.str σ T.isLB T.b hb (T.A σ) (hh σ)

theorem isSmooth_weight (hb : T.BasePointFree) (hh : T.Hermitian) {σ : F →+* ℂ} {D : ℕ} (R : AnRead T.str σ D) :
    (T.weight hb hh σ).IsSmooth R := Weight.isSmooth_fsBasis _ _ _ _ _

theorem weight_φ (hb : T.BasePointFree) (hh : T.Hermitian) (σ : F →+* ℂ) (i : T.L.ι) (y : CxPts T.str σ) :
    (T.weight hb hh σ).φ i y = Real.log (archSize (T.A σ) (fun j => secVal T.str σ (T.b j) i y) ^ 2) := by
  rw [archSize, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact Weight.fsBasis_φ _ _ _ _ _ _ _

abbrev withBundle (L : LB T.Y) (hL : L.IsLB) {N n : ℕ} (b : Fin N → L.Sec) (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) : HermSys F :=
  { Y := T.Y, str := T.str, D := T.D, L := L, isLB := hL, N := N, b := b, n := n, w := w, A := A, abelian₂ := T.abelian₂ }

variable {T} (E : Type) [Field E] [NumberField E] [Algebra F E]

theorem IsAlgebraicData.baseChange (h : T.IsAlgebraicData) : (T.baseChange E).IsAlgebraicData := by
  refine ⟨h.variety.baseChange E, IndepBaseChange.indep_baseChange F E _ h.indep, ?_, h.bpf.baseChange E⟩
  have key : ∀ u ∈ Submodule.span F (Set.range T.w.col), (fun j => algebraMap F E (u j)) ∈
      Submodule.span E (Set.range (T.w.map (algebraMap F E)).col) := fun u hu => by
    induction hu using Submodule.span_induction with
    | mem _ h => obtain ⟨k, rfl⟩ := h; exact Submodule.subset_span ⟨k, rfl⟩
    | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
    | add a b _ _ ha hb => simp only [Pi.add_apply, map_add]; exact add_mem ha hb
    | smul c a _ ha => simp only [Pi.smul_apply, smul_eq_mul, map_mul]; exact Submodule.smul_mem _ _ ha
  refine top_le_iff.1 fun (u : Fin T.N → E) _ => ?_
  rw [pi_eq_sum_univ' u]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
  exact (funext fun j => by simp [Pi.single_apply] : (fun j => algebraMap F E (Pi.single (M := fun _ => F) k 1 j)) =
    Pi.single k 1) ▸ key (Pi.single k 1) (h.spans.ge trivial)

end HermSys

namespace Tuple

variable (T : Tuple F) (E : Type) [Field E] [NumberField E] [Algebra F E]

def baseChange : Tuple E where
  toHermSys := T.toHermSys.baseChange E
  bd := ⟨T.bcFst E ⁻¹' T.bd, T.bd.isClosed.preimage (T.bcFst E).continuous⟩
  j₀ := T.j₀
  th := GlobalTheory.chartSec (chartPullZPow (GlobalTheory.chartPullPull T.L (T.bcFst E)) T.j₀) T.th

theorem U_baseChange : (T.baseChange E).U = T.bcFst E ⁻¹ᵁ T.U := rfl

variable {T} in

theorem IsGeometric.baseChange (h : T.IsGeometric) : (T.baseChange E).IsGeometric := by
  refine ⟨h.alg.baseChange E, fun e => h.bd_ne (top_le_iff.1 fun y _ => ?_)⟩
  have : Surjective (spMap (algebraMap F E)) := ⟨Function.surjective_to_subsingleton _⟩
  have : Surjective (T.bcFst E) := MorphismProperty.of_isPullback (T.isPullback_baseChange E).flip this
  obtain ⟨z, rfl⟩ := (T.bcFst E).surjective y
  exact e.ge (Set.mem_univ z)

variable {T} in

theorem IsGeometric.nonempty_U (h : T.IsGeometric) : (T.U : Set T.Y).Nonempty :=
  Set.nonempty_compl.2 fun e => h.bd_ne (Closeds.ext e)

end Tuple

end GlobalTheory.Adelic

namespace GlobalTheory.HilbertSamuel

open GlobalTheory.Adelic

structure Geo (F : Type) [Field F] [NumberField F] extends Tuple F where

  geom : toTuple.IsGeometric

  herm : toTuple.Hermitian

  conj : toTuple.ConjInvariant

  K : @CanonLB _ _ _ str D geom.alg.variety.smooth

  L₂ : LB Y

  isLB₂ : L₂.IsLB

  N₂ : ℕ

  b₂ : Fin N₂ → L₂.Sec

  n₂ : ℕ

  w₂ : Matrix (Fin N₂) (Fin n₂) F

  A₂ : (F →+* ℂ) → Matrix (Fin N₂) (Fin N₂) ℂ

  alg₂ : (toTuple.withBundle L₂ isLB₂ b₂ w₂ A₂).IsAlgebraicData

  herm₂ : (toTuple.withBundle L₂ isLB₂ b₂ w₂ A₂).Hermitian

  conj₂ : (toTuple.withBundle L₂ isLB₂ b₂ w₂ A₂).ConjInvariant

  LA : LB Y

  isLBA : LA.IsLB

  e : (LB.div LA (tw L₂ L D)).Sec

  U_le : toTuple.U ≤ nonzeroLocus e

namespace Geo

variable {F : Type} [Field F] [NumberField F] (G : Geo F)

instance smooth : SmoothOfRelativeDimension G.D G.str := G.geom.alg.variety.smooth

instance isIntegral : IsIntegral G.Y := G.geom.alg.variety.isIntegral

instance compactSpace (σ : F →+* ℂ) : CompactSpace (CxPts G.str σ) := CxPts.compactSpace σ G.geom.alg.variety.proj

instance secondCountableTopology (σ : F →+* ℂ) : SecondCountableTopology (CxPts G.str σ) :=
  secondCountableTopology_of_isProjOver σ G.geom.alg.variety.proj

theorem one_le_n : 1 ≤ G.n := by
  obtain ⟨j, -⟩ := Opens.mem_iSup.1 (G.geom.alg.bpf.ge (Set.mem_univ (genericPoint G.Y)))
  by_contra h
  have : IsEmpty (Fin G.n) := ⟨fun k => h (Nat.one_le_of_lt k.2)⟩
  have e : (Pi.single j 1 : Fin G.N → F) ∈ Submodule.span F (Set.range G.w.col) := G.geom.alg.spans.ge trivial
  rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at e
  simpa using congrFun e j

abbrev second : HermSys F := G.withBundle G.L₂ G.isLB₂ G.b₂ G.w₂ G.A₂

def φ (σ : F →+* ℂ) : Weight G.str σ G.L := G.weight G.geom.alg.bpf G.herm σ

def φ₂ (σ : F →+* ℂ) : Weight G.str σ G.L₂ := G.second.weight G.alg₂.bpf G.herm₂ σ

def φTw (m : ℤ) (σ : F →+* ℂ) : Weight G.str σ (tw G.L₂ G.L m) := (G.φ₂ σ).tens ((G.φ σ).zpow m)

theorem isSmooth_φTw (m : ℤ) {σ : F →+* ℂ} (R : AnRead G.str σ G.D) : (G.φTw m σ).IsSmooth R :=
  (G.second.isSmooth_weight _ _ R).tens ((G.isSmooth_weight _ _ R).zpow m)

abbrev adj (j : ℕ) : LB G.Y := tw (tens G.K.bundle G.LA) G.L j

abbrev adj₂ (j : ℕ) : LB G.Y := tw (tens G.K.bundle G.L₂) G.L (j + G.D)

theorem isLB_adj (j : ℕ) : (G.adj j).IsLB := isLB_tw (isLB_tens G.K.isLB G.isLBA) G.isLB j

abbrev Sec (j : ℕ) : Type := H0 G.str (G.adj j) G.U

def global (j : ℕ) : Submodule F (G.Sec j) := LinearMap.range (H0.restr le_top)

theorem restr_injective (B : LB G.Y) : Function.Injective (H0.restr le_top : H0 G.str B ⊤ → H0 G.str B G.U) :=
  Vanishing.restr_injective _ G.geom.nonempty_U

instance finiteDimensional_global (j : ℕ) : FiniteDimensional F (G.global j) :=
  have := finite_top G.geom.alg.variety.proj (G.isLB_adj j)
  LinearMap.finiteDimensional_range _

theorem finrank_global (j : ℕ) : Module.finrank F (G.global j) = lbH0 F (G.adj j) :=
  (LinearMap.finrank_range_of_inj (G.restr_injective _)).trans (H0.finrank_top _ _)

def mulW (j : ℕ) : (Fin G.N → F) →ₗ[F] G.Sec j →ₗ[F] G.Sec (j + 1) :=
  (oneChart (isLB_tens G.K.isLB G.isLBA) G.isLB (Nat.cast_succ j).symm).mul ∘ₗ
    Fintype.linearCombination F fun k => H0.ofSec G.str G.U (G.b k)

theorem mulW_apply (j : ℕ) (u : Fin G.N → F) :
    G.mulW j u = mulSec (isLB_tens G.K.isLB G.isLBA) G.isLB (G.comb u) (Nat.cast_succ j).symm :=
  congrArg (oneChart (isLB_tens G.K.isLB G.isLBA) G.isLB (Nat.cast_succ j).symm).mul (G.ofSec_comb G.U u).symm

def mulE (j : ℕ) : H0 G.str (G.adj₂ j) ⊤ →ₗ[F] G.Sec j :=
  H0.restr le_top ∘ₗ Vanishing.mulE G.K G.isLB G.isLBA G.isLB₂ G.e rfl

theorem mulE_mem_global (j : ℕ) (f : H0 G.str (G.adj₂ j) ⊤) : G.mulE j f ∈ G.global j := ⟨_, rfl⟩

theorem mulE_apply (j : ℕ) (f : H0 G.str (G.adj₂ j) ⊤) :
    G.mulE j f = Vanishing.mulE G.K G.isLB G.isLBA G.isLB₂ G.e rfl (H0.restr le_top f) :=
  (ProdChart.restr_mul _ _ _ _).trans (by rw [H0.restr_ofSec]; rfl)

theorem mulE_injective (j : ℕ) : Function.Injective (G.mulE j) := fun f f' h => by
  rw [mulE_apply, mulE_apply] at h
  exact G.restr_injective _ ((ProdChart.bijective_mul _ fun y hy i hi => by
    rw [H0.germ_ofSec, isUnit_ger_iff]; exact G.U_le hy).1 h)

def sqInt (j : ℕ) (σ : F →+* ℂ) (f : (G.adj₂ j).ι → CxPts G.str σ → ℂ) : ℝ≥0∞ :=
  (AnRead.all G.str σ G.D).topInt G.K (G.φTw (j + G.D) σ) (assocVal f)

theorem sqInt_eq (j : ℕ) {σ : F →+* ℂ} (R : AnRead G.str σ G.D) (f : (G.adj₂ j).ι → CxPts G.str σ → ℂ) :
    G.sqInt j σ f = R.topInt G.K (G.φTw (j + G.D) σ) (assocVal f) := AnRead.topInt_eq _ _ _ _ _

theorem sqInt_lt_top (j : ℕ) (σ : F →+* ℂ) {ι : Type*} [Fintype ι] (c : ι → ℂ) (f : ι → H0 G.str (G.adj₂ j) ⊤) :
    G.sqInt j σ (∑ i, c i • cval σ (f i)) < ⊤ :=
  AnRead.topInt_lt_top _ (G.isSmooth_φTw _ _) (assocVal_mem_holSec
    (Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _ (cval_mem_holSec σ _ _)))

variable (s : Fin G.D → Fin G.N → F)

abbrev sec : Fin G.D → G.L.Sec := fun i => G.comb (s i)

abbrev ideal : G.Y.IdealSheafData := cutIdeal G.isLB (G.sec s)

structure IsGood : Prop where

  finite : IsFinite ((G.ideal s).subschemeι ≫ G.str)

  etale : Etale ((G.ideal s).subschemeι ≫ G.str)

  inU : SuppIn G.U (G.ideal s)

abbrev SecOn (j : ℕ) : Type := sectionsOnClosedSubscheme G.str (tw G.L₂ G.L j) (G.ideal s)

variable {G s} (hs : G.IsGood s)

include hs in

theorem IsGood.suppIn_e : SuppIn (nonzeroLocus G.e) (G.ideal s) := fun y hy => G.U_le (hs.inU y hy)

def IsGood.res (j : ℕ) : G.Sec j →ₗ[F] G.SecOn s j :=
  Res G.K G.isLB G.isLBA G.isLB₂ (G.sec s) hs.etale j G.e hs.suppIn_e hs.inU

theorem IsGood.res_mulW (j : ℕ) (u : Fin G.N → F) (m : G.Sec j) :
    hs.res (j + 1) (G.mulW j u m) = mulSecOn G.isLB₂ G.isLB (G.comb u) (Nat.cast_succ j).symm (hs.res j m) := by
  rw [mulW_apply]
  exact Res_mulSec _ _ _ _ _ _ _ _ _ _ _ m

theorem IsGood.res_mulE (j : ℕ) (f : H0 G.str (G.adj₂ j) ⊤) :
    hs.res j (G.mulE j f) = resDs G.K G.isLB G.isLB₂ (G.sec s) hs.etale suppIn_top rfl f :=
  (Res_restr _ _ _ _ _ _ _ _ suppIn_top hs.inU le_top _).trans (Res_mulE _ _ _ _ _ _ _ _ _ rfl f)

def IsGood.sym {a j l : ℕ} (h : j + a = l) (V : Submodule F (G.Sec l)) :
    Fil (G.ideal s) a V →ₗ[F] SymTarget G.str G.L₂ G.isLB (G.sec s) a j :=
  Vanishing.sym G.K G.isLB G.isLBA G.isLB₂ (G.sec s) hs.etale G.e hs.suppIn_e hs.inU
    ((Nat.cast_add j a).symm.trans (congrArg _ h)) V

def weightOn (s : Fin G.D → Fin G.N → F) (j : ℕ) (σ : F →+* ℂ) :
    Weight ((G.ideal s).subschemeι ≫ G.str) σ ((tw G.L₂ G.L j).pull (G.ideal s).subschemeι) :=
  (G.φTw j σ).pull _ rfl

def IsGood.normOn (j : ℕ) : HermFam F (G.SecOn s j) := pointHerm hs.finite hs.etale (weightOn s j)

theorem IsGood.nrm_normOn_sq (j : ℕ) (σ : F →+* ℂ) (g : G.SecOn s j) :
    (hs.normOn j).nrm σ g ^ 2 = ∑ᶠ y, (weightOn s j σ).nsq (cval σ g) y := nrm_pointHerm_sq _ _ _ σ g

variable (G) (E : Type) [Field E] [NumberField E] [Algebra F E]

def baseChange : Geo E where
  toTuple := G.toTuple.baseChange E
  geom := G.geom.baseChange E
  herm _ := G.herm _
  conj τ := G.conj (τ.comp (algebraMap F E))
  K := @CanonLB.baseChange _ _ _ _ _ _ _ _ _ _ _ G.smooth (G.geom.baseChange E).alg.variety.smooth
    (G.isPullback_baseChange E) G.K
  L₂ := G.L₂.pull (G.bcFst E)
  isLB₂ := LB.isLB_pull G.isLB₂ _
  N₂ := G.N₂
  b₂ j := secPull (G.b₂ j) _
  n₂ := G.n₂
  w₂ := G.w₂.map (algebraMap F E)
  A₂ τ := G.A₂ (τ.comp (algebraMap F E))
  alg₂ := G.alg₂.baseChange E
  herm₂ _ := G.herm₂ _
  conj₂ τ := G.conj₂ (τ.comp (algebraMap F E))
  LA := G.LA.pull (G.bcFst E)
  isLBA := LB.isLB_pull G.isLBA _
  e := GlobalTheory.chartSec (chartPullQuot (GlobalTheory.chartPullPull _ _)
    (chartPullTwist (GlobalTheory.chartPullPull _ _) (GlobalTheory.chartPullPull _ _) _)) G.e
  U_le y hy := (nonzeroLocus_chartSec _ G.e fun z _ _ => exists_chart (LB.isLB_div (LB.isLB_pull G.isLBA _)
    (isLB_tw (LB.isLB_pull G.isLB₂ _) (LB.isLB_pull G.isLB _) _)) z).ge (G.U_le hy)

def fst : (G.baseChange E).Y ⟶ G.Y := G.bcFst E

theorem isPullback_fst : IsPullback (G.fst E) (G.baseChange E).str G.str (spMap (algebraMap F E)) :=
  G.isPullback_baseChange E

def chartAdj (j : ℕ) : ChartPull ((G.baseChange E).adj j) (G.adj j) (G.fst E) :=
  chartPullTwist (chartPullTens (GlobalTheory.chartPullPull G.K.bundle _) (GlobalTheory.chartPullPull G.LA _)) (GlobalTheory.chartPullPull G.L _) j

def toExt (j : ℕ) : G.Sec j →ₛₗ[algebraMap F E] (G.baseChange E).Sec j :=
  pullChart (G.chartAdj E j) (G.isPullback_fst E).w le_rfl

theorem linearIndependent_toExt (j n : ℕ) (v : Fin n → G.Sec j) (hv : LinearIndependent F v) :
    LinearIndependent E fun i => G.toExt E j (v i) :=
  linearIndependent_pullChart (G.isPullback_fst E) (G.isLB_adj j) ((G.baseChange E).isLB_adj j) _ _ le_rfl hv

theorem extSpace_global (j : ℕ) : extSpace (G.toExt E j) (G.global j) = (G.baseChange E).global j := by
  have h := (isExtension_pullChart_top (G.isPullback_fst E) (G.isLB_adj j) ((G.baseChange E).isLB_adj j)
    (G.chartAdj E j) G.geom.alg.variety.proj (G.baseChange E).geom.alg.variety.proj).span
  refine Eq.symm ((LinearMap.range_eq_map _).trans ((congrArg _ h.symm).trans ((Submodule.map_span _ _).trans
    (congrArg _ ?_))))
  rw [global, LinearMap.coe_range, ← Set.range_comp, ← Set.range_comp]
  exact congrArg _ (funext fun f => restr_pullChart _ _ _ _ _ _ f)

variable {G E} in

theorem isGood_baseChange_iff {s : Fin G.D → Fin G.N → E} : (G.baseChange E).IsGood s ↔ G.IsGoodSection E s :=
  ⟨fun h => ⟨⟨h.finite, h.etale⟩, h.inU⟩, fun h => ⟨h.finiteEtale.finite, h.finiteEtale.etale, h.inOpen⟩⟩

end Geo

structure Data (F : Type) [Field F] [NumberField F] extends Geo F where

  T : ℕ

  le_T : D + 1 ≤ T

  V : ∀ j : ℕ, Submodule F (toGeo.Sec j)

  global_le : ∀ j ≤ T, toGeo.global j ≤ V j

  V_zero : V 0 = toGeo.global 0

  M : ∀ j, Submodule (𝓞 F) (V j)

  full : ∀ j, IsFull (M j)

  nm : ∀ j, HermFam F (V j)

  conjInv : ∀ j, (nm j).IsConjInv

  beta : ℝ

  LamD : ℝ

  LamT : ℝ

  J : ℝ

  one_le_beta : 1 ≤ beta

  one_le_LamD : 1 ≤ LamD

  one_le_LamT : 1 ≤ LamT

namespace Geo

variable {F : Type} [Field F] [NumberField F] (G : Geo F)

structure Positivity : Prop where

  bir : G.IsBirationalOffBoundary

  nef : IsNef F G.LA

  big : IsBig F G.LA

def logRho (C h : ℝ) : ℝ := Real.log G.abelian₂ + C * Real.log (G.theta h)

def rho (C h : ℝ) : ℝ := Real.exp (G.logRho C h)

def g : ℝ := ((G.D : ℝ) + 1) * (Real.log G.n + 1) / 2 + 1

def Ra (a : ℕ) : ℕ := (a + G.D - 1).choose (G.D - 1)

def globalData (T : ℕ) (hT : G.D + 1 ≤ T) : Data F where
  toGeo := G
  T := T
  le_T := hT
  V := G.global
  global_le _ _ := le_rfl
  V_zero := rfl
  M j := Submodule.span (𝓞 F) (Set.range (Module.finBasis F (G.global j)))
  full _ := isFull_span _
  nm j := ofBasis (Module.finBasis F (G.global j))
  conjInv _ := isConjInv_ofBasis _
  beta := 1
  LamD := 1
  LamT := 1
  J := 1
  one_le_beta := le_rfl
  one_le_LamD := le_rfl
  one_le_LamT := le_rfl

end Geo

namespace Data

variable {F : Type} [Field F] [NumberField F] (X : Data F)

instance finiteDimensional (j : ℕ) : FiniteDimensional F (X.V j) := (X.full j).finiteDimensional

theorem latRank_M (j : ℕ) : latRank F (X.M j) = Module.finrank F (X.V j) := (X.full j).latRank_eq

def HasBoundedPoles : Prop :=
  ∀ j ≤ X.T, ∃ (P : LB X.Y) (hP : P.IsLB) (t : P.Sec) (ht : X.U ≤ nonzeroLocus t),
    X.V j ≤ polar X.str (X.adj j) hP (X.isLB_adj j) t ht

def inclE {j : ℕ} (hj : j ≤ X.T) : H0 X.str (X.adj₂ j) ⊤ →ₗ[F] X.V j :=
  (X.mulE j).codRestrict _ fun f => X.global_le j hj (X.mulE_mem_global j f)

def resLat {s : Fin X.D → Fin X.N → F} (hs : X.IsGood s) : Submodule (𝓞 F) (X.SecOn s 0) :=
  (X.M 0).map ((hs.res 0 ∘ₗ (X.V 0).subtype).restrictScalars (𝓞 F))

def degM (j : ℕ) : ℝ := deg (X.nm j) (X.M j)

section BaseChange

variable (E : Type) [Field E] [NumberField E] [Algebra F E]

theorem isExtension_extMap (j : ℕ) : IsExtension (extMap (X.toExt E j) (X.V j)) :=
  HermTools.isExtension_extMap _ (X.linearIndependent_toExt E j) _

def baseChange : Data E where
  toGeo := X.toGeo.baseChange E
  T := X.T
  le_T := X.le_T
  V j := extSpace (X.toExt E j) (X.V j)
  global_le j hj := (X.extSpace_global E j).ge.trans (Submodule.span_mono (Set.image_mono (X.global_le j hj)))
  V_zero := X.V_zero ▸ X.extSpace_global E 0
  M j := extLat (extMap (X.toExt E j) (X.V j)) (X.M j)
  full j := (X.full j).extLat (X.isExtension_extMap E j)
  nm j := extend (X.isExtension_extMap E j) (X.nm j)
  conjInv j := isConjInv_extend _ (X.conjInv j)
  beta := X.beta
  LamD := X.LamD
  LamT := X.LamT
  J := X.J
  one_le_beta := X.one_le_beta
  one_le_LamD := X.one_le_LamD
  one_le_LamT := X.one_le_LamT

def toExtV (j : ℕ) : X.V j →ₛₗ[algebraMap F E] (X.baseChange E).V j := extMap (X.toExt E j) (X.V j)

theorem nrm_toExtV (j : ℕ) (τ : E →+* ℂ) (x : X.V j) :
    ((X.baseChange E).nm j).nrm τ (X.toExtV E j x) = (X.nm j).nrm (τ.comp (algebraMap F E)) x :=
  nrm_extend (X.isExtension_extMap E j) _ τ x

theorem finrank_V_baseChange (j : ℕ) : Module.finrank E ((X.baseChange E).V j) = Module.finrank F (X.V j) :=
  (X.isExtension_extMap E j).finrank_eq

end BaseChange

def MulStable : Prop :=
  ∀ j < X.T, ∀ w ∈ X.lattice, ∀ f ∈ X.M j, ∃ g ∈ X.M (j + 1), (g : X.Sec (j + 1)) = X.mulW j w f

def MulBound (β : (F →+* ℂ) → ℝ) : Prop :=
  ∀ j < X.T, ∀ σ, ∀ w ∈ X.lattice, ∀ f ∈ X.M j, ∀ g : X.V (j + 1), (g : X.Sec (j + 1)) = X.mulW j w f →
    (X.nm (j + 1)).nrm σ g ≤ Real.sqrt (β σ) * X.normAt σ w * (X.nm j).nrm σ f

def MulBoundAt (σ : F →+* ℂ) (β : ℝ) : Prop :=
  ∀ j < X.T, ∀ (u : Fin X.N → ℂ) (m : ℕ) (c : Fin m → ℂ) (f : Fin m → X.V j) (g : Fin X.N × Fin m → X.V (j + 1)),
    (∀ k i, (g (k, i) : X.Sec (j + 1)) = X.mulW j (Pi.single k 1) (f i)) →
      cnrm (X.nm (j + 1)) σ (fun t => u t.1 * c t.2) g ≤ Real.sqrt β * frameNorm (X.A σ) u * cnrm (X.nm j) σ c f

def IntegralBound (β κ : (F →+* ℂ) → ℝ) : Prop :=
  ∀ j (hj : j ≤ X.T) σ (m : ℕ) (c : Fin m → ℂ) (f : Fin m → H0 X.str (X.adj₂ j) ⊤),
    csq (X.nm j) σ c (fun i => X.inclE hj (f i)) ≤
      κ σ * β σ ^ (X.D + j + 1) * (X.sqInt j σ (∑ i, c i • cval σ (f i))).toReal

def ShortFamily (j : ℕ) (Λ : ℝ) : Prop :=
  ∃ v : Fin (latRank F (X.M j)) → X.V j, (∀ i, v i ∈ X.M j) ∧ LinearIndependent F v ∧
    ∀ i σ, (X.nm j).nrm σ (v i) ≤ Λ

def ShortFamilyMean (j : ℕ) (Λ : ℝ) : Prop :=
  ∃ v : Fin (latRank F (X.M j)) → X.V j, (∀ i, v i ∈ X.M j) ∧ LinearIndependent F v ∧
    ∀ i, meanLog F (fun σ => (X.nm j).nrm σ (v i)) ≤ Real.log Λ

def ResidueDegree (J : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin X.D → Fin X.N → E),
    (∀ i, s i ∈ X.latticeOver E) → ∀ hs : (X.baseChange E).IsGood s,
      IsFull ((X.baseChange E).resLat hs) ∧
        -(X.del * J) - (X.D + 3) * X.cycleHeight E (X.linSection E s) ≤
          deg (hs.normOn 0) ((X.baseChange E).resLat hs)

structure Hyp : Prop where

  totallyComplex : IsTotallyComplex F

  pos : X.Positivity

  mulStable : X.MulStable

  mulBound : X.MulBound fun _ => X.beta

  integralBound : X.IntegralBound (fun _ => X.beta) fun _ => 1

  shortW : X.ShortGenerators

  shortD : X.ShortFamily X.D X.LamD

  shortT : X.ShortFamily X.T X.LamT

  residueDegree : X.ResidueDegree X.J

structure MeanHyp (β κ : (F →+* ℂ) → ℝ) : Prop where

  totallyComplex : IsTotallyComplex F

  beta_pos : ∀ σ, 0 < β σ

  kappa_pos : ∀ σ, 0 < κ σ

  log_beta : Real.log X.beta = max 0 (meanLog F β)

  pos : X.Positivity

  mulStable : X.MulStable

  mulBound : X.MulBound β

  integralBound : X.IntegralBound β κ

  shortW : X.ShortGenerators

  shortD : X.ShortFamilyMean X.D X.LamD

  shortT : X.ShortFamilyMean X.T X.LamT

  residueDegree : X.ResidueDegree X.J

def d : ℕ := latRank F (X.M X.T)

def a₀ : ℕ := X.T - X.D - 1

def R : ℕ := (X.T - 1).choose X.D

def z : ℝ := 1 - X.R * X.del / X.d

theorem d_eq_finrank : X.d = Module.finrank F (X.V X.T) := (X.full _).latRank_eq

theorem a₀_add : X.a₀ + X.D + 1 = X.T := by have := X.le_T; rw [a₀]; omega

theorem sum_Ra : ∑ a ∈ Finset.range (X.a₀ + 1), X.Ra a = X.R := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' X.geom.alg.variety.one_le
  simp only [R, ← X.a₀_add, Geo.Ra, hk, ← add_assoc, Nat.add_sub_cancel]
  exact Nat.sum_range_add_choose _ _

theorem R_pos : 0 < X.R := Nat.choose_pos (by have := X.le_T; omega)

theorem d_baseChange (E : Type) [Field E] [NumberField E] [Algebra F E] : (X.baseChange E).d = X.d := by
  rw [d_eq_finrank, d_eq_finrank]
  exact X.finrank_V_baseChange E _

theorem z_baseChange (E : Type) [Field E] [NumberField E] [Algebra F E] : (X.baseChange E).z = X.z := by
  rw [z, z, d_baseChange, ← FieldChangeInter.del_baseChange F E _ X.geom.alg.variety.proj]
  rfl

variable {X}

theorem MulStable.mem (h : X.MulStable) {j : ℕ} (hj : j < X.T) (u : Fin X.N → F) (f : X.V j) :
    X.mulW j u f ∈ X.V (j + 1) := by
  have : ((X.mulW j).compl₂ (X.V j).subtype).compr₂ (X.V (j + 1)).mkQ = 0 :=
    LinearMap.ext_on X.geom.alg.spans fun w hw => LinearMap.ext_on (X.full j).span fun f hf => by
      obtain ⟨g, -, e⟩ := h j hj w (Submodule.subset_span hw) f hf
      exact (Submodule.Quotient.mk_eq_zero _).2 (e ▸ g.2 :)
  exact (Submodule.Quotient.mk_eq_zero _).1 (LinearMap.congr_fun₂ this u f)

theorem MulStable.mulBound (h : X.MulStable) {β : (F →+* ℂ) → ℝ} (hb : ∀ σ, X.MulBoundAt σ (β σ)) :
    X.MulBound β := fun j hj σ w _ f _ g e => by
  have := hb σ j hj (fun k => σ (w k)) 1 (fun _ => σ 1) (fun _ => f)
    (fun t => ⟨_, h.mem hj (Pi.single t.1 1) f⟩) fun _ _ => rfl
  simp only [← map_mul, cnrm_map, mul_one, one_smul, Fin.sum_univ_one] at this
  refine le_of_eq_of_le (congrArg _ ?_) this
  refine Subtype.ext (e.trans ?_)
  conv_lhs => rw [pi_eq_sum_univ' w]
  simp [Fintype.sum_prod_type, LinearMap.sum_apply]

theorem meanLog_const (c : ℝ) : meanLog F (fun _ => c) = Real.log c := by
  rw [meanLog, Finset.sum_const, Finset.card_univ, Embeddings.card, nsmul_eq_mul,
    mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 Module.finrank_pos.ne')]

theorem ShortFamily.mean {j : ℕ} {Λ : ℝ} (h : X.ShortFamily j Λ) : X.ShortFamilyMean j Λ := by
  obtain ⟨v, h₁, h₂, h₃⟩ := h
  refine ⟨v, h₁, h₂, fun i => meanLog_const (F := F) Λ ▸ div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun σ _ => Real.log_le_log (nrm_pos _ σ (h₂.ne_zero i)) (h₃ i σ)) (Nat.cast_nonneg _)⟩

theorem Hyp.meanHyp (h : X.Hyp) : X.MeanHyp (fun _ => X.beta) fun _ => 1 :=
  ⟨h.1, fun _ => one_pos.trans_le X.one_le_beta, fun _ => one_pos,
    by rw [meanLog_const, max_eq_right (Real.log_nonneg X.one_le_beta)], h.2, h.3, h.4, h.5, h.6, h.7.mean,
    h.8.mean, h.9⟩

theorem MeanHyp.isAdelic {β κ : (F →+* ℂ) → ℝ} (h : X.MeanHyp β κ) : X.IsAdelic :=
  ⟨X.geom, h.pos.bir, X.herm, X.conj, h.shortW⟩

theorem MeanHyp.two_le_theta {β κ : (F →+* ℂ) → ℝ} (h : X.MeanHyp β κ) (hd : 0 < X.del) (t : ℝ) :
    2 ≤ X.theta t := by
  have h₁ : (1 : ℝ) ≤ X.n := Nat.one_le_cast.2 X.one_le_n
  have h₂ : (1 : ℝ) ≤ X.D := Nat.one_le_cast.2 X.geom.alg.variety.one_le
  have h₃ : (1 : ℝ) ≤ X.j₀ := Nat.one_le_cast.2 h.pos.bir.one_le
  have h₄ : (1 : ℝ) ≤ X.del := by exact_mod_cast hd
  have h₅ := Real.log_nonneg h.shortW.one_le
  exact (by linarith [abs_nonneg t] : 2 ≤ 2 + |t| + Real.log X.abelian₂).trans (le_mul_of_one_le_left (by positivity)
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h₁ h₂) h₃) h₄))

end Data

theorem Geo.hasBoundedPoles_globalData {F : Type} [Field F] [NumberField F] (G : Geo F) {T : ℕ} (hT : G.D + 1 ≤ T) :
    (G.globalData T hT).HasBoundedPoles := fun _ _ =>
  ⟨_, LB.isLB_div G.isLBA (isLB_tw G.isLB₂ G.isLB _), G.e, G.U_le, range_restr_le_polar _ _ _ _⟩

theorem Geo.shortFamily_globalData {F : Type} [Field F] [NumberField F] (G : Geo F) {T : ℕ} (hT : G.D + 1 ≤ T)
    (j : ℕ) : (G.globalData T hT).ShortFamily j 1 := by
  have e := (G.globalData T hT).latRank_M j
  exact ⟨Module.finBasis F (G.global j) ∘ Fin.cast e,
    fun i => Submodule.subset_span (M := G.global j) ⟨_, rfl⟩,
    (Module.finBasis F (G.global j)).linearIndependent.comp _ (Fin.cast_injective e),
    fun i σ => (nrm_ofBasis _ σ _).le⟩

namespace Proj

open ProjSpace

variable (F : Type) [Field F] [NumberField F] (M : ℕ)

abbrev tuple : Tuple F where
  toLinSys := projSys F M
  n := M + 1
  w := 1
  A _ := 1
  abelian₂ := 1
  bd := (chart F M (Fin.last M)).compl
  j₀ := 1
  th := secToPow (coord F M (Fin.last M)) 1

theorem U_eq : (tuple F M).U = nonzeroLocus (coord F M (Fin.last M)) :=
  (Opens.compl_compl _).trans (nonzeroLocus_coord F M _).symm

theorem isAlgebraicData (hM : 1 ≤ M) : (tuple F M).IsAlgebraicData :=
  ⟨projSys.isVariety F M hM, projSys.indep F M, top_le_iff.1 fun u _ => by
    rw [pi_eq_sum_univ' u]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, funext fun j => ?_⟩)
    simp [Matrix.one_apply, Pi.single_apply], projSys.basePointFree F M⟩

abbrev bundleA : LB (PSpace F M) := tens (O1 F M) (tw (O1 F M) (O1 F M) M)

theorem isLB_bundleA : (bundleA F M).IsLB := isLB_tens (O1_isLB F M) (isLB_tw (O1_isLB F M) (O1_isLB F M) M)

theorem exists_e : ∃ e : (LB.div (bundleA F M) (tw (O1 F M) (O1 F M) M)).Sec,
    nonzeroLocus e = nonzeroLocus (coord F M (Fin.last M)) :=
  have h := isLB_tw (O1_isLB F M) (O1_isLB F M) M
  exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_div (isLB_bundleA F M) h) (O1_isLB F M)
    ((cls_eq_iff (LB.isLB_div (isLB_bundleA F M) h) _).1 (by rw [cls_div (isLB_bundleA F M) h, cls_tens (O1_isLB F M) h, add_sub_cancel_right])) _

variable {M} (hM : 1 ≤ M)

def geo : Geo F where
  toTuple := tuple F M
  geom := ⟨isAlgebraicData F M hM, fun h => (h.ge (Set.mem_univ (projSys.gen F M))) (projSys.gen_mem F M _)⟩
  herm σ := by simp
  conj σ x := by simp [frameNorm]
  K := CanonLB.all _ _
  L₂ := O1 F M
  isLB₂ := O1_isLB F M
  N₂ := M + 1
  b₂ := coord F M
  n₂ := M + 1
  w₂ := 1
  A₂ _ := 1
  alg₂ := isAlgebraicData F M hM
  herm₂ σ := by simp
  conj₂ σ x := by simp [frameNorm]
  LA := bundleA F M
  isLBA := isLB_bundleA F M
  e := (exists_e F M).choose
  U_le := ((U_eq F M).trans (exists_e F M).choose_spec.symm).le

theorem hasNonzeroSec_pow (M n : ℕ) : HasNonzeroSec (lbPow (O1 F M) n) :=
  lineBundleHasNonzeroSection_of_globalSectionsDim_pos (k := F) (by rw [sectionDim_twistingSheaf_pow]; exact Nat.choose_pos (by omega))

theorem positivity : (geo F hM).Positivity := by
  have hl : nonzeroLocus (tuple F M).th = chart F M (Fin.last M) :=
    (nonzeroLocus_secToPow _ le_rfl).trans (nonzeroLocus_coord F M (Fin.last M))
  have := (geo F hM).isIntegral
  have hc : cls _ (isLB_bundleA F M) = cls _ (isLB_lbPow (O1_isLB F M) (M + 2)) := by
    rw [cls_tens (O1_isLB F M) (isLB_tw (O1_isLB F M) (O1_isLB F M) M),
      cls_tens (O1_isLB F M) (Twist.isLB_lbZPow (O1_isLB F M) M), cls_lbZPow (O1_isLB F M), cls_lbPow (O1_isLB F M)]
    module
  have key : IsNef F (bundleA F M) ∧ IsBig F (bundleA F M) :=
    ⟨((isNef_twistingSheaf F M).pow (isAmple_projective_O_one F M) _).of_cls_eq _ hc,
      (@IsBig.pow _ _ _ _ _ this _ (algebraMap_top_eq F M) (isProjOver_str F M) (isBig_twistingSheaf F M) _
        (by omega)).of_cls_eq _ hc⟩
  rw [← projSys.algebraΓ_eq] at key
  refine ⟨⟨projSys.birational F M, projSys.noContract F M _, le_rfl, fun h => ?_, fun y hy => hl ▸ hy⟩, key.1, key.2⟩
  have := hl.ge (projSys.gen_mem F M _)
  rw [show (tuple F M).th = 0 from h] at this
  exact nonzeroLocus_secZero.le this

omit hM in

theorem cls_adj {Y : Scheme.{0}} {K L : LB Y} (hK : K.IsLB) (hL : L.IsLB) (M j : ℕ) (h₁ h₂ h₃) :
    cls (tw (tens K (tens L (tw L L M))) L j) h₁ = cls (tens K (lbPow L (M + 1))) h₂ + cls (lbPow L (j + 1)) h₃ := by
  have h := isLB_tens hL (isLB_tw hL hL M)
  rw [cls_tens (isLB_tens hK h) (Twist.isLB_lbZPow hL j), cls_tens hK h, cls_tens hL (isLB_tw hL hL M),
    cls_tens hL (Twist.isLB_lbZPow hL M), cls_tens hK (isLB_lbPow hL _), cls_lbZPow hL, cls_lbZPow hL, cls_lbPow hL,
    cls_lbPow hL]
  module

theorem finrank_global_pos (j : ℕ) : 0 < Module.finrank F ((geo F hM).global j) := by
  have hO := O1_isLB F M
  let G := geo F hM
  obtain ⟨c, hc⟩ := exists_chart (G.K.isLB_adj hO (M + 1)) (projSys.gen F M)
  have h₁ : HasNonzeroSec (G.K.adj (O1 F M) (M + 1)) := ⟨G.K.jacSec (coord F M), sec_ne_zero_of_mem
    ((isUnit_ger_iff _ hc).1 ((@isUnit_jacSec_coord F _ M G.smooth G.K c).map _))⟩
  obtain ⟨s, hs⟩ := HasNonzeroSec.of_cls_eq_add (X := G.Y) h₁ (hasNonzeroSec_pow F M (j + 1)) (G.isLB_adj j)
    (G.K.isLB_adj hO _) (isLB_lbPow hO _) (cls_adj G.K.isLB hO M j _ _ _)
  refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨_, H0.ofSec _ ⊤ s, rfl⟩, fun h => hs ?_⟩
  exact H0.bijective_ofSec_top.1 ((G.restr_injective _ ((congrArg Subtype.val h).trans (map_zero _).symm)).trans
    (map_zero _).symm)

def data (T : ℕ) (hT : M + 1 ≤ T) : Data F := (geo F hM).globalData T hT

theorem d_pos (T : ℕ) (hT : M + 1 ≤ T) : 0 < (data F hM T hT).d :=
  (finrank_global_pos F hM T).trans_eq (data F hM T hT).d_eq_finrank.symm

end Proj

example : ∃ X : Data (CyclotomicField 4 ℚ), X.U ≠ ⊤ ∧ 0 < X.d ∧ X.Positivity ∧ X.HasBoundedPoles ∧
    X.ShortFamily X.D X.LamD ∧ X.ShortFamily X.T X.LamT :=
  ⟨Proj.data _ le_rfl 3 (by norm_num), fun h => AmpleModel.coord_ne_top _ ((Proj.U_eq _ 1).symm.trans h),
    Proj.d_pos _ le_rfl _ _, Proj.positivity _ le_rfl, Geo.hasBoundedPoles_globalData _ _, Geo.shortFamily_globalData _ _ _,
    Geo.shortFamily_globalData _ _ _⟩

example : (Proj.data ℚ one_le_two 5 (by norm_num)).a₀ = 2 ∧ (Proj.data ℚ one_le_two 5 (by norm_num)).R = 6 ∧
    (Proj.data ℚ one_le_two 5 (by norm_num)).Ra 2 = 3 := ⟨rfl, rfl, rfl⟩

example : (Proj.geo ℚ le_rfl).g = Real.log 2 + 2 := by
  change (((1 : ℕ) : ℝ) + 1) * (Real.log ((1 + 1 : ℕ) : ℝ) + 1) / 2 + 1 = _
  norm_num
  ring

end GlobalTheory.HilbertSamuel
