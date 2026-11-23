import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.IsClosedImmersionLift

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog HermLine IsSmoothHerm IsHorizontal divSupp multAt geoNum charOf ptsIntegral
  IsIntersectionFamily IntersectionSystem IsFullIntersectionSystem)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat RatRStatement)
open GlobalTheory.CompanionTheory.MPDict

namespace GlobalTheory.CompanionTheory.MixZ

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem dim_of_generic {X Z : Scheme.{0}} [IsIntegral Z] (j : Z ⟶ X) [IsClosedImmersion j] :
    topologicalKrullDim (closure ({j (genericPoint Z)} : Set X)) = topologicalKrullDim Z := by
  have hrange : Set.range j = closure {j (genericPoint Z)} := by
    have h₁ := (genericPoint_spec Z).image j.continuous
    rw [Set.image_univ, j.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  exact topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding hrange

theorem dim_closure_image {X Y : Scheme.{0}} (j : Y ⟶ X) [IsClosedImmersion j] (z : Y) :
    topologicalKrullDim (closure ({j z} : Set X)) = topologicalKrullDim (closure ({z} : Set Y)) := by
  obtain ⟨Z, k, _, _, rfl⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint z
  exact (dim_of_generic (k ≫ j)).trans (dim_of_generic k).symm

theorem isometric_restr_restr {X Z : Scheme.{0}} (N : HermLB (mpStr ℤ m n)) (i : X ⟶ MP ℤ m n) (j : Z ⟶ X) :
    ((N.restr i).restr j).Isometric (N.pull (j ≫ i) (Category.assoc _ _ _)) := by
  have hm : ∀ (c : ((N.restr i).restr j).B.ι) (x : Z), x ∈ ((N.restr i).restr j).B.U c →
      x ∈ (N.pull (j ≫ i) (Category.assoc _ _ _)).B.U (fun _ => c PUnit.unit PUnit.unit) := fun c x h =>
    (mem_pull (F := j ≫ i) (x := x)).2 ((mem_pull (F := i) (x := j x)).1 ((mem_pull (F := j) (x := x)).1 h))
  refine HermLB.isometric_of_chart (fun c _ => c PUnit.unit PUnit.unit) (fun c x h => hm c x h) (fun x c c' h h' => ?_)
    fun σ c y hy => ?_
  · have h₁ := (mem_pull (F := j) (x := x)).1 h
    have h₁' := (mem_pull (F := j) (x := x)).1 h'
    refine (gm_pull_g (N.B.pull i) j (𝟙 Z) x c c' h h').trans ?_
    refine (gm_pull_g N.B i (𝟙 Z ≫ j) x _ _ h₁ h₁').trans ?_
    refine Eq.trans ?_ (gm_pull_g N.B (j ≫ i) (𝟙 Z) x _ _ (hm c x h) (hm c' x h')).symm
    simp only [Category.assoc]
  · refine ((N.φ σ).pull_φ (j ≫ i) (Category.assoc _ _ _) _ y).trans ?_
    refine Eq.trans ?_ ((((N.φ σ).pull i rfl).pull_φ j rfl c y)).symm
    refine Eq.trans ?_ ((N.φ σ).pull_φ i rfl _ _).symm
    congr 1

theorem archInt_transport {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp ℤ} {L M : HermLB q} (iso : L.Isometric M)
    {r : L.B.ι → Z.functionFieldˣ} (hr : IsRatSec L.B r) :
    ∃ (r' : M.B.ι → Z.functionFieldˣ) (hr' : IsRatSec M.B r'), M.div hr' = L.div hr ∧
      (∀ e, M.archInt M e hr' = L.archInt L e hr) ∧
      ∀ σ, Set.EqOn (GlobalTheory.Cartier.logNorm (M.φ σ) r') (GlobalTheory.Cartier.logNorm (L.φ σ) r) (GlobalTheory.Cartier.offSupp q σ (L.div hr)) := by
  obtain ⟨r', hr', h₁, h₂⟩ := iso.exists_isRatSec hr
  refine ⟨r', hr', h₁, fun e => ?_, h₂⟩
  simp only [HermLB.archInt, h₁, iso.chernInt_eq]
  exact finsum_congr fun σ => Weight.chernInt_congr (isOpen_offSupp _).measurableSet (h₂ σ)

theorem rec_eq (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hR : RatRStatement)
    (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (hN : IsHermRep N A) (hA : IsSmoothHerm A) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] (e : ℕ) (hZ : GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) e)
    (hP : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) (e + 1))
    (r : (N.restr i).B.ι → Z.functionFieldˣ) (hr : IsRatSec (N.restr i).B r) :
    cycVal II A (e + 1) (ptIdeal (i (genericPoint Z))) =
      ∑ᶠ z, (((N.restr i).div hr).mult z : ℝ) * cycVal II A e (ptIdeal (i z)) -
        (N.restr i).archInt (N.restr i) e hr := by
  obtain ⟨f, g, hfg, hrat⟩ := h₅ m n N A hN Z i r hr
  have hcyc := h₆ m n N A hN Z i e hZ r hr f g hfg hrat (cycVal II A e)
  have hint := h₇ m n N N A A hN hN Z i e hZ hA hA r hr f g hfg hrat
  have hrr := hR _ _ (II _ (Bk n)) (hII.1 _ _) _ e (fun _ => A) A f g hP (fun _ => hA) hA hfg
  have hs : (Fin.snoc (fun _ : Fin e => A) A : Fin (e + 1) → HermLine (Bk n)) = fun _ => A := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  rw [hs] at hrr
  rw [hint, hcyc, cycVal, if_pos hP.2.2.1, hrr]
  rfl

theorem mp_var (m : ℕ) (n : Fin (m + 1) → ℕ) : GlobalTheory.IsArithVar (mpStr ℤ m n) (∑ i, n i) :=
  GlobalTheory.Amb.isArithVar_mp ℤ inferInstance m n

theorem not_horizontal_of_dim_zero (h₃ : PtDict) {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (z : X)
    (hz : topologicalKrullDim (closure ({z} : Set X)) = (0 : ℕ)) : ¬ IsHorizontal (ptIdeal (i z)) := by
  obtain ⟨Z, k, _, _, rfl⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint z
  have hd : topologicalKrullDim Z = (0 : ℕ) := (dim_of_generic k).symm.trans hz
  obtain ⟨-, h2, -, -⟩ := h₃ m n Z (k ≫ i) 0 hd
  intro hh
  have hc : CharZero Γ(Z, ⊤) := h2.1 hh
  exact (mp_var m n).dim_ne_zero (k ≫ i) hc (by exact_mod_cast hd)

theorem curve_eq (h₃ : PtDict) (h₄ : CodimOne) (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hPt : PtLen)
    (hC : CurveInt) (hR : RatRStatement)
    (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (hN : IsHermRep N A) (hA : IsSmoothHerm A) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] (hZ : GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) 0)
    (hP : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) 1)
    (r : (N.restr i).B.ι → Z.functionFieldˣ) (hr : IsRatSec (N.restr i).B r) :
    cycVal II A 1 (ptIdeal (i (genericPoint Z))) =
      ∑ᶠ z, (((N.restr i).div hr).mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) -
        ∑ᶠ σ, ∑ᶠ y : CxPts (i ≫ mpStr ℤ m n) σ, logNorm ((N.restr i).φ σ) r y := by
  rw [rec_eq h₅ h₆ h₇ hR II hII N A hN hA Z i 0 hZ hP r hr, (hC Z _ hZ (N.restr i) (N.restr i) r hr).2]
  refine congrArg (· - _) (finsum_congr fun z => ?_)
  by_cases hz : ((N.restr i).div hr).mult z = 0
  · simp [hz]
  have hd := h₄ Z _ 0 hZ z (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)
  rw [cycVal, if_neg (not_horizontal_of_dim_zero h₃ i z hd), hPt m n Z i z hd]

theorem rec_eq' (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hR : RatRStatement)
    (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (hN : IsHermRep N A) (hA : IsSmoothHerm A) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] {q : Z ⟶ Sp ℤ} (hq : i ≫ mpStr ℤ m n = q) (e : ℕ)
    (hZ : GlobalTheory.IsArithVar q e) (hP : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) (e + 1))
    (r : (N.pull i hq).B.ι → Z.functionFieldˣ) (hr : IsRatSec (N.pull i hq).B r) :
    cycVal II A (e + 1) (ptIdeal (i (genericPoint Z))) =
      ∑ᶠ z, (((N.pull i hq).div hr).mult z : ℝ) * cycVal II A e (ptIdeal (i z)) -
        (N.pull i hq).archInt (N.pull i hq) e hr := by
  subst hq
  exact rec_eq h₅ h₆ h₇ hR II hII N A hN hA Z i e hZ hP r hr

theorem curve_eq' (h₃ : PtDict) (h₄ : CodimOne) (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hPt : PtLen)
    (hC : CurveInt) (hR : RatRStatement)
    (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (hN : IsHermRep N A) (hA : IsSmoothHerm A) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] {q : Z ⟶ Sp ℤ} (hq : i ≫ mpStr ℤ m n = q)
    (hZ : GlobalTheory.IsArithVar q 0) (hP : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) 1)
    (r : (N.pull i hq).B.ι → Z.functionFieldˣ) (hr : IsRatSec (N.pull i hq).B r) :
    cycVal II A 1 (ptIdeal (i (genericPoint Z))) =
      ∑ᶠ z, (((N.pull i hq).div hr).mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) -
        ∑ᶠ σ, ∑ᶠ y : CxPts q σ, logNorm ((N.pull i hq).φ σ) r y := by
  subst hq
  exact curve_eq h₃ h₄ h₅ h₆ h₇ hPt hC hR II hII N A hN hA Z i hZ hP r hr

theorem charP_of_cast {R : Type} [CommRing R] [IsDomain R] {p : ℕ} (hp : p.Prime) (h : (p : R) = 0) : CharP R p := by
  obtain ⟨ℓ, hℓ⟩ := CharP.exists R
  rcases (Nat.dvd_prime hp).1 ((CharP.cast_eq_zero_iff R ℓ p).1 h) with rfl | rfl
  · exact absurd ((Nat.cast_one (R := R)).symm.trans ((CharP.cast_eq_zero_iff R 1 1).2 dvd_rfl)) one_ne_zero
  · exact hℓ

theorem heightEq_of (h₃ : PtDict) (h₄ : CodimOne) (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hV : VertEq)
    (hPt : PtLen) (hC : CurveInt) (hR : RatRStatement) (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) :
    HeightEq II := by
  intro m n N A hN hA X _ _ i _ h H z d hd
  induction d using Nat.strong_induction_on generalizing z with
  | _ d ih =>
  obtain ⟨Z, j, _, _, rfl⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint z
  have hZd : topologicalKrullDim Z = d := (dim_of_generic j).symm.trans hd
  have hmp := mp_var m n
  have hnoeth := hmp.isNoetherian_sub (j ≫ i)
  have hln : IsLocallyNoetherian Z := hnoeth.toIsLocallyNoetherian
  have hcomp : ∀ x, (j ≫ i) x = i (j x) := fun x => by simp
  obtain ⟨-, hp₃, hp₄, hp₅⟩ := h₃ m n Z (j ≫ i) d hZd
  simp only [hcomp] at hp₃ hp₄ hp₅
  by_cases hW : IsHorizontal (ptIdeal (i (j (genericPoint Z))))
  · have hc : CharZero Γ(Z, ⊤) := hp₃.1 hW
    have hP := hp₄ hW
    obtain ⟨r₀, hr₀⟩ := exists_isRatSec ((N.restr i).restr j).isLB
    obtain ⟨r, hr, e₁, e₂, e₃⟩ := archInt_transport (isometric_restr_restr N i j) hr₀
    cases d with
    | zero => exact absurd (by exact_mod_cast hZd) (hmp.dim_ne_zero (j ≫ i) hc)
    | succ e =>
      have hZ₀ : GlobalTheory.IsArithVar ((j ≫ i) ≫ mpStr ℤ m n) e := hmp.of_isClosedImmersion (j ≫ i) hc hZd
      have hZ : GlobalTheory.IsArithVar (j ≫ i ≫ mpStr ℤ m n) e := by
        rw [← Category.assoc]
        exact hZ₀
      rcases Nat.eq_zero_or_pos e with rfl | he
      · have hcv := curve_eq' h₃ h₄ h₅ h₆ h₇ hPt hC hR II hII N A hN hA Z (j ≫ i) (Category.assoc _ _ _) hZ
          (by simpa only [hcomp] using hP) r hr
        simp only [hcomp] at hcv
        rw [H.point Z j hc hZd r₀ hr₀, hcv, HermLB.curveDeg, e₁]
        refine congrArg _ (finsum_congr fun σ => finsum_congr fun y => (e₃ σ (mem_offSupp.2 ?_)).symm)
        rw [hZ.under_eq_genericPoint]
        exact CartierDiv.genericPoint_notMem_supp _
      · have hrc := rec_eq' h₅ h₆ h₇ hR II hII N A hN hA Z (j ≫ i) (Category.assoc _ _ _) e hZ
          (by simpa only [hcomp] using hP) r hr
        simp only [hcomp] at hrc
        rw [(H.recursion_one j hc he hZd hr₀).2, hrc, e₂, e₁]
        refine congrArg (· - _) (finsum_congr fun z' => ?_)
        by_cases hz : (((N.restr i).restr j).div hr₀).mult z' = 0
        · simp [hz]
        have hdz := h₄ Z _ e hZ z' (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)
        rw [ih e (Nat.lt_succ_self e) (j z') ((dim_closure_image j z').trans hdz)]
  · obtain ⟨hpr, hz⟩ := hp₅ hW
    have key : ∀ p : ℕ, p.Prime → ((p : ℕ) : Γ(Z, ⊤)) = 0 → h (j (genericPoint Z)) =
        (geoNum d (ptIdeal (i (j (genericPoint Z)))) (fun _ => A.a) : ℝ) * Real.log p := by
      intro p hp h0
      haveI : Fact p.Prime := ⟨hp⟩
      haveI : CharP Γ(Z, ⊤) p := charP_of_cast hp h0
      letI : Algebra (ZMod p) Γ(Z, ⊤) := ZMod.algebra _ p
      have e₁ := H.vertical Z j (ZMod p) d hZd
      have e₂ : topSelfIntersection (ZMod p) ((N.restr i).B.pull j) d = _ := hV m n N A hN X i Z j p d hZd
      rw [e₁, e₂, Nat.card_zmod]
    rw [key _ hpr hz, cycVal, if_neg hW]

theorem heightEq_holds : PtDict → CodimOne → ExistsRat → CycleOfRat → ArchIntEq → VertEq → PtLen → CurveInt →
    RatRStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → HeightEq II :=
  fun h₃ h₄ h₅ h₆ h₇ hV hPt hC hR II hII => heightEq_of h₃ h₄ h₅ h₆ h₇ hV hPt hC hR II hII

end GlobalTheory.CompanionTheory.MixZ
