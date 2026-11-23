import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.CycleHeightFormulas.TopSelfTower
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RationalityOfResolutionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPermOfCntEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleCodimensionOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCurveIntersectionFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightEqOfFullIntersectionSystem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedPolarizationIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTensorPower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleReadExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleReadCombination
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCyclePointDictionary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleRationalExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleOfRationalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanIntegralEqStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanIntegrableOnStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsFurther
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedPointLengthFormula

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog HermLine IsSmoothHerm IsHorizontal divSupp multAt geoNum charOf ptsIntegral
  IsIntersectionFamily IntersectionSystem IsFullIntersectionSystem)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat RatRStatement)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet (powLine powLine_a constLine isSmoothHerm_powLine isSmoothHerm_constLine)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ

namespace GlobalTheory.ArithmeticHeightTower.FormZc

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

def dimOf (x : MP ℤ m n) : ℕ := by
  classical
  exact if h : ∃ d : ℕ, topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = d then h.choose else 0

theorem dimOf_eq {x : MP ℤ m n} {d : ℕ} (h : topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = d) :
    dimOf x = d := by
  have hx : ∃ d : ℕ, topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = d := ⟨d, h⟩
  have e := hx.choose_spec.symm.trans h
  have e' : hx.choose = d := by exact_mod_cast e
  rw [dimOf, dif_pos hx, e']

def htFn (II : IntersectionSystem) (A : HermLine (Bk n)) (x : MP ℤ m n) : ℝ :=
  cycVal II A (dimOf x) (ptIdeal x)

theorem htFn_eq (II : IntersectionSystem) (A : HermLine (Bk n)) {x : MP ℤ m n} {d : ℕ}
    (h : topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = d) :
    htFn II A x = cycVal II A d (ptIdeal x) := by
  rw [htFn, dimOf_eq h]

theorem last_powLine (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) {W : Ideal (Pol n)} {e : ℕ}
    (hW : Geo.IsArithVar W (e + 1)) {A : HermLine (Bk n)} (hA : IsSmoothHerm A) (r : ℕ) :
    II (Fin (m + 1)) (Bk n) W (e + 1) (Fin.snoc (fun _ : Fin e => A) (powLine A r)) =
      r * II (Fin (m + 1)) (Bk n) W (e + 1) (fun _ => A) := by
  have hadd : ∀ B C : HermLine (Bk n), IsSmoothHerm B → IsSmoothHerm C →
      II (Fin (m + 1)) (Bk n) W (e + 1) (Fin.snoc (fun _ : Fin e => A) (B.tensor C)) =
      II (Fin (m + 1)) (Bk n) W (e + 1) (Fin.snoc (fun _ : Fin e => A) B) +
        II (Fin (m + 1)) (Bk n) W (e + 1) (Fin.snoc (fun _ : Fin e => A) C) := by
    intro B C hB hC
    have h := hII.2.1 _ _ W (e + 1) (fun _ => A) (Fin.last e) B C hW (fun _ => hA) hB hC
    have e₁ : ∀ E : HermLine (Bk n), Function.update (fun _ : Fin (e + 1) => A) (Fin.last e) E =
        Fin.snoc (fun _ : Fin e => A) E := by
      intro E
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp
      · simp [Function.update_of_ne (Fin.castSucc_lt_last j).ne]
    simpa only [e₁] using h
  have hs : (Fin.snoc (fun _ : Fin e => A) A : Fin (e + 1) → HermLine (Bk n)) = fun _ => A := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  have s₁ : IsSmoothHerm (constLine (ι := Bk n) 1 one_pos) := isSmoothHerm_constLine 1 one_pos
  have h0 : II (Fin (m + 1)) (Bk n) W (e + 1) (Fin.snoc (fun _ : Fin e => A) (constLine 1 one_pos)) = 0 := by
    have h := hadd _ _ s₁ s₁
    have e₁ : (constLine (ι := Bk n) 1 one_pos).tensor (constLine 1 one_pos) = constLine 1 one_pos :=
      PolarProof.hermLine_ext (by simp [HermLine.tensor, constLine]) (by
        funext z
        simp [HermLine.tensor, constLine])
    rw [e₁] at h
    linarith
  induction r with
  | zero => simpa [powLine] using h0
  | succ r ih =>
    rw [powLine, hadd _ _ (isSmoothHerm_powLine hA r) hA, ih, hs]
    push_cast
    ring

theorem vertical_eq (h₃ : PtDict) (hV : VertEq) (II : IntersectionSystem) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (hN : IsHermRep N A) (Z : Scheme.{0}) [IsIntegral Z] (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] (κ : Type) [Field κ]
    [Finite κ] [Algebra κ Γ(Z, ⊤)] (d : ℕ) (hd : topologicalKrullDim Z = d) :
    cycVal II A d (ptIdeal (i (genericPoint Z))) = topSelfIntersection κ (N.B.pull i) d * Real.log (Nat.card κ) := by
  obtain ⟨-, hp₃, -, hp₅⟩ := h₃ m n Z i d hd
  have hnh : ¬ IsHorizontal (ptIdeal (i (genericPoint Z))) := by
    intro hh
    haveI hc : CharZero Γ(Z, ⊤) := hp₃.1 hh
    obtain ⟨p, hp⟩ := CharP.exists κ
    haveI := hp
    have hp0 : p ≠ 0 := CharP.char_ne_zero_of_finite κ p
    have h0 : (p : Γ(Z, ⊤)) = 0 := by
      rw [← map_natCast (algebraMap κ Γ(Z, ⊤)) p, CharP.cast_eq_zero, map_zero]
    exact hp0 (Nat.cast_eq_zero.1 h0)
  obtain ⟨hpr, hz⟩ := hp₅ hnh
  rw [cycVal, if_neg hnh]
  generalize charOf (ptIdeal (i (genericPoint Z))) = l at hpr hz ⊢
  haveI : Fact l.Prime := ⟨hpr⟩
  haveI : CharP Γ(Z, ⊤) l := charP_of_cast hpr hz
  haveI : CharP κ l := (RingHom.charP_iff (algebraMap κ Γ(Z, ⊤)) (algebraMap κ Γ(Z, ⊤)).injective l).2 inferInstance
  letI : Algebra (ZMod l) κ := ZMod.algebra κ l
  letI : Algebra (ZMod l) Γ(Z, ⊤) := ZMod.algebra _ l
  have e₀ := GlobalTheory.ArithmeticHeightTower.TowerCopy.topSelf_eq_finrank_mul (X := Z) (ZMod l) κ
    (fun a => RingHom.congr_fun (Subsingleton.elim (algebraMap (ZMod l) Γ(Z, ⊤))
      ((algebraMap κ Γ(Z, ⊤)).comp (algebraMap (ZMod l) κ))) a) (N.B.pull i) d
  have e₁ := hV m n N A hN (MP ℤ m n) (𝟙 _) Z i l d hd
  have e₂ : topSelfIntersection (ZMod l) (N.B.pull (i ≫ 𝟙 _)) d = topSelfIntersection (ZMod l) ((N.B.pull (𝟙 _)).pull i) d :=
    topSelf_congr (ZMod l) (N.restr (i ≫ 𝟙 _)).isLB ((N.pull (𝟙 _) (Category.id_comp _)).restr i).isLB
      (N.refines_pull_comp (𝟙 _) (Category.id_comp _) i rfl (by rw [Category.assoc, Category.id_comp])).lbIso d
  rw [Category.comp_id] at e₂
  have e₃ : (𝟙 (MP ℤ m n) : _ ⟶ _) (i (genericPoint Z)) = i (genericPoint Z) := by simp
  rw [e₃] at e₁
  haveI : Fintype κ := Fintype.ofFinite κ
  have e₄ : Nat.card κ = l ^ Module.finrank (ZMod l) κ := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod l) (V := κ), ZMod.card]
  rw [← e₁, ← e₂, e₀, e₄]
  push_cast
  rw [Real.log_pow]
  ring

theorem rec_pow (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (h₈ : ArchIntegrableOn) (hR : RatRStatement)
    (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (hN : IsHermRep N A) (hA : IsSmoothHerm A) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] (e : ℕ) (hZ : GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) e)
    (hP : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) (e + 1)) (mm : ℕ)
    (r : ((N.restr i).pow mm).B.ι → Z.functionFieldˣ) (hr : IsRatSec ((N.restr i).pow mm).B r) :
    (N.restr i).ArchIntegrable ((N.restr i).pow mm) e hr ∧
    mm * cycVal II A (e + 1) (ptIdeal (i (genericPoint Z))) =
      ∑ᶠ z, ((((N.restr i).pow mm).div hr).mult z : ℝ) * cycVal II A e (ptIdeal (i z)) -
        (N.restr i).archInt ((N.restr i).pow mm) e hr := by
  have hRep := GlobalTheory.CompanionTheory.MPDict.PowRep.isHermRep_pow m n N A mm hN
  have sB := isSmoothHerm_powLine hA mm
  have iso : ((N.restr i).pow mm).Isometric ((N.pow mm).restr i) :=
    HermLB.icls_eq_iff.1 (by simp [HermLB.icls_pow, HermLB.icls_pull, map_nsmul])
  obtain ⟨r', hr', e₁, e₂⟩ := iso.exists_isRatSec hr
  have hI := h₈ m n N (N.pow mm) Z i e hZ r' hr'
  obtain ⟨f, g, hfg, hrat⟩ := h₅ m n (N.pow mm) (powLine A mm) hRep Z i r' hr'
  have hcyc := h₆ m n (N.pow mm) (powLine A mm) hRep Z i e hZ r' hr' f g hfg hrat (cycVal II A e)
  have hint := h₇ m n N (N.pow mm) A (powLine A mm) hN hRep Z i e hZ hA sB r' hr' f g hfg hrat
  have hrr := hR _ _ (II _ (Bk n)) (hII.1 _ _) _ e (fun _ => A) (powLine A mm) f g hP (fun _ => hA) sB hfg
  have hpw := last_powLine II hII hP hA mm
  refine ⟨?_, ?_⟩
  · unfold HermLB.ArchIntegrable Weight.ChernIntegrableOn at hI ⊢
    rw [e₁] at hI
    exact fun σ => Weight.ChernIntegrableOn.congr (hI σ) (isOpen_offSupp _).measurableSet (e₂ σ)
  · have e₃ : (N.restr i).archInt ((N.restr i).pow mm) e hr = (N.restr i).archInt ((N.pow mm).restr i) e hr' := by
      simp only [HermLB.archInt, e₁]
      exact finsum_congr fun σ => (Weight.chernInt_congr (isOpen_offSupp _).measurableSet (e₂ σ)).symm
    have e₄ : ((N.restr i).pow mm).div hr = ((N.pow mm).restr i).div hr' := e₁.symm
    rw [cycVal, if_pos hP.2.2.1, ← hpw, hrr, e₃, hint, e₄, hcyc]
    rfl

theorem exists_height (h₃ : PtDict) (h₄ : CodimOne) (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq)
    (h₈ : ArchIntegrableOn) (hV : VertEq) (hPt : PtLen) (hC : CurveInt) (hR : RatRStatement) (II : IntersectionSystem)
    (hII : IsFullIntersectionSystem II) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n)) (hN : IsHermRep N A)
    (hA : IsSmoothHerm A) : N.IsArithHeight (htFn II A) where
  vertical Z i _ _ κ _ _ _ d hd := by
    rw [htFn_eq II A ((dim_of_generic i).trans hd)]
    exact vertical_eq h₃ hV II N A hN Z i κ d hd
  point Z i _ _ _ hc hd r hr := by
    have hd' : topologicalKrullDim Z = ((0 + 1 : ℕ) : _) := by simpa using hd
    have hZ : GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) 0 := (mp_var m n).of_isClosedImmersion i hc hd'
    obtain ⟨-, hp₃, hp₄, -⟩ := h₃ m n Z i 1 hd'
    rw [htFn_eq II A ((dim_of_generic i).trans hd'),
      curve_eq h₃ h₄ h₅ h₆ h₇ hPt hC hR II hII N A hN hA Z i hZ (hp₄ (hp₃.2 hc)) r hr]
    rfl
  recursion Z i _ _ _ hc e he hd mm r hr := by
    have hZ : GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) e := (mp_var m n).of_isClosedImmersion i hc hd
    obtain ⟨-, hp₃, hp₄, -⟩ := h₃ m n Z i (e + 1) hd
    obtain ⟨h₁, h₂⟩ := rec_pow h₅ h₆ h₇ h₈ hR II hII N A hN hA Z i e hZ (hp₄ (hp₃.2 hc)) mm r hr
    refine ⟨h₁, ?_⟩
    rw [htFn_eq II A ((dim_of_generic i).trans hd), h₂]
    refine congrArg (· - _) (finsum_congr fun z => ?_)
    by_cases hz : (((N.restr i).pow mm).div hr).mult z = 0
    · simp [hz]
    · rw [htFn_eq II A ((dim_closure_image i z).trans
        (h₄ Z _ e hZ z (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)))]

section Expand

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {κ : Type} [Fintype κ]

theorem combLine_single [DecidableEq κ] (A : κ → HermLine ι)
    (cA : ∀ j z, (¬ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (A j).h z = 0) (o : κ) : combLine A (Pi.single o 1) = A o := by
  refine PolarProof.hermLine_ext ?_ ?_
  · simp [combLine, Pi.single_apply, ite_smul]
  · funext z
    by_cases hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
    · simp only [combLine]
      rw [if_pos hz, Finset.prod_eq_single o]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · simp
    · simp only [combLine]
      rw [if_neg hz, cA o z hz]

theorem expand_comb (A : κ → HermLine ι) (sA : ∀ o, IsSmoothHerm (A o))
    (cA : ∀ j z, (¬ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (A j).h z = 0) (e : ℕ) (F : (Fin e → HermLine ι) → ℝ)
    (hF : ∀ (L : Fin e → HermLine ι) (j : Fin e) (B C : HermLine ι), (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm B →
      IsSmoothHerm C → F (Function.update L j (B.tensor C)) = F (Function.update L j B) + F (Function.update L j C))
    (a : κ → ℤ) :
    F (fun _ => combLine A a) = ∑ f : Fin e → κ, (∏ j, (a (f j) : ℝ)) * F (A ∘ f) := by
  classical
  have sC : ∀ b, IsSmoothHerm (combLine A b) := isSmoothHerm_combLine sA
  have up : ∀ (x : Fin e → κ → ℤ) (j : Fin e) (b : κ → ℤ),
      (fun i => combLine A (Function.update x j b i)) = Function.update (fun i => combLine A (x i)) j (combLine A b) := by
    intro x j b
    funext i
    by_cases h : i = j
    · subst h
      simp
    · simp [Function.update_of_ne h]
  have aG : ∀ (x : Fin e → κ → ℤ) (j : Fin e) (b c : κ → ℤ),
      F (fun i => combLine A (Function.update x j (b + c) i)) =
        F (fun i => combLine A (Function.update x j b i)) + F (fun i => combLine A (Function.update x j c i)) := by
    intro x j b c
    simp only [up, PolarProof.combLine_add]
    exact hF _ j _ _ (fun _ => sC _) (sC _) (sC _)
  let M : MultilinearMap ℤ (fun _ : Fin e => κ → ℤ) ℝ :=
    { toFun := fun x => F fun i => combLine A (x i)
      map_update_add' := by
        intro inst x j b c
        rw [Subsingleton.elim inst (fun a b => instDecidableEqFin e a b)]
        exact aG x j b c
      map_update_smul' := by
        intro inst x j c b
        obtain rfl : inst = (fun a b => instDecidableEqFin e a b) := Subsingleton.elim _ _
        exact map_zsmul (AddMonoidHom.mk' (fun y => F fun i => combLine A (Function.update x j y i)) (aG x j)) c b }
  have ha : a = ∑ o, a o • (Pi.single o 1 : κ → ℤ) := by
    funext o
    simp [Finset.sum_apply, Pi.single_apply]
  have h₁ : M (fun _ => a) = F (fun _ => combLine A a) := rfl
  rw [← h₁]
  have h₂ : M (fun _ => a) = M (fun _ => ∑ o, a o • (Pi.single o 1 : κ → ℤ)) := by rw [← ha]
  rw [h₂, M.map_sum (fun _ o => a o • (Pi.single o 1 : κ → ℤ))]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [M.map_smul_univ (fun j => a (f j)) (fun j => (Pi.single (f j) 1 : κ → ℤ))]
  have h₃ : M (fun j => (Pi.single (f j) 1 : κ → ℤ)) = F (A ∘ f) := by
    change F (fun i => combLine A (Pi.single (f i) 1)) = F (A ∘ f)
    congr 1
    funext i
    exact combLine_single A cA (f i)
  rw [h₃, zsmul_eq_mul]
  push_cast
  rfl

end Expand

end GlobalTheory.ArithmeticHeightTower.FormZc
