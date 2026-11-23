import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictChernPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MIntEqOfLeviEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartDirectionalDerivativeRegularCoordinate

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory GlobalTheory.ArInt GlobalTheory.Mean4O GlobalTheory.CxPts

namespace GlobalTheory.Mean4O.ReadsProj

section Local

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} (σ : k →+* ℂ)

def HalfWeight (L : HermLB p) (g : CxPts p σ → CxPts p σ → ℝ) : Prop :=
  ∀ x, ∃ i, x ∈ ptsIn p σ (L.B.U i) ∧ ∀ z, (L.φ σ).φ i z / 2 = g x z

variable {σ} {L L' : HermLB p} {g g' : CxPts p σ → CxPts p σ → ℝ}

theorem HalfWeight.congr (h : HalfWeight σ L g) (e : ∀ x z, g x z = g' x z) : HalfWeight σ L g' := by
  rwa [← show g = g' from funext₂ e]

theorem halfWeight_locPot (L : HermLB p) : HalfWeight σ L (L.φ σ).locPot.φ :=
  fun x => ⟨_, (L.φ σ).locPot.mem_U x, fun _ => rfl⟩

theorem halfWeight_triv : HalfWeight σ (HermLB.triv p) fun _ _ => 0 :=
  fun _ => ⟨PUnit.unit, mem_ptsIn_top, fun _ => zero_div _⟩

theorem halfWeight_fnB (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) (hu hc) :
    HalfWeight σ (fnB u hu hc) fun _ z => u σ z / 2 :=
  fun _ => ⟨PUnit.unit, mem_ptsIn_top, fun _ => rfl⟩

theorem HalfWeight.tens (h : HalfWeight σ L g) (h' : HalfWeight σ L' g') :
    HalfWeight σ (L.tens L') fun x z => g x z + g' x z := fun x => by
  obtain ⟨i, hi, e⟩ := h x
  obtain ⟨j, hj, e'⟩ := h' x
  exact ⟨(i, j), mem_ptsIn_inf.2 ⟨hi, hj⟩, fun z => (add_div _ _ _).trans (congrArg₂ (· + ·) (e z) (e' z))⟩

theorem HalfWeight.dual (h : HalfWeight σ L g) : HalfWeight σ L.dual fun x z => -g x z := fun x => by
  obtain ⟨i, hi, e⟩ := h x
  exact ⟨i, hi, fun z => (neg_div _ _).trans (congrArg (-·) (e z))⟩

theorem HalfWeight.pow (h : HalfWeight σ L g) (m : ℕ) : HalfWeight σ (L.pow m) fun x z => m * g x z := fun x => by
  obtain ⟨i, hi, e⟩ := h x
  refine ⟨fun _ => i, CxPts.mem_pow_iff.2 hi, fun z => ?_⟩
  refine (congrArg (· / 2) ((L.φ σ).zpow_φ m _ z)).trans ?_
  simp only [← e z, mul_div_assoc, Int.cast_natCast]

theorem HalfWeight.zp (h : HalfWeight σ L g) (n : ℤ) : HalfWeight σ (zp L n) fun x z => n * g x z :=
  ((h.pow n.toNat).tens (h.pow (-n).toNat).dual).congr fun x z => by
    have e : ((n.toNat : ℤ) : ℝ) - ((-n).toNat : ℤ) = n := by exact_mod_cast Int.toNat_sub_toNat_neg n
    rw [← e]
    simp only [Int.cast_natCast]
    ring

theorem halfWeight_comb {ι : Type} [Fintype ι] {L : ι → HermLB p} {g : ι → CxPts p σ → CxPts p σ → ℝ}
    (h : ∀ i, HalfWeight σ (L i) (g i)) (n : ι → ℤ) :
    HalfWeight σ (ArInt.comb L n) fun x z => ∑ i, n i * g i x z := by
  have key (l : List ι) : HalfWeight σ (l.foldr (fun i M => (zp (L i) (n i)).tens M) (HermLB.triv p))
      fun x z => (l.map fun i => n i * g i x z).sum := by
    induction l with
    | nil => exact halfWeight_triv
    | cons i l ih => exact ((h i).zp (n i)).tens ih
  exact (key _).congr fun x z => Finset.sum_map_toList _ _

end Local

open ProjSpace

variable (N : ℕ)

abbrev σ₀ : ℤ →+* ℂ := Int.castRingHom ℂ

abbrev rd : AnRead (PSpace.str ℤ N) σ₀ N := AnRead.all _ _ N

theorem isAlg : IsAlgAtlas (ProjAn.finAtlas ℤ σ₀ N) := (rd N).isAlgAtlas_finAtlas

abbrev om : LocPot (CxPts (PSpace.str ℤ N) σ₀) :=
  ((ProjAn.fsO1 ℤ σ₀ N).pull (𝟙 _) (Category.id_comp _)).locPot

theorem om_pot : IsPotential (ProjAn.finAtlas ℤ σ₀ N) (om N) :=
  (ProjPos.fubiniStudy_weight_pullback_isSmooth _ _ (rd N)).isPotential (isAlg N)

theorem om_pos : IsPosPot (ProjAn.finAtlas ℤ σ₀ N) (om N) :=
  ((ProjPos.fubiniStudy_weight_pullback_isSmooth _ _ (rd N)).isPosPot_iff (isAlg N)).2 (ProjPos.fubiniStudy_weight_pullback_closed_immersion_strictPos _ _ (rd N))

theorem fs_pot : IsPotential (ProjAn.finAtlas ℤ σ₀ N) ((hermitianTwistingSheaf ℤ N).φ σ₀).locPot :=
  ((hermitianTwistingSheaf ℤ N).isSmooth (rd N)).isPotential (isAlg N)

theorem om_sameForm : SameForm (ProjAn.finAtlas ℤ σ₀ N) (om N) ((hermitianTwistingSheaf ℤ N).φ σ₀).locPot :=
  Weight.sameForm_of_eq _ (isAlg N) (fs_pot N) fun x =>
    ⟨fun _ => _, mem_ptsIn.2 (Set.mem_iInter.2 fun _ => mem_ptsIn.1 (((hermitianTwistingSheaf ℤ N).φ σ₀).locPot.mem_U x)), fun z => by
      refine (congrArg (· / 2) (Weight.pull_φ _ _ _ _ _)).trans ?_
      have e : Points.PtsOver.map (𝟙 _) (Category.id_comp (PSpace.str ℤ N)) _ z = z := Subtype.ext (Category.comp_id _)
      erw [e]
      rfl⟩

def man : Man N where
  n := 0
  X _ := CxPts (PSpace.str ℤ N) σ₀
  cpt _ := (isArithVar_int N).compactSpace _
  t2 _ := CxPts.t2Space_cxPts_of_isProjOver _ (isArithVar_int N).isProjOver
  ne _ := ⟨Points.projPt σ₀ ⟨fun _ => 1, by
    rw [Ideal.eq_top_iff_one]; exact Ideal.subset_span ⟨0, rfl⟩⟩⟩
  A _ := ProjAn.finAtlas ℤ σ₀ N
  Z _ := ∅
  r _ _ := Real.exp 1
  Om _ := om N
  bd _ := InhabCalc.isBd_empty _ _ (om_pot N) (om_pos N)
  κ := 1
  κ_pos := one_pos

theorem man_int (P : Fin N → (man N).Pot) (u : (man N).Fun) :
    (man N).int P u = mInt (ProjAn.finAtlas ℤ σ₀ N) (fun i => P i (0 : Fin 1)) (u (0 : Fin 1)) :=
  (one_mul _).trans (Fin.sum_univ_one _)

def pts (σ : ℤ →+* ℂ) : CxPts (PSpace.str ℤ N) σ → (man N).X 0 :=
  cast (congrArg (CxPts (PSpace.str ℤ N)) (Subsingleton.elim σ σ₀))

theorem smooth_iff (u : CxPts (PSpace.str ℤ N) σ₀ → ℝ) :
    (ProjAn.finAtlas ℤ σ₀ N).Smooth u ↔ ∀ y, CInfAt u y := by
  rw [(isAlg N).smooth_iff (rd N), ← CxPts.cInfAt_iff_smoothOn (rd N) isOpen_univ]
  simp

def calc₀ : Calc (man N) :=
  InhabCalc.calcOf (man N) (fun (_ : Unit) _ => ((hermitianTwistingSheaf ℤ N).φ σ₀).locPot) fun _ _ => fs_pot N

def cls₀ (i : Unit) : (calc₀ N).V := InhabCalc.cls (man N) _ (fun _ _ => fs_pot N) i

theorem chernOn : (calc₀ N).ChernOn (fun _ => 0) (pts N) 1 (fun _ : Unit => hermitianTwistingSheaf ℤ N) (cls₀ N) := by
  intro u hs hu hc n f hf
  have := (isArithVar_int N).compactSpace σ₀
  have := CxPts.t2Space_cxPts_of_isProjOver σ₀ (isArithVar_int N).isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver σ₀ (isArithVar_int N).isProjOver
  rw [one_mul, man_int, chInt, finsum_eq_single _ σ₀ fun σ h => absurd (Subsingleton.elim _ _) h]
  refine (ChernMA.chernInt_eq_mInt (HermLB.cInf _ _) (isAlg N) (projLine_continuous_of_smooth _ (hf 0))).trans ?_
  refine SameForm.mInt_eq (fun _ => Weight.sameForm_of_eq _ (isAlg N) ((calc₀ N).firstChern_isPotential _ 0) ?_) _
  refine (halfWeight_comb (σ := σ₀) (g := fun o : Option Unit => o.elim (fun _ z => u 0 z)
    fun _ => ((hermitianTwistingSheaf ℤ N).φ σ₀).locPot.φ) (fun o => ?_) n).congr fun x z => ?_
  · cases o with
    | none => exact (halfWeight_fnB _ hu hc).congr fun x z => mul_div_cancel_left₀ _ two_ne_zero
    | some i => exact halfWeight_locPot _
  · have e : (InhabCalc.smProj (man N) u : (man N).Fun) = u := InhabCalc.smProj_of_smooth _ hs
    rw [Fintype.sum_option, Fintype.sum_unique, Fintype.sum_unique]
    change _ = ∑ i : Unit, ((n (some ()) : ℝ) * @Pi.single Unit (fun _ => ℝ) _ (fun _ _ => Classical.propDecidable _) () 1 i + (n none : ℝ) * 0) *
      ((hermitianTwistingSheaf ℤ N).φ σ₀).locPot.φ x z + ((n (some ()) : ℝ) * 0 +
        (n none : ℝ) * (InhabCalc.smProj (man N) u : (man N).Fun) 0 z)
    rw [e]
    simp [add_comm]

theorem reads_proj_of (N : ℕ) (H : (calc₀ N).ChernOn (fun _ => 0) (pts N) 1 (fun _ : Unit => hermitianTwistingSheaf ℤ N) (cls₀ N) →
      ∃ (K : Calc (man N)) (v : Unit → K.V),
        (∀ i σ, LeviEq ((man N).A σ) (K.c1 (v i) σ) ((calc₀ N).c1 (cls₀ N i) σ)) ∧
        K.ChernOn (fun _ => 0) (pts N) 1 (fun _ : Unit => hermitianTwistingSheaf ℤ N) v ∧
        @Calc.NumOn N (man N) ℤ _ _ (PSpace.str ℤ N) K (fun _ => 0) (pts N) 1 Unit _ (fun _ => hermitianTwistingSheaf ℤ N) v
          (isArithVar_int N).isIntegral) :
    ∃ (M : Man N) (K : Calc M) (ε : (ℤ →+* ℂ) → Fin (M.n + 1))
    (π : ∀ σ, CxPts (PSpace.str ℤ N) σ → M.X (ε σ)) (v : Unit → K.V), (∀ σ, Function.Injective (π σ)) ∧
    0 < M.int (fun _ => K.c1 (v ())) (fun _ _ => 1) ∧
    @Calc.Reads N M ℤ _ _ (PSpace.str ℤ N) K ε π 1 Unit _ (fun _ => GlobalTheory.ProjSpace.hermitianTwistingSheaf ℤ N) v
      (GlobalTheory.ProjSpace.isArithVar_int N).isIntegral := by
  obtain ⟨K, v, h₁, h₂, h₃⟩ := H (chernOn N)
  refine ⟨man N, K, fun _ => 0, pts N, v, fun σ => ?_, ?_, isArithVar_int N, one_pos, fun σ => ?_,
    fun j => ⟨σ₀, Subsingleton.elim (α := Fin 1) _ _⟩, fun u hu σ => ?_, h₂, h₃⟩
  · obtain rfl : σ = σ₀ := Subsingleton.elim _ _
    exact Function.injective_id
  · refine lt_of_lt_of_eq (InhabCalc.int_Om_pos (man N) ⟨0, inferInstance⟩) ?_
    rw [man_int, man_int]
    refine (SameForm.mInt_eq (fun _ => om_sameForm N) _).trans (Eq.symm ?_)
    refine (LeviOnly.mInt_eq_of_leviEq N ((man N).X 0) ((man N).A 0) _ _ _ (fun _ => K.firstChern_isPotential _ 0)
      (fun _ => (calc₀ N).firstChern_isPotential (cls₀ N ()) 0) (fun _ => h₁ () 0)).1.trans ?_
    exact InhabCalc.mInt_congr_φ _ (fun _ => InhabCalc.first_chern_class_potential (man N) _ (fun _ _ => fs_pot N) () 0) _
  · obtain rfl : σ = σ₀ := Subsingleton.elim _ _
    exact ⟨continuous_id, Function.surjective_id⟩
  · obtain rfl : σ = σ₀ := Subsingleton.elim _ _
    exact (smooth_iff N _).1 (hu 0)

end GlobalTheory.Mean4O.ReadsProj
