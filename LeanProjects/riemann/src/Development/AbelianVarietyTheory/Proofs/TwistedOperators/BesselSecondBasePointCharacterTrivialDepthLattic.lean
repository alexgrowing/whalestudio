import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartTraceCharacterIdempotentInverseDiffere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentSumAuxiliaryPlaces

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.SecondBaseChar

open GlobalTheory.StdFrames (cpt)

variable {D : D7}

def bnd (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : AddSubgroup (AE D) where
  carrier := {t | infPart D t = 0 ∧ ∀ (Q : HeightOneSpectrum (𝓞 D.host.E)) (d : D.host.E),
    (∀ s ∈ I, Q.valuation D.host.E (d * s) ≤ 1) → Valued.v (cpt (D := D) Q (toEAf D (incA D d * t))) ≤ 1}
  zero_mem' := ⟨RingHom.map_zero _, fun Q d _ => by
    rw [mul_zero, RingHom.map_zero, RingHom.map_zero, Valuation.map_zero]; exact zero_le⟩
  add_mem' := fun {a b} ha hb => ⟨by rw [RingHom.map_add, ha.1, hb.1, add_zero], fun Q d h => by
    rw [mul_add, RingHom.map_add, RingHom.map_add]
    exact Valuation.map_add_le _ (ha.2 Q d h) (hb.2 Q d h)⟩
  neg_mem' := fun {a} ha => ⟨by rw [RingHom.map_neg, ha.1, neg_zero], fun Q d h => by
    rw [mul_neg, RingHom.map_neg, RingHom.map_neg, Valuation.map_neg]
    exact ha.2 Q d h⟩

theorem tmul_mem_bnd {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {α : Af D.host.F} (hα : α ∈ intAf D.host.F)
    {s : D.host.E} (hs : s ∈ I) : (pairA D.host.F 0 α) ⊗ₜ[D.host.F] s ∈ bnd I := by
  refine ⟨GlobalTheory.LatVac.infPart_pair α s, fun Q d h => ?_⟩
  have h1 : finPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ intAE D := by
    rw [GlobalTheory.LatVac.finPart_pair]
    exact AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩
  have h2 : Valued.v (cpt (D := D) Q (toEAf D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E)))) ≤ 1 :=
    ((GlobalTheory.StdFrames.comp_toAd D).int _).1 h1 Q
  have e : incA D d * (pairA D.host.F 0 α) ⊗ₜ[D.host.F] s =
      incA D (d * s) * (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [GlobalTheory.IdeleAA.tmul_eq, GlobalTheory.IdeleAA.tmul_eq, RingHom.map_mul, RingHom.map_one]; ring
  rw [e, RingHom.map_mul, RingHom.map_mul, Valuation.map_mul, Good.cpt_incA, Good.valued_alg]
  exact mul_le_one' (h s hs) h2

theorem psiE_eq_one {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {t : AE D} (h0 : infPart D t = 0)
    (h : ∀ d ∈ (GlobalTheory.IdeleAA.Dual D)⁻¹, ∀ Q : HeightOneSpectrum (𝓞 D.host.E),
      Valued.v (cpt (D := D) Q (toEAf D (incA D d * t))) ≤ 1) : psiE ψ t = 1 := by
  have hne : GlobalTheory.IdeleAA.Dual D ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  have h1 : (1 : D.host.E) ∈ GlobalTheory.IdeleAA.Dual D * (GlobalTheory.IdeleAA.Dual D)⁻¹ := by
    rw [mul_inv_cancel₀ hne]; exact FractionalIdeal.one_mem_one _
  have key : GlobalTheory.FinPl.Conductor.chi ψ (finPart D (incA D 1 * t)) = 1 := by
    refine FractionalIdeal.mul_induction_on
      (C := fun x => GlobalTheory.FinPl.Conductor.chi ψ (finPart D (incA D x * t)) = 1) h1 ?_ ?_
    · intro i hi j hj
      have h2 := GlobalTheory.IdeleAA.chi_dual hψ (γ := 1) (fun v => by rw [map_one]; exact one_mem _) hi
        (Good.mem_intAE (h j hj))
      rw [RingHom.map_mul (incA D), mul_assoc, RingHom.map_mul (finPart D), GlobalTheory.LatVac.finPart_incA]
      exact h2
    · intro x y hx hy
      rw [RingHom.map_add, add_mul, RingHom.map_add, GlobalTheory.FinPl.Conductor.chi_add, hx, hy, one_mul]
  rw [GlobalTheory.FinPl.Conductor.psiE_eq_chi ψ h0]
  rwa [RingHom.map_one, one_mul] at key

theorem val_le_of_mem_one (Q : HeightOneSpectrum (𝓞 D.host.E)) {x : D.host.E}
    (hx : x ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) : Q.valuation D.host.E x ≤ 1 := by
  obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
  exact Q.valuation_le_one c

theorem val_le_of_mem_inv (Q : HeightOneSpectrum (𝓞 D.host.E)) {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}
    {c : 𝓞 D.host.E} (hc : algebraMap _ D.host.E c ∈ I) (hQ : c ∉ Q.asIdeal) {x : D.host.E} (hx : x ∈ I⁻¹) :
    Q.valuation D.host.E x ≤ 1 := by
  have hI : I ≠ 0 := by
    rintro rfl
    have h := (FractionalIdeal.mem_zero_iff _).1 hc
    have : c = 0 := by simpa using h
    exact hQ (this ▸ zero_mem _)
  have h := val_le_of_mem_one Q ((FractionalIdeal.mem_inv_iff hI).1 hx _ hc)
  rwa [map_mul, Q.valuation_of_algebraMap, Q.intValuation_eq_one_iff.2 hQ, mul_one] at h

def coefLat {m n : ℕ} (r : Fin m → D.host.E) (z : Fin n → D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
    Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E) where
  carrier := {x | r ⬝ᵥ x *ᵥ z ∈ I}
  zero_mem' := by
    change _ ∈ I
    rw [zero_mulVec, dotProduct_zero]; exact I.zero_mem
  add_mem' := fun {a b} ha hb => by
    change _ ∈ I
    rw [add_mulVec, dotProduct_add]; exact I.val.add_mem ha hb
  smul_mem' := fun c x hx => by
    change _ ∈ I
    rw [smul_mulVec, dotProduct_smul]; exact I.val.smul_mem c hx

theorem coef_mem_bnd {m n : ℕ} (r : Fin m → D.host.E) (z : Fin n → D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    {M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E)} (hM : M ≤ coefLat r z I) {u : Mx D m n}
    (hu : u ∈ hatMx M) : ratV r ⬝ᵥ u *ᵥ ratV z ∈ bnd I := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    have e : ratV r ⬝ᵥ (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] x i j : Mx D m n) *ᵥ ratV z =
        (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (r ⬝ᵥ x *ᵥ z) := by
      simp only [GlobalTheory.IdeleAA.tmul_eq, dotProduct, mulVec, ratV, Matrix.of_apply, map_sum, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact tmul_mem_bnd hα (hM hx)
  | zero => rw [zero_mulVec, dotProduct_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mulVec, dotProduct_add]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mulVec, dotProduct_neg]; exact neg_mem hx

section SlopeTestRemainingChoices

variable {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
  (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)

theorem col_mem (p : Fin c) {β : D.host.E} (hβ : β ∈ 𝔟 p) : (β • fun k => d.a k p) ∈ d.lat Λ 𝔟 := by
  refine ⟨0, Λ.zero_mem, Pi.single p β, fun q => ?_, ?_⟩
  · by_cases h : q = p
    · subst h; rwa [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h]; exact (𝔟 q).zero_mem
  · rw [mulVec_zero, zero_add]
    funext k
    simp [mul_comm]

theorem coef_mem (p : Fin c) (hp : p.rev ≠ p) {y : Fin B.rank → D.host.E} (hy : y ∈ d.lat Λ 𝔟) :
    ((d.aᴴ * B.gram) *ᵥ y) p.rev ∈ 𝔟 p := by
  obtain ⟨y₀, -, u, hu, rfl⟩ := hy
  have h1 : d.aᴴ * B.gram * d.a = antiDiagonalSignGramMatrix c ε := by rw [← cT_sig]; exact d.gram
  have h2 : d.aᴴ * B.gram * frameMat B A d.ι = 0 := by
    have h := d.perp
    rw [cT_sig] at h
    have h' := congrArg conjTranspose h
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
      ← Matrix.mul_assoc] at h'
  rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, h1, h2, zero_mulVec, zero_add]
  have e : (antiDiagonalSignGramMatrix c ε *ᵥ u) p.rev = u p := by
    have := p.2
    rw [mulVec, dotProduct, Finset.sum_eq_single p]
    · rw [antiDiagonalSignGramMatrix, if_pos (by rw [Fin.val_rev]; omega), if_neg hp, one_mul]
    · intro q _ hq
      rw [antiDiagonalSignGramMatrix, if_neg, zero_mul]
      rw [Fin.val_rev]
      intro h
      exact hq (Fin.ext (by omega))
    · exact fun h => absurd (Finset.mem_univ p) h
  rw [e]
  exact hu p

theorem qX_apply {A B B₀ : HSp D} {c ρ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (w : HypDec B B₀ ρ) (hw : IsAuxiliaryVectorWittDec d w) (i : Fin ρ)
    (p : Fin c) (hp : p.1 = i.1) (y : Fin B.rank → D.host.E) :
    (-D.host.xi0) ^ (i.1 + 1) * (w.qX *ᵥ y) i = ((d.aᴴ * B.gram) *ᵥ y) p.rev := by
  obtain ⟨h, he, s, he'⟩ := hw
  have hle : ρ ≤ c := by clear hp; omega
  obtain rfl : p = Fin.castLE hle i := Fin.ext hp
  have k : ∀ y : Fin B.rank → D.host.E, (w.qX *ᵥ y) i =
      star (s i) * ((d.aᴴ * B.gram) *ᵥ y) (Fin.castLE (by omega) i : Fin c).rev := fun y => by
    rw [HypDec.qX, ← mulVec_mulVec, ← mulVec_mulVec, he']
    simp only [mulVec, dotProduct, conjTranspose_apply, colsOf, star_mul', Finset.mul_sum, mul_assoc]
  have h1 : d.aᴴ * B.gram * d.a = antiDiagonalSignGramMatrix c (-1) := by rw [← cT_sig]; exact d.gram
  have h2 : star (s i) * (-D.host.xi0) ^ (i.1 + 1) = 1 := by
    have h3 : (w.qX *ᵥ fun k => w.e k i) i = 1 := by
      have := congrFun (congrFun (qX_e w) i) i
      rw [Matrix.one_apply_eq] at this
      exact this
    have h4 : (fun k => w.e k i) = (-D.host.xi0) ^ (i.1 + 1) • fun k => d.a k (Fin.castLE (by omega) i) := by
      rw [he]; rfl
    have h5 : ((d.aᴴ * B.gram) *ᵥ fun k => d.a k (Fin.castLE (by omega) i)) (Fin.castLE (by omega) i : Fin c).rev = 1 := by
      have := congrFun (congrFun h1 (Fin.castLE (by omega) i : Fin c).rev) (Fin.castLE (by omega) i)
      refine Eq.trans this ?_
      have := i.2
      rw [antiDiagonalSignGramMatrix, if_pos (by rw [Fin.val_rev, Fin.val_castLE]; omega), if_neg]
      intro h
      have := congrArg Fin.val h
      rw [Fin.val_rev, Fin.val_castLE] at this
      omega
    rw [k, h4, mulVec_smul, Pi.smul_apply, h5, smul_eq_mul, mul_one] at h3
    exact h3
  rw [k, ← mul_assoc, mul_comm _ (star (s i)), h2, one_mul]

end SlopeTestRemainingChoices

theorem mem_of_forall_mul {I J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hI : I ≠ 0) {x : D.host.E}
    (h : ∀ β ∈ I, x * β ∈ J) : x ∈ J * I⁻¹ := by
  have hle : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ x * I ≤ J := by
    rw [FractionalIdeal.mul_le]
    intro i hi j hj
    obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
    rw [smul_mul_assoc]
    exact J.val.smul_mem c (h j hj)
  have h2 := mul_le_mul_left hle I⁻¹
  rw [mul_assoc, mul_inv_cancel₀ hI, mul_one] at h2
  exact h2 (FractionalIdeal.mem_spanSingleton_self _ x)

theorem latO_le {S T : HSp D} {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS)
    {M : Submodule (𝓞 D.host.E) (Matrix (Fin T.rank) (Fin S.rank) D.host.E)}
    (hM : ∀ a ∈ D.host.AA, ∀ x ∈ homLat LS LT, a • x ∈ M) {u : Mx D T.rank S.rank}
    (hu : u ∈ latO (negSp S) T (LS : Set _) (LT : Set _) fun _ => True) : u ∈ hatMx M := by
  refine (AddSubgroup.closure_le (hatMx M)).2 ?_ hu
  rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
  refine AddSubgroup.subset_closure ⟨α, hα, a • Matrix.of fun i j => t i * ∑ k, star (s k) * (negSp S).gram k j,
    hM a ha _ fun y hy => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := (hS.2 y).1 hy s hs
    have e : (Matrix.of fun i j => t i * ∑ k, star (s k) * (negSp S).gram k j) *ᵥ y = (-b) • t := by
      funext i
      rw [Pi.smul_apply, Algebra.smul_def, map_neg]
      change _ = -(b : D.host.E) * t i
      rw [hb, Finset.sum_comm]
      simp only [mulVec, dotProduct, Matrix.of_apply, negSp_gram, Matrix.neg_apply, Finset.sum_mul, Finset.mul_sum,
        ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    exact LT.smul_mem _ ht
  · funext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc]

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem coe_ne {I : Ideal (𝓞 D.host.E)} (h : I ≠ ⊥) : (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.2 h

theorem ideals_ne (D : D7) : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 ≠ 0 ∧ D.host.AA ≠ 0 ∧ D.host.AAbar ≠ 0 := by
  have hne : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA * D.host.AAbar ≠ 0 := by
    rw [Formalism.L2.Pj.dual_eq Formalism.IndefR.Fin.factPrincipalDatum D]
    exact FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  exact ⟨left_ne_zero_of_mul (left_ne_zero_of_mul hne), right_ne_zero_of_mul (left_ne_zero_of_mul hne),
    right_ne_zero_of_mul hne⟩

open scoped Pointwise in
theorem st_ne (P : Places L) : P.stA sc ≠ 0 ∧ P.stAbar sc ≠ 0 := by
  refine ⟨mul_ne_zero (ideals_ne D).2.1 (inv_ne_zero (coe_ne ?_)),
    mul_ne_zero (ideals_ne D).2.2 (inv_ne_zero (coe_ne (P.modul_ne_bot sc)))⟩
  intro h
  apply P.modul_ne_bot sc
  have h2 := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h
  simp only [Places.modulBar, inv_smul_smul] at h2
  rw [h2]
  exact smul_zero _

theorem z_eq {F : Asc.Frames G} (hF : Std F) (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) :
    (F.dB ρ h).i₀ *ᵥ vecB (F.oB ρ h) (F.ζ (ρ + 1)) =
      (-D.host.xi0) ^ (ρ + 1) • fun k => (G.colDec (2 * ρ + 2) (by omega) h).a k ⟨ρ, by omega⟩ := by
  rw [vecB, mulVec_mulVec, hF.ζ (ρ + 1), mulVec_smul, hF.zB' ρ h]

theorem homLat_le {F : Asc.Frames G} (hF : Std F) (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (i : Fin ρ) (hi : i.1 + 1 = ρ) :
    homLat (G.Λ (.grid (2 * ρ + 1 + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) ≤
      coefLat ((F.dJ ρ h).qX i) ((F.dB ρ h).i₀ *ᵥ vecB (F.oB ρ h) (F.ζ (ρ + 1)))
        (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * G.pl.stAbar sc) := by
  intro x hx
  obtain ⟨n1, n2⟩ := st_ne (sc := sc) G.pl
  have lS : G.Λ (.grid (2 * ρ + 1 + 1) 0) = _ := G.sp.colLat (2 * ρ + 2) (by omega) h
  have lT : G.Λ (.grid (2 * ρ + 1) 0) = _ := G.sp.colLat (2 * ρ + 1) (by omega) (by omega)
  set dS := G.colDec (2 * ρ + 2) (by omega) h with hdS
  set dT := G.colDec (2 * ρ + 1) (by omega) (by omega) with hdT
  let pS : Fin (2 * ρ + 2 - 1) := ⟨ρ, by omega⟩
  let pT : Fin (2 * ρ + 1 - 1) := ⟨i.1, by omega⟩
  have hrev : pT.rev ≠ pT := fun e => by
    have := congrArg Fin.val e
    rw [Fin.val_rev] at this
    change 2 * ρ + 1 - 1 - (i.1 + 1) = i.1 at this
    omega
  have hc := mem_of_forall_mul (I := stairId (G.pl.stA sc) (G.pl.stAbar sc) _ pS)
    (J := stairId (G.pl.stA sc) (G.pl.stAbar sc) _ pT)
    (x := ((dT.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ (x *ᵥ fun k => dS.a k pS)) pT.rev)
    (mul_ne_zero (pow_ne_zero _ n1) (inv_ne_zero (pow_ne_zero _ n2))) fun β hβ => by
      have h1 := hx _ (lS ▸ col_mem dS (G.Λ (.core (2 * ρ + 2))) _ pS hβ)
      rw [lT] at h1
      have h2 := coef_mem dT _ _ pT hrev h1
      rwa [mulVec_smul, mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_comm β] at h2
  have e : stairId (G.pl.stA sc) (G.pl.stAbar sc) _ pT * (stairId (G.pl.stA sc) (G.pl.stAbar sc) _ pS)⁻¹ =
      G.pl.stAbar sc := by
    have e1 : 2 * ρ + 1 - 1 - pT.1 = ρ + 1 := by change 2 * ρ + 1 - 1 - i.1 = _; omega
    have e2 : 2 * ρ + 2 - 1 - pS.1 = ρ + 1 := by change 2 * ρ + 2 - 1 - ρ = _; omega
    have e3 : pT.1 + 1 = ρ := hi
    have e4 : pS.1 + 1 = ρ + 1 := rfl
    unfold stairId
    rw [e1, e2, e3, e4, pow_succ (G.pl.stAbar sc)]
    field_simp
  rw [e, ← qX_apply dT (F.dJ ρ h) (hF.hJ ρ h) i pT rfl, hi] at hc
  have h3 := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self (𝓞 D.host.E)⁰ D.host.xi0) hc
  change ((F.dJ ρ h).qX *ᵥ (x *ᵥ _)) i ∈ (_ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
  rw [z_eq hF ρ h, mulVec_smul, mulVec_smul, Pi.smul_apply, smul_eq_mul, pow_succ', mul_assoc, neg_mul]
  exact Submodule.neg_mem _ h3

theorem mul_mem_inv {J I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hJ : J ≠ 0) {d s : D.host.E} (hd : d ∈ J⁻¹)
    (hs : s ∈ J * I⁻¹) : d * s ∈ I⁻¹ := by
  have h := FractionalIdeal.mul_mem_mul hd hs
  rwa [← mul_assoc, inv_mul_cancel₀ hJ, one_mul] at h

theorem exists_modul (G : GridData L sc) {Q : HeightOneSpectrum (𝓞 D.host.E)} (hQ : Q ∉ G.pl.W0) :
    ∃ c ∈ G.modul, c ∉ Q.asIdeal := by
  classical
  by_contra hc
  push Not at hc
  have hle : G.pl.modul sc ≤ Q.asIdeal := hc
  rw [Places.modul] at hle
  obtain ⟨v, hv, h⟩ := (Ideal.IsPrime.prod_le Q.isPrime).1 hle
  have h2 := GlobalTheory.IdemSupport.eq_of_le (Ideal.IsPrime.le_of_pow_le (hP := Q.isPrime) h)
  apply hQ
  rw [← h2]
  unfold Places.W0
  convert Finset.mem_image_of_mem G.pl.w hv

theorem exists_AA {μ₀ : T} (hL : L.Is μ₀) (hq : OffQ D) (G : GridData L sc) {Q : HeightOneSpectrum (𝓞 D.host.E)}
    (hQ : Q ∈ G.pl.W0) : ∃ c : 𝓞 D.host.E, algebraMap _ D.host.E c ∈ D.host.AA ∧ c ∉ Q.asIdeal := by
  classical
  have hb := Good.badInt_notMem hL (G := G) (t := μ₀) hq (fun P hP => absurd
    (show (L.xiH μ₀).UnrAt P by rw [hL.xi_base]; exact fun x _ => rfl) ((hL.Q_ram μ₀ P).2 (Or.inl hP)))
    (Finset.mem_union_left _ hQ)
  refine ⟨((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E), ?_,
    fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro_left _ rfl))⟩
  have h1 : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∈ D.host.ccE := by
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) (Ideal.absNorm_mem D.host.ccK)
    rwa [map_natCast] at this
  have h0 : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := fun h => by
    apply (ideals_ne D).2.1
    rw [Host.AA, Host.AA0, h, _root_.inv_zero, mul_zero]
  have h2 : (1 : D.host.E) ∈ D.host.AA0 := by
    rw [Host.AA0, FractionalIdeal.mem_inv_iff h0]
    intro y hy
    rw [one_mul]
    exact FractionalIdeal.coeIdeal_le_one hy
  have h3 := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 D.host.E)⁰ h1) h2
  rwa [mul_one] at h3

set_option maxHeartbeats 1000000 in

theorem ychar : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * ρ + 1), W.ψ (symplO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).incAdj (F.V₀ ρ) (yBF F ρ h)) ((F.dJ ρ h).incX (F.V₀ ρ) ((F.dJ ρ h).pX ⬝ (u ⬝ (F.dB ρ h).j0)))) = 1 := by
  intro D hq T L μ₀ hL sc G W M _ F hF ρ h u hu
  refine (congrArg W.ψ (symplO_yZero (F.dJ ρ h) _ _)).trans ?_
  change psiE W.ψ _ = 1
  rcases Nat.eq_zero_or_pos ρ with rfl | hρ
  · rw [dotProduct, Finset.sum_of_isEmpty, psiE_zero]
  let i : Fin ρ := ⟨ρ - 1, by omega⟩
  have hi : i.1 + 1 = ρ := by change ρ - 1 + 1 = ρ; omega
  set r := (F.dJ ρ h).qX i with hr
  set z := (F.dB ρ h).i₀ *ᵥ vecB (F.oB ρ h) (F.ζ (ρ + 1)) with hz
  have e : ell D ρ ⬝ᵥ ((F.dJ ρ h).pX ⬝ (u ⬝ (F.dB ρ h).j0)) *ᵥ ratV (vecB (F.oB ρ h) (F.ζ (ρ + 1))) =
      ratV r ⬝ᵥ (show Mx D _ _ from u) *ᵥ ratV z := by
    rw [hz, ratV_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct, Finset.sum_eq_single i]
    · rw [ell, if_pos hi, one_mul]; rfl
    · intro j _ hj
      rw [ell, if_neg fun e => hj (Fin.ext (by omega)), zero_mul]
    · exact fun h => absurd (Finset.mem_univ i) h
  rw [e]
  obtain ⟨n0, n1, n2⟩ := ideals_ne D
  have n3 := coe_ne (G.pl.modul_ne_bot sc)
  have hJ : GlobalTheory.IdeleAA.Dual D = _ := (Formalism.L2.Pj.dual_eq Formalism.IndefR.Fin.factPrincipalDatum D).symm
  have hne : GlobalTheory.IdeleAA.Dual D ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  have hle := homLat_le hF ρ h i hi
  have hS : IsSelfDualC _ (G.Λ (.grid (2 * ρ + 1 + 1) 0)) :=
    (G.sp.V_is (2 * ρ + 1 + 1) 0 (by omega) h (by omega)).sd
  have b1 : ratV r ⬝ᵥ (show Mx D _ _ from u) *ᵥ ratV z ∈
      bnd (GlobalTheory.IdeleAA.Dual D * ((G.modul : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹) := by
    refine coef_mem_bnd r z _ le_rfl (latO_le hS (fun a ha x hx => ?_) hu.1)
    have h1 := FractionalIdeal.mul_mem_mul ha (hle hx)
    change _ ∈ (_ : FractionalIdeal _ _)
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul, hJ]
    convert h1 using 1
    rw [Places.stAbar]; ring
  obtain ⟨ε, hε⟩ := GlobalTheory.GridIdem.exists_idempotentSum_auxiliaryPlaces D T L G.pl
  have b2 : ε * (ratV r ⬝ᵥ (show Mx D _ _ from u) *ᵥ ratV z) ∈ bnd (GlobalTheory.IdeleAA.Dual D * D.host.AA⁻¹) := by
    have h1 := coef_mem_bnd r z (GlobalTheory.IdeleAA.Dual D * D.host.AA⁻¹) (Submodule.smul_le.2 fun a ha x hx => ?_) (hu.2 ε hε)
    · rwa [smul_mulVec, dotProduct_smul, smul_eq_mul] at h1
    have h1 := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 D.host.E)⁰ ha) (hle hx)
    change _ ∈ (_ : FractionalIdeal _ _)
    rw [smul_mulVec, dotProduct_smul, Algebra.smul_def, hJ]
    convert h1 using 1
    rw [Places.stAbar]; field_simp
  refine psiE_eq_one W.ψ_std b1.1 fun d hd Q => ?_
  by_cases hQ : Q ∈ G.pl.W0
  · obtain ⟨c, hc, hcQ⟩ := exists_AA hL hq G hQ
    have h1 := b2.2 Q d fun s hs => val_le_of_mem_inv Q hc hcQ (mul_mem_inv hne hd hs)
    rwa [mul_left_comm, RingHom.map_mul, RingHom.map_mul, (Comparison₂.cpt_idemSum hε).2.1 Q hQ, one_mul] at h1
  · obtain ⟨c, hc, hcQ⟩ := exists_modul G hQ
    exact b1.2 Q d fun s hs =>
      val_le_of_mem_inv Q (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 D.host.E)⁰ hc) hcQ (mul_mem_inv hne hd hs)

end GlobalTheory.SecondBaseChar

end
