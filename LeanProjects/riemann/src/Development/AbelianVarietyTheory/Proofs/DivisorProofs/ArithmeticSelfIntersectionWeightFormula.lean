import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArithmeticVarietyDimZeroFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLogarithmSpanningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralLogUnitVanishesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.Points ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ChIntPull

open GlobalTheory.CxPts

theorem valR_spMap_top {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a : R) :
    valR (spMap f) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) = f a := by
  have h : ⊤ ≤ spMap f ⁻¹ᵁ ⊤ := fun x _ => trivial
  unfold valR
  rw [dif_pos h, show (spMap f).appLE ⊤ ⊤ h = (spMap f).appTop from Scheme.Hom.appLE_eq_app _]
  have e := congrArg (fun q => CommRingCat.Hom.hom q ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.comp_apply] at e
  calc _ = _ := e
    _ = f a := by simp

theorem chernInt_sum_mul {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {B : LB X}
    (φ : Weight p σ B) (D : ℕ) (S : Set (CxPts p σ)) {m : ℕ} (f : Fin m → CxPts p σ → ℝ) (r : Fin m → ℝ)
    (h : ∀ j, φ.ChernIntegrableOn D S (f j)) :
    φ.chernInt D S (fun y => ∑ j, r j * f j y) = ∑ j, r j * φ.chernInt D S (f j) := by
  unfold Weight.chernInt
  rw [MeasureTheory.integral_finset_sum _ fun j _ => (h j).1.const_mul (r j),
    MeasureTheory.integral_finset_sum _ fun j _ => (h j).2.const_mul (r j), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, mul_sub]

variable {k k' : Type} [CommRing k] [CommRing k'] [Algebra k k']

def ptsEquiv : (Σ σ : k →+* ℂ, CxPts (spMap (algebraMap k k')) σ) ≃ (k' →+* ℂ) where
  toFun q := (Spec.preimage q.2.1).hom
  invFun τ := ⟨τ.comp (algebraMap k k'), ⟨spMap τ, by
    show Spec.map _ ≫ Spec.map _ = Spec.map (CommRingCat.ofHom (algebraMap k k') ≫ CommRingCat.ofHom τ)
    rw [Spec.map_comp]⟩⟩
  left_inv := by
    rintro ⟨σ, y, hy⟩
    have hσ : (Spec.preimage y).hom.comp (algebraMap k k') = σ := by
      have e : Spec.map (CommRingCat.ofHom (algebraMap k k') ≫ Spec.preimage y) = Spec.map (CommRingCat.ofHom σ) := by
        rw [Spec.map_comp, Spec.map_preimage]
        exact hy
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
    subst hσ
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext (Spec.map_preimage y)))
  right_inv τ := by
    show (Spec.preimage (Spec.map (CommRingCat.ofHom τ))).hom = τ
    rw [Spec.preimage_map]
    rfl

theorem ptsEquiv_apply (q : Σ σ : k →+* ℂ, CxPts (spMap (algebraMap k k')) σ) (a : k') :
    ptsEquiv q a = CxPts.ev _ q.1 ⊤ ((Scheme.ΓSpecIso (CommRingCat.of k')).inv a) q.2 := by
  show (Spec.preimage q.2.1).hom a = valR q.2.1 ⊤ _
  conv_rhs => rw [← Spec.map_preimage q.2.1]
  exact (valR_spMap_top (Spec.preimage q.2.1).hom a).symm

end GlobalTheory.ChIntPull

open GlobalTheory.ChIntPull in

theorem GlobalTheory.ChIntPull.chInt_pull_eq_zero : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (k' : Type) [CommRing k'] [IsDomain k'] [Algebra k k'] (ρ : X ⟶ Sp k')
    (hρ : ρ ≫ spMap (algebraMap k k') = p), IsArithVar (spMap (algebraMap k k')) 0 →
    ∀ (c : ∀ σ : k →+* ℂ, CxPts (spMap (algebraMap k k')) σ → ℝ), (∀ σ y, CxPts.CInfAt (c σ) y) →
    (∀ σ σ', (Weight.ofFun (c σ)).IsConj (Weight.ofFun (c σ'))) → ∑ᶠ σ, ∑ᶠ y, c σ y = 0 →
    ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ),
      chInt (comb L n) D (fun σ y => c σ (PtsOver.map ρ hρ _ y)) = 0 := by
  intro H k _ X _ p D hX k' _ _ _ ρ hρ hk' c hc hcc hs ι _ L n
  have hfin : Module.Finite ℤ k' := by
    have := hX.finite
    have hF := GlobalTheory.ArithCurveFinite.isFinite k (Sp k') _ hk'
    have : Module.Finite k k' := RingHom.finite_algebraMap.1 ((IsFinite.SpecMap_iff _).1 hF)
    exact Module.Finite.trans k k'
  have hcz : CharZero k' := by
    have := hk'.charZero
    exact RingHom.charZero (Scheme.ΓSpecIso (CommRingCat.of k')).inv.hom
  have hfe : Finite (k' →+* ℂ) := .of_equiv _ (RingHom.equivIntAlgHom k' ℂ).symm
  have hfk : Finite (k →+* ℂ) := hX.finite_emb
  have hfy : ∀ σ, Finite (CxPts (spMap (algebraMap k k')) σ) := fun σ =>
    Finite.of_injective (fun y => ptsEquiv (⟨σ, y⟩ : Σ σ : k →+* ℂ, CxPts (spMap (algebraMap k k')) σ))
      fun y y' h => by simpa using ptsEquiv.injective h
  let C : (k' →+* ℂ) → ℝ := fun τ => c (ptsEquiv.symm τ).1 (ptsEquiv.symm τ).2
  have hCe : ∀ q, C (ptsEquiv q) = c q.1 q.2 := fun q => by
    show c (ptsEquiv.symm (ptsEquiv q)).1 (ptsEquiv.symm (ptsEquiv q)).2 = _
    rw [Equiv.symm_apply_apply]
  have hCc : ∀ τ, C ((starRingEnd ℂ).comp τ) = C τ := fun τ =>
    hcc _ _ PUnit.unit (ptsEquiv.symm τ).2 (ptsEquiv.symm ((starRingEnd ℂ).comp τ)).2
      (show Spec.map (CommRingCat.ofHom ((starRingEnd ℂ).comp τ)) = Spec.map _ ≫ Spec.map _ by
        rw [← Spec.map_comp]; rfl) CxPts.mem_ptsIn_top
  have hCs : ∑ᶠ τ, C τ = 0 := by
    have := Fintype.ofFinite (k →+* ℂ)
    have := fun σ => Fintype.ofFinite (CxPts (spMap (algebraMap k k')) σ)
    rw [← finsum_comp_equiv (ptsEquiv (k := k) (k' := k')), ← hs]
    simp only [hCe, finsum_eq_sum_of_fintype]
    exact Fintype.sum_sigma _
  obtain ⟨m, a, r, hr⟩ := GlobalTheory.T.unit_logarithm_spanning k' C hCc hCs
  let aX : Fin m → Γ(X, ⊤)ˣ := fun j =>
    Units.map (ρ.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k')).inv.hom).toMonoidHom (a j)
  have key : ∀ σ (y : CxPts p σ), c σ (PtsOver.map ρ hρ _ y) = ∑ j, r j * CxPts.logSq y ⊤ (aX j) := by
    intro σ y
    rw [← hCe ⟨σ, PtsOver.map ρ hρ _ y⟩, hr]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ptsEquiv_apply, CxPts.logSq, ← CxPts.ev_app ρ hρ ⊤]
    rfl
  have hint := fun j => GlobalTheory.T.chern_integral_log_unit_vanishes H k X p D hX (aX j) ι L n
  have := Fintype.ofFinite (k →+* ℂ)
  have e : ∀ σ, ((comb L n).φ σ).chernInt D Set.univ (fun y => c σ (PtsOver.map ρ hρ _ y)) =
      ∑ j, r j * ((comb L n).φ σ).chernInt D Set.univ (fun y => CxPts.logSq y ⊤ (aX j)) := fun σ => by
    simp only [key]
    exact chernInt_sum_mul _ D _ _ r fun j => (hint j).1 σ
  unfold chInt
  rw [finsum_eq_sum_of_fintype]
  simp only [e]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← Finset.mul_sum]
  have h0 := (hint j).2
  unfold chInt at h0
  rw [finsum_eq_sum_of_fintype] at h0
  rw [h0, mul_zero]
