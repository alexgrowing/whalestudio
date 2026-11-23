import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSIffKsRel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvRFrMapOfIsReduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualNumberEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerMatrixFirstOrderDeformationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCoverWithDualNumberDerivationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerTangentVectorsLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomDualNumberSndEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberDeformationExtendsAwayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartFrameDeformationOfDerivationCombinatiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenKodairaSpencerLeftInverseStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

namespace GlobalTheory.HorFrame

def combDer {R : Type} [CommRing R] {ι : Type} [Fintype ι] (δ : ι → (R →+* DualNumber R))
    (hδ : ∀ i s, (δ i s).fst = s) (A : ι → R) : R →+* DualNumber R where
  toFun s := TrivSqZeroExt.inl s + TrivSqZeroExt.inr (∑ i, A i * (δ i s).snd)
  map_one' := by
    have h : ∀ i, (δ i 1).snd = 0 := fun i => by rw [map_one]; rfl
    ext <;> simp [h]
  map_mul' x y := by
    have h : ∀ i, (δ i (x * y)).snd = x * (δ i y).snd + (δ i x).snd * y := fun i => by
      rw [map_mul, TrivSqZeroExt.snd_mul, hδ, hδ, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
        TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
        smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, h, Finset.mul_sum, Finset.sum_mul,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
  map_zero' := by
    have h : ∀ i, (δ i 0).snd = 0 := fun i => by rw [map_zero]; rfl
    ext <;> simp [h]
  map_add' x y := by
    ext <;> simp [Finset.sum_add_distrib, mul_add]

theorem combDer_fst {R : Type} [CommRing R] {ι : Type} [Fintype ι] (δ : ι → (R →+* DualNumber R))
    (hδ : ∀ i s, (δ i s).fst = s) (A : ι → R) (s : R) : (combDer δ hδ A s).fst = s := by
  simp [combDer]

theorem combDer_snd {R : Type} [CommRing R] {ι : Type} [Fintype ι] (δ : ι → (R →+* DualNumber R))
    (hδ : ∀ i s, (δ i s).fst = s) (A : ι → R) (s : R) :
    (combDer δ hδ A s).snd = ∑ i, A i * (δ i s).snd := by
  simp [combDer]

theorem fst_dualMap {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (x : DualNumber S) :
    (dualMap φ x).fst = φ x.fst := by simp [dualMap]

theorem snd_dualMap {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (x : DualNumber S) :
    (dualMap φ x).snd = φ x.snd := by simp [dualMap]

end GlobalTheory.HorFrame

open GlobalTheory.HorFrame in

theorem GlobalTheory.HorFrame.exists_horizontal_lift : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (hP : GlobalTheory.Published.AbelianDeRham)
    (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) (k : X.F.J)
    (W : M.X.Opens) (hW : W ≤ M.off ⊓ (toFlag M) ⁻¹ᵁ X.F.U k) (p : M.X) (hp : p ∈ W), ∃ (W' : M.X.Opens) (hW' : IsAffineOpen W')
      (e : HIx Dw (psiSet H) → (Γ(M.X, W') →+* DualNumber Γ(M.X, W'))),
      p ∈ W' ∧ W' ≤ W ∧ (∀ b s, (e b s).fst = s) ∧
      ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W') →+* K)
        (hk : ⊤ ≤ ((spMap ψ ≫ tau hW') ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K),
        X.F.ChartFr k _ hk Q → ∀ b, ∃ w : FrPt Xo c (DualNumber K), IsDef Q w ∧
          GlobalTheory.FlagTan.IsKS (psiSet H) Q w.x (Pi.single b 1) ∧
          spMap ((dualMap ψ).comp (e b)) ≫ tau hW' ≫ toFlag M = X.ptY w := by
  intro E _ _ _ H Dw l Xo c Y X Z M hP hKS k W hW p hp
  haveI := c.fin
  obtain ⟨W₁, hW₁, d, hpW₁, hW₁W, hd, hspan⟩ := GlobalTheory.T.exists_affine_cover_with_dual_number_derivations M W p hp
  have hoff : W₁ ≤ M.off := fun x hx => (hW (hW₁W hx)).1
  have hτ : ⊤ ≤ tau hW₁ ⁻¹ᵁ W₁ := tau_le hW₁ le_rfl
  have hk₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ X.F.U k := fun s _ => (hW (hW₁W (hτ (Set.mem_univ s)))).2
  have hF₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ flagOpen X := fun s _ => by
    have := hoff (hτ (Set.mem_univ s))
    rw [M.off_eq] at this
    exact this
  obtain ⟨alg₁, hch⟩ := GlobalTheory.CompHS.exists_chartFr (tau hW₁ ≫ toFlag M) hF₁
  obtain ⟨Q₀, hQ₀⟩ := hch k hk₁
  have hdalg : ∀ b, (d b).comp (algebraMap c.F Γ(M.X, W₁)) = algebraMap c.F (DualNumber Γ(M.X, W₁)) :=
    fun b => RingHom.ext fun a => TrivSqZeroExt.ext
      (by rw [RingHom.comp_apply, hd]; rfl) (by
      rw [GlobalTheory.T.ringHom_numberField_dualNumber_snd_eq_zero c.F ((d b).comp (algebraMap c.F _)) a]; rfl)
  have hx1 : ∀ b, (spMap (d b) ≫ Q₀.x) ≫ Xo.s = sOf c (DualNumber Γ(M.X, W₁)) := fun b => by
    rw [Category.assoc, Q₀.x_over]
    unfold sOf
    rw [spMap_comp', ← RingHom.comp_assoc, hdalg]
  have hx2 : ∀ b, spMap (TrivSqZeroExt.fstHom Γ(M.X, W₁) Γ(M.X, W₁) Γ(M.X, W₁)).toRingHom ≫ spMap (d b) ≫ Q₀.x
      = Q₀.x := fun b => by
    rw [← Category.assoc, spMap_comp']
    have : (TrivSqZeroExt.fstHom Γ(M.X, W₁) Γ(M.X, W₁) Γ(M.X, W₁)).toRingHom.comp (d b) = RingHom.id _ :=
      RingHom.ext fun s => hd b s
    rw [this]
    exact (congrArg (· ≫ Q₀.x) (Spec.map_id _)).trans (Category.id_comp _)
  choose Mx hMx using fun b => GlobalTheory.T.exists_kodairaSpencerMatrix_firstOrderDeformation hP Q₀ (spMap (d b) ≫ Q₀.x) (hx1 b) (hx2 b)
  obtain ⟨B, hB⟩ := GlobalTheory.T.exists_basicOpen_kodairaSpencer_left_inverse M hKS k hW₁ hoff hk₁ Q₀ hQ₀ d hd hspan Mx hMx p hpW₁
  set MxM : Matrix (Fin (dimFlag Dw)) (HIx Dw (psiSet H)) Γ(M.X, W₁) := Matrix.of (fun a h => Mx a h) with hMxM
  set g : Γ(M.X, W₁) := (B * MxM).det with hg
  have hW' : IsAffineOpen (M.X.basicOpen g) := hW₁.basicOpen g
  have hW'W₁ : M.X.basicOpen g ≤ W₁ := M.X.basicOpen_le g
  haveI := hW₁.isLocalization_basicOpen g
  set ρ := algebraMap Γ(M.X, W₁) Γ(M.X, M.X.basicOpen g) with hρ
  choose d' hd'1 hd'2 using fun b => GlobalTheory.T.exists_dualNumber_deformation_extend_away (S' := Γ(M.X, M.X.basicOpen g)) g (d b) (hd b)
  have hunit : IsUnit ((B * MxM).map ρ).det := by
    have : ((B * MxM).map ρ).det = ρ (B * MxM).det := by rw [RingHom.map_det]; rfl
    rw [this]
    exact IsLocalization.Away.algebraMap_isUnit g
  set A := ((B * MxM).map ρ)⁻¹ * B.map ρ with hA
  have hAM : A * MxM.map ρ = 1 := by
    rw [hA, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hunit]
  have hτ' : spMap ρ ≫ tau hW₁ = tau hW' := by
    have e1 := spMap_ev (tau hW') hW₁ (tau_le hW' hW'W₁)
    have e2 : ev (tau hW') W₁ (tau_le hW' hW'W₁) = ρ := RingHom.ext fun a => ev_tau hW' hW'W₁ _ a
    rw [← e2]
    exact e1
  refine ⟨M.X.basicOpen g, hW', fun b => combDer d' hd'1 (fun a => A b a), hB, hW'W₁.trans hW₁W,
    fun b s => combDer_fst _ _ _ _, ?_⟩
  intro K _ _ ψ hk Q hQ b
  have ez : (spMap ψ ≫ tau hW') ≫ toFlag M = (spMap (ψ.comp ρ) ≫ tau hW₁) ≫ toFlag M := by
    rw [← hτ', ← spMap_comp' ρ ψ]
    simp only [Category.assoc]
  have hk' : ⊤ ≤ ((spMap (ψ.comp ρ) ≫ tau hW₁) ≫ toFlag M) ⁻¹ᵁ X.F.U k := ez ▸ hk
  have hQ' : X.F.ChartFr k _ hk' Q :=
    hQ.frMap (frMap_refl Q) ((spMap_algId _).trans ez) hk'
  obtain ⟨w, hwD, hwKS, hwpt⟩ := GlobalTheory.T.exists_chart_frame_deformation_of_derivation_combination M hKS k hW₁ hk₁ Q₀ hQ₀ d hd Mx hMx K (ψ.comp ρ) hk' Q hQ'
    ((dualMap ψ).comp ((combDer d' hd'1 (fun a => A b a)).comp ρ)) (fun a => ψ (A b a))
    (fun s => by rw [RingHom.comp_apply, fst_dualMap, RingHom.comp_apply, combDer_fst]; rfl)
    (fun s => by
      rw [RingHom.comp_apply, snd_dualMap, RingHom.comp_apply, combDer_snd, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, hd'2]
      rfl)
  refine ⟨w, hwD, ?_, ?_⟩
  · have key : ∀ h, ∑ a, ψ (A b a) * ψ (ρ (Mx a h)) = (Pi.single b (1 : K) : HIx Dw (psiSet H) → K) h := fun h => by
      have e := congrArg (fun N => ψ (N b h)) hAM
      simp only [Matrix.mul_apply, Matrix.map_apply, hMxM, Matrix.of_apply, map_sum, map_mul] at e
      rw [e, Matrix.one_apply, Pi.single_apply]
      by_cases hh : h = b
      · subst hh; simp
      · simp [hh, Ne.symm hh]
    convert hwKS using 1
    funext h
    rw [Finset.sum_apply, ← key h]
    rfl
  · rw [← hwpt, ← hτ']
    simp only [← Category.assoc, spMap_comp']
