import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSIffKsRel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueModificationLiftSqZeroFlagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJacobianEvalRingPointNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroTangentOfJacobianDerivsVanishStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalFirstOrderDeformationStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap b ≫ spMap a = spMap (b.comp a) := (Spec.map_comp _ _).symm

theorem exists_datum {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c}
    (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))
    (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (psiSet H) y)
    (i : M.K.bundle.ι) (k : X.F.J) (K : Type) [Field K] (z : Sp K ⟶ M.X) (hz : ⊤ ≤ z ⁻¹ᵁ ksOpen M i k) :
    ∃ (_ : Algebra c.F K) (P Q : FrPt Xo c K) (t : Ix Dw → Kˣ) (v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K))
      (zv : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)) (O : M.X.Opens) (hO : O ≤ M.K.bundle.U i)
      (g : Fin (dimFlag Dw) → Γ(M.X, O)) (hz : ⊤ ≤ z ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O)
      (hk : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k),
      X.F.ChartFr k (z ≫ toFlag M) hk Q ∧ FrBor t Q P ∧ IsTanFrame (psiSet H) P v ∧
      (∀ b, zv b ≫ toFlag M = X.ptY (v b)) ∧
      (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det ≠ 0 ∧
      (∏ ix, t ix ^ exOf Dw (FlagTan.kap Dw) 0 ix).val * evalPt z O hz (M.K.jacobian i hO g) ≠ 0 := by
  have ho : ⊤ ≤ z ⁻¹ᵁ M.off := fun s hs => (hz hs).1
  have hi : ⊤ ≤ z ⁻¹ᵁ M.K.bundle.U i := fun s hs => (hz hs).2.1
  have hk : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k := fun s hs =>
    (((common₀ X Z).pull M.σ).mem _ k _).1 (hz hs).2.2
  have hfo : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ flagOpen X := fun s hs => by
    have := ho hs
    rw [M.off_eq] at this
    exact this
  obtain ⟨alg, hQex⟩ := exists_chartFr (z ≫ toFlag M) hfo
  obtain ⟨Q, hQ⟩ := hQex k hk
  have hzQ : z ≫ toFlag M = X.ptY Q := FlagCover.eq_ptY hQ.lies
  obtain ⟨W, v, hWP, hWv, hv, hinj⟩ := GlobalTheory.T.exists_universal_first_order_deformation X K Q (hKS K Q)
  have hW0 : spMap (TrivSqZeroExt.fstHom K K (TIx Dw (psiSet H) → K)).toRingHom ≫ X.ptY W = z ≫ toFlag M := by
    have e : (TrivSqZeroExt.fstHom K K (TIx Dw (psiSet H) → K)).toRingHom =
        (TrivSqZeroExt.fstHom c.F K (TIx Dw (psiSet H) → K)).toRingHom := RingHom.ext fun _ => rfl
    rw [hzQ, e]; exact X.ptY_frMap hWP
  obtain ⟨W', hW'1, hW'2, hW'3⟩ := GlobalTheory.T.existsUnique_modification_lift_sqZero_flag M z ho (X.ptY W) hW0
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_jacobian_evalRingPoint_ne_zero M.K i z hi
  have hW'O := hW'3 _ hi
  have hpre : ∀ {R : Type} [CommRing R] (φ : TrivSqZeroExt K (TIx Dw (psiSet H) → K) →+* R),
      ⊤ ≤ (spMap φ ≫ W') ⁻¹ᵁ M.K.bundle.U i := fun φ s _ => hW'O (Set.mem_univ ((spMap φ).base s))
  let zv : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X) := fun b =>
    spMap (GlobalTheory.FlagTan.dir c (Pi.single b (1 : K))).toRingHom ≫ W'
  have hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ M.K.bundle.U i := fun b => hpre _
  have hent : ∀ a b, (evalPt (zv b) _ (hzv b) (g a)).snd = (evalPt W' _ hW'O (g a)).snd b := fun a b => by
    simp only [zv]
    rw [evalPt_spMap_comp _ W' _ hW'O]
    simp [Pi.single_apply]
  have hdet : (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) _ (hzv _) (g a)).snd).det ≠ 0 := by
    intro hd
    obtain ⟨m, hm0, hm⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    let m' : TIx Dw (psiSet H) → K := fun b => m ((tanOrd Dw).symm b)
    obtain ⟨u, hu⟩ := GlobalTheory.FlagTan.exists_frMap (GlobalTheory.FlagTan.dir c m') W
    obtain ⟨P₀, hP₀⟩ := GlobalTheory.FlagTan.exists_frMap (GlobalTheory.FlagTan.cst c K) Q
    have key := GlobalTheory.T.eq_zero_tangent_of_jacobian_derivs_vanish M.K i z hi g hg (spMap (GlobalTheory.FlagTan.dir c m').toRingHom ≫ W') (hpre _) ?_ ?_ ?_
    · apply hm0
      have hm'0 : m' = 0 := by
        refine hinj m' u P₀ hu hP₀ ?_
        rw [← X.ptY_frMap hu, ← X.ptY_frMap hP₀, ← hW'1, ← hzQ, ← Category.assoc, key, Category.assoc]
        rfl
      funext b
      simpa [m'] using congrFun hm'0 (tanOrd Dw b)
    · rw [← Category.assoc, spectrumMap_comp, ← hW'2]
      congr 2
      ext x <;> simp
    · have a1 : W' ≫ M.σ ≫ inc₀ X Z ≫ flagStr X = spMap (algebraMap c.F _) := by
        rw [← Category.assoc M.σ, ← Category.assoc W']
        exact (congrArg (· ≫ flagStr X) hW'1).trans (ptY_str X W)
      have a2 : z ≫ M.σ ≫ inc₀ X Z ≫ flagStr X = spMap (algebraMap c.F K) := by
        rw [← Category.assoc M.σ, ← Category.assoc z]
        exact (congrArg (· ≫ flagStr X) hzQ).trans (ptY_str X Q)
      change (spMap _ ≫ W') ≫ M.σ ≫ inc₀ X Z ≫ flagStr X = spMap _ ≫ z ≫ M.σ ≫ inc₀ X Z ≫ flagStr X
      rw [Category.assoc, a1, a2, spectrumMap_comp, spectrumMap_comp]
      refine congrArg spMap (RingHom.ext fun x => ?_)
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
      rfl
    · intro a
      rw [evalPt_spMap_comp _ W' _ hW'O]
      have := congrFun hm a
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, hent] at this
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, GlobalTheory.FlagTan.snd_dir]
      rw [← (tanOrd Dw).sum_comp]
      simpa [m'] using this
  refine ⟨alg, Q, Q, 1, v, zv, _, le_rfl, g, hi, hzv, hk, hQ,
    (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c K).1 Q, hv, fun b => ?_, hdet, ?_⟩
  · simp only [zv]
    rw [Category.assoc, hW'1]
    exact X.ptY_frMap (hWv b)
  · simpa using hg

theorem ksRel_unique_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y}
    {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)),
    (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) →
    ∀ (i : M.K.bundle.ι) (k : X.F.J) (K : Type) [Field K] (z : Sp K ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ ksOpen M i k →
      (∀ x y : K, KSRel M i k z x → KSRel M i k z y → x = y) ∧ ∀ x : K, KSRel M i k z x → x ≠ 0 := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS i k K _ z hz
  obtain ⟨alg, P, Q, t, v, zv, O, hO, g, hz', hzv, hk, hQ, ht, hv, hl, hd, hr⟩ := exists_datum M hKS i k K z hz
  refine ⟨fun x y hx hy => mul_right_cancel₀ hd ((hx P Q t v zv O hO g hz' hzv hk hQ ht hv hl).trans
    (hy P Q t v zv O hO g hz' hzv hk hQ ht hv hl).symm), fun x hx h0 => hr ?_⟩
  have := hx P Q t v zv O hO g hz' hzv hk hQ ht hv hl
  rw [h0, zero_mul] at this
  exact this.symm

end GlobalTheory.CompHS
