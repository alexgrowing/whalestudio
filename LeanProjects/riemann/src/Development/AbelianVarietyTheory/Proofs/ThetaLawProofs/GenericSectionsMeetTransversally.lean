import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SectionsSeparatePointsAndTangents
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DetNeZeroOfGenericLinearFormsVanish
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.FiniteOfIsClosedSingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrdegEqOfLocallyIsStandardSmoothOfRelativeDimens
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.UnifPreGenericFibreSurjectiveAppTopAndIsIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyKa.GenericZeros
open EtBaseChange

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem trdeg_adjoin_range_le {k K B : Type} [Field k] [Field K] [Algebra k K] [CommRing B] [Algebra k B]
    (ψ : B →ₐ[k] K) : Algebra.trdeg k (IntermediateField.adjoin k (Set.range ψ)) ≤ Algebra.trdeg k B := by
  rw [trdeg_eq_of_isAlgebraic_top k (Algebra.adjoin k (Set.range ψ)) (IntermediateField.adjoin k (Set.range ψ))]
  refine trdeg_le_of_surjective (ψ.codRestrict _ fun b => Algebra.subset_adjoin ⟨b, rfl⟩) ?_
  rintro ⟨y, hy⟩
  have hle : Algebra.adjoin k (Set.range ψ) ≤ ψ.range := Algebra.adjoin_le fun _ h => h
  obtain ⟨b, hb⟩ := hle hy
  exact ⟨b, Subtype.ext hb⟩

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_field_of_definition {k K : Type} [Field k] [Field K] [Algebra k K] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Sp k) (g : ℕ) (hf : SmoothOfRelativeDimension g f) (p : Sp K ⟶ X)
    (hp : p ≫ f = spMap (algebraMap k K)) :
    ∃ F : IntermediateField k K, Algebra.trdeg k F ≤ g ∧ ∃ q : Sp F ⟶ X,
      q ≫ f = spMap (algebraMap k F) ∧ spMap (algebraMap F K) ≫ q = p := by
  obtain ⟨R, j, hj, hmem, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := p (IsLocalRing.closedPoint K)) (U := ⊤) trivial
  have hr : Set.range p ⊆ Set.range j := by
    rintro _ ⟨y, rfl⟩
    obtain rfl : y = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    exact hmem
  let ψ₀ : R ⟶ CommRingCat.of K := Spec.preimage (IsOpenImmersion.lift j p hr)
  have h₀ : Spec.map ψ₀ ≫ j = p := by
    rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  let a : CommRingCat.of k ⟶ R := Spec.preimage (j ≫ f)
  have ha : j ≫ f = Spec.map a := (Spec.map_preimage _).symm
  let _ : Algebra k R := a.hom.toAlgebra
  have hc : a ≫ ψ₀ = CommRingCat.ofHom (algebraMap k K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← ha, ← Category.assoc, h₀, hp]
  let ψ : R →ₐ[k] K := { ψ₀.hom with commutes' := fun r => congrArg (fun q => q.hom r) hc }
  have : Nontrivial R := ψ₀.hom.domain_nontrivial
  have htr : Algebra.trdeg k R = g := trdeg_eq_of_smoothOfRelativeDimension k X f g hf R j hj ha
  let F := IntermediateField.adjoin k (Set.range ψ)
  let ψ' : R →+* F := ψ₀.hom.codRestrict F fun b => IntermediateField.subset_adjoin _ _ ⟨b, rfl⟩
  refine ⟨F, htr ▸ trdeg_adjoin_range_le ψ, spMap ψ' ≫ j, ?_, ?_⟩
  · have e : ψ'.comp a.hom = algebraMap k F := RingHom.ext fun r => Subtype.ext (ψ.commutes r)
    rw [Category.assoc, ← e, ← spMap_comp]
    exact congrArg (spMap ψ' ≫ ·) ha
  · rw [← Category.assoc, spMap_comp]
    exact h₀

theorem valT_cst {R T : Type} [CommRing R] [CommRing T] {X : Scheme.{0}} (f : X ⟶ Sp R) (p : Sp T ⟶ X) (a : R →+* T)
    (hp : p ≫ f = spMap a) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) (c : R) : valT p U (cst f U c) = a c := by
  have h0 : valT p U (cst f U c) =
      valT p U ((f.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) := rfl
  refine h0.trans ((valT_appLE p f (U := ⊤) le_top h _).trans ?_)
  rw [hp, ← Category.comp_id (spMap a), valT_spMap a (𝟙 (Sp R)) (U := ⊤) le_top, valT_eq _ _ le_top]
  have e3 : Scheme.Hom.appLE (𝟙 (Sp R)) ⊤ ⊤ le_top = 𝟙 _ := by
    rw [← Scheme.Hom.id_appTop]; exact Scheme.Hom.appLE_eq_app _
  unfold valH
  erw [e3]
  simp

theorem exists_translate {k F K : Type} [CommRing k] [CommRing F] [CommRing K] (a : k →+* F) (e : F →+* K)
    {G : Over (Sp k)} [GrpObj G] {G' : Over (Sp K)} [GrpObj G'] {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G (spMap (e.comp a)) φ) (E : DualNumber k →+* DualNumber K)
    (h₁ : ∀ r, E (algebraMap k _ r) = algebraMap K _ (e (a r))) (h₂ : E DualNumber.eps = DualNumber.eps)
    (z' : 𝟙_ (Over (Sp K)) ⟶ G') (q : Sp F ⟶ G.left) (hq : q ≫ G.hom = spMap a) (hz : spMap e ≫ q = z'.left ≫ φ)
    (v : epsR k ⟶ G) (v' : epsR K ⟶ G') (hv : v'.left ≫ φ = spMap E ≫ v.left) :
    ∃ r : Sp (DualNumber F) ⟶ G.left,
      ((toUnit (epsR K) ≫ z') * v').left ≫ φ = spMap (Chart.dualMapR e) ≫ r := by
  have hE : (Chart.dualMapR e).comp (Chart.dualMapR a) = E := by
    refine RingHom.ext fun t => ?_
    have : t = algebraMap k _ t.fst + algebraMap k _ t.snd * DualNumber.eps := by
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
    conv_rhs => rw [this, map_add, map_mul, h₁, h₁, h₂]
    ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have c₁ : (Chart.dualMapR e).comp (algebraMap F (DualNumber F)) = (algebraMap K (DualNumber K)).comp e := by
    ext r <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have c₂ : (Chart.dualMapR a).comp (algebraMap k (DualNumber k)) = (algebraMap F (DualNumber F)).comp a := by
    ext r <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have s₁ : spMap (Chart.dualMapR e) ≫ spMap (algebraMap F (DualNumber F)) =
      spMap (algebraMap K (DualNumber K)) ≫ spMap e := by rw [spMap_comp, spMap_comp, c₁]
  have s₂ : spMap (Chart.dualMapR a) ≫ spMap (algebraMap k (DualNumber k)) =
      spMap (algebraMap F (DualNumber F)) ≫ spMap a := by rw [spMap_comp, spMap_comp, c₂]
  let T : Over (Sp k) := Over.mk (spMap (algebraMap F (DualNumber F)) ≫ spMap a)
  let qT : T ⟶ G := Over.homMk (spMap (algebraMap F (DualNumber F)) ≫ q)
    ((Category.assoc _ _ _).trans (congrArg (spMap (algebraMap F (DualNumber F)) ≫ ·) hq))
  have hvw : v.left ≫ G.hom = spMap (algebraMap k (DualNumber k)) := Over.w v
  let vT : T ⟶ G := Over.homMk (spMap (Chart.dualMapR a) ≫ v.left)
    ((Category.assoc _ _ _).trans ((congrArg (spMap (Chart.dualMapR a) ≫ ·) hvw).trans s₂))
  have hD : spMap (Chart.dualMapR e) ≫ spMap (algebraMap F (DualNumber F)) ≫ spMap a =
      spMap (algebraMap K (DualNumber K)) ≫ spMap (e.comp a) := by
    rw [← Category.assoc, s₁, Category.assoc, spMap_comp a e]
  let D : Over.mk ((epsR K).hom ≫ spMap (e.comp a)) ⟶ T := Over.homMk (spMap (Chart.dualMapR e)) hD
  have e₁ : (D ≫ qT).left = (toUnit (epsR K) ≫ z').left ≫ φ := by
    show spMap (Chart.dualMapR e) ≫ spMap (algebraMap F (DualNumber F)) ≫ q =
      (spMap (algebraMap K (DualNumber K)) ≫ z'.left) ≫ φ
    rw [← Category.assoc, s₁, Category.assoc, hz]
    exact (Category.assoc _ _ _).symm
  have e₂ : (D ≫ vT).left = v'.left ≫ φ := by
    refine Eq.trans ?_ hv.symm
    show spMap (Chart.dualMapR e) ≫ spMap (Chart.dualMapR a) ≫ v.left = _
    rw [← Category.assoc, spMap_comp, hE]
  refine ⟨(qT * vT).left, ?_⟩
  rw [← h.2 (epsR K) _ _ (D ≫ qT) (D ≫ vT) e₁ e₂, ← MonObj.comp_mul]
  rfl

theorem sum_valT_via {k K T : Type} [CommRing k] [CommRing K] [CommRing T] {x : KeyIn k} {x' : KeyIn K}
    {φ : x'.P.A.left ⟶ x.P.A.left} {w : LB.Iso x'.P.L (x.P.L.pull φ)} {n N : ℕ} {b : Fin N → RR x n}
    {b' : Fin N → RR x' n} (hb : ∀ j, SecVia x' x φ w (b' j) (b j)) (p : Sp T ⟶ x'.P.A.left) (a : K →+* T)
    (hp : p ≫ x'.P.A.hom = spMap a) (c : x.P.L.ι) (c' : x'.P.L.ι) (h : ⊤ ≤ (p ≫ φ) ⁻¹ᵁ x.P.L.U c)
    (h' : ⊤ ≤ p ⁻¹ᵁ x'.P.L.U c') (t : RR x' n) (m : Fin N → K) (ht : Coords x' b' m t.f) :
    ∑ j, a (m j) * valT (p ≫ φ) (x.P.L.U c) ((b j).f c) =
      valT p ((x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c') (w.s (fun _ => c, c')).val ^ n *
        valT p (x'.P.L.U c') (t.f c') := by
  have e : valT p (x'.P.L.U c') (t.f c') = ∑ j, a (m j) * valT p (x'.P.L.U c') ((b' j).f c') := by
    refine (congrArg (valT p (x'.P.L.U c')) (ht c')).trans ((valT_eq p _ h' _).trans ((map_sum _ _ _).trans ?_))
    refine Finset.sum_congr rfl fun j _ => (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (valT_eq p _ h' _).symm)
    exact (valT_eq p _ h' _).symm.trans (valT_cst _ p a hp _ h' _)
  rw [e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [valT_via (hb j) p c c' h h', mul_left_comm]

theorem exists_jets {k K : Type} [Field k] [Field K] [Algebra k K] {x : KeyIn k} {x' : KeyIn K}
    {φ : x'.P.A.left ⟶ x.P.A.left} {w : LB.Iso x'.P.L (x.P.L.pull φ)} (H : KeyVia x' x (algebraMap k K) φ w)
    {n N : ℕ} {b : Fin N → RR x n} {b' : Fin N → RR x' n} (hb : ∀ j, SecVia x' x φ w (b' j) (b j))
    (z : Pt x') (c' : x'.P.L.ι) (h' : ⊤ ≤ z.left ⁻¹ᵁ x'.P.L.U c') :
    ∃ (F : IntermediateField k K) (e : Fin N → K) (D : Fin x'.P.g → Fin N → K) (u : K), u ≠ 0 ∧
      Algebra.trdeg k F ≤ x'.P.g ∧ (∀ j, e j ∈ F) ∧ (∀ a j, D a j ∈ F) ∧
      ∀ (t : RR x' n) (m : Fin N → K), Coords x' b' m t.f →
        ∑ j, m j * e j = u * valT (T := K) z.left (x'.P.L.U c') (t.f c') ∧
        (valT (T := K) z.left (x'.P.L.U c') (t.f c') = 0 → ∀ a, ∑ j, m j * D a j = u * TrivSqZeroExt.snd
          (valT (T := DualNumber K) ((toUnit (epsR K) ≫ z) * x'.v a).left (x'.P.L.U c') (t.f c'))) := by
  obtain ⟨-, hg, E, hp, -, -, -, hE₁, hE₂, hv⟩ := H
  have : IsIntegral x.P.A.left := isIntegral_left_of_isAbelianScheme_field x.P.A x.P.isAb
  let z₀ : Sp K ⟶ x'.P.A.left := z.left
  have hz : z₀ ≫ x'.P.A.hom = 𝟙 (Sp K) := Over.w z
  have hz' : z₀ ≫ x'.P.A.hom = spMap (RingHom.id K) := hz.trans (Spec.map_id _).symm
  obtain ⟨F, hF, q, hq, hzq⟩ := exists_field_of_definition x.P.A.hom x.P.g x.P.smoothDim (z₀ ≫ φ) (by
    rw [Category.assoc, hp.1.w, ← Category.assoc, hz, Category.id_comp])
  obtain ⟨c, hc⟩ := exists_chart x.P.isLB (q (IsLocalRing.closedPoint F))
  have hqc : ⊤ ≤ q ⁻¹ᵁ x.P.L.U c := fun p _ => by
    obtain rfl : p = IsLocalRing.closedPoint F := Subsingleton.elim _ _
    exact hc
  have hφ : ⊤ ≤ (z₀ ≫ φ) ⁻¹ᵁ x.P.L.U c := fun p _ => by
    rw [← hzq]
    exact hqc (show spMap (algebraMap F K) p ∈ ⊤ from trivial)
  have hW := le_inf_pull (T := K) z₀ c c' hφ h'
  let p : Fin x'.P.g → (Sp (DualNumber K) ⟶ x'.P.A.left) := fun a => ((toUnit (epsR K) ≫ z) * x'.v a).left
  have hpw : ∀ a, p a ≫ x'.P.A.hom = spMap (algebraMap K (DualNumber K)) := fun a =>
    Over.w ((toUnit (epsR K) ≫ z) * x'.v a)
  have l₂ : ∀ a, ⊤ ≤ p a ⁻¹ᵁ x'.P.L.U c' := fun a => translate_le z (x'.v a) (x'.basis.1 _) h'
  have l₃ : ∀ a, ⊤ ≤ (p a ≫ φ) ⁻¹ᵁ x.P.L.U c := fun a =>
    translate_le z (x'.v a) (x'.basis.1 _) (U := φ ⁻¹ᵁ x.P.L.U c) hφ
  let u := valT (T := K) z₀ ((x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c') (w.s (fun _ => c, c')).val
  have hu : IsUnit u := by
    have := (w.s (fun _ => c, c')).isUnit.map (valH (T := K) z₀ _ hW)
    exact (congrArg IsUnit (valT_eq (T := K) z₀ _ hW _)).mpr this
  refine ⟨F, fun j => valT (z₀ ≫ φ) (x.P.L.U c) ((b j).f c),
    fun a j => (valT (p a ≫ φ) (x.P.L.U c) ((b j).f c)).snd, u ^ n, pow_ne_zero _ hu.ne_zero, hg ▸ hF,
    fun j => ?_, fun a j => ?_, fun t m ht => ⟨?_, fun h0 a => ?_⟩⟩
  · show valT (z₀ ≫ φ) _ _ ∈ F
    rw [← hzq]
    exact (congrArg (· ∈ F) (valT_spMap _ q hqc _)).mpr (Subtype.property _)
  · have hp' : IsGrpPullback x'.P.A x.P.A (spMap ((algebraMap F K).comp (algebraMap k F))) φ := by
      rw [← IsScalarTower.algebraMap_eq]; exact hp
    obtain ⟨r, hr⟩ := exists_translate (algebraMap k F) (algebraMap F K) hp' E hE₁ hE₂ z q hq hzq _ _ (hv a)
    have hr' : p a ≫ φ = spMap (Chart.dualMapR (algebraMap F K)) ≫ r := hr
    have hrc : ⊤ ≤ r ⁻¹ᵁ x.P.L.U c := fun y _ => by
      have h₁ := l₃ a (show IsLocalRing.closedPoint (DualNumber K) ∈ ⊤ from trivial)
      rw [hr'] at h₁
      have hsub : ∀ y y' : Sp (DualNumber F), y = y' := fun y y' => by
        obtain ⟨y, rfl⟩ := fst_surjective F y
        obtain ⟨y', rfl⟩ := fst_surjective F y'
        rw [Subsingleton.elim y y']
      rw [hsub y (spMap (Chart.dualMapR (algebraMap F K)) (IsLocalRing.closedPoint (DualNumber K)))]
      exact h₁
    show (valT (p a ≫ φ) _ _).snd ∈ F
    rw [hr']
    refine (congrArg (fun y : DualNumber K => y.snd ∈ F) (valT_spMap _ r hrc _)).mpr ?_
    simp [Chart.dualMapR]
  · exact sum_valT_via hb z₀ (RingHom.id K) hz' c c' hφ h' t m ht
  · have e := congrArg TrivSqZeroExt.snd (sum_valT_via hb (p a) _ (hpw a) c c' (l₃ a) (l₂ a) t m ht)
    rw [snd_pow_mul _ _ _ ((fst_valT_translate z (x'.v a) (x'.basis.1 _) h' _).trans h0)] at e
    refine Eq.trans ?_ (e.trans (congrArg (· ^ n * _) (fst_valT_translate z (x'.v a) (x'.basis.1 _) hW _)))
    rw [TrivSqZeroExt.snd_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_etZ_of_algebraicIndependent : Out.Laws → ∀ (k K : Type) [Field k] [Field K] [IsAlgClosed K] [Algebra k K] (x : KeyIn k) (x' : KeyIn K) φ w (n : ℕ) (b : Fin (n ^ x.P.g) → RR x n) (b' : Fin (n ^ x.P.g) → RR x' n) (T : Fin x'.P.g × Fin (n ^ x.P.g) → K) (s : Fin x'.P.g → RR x' n), 4 ≤ n → KeyVia x' x (algebraMap k K) φ w → IsBasis x b → (∀ j, SecVia x' x φ w (b' j) (b j)) → AlgebraicIndependent k T → (∀ i, Coords x' b' (fun j => T (i, j)) (s i).f) → ∃ (d : ℕ) (z : Fin d → Pt x') (ch : Fin d → x'.P.L.ι), EtZ x' s z ch := by
  intro hL k K _ _ _ _ x x' φ w n b b' T s hn H hb hb' hT hs
  have hB : IsBasis x' b' := (GlobalTheory.KeyBasis.main hL k x n (by omega)).2 b hb K _ x' φ w b' H hb'
  refine GlobalTheory.KeyKa.exists_etZ_of_jac_ne_zero K x' n s fun z c hc h0 => ?_
  obtain ⟨F, e, D, u, hu, hF, he, hD, hval⟩ := exists_jets H hb' z c hc
  have hdet : ∀ (t : Fin x'.P.g → RR x' n) (m : Fin x'.P.g → Fin (n ^ x.P.g) → K),
      (∀ i, Coords x' b' (m i) (t i).f) → (∀ i, valT (T := K) z.left (x'.P.L.U c) ((t i).f c) = 0) →
      (∀ i, ∑ j, m i j * e j = 0) ∧
        (Matrix.of fun i a => ∑ j, m i j * D a j).det = u ^ Fintype.card (Fin x'.P.g) * jac x' t z c := by
    intro t m hm ht
    refine ⟨fun i => by rw [(hval _ _ (hm i)).1, ht i, mul_zero], Eq.trans ?_ (Matrix.det_smul _ _)⟩
    congr 1
    ext i a
    exact (hval _ _ (hm i)).2 (ht i) a
  obtain ⟨⟨s₀, hs₀⟩, t, ht, hj⟩ := (GlobalTheory.KeyKa.sections_separate_points_and_tangents hL K x' n hn).1 z c hc
  choose m hm _ using hB
  have h₁ := hdet s (fun i j => T (i, j)) hs h0
  have h₂ := hdet t (fun i => m (t i)) (fun i => hm _) ht
  have h₃ := GlobalTheory.det_ne_zero_of_generic_linear_forms_vanish k K F _ _ T e D hT hF he hD ?_
    ⟨_, h₂.1, h₂.2 ▸ mul_ne_zero (pow_ne_zero _ hu) hj⟩ h₁.1
  · exact right_ne_zero_of_mul (h₁.2 ▸ h₃)
  · by_contra hne
    push Not at hne
    have := (hval _ _ (hm s₀)).1
    simp only [hne, mul_zero, Finset.sum_const_zero] at this
    exact mul_ne_zero hu hs₀ this.symm

end GlobalTheory.KeyKa.GenericZeros
end
