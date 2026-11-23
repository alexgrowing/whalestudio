import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FibreIff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

namespace GlobalTheory.FlatRow.EigLocal

open GlobalTheory.Serre

theorem hom_ext_of_loc {R : Type} [CommRing R] {X : Scheme.{0}} {f g : Sp R ⟶ X}
    (h : ∀ (p : Ideal R) [p.IsPrime], spMap (algebraMap R (Localization.AtPrime p)) ≫ f =
      spMap (algebraMap R (Localization.AtPrime p)) ≫ g) : f = g := by
  let q : ∀ p : PrimeSpectrum R, Sp (Localization.AtPrime p.asIdeal) ⟶ Sp R := fun p => spMap (algebraMap R _)
  have : ∀ p, Flat (q p) := fun p => by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ p.asIdeal.primeCompl)
  have : Surjective (Sigma.desc q) := Surjective.sigmaDesc_of_union_range_eq_univ (by
    refine Set.eq_univ_of_forall fun p : PrimeSpectrum R => Set.mem_iUnion.2 ⟨p, IsLocalRing.closedPoint _, ?_⟩
    exact PrimeSpectrum.ext (Localization.AtPrime.under_maximalIdeal (I := p.asIdeal)))
  have : Epi (Sigma.desc q) := Flat.epi_of_flat_of_surjective _
  rw [← cancel_epi (Sigma.desc q)]
  refine Sigma.hom_ext _ _ fun p => ?_
  rw [Sigma.ι_desc_assoc, Sigma.ι_desc_assoc]
  exact h p.asIdeal

section Res

variable {R R' O : Type} [CommRing R] [CommRing R'] [CommRing O] {f : R →+* R'} {A : Over (Sp R)} {A' : Over (Sp R')}
  [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}

theorem fst_dual (f : R →+* R') :
    spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (Chart.dualMapR f) =
      spMap f ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
  congr 1
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem scale_dual (f : R →+* R') (c : R) :
    spMap (epsScaleR (f c)) ≫ spMap (Chart.dualMapR f) = spMap (Chart.dualMapR f) ≫ spMap (epsScaleR c) := by
  refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
  congr 1
  ext a <;> simp [Chart.dualMapR, epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem isVecOver_mul (h : IsGrpPullback A' A (spMap f) φ) {v w : epsR R ⟶ A} {v' w' : epsR R' ⟶ A'}
    (hv : IsVecOver f φ v v') (hw : IsVecOver f φ w w') : IsVecOver f φ (v * w) (v' * w') := by
  let k : Over.mk ((epsR R').hom ≫ spMap f) ⟶ epsR R := Over.homMk (spMap (Chart.dualMapR f)) (by
    refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
    congr 1
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
  have e := h.2 (epsR R') v' w' (k ≫ v) (k ≫ w) hv.symm hw.symm
  rw [← MonObj.comp_mul] at e
  exact e.symm

variable [IsCommMonObj A] [IsCommMonObj A']

theorem exists_res (h : IsGrpPullback A' A (spMap f) φ) (a : OAct O A) (a' : OAct O A')
    (ha : ∀ x, (a'.act x).left ≫ φ = φ ≫ (a.act x).left) :
    ∃ ρ : Lie a →ₛₗ[f] Lie a', (∀ w, IsVecOver f φ w.hom (ρ w).hom) ∧ ∀ (x : O) w, ρ (x • w) = x • ρ w := by
  choose r hr hu using fun w : Lie a => existsUnique_isVecOver h.1 w.hom
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Lie a → Lie a', ∀ w, (ρ w).hom = r w :=
    ⟨fun w => Lie.mk a' (r w) ((hr w).isTangent h w.isTangent), fun _ => rfl⟩
  have key : ∀ (w : Lie a) (w' : Lie a'), IsVecOver f φ w.hom w'.hom → ρ w = w' := fun w w' e =>
    Lie.ext ((hρ w).trans (hu w _ e).symm)
  replace hr : ∀ w, IsVecOver f φ w.hom (ρ w).hom := fun w => hρ w ▸ hr w
  have h₁ : ∀ v w, ρ (v + w) = ρ v + ρ w := fun v w => key _ _ (by
    rw [Lie.hom_add, Lie.hom_add]; exact isVecOver_mul h (hr v) (hr w))
  have h₂ : ∀ (c : R) w, ρ (c • w) = f c • ρ w := fun c w => key _ _ (by
    have e := hr w
    unfold IsVecOver at e ⊢
    rw [Lie.hom_smul_left, Lie.hom_smul_left]
    exact (Category.assoc _ _ _).trans ((congrArg (spMap (epsScaleR (f c)) ≫ ·) e).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ w.hom.left) (scale_dual f c)).trans (Category.assoc _ _ _)))))
  have h₃ : ∀ (x : O) w, ρ (x • w) = x • ρ w := fun x w => key _ _ (by
    have e := hr w
    unfold IsVecOver at e ⊢
    rw [Lie.hom_act_smul, Lie.hom_act_smul, Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, e]
    exact Category.assoc _ _ _)
  exact ⟨⟨⟨ρ, h₁⟩, h₂⟩, hr, h₃⟩

theorem isEigVec_iff (a : OAct O A) (χ : O →+* R) (w : Lie a) :
    EigenvectorLieDegree.IsEigVec a χ w.hom ↔ ∀ x, x • w = χ x • w :=
  ⟨fun h x => Lie.ext (Over.OverMorphism.ext (h.2 x)),
    fun h => ⟨w.isTangent, fun x => congrArg (fun u : Lie a => u.hom.left) (h x)⟩⟩

theorem isEigBasis_iff (a : OAct O A) (χ : O →+* R) {m : ℕ} (v : Fin m → Lie a) :
    EigenvectorLieDegree.IsEigBasis a χ (fun i => (v i).hom) ↔ (∀ i x, x • v i = χ x • v i) ∧
      ∀ w : Lie a, (∀ x, x • w = χ x • w) → ∃! c : Fin m → R, w = ∑ i, c i • v i := by
  refine and_congr (forall_congr' fun i => isEigVec_iff a χ _) ⟨fun h w hw => ?_, fun h w hw => ?_⟩
  · exact (existsUnique_congr fun c => (Lie.isLieComb_iff c v _).trans Lie.ext_iff.symm).1
      (h w.hom ((isEigVec_iff a χ w).2 hw))
  · exact (existsUnique_congr fun c => (Lie.isLieComb_iff c v _).trans (Lie.ext_iff (v := Lie.mk a w hw.1)).symm).2
      (h (Lie.mk a w hw.1) ((isEigVec_iff a χ _).1 hw))

end Res

theorem exists_smul_eq_zero {R O : Type} [CommRing R] [CommRing O] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] (a : OAct O A) (p : Ideal R) [p.IsPrime] (w : Lie a)
    (h : spMap (Chart.dualMapR (algebraMap R (Localization.AtPrime p))) ≫ w.hom.left =
      spMap (Chart.dualMapR (algebraMap R (Localization.AtPrime p))) ≫ (1 : epsR R ⟶ A).left) :
    ∃ q ∉ p, q • w = 0 := by
  have : ∀ s : R, Smooth (Chart.Gs A s).hom := fun s => show Smooth (pullback.snd A.hom _) from inferInstance
  obtain ⟨q, hq, hs⟩ := Chart.tan_prime_uniq (G := A) p (w := w.hom) ((Chart.isTan_iff _).2 w.isTangent) (by
    rw [← MonObj.comp_one (Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.AtPrime p))))]
    exact Over.OverMorphism.ext h)
  exact ⟨q, hq, Lie.ext (Over.OverMorphism.ext (congrArg (fun u => u.left) hs))⟩

theorem eq_zero_of_loc {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {w : M}
    (h : ∀ (p : Ideal R) [p.IsPrime], ∃ q ∉ p, q • w = 0) : w = 0 := by
  have : (Submodule.span R {w}).annihilator = ⊤ := by
    by_contra hne
    obtain ⟨p, hp, hI⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨q, hq, e⟩ := h p
    exact hq (hI ((Submodule.mem_annihilator_span_singleton _ _).2 e))
  have h1 : (1 : R) ∈ (Submodule.span R {w}).annihilator := this ▸ Submodule.mem_top
  exact (one_smul R _).symm.trans ((Submodule.mem_annihilator_span_singleton _ _).1 h1)

theorem eigBasis_of_loc {R O M : Type} [CommRing R] [AddCommGroup M] [Module R M] [SMul O M] (χ : O → R) {m : ℕ}
    (u : Fin m → M)
    (loc : ∀ (p : Ideal R) [p.IsPrime], ∃ (M' : Type) (_ : AddCommGroup M') (_ : Module (Localization.AtPrime p) M')
      (_ : SMul O M') (ρ : M →ₛₗ[algebraMap R (Localization.AtPrime p)] M'),
      (∀ (x : O) w, ρ (x • w) = x • ρ w) ∧ (∀ w, ρ w = 0 → ∃ q ∉ p, q • w = 0) ∧
      (∀ i (x : O), x • ρ (u i) = algebraMap R (Localization.AtPrime p) (χ x) • ρ (u i)) ∧
      ∀ w : M', (∀ x : O, x • w = algebraMap R (Localization.AtPrime p) (χ x) • w) →
        ∃! c : Fin m → Localization.AtPrime p, w = ∑ i, c i • ρ (u i)) :
    (∀ i (x : O), x • u i = χ x • u i) ∧
      ∀ w : M, (∀ x : O, x • w = χ x • w) → ∃! c : Fin m → R, w = ∑ i, c i • u i := by
  refine ⟨fun i x => sub_eq_zero.1 (eq_zero_of_loc (R := R) fun p _ => ?_), fun w hw => ?_⟩
  · obtain ⟨M', _, _, _, ρ, h₁, h₂, h₃, -⟩ := loc p
    exact h₂ _ (by rw [map_sub, h₁, h₃, map_smulₛₗ, sub_self])
  have ex : w ∈ Submodule.span R (Set.range u) := by
    rw [← Submodule.Quotient.mk_eq_zero]
    refine eq_zero_of_loc (R := R) fun p _ => ?_
    obtain ⟨M', _, _, _, ρ, h₁, h₂, -, h₄⟩ := loc p
    obtain ⟨c, hc, -⟩ := h₄ (ρ w) fun x => by rw [← h₁, hw, map_smulₛₗ]
    obtain ⟨⟨q, hq⟩, hqi⟩ := IsLocalization.exist_integer_multiples p.primeCompl (Finset.univ : Finset (Fin m)) c
    choose b hb using fun i => hqi i (Finset.mem_univ _)
    obtain ⟨r, hr, e⟩ := h₂ (q • w - ∑ i, b i • u i) (by
      rw [map_sub, map_smulₛₗ, hc, map_sum, Finset.smul_sum, sub_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smulₛₗ, hb, smul_smul, Algebra.smul_def])
    refine ⟨r * q, p.primeCompl.mul_mem hr hq, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mul_smul, sub_eq_zero.1 ((smul_sub _ _ _).symm.trans e)]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 ex
  refine ⟨c, hc.symm, fun c' hc' => funext fun i => Chart.eq_of_loc fun p _ => ?_⟩
  obtain ⟨M', _, _, _, ρ, h₁, -, -, h₄⟩ := loc p
  have k : ∀ c : Fin m → R, w = ∑ i, c i • u i →
      ρ w = ∑ i, algebraMap R (Localization.AtPrime p) (c i) • ρ (u i) := fun c e => by
    rw [e, map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smulₛₗ _ _ _
  exact congrFun ((h₄ (ρ w) fun x => by rw [← h₁, hw, map_smulₛₗ]).unique (k _ hc') (k _ hc.symm)) i

end GlobalTheory.FlatRow.EigLocal

open GlobalTheory.Serre GlobalTheory.FlatRow.EigLocal in

theorem GlobalTheory.FlatRow.isEigBasis_of_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (χ : 𝓞 E →+* R) (m : ℕ) (v : Fin m → (epsR R ⟶ t.G)), (∀ (p : Ideal R) [p.IsPrime], ∃ (t' : SAB H (Sp (Localization.AtPrime p))) (n : SABMap t' t (spMap (algebraMap R (Localization.AtPrime p)))) (v' : Fin m → (epsR (Localization.AtPrime p) ⟶ t'.G)), (∀ i, IsVecOver (algebraMap R (Localization.AtPrime p)) n.φ (v i) (v' i)) ∧ EigenvectorLieDegree.IsEigBasis t'.act ((algebraMap R (Localization.AtPrime p)).comp χ) v') → EigenvectorLieDegree.IsEigBasis t.act χ v := by
  intro E _ _ _ H R _ t χ m v h
  have := t.semi.smooth
  have hT : ∀ i, IsTangent (v i) := fun i => hom_ext_of_loc fun p _ => by
    obtain ⟨t', n, v', hv, hb⟩ := h p
    have e := PolBaseChange.eSec_comm n.cart
    unfold eSec at e
    rw [← e, ← (hb.1 i).1, ← Category.assoc, ← fst_dual, Category.assoc, ← hv i, Category.assoc]
  obtain ⟨u, rfl⟩ : ∃ u : Fin m → Lie t.act, v = fun i => (u i).hom := ⟨fun i => Lie.mk _ _ (hT i), rfl⟩
  refine (isEigBasis_iff t.act χ u).2 (eigBasis_of_loc χ u fun p _ => ?_)
  obtain ⟨t', n, v', hv, hb⟩ := h p
  obtain ⟨ρ, hρ, hx⟩ := exists_res n.cart t.act t'.act n.act
  obtain rfl : v' = fun i => (ρ (u i)).hom :=
    funext fun i => (existsUnique_isVecOver n.cart.1 _).unique (hv i) (hρ _)
  have hb' := (isEigBasis_iff t'.act _ fun i => ρ (u i)).1 hb
  refine ⟨Lie t'.act, inferInstance, inferInstance, inferInstance, ρ, hx, fun w hw => exists_smul_eq_zero _ p w ?_, hb'⟩
  have e := hρ w
  have e₀ := hρ 0
  rw [map_zero, Lie.hom_zero, Lie.hom_zero] at e₀
  rw [hw, Lie.hom_zero] at e
  exact e.symm.trans e₀
