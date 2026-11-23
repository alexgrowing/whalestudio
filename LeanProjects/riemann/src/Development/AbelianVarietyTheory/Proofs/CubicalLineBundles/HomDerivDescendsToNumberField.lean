import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolFibreIdCompCancel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

namespace HomDerivDescent

variable {R R' : Type} [CommRing R] [CommRing R']

theorem isLieComb_one_iff {G : Over (Sp R)} [GrpObj G] (a : R) (t w : epsR R ⟶ G) :
    IsLieComb ![a] ![t] w ↔ w.left = spMap (epsScaleR a) ≫ t.left := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu 0
  · intro h
    refine ⟨![w], fun i => ?_, by simp⟩
    fin_cases i
    exact h

theorem epsScaleR_comp_dualMapR (g : R →+* R') (a : R) :
    (epsScaleR (g a)).comp (Chart.dualMapR g) = (Chart.dualMapR g).comp (epsScaleR a) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [Chart.dualMapR, epsScaleR, mul_comm]

theorem isLieComb_pull {g : R →+* R'} {G H : Over (Sp R)} {G' H' : Over (Sp R')} [GrpObj H] [GrpObj H']
    {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hψ : IsPullback ψ H'.hom H.hom (spMap g))
    {v : epsR R ⟶ G} {t : epsR R ⟶ H} {v' : epsR R' ⟶ G'} {t' : epsR R' ⟶ H'}
    (hv : IsVecOver g φ v v') (ht : IsVecOver g ψ t t') {f : G ⟶ H} {f' : G' ⟶ H'}
    (hf : f'.left ≫ ψ = φ ≫ f.left) {a : R} (h : IsLieComb ![a] ![t] (v ≫ f)) :
    IsLieComb ![g a] ![t'] (v' ≫ f') := by
  rw [isLieComb_one_iff] at h ⊢
  unfold IsVecOver at hv ht
  refine hψ.hom_ext ?_ ?_
  · rw [Over.comp_left] at h ⊢
    rw [Category.assoc, hf, ← Category.assoc, hv, Category.assoc, h, Category.assoc, ht, ← Category.assoc,
      ← Category.assoc]
    congr 1
    exact (spMap_comp_spMap _ _).trans
      ((congrArg spMap (epsScaleR_comp_dualMapR g a).symm).trans (spMap_comp_spMap _ _).symm)
  · rw [Over.w, Category.assoc, Over.w]
    refine Eq.trans ?_ (spMap_comp_spMap _ _).symm
    change spMap _ = _
    congr 1
    ext x <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_descent (hT : ThetaUnifAV) (hB : Out.PolBaseChangeSt) (k : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ k] (P Q : Out.PolAV (Sp k)) {Pc Qc : Out.PolAV (Sp ℂ)} {φc : Pc.A.left ⟶ P.A.left}
    {ψc : Qc.A.left ⟶ Q.A.left} (hP : IsPolFibre (algebraMap k ℂ) P Pc φc) (hQ : IsPolFibre (algebraMap k ℂ) Q Qc ψc)
    (fc : Pc.A ⟶ Qc.A) [IsMonHom fc] :
    ∃ (K : IntermediateField k ℂ) (P₁ Q₁ : Out.PolAV (Sp K)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left)
      (m : Pc.A.left ⟶ P₁.A.left) (n : Qc.A.left ⟶ Q₁.A.left) (f₁ : P₁.A ⟶ Q₁.A), FiniteDimensional k K ∧
      IsPolFibre (algebraMap k K) P P₁ φ₁ ∧ IsPolFibre (algebraMap k K) Q Q₁ ψ₁ ∧
      IsPolFibre (algebraMap K ℂ) P₁ Pc m ∧ IsPolFibre (algebraMap K ℂ) Q₁ Qc n ∧ m ≫ φ₁ = φc ∧ n ≫ ψ₁ = ψc ∧
      IsMonHom f₁ ∧ fc.left ≫ n = m ≫ f₁.left := by
  obtain ⟨e, he, he'⟩ := grpPullback_iso hP.2.1 (isGrpPullback_pullback P.A _)
  obtain ⟨d, hd, hd'⟩ := grpPullback_iso hQ.2.1 (isGrpPullback_pullback Q.A _)
  obtain ⟨K, f, j, hK, hf, j₁, j₂, j₃⟩ := hom_descends_to_numberField hT hB k P Q (e.inv ≫ fc ≫ d.hom) inferInstance
  obtain ⟨P₁, φ₁, hP₁⟩ := exists_isPolFibre hB (algebraMap k K) P
  obtain ⟨Q₁, ψ₁, hQ₁⟩ := exists_isPolFibre hB (algebraMap k K) Q
  obtain ⟨m, hm, hm'⟩ := PolFibre.cancel (g := algebraMap K ℂ) hP₁ hP
  obtain ⟨n, hn, hn'⟩ := PolFibre.cancel (g := algebraMap K ℂ) hQ₁ hQ
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso hP₁.2.1 (isGrpPullback_pullback P.A _)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso (isGrpPullback_pullback Q.A _) hQ₁.2.1
  refine ⟨K, P₁, Q₁, φ₁, ψ₁, m, n, a.hom ≫ f ≫ b.hom, hK, hP₁, hQ₁, hm, hn, hm', hn', inferInstance, ?_⟩
  have key : m ≫ a.hom.left = e.hom.left ≫ j := by
    apply pullback.hom_ext
    · exact ((Category.assoc _ _ _).trans ((congrArg (m ≫ ·) ha').trans hm')).trans
        ((Category.assoc _ _ _).trans ((congrArg (e.hom.left ≫ ·) j₁).trans he')).symm
    · exact ((Category.assoc _ _ _).trans ((congrArg (m ≫ ·) (Over.w a.hom)).trans hm.2.1.1.w)).trans
        ((Category.assoc _ _ _).trans ((congrArg (e.hom.left ≫ ·) j₂).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ _) (Over.w e.hom))))).symm
  refine hQ₁.2.1.1.hom_ext ?_ ?_
  · have r : e.hom.left ≫ (e.inv ≫ fc ≫ d.hom).left = fc.left ≫ d.hom.left := by
      rw [← Over.comp_left, e.hom_inv_id_assoc, Over.comp_left]
    rw [Category.assoc, hn', Over.comp_left, Over.comp_left]
    simp only [Category.assoc]
    rw [hb', ← Category.assoc, key, Category.assoc, ← hd', ← Category.assoc, ← r, Category.assoc]
    exact congrArg (e.hom.left ≫ ·) j₃.symm
  · rw [Category.assoc, Category.assoc, Over.w, hn.2.1.1.w, hm.2.1.1.w, ← Category.assoc, Over.w]

end HomDerivDescent

open HomDerivDescent in

theorem hom_deriv_descends_to_numberField : ThetaUnifAV → Out.PolBaseChangeSt → ∀ (R : Type) [CommRing R] (P Q : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (t : epsR R ⟶ Q.A) (k : IntermediateField ℚ ℂ) (ρ : R →+* k) (α : ℂ), FiniteDimensional ℚ k → IsTangent v → (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ Q.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' Q P' φ' → IsVecOver f' φ' t v' → IsLieBasis ![v']) → (∀ (P₁ Q₁ : Out.PolAV (Sp ℂ)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR ℂ ⟶ P₁.A) (t₁ : epsR ℂ ⟶ Q₁.A), IsPolFibre ((algebraMap k ℂ).comp ρ) P P₁ φ₁ → IsPolFibre ((algebraMap k ℂ).comp ρ) Q Q₁ ψ₁ → IsVecOver ((algebraMap k ℂ).comp ρ) φ₁ v v₁ → IsVecOver ((algebraMap k ℂ).comp ρ) ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![α] ![t₁] (v₁ ≫ f₁)) → ∃ (K₁ : IntermediateField ℚ ℂ) (hk : k ≤ K₁) (a : K₁), FiniteDimensional ℚ K₁ ∧ (a : ℂ) = α ∧ (∀ (P₁ Q₁ : Out.PolAV (Sp K₁)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR K₁ ⟶ P₁.A) (t₁ : epsR K₁ ⟶ Q₁.A), IsPolFibre ((IntermediateField.inclusion hk).toRingHom.comp ρ) P P₁ φ₁ → IsPolFibre ((IntermediateField.inclusion hk).toRingHom.comp ρ) Q Q₁ ψ₁ → IsVecOver ((IntermediateField.inclusion hk).toRingHom.comp ρ) φ₁ v v₁ → IsVecOver ((IntermediateField.inclusion hk).toRingHom.comp ρ) ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![a] ![t₁] (v₁ ≫ f₁)) := by
  intro hT hB R _ P Q v t k ρ α hk hv hbas hhom
  obtain ⟨Pk, φk, hPk⟩ := exists_isPolFibre hB ρ P
  obtain ⟨Qk, ψk, hQk⟩ := exists_isPolFibre hB ρ Q
  obtain ⟨Pc, φc, hPc⟩ := exists_isPolFibre hB (algebraMap k ℂ) Pk
  obtain ⟨Qc, ψc, hQc⟩ := exists_isPolFibre hB (algebraMap k ℂ) Qk
  have hPc' := PolFibre.comp hPk hPc
  have hQc' := PolFibre.comp hQk hQc
  obtain ⟨vc, hvc, -⟩ := existsUnique_isVecOver hPc'.2.1.1 v
  obtain ⟨tc, htc, -⟩ := existsUnique_isVecOver hQc'.2.1.1 t
  obtain ⟨fc, hfc, hα⟩ := hhom Pc Qc _ _ vc tc hPc' hQc' hvc htc
  obtain ⟨K, P₀, Q₀, φ₀, ψ₀, m, n, f₀, hK, hP₀, hQ₀, hm, hn, em, en, hf₀, ef⟩ :=
    exists_descent hT hB k Pk Qk hPc hQc fc
  have hP₀' := PolFibre.comp hPk hP₀
  have hQ₀' := PolFibre.comp hQk hQ₀
  obtain ⟨v₀, hv₀, -⟩ := existsUnique_isVecOver hP₀'.2.1.1 v
  obtain ⟨t₀, ht₀, -⟩ := existsUnique_isVecOver hQ₀'.2.1.1 t
  obtain ⟨c, hc, -⟩ := (hbas _ _ _ _ _ hQ₀' ht₀).2 (v₀ ≫ f₀)
    (HomDescent.isTangent_comp f₀ (hv₀.isTangent hP₀'.2.1 hv))
  obtain ⟨a, rfl⟩ : ∃ a, c = ![a] := ⟨c 0, by ext i; fin_cases i; rfl⟩
  have hv' : IsVecOver (algebraMap K ℂ) m v₀ vc :=
    (PolFibre.vec_iff hP₀'.2.1.1 hm.2.1.1.w hv₀).2 (by rw [← Category.assoc, em]; exact hvc)
  have ht' : IsVecOver (algebraMap K ℂ) n t₀ tc :=
    (PolFibre.vec_iff hQ₀'.2.1.1 hn.2.1.1.w ht₀).2 (by rw [← Category.assoc, en]; exact htc)
  have hα' := isLieComb_pull hn.2.1.1 hv' ht' ef hc
  have haα : algebraMap K ℂ a = α := congrFun (((hbas _ _ _ _ _ hQc' htc).2 (vc ≫ fc)
    (HomDescent.isTangent_comp fc (hvc.isTangent hPc'.2.1 hv))).unique hα' hα) 0
  have main : ∀ (P₁ Q₁ : Out.PolAV (Sp K)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left)
      (v₁ : epsR K ⟶ P₁.A) (t₁ : epsR K ⟶ Q₁.A), IsPolFibre ((algebraMap k K).comp ρ) P P₁ φ₁ →
      IsPolFibre ((algebraMap k K).comp ρ) Q Q₁ ψ₁ → IsVecOver ((algebraMap k K).comp ρ) φ₁ v v₁ →
      IsVecOver ((algebraMap k K).comp ρ) ψ₁ t t₁ →
      ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![a] ![t₁] (v₁ ≫ f₁) := by
    intro P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP₁ hQ₁ hv₁ ht₁
    obtain ⟨p, hp, rfl⟩ := PolFibre.cancel (g := RingHom.id K) hP₀' hP₁
    obtain ⟨q, hq, rfl⟩ := PolFibre.cancel (g := RingHom.id K) hQ₀' hQ₁
    obtain ⟨f₁, hf₁, e₁⟩ := HomDescent.exists_isMonHom_pull hp.2.1 hq.2.1 f₀
    exact ⟨f₁, hf₁, isLieComb_pull hq.2.1.1 ((PolFibre.vec_iff hP₀'.2.1.1 hp.2.1.1.w hv₀).2 hv₁)
      ((PolFibre.vec_iff hQ₀'.2.1.1 hq.2.1.1.w ht₀).2 ht₁) e₁ hc⟩
  have : IsScalarTower ℚ k K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hfin : FiniteDimensional ℚ K := Module.Finite.trans k K
  exact ⟨K.restrictScalars ℚ, fun x hx => K.algebraMap_mem ⟨x, hx⟩, a, hfin, haα, main⟩

end GlobalTheory
