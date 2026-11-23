import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBOn
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LieBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GeomIntegralBaseChangeAndLocalization

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.KeyFam

theorem GeomInt.mvPolynomial {k S : Type} [Field k] [CommRing S] [Algebra k S] (σ : Type) [Finite σ]
    (h : GeomInt k S) : GeomInt k (MvPolynomial σ S) := by
  have h₀ := h.1
  have h₁ : Algebra.Smooth S (MvPolynomial σ S) := ⟨inferInstance, inferInstance⟩
  refine ⟨Algebra.Smooth.comp k S _, fun K _ _ => ?_⟩
  have := h.2 K
  let e₁ : K ⊗[k] MvPolynomial σ S ≃ₐ[k] K ⊗[k] (S ⊗[k] MvPolynomial σ k) :=
    Algebra.TensorProduct.congr AlgEquiv.refl ((MvPolynomial.algebraTensorAlgEquiv k S).symm.restrictScalars k)
  let e₂ : (K ⊗[k] S) ⊗[k] MvPolynomial σ k ≃ₐ[k] K ⊗[k] (S ⊗[k] MvPolynomial σ k) :=
    Algebra.TensorProduct.assoc k k k K S (MvPolynomial σ k)
  let e₃ := MvPolynomial.algebraTensorAlgEquiv (σ := σ) k (K ⊗[k] S)
  exact ((e₁.trans e₂.symm).toMulEquiv.trans e₃.toMulEquiv).isDomain _

theorem exists_univ_scalars {k S : Type} [Field k] [CommRing S] [Algebra k S] (h : GeomInt k S) (s : S →+* ℂ)
    (s₀ : S →ₐ[k] k) (n : ℕ) (a : ℂˣ) (N : Matrix (Fin n) (Fin n) ℂ) (hN : IsUnit N.det) :
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra k S') (j : S →ₐ[k] S') (s' : S' →+* ℂ) (s₀' : S' →ₐ[k] k)
      (b : S'ˣ) (M : Matrix (Fin n) (Fin n) S'), GeomInt k S' ∧ s'.comp j.toRingHom = s ∧ s₀'.comp j = s₀ ∧
      IsUnit M.det ∧ s' b = a ∧ ∀ i l, s' (M i l) = N i l := by
  let T := MvPolynomial (Option (Fin n × Fin n)) S
  let M₀ : Matrix (Fin n) (Fin n) T := fun i l => MvPolynomial.X (some (i, l))
  let r : T := MvPolynomial.X none * M₀.det
  have key : ∀ {L : Type} [CommRing L] (f : S →+* L) (c : L) (B : Matrix (Fin n) (Fin n) L),
      ∃ F : T →+* L, (∀ z, F (MvPolynomial.C z) = f z) ∧ F (MvPolynomial.X none) = c ∧
        (∀ i l, F (M₀ i l) = B i l) ∧ F r = c * B.det := by
    intro L _ f c B
    let F : T →+* L := MvPolynomial.eval₂Hom f (fun o => o.elim c fun p => B p.1 p.2)
    have h₁ : F (MvPolynomial.X none) = c := MvPolynomial.eval₂Hom_X' _ _ _
    have h₂ : ∀ i l, F (M₀ i l) = B i l := fun i l => MvPolynomial.eval₂Hom_X' _ _ _
    refine ⟨F, fun z => MvPolynomial.eval₂Hom_C _ _ _, h₁, h₂, ?_⟩
    rw [map_mul, h₁, RingHom.map_det]
    congr 2
    ext i l
    exact h₂ i l
  obtain ⟨F, hF₁, hF₂, hF₃, hF₄⟩ := key s a N
  obtain ⟨G, hG₁, -, -, hG₄⟩ := key s₀.toRingHom 1 1
  have uF : IsUnit (F r) := hF₄ ▸ a.isUnit.mul hN
  have uG : IsUnit (G r) := by rw [hG₄]; simp
  have hr : r ≠ 0 := fun e => uG.ne_zero (by rw [e, map_zero])
  let S' := Localization.Away r
  have ur : IsUnit (algebraMap T S' r) := IsLocalization.Away.algebraMap_isUnit r
  rw [map_mul, IsUnit.mul_iff] at ur
  obtain ⟨⟨b, hb⟩, uM⟩ := ur
  let j : S →ₐ[k] S' := (IsScalarTower.toAlgHom k T S').comp (IsScalarTower.toAlgHom k S T)
  have hj : ∀ z, j z = algebraMap T S' (MvPolynomial.C z) := fun _ => rfl
  let g₀ : S' →+* k := IsLocalization.Away.lift r uG
  have hg : ∀ z, g₀ (j z) = s₀ z := fun z => by
    rw [hj, IsLocalization.Away.lift_eq, hG₁]; rfl
  refine ⟨S', inferInstance, inferInstance, j, IsLocalization.Away.lift r uF,
    { g₀ with commutes' := fun c => ?_ }, b, (algebraMap T S').mapMatrix M₀,
    (GlobalTheory.KeyFam.geomInt_baseChange_and_away k k T (h.mvPolynomial _)).2 r hr, RingHom.ext fun z => ?_, AlgHom.ext hg, ?_, ?_, fun i l => ?_⟩
  · change g₀ _ = _
    rw [← j.commutes, hg, s₀.commutes]
  · change IsLocalization.Away.lift r uF (j z) = _
    rw [hj, IsLocalization.Away.lift_eq, hF₁]
  · rwa [← RingHom.map_det]
  · rw [hb, IsLocalization.Away.lift_eq, hF₂]
  · change IsLocalization.Away.lift r uF (algebraMap T S' (M₀ i l)) = _
    rw [IsLocalization.Away.lift_eq, hF₃]

theorem exists_polPB_of_keyPB {R R' : Type} [CommRing R] [CommRing R'] {x' : KeyIn R'} {x : KeyIn R} {f : R →+* R'}
    (h : KeyPB x' x f) : ∃ φ, PolPB x'.P x.P (spMap f) φ := by
  obtain ⟨φ, -, w, hg, -, hp, hw, -⟩ := h
  exact ⟨φ, hp, hg, w, hw⟩

theorem exists_univ_frames : Out.Laws → ∀ (k S : Type) [Field k] [CommRing S] [Algebra k S] (y : KeyIn S) (x : KeyIn ℂ) (s : S →+* ℂ) (φ : x.P.A.left ⟶ y.P.A.left) (s₀ : S →ₐ[k] k), GeomInt k S → PolPB x.P y.P (spMap s) φ → ∃ (S' : Type) (_ : CommRing S') (_ : Algebra k S') (j : S →ₐ[k] S') (y' : KeyIn S') (s' : S' →+* ℂ) (s₀' : S' →ₐ[k] k) (ψ : y'.P.A.left ⟶ y.P.A.left), GeomInt k S' ∧ KeyPB x y' s' ∧ PolPB y'.P y.P (spMap j.toRingHom) ψ ∧ s₀'.comp j = s₀ := by
  intro hL k S _ _ _ y x s φ s₀ hS hφ
  obtain ⟨Q, hg, rig', hr', th', hth', v', hv'⟩ := x
  dsimp only at φ hφ
  obtain ⟨rig, hr, th, hth, v, hv, H⟩ := KeyTf.exists_keyPB_on S ℂ s y Q φ hg hφ.2.1 hφ.1 hφ.2.2
  obtain ⟨a, t, ht, hat, Hid⟩ := (KeyOnPol.main hL ℂ).2 ⟨Q, hg, rig, hr, th, hth, v, hv⟩ rig' hr' th' hth' v' hv'
  choose N hN using fun i => (hv.2 _ (hv'.1 i)).exists
  have := Q.isAb.comm
  have uN : IsUnit (Matrix.det (N : Matrix _ _ ℂ)) :=
    ((LieComb.lieComb_algebra ℂ Q.A Q.g v hv.1).2.2.2.2 N v' hv hN).1 hv'
  obtain ⟨S', _, _, j, s', s₀', b, M, hS', hs, hs₀, uM, hb, hM⟩ := exists_univ_scalars hS s s₀ Q.g a N uN
  obtain ⟨y₁, H₁⟩ := exists_keyPB_ring y j.toRingHom
  have H₂ := KeyCancel.keyPB_cancel _ _ _ y y₁ _ _ s' H₁ (hs ▸ H)
  obtain ⟨ψ, hψ⟩ := exists_polPB_of_keyPB H₁
  have e : Q.g = y₁.P.g := KeyGalDesc.g_eq H₂
  have := y₁.P.isAb.comm
  let M' : Matrix (Fin y₁.P.g) (Fin y₁.P.g) S' := Matrix.reindex (finCongr e) (finCongr e) M
  have uM' : IsUnit M'.det := by rwa [Matrix.det_reindex_self]
  obtain ⟨ex, -, -, -, bas⟩ := LieComb.lieComb_algebra S' y₁.P.A y₁.P.g y₁.v y₁.basis.1
  choose v₁ hv₁ using fun i => (ex (M' i)).exists
  obtain ⟨t₁, ht₁, -, hle⟩ := exists_sec_div y₁.P.A.hom b.inv_mul y₁.th
  refine ⟨S', _, _, j, ⟨y₁.P, y₁.g_pos, y₁.rig, y₁.rig_gen, t₁,
    fun p => (y₁.th_ne p).imp fun z hz => ⟨hz.1, hle hz.2⟩, v₁, (bas M' v₁ y₁.basis hv₁).2 uM'⟩, s', s₀', ψ, hS', ?_, hψ, hs₀⟩
  rw [← RingHom.id_comp s']
  refine keyPB_trans _ _ _ _ _ _ _ _ ?_ Hid
  refine KeyPBScale.keyPB_scale S' ℂ s' y₁.P y₁.g_pos y₁.rig y₁.rig_gen y₁.th y₁.th_ne y₁.v y₁.basis t₁ _ v₁ _ b M' Q e
    hg rig hr th hth v hv t ht v' hv' ht₁ hv₁ (hb ▸ hat) (fun i => ?_) H₂
  convert hN i using 2 with l
  exact hM i l

end GlobalTheory.KeyFam
end
