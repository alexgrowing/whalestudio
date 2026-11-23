import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DFormMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormAlternating
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormLocalOfFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormVanishOfFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGradedVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolynomialTransfer
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Onto
noncomputable section
namespace GlobalTheory.CompanionTheory.AffOmP

section Alg
open KaehlerDifferential

theorem kaehler_basis {K A : Type} [CommRing K] [CommRing A] [Algebra K A] {d : ℕ} (t : Fin d → A)
    (h : (MvPolynomial.eval₂Hom (algebraMap K A) t : MvPolynomial (Fin d) K →+* A).Etale) :
    ∃ b : Module.Basis (Fin d) A Ω[A⁄K], ∀ i, b i = KaehlerDifferential.D K A (t i) := by
  letI : Algebra (MvPolynomial (Fin d) K) A := (MvPolynomial.eval₂Hom (algebraMap K A) t).toAlgebra
  haveI : IsScalarTower K (MvPolynomial (Fin d) K) A :=
    .of_algebraMap_eq fun r => (MvPolynomial.eval₂_C _ _ _).symm
  haveI : Algebra.Etale (MvPolynomial (Fin d) K) A := h
  refine ⟨((mvPolynomialBasis K (Fin d)).baseChange _).map
    (tensorKaehlerEquivOfFormallyEtale K (MvPolynomial (Fin d) K) _), fun i => ?_⟩
  rw [Module.Basis.map_apply, tensorKaehlerEquivOfFormallyEtale_apply]
  simp only [Module.Basis.baseChange_apply, mvPolynomialBasis_apply, mapBaseChange_tmul, one_smul, map_D]
  exact congrArg _ (MvPolynomial.eval₂_X _ _ _)

theorem ring_diff {K A B : Type} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] {d : ℕ}
    (J J' : Ideal B) (hJ : J * J ≤ J') (f f' : A →ₐ[K] B) (hf : ∀ g, f' g - f g ∈ J) (t : Fin d → A) (g : A) (p : Fin d → A)
    (hp : KaehlerDifferential.D K A g = ∑ i, p i • KaehlerDifferential.D K A (t i)) :
    f' g - f g - ∑ i, f (p i) * (f' (t i) - f (t i)) ∈ J' := by
  letI : Algebra A (B ⧸ J') := ((Ideal.Quotient.mk J').comp f.toRingHom).toAlgebra
  haveI : IsScalarTower K A (B ⧸ J') := .of_algebraMap_eq fun r => by
    change _ = Ideal.Quotient.mk J' (f (algebraMap K A r))
    rw [AlgHom.commutes]
    rfl
  have hsm : ∀ (x : A) (y : B), x • (Ideal.Quotient.mk J' y) = Ideal.Quotient.mk J' (f x * y) := fun x y => by
    rw [Algebra.smul_def, map_mul]
    rfl
  let dl : A →ₗ[K] B ⧸ J' := (Ideal.Quotient.mkₐ K J').toLinearMap ∘ₗ (f'.toLinearMap - f.toLinearMap)
  have hdl : ∀ x, dl x = Ideal.Quotient.mk J' (f' x - f x) := fun x => rfl
  let δ : Derivation K A (B ⧸ J') := Derivation.mk' dl fun x y => by
    rw [hdl, hdl, hdl, hsm, hsm, ← map_add]
    refine Ideal.Quotient.eq.2 (?_ : _ ∈ J')
    have := hJ (Ideal.mul_mem_mul (hf x) (hf y))
    convert this using 1
    simp only [map_mul]
    ring
  have hδ : ∀ x, δ x = Ideal.Quotient.mk J' (f' x - f x) := fun x => rfl
  have h := congrArg δ.liftKaehlerDifferential hp
  rw [map_sum] at h
  simp only [map_smul, Derivation.liftKaehlerDifferential_comp_D, hδ, hsm] at h
  rw [← map_sum] at h
  exact Ideal.Quotient.eq.1 h

theorem form_expand {K A : Type} [CommRing K] [CommRing A] [Algebra K A] {d a : ℕ}
    (b : Module.Basis (Fin d) A Ω[A⁄K]) (g₀ : A) (g : Fin a → A) (p : Fin a → Fin d → A)
    (hp : ∀ k, KaehlerDifferential.D K A (g k) = ∑ i, p k i • b i) :
    form K g₀ g = ∑ I : Fin a → Fin d, (g₀ * ∏ k, p k (I k)) • exteriorPower.ιMulti A a (b ∘ I) := by
  unfold form
  have e : (fun k => KaehlerDifferential.D K A (g k)) = fun k => ∑ i, p k i • b i := funext hp
  rw [e]
  have := (exteriorPower.ιMulti A a (M := Ω[A⁄K])).toMultilinearMap.map_sum (fun k i => p k i • b i)
  change (exteriorPower.ιMulti A a (M := Ω[A⁄K])) _ = _ at this
  rw [this, Finset.smul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  have h2 := (exteriorPower.ιMulti A a (M := Ω[A⁄K])).toMultilinearMap.map_smul_univ (fun k => p k (I k)) (fun k => b (I k))
  rw [mul_smul]
  exact congrArg (g₀ • ·) h2

end Alg

section Rp
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem rep_unique {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ}
    {z : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c c' : CH.H (sq a b) j}
    (h : Rep a b z c) (h' : Rep a b z c') : c = c' := by
  obtain ⟨f, hf, rfl, e⟩ := h
  obtain ⟨f', hf', rfl, e'⟩ := h'
  have : f = f' := funext fun s => Subtype.ext ((e s).trans (e' s).symm)
  subst this
  rfl

theorem rep_sum {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ} {ι : Type} (S : Finset ι)
    (z : ι → ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))) (c : ι → CH.H (sq a b) j)
    (h : ∀ i ∈ S, Rep a b (z i) (c i)) (h0 : Rep a b (fun _ => 0) (0 : CH.H (sq a b) j)) :
    Rep a b (fun s => ∑ i ∈ S, z i s) (∑ i ∈ S, c i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using h0
  | insert i S hi ih =>
    rw [Finset.sum_insert hi]
    refine GlobalTheory.CompanionTheory.GrForm.rep_add (fun s => ?_) (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert hi, sub_self]
    exact zero_mem _

theorem rep_res {A : C ⥤ CommAlgCat.{0} R} {U U' : ObjectProperty C} (h : U' ≤ U) (a b : IdF A) {j : ℕ}
    {z : ∀ s : ComposableArrows U.FullSubcategory j, A.obj (s.obj (Fin.last j)).obj}
    {c : HU (sq a b) U j}
    (hr : Rep (a.res U.ι) (b.res U.ι) z c) :
    Rep (a.res U'.ι) (b.res U'.ι) (fun s => z (s ⋙ ObjectProperty.ιOfLE h)) ((resU (sq a b) h).pull j c) := by
  obtain ⟨f, hf, rfl, hz⟩ := hr
  refine ⟨(resU (sq a b) h).pullC j f, ?_, rfl, fun s => hz (s ⋙ ObjectProperty.ιOfLE h)⟩
  have := (resU (sq a b) h).d_pullC j f
  refine this.trans ?_
  have hf' : CH.d (U.ι ⋙ sq a b) j f = 0 := hf
  rw [hf', map_zero]

end Rp

section Alg2

theorem ext_alt {K A : Type} [CommRing K] [CommRing A] [Algebra K A] {H : Type 1} [AddCommGroup H] [Module K H] {d a : ℕ}
    (b : Module.Basis (Fin d) A Ω[A⁄K]) (Cl : (Fin a → Fin d) → A →ₗ[K] H)
    (h0 : ∀ I, ¬ Function.Injective I → Cl I = 0)
    (hs : ∀ (I : Fin a → Fin d) (π : Equiv.Perm (Fin a)) (x : A), Cl (I ∘ π) x = (Equiv.Perm.sign π : ℤ) • Cl I x)
    (hb : Function.Bijective fun x : Idx a d → A => ∑ J : Idx a d, Cl J.1 (x J)) :
    ∃ e : Om K A a ≃ₗ[K] H, ∀ (I : Fin a → Fin d) (x : A), e (x • exteriorPower.ιMulti A a (b ∘ I)) = Cl I x := by
  classical
  let ε : Idx a d ≃ Set.powersetCard (Fin d) a :=
    { toFun := fun J => Set.powersetCard.ofFinEmbEquiv (OrderEmbedding.ofStrictMono J.1 J.2)
      invFun := fun s => ⟨Set.powersetCard.ofFinEmbEquiv.symm s, (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono⟩
      left_inv := fun J => Subtype.ext (by
        funext k
        simp)
      right_inv := fun s => by
        have : OrderEmbedding.ofStrictMono (⇑(Set.powersetCard.ofFinEmbEquiv.symm s))
            (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono = Set.powersetCard.ofFinEmbEquiv.symm s := by
          ext k
          simp
        simp [this] }
  let B := (b.exteriorPower a).reindex ε.symm
  have hB : ∀ J : Idx a d, B J = exteriorPower.ιMulti A a (b ∘ J.1) := by
    intro J
    have e1 : ε J = Set.powersetCard.ofFinEmbEquiv (OrderEmbedding.ofStrictMono J.1 J.2) := rfl
    simp only [B, Module.Basis.reindex_apply, Equiv.symm_symm, exteriorPower.basis_apply, exteriorPower.ιMulti_family, e1]
    simp
  let L : (Idx a d → A) →ₗ[K] H := ∑ J : Idx a d, (Cl J.1).comp (LinearMap.proj J)
  have hL : ∀ x, L x = ∑ J : Idx a d, Cl J.1 (x J) := fun x => by simp [L]
  have hLb : Function.Bijective L := by
    have : (L : (Idx a d → A) → H) = fun x => ∑ J : Idx a d, Cl J.1 (x J) := funext hL
    rw [this]
    exact hb
  let e : Om K A a ≃ₗ[K] H := (B.equivFun.restrictScalars K).trans (LinearEquiv.ofBijective L hLb)
  have hJ : ∀ (J : Idx a d) (x : A), e (x • exteriorPower.ιMulti A a (b ∘ J.1)) = Cl J.1 x := by
    intro J x
    change L (B.equivFun (x • exteriorPower.ιMulti A a (b ∘ J.1))) = _
    rw [← hB, map_smul, hL]
    rw [Finset.sum_eq_single J]
    · simp [Module.Basis.equivFun_apply]
    · intro J' _ hne
      have : (Finsupp.single J (1 : A)) J' = 0 := Finsupp.single_eq_of_ne hne
      simp [Module.Basis.equivFun_apply, this]
    · simp
  refine ⟨e, fun I x => ?_⟩
  by_cases hI : Function.Injective I
  · let π := Tuple.sort I
    have hm : Monotone (I ∘ π) := Tuple.monotone_sort I
    have hsm : StrictMono (I ∘ π) := hm.strictMono_of_injective (hI.comp π.injective)
    have e1 : I = (I ∘ π) ∘ (π⁻¹ : Equiv.Perm (Fin a)) := by
      funext k
      simp
    have h1 := hJ ⟨I ∘ π, hsm⟩ x
    have h2 : exteriorPower.ιMulti A a (b ∘ I) =
        (Equiv.Perm.sign (π⁻¹ : Equiv.Perm (Fin a)) : ℤ) • exteriorPower.ιMulti A a (b ∘ (I ∘ π)) := by
      conv_lhs => rw [e1]
      exact (exteriorPower.ιMulti A a (M := Ω[A⁄K])).map_perm (b ∘ (I ∘ π)) (π⁻¹ : Equiv.Perm (Fin a))
    rw [h2, smul_comm, map_zsmul, h1, ← hs]
    rw [← e1]
  · have h1 : exteriorPower.ιMulti A a (b ∘ I) = 0 :=
      (exteriorPower.ιMulti A a (M := Ω[A⁄K])).map_eq_zero_of_not_injective _ fun h => hI (Function.Injective.of_comp h)
    rw [h1, smul_zero, map_zero, h0 I hI]
    rfl
end Alg2

section Frame
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} {d : ℕ}

theorem form_add (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) {j : ℕ} (I : Fin j → Fin d) (x y : Φ.A.obj E.D)
    (s : ComposableArrows C j) : E.form σ I (x + y) s = E.form σ I x s + E.form σ I y s := by
  simp only [Frame.form, map_add, mul_add]

theorem form_smul (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) {j : ℕ} (I : Fin j → Fin d) (r : R) (x : Φ.A.obj E.D)
    (s : ComposableArrows C j) : E.form σ I (r • x) s = r • E.form σ I x s := by
  simp only [Frame.form, map_smul, mul_smul_comm]

theorem rep_smul {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ}
    {z : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c : CH.H (sq a b) j} (r : R)
    (h : Rep a b z c) : Rep a b (fun s => r • z s) (r • c) := by
  obtain ⟨f, hf, rfl, e⟩ := h
  refine ⟨r • f, by rw [map_smul, hf, smul_zero], rfl, fun s => ?_⟩
  change r • (show sqM a b _ from f s).1 = _
  rw [e s]
  rfl

theorem frame_cl (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (a : ℕ) :
    ∃ Cl : (Fin a → Fin d) → Φ.A.obj E.D →ₗ[R] CH.H (gr Fil (a : ℤ)) a,
      (∀ I x, Rep (Fil (a : ℤ)) (Fil ((a : ℤ) + 1)) (E.form σ I x) (Cl I x)) ∧
      (∀ I, ¬ Function.Injective I → Cl I = 0) ∧
      ∀ (I : Fin a → Fin d) (π : Equiv.Perm (Fin a)) x, Cl (I ∘ π) x = (Equiv.Perm.sign π : ℤ) • Cl I x := by
  have hx0 : ∀ x : Φ.A.obj E.D, x ∈ (Fil ((0 : ℕ) : ℤ)).S E.D := fun x => by
    rw [hF.top _ (by simp)]
    trivial
  have hex : ∀ (I : Fin a → Fin d) (x : Φ.A.obj E.D), ∃ c, Rep (Fil (a : ℤ)) (Fil ((a : ℤ) + 1)) (E.form σ I x) c :=
    fun I x => GlobalTheory.CompanionTheory.CocProd.rep_form hF E σ hc a 0 (a : ℤ) (by simp) I x (hx0 x)
  choose c hcr using hex
  let Cl : (Fin a → Fin d) → Φ.A.obj E.D →ₗ[R] CH.H (gr Fil (a : ℤ)) a := fun I =>
    { toFun := c I
      map_add' := fun x y => rep_unique (hcr I (x + y)) (GlobalTheory.CompanionTheory.GrForm.rep_add (fun s => by
        rw [form_add, sub_self]
        exact zero_mem _) (hcr I x) (hcr I y))
      map_smul' := fun r x => rep_unique (hcr I (r • x)) (by
        have e : E.form σ I (r • x) = fun s => r • E.form σ I x s := funext (form_smul E σ I r x)
        rw [e]
        exact rep_smul r (hcr I x)) }
  refine ⟨Cl, hcr, fun I hI => ?_, fun I π x => ?_⟩
  · ext x
    exact (GlobalTheory.CompanionTheory.AltForm.form_alternating hF E σ hc a 0 (a : ℤ) (by simp) I x (hx0 x) _ (hcr I x)).1 hI
  · exact rep_unique (hcr (I ∘ π) x)
      ((GlobalTheory.CompanionTheory.AltForm.form_alternating hF E σ hc a 0 (a : ℤ) (by simp) I x (hx0 x) _ (hcr I x)).2.1 π)

theorem frame_bij (Q : Poly Φ) (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (a : ℕ)
    (hQ : ∀ r' ≤ (a : ℤ) + 1, Q.Crit Fil r') (hbot : (Fil 1).S E.D = ⊥)
    (Cl : (Fin a → Fin d) → Φ.A.obj E.D →ₗ[R] CH.H (gr Fil (a : ℤ)) a)
    (hCl : ∀ I x, Rep (Fil (a : ℤ)) (Fil ((a : ℤ) + 1)) (E.form σ I x) (Cl I x)) :
    Function.Bijective fun x : Idx a d → Φ.A.obj E.D => ∑ J : Idx a d, Cl J.1 (x J) := by
  obtain ⟨-, hL⟩ := GlobalTheory.CompanionTheory.LocGrStep.loc_gr Q hF E σ hc (a : ℤ) hQ a
  obtain ⟨h2, h3⟩ := hL 0 (by simp)
  have hx0 : ∀ x : Φ.A.obj E.D, x ∈ (Fil ((0 : ℕ) : ℤ)).S E.D := fun x => by
    rw [hF.top _ (by simp)]
    trivial
  have hrep : ∀ x : Idx a d → Φ.A.obj E.D, Rep (Fil (a : ℤ)) (Fil ((a : ℤ) + 1))
      (fun s => ∑ J : Idx a d, E.form σ J.1 (x J) s) (∑ J : Idx a d, Cl J.1 (x J)) := fun x =>
    rep_sum Finset.univ (fun J : Idx a d => E.form σ J.1 (x J)) _ (fun J _ => hCl J.1 (x J)) ⟨0, map_zero _, rfl, fun s => rfl⟩
  have hinj : ∀ x : Idx a d → Φ.A.obj E.D, ∑ J : Idx a d, Cl J.1 (x J) = 0 → x = 0 := by
    intro x hx
    have h4 := h3 x (fun J => hx0 _) (by
      have := hrep x
      rw [hx] at this
      exact this)
    funext J
    have h5 := h4 J
    have e : (Fil (((0 : ℕ) : ℤ) + 1)).S E.D = ⊥ := by simpa using hbot
    rw [e] at h5
    exact Ideal.mem_bot.1 h5
  refine ⟨fun x y hxy => ?_, fun c => ?_⟩
  · have := hinj (x - y) (by
      simp only [Pi.sub_apply, map_sub, Finset.sum_sub_distrib]
      exact sub_eq_zero.2 hxy)
    exact sub_eq_zero.1 this
  · obtain ⟨x, -, hx⟩ := h2 c
    exact ⟨x, rep_unique (hrep x) hx⟩
end Frame

section Rule
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} {d : ℕ}

def liftF (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) {A : Type} [CommRing A] (θ : A → Φ.A.obj E.D) {a : ℕ} (g₀ : A) (g : Fin a → A)
    (s : ComposableArrows C a) : Φ.A.obj (s.obj (Fin.last a)) :=
  (Φ.A.map (σ _)).hom (θ g₀) * ∏ k : Fin a, ((Φ.A.map (s.map (homOfLE (Fin.le_last k.succ)))).hom ((Φ.A.map (σ _)).hom (θ (g k))) -
    (Φ.A.map (s.map (homOfLE (Fin.le_last k.castSucc)))).hom ((Φ.A.map (σ _)).hom (θ (g k))))

theorem prod_fil (hF : IsFil Φ Fil) (T : C) {ι : Type} (S : Finset ι) (u : ι → Φ.A.obj T)
    (h : ∀ k ∈ S, u k ∈ (Fil ((1 : ℕ) : ℤ)).S T) : ∏ k ∈ S, u k ∈ (Fil ((S.card : ℕ) : ℤ)).S T := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.card_empty, hF.top _ (by simp)]
    trivial
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, Nat.add_comm]
    exact hF.mul 1 S.card T (h i (Finset.mem_insert_self _ _)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem prod_sub_fil (hF : IsFil Φ Fil) (T : C) {ι : Type} (S : Finset ι) (u v : ι → Φ.A.obj T)
    (hu : ∀ k ∈ S, u k ∈ (Fil ((1 : ℕ) : ℤ)).S T) (hv : ∀ k ∈ S, v k ∈ (Fil ((1 : ℕ) : ℤ)).S T)
    (h : ∀ k ∈ S, u k - v k ∈ (Fil ((2 : ℕ) : ℤ)).S T) :
    ∏ k ∈ S, u k - ∏ k ∈ S, v k ∈ (Fil ((S.card + 1 : ℕ) : ℤ)).S T := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    have hu' := fun k (hk : k ∈ S) => hu k (Finset.mem_insert_of_mem hk)
    have hv' := fun k (hk : k ∈ S) => hv k (Finset.mem_insert_of_mem hk)
    have h' := fun k (hk : k ∈ S) => h k (Finset.mem_insert_of_mem hk)
    have h1 := hF.mul 2 S.card T (h i (Finset.mem_insert_self _ _)) (prod_fil hF T S u hu')
    have h2 := hF.mul 1 (S.card + 1) T (hv i (Finset.mem_insert_self _ _)) (ih hu' hv' h')
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have e : u i * ∏ k ∈ S, u k - v i * ∏ k ∈ S, v k =
        (u i - v i) * ∏ k ∈ S, u k + v i * (∏ k ∈ S, u k - ∏ k ∈ S, v k) := by ring
    rw [e]
    have e1 : 2 + S.card = S.card + 1 + 1 := by omega
    have e2 : 1 + (S.card + 1) = S.card + 1 + 1 := by omega
    rw [e1] at h1
    rw [e2] at h2
    exact add_mem h1 h2

theorem frame_rule (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil)
    {A : Type} [CommRing A] [Algebra R A] (θ : A →ₐ[R] Φ.A.obj E.D) (τ : Fin d → A) (ht : E.Coords fun i => θ (τ i))
    {a : ℕ} (g₀ : A) (g : Fin a → A) (p : Fin a → Fin d → A)
    (hp : ∀ k, KaehlerDifferential.D R A (g k) = ∑ i, p k i • KaehlerDifferential.D R A (τ i))
    (s : ComposableArrows C a) :
    liftF E σ θ g₀ g s - ∑ I : Fin a → Fin d, E.form σ I (θ (g₀ * ∏ k, p k (I k))) s ∈ (Fil ((a : ℤ) + 1)).S _ := by
  classical
  let T := s.obj (Fin.last a)
  have hx0 : ∀ x : Φ.A.obj E.D, x ∈ (Fil ((0 : ℕ) : ℤ)).S E.D := fun x => by
    rw [hF.top _ (by simp)]
    trivial
  have hcong : ∀ (m m' : E.D ⟶ T) (x : Φ.A.obj E.D), (Φ.A.map m').hom x - (Φ.A.map m).hom x ∈ (Fil ((1 : ℕ) : ℤ)).S T := by
    intro m m' x
    have := hc 0 m' m (hx0 x)
    simpa using this
  let mS : Fin a → (E.D ⟶ T) := fun k => σ _ ≫ s.map (homOfLE (Fin.le_last k.succ))
  let mC : Fin a → (E.D ⟶ T) := fun k => σ _ ≫ s.map (homOfLE (Fin.le_last k.castSucc))
  let fS : Fin a → (A →ₐ[R] Φ.A.obj T) := fun k => (Φ.A.map (mS k)).hom.comp θ
  let fC : Fin a → (A →ₐ[R] Φ.A.obj T) := fun k => (Φ.A.map (mC k)).hom.comp θ
  let F : A →ₐ[R] Φ.A.obj T := (Φ.A.map (σ T)).hom.comp θ
  let w : Fin a → Fin d → Φ.A.obj T := fun k i => fS k (τ i) - fC k (τ i)
  have hw : ∀ k i, (Φ.A.map (s.map (homOfLE (Fin.le_last k.succ)))).hom
      (E.a σ i (s.map (homOfLE (Fin.castSucc_lt_succ (i := k)).le))) = w k i := by
    intro k i
    have e : (σ _ ≫ s.map (homOfLE (Fin.castSucc_lt_succ (i := k)).le)) ≫ s.map (homOfLE (Fin.le_last k.succ)) = mC k := by
      rw [Category.assoc, ← s.map_comp]
      rfl
    rw [Frame.a, ← E.nat, e, ht]
    rfl
  have hform : ∀ (I : Fin a → Fin d) (x : A), E.form σ I (θ x) s = (∏ k, w k (I k)) * F x := by
    intro I x
    unfold Frame.form
    refine congrArg (· * _) (Finset.prod_congr rfl fun k _ => hw k (I k))
  have hlift : liftF E σ θ g₀ g s = F g₀ * ∏ k, (fS k (g k) - fC k (g k)) := by
    unfold liftF
    refine congrArg (_ * ·) (Finset.prod_congr rfl fun k _ => ?_)
    have e1 : (Φ.A.map (mS k)).hom (θ (g k)) = (Φ.A.map (s.map (homOfLE (Fin.le_last k.succ)))).hom ((Φ.A.map (σ _)).hom (θ (g k))) := by
      simp only [mS, Functor.map_comp]
      rfl
    have e2 : (Φ.A.map (mC k)).hom (θ (g k)) = (Φ.A.map (s.map (homOfLE (Fin.le_last k.castSucc)))).hom ((Φ.A.map (σ _)).hom (θ (g k))) := by
      simp only [mC, Functor.map_comp]
      rfl
    change _ = (Φ.A.map (mS k)).hom (θ (g k)) - (Φ.A.map (mC k)).hom (θ (g k))
    rw [e1, e2]
  have hFS : ∀ k x, fS k x - fC k x ∈ (Fil ((1 : ℕ) : ℤ)).S T := fun k x => hcong _ _ _
  have hwJ : ∀ k i, w k i ∈ (Fil ((1 : ℕ) : ℤ)).S T := fun k i => hFS k _
  have hJ2 : (Fil ((1 : ℕ) : ℤ)).S T * (Fil ((1 : ℕ) : ℤ)).S T ≤ (Fil ((2 : ℕ) : ℤ)).S T := by
    refine Ideal.mul_le.2 fun x hx y hy => ?_
    exact hF.mul 1 1 T hx hy
  let v : Fin a → Φ.A.obj T := fun k => ∑ i, F (p k i) * w k i
  have hv1 : ∀ k, v k ∈ (Fil ((1 : ℕ) : ℤ)).S T := fun k =>
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hwJ k i)
  have hdiff : ∀ k, (fS k (g k) - fC k (g k)) - v k ∈ (Fil ((2 : ℕ) : ℤ)).S T := by
    intro k
    have h1 := ring_diff _ _ hJ2 (fC k) (fS k) (hFS k) τ (g k) (p k) (hp k)
    have h2 : ∑ i, fC k (p k i) * (fS k (τ i) - fC k (τ i)) - v k ∈ (Fil ((2 : ℕ) : ℤ)).S T := by
      rw [← Finset.sum_sub_distrib]
      refine Ideal.sum_mem _ fun i _ => ?_
      rw [← sub_mul]
      exact hF.mul 1 1 T (hcong _ _ _) (hwJ k i)
    have := add_mem h1 h2
    simpa using this
  have hprod := prod_sub_fil hF T Finset.univ (fun k => fS k (g k) - fC k (g k)) v
    (fun k _ => hFS k _) (fun k _ => hv1 k) (fun k _ => hdiff k)
  have hsum : ∑ I : Fin a → Fin d, E.form σ I (θ (g₀ * ∏ k, p k (I k))) s = F g₀ * ∏ k, v k := by
    have e : ∏ k, v k = ∑ I : Fin a → Fin d, ∏ k, F (p k (I k)) * w k (I k) := by
      simp only [v]
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    rw [e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hform, map_mul, map_prod, Finset.prod_mul_distrib]
    ring
  rw [hlift, hsum, ← mul_sub]
  have hc' : ((Finset.univ : Finset (Fin a)).card + 1 : ℕ) = a + 1 := by simp
  rw [hc'] at hprod
  have := Ideal.mul_mem_left _ (F g₀) hprod
  simpa using this
end Rule

section FrameMain
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} {d : ℕ}

theorem frame_main (Q : Poly Φ) (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (a : ℕ)
    (hQ : ∀ r' ≤ (a : ℤ) + 1, Q.Crit Fil r') (hbot : (Fil 1).S E.D = ⊥)
    {A : Type} [CommRing A] [Algebra R A] (θ : A ≃ₐ[R] Φ.A.obj E.D) (τ : Fin d → A) (ht : E.Coords fun i => θ (τ i))
    (b : Module.Basis (Fin d) A Ω[A⁄R]) (hb : ∀ i, b i = KaehlerDifferential.D R A (τ i)) :
    ∃ e : Om R A a ≃ₗ[R] CH.H (gr Fil (a : ℤ)) a, ∀ (g₀ : A) (g : Fin a → A) (c : CH.H (gr Fil (a : ℤ)) a),
      Rep (Fil (a : ℤ)) (Fil ((a : ℤ) + 1)) (liftF E σ θ g₀ g) c → e (form R g₀ g) = c := by
  obtain ⟨Cl, hCl, h0, hs⟩ := frame_cl hF E σ hc a
  have hbij := frame_bij Q hF E σ hc a hQ hbot Cl hCl
  let Cl' : (Fin a → Fin d) → A →ₗ[R] CH.H (gr Fil (a : ℤ)) a := fun I => (Cl I).comp θ.toLinearMap
  have hb' : Function.Bijective fun x : Idx a d → A => ∑ J : Idx a d, Cl' J.1 (x J) := by
    have e : (fun x : Idx a d → A => ∑ J : Idx a d, Cl' J.1 (x J)) =
        (fun x : Idx a d → Φ.A.obj E.D => ∑ J : Idx a d, Cl J.1 (x J)) ∘ (fun x J => θ (x J)) := rfl
    rw [e]
    refine hbij.comp ⟨fun x y h => funext fun J => θ.injective (congrFun h J), fun y => ⟨fun J => θ.symm (y J), ?_⟩⟩
    funext J
    simp
  obtain ⟨e, he⟩ := ext_alt b Cl' (fun I hI => by
      ext x
      simp [Cl', h0 I hI]) (fun I π x => hs I π (θ x)) hb'
  refine ⟨e, fun g₀ g c hrep => ?_⟩
  have hp : ∀ k, KaehlerDifferential.D R A (g k) = ∑ i, (b.repr (KaehlerDifferential.D R A (g k)) i) • b i := fun k =>
    (b.sum_repr _).symm
  have hrule := frame_rule hF E σ hc θ.toAlgHom τ ht g₀ g (fun k i => b.repr (KaehlerDifferential.D R A (g k)) i)
    (fun k => by simpa only [hb] using hp k)
  rw [form_expand b g₀ g _ hp, map_sum]
  simp only [he]
  have hsum := rep_sum (a := Fil (a : ℤ)) (b := Fil ((a : ℤ) + 1)) Finset.univ
    (fun I : Fin a → Fin d => E.form σ I (θ (g₀ * ∏ k, b.repr (KaehlerDifferential.D R A (g k)) (I k))))
    (fun I => Cl I (θ (g₀ * ∏ k, b.repr (KaehlerDifferential.D R A (g k)) (I k)))) (fun I _ => hCl I _)
    ⟨0, map_zero _, rfl, fun s => rfl⟩
  refine rep_unique hsum (GlobalTheory.CompanionTheory.GrForm.rep_congr (fun s => hrule s) hrep)

end FrameMain

section Geo
variable {K : Type} [Field K] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of K))
open GlobalTheory.CompanionTheory.GrForm

theorem sq_tau_id {Q Q' : ObjectProperty (Thick (smFun Z q))} (h : Q' ≤ Q) (r r' : ℤ) (T : Q'.FullSubcategory)
    (x : Pb.sqM (Pb.sFil Q r) (Pb.sFil Q r') ((Pb.incl h).G.obj T)) :
    (show Pb.sqM (Pb.sFil Q' r) (Pb.sFil Q' r') T from
      ((Pb.incl h).sq (Pb.incl_fil h r) (Pb.incl_fil h r')).τ T x).1 = x.1 := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem inU_eq (V : Z.Opens) :
    inU q V = St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) ⊤ {V} := by
  funext T
  refine propext ⟨fun h => ⟨trivial, V, rfl, h⟩, ?_⟩
  rintro ⟨-, W, hW, h⟩
  rw [Set.mem_singleton_iff.1 hW] at h
  exact h

theorem res_bij (V : Z.Opens) (a j : ℕ) (h : SS q 1 (a + 1) V ≤ inU q V) :
    Function.Bijective ((resU (G q a) h).pull j) := by
  have key : ∀ (U : ObjectProperty (Thick (smFun Z q)))
      (hU : U = St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) ⊤ {V})
      (h : SS q 1 (a + 1) V ≤ U), Function.Bijective ((resU (G q a) h).pull j) := by
    intro U hU h
    subst hU
    have hb := Pb.refl (γ := dividedPowersBot K) (q := q) (κ := Ideal.Quotient.mk ⊥) ⊤ 1 (a + 1) (Or.inl ⟨rfl, rfl⟩) {V} h
      (a : ℤ) ((a : ℤ) + 1) (by push_cast; exact le_rfl) j
    have e : (((resU (G q a) h).pull j : _ → _)) = (((Pb.incl h).sq (Pb.incl_fil h (a : ℤ)) (Pb.incl_fil h ((a : ℤ) + 1))).pull j : _ → _) := by
      funext x
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
      funext s
      refine Subtype.ext ?_
      exact (sq_tau_id q h _ _ _ _).symm
    rw [e]
    exact hb
  exact key _ (inU_eq q V) h

theorem theta_alg {V : Z.Opens} {s d : ℕ} (E : Frame (sP (SS q 1 s V)) d) (σ : ∀ T, E.D ⟶ T)
    (θ : Γ(Z, V) ≃+* (sP (SS q 1 s V)).A.obj E.D) (hGr : E.GrConst (sFil (SS q 1 s V)))
    (hbot : (sFil (SS q 1 s V) 1).S E.D = ⊥)
    (hpt : ∀ (T : (SS q 1 s V).FullSubcategory) (h : InU V T.obj) (f : Γ(Z, V)),
        Ideal.Quotient.mk T.obj.J (show T.obj.B from ((sP (SS q 1 s V)).A.map (σ T)).hom (θ f)) = ev T.obj h f) :
    ∃ θ' : Sec q V ≃ₐ[K] (sP (SS q 1 s V)).A.obj E.D, ∀ f : Γ(Z, V), θ' f = θ f := by
  have hF : IsFil (sP (SS q 1 s V)) (sFil (SS q 1 s V)) := GlobalTheory.CompanionTheory.DPFil.isFil_sFil _
  have hJ : E.D.obj.J = ⊥ := by
    have := hF.one E.D
    rw [hbot] at this
    exact this.symm
  have hD : InU V E.D.obj := FrameEx.inU_of_SS _ E.D.property
  have hid : ∀ x : (sP (SS q 1 s V)).A.obj E.D, ((sP (SS q 1 s V)).A.map (σ E.D)).hom x = x := by
    intro x
    have h1 := hGr 0 (σ E.D) (𝟙 _) (x := x) (by
      rw [hF.top _ (by simp)]
      trivial)
    have h2 : (sFil (SS q 1 s V) (((0 : ℕ) : ℤ) + 1)).S E.D = ⊥ := by simpa using hbot
    rw [h2, Ideal.mem_bot, sub_eq_zero, CategoryTheory.Functor.map_id] at h1
    exact h1
  refine ⟨AlgEquiv.ofRingEquiv (f := θ) fun k => ?_, fun _ => rfl⟩
  have h1 := hpt E.D hD (strV q V k)
  rw [ev_str, hid] at h1
  have h2 := Ideal.Quotient.eq.1 h1
  rw [hJ, Ideal.mem_bot, sub_eq_zero] at h2
  exact h2

theorem exists_lifts {V : Z.Opens} {s d : ℕ} (hle : SS q 1 s V ≤ inU q V) (E : Frame (sP (SS q 1 s V)) d) (σ : ∀ T, E.D ⟶ T)
    (θ : Sec q V → (sP (SS q 1 s V)).A.obj E.D)
    (hpt : ∀ (T : (SS q 1 s V).FullSubcategory) (h : InU V T.obj) (f : Γ(Z, V)),
        Ideal.Quotient.mk T.obj.J (show T.obj.B from ((sP (SS q 1 s V)).A.map (σ T)).hom (θ f)) = ev T.obj h f) :
    ∃ Λ : Lifts q V, ∀ {a : ℕ} (g₀ : Sec q V) (g : Fin a → Sec q V) (x : ComposableArrows (SS q 1 s V).FullSubcategory a),
      Λ.form g₀ g (x ⋙ ObjectProperty.ιOfLE hle) = liftF E σ θ g₀ g x := by
  classical
  let v : ∀ T : (inU q V).FullSubcategory, Sec q V → T.obj.B := fun T g =>
    if hT : SS q 1 s V T.obj then ((sP (SS q 1 s V)).A.map (σ ⟨T.obj, hT⟩)).hom (θ g) else lft V T.obj g
  have hvP : ∀ (T : (SS q 1 s V).FullSubcategory) (g : Sec q V),
      v ⟨T.obj, hle _ T.property⟩ g = ((sP (SS q 1 s V)).A.map (σ T)).hom (θ g) := fun T g => dif_pos T.property
  refine ⟨⟨v, fun T g => ?_⟩, fun {a} g₀ g x => ?_⟩
  · by_cases hT : SS q 1 s V T.obj
    · have e : v T g = ((sP (SS q 1 s V)).A.map (σ ⟨T.obj, hT⟩)).hom (θ g) := dif_pos hT
      rw [e]
      exact hpt ⟨T.obj, hT⟩ T.property g
    · have e : v T g = lft V T.obj g := dif_neg hT
      rw [e]
      exact lft_spec _ T.property g
  · unfold Lifts.form liftF
    refine congrArg₂ (· * ·) (hvP _ g₀) (Finset.prod_congr rfl fun k _ => ?_)
    have e1 := hvP (x.obj k.succ) (g k)
    have e2 := hvP (x.obj k.castSucc) (g k)
    change (x.map _).hom.φ (v ⟨_, _⟩ (g k)) - (x.map _).hom.φ (v ⟨_, _⟩ (g k)) = _
    rw [e1, e2]
    rfl

set_option maxHeartbeats 3000000 in

theorem affOm : FormUniq → AffOm := by
  intro hU K _ _ Z q V d ⟨c⟩ a
  have hle : SS q 1 (a + 1) V ≤ inU q V := fun T hT => FrameEx.inU_of_SS T hT
  have hb : TFBase (dividedPowersBot K) 1 (a + 1) :=
    { nil := FrameEx.dividedPowerFiltration_dividedPowersBot K (Nat.succ_ne_zero a)
      tf := fun r x h => by simpa using h
      dv := fun n hn => ⟨0, (n : K)⁻¹, by
        simp only [Nat.cast_one, one_pow]
        exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn)⟩ }
  refine ⟨fun j hj => ?_, ?_⟩
  · have hS : Subsingleton (HU (GF q a) (SS q 1 (a + 1) V) j) :=
      van stFrame LocGrStep.loc_gr PolyTfCon.polyTf 1 (a + 1) hb q c a j (Nat.lt_succ_self a) hj
    exact @Function.Injective.subsingleton _ _ _ (res_bij q V a j hle).1 hS
  obtain ⟨E, σ, θ, hGr, hbot, hco, -, hpt⟩ := stFrame 1 (a + 1) hb q c _ (isLift_lft V c.t)
  obtain ⟨Qp, hQ⟩ := PolyTfCon.polyTf (dividedPowersBot K) q (Ideal.Quotient.mk ⊥) 1 (a + 1) {V}
  have hF : IsFil (sP (SS q 1 (a + 1) V)) (sFil (SS q 1 (a + 1) V)) := GlobalTheory.CompanionTheory.DPFil.isFil_sFil _
  have hbot1 : (sFil (SS q 1 (a + 1) V) 1).S E.D = ⊥ := by simpa using hbot 1 one_ne_zero
  obtain ⟨θ', hθ'⟩ := theta_alg q E σ θ hGr hbot1 hpt
  obtain ⟨b, hbb⟩ := kaehler_basis (K := K) (A := Sec q V) c.t c.etale
  obtain ⟨e₀, he₀⟩ := frame_main Qp hF E σ hGr a (fun r' h => (hQ r' (by push_cast at h ⊢; omega)).1) hbot1 θ' c.t
    (by simpa only [hθ'] using hco) b hbb
  let ρ := LinearEquiv.ofBijective ((resU (G q a) hle).pull a) (res_bij q V a a hle)
  refine ⟨(e₀.trans ρ.symm).toLinearMap, fun g₀ g => ?_, (e₀.trans ρ.symm).bijective⟩
  obtain ⟨-, hu⟩ := hU K Z q V
  obtain ⟨c₀, hc₀, -⟩ := hu a g₀ g
  obtain ⟨Λ, hΛ⟩ := exists_lifts q hle E σ θ' (fun T h f => by rw [hθ']; exact hpt T h f)
  have h1 := rep_res hle (thFil (smFun Z q) (a : ℤ)) (thFil (smFun Z q) ((a : ℤ) + 1)) (hc₀ Λ)
  have h2 : e₀ (form K g₀ g) = ρ c₀ := he₀ g₀ g _ (by
    have e : (fun x => Λ.form g₀ g (x ⋙ ObjectProperty.ιOfLE hle)) = liftF E σ θ' g₀ g := funext fun x => hΛ g₀ g x
    rw [← e]
    exact h1)
  have h3 : (e₀.trans ρ.symm) (form K g₀ g) = c₀ := by
    change ρ.symm (e₀ (form K g₀ g)) = c₀
    rw [h2, LinearEquiv.symm_apply_apply]
  change IsForm q V g₀ g ((e₀.trans ρ.symm) (form K g₀ g))
  rw [h3]
  exact hc₀

end Geo

end GlobalTheory.CompanionTheory.AffOmP
