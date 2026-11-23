import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyPBId
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.StalkOfAppLEEq
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyGalDesc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa

theorem g_eq {R S : Type} [CommRing R] [CommRing S] {y : KeyIn S} {x : KeyIn R} {f : R →+* S} (h : KeyPB y x f) :
    y.P.g = x.P.g := by
  obtain ⟨_, _, _, hg, _⟩ := h
  exact hg

private lemma presheaf_map_constFn {A : Type} [CommRing A] {X : Scheme.{0}} (p : X ⟶ Sp A) {U V : X.Opens} (h : V ≤ U)
    (c : A) : (X.presheaf.map (homOfLE h).op).hom (constFn p U c) = constFn p V c := by
  have key : ∀ (e : U ≤ p ⁻¹ᵁ ⊤) (e' : V ≤ p ⁻¹ᵁ ⊤) (z : Γ(Sp A, ⊤)),
      (X.presheaf.map (homOfLE h).op).hom ((p.appLE ⊤ U e).hom z) = (p.appLE ⊤ V e').hom z := by
    intro e e' z
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
  exact key _ _ _

private lemma appLE_constFn_theta_law {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {X Y : Scheme.{0}}
    (p : X ⟶ Sp A) (q : Y ⟶ Sp B) (φ : Y ⟶ X) (hsq : φ ≫ p = q ≫ spMap f) (U : X.Opens) (V : Y.Opens)
    (h : V ≤ φ ⁻¹ᵁ U) (c : A) : (φ.appLE U V h).hom (constFn p U c) = constFn q V (f c) := by
  have key : ∀ (e : U ≤ p ⁻¹ᵁ ⊤) (e' : V ≤ q ⁻¹ᵁ ⊤) (z : Γ(Sp A, ⊤)),
      (φ.appLE U V h).hom ((p.appLE ⊤ U e).hom z) = (q.appLE ⊤ V e').hom ((spMap f).appTop.hom z) := by
    intro e e' z
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
    generalize_proofs e₃
    revert e₃
    rw [hsq]
    intro e₃
    rw [Scheme.Hom.comp_appLE, CommRingCat.hom_comp, RingHom.comp_apply]
    rfl
  have hn := congrArg (fun g => g.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hn
  unfold constFn
  rw [hn]
  exact key _ _ _

private lemma isUnit_of_sec_eq_const_mul_nonvanishing {A : Type} [CommRing A] (P : Out.PolAV (Sp A)) (th th' : P.L.Sec) (a : A)
    (ha : ∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i)
    (hth' : ∀ s : Sp A, ∃ x : P.A.left, P.A.hom x = s ∧ x ∈ Out.nonzeroLocus th') : IsUnit a := by
  by_contra hna
  obtain ⟨m, hm, ham⟩ := Ideal.exists_le_maximal (Ideal.span {a}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  obtain ⟨x, hx, hxL⟩ := hth' ⟨m, hm.isPrime⟩
  unfold Out.nonzeroLocus at hxL
  rw [TopologicalSpace.Opens.mem_iSup] at hxL
  obtain ⟨k, hk⟩ := hxL
  rw [ha, Scheme.basicOpen_mul] at hk
  have hk1 := hk.1
  unfold constFn Scheme.Hom.appLE at hk1
  rw [CommRingCat.hom_comp, RingHom.comp_apply, Scheme.basicOpen_res, ← Scheme.preimage_basicOpen,
    basicOpen_eq_of_affine] at hk1
  have h2 : P.A.hom x ∈ PrimeSpectrum.basicOpen a := hk1.2
  rw [hx] at h2
  exact (show a ∉ m from h2) (ham (Ideal.subset_span rfl))

private lemma isLieComb_comp_cast' {A : Type} [CommRing A] {G : Over (Sp A)} [GrpObj G] {m n : ℕ} (h : m = n)
    {c : Fin n → A} {v : Fin n → (epsR A ⟶ G)} {w : epsR A ⟶ G} (hc : IsLieComb c v w) :
    IsLieComb (fun k : Fin m => c (k.cast h)) (fun k => v (k.cast h)) w := by
  subst h
  simpa using hc

private lemma isLieBasis_comp_cast {A : Type} [CommRing A] {G : Over (Sp A)} [GrpObj G] {m n : ℕ} (h : m = n)
    {v : Fin n → (epsR A ⟶ G)} (hv : IsLieBasis v) : IsLieBasis (fun k : Fin m => v (k.cast h)) := by
  subst h
  simpa using hv

theorem exists_keyPB_pair {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (P : Out.PolAV (Sp R))
    (hg rig hr th hth v hv th' hth' v' hv') (a : R) (Mx : Matrix (Fin P.g) (Fin P.g) R)
    (ha : ∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) (hM : ∀ i, IsLieComb (Mx i) v (v' i)) :
    ∃ (Q : Out.PolAV (Sp R')) (hg₁ : _) (rig₁ : _) (hr₁ : _) (th₁ : _) (hth₁ : _) (v₁ : _) (hv₁ : _) (th₁' : _) (hth₁' : _)
      (v₁' : _) (hv₁' : _) (Mx₁ : Matrix (Fin Q.g) (Fin Q.g) R'),
      KeyPB ⟨Q, hg₁, rig₁, hr₁, th₁, hth₁, v₁, hv₁⟩ ⟨P, hg, rig, hr, th, hth, v, hv⟩ f ∧
      KeyPB ⟨Q, hg₁, rig₁, hr₁, th₁', hth₁', v₁', hv₁'⟩ ⟨P, hg, rig, hr, th', hth', v', hv'⟩ f ∧
      (∀ i, LB.Sec.f th₁' i = constFn Q.A.hom _ (f a) * LB.Sec.f th₁ i) ∧ (∀ i, IsLieComb (Mx₁ i) v₁ (v₁' i)) ∧
      Mx₁.det = f Mx.det := by
  classical
  obtain ⟨y, hy⟩ := exists_keyPB_ring (⟨P, hg, rig, hr, th, hth, v, hv⟩ : KeyIn R) f
  obtain ⟨y₂, hy₂⟩ := exists_keyPB_ring (⟨P, hg, rig, hr, th', hth', v', hv'⟩ : KeyIn R) f
  obtain ⟨φ, he, w, hgq, F, hpb, hwg, hrig, hth1, hF1, hFe, hv1⟩ := id hy
  obtain ⟨φ₂, -, -, hgq₂, F₂, hpb₂, -, -, -, hF₂1, hF₂e, hv₂⟩ := hy₂

  have hF : F = ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f := by
    apply GlobalTheory.KeyCancel.dualNumber_ringHom_ext
    · intro c
      rw [hF1]
      have pr1 : ∀ c : R, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f (algebraMap R _ c) = algebraMap R' _ (f c) := by
        clear * - f
        intro c
        unfold ReciprocityTheory.ChartRestriction.G.Chart.dualMapR
        apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
      exact (pr1 c).symm
    · rw [hFe]
      have pr2 : ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f DualNumber.eps = DualNumber.eps := by
        clear * - f
        unfold ReciprocityTheory.ChartRestriction.G.Chart.dualMapR
        apply TrivSqZeroExt.ext <;> simp
      exact pr2.symm
  have hF₂ : F₂ = F := by
    apply GlobalTheory.KeyCancel.dualNumber_ringHom_ext
    · intro c
      rw [hF₂1, hF1]
    · rw [hF₂e, hFe]

  let Mx₁ : Matrix (Fin y.P.g) (Fin y.P.g) R' := fun i k => f (Mx (i.cast hgq) (k.cast hgq))
  have hov : ∀ (c : R') (k : Fin y.P.g), (spMap (epsScaleR c) ≫ (y.v k).left) ≫ y.P.A.hom = (epsR R').hom := by
    intro c k
    rw [Category.assoc, Over.w (y.v k), GlobalTheory.LieCombBaseChange.epsScale_over]
  let u : Fin y.P.g → Fin y.P.g → (epsR R' ⟶ y.P.A) := fun i k =>
    Over.homMk (spMap (epsScaleR (Mx₁ i k)) ≫ (y.v k).left) (hov _ k)
  let v₁' : Fin y.P.g → (epsR R' ⟶ y.P.A) := fun i => (List.ofFn (u i)).prod
  have hcomb : ∀ i, IsLieComb (Mx₁ i) y.v (v₁' i) := fun i => ⟨u i, fun k => rfl, rfl⟩
  have hover : ∀ i, (v₁' i).left ≫ φ = spMap F ≫ (v' (i.cast hgq)).left := by
    intro i
    rw [hF]
    refine (GlobalTheory.lieComb_baseChange R R' f P.A y.P.A φ hpb y.P.g (fun k => v (k.cast hgq)) (v' (i.cast hgq))
      (fun k => Mx (i.cast hgq) (k.cast hgq)) y.v (v₁' i) ?_ (isLieComb_comp_cast' hgq (hM _))).mpr (hcomb i)
    intro k
    have h0 := hv1 k
    rw [hF] at h0
    exact h0

  obtain ⟨e, he1, he2⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.grpPullback_iso hpb hpb₂
  have hv₁' : IsLieBasis v₁' := by
    have := he1
    apply ReciprocityTheory.ChartRestriction.G.Chart.isLieBasis_iso e
    have hb := isLieBasis_comp_cast (hgq.trans hgq₂.symm) y₂.basis
    have hfun : (fun i => v₁' i ≫ e.hom) = fun k => y₂.v (k.cast (hgq.trans hgq₂.symm)) := by
      funext i
      apply Over.OverMorphism.ext
      apply hpb₂.1.hom_ext
      · rw [Over.comp_left, Category.assoc, he2, hover, hv₂, hF₂]
        congr 3
      · rw [Over.w (v₁' i ≫ e.hom), Over.w (y₂.v _)]
    rw [hfun]
    exact hb

  have hfa : IsUnit (f a) := (isUnit_of_sec_eq_const_mul_nonvanishing P th th' a ha hth').map f
  let th₁' : y.P.L.Sec := ⟨fun i => constFn y.P.A.hom _ (f a) * y.th.f i, fun i j => by
    rw [map_mul, map_mul, y.th.compat i j, presheaf_map_constFn, presheaf_map_constFn]
    ring⟩
  have hcu : ∀ U, IsUnit (constFn y.P.A.hom U (f a)) := fun U => by
    unfold constFn
    exact (hfa.map _).map _
  have hnz : Out.nonzeroLocus th₁' = Out.nonzeroLocus y.th := by
    unfold Out.nonzeroLocus
    refine iSup_congr fun k => ?_
    show y.P.A.left.basicOpen (constFn y.P.A.hom _ (f a) * y.th.f k) = _
    rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (hcu _), inf_eq_right.mpr (Scheme.basicOpen_le _ _)]
  have hth₁' : ∀ s : Sp R', ∃ x : y.P.A.left, y.P.A.hom x = s ∧ x ∈ Out.nonzeroLocus th₁' := by
    rw [hnz]
    exact y.th_ne
  have hsq : φ ≫ P.A.hom = y.P.A.hom ≫ spMap f := hpb.1.w
  refine ⟨y.P, y.g_pos, y.rig, y.rig_gen, y.th, y.th_ne, y.v, y.basis, th₁', hth₁', v₁', hv₁', Mx₁, hy,
    ⟨φ, he, w, hgq, F, hpb, hwg, hrig, ?_, hF1, hFe, hover⟩, fun i => rfl, hcomb, ?_⟩
  · intro j i h
    rw [ha, map_mul, hth1 j i h]
    show _ = _ * resG _ _ (constFn y.P.A.hom _ (f a) * y.th.f i)
    rw [map_mul, appLE_constFn_theta_law f P.A.hom y.P.A.hom φ hsq, presheaf_map_constFn]
    ring
  · show ((Mx.map f).submatrix (finCongr hgq) (finCongr hgq)).det = _
    rw [Matrix.det_submatrix_equiv_self]
    exact (RingHom.map_det f Mx).symm

theorem exists_descent (g : ℕ) (ka : ∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K], KeyIn K → Kˣ)
    (hF : ∀ (K K' : Type) [Field K] [CharZero K] [IsAlgClosed K] [Field K'] [CharZero K'] [IsAlgClosed K'] (f : K →+* K')
      (x : KeyIn K) (x' : KeyIn K'), x.P.g = g → KeyPB x' x f → (ka K' x' : K') = f (ka K x))
    (K : Type) [Field K] [CharZero K] (x : KeyIn K) :
    ∃ y : Kˣ, x.P.g = g → ∀ (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (f : K →+* L) (xL : KeyIn L),
      KeyPB xL x f → (ka L xL : L) = f y := by
  classical
  by_cases hx : x.P.g = g
  swap
  · exact ⟨1, fun h => absurd h hx⟩
  have : CharZero (AlgebraicClosure K) :=
    charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective
  obtain ⟨xb, hxb⟩ := exists_keyPB_ring x (algebraMap K (AlgebraicClosure K))
  have hgb : xb.P.g = g := (g_eq hxb).trans hx

  have key : ∀ (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (e : AlgebraicClosure K →+* L) (xL : KeyIn L),
      KeyPB xL x (e.comp (algebraMap K (AlgebraicClosure K))) →
        (ka L xL : L) = e (ka (AlgebraicClosure K) xb) := by
    intro L _ _ _ e xL hL
    exact hF _ _ e xb xL hgb (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ x xb xL _ e hxb hL)

  have hfix : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      σ (ka (AlgebraicClosure K) xb : AlgebraicClosure K) = ka (AlgebraicClosure K) xb := by
    intro σ
    have hc : ((σ.symm : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) : AlgebraicClosure K →+* AlgebraicClosure K).comp
        (algebraMap K (AlgebraicClosure K)) = algebraMap K (AlgebraicClosure K) := by
      ext a
      simp
    have h2 := key _ ((σ.symm : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) : AlgebraicClosure K →+* AlgebraicClosure K)
      xb (by rw [hc]; exact hxb)
    have h3 := congrArg σ h2
    simpa using h3
  obtain ⟨y₀, hy₀⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K)
    (ka (AlgebraicClosure K) xb : AlgebraicClosure K)).mpr hfix
  have h0 : y₀ ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hy₀
    exact (ka (AlgebraicClosure K) xb).ne_zero hy₀.symm
  refine ⟨Units.mk0 y₀ h0, fun _ L _ _ _ f xL hL => ?_⟩
  let _ : Algebra K L := f.toAlgebra
  let e : AlgebraicClosure K →ₐ[K] L := IsAlgClosed.lift
  have hc : (e : AlgebraicClosure K →+* L).comp (algebraMap K (AlgebraicClosure K)) = f := by
    ext a
    show e (algebraMap K _ a) = f a
    rw [e.commutes]
    rfl
  have h1 := key L (e : AlgebraicClosure K →+* L) xL (by rw [hc]; exact hL)
  rw [h1, ← hy₀, Units.val_mk0]
  show e (algebraMap K _ y₀) = f y₀
  rw [e.commutes]
  rfl

theorem exists_kaRuleK : Out.PolBaseChangeSt → ∀ g c M : ℕ, KaRule g c M → ∃ ka, KaRuleK g c M ka := by
  intro _ g c M ⟨ka, hS, hF, hI, hC⟩
  classical
  let kaK : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ :=
    fun K _ _ x => Classical.choose (exists_descent g ka hF K x)
  have hK : ∀ (K : Type) [Field K] [CharZero K] (x : KeyIn K), x.P.g = g →
      ∀ (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (f : K →+* L) (xL : KeyIn L),
        KeyPB xL x f → (ka L xL : L) = f (kaK K x) :=
    fun K _ _ x => Classical.choose_spec (exists_descent g ka hF K x)
  refine ⟨kaK, ?_, ?_, ?_, ?_⟩
  ·
    intro K _ _ P hg rig hr th hth v hv th' hth' v' hv' a Mx hPg ha hM
    have : CharZero (AlgebraicClosure K) :=
      charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective
    obtain ⟨Q, hg₁, rig₁, hr₁, th₁, hth₁, v₁, hv₁, th₁', hth₁', v₁', hv₁', Mx₁, h1, h2, ha₁, hM₁, hdet⟩ :=
      exists_keyPB_pair (algebraMap K (AlgebraicClosure K)) P hg rig hr th hth v hv th' hth' v' hv' a Mx ha hM
    have hQ : Q.g = g := (g_eq h1).trans hPg
    have e1 := hK K ⟨P, hg, rig, hr, th, hth, v, hv⟩ hPg _ (algebraMap K _) _ h1
    have e2 := hK K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ hPg _ (algebraMap K _) _ h2
    have e3 := hS (AlgebraicClosure K) Q hg₁ rig₁ hr₁ th₁ hth₁ v₁ hv₁ th₁' hth₁' v₁' hv₁'
      (algebraMap K _ a) Mx₁ hQ ha₁ hM₁
    apply (algebraMap K (AlgebraicClosure K)).injective
    rw [map_mul, map_mul, map_pow, map_pow, ← e1, ← e2, ← hdet]
    exact e3
  ·
    intro K K' _ _ _ _ f x x' hx hx'
    have : CharZero (AlgebraicClosure K') :=
      charZero_of_injective_algebraMap (algebraMap K' (AlgebraicClosure K')).injective
    obtain ⟨xb, hxb⟩ := exists_keyPB_ring x' (algebraMap K' (AlgebraicClosure K'))
    have h1 := hK K' x' ((g_eq hx').trans hx) _ (algebraMap K' _) xb hxb
    have h2 := hK K x hx _ ((algebraMap K' (AlgebraicClosure K')).comp f) xb
      (keyPB_trans _ _ _ x x' xb f _ hx' hxb)
    apply (algebraMap K' (AlgebraicClosure K')).injective
    rw [← h1, h2]
    rfl
  ·
    intro R K _ _ _ _ _ _ _ x xK hx hMu hxK
    have : CharZero R := RingHom.charZero (algebraMap R K)
    obtain ⟨R', _, _, _, j, u, hj, hjl, hu⟩ := hI R x hx hMu

    let fΩ : R' →+* AlgebraicClosure (FractionRing R') :=
      (algebraMap (FractionRing R') (AlgebraicClosure (FractionRing R'))).comp (algebraMap R' (FractionRing R'))
    have hfΩ : Function.Injective fΩ :=
      (algebraMap (FractionRing R') (AlgebraicClosure (FractionRing R'))).injective.comp
        (IsFractionRing.injective R' (FractionRing R'))
    have hinj : Function.Injective (fΩ.comp j) := hfΩ.comp hj
    let h : K →+* AlgebraicClosure (FractionRing R') := IsFractionRing.lift hinj
    have hh : ∀ r : R, h (algebraMap R K r) = fΩ (j r) := fun r => IsFractionRing.lift_algebraMap hinj r
    have : CharZero (AlgebraicClosure (FractionRing R')) := charZero_of_injective_ringHom h.injective
    obtain ⟨xΩ, hxΩ⟩ := exists_keyPB_ring x (fΩ.comp j)
    have hc : h.comp (algebraMap R K) = fΩ.comp j := RingHom.ext hh
    have hxΩ' : KeyPB xΩ xK h :=
      GlobalTheory.KeyCancel.keyPB_cancel _ _ _ x xK xΩ (algebraMap R K) h hxK (by rw [hc]; exact hxΩ)
    have key : h (kaK K xK) = fΩ u :=
      (hK K xK ((g_eq hxK).trans hx) _ h xΩ hxΩ').symm.trans (hu _ fΩ xΩ hxΩ)

    obtain ⟨u₀, hy₀, hju₀⟩ : ∃ u₀ : Rˣ, algebraMap R K u₀ = kaK K xK ∧ j u₀ = u := by
      rcases ValuationRing.isInteger_or_isInteger R (kaK K xK : K) with ⟨r, hr⟩ | ⟨s, hs⟩
      · have hjr : j r = u := hfΩ (by rw [← hh, hr, key])
        have hru : IsUnit r := isUnit_of_map_unit j r (hjr ▸ u.isUnit)
        exact ⟨hru.unit, hr, hjr⟩
      · have hjs : j s = ((u⁻¹ : R'ˣ) : R') := by
          apply hfΩ
          rw [← hh, hs, map_inv₀, key]
          exact (map_units_inv fΩ u).symm
        have hsu : IsUnit s := isUnit_of_map_unit j s (hjs ▸ (u⁻¹).isUnit)
        refine ⟨hsu.unit⁻¹, ?_, ?_⟩
        · rw [map_units_inv, IsUnit.unit_spec, hs, inv_inv]
        · have hw : Units.map (j : R →* R') hsu.unit = u⁻¹ := Units.ext (by simpa using hjs)
          have hw' := congrArg (fun w : R'ˣ => ((w⁻¹ : R'ˣ) : R')) hw
          simpa using hw'
    refine ⟨u₀, hy₀.symm, ?_⟩
    intro k _ _ r xk hr hxk

    let f' : R' →+* AlgebraicClosure (IsLocalRing.ResidueField R') :=
      (algebraMap (IsLocalRing.ResidueField R') (AlgebraicClosure (IsLocalRing.ResidueField R'))).comp
        (IsLocalRing.residue R')
    have hker : RingHom.ker r ≤ RingHom.ker (f'.comp j) := by
      intro z hz
      rw [RingHom.mem_ker] at hz ⊢
      have hzn : ¬ IsUnit z := fun hzu => by
        have := hzu.map r
        rw [hz] at this
        exact not_isUnit_zero this
      have hjz : ¬ IsUnit (j z) := fun hu' => hzn (isUnit_of_map_unit j z hu')
      have : IsLocalRing.residue R' (j z) = 0 :=
        (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hjz)
      simp only [f', RingHom.comp_apply, this, map_zero]
    let e : k →+* AlgebraicClosure (IsLocalRing.ResidueField R') := (r.liftOfSurjective hr) ⟨f'.comp j, hker⟩
    have hcomp : e.comp r = f'.comp j := r.liftOfSurjective_comp hr ⟨f'.comp j, hker⟩
    have : CharZero (AlgebraicClosure (IsLocalRing.ResidueField R')) := charZero_of_injective_ringHom e.injective
    obtain ⟨xΩ', hxΩ''⟩ := exists_keyPB_ring x (f'.comp j)
    have hxk' : KeyPB xΩ' xk e :=
      GlobalTheory.KeyCancel.keyPB_cancel _ _ _ x xk xΩ' r e hxk (by rw [hcomp]; exact hxΩ'')
    have e2 := hK k xk ((g_eq hxk).trans hx) _ e xΩ' hxk'
    have e1 := hu _ f' xΩ' hxΩ''
    apply e.injective
    rw [← e2, e1, ← hju₀]
    exact (RingHom.congr_fun hcomp (u₀ : R)).symm
  ·
    intro a b hab
    obtain ⟨U, hU, hUx⟩ := hC a b hab
    refine ⟨U, hU, fun x h τ hN => ?_⟩
    have := hK ℂ x h ℂ (RingHom.id ℂ) x (keyPB_id ℂ x)
    rw [← hUx x h τ hN, this]
    rfl

end GlobalTheory.KeyGalDesc
