import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbPowDescendsOfIsotropic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EtaleOfTwistedBasis
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.ThetaLin

open GlobalTheory.CommPairing GlobalTheory.ThetaSplit ReciprocityTheory.ChartRestriction.G.H1

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem translT_mul [IsCommMonObj A] {T : Over S} (x y : T ⟶ A) :
    Out.translT A (x * y) = Out.translT A x ≫ Out.translT A y := by
  conv_rhs => rw [Out.translT, CommutatorPairing.lift_translT]
  rw [Out.translT]
  congr 1
  show (fst T A ≫ (x * y)) * snd T A = (fst T A ≫ y) * ((fst T A ≫ x) * snd T A)
  rw [MonObj.comp_mul, _root_.mul_assoc, mul_left_comm]

theorem translT_snd {T : Over S} (x : T ⟶ A) :
    (Out.translT A x).left ≫ (snd T A).left = (Out.translPt A x).left := by
  rw [← Over.comp_left, Out.translT, lift_snd]

theorem translT_translPt [IsCommMonObj A] {T : Over S} (x y : T ⟶ A) :
    (Out.translT A x).left ≫ (Out.translPt A y).left = (Out.translPt A (x * y)).left := by
  rw [← translT_snd (x * y), translT_mul, Over.comp_left, Category.assoc, translT_snd]

theorem exists_symm_cocycle (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) {k : ℤ}
    {T : Over S} {C : Type} [CommGroup C] (θ : C → Out.ThetaGrp A L k T)
    (hm : ∀ c c', (θ (c * c')).pt = (θ c).pt * (θ c').pt) (hc : ∀ c c', Out.CommIsOf A L k (θ c) (θ c') 1) :
    ∃ a : C → C → Γ(T.left, ⊤)ˣ, (∀ x y, a x y = a y x) ∧ (∀ x y z, a x y * a (x * y) z = a y z * a x (y * z)) ∧
      ∀ c c' (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
        tval (θ (c * c')) r z J = tval (θ c) r z J * tval (θ c') (r ≫ (Out.translT A (θ c).pt).left) z J *
          gm (r ≫ (fst T A).left) z ⊤ (a c c') := by
  have := hA.comm
  let e : T.left ⟶ (T ⊗ A).left := (lift (𝟙 T) 1).left
  have he : e ≫ (fst T A).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst]; rfl
  have ex : ∀ c c', ∃ a : Γ(T.left, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      tval (θ (c * c')) r z J = tval (θ c) r z J * tval (θ c') (r ≫ (Out.translT A (θ c).pt).left) z J *
          gm (r ≫ (fst T A).left) z ⊤ a := fun c c' => by
    obtain ⟨a, ha⟩ := CommutatorPairing.exists_ratio hL (fun U _ g => by
        refine Eq.trans ?_ (Fintype.prod_sum_type _).symm
        simp only [Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr]
        show g (snd T A).left ^ k * g (Out.translPt A (θ (c * c')).pt).left ^ (-k) =
          g (snd T A).left ^ k * g (Out.translPt A (θ c).pt).left ^ (-k) *
            (g ((Out.translT A (θ c).pt).left ≫ (snd T A).left) ^ k *
              g ((Out.translT A (θ c).pt).left ≫ (Out.translPt A (θ c').pt).left) ^ (-k))
        rw [translT_snd, translT_translPt, hm]
        simp only [zpow_neg, _root_.mul_assoc, inv_mul_cancel_left]) (fst T A).left e he (surj_fst hG hA T)
      (θ (c * c')).isGen
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (θ c).isGen
        (DVR.pullGen_isGen _ _ _ _ (θ c').isGen (Out.translT A (θ c).pt).left))
    exact ⟨a, fun Z r z J hJ => (ha Z r z J hJ).trans (congrArg (· * _) ((val_mul hJ _ _ _).trans
      (congrArg (tval (θ c) r z J * ·) (val_pull hJ _ _ _))))⟩
  choose a ha using ex
  have inj : ∀ u u' : Γ(T.left, ⊤)ˣ, (∀ (y : T.left) (J), Good L y J →
      gm (e ≫ (fst T A).left) y ⊤ u = gm (e ≫ (fst T A).left) y ⊤ u') → u = u' :=
    fun u u' h => unit_ext fun y _ => by
      choose J hJ using fun χ : T.left ⟶ A.left => exists_chart hL (χ y)
      rw [← he]; exact h y J hJ
  refine ⟨a, fun c c' => inj _ _ fun y J hJ => ?_, fun c c' c'' => inj _ _ fun y J hJ => ?_, ha⟩
  · have e₁ := ha c c' _ e y J hJ
    have e₂ := ha c' c _ e y J hJ
    have e₃ := (commIsOf_iff hL _ _ _).1 (hc c c') _ e y J hJ
    rw [map_one, _root_.mul_one] at e₃
    rw [e₃] at e₁
    rw [mul_comm c' c, e₁] at e₂
    exact mul_left_cancel e₂
  · have e₁ := ha c c' _ e y J hJ
    have e₂ := ha (c * c') c'' _ e y J hJ
    have e₃ := ha c' c'' _ (e ≫ (Out.translT A (θ c).pt).left) y J hJ
    have e₄ := ha c (c' * c'') _ e y J hJ
    rw [_root_.mul_assoc c] at e₂
    rw [Category.assoc, Category.assoc, translT_fst, ← Over.comp_left _ _ _ (Out.translT A (θ c).pt), ← translT_mul, ← hm] at e₃
    rw [map_mul, map_mul]
    apply Additive.ofMul.injective
    have a₁ := congrArg Additive.ofMul e₁
    have a₂ := congrArg Additive.ofMul e₂
    have a₃ := congrArg Additive.ofMul e₃
    have a₄ := congrArg Additive.ofMul e₄
    simp only [ofMul_mul] at a₁ a₂ a₃ a₄ ⊢
    linear_combination (norm := abel) a₃ + a₄ - a₁ - a₂

theorem exists_linearisation {L : LB A.left} (hL : L.IsLB) (n : ℕ) {T : Over S} {C : Type} [CommGroup C]
    (θ : C → Out.ThetaGrp A L n T) (a : C → C → Γ(T.left, ⊤)ˣ)
    (ha : ∀ c c' (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
        tval (θ (c * c')) r z J = tval (θ c) r z J * tval (θ c') (r ≫ (Out.translT A (θ c).pt).left) z J *
          gm (r ≫ (fst T A).left) z ⊤ (a c c'))
    {S' : Scheme.{0}} {A' : Over S'} [GrpObj A'] [IsCommMonObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (hp : IsGrpPullback A' A f φ) {L' : LB A'.left} (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ))
    (τ : S' ⟶ T.left) (hτ : τ ≫ T.hom = f) (i' : C →* (𝟙_ (Over S') ⟶ A'))
    (hi : ∀ c, τ ≫ (θ c).pt.left = (i' c).left ≫ φ) (b : C → Γ(S', ⊤)ˣ)
    (hb : ∀ c c', Units.map τ.appTop.hom.toMonoidHom (a c c') * b (c * c') = b c * b c') :
    ∃ u : ∀ c, LB.Gen (LB.LinComb (lbPow L' n) (K := Fin 2) ![𝟙 A'.left, transl (i' c)] ![1, -1]),
      (∀ c, (u c).IsGen) ∧ ∀ c c', LB.Gen.Corr (lbPow L' n) _ _ _ _ (u (c * c'))
        (LB.mulGen (lbPow L' n) _ _ _ _ (u c) (LB.pullGen (lbPow L' n) _ _ (u c') (transl (i' c)))) := by
  obtain ⟨w, hw⟩ := hw
  have hτ' : (τ : (𝟙_ (Over S')).left ⟶ T.left) ≫ T.hom = (𝟙_ (Over S')).hom ≫ f :=
    hτ.trans (Category.id_comp _).symm
  choose θ' hθ' hR using fun c => WeilPull.exists_rel_down hp (T := 𝟙_ (Over S')) τ hτ' hL hL' w hw (i' c) (θ c) (hi c)
  have key : ∀ c c' (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S') ⊗ A').left) (z : Z) (J), Good L' z J →
      tval (θ' (c * c')) r z J = tval (θ' c) r z J * tval (θ' c') (r ≫ (Out.translT A' (i' c)).left) z J *
        gm ((r ≫ (fst _ A').left) ≫ τ) z ⊤ (a c c') := fun c c' Z r z J hJ => by
    choose J₀ hJ₀ using fun ψ : Z ⟶ A.left => exists_chart hL (ψ z)
    have e := ha c c' Z (r ≫ (psiO hp (T := 𝟙_ (Over S')) τ hτ').left) z J₀ hJ₀
    have t : (r ≫ (psiO hp (T := 𝟙_ (Over S')) τ hτ').left) ≫ (Out.translT A (θ c).pt).left =
        (r ≫ (Out.translT A' (i' c)).left) ≫ (psiO hp (T := 𝟙_ (Over S')) τ hτ').left := by
      rw [Category.assoc, Category.assoc, psi_transl hp (T := 𝟙_ (Over S')) τ hτ' _ _ (hi c)]
    have g : (r ≫ (psiO hp (T := 𝟙_ (Over S')) τ hτ').left) ≫ (fst T A).left = (r ≫ (fst _ A').left) ≫ τ := by
      rw [Category.assoc, psi_fst, Category.assoc]
    have s : (r ≫ (Out.translT A' (i' c)).left) ≫ (snd _ A').left = r ≫ (Out.translPt A' (i' c)).left := by
      rw [Category.assoc, translT_snd]
    have q : (r ≫ (Out.translT A' (i' c)).left) ≫ (Out.translPt A' (i' c')).left =
        r ≫ (Out.translPt A' (i' (c * c'))).left := by
      rw [Category.assoc, translT_translPt, map_mul]
    rw [t, g, hR _ Z _ z J₀ J hJ₀ hJ, hR _ Z _ z J₀ J hJ₀ hJ, hR _ Z _ z J₀ J hJ₀ hJ, hθ', hθ', hθ', s, q] at e
    simp only [zpow_neg] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  choose v hv ev using fun c => exists_gen_theta hL' (θ' c) (hθ' c)
  choose u hu eu using fun c => exists_gen_lbPow n (ε := ![1, -1]) (fun k => by fin_cases k <;> simp) (v c) (hv c)
    (pullU A'.hom ⊤ (b c))
  refine ⟨u, hu, fun c c' => corr_of_val (DVR.linComb_isLB L' hL' _ _) fun y J hJ => ?_⟩
  have hJ' : Good L' y (fun χ => J χ PUnit.unit) := fun χ => Set.mem_iInter.1 (hJ χ) PUnit.unit
  have g : ∀ (r : A'.left ⟶ A'.left) (a : Γ(S', ⊤)ˣ), gm r y ⊤ (pullU A'.hom ⊤ a) = gm (r ≫ A'.hom) y ⊤ a :=
    fun r a => gm_pull r A'.hom y ⊤ trivial a
  refine Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg (val (u c) (𝟙 _) y J * ·) (val_pull hJ _ _ _))).symm
  rw [eu _ _ _ y J hJ, eu _ _ _ y J hJ, eu _ _ _ y J hJ, g, g, g, Category.assoc, transl_hom,
    ev _ _ _ y _ hJ', ev _ _ _ y _ hJ', ev _ _ _ y _ hJ', key c c' _ _ y _ hJ']
  have f₁ : (𝟙 A'.left ≫ (lift (toUnit A') (𝟙 A')).left) ≫ (fst _ A').left = 𝟙 A'.left ≫ A'.hom := by
    rw [Category.assoc, ← Over.comp_left, lift_fst]; rfl
  have f₂ : (𝟙 A'.left ≫ (lift (toUnit A') (𝟙 A')).left) ≫ (Out.translT A' (i' c)).left =
      (𝟙 A'.left ≫ transl (i' c)) ≫ (lift (toUnit A') (𝟙 A')).left := by
    rw [Category.assoc, Category.assoc, transl_lift]
  have f₃ := gm_pull (𝟙 A'.left ≫ A'.hom) τ y ⊤ trivial (a c c')
  have f₄ := congrArg (gm (𝟙 A'.left ≫ A'.hom) y ⊤) (hb c c')
  rw [map_mul, map_mul] at f₄
  rw [f₁, f₂, _root_.mul_assoc]
  exact (congrArg (_ * ·) ((congrArg (· * _) f₃.symm).trans f₄)).trans (_root_.mul_mul_mul_comm _ _ _ _)

theorem exists_lifts_away {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {k : ℤ}
    {C : Type} [Finite C] (x : C → (𝟙_ (Over (Sp R)) ⟶ A)) (q : PrimeSpectrum R)
    (hW : ∀ c, Out.WeilIs A L k (x c) (x c) 1) :
    ∃ r : R, r ∉ q.asIdeal ∧ ∀ c, ∃ θ : Out.ThetaGrp A L k (Over.mk (spMap (algebraMap R (Localization.Away r)))),
      θ.pt = toUnit _ ≫ x c := by
  choose V hV hθ using fun c => hW c q
  have ho : IsOpen (X := PrimeSpectrum R) (⋂ c, (V c).1) := isOpen_iInter_of_finite fun c => (V c).2
  obtain ⟨_, ⟨r, rfl⟩, hr, hle⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (Set.mem_iInter.2 hV) ho
  refine ⟨r, hr, fun c => ?_⟩
  obtain ⟨⟨θ, -, e, -⟩, -⟩ := hθ c
  have hsub : Set.range (spMap (algebraMap R (Localization.Away r))) ⊆ Set.range (V c).ι := by
    rintro _ ⟨p, rfl⟩
    have : PrimeSpectrum.comap (algebraMap R (Localization.Away r)) p ∈
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]; exact ⟨p, rfl⟩
    exact ⟨⟨_, Set.mem_iInter.1 (hle this) c⟩, rfl⟩
  let h : Over.mk (spMap (algebraMap R (Localization.Away r))) ⟶ Out.overRes (V c) :=
    Over.homMk (IsOpenImmersion.lift (V c).ι _ hsub) (by
      show IsOpenImmersion.lift (V c).ι _ hsub ≫ (V c).ι ≫ 𝟙 _ = _
      rw [Category.comp_id, IsOpenImmersion.lift_fac]; rfl)
  obtain ⟨θ', e', -⟩ := exists_pull hL h θ
  exact ⟨θ', by rw [e', e, ← Category.assoc, toUnit_unique (h ≫ _) (toUnit _)]⟩

end GlobalTheory.ThetaLin

namespace GlobalTheory

open ThetaLin in

theorem exists_etale_linearisation : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (n : ℕ) (C : Type) [CommGroup C] [Finite C] (i : C →* (𝟙_ (Over (Sp R)) ⟶ P.A)) (q : PrimeSpectrum R), IsUnit (n : R) → 0 < n → (∀ c : C, c ^ n = 1) → (∀ c c', Out.WeilIs P.A P.L n (i c) (i c') 1) → ∃ (R' : Type) (_ : CommRing R') (_ : Algebra R R'), Algebra.Etale R R' ∧ q ∈ Set.range (PrimeSpectrum.comap (algebraMap R R')) ∧ ∀ (A' : Over (Sp R')) [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ P.A.left) (L' : LB A'.left) (i' : C →* (𝟙_ (Over (Sp R')) ⟶ A')), IsGrpPullback A' P.A (spMap (algebraMap R R')) φ → L'.IsLB → LBIso L' (P.L.pull φ) → (∀ c, (i' c).left ≫ φ = spMap (algebraMap R R') ≫ (i c).left) → ∃ u : ∀ c : C, LB.Gen (LB.LinComb (lbPow L' n) (K := Fin 2) ![𝟙 A'.left, ((toUnit A' ≫ i' c) * 𝟙 A').left] ![1, -1]), (∀ c, (u c).IsGen) ∧ ∀ c c', LB.Gen.Corr (lbPow L' n) _ _ _ _ (u (c * c')) (LB.mulGen (lbPow L' n) _ _ _ _ (u c) (LB.pullGen (lbPow L' n) _ _ (u c') ((toUnit A' ≫ i' c) * 𝟙 A').left)) := by
  intro R _ P n C _ _ i q hnR hn htor hW
  have hG := GlobalTheory.globalFns_holds
  have := P.isAb.comm
  obtain ⟨r, hr, hθ⟩ := exists_lifts_away P.isLB (fun c => i c) q (fun c => hW c c)
  choose θ hθ using hθ
  let R₁ := Localization.Away r
  obtain ⟨a, hs, hc, ha⟩ := exists_symm_cocycle hG P.isAb P.isLB θ
    (fun c c' => by rw [hθ, hθ, hθ, map_mul, MonObj.comp_mul]) (fun c c' => by
      refine (GlobalLift.weilIs_iff_commIsOf hG P.isAb P.isLB _ _ _).1 ?_
      have H := CommPairing.weilIs_pull hG P.isAb P.isLB (toUnit (Over.mk (spMap (algebraMap R R₁)))) (hW c c')
      rw [map_one] at H
      rw [hθ, hθ]; exact H)
  let e₁ : Γ(Sp R₁, ⊤) ≃+* R₁ := (Scheme.ΓSpecIso (CommRingCat.of R₁)).commRingCatIsoToRingEquiv
  let E₁ : Γ(Sp R₁, ⊤)ˣ →* R₁ˣ := Units.map e₁.toRingHom.toMonoidHom
  obtain ⟨R', _, _, het, -, hff, b, hb⟩ := GlobalTheory.CocycleSplit.exists_etale_splitting R₁ n C (fun x y => E₁ (a x y))
    (by simpa using hnR.map (algebraMap R R₁)) hn htor (fun x y => congrArg E₁ (hs x y))
    (fun x y z => (map_mul E₁ _ _).symm.trans ((congrArg E₁ (hc x y z)).trans (map_mul E₁ _ _)))
  letI : Algebra R R' := ((algebraMap R₁ R').comp (algebraMap R R₁)).toAlgebra
  have : IsScalarTower R R₁ R' := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.Etale R R₁ := Algebra.Etale.of_isLocalizationAway r
  refine ⟨R', inferInstance, inferInstance, Algebra.Etale.comp R R₁ R', ?_, ?_⟩
  · have h₁ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap R R₁)) := by
      rw [PrimeSpectrum.localization_away_comap_range R₁ r]; exact hr
    obtain ⟨p, rfl⟩ := h₁
    obtain ⟨p', rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R₁) (B := R') p
    exact ⟨p', rfl⟩
  · intro A' _ _ φ L' i' hp hL' hw hi
    have hτ : spMap (algebraMap R₁ R') ≫ spMap (algebraMap R R₁) = spMap (algebraMap R R') := by
      rw [← Spec.map_comp]; rfl
    let e' : Γ(Sp R', ⊤) ≃+* R' := (Scheme.ΓSpecIso (CommRingCat.of R')).commRingCatIsoToRingEquiv
    refine exists_linearisation P.isLB n θ a ha hp hL' hw (spMap (algebraMap R₁ R')) hτ i' (fun c => ?_)
      (fun c => Units.map e'.symm.toRingHom.toMonoidHom (b c)) (fun c c' => ?_)
    · rw [hθ, hi, ← hτ, Category.assoc]; rfl
    · rw [← map_mul, ← hb, map_mul]
      congr 1
      apply Units.ext
      apply e'.injective
      have := congrArg (fun g => g.hom (a c c').val)
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R₁ R')))
      exact this.trans (e'.apply_symm_apply _).symm

end GlobalTheory
