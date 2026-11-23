import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActMatApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageFiniteProjective

set_option autoImplicit false

noncomputable section

open CategoryTheory NumberField WithConv
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.RingChain
open GlobalTheory.GroupBplus (IsPropG TorsionMap dualVec)
open scoped TensorProduct Pointwise

namespace GlobalTheory.ChainPts.SysB.RingRes

section Rings

variable {A A' R : Type} [CommRing A] [CommRing A'] [CommRing R]

theorem exists_completion_map (p : ℕ) (φ : A →+* A') :
    ∃ g : AdicCompletion (Ideal.span {(p : A)}) A →+* AdicCompletion (Ideal.span {(p : A')}) A',
      ∀ a, g (algebraMap A _ a) = algebraMap A' _ (φ a) := by
  let I : Ideal A := Ideal.span {(p : A)}
  let J : Ideal A' := Ideal.span {(p : A')}
  have hle : ∀ n : ℕ, I ^ n ≤ (J ^ n).comap φ := fun n => by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast]
  let g : ∀ n : ℕ, AdicCompletion I A →+* A' ⧸ J ^ n := fun n =>
    (Ideal.quotientMap (J ^ n) φ (hle n)).comp (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n)
  have hg : ∀ {m n : ℕ} (h : m ≤ n), (Ideal.Quotient.factorPow J h).comp (g n) = g m := by
    intro m n h
    refine RingHom.ext fun x => ?_
    obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective I A x
    simp only [g, RingHom.comp_apply, RingHom.coe_coe]
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, ← AdicCompletion.Ideal.mk_eq_mk I h x]
    rfl
  refine ⟨AdicCompletion.liftRingHom J g hg, fun b => AdicCompletion.ext_evalₐ fun n => ?_⟩
  rw [AdicCompletion.evalₐ_liftRingHom]
  change Ideal.quotientMap (J ^ n) φ (hle n) (AdicCompletion.evalₐ I n (algebraMap A _ b)) = _
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
  rfl

theorem modIso_completion [Algebra A R] {q : A} (ec : AdicCompletion (Ideal.span {q}) A ≃+* R)
    (he : ∀ a, ec (algebraMap A _ a) = algebraMap A R a) {a : A} (ha : a ∣ q) : ModIso R a := by
  obtain ⟨t, ht⟩ := ha
  refine ⟨fun r => ?_, fun x ⟨r, hr⟩ => ?_⟩
  · obtain ⟨x, y, hy⟩ := LatDescent.adic_surj A q (ec.symm r)
    have h1 := congrArg ec hy
    rw [ec.apply_symm_apply, map_add, map_mul, he, he] at h1
    exact ⟨x, algebraMap A R t * ec y, by rw [h1, ← mul_assoc, ← map_mul, ← ht]; ring⟩
  · obtain ⟨x', y, hy⟩ := LatDescent.adic_surj A q (ec.symm r)
    obtain ⟨b, hb⟩ := LatDescent.adic_inj A q (x - a * x') (algebraMap A _ a * y) (ec.injective (by
      have h1 := congrArg ec hy
      rw [ec.apply_symm_apply, map_add, map_mul, he, he] at h1
      rw [map_mul, map_mul, he, he, he, map_sub, map_mul, hr, h1]; ring))
    exact ⟨x' + t * b, by rw [mul_add, ← mul_assoc, ← ht, ← hb]; ring⟩

theorem mv_one (φ : A →+* A') {h : ℕ} (x : Fin h → A) : mv φ 1 x = fun i => φ (x i) := by
  rw [mv, Matrix.map_one _ Int.cast_zero Int.cast_one, Matrix.one_mulVec]

theorem of_isUnit {p h o : ℕ} {π : A} {γ : ℕ → A} {Lie Om : Type} [AddCommGroup Lie] [Module A Lie] [AddCommGroup Om]
    [Module A Om] {π' : A'} {γ' : ℕ → A'} {Lie' Om' : Type} [AddCommGroup Lie'] [Module A' Lie'] [AddCommGroup Om']
    [Module A' Om'] (C : RChain p A h o π γ Lie Om) (C' : RChain p A' h o π' γ' Lie' Om') (φ : A →+* A') (l : Lie → Lie')
    (m : Om → Om') (hp : IsUnit (p : A')) (hd : π ∣ (p : A)) (hπ : π' = φ π) :
    (∀ k, C'.L k = Submodule.span A' (piMap φ (Fin h) '' (C.L k : Set (Fin h → A)))) ∧ C.Map C' φ 1 l m := by
  have hu : IsUnit π' := isUnit_of_dvd_unit (by rw [hπ, ← map_natCast φ]; exact map_dvd φ hd) hp
  have top : ∀ (M : Type) [AddCommGroup M] [Module A' M] (u : A'), IsUnit u → ∀ x : M, x ∈ u • (⊤ : Submodule A' M) := by
    rintro M _ _ _ ⟨u, rfl⟩ x
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨(↑u⁻¹ : A') • x, trivial, by rw [smul_smul]; simp⟩
  have hL : ∀ k x, x ∈ C'.L k := fun k x => C'.base_le k (top _ _ hu x)
  have hQ : ∀ k, Subsingleton (Qt (C'.L k) (baseOf π' h)) := fun k =>
    Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun x _ => top _ _ hu x.1)
  have hK : Subsingleton (Lie' ⧸ (p : A') • (⊤ : Submodule A' Lie')) :=
    Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun x _ => top _ _ hp x)
  refine ⟨fun k => le_antisymm (fun x _ => ?_) fun x _ => hL k x, fun n x _ => hL n _, fun _ _ _ _ _ => Subsingleton.elim _ _,
    fun _ _ _ _ _ => Subsingleton.elim _ _, fun _ _ _ _ _ _ _ _ _ => Subsingleton.elim _ _,
    fun _ _ _ _ _ _ _ => Subsingleton.elim _ _⟩
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 (top _ _ hu x)
  rw [pi_eq_sum_univ' y, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [smul_comm]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨π • Pi.single i 1,
    C.base_le k (Submodule.smul_mem_pointwise_smul _ _ _ trivial), funext fun j => ?_⟩)
  simp [hπ, Pi.single_apply, apply_ite φ]

end Rings

section Groups

variable {p : ℕ} [Fact p.Prime] {A A' : Type} [CommRing A] [CommRing A'] {GG : PDivGroup p A} {GG' : PDivGroup p A'}

theorem char_ext {χ ψ : GG.dual.Tate} (h : ∀ n, charElem χ n = charElem ψ n) : χ = ψ :=
  TateOver.ext (funext fun n => AlgHom.ext fun φ => by rw [← apply_charElem, ← apply_charElem, h])

theorem omegaMap_bijective {G H : PDivGroup p A} (e : G ≅ H) : Function.Bijective (omegaMap _ _ e.hom) :=
  Function.bijective_iff_has_inverse.2 ⟨omegaMap _ _ e.inv,
    fun x => by rw [← LinearMap.comp_apply, ← omegaMap_comp, e.inv_hom_id, omegaMap_id, LinearMap.id_apply],
    fun x => by rw [← LinearMap.comp_apply, ← omegaMap_comp, e.hom_inv_id, omegaMap_id, LinearMap.id_apply]⟩

theorem omegaMap_polBC_bijective (pol : GG ≅ GG.dual) (R : Type) [CommRing R] [Algebra A R] :
    Function.Bijective (omegaMap _ _ (polBC pol R)) :=
  omegaMap_bijective ((baseChangeFunctor p A R).mapIso pol ≪≫ (dualBaseChange R GG).symm)

theorem hodgeTate_bcTate (R : Type) [CommRing R] [Algebra A R] (t : GG.Tate) :
    omegaMap _ _ (dualBaseChange R GG).inv (hodgeTate _ (bcTate R t)) = (GG.dual.toBase R).omega (hodgeTate GG t) :=
  Subtype.ext (funext fun n => by
    rw [omegaMap_val, hodgeTate_val, cotMap_d, SemiHom.omega_val, hodgeTate_val, SemiBialgHom.cot_d, toBase_app]
    refine congrArg _ ((CartierDual.baseChange A R (GG.A n)).injective ?_)
    refine ((CartierDual.baseChange A R (GG.A n)).apply_symm_apply _).trans (CartierDual.ext_apply fun x => ?_)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r a =>
      refine Eq.trans ?_ (CartierDual.baseChange_tmul_tmul _ _ _ _ _).symm
      change r * algebraMap A R (t.pt n a) = _
      simp [Algebra.smul_def, mul_comm])

theorem omegaMap_polBC_hodgeTate (pol : GG ≅ GG.dual) (skew : GG.bidual.hom ≫ dualHom GG GG.dual pol.hom = -pol.hom)
    (R : Type) [CommRing R] [Algebra A R] (t : GG.Tate) :
    omegaMap _ _ (polBC pol R) (hodgeTate _ (bcTate R t)) = -dlog _ (bcChar R (tateMap _ _ A pol.hom t)) := by
  rw [polBC, omegaMap_comp, LinearMap.comp_apply, hodgeTate_bcTate,
    ← (GG.toBase R).omega_naturality (GG.dual.toBase R) pol.hom _ (fun _ _ => rfl), hodgeTate_apply, ← dlog_tateMap,
    ← tateMap_comp, skew, map_neg, LinearMap.neg_apply, map_neg, map_neg, dlog_bcChar]

variable [Algebra A A'] (f : GG' ≅ GG.baseChange A')

theorem charElem_pol (pol : GG ≅ GG.dual) (pol' : GG' ≅ GG'.dual)
    (hpol : pol'.hom ≫ dualHom _ _ f.inv ≫ (dualBaseChange A' GG).hom = f.hom ≫ PDivGroup.baseChangeMap A' pol.hom)
    {t : GG.Tate} {t' : GG'.Tate} (ht : tateMap _ _ A' f.hom t' = bcTate A' t) (n : ℕ) :
    charElem (tateMap _ _ A' pol'.hom t') n = f.hom.app n (1 ⊗ₜ charElem (tateMap _ _ A pol.hom t) n) := by
  have h1 : tateMap _ _ A' (dualBaseChange A' GG).hom (bcChar A' (tateMap GG GG.dual A pol.hom t)) =
      tateMap _ _ A' (dualBaseChange A' GG).hom (tateMap _ _ A' (pol'.hom ≫ dualHom _ _ f.inv) t') := by
    rw [tateMap_dualBaseChange, ← tateMap_bcTate, ← ht, ← tateMap_comp, ← tateMap_comp, Category.assoc, hpol]
  have h2 := congrArg (tateMap _ _ A' (dualBaseChange A' GG).inv) h1
  rw [← tateMap_comp, ← tateMap_comp, Iso.hom_inv_id, tateMap_id, tateMap_id] at h2
  rw [← charElem_bcChar, h2, ← charElem_tateMap, ← tateMap_comp, Category.assoc, ← dualHom_comp, Iso.hom_inv_id, dualHom_id,
    Category.comp_id]

omit [Fact p.Prime] in

theorem exists_square (R R' : Type) [CommRing R] [CommRing R'] [Algebra A R] [Algebra A' R'] [Algebra R R']
    (hσ : ∀ a, algebraMap R R' (algebraMap A R a) = algebraMap A' R' (algebraMap A A' a)) :
    ∃ (s : SemiHom (algebraMap R R') (GG'.baseChange R') (GG.baseChange R))
      (F : (GG.baseChange R).baseChange R' ⟶ GG'.baseChange R'), IsIso F ∧
      (∀ n a, s.app n (1 ⊗ₜ a) = 1 ⊗ₜ f.hom.app n (1 ⊗ₜ a)) ∧
      ∀ n a, F.app n (1 ⊗ₜ f.hom.app n (1 ⊗ₜ a)) = 1 ⊗ₜ (1 ⊗ₜ a) := by
  let s : SemiHom (algebraMap R R') (GG'.baseChange R') (GG.baseChange R) :=
    ((GG'.toBase R').comp ((SemiHom.ofHom f.hom).comp (GG.toBase A'))).liftOver _ fun a => (hσ a).symm
  have hs : ∀ n r a, s.app n (r ⊗ₜ a) = algebraMap R R' r • (1 : R') ⊗ₜ[A'] f.hom.app n (1 ⊗ₜ a) := fun n r a =>
    SemiHom.liftOver_app _ _ _ n r a
  let k₀ : SemiHom (algebraMap A' R') ((GG.baseChange R).baseChange R') (GG.baseChange A') :=
    (((GG.baseChange R).toBase R').comp (GG.toBase R)).liftOver _ hσ
  have hk : ∀ n r a, k₀.app n (r ⊗ₜ a) = algebraMap A' R' r • (1 : R') ⊗ₜ[R] ((1 : R) ⊗ₜ[A] a) := fun n r a =>
    SemiHom.liftOver_app _ _ _ n r a
  have hF : ∀ n a, (k₀.lift ≫ PDivGroup.baseChangeMap R' f.inv).app n (1 ⊗ₜ f.hom.app n (1 ⊗ₜ a)) = 1 ⊗ₜ (1 ⊗ₜ a) :=
    fun n a => by
      change k₀.lift.app n (1 ⊗ₜ (f.inv ≫ f.hom).app n (1 ⊗ₜ a)) = _
      rw [f.inv_hom_id]
      exact (k₀.lift_app n 1 (1 ⊗ₜ a)).trans ((one_smul _ _).trans ((hk n 1 a).trans (by rw [map_one, one_smul])))
  refine ⟨s, k₀.lift ≫ PDivGroup.baseChangeMap R' f.inv, ⟨s.lift, baseChange_hom_ext fun n y => ?_,
    baseChange_hom_ext fun n y => ?_⟩, fun n a => (hs n 1 a).trans (by rw [map_one, one_smul]), hF⟩
  · change (k₀.lift ≫ PDivGroup.baseChangeMap R' f.inv).app n (s.lift.app n (1 ⊗ₜ y)) = 1 ⊗ₜ y
    rw [SemiHom.lift_app, one_smul]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
    | tmul r a =>
      rw [hs, map_smul, hF, algebraMap_smul, ← TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  · have key : ∀ x, s.lift.app n (k₀.app n x) = 1 ⊗ₜ f.hom.app n x := fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
      | tmul r a =>
        rw [hk, map_smul, SemiHom.lift_app, one_smul, hs, map_one, one_smul, algebraMap_smul, ← TensorProduct.tmul_smul,
          ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    change s.lift.app n (k₀.lift.app n (1 ⊗ₜ f.inv.app n y)) = 1 ⊗ₜ y
    rw [SemiHom.lift_app, one_smul, key]
    change 1 ⊗ₜ (f.hom ≫ f.inv).app n y = _
    rw [f.hom_inv_id]
    rfl

theorem omega_square {R R' : Type} [CommRing R] [CommRing R'] [Algebra A R] [Algebra A' R'] {σ : R →+* R'}
    (s : SemiHom σ (GG'.baseChange R') (GG.baseChange R)) (hs : ∀ n a, s.app n (1 ⊗ₜ a) = 1 ⊗ₜ f.hom.app n (1 ⊗ₜ a))
    (w : GG.omega) :
    s.omega ((GG.toBase R).omega w) = (GG'.toBase R').omega (omegaMap _ _ f.hom ((GG.toBase A').omega w)) :=
  Subtype.ext (funext fun k => by
    obtain ⟨a, ha⟩ := AugCot.d_surjective _ (w.1 k)
    have ha' : dUnit A a = w.1 k := ha
    rw [SemiHom.omega_val, SemiHom.omega_val, SemiHom.omega_val, omegaMap_val, SemiHom.omega_val, ← ha', SemiBialgHom.cot_d,
      SemiBialgHom.cot_d, SemiBialgHom.cot_d, cotMap_d, SemiBialgHom.cot_d, toBase_app, toBase_app, toBase_app, hs])

end Groups

theorem dualVec_reindex {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {J J' : Type}
    (b : Module.Basis J ℤ Dw.La) (e : J ≃ J') (j : J) : dualVec (b.reindex e) (e j) = dualVec b j := by
  have h : (b.reindex e).coord (e j) = b.coord j := LinearMap.ext fun x => by simp
  exact congrArg (fun u => -(Dw.unimod.2 u).choose) h

set_option maxHeartbeats 400000 in

theorem ringRes (hM : GlobalTheory.RingChain.MapSt) : GlobalTheory.ChainPts.SysB.RingResSt := by
  intro E _ _ _ H Dw p _ D A A' _ _ _ t GG act pol θ ε τ hP t' GG' act' pol' θ' ε' τ' hP' n o e e' b π γ π' γ' Lie Om Lie' Om'
    _ _ _ _ _ _ _ _ cω pr cω' pr' C C' f l m hC hC' hε hpol hτ hω hpr hd hπ
  by_cases hp' : IsUnit (p : A')
  · exact of_isUnit C C' _ l m hp' hd hπ
  have hp : ¬ IsUnit (p : A) := fun h => hp' (map_natCast (algebraMap A A') p ▸ h.map _)
  obtain ⟨S, _, ec, hec, kε, eL, eO, hL, hO, hI⟩ := hC hp
  obtain ⟨S', _, ec', hec', kε', eL', eO', hL', hO', hI'⟩ := hC' hp'
  obtain ⟨g, hg⟩ := exists_completion_map p (algebraMap A A')
  letI : Algebra S.R S'.R := (ec'.toRingHom.comp (g.comp ec.symm.toRingHom)).toAlgebra
  have hσ : ∀ a, algebraMap S.R S'.R (algebraMap A S.R a) = algebraMap A' S'.R (algebraMap A A' a) := fun a => by
    change ec' (g (ec.symm _)) = _
    rw [← hec, ec.symm_apply_apply, hg, hec']
  obtain ⟨s, F, hF, hs, hF'⟩ := exists_square f S.R S'.R hσ
  have hz : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.zeta S'.ε k = algebraMap S.R S'.R (GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.zeta S.ε k) := fun k => by
    rw [← muRoot_eps, ← muRoot_eps, kε, kε', hε, hσ]
  have hch := fun x => charElem_pol f pol pol' hpol (hτ x)
  have hdl : ∀ x, s.omega (dlog _ (bcChar S.R (tateMap _ _ A pol.hom (τ x)))) =
      dlog _ (bcChar S'.R (tateMap _ _ A' pol'.hom (τ' x))) := fun x => Subtype.ext (funext fun k => by
    rw [SemiHom.omega_val, dlog_val, dlog_val, SemiBialgHom.cot_d, charElem_bcChar, charElem_bcChar, hs, hch])
  have hom : ∀ w, s.omega ((GG.toBase S.R).omega (cω w)) = (GG'.toBase S'.R).omega (cω' (m w)) := fun w => by
    rw [hω, omega_square f s hs]
  have hlie : ∀ y u, eL' (1 ⊗ₜ l y) (s.omega u) = algebraMap S.R S'.R (eL (1 ⊗ₜ y) u) := fun y u => by
    obtain ⟨u, rfl⟩ := (omegaMap_polBC_bijective pol S.R).2 u
    obtain ⟨u, rfl⟩ := eO.surjective u
    induction u using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add u v hu hv => simp only [map_add, hu, hv]
    | tmul r w =>
      rw [← mul_one r, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, map_smul, hO, map_smulₛₗ, map_smul, map_smul,
        hom, hL, hL', hpr, smul_eq_mul, smul_eq_mul, map_mul, hσ]
  have ht' : ∀ j, (ct hP e b).t' (Fin.cast e.symm j) = tateMap _ _ A pol.hom (τ (dualVec b j)) := fun j =>
    congrArg (fun x => tateMap _ _ A pol.hom (τ x)) (dualVec_reindex b (finCongr e.symm) j)
  have ht'' : ∀ j, (ct hP' e' b).t' (Fin.cast e'.symm j) = tateMap _ _ A' pol'.hom (τ' (dualVec b j)) := fun j =>
    congrArg (fun x => tateMap _ _ A' pol'.hom (τ' x)) (dualVec_reindex b (finCongr e'.symm) j)
  have key := hM p D S S' _ _ _ _ A A' (algebraMap A A') n o e e' π π' γ γ' Lie Om Lie' Om' _ _ _ _ C C' F 1 l m hI hI'
    hσ hz
  refine (key (fun j => ?_) (fun y j => ?_) fun w x hx => ?_).elim fun h1 h2 => ⟨h2 hF rfl hπ.symm
    (modIso_completion ec hec hd)
    (modIso_completion ec' hec' (by rw [hπ, ← map_natCast (algebraMap A A')]; exact map_dvd _ hd)), h1⟩
  · rw [Finset.sum_eq_single j (fun i _ hi => by rw [Matrix.one_apply_ne' hi, zero_smul]) (fun h => absurd (Finset.mem_univ _) h),
      Matrix.one_apply_eq, one_smul]
    refine char_ext fun k => ?_
    change charElem (tateMap _ _ _ (dualHom _ _ F) (bcChar S'.R ((ct hP' e' b).t' _))) k =
      charElem (bcChar S'.R (bcChar S.R ((ct hP e b).t' _))) k
    rw [charElem_tateMap, charElem_bcChar, charElem_bcChar, charElem_bcChar, ht', ht'', hch, hF']
  · rw [mv_one]
    change eL' (1 ⊗ₜ l y) (dlog _ (bcChar S'.R ((ct hP' e' b).t' _))) =
      algebraMap S.R S'.R (eL (1 ⊗ₜ y) (dlog _ (bcChar S.R ((ct hP e b).t' _))))
    rw [ht', ht'', ← hdl, hlie]
  · apply (omegaMap_polBC_bijective pol' S'.R).1
    have h3 := congrArg (fun u => s.omega (omegaMap _ _ (polBC pol S.R) u)) hx
    beta_reduce at h3
    rw [map_smul, hO, map_smulₛₗ, hom, map_sub, map_one, ← hz, ConstTate.al_apply, map_sum, map_sum] at h3
    rw [map_smul, hO', h3, mv_one, ConstTate.al_apply, map_sum]
    refine Fintype.sum_equiv (finCongr (e.trans e'.symm)) _ _ fun i => ?_
    rw [map_smul (omegaMap _ _ (polBC pol S.R)), map_smul (omegaMap _ _ (polBC pol' S'.R)), map_smulₛₗ s.omega]
    refine congrArg₂ _ rfl ?_
    change s.omega (omegaMap _ _ (polBC pol S.R) (hodgeTate _ (bcTate S.R (τ (b.reindex (finCongr e.symm) i))))) =
      omegaMap _ _ (polBC pol' S'.R) (hodgeTate _ (bcTate S'.R (τ' (b.reindex (finCongr e'.symm) _))))
    rw [omegaMap_polBC_hodgeTate pol hP.skew, omegaMap_polBC_hodgeTate pol' hP'.skew, map_neg, hdl, b.reindex_apply,
      b.reindex_apply]
    rfl

end GlobalTheory.ChainPts.SysB.RingRes

end
