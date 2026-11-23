import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DeRham

open GlobalTheory.Cris GlobalTheory.CatCoh GlobalTheory.Published GlobalTheory.Published.AbelianDeRham DividedPowers MonoidalCategory CartesianMonoidalCategory MonObj

variable {R : Type} [CommRing R]

def wedgeDual {M : Type*} [AddCommGroup M] [Module R M] (x y : Module.Dual R M) : M [⋀^Fin 2]→ₗ[R] R where
  toFun v := x (v 0) * y (v 1) - x (v 1) * y (v 0)
  map_update_add' v i a b := by
    fin_cases i <;> simp <;> ring
  map_update_smul' v i r a := by
    fin_cases i <;> simp <;> ring
  map_eq_zero_of_eq' v i j h hij := by
    fin_cases i <;> fin_cases j <;> simp_all <;> ring

theorem IsPolForm.unique (P : AbelianDeRham.Free) {A : Over (Sp R)} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) {L : LB A.left} (hL : L.IsLB) {ψ ψ' : LinearMap.BilinForm R (HdR A)}
    (h : IsPolForm (dp0 R) (𝟙 _) A L ψ) (h' : IsPolForm (dp0 R) (𝟙 _) A L ψ') : ψ = ψ' := by
  obtain ⟨h0, -, -, -, e, he⟩ := P R A g hA hg
  obtain ⟨n, a, b, hc, rfl⟩ := h
  obtain ⟨n', a', b', hc', rfl⟩ := h'
  have hz := ((isChern_existsUnique_and_iso R _ (dp0 R) _ _).1 L hL).unique hc hc'
  have hw : ∑ k, exteriorPower.ιMulti R 2 ![(a k).1, (b k).1] = ∑ k, exteriorPower.ιMulti R 2 ![(a' k).1, (b' k).1] :=
    e.injective (by simpa only [map_sum, he] using hz)
  refine LinearMap.ext₂ fun x y => ?_
  rw [wedgeForm_apply, wedgeForm_apply]
  let o : primDR A ≃ₗ[R] FirstDeRham (A.hom ≫ 𝟙 _) := LinearEquiv.ofTop _ h0
  let x' : Module.Dual R (FirstDeRham (A.hom ≫ 𝟙 _)) := x ∘ₗ o.symm.toLinearMap
  let y' : Module.Dual R (FirstDeRham (A.hom ≫ 𝟙 _)) := y ∘ₗ o.symm.toLinearMap
  have ex : ∀ c : primDR A, x' c.1 = x c := fun c => congrArg x (o.symm_apply_apply c)
  have ey : ∀ c : primDR A, y' c.1 = y c := fun c => congrArg y (o.symm_apply_apply c)
  have := congrArg (exteriorPower.alternatingMapLinearEquiv (wedgeDual x' y')) hw
  simpa [map_sum, wedgeDual, ex, ey] using this

theorem isDPMorphism_red : IsDPMorphism (epsDP R) (dp0 R) (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine (isDPMorphism_iff _ _ _).2 ⟨Ideal.map_le_iff_le_comap.2 fun a ha => ?_, fun n hn a ha => ?_⟩
  · exact ha
  · have ha' : (TrivSqZeroExt.fstHom R R R).toRingHom a = 0 := ha
    rw [ha', dpow_eval_zero _ hn]
    rcases n with _ | _ | n
    · exact absurd rfl hn
    · rw [zero_add, (epsDP R).dpow_one ha, ha']
    · have e : (epsDP R).dpow (n + 1 + 1) a = 0 := squareZeroDividedPowers_dpow _ (by omega) a
      rw [e, map_zero]

variable (A : Over (Sp R)) [GrpObj A] in

theorem redMor : GrpMor (epsDP R) (epsRed R) A (dp0 R) (𝟙 _) A (TrivSqZeroExt.fstHom R R R).toRingHom (𝟙 _)
    (Over.Hom.left (𝟙 A)) :=
  GrpMor.of_hom isDPMorphism_red (by rw [Category.id_comp]) (𝟙 A)

theorem redMor_constMor {A : Over (Sp R)} [GrpObj A] (c : primDR A) : (redMor A).pull ((constMor A).pull c) = c :=
  (GrpMor.pull_pull (constMor A) (redMor A) (homMor (dp0 R) (𝟙 _) (𝟙 A))
    (fun r => by simp [TrivSqZeroExt.algebraMap_eq_inl]) (by simp) c).trans (Subtype.ext (IsMor.pullCohomologyOne_id _ c.1))

theorem constMor_surjective (P : AbelianDeRham) {A : Over (Sp R)} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) : Function.Surjective (liftSemi (constMor A).pull) := by
  obtain ⟨-, -, PB, PR, -⟩ := P
  obtain ⟨C, _, φ, hφ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A (spMap (algebraMap R (DualNumber R)))
  have eid : epsRed R ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    have e0 : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [epsRed, spMap_comp_spMap, e0]
    exact Spec.map_id _
  have w : 𝟙 A.left ≫ A.hom = (A.hom ≫ epsRed R) ≫ spMap (algebraMap R (DualNumber R)) := by
    rw [Category.assoc, eid, Category.comp_id, Category.id_comp]
  have e1 : hφ.1.lift _ _ w ≫ φ = 𝟙 _ := hφ.1.lift_fst _ _ _
  have e2 : hφ.1.lift _ _ w ≫ C.hom = A.hom ≫ epsRed R := hφ.1.lift_snd _ _ _
  haveI : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
  have hic : IsGrpPullback A C (epsRed R) (hφ.1.lift _ _ w) :=
    hφ.cancel ((isGrpPullback_of_iso (Iso.refl A)).congr eid.symm e1.symm) e2
  have hC := PolPull.isAbelianScheme_of_isGrpPullback hA hφ
  have gC := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hφ.1 hg
  obtain ⟨bc, -⟩ := PB R A g hA hg (DualNumber R) C φ hφ
  have su : Function.Surjective (TrivSqZeroExt.fstHom R R R).toRingHom := fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  have rg := PR _ C g hC gC _ (epsDP R) (isDPNilpotent_squareZero _) R _ su rfl A _ hic
  intro p
  obtain ⟨q, rfl⟩ := rg.2 p
  obtain ⟨z, rfl⟩ := bc.2 q
  refine ⟨z, ?_⟩
  induction z with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r c =>
    rw [liftSemi_tmul, liftSemi_tmul, map_smul,
      ← GrpMor.pull_pull (bcMor hφ) (liftMor (epsDP R) hic) (constMor A) (fun _ => rfl) (by simpa using e1) c]

set_option maxHeartbeats 1000000 in

theorem IsKSValue.unique (P : AbelianDeRham) {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A']
    {g : ℕ} (hA : IsAbelianScheme A') (hg : SmoothOfRelativeDimension g A'.hom) {i : A.left ⟶ A'.left}
    {h : IsGrpPullback A A' (epsRed R) i} {f : HdR A} {v v' : epsR R ⟶ A} (e : IsKSValue h f v)
    (e' : IsKSValue h f v') : v = v' := by
  have a₀ := PolPull.isAbelianScheme_of_isGrpPullback hA h
  have g₀ := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg
  have hL := (P.2.1 R A g a₀ g₀).1
  obtain ⟨k, ⟨d, hd, ed⟩, hk⟩ := e
  obtain ⟨k', ⟨d', hd', ed'⟩, hk'⟩ := e'
  suffices hkk : k - k' ∈ Fil A by
    have := (isLieImage_one_iff.2 hkk).add hk'
    rw [sub_add_cancel, show (1 * v' : epsR R ⟶ A) = v' from _root_.one_mul v'] at this
    exact (hL.1 k).unique hk this
  letI : Algebra (DualNumber R) R := (TrivSqZeroExt.fstHom R R R).toRingHom.toAlgebra
  obtain ⟨-, hF⟩ := P.2.2.1 (DualNumber R) A' g hA hg R A i h
  rw [Fil, hF, Submodule.mem_dualAnnihilator]
  intro c hc
  refine (Submodule.span_le (p := LinearMap.ker (k - k'))).2 (fun c hc => ?_) hc
  obtain ⟨c', hc', rfl⟩ := hc
  have hD : d - d' ∈ liftFil (epsDP R) h := sub_mem hd hd'
  have z0 : (d - d') ((liftMor (epsDP R) h).pull c') = 0 := (Submodule.mem_dualAnnihilator _).1 hD c' hc'
  have eD : ∀ c, (d - d') ((constMor A).pull c) = TrivSqZeroExt.inr ((k - k') c) := fun c => by
    rw [LinearMap.sub_apply, ed, ed', LinearMap.sub_apply]
    ext <;> simp
  have key : ∀ z, (d - d') (liftSemi (constMor A).pull z) =
      TrivSqZeroExt.inr ((k - k') ((redMor A).pull (liftSemi (constMor A).pull z))) := fun z => by
    induction z with
    | zero => simp only [map_zero, TrivSqZeroExt.inr_zero]
    | add x y hx hy => simp only [map_add, hx, hy, TrivSqZeroExt.inr_add]
    | tmul r c =>
      rw [liftSemi_tmul, LinearMap.map_smul, eD, LinearMap.map_smulₛₗ, redMor_constMor, LinearMap.map_smul]
      ext <;> simp [mul_comm]
  obtain ⟨z, hz⟩ := constMor_surjective P a₀ g₀ ((liftMor (epsDP R) h).pull c')
  have red : (redMor A).pull ((liftMor (epsDP R) h).pull c') = (bcMor h).pull c' :=
    GrpMor.pull_pull (liftMor (epsDP R) h) (redMor A) (bcMor h) (fun _ => rfl) (by simp) c'
  have := key z
  rw [hz, z0, red] at this
  exact (TrivSqZeroExt.inr_injective this.symm)

end GlobalTheory.DeRham

namespace GlobalTheory.FlagTan

open GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.Published ReciprocityTheory.ChartRestriction.G.PullbackSections MonoidalCategory CartesianMonoidalCategory MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K]

section Frame

variable {y : FrPt Xo c K} {B : Over (Sp K)} [GrpObj B] [IsCommMonObj B] {ρ : B.left ⟶ Xo.univ.t.G.left}
  (hρ : IsGrpPullback B Xo.univ.t.G y.x ρ)

include hρ in

theorem exists_sub_mem_Fil (hL : LieExact B) {vb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → (epsR K ⟶ B)}
    {kb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → HdR B} (hv : ∀ k, pushHom hρ (epsR K) (vb k) = tv (fullB y k))
    (hl : ∀ k, IsLieImage (kb k) (vb k)) (h : HdR B) : ∃ a : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → K,
      h - ∑ k, a k • kb k ∈ Fil B := by
  obtain ⟨v, hh, -⟩ := hL.1 h
  obtain ⟨a, ha, -⟩ := fullB_basis y (mkT _ ((ReciprocityTheory.ChartRestriction.G.PullbackSections.isTangent_iff hρ v).1 hh.1))
  refine ⟨a, ?_⟩
  have key : ∀ s : Finset (Σ σ : E →+* ℂ, Fin (Dw.mult σ)), ∃ w : epsR K ⟶ B,
      IsLieImage (∑ k ∈ s, a k • kb k) w ∧ pushHom hρ (epsR K) w = tv (∑ k ∈ s, a k • fullB y k) := fun s => by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, isLieImage_one_iff.2 (by simp), by simp [tv_zero]⟩
    | insert k s hk ih =>
      obtain ⟨w, hw, ew⟩ := ih
      refine ⟨(GlobalTheory.GrpTangent.epsScale (a k) ≫ vb k) * w, ?_, ?_⟩
      · rw [Finset.sum_insert hk]
        exact ((hl k).smul _).add hw
      · rw [Finset.sum_insert hk, tv_add, map_mul, ew, tv_smul, ← hv k, ← push_scK]
        rfl
  obtain ⟨w, hw, ew⟩ := key Finset.univ
  rw [← ha, tv_mkT] at ew
  obtain rfl := push_inj hρ ew
  exact hh.sub_mem hw

include hρ in

theorem coef_unique {τ : E →+* ℂ} {u : Fin (Dw.mult τ) → (epsR K ⟶ B)}
    (hu : ∀ i, pushHom hρ (epsR K) (u i) = tv (fullB y ⟨τ, i⟩)) {a b : Fin (Dw.mult τ) → K} {w : epsR K ⟶ B}
    (ha : IsLieComb a u w) (hb : IsLieComb b u w) : a = b := by
  have key : ∀ a : Fin (Dw.mult τ) → K, IsLieComb a u w →
      pushHom hρ (epsR K) w = tv (∑ i, a i • fullB y ⟨τ, i⟩) := fun a h => by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.isLieComb_iff hρ] at h
    rw [h, tv_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [tv_smul]
    exact congrArg _ (hu i)
  have e := tanM_ext ((key a ha).symm.trans (key b hb))
  exact (eig_coords y τ _ (eig_comb τ _ (fun i => fullB_eig y τ i) a)).unique rfl e

end Frame

theorem spMap_dualMap_id : spMap (dualMap (algebraMap K K)) = 𝟙 (Sp (DualNumber K)) := by
  have e : dualMap (algebraMap K K) = RingHom.id (DualNumber K) := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  rw [e]
  exact Spec.map_id _

theorem spMap_algebraMap_id : spMap (algebraMap K K) = 𝟙 (Sp K) := by
  rw [Algebra.algebraMap_self]
  exact Spec.map_id _

theorem exists_isGrpPullback_self {S S₁ : Scheme.{0}} {G : Over S} [GrpObj G] {t : S₁ ⟶ S} {A B : Over S₁} [GrpObj A]
    [GrpObj B] {π : A.left ⟶ G.left} {ρ : B.left ⟶ G.left} (hπ : IsGrpPullback A G t π) (hρ : IsGrpPullback B G t ρ)
    {e : S₁ ⟶ S₁} (he : e = 𝟙 _) : ∃ φ : B.left ⟶ A.left, IsGrpPullback B A e φ ∧ φ ≫ π = ρ := by
  subst he
  have w : ρ ≫ G.hom = B.hom ≫ t := hρ.1.w
  refine ⟨hπ.1.lift _ _ w, ?_, hπ.1.lift_fst _ _ _⟩
  exact hπ.cancel (hρ.congr (Category.id_comp _).symm (hπ.1.lift_fst _ _ w).symm)
    ((hπ.1.lift_snd _ _ w).trans (Category.comp_id _).symm)

theorem IsKS.unique (P : AbelianDeRham) {Φ : Finset (E →+* ℂ)} {y : FrPt Xo c K} {x' : Sp (DualNumber K) ⟶ Xo.X}
    {M M' : HIx Dw Φ → K} (hM : IsKS Φ y x' M) (hM' : IsKS Φ y x' M') : M = M' := by
  obtain ⟨A, _, A', _, π, π', i, hi, b, ub, hb, hπ, hπ', e, hpol, hu, hl, hM⟩ := hM
  obtain ⟨B, _, B', _, ρ, ρ', j, hj, b₂, vb, kb, hρ, hρ', e₂, hpol₂, hv, hl₂, hM'⟩ := hM'
  obtain ⟨φ, hφ, eφ⟩ := exists_isGrpPullback_self hπ hρ (spMap_algebraMap_id (K := K))
  obtain ⟨φ', hφ', eφ'⟩ := exists_isGrpPullback_self hπ' hρ' (spMap_dualMap_id (K := K))
  have hU := ObjDim.isAbelianScheme Xo.univ
  have hg := ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := PolPull.isAbelianScheme_of_isGrpPullback hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hB := PolPull.isAbelianScheme_of_isGrpPullback hU hρ
  have gB := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hρ.1 hg
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  have hB' := PolPull.isAbelianScheme_of_isGrpPullback hU hρ'
  have gB' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hρ'.1 hg
  haveI : IsCommMonObj B := PolPull.isCommMonObj_of_isGrpPullback hρ
  have sq : j ≫ φ' = φ ≫ i := by
    apply hπ'.1.hom_ext
    · rw [Category.assoc, Category.assoc, eφ', e₂, e, eφ]
    · have w1 : φ' ≫ A'.hom = B'.hom ≫ spMap (dualMap (algebraMap K K)) := hφ'.1.w
      have w2 : i ≫ A'.hom = A.hom ≫ DeRham.epsRed K := hi.1.w
      have w3 : j ≫ B'.hom = B.hom ≫ DeRham.epsRed K := hj.1.w
      have w4 : φ ≫ A.hom = B.hom ≫ spMap (algebraMap K K) := hφ.1.w
      rw [spMap_dualMap_id, Category.comp_id] at w1
      rw [spMap_algebraMap_id, Category.comp_id] at w4
      rw [Category.assoc, Category.assoc, w1, w2, ← Category.assoc, w3, w4]
  obtain ⟨bc, hF⟩ := P.2.2.1 K A _ hA gA K B φ hφ
  have hL := (P.2.1 K B _ hB gB).1
  have isL := Xo.univ.t.PP.isLB
  have isLρ := pull_isLB isL ρ
  obtain ⟨b', hpol', eb⟩ := hpol.pull_comp (AbelianDeRham.bcMor hφ) isL
  rw [eφ] at hpol'
  obtain rfl : b' = b₂ := IsPolForm.unique P.1 hB gB isLρ hpol' hpol₂
  obtain ⟨iso, perf⟩ := P.2.2.2.2 K B _ hB gB _ isLρ _ hpol'
  obtain ⟨w, hw⟩ := ChernExists.lbIso_refl isLρ
  have pp := perf (kTriv_pull hρ isL isLρ ((isGen_iff w).1 hw) Xo.univ.ktriv)
  choose tv' htv using ArcQ.NormalForm.exists_baseChange hφ
  choose th hth using bc.exists

  have et : ∀ (σ k), tv' (ub σ k) = vb σ k := fun σ k => by
    apply push_inj hρ
    apply Over.OverMorphism.ext
    change (tv' (ub σ k)).left ≫ ρ = (vb σ k).left ≫ ρ
    rw [hv, ← eφ, ← Category.assoc, htv, spMap_dualMap_id, Category.id_comp, hu]
  have hvs : ∀ k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)), pushHom hρ (epsR K) (vb k.1 k.2) = tv (fullB y k) :=
    fun k => Over.OverMorphism.ext (hv k.1 k.2)

  have zero : ∀ f ∈ Fil B, (∀ k, b' f (kb k) = 0) → f = 0 := fun f hf h0 => by
    apply pp.bijective_left.1
    rw [map_zero]
    refine LinearMap.ext fun h => ?_
    obtain ⟨a, ha⟩ := exists_sub_mem_Fil hρ hL hvs (kb := kb) (fun k => hl₂ k.1 k.2) h
    have := iso f hf _ ha
    rw [map_sub, map_sum] at this
    simpa [h0] using this
  have ed : ∀ k, th (hb k) - kb k ∈ Fil B := fun k => by
    have := (hl k.1 k.2).baseChange (hφ := hφ) hF hL (hth _) (htv _)
    rw [et] at this
    exact this.sub_mem (hl₂ k.1 k.2)
  funext t
  obtain ⟨τ, r, s⟩ := t
  obtain ⟨w₁, hc₁, f₁, hf₁, hd₁, hv₁⟩ := hM τ r
  obtain ⟨w₂, hc₂, f₂, hf₂, hd₂, hv₂⟩ := hM' τ r
  have mf : th f₁ ∈ Fil B := mem_Fil_of_corr (hφ := hφ) hF (hth f₁) hf₁
  have ev₁ : IsKSValue hj (th f₁) (tv' w₁) := hv₁.baseChange (hφ := hφ) P hA' gA' hj hφ' sq (hth f₁) (htv w₁)
  have e0 : th f₁ - f₂ = 0 := zero _ (sub_mem mf hf₂) fun k => by
    have h1 := eb _ _ _ _ (hth f₁) (hth (hb k))
    have h2 := iso _ mf _ (ed k)
    rw [map_sub, h1, hd₁, sub_eq_zero] at h2
    rw [map_sub, LinearMap.sub_apply, hd₂, ← h2]
    simp
  rw [sub_eq_zero.1 e0] at ev₁
  have ew := IsKSValue.unique P hB' gB' ev₁ hv₂
  have c₁ := ArcQ.NormalForm.isLieComb_baseChange hφ (u := fun i => tv' (ub τ.1 i)) (fun _ => htv _) (htv w₁) hc₁
  simp only [et, ew, Algebra.algebraMap_self, RingHom.id_apply] at c₁
  exact congrFun (coef_unique hρ (fun i => hvs ⟨τ.1, i⟩) c₁ hc₂) s

theorem isKS_unique : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K]
    [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' →
    ∀ M M' : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M →
      GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M' → M = M' :=
  fun Pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h h' => IsKS.unique Pr.p5 h h'

end GlobalTheory.FlagTan
