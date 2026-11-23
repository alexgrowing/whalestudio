import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqOfRankAtStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HodgeWeil

theorem triv_theta (hC : GlobalTheory.Published.CubeTheorem) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) : AbLaw.Triv (Theta A L) := by
  have := hA.comm
  have h := hC S A hA L hL (G3 A) (x3 A 0) (x3 A 1) (x3 A 2)
  have e := (CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 h
  rw [CechPic.cls_linComb hL _ _ _, Fin.sum_univ_eight] at e
  refine (CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_
  rw [CechPic.cls_linComb hL _ _ _, ← e, ← Equiv.ulift.symm.sum_comp]
  have u : (Finset.univ : Finset (Finset (Fin 3))) = {{0, 1, 2}, {0, 1}, {0, 2}, {1, 2}, {0}, {1}, {2}, ∅} := by
    decide
  rw [u]
  iterate 7 rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  have k0 : psum A (x3 A) {0, 1, 2} = x3 A 0 * x3 A 1 * x3 A 2 :=
    (show _ = x3 A 0 * (x3 A 1 * (x3 A 2 * 1)) from rfl).trans (by rw [_root_.mul_one, _root_.mul_assoc])
  have k1 : psum A (x3 A) {0, 1} = x3 A 0 * x3 A 1 :=
    (show _ = x3 A 0 * (x3 A 1 * 1) from rfl).trans (by rw [_root_.mul_one])
  have k2 : psum A (x3 A) {0, 2} = x3 A 0 * x3 A 2 :=
    (show _ = x3 A 0 * (x3 A 2 * 1) from rfl).trans (by rw [_root_.mul_one])
  have k3 : psum A (x3 A) {1, 2} = x3 A 1 * x3 A 2 :=
    (show _ = x3 A 1 * (x3 A 2 * 1) from rfl).trans (by rw [_root_.mul_one])
  have k4 : psum A (x3 A) {0} = x3 A 0 := _root_.mul_one (x3 A 0)
  have k5 : psum A (x3 A) {1} = x3 A 1 := _root_.mul_one (x3 A 1)
  have k6 : psum A (x3 A) {2} = x3 A 2 := _root_.mul_one (x3 A 2)
  have k7 : psum A (x3 A) ∅ = 1 := rfl
  simp only [Equiv.ulift_symm_down, k0, k1, k2, k3, k4, k5, k6, k7, ← add_assoc]
  rfl

theorem weilIs_comp (hC : GlobalTheory.Published.CubeTheorem) {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B]
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hP : IsDual A B P) {n : ℕ}
    {T T' : Over (Sp R)} {X Y : T ⟶ A ⊗ B} (hX : X ^ n = 1) (hY : Y ^ n = 1) {e : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs (A ⊗ B) P (n : ℤ) X Y e) (σ : T' ⟶ T) :
    Out.WeilIs (A ⊗ B) P (n : ℤ) (σ ≫ X) (σ ≫ Y) (Units.map σ.left.appTop.hom.toMonoidHom e) := by
  have hAB := AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB
  have := hAB.comm
  obtain ⟨r, hr⟩ : AbLaw.Triv (P.pull (eSec (A ⊗ B))) := by
    have e := (AbDual.triv_ev_iff hP.isLB _ _).2
      (AbDual.evc_one_right hP.isLB hP.zero (1 : 𝟙_ (Over (Sp R)) ⟶ A))
    have e' : CartesianMonoidalCategory.lift (1 : 𝟙_ (Over (Sp R)) ⟶ A) (1 : 𝟙_ (Over (Sp R)) ⟶ B) = η[A ⊗ B] := by
      ext <;> simp [Hom.one_def]
    rw [AbDual.ev, e'] at e
    exact e
  let M : RigLB (A ⊗ B) := ⟨P, r, hP.isLB, hr⟩
  obtain ⟨t, ht⟩ := triv_theta hC hAB hP.isLB
  obtain ⟨t', ht', hn'⟩ := AbLaw.Cube.exists_normalised hP.isLB t ht
  let c := AbLaw.Cube.cubicalOfNormalised globalFns_holds hAB M t' ht' hn'
  obtain ⟨w, hw⟩ := WeilCube.exists_isRatio c n X Y hX hY
  obtain rfl := (WeilCube.weilIs_iff c globalFns_holds hAB hX hY hw _).1 h
  exact (WeilCube.weilIs_iff c globalFns_holds hAB (by rw [← MonObj.comp_pow, hX, MonObj.comp_one])
    (by rw [← MonObj.comp_pow, hY, MonObj.comp_one]) (hw.comp c σ) _).2 rfl

section Point

variable {R D : Type} [CommRing R] [CommRing D] [Bialgebra R D] [Module.Finite R D] [Module.Projective R D]
  [Coalgebra.IsCocomm R D]

theorem cobOne_eq_zero_iff (b : CartierDual R D) : cobOne R _ b = 0 ↔
    ∀ x y : D, b (x * y) = Coalgebra.counit (R := R) x * b y + Coalgebra.counit (R := R) y * b x := by
  rw [cobOne_apply, sub_sub, sub_eq_zero, CartierDual.comul_eq_iff]
  refine forall₂_congr fun x y ↦ ?_
  rw [map_add, LinearMap.add_apply, CartierDual.pair_tmul_tmul, CartierDual.pair_tmul_tmul,
    CartierDual.one_apply, CartierDual.one_apply, eq_comm, add_comm, mul_comm (b x)]

def epsPoint (b : CartierDual R D) (hb : cobOne R _ b = 0) : D →ₐ[R] DualNumber R :=
  AlgHom.ofLinearMap
    (Algebra.linearMap R (DualNumber R) ∘ₗ Coalgebra.counit + TrivSqZeroExt.inrHom R R ∘ₗ b.ofConv)
    (by
      have h : b 1 = 0 := (mulBy_of_cobOne_eq_zero hb 0).2
      simp [h])
    (fun x y ↦ by
      have h := (cobOne_eq_zero_iff b).1 hb x y
      ext
      · simp [TrivSqZeroExt.algebraMap_eq_inl]
      · simp [TrivSqZeroExt.algebraMap_eq_inl, h, mul_comm])

theorem fst_epsPoint (b : CartierDual R D) (hb : cobOne R _ b = 0) (a : D) :
    (epsPoint b hb a).fst = Coalgebra.counit (R := R) a := by
  simp [epsPoint, TrivSqZeroExt.algebraMap_eq_inl]

theorem snd_epsPoint (b : CartierDual R D) (hb : cobOne R _ b = 0) (a : D) : (epsPoint b hb a).snd = b a := by
  simp [epsPoint, TrivSqZeroExt.algebraMap_eq_inl]

end Point

section Tower

variable {p : ℕ} {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {𝒜 ℬ : PDivGroup p R}

theorem isTangent_epsPoint (u : ℬ.TorsionTower B) (b : CartierDual R (ℬ.A 1)) (hb : cobOne R _ b = 0) :
    IsTangent (spOver (epsPoint b hb) ≫ u.y 1 : epsR R ⟶ B) := by
  have h := (u.eq_one_iff 1 ((TrivSqZeroExt.fstHom R R R).comp (epsPoint b hb))).2 (fst_epsPoint b hb)
  rw [← spOver_comp, Category.assoc] at h
  refine (congrArg Over.Hom.left h).trans ?_
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  exact (congrArg (· ≫ η[B].left) (Cris.spMap_id R)).trans (Category.id_comp _)

theorem lieCorr_epsPoint [Nontrivial R] (hR : (p : R) = 0) (u : ℬ.TorsionTower B) (b : CartierDual R (ℬ.A 1))
    (hb : cobOne R _ b = 0) {x : ℬ.Lie} (h : u.LieCorr x (spOver (epsPoint b hb) ≫ u.y 1)) (z : ℬ.omega)
    (a : ℬ.A 1) (ha : dUnit R a = z.1 1) : x z = b a := by
  obtain ⟨ψ, h₁, h₂⟩ := h.2 1
  have e : ψ = (epsTo R (ModPow p R 1)).comp (epsPoint b hb) :=
    u.inj 1 _ _ _ (by rw [h₁, ← spOver_comp, Category.assoc])
  have k := h₂ z a ha
  rw [e, AlgHom.comp_apply, snd_epsTo, snd_epsPoint, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq, pow_one, hR,
    Ideal.mem_span_singleton, zero_dvd_iff, sub_eq_zero] at k
  exact k

theorem pairsTo_epsPoint [Fact p.Prime] (hC : GlobalTheory.Published.CubeTheorem) (hA : IsAbelianScheme A) (hB : IsAbelianScheme B)
    {P : LB (A ⊗ B).left} (hP : IsDual A B P) {t : 𝒜.TorsionTower A} {u : ℬ.TorsionTower B} {w : 𝒜 ⟶ ℬ.dual}
    (hw : IsWeilHom t u P w) (b : CartierDual R (ℬ.A 1)) (hb : cobOne R _ b = 0) :
    EpsWeil.PairsTo P p (t.y 1) (spOver (epsPoint b hb) ≫ u.y 1) (w.app 1 b) := by
  obtain ⟨U, hU, hχ⟩ := hw 1
  let f : 𝒜.A 1 ⊗[R] ℬ.A 1 →ₐ[R] DualNumber (𝒜.A 1) :=
    Algebra.TensorProduct.lift (TrivSqZeroExt.inlAlgHom R _ _)
      ((EpsWeil.epsMap R (𝒜.A 1)).comp (epsPoint b hb)) fun _ _ ↦ .all _ _
  have k := weilIs_comp hC hA hB hP (by
      ext1 <;> simp only [MonObj.pow_comp, MonObj.one_comp, lift_fst, lift_snd, one_pow,
        ← MonObj.comp_pow, t.y_pow, MonObj.comp_one]) (by
      ext1 <;> simp only [MonObj.pow_comp, MonObj.one_comp, lift_fst, lift_snd, one_pow,
        ← MonObj.comp_pow, u.y_pow, MonObj.comp_one]) hU (spOver f)
  have hf : ∀ z, (f z).fst = TensorProduct.rid R _ ((1 : CartierDual R (ℬ.A 1)).ofConv.lTensor _ z) ∧
      (f z).snd = TensorProduct.rid R _ (b.ofConv.lTensor _ z) := fun z ↦ by
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, hx, hy, and_self]
    | tmul x y =>
      simp [f, EpsWeil.epsMap, DualNumber.lift_apply_apply, TrivSqZeroExt.algebraMap_eq_inl', fst_epsPoint,
        snd_epsPoint, Algebra.smul_def, mul_comm, CartierDual.one_apply]
  have e₃ : Units.map (spOver f).left.appTop.hom.toMonoidHom (unitOn U) = unitOn (EpsWeil.epsUnit (w.app 1 b)) := by
    refine (EpsWeil.map_unitOn _ U).trans (congrArg unitOn (Units.ext (TrivSqZeroExt.ext ?_ ?_)))
    · refine (hf _).1.trans ((hχ 1).symm.trans ((map_one (w.app 1)).trans ?_))
      simp [EpsWeil.epsUnit]
    · refine (hf _).2.trans ((hχ b).symm.trans ?_)
      simp [EpsWeil.epsUnit]
  have e₁ : f.comp Algebra.TensorProduct.includeLeft = TrivSqZeroExt.inlAlgHom R _ _ :=
    AlgHom.ext fun a ↦ by simp [f]
  have e₂ : f.comp Algebra.TensorProduct.includeRight = (EpsWeil.epsMap R (𝒜.A 1)).comp (epsPoint b hb) :=
    AlgHom.ext fun a ↦ by simp [f]
  rw [e₃, comp_lift, comp_lift, MonObj.comp_one, MonObj.comp_one, ← Category.assoc, ← Category.assoc, spOver_comp,
    spOver_comp, e₁, e₂, ← spOver_comp, Category.assoc, pow_one] at k
  exact k

end Tower

section Linear

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {𝒜 : PDivGroup p K}
  {w : 𝒜 ⟶ 𝒜.dual} {E : V ≃ₗ[K] 𝒜.RigExt} {β : V →ₗ[K] V →ₗ[K] K} {ε : ℤˣ}

theorem pairing_rigExtMap (hK : (p : K) = 0)
    (lag : ∀ s, 𝒜.rigToExt (E s) = 0 ↔ ∀ z, β s (E.symm (𝒜.rigOfOmega z)) = 0)
    (geo : ∀ b : CartierDual K (𝒜.A 1), cobOne K _ b = 0 → ∃ c, 𝒜.IsConnecting (𝒜.rigToExt (E c)) (ε • w.app 1 b) ∧
      ∀ (z : 𝒜.omega) (a : 𝒜.A 1), dUnit K a = z.1 1 → β c (E.symm (𝒜.rigOfOmega z)) = -b a)
    (y : 𝒜.dual.RigExt) (b : CartierDual K (𝒜.A 1)) (hy : 𝒜.dual.IsConnecting (𝒜.dual.rigToExt y) b)
    (z : 𝒜.omega) (a : 𝒜.A 1) (ha : dUnit K a = z.1 1) :
    β (E.symm (rigExtMap w y)) (E.symm (𝒜.rigOfOmega z)) = (-ε) • b a := by
  obtain ⟨c, k₁, k₄⟩ := geo b (cobOne_eq_zero_of_connecting (G := 𝒜.dual) hy)
  have k₂ : (𝒜.extChar hK (𝒜.rigToExt (E c))).1 = ε • w.app 1 b := (𝒜.extChar_eq_iff hK _ _).2 k₁
  have k₃ : (𝒜.extChar hK (𝒜.rigToExt (rigExtMap w y))).1 = w.app 1 b := by
    rw [rigToExt_rigExtMap, extChar_vecExtMap, (𝒜.dual.extChar_eq_iff hK _ _).2 hy]
  have k₅ : 𝒜.rigToExt (E (E.symm (rigExtMap w y) - (ε : ℤ) • c)) = 0 := by
    rw [map_sub, map_sub, LinearEquiv.apply_symm_apply, map_zsmul, map_zsmul, sub_eq_zero]
    refine (𝒜.extChar_bijective hK).1 (Subtype.ext ?_)
    rw [map_zsmul, k₃, Submodule.coe_smul_of_tower, k₂, ← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]
  have k₆ := (lag _).1 k₅ z
  rw [map_sub, map_zsmul, LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, k₄ z a ha] at k₆
  rw [k₆, Units.neg_smul, smul_neg, Units.smul_def]

theorem vecExtMap_bijective (hK : (p : K) = 0)
    (lag : ∀ s, 𝒜.rigToExt (E s) = 0 ↔ ∀ z, β s (E.symm (𝒜.rigOfOmega z)) = 0)
    (key : ∀ (y : 𝒜.dual.RigExt) (b : CartierDual K (𝒜.A 1)), 𝒜.dual.IsConnecting (𝒜.dual.rigToExt y) b →
      ∀ (z : 𝒜.omega) (a : 𝒜.A 1), dUnit K a = z.1 1 →
      β (E.symm (rigExtMap w y)) (E.symm (𝒜.rigOfOmega z)) = (-ε) • b a) :
    Function.Bijective (vecExtMap w) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := 𝒜.dual.rigToExt_surjective x
    obtain ⟨b, hy⟩ := 𝒜.dual.exists_connecting hK (𝒜.dual.rigToExt y)
    have h₀ : b = 0 := CartierDual.ext_apply fun a ↦ by
      obtain ⟨z, hz⟩ := 𝒜.omegaLevel_surjective 1 (dUnit K a)
      have k := key y b hy z a hz.symm
      rw [(lag _).1 (by rw [LinearEquiv.apply_symm_apply, rigToExt_rigExtMap, hx]) z,
        eq_comm, smul_eq_zero_iff_eq] at k
      exact k
    exact (map_eq_zero_iff _ (𝒜.dual.extChar_bijective hK).1).1
      (Subtype.ext (((𝒜.dual.extChar_eq_iff hK _ _).2 hy).trans h₀))
  · obtain ⟨x, rfl⟩ := 𝒜.rigToExt_surjective x
    let o := LinearEquiv.ofBijective _ (𝒜.omegaLevel_one_bijective hK)
    let l : Cot K (𝒜.A 1) →ₗ[K] K :=
      (-ε) • (β (E.symm x) ∘ₗ E.symm.toLinearMap ∘ₗ 𝒜.rigOfOmega ∘ₗ o.symm.toLinearMap)
    let b : CartierDual K (𝒜.A 1) := WithConv.toConv (l ∘ₗ AugCot.d (Bialgebra.counitAlgHom K _))
    have hb₀ : cobOne K _ b = 0 := (cobOne_eq_zero_iff b).2 fun a a' ↦ by
      change l (AugCot.d _ (a * a')) = _
      rw [AugCot.d_mul, map_add, map_smul, map_smul]
      rfl
    obtain ⟨x', hx'⟩ := exists_of_cobOne_eq_zero (G := 𝒜.dual) hb₀
    obtain ⟨y, rfl⟩ := 𝒜.dual.rigToExt_surjective x'
    refine ⟨𝒜.dual.rigToExt y, ?_⟩
    rw [← rigToExt_rigExtMap, ← sub_eq_zero, ← map_sub, ← E.apply_symm_apply (_ - _), lag]
    intro z
    obtain ⟨a, ha⟩ := AugCot.d_surjective _ (z.1 1)
    have k : b a = (-ε) • β (E.symm x) (E.symm (𝒜.rigOfOmega z)) := by
      change l (AugCot.d _ a) = _
      rw [ha, ← o.symm_apply_apply z]
      exact congrArg l (congrArg (fun u : 𝒜.omega ↦ u.1 1) (o.symm_apply_apply z))
    rw [map_sub, map_sub, LinearMap.sub_apply, key y b hx' z a ha, k, smul_smul, Int.units_mul_self, one_smul,
      sub_self]

omit [Fact p.Prime] in

theorem rigToExt_eq_zero_iff {F : Submodule K V} (hF : F.map E.toLinearMap = LinearMap.range 𝒜.rigOfOmega)
    (lag : ∀ s, s ∈ F ↔ ∀ s' ∈ F, β s s' = 0) (s : V) :
    𝒜.rigToExt (E s) = 0 ↔ ∀ z, β s (E.symm (𝒜.rigOfOmega z)) = 0 := by
  have F₁ : ∀ c, c ∈ F ↔ ∃ z, 𝒜.rigOfOmega z = E c := fun c ↦ by
    rw [← LinearMap.mem_range, ← hF, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
  rw [𝒜.exact_rigOfOmega_rigToExt, Set.mem_range, ← F₁, lag]
  refine ⟨fun h z ↦ h _ ((F₁ _).2 ⟨z, (E.apply_symm_apply _).symm⟩), fun h s' hs ↦ ?_⟩
  obtain ⟨z, hz⟩ := (F₁ s').1 hs
  rw [← E.symm_apply_apply s', ← hz, h]

end Linear

theorem vecExtMap_bijective_and_pairing : GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.ConjugateFiltration → GlobalTheory.Published.CubeTheorem → ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (hK : (p : K) = 0) (A : Over (Sp K)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A), SmoothOfRelativeDimension g A.hom → ∀ P : LB (A ⊗ A).left, IsDual A A P → LBIso (swap P) P → ∀ (ψ : HdR A →ₗ[K] HdR A →ₗ[K] K) (β : primDR A →ₗ[K] HdR A), IsCorrForm (dp0 K) (𝟙 _) A A P ψ → (∀ s y, ψ (β s) y = y s) → ∀ (e : GlobalTheory.Published.DeRhamVectorExtension.Family p) (ε : ℤˣ), e.Filtered → e.Tangent → GlobalTheory.Published.BarsottiTateDieudonne.WeilCompatible e ε → ∀ (hn : IsNilpotent (p : K)) (𝒜 : PDivGroup p K) (t : 𝒜.TorsionTower A) (w : 𝒜 ⟶ 𝒜.dual), IsWeilHom t t P w → Function.Bijective (vecExtMap w) ∧ ∀ (y : 𝒜.dual.RigExt) (b : CartierDual K (𝒜.A 1)), 𝒜.dual.IsConnecting (𝒜.dual.rigToExt y) b → ∀ (η' : 𝒜.omega) (a : 𝒜.A 1), dUnit K a = η'.1 1 → β ((e hn hA t).symm (rigExtMap w y)) ((e hn hA t).symm (𝒜.rigOfOmega η')) = (-ε) • b a := by
  intro hD hF hC p _ K _ hK A _ g hA hg P hd hs ψ β hψ hβ e ε eF eT eW hn 𝒜 t w hw
  obtain ⟨-, hb, sk, lag, -⟩ := SymmPoincare.skew_lagrangian hD hF p K hK A g hA hg P hd hs ψ β hψ hβ
  have lag' := rigToExt_eq_zero_iff (β := β) (eF hn hA t) lag
  have key := pairing_rigExtMap (w := w) (ε := ε) hK lag' fun b hb₀ ↦ by
    obtain ⟨h', hh⟩ := (hD.2.1 K A g hA hg).1.2 _ (isTangent_epsPoint t b hb₀)
    obtain ⟨c, hc⟩ := hb.2 (-h')
    have hc' : ∀ s, β c s = -h' s := fun s ↦ LinearMap.congr_fun hc s
    refine ⟨c, eW hK hA hA hg hg hd hψ t hh (pairsTo_epsPoint hC hA hA hd hw b hb₀) fun h _ ↦ ?_,
      fun z a ha ↦ (hc' _).trans (congrArg Neg.neg
        (lieCorr_epsPoint hK t b hb₀ ((eT hn hA t _ _).1 hh) z a ha))⟩
    obtain ⟨s, rfl⟩ := hb.2 h
    exact (hβ s h').trans (((sk s c).trans ((congrArg Neg.neg (hc' s)).trans (neg_neg _))).symm)
  exact ⟨vecExtMap_bijective hK lag' key, key⟩

end GlobalTheory.HodgeWeil
