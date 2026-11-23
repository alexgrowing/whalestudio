import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnTorusComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalLatticeIdentificationEqId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothConeSumGeneratorsEqOfCommonInteriorPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalCoordsEqOfMatchingData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointPairsLowerBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCDvrTwoEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromBaseOfPullbackInjectiveDomains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodPartMemTautologicalPointTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalPointTransportFieldMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBaseMatchingMonomialsRatioUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataNsmulRescaleKeepsLawsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBaseInjectionsAgreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalBaseNsmulDegenerationDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromTautBaseOfRescaledPullbackMonomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfMumfordBundleTorsionPresentationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfProdZpowEqBalancedFormsBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.UInj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem lattice_id {O : Type} [CommRing O] {bar : O → O} {ψ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Free ℤ X] [Module.Finite ℤ X] {m : ℕ} {δ : Fin m → LinearMap.BilinForm ℤ X} (hδ : IsCone bar ψ δ)
    (hdef : ∀ x, x ≠ 0 → ∃ k, 0 < δ k x x) (ga : X ≃ₗ[O] X) (c c' : Fin m → ℕ) (hc : ∀ k, 0 < c k) (hc' : ∀ k, 0 < c' k)
    (he : ∑ k, c k • δ k = ∑ k, c' k • pull ga.toLinearMap (δ k)) {n : ℕ} (hn : 3 ≤ n)
    (hcong : ∀ x, GlobalTheory.Poinc.CongMod n (ga x) x) (x : X) : ga x = x := by
  classical
  have hδ' := hδ.pull_equiv ga
  set δ' := fun k => pull ga.toLinearMap (δ k) with hd
  have h1 : ∀ k, ∃ j, δ k = δ' j := cone_gen_mem_of_common hδ hδ' c c' hc he
  have h2 : ∀ j, ∃ k, δ' j = δ k := cone_gen_mem_of_common hδ' hδ c' c hc' he.symm
  have himg : Finset.univ.image δ = Finset.univ.image δ' := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨by rintro ⟨k, rfl⟩; exact (h1 k).imp fun _ => Eq.symm, by rintro ⟨j, rfl⟩; exact (h2 j).imp fun _ => Eq.symm⟩
  have e1 : ∑ x ∈ Finset.univ.image δ, x = ∑ k, δ k := Finset.sum_image fun a _ b _ h => hδ.injective h
  have e2 : ∑ x ∈ Finset.univ.image δ', x = ∑ k, δ' k := Finset.sum_image fun a _ b _ h => hδ'.injective h
  have hS : ∑ k, δ k = ∑ k, δ' k := by rw [← e1, ← e2, himg]
  have hk : ∀ x y, (∑ k, δ k) (ga x) (ga y) = (∑ k, δ k) x y := by
    intro x y
    have h := LinearMap.congr_fun₂ hS x y
    simp only [LinearMap.sum_apply, hd, pull_apply, LinearEquiv.coe_coe] at h ⊢
    exact h.symm
  have hpos : ∀ x, x ≠ 0 → 0 < (∑ k, δ k) x x := by
    intro x hx
    obtain ⟨k, hk⟩ := hdef x hx
    simp only [LinearMap.sum_apply]
    exact Finset.sum_pos' (fun i _ => hδ.nonneg i x) ⟨k, Finset.mem_univ _, hk⟩
  exact DFunLike.congr_fun (GlobalTheory.Poinc.eq_refl_of_isometry_congMod X _ hpos ga.toAddEquiv.toIntLinearEquiv hk n hn hcong) x

theorem tors_sec {D' : Datum H} {l : Geo.Tor.Level H} {B : Type} [CommRing B] {bs : Geo.Tor.Base l B} {S : Scheme.{0}}
    {s : S ⟶ Sp B} (o : Obj D' l bs s) {G : Over S} [GrpObj G] {φ : o.t.G.left ⟶ G.left}
    (h : IsGrpPullback o.t.G G (𝟙 S) φ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (p : Over.mk x ⟶ G)
    (hp : p ^ l.A = 1) : ∃ σ : 𝟙_ (Over S) ⟶ G, σ ^ l.A = 1 ∧ p.left = x ≫ σ.left := by
  have : IsMonHom (Iso.refl G).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨e, he, -⟩ := grpPullback_iso h (isGrpPullback_of_iso (Iso.refl G))
  obtain ⟨-, I, -, hI, -⟩ := o.geom K x (Spec.preimage (x ≫ s)).hom (Spec.map_preimage _).symm
  obtain ⟨a, ha⟩ := (I.onto l.A l.A_pos (p ≫ e.inv)).1 (by rw [← MonObj.pow_comp, hp, MonObj.one_comp])
  have h0 : o.etaA 0 = 1 := by simpa using o.etaA_ker 0
  have hpow : ∀ n : ℕ, o.etaA (n • a) = o.etaA a ^ n := fun n => by
    induction n with
    | zero => simpa using h0
    | succ n ih => rw [succ_nsmul, o.etaA_add, ih, pow_succ]
  refine ⟨o.etaA a ≫ e.hom, by rw [← MonObj.pow_comp, ← hpow, o.etaA_ker, MonObj.one_comp], ?_⟩
  have : p = toUnit _ ≫ o.etaA a ≫ e.hom := by
    rw [← Category.assoc, hI, ha, Category.assoc, e.inv_hom_id, Category.comp_id]
  rw [this]
  rfl

theorem second_diff {X Y K I : Type} [AddCommGroup X] [Module (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y] [Field K]
    [Fintype I] (e : X ≃ₗ[𝓞 E] Y) (s : I → K) (hs : ∀ k, s k ≠ 0) (ε : I → LinearMap.BilinForm ℤ Y)
    (hε : ∀ k, ε k ∈ balForms H.bar Y) (n : ℤ) (g : X → Kˣ)
    (hg : ∀ y, (((g y)⁻¹ : Kˣ) : K) = ∏ k, s k ^ (n * ε k (e y) (H.w0 • e y))) (a a' : X) :
    (((g (a + a'))⁻¹ * g a * g a' : Kˣ) : K) = ∏ k, s k ^ (n * ε k (e a) (e a')) := by
  have hw : H.w0 + H.bar H.w0 = 1 := GlobalTheory.PelPrim.cmHostUnit_add_conj_eq_one H
  have hg' : ∀ y, (g y : K) = (∏ k, s k ^ (n * ε k (e y) (H.w0 • e y)))⁻¹ := fun y => by
    rw [← hg, Units.val_inv_eq_inv_val, inv_inv]
  rw [Units.val_mul, Units.val_mul, hg, hg', hg', ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_neg, ← zpow_neg, ← zpow_add₀ (hs k), ← zpow_add₀ (hs k)]
  congr 1
  have h1 : ε k (e a') (H.w0 • e a) = ε k (e a) (H.bar H.w0 • e a') := by rw [(hε k).1, (hε k).2]
  have h2 : ε k (e a) (H.w0 • e a') + ε k (e a) (H.bar H.w0 • e a') = ε k (e a) (e a') := by
    rw [← map_add, ← add_smul, hw, one_smul]
  simp only [map_add, smul_add, LinearMap.add_apply, h1]
  rw [← h2]
  ring

theorem monomials_eq {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (ω : W →+* V) (D₁ D₂ : DegPre V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F] : 1 ≤ n → D₁.TauBimult → D₂.TauBimult → From T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → Match D₁ D₂ b φ F → (∀ y, e₂ (φ y) = e₁ y) → b.left ≫ β₂ = β₁ → (∀ a : Fin T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → ∀ c a : Fin T.r → ℤ, ∏ i, algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (s₁ i)) ^ ε i c a = ∏ i, algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (s₂ i)) ^ ε i c a := by
  intro hn hD₁ hD₂ hF₁ hF₂ hM he hb H c a
  obtain ⟨hbm, -, -, hu, -⟩ := hM
  obtain ⟨p₁, p₂, hy₁, ht₁, hy₂, ht₂, p', hy', hA, hE⟩ := H a
  have hg : p'.g = p₂.g := GlobalTheory.T.torsionPoint_torusPart_eq_of_equiv_same_lattice V D₂ hD₂ F n hn p' p₂ (by
    rw [hy', hy₁, hy₂]; apply e₂.injective; rw [he, e₁.apply_symm_apply, e₂.apply_symm_apply]) hE
  rw [hg] at hA
  have hχ : e₁ (φ.symm (e₂.symm c)) = e₂ (e₂.symm c) := by rw [← he, φ.apply_symm_apply]
  obtain ⟨u, hun⟩ := hu (e₂.symm c)
  obtain ⟨k₁, hk₁, hv₁⟩ := ht₁.2 (φ.symm (e₂.symm c))
  obtain ⟨k₂, hk₂, hv₂⟩ := ht₂.2 (e₂.symm c)
  let z : (TF (R := V) F).left := (⊥ : PrimeSpectrum F)
  obtain ⟨J, hJ, -⟩ := exists_good (JN D₁ D₂) (jn_isLB D₁ D₂) z (K := Empty) Empty.elim Empty.elim
    (fun a => a.elim) (fun k => k.elim)
  obtain ⟨J₀, hJ₀, -⟩ := exists_good T.M.L T.M.isLB z (K := Empty) Empty.elim Empty.elim
    (fun a => a.elim) (fun k => k.elim)
  have a₁ := hv₁ z J₀ (rl J) hJ₀ ((isPart_inl D₁.P.L D₂.P.L).good hJ)
  have a₂ := hv₂ z J₀ (rr J) hJ₀ ((isPart_inr D₁.P.L D₂.P.L).good hJ)
  have a₃ := hA.2 (e₂.symm c) u hun z J hJ
  have a₄ := GlobalTheory.T.mumfordBundleIso_comparison_normalisedGenerator T ε n V ω D₁ D₂ s₁ e₁ β₁ ββ₁ w₁ s₂ e₂ β₂ ββ₂ w₂ b hD₁ hD₂ hF₁ hF₂ hbm hb
    (φ.symm (e₂.symm c)) (e₂.symm c) hχ u hun (TF (R := V) F) p₁.g.b z J J₀ hJ hJ₀
  rw [← hA.1] at a₄
  rw [hχ] at a₁
  have hk : k₁ = k₂ := by
    apply gm_unitOn_inj z
    exact cancel_four a₁ a₂ a₃ a₄
  have := congrArg Units.val hk
  rw [hk₁, hk₂, hχ, e₂.apply_symm_apply] at this
  exact this

theorem torsion_fixed {W R V : Type} [CommRing W] [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {B : Over (Sp W)} [GrpObj B]
    {n : ℕ} (hn : 1 ≤ n) (hB : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp W) (p : Over.mk x ⟶ B), p ^ n = 1 →
      ∃ σ : 𝟙_ (Over (Sp W)) ⟶ B, σ ^ n = 1 ∧ p.left = x ≫ σ.left)
    {D₀ : DegPre R} {D₁ D₂ : DegPre V} (h₀ : D₀.TauBimult) (h₂ : D₂.TauBimult) {ω : W →+* R} {β : D₀.P.A.left ⟶ B.left}
    (hβ : IsGrpPullback D₀.P.A B (spMap ω) β) {f₁ f₂ : R →+* V} (hf : f₁.comp ω = f₂.comp ω) (hD₁ : IsPullDeg f₁ D₀ D₁)
    (hD₂ : IsPullDeg f₂ D₀ D₂) {F₀ F : Type} [Field F₀] [IsAlgClosed F₀] [Algebra (FractionRing R) F₀] [Field F]
    [IsAlgClosed F] [Algebra (FractionRing V) F] {j₁ j₂ : F₀ →+* F} {b : D₁.P.A ⟶ D₂.P.A} {φ : D₁.X ≃+ D₂.X}
    (hj₁ : Ext f₁ j₁) (hj₂ : Ext f₂ j₂)
    (hβ₁ : IsGrpPullback D₁.P.A B (spMap (f₁.comp ω)) ((hD₁.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f₁)) ≫ β))
    (HP : ∀ p₀ : QkPt D₀ F₀ n, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = hD₁.xe.symm p₀.y ∧ Tr f₁ hD₁ j₁ p₀.g p₁.g ∧
      p₂.y = hD₂.xe.symm p₀.y ∧ Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ QImg b φ p₁ p₂)
    (x : TF (R := V) F ⟶ D₁.P.A) (hx : x ^ n = 1) :
    x.left ≫ (hD₁.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f₁)) ≫ β =
      x.left ≫ b.left ≫ (hD₂.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f₂)) ≫ β := by
  obtain ⟨σ, hσ, hxσ⟩ := hB F ((TF (R := V) F).hom ≫ spMap (f₁.comp ω)) (pushHom hβ₁ _ x) (by rw [← map_pow, hx, map_one])
  have hxσ' : x.left ≫ (hD₁.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f₁)) ≫ β =
      ((TF (R := V) F).hom ≫ spMap (f₁.comp ω)) ≫ σ.left := hxσ
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.SiegelPull.push_surjective hβ (TF (R := R) F₀) (toUnit _ ≫ σ)
  have hb₀' : b₀.left ≫ β = (TF (R := R) F₀).hom ≫ spMap ω ≫ σ.left := by
    have e := congrArg (fun z => z.left) hb₀
    simp only [pushHom, pushPt, MonoidHom.mk'_apply, Over.homMk_left, Over.comp_left] at e
    rw [e]
    simp
  have hpow : b₀ ^ n = 1 := by
    apply GlobalTheory.SiegelPull.push_injective hβ
    rw [map_pow, hb₀, ← MonObj.comp_pow, hσ, MonObj.comp_one, map_one]
  obtain ⟨p₀, hp₀y, hp₀b⟩ := GlobalTheory.TInj.exists_qk_zero_over R D₀ h₀ F₀ n hn b₀ hpow
  obtain ⟨p₁, p₂, h1y, htr1, h2y, htr2, p', hp'y, hact, heqv⟩ := HP p₀
  have hg₀ : p₀.g.b.left ≫ β = (TF (R := R) F₀).hom ≫ (spMap ω ≫ σ.left) := by rw [hp₀b, hb₀']
  have hsp : ∀ f : R →+* V, spMap (f.comp ω) = spMap f ≫ spMap ω := fun f => by
    simp only [spMap, ← Spec.map_comp]; rfl
  have e₁ := tr_base hj₁ htr1 _ _ hg₀
  have e₂ := tr_base hj₂ htr2 _ _ hg₀
  rw [← Category.assoc (spMap _), ← hsp] at e₁ e₂
  have hg : p'.g = p₂.g := GlobalTheory.T.torsionPoint_torusPart_eq_of_equiv_same_lattice V D₂ h₂ F n hn p' p₂ (by rw [hp'y, h1y, h2y, hp₀y, map_zero, map_zero, map_zero]) heqv
  have hx₁ : x.left = p₁.g.b.left := by
    apply hβ₁.1.hom_ext
    · rw [hxσ', e₁, Category.assoc]
    · rw [Over.w, Over.w]
  rw [hx₁, e₁, hf, ← e₂, ← hg, hact.1, Over.comp_left, Category.assoc]

set_option maxHeartbeats 1000000 in

theorem coords_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], GlobalTheory.Mum.Base R' → ∀ θ₁ θ₂ : R →+* R', Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ κ₁ κ₂ : Sp (FractionRing R') ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK R' ≫ spMap θ₁ → κ₂ ≫ jK R = jK R' ≫ spMap θ₂ → κ₁ ≫ C.y = κ₂ ≫ C.y → ∀ k, θ₁ (Cn.ψ (MvPolynomial.X k)) = θ₂ (Cn.ψ (MvPolynomial.X k)) := by
  intro E _ _ _ H Dw l Xo c φ hpq hφ hns R _ _ _ hR C Cn R' _ _ _ hR' θ₁ θ₂ i₁ i₂ l₁ l₂ κ₁ κ₂ hκ₁ hκ₂ hy
  have hW := GlobalTheory.T.canonicalFamily_base_injections_agree Xo c φ hpq hφ hns R hR C Cn R' hR' θ₁ θ₂ i₁ i₂ l₁ l₂ κ₁ κ₂ hκ₁ hκ₂ hy
  letI := H.starRing
  have hn : 3 ≤ l.M' := l.three_le.trans (Nat.le_of_dvd (level_pos l) (Nat.dvd_lcm_left _ _))
  have hn1 : 1 ≤ l.M' := by omega
  set iw := Cn.ψ.comp MvPolynomial.C with hiwd
  have hiw : Function.Injective iw := by
    have hfl : iw.Flat := RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 inferInstance) Cn.compl.2.2.1
    letI := iw.toAlgebra
    have : Module.Flat Cn.L.W R := hfl
    have : IsLocalHom (algebraMap Cn.L.W R) := Cn.ψ_loc
    have : Module.FaithfullyFlat Cn.L.W R := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact FaithfulSMul.algebraMap_injective Cn.L.W R
  let s : Fin C.m ⊕ Fin Cn.N → R := fun k => Cn.ψ (MvPolynomial.X k)
  have hs0 : ∀ k, s k ≠ 0 := by
    rintro (k | k)
    · exact (Cn.bd k).trans_ne (C.s_ne_zero k)
    · exact (Cn.tor k).ne_zero
  obtain ⟨hev, hbi, hgen, -⟩ := GlobalTheory.T.degenerationDataNsmulRescale_keeps_laws Cn.L.W Cn.L.D (𝓞 E) Cn.L.oa H.w0 l.M' Cn.L.even Cn.L.bimult Cn.L.w0 Cn.L.gen
  obtain ⟨T, ib, β₀, ββ₀, w₀, hF₀⟩ := GlobalTheory.T.exists_tautologicalBase_nsmul_degenerationData Cn.L.b Cn.L.D Cn.L.bimult Cn.L.gen l.M'
  obtain ⟨g, hD, hg, hxe, -⟩ := Cn.data
  let ε : Fin C.m ⊕ Fin Cn.N → LinearMap.BilinForm ℤ (Fin T.r → ℤ) := fun k =>
    (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X).compl₁₂ ib.symm.toIntLinearEquiv.toLinearMap ib.symm.toIntLinearEquiv.toLinearMap
  have hε : ∀ k a b, ε k (ib a) (ib b) = (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) a b := fun k a b =>
    congrArg₂ (fun x y => (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) x y) (ib.symm_apply_apply a) (ib.symm_apply_apply b)
  let e : C.P.D.toPre.X ≃+ (Fin T.r → ℤ) := Cn.e.toAddEquiv.trans ib
  have he : ∀ y, e y = ib (Cn.e y) := fun _ => rfl
  obtain ⟨β, ββ, w, hF⟩ := GlobalTheory.T.comesFromTautBase_of_rescaled_pullback_monomial T l.M' (mulDeg Cn.L.D l.M') hev hbi hgen ib β₀ ββ₀ w₀ hF₀ R iw hiw C.P.D.toPre g hD
    s ε e (fun y => congrArg ib (hxe y).symm) (fun a a' => by
      simp only [he, hε]
      exact second_diff Cn.e _ (fun k => (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 (hs0 k)) _
        (fun k => (Cn.ε k).2) _ g hg a a')
  have hT : IsGrpPullback Cn.L.o.t.G T.B (𝟙 _) (Cn.L.φB ≫ β₀) :=
    (Cn.L.ab.1.comp hF₀.1).congr ((Category.id_comp _).trans (Spec.map_id _)) rfl
  obtain ⟨V, _, _, _, _, η', f₁, f₂, hV, hη, hf₁, hf₂, lf₁, lf₂, c₁, c₂⟩ :=
    exists_cDvr_two_embeddings R R R' (RingHom.id R) Function.injective_id (RingHom.Finite.id R)
      ⟨hR'.1.1, hR'.1.2.2.1, hR'.1.2.2.2, hR'.2⟩ θ₁ θ₂ i₁ i₂ l₁ l₂
  rw [RingHom.comp_id] at c₁ c₂
  obtain ⟨k₀, hk₀⟩ := exists_genericMap hη
  have hk : ∀ (θ : R →+* R') (κ : Sp (FractionRing R') ⟶ Sp (FractionRing R)), κ ≫ jK R = jK R' ≫ spMap θ →
      (k₀ ≫ κ) ≫ jK R = jK V ≫ spMap (η'.comp θ) := fun θ κ hκ => by
    rw [Category.assoc, hκ, ← Category.assoc, hk₀, Category.assoc, GlobalTheory.GenericBundleDescent.sp_comp]
  obtain ⟨D₁, D₂, hD₁, hD₂, j₁, j₂, b, ph, hE₁, hE₂, hM, hlin, hpairs, -⟩ := pair_match Xo c φ R hR C.toFam V hV f₁ f₂ hf₁ hf₂
    lf₁ lf₂ (k₀ ≫ κ₁) (k₀ ≫ κ₂) (c₁ ▸ hk θ₁ κ₁ hκ₁) (c₂ ▸ hk θ₂ κ₂ hκ₂) (by rw [Category.assoc, hy, Category.assoc])
  obtain ⟨ββ₁, w₁, hF₁⟩ := from_pull T ε l.M' R V _ C.P.D iw s e β ββ w f₁ D₁.toPre hD₁ hf₁ hF
  obtain ⟨ββ₂, w₂, hF₂⟩ := from_pull T ε l.M' R V _ C.P.D iw s e β ββ w f₂ D₂.toPre hD₂ hf₂ hF
  have htaut : ∀ a : Fin T.r → ℤ, ∃ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) l.M')
      (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) l.M'),
      p₁.y = (hD₁.xe.trans e).symm a ∧ TautPt T (f₁.comp iw) (fun k => f₁ (s k)) ε l.M' D₁.toPre (hD₁.xe.trans e)
        ((hD₁.e.hom.left ≫ pullback.fst C.P.D.toPre.P.A.hom (specOf f₁)) ≫ β) ββ₁ w₁ (AlgebraicClosure (FractionRing V)) a p₁.g ∧
      p₂.y = (hD₂.xe.trans e).symm a ∧ TautPt T (f₂.comp iw) (fun k => f₂ (s k)) ε l.M' D₂.toPre (hD₂.xe.trans e)
        ((hD₂.e.hom.left ≫ pullback.fst C.P.D.toPre.P.A.hom (specOf f₂)) ≫ β) ββ₂ w₂ (AlgebraicClosure (FractionRing V)) a p₂.g ∧
      QImg b ph p₁ p₂ := by
    intro a
    obtain ⟨p₀, hp₀y, hp₀⟩ := GlobalTheory.T.periodPart_mem_tautologicalPoint_torsion T ε l.M' R C.P.D.toPre iw s e β ββ w C.P.D.tau_bimult hF hs0
      (AlgebraicClosure (FractionRing R)) a
    obtain ⟨p₁, p₂, hp₁y, hTr₁, hp₂y, hTr₂, hQ⟩ := hpairs p₀
    exact ⟨p₁, p₂, by rw [hp₁y, hp₀y]; rfl,
      GlobalTheory.T.tautologicalPoint_transport_fieldMap T ε l.M' R V _ C.P.D iw s e β ββ w f₁ D₁.toPre hD₁ ββ₁ w₁ hf₁ D₁.tau_bimult hF hF₁ _ _ j₁ hE₁ a _ _ hp₀ hTr₁,
      by rw [hp₂y, hp₀y]; rfl,
      GlobalTheory.T.tautologicalPoint_transport_fieldMap T ε l.M' R V _ C.P.D iw s e β ββ w f₂ D₂.toPre hD₂ ββ₂ w₂ hf₂ D₂.tau_bimult hF hF₂ _ _ j₂ hE₂ a _ _ hp₀ hTr₂,
      hQ⟩

  let ga : C.P.D.toPre.X ≃ₗ[𝓞 E] C.P.D.toPre.X :=
    { (hD₁.xe.symm.trans ph).trans hD₂.xe with map_smul' := hlin }
  have hga : ∀ y, ga y = hD₂.xe (ph (hD₁.xe.symm y)) := fun _ => rfl
  have hbd : ∀ f : R →+* V, Function.Injective f → IsLocalHom f → ∀ k, f (s (.inl k)) ∈ maximalIdeal V ∧ f (s (.inl k)) ≠ 0 :=
    fun f hf hl k => ⟨map_nonunit f _ (show Cn.ψ _ ∈ maximalIdeal R from (Cn.bd k).symm ▸ C.s_mem k),
      (map_ne_zero_iff f hf).2 (hs0 _)⟩
  have hpu := GlobalTheory.T.tautologicalBase_matching_monomials_ratio_unit T ε l.M' V D₁.toPre D₂.toPre _ _ _ _ ββ₁ w₁ _ _ _ _ ββ₂ w₂ b ph _ D₁.tau_bimult D₂.tau_bimult hF₁ hF₂ hM
  obtain ⟨d₁, d₂, hd₁, hd₂, hsum⟩ := GlobalTheory.T.monomials_differ_by_units_positive_boundaryCombination V T.r C.m Cn.N l.M' hn1 ε (fun k => f₁ (s k)) (fun k => f₂ (s k))
    ((e.symm.trans ga.toAddEquiv).trans e).toIntLinearEquiv (hbd f₁ hf₁ lf₁) (fun k => (Cn.tor k).map f₁) (hbd f₂ hf₂ lf₂)
    (fun k => (Cn.tor k).map f₂) (fun a a' => by
      obtain ⟨u, hu⟩ := hpu (hD₁.xe.symm (e.symm a)) (hD₁.xe.symm (e.symm a'))
      simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply] at hu
      exact ⟨u, hu⟩)
  have hδ : ∀ k a a', C.δ k a a' = ε (.inl k) (e a) (e a') := fun k a a' => by rw [he, he, hε, Cn.cone]; rfl
  have hid := lattice_id C.cone (fun x hx => by
      obtain ⟨i, hi⟩ := C.mono.exists_pos (maximalIdeal.isMaximal _).ne_top hx
      exact ⟨i, (mul_pos_iff_of_pos_left (show (0 : ℤ) < l.M' by exact_mod_cast level_pos l)).1 hi⟩) ga d₁ d₂ hd₁ hd₂
    (LinearMap.ext₂ fun a a' => by
      have h := LinearMap.congr_fun₂ hsum (e a) (e a')
      simpa [LinearMap.sum_apply, hδ] using h) hn (fun x => by
      obtain ⟨p₁, p₂, hy₁, -, hy₂, -, p', hp', -, z, hz, -⟩ := htaut (e x)
      have h : hD₂.xe p₂.y = hD₂.xe (ph p₁.y) + l.M' • hD₂.xe z := by rw [hz, map_add, hp', map_nsmul]
      rw [hy₂, hy₁] at h
      refine ⟨-(hD₂.xe z), ?_⟩
      rw [smul_neg, eq_add_neg_iff_add_eq, hga]
      simpa using h.symm)
  have hlat : ∀ y, (hD₂.xe.trans e) (ph y) = (hD₁.xe.trans e) y := fun y => by
    have := hid (hD₁.xe y)
    rw [hga, AddEquiv.symm_apply_apply] at this
    exact congrArg e this

  have hω : f₁.comp iw = f₂.comp iw := by rw [c₁, c₂, RingHom.comp_assoc, RingHom.comp_assoc, hW]
  rw [← hω] at hF₂ htaut
  haveI := hM.2.1
  haveI : IsMonHom (asIso b).hom := hM.1
  have hbsq : IsSquare b.left (lift (fst D₁.toPre.P.A D₁.toPre.P.A ≫ b) (snd D₁.toPre.P.A D₁.toPre.P.A ≫ b) :
      G2 D₁.toPre.P.A ⟶ G2 D₂.toPre.P.A).left :=
    ⟨by rw [← Over.comp_left, lift_fst, Over.comp_left], by rw [← Over.comp_left, lift_snd, Over.comp_left]⟩
  have hLam : ∀ D : DegPre V, (abelian₂ D.P.A D.P.L).IsLB := fun D => LB.isLB_linComb D.P.isLB _ _
  have hLamT : (abelian₂ T.B T.M.L).IsLB := LB.isLB_linComb T.M.isLB _ _
  have hb := GlobalTheory.T.eq_of_mumfordBundle_torsion_presentations V D₁.toPre T.B _ hLamT _ _ _ _ _ hF₁.1
    (((isGrpPullback_of_iso (asIso b)).comp hF₂.1).congr (Category.id_comp _) rfl) hF₁.2.1 (isSquare_comp hbsq hF₂.2.1)
    ⟨w₁, hF₁.2.2.1⟩ (LBIso.trans (hLam _) (pull_isLB (hLam _) _) (pull_isLB hLamT _) hM.2.2.1
      (lbIso_pull_comp ⟨w₂, hF₂.2.2.1⟩ _ rfl)) l.M' hn (AlgebraicClosure (FractionRing V))
    (torsion_fixed hn1 (tors_sec Cn.L.o hT) C.P.D.tau_bimult D₂.tau_bimult hF.1 hω hD₁ hD₂ hE₁ hE₂ hF₁.1 hpairs)
  have key := monomials_eq T ε l.M' V _ D₁.toPre D₂.toPre _ _ _ ββ₁ w₁ _ _ _ ββ₂ w₂ b ph _ hn1 D₁.tau_bimult D₂.tau_bimult
    hF₁ hF₂ hM hlat hb.symm htaut
  let f : V →+* AlgebraicClosure (FractionRing V) := (algebraMap (FractionRing V) _).comp (algebraMap V (FractionRing V))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing V) _).injective.comp (IsFractionRing.injective V (FractionRing V))
  have hx := GlobalTheory.T.eq_of_prod_zpow_eq_balancedForms_basis H Cn.L.D.X _ _ Cn.ε (fun k => f (f₁ (s k))) (fun k => f (f₂ (s k)))
    (fun k => (map_ne_zero_iff _ hf).2 ((map_ne_zero_iff _ hf₁).2 (hs0 k)))
    (fun k => (map_ne_zero_iff _ hf).2 ((map_ne_zero_iff _ hf₂).2 (hs0 k)))
    (fun a a' => by
      have := key (ib a) (ib a')
      simp only [hε] at this
      exact this)
  intro k
  have h1 := hf (congrFun hx k)
  rw [c₁, c₂] at h1
  exact hη h1

end GlobalTheory.UInj
