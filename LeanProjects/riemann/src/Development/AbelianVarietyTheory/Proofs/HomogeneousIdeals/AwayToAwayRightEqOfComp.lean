import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsResEqOfUnitInChart

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)

namespace GlobalTheory.SqZero

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {S S' A : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
  [CommRing A] [Algebra R A]

abbrev tanExp (v : Fin n → (epsR R ⟶ G)) (s : Fin n → S) : sp (R₀ := R) (DualNumber S) ⟶ G :=
  lieExp v (fun i => (inr (s i) : DualNumber S)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)

variable (S) in

def IsLieBasisOver (v : Fin n → (epsR R ⟶ G)) : Prop :=
  (∀ s s' : Fin n → S, tanExp v s = tanExp v s' → s = s') ∧
    ∀ w : sp (R₀ := R) (DualNumber S) ⟶ G, IsTanOver w → ∃ s, w = tanExp v s

variable (A) in

def ExpBij (v : Fin n → (epsR R ⟶ G)) : Prop :=
  ∀ J : Ideal A, J ^ 2 = ⊥ →
    (∀ (c c' : Fin n → A), (∀ i, c i ∈ J) → (∀ i, c' i ∈ J) → ∀ hc hc',
      lieExp v c hc = lieExp v c' hc' → c = c') ∧
    ∀ y ∈ redKer G J, ∃ (c : Fin n → A) (hc : ∀ i, c i * c i = 0),
      (∀ i, c i ∈ J) ∧ y = lieExp v c hc

variable {v : Fin n → (epsR R ⟶ G)}

theorem res_tanExp (ρ : S →ₐ[R] S') (s : Fin n → S) :
    res ρ (tanExp v s) = tanExp v fun i => ρ (s i) := by
  rw [res, comp_lieExp]
  exact lieExp_congr _ (fun i => dualMap_inr _ _) _ _

theorem scl_tanExp (t : S) (s : Fin n → S) :
    scl t (tanExp v s) = tanExp v fun i => s i * t := by
  rw [scl, comp_lieExp]
  exact lieExp_congr _ (fun i => dualScale_inr _ _) _ _

theorem isTanOver_tanExp (hv : ∀ i, IsTangent (v i)) (s : Fin n → S) :
    IsTanOver (tanExp v s) := by
  rw [IsTanOver, comp_lieExp]
  exact lieExp_eq_one hv _ (fun i => rfl) _

theorem isLieBasisOver_self (hv : IsLieBasis v) : IsLieBasisOver R v := by
  refine ⟨fun s s' h => ?_, fun w hw => ?_⟩
  · exact (hv.2 _ ((isTan_iff _).1 (isTanOver_tanExp hv.1 s))).unique
      ((isLieComb_iff_lieExp _ _).2 rfl) ((isLieComb_iff_lieExp _ _).2 h)
  · obtain ⟨c, hc, -⟩ := hv.2 w ((isTan_iff _).1 hw)
    exact ⟨c, (isLieComb_iff_lieExp _ _).1 hc⟩

variable [Smooth G.hom]

theorem IsLieBasisOver.away (hv : ∀ i, IsTangent (v i)) (h : IsLieBasisOver S v)
    {ρ : S →ₐ[R] S'} {g : S} (hρ : IsAway ρ g) : IsLieBasisOver S' v := by
  refine ⟨fun s s' e => ?_, fun w' hw' => ?_⟩
  · obtain ⟨N, a, ha⟩ := hρ.surj_fin (Sum.elim s s')
    have e₁ : res ρ (tanExp v fun i => a (.inl i)) = res ρ (tanExp v fun i => a (.inr i)) := by
      rw [res_tanExp, res_tanExp]
      simp only [← ha, Sum.elim_inl, Sum.elim_inr]
      rw [← scl_tanExp, ← scl_tanExp, e]
    obtain ⟨M, hM⟩ := exists_scl_eq hρ (isTanOver_tanExp hv _) (isTanOver_tanExp hv _) e₁
    rw [scl_tanExp, scl_tanExp] at hM
    funext i
    have e₂ := congrArg ρ (congrFun (h.1 _ _ hM) i)
    simp only [map_mul, map_pow, ← ha, Sum.elim_inl, Sum.elim_inr] at e₂
    exact (hρ.unit.pow N).mul_right_cancel ((hρ.unit.pow M).mul_right_cancel e₂)
  · obtain ⟨N, w, hw, e⟩ := exists_res_eq hρ hw'
    obtain ⟨s, rfl⟩ := h.2 w hw
    obtain ⟨t, ht⟩ := (hρ.unit.pow N).exists_left_inv
    refine ⟨fun i => ρ (s i) * t, ?_⟩
    rw [← scl_tanExp, ← res_tanExp, e, scl_scl, ht, scl_one]

theorem expBij_of_unitInChart (hv : ∀ i, IsTangent (v i)) (hS : UnitInChart G S)
    (h : IsLieBasisOver S v) (α : S →ₐ[R] A) : ExpBij A v := by
  obtain ⟨B, _, _, j, u, hj, hu⟩ := hS
  have := smooth_of_chart j
  obtain ⟨κ, _, β, τ, hτ⟩ := exists_ders R B
  let E := TrivSqZeroExt S (Fin n → S)
  let e : Fin n → E := fun i => inr (Pi.single i 1)
  have he : ∀ i j, e i * e j = 0 := fun i j => TrivSqZeroExt.inr_mul_inr _ _ _
  obtain ⟨χ, hχ, hχu⟩ := exists_chart_of_mem_redKer j
    ((TrivSqZeroExt.inlAlgHom R S (Fin n → S)).comp u)
    (by rw [← spMap_comp, Category.assoc, hu, comp_one']) (ker_fst_sq (R := R) (S := S) (Fin n → S))
    (lieExp_mem_redKer hv e (fun i => rfl) fun i => he i i)
  have hχu' : ∀ b, (χ b).fst = u b := fun b => by
    simpa [RingHom.mem_ker, sub_eq_zero] using hχu b
  have F : ∀ {T : Type} [CommRing T] [Algebra R T] (θ : S →ₐ[R] T) (c : Fin n → T)
      (hc : ∀ i k, c i * c k = 0),
      lieExp v c (fun i => hc i i) = spMap ((vecTo θ c hc).comp χ) ≫ j := by
    intro T _ _ θ c hc
    rw [← spMap_comp, Category.assoc, ← hχ, comp_lieExp]
    exact lieExp_congr _ (fun i => (vecTo_single θ c hc i).symm) _ _
  have Finr : ∀ s : Fin n → S, tanExp v s = spMap ((vecTo (inlS R S) (fun i => inr (s i))
      (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)).comp χ) ≫ j := fun s => F _ _ _
  have ha : ∀ i, ∃ a : Fin n → S, ∀ b, u (τ i b) = ∑ k, (χ b).snd k * a k := by
    intro i
    classical
    let t : κ → DualNumber S := fun k => inr (if k = i then 1 else 0)
    have ht : ∀ k l, t k * t l = 0 := fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _
    obtain ⟨a, ha⟩ := h.2 (spMap (addDers τ ((inlS R S).comp u) t ht) ≫ j) (by
      rw [IsTanOver, ← Category.assoc, spMap_comp, ← hu]
      congr 2
      ext b
      simp [addDers_apply, TrivSqZeroExt.fst_sum, t])
    rw [Finr] at ha
    refine ⟨a, fun b => ?_⟩
    have := congrArg TrivSqZeroExt.snd (AlgHom.congr_fun (chart_inj j ha) b)
    simpa [addDers_apply, vecTo_apply, TrivSqZeroExt.snd_sum, t, mul_comm] using this
  choose a ha using ha
  have hX : ∀ b k, (χ b).snd k = ∑ i, u (τ i b) * (χ (β i)).snd k := by
    intro b k
    have := congrFun (congrArg TrivSqZeroExt.snd (hτ _ χ
      ((TrivSqZeroExt.inlAlgHom R S (Fin n → S)).comp u)
      (fun b b' => by ext <;> simp [hχu']) b)) k
    simpa [TrivSqZeroExt.snd_sum, hχu'] using this
  have hδ : ∀ k, (fun l => ∑ i, a i l * (χ (β i)).snd k) = Pi.single k 1 := by
    intro k
    refine h.1 _ _ ?_
    rw [Finr, Finr]
    congr 2
    refine AlgHom.ext fun b => TrivSqZeroExt.ext
      (by simp [vecTo_apply, TrivSqZeroExt.fst_sum]) ?_
    have : ∑ l, (χ b).snd l * ∑ i, a i l * (χ (β i)).snd k = (χ b).snd k := by
      rw [hX b k]
      simp only [ha, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
    simpa [vecTo_apply, TrivSqZeroExt.snd_sum, Pi.single_apply, mul_comm] using this
  intro J hJ
  refine ⟨fun c c' hcJ hcJ' hc hc' hcc => ?_, fun y hy => ?_⟩
  · rw [F α c fun i k => mul_eq_zero_of_sq hJ (hcJ i) (hcJ k),
      F α c' fun i k => mul_eq_zero_of_sq hJ (hcJ' i) (hcJ' k)] at hcc
    have e₁ : ∀ b, ∑ k, α ((χ b).snd k) * c k = ∑ k, α ((χ b).snd k) * c' k := fun b => by
      simpa [vecTo_apply] using AlgHom.congr_fun (chart_inj j hcc) b
    have e₂ : ∀ (d : Fin n → A) l, d l = ∑ i, α (a i l) * ∑ k, α ((χ (β i)).snd k) * d k := by
      intro d l
      simp only [Finset.mul_sum, ← mul_assoc, ← map_mul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, ← map_sum]
      have : ∀ k, ∑ i, a i l * (χ (β i)).snd k = (Pi.single k 1 : Fin n → S) l :=
        fun k => congrFun (hδ k) l
      simp [this, Pi.single_apply, apply_ite]
    funext l
    rw [e₂ c l, e₂ c' l]
    simp only [e₁]
  · obtain ⟨φ, rfl, hφ⟩ := exists_chart_of_mem_redKer j (α.comp u)
      (by rw [← spMap_comp, Category.assoc, hu, comp_one']) hJ hy
    let c : Fin n → A := fun k => ∑ i, α (a i k) * (φ (β i) - α (u (β i)))
    have hcJ : ∀ k, c k ∈ J := fun k => sum_mem fun i _ => J.mul_mem_left _ (hφ _)
    refine ⟨c, fun k => mul_eq_zero_of_sq hJ (hcJ k) (hcJ k), hcJ, ?_⟩
    rw [F α c fun i k => mul_eq_zero_of_sq hJ (hcJ i) (hcJ k)]
    congr 2
    ext b
    have := hτ A φ (α.comp u) (fun b b' => mul_eq_zero_of_sq hJ (hφ b) (hφ b')) b
    rw [AlgHom.comp_apply, vecTo_apply, hχu', ← sub_eq_iff_eq_add']
    refine this.trans ?_
    simp only [AlgHom.comp_apply, ha, map_sum, map_mul, c, Finset.mul_sum, Finset.sum_mul,
      mul_assoc]
    exact Finset.sum_comm

theorem awayToAwayRight_eq_of_comp (f g : A)
    (a : Localization.Away f →ₐ[R] Localization.Away (f * g))
    (ha : a.comp (awayHom R f) = awayHom R (f * g)) (x : Localization.Away f) :
    IsLocalization.Away.awayToAwayRight (P := Localization.Away (f * g)) f g x = a x := by
  have : IsLocalization.Away.awayToAwayRight (S := Localization.Away f)
      (P := Localization.Away (f * g)) f g = a.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext y
    rw [RingHom.comp_apply, IsLocalization.Away.awayToAwayRight_eq]
    exact (AlgHom.congr_fun ha y).symm
  rw [this]
  rfl

theorem awayToAwayLeft_eq_of_comp (f g : A)
    (b : Localization.Away g →ₐ[R] Localization.Away (f * g))
    (hb : b.comp (awayHom R g) = awayHom R (f * g)) (x : Localization.Away g) :
    IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f * g)) g f x = b x := by
  have : IsLocalization.Away.awayToAwayLeft (S := Localization.Away g)
      (P := Localization.Away (f * g)) g f = b.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    ext y
    rw [RingHom.comp_apply, IsLocalization.Away.awayToAwayLeft_eq]
    exact (AlgHom.congr_fun hb y).symm
  rw [this]
  rfl

omit [Smooth G.hom] in
theorem expBij_of_span {s : Set A} (hs : Ideal.span s = ⊤)
    (h : ∀ f ∈ s, ∀ (T : Type) [CommRing T] [Algebra R T] (φ : A →ₐ[R] T), IsUnit (φ f) →
      ExpBij T v) : ExpBij A v := by
  intro J hJ
  have hs' : Ideal.span (Set.range (Subtype.val : s → A)) = ⊤ := by
    rwa [Subtype.range_coe_subtype]
  let q : ∀ f : s, A →ₐ[R] Localization.Away f.1 := fun f => awayHom R f.1
  have hq : ∀ f : s, IsAway (q f) f.1 := fun f => isAway_awayHom _
  have hb := fun f : s => h f f.2 _ (q f) (hq f).unit (J.map (q f)) (map_sq hJ _)
  refine ⟨fun c c' hcJ hcJ' hc hc' hcc => funext fun i => ?_, fun y hy => ?_⟩
  · refine Localization.algebraMap_injective_of_span_eq_top s hs (funext fun f => ?_)
    have := congrArg (spMap (q f) ≫ ·) hcc
    simp only [comp_lieExp] at this
    exact congrFun ((hb f).1 _ _ (fun i => Ideal.mem_map_of_mem _ (hcJ i))
      (fun i => Ideal.mem_map_of_mem _ (hcJ' i)) _ _ this) i
  · choose d hd hdJ ed using fun f : s => (hb f).2 _
      (comp_mem_redKer hy (q f) fun a ha => Ideal.mem_map_of_mem _ ha)
    have compat : ∀ (i : Fin n) (f g : s),
        IsLocalization.Away.awayToAwayRight (P := Localization.Away (f * g : A)) f.1 g (d f i) =
          IsLocalization.Away.awayToAwayLeft g.1 f (d g i) := by
      intro i f g
      let p := awayHom R (f * g : A)
      have hp : IsAway p (f * g : A) := isAway_awayHom _
      have hpf : IsUnit (p f) := isUnit_of_mul_isUnit_left (by rw [← map_mul]; exact hp.unit)
      obtain ⟨a, ha⟩ := (hq f).lift p hpf
      obtain ⟨b, hb⟩ := (hq g).lift p
        (isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact hp.unit))
      rw [awayToAwayRight_eq_of_comp f.1 g.1 a ha, awayToAwayLeft_eq_of_comp f.1 g.1 b hb]
      have e : spMap a ≫ lieExp v (d f) (hd f) = spMap b ≫ lieExp v (d g) (hd g) := by
        rw [← ed, ← ed, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, ha, hb]
      rw [comp_lieExp, comp_lieExp] at e
      refine congrFun ((h f f.2 _ p hpf (J.map p) (map_sq hJ _)).1 _ _ (fun k => ?_) (fun k => ?_)
        _ _ e) i
      · rw [← ha, ← Ideal.map_mapₐ]
        exact Ideal.mem_map_of_mem _ (hdJ f k)
      · rw [← hb, ← Ideal.map_mapₐ]
        exact Ideal.mem_map_of_mem _ (hdJ g k)
    choose c hc using fun i => (Localization.existsUnique_algebraMap_eq_of_span_eq_top s hs
      (fun f => d f i) (compat i)).exists
    have hcJ : ∀ i, c i ∈ J := fun i =>
      Submodule.mem_of_span_eq_top_of_smul_pow_mem J s hs _ fun f =>
        (hq f).pow_mul_mem (by
          have : q f (c i) = d f i := hc i f
          rw [this]
          exact hdJ f i)
    refine ⟨c, fun i => mul_eq_zero_of_sq hJ (hcJ i) (hcJ i), hcJ,
      away_ext hs' q hq fun f => ?_⟩
    rw [ed, comp_lieExp]
    exact lieExp_congr _ (fun i => (hc i f).symm) _ _

variable (A) in

theorem expBij (hv : IsLieBasis v) : ExpBij A v := by
  refine expBij_of_span
    (s := Algebra.ofId R A '' {g : R | UnitInChart G (Localization.Away g)}) ?_ ?_
  · rw [← Ideal.map_span, span_unitInChart, Ideal.map_top]
  · rintro _ ⟨g, hg, rfl⟩ T _ _ φ hφ
    have hρ := isAway_awayHom (R := R) g
    obtain ⟨α, -⟩ := hρ.lift (φ.comp (Algebra.ofId R A)) hφ
    exact expBij_of_unitInChart hv.1 hg ((isLieBasisOver_self hv).away hv.1 hρ) α

end GlobalTheory.SqZero
