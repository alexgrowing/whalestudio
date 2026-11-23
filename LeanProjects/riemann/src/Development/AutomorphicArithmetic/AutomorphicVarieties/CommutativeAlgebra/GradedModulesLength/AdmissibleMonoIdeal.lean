import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LaDifPerm
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.FrobeniusInclusionXEqMulQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ReesGradedPieceSurjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LkHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.GrEqRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.FgHolds
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleMono
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleCong

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R] (𝒜 : Deg k → Submodule B R)

private theorem self_isGr [GradedAlgebra 𝒜] : (GMod.self 𝒜).IsGr 𝒜 where
  smul_mem {d m a x} ha hx := by
    have h : a * (show R from x) ∈ 𝒜 (d + m) := SetLike.mul_mem_graded ha hx
    exact h
  internal := DirectSum.Decomposition.isInternal 𝒜
  fin := Module.Finite.self R

private theorem mem_quo_ann_of_smul_mem {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R] (F : GMod B R k)
    (N : Submodule R F.M) (x : R) (h : ∀ y : F.M, x • y ∈ N) : x ∈ (F.quo N).Ann := by
  rw [GMod.Ann, Module.mem_annihilator]
  intro m
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  exact (Submodule.Quotient.mk_smul _ x y).symm.trans ((Submodule.Quotient.mk_eq_zero _).mpr (h y))

private theorem le_ann_quo (J : Ideal R) : J ≤ ((GMod.self 𝒜).quo J).Ann := by
  intro x hx
  exact mem_quo_ann_of_smul_mem (GMod.self 𝒜) J x fun (y : R) => J.mul_mem_right y hx

private theorem mem_ann_quot (F : GMod B R k) (s : R) : s ∈ (F.quot s).Ann := by
  rw [GMod.Ann, Module.mem_annihilator]
  intro m
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  exact (Submodule.Quotient.mk_smul _ s y).symm.trans
    ((Submodule.Quotient.mk_eq_zero _).mpr ⟨y, rfl⟩)

private theorem secs_le_sup_secs_of_forall₂_sub_mem {k : ℕ} {R : Type} [CommRing R] {J' : Ideal R} :
    ∀ {ts ts' : List (Deg k × R)}, List.Forall₂ (fun p q => p.1 = q.1 ∧ p.2 - q.2 ∈ J') ts ts' →
      secs ts ≤ J' ⊔ secs ts'
  | _, _, .nil => by simp [secs]
  | p :: l, q :: l', .cons hpq hl => by
    have ih := secs_le_sup_secs_of_forall₂_sub_mem hl
    have hsub : secs l' ≤ secs (q :: l') :=
      Ideal.span_mono fun s ⟨d, hd⟩ => ⟨d, List.mem_cons_of_mem _ hd⟩
    have hq : q.2 ∈ secs (q :: l') := Ideal.subset_span ⟨q.1, List.mem_cons_self ..⟩
    rw [secs, Ideal.span_le]
    rintro s ⟨d, hd⟩
    rcases List.mem_cons.mp hd with h | h
    · subst h
      have hs : s = (s - q.2) + q.2 := by ring
      rw [hs]
      exact Ideal.add_mem _ (Ideal.mem_sup_left hpq.2) (Ideal.mem_sup_right hq)
    · exact sup_le_sup_left hsub _ (ih (Ideal.subset_span ⟨d, h⟩))

private theorem admissible_mono_ideal [IsLocalRing B] {ts ts' : List (Deg k × R)} {J J' : Ideal R} (h : admitted 𝒜 ts J) (hJ : J ≤ J')
    (ht : List.Forall₂ (fun p q => p.1 = q.1 ∧ p.2 - q.2 ∈ J') ts ts') : admitted 𝒜 ts' J' := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, hN.trans (sup_le (hJ.trans le_sup_left) (secs_le_sup_secs_of_forall₂_sub_mem ht))⟩

end

private theorem exists_surjective_graded_quot_to_quo {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R] (F0 : GMod B R k)
    (J Q : Submodule R F0.M) (hle : J ≤ Q) (a : R) (haQ : ∀ x : F0.M, a • x ∈ Q) (hQ : F0.IsHomSub Q) :
    ∃ g : ((F0.quo J).quot a).M →ₗ[R] (F0.quo Q).M, Function.Surjective g ∧
      (∀ m, (F0.quo Q).gr m = Submodule.map (g.restrictScalars B) (((F0.quo J).quot a).gr m)) ∧
      ((F0.quo J).quot a).IsHomSub (LinearMap.ker g) := by
  let g1 : (F0.quo J).M →ₗ[R] (F0.quo Q).M := Submodule.factor hle
  let N : Submodule R (F0.quo J).M := (LinearMap.lsmul R (F0.quo J).M a).range
  have hN : N ≤ LinearMap.ker g1 := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective J y
    have h0 : (Submodule.Quotient.mk (a • x) : F0.M ⧸ Q) = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr (haQ x)
    exact h0
  let g : ((F0.quo J).quot a).M →ₗ[R] (F0.quo Q).M := N.liftQ g1 hN
  refine ⟨g, ?_, ?_, ?_⟩
  · intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective Q z
    exact ⟨Submodule.Quotient.mk (Submodule.Quotient.mk x), rfl⟩
  · intro m
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Submodule.Quotient.mk (Submodule.Quotient.mk x), ⟨Submodule.Quotient.mk x, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨v, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  · unfold GMod.IsHomSub
    apply le_antisymm
    · intro z hz
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      have hz' : (Submodule.Quotient.mk x : F0.M ⧸ Q) = 0 := hz
      have hxQ : x ∈ Q := (Submodule.Quotient.mk_eq_zero Q).mp hz'
      let π : F0.M →ₗ[R] ((F0.quo J).quot a).M := N.mkQ ∘ₗ J.mkQ
      have hS : Q ≤ Submodule.comap π
          (Submodule.span R {x | x ∈ LinearMap.ker g ∧ ∃ m, x ∈ ((F0.quo J).quot a).gr m}) := by
        refine (le_of_eq hQ).trans ?_
        rw [Submodule.span_le]
        rintro s ⟨hsQ, m, hsm⟩
        show π s ∈ Submodule.span R _
        apply Submodule.subset_span
        have hs0 : (Submodule.Quotient.mk s : F0.M ⧸ Q) = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr hsQ
        exact ⟨hs0, m, ⟨Submodule.Quotient.mk s, ⟨s, hsm, rfl⟩, rfl⟩⟩
      exact hS hxQ
    · exact Submodule.span_le.mpr fun x hx => hx.1

private theorem mono_quo {k : ℕ} (X : HidaSetting k) (J 𝔮 : Ideal X.R) (hJ : (GMod.self X.𝒜).IsHomSub J)
    (h𝔮 : (GMod.self X.𝒜).IsHomSub 𝔮) (hle : J ≤ 𝔮) (a : X.R) (ha0 : a ∈ X.𝒜 0) (ha : a ∈ 𝔮)
    (ts : List (Deg k × X.R)) (hts : Valid X.𝒜 ts) (hadm : admitted X.𝒜 ts (J ⊔ Ideal.span {a})) :
    ∀ᶠ m in atTop, chi ts ((GMod.self X.𝒜).quo 𝔮) m ≤ chi ts (((GMod.self X.𝒜).quo J).quot a) m := by
  obtain ⟨g, hgs, hgr, hker⟩ :=
    exists_surjective_graded_quot_to_quo (GMod.self X.𝒜) J 𝔮 hle a (fun (x : X.R) => 𝔮.mul_mem_right x ha) h𝔮
  have hS := self_isGr X.𝒜
  have hFJ := quo_isGr X.𝒜 hS hJ
  have hF := ((ruleGr k X ((GMod.self X.𝒜).quo J) hFJ).2.2 0 a ha0).1
  have hF'' := quo_isGr X.𝒜 hS h𝔮
  have hF' := ((ruleGr k X _ hF).1 (LinearMap.ker g) hker).1
  have ses : SES ((((GMod.self X.𝒜).quo J).quot a).sub (LinearMap.ker g))
      (((GMod.self X.𝒜).quo J).quot a) ((GMod.self X.𝒜).quo 𝔮) :=
    ⟨(LinearMap.ker g).subtype, g, Submodule.injective_subtype _, hgs, LinearMap.exact_subtype_ker_map g,
      fun m => rfl, hgr⟩
  have hann : J ⊔ Ideal.span {a} ≤ (((GMod.self X.𝒜).quo J).quot a).Ann :=
    sup_le ((le_ann_quo X.𝒜 J).trans (Cong.ann_le_quot _ a))
      ((Ideal.span_singleton_le_iff_mem _).mpr (mem_ann_quot _ a))
  have hadm' := admissible_mono_ideal X.𝒜 hadm hann (List.forall₂_same.mpr fun p _ => ⟨rfl, by simp⟩)
  exact ruleMono k X ts _ _ _ hts hF' hF hF'' ses hadm'

private theorem coef_hom {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ} (N : Fin k → Submodule B A)
    (J : Ideal A) : (GMod.self (reesGr N)).IsHomSub (coefIdeal N J) := by
  classical
  refine le_antisymm (fun p hp => ?_) (Submodule.span_le.2 fun w hw => hw.1)
  rw [eq_sum_mono N p]
  refine Submodule.sum_mem _ fun m _ => Submodule.subset_span ⟨fun n => ?_, _, mono_mem N m _ _⟩
  show MvPolynomial.coeff n (MvPolynomial.monomial m _) ∈ J
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · exact hp m
  · exact zero_mem _

private theorem e_nn {k : ℕ} (i : Fin k) : 0 ≤ e i := by
  intro j
  simp only [e, Pi.zero_apply]
  rcases eq_or_ne j i with rfl | h
  · simp
  · simp [Pi.single_apply, h]

private theorem dif_congr {k : ℕ} (h h' : Deg k → ℤ) (hh : ∀ᶠ d in atTop, h d = h' d) (L : List (Deg k)) :
    ∀ᶠ d in atTop, dif L h d = dif L h' d := by
  induction L with
  | nil =>
    filter_upwards [hh] with d hd
    rw [dif.eq_1, dif.eq_1, hd]
  | cons a ds ih =>
    have ht : Tendsto (fun d : Deg k => d - a) atTop atTop :=
      tendsto_atTop_atTop.mpr fun b => ⟨b + a, fun d hd => le_sub_iff_add_le.mpr hd⟩
    filter_upwards [ih, ht.eventually ih] with d h1 h2
    rw [dif.eq_2, dif.eq_2, h1, h2]

private theorem sec_congr' {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ}
    (N : Fin k → Submodule B A) (i : Fin k) {f f' : A} (h : f ∈ N i) (h' : f' ∈ N i) (hff : f = f') :
    sec N i f h = sec N i f' h' := by
  subst hff
  rfl

private theorem sec_smul_eq_algebraMap_mul_sec {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ}
    (N : Fin k → Submodule B A) (i : Fin k) (b : B) (f : A) (hf : f ∈ N i) (hbf : b • f ∈ N i) :
    sec N i (b • f) hbf = algebraMap B (rees N) b * sec N i f hf := by
  apply Subtype.ext
  show MvPolynomial.monomial _ (b • f) = algebraMap B (MvPolynomial (Fin k) A) b * MvPolynomial.monomial _ f
  rw [MvPolynomial.algebraMap_apply, MvPolynomial.C_mul_monomial, Algebra.smul_def]

private theorem quo_smul_eq_zero_imp_eq_zero_of_regular {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R] (F : GMod B R k)
    (N : Submodule R F.M) (t : R) (h : ∀ y : F.M, t • y ∈ N → y ∈ N) :
    ∀ z : (F.quo N).M, t • z = 0 → z = 0 := by
  intro z hz
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hz' : (Submodule.Quotient.mk (t • y) : F.M ⧸ N) = 0 := hz
  exact (Submodule.Quotient.mk_eq_zero _).mpr (h y ((Submodule.Quotient.mk_eq_zero _).mp hz'))

private theorem list_forall₂_ofFn {α β : Type} {R : α → β → Prop} :
    ∀ {n : ℕ} (f : Fin n → α) (g : Fin n → β), (∀ i, R (f i) (g i)) → List.Forall₂ R (List.ofFn f) (List.ofFn g)
  | 0, f, g, _ => by simp
  | n + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ]
    exact .cons (h 0) (list_forall₂_ofFn _ _ fun i => h i.succ)

theorem UpperTheory.V.Alg.M.low_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ (τ : Type) [Fintype τ] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart0 𝒜 x wt φ →
    1 ≤ r → (∀ j, Nat.card {i // wt i = j} = mDims r s r' s' 0 j) → ∀ ϖ : O, Irreducible ϖ →
    ∀ (y : Fin r → A) (c : Fin r → ℕ), (∀ i, y i ∈ 𝒜 (-1) ∧ Q.F i.castSucc - ϖ ^ c i • y i ∈ satSq x) → Q.F (Fin.last r) ∈ satSq x →
    ∀ a : 𝒜 0, x a = 0 →
      admitted (mGr Q) (ts Q) (coefIdeal _ (RingHom.ker φ) ⊔ Ideal.span {algebraMap (𝒜 0) (mR Q) a}) →
      ∀ᶠ d in atTop, ((∑ i, c i : ℕ) : ℤ) * 2 ^ (r + r') ≤
        chi (ts Q) ((mQ Q (coefIdeal _ (RingHom.ker φ))).quot (algebraMap (𝒜 0) (mR Q) a)) d := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q τ _ wt φ hφ hr hdim ϖ hϖ y c hy hlast a ha hadm
  classical
  have hfg : ∀ i, (mN 𝒜 (Q.F (Fin.last r)) i).FG := by
    intro i
    fin_cases i
    · exact fg_holds O A 𝒜 x hW (-2)
    · exact fg_holds O A 𝒜 x hW 2
    · exact (Submodule.fg_span_singleton _).sup
        (((fg_holds O A 𝒜 x hW (-2)).mul (fg_holds O A 𝒜 x hW (-2))).mul (fg_holds O A 𝒜 x hW 2))
  let X : HidaSetting 3 := HidaSetting.mk (𝒜 0) (mR Q) (mGr Q) (std_holds (𝒜 0) A 3 _ hfg)
  obtain ⟨𝔮, h𝔮lead, h𝔮hom, hJ𝔮, h𝔮x, h𝔮reg, h𝔮sq⟩ := lk_holds O A 𝒜 x hW r s r' s' m Q τ wt φ hφ hlast
  have hF : GMod.IsGr (mGr Q) ((GMod.self (mGr Q)).quo 𝔮) := quo_isGr (mGr Q) (self_isGr (mGr Q)) h𝔮hom
  have ha0 : algebraMap (𝒜 0) (mR Q) a ∈ mGr Q 0 := SetLike.algebraMap_mem_graded _ _
  have haq : algebraMap (𝒜 0) (mR Q) a ∈ 𝔮 := h𝔮x a ha
  have hvalR : Valid (mGr Q) (tsR Q) := by
    intro p hp
    simp only [tsR, List.mem_append, List.mem_ofFn, List.mem_singleton] at hp
    rcases hp with ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | rfl
    · exact ⟨e_nn _, sec_mem _ _ _ (Q.hG i)⟩
    · exact ⟨e_nn _, sec_mem _ _ _ (sq_mem_pos 𝒜 (Q.hE i))⟩
    · exact ⟨e_nn _, sec_mem _ _ _ (Q.hE' i)⟩
    · exact ⟨e_nn _, sec_mem _ _ _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))⟩
  have hvalF : Valid (mGr Q) (tsF Q) := by
    intro p hp
    simp only [tsF, List.mem_ofFn] at hp
    obtain ⟨i, rfl⟩ := hp
    exact ⟨e_nn _, sec_mem _ _ _ (sq_mem_neg 𝒜 (Q.hF _))⟩
  have hval : Valid (mGr Q) (ts Q) := by
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact hvalF p h
    · exact hvalR p h
  have hup := mono_quo X (coefIdeal _ (RingHom.ker φ)) 𝔮 (coef_hom _ _) h𝔮hom hJ𝔮 _ ha0 haq (ts Q) hval hadm
  have hy2 : ∀ i, y i ^ 2 ∈ mN 𝒜 (Q.F (Fin.last r)) 0 := fun i => sq_mem_neg 𝒜 (hy i).1
  have hreg := quo_smul_eq_zero_imp_eq_zero_of_regular (GMod.self (mGr Q)) 𝔮 (algebraMap (𝒜 0) (mR Q) (algebraMap O (𝒜 0) ϖ))
    (fun (p : mR Q) hp => h𝔮reg ϖ hϖ.ne_zero p hp)
  have hadm0 : admitted (mGr Q) []
      (((GMod.self (mGr Q)).quo 𝔮).quot (algebraMap (𝒜 0) (mR Q) (algebraMap O (𝒜 0) ϖ))).Ann := by
    refine ⟨1, ?_⟩
    rw [pow_one]
    refine le_trans Ideal.mul_le_left (le_trans ?_ le_sup_left)
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap]
    have hxb : res0 𝒜 x b ∈ maximalIdeal O := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨v, hv⟩ := hu.exists_right_inv
      have hm : b * algebraMap O (𝒜 0) v ∈ maximalIdeal (𝒜 0) := Ideal.mul_mem_right _ _ hb
      have h1 : IsUnit (1 - b * algebraMap O (𝒜 0) v) := by
        by_contra hn
        have hn' : 1 - b * algebraMap O (𝒜 0) v ∈ maximalIdeal (𝒜 0) := (IsLocalRing.mem_maximalIdeal _).mpr hn
        have h1m := Ideal.add_mem _ hn' hm
        rw [sub_add_cancel] at h1m
        exact (maximalIdeal.isMaximal (𝒜 0)).ne_top ((Ideal.eq_top_iff_one _).mpr h1m)
      have h2 := h1.map (res0 𝒜 x)
      rw [map_sub, map_one, map_mul, AlgHom.commutes, Algebra.algebraMap_self_apply, hv, sub_self] at h2
      exact not_isUnit_zero h2
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp
      (((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ) ▸ hxb)
    have hc : x ↑(b - algebraMap O (𝒜 0) (res0 𝒜 x b)) = 0 := by
      change res0 𝒜 x (b - algebraMap O (𝒜 0) (res0 𝒜 x b)) = 0
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
    have hcq := h𝔮x _ hc
    have hb' : algebraMap (𝒜 0) (mR Q) b = algebraMap (𝒜 0) (mR Q) (b - algebraMap O (𝒜 0) (res0 𝒜 x b)) +
        algebraMap (𝒜 0) (mR Q) (algebraMap O (𝒜 0) ϖ) * algebraMap (𝒜 0) (mR Q) (algebraMap O (𝒜 0) u) := by
      rw [← hu, map_sub, map_mul, map_mul]
      ring
    rw [hb']
    refine Ideal.add_mem _ ((Cong.ann_le_quot _ _) (le_ann_quo (mGr Q) 𝔮 hcq)) ?_
    exact Ideal.mul_mem_right _ _ (mem_ann_quot _ _)
  have hkey : ∀ i : Fin r, ∀ h : (ϖ ^ c i • y i) ^ 2 ∈ mN 𝒜 (Q.F (Fin.last r)) 0,
      sec (mN 𝒜 (Q.F (Fin.last r))) 0 ((ϖ ^ c i • y i) ^ 2) h =
        algebraMap (𝒜 0) (mR Q) (algebraMap O (𝒜 0) ϖ) ^ (2 * c i) *
          sec (mN 𝒜 (Q.F (Fin.last r))) 0 (y i ^ 2) (hy2 i) := by
    intro i h
    have hs : (algebraMap O (𝒜 0) ϖ) ^ (2 * c i) • y i ^ 2 ∈ mN 𝒜 (Q.F (Fin.last r)) 0 :=
      Submodule.smul_mem _ _ (hy2 i)
    have heq : ((ϖ ^ c i • y i) ^ 2 : A) = (algebraMap O (𝒜 0) ϖ) ^ (2 * c i) • y i ^ 2 := by
      rw [smul_pow, ← map_pow, algebraMap_smul, ← pow_mul, mul_comm (c i) 2]
    rw [sec_congr' _ 0 h hs heq, sec_smul_eq_algebraMap_mul_sec _ 0 _ _ (hy2 i) hs, map_pow]
  have hrel : List.Forall₂ (fun p q => p.1 = q.1 ∧ p.2 - q.2 ∈ ((GMod.self (mGr Q)).quo 𝔮).Ann) (ts Q)
      (List.ofFn (fun i => (e 0, algebraMap (𝒜 0) (mR Q) (algebraMap O (𝒜 0) ϖ) ^ (2 * c i) *
        sec (mN 𝒜 (Q.F (Fin.last r))) 0 (y i ^ 2) (hy2 i))) ++ tsR Q) := by
    refine List.rel_append ?_ (List.forall₂_same.mpr fun p _ => ⟨rfl, by simp⟩)
    refine list_forall₂_ofFn _ _ fun i => ⟨rfl, ?_⟩
    have hg : ϖ ^ c i • y i ∈ 𝒜 (-1) := Submodule.smul_mem _ _ (hy i).1
    have h := h𝔮sq (Q.F i.castSucc) (ϖ ^ c i • y i) (Q.hF _) hg (hy i).2
    have h' := hkey i (sq_mem_neg 𝒜 hg)
    refine le_ann_quo (mGr Q) 𝔮 ?_
    convert h using 2
    exact h'.symm
  have hJa : coefIdeal _ (RingHom.ker φ) ⊔ Ideal.span {algebraMap (𝒜 0) (mR Q) a} ≤
      ((GMod.self (mGr Q)).quo 𝔮).Ann :=
    sup_le (hJ𝔮.trans (le_ann_quo (mGr Q) 𝔮))
      ((Ideal.span_singleton_le_iff_mem _).mpr (le_ann_quo (mGr Q) 𝔮 haq))
  have hadmF := admissible_mono_ideal (mGr Q) hadm hJa hrel
  have hla := la_holds 3 X ((GMod.self (mGr Q)).quo 𝔮) hF (algebraMap O (𝒜 0) ϖ) hreg hadm0 (e 0) (e_nn 0) r
    (fun i => sec (mN 𝒜 (Q.F (Fin.last r))) 0 (y i ^ 2) (hy2 i)) (fun i => 2 * c i)
    (fun i => sec_mem _ _ _ _) (tsR Q) hvalR hadmF
  have hhilb : ∀ᶠ d in atTop, hilb (((GMod.self (mGr Q)).quo 𝔮).quot
      (algebraMap (𝒜 0) (mR Q) (algebraMap O (𝒜 0) ϖ))) d = cnt wt (2 * d 0 + 4 * d 2) (2 * d 1 + 2 * d 2) := by
    filter_upwards [eventually_ge_atTop 0] with d hd
    exact hf_holds O A 𝒜 x hW r s r' s' m Q τ wt φ hφ hlast 𝔮 h𝔮lead ϖ hϖ d hd
  have hdif := dif_congr _ _ hhilb (List.replicate (r - 1) (e 0) ++ List.map Prod.fst (tsR Q))
  have hnum := num_holds τ wt r s r' s' hr hdim
  have hmap : List.map Prod.fst (tsR Q) =
      List.replicate s (e 0) ++ List.replicate r' (e 1) ++ List.replicate s' (e 1) ++ [e 2] := by
    simp [tsR, List.map_ofFn, Function.comp_def, List.ofFn_const]
    rw [← List.append_assoc, List.replicate_append_replicate]
  have hchi := Cong.chi_cong ((GMod.self (mGr Q)).quo 𝔮) hrel
  have harith : ((∑ i, c i : ℕ) : ℤ) * 2 ^ (r + r') = ((∑ i, 2 * c i : ℕ) : ℤ) * 2 ^ (r - 1 + r') := by
    have hr' : r + r' = (r - 1 + r') + 1 := by omega
    rw [hr', pow_succ, ← Finset.mul_sum]
    push_cast
    ring
  filter_upwards [hup, hla, hdif, hnum] with d h1 h2 h3 h4
  rw [h3, hmap, h4, ← hchi] at h2
  calc ((∑ i, c i : ℕ) : ℤ) * 2 ^ (r + r') = ((∑ i, 2 * c i : ℕ) : ℤ) * 2 ^ (r - 1 + r') := harith
    _ ≤ chi (ts Q) ((GMod.self (mGr Q)).quo 𝔮) d := h2
    _ ≤ _ := h1
