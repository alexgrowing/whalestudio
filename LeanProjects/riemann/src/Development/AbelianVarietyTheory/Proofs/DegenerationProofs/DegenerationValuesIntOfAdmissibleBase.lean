import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBimultiplicativeOfSecondQuotConst

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.Ex.IntVal

def evR {S : Type} [CommRing S] {Y : Scheme.{0}} (r : Sp S ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ r ⁻¹ᵁ U) : Γ(Y, U) →+* S :=
  (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.comp (r.appLE U ⊤ h).hom

theorem evR_comp {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S') {Y : Scheme.{0}} (r : Sp S ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ r ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap f ≫ r) ⁻¹ᵁ U) (a : Γ(Y, U)) :
    evR (spMap f ≫ r) U h' a = f (evR r U h a) := by
  have e : (spMap f ≫ r).appLE U ⊤ h' = r.appLE U ⊤ h ≫ (spMap f).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE (spMap f) r U ⊤ ⊤ h le_rfl).symm
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)
  have := congrArg (fun q => q.hom ((r.appLE U ⊤ h).hom a)) n
  simp only [evR, e]
  exact this

theorem valF_eq {F : Type} [Field F] {Y : Scheme.{0}} (r : Sp F ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ r ⁻¹ᵁ U) (a : Γ(Y, U)) :
    valF r U a = evR r U h a := dif_pos h

theorem le_comp {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S') {Y : Scheme.{0}} (r : Sp S ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ r ⁻¹ᵁ U) : ⊤ ≤ (spMap f ≫ r) ⁻¹ᵁ U := fun x _ => h (Set.mem_univ ((spMap f) x))

theorem valF_comp {S F : Type} [CommRing S] [Field F] (f : S →+* F) {Y : Scheme.{0}} (r : Sp S ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ r ⁻¹ᵁ U) (a : Γ(Y, U)) : valF (spMap f ≫ r) U a = f (evR r U h a) := by
  rw [valF_eq _ _ (le_comp f r U h), evR_comp f r U h]

theorem ext_unique {F : Type} [Field F] (S : ValuationSubring F) {Y : Scheme.{0}} [Y.IsSeparated] {a b : Sp S ⟶ Y}
    (h : spMap S.subtype ≫ a = spMap S.subtype ≫ b) : a = b := by
  have : IsDominant (spMap S.subtype) := by
    constructor
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical S.subtype).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]; exact bot_le)
  exact ext_of_isDominant _ h

theorem norm_unit {C S : Type} [NormedField C] [CommRing S] (f : S →+* C) (hf : ∀ x, ‖f x‖ ≤ 1) {x : S}
    (hx : IsUnit x) : ‖f x‖ = 1 := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have : ‖f x‖ * ‖f y‖ = 1 := by rw [← norm_mul, ← map_mul, hy, map_one, norm_one]
  have h1 := hf x; have h2 := hf y
  nlinarith [norm_nonneg (f x), norm_nonneg (f y)]

def ball {C S : Type} [NormedField C] [IsUltrametricDist C] [CommRing S] (f : S →+* C) (hf : ∀ x, ‖f x‖ ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) : Ideal S where
  carrier := {x | ‖f x‖ ≤ t}
  zero_mem' := by simpa using ht
  add_mem' := fun {a b} ha hb => by
    show ‖f (a + b)‖ ≤ t
    rw [map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  smul_mem' := fun c x hx => by
    show ‖f (c * x)‖ ≤ t
    rw [map_mul, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf c)).trans hx

theorem exists_radius {C S : Type} [NormedField C] [IsUltrametricDist C] [CommRing S] (f : S →+* C) (hf : ∀ x, ‖f x‖ ≤ 1)
    (I : Ideal S) (hI : I.FG) (h : ∀ x ∈ I, ‖f x‖ < 1) :
    ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ ∀ n : ℕ, ∀ x ∈ I ^ n, ‖f x‖ ≤ t ^ n := by
  obtain ⟨s, rfl⟩ := hI
  obtain ⟨t, h0, h1, ht⟩ : ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ ∀ x ∈ s, ‖f x‖ ≤ t := by
    refine ⟨(s.sup fun x => ‖f x‖₊ : NNReal), NNReal.coe_nonneg _, ?_, fun x hx => ?_⟩
    · have : (s.sup fun x => ‖f x‖₊ : NNReal) < 1 :=
        (Finset.sup_lt_iff (by simp)).2 fun x hx => h x (Ideal.subset_span hx)
      exact_mod_cast this
    · exact_mod_cast Finset.le_sup (f := fun x => ‖f x‖₊) hx
  have hI : Ideal.span (s : Set S) ≤ ball f hf t h0 := Ideal.span_le.2 ht
  refine ⟨t, h0, h1, fun n => ?_⟩
  induction n with
  | zero => intro x _; simpa using hf x
  | succ n ih =>
    have : Ideal.span (s : Set S) ^ n * Ideal.span (s : Set S) ≤ ball f hf (t ^ (n + 1)) (by positivity) :=
      Ideal.mul_le.2 fun a ha b hb => by
        show ‖f (a * b)‖ ≤ _
        rw [map_mul, norm_mul, pow_succ]
        exact mul_le_mul (ih a ha) (hI hb) (norm_nonneg _) (by positivity)
    intro x hx
    rw [pow_succ] at hx
    exact this hx

theorem exists_int {C : Type} [NormedField C] (N : NumD C) (hθ : ∀ x y u, ‖(N.θ x y u : C)‖ = 1)
    (hσ : ∀ x, ‖(N.σ x : C)‖ = 1) (hth : ∀ x, ‖N.th x‖ ≤ 1)
    (hψ : Filter.Tendsto (fun χ => ‖(N.ψ χ : C)‖) Filter.cofinite (nhds 0)) : ∃ q, N.Int q := by
  have pos : ∀ χ, 0 < ‖(N.ψ χ : C)‖ := fun χ => norm_pos_iff.2 (N.ψ χ).ne_zero
  let f : N.X → ℝ := fun χ => -Real.log ‖(N.ψ χ : C)‖
  have ef : ∀ χ, ‖(N.ψ χ : C)‖ = Real.exp (-f χ) := fun χ => by simp [f, Real.exp_log (pos χ)]
  have f0 : f 0 = 0 := by simp [f, N.ψ_zero]
  have he : ∀ x, f (-x) = f x := fun x => by
    have := congrArg (fun u : Cˣ => ‖(u : C)‖) (N.even x)
    simp only [Units.val_mul, norm_mul, hσ, _root_.mul_one] at this
    simp only [f, this]
  have hc : HasConstSecondDiff f := (hasConstSecondDiff_iff f).2 fun a b c => by
    have := congrArg (fun u : Cˣ => ‖(u : C)‖) (N.bimult a b c)
    simp only [Units.val_mul, Units.val_div_eq_div_val, norm_mul, norm_div, hθ, _root_.mul_one, ef, ← Real.exp_sub,
      ← Real.exp_add, Real.exp_eq_exp] at this
    linarith
  refine ⟨hc.quadraticMap he, hθ, hσ, hth, fun χ => by simp [f0, ef], ?_⟩
  have : Filter.Tendsto f Filter.cofinite Filter.atTop :=
    Filter.tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp
      (tendsto_nhdsWithin_iff.2 ⟨hψ, Filter.Eventually.of_forall pos⟩))
  exact this.congr fun χ => by simp [f0]

section Gauge
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F} {ν : NumOf D F N} {S : ValuationSubring F}

theorem isSeparated_left (D : DegPre R) : D.P.A.left.IsSeparated := by
  have := D.P.isAb.proper
  constructor
  rw [← terminal.comp_from D.P.A.hom]
  infer_instance

theorem le_chart (hI : ν.Integral S) (x₀ : Sp S ⟶ D.P.A.left)
    (h : (spMap S.subtype ≫ x₀) ≫ D.P.A.hom = (TF (R := R) F).hom) :
    ⊤ ≤ x₀ ⁻¹ᵁ D.P.L.U (ν.J (spMap S.subtype ≫ x₀)) := by
  obtain ⟨x₁, e, h₁⟩ := hI (Over.homMk (spMap S.subtype ≫ x₀) h)
  have := isSeparated_left D
  obtain rfl : x₁ = x₀ := ext_unique S e
  exact h₁

theorem le_wchart (hI : ν.Integral S) {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ D.P.A.left))
    (r₀ : Sp S ⟶ Y) (h : ∀ k, (spMap S.subtype ≫ r₀) ≫ φ k ≫ D.P.A.hom = (TF (R := R) F).hom) :
    ⊤ ≤ r₀ ⁻¹ᵁ LB.wchart D.P.L φ fun k => ν.J ((spMap S.subtype ≫ r₀) ≫ φ k) := fun y hy =>
  Set.mem_iInter.2 fun k => by
    have := le_chart hI (r₀ ≫ φ k) (by simpa only [Category.assoc] using h k) hy
    rw [← Category.assoc] at this
    exact this

theorem exists_ext (hI : ν.Integral S) (g : R →+* S) (hg : spMap S.subtype ≫ spMap g = (TF (R := R) F).hom)
    (x : TF (R := R) F ⟶ D.P.A) :
    ∃ x₀ : Over.mk (spMap g) ⟶ D.P.A, (Over.homMk (spMap S.subtype) hg : TF (R := R) F ⟶ Over.mk (spMap g)) ≫ x₀ = x := by
  obtain ⟨x₁, e, -⟩ := hI x
  refine ⟨Over.homMk x₁ (ext_unique S ?_), Over.OverMorphism.ext e⟩
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ D.P.A.hom) e).trans ((Over.w x).trans hg.symm))

end Gauge

section Norm
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {C : Type} [NormedField C] [Algebra (FractionRing R) C]
  {N : NumD C} {ν : NumOf D C N} {S : ValuationSubring C}

theorem norm_vF (hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1) (hI : ν.Integral S) {Y : Scheme.{0}} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb D.P.L φ ε)) (r : Sp C ⟶ Y)
    (r₀ : Sp S ⟶ Y) (e : spMap S.subtype ≫ r₀ = r) (h : ∀ k, r ≫ φ k ≫ D.P.A.hom = (TF (R := R) C).hom) :
    ‖vF t r ν.J‖ = 1 := by
  subst e
  refine (congrArg norm (valF_comp S.subtype r₀ _ (le_wchart hI φ r₀ h) _)).trans ?_
  exact norm_unit S.subtype (fun x => (hS _).1 x.2) ((Units.isUnit _).map _)

theorem norm_sF (hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1) (hI : ν.Integral S) {Y : Scheme.{0}} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb D.P.L φ ε)) (r : Sp C ⟶ Y)
    (r₀ : Sp S ⟶ Y) (e : spMap S.subtype ≫ r₀ = r) (h : ∀ k, r ≫ φ k ≫ D.P.A.hom = (TF (R := R) C).hom) :
    ‖sF s r ν.J‖ ≤ 1 := by
  subst e
  refine (congrArg norm (valF_comp S.subtype r₀ _ (le_wchart hI φ r₀ h) _)).trans_le ?_
  exact (hS _).1 (Subtype.prop _)

theorem norm_psi [IsUltrametricDist C] (hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1) (hI : ν.Integral S) (g : R →+* S)
    (hg : spMap S.subtype ≫ spMap g = (TF (R := R) C).hom) (χ : D.X) (J : Ideal R) (hJ : D.PsiIn χ J) (t : ℝ)
    (ht : ∀ x ∈ J, ‖(g x : C)‖ ≤ t) : ‖vF (D.psi χ) (jFK (R := R) C) ν.J‖ ≤ t := by
  have h0 : 0 ≤ t := by simpa using ht 0 J.zero_mem
  have e : spMap S.subtype ≫ spMap g ≫ (D.c χ).left = jFK (R := R) C ≫ D.xK χ := by
    rw [← Category.assoc, hg]; exact Category.assoc _ _ _
  have h1 := le_chart hI (spMap g ≫ (D.c χ).left) (by
    have w : (D.c χ).left ≫ D.P.A.hom = 𝟙 _ := Over.w (D.c χ)
    rw [Category.assoc, Category.assoc, w]
    exact (congrArg (spMap S.subtype ≫ ·) (Category.comp_id _)).trans hg)
  rw [e] at h1
  obtain ⟨_, ⟨V, hV, rfl⟩, hm, hle⟩ := (Sp R).isBasis_affineOpens.exists_subset_of_mem_open
    (a := spMap g (IsLocalRing.closedPoint S)) (u := ((D.c χ).left ⁻¹ᵁ D.P.L.U (ν.J (jFK (R := R) C ≫ D.xK χ)) : (Sp R).Opens))
    (h1 (Set.mem_univ _)) (TopologicalSpace.Opens.isOpen _)
  have hV0 : ⊤ ≤ spMap g ⁻¹ᵁ V := ((IsLocalRing.closed_point_mem_iff (U := spMap g ⁻¹ᵁ V)).1 hm).ge
  have hle' : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U
      (fun _ => ν.J (jFK (R := R) C ≫ D.xK χ)) := fun y hy => Set.mem_iInter.2 fun k => hle hy
  obtain ⟨r, hr, er⟩ := hJ (fun _ => ν.J (jFK (R := R) C ≫ D.xK χ)) V hV hle hle'
  have hV1 := le_comp S.subtype _ _ hV0
  have hV2 : ⊤ ≤ (jFK (R := R) C ≫ jK R) ⁻¹ᵁ V := by rw [hg] at hV1; exact hV1
  have hW : ⊤ ≤ jFK (R := R) C ⁻¹ᵁ LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ)
      (fun _ => ν.J (jFK (R := R) C ≫ D.xK χ)) := fun y hy => hle' (hV2 hy)
  have key : vF (D.psi χ) (jFK (R := R) C) ν.J = S.subtype (evR (spMap g) V hV0 r) := by
    rw [← valF_comp, hg]
    refine (valF_eq _ _ hW _).trans (Eq.trans ?_ (valF_eq _ _ hV2 r).symm)
    have a1 : (jFK (R := R) C ≫ jK R).appLE V ⊤ hV2 = (jK R).app V ≫ (jFK (R := R) C).appLE (jK R ⁻¹ᵁ V) ⊤ hV2 :=
      Scheme.Hom.comp_appLE _ _ _ _ _
    have a2 := (jFK (R := R) C).map_appLE (U := jK R ⁻¹ᵁ V) (V := ⊤) hV2 (homOfLE hle').op
    have a3 := congrArg (fun q => q.hom ((D.psi χ).s fun _ => ν.J (jFK (R := R) C ≫ D.xK χ)).val) a2
    have a4 := congrArg (fun q => q.hom r) a1
    refine congrArg (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom (a3.symm.trans (Eq.trans ?_ a4.symm))
    exact congrArg ((jFK (R := R) C).appLE (jK R ⁻¹ᵁ V) ⊤ hV2).hom er.symm
  rw [key]
  have : J.map (DegPre.toOpen V) ≤ ball (S.subtype.comp (evR (spMap g) V hV0)) (fun x => (hS _).1 (Subtype.prop _)) t h0 :=
    Ideal.map_le_iff_le_comap.2 fun x hx => by
      have : evR (spMap g) V hV0 (DegPre.toOpen V x) = g x := by
        have a2 := (spMap g).map_appLE hV0 (homOfLE (le_top : V ≤ ⊤)).op
        have a3 := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x)) a2
        refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom a3).trans ?_
        have n := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x))
          (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g))
        rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at n
        refine n.trans ?_
        simp
      show ‖S.subtype (evR (spMap g) V hV0 (DegPre.toOpen V x))‖ ≤ t
      rw [this]; exact ht x hx
  exact this hr

end Norm

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (C : Type) [NormedField C] [IsUltrametricDist C] [Algebra (FractionRing R) C], CExt R I C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∃ q, N.Int q := by
  intro R _ _ _ I hR D C _ _ _ hC N ν ⟨S, hS, hI⟩
  let f : R →+* C := (algebraMap (FractionRing R) C).comp (algebraMap R _)
  let g : R →+* S := f.codRestrict S fun x => (hS _).2 (hC.1 x)
  have hg : spMap S.subtype ≫ spMap g = (TF (R := R) C).hom := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  have hrig : ‖vF (L := D.toPre.P.L) (φ := fun _ : PUnit => eSec D.toPre.P.A) (ε := fun _ => 1) D.toPre.rig
      (TF (R := R) C).hom ν.J‖ = 1 :=
    norm_vF hS hI _ _ (spMap g) hg fun _ =>
      (congrArg ((TF (R := R) C).hom ≫ ·) (Over.w η[D.toPre.P.A])).trans (Category.comp_id _)
  refine exists_int N (fun x y u => ?_) (fun x => ?_) (fun x => ?_) ?_
  · obtain ⟨x₀, hx⟩ := exists_ext hI g hg (ν.eA x)
    obtain ⟨y₀, hy⟩ := exists_ext hI g hg (ν.eA y)
    obtain ⟨u₀, hu⟩ := exists_ext hI g hg (ν.eA u)
    rw [ν.θ_eq]
    refine norm_vF hS hI _ _ (lift x₀ (lift y₀ u₀)).left ?_ fun k => ?_
    · rw [← hx, ← hy, ← hu, ← comp_lift, ← comp_lift]; rfl
    · exact (congrArg (_ ≫ ·) (Over.w _)).trans (Over.w _)
  · obtain ⟨x₀, hx⟩ := exists_ext hI g hg (ν.eA x)
    rw [ν.σ_eq]
    refine norm_vF hS hI _ _ x₀.left (congrArg CommaMorphism.left hx) fun k => ?_
    fin_cases k
    · exact (congrArg (_ ≫ ·) (Over.w ι[D.toPre.P.A])).trans (Over.w _)
    · exact (congrArg (_ ≫ ·) (Category.id_comp _)).trans (Over.w _)
  · obtain ⟨x₀, hx⟩ := exists_ext hI g hg (ν.eA x)
    have := congrArg norm (ν.th_eq x)
    rw [norm_mul, hrig, _root_.mul_one] at this
    rw [this]
    exact norm_sF hS hI _ _ x₀.left (congrArg CommaMorphism.left hx) fun k =>
      (congrArg (_ ≫ ·) (Category.id_comp _)).trans (Over.w _)
  · have := hR.1
    obtain ⟨t, h0, h1, ht⟩ := exists_radius f hC.1 I (IsNoetherian.noetherian I) hC.2
    refine Metric.tendsto_nhds.2 fun δ hδ => ?_
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ h1
    refine Filter.eventually_cofinite.2 (((D.psi_tendsto n).preimage ν.eX.injective.injOn).subset fun χ hχ h => hχ ?_)
    rw [dist_zero_right, norm_norm, ν.ψ_eq, norm_mul, hrig, _root_.mul_one]
    exact (norm_psi hS hI g hg _ _ h _ (ht n)).trans_lt hn

end GlobalTheory.Ex.IntVal
end
