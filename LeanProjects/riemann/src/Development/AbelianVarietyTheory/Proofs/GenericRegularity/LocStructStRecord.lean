import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
import Formalism.LocalToGlobal.ProjectiveLattices.CurveSec
import Formalism.LocalToGlobal.ProjectiveLattices.SecPtRed
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EfRankSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.RApprox
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FinrankHostDivTwo
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenericSectionPointsInequivalentValuationsStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IntegralElementsGenericLinearSectionGaussPointStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SubalgebraEqIntegralClosureOfValuesResiduesStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRatioFormsAtPointsStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GaussValuationDensityGenerationLocalisationStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsSubfieldValuationClosureStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralCongrWeakApproximationStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.Reg.UnitBall

def castHom {ι : Type} {Ω : ι → Type} [∀ Z, Field (Ω Z)] {U : Type} [Field U] {Z Z' : ι} (h : Z = Z')
    (f : Ω Z →+* U) : Ω Z' →+* U := h ▸ f

theorem castHom_apply {ι : Type} {Ω : ι → Type} [∀ Z, Field (Ω Z)] {U : Type} [Field U] {Z Z' : ι} (h : Z = Z')
    (f : Ω Z →+* U) (a : ∀ Z, Ω Z) : castHom h f (a Z') = f (a Z) := by
  subst h; rfl

theorem core {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] {ϖ : O}
    (hU : IsUnif A ϖ) [∀ ζ : Pts O A, IsDVRAt ζ] [Finite (Pts O A)] [Module.Finite O ↥(As O A)]
    (C : Subalgebra O A) (hC : C ≤ As O A)
    {ι : Type} {Ω : ι → Type} [∀ Z, Field (Ω Z)] (Zc : Pts O A → ι) {U : Pts O A → Type} [∀ ζ, Field (U ζ)]
    (v : ∀ ζ, Valuation (U ζ) (WithZero (Multiplicative ℤ))) (φ : ∀ ζ, A →+* U ζ) (jz : ∀ ζ, Ω (Zc ζ) →+* U ζ)
    (hord : ∀ ζ x, (φ ζ x = 0 ∧ ord ϖ ζ x = ⊤) ∨
      ∃ n : ℤ, v ζ (φ ζ x) = WithZero.exp (-n) ∧ ord ϖ ζ x = (n : WithTop ℤ))
    (hconst : ∀ a : ∀ Z, Ω Z, (∀ ζ, v ζ (jz ζ (a (Zc ζ))) ≤ 1) → ∃ c ∈ C, ∀ ζ, φ ζ c = jz ζ (a (Zc ζ)))
    (hgen : ∀ ζ, ∃ a, v ζ (jz ζ a) = WithZero.exp 1)
    (hsep : ∀ ζ ζ', ζ ≠ ζ' → Zc ζ = Zc ζ' →
      ∃ a : ∀ Z, Ω Z, v ζ (jz ζ (a (Zc ζ))) < 1 ∧ v ζ' (jz ζ' (a (Zc ζ'))) = 1)
    (hres : ∀ ζ, ∃ Tz : Set (U ζ), (∀ u ∈ Tz, ∃ c ∈ C, φ ζ c = u) ∧ ∀ b ∈ As O A,
      ∃ a ∈ Subring.closure ({u | u ∈ Set.range (jz ζ) ∧ v ζ u ≤ 1} ∪ Tz),
      ∃ d ∈ Subring.closure ({u | u ∈ Set.range (jz ζ) ∧ v ζ u ≤ 1} ∪ Tz),
        v ζ d = 1 ∧ v ζ (φ ζ b * d - a) < 1) :
    As O A ≤ C := by
  classical
  have hint : ∀ ζ, ∀ x ∈ As O A, v ζ (φ ζ x) ≤ 1 := fun ζ x hx => by
    have h0 := ord_nonneg ζ hU hx
    rcases hord ζ x with ⟨h1, -⟩ | ⟨n, h1, h2⟩
    · rw [h1, map_zero]; exact zero_le
    · rw [h2] at h0
      have : (0 : ℤ) ≤ n := by exact_mod_cast h0
      rw [h1, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  have hval : ∀ ζ x (n : ℤ), v ζ (φ ζ x) = WithZero.exp (-n) → ord ϖ ζ x = (n : WithTop ℤ) := fun ζ x n h => by
    rcases hord ζ x with ⟨h1, -⟩ | ⟨m, h1, h2⟩
    · rw [h1, map_zero] at h; exact absurd h.symm WithZero.exp_ne_zero
    · rw [h1, WithZero.exp_inj] at h
      rw [h2, show m = n by omega]
  have hpos : ∀ ζ x, v ζ (φ ζ x) < 1 → 0 < ord ϖ ζ x := fun ζ x h => by
    rcases hord ζ x with ⟨-, h2⟩ | ⟨m, h1, h2⟩
    · rw [h2]; exact WithTop.coe_lt_top 0
    · rw [h1, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
      rw [h2]; exact_mod_cast (show (0 : ℤ) < m by omega)
  let w : ∀ Z, {ζ // Zc ζ = Z} → Valuation (Ω Z) (WithZero (Multiplicative ℤ)) := fun Z ζ => (v ζ.1).comap (castHom ζ.2 (jz ζ.1))
  have hw : ∀ Z (ζ : {ζ // Zc ζ = Z}) (a : ∀ Z, Ω Z), w Z ζ (a Z) = v ζ.1 (jz ζ.1 (a (Zc ζ.1))) :=
    fun Z ζ a => by
      show v ζ.1 (castHom ζ.2 (jz ζ.1) (a Z)) = _
      rw [castHom_apply]
  have hwgen : ∀ Z (ζ : {ζ // Zc ζ = Z}), ∃ x, w Z ζ x =
      ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rintro Z ⟨ζ, rfl⟩
    exact hgen ζ
  have hwind : ∀ Z (ζ ζ' : {ζ // Zc ζ = Z}), ζ ≠ ζ' → ¬ (w Z ζ).IsEquiv (w Z ζ') := by
    intro Z ζ ζ' hne heq
    obtain ⟨a, h1, h2⟩ := hsep ζ.1 ζ'.1 (fun h => hne (Subtype.ext h)) (ζ.2.trans ζ'.2.symm)
    rw [← hw Z ζ a] at h1
    rw [← hw Z ζ' a] at h2
    have := (Valuation.isEquiv_iff_val_lt_one.1 heq).1 h1
    rw [h2] at this
    exact lt_irrefl _ this
  refine GlobalTheory.T.subalgebra_eq_integralClosure_of_values_residues O A ϖ hU C hC (fun n => ?_) (fun ζ b hb => ?_)
  · have hex : ∀ Z, ∃ x : Ω Z, ∀ ζ : {ζ // Zc ζ = Z}, w Z ζ x = WithZero.exp (-(n ζ.1 : ℤ)) := fun Z => by
      haveI := Fintype.ofFinite {ζ // Zc ζ = Z}
      exact ReciprocityTheory.ChartRestriction.G.Lift.exists_val_eq (w Z) (hwgen Z) (hwind Z) (fun ζ => -(n ζ.1 : ℤ))
    choose a ha using hex
    have ha' : ∀ ζ, v ζ (jz ζ (a (Zc ζ))) = WithZero.exp (-(n ζ : ℤ)) := fun ζ =>
      (hw _ ⟨ζ, rfl⟩ a).symm.trans (ha _ ⟨ζ, rfl⟩)
    obtain ⟨c, hc, hca⟩ := hconst a fun ζ => by
      rw [ha', ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    exact ⟨c, hc, fun ζ => hval ζ c _ (by rw [hca, ha'])⟩
  · obtain ⟨Tz, hT, hb'⟩ := hres ζ
    have key : ∀ u ∈ Subring.closure ({u | u ∈ Set.range (jz ζ) ∧ v ζ u ≤ 1} ∪ Tz),
        ∃ c ∈ C, v ζ (u - φ ζ c) < 1 := by
      intro u hu
      induction hu using Subring.closure_induction with
      | mem u hu =>
        rcases hu with ⟨⟨x, rfl⟩, hx⟩ | hu
        · obtain ⟨x', h1, h2⟩ := GlobalTheory.T.exists_integral_congr_weak_approximation (Ω (Zc ζ)) _ (w (Zc ζ)) (hwgen _) (hwind _) ⟨ζ, rfl⟩ x hx
          let a : ∀ Z, Ω Z := Function.update (fun _ => 0) (Zc ζ) x'
          have haζ : a (Zc ζ) = x' := Function.update_self _ _ _
          obtain ⟨c, hc, hca⟩ := hconst a fun ζ' => by
            by_cases hz : Zc ζ' = Zc ζ
            · rw [← hw (Zc ζ) ⟨ζ', hz⟩ a, haζ]; exact h1 _
            · rw [show a (Zc ζ') = 0 from Function.update_of_ne hz _ _, map_zero, map_zero]; exact zero_le
          refine ⟨c, hc, ?_⟩
          rw [hca, haζ, ← map_sub]
          exact h2
        · obtain ⟨c, hc, rfl⟩ := hT u hu
          exact ⟨c, hc, by rw [sub_self, map_zero]; exact zero_lt_one⟩
      | zero => exact ⟨0, C.zero_mem, by rw [map_zero, sub_self, map_zero]; exact zero_lt_one⟩
      | one => exact ⟨1, C.one_mem, by rw [map_one, sub_self, map_zero]; exact zero_lt_one⟩
      | add x y _ _ hx hy =>
        obtain ⟨c, hc, h1⟩ := hx
        obtain ⟨c', hc', h2⟩ := hy
        refine ⟨c + c', C.add_mem hc hc', ?_⟩
        rw [map_add, add_sub_add_comm]
        exact (v ζ).map_add_lt h1 h2
      | neg x _ hx =>
        obtain ⟨c, hc, h1⟩ := hx
        refine ⟨-c, C.neg_mem hc, ?_⟩
        rw [map_neg, ← neg_sub', Valuation.map_neg]
        exact h1
      | mul x y _ _ hx hy =>
        obtain ⟨c, hc, h1⟩ := hx
        obtain ⟨c', hc', h2⟩ := hy
        refine ⟨c * c', C.mul_mem hc hc', ?_⟩
        have e : x * y - φ ζ (c * c') = (x - φ ζ c) * (y - φ ζ c') + ((x - φ ζ c) * φ ζ c' + φ ζ c * (y - φ ζ c')) := by
          rw [map_mul]; ring
        have i1 := hint ζ c (hC hc)
        have i2 := hint ζ c' (hC hc')
        rw [e]
        refine (v ζ).map_add_lt ?_ ((v ζ).map_add_lt ?_ ?_) <;> rw [map_mul]
        · exact lt_of_le_of_lt (mul_le_of_le_one_right' h2.le) h1
        · exact lt_of_le_of_lt (mul_le_of_le_one_right' i2) h1
        · exact lt_of_le_of_lt (mul_le_of_le_one_left' i1) h2
    obtain ⟨a, ha, d, hd, hd1, hab⟩ := hb' b hb
    obtain ⟨c, hc, h1⟩ := key a ha
    obtain ⟨c', hc', h2⟩ := key d hd
    refine ⟨c, hc, c', hc', ?_, hpos ζ _ ?_⟩
    · have : v ζ (φ ζ c') = 1 := by
        have e : φ ζ c' = d + -(d - φ ζ c') := by ring
        rw [e, (v ζ).map_add_eq_of_lt_left (by rw [Valuation.map_neg, hd1]; exact h2), hd1]
      exact hval ζ c' 0 (by rw [this]; rfl)
    · have e : φ ζ (c' * b - c) = (φ ζ b * d - a) + ((a - φ ζ c) + -(φ ζ b * (d - φ ζ c'))) := by
        rw [map_sub, map_mul]; ring
      rw [e]
      refine (v ζ).map_add_lt hab ((v ζ).map_add_lt h1 ?_)
      rw [Valuation.map_neg, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint ζ b hb)) h2

theorem ord_cases {T : CDVR} {o : WithTop ℤ} {u : T.Fr} (h : toE o = nval T.V 1 u) :
    (u = 0 ∧ o = ⊤) ∨ ∃ n : ℤ, valV T.V u = WithZero.exp (-n) ∧ o = (n : WithTop ℤ) := by
  by_cases hu : u = 0
  · subst hu
    rw [nval_zero] at h
    exact Or.inl ⟨rfl, toE_eq_top h⟩
  · right
    rw [nval_of_ne hu] at h
    refine ⟨vV T.V u, ?_, ?_⟩
    · rw [vV, neg_neg, WithZero.exp_log (valV_ne_zero hu)]
    · cases o with
      | top => exact absurd h.symm (EReal.coe_ne_top _)
      | coe n =>
        have h' : ((n : ℝ) : EReal) = _ := h
        rw [EReal.coe_eq_coe_iff, Nat.cast_one, div_one] at h'
        have : n = vV T.V u := by exact_mod_cast h'
        rw [this]

theorem nval_nonneg_iff {T : CDVR} {u : T.Fr} : 0 ≤ nval T.V 1 u ↔ valV T.V u ≤ 1 := by
  by_cases hu : u = 0
  · subst hu; rw [nval_zero, map_zero]; exact ⟨fun _ => zero_le, fun _ => le_top⟩
  · rw [nval_of_ne hu, EReal.coe_nonneg, Nat.cast_one, div_one, ← WithZero.exp_log (valV_ne_zero (V := T.V) hu),
      ← WithZero.exp_zero, WithZero.exp_le_exp, vV]
    constructor
    · intro h
      have : (0 : ℤ) ≤ -WithZero.log (valV T.V u) := by exact_mod_cast h
      omega
    · intro h
      exact_mod_cast (show (0 : ℤ) ≤ -WithZero.log (valV T.V u) by omega)

theorem valV_lt_of_nval_lt {T : CDVR} {u u' : T.Fr} (hu' : u' ≠ 0) (h : nval T.V 1 u' < nval T.V 1 u) :
    valV T.V (u / u') < 1 := by
  rw [map_div₀, div_lt_one₀ (zero_lt_iff.2 (valV_ne_zero hu'))]
  by_cases hu : u = 0
  · subst hu; rw [map_zero]; exact zero_lt_iff.2 (valV_ne_zero hu')
  · rw [nval_of_ne hu, nval_of_ne hu', EReal.coe_lt_coe_iff, Nat.cast_one, div_one, div_one] at h
    have h' : vV T.V u' < vV T.V u := by exact_mod_cast h
    rw [← WithZero.exp_log (valV_ne_zero (V := T.V) hu), ← WithZero.exp_log (valV_ne_zero (V := T.V) hu'),
      WithZero.exp_lt_exp]
    simp only [vV] at h'
    omega

section Rec

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}

def phiPt {ζ : PtsG G la} {y₀ : E.Pt' la} (h : SecPt ζ y₀) : OsK (xplus X E hM) la G.w →+* h.T.Fr :=
  Ideal.Quotient.lift (Jid (xplus X E hM) la G.w) (h.lift.comp (Frac0 (xplus X E hM) la G.w).val.toRingHom) (fun _ hr => h.lift_Jid hr)

theorem phiPt_to {ζ : PtsG G la} {y₀ : E.Pt' la} (h : SecPt ζ y₀) (x : ↥(Frac0 (xplus X E hM) la G.w)) :
    phiPt h (toOsK (xplus X E hM) la G.w x) = h.lift (x : Lw (xplus X E hM) la G.w) := rfl

theorem ord_phiPt {ζ : PtsG G la} {y₀ : E.Pt' la} (h : SecPt ζ y₀) (a : OsK (xplus X E hM) la G.w) :
    toE (ord (unifO (xplus X E hM) la G.N) ζ a) = nval h.T.V 1 (phiPt h a) := by
  obtain ⟨x, rfl⟩ := toOsK_surjective (xplus X E hM) la G.w a
  exact h.ord x

theorem phiPt_Kp {ζ : PtsG G la} {y₀ : E.Pt' la} (h : SecPt ζ y₀) (c : Kp (xplus X E hM) la G.N) :
    phiPt h (algebraMap (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) c) = h.ev (algebraMap (Kp (xplus X E hM) la G.N) (Rp (xplus X E hM) la G.N) c) := by
  rw [← (toOsK (xplus X E hM) la G.w).commutes c, phiPt_to, ← h.lift_alg, ← IsScalarTower.algebraMap_apply]
  rfl

theorem phiPt_int (hU : IsUnif (OsK (xplus X E hM) la G.w) (unifO (xplus X E hM) la G.N)) {ζ : PtsG G la} [IsDVRAt ζ] {y₀ : E.Pt' la}
    (h : SecPt ζ y₀) {a : OsK (xplus X E hM) la G.w} (ha : a ∈ As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) :
    valV h.T.V (phiPt h a) ≤ 1 := by
  have h0 := ord_nonneg ζ hU ha
  rcases ord_cases (ord_phiPt h a) with ⟨h1, -⟩ | ⟨n, h1, h2⟩
  · rw [h1, map_zero]; exact zero_le
  · rw [h2] at h0
    have : (0 : ℤ) ≤ n := by exact_mod_cast h0
    rw [h1, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega

theorem ord_nonneg_of {ζ : PtsG G la} {y₀ : E.Pt' la}
    (h : SecPt ζ y₀) {a : OsK (xplus X E hM) la G.w} (ha : valV h.T.V (phiPt h a) ≤ 1) :
    0 ≤ ord (unifO (xplus X E hM) la G.N) ζ a := by
  rcases ord_cases (ord_phiPt h a) with ⟨-, h2⟩ | ⟨n, h1, h2⟩
  · rw [h2]; exact le_top
  · rw [h1, ← WithZero.exp_zero, WithZero.exp_le_exp] at ha
    rw [h2]; exact_mod_cast (show (0 : ℤ) ≤ n by omega)

variable {y : PtsG G la → E.Pt' la} (hs : ∀ ζ, SecPt ζ (y ζ))

theorem op_mem_RGL (hU : IsUnif (OsK (xplus X E hM) la G.w) (unifO (xplus X E hM) la G.N)) [∀ ζ : PtsG G la, IsDVRAt ζ] (o : Op (xplus X E hM) la G.N) :
    ιW hs (algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) (algebraMap (Kp (xplus X E hM) la G.N) (Rp (xplus X E hM) la G.N)
      (algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) o))) ∈ RGL hs := by
  refine mem_RGL_of_stable hs (S := Set.range fun o : Op (xplus X E hM) la G.N =>
    ιW hs (algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) (algebraMap (Kp (xplus X E hM) la G.N) (Rp (xplus X E hM) la G.N)
      (algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) o)))) ?_ ?_ ⟨o, rfl⟩
  · rintro β _ ⟨o, rfl⟩
    refine ⟨hasseOp (xplus X E hM) la G.N β o, ?_⟩
    show _ = hdL hs β (ιW hs _)
    rw [hdW_ι]
    refine congrArg (ιW hs) ?_
    refine Eq.trans ?_ (hasse_algebraMap (xplus X E hM) la G.w β _).symm
    rw [hasseRp_algebraMap, hasseKp_algebraMap]
    rfl
  · rintro _ ⟨o, rfl⟩ ζ
    show 0 ≤ nval _ 1 (evL hs ζ (ιW hs _))
    rw [evW_ι, (hs ζ).lift_alg, ← phiPt_Kp, nval_nonneg_iff]
    exact phiPt_int hU (hs ζ) ((As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)).algebraMap_mem o)

def liftable (hU : IsUnif (OsK (xplus X E hM) la G.w) (unifO (xplus X E hM) la G.N)) [∀ ζ : PtsG G la, IsDVRAt ζ] :
    Subalgebra (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) where
  carrier := {a | ∃ f d : ↥(Frac0 (xplus X E hM) la G.w), (∀ ζ, (hs ζ).lift (d : Lw (xplus X E hM) la G.w) ≠ 0) ∧
    toOsK (xplus X E hM) la G.w f = toOsK (xplus X E hM) la G.w d * a ∧ ∃ r ∈ RGL hs, ιW hs (f : Lw (xplus X E hM) la G.w) = r * ιW hs (d : Lw (xplus X E hM) la G.w)}
  mul_mem' := by
    rintro a b ⟨f, d, hd, he, r, hr, hf⟩ ⟨f', d', hd', he', r', hr', hf'⟩
    refine ⟨f * f', d * d', fun ζ => ?_, ?_, r * r', (RGL hs).mul_mem hr hr', ?_⟩
    · rw [Subalgebra.coe_mul, map_mul]; exact mul_ne_zero (hd ζ) (hd' ζ)
    · rw [map_mul, map_mul, he, he']; ring
    · rw [Subalgebra.coe_mul, Subalgebra.coe_mul, map_mul, map_mul, hf, hf']; ring
  add_mem' := by
    rintro a b ⟨f, d, hd, he, r, hr, hf⟩ ⟨f', d', hd', he', r', hr', hf'⟩
    refine ⟨f * d' + d * f', d * d', fun ζ => ?_, ?_, r + r', (RGL hs).add_mem hr hr', ?_⟩
    · rw [Subalgebra.coe_mul, map_mul]; exact mul_ne_zero (hd ζ) (hd' ζ)
    · rw [map_add, map_mul, map_mul, map_mul, he, he']; ring
    · rw [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_mul, Subalgebra.coe_mul, map_add, map_mul, map_mul,
        map_mul, hf, hf']; ring
  algebraMap_mem' o := by
    refine ⟨algebraMap (Kp (xplus X E hM) la G.N) _ (algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) o), 1, fun ζ => ?_, ?_, _,
      op_mem_RGL hs hU o, ?_⟩
    · rw [Subalgebra.coe_one, map_one]; exact one_ne_zero
    · rw [map_one, one_mul, AlgHom.commutes]; rfl
    · rw [Subalgebra.coe_one, map_one, mul_one, ← IsScalarTower.algebraMap_apply (Kp (xplus X E hM) la G.N) (Rp (xplus X E hM) la G.N)]
      rfl

theorem liftable_le (hU : IsUnif (OsK (xplus X E hM) la G.w) (unifO (xplus X E hM) la G.N)) [∀ ζ : PtsG G la, IsDVRAt ζ] :
    liftable hs hU ≤ As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) := by
  rintro a ⟨f, d, hd, he, r, hr, hf⟩
  rw [mem_As_iff hU]
  intro ζ
  refine ord_nonneg_of (hs ζ) ?_
  have h1 := congrArg (phiPt (hs ζ)) he
  rw [map_mul, phiPt_to, phiPt_to] at h1
  have h2 := congrArg (evL hs ζ) hf
  rw [map_mul, evW_ι, evW_ι, h1, mul_comm] at h2
  rw [mul_right_cancel₀ (hd ζ) h2, ← nval_nonneg_iff]
  exact RGL_int hs hr ζ

theorem isUnit_of_ne (hfd : FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))
    (hU : IsUnif (OsK (xplus X E hM) la G.w) (unifO (xplus X E hM) la G.N)) [∀ ζ : PtsG G la, IsDVRAt ζ] {a : OsK (xplus X E hM) la G.w}
    (ha : ∀ ζ, phiPt (hs ζ) a ≠ 0) : IsUnit a := by
  haveI : IsArtinianRing (OsK (xplus X E hM) la G.w) := IsArtinianRing.of_finite (Kp (xplus X E hM) la G.N) _
  refine IsArtinianRing.isUnit_of_mem_nonZeroDivisors ?_
  rw [mem_nonZeroDivisors_iff_right]
  intro c hc
  refine eq_zero_of_ord_top hU c fun ζ => ?_
  have h1 := congrArg (phiPt (hs ζ)) hc
  rw [map_mul, map_zero] at h1
  have h2 := ord_phiPt (hs ζ) c
  rw [(mul_eq_zero.1 h1).resolve_right (ha ζ), nval_zero] at h2
  exact toE_eq_top h2

theorem eFormL_isCst (F : X.Forms) : Tay.IsCst (tayL hs) (eFormL hs F) :=
  Tay.loc_isCst _ _ _ _ (Tay.loc_isCst _ _ _ _ (tayRp_isCst_emb (xplus X E hM) la F))

theorem ratio_liftable (hfd : FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))
    (hU : IsUnif (OsK (xplus X E hM) la G.w) (unifO (xplus X E hM) la G.N)) [∀ ζ : PtsG G la, IsDVRAt ζ] (k : ℕ)
    (F F' : B.Cusp j (addL (wt0 D j) wL k)) (u : ∀ ζ, (hs ζ).T.Fr) (hu : ∀ ζ, valV (hs ζ).T.V (u ζ) ≤ 1)
    (h : ∀ ζ, (hs ζ).ev (emb (xplus X E hM) la G.N (X.inc _ F')) ≠ 0 ∧
      (hs ζ).ev (emb (xplus X E hM) la G.N (X.inc _ F)) = u ζ * (hs ζ).ev (emb (xplus X E hM) la G.N (X.inc _ F'))) :
    ∃ c ∈ liftable hs hU, ∀ ζ, phiPt (hs ζ) c = u ζ := by
  let f := CurveLoc.fr0 (xplus X E hM) la G.N G.w k (X.inc _ F) (emb_mem_Vw (xplus X E hM) la G.N _ F)
  let d := CurveLoc.fr0 (xplus X E hM) la G.N G.w k (X.inc _ F') (emb_mem_Vw (xplus X E hM) la G.N _ F')
  have hf : ∀ ζ, (hs ζ).lift (f : Lw (xplus X E hM) la G.w) =
      (hs ζ).ev (emb (xplus X E hM) la G.N (X.inc _ F)) * ((hs ζ).ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0))⁻¹ ^ k := fun ζ => (hs ζ).lift_frac k _
  have hd : ∀ ζ, (hs ζ).lift (d : Lw (xplus X E hM) la G.w) =
      (hs ζ).ev (emb (xplus X E hM) la G.N (X.inc _ F')) * ((hs ζ).ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0))⁻¹ ^ k := fun ζ => (hs ζ).lift_frac k _
  have hd0 : ∀ ζ, (hs ζ).lift (d : Lw (xplus X E hM) la G.w) ≠ 0 := fun ζ => by
    rw [hd]; exact mul_ne_zero (h ζ).1 (pow_ne_zero _ (inv_ne_zero (hs ζ).s0.ne_zero))
  obtain ⟨e, he⟩ := (isUnit_of_ne hs hfd hU (a := toOsK (xplus X E hM) la G.w d) hd0).exists_right_inv
  have hfe : toOsK (xplus X E hM) la G.w f = toOsK (xplus X E hM) la G.w d * (e * toOsK (xplus X E hM) la G.w f) := by rw [← mul_assoc, he, one_mul]
  have hval : ∀ ζ, phiPt (hs ζ) (e * toOsK (xplus X E hM) la G.w f) = u ζ := fun ζ => by
    have h1 := congrArg (phiPt (hs ζ)) hfe
    rw [map_mul (phiPt (hs ζ)) (toOsK (xplus X E hM) la G.w d), phiPt_to, phiPt_to] at h1
    refine mul_left_cancel₀ (hd0 ζ) ?_
    rw [← h1, hf, hd, (h ζ).2]; ring
  have hun : IsUnit (eFormL hs (X.inc _ F')) :=
    isUnit_of_lift_ne hs (x := algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) (emb (xplus X E hM) la G.N (X.inc _ F')))
      fun ζ => by rw [(hs ζ).lift_alg]; exact (h ζ).1
  obtain ⟨e', he'⟩ := hun.exists_right_inv
  have hr : eFormL hs (X.inc _ F') * (e' * eFormL hs (X.inc _ F)) = eFormL hs (X.inc _ F) := by
    rw [← mul_assoc, he', one_mul]
  have hc : Tay.IsCst (tayL hs) (e' * eFormL hs (X.inc _ F)) :=
    Tay.IsCst.of_mul (eFormL_isCst hs _) (by rw [hr]; exact eFormL_isCst hs _) hun
  refine ⟨e * toOsK (xplus X E hM) la G.w f, ⟨f, d, hd0, hfe, e' * eFormL hs (X.inc _ F), ?_, ?_⟩, hval⟩
  · refine mem_RGL_of_stable hs (S := {e' * eFormL hs (X.inc _ F), 0}) ?_ ?_ (Or.inl rfl)
    · rintro β s (rfl | rfl)
      · by_cases hβ : β = 0
        · rw [hβ, hdL_zero]; exact Or.inl rfl
        · exact Or.inr (hc.co hβ)
      · exact Or.inr (map_zero _)
    · rintro s (rfl | rfl)
      · intro ζ
        have h1 := congrArg (evL hs ζ) hr
        rw [map_mul (evL hs ζ) (eFormL hs _), evL_eFormL, evL_eFormL, (h ζ).2, mul_comm] at h1
        rw [mul_right_cancel₀ (h ζ).1 h1, nval_nonneg_iff]
        exact hu ζ
      · exact intAll_zero hs
  · show ιW hs (algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) (emb (xplus X E hM) la G.N (X.inc _ F)) * w0inv (xplus X E hM) la G.w ^ k) =
      _ * ιW hs (algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) (emb (xplus X E hM) la G.N (X.inc _ F')) * w0inv (xplus X E hM) la G.w ^ k)
    rw [map_mul, map_mul, ← mul_assoc]
    congr 1
    exact hr.symm.trans (mul_comm _ _)

theorem pow_form (w₀ : B.Cusp j wL) (k : ℕ) :
    ∃ H : B.Cusp j (addL (wt0 D j) wL (k + 1)), X.inc _ H = X.inc wL w₀ ^ (k + 1) := by
  induction k with
  | zero =>
    show X.inc wL w₀ ^ (0 + 1) ∈ Set.range (X.inc (addL (wt0 D j) wL 1))
    rw [add_zero_weight_one_eq, zero_add, pow_one]; exact ⟨w₀, rfl⟩
  | succ k ih =>
    obtain ⟨H, hH⟩ := ih
    show X.inc wL w₀ ^ (k + 1 + 1) ∈ Set.range (X.inc (addL (wt0 D j) wL (k + 1 + 1)))
    rw [← wadd_addL, pow_succ', ← hH]
    obtain ⟨H', hH'⟩ := X.inc_mul _ _ w₀ H
    exact ⟨H', hH'.symm⟩

theorem mul_form (w₀ : B.Cusp j wL) (k : ℕ) (F : B.Cusp j (addL (wt0 D j) wL k)) :
    ∃ H : B.Cusp j (addL (wt0 D j) wL (k + 1)), X.inc _ H = X.inc wL w₀ * X.inc _ F := by
  show X.inc wL w₀ * X.inc _ F ∈ Set.range (X.inc (addL (wt0 D j) wL (k + 1)))
  rw [← wadd_addL]
  obtain ⟨H', hH'⟩ := X.inc_mul _ _ w₀ F
  exact ⟨H', hH'.symm⟩

section Point

variable {ζ : PtsG G la} {y₀ : E.Pt' la} (h : SecPt ζ y₀)

theorem ev_sec (i : Fin (WeightFamilies.dimY D j + 1)) : h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w i) =
    ∑ k, h.ev (algebraMap (Kp (xplus X E hM) la G.N) (Rp (xplus X E hM) la G.N) (algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) (Tv (xplus X E hM) la G.N (i, k)))) *
      h.ev (emb (xplus X E hM) la G.N (X.inc wL (G.w k))) := by
  unfold Formalism.MainNotions.Gaps.EtaleWeightGaps.sec
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def, map_mul]
  rfl

theorem exists_ev_ne : ∃ k, h.ev (emb (xplus X E hM) la G.N (X.inc wL (G.w k))) ≠ 0 := by
  by_contra hne
  push Not at hne
  refine h.s0.ne_zero ?_
  rw [ev_sec]
  exact Finset.sum_eq_zero fun k _ => by rw [hne, mul_zero]

variable {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) (jz : Ω →+* h.T.Fr)
  (h2 : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), gF (X.inc u F) = 0 → h.ev (emb (xplus X E hM) la G.N (X.inc u F)) = 0)
  (h3 : ∀ (u : WeightFamilies.Wt D j) (F F' : B.Cusp j u), jz (gF (X.inc u F)) * h.ev (emb (xplus X E hM) la G.N (X.inc u F')) =
    jz (gF (X.inc u F')) * h.ev (emb (xplus X E hM) la G.N (X.inc u F)))

include h2 h3

theorem jz_ratio {u : WeightFamilies.Wt D j} (F F' : B.Cusp j u) (hF' : h.ev (emb (xplus X E hM) la G.N (X.inc u F')) ≠ 0) :
    jz (gF (X.inc u F) / gF (X.inc u F')) =
      h.ev (emb (xplus X E hM) la G.N (X.inc u F)) / h.ev (emb (xplus X E hM) la G.N (X.inc u F')) := by
  have h0 : jz (gF (X.inc u F')) ≠ 0 := (map_ne_zero jz).2 fun e => hF' (h2 u F' e)
  rw [map_div₀, div_eq_div_iff h0 hF', h3, mul_comm]

theorem jz_const (a : B.KO) : jz (algebraMap B.KO Ω a) = h.ev (algebraMap (Kp (xplus X E hM) la G.N) (Rp (xplus X E hM) la G.N)
    (algebraMap ((xplus X E hM).Kl la) (Kp (xplus X E hM) la G.N) (algebraMap B.KO ((xplus X E hM).Kl la) a))) := by
  obtain ⟨k, hk⟩ := exists_ev_ne h
  have h0 : gF (X.inc wL (G.w k)) ≠ 0 := fun e => hk (h2 _ _ e)
  have h1 := jz_ratio h gF jz h2 h3 (a • G.w k) (G.w k) hk
  have e1 : emb (xplus X E hM) la G.N (X.inc wL (a • G.w k)) =
      algebraMap (Kp (xplus X E hM) la G.N) (Rp (xplus X E hM) la G.N)
        (algebraMap ((xplus X E hM).Kl la) (Kp (xplus X E hM) la G.N) (algebraMap B.KO ((xplus X E hM).Kl la) a)) *
        emb (xplus X E hM) la G.N (X.inc wL (G.w k)) := by
    rw [map_smul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def]
    exact emb_smul (xplus X E hM) la G.N a _
  rw [e1, map_smul, map_smul, Algebra.smul_def, map_mul, mul_div_cancel_right₀ _ h0, mul_div_cancel_right₀ _ hk] at h1
  exact h1

theorem phiPt_mem (S : Subfield h.T.Fr) (hK : ∀ c, h.ev (algebraMap (Kp (xplus X E hM) la G.N) (Rp (xplus X E hM) la G.N) c) ∈ S)
    (hΩ : ∀ a, jz a ∈ S) (b : OsK (xplus X E hM) la G.w) : phiPt h b ∈ S := by
  obtain ⟨x, rfl⟩ := toOsK_surjective (xplus X E hM) la G.w b
  obtain ⟨k, g, hg, hx⟩ := (mem_Hfr (xplus X E hM) la G.w).1 ((mem_Frac0 (xplus X E hM) la G.w).1 x.2)
  rw [phiPt_to, hx, h.lift_frac]
  obtain ⟨k₀, hk⟩ := exists_ev_ne h
  set w₀ := h.ev (emb (xplus X E hM) la G.N (X.inc wL (G.w k₀))) with hw₀
  have hs0 : h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) / w₀ ∈ S := by
    rw [ev_sec, Finset.sum_div]
    refine S.sum_mem fun k _ => ?_
    rw [mul_div_assoc, ← jz_ratio h gF jz h2 h3 _ _ hk]
    exact S.mul_mem (hK _) (hΩ _)
  have hg' : h.ev g / w₀ ^ k ∈ S := by
    clear hx
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨F, rfl⟩ := hg
      obtain ⟨H, hH⟩ := pow_form (X := X) (G.w k₀) k
      obtain ⟨H', hH'⟩ := mul_form (X := X) (G.w k₀) k F
      have e : h.ev (emb (xplus X E hM) la G.N (X.inc _ H)) = w₀ ^ (k + 1) := by
        rw [hH]; exact (congrArg h.ev (map_pow (emb (xplus X E hM) la G.N) _ _)).trans (map_pow _ _ _)
      have e' : h.ev (emb (xplus X E hM) la G.N (X.inc _ H')) = w₀ * h.ev (emb (xplus X E hM) la G.N (X.inc _ F)) := by
        rw [hH']; exact (congrArg h.ev (map_mul (emb (xplus X E hM) la G.N) _ _)).trans (map_mul _ _ _)
      have h1 := jz_ratio h gF jz h2 h3 H' H (by rw [e]; exact pow_ne_zero _ hk)
      rw [e, e', pow_succ', mul_div_mul_left _ _ hk] at h1
      exact h1 ▸ hΩ _
    | zero => rw [map_zero, zero_div]; exact S.zero_mem
    | add a b _ _ ha hb => rw [map_add, add_div]; exact S.add_mem ha hb
    | smul c a _ ha => rw [Algebra.smul_def, map_mul, mul_div_assoc]; exact S.mul_mem (hK c) ha
  have e : h.ev g * (h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0))⁻¹ ^ k = h.ev g / w₀ ^ k * (h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) / w₀)⁻¹ ^ k := by
    rw [inv_div, div_pow, inv_pow, div_mul_div_cancel₀ (pow_ne_zero k hk), div_eq_mul_inv]
  rw [e]
  exact S.mul_mem hg' (S.pow_mem (S.inv_mem hs0) k)

theorem residue_at (hU : IsUnif (OsK (xplus X E hM) la G.w) (unifO (xplus X E hM) la G.N)) [IsDVRAt ζ]
    (htr : Algebra.trdeg B.KO Ω = WeightFamilies.dimY D j) (t : Idx D j G.N → h.T.Fr)
    (ht : ∀ q, t q = phiPt h (algebraMap (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) (Tv (xplus X E hM) la G.N q)))
    (b : OsK (xplus X E hM) la G.w) (hb : b ∈ As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) :
    ∃ a ∈ Subring.closure ({u | u ∈ Set.range jz ∧ valV h.T.V u ≤ 1} ∪ Set.range t),
    ∃ d ∈ Subring.closure ({u | u ∈ Set.range jz ∧ valV h.T.V u ≤ 1} ∪ Set.range t),
      valV h.T.V d = 1 ∧ valV h.T.V (phiPt h b * d - a) < 1 := by
  let ψ : Kp (xplus X E hM) la G.N →+* h.T.Fr := h.ev.comp (algebraMap (Kp (xplus X E hM) la G.N) (Rp (xplus X E hM) la G.N))
  have hψ : ∀ o : Op (xplus X E hM) la G.N, ψ (algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) o) =
      phiPt h (algebraMap (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) o) := fun o => (phiPt_Kp h _).symm
  have hint : ∀ o : Op (xplus X E hM) la G.N, valV h.T.V (ψ (algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) o)) ≤ 1 := fun o => by
    rw [hψ]; exact phiPt_int hU h ((As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)).algebraMap_mem o)
  have hϖ : valV h.T.V (ψ (algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) (unifO (xplus X E hM) la G.N))) < 1 := by
    rw [hψ]
    have he := ep_pos ζ hU
    rcases ord_cases (ord_phiPt h (algebraMap (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) (unifO (xplus X E hM) la G.N))) with
      ⟨h1, -⟩ | ⟨n, h1, h2⟩
    · rw [h1, map_zero]; exact zero_lt_one
    · rw [ord_unif ζ hU, WithTop.coe_inj] at h2
      rw [h1, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have ht' : t = fun q => ψ (algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) (Tv (xplus X E hM) la G.N q)) :=
    funext fun q => (ht q).trans (hψ _).symm
  obtain ⟨g1, g2, g3⟩ := GlobalTheory.T.gauss_valuation_density_generation_localisation D B P j (xplus X E hM) la G.N h.T.Fr (valV h.T.V) ψ hint hϖ
  obtain ⟨S', hS'⟩ := GlobalTheory.T.exists_subfield_valuation_closure' h.T.Fr (valV h.T.V) (Subfield.closure (Set.range jz ∪ Set.range t))
  have hle : ∀ u ∈ Subfield.closure (Set.range jz ∪ Set.range t), u ∈ S' := fun u hu =>
    (hS' u).2 fun γ hγ => ⟨u, hu, by rw [sub_self, map_zero]; exact zero_lt_iff.2 hγ⟩
  have hK : ∀ c, ψ c ∈ S' := by
    refine g3 S' (fun c => (hS' _).2 fun γ hγ => ?_) fun q => hle _ (Subfield.subset_closure (Or.inr ⟨q, by rw [ht']⟩))
    obtain ⟨a, ha⟩ := g2 c γ hγ
    exact ⟨_, Subfield.subset_closure (Or.inl ⟨algebraMap B.KO Ω a, jz_const h gF jz h2 h3 a⟩), ha⟩
  have hmem := phiPt_mem h gF jz h2 h3 S' hK (fun a => hle _ (Subfield.subset_closure (Or.inl ⟨a, rfl⟩))) b
  obtain ⟨g, hg, hgb⟩ := (hS' _).1 hmem 1 one_ne_zero
  have hg1 : valV h.T.V g ≤ 1 := by
    have e : g = phiPt h b + -(phiPt h b - g) := by ring
    rw [e]
    exact (valV h.T.V).map_add_le (phiPt_int hU h hb) (by rw [Valuation.map_neg]; exact hgb.le)
  obtain ⟨k₀, hk⟩ := exists_ev_ne h
  obtain ⟨a, ha, d, hd, hd1, hgd⟩ := GlobalTheory.T.integral_elements_generic_linear_section_gauss_point B.KO Ω h.T.Fr jz (WeightFamilies.dimY D j) G.N htr (valV h.T.V) t
    (fun k => gF (X.inc wL (G.w k)) / gF (X.inc wL (G.w k₀)))
    ⟨k₀, div_ne_zero (fun e => hk (h2 _ _ e)) (fun e => hk (h2 _ _ e))⟩
    (fun i => by
      have h0 := h.onS i
      rw [ev_sec] at h0
      simp only [jz_ratio h gF jz h2 h3 _ _ hk, ← mul_div_assoc, ← Finset.sum_div, ht']
      exact div_eq_zero_iff.2 (Or.inl h0))
    (fun q => by rw [ht']; exact hint _)
    (fun p hp hp' => by
      rw [ht']
      exact g1 (jz.comp (algebraMap B.KO Ω)) (fun a => jz_const h gF jz h2 h3 a) p hp hp')
    g hg hg1
  refine ⟨a, ha, d, hd, hd1, ?_⟩
  rw [← hgd, ← sub_mul, map_mul, hd1, mul_one]
  exact hgb

end Point

theorem as_le_liftable (hfd : FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) (hred : IsReduced (OsK (xplus X E hM) la G.w))
    (hU : IsUnif (OsK (xplus X E hM) la G.w) (unifO (xplus X E hM) la G.N)) [∀ ζ : PtsG G la, IsDVRAt ζ]
    {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)
    (Zc : PtsG G la → ι) (jz : ∀ ζ, Ω (Zc ζ) →+* (hs ζ).T.Fr)
    (htr : ∀ Z, Algebra.trdeg B.KO (Ω Z) = WeightFamilies.dimY D j)
    (h1 : ∀ ζ, ∃ a, vV (hs ζ).T.V (jz ζ a) = 1)
    (h2 : ∀ ζ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), gF (Zc ζ) (X.inc u F) = 0 →
      (hs ζ).ev (emb (xplus X E hM) la G.N (X.inc u F)) = 0)
    (h3 : ∀ ζ (u : WeightFamilies.Wt D j) (F F' : B.Cusp j u),
      jz ζ (gF (Zc ζ) (X.inc u F)) * (hs ζ).ev (emb (xplus X E hM) la G.N (X.inc u F')) =
        jz ζ (gF (Zc ζ) (X.inc u F')) * (hs ζ).ev (emb (xplus X E hM) la G.N (X.inc u F)))
    (h4 : ∀ ζ ζ', ζ ≠ ζ' → Zc ζ = Zc ζ' → ∃ (u : WeightFamilies.Wt D j) (F F' : B.Cusp j u),
      (hs ζ).ev (emb (xplus X E hM) la G.N (X.inc u F')) ≠ 0 ∧ (hs ζ').ev (emb (xplus X E hM) la G.N (X.inc u F')) ≠ 0 ∧
      nval (hs ζ).T.V 1 ((hs ζ).ev (emb (xplus X E hM) la G.N (X.inc u F'))) <
        nval (hs ζ).T.V 1 ((hs ζ).ev (emb (xplus X E hM) la G.N (X.inc u F))) ∧
      nval (hs ζ').T.V 1 ((hs ζ').ev (emb (xplus X E hM) la G.N (X.inc u F'))) <
        nval (hs ζ').T.V 1 ((hs ζ').ev (emb (xplus X E hM) la G.N (X.inc u F)) - (hs ζ').ev (emb (xplus X E hM) la G.N (X.inc u F'))))
    (hB : ∀ Z, CurveLoc.BirAt (xplus X E hM) G.N G.w (gF Z))
    (hC : ∀ Z (u : WeightFamilies.Wt D j) (F : B.Cusp j u), ∃ F' : B.Cusp j u, gF Z (X.inc u F') = gF Z (X.inc u F) ∧
      ∀ Z', Z' ≠ Z → gF Z' (X.inc u F') = 0) :
    As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) ≤ liftable hs hU := by
  haveI := kp_charZero' (la := la) (G := G)
  haveI hfin : Module.Finite (Op (xplus X E hM) la G.N) ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) :=
    (integralClosure_dvr' (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)).1
  haveI : Finite (PtsG G la) :=
    (_root_.ramificationDegreeSum (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) (unifO (xplus X E hM) la G.N) hU.irreducible hfin).1
  refine core hU (liftable hs hU) (liftable_le hs hU) Zc (fun ζ => valV (hs ζ).T.V) (fun ζ => phiPt (hs ζ)) jz
    (fun ζ x => ord_cases (ord_phiPt (hs ζ) x)) (fun a ha => ?_) (fun ζ => ?_) (fun ζ ζ' hne hZ => ?_) (fun ζ => ?_)
  · obtain ⟨k, F, F', hF⟩ := GlobalTheory.T.exists_ratio_forms_at_points_alt D B P j (xplus X E hM) la G.N wL G.w (PtsG G la) (fun ζ => (hs ζ).T.Fr)
      (fun ζ => (hs ζ).ev) ι Ω gF Zc jz (fun ζ => exists_ev_ne (hs ζ)) h2 h3 hB hC a
    exact ratio_liftable hs hfd hU k F F' _ ha hF
  · obtain ⟨a, ha⟩ := h1 ζ
    have h0 : jz ζ a ≠ 0 := fun e => by rw [e] at ha; simp [vV] at ha
    refine ⟨a⁻¹, ?_⟩
    show valV _ _ = _
    rw [map_inv₀, map_inv₀, ← WithZero.exp_log (valV_ne_zero (V := (hs ζ).T.V) h0), ← WithZero.exp_neg]
    exact congrArg _ ha
  · obtain ⟨u, F, F', a1, a2, a3, a4⟩ := h4 ζ ζ' hne hZ
    refine ⟨fun Z => gF Z (X.inc u F) / gF Z (X.inc u F'), ?_, ?_⟩
    · show valV _ (jz ζ (_ / _)) < 1
      rw [jz_ratio (hs ζ) (gF _) (jz ζ) (h2 ζ) (h3 ζ) F F' a1]
      exact valV_lt_of_nval_lt a1 a3
    · show valV _ (jz ζ' (_ / _)) = 1
      rw [jz_ratio (hs ζ') (gF _) (jz ζ') (h2 ζ') (h3 ζ') F F' a2]
      have h5 := valV_lt_of_nval_lt a2 a4
      rw [sub_div, div_self a2] at h5
      rw [← add_sub_cancel 1 (_ / _)]
      exact Valuation.map_one_add_of_lt _ h5
  · refine ⟨Set.range fun q => phiPt (hs ζ) (algebraMap (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) (Tv (xplus X E hM) la G.N q)), ?_,
      fun b hb => residue_at (hs ζ) (gF _) (jz ζ) (h2 ζ) (h3 ζ) hU (htr _) _ (fun _ => rfl) b hb⟩
    rintro _ ⟨q, rfl⟩
    exact ⟨_, (liftable hs hU).algebraMap_mem _, rfl⟩

theorem locStruct_of
    {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)
    (evF : ∀ Z (u : WeightFamilies.Wt D j), B.Cusp j u → Ω Z) (hev : ∀ Z u F, gF Z (X.inc u F) = evF Z u F)
    (htr : ∀ Z, Algebra.trdeg B.KO (Ω Z) = WeightFamilies.dimY D j)
    (hV : ∀ (y : PtsG G la → E.Pt' la) (hw : ∀ ζ, FromW ζ (y ζ)),
      ∃ (Zc : PtsG G la → ι) (jz : ∀ ζ, Ω (Zc ζ) →+* (hw ζ).T.Fr),
      (∀ ζ, ∃ a, vV (hw ζ).T.V (jz ζ a) = 1) ∧
      (∀ ζ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), evF (Zc ζ) u F = 0 →
        (hw ζ).ev (emb (xplus X E hM) la G.N (X.inc u F)) = 0) ∧
      (∀ ζ (u : WeightFamilies.Wt D j) (F F' : B.Cusp j u),
        jz ζ (evF (Zc ζ) u F) * (hw ζ).ev (emb (xplus X E hM) la G.N (X.inc u F')) =
          jz ζ (evF (Zc ζ) u F') * (hw ζ).ev (emb (xplus X E hM) la G.N (X.inc u F))) ∧
      ∀ ζ ζ', ζ ≠ ζ' → Zc ζ = Zc ζ' → ∃ (u : WeightFamilies.Wt D j) (F F' : B.Cusp j u),
        (hw ζ).ev (emb (xplus X E hM) la G.N (X.inc u F')) ≠ 0 ∧ (hw ζ').ev (emb (xplus X E hM) la G.N (X.inc u F')) ≠ 0 ∧
        nval (hw ζ).T.V 1 ((hw ζ).ev (emb (xplus X E hM) la G.N (X.inc u F'))) <
          nval (hw ζ).T.V 1 ((hw ζ).ev (emb (xplus X E hM) la G.N (X.inc u F))) ∧
        nval (hw ζ').T.V 1 ((hw ζ').ev (emb (xplus X E hM) la G.N (X.inc u F'))) <
          nval (hw ζ').T.V 1 ((hw ζ').ev (emb (xplus X E hM) la G.N (X.inc u F)) - (hw ζ').ev (emb (xplus X E hM) la G.N (X.inc u F'))))
    (hB : ∀ Z, CurveLoc.BirAt (xplus X E hM) G.N G.w (gF Z))
    (hC : ∀ Z (u : WeightFamilies.Wt D j) (F : B.Cusp j u), ∃ F' : B.Cusp j u, evF Z u F' = evF Z u F ∧
      ∀ Z', Z' ≠ Z → evF Z' u F' = 0) :
    Formalism.L2.Pj.LocStructSt G la := by
  rintro y hw g0 ⟨M⟩ - g hg
  obtain ⟨Zc, jz, h1, h2, h3, h4⟩ := hV y hw
  have hfd : FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) := by
    haveI : FiniteDimensional (Kp (xplus X E hM) la G.N) (↥M.A' ⧸ M.JA) := M.fin
    exact LinearEquiv.finiteDimensional M.quotEquiv.toLinearEquiv
  have hred : IsReduced (OsK (xplus X E hM) la G.w) := by
    haveI : IsReduced (↥M.A' ⧸ M.JA) := M.red
    exact isReduced_of_injective M.quotEquiv.symm.toRingHom M.quotEquiv.symm.injective
  have hU := isUnif_of_ring (G := G) hfd
  haveI : ∀ ζ : PtsG G la, IsDVRAt ζ := isDVRAt_of_ring hfd hred
  have hmem : toOsK (xplus X E hM) la G.w g ∈ As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) :=
    (mem_As_iff hU _).2 fun ζ => ord_nonneg_of (hw ζ).toSecPt (nval_nonneg_iff.1 (hg ζ))
  obtain ⟨f, d, hd, he, r, hr, hf⟩ := as_le_liftable (fun ζ => (hw ζ).toSecPt) hfd hred hU Ω gF Zc jz htr h1
    (fun ζ u F e => h2 ζ u F ((hev _ _ _).symm.trans e)) (fun ζ u F F' => by rw [hev, hev]; exact h3 ζ u F F') h4 hB
    (fun Z u F => by simp only [hev]; exact hC Z u F) hmem
  refine ⟨f, d, hd, he, fun l ζ => ?_⟩
  rw [hf, mul_assoc, IsUnit.mul_val_inv, mul_one]
  exact hr l ζ

end Rec

end GlobalTheory.Reg.UnitBall

namespace GlobalTheory.Reg

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem locStructSt_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → Formalism.L2.Pj.LocStructSt (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G la := by
  intro D T h j hj hG hT ka wL wF G S g0 la hH hI hC hB
  exact UnitBall.locStruct_of (X := recPJ h j hj) (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (G := G) (la := la)
    (fun Z : Comp (T.Q.Xo j) T.Q.c => Om Z) (fun Z => formsEvR j hG hT Z)
    (fun Z u F => evC hG Z ((F : (recB h.toLawsCore).Cusp j u) : T.R j))
    (fun Z u F => formsEvR_inc h j hj hG hT Z u F)
    (GlobalTheory.FlagDim.fnFG_fnTrdeg_record D T.Q h.pins.2.2.2 j hj).2
    (GlobalTheory.T.generic_section_points_inequivalent_valuations D T h j hj hG hT ka wL wF G S g0 la hH hI hC hB)
    (fun Z => birAt_of h j hj hG hT G hB Z) hC

end GlobalTheory.Reg
