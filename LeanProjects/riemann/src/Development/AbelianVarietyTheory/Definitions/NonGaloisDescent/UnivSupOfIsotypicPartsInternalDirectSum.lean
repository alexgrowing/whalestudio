import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TypePreservedOfAdmissibleIntegral

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.SupLaw.Model

open GlobalTheory.TwAll GlobalTheory.TwAll.Model

variable (D : D7)

theorem supG_of_gKeeps (h : GKeeps D.nth) : SupG D := fun i hi j hj b g f hf =>
  bsup_stable_of_gKeeps D.nth h i hi j hj b g ⟨f, hf, rfl⟩

theorem supHk_of_hkKeeps (h : HkKeeps D.nth) : SupHk D := fun i hi j hj b k P hk f hf =>
  bsup_stable_of_hkKeeps D.nth h i hi j hj b k P hk ⟨f, hf, rfl⟩

theorem univSup_iff (E : XD D) : UnivSup D E ↔ UnivBdd D.nth E := by
  constructor
  · intro h i hi j hj b a ha
    obtain ⟨c, hc⟩ := h i hi j hj b a ha
    refine ⟨c, fun Q M h1 h2 h3 h4 => ?_⟩
    obtain ⟨Xi, e, hX⟩ := hc Q M h1 h2 h3 h4
    refine ⟨Xi, e, fun δ => ⟨(hX δ).1, ?_⟩⟩
    have := inv_smul_span D.nth i j b c _ (hX δ).2
    rwa [smul_l_pow, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (l_ne_zero D.nth i)), one_smul] at this
  · intro h i hi j hj b a ha
    obtain ⟨c, hc⟩ := h i hi j hj b a ha
    refine ⟨c, fun Q M h1 h2 h3 h4 => ?_⟩
    obtain ⟨Xi, e, hX⟩ := hc Q M h1 h2 h3 h4
    exact ⟨Xi, e, fun δ => ⟨(hX δ).1, l_pow_smul_span D.nth i j b c _ (hX δ).2⟩⟩

theorem univSup_of_isotypicPartsInternalDirectSum (E : XD D) (h : IsotypicPartsInternalDirectSum D.nexp E) : UnivSup D E :=
  (univSup_iff D E).2 (uniformBound_of_admissibleIntegral D.nth h)

theorem heckeLaws_of (h1 : HkComm D) (h2 : OffRange D) : GlobalTheory.TwSys.HeckeLaws D.nexp := by
  intro i hi
  refine ⟨fun j b k P k' P' hk hk' => ?_, (h2 i hi).2⟩
  by_cases hj : j ∈ Finset.Icc 1 D.R.m
  · exact h1 i hi j hj b k P k' P' hk hk'
  · haveI := (h2 i hi).1 j hj b
    ext x
    exact Subsingleton.elim _ _

instance finG : Finite (G0g D.nd) := by
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  infer_instance

abbrev Pt (j : ℕ) : Type := {_g : G0g D.nd // j ∈ Finset.Icc 1 D.R.m}

instance finPt (j : ℕ) : Fintype (Pt D j) := Fintype.ofFinite _

abbrev KK (i : D.ntw.Tw) : Type := FractionRing (D.ntw.O i)

@[reducible] def tw : @NTw D.R D.host D.what₂ D.nfLL D.starLL D.LL0 D.nd :=
  { D.ntw with
    B := fun i j _ => Pt D j → D.ntw.O i
    acgB := fun _ _ _ => inferInstance
    modB := fun _ _ _ => inferInstance
    freeB := fun _ _ _ => inferInstance
    finB := fun _ _ _ => inferInstance
    Theta := fun _ _ _ => ⊤
    ThetaPsi := fun _ _ _ _ _ _ => ⊤
    ThetaPsi_one := fun _ _ _ _ => (Submodule.baseChange_top _).symm
    hk := fun _ _ _ _ _ => 1
    hk_zero := fun _ _ _ _ => rfl
    hEig := fun _ _ _ _ => 1 }

def transl (i : D.ntw.Tw) (j : ℕ) : G0g D.nd →* ((Pt D j → KK D i) ≃ₗ[KK D i] (Pt D j → KK D i)) where
  toFun g :=
    { toFun := fun f y => f ⟨y.1 * g, y.2⟩
      invFun := fun f y => f ⟨y.1 * g⁻¹, y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun f => by funext y; simp
      right_inv := fun f => by funext y; simp }
  map_one' := by ext f y; simp
  map_mul' g h := by ext f y; simp [mul_assoc]

def intF (i : D.ntw.Tw) (j : ℕ) : (Pt D j → D.ntw.O i) →ₗ[D.ntw.O i] (Pt D j → KK D i) :=
  (Algebra.linearMap (D.ntw.O i) (KK D i)).compLeft _

variable (A : ∀ (i : D.ntw.Tw) (j : ℕ), ℕ → PlE D.host → Module.End (KK D i) (Pt D j → KK D i))
  (s : ∀ i : D.ntw.Tw, ℕ → KK D i)

@[reducible] def ex : @NExp D.R D.host D.what₂ D.nfLL D.starLL D.LL0 D.nd (tw D) :=
  { D.nexp with
    Fm := fun i j _ => Pt D j → KK D i
    acgFm := fun _ _ _ => inferInstance
    modFmK := fun _ _ _ => inferInstance
    modFmO := fun _ _ _ => inferInstance
    towFm := fun _ _ _ => inferInstance
    fdFm := fun _ _ _ => inferInstance
    actG := fun i j _ => transl D i j
    U := ⊥
    psiU := fun _ _ => 1
    Bsup := fun i j _ => LinearMap.range (intF D i j)
    Dat := fun i j _ => Pt D j → KK D i
    th := fun _ _ _ a => a
    lev := fun _ _ _ _ => ∅
    thPsi := fun i _ _ k _ _ a => {(1 : D.ntw.Ok i k) ⊗ₜ[D.ntw.O i] a}
    thPsi_one := fun _ _ _ _ _ => rfl
    thU := fun i _ _ Q M a => (s i M • a) ⊗ₜ[D.ntw.O i]
      AddMonoidAlgebra.single (0 : DelQM D.host (D.ntw.l i) Q M) (1 : D.ntw.O i)
    twPsi := fun i j _ k _ => TensorProduct.mk (D.ntw.O i) (D.ntw.Ok i k) (Pt D j → KK D i) 1
    twPsi_one := fun _ _ _ _ _ => rfl
    twDel := fun _ _ _ _ _ => 0
    thP := fun _ _ _ _ _ _ => 0
    hkF := fun i j _ => A i j
    embB := fun i j _ => intF D i j
    embB_inj := fun i j _ f g h => by
      funext y
      exact IsFractionRing.injective (D.ntw.O i) (KK D i) (congrFun h y)
    eH := fun _ _ _ => 1
    eH_idem := fun _ _ _ => mul_one _ }

theorem mem_intF (i : D.ntw.Tw) (j : ℕ) (f : Pt D j → KK D i) :
    f ∈ LinearMap.range (intF D i j) ↔ ∀ y, f y ∈ (algebraMap (D.ntw.O i) (KK D i)).range := by
  constructor
  · rintro ⟨g, rfl⟩ y
    exact ⟨g y, rfl⟩
  · intro h
    choose g hg using h
    exact ⟨g, funext hg⟩

open Classical in

@[reducible] def th : @NTh D.R D.host D.what₂ D.nfLL D.starLL D.LL0 D.nd (tw D) (ex D A s) :=
  { D.nth with
    Pt := fun _ j => Pt D j
    ev := fun i j _ => (D.nth.iC i).toAddMonoidHom.compLeft _
    ev_smul := fun i j _ a f y => map_mul (D.nth.iC i) a (f y)
    ev_inj := fun i j _ f g h => by
      funext y
      exact (D.nth.iC i).injective (congrFun h y)
    thV := fun _ _ _ _ _ => 0
    thV_add := fun _ _ _ _ _ _ => (add_zero _).symm
    thV_smul := fun _ _ _ _ _ _ => (mul_zero _).symm
    thV_addP := fun _ _ _ _ _ _ => (add_zero _).symm
    thV_smulP := fun _ _ _ _ _ _ => (mul_zero _).symm
    datPhi := fun _ _ _ _ _ => 0
    datP := fun _ _ _ _ => 0
    recDet := fun _ _ _ => 1
    Kq := fun _ _ _ => PUnit
    grpKq := fun _ _ _ => inferInstance
    actK := fun _ _ _ _ y => y
    actK_one := fun _ _ _ _ => rfl
    actK_mul := fun _ _ _ _ _ _ => rfl
    recDetq := fun _ _ _ _ => 1
    recDetq_mem := fun _ _ _ _ => one_mem _
    recDet_act := fun _ _ _ _ _ _ _ _ _ _ => rfl
    recDetq_act := fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    hkIdx := fun _ j _ _ => Pt D j
    finHk := fun _ _ _ _ => inferInstance
    hkMove := fun _ _ _ _ c _ => c
    hkU := fun i j _ k P c y => D.nth.iC i (A i j k P (Pi.single c 1) y)
    hk_ev := fun i j _ k P _ _ _ _ f y => by
      change D.nth.iC i (A i j k P f y) = ∑ c, D.nth.iC i (A i j k P (Pi.single c 1) y) * D.nth.iC i (f c)
      simp_rw [← map_mul, ← map_sum]
      congr 1
      conv_lhs => rw [pi_eq_sum_univ' f]
      simp [map_sum, mul_comm]
    MaximalUnramifiedExtension := fun _ => ⊤
    FmUr := fun _ _ _ => ⊤
    FmUr_smul := fun _ _ _ _ _ _ _ => trivial
    FmUr_span := fun _ _ _ => by simp
    Bsup_def := fun i j _ => by
      have : {f : Pt D j → KK D i | f ∈ (⊤ : AddSubgroup (Pt D j → KK D i)) ∧ ∀ y, ‖D.nth.iC i (f y)‖ ≤ 1} =
          (LinearMap.range (intF D i j) : Set _) := by
        ext f
        simp only [AddSubgroup.mem_top, true_and, Set.mem_setOf_eq, SetLike.mem_coe, mem_intF, D.nth.iC_int]
      change LinearMap.range (intF D i j) = Submodule.span _
        {f : Pt D j → KK D i | f ∈ (⊤ : AddSubgroup (Pt D j → KK D i)) ∧ ∀ y, ‖D.nth.iC i (f y)‖ ≤ 1}
      rw [this, Submodule.span_eq] }

@[reducible] def rec : D7 := { D with ntw := tw D, nexp := ex D A s, nth := th D A s }

theorem goodFiltration_eq_top (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Fm0 (D := rec D A s) (ex D A s) i j b = ⊤ := by
  rw [eq_top_iff]
  intro f _
  simp only [Fm0, Submodule.mem_iInf, LinearMap.mem_ker]
  intro u
  have hu : (u : G0g D.nd) = 1 := Subgroup.mem_bot.1 u.2
  rw [hu]
  funext y
  simp [transl]

def dat : XD (rec D A s) where
  Dat0 := fun _ _ _ => Set.univ
  theta_base_equivariant := fun i j b a _ u => by
    have hu : (u : G0g D.nd) = 1 := Subgroup.mem_bot.1 u.2
    rw [hu]
    funext y
    simp [transl]

theorem inNonzeroPlaces_recursive_iff (i : D.ntw.Tw) : (rec D A s).ntw.NonzeroIndexPlace i ↔ D.ntw.NonzeroIndexPlace i := Iff.rfl

theorem nontrivial_fm (i : D.ntw.Tw) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m) (b : Bool) :
    Nontrivial ((rec D A s).nexp.Fm i j b) :=
  haveI : Nonempty (Pt D j) := ⟨⟨1, hj⟩⟩
  inferInstanceAs (Nontrivial (Pt D j → KK D i))

theorem one_mem_range : 1 ∈ Finset.Icc 1 D.R.m := by
  have := D.R.two_le_m
  simp; omega

theorem supG : SupG (rec D A s) := fun i _ j _ _ g f hf =>
  (mem_intF D i j _).2 fun y => (mem_intF D i j f).1 hf ⟨y.1 * g, y.2⟩

theorem exists_pow (i : D.ntw.Tw) (j : ℕ) (f : Pt D j → KK D i) :
    ∃ c : ℕ, ((D.ntw.l i : D.ntw.O i) ^ c) • f ∈ LinearMap.range (intF D i j) := by
  have hl : (1 : ℝ) < D.ntw.l i := by exact_mod_cast (D.ntw.lPrime i).out.one_lt
  obtain ⟨c, hc⟩ := pow_unbounded_of_one_lt (∑ y, ‖D.nth.iC i (f y)‖) hl
  refine ⟨c, l_pow_smul_span (D := rec D (fun _ _ _ _ => 1) (fun _ _ => 1)) (th D (fun _ _ _ _ => 1) (fun _ _ => 1))
    i j true c f (Submodule.subset_span ⟨trivial, fun y => ?_⟩)⟩
  exact (Finset.single_le_sum (f := fun y => ‖D.nth.iC i (f y)‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ y)).trans hc.le

theorem supFull : SupFull (rec D A s) := fun i hi j hj b =>
  ⟨by
    change (LinearMap.range (intF D i j)).FG
    rw [LinearMap.range_eq_map]
    exact Submodule.FG.map _ Module.Finite.fg_top,
   span_bsup_of_supBdd (D := rec D A s) (th D A s) (fun i _ j _ b f _ =>
    ⟨∑ y, ‖D.nth.iC i (f y)‖, trivial, fun y => Finset.single_le_sum (f := fun y => ‖D.nth.iC i (f y)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ y)⟩) i hi j hj b⟩

theorem offRange : OffRange (rec D A s) := fun i _ =>
  ⟨fun j hj _ =>
    haveI : IsEmpty (Pt D j) := ⟨fun y => hj y.2⟩
    inferInstanceAs (Subsingleton (Pt D j → KK D i)), fun _ _ => rfl⟩

theorem univSup_one : UnivSup (rec D A fun _ _ => 1) (dat D A fun _ _ => 1) := by
  intro i _ j _ b a _
  obtain ⟨c, hc⟩ := exists_pow D i j a
  refine ⟨c, fun Q M _ _ _ _ => ⟨Finsupp.single 0 a, ?_, fun δ => ⟨by rw [goodFiltration_eq_top]; trivial, ?_⟩⟩⟩
  · rw [Finsupp.sum_single_index (by exact TensorProduct.zero_tmul _ _)]
    exact congrArg (· ⊗ₜ _) (one_smul _ _)
  · classical
    rw [Finsupp.single_apply]
    split_ifs
    · exact hc
    · rw [smul_zero]; exact zero_mem _

abbrev scal (t : ∀ i : D.ntw.Tw, ℕ → KK D i) :
    ∀ (i : D.ntw.Tw) (j : ℕ), ℕ → PlE D.host → Module.End (KK D i) (Pt D j → KK D i) :=
  fun i _ k _ => t i k • LinearMap.id

theorem hkComm_scal (t) : HkComm (rec D (scal D t) s) := fun i _ j _ b k P k' P' _ _ => by
  change Commute (t i k • (1 : Module.End (KK D i) (Pt D j → KK D i))) (t i k' • 1)
  exact ((Commute.refl _).smul_left _).smul_right _

theorem hkSS_scal (t) : HkSS (rec D (scal D t) s) := fun i _ j _ b => by
  refine le_iSup_of_le (fun k _ => t i k) (le_inf ?_ le_rfl)
  intro f _
  simp only [Eigsp, Submodule.mem_iInf, LinearMap.mem_ker]
  intro k P _
  rw [sub_self]; rfl

theorem supHk_nat : SupHk (rec D (scal D fun _ k => k) s) := fun i _ j _ b k P _ f hf =>
  (mem_intF D i j _).2 fun y => mul_mem (natCast_mem _ k) ((mem_intF D i j f).1 hf y)

theorem all_laws : ∃ (D' : D7) (E : XD D') (e : D'.ntw.Tw ≃ D.ntw.Tw), (∀ i, D'.ntw.NonzeroIndexPlace i ↔ D.ntw.NonzeroIndexPlace (e i)) ∧
    (∀ i, ∀ j ∈ Finset.Icc 1 D'.R.m, ∀ b, Nontrivial (D'.nexp.Fm i j b) ∧ E.Dat0 i j b = Set.univ ∧
      Function.Surjective (D'.nexp.th i j b)) ∧
    SupG D' ∧ SupFull D' ∧ SupHk D' ∧ UnivSup D' E ∧ HkComm D' ∧ OffRange D' ∧ HkSS D' :=
  ⟨rec D (scal D fun _ k => k) fun _ _ => 1, dat D _ _, Equiv.refl _, fun _ => Iff.rfl,
    fun i j hj b => ⟨nontrivial_fm D _ _ i j hj b, rfl, Function.surjective_id⟩,
    supG D _ _, supFull D _ _, supHk_nat D _, univSup_one D _, hkComm_scal D _ _, offRange D _ _, hkSS_scal D _ _⟩

theorem inv_l_not_mem (i : D.ntw.Tw) : ((D.ntw.l i : KK D i))⁻¹ ∉ (algebraMap (D.ntw.O i) (KK D i)).range := by
  have hl : (1 : ℝ) < D.ntw.l i := by exact_mod_cast (D.ntw.lPrime i).out.one_lt
  rw [← D.nth.iC_int, map_inv₀, map_natCast, norm_inv, norm_l, inv_inv, not_le]
  exact hl

theorem not_supHk (i : D.ntw.Tw) (hi : D.ntw.NonzeroIndexPlace i) (k P) (hk : HkIdx (D := D) i k P) :
    ¬ SupHk (rec D (scal D fun i _ => ((D.ntw.l i : KK D i))⁻¹) s) := fun h => by
  have := (mem_intF D i 1 _).1 (h i hi 1 (one_mem_range D) true k P hk (fun _ => 1)
    ((mem_intF D i 1 _).2 fun _ => one_mem _)) ⟨1, one_mem_range D⟩
  exact inv_l_not_mem D i (by simpa using this)

theorem not_univSup (i : D.ntw.Tw) (hi : D.ntw.NonzeroIndexPlace i) :
    ¬ UnivSup (rec D A fun i M => ((D.ntw.l i : KK D i) ^ M)⁻¹) (dat D A _) := fun h => by
  classical
  obtain ⟨c, hc⟩ := h i hi 1 (one_mem_range D) true (fun _ => 1) trivial
  obtain ⟨Xi, e, hX⟩ := hc ∅ (c + 1) (by simp) (by simp [ClsQ]) (by simp) (by simp)
  let φ : ((Pt D 1 → KK D i) ⊗[D.ntw.O i] AddMonoidAlgebra (D.ntw.O i) (DelQM D.host (D.ntw.l i) ∅ (c + 1))) →ₗ[D.ntw.O i]
      (Pt D 1 → KK D i) := (TensorProduct.rid _ _).toLinearMap ∘ₗ
        (AddMonoidAlgebra.lift (D.ntw.O i) (D.ntw.O i) (DelQM D.host (D.ntw.l i) ∅ (c + 1)) 1).toLinearMap.lTensor _
  have hφ : ∀ f δ, φ (f ⊗ₜ AddMonoidAlgebra.single δ (1 : D.ntw.O i)) = f := fun f δ => by simp [φ]
  have e2 := congrArg φ e
  rw [map_finsuppSum] at e2
  simp only [hφ] at e2
  have e3 : Xi.sum (fun _ f => f) = Xi 0 := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_subsingleton _ 0]
  have h2 := (mem_intF D i 1 _).1 (hX 0).2 ⟨1, one_mem_range D⟩
  rw [← e3, ← e2] at h2
  apply inv_l_not_mem D i
  have hne := l_ne_zero D.nth i
  change ((D.ntw.l i : D.ntw.O i) ^ c) • (((D.ntw.l i : KK D i) ^ (c + 1))⁻¹ * 1) ∈ _ at h2
  have e4 : ((D.ntw.l i : D.ntw.O i) ^ c) • (((D.ntw.l i : KK D i) ^ (c + 1))⁻¹ * 1) = ((D.ntw.l i : KK D i))⁻¹ := by
    rw [Algebra.smul_def, map_pow, map_natCast, mul_one, pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hne), one_mul]
  rwa [e4] at h2

theorem goodPart_ne_bot (i : D.ntw.Tw) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m) (b : Bool) (he : D.nexp.eAlg i b ≠ 0) :
    V0 (D := rec D A s) (ex D A s) i j b ≠ ⊥ := by
  classical
  intro h
  apply he
  ext g
  have h1 : eG (D := rec D A s) (ex D A s) i j b (Pi.single ⟨g, hj⟩ 1) ∈ V0 (D := rec D A s) (ex D A s) i j b :=
    ⟨_, by rw [goodFiltration_eq_top]; trivial, rfl⟩
  rw [h, Submodule.mem_bot] at h1
  have h2 := congrFun h1 ⟨1, hj⟩
  simp only [eG, MonoidAlgebra.lift_apply, Finsupp.sum, LinearMap.sum_apply, Finset.sum_apply] at h2
  rw [Finset.sum_eq_single g] at h2
  · simp [transl] at h2
    exact h2
  · intro g' _ hg
    simp [transl, hg]
  · intro hg
    simp [Finsupp.notMem_support_iff.1 hg]

open Classical in

def unitOp (i : D.ntw.Tw) (j : ℕ) (g₁ g₀ : G0g D.nd) : Module.End (KK D i) (Pt D j → KK D i) where
  toFun f y := if y.1 = g₁ then f ⟨g₀, y.2⟩ else 0
  map_add' f f' := by funext y; by_cases h : y.1 = g₁ <;> simp [h]
  map_smul' a f := by funext y; by_cases h : y.1 = g₁ <;> simp [h]

theorem not_hkComm (i : D.ntw.Tw) (hi : D.ntw.NonzeroIndexPlace i) (P) (hP : HkIdx (D := D) i 1 P) (g₀ g₁ : G0g D.nd) (hg : g₀ ≠ g₁) :
    ¬ HkComm (rec D (fun i j k _ => if k = 1 then unitOp D i j g₁ g₀ else unitOp D i j g₀ g₁) s) := fun h => by
  have hr : 2 ≤ D.R.r := by
    have := D.R.two_le_m
    have := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have h1 := h i hi 1 (one_mem_range D) true 1 P 2 P hP ⟨by norm_num, hr, hP.2.2⟩
  have h2 := congrFun (LinearMap.congr_fun h1.eq (fun _ => 1)) ⟨g₁, one_mem_range D⟩
  simp [unitOp, hg.symm] at h2

theorem not_hkSS [Nontrivial (G0g D.nd)] (i : D.ntw.Tw) (hi : D.ntw.NonzeroIndexPlace i) (k P) (hP : HkIdx (D := D) i k P)
    (he : D.nexp.eAlg i true ≠ 0) : ∃ A, ¬ HkSS (rec D A s) := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1
    (goodPart_ne_bot D (fun _ _ _ _ => 1) s i 1 (one_mem_range D) true he)
  obtain ⟨y₀, hy₀⟩ := Function.ne_iff.1 hx0
  obtain ⟨g₁, hg⟩ := exists_ne y₀.1
  refine ⟨fun i j _ _ => unitOp D i j g₁ y₀.1, fun h => hy₀ ?_⟩
  have h1 := h i hi 1 (one_mem_range D) true
  have h2 : (⨆ ev, (Eigsp (D := rec D (fun i j _ _ => unitOp D i j g₁ y₀.1) s) (ex D (fun i j _ _ => unitOp D i j g₁ y₀.1) s) i 1 true ev ⊓
      V0 (D := rec D (fun i j _ _ => unitOp D i j g₁ y₀.1) s) (ex D (fun i j _ _ => unitOp D i j g₁ y₀.1) s) i 1 true)) ≤
      LinearMap.ker (LinearMap.proj (R := KK D i) (φ := fun _ : Pt D 1 => KK D i) y₀) := by
    refine iSup_le fun ev f hf => ?_
    have h3 := hf.1
    simp only [Eigsp, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker] at h3
    have h4 := h3 k P hP
    have a := congrFun h4 y₀
    have c := congrFun h4 ⟨g₁, one_mem_range D⟩
    simp [unitOp, hg.symm] at a c
    change f y₀ = 0
    rcases a with a | a
    · simpa [a] using c
    · exact a
  exact h2 (h1 hx)

end GlobalTheory.SupLaw.Model

end
