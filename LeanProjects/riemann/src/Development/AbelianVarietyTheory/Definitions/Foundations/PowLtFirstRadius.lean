import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis

noncomputable section

namespace GlobalTheory.Cyc.Model

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial

variable {l : ℕ} [Fact l.Prime]

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Cyc.Model.isom_gal (g : _root_.Formalism.BasicNotions.Loc.GQ l) :
    Isometry (g : _root_.Formalism.BasicNotions.Loc.Om l →+* _root_.Formalism.BasicNotions.Loc.Om l) := by
  refine AddMonoidHomClass.isometry_of_norm _ fun x => ?_
  change spectralNorm ℚ_[l] (PadicAlgCl l) (g x) = spectralNorm ℚ_[l] (PadicAlgCl l) x
  exact (spectralNorm_eq_of_equiv g x).symm

def extHom (g : GQ l) : PadicComplex l →+* PadicComplex l :=
  UniformSpace.Completion.mapRingHom (g : Om l →+* Om l) (isom_gal g).continuous

theorem extHom_coe (g : GQ l) (x : Om l) : extHom g (x : PadicComplex l) = ((g x : Om l) : PadicComplex l) :=
  UniformSpace.Completion.mapRingHom_coe _ x

theorem extHom_cont (g : GQ l) : Continuous (extHom g) := UniformSpace.Completion.continuous_map

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
private theorem continuous_cyc_extHom (g : _root_.Formalism.BasicNotions.Loc.GQ l) :
    Continuous (_root_.GlobalTheory.Cyc.Model.extHom g) :=
  UniformSpace.Completion.continuous_extension

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
private theorem cyc_extHom_coe (g : _root_.Formalism.BasicNotions.Loc.GQ l) (x : _root_.Formalism.BasicNotions.Loc.Om l) :
    _root_.GlobalTheory.Cyc.Model.extHom g (x : PadicComplex l) = ((g x : _root_.Formalism.BasicNotions.Loc.Om l) : PadicComplex l) := by
  simp only [_root_.GlobalTheory.Cyc.Model.extHom, UniformSpace.Completion.mapRingHom]
  rw [UniformSpace.Completion.extensionHom_coe]; rfl

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Cyc.Model.extHom_mul (g h : _root_.Formalism.BasicNotions.Loc.GQ l) (y : PadicComplex l) :
    _root_.GlobalTheory.Cyc.Model.extHom (g * h) y =
      _root_.GlobalTheory.Cyc.Model.extHom g (_root_.GlobalTheory.Cyc.Model.extHom h y) := by
  refine UniformSpace.Completion.induction_on y (isClosed_eq (continuous_cyc_extHom _)
    ((continuous_cyc_extHom g).comp (continuous_cyc_extHom h))) fun x => ?_
  rw [cyc_extHom_coe, cyc_extHom_coe, cyc_extHom_coe]; rfl

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Cyc.Model.extHom_one (y : PadicComplex l) :
    _root_.GlobalTheory.Cyc.Model.extHom (1 : _root_.Formalism.BasicNotions.Loc.GQ l) y = y := by
  refine UniformSpace.Completion.induction_on y
    (isClosed_eq (continuous_cyc_extHom _) continuous_id) fun x => ?_
  rw [cyc_extHom_coe]; rfl

def actC : GQ l →* (PadicComplex l ≃+* PadicComplex l) where
  toFun g := { extHom g with
    invFun := extHom g⁻¹
    left_inv := fun y => by
      change extHom g⁻¹ (extHom g y) = y
      rw [← extHom_mul, inv_mul_cancel, extHom_one]
    right_inv := fun y => by
      change extHom g (extHom g⁻¹ y) = y
      rw [← extHom_mul, mul_inv_cancel, extHom_one] }
  map_one' := by ext y; exact extHom_one y
  map_mul' g h := by ext y; exact extHom_mul g h y

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
private theorem norm_cyc_extHom (g : _root_.Formalism.BasicNotions.Loc.GQ l) (y : PadicComplex l) :
    ‖_root_.GlobalTheory.Cyc.Model.extHom g y‖ = ‖y‖ := by
  refine UniformSpace.Completion.induction_on y
    (isClosed_eq (continuous_norm.comp (continuous_cyc_extHom g)) continuous_norm) fun x => ?_
  rw [cyc_extHom_coe, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
  exact (_root_.GlobalTheory.Cyc.Model.isom_gal g).norm_map_of_map_zero (map_zero _) x

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Cyc.Model.isActC_actC :
    _root_.GlobalTheory.Cyc.IsActC (_root_.GlobalTheory.Cyc.Model.actC (l := l)) :=
  ⟨fun g x => cyc_extHom_coe g x, fun g y => norm_cyc_extHom g y⟩

def chiZ : GQ l →* ℤ_[l]ˣ :=
  (cyclotomicCharacter (Om l) l).comp (MulSemiringAction.toRingAut (GQ l) (Om l))

def chi : GQ l →* ℚ_[l]ˣ :=
  (Units.map (algebraMap ℤ_[l] ℚ_[l]).toMonoidHom).comp chiZ

theorem chi_val (g : GQ l) : (chi g : ℚ_[l]) = ((chiZ g : ℤ_[l]) : ℚ_[l]) := rfl

theorem isCyc_chi : IsCyc (chi (l := l)) := by
  intro g m ζ hζ
  refine ⟨(PadicInt.toZModPow m (chiZ g : ℤ_[l])).val, ?_, ?_⟩
  · have : ‖(chiZ g : ℤ_[l]) - ((PadicInt.toZModPow m (chiZ g : ℤ_[l])).val : ℤ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
        map_natCast, ZMod.natCast_zmod_val, sub_self]
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at this
    exact this
  · exact cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GQ l) (Om l) g) ζ hζ

theorem chi_cont : Continuous fun g : GQ l => (chi g : ℚ_[l]) :=
  (continuous_subtype_val : Continuous fun x : ℤ_[l] => (x : ℚ_[l])).comp
    ((Units.continuous_val (M := ℤ_[l])).comp (cyclotomicCharacter.continuous l ℚ_[l] (Om l)))

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Cyc.Model.cyc_irred (n : ℕ) :
    Irreducible (cyclotomic (l ^ (n + 1)) ℚ_[l]) := by
  have hP : (Ideal.span {(l : ℤ_[l])}).IsPrime :=
    PadicInt.maximalIdeal_eq_span_p (p := l) ▸ (IsLocalRing.maximalIdeal.isMaximal _).isPrime
  have hnu : ¬ IsUnit (l : ℤ_[l]) := fun h => hP.ne_top (Ideal.span_singleton_eq_top.2 h)
  have hE := cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt l n
  have hmap : taylor (1 : ℤ_[l]) (cyclotomic (l ^ (n + 1)) ℤ_[l]) =
      ((cyclotomic (l ^ (n + 1)) ℤ).comp (X + 1)).map (Int.castRingHom ℤ_[l]) := by
    rw [taylor_apply, Polynomial.map_comp, map_cyclotomic]; simp
  have hmon : (taylor (1 : ℤ_[l]) (cyclotomic (l ^ (n + 1)) ℤ_[l])).Monic := by
    rw [taylor_apply]; exact (cyclotomic.monic _ _).comp_X_add_C 1
  have hdeg : (taylor (1 : ℤ_[l]) (cyclotomic (l ^ (n + 1)) ℤ_[l])).natDegree =
      ((cyclotomic (l ^ (n + 1)) ℤ).comp (X + 1)).natDegree := by
    rw [natDegree_taylor, natDegree_comp, natDegree_cyclotomic, natDegree_cyclotomic,
      show (X + 1 : ℤ[X]) = X + C 1 by simp, natDegree_X_add_C, mul_one]
  have hZ : Irreducible (cyclotomic (l ^ (n + 1)) ℤ_[l]) := by
    rw [← MulEquiv.irreducible_iff (taylorEquiv (1 : ℤ_[l]))]
    change Irreducible (taylor (1 : ℤ_[l]) _)
    refine irreducible_of_eisenstein_criterion hP ?_ ?_ ?_ ?_ hmon.isPrimitive
    · rw [hmon.leadingCoeff]; exact fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · intro k hk
      rw [degree_eq_natDegree hmon.ne_zero, Nat.cast_lt, hdeg] at hk
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 (hE.mem hk)
      rw [hmap, coeff_map, Ideal.mem_span_singleton, hd]
      exact ⟨d, by simp⟩
    · rw [degree_eq_natDegree hmon.ne_zero, natDegree_taylor, natDegree_cyclotomic, Nat.cast_pos]
      exact Nat.totient_pos.2 (pow_pos (Fact.out : l.Prime).pos _)
    · rw [taylor_coeff_zero, eval_one_cyclotomic_prime_pow, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
      rintro ⟨c, hc⟩
      apply hnu
      have hl : (l : ℤ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
      refine isUnit_iff_exists_inv.2 ⟨c, mul_left_cancel₀ hl ?_⟩
      rw [mul_one, ← mul_assoc, ← pow_two]; exact hc.symm
  have h := (cyclotomic.monic (l ^ (n + 1)) ℤ_[l]).irreducible_iff_irreducible_map_fraction_map
    (K := ℚ_[l]) |>.1 hZ
  rwa [map_cyclotomic] at h

def base (l : ℕ) [Fact l.Prime] : FinExt l := ⟨⊥, inferInstance⟩

theorem norm_sub_of_pow_eq {ζ : Om l} {m a b : ℕ} (hζ : IsPrimitiveRoot ζ (l ^ m)) (h : ζ ^ a = ζ ^ b) :
    ‖(a : ℚ_[l]) - (b : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
  have hl : l.Prime := Fact.out
  have hu := hζ.isUnit (pow_pos hl.pos m).ne'
  have h1 : a ≡ b [MOD l ^ m] := by
    rw [hζ.eq_orderOf]
    obtain ⟨u, rfl⟩ := hu
    rw [orderOf_units, ← pow_eq_pow_iff_modEq]
    ext; simpa using h
  have h2 : ((l : ℤ) ^ m) ∣ ((a : ℤ) - b) := by
    have := (Nat.modEq_iff_dvd.mp h1.symm); exact_mod_cast this
  have := (Padic.norm_int_le_pow_iff_dvd (p := l) ((a : ℤ) - b) m).mpr h2
  simpa using this

theorem exists_isGen {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) {j : ℕ} (hj : 1 ≤ j) :
    ∃ g, IsGen χ (base l) j g := by
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ (j + 1))
  have hco : (1 + l ^ j).Coprime (l ^ (j + 1)) := by
    apply Nat.Coprime.pow_right
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj
    rw [pow_succ, Nat.coprime_add_mul_right_left]
    exact Nat.coprime_one_left _
  have hζ' := hζ.pow_of_coprime _ hco
  have hmin : minpoly ℚ_[l] (ζ ^ (1 + l ^ j)) = minpoly ℚ_[l] ζ := by
    rw [← hζ.minpoly_eq_cyclotomic_of_irreducible (cyc_irred j),
      ← hζ'.minpoly_eq_cyclotomic_of_irreducible (cyc_irred j)]
  obtain ⟨g, hg⟩ : ∃ g : GQ l, g ζ = ζ ^ (1 + l ^ j) :=
    (isConjRoot_iff_exists_algEquiv.mp (hmin : IsConjRoot ℚ_[l] _ ζ))
  refine ⟨g, ?_, ?_⟩
  · have hle : Ks (base l) j ≤ IntermediateField.fixedField (Subgroup.zpowers g) := by
      refine sup_le (inf_le_left.trans bot_le) (IntermediateField.adjoin_le_iff.mpr ?_)
      intro x hx
      have hp : IsPrimitiveRoot (ζ ^ l) (l ^ j) := hζ.pow (pow_pos hl.pos _) (by ring)
      obtain ⟨i, -, rfl⟩ := hp.eq_pow_of_pow_eq_one hx
      have h1 : g ((ζ ^ l) ^ i) = (ζ ^ l) ^ i := by
        rw [map_pow, map_pow, hg, ← pow_mul ζ (1 + l ^ j), add_mul, one_mul, pow_add, ← pow_succ,
          hζ.pow_eq_one, mul_one]
      have : Subgroup.zpowers g ≤ MulAction.stabilizer (GQ l) ((ζ ^ l) ^ i) :=
        (Subgroup.zpowers_le).mpr h1
      exact fun σ => this σ.2
    intro x
    exact hle x.2 ⟨g, Subgroup.mem_zpowers g⟩
  · obtain ⟨a, ha, hga⟩ := hχ g (j + 1) ζ hζ.pow_eq_one
    have hb := norm_sub_of_pow_eq hζ (hga.symm.trans hg)
    have hn : ‖(l : ℚ_[l]) ^ j‖ = (l : ℝ) ^ (-(j : ℤ)) := Padic.norm_p_pow j
    have hlt : ‖((χ g : ℚ_[l]) - a) + ((a : ℚ_[l]) - ((1 + l ^ j : ℕ) : ℚ_[l]))‖ < ‖(l : ℚ_[l]) ^ j‖ := by
      refine (Padic.nonarchimedean _ _).trans_lt ?_
      rw [hn]
      refine (max_le ha hb).trans_lt (zpow_lt_zpow_right₀ hl1 (by push_cast; omega))
    have e : (χ g : ℚ_[l]) - 1 = (((χ g : ℚ_[l]) - a) + ((a : ℚ_[l]) - ((1 + l ^ j : ℕ) : ℚ_[l]))) + (l : ℚ_[l]) ^ j := by
      push_cast; ring
    rw [e, Padic.add_eq_max_of_ne hlt.ne, max_eq_right hlt.le, hn]

theorem chi_Hinf {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (K : FinExt l) {σ : GQ l} (hσ : σ ∈ Hinf K) :
    (χ σ : ℚ_[l]) = 1 := by
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have key : ∀ m : ℕ, ‖(χ σ : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    intro m
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ m)
    obtain ⟨a, ha, hga⟩ := hχ σ m ζ hζ.pow_eq_one
    have hmem : ζ ∈ Kinf K := (le_sup_right : _ ≤ Kinf K)
      (IntermediateField.subset_adjoin _ _ ⟨m, hζ.pow_eq_one⟩)
    have hfix : σ ζ = ζ := hσ ⟨ζ, hmem⟩
    have hb := norm_sub_of_pow_eq hζ (a := a) (b := 1) (by rw [← hga, hfix, pow_one])
    have := (Padic.nonarchimedean ((χ σ : ℚ_[l]) - (a : ℚ_[l])) _).trans (max_le ha hb)
    simpa using this
  by_contra hne
  have hpos : 0 < ‖(χ σ : ℚ_[l]) - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt l hpos
  exact absurd (key k) (not_le.mpr hk)

theorem pow_lt_first_radius {m : ℕ} (h : Lev l m) : (l : ℝ) ^ (-(m : ℤ)) < rho1 l := by
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  rw [rho1, ← Real.rpow_intCast]
  apply Real.rpow_lt_rpow_of_exponent_lt hl1
  rw [lt_div_iff₀ (by linarith)]
  push_cast
  have h1 : (1 : ℝ) ≤ m := by exact_mod_cast h.1
  by_cases h2 : l = 2
  · have h3 : (2 : ℝ) ≤ m := by exact_mod_cast h.2 h2
    have h4 : (l : ℝ) = 2 := by exact_mod_cast h2
    rw [h4]; linarith
  · have : (3 : ℝ) ≤ l := by have := hl.two_le; exact_mod_cast (by omega : 3 ≤ l)
    nlinarith

def Utw (σ : GQ l) : Matrix (Fin 1) (Fin 1) (PadicComplex l) := fun _ _ => chiC chi 1 σ

theorem chiC_one (σ : GQ l) : chiC chi 1 σ = (((chi σ : ℚ_[l]) : Om l) : PadicComplex l) := by
  simp only [chiC, zpow_one]; rfl

theorem exists_frame {m : ℕ} (h : Lev l m) :
    ∃ g, Frame chi (base l) m (Utw (l := l)) g ∧ Utw g ≠ 1 := by
  obtain ⟨g, hg⟩ := exists_isGen (isCyc_chi (l := l)) h.1
  have hn : ‖(Utw g - 1) 0 0‖ = (l : ℝ) ^ (-(m : ℤ)) := by
    rw [← hg.2, ← PadicComplex.norm_extends' l ((chi g : ℚ_[l]) - 1)]
    congr 1
    change chiC chi 1 g - 1 = algebraMap ℚ_[l] (PadicComplex l) ((chi g : ℚ_[l]) - 1)
    simp [chiC]
  refine ⟨g, ⟨hg, fun a b => ?_, fun σ _ a b => ⟨?_, ?_⟩, fun σ _ τ _ => ?_, fun σ hσ => ?_, fun a b => ?_⟩, ?_⟩
  · refine Continuous.continuousOn ?_
    simp only [Utw, chiC, zpow_one]
    exact (continuous_algebraMap ℚ_[l] (PadicComplex l)).comp chi_cont
  · exact ⟨_, IntermediateField.algebraMap_mem _ (chi σ : ℚ_[l]), (chiC_one σ).symm⟩
  · change ‖chiC chi 1 σ‖ ≤ 1
    rw [chiC_one, PadicComplex.norm_extends', chi_val]
    exact (chiZ σ : ℤ_[l]).2
  · ext a b; simp [Utw, chiC, Matrix.mul_apply]
  · ext a b
    have := chi_Hinf isCyc_chi _ hσ
    rw [Subsingleton.elim a b]
    simp [Utw, chiC, this]
  · rw [Subsingleton.elim a 0, Subsingleton.elim b 0, hn]; exact pow_lt_first_radius h
  · intro h1
    rw [h1, sub_self, Matrix.zero_apply, norm_zero] at hn
    have : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    exact absurd hn (zpow_pos this _).ne

theorem htBasis_twist (G : Subgroup (GQ l)) : HTBasis actC chi G (Utw (l := l)) {-1} := by
  refine ⟨fun _ _ => 1, fun _ => -1, ?_, fun _ => rfl, fun σ _ k => ?_⟩
  · rw [linearIndependent_unique_iff]
    intro h; exact one_ne_zero (congrFun h 0)
  · ext a
    simp [twAct, Utw, chiC, Matrix.mulVec, dotProduct]

theorem zeta_mem_Xj (K : FinExt l) (j : ℕ) {ζ : PadicComplex l} (h : IsPrimitiveRoot ζ (l ^ (j + 1))) :
    ζ ∈ Xj K j := by
  apply AddSubgroup.le_topologicalClosure
  refine (le_iSup₂_of_le (j + 1) (Nat.lt_succ_self j) le_rfl : Xlev K (j + 1) ≤ _) ?_
  refine AddSubgroup.subset_closure ⟨ζ, 1, h, ⟨⟨1, one_mem _, rfl⟩, by simp⟩, (mul_one _).symm⟩

theorem coc_twist (G : Subgroup (GQ l)) :
    CobOn G (twAct actC chi 1 (fun _ => (1 : Matrix (Fin 1) (Fin 1) (PadicComplex l)))) (ball l 1)
      (fun σ _ => chiC chi 1 σ - 1) ∧
    CocOn G (twAct actC chi 1 (fun _ => (1 : Matrix (Fin 1) (Fin 1) (PadicComplex l)))) (ball l 1)
      (fun σ _ => chiC chi 1 σ - 1) := by
  refine ⟨⟨fun _ => 1, fun _ => by simp, fun g _ => ?_⟩, ?_, fun g _ a => ?_, fun g _ h _ => ?_⟩
  · ext a; simp [twAct]
  · refine Continuous.continuousOn (continuous_pi fun _ => Continuous.sub ?_ continuous_const)
    change Continuous fun σ : GQ l => algebraMap ℚ_[l] (PadicComplex l) ((chi σ ^ (1 : ℤ) : ℚ_[l]ˣ) : ℚ_[l])
    simp only [zpow_one]
    exact (continuous_algebraMap ℚ_[l] (PadicComplex l)).comp chi_cont
  · have h1 : ‖chiC chi 1 g‖ ≤ 1 := by
      rw [chiC_one, PadicComplex.norm_extends', chi_val]
      exact (chiZ g : ℤ_[l]).2
    change ‖chiC chi 1 g - 1‖ ≤ 1
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 (by simp))
  · ext a
    have h1 : actC g (chiC chi 1 h) = chiC chi 1 h := by
      rw [chiC_one, isActC_actC.1, AlgEquiv.commutes]
    have h2 : chiC chi 1 (g * h) = chiC chi 1 g * chiC chi 1 h := by simp [chiC]
    simp only [twAct, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_one, h1, h2]
    ring

theorem isActC_unique {a b : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC a)
    (hb : IsActC b) : a = b := by
  ext g y
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (AddMonoidHomClass.isometry_of_norm (a g) (ha.2 g)).continuous
            (AddMonoidHomClass.isometry_of_norm (b g) (hb.2 g)).continuous
  | ih x => rw [ha.1, hb.1]

end GlobalTheory.Cyc.Model
