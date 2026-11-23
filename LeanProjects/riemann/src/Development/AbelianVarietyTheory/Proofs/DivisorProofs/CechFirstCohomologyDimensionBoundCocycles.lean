import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HomologyRestrictScalarsBijective
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrdCechDep

open GlobalTheory GlobalTheory.AbLaw

variable {K : Type} [Field K] {Y : Scheme.{0}} (s : Y ⟶ Sp K)

abbrev ch (V : Y.Opens) : SecOnR s (LB.triv Y) V ≃ₗ[Γ(Y, V)] Γ(Y, V) :=
  SecOnR.chart s (LB.isLB_triv Y) PUnit.unit le_top

theorem ch_restrict {U V : Y.Opens} (h : V ≤ U) (x : SecOnR s (LB.triv Y) U) :
    ch s V (SecOnR.restrict s (LB.triv Y) h x) = resG Y h (ch s U x) :=
  SecOn.chart_restrict (LB.isLB_triv Y) PUnit.unit le_top h x

theorem cst_eq (V : Y.Opens) (r : K) :
    cst s V r = (s.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom r) := rfl

theorem ch_smul (V : Y.Opens) (r : K) (x : SecOnR s (LB.triv Y) V) :
    ch s V (r • x) = cst s V r * ch s V x := by
  rw [SecOnR.smul_def, LinearEquiv.map_smul]
  rfl

theorem resG_eq_zero {U V : Y.Opens} (e : U = V) (h : V ≤ U) (x : Γ(Y, U)) (hx : resG Y h x = 0) :
    x = 0 := by
  subst e
  simpa using hx

section Coc

variable {κ : Type} [LinearOrder κ] (D : κ → Y.Opens)

theorem biInf_pair_le {t : Finset κ} {a c : κ} (ha : a ∈ t) (hc : c ∈ t) :
    ⨅ j ∈ t, D j ≤ D a ⊓ D c :=
  le_inf (biInf_le _ ha) (biInf_le _ hc)

theorem ne_two (t : {t : Finset κ // t.card = 1 + 1}) : t.1.Nonempty :=
  Finset.card_pos.1 (by rw [t.2]; norm_num)

def coc (e : ∀ i i' : κ, Γ(Y, D i ⊓ D i')) : Cube.Term (secCube s (LB.triv Y) D) (1 + 1) :=
  fun t => (ch s (⨅ j ∈ t.1, D j)).symm
    (resG Y (biInf_pair_le D (t.1.min'_mem (ne_two t)) (t.1.max'_mem (ne_two t))) (e _ _))

theorem resG_e_congr (e : ∀ i i' : κ, Γ(Y, D i ⊓ D i')) {a a' c c' : κ} (ha : a = a') (hc : c = c')
    {V : Y.Opens} (h : V ≤ D a ⊓ D c) (h' : V ≤ D a' ⊓ D c') :
    resG Y h (e a c) = resG Y h' (e a' c') := by
  subst ha hc; rfl

theorem coc_pair (e : ∀ i i' : κ, Γ(Y, D i ⊓ D i')) {i i' : κ} (hii : i < i')
    (t : {t : Finset κ // t.card = 1 + 1}) (ht : t.1 = {i, i'}) :
    ch s _ (coc s D e t) = resG Y (biInf_pair_le D (by simp [ht]) (by simp [ht])) (e i i') := by
  have hmin : t.1.min' (ne_two t) = i := by
    refine le_antisymm (Finset.min'_le _ _ (by simp [ht])) (Finset.le_min' _ _ _ ?_)
    intro y hy
    rw [ht] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact le_rfl
    · exact hii.le
  have hmax : t.1.max' (ne_two t) = i' := by
    refine le_antisymm (Finset.max'_le _ _ _ ?_) (Finset.le_max' _ _ (by simp [ht]))
    intro y hy
    rw [ht] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact hii.le
    · exact le_rfl
  unfold coc
  rw [LinearEquiv.apply_symm_apply]
  exact resG_e_congr D e hmin hmax _ _

end Coc

section Tri

variable {κ : Type} [LinearOrder κ] (D : κ → Y.Opens)

def IsCoc (e : ∀ i i' : κ, Γ(Y, D i ⊓ D i')) : Prop :=
  ∀ i i' i'', resG Y (inf_le_left : D i ⊓ D i' ⊓ D i'' ≤ D i ⊓ D i') (e i i') +
    resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right : D i ⊓ D i' ⊓ D i'' ≤ D i' ⊓ D i'')
      (e i' i'') =
    resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right : D i ⊓ D i' ⊓ D i'' ≤ D i ⊓ D i'')
      (e i i'')

theorem ch_d (p : ℕ) (x : Cube.Term (secCube s (LB.triv Y) D) p)
    (t : {t : Finset κ // t.card = p + 1}) :
    ch s (⨅ j ∈ t.1, D j) (Cube.d (secCube s (LB.triv Y) D) p x t) =
      ∑ i : t.1, cubeSign t.1 i.1 • resG Y (iInf_le_iInf_of_subset D (Finset.erase_subset i.1 t.1))
        (ch s (⨅ j ∈ (Cube.eraseIdx t i).1, D j) (x (Cube.eraseIdx t i))) := by
  rw [Cube.d_apply]
  show ch s _ (∑ i : t.1, cubeSign t.1 i.1 • (SecOnR.restrict s (LB.triv Y)
    (iInf_le_iInf_of_subset D (Finset.erase_subset i.1 t.1)) (x (Cube.eraseIdx t i)) :
      SecOnR s (LB.triv Y) (⨅ j ∈ t.1, D j))) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  congr 1
  exact ch_restrict s _ _

theorem coc_tri (e : ∀ i i' : κ, Γ(Y, D i ⊓ D i')) (he : IsCoc D e) {a b c : κ} (hab : a < b)
    (hbc : b < c) (t : {t : Finset κ // t.card = 1 + 1 + 1}) (ht : t.1 = {a, b, c}) :
    Cube.d (secCube s (LB.triv Y) D) (1 + 1) (coc s D e) t = 0 := by
  have hac := hab.trans hbc
  have ha : a ∈ t.1 := by simp [ht]
  have hb : b ∈ t.1 := by simp [ht]
  have hc : c ∈ t.1 := by simp [ht]
  have ea : t.1.erase a = {b, c} := by
    rw [ht]; exact Finset.erase_insert (by simp [hab.ne, hac.ne])
  have eb : t.1.erase b = {a, c} := by
    rw [ht, Finset.erase_insert_of_ne hab.ne, Finset.erase_insert (by simp [hbc.ne])]
  have ec : t.1.erase c = {a, b} := by
    rw [ht]
    ext i
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h, h' | h' | h'⟩
      · exact Or.inl h'
      · exact Or.inr h'
      · exact (h h').elim
    · rintro (rfl | rfl)
      · exact ⟨hac.ne, Or.inl rfl⟩
      · exact ⟨hbc.ne, Or.inr (Or.inl rfl)⟩
  have sa : cubeSign t.1 a = 1 := cubeSign_eq_one_of_forall_le (by
    rw [ht]; simp [hab.le, hac.le])
  have sbc : cubeSign ({b, c} : Finset κ) b = 1 := cubeSign_eq_one_of_forall_le (by simp [hbc.le])
  have sb : cubeSign t.1 b = -1 := by
    have := cubeSign_erase_of_lt ha hab
    rw [ea, sbc] at this
    omega
  have scc : cubeSign ({b, c} : Finset κ) c = -1 := by
    have := cubeSign_erase_of_lt (t := ({b, c} : Finset κ)) (by simp) hbc
    rw [Finset.erase_insert (by simp [hbc.ne]), cubeSign_singleton] at this
    omega
  have sc : cubeSign t.1 c = 1 := by
    have := cubeSign_erase_of_lt ha hac
    rw [ea, scc] at this
    omega
  have hu : (Finset.univ : Finset t.1) = {⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩} := by
    ext ⟨i, hi⟩
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq]
    rw [ht] at hi
    simpa using hi
  refine (ch s (⨅ j ∈ t.1, D j)).map_eq_zero_iff.1 ?_
  rw [ch_d, hu, Finset.sum_insert (by simp [hab.ne, hac.ne]),
    Finset.sum_pair (by simp [hbc.ne])]
  rw [coc_pair s D e hbc _ ea, coc_pair s D e hac _ eb, coc_pair s D e hab _ ec, sa, sb, sc]
  have hV : ⨅ j ∈ t.1, D j ≤ D a ⊓ D b ⊓ D c :=
    le_inf (le_inf (biInf_le _ ha) (biInf_le _ hb)) (biInf_le _ hc)
  have h' := congrArg (resG Y hV) (he a b c)
  simp only [map_add, resG_resG] at h' ⊢
  rw [one_smul, one_smul, neg_smul, one_smul]
  linear_combination h'

end Tri

section Main

variable {κ : Type} [LinearOrder κ] (D : κ → Y.Opens)

theorem coc_mem (e : ∀ i i' : κ, Γ(Y, D i ⊓ D i')) (he : IsCoc D e) :
    coc s D e ∈ LinearMap.ker (Cube.d (secCube s (LB.triv Y) D) (1 + 1)) := by
  rw [LinearMap.mem_ker]
  funext t
  have h3 : t.1.card = 3 := t.2
  let f := t.1.orderEmbOfFin h3
  have ht : t.1 = {f 0, f 1, f 2} := by
    ext j
    constructor
    · intro hj
      have : j ∈ Set.range f := by rw [Finset.range_orderEmbOfFin]; exact hj
      obtain ⟨k, rfl⟩ := this
      fin_cases k <;> simp
    · intro hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl <;> exact Finset.orderEmbOfFin_mem _ _ _
  exact coc_tri s D e he (f.strictMono (by decide)) (f.strictMono (by decide)) t ht

theorem resG_inj {U V : Y.Opens} (e : U = V) (h : V ≤ U) {x x' : Γ(Y, U)}
    (hx : resG Y h x = resG Y h x') : x = x' := by
  subst e
  simpa using hx

theorem single_le (i : κ) : D i ≤ ⨅ j ∈ ({i} : Finset κ), D j := by simp

theorem ch_sum_smul {ι : Type} [Fintype ι] (c : ι → K)
    (x : ι → Cube.Term (secCube s (LB.triv Y) D) (1 + 1)) (t : {t : Finset κ // t.card = 1 + 1}) :
    ch s (⨅ j ∈ t.1, D j) ((∑ b, c b • x b) t) = ∑ b, AbLaw.cst s (⨅ j ∈ t.1, D j) (c b) * ch s _ (x b t) := by
  rw [Finset.sum_apply]
  have key : ∀ v : ι → SecOnR s (LB.triv Y) (⨅ j ∈ t.1, D j),
      ch s _ (∑ b, c b • v b) = ∑ b, AbLaw.cst s (⨅ j ∈ t.1, D j) (c b) * ch s _ (v b) := by
    intro v
    rw [map_sum]
    exact Finset.sum_congr rfl fun b _ => ch_smul s _ _ _
  exact key fun b => x b t

end Main

section Pair

variable {κ : Type} [LinearOrder κ] (D : κ → Y.Opens)

def hh (y : Cube.Term (secCube s (LB.triv Y) D) (0 + 1)) (i : κ) : Γ(Y, D i) :=
  - resG Y (single_le D i) (ch s _ (y ⟨{i}, Finset.card_singleton i⟩))

theorem y_congr (y : Cube.Term (secCube s (LB.triv Y) D) (0 + 1)) {u u' : {t : Finset κ // t.card = 0 + 1}}
    (h : u.1 = u'.1) {V : Y.Opens} (hV : V ≤ ⨅ j ∈ u.1, D j) (hV' : V ≤ ⨅ j ∈ u'.1, D j) :
    resG Y hV (ch s _ (y u)) = resG Y hV' (ch s _ (y u')) := by
  obtain rfl : u = u' := Subtype.ext h
  rfl

theorem resG_cst {U V : Y.Opens} (h : V ≤ U) (r : K) :
    resG Y h (AbLaw.cst s U r) = AbLaw.cst s V r :=
  rs_cst s h r

theorem pair_lt {ι : Type} [Fintype ι] (e : ι → ∀ i i' : κ, Γ(Y, D i ⊓ D i')) (c : ι → K)
    (y : Cube.Term (secCube s (LB.triv Y) D) (0 + 1))
    (hy : Cube.d (secCube s (LB.triv Y) D) (0 + 1) y = ∑ b, c b • coc s D (e b)) {i i' : κ}
    (hii : i < i') :
    ∑ b, AbLaw.cst s (D i ⊓ D i') (c b) * e b i i' =
      resG Y inf_le_left (hh s D y i) - resG Y inf_le_right (hh s D y i') := by
  let t : {t : Finset κ // t.card = 0 + 1 + 1} := ⟨{i, i'}, Finset.card_pair hii.ne⟩
  have hW : D i ⊓ D i' = ⨅ j ∈ t.1, D j := by
    show D i ⊓ D i' = ⨅ j ∈ ({i, i'} : Finset κ), D j
    rw [Finset.iInf_insert, Finset.iInf_singleton]
  have hi : i ∈ t.1 := by simp [t]
  have hi' : i' ∈ t.1 := by simp [t]
  have hle : ⨅ j ∈ t.1, D j ≤ D i ⊓ D i' := biInf_pair_le D hi hi'
  apply resG_inj hW hle
  have key : ch s (⨅ j ∈ t.1, D j) (Cube.d (secCube s (LB.triv Y) D) (0 + 1) y t) =
      ch s (⨅ j ∈ t.1, D j) ((∑ b, c b • coc s D (e b)) t) := by rw [hy]
  rw [ch_d, ch_sum_smul] at key
  have hu : (Finset.univ : Finset t.1) = {⟨i, hi⟩, ⟨i', hi'⟩} := by
    ext ⟨j, hj⟩
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq]
    simpa [t] using hj
  rw [hu, Finset.sum_pair (by simp [hii.ne])] at key
  have si : cubeSign t.1 i = 1 := cubeSign_eq_one_of_forall_le (by simp [t, hii.le])
  have si' : cubeSign t.1 i' = -1 := by
    have := cubeSign_erase_of_lt (t := t.1) hi hii
    have e1 : t.1.erase i = {i'} := Finset.erase_insert (by simp [hii.ne])
    rw [e1, cubeSign_singleton] at this
    omega
  have ei : (Cube.eraseIdx t ⟨i, hi⟩).1 = ({i'} : Finset κ) := Finset.erase_insert (by simp [hii.ne])
  have ei' : (Cube.eraseIdx t ⟨i', hi'⟩).1 = ({i} : Finset κ) := by
    show ({i, i'} : Finset κ).erase i' = {i}
    rw [Finset.erase_insert_of_ne hii.ne, Finset.erase_singleton]
    simp
  rw [y_congr s D y (u' := ⟨{i'}, Finset.card_singleton i'⟩) ei _
      ((single_le D i').trans' (hle.trans inf_le_right)),
    y_congr s D y (u' := ⟨{i}, Finset.card_singleton i⟩) ei' _
      ((single_le D i).trans' (hle.trans inf_le_left)), si, si'] at key
  have hc : ∀ b, ch s (⨅ j ∈ t.1, D j) (coc s D (e b) t) = resG Y hle (e b i i') :=
    fun b => coc_pair s D (e b) hii t rfl
  simp only [hc] at key
  simp only [hh, map_sum, map_mul, map_sub, map_neg, resG_resG, resG_cst]
  rw [one_smul, neg_smul, one_smul] at key
  linear_combination -key

end Pair

theorem exists_comb_coboundary : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (s : Y ⟶ Sp K) (g : ℕ) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), Module.Finite K ((GlobalTheory.AbLaw.cechLB s (LB.triv Y) D).homology 1) → Module.finrank K ((GlobalTheory.AbLaw.cechLB s (LB.triv Y) D).homology 1) ≤ g → ∀ (e : Fin (g + 1) → ∀ i i' : κ, Γ(Y, D i ⊓ D i')), (∀ b i i' i'', resG Y (inf_le_left : D i ⊓ D i' ⊓ D i'' ≤ D i ⊓ D i') (e b i i') + resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right : D i ⊓ D i' ⊓ D i'' ≤ D i' ⊓ D i'') (e b i' i'') = resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right : D i ⊓ D i' ⊓ D i'' ≤ D i ⊓ D i'') (e b i i'')) → ∃ c : Fin (g + 1) → K, c ≠ 0 ∧ ∃ h : ∀ i, Γ(Y, D i), ∀ i i', ∑ b, (s.appLE ⊤ (D i ⊓ D i') le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c b)) * e b i i' = resG Y inf_le_left (h i) - resG Y inf_le_right (h i') := by
  intro K _ Y s g κ _ _ D hfin hrank e he
  classical
  let A := secCube s (LB.triv Y) D
  let z : Fin (g + 1) → LinearMap.ker (Cube.d A (1 + 1)) :=
    fun b => ⟨coc s D (e b), coc_mem s D (e b) (he b)⟩
  haveI : Module.Finite K ((cechComplex A).homology 1) := hfin
  have hnli : ¬ LinearIndependent K (fun b => cechClass A 1 (z b)) := by
    intro hli
    have h1 := hli.fintype_card_le_finrank
    have h2 : Module.finrank K ((cechComplex A).homology 1) ≤ g := hrank
    simp only [Fintype.card_fin] at h1
    omega
  obtain ⟨c, hc, b0, hb0⟩ := Fintype.not_linearIndependent_iff.1 hnli
  have h0 : cechClass A 1 (∑ b, c b • z b) = 0 := by
    rw [map_sum]
    simpa only [map_smul] using hc
  obtain ⟨y, hy⟩ := (cechClass_succ_eq_zero_iff A 0 _).1 h0
  have hy' : Cube.d A (0 + 1) y = ∑ b, c b • coc s D (e b) := by
    rw [hy]
    simp [z]
  refine ⟨c, fun h => hb0 (by simp [h]), hh s D y, ?_⟩
  have hdiag : ∀ b i, e b i i = 0 := by
    intro b i
    have h := he b i i i
    have h' : resG Y (inf_le_left : D i ⊓ D i ⊓ D i ≤ D i ⊓ D i) (e b i i) = 0 := add_eq_right.1 h
    exact resG_eq_zero (by simp) _ _ h'
  intro i i'
  show ∑ b, AbLaw.cst s (D i ⊓ D i') (c b) * e b i i' = _
  rcases lt_trichotomy i i' with h | rfl | h
  · exact pair_lt s D e c y hy' h
  · simp [hdiag]
  · have P := pair_lt s D e c y hy' h
    have hanti : ∀ b, resG Y (inf_le_left : D i ⊓ D i' ⊓ D i ≤ D i ⊓ D i') (e b i i') =
        - resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          D i ⊓ D i' ⊓ D i ≤ D i' ⊓ D i) (e b i' i) := by
      intro b
      have h1 := he b i i' i
      rw [hdiag, map_zero] at h1
      exact eq_neg_of_add_eq_zero_left h1
    have hW : D i ⊓ D i' = D i ⊓ D i' ⊓ D i := by
      refine le_antisymm (le_inf le_rfl inf_le_left) inf_le_left
    apply resG_inj hW inf_le_left
    have P' := congrArg (resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      D i ⊓ D i' ⊓ D i ≤ D i' ⊓ D i)) P
    simp only [map_sum, map_mul, map_sub, resG_cst, resG_resG] at P' ⊢
    simp only [hanti, mul_neg, Finset.sum_neg_distrib]
    linear_combination -P'

end GlobalTheory.OrdCechDep
