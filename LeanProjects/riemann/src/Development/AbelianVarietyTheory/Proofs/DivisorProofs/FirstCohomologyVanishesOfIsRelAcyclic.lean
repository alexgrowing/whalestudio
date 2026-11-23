import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CharChPartZero

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.ExactCoboundaryTriple

theorem exists_triple {κ : Type} [LinearOrder κ] {t : Finset κ} (ht : t.card = 3) :
    ∃ i j k, i < j ∧ j < k ∧ t = {i, j, k} := by
  refine ⟨t.orderEmbOfFin ht 0, t.orderEmbOfFin ht 1, t.orderEmbOfFin ht 2,
    (t.orderEmbOfFin ht).strictMono (by decide), (t.orderEmbOfFin ht).strictMono (by decide), ?_⟩
  ext x
  constructor
  · intro hx
    have : x ∈ Set.range (t.orderEmbOfFin ht) := by rw [Finset.range_orderEmbOfFin]; exact hx
    obtain ⟨m, rfl⟩ := this
    fin_cases m <;> simp
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> exact Finset.orderEmbOfFin_mem _ _ _

theorem totalD_triple {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (A : Cube.{0} κ R)
    (x : ∀ s, A.obj s) {i j k : κ} (hij : i < j) (hjk : j < k) :
    Cube.totalD A x {i, j, k} =
      Cube.res A (by intro; simp; tauto) (x {j, k}) - Cube.res A (by intro; simp; tauto) (x {i, k}) +
        Cube.res A (by intro; simp; tauto) (x {i, j}) := by
  have hik := hij.trans hjk
  have e1 : ({i, j, k} : Finset κ).erase i = {j, k} := by
    ext m; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl)
      · exact ⟨hij.ne', by tauto⟩
      · exact ⟨hik.ne', by tauto⟩
  have e2 : ({i, j, k} : Finset κ).erase j = {i, k} := by
    ext m; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl)
      · exact ⟨hij.ne, by tauto⟩
      · exact ⟨hjk.ne', by tauto⟩
  have e3 : ({i, j, k} : Finset κ).erase k = {i, j} := by
    ext m; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl)
      · exact ⟨hik.ne, by tauto⟩
      · exact ⟨hjk.ne, by tauto⟩
  have s1 : cubeSign ({i, j, k} : Finset κ) i = 1 :=
    cubeSign_eq_one_of_forall_le (by simp [hij.le, hik.le])
  have s2 : cubeSign ({i, j, k} : Finset κ) j = -1 := by
    have h := cubeSign_erase_of_lt (t := {i, j, k}) (by simp) hij
    rw [e1, cubeSign_eq_one_of_forall_le (by simp [hjk.le])] at h
    omega
  have s3 : cubeSign ({i, j, k} : Finset κ) k = 1 := by
    have h := cubeSign_erase_of_lt (t := {i, j, k}) (by simp) hik
    have h' := cubeSign_erase_of_lt (t := {j, k}) (by simp) hjk
    rw [e1] at h
    rw [cubeSign_eq_one_of_forall_le (by
      intro m hm
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hm
      exact (hm.2.resolve_left hm.1).ge)] at h'
    omega
  rw [Cube.totalD_apply, Finset.sum_insert (by simp [hij.ne, hik.ne]), Finset.sum_pair hjk.ne,
    Cube.res_congr A x e1 _ (by intro; simp; tauto), Cube.res_congr A x e2 _ (by intro; simp; tauto),
    Cube.res_congr A x e3 _ (by intro; simp; tauto), s1, s2, s3]
  simp only [one_smul, neg_smul, sub_eq_add_neg, add_assoc]

variable {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X)

theorem coboundary_of_exact {κ : Type} [LinearOrder κ] (W : κ → X.Opens)
    (hW : (cechLB f M W).ExactAt (0 + 1)) (Φ : ∀ k l, SecOnR f M (W k ⊓ W l))
    (hΦ : ∀ k l m (O : X.Opens) (h₁ : O ≤ W k ⊓ W l) (h₂ : O ≤ W l ⊓ W m) (h₃ : O ≤ W k ⊓ W m),
      SecOnR.restrict f M h₁ (Φ k l) + SecOnR.restrict f M h₂ (Φ l m) = SecOnR.restrict f M h₃ (Φ k m)) :
    ∃ y : ∀ k, SecOnR f M (W k), ∀ k l (O : X.Opens) (h : O ≤ W k ⊓ W l),
      SecOnR.restrict f M h (Φ k l) =
        SecOnR.restrict f M (h.trans inf_le_right) (y l) - SecOnR.restrict f M (h.trans inf_le_left) (y k) := by
  classical
  have hle : ∀ {s : Finset κ} {i : κ}, i ∈ s → ⨅ j ∈ s, W j ≤ W i := fun {s i} hi => biInf_le W hi
  let x : ∀ s : Finset κ, SecOnR f M (⨅ j ∈ s, W j) := fun s =>
    if h : s.Nonempty then
      SecOnR.restrict f M (le_inf (hle (s.min'_mem h)) (hle (s.max'_mem h))) (Φ (s.min' h) (s.max' h))
    else 0
  have hcongr : ∀ {k l k' l' : κ} (_ : k = k') (_ : l = l') {O : X.Opens} (h : O ≤ W k ⊓ W l)
      (h' : O ≤ W k' ⊓ W l'), SecOnR.restrict f M h (Φ k l) = SecOnR.restrict f M h' (Φ k' l') := by
    rintro k l _ _ rfl rfl O h h'
    rfl
  have hx : ∀ {k l : κ} (_ : k < l), x {k, l} =
      SecOnR.restrict f M (le_inf (hle (by simp)) (hle (by simp))) (Φ k l) := by
    intro k l hkl
    have hn : ({k, l} : Finset κ).Nonempty := by simp
    simp only [x, dif_pos hn]
    exact hcongr (by simp [hkl.le]) (by simp [hkl.le]) _ _
  have hE := (cechComplex_exactAt_succ_iff (secCube f M W) 0).1 hW
  have hd : Cube.d (secCube f M W) (0 + 2) (fun s => x s.1) = 0 := by
    funext t
    rw [Cube.d_apply_eq_totalD (secCube f M W) _ x (fun _ => rfl)]
    obtain ⟨t, ht⟩ := t
    obtain ⟨i, j, k, hij, hjk, rfl⟩ := exists_triple ht
    refine (totalD_triple (secCube f M W) x hij hjk).trans ?_
    rw [hx hij, hx hjk, hx (hij.trans hjk)]
    simp only [res_secCube]
    erw [SecOnR.restrict_restrict, SecOnR.restrict_restrict, SecOnR.restrict_restrict]
    rw [← hΦ i j k _ (le_inf (hle (by simp)) (hle (by simp))) (le_inf (hle (by simp)) (hle (by simp)))]
    change (_ : SecOnR f M _) = 0
    abel
  obtain ⟨z, hz⟩ := (hE _).1 hd
  have hs : ∀ k, W k ≤ ⨅ j ∈ ({k} : Finset κ), W j := fun k => by simp
  let y : ∀ k, SecOnR f M (W k) := fun k => SecOnR.restrict f M (hs k) (z ⟨{k}, Finset.card_singleton k⟩)
  have hlt : ∀ k l, k < l → ∀ (O : X.Opens) (h : O ≤ W k ⊓ W l),
      SecOnR.restrict f M h (Φ k l) =
        SecOnR.restrict f M (h.trans inf_le_right) (y l) - SecOnR.restrict f M (h.trans inf_le_left) (y k) := by
    intro k l hkl O h
    have hO : O ≤ ⨅ j ∈ ({k, l} : Finset κ), W j := by
      simp only [Finset.mem_insert, Finset.mem_singleton, le_iInf_iff]
      rintro j (rfl | rfl)
      · exact h.trans inf_le_left
      · exact h.trans inf_le_right
    have e := (congrFun hz ⟨{k, l}, Finset.card_pair hkl.ne⟩).symm.trans
      (Cube.d_one_apply_pair (secCube f M W) z hkl)
    have e' := congrArg (SecOnR.restrict f M hO) ((hx hkl).symm.trans e)
    simp only [res_secCube] at e'
    erw [map_sub, SecOnR.restrict_restrict, SecOnR.restrict_restrict, SecOnR.restrict_restrict] at e'
    exact e'.trans (congrArg₂ (· - ·) (SecOnR.restrict_restrict f (hs l) _ _).symm
      (SecOnR.restrict_restrict f (hs k) _ _).symm)
  have h0 : ∀ k (O : X.Opens) (h : O ≤ W k ⊓ W k), SecOnR.restrict f M h (Φ k k) = 0 := fun k O h =>
    add_eq_left.1 (hΦ k k k O h h h)
  refine ⟨y, fun k l O h => ?_⟩
  rcases lt_trichotomy k l with hkl | rfl | hkl
  · exact hlt k l hkl O h
  · rw [h0, sub_self]
  · have h' : O ≤ W l ⊓ W k := le_inf (h.trans inf_le_right) (h.trans inf_le_left)
    have e := hΦ k l k O h h' (le_inf (h.trans inf_le_left) (h.trans inf_le_left))
    rw [h0, hlt l k hkl O h'] at e
    rw [eq_neg_of_add_eq_zero_left e, neg_sub]

theorem coboundary_of_refine {I κ : Type} (V : I → X.Opens) (W : κ → X.Opens) (hW : ⨆ k, W k = ⊤) (r : κ → I)
    (hr : ∀ k, W k ≤ V (r k)) (Φ : ∀ a b, SecOnR f M (V a ⊓ V b))
    (hΦ : ∀ a b d (O : X.Opens) (h₁ : O ≤ V a ⊓ V b) (h₂ : O ≤ V b ⊓ V d) (h₃ : O ≤ V a ⊓ V d),
      SecOnR.restrict f M h₁ (Φ a b) + SecOnR.restrict f M h₂ (Φ b d) = SecOnR.restrict f M h₃ (Φ a d))
    (y : ∀ k, SecOnR f M (W k))
    (hy : ∀ k l (O : X.Opens) (h : O ≤ W k ⊓ W l),
      SecOnR.restrict f M (h.trans (inf_le_inf (hr k) (hr l))) (Φ (r k) (r l)) =
        SecOnR.restrict f M (h.trans inf_le_right) (y l) - SecOnR.restrict f M (h.trans inf_le_left) (y k)) :
    ∃ Ψ : ∀ a, SecOnR f M (V a), ∀ a b, Φ a b =
      SecOnR.restrict f M inf_le_left (Ψ a) - SecOnR.restrict f M inf_le_right (Ψ b) := by
  have hcov : ∀ U : X.Opens, U ≤ ⨆ k, U ⊓ W k := fun U => by
    rw [← inf_iSup_eq, hW, inf_top_eq]
  have hg : ∀ a, ∃ t : SecOnR f M (V a), ∀ k, SecOnR.restrict f M (inf_le_left : V a ⊓ W k ≤ V a) t =
      SecOnR.restrict f M (inf_le_inf_left _ (hr k)) (Φ a (r k)) -
        SecOnR.restrict f M inf_le_right (y k) := by
    intro a
    refine (SecOnR.existsUnique_glue f (fun k => V a ⊓ W k) (fun _ => inf_le_left) (hcov _) _ ?_).exists
    intro k l
    simp only [map_sub, SecOnR.restrict_restrict]
    have h : V a ⊓ W k ⊓ (V a ⊓ W l) ≤ W k ⊓ W l := inf_le_inf inf_le_right inf_le_right
    rw [← hΦ a (r k) (r l) _ (inf_le_left.trans (inf_le_inf_left _ (hr k)))
      (h.trans (inf_le_inf (hr k) (hr l))), hy k l _ h]
    abel
  choose Ψ hΨ using hg
  refine ⟨Ψ, fun a b => SecOnR.ext_of_cover f (fun k => V a ⊓ V b ⊓ W k) (fun _ => inf_le_left) (hcov _)
    fun k => ?_⟩
  have ea := congrArg (SecOnR.restrict f M (inf_le_inf_right _ inf_le_left :
    V a ⊓ V b ⊓ W k ≤ V a ⊓ W k)) (hΨ a k)
  have eb := congrArg (SecOnR.restrict f M (inf_le_inf_right _ inf_le_right :
    V a ⊓ V b ⊓ W k ≤ V b ⊓ W k)) (hΨ b k)
  simp only [map_sub, SecOnR.restrict_restrict] at ea eb ⊢
  rw [ea, eb, ← hΦ a b (r k) _ inf_le_left (inf_le_inf inf_le_right (hr k))]
  abel

theorem exists_affine_refinement [CompactSpace X] {I : Type} (V : I → X.Opens) (hV : ⨆ a, V a = ⊤) :
    ∃ (n : ℕ) (W : Fin n → X.Opens) (r : Fin n → I), (∀ k, IsAffineOpen (W k)) ∧ ⨆ k, W k = ⊤ ∧
      ∀ k, W k ≤ V (r k) := by
  classical
  have h : ∀ x : X, ∃ (a : I) (U : X.Opens), IsAffineOpen U ∧ x ∈ U ∧ U ≤ V a := by
    intro x
    have hx : x ∈ ⨆ a, V a := by rw [hV]; trivial
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨U, hU, hxU, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens ha
    exact ⟨a, U, hU, hxU, hle⟩
  choose c U hU hxU hle using h
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set X)) (fun x => (U x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxU x⟩)
  refine ⟨T.card, fun k => U (T.equivFin.symm k), fun k => c (T.equivFin.symm k), fun _ => hU _, ?_,
    fun _ => hle _⟩
  refine top_unique fun x _ => ?_
  obtain ⟨p, hp, hx⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ x))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨T.equivFin ⟨p, hp⟩, ?_⟩
  simpa using hx

theorem firstCohomologyVanishes_of_isRelAcyclic (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R))
    (M : LB X) (hM : M.IsLB) (hX : CompactSpace X) (h : GlobalTheory.CxForm.IsRelAcyclic f f M) : FirstCohomologyVanishes M := by
  intro I V c hV hc φ hφ
  obtain ⟨n, W, r, hW, hWc, hr⟩ := exists_affine_refinement V hc
  let Φ : ∀ a b, SecOnR f M (V a ⊓ V b) := fun a b =>
    (SecOn.chart hM (c a) (inf_le_left.trans (hV a))).symm (φ a b)
  have hch : ∀ a b (O : X.Opens) (h₁ : O ≤ V a ⊓ V b),
      SecOn.chart hM (c a) (h₁.trans (inf_le_left.trans (hV a))) (SecOnR.restrict f M h₁ (Φ a b)) =
        rs X h₁ (φ a b) := fun a b O h₁ =>
    (SecOn.chart_restrict hM (c a) (inf_le_left.trans (hV a)) h₁ (Φ a b)).trans
      (congrArg _ (LinearEquiv.apply_symm_apply _ _))
  have hΦ : ∀ a b d (O : X.Opens) (h₁ : O ≤ V a ⊓ V b) (h₂ : O ≤ V b ⊓ V d) (h₃ : O ≤ V a ⊓ V d),
      SecOnR.restrict f M h₁ (Φ a b) + SecOnR.restrict f M h₂ (Φ b d) = SecOnR.restrict f M h₃ (Φ a d) := by
    intro a b d O h₁ h₂ h₃
    have ha : O ≤ M.U (c a) := h₁.trans (inf_le_left.trans (hV a))
    have hb : O ≤ M.U (c b) := h₂.trans (inf_le_left.trans (hV b))
    apply (SecOn.chart hM (c a) ha).injective
    have e := congrArg (rs X (le_inf h₁ (h₂.trans inf_le_right) : O ≤ V a ⊓ V b ⊓ V d)) (hφ a b d)
    simp only [map_add, map_mul, rs_rs] at e
    refine ((SecOn.chart hM (c a) ha).map_add _ _).trans ?_
    refine Eq.trans ?_ (e.trans (hch a d O h₃).symm)
    exact congrArg₂ (· + ·) (hch a b O h₁) ((SecOn.chart_change hM (c a) (c b) ha hb _).trans
      (congrArg (rs X (le_inf ha hb) (M.g (c a) (c b)).val * ·) (hch b d O h₂)))
  obtain ⟨y, hy⟩ := coboundary_of_exact f M W (h ⊤ (isAffineOpen_top _) (Fin n) W hW (by rw [hWc]; rfl) 0)
    (fun k l => SecOnR.restrict f M (inf_le_inf (hr k) (hr l)) (Φ (r k) (r l)))
    (fun k l m O h₁ h₂ h₃ => by
      simp only [SecOnR.restrict_restrict]
      exact hΦ _ _ _ _ _ _ _)
  obtain ⟨Ψ, hΨ⟩ := coboundary_of_refine f M V W hWc r hr Φ hΦ y (fun k l O hO => by
    simpa only [SecOnR.restrict_restrict] using hy k l O hO)
  refine ⟨fun a => SecOn.chart hM (c a) (hV a) (Ψ a), fun a b => ?_⟩
  have ha : V a ⊓ V b ≤ M.U (c a) := inf_le_left.trans (hV a)
  have hb : V a ⊓ V b ≤ M.U (c b) := inf_le_right.trans (hV b)
  have e := congrArg (SecOn.chart hM (c a) ha) (hΨ a b)
  refine ((LinearEquiv.apply_symm_apply _ _).symm.trans e).trans ?_
  refine ((SecOn.chart hM (c a) ha).map_sub _ _).trans ?_
  exact congrArg₂ (· - ·) (SecOn.chart_restrict hM (c a) (hV a) inf_le_left (Ψ a))
    ((SecOn.chart_change hM (c a) (c b) ha hb _).trans
      (congrArg (rs X (le_inf ha hb) (M.g (c a) (c b)).val * ·)
        (SecOn.chart_restrict hM (c b) (hV b) inf_le_right (Ψ b))))

end GlobalTheory.ExactCoboundaryTriple
