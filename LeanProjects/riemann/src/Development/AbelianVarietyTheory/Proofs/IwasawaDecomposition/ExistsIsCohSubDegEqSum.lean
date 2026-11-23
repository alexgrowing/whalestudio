import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB
open GlobalTheory.LB (resG_resG resG_self homOfLinear toMod fun_ext_of_cover)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)

namespace GlobalTheory.TriangularFrames

variable {C : Scheme.{0}} {F : C.Modules} {J : Type} {T : J → C.Opens} {κ : J → Type}
  [∀ j, Fintype (κ j)] {v : ∀ j, κ j → Γ(F, T j)} {α : Type}

variable (v) in

abbrev spn (e : ∀ j, α ↪ κ j) (S : Finset α) (j : J) {V : C.Opens} (h : V ≤ T j) :
    Submodule Γ(C, V) Γ(F, V) :=
  Submodule.span Γ(C, V) ((fun a => resM F h (v j (e j a))) '' (S : Set α))

theorem mem_spn_iff (hv : ∀ j, IsFrame (v j)) {e : ∀ j, α ↪ κ j} {S : Finset α} {j : J}
    {V : C.Opens} (h : V ≤ T j) {x : Γ(F, V)} :
    x ∈ spn v e S j h ↔ ∀ b, (∀ a ∈ S, e j a ≠ b) → ((hv j).basis h).repr x b = 0 := by
  have hB : (fun a => resM F h (v j (e j a))) '' (S : Set α) =
      ((hv j).basis h) '' ((e j) '' (S : Set α)) := by
    rw [Set.image_image]
    simp only [IsFrame.basis_apply]
  rw [spn, hB, Module.Basis.mem_span_image]
  constructor
  · intro hs b hb
    by_contra hne
    obtain ⟨a, ha, rfl⟩ := hs (Finsupp.mem_support_iff.2 hne)
    exact hb a ha rfl
  · intro H b hb
    by_contra hn
    exact (Finsupp.mem_support_iff.1 hb) (H b fun a ha hab => hn ⟨a, ha, hab⟩)

def sub (hv : ∀ j, IsFrame (v j)) (e : ∀ j, α ↪ κ j) (S : Finset α) : Sub F where
  sec V :=
    { carrier := {x | ∀ j (W : C.Opens) (h₁ : W ≤ V) (h₂ : W ≤ T j), resM F h₁ x ∈ spn v e S j h₂}
      add_mem' := fun hs ht j W h₁ h₂ => by
        rw [map_add]; exact add_mem (hs j W h₁ h₂) (ht j W h₁ h₂)
      zero_mem' := fun j W h₁ h₂ => by rw [map_zero]; exact zero_mem _
      smul_mem' := fun a s hs j W h₁ h₂ => by
        rw [resM_smul]; exact Submodule.smul_mem _ _ (hs j W h₁ h₂) }
  res_mem h s hs j W h₁ h₂ := by rw [resM_resM]; exact hs j W _ h₂
  mem_of_local {V s} H j W h₁ h₂ := by
    refine (mem_spn_iff hv h₂).2 fun b hb => ?_
    choose U hU hx hs using fun x : W => H x (h₁ x.2)
    refine fun_ext_of_cover (fun x => W ⊓ U x) (fun _ => inf_le_left)
      (fun x hx' => Opens.mem_iSup.2 ⟨⟨x, hx'⟩, hx', hx _⟩) fun x => ?_
    have := (mem_spn_iff hv _).1 (hs x j (W ⊓ U x) inf_le_right (inf_le_left.trans h₂)) b hb
    rw [resM_resM] at this
    rw [map_zero, ← IsFrame.repr_resM, resM_resM, this]

theorem res_mem_spn (hv : ∀ j, IsFrame (v j)) {e : ∀ j, α ↪ κ j} {S : Finset α} {j : J}
    {V W : C.Opens} (h : V ≤ T j) (h' : W ≤ V) {x : Γ(F, V)} (hx : x ∈ spn v e S j h) :
    resM F h' x ∈ spn v e S j (h'.trans h) := by
  rw [mem_spn_iff hv] at hx ⊢
  intro b hb
  rw [(hv j).repr_resM h h', hx b hb, map_zero]

variable [Fintype α] {rk : α → ℕ} {e : ∀ j, α ↪ κ j}

variable (v rk e) in

def IsTriangular (g : α → ∀ j j', Γ(C, T j ⊓ T j')) : Prop :=
  ∀ j j' a, ∃ cf : α → Γ(C, T j ⊓ T j'), cf a = g a j j' ∧ (∀ b, b ≠ a → rk a ≤ rk b → cf b = 0) ∧
    resM F inf_le_right (v j' (e j' a)) = ∑ b, cf b • resM F inf_le_left (v j (e j b))

variable {g : α → ∀ j j', Γ(C, T j ⊓ T j')}

theorem IsTriangular.res (H : IsTriangular v rk e g) (j j' : J) (a : α) {V : C.Opens}
    (h : V ≤ T j) (h' : V ≤ T j') : ∃ cf : α → Γ(C, V), cf a = resG C (le_inf h h') (g a j j') ∧
      (∀ b, b ≠ a → rk a ≤ rk b → cf b = 0) ∧
      resM F h' (v j' (e j' a)) = ∑ b, cf b • resM F h (v j (e j b)) := by
  obtain ⟨cf, h1, h2, h3⟩ := H j j' a
  refine ⟨fun b => resG C (le_inf h h') (cf b), by dsimp only; rw [h1], fun b hb hr => by dsimp only; rw [h2 b hb hr, map_zero], ?_⟩
  have e1 : resM F h' (v j' (e j' a)) = resM F (le_inf h h') (resM F inf_le_right (v j' (e j' a))) := by
    rw [resM_resM]
  rw [e1, h3, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [resM_smul, resM_resM]

theorem IsTriangular.spn_le (H : IsTriangular v rk e g) {S : Finset α}
    (hS : ∀ a ∈ S, ∀ b, rk b < rk a → b ∈ S) (j j' : J) {V : C.Opens}
    (h : V ≤ T j) (h' : V ≤ T j') : spn v e S j' h' ≤ spn v e S j h := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨cf, -, h2, h3⟩ := H.res j j' a h h'
  change resM F h' (v j' (e j' a)) ∈ spn v e S j h
  rw [h3]
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : b = a ∨ rk b < rk a
  · have hbS : b ∈ S := hb.elim (fun hba => hba ▸ ha) (hS a ha b)
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hbS, rfl⟩)
  · push_neg at hb
    rw [h2 b hb.1 hb.2, zero_smul]
    exact zero_mem _

theorem IsTriangular.mem_sub_iff (H : IsTriangular v rk e g) (hv : ∀ j, IsFrame (v j))
    {S : Finset α} (hS : ∀ a ∈ S, ∀ b, rk b < rk a → b ∈ S) (j : J) {V : C.Opens}
    (h : V ≤ T j) {x : Γ(F, V)} : x ∈ (sub hv e S).sec V ↔ x ∈ spn v e S j h := by
  constructor
  · intro hx
    have := hx j V le_rfl h
    rwa [resM_self] at this
  · intro hx j' W h₁ h₂
    exact H.spn_le hS j' j h₂ (h₁.trans h) (res_mem_spn hv h h₁ hx)

theorem IsTriangular.repr_eq (H : IsTriangular v rk e g) (hv : ∀ j, IsFrame (v j))
    {S : Finset α} {a : α} (ha : ∀ b ∈ S, rk b ≤ rk a) (j j' : J) {V : C.Opens}
    (h : V ≤ T j) (h' : V ≤ T j') {x : Γ(F, V)} (hx : x ∈ spn v e S j' h') :
    ((hv j).basis h).repr x (e j a) =
      resG C (le_inf h h') (g a j j') * ((hv j').basis h').repr x (e j' a) := by
  classical
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, rfl⟩ := hy
    obtain ⟨cf, h1, h2, h3⟩ := H.res j j' b h h'
    have hcf : cf a = resG C (le_inf h h') (g a j j') * (if b = a then 1 else 0) := by
      by_cases hab : b = a
      · subst hab
        rw [if_pos rfl, mul_one, h1]
      · rw [if_neg hab, mul_zero]
        exact h2 a (Ne.symm hab) (ha b hb)
    have hB : ∀ i, resM F h (v j i) = (hv j).basis h i := fun i => ((hv j).basis_apply h i).symm
    have hr : ((hv j').basis h').repr (resM F h' (v j' (e j' b))) (e j' a) = if b = a then 1 else 0 := by
      rw [← (hv j').basis_apply h' (e j' b), Module.Basis.repr_self, Finsupp.single_apply,
        (e j').injective.eq_iff]
    change ((hv j).basis h).repr (resM F h' (v j' (e j' b))) (e j a) =
      resG C (le_inf h h') (g a j j') * ((hv j').basis h').repr (resM F h' (v j' (e j' b))) (e j' a)
    rw [hr, h3, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
    simp only [hB, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
      (e j).injective.eq_iff, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rwa [mul_ite, mul_one, mul_zero] at hcf
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, map_add, Finsupp.add_apply, Finsupp.add_apply, hx, hy, mul_add]
  | smul c x _ hx =>
    rw [map_smul, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, hx, smul_eq_mul, smul_eq_mul,
      mul_left_comm]

theorem IsTriangular.isVB (H : IsTriangular v rk e g) (hT : ⨆ j, T j = ⊤)
    (hv : ∀ j, IsFrame (v j)) {S : Finset α} (hS : ∀ a ∈ S, ∀ b, rk b < rk a → b ∈ S) :
    IsVB (sub hv e S).toMod S.card := by
  classical
  intro x
  obtain ⟨j, hxj⟩ : ∃ j, x ∈ T j := by
    have hx : x ∈ (⨆ j, T j : C.Opens) := by rw [hT]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hx
  let σ : Fin S.card ≃ S := S.equivFin.symm
  have hmem : ∀ b ∈ S, v j (e j b) ∈ (sub hv e S).sec (T j) := by
    intro b hb
    refine (H.mem_sub_iff hv hS j le_rfl).2 ?_
    have h0 : resM F le_rfl (v j (e j b)) ∈ spn v e S j (le_rfl : T j ≤ T j) :=
      Submodule.subset_span ⟨b, hb, rfl⟩
    rwa [resM_self] at h0
  let w : Fin S.card → Γ((sub hv e S).toMod, T j) := fun k =>
    (sub hv e S).mkSec (v j (e j (σ k))) (hmem _ (σ k).2)
  refine ⟨T j, w, hxj, fun V h => ?_⟩
  let ι' : Fin S.card → κ j := fun k => e j (σ k)
  have hι' : Function.Injective ι' := fun k l hkl => σ.injective (Subtype.ext ((e j).injective hkl))
  have hinc : ∀ k, (sub hv e S).incl.app V (resM (sub hv e S).toMod h (w k)) = (hv j).basis h (ι' k) := by
    intro k
    rw [app_resM, Sub.incl_app_mkSec, IsFrame.basis_apply]
  have hLC : ∀ c : Fin S.card → Γ(C, V), (sub hv e S).incl.app V
      (Fintype.linearCombination Γ(C, V) (fun k => resM (sub hv e S).toMod h (w k)) c) =
        ∑ k, c k • (hv j).basis h (ι' k) := by
    intro c
    rw [Fintype.linearCombination_apply, ← GlobalTheory.QCoh.appLinear_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, GlobalTheory.QCoh.appLinear_apply, hinc]
  have hli : LinearIndependent Γ(C, V) (fun k => (hv j).basis h (ι' k)) :=
    ((hv j).basis h).linearIndependent.comp ι' hι'
  constructor
  · intro c d hcd
    have h1 := congrArg ((sub hv e S).incl.app V) hcd
    rw [hLC, hLC] at h1
    have h2 := Fintype.linearIndependent_iff.1 hli (c - d) (by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h1, sub_self])
    funext k
    exact sub_eq_zero.1 (h2 k)
  · intro t
    have ht : (sub hv e S).incl.app V t ∈ spn v e S j h :=
      (H.mem_sub_iff hv hS j h).1 ((sub hv e S).incl_app_mem t)
    refine ⟨fun k => ((hv j).basis h).repr ((sub hv e S).incl.app V t) (ι' k),
      (sub hv e S).incl_app_injective V ?_⟩
    rw [hLC]
    conv_rhs => rw [← ((hv j).basis h).sum_repr ((sub hv e S).incl.app V t)]
    refine Fintype.sum_of_injective ι' hι' _ _ (fun i hi => ?_) (fun k => rfl)
    rw [(mem_spn_iff hv h).1 ht i ?_, zero_smul]
    intro b hb hbi
    exact hi ⟨S.equivFin ⟨b, hb⟩, by simp [ι', σ, hbi]⟩

def refine (M : LB C) (idx : J → M.ι) (hle : ∀ j, T j ≤ M.U (idx j)) : LB C where
  ι := J
  U := T
  g j j' := res (inf_le_inf (hle j) (hle j')) (M.g (idx j) (idx j'))

theorem isLB_refine (hT : ⨆ j, T j = ⊤) {M : LB C} (hM : M.IsLB) (idx : J → M.ι)
    (hle : ∀ j, T j ≤ M.U (idx j)) : (refine M idx hle).IsLB where
  cover := hT
  g_self j := by
    have hg : ((refine M idx hle).g j j).val =
        resG C (inf_le_inf (hle j) (hle j)) (M.g (idx j) (idx j)).val :=
      GlobalTheory.LB.val_res _ _
    have h0 := hM.g_self (idx j)
    rw [Units.ext_iff, GlobalTheory.LB.val_res, Units.val_one] at h0
    apply Units.ext
    rw [GlobalTheory.LB.val_res, hg]
    have h1 := congrArg (resG C (hle j)) h0
    rw [resG_resG, map_one] at h1
    exact (resG_resG _ _ _).trans h1
  cocycle i j k := by
    have hg : ∀ i j : J, ((refine M idx hle).g i j).val =
        resG C (inf_le_inf (hle i) (hle j)) (M.g (idx i) (idx j)).val :=
      fun i j => GlobalTheory.LB.val_res _ _
    have h0 := hM.cocycle (idx i) (idx j) (idx k)
    rw [Units.ext_iff, Units.val_mul, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res] at h0
    apply Units.ext
    rw [Units.val_mul, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, hg i j, hg j k, hg i k]
    have h1 := congrArg (resG C (inf_le_inf (inf_le_inf (hle i) (hle j)) (hle k))) h0
    rw [map_mul, resG_resG, resG_resG, resG_resG] at h1
    exact (congrArg₂ (· * ·) (resG_resG _ _ _) (resG_resG _ _ _)).trans
      (h1.trans (resG_resG _ _ _).symm)

private theorem res_transition_mul_comm_square {M : LB C} (hM : M.IsLB) (i i' k k' : M.ι) {W : C.Opens}
    (h₁ : W ≤ M.U i) (h₂ : W ≤ M.U i') (h₃ : W ≤ M.U k) (h₄ : W ≤ M.U k') :
    resG C (le_inf h₁ h₃) (M.g i k).val * resG C (le_inf h₃ h₄) (M.g k k').val =
      resG C (le_inf h₁ h₂) (M.g i i').val * resG C (le_inf h₂ h₄) (M.g i' k').val := by
  have c1 := hM.cocycle i k k'
  have c2 := hM.cocycle i i' k'
  rw [Units.ext_iff, Units.val_mul, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res] at c1 c2
  have d1 := congrArg (resG C (le_inf (le_inf h₁ h₃) h₄)) c1
  have d2 := congrArg (resG C (le_inf (le_inf h₁ h₂) h₄)) c2
  rw [map_mul, resG_resG, resG_resG, resG_resG] at d1 d2
  exact d1.trans d2.symm

theorem lbIso_refine {M : LB C} (hM : M.IsLB) (idx : J → M.ι)
    (hle : ∀ j, T j ≤ M.U (idx j)) : LBIso (refine M idx hle) M := by
  have grp : ∀ {R : Type} [CommRing R] (X A B Y : Rˣ), X * B = A * Y → X = A * B⁻¹ * Y := by
    intro R _ X A B Y h
    rw [mul_right_comm, eq_mul_inv_iff_mul_eq, h]
  have hv2 : ∀ {U V W : C.Opens} (h : V ≤ U) (h' : W ≤ V) (u : Γ(C, U)ˣ),
      ((res h' (res h u) : Γ(C, W)ˣ) : Γ(C, W)) = resG C (h'.trans h) (u : Γ(C, U)) := by
    intro U V W h h' u
    rw [GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, resG_resG]
  refine ⟨⟨fun p => res (show M.U p.1 ⊓ T p.2 ≤ M.U p.1 ⊓ M.U (idx p.2) from
    inf_le_inf le_rfl (hle p.2)) (M.g p.1 (idx p.2))⟩, ?_⟩
  rintro ⟨i, j⟩ ⟨i', j'⟩
  apply grp
  apply Units.ext
  have key := res_transition_mul_comm_square hM i i' (idx j) (idx j') (W := (M.U i ⊓ T j) ⊓ (M.U i' ⊓ T j'))
    (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    ((inf_le_left.trans inf_le_right).trans (hle j)) ((inf_le_right.trans inf_le_right).trans (hle j'))
  exact ((Units.val_mul _ _).trans ((congrArg₂ (· * ·) (hv2 _ _ _) (hv2 _ _ _)).trans
    (key.trans (congrArg₂ (· * ·) (GlobalTheory.LB.val_res _ _).symm (hv2 _ _ _).symm)))).trans
    (Units.val_mul _ _).symm

private theorem coord_resM_eq_resG_coord {L : LB C} {V W : C.Opens} (h : W ≤ V) (s : Γ(toMod L, V)) (i : L.ι) :
    LB.coord (resM (toMod L) h s) i = resG C (inf_le_inf_right _ h) (LB.coord s i) := by rfl

theorem IsTriangular.exists_hom (H : IsTriangular v rk e g) (hv : ∀ j, IsFrame (v j))
    {S : Finset α} {a : α} (ha' : ∀ b ∈ S, rk b ≤ rk a)
    (u : ∀ j j', Γ(C, T j ⊓ T j')ˣ) (hu : ∀ j j', g a j j' = u j j') :
    ∃ φ : (sub hv e S).toMod ⟶ toMod ⟨J, T, u⟩, ∀ (V : C.Opens) (s : Γ((sub hv e S).toMod, V))
      (j : J) (W : C.Opens) (h₁ : W ≤ V) (h₂ : W ≤ T j),
      resG C (le_inf h₁ h₂) (LB.coord (φ.app V s) j) =
        ((hv j).basis h₂).repr (resM F h₁ ((sub hv e S).incl.app V s)) (e j a) := by
  let f : ∀ V : C.Opens, Γ((sub hv e S).toMod, V) → ∀ j, Γ(C, V ⊓ T j) := fun V s j =>
    ((hv j).basis (inf_le_right : V ⊓ T j ≤ T j)).repr
      (resM F inf_le_left ((sub hv e S).incl.app V s)) (e j a)
  have hf : ∀ (V : C.Opens) (s : Γ((sub hv e S).toMod, V)),
      f V s ∈ secOn (⟨J, T, u⟩ : LB C) V := by
    intro V s i j
    have hW₁ : V ⊓ T i ⊓ T j ≤ V := inf_le_left.trans inf_le_left
    have hW₂ : V ⊓ T i ⊓ T j ≤ T i := inf_le_left.trans inf_le_right
    have hW₃ : V ⊓ T i ⊓ T j ≤ T j := inf_le_right
    have hy : resM F hW₁ ((sub hv e S).incl.app V s) ∈ spn v e S j hW₃ :=
      (sub hv e S).incl_app_mem s j _ hW₁ hW₃
    have key := H.repr_eq hv ha' i j hW₂ hW₃ hy
    rw [hu] at key
    have e1 : resG C (inf_le_left : V ⊓ T i ⊓ T j ≤ V ⊓ T i) (f V s i) =
        ((hv i).basis hW₂).repr (resM F hW₁ ((sub hv e S).incl.app V s)) (e i a) := by
      simp only [f]
      rw [← IsFrame.repr_resM, resM_resM]
    have e2 : resG C (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          V ⊓ T i ⊓ T j ≤ V ⊓ T j) (f V s j) =
        ((hv j).basis hW₃).repr (resM F hW₁ ((sub hv e S).incl.app V s)) (e j a) := by
      simp only [f]
      rw [← IsFrame.repr_resM, resM_resM]
    exact e1.trans (key.trans (congrArg _ e2.symm))
  let hlin : ∀ V : C.Opens, Γ((sub hv e S).toMod, V) →ₗ[Γ(C, V)] Γ(toMod (⟨J, T, u⟩ : LB C), V) :=
    fun V =>
    { toFun := fun s => LB.mkSec (f V s) (hf V s)
      map_add' := fun s t => by
        refine GlobalTheory.LB.sec_ext fun j => ?_
        rw [GlobalTheory.LB.coord_add, GlobalTheory.LB.coord_mkSec, GlobalTheory.LB.coord_mkSec, GlobalTheory.LB.coord_mkSec]
        simp only [f, map_add, Finsupp.add_apply]
      map_smul' := fun c s => by
        refine GlobalTheory.LB.sec_ext fun j => ?_
        rw [RingHom.id_apply, GlobalTheory.LB.coord_smul, GlobalTheory.LB.coord_mkSec, GlobalTheory.LB.coord_mkSec]
        simp only [f]
        rw [← GlobalTheory.QCoh.appLinear_apply (sub hv e S).incl, map_smul, GlobalTheory.QCoh.appLinear_apply, resM_smul,
          map_smul, Finsupp.smul_apply, smul_eq_mul] }
  refine ⟨GlobalTheory.LB.homOfLinear hlin ?_, ?_⟩
  · intro V W h s
    refine GlobalTheory.LB.sec_ext fun j => ?_
    change LB.coord (LB.mkSec (f W (resM _ h s)) (hf W _)) j =
      LB.coord (resM (toMod (⟨J, T, u⟩ : LB C)) h (LB.mkSec (f V s) (hf V s))) j
    rw [coord_resM_eq_resG_coord, GlobalTheory.LB.coord_mkSec, GlobalTheory.LB.coord_mkSec]
    simp only [f]
    rw [app_resM, resM_resM, ← IsFrame.repr_resM, resM_resM]
  · intro V s j W h₁ h₂
    rw [GlobalTheory.LB.homOfLinear_app]
    rw [show hlin V s = LB.mkSec (f V s) (hf V s) from rfl, GlobalTheory.LB.coord_mkSec]
    simp only [f]
    rw [← IsFrame.repr_resM, resM_resM]

theorem IsTriangular.deg_insert [DecidableEq α] {k : Type} [Field k] [Algebra k Γ(C, ⊤)]
    [IsIntegral C] (hC : IsProjCurve k C) (H : IsTriangular v rk e g) (hT : ⨆ j, T j = ⊤)
    (hv : ∀ j, IsFrame (v j)) {S : Finset α} {a : α} (haS : a ∉ S) (ha : ∀ b ∈ S, rk b ≤ rk a)
    (hS : ∀ a ∈ S, ∀ b, rk b < rk a → b ∈ S)
    (hS' : ∀ c ∈ insert a S, ∀ b, rk b < rk c → b ∈ insert a S)
    (u : ∀ j j', Γ(C, T j ⊓ T j')ˣ) (hu : ∀ j j', g a j j' = u j j')
    (hL : LB.IsLB ⟨J, T, u⟩) :
    deg k (sub hv e (insert a S)).toMod = deg k (sub hv e S).toMod + degLB k ⟨J, T, u⟩ := by
  have hsub : ∀ (V : C.Opens) (x : Γ(F, V)), x ∈ (sub hv e S).sec V → x ∈ (sub hv e (insert a S)).sec V :=
    fun V x hx j W h₁ h₂ => Submodule.span_mono
      (Set.image_mono (Finset.coe_subset.2 (Finset.subset_insert a S))) (hx j W h₁ h₂)
  let f : (sub hv e S).toMod ⟶ (sub hv e (insert a S)).toMod :=
    (sub hv e (insert a S)).lift (sub hv e S).incl fun V s => hsub V _ ((sub hv e S).incl_app_mem s)
  have hf : f ≫ (sub hv e (insert a S)).incl = (sub hv e S).incl := Sub.lift_incl _ _ _
  have ha' : ∀ b ∈ insert a S, rk b ≤ rk a := by
    intro b hb
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact le_rfl
    · exact ha b hb
  obtain ⟨φ, hφ⟩ := H.exists_hom hv ha' u hu
  have hcoord : ∀ (V : C.Opens) (s : Γ((sub hv e (insert a S)).toMod, V)) (j : J),
      LB.coord (φ.app V s) j = ((hv j).basis (inf_le_right : V ⊓ T j ≤ T j)).repr
        (resM F inf_le_left ((sub hv e (insert a S)).incl.app V s)) (e j a) := by
    intro V s j
    have h0 := hφ V s j (V ⊓ T j) inf_le_left inf_le_right
    rwa [resG_self] at h0
  have hfs : ∀ (V : C.Opens) (s : Γ((sub hv e S).toMod, V)),
      (sub hv e (insert a S)).incl.app V (f.app V s) = (sub hv e S).incl.app V s := by
    intro V s
    have h0 := congrArg (fun m => Scheme.Modules.Hom.app m V) hf
    simp only [Scheme.Modules.Hom.comp_app] at h0
    rw [← h0]
    rfl
  have hzero : f ≫ φ = 0 := by
    refine Scheme.Modules.hom_ext _ _ fun V => ?_
    rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.zero_app]
    ext s j
    change LB.coord (φ.app V (f.app V s)) j = LB.coord (0 : Γ(toMod (⟨J, T, u⟩ : LB C), V)) j
    rw [hcoord, hfs, GlobalTheory.LB.coord_zero]
    have hx := (sub hv e S).incl_app_mem s j (V ⊓ T j) inf_le_left inf_le_right
    refine (mem_spn_iff hv _).1 hx (e j a) fun b hb hba => ?_
    exact haS ((e j).injective hba ▸ hb)
  have hmono : Mono f := mono_of_mono_fac hf
  have hepi : Epi φ := by
    rw [GlobalTheory.QCoh.epi_iff_stalkLinear_surjective]
    intro x t
    obtain ⟨U, hxU, τ, rfl⟩ := (toMod (⟨J, T, u⟩ : LB C)).presheaf.exists_germ_eq t
    obtain ⟨j, hxj⟩ : ∃ j, x ∈ T j := by
      have hx : x ∈ (⨆ j, T j : C.Opens) := by rw [hT]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 hx
    have hxW : x ∈ U ⊓ T j := ⟨hxU, hxj⟩
    let y0 : Γ(F, U ⊓ T j) := LB.coord τ j • resM F inf_le_right (v j (e j a))
    have hy0 : y0 ∈ (sub hv e (insert a S)).sec (U ⊓ T j) := by
      refine (H.mem_sub_iff hv hS' j inf_le_right).2 ?_
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, Finset.mem_insert_self a S, rfl⟩)
    refine ⟨(sub hv e (insert a S)).toMod.presheaf.germ (U ⊓ T j) x hxW
      ((sub hv e (insert a S)).mkSec y0 hy0), ?_⟩
    rw [GlobalTheory.QCoh.stalkLinear_germ, ← (toMod (⟨J, T, u⟩ : LB C)).presheaf.germ_res_apply
      (homOfLE (inf_le_left : U ⊓ T j ≤ U)) x hxW τ]
    congr 1
    refine GlobalTheory.LB.sec_ext fun j' => ?_
    change _ = LB.coord (resM _ (inf_le_left : U ⊓ T j ≤ U) τ) j'
    rw [coord_resM_eq_resG_coord, hcoord, Sub.incl_app_mkSec]
    have hW1 : U ⊓ T j ⊓ T j' ≤ T j' := inf_le_right
    have hW2 : U ⊓ T j ⊓ T j' ≤ T j := inf_le_left.trans inf_le_right
    have hz := hy0 j (U ⊓ T j ⊓ T j') inf_le_left hW2
    have key := H.repr_eq hv ha' j' j hW1 hW2 hz
    rw [hu] at key
    have hrj : ((hv j).basis hW2).repr (resM F inf_le_left y0) (e j a) =
        resG C (inf_le_left : U ⊓ T j ⊓ T j' ≤ U ⊓ T j) (LB.coord τ j) := by
      simp only [y0]
      rw [resM_smul, resM_resM, ← (hv j).basis_apply hW2 (e j a), map_smul, Module.Basis.repr_self,
        Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
    rw [key, hrj]
    have hc : _ := (GlobalTheory.LB.coord_mem τ : _) j' j
    have hc2 := congrArg (resG C (show U ⊓ T j ⊓ T j' ≤ U ⊓ T j' ⊓ T j from
      le_inf (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (inf_le_left.trans inf_le_right))) hc
    rw [map_mul, resG_resG, resG_resG, resG_resG] at hc2
    exact hc2.symm
  have hex : (ShortComplex.mk f φ hzero).Exact := by
    rw [GlobalTheory.QCoh.exact_iff_stalkLinear]
    intro x t
    obtain ⟨U, hxU, y, rfl⟩ := (sub hv e (insert a S)).toMod.presheaf.exists_germ_eq t
    constructor
    · intro hy
      change GlobalTheory.QCoh.stalkLinear φ x _ = 0 at hy
      rw [GlobalTheory.QCoh.stalkLinear_germ] at hy
      have hy' : (toMod (⟨J, T, u⟩ : LB C)).presheaf.germ U x hxU (φ.app U y) =
          (toMod (⟨J, T, u⟩ : LB C)).presheaf.germ U x hxU 0 := by
        rw [hy, map_zero]
      obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ x hxU hxU _ _ hy'
      rw [map_zero] at hW
      obtain ⟨j, hxj⟩ : ∃ j, x ∈ T j := by
        have hx : x ∈ (⨆ j, T j : C.Opens) := by rw [hT]; trivial
        exact TopologicalSpace.Opens.mem_iSup.1 hx
      have hWU : W ≤ U := leOfHom iU
      have hW' : W ⊓ T j ≤ U := inf_le_left.trans hWU
      have hφ0 : resM _ hWU (φ.app U y) = 0 := hW
      have hzS : resM F hW' ((sub hv e (insert a S)).incl.app U y) ∈ (sub hv e S).sec (W ⊓ T j) := by
        refine (H.mem_sub_iff hv hS j inf_le_right).2 ?_
        rw [mem_spn_iff hv]
        intro b hb
        have hz' := (sub hv e (insert a S)).incl_app_mem y j (W ⊓ T j) hW' inf_le_right
        by_cases hba : b = e j a
        · subst hba
          have h0 := hφ W (resM _ hWU y) j (W ⊓ T j) inf_le_left inf_le_right
          rw [app_resM, hφ0, GlobalTheory.LB.coord_zero, map_zero, app_resM, resM_resM] at h0
          exact h0.symm
        · refine (mem_spn_iff hv _).1 hz' b fun c hc hcb => ?_
          rcases Finset.mem_insert.1 hc with rfl | hc
          · exact hba hcb.symm
          · exact hb c hc hcb
      have hxWj : x ∈ W ⊓ T j := ⟨hxW, hxj⟩
      have hgerm : GlobalTheory.QCoh.stalkLinear f x ((sub hv e S).toMod.presheaf.germ (W ⊓ T j) x hxWj
          ((sub hv e S).mkSec _ hzS)) = (sub hv e (insert a S)).toMod.presheaf.germ U x hxU y := by
        rw [GlobalTheory.QCoh.stalkLinear_germ, ← (sub hv e (insert a S)).toMod.presheaf.germ_res_apply
          (homOfLE hW') x hxWj y]
        congr 1
      exact ⟨_, hgerm⟩
    · rintro ⟨t', ht'⟩
      rw [← ht']
      change GlobalTheory.QCoh.stalkLinear φ x (GlobalTheory.QCoh.stalkLinear f x t') = 0
      rw [← LinearMap.comp_apply, ← GlobalTheory.QCoh.stalkLinear_comp, hzero, GlobalTheory.QCoh.stalkLinear_zero,
        LinearMap.zero_apply]
  have hSE : (ShortComplex.mk f φ hzero).ShortExact := ⟨hex⟩
  haveI : GlobalTheory.QCoh.IsFiniteQC (sub hv e S).toMod := (H.isVB hT hv hS).isFiniteQC
  haveI : GlobalTheory.QCoh.IsFiniteQC (sub hv e (insert a S)).toMod := (H.isVB hT hv hS').isFiniteQC
  haveI : GlobalTheory.QCoh.IsFiniteQC (toMod (⟨J, T, u⟩ : LB C)) := (isVB_toMod hL).isFiniteQC
  have h3 := hC.deg_shortExact hSE
  unfold degLB
  exact h3

end GlobalTheory.TriangularFrames

namespace GlobalTheory.TriangularFrames

theorem exists_isCohSub_deg_eq_sum (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)]
    [IsIntegral C] (hC : IsProjCurve k C) (F : C.Modules) (J : Type) (T : J → C.Opens)
    (hT : ⨆ j, T j = ⊤) (κ : J → Type) [∀ j, Fintype (κ j)] (v : ∀ j, κ j → Γ(F, T j))
    (hv : ∀ j, IsFrame (v j)) (α : Type) [Fintype α] (rk : α → ℕ) (e : ∀ j, α ↪ κ j)
    (M : α → LB C) (hM : ∀ a, (M a).IsLB) (idx : ∀ a, J → (M a).ι)
    (hle : ∀ a j, T j ≤ (M a).U (idx a j))
    (H : ∀ j j' a, ∃ cf : α → Γ(C, T j ⊓ T j'),
      cf a = resG C (inf_le_inf (hle a j) (hle a j')) ((M a).g (idx a j) (idx a j')).val ∧
      (∀ b, b ≠ a → rk a ≤ rk b → cf b = 0) ∧
      GlobalTheory.Twist.resM F inf_le_right (v j' (e j' a)) =
        ∑ b, cf b • GlobalTheory.Twist.resM F inf_le_left (v j (e j b)))
    (S : Finset α) (hS : ∀ a ∈ S, ∀ b, rk b < rk a → b ∈ S) :
    ∃ (G : C.Modules) (i : G ⟶ F), IsCohSub i ∧ deg k G = ∑ a ∈ S, degLB k (M a) ∧
      ∀ (j : J) (V : C.Opens) (h : V ≤ T j) (x : Γ(F, V)), (∃ y, i.app V y = x) ↔
        x ∈ Submodule.span Γ(C, V) ((fun a => GlobalTheory.Twist.resM F h (v j (e j a))) '' (S : Set α)) := by
  classical
  let g : α → ∀ j j', Γ(C, T j ⊓ T j') := fun a j j' =>
    resG C (inf_le_inf (hle a j) (hle a j')) ((M a).g (idx a j) (idx a j')).val
  have HT : IsTriangular v rk e g := H
  refine ⟨(sub hv e S).toMod, (sub hv e S).incl, ⟨inferInstance, (HT.isVB hT hv hS).isFiniteQC⟩, ?_,
    fun j V h x => ((sub hv e S).mem_sec_iff).symm.trans (HT.mem_sub_iff hv hS j h)⟩
  have key : ∀ n, ∀ S : Finset α, S.card = n → (∀ a ∈ S, ∀ b, rk b < rk a → b ∈ S) →
      deg k (sub hv e S).toMod = ∑ a ∈ S, degLB k (M a) := by
    intro n
    induction n with
    | zero =>
      intro S hS0 hS
      obtain rfl := Finset.card_eq_zero.1 hS0
      rw [Finset.sum_empty]
      have h0 := HT.isVB hT hv (S := ∅) (by simp)
      rw [Finset.card_empty] at h0
      exact deg_eq_zero_of_isZero k (isVB_zero_iff.1 h0)
    | succ n ih =>
      intro S hSn hS
      have hne : S.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨a, haS, hamax⟩ := S.exists_max_image rk hne
      have hS'cl : ∀ c ∈ S.erase a, ∀ b, rk b < rk c → b ∈ S.erase a := by
        intro c hc b hb
        have hcS := Finset.mem_of_mem_erase hc
        refine Finset.mem_erase.2 ⟨?_, hS c hcS b hb⟩
        rintro rfl
        exact absurd (hamax c hcS) (not_le.2 hb)
      have hins : insert a (S.erase a) = S := Finset.insert_erase haS
      have hcard : (S.erase a).card = n := by rw [Finset.card_erase_of_mem haS]; omega
      let u : ∀ j j', Γ(C, T j ⊓ T j')ˣ := fun j j' =>
        res (inf_le_inf (hle a j) (hle a j')) ((M a).g (idx a j) (idx a j'))
      have hu : ∀ j j', g a j j' = u j j' := fun j j' => (GlobalTheory.LB.val_res _ _).symm
      have hLa : LB.IsLB (⟨J, T, u⟩ : LB C) := isLB_refine hT (hM a) (idx a) (hle a)
      have hd := HT.deg_insert hC hT hv (Finset.notMem_erase a S)
        (fun b hb => hamax b (Finset.mem_of_mem_erase hb)) hS'cl (by rw [hins]; exact hS) u hu hLa
      rw [hins] at hd
      rw [hd, ih (S.erase a) hcard hS'cl, ← Finset.sum_erase_add S _ haS]
      congr 1
      exact degLB_congr hLa (hM a) (lbIso_refine (hM a) (idx a) (hle a))
  exact key _ S rfl hS

end GlobalTheory.TriangularFrames
