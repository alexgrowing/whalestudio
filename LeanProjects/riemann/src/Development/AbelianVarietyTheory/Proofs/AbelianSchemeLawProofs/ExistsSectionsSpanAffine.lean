import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecAff

section Calc
variable {X X' X'' : Scheme.{0}}

def rs {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) := (X.presheaf.map (homOfLE h).op).hom

def pa (φ : X' ⟶ X) {U : X.Opens} {V : X'.Opens} (h : V ≤ φ ⁻¹ᵁ U) : Γ(X, U) →+* Γ(X', V) :=
  (φ.appLE U V h).hom

theorem le_pre_top (φ : X' ⟶ X) {V : X'.Opens} : V ≤ φ ⁻¹ᵁ ⊤ := le_top

theorem le_pre_inf {φ : X' ⟶ X} {V : X'.Opens} {U U' : X.Opens} (h : V ≤ φ ⁻¹ᵁ U)
    (h' : V ≤ φ ⁻¹ᵁ U') : V ≤ φ ⁻¹ᵁ (U ⊓ U') := le_inf h h'

theorem rs_rs {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)) :
    rs h₂ (rs h₁ x) = rs (h₂.trans h₁) x := by
  change ((X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom) x = _
  rw [← Functor.map_comp]
  rfl

theorem rs_self {U : X.Opens} (h : U ≤ U) (x : Γ(X, U)) : rs h x = x := by
  change (X.presheaf.map (𝟙 _)).hom x = x
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem rs_pa (φ : X' ⟶ X) {U : X.Opens} {V W : X'.Opens} (h : V ≤ φ ⁻¹ᵁ U) (h₂ : W ≤ V)
    (x : Γ(X, U)) : rs h₂ (pa φ h x) = pa φ (h₂.trans h) x := by
  change (φ.appLE U V h ≫ X'.presheaf.map (homOfLE h₂).op).hom x = _
  rw [Scheme.Hom.appLE_map]
  rfl

theorem pa_rs (φ : X' ⟶ X) {U U' : X.Opens} {V : X'.Opens} (h₁ : U' ≤ U) (h : V ≤ φ ⁻¹ᵁ U')
    (x : Γ(X, U)) : pa φ h (rs h₁ x) = pa φ (h.trans (φ.preimage_mono h₁)) x := by
  change (X.presheaf.map (homOfLE h₁).op ≫ φ.appLE U' V h).hom x = _
  rw [Scheme.Hom.map_appLE]
  rfl

theorem pa_pa (φ : X' ⟶ X) (ψ : X'' ⟶ X') {U : X.Opens} {V : X'.Opens} {W : X''.Opens}
    (h : V ≤ φ ⁻¹ᵁ U) (h' : W ≤ ψ ⁻¹ᵁ V) (χ : X'' ⟶ X) (e : ψ ≫ φ = χ) (h'' : W ≤ χ ⁻¹ᵁ U)
    (x : Γ(X, U)) : pa ψ h' (pa φ h x) = pa χ h'' x := by
  subst e
  change (φ.appLE U V h ≫ ψ.appLE V W h').hom x = _
  rw [Scheme.Hom.appLE_comp_appLE]
  rfl

theorem pa_id {U V : X.Opens} (h : V ≤ (𝟙 X) ⁻¹ᵁ U) (x : Γ(X, U)) : pa (𝟙 X) h x = rs h x := by
  simp [pa, rs, Scheme.Hom.appLE]
  rfl

theorem pa_bijective (φ : X' ⟶ X) [IsOpenImmersion φ] {U : X.Opens} {V : X'.Opens}
    (h : V ≤ φ ⁻¹ᵁ U) (h' : φ ⁻¹ᵁ U ≤ V) (hU : U ≤ φ.opensRange) :
    Function.Bijective (pa φ h) := by
  obtain rfl : V = φ ⁻¹ᵁ U := le_antisymm h h'
  have := φ.isIso_app U hU
  have e : pa φ h = (φ.app U).hom := by rw [Scheme.Hom.app_eq_appLE]; rfl
  rw [e]
  exact ConcreteCategory.bijective_of_isIso (φ.app U)

theorem eq_of_cover {κ : Type} {U : X.Opens} (W : κ → X.Opens) (hW : ∀ a, W a ≤ U)
    (hc : U ≤ ⨆ a, W a) (x y : Γ(X, U)) (h : ∀ a, rs (hW a) x = rs (hW a) y) : x = y :=
  X.sheaf.eq_of_locally_eq' W U (fun a => homOfLE (hW a)) hc x y h

theorem glue_cover {κ : Type} {U : X.Opens} (W : κ → X.Opens) (hW : ∀ a, W a ≤ U)
    (hc : U ≤ ⨆ a, W a) (x : ∀ a, Γ(X, W a))
    (h : ∀ a b, rs (inf_le_left : W a ⊓ W b ≤ W a) (x a) = rs (inf_le_right : W a ⊓ W b ≤ W b) (x b)) :
    ∃ y : Γ(X, U), ∀ a, rs (hW a) y = x a := by
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W U (fun a => homOfLE (hW a)) hc x h
  exact ⟨s, hs⟩

theorem fun_extend (φ : X' ⟶ X) [IsOpenImmersion φ] (f : Γ(X, ⊤))
    (hφ : φ.opensRange = X.basicOpen f) {W : X.Opens} (hW : IsAffineOpen W) {W' : X'.Opens}
    (h : W' ≤ φ ⁻¹ᵁ W) (h' : φ ⁻¹ᵁ W ≤ W') (t : Γ(X', W')) :
    ∃ (N : ℕ) (x : Γ(X, W)), pa φ h x = pa φ (le_pre_top φ) f ^ N * t := by
  have hb : X.basicOpen (rs (le_top : W ≤ ⊤) f) = W ⊓ X.basicOpen f := X.basicOpen_res f _
  have hle : W' ≤ φ ⁻¹ᵁ X.basicOpen (rs (le_top : W ≤ ⊤) f) := by
    rw [hb, ← hφ]
    exact fun y hy => ⟨h hy, ⟨y, rfl⟩⟩
  obtain ⟨z, rfl⟩ := (pa_bijective φ hle ((φ.preimage_mono (X.basicOpen_le _)).trans h')
    (by rw [hb, hφ]; exact inf_le_right)).2 t
  obtain ⟨N, x, e⟩ := exists_eq_pow_mul_of_isAffineOpen X W hW _ z
  replace e : rs (X.basicOpen_le _) x =
    rs (X.basicOpen_le _) (rs (le_top : W ≤ ⊤) f) ^ N * z := e
  refine ⟨N, x, ?_⟩
  have := congrArg (pa φ hle) e
  rw [map_mul, map_pow, rs_rs, pa_rs, pa_rs] at this
  exact this

theorem fun_kill (φ : X' ⟶ X) [IsOpenImmersion φ] (f : Γ(X, ⊤))
    (hφ : φ.opensRange = X.basicOpen f) {W : X.Opens} (hW : IsCompact (W : Set X)) {W' : X'.Opens}
    (h : W' ≤ φ ⁻¹ᵁ W) (h' : φ ⁻¹ᵁ W ≤ W') (x : Γ(X, W)) (hx : pa φ h x = 0) :
    ∃ N : ℕ, rs (le_top : W ≤ ⊤) f ^ N * x = 0 := by
  have hb : X.basicOpen (rs (le_top : W ≤ ⊤) f) = W ⊓ X.basicOpen f := X.basicOpen_res f _
  have hle : W' ≤ φ ⁻¹ᵁ X.basicOpen (rs (le_top : W ≤ ⊤) f) := by
    rw [hb, ← hφ]
    exact fun y hy => ⟨h hy, ⟨y, rfl⟩⟩
  refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hW x _ ?_
  change rs (X.basicOpen_le _) x = 0
  apply (pa_bijective φ hle ((φ.preimage_mono (X.basicOpen_le _)).trans h')
    (by rw [hb, hφ]; exact inf_le_right)).1
  rw [pa_rs, map_zero]
  exact hx

theorem pow_mul_zero_mono {R : Type} [CommRing R] {a x : R} {m n : ℕ} (h : a ^ m * x = 0)
    (hmn : m ≤ n) : a ^ n * x = 0 := by
  rw [← Nat.sub_add_cancel hmn, pow_add, _root_.mul_assoc, h, mul_zero]

theorem exists_fin_cover [CompactSpace X] (M : LB X) (hM : M.IsLB) :
    ∃ (κ : Type) (_ : Fintype κ) (W : κ → X.Opens) (c : κ → M.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ M.U (c a)) ∧ ⊤ ≤ ⨆ a, W a := by
  have h : ∀ x : X, ∃ (W : X.Opens) (c : M.ι), IsAffineOpen W ∧ x ∈ W ∧ W ≤ M.U c := by
    intro x
    obtain ⟨c, hc⟩ := LB.mem_of_cover hM x
    obtain ⟨_, ⟨W, hW, rfl⟩, hx, hle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hc (M.U c).isOpen
    exact ⟨W, c, hW, hx, hle⟩
  choose W c hW hx hle using h
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set X))
    (fun x => (W x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  refine ⟨s, inferInstance, fun a => W a, fun a => c a, fun a => hW a, fun a => hle a, ?_⟩
  intro x _
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩

theorem sec_at {M : LB X} (s : LB.Sec M) (i j : M.ι) {W : X.Opens} (hi : W ≤ M.U i)
    (hj : W ≤ M.U j) :
    rs hi (s.f i) = rs (le_inf hi hj) (M.g i j : Γ(X, M.U i ⊓ M.U j)) * rs hj (s.f j) := by
  have : rs inf_le_left (s.f i) = (M.g i j : Γ(X, M.U i ⊓ M.U j)) * rs inf_le_right (s.f j) :=
    s.compat i j
  have := congrArg (rs (le_inf hi hj)) this
  rwa [map_mul, rs_rs, rs_rs] at this

theorem cocycle_at {M : LB X} (hM : M.IsLB) (i j k : M.ι) {W : X.Opens}
    (h₁ : W ≤ M.U i ⊓ M.U j) (h₂ : W ≤ M.U j ⊓ M.U k) (h₃ : W ≤ M.U i ⊓ M.U k) :
    rs h₁ (M.g i j : Γ(X, M.U i ⊓ M.U j)) * rs h₂ (M.g j k : Γ(X, M.U j ⊓ M.U k)) =
      rs h₃ (M.g i k : Γ(X, M.U i ⊓ M.U k)) :=
  congrArg Units.val (LB.res_cocycle hM i j k h₁ h₂ h₃)

theorem le_iSup_inf {κ : Type} (U : X.Opens) {W : κ → X.Opens} (hc : ⊤ ≤ ⨆ a, W a) :
    U ≤ ⨆ a, U ⊓ W a := by
  intro x hx
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc (TopologicalSpace.Opens.mem_top x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, hx, ha⟩

theorem sec_kill [CompactSpace X] (φ : X' ⟶ X) [IsOpenImmersion φ] (f : Γ(X, ⊤))
    (hφ : φ.opensRange = X.basicOpen f) (M : LB X) (hM : M.IsLB) (U' : M.ι → X'.Opens)
    (h : ∀ j, U' j ≤ φ ⁻¹ᵁ M.U j) (h' : ∀ j, φ ⁻¹ᵁ M.U j ≤ U' j) (s : LB.Sec M)
    (hs : ∀ j, pa φ (h j) (s.f j) = 0) :
    ∃ N : ℕ, ∀ j, rs (le_top : M.U j ≤ ⊤) f ^ N * s.f j = 0 := by
  obtain ⟨κ, _, W, c, hW, hWc, hc⟩ := exists_fin_cover M hM
  have : ∀ a, ∃ N : ℕ, rs (le_top : W a ≤ ⊤) f ^ N * rs (hWc a) (s.f (c a)) = 0 := by
    intro a
    refine fun_kill φ f hφ (hW a).isCompact le_rfl le_rfl _ ?_
    have := congrArg (rs ((φ.preimage_mono (hWc a)).trans (h' (c a)))) (hs (c a))
    rw [rs_pa, map_zero] at this
    rw [pa_rs]
    exact this
  choose n hn using this
  refine ⟨Finset.univ.sup n, fun j => ?_⟩
  refine eq_of_cover (fun a => M.U j ⊓ W a) (fun a => inf_le_left) (le_iSup_inf _ hc) _ _ fun a => ?_
  have := congrArg (rs (inf_le_right : M.U j ⊓ W a ≤ W a))
    (pow_mul_zero_mono (hn a) (Finset.le_sup (f := n) (Finset.mem_univ a)))
  rw [map_mul, map_pow, rs_rs, rs_rs, map_zero] at this
  rw [map_mul, map_pow, rs_rs, map_zero,
    sec_at s j (c a) inf_le_left (inf_le_right.trans (hWc a)), mul_left_comm, this, mul_zero]

theorem sec_extend [CompactSpace X] [QuasiSeparatedSpace X] (φ : X' ⟶ X) [IsOpenImmersion φ]
    (f : Γ(X, ⊤)) (hφ : φ.opensRange = X.basicOpen f) (M : LB X) (hM : M.IsLB)
    (U' : M.ι → X'.Opens) (h : ∀ j, U' j ≤ φ ⁻¹ᵁ M.U j) (h' : ∀ j, φ ⁻¹ᵁ M.U j ≤ U' j)
    (t : ∀ j, Γ(X', U' j))
    (ht : ∀ i j, rs (inf_le_left : U' i ⊓ U' j ≤ U' i) (t i) =
      pa φ (le_pre_inf (inf_le_left.trans (h i)) (inf_le_right.trans (h j)))
        (M.g i j : Γ(X, M.U i ⊓ M.U j)) *
        rs (inf_le_right : U' i ⊓ U' j ≤ U' j) (t j)) :
    ∃ (N : ℕ) (s : LB.Sec M), ∀ j, pa φ (h j) (s.f j) = pa φ (le_pre_top φ) f ^ N * t j := by
  obtain ⟨κ, _, W, c, hW, hWc, hc⟩ := exists_fin_cover M hM
  have hWU : ∀ a, φ ⁻¹ᵁ W a ≤ U' (c a) := fun a => (φ.preimage_mono (hWc a)).trans (h' (c a))
  have ht' : ∀ i j {V : X'.Opens} (hi : V ≤ U' i) (hj : V ≤ U' j), rs hi (t i) =
      pa φ (le_pre_inf (hi.trans (h i)) (hj.trans (h j)))
        (M.g i j : Γ(X, M.U i ⊓ M.U j)) * rs hj (t j) := by
    intro i j V hi hj
    have := congrArg (rs (le_inf hi hj)) (ht i j)
    rwa [map_mul, rs_rs, rs_rs, rs_pa] at this
  choose n x hx using fun a => fun_extend φ f hφ (hW a) le_rfl le_rfl (rs (hWU a) (t (c a)))
  obtain ⟨N, hN⟩ : ∃ N, ∀ a, n a ≤ N := ⟨Finset.univ.sup n, fun a => Finset.le_sup (Finset.mem_univ a)⟩
  let x' : ∀ a, Γ(X, W a) := fun a => rs le_top f ^ (N - n a) * x a
  have hx' : ∀ a {V : X'.Opens} (hV : V ≤ φ ⁻¹ᵁ W a), pa φ hV (x' a) =
      pa φ (le_pre_top φ) f ^ N * rs (hV.trans (hWU a)) (t (c a)) := by
    intro a V hV
    have := congrArg (rs hV) (hx a)
    rw [rs_pa, map_mul, map_pow, rs_pa, rs_rs] at this
    simp only [x']
    rw [map_mul, map_pow, pa_rs, this, ← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel (hN a)]
  clear_value x'
  have hk : ∀ p : κ × κ, ∃ K : ℕ, rs (le_top : W p.1 ⊓ W p.2 ≤ ⊤) f ^ K *
      (rs inf_le_left (x' p.1) - rs (inf_le_inf (hWc p.1) (hWc p.2))
        (M.g (c p.1) (c p.2) : Γ(X, M.U (c p.1) ⊓ M.U (c p.2))) * rs inf_le_right (x' p.2)) = 0 := by
    rintro ⟨a, b⟩
    refine fun_kill φ f hφ (QuasiSeparatedSpace.inter_isCompact _ _ (W a).isOpen (hW a).isCompact
      (W b).isOpen (hW b).isCompact) le_rfl le_rfl _ ?_
    rw [map_sub, map_mul, pa_rs, pa_rs, pa_rs, hx', hx', ht' (c a) (c b) _
      ((φ.preimage_mono inf_le_right).trans (hWU b))]
    ring
  choose k hk using hk
  obtain ⟨K, hK⟩ : ∃ K, ∀ p, k p ≤ K := ⟨Finset.univ.sup k, fun a => Finset.le_sup (Finset.mem_univ a)⟩
  let y : ∀ a, Γ(X, W a) := fun a => rs le_top f ^ K * x' a
  have hy : ∀ a b {V : X.Opens} (ha : V ≤ W a) (hb : V ≤ W b), rs ha (y a) =
      rs (le_inf (ha.trans (hWc a)) (hb.trans (hWc b)))
        (M.g (c a) (c b) : Γ(X, M.U (c a) ⊓ M.U (c b))) * rs hb (y b) := by
    intro a b V ha hb
    have := congrArg (rs (le_inf ha hb)) (pow_mul_zero_mono (hk (a, b)) (hK (a, b)))
    simp only [map_mul, map_pow, map_sub, rs_rs, map_zero] at this
    simp only [y, map_mul, map_pow, rs_rs]
    linear_combination this
  have hg : ∀ j, ∃ z : Γ(X, M.U j), ∀ a, rs (inf_le_left : M.U j ⊓ W a ≤ M.U j) z =
      rs (inf_le_inf le_rfl (hWc a)) (M.g j (c a) : Γ(X, M.U j ⊓ M.U (c a))) *
        rs inf_le_right (y a) := by
    intro j
    refine glue_cover (fun a => M.U j ⊓ W a) (fun a => inf_le_left) (le_iSup_inf _ hc) _
      fun a b => ?_
    simp only [map_mul, rs_rs]
    rw [hy a b _ (inf_le_right.trans inf_le_right), ← _root_.mul_assoc, cocycle_at hM]
  choose z hz using hg
  have hz' : ∀ j a {V : X.Opens} (hj : V ≤ M.U j) (ha : V ≤ W a), rs hj (z j) =
      rs (le_inf hj (ha.trans (hWc a))) (M.g j (c a) : Γ(X, M.U j ⊓ M.U (c a))) * rs ha (y a) := by
    intro j a V hj ha
    have := congrArg (rs (le_inf hj ha)) (hz j a)
    rwa [map_mul, rs_rs, rs_rs, rs_rs] at this
  refine ⟨K + N, ⟨z, fun i j => ?_⟩, fun j => ?_⟩
  · change rs inf_le_left (z i) = (M.g i j : Γ(X, M.U i ⊓ M.U j)) * rs inf_le_right (z j)
    refine eq_of_cover (fun a => M.U i ⊓ M.U j ⊓ W a) (fun a => inf_le_left) (le_iSup_inf _ hc)
      _ _ fun a => ?_
    rw [map_mul, rs_rs, rs_rs, hz' i a _ inf_le_right, hz' j a _ inf_le_right, ← _root_.mul_assoc,
      cocycle_at hM]
  · refine eq_of_cover (fun a => U' j ⊓ φ ⁻¹ᵁ W a) (fun a => inf_le_left)
      (le_iSup_inf _ ?_) _ _ fun a => ?_
    · intro q _
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1
        (hc (TopologicalSpace.Opens.mem_top (φ q)))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, ha⟩
    have hV : U' j ⊓ φ ⁻¹ᵁ W a ≤ φ ⁻¹ᵁ (M.U j ⊓ W a) :=
      le_pre_inf (inf_le_left.trans (h j)) inf_le_right
    have := congrArg (pa φ hV) (hz j a)
    rw [pa_rs, map_mul, pa_rs, pa_rs] at this
    simp only [y] at this
    rw [map_mul, map_pow, pa_rs, hx'] at this
    rw [rs_pa, this, map_mul, map_pow, rs_pa, ht' j (c a) _ (inf_le_right.trans (hWU a))]
    ring

end Calc

theorem pa_linComb_g {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ψ : K → (Z ⟶ X)) (ε : K → ℤ) (h : Z ⟶ Y) (hψ : ∀ k, h ≫ φ k = ψ k) (i j : K → L.ι)
    (e : LB.wchart L ψ i ⊓ LB.wchart L ψ j ≤ h ⁻¹ᵁ (LB.wchart L φ i ⊓ LB.wchart L φ j)) :
    pa h e (LB.lcg L φ ε i j : Γ(Y, LB.wchart L φ i ⊓ LB.wchart L φ j)) =
      (LB.lcg L ψ ε i j : Γ(Z, LB.wchart L ψ i ⊓ LB.wchart L ψ j)) := by
  have : Units.map (pa h e).toMonoidHom (LB.lcg L φ ε i j) = LB.lcg L ψ ε i j := by
    unfold LB.lcg
    rw [map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow]
    congr 1
    exact Units.ext (pa_pa (φ k) h _ e (ψ k) (hψ k) _ _)
  exact congrArg Units.val this

theorem map_mem_span {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M]
    [AddCommGroup M'] [Module R M] [Module R' M'] {σ : R →+* R'} (F : M →ₛₗ[σ] M') {κ : Type}
    (b : κ → M) (s : M) (hs : s ∈ Submodule.span R (Set.range b)) :
    F s ∈ Submodule.span R' (Set.range fun i => F (b i)) := by
  induction hs using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨i, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

theorem pow_smul_mem_of {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M]
    [AddCommGroup M'] [Module R M] [Module R' M'] {σ : R →+* R'} (F : M →ₛₗ[σ] M') (r : R)
    (h₁ : ∀ c : R', ∃ (n : ℕ) (d : R), σ d = σ r ^ n * c)
    (h₂ : ∀ s : M, F s = 0 → ∃ n : ℕ, r ^ n • s = 0) (W : Submodule R M) (s : M)
    (hs : F s ∈ Submodule.span R' (F '' W)) : ∃ N : ℕ, r ^ N • s ∈ W := by
  have key : ∀ t ∈ Submodule.span R' (F '' W), ∃ (N : ℕ), ∃ w ∈ W, F w = σ r ^ N • t := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem x hx => obtain ⟨w, hw, rfl⟩ := hx; exact ⟨0, w, hw, by rw [pow_zero, _root_.one_smul]⟩
    | zero => exact ⟨0, 0, W.zero_mem, by rw [map_zero, smul_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨m, u, hu, eu⟩ := hx
      obtain ⟨n, v, hv, ev⟩ := hy
      refine ⟨m + n, r ^ n • u + r ^ m • v, W.add_mem (W.smul_mem _ hu) (W.smul_mem _ hv), ?_⟩
      rw [map_add, map_smulₛₗ, map_smulₛₗ, eu, ev, map_pow, map_pow, smul_smul, smul_smul,
        ← pow_add, ← pow_add, add_comm n m, smul_add]
    | smul c x _ hx =>
      obtain ⟨m, u, hu, eu⟩ := hx
      obtain ⟨n, d, hd⟩ := h₁ c
      refine ⟨m + n, d • u, W.smul_mem _ hu, ?_⟩
      rw [map_smulₛₗ, eu, hd, smul_smul, smul_smul]
      congr 1
      ring
  obtain ⟨N, w, hw, e⟩ := key _ hs
  obtain ⟨K, hK⟩ := h₂ (r ^ N • s - w) (by rw [map_sub, map_smulₛₗ, map_pow, e, sub_self])
  refine ⟨K + N, ?_⟩
  rw [smul_sub, sub_eq_zero, smul_smul, ← pow_add] at hK
  rw [hK]
  exact W.smul_mem _ hw

section Pull
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' T'' : Over S}

theorem chart_le (h : T' ⟶ T) (j : Fin 1 → L.ι) :
    (LPow A L a T').U j ≤ (h ▷ A).left ⁻¹ᵁ (LPow A L a T).U j :=
  chart_le_res A L (h ▷ A) (whiskerRight_snd h A) a j

omit [GrpObj A] in
theorem whisker_snd_left (h : T' ⟶ T) : (h ▷ A).left ≫ (snd T A).left = (snd T' A).left := by
  rw [← Over.comp_left, whiskerRight_snd]

omit [GrpObj A] in
theorem whisker_fst_left (h : T' ⟶ T) :
    (h ▷ A).left ≫ (fst T A).left = (fst T' A).left ≫ h.left := by
  rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]

theorem chart_ge (h : T' ⟶ T) (j : Fin 1 → L.ι) :
    (h ▷ A).left ⁻¹ᵁ (LPow A L a T).U j ≤ (LPow A L a T').U j := by
  intro y hy
  refine Set.mem_iInter.2 fun i => ?_
  have h1 : ((h ▷ A).left ≫ (snd T A).left) y ∈ (L.U (j i) : Set A.left) := Set.mem_iInter.1 hy i
  rw [whisker_snd_left] at h1
  exact h1

theorem pa_g (h : T' ⟶ T) (i j : Fin 1 → L.ι)
    (e : (LPow A L a T').U i ⊓ (LPow A L a T').U j ≤
      (h ▷ A).left ⁻¹ᵁ ((LPow A L a T).U i ⊓ (LPow A L a T).U j)) :
    pa (h ▷ A).left e ((LPow A L a T).g i j :
      Γ((T ⊗ A).left, (LPow A L a T).U i ⊓ (LPow A L a T).U j)) =
      ((LPow A L a T').g i j : Γ((T' ⊗ A).left, (LPow A L a T').U i ⊓ (LPow A L a T').U j)) := by
  exact pa_linComb_g L (fun _ : Fin 1 => (snd T A).left) (fun _ => (snd T' A).left) (fun _ => a)
    (h ▷ A).left (fun _ => whisker_snd_left A h) i j e

theorem liftHom_eq (W : (T ⊗ A).left.Opens) (r : Γ(T.left, ⊤)) :
    liftHom A W r = pa (fst T A).left (le_pre_top _) r := rfl

theorem pa_liftHom (h : T' ⟶ T) {W : (T ⊗ A).left.Opens} {W' : (T' ⊗ A).left.Opens}
    (e : W' ≤ (h ▷ A).left ⁻¹ᵁ W) (r : Γ(T.left, ⊤)) :
    pa (h ▷ A).left e (liftHom A W r) = liftHom A W' (pa h.left (le_pre_top _) r) := by
  rw [liftHom_eq, liftHom_eq, pa_pa _ _ _ _ _ (whisker_fst_left A h) (le_pre_top _),
    pa_pa _ _ _ _ _ rfl (le_pre_top _)]

def pull (h : T' ⟶ T) :
    SecM A L a T →ₛₗ[pa h.left (V := ⊤) (le_pre_top _)] SecM A L a T' where
  toFun s := ⟨fun j => pa (h ▷ A).left (chart_le A L a h j) (s.1 j), fun i j => by
    have hs : rs inf_le_left (s.1 i) = ((LPow A L a T).g i j :
      Γ((T ⊗ A).left, (LPow A L a T).U i ⊓ (LPow A L a T).U j)) * rs inf_le_right (s.1 j) :=
      s.2 i j
    have e := le_pre_inf (inf_le_left.trans (chart_le A L a h i))
      (inf_le_right.trans (chart_le A L a h j))
    have := congrArg (pa (h ▷ A).left e) hs
    rw [map_mul, pa_rs, pa_rs] at this
    replace this := this.trans (congrArg (· * _) (pa_g A L a h i j e))
    change rs _ _ = _ * rs _ _
    rw [rs_pa, rs_pa]
    exact this⟩
  map_add' s t := by
    ext j
    exact map_add (pa (h ▷ A).left (chart_le A L a h j)) _ _
  map_smul' r s := by
    ext j
    change pa (h ▷ A).left (chart_le A L a h j) (liftHom A _ r * s.1 j) =
      liftHom A _ _ * pa (h ▷ A).left (chart_le A L a h j) (s.1 j)
    rw [map_mul, pa_liftHom]

theorem pull_apply (h : T' ⟶ T) (s : SecM A L a T) (j : Fin 1 → L.ι) :
    (pull A L a h s).1 j = pa (h ▷ A).left (chart_le A L a h j) (s.1 j) := rfl

theorem pull_pull (h : T' ⟶ T) (k : T'' ⟶ T') (s : SecM A L a T) :
    pull A L a k (pull A L a h s) = pull A L a (k ≫ h) s := by
  ext j
  exact pa_pa _ _ _ _ _ (by rw [← Over.comp_left, comp_whiskerRight]) _ _

theorem pull_id (s : SecM A L a T) : pull A L a (𝟙 T) s = s := by
  ext j
  have : ∀ (φ : (T ⊗ A).left ⟶ (T ⊗ A).left) (_ : φ = 𝟙 _) (W : (T ⊗ A).left.Opens)
      (e : W ≤ φ ⁻¹ᵁ W) (x : Γ((T ⊗ A).left, W)), pa φ e x = x := by
    rintro _ rfl W e x
    rw [pa_id]
    exact rs_self _ _
  exact this _ (by rw [id_whiskerRight]; rfl) _ _ _

theorem isPullSec_iff (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) (s' : LB.Sec (LPow A L a T')) :
    IsPullSec A L a (h ▷ A) (whiskerRight_snd h A) s s' ↔
      SecM.ofSec A s' = pull A L a h (SecM.ofSec A s) :=
  ⟨fun H => Subtype.ext (funext H), fun H j => congrFun (congrArg Subtype.val H) j⟩

omit [GrpObj A] in
theorem isPullback_whisker (h : T' ⟶ T) :
    IsPullback (h ▷ A).left (fst T' A).left (fst T A).left h.left := by
  have h1 : IsPullback (snd T A).left (fst T A).left A.hom T.hom :=
    (IsPullback.of_hasPullback T.hom A.hom).flip
  have h2 : IsPullback (snd T' A).left (fst T' A).left A.hom T'.hom :=
    (IsPullback.of_hasPullback T'.hom A.hom).flip
  refine IsPullback.of_right ?_ (whisker_fst_left A h) h1
  rw [whisker_snd_left, Over.w h]
  exact h2

omit [GrpObj A] in
theorem whisker_open (h : T' ⟶ T) [IsOpenImmersion h.left] : IsOpenImmersion (h ▷ A).left :=
  MorphismProperty.of_isPullback (isPullback_whisker A h).flip ‹_›

omit [GrpObj A] in
theorem whisker_range (h : T' ⟶ T) [IsOpenImmersion h.left] [IsOpenImmersion (h ▷ A).left]
    (r : Γ(T.left, ⊤)) (hr : h.left.opensRange = T.left.basicOpen r) :
    (h ▷ A).left.opensRange =
      (T ⊗ A).left.basicOpen (pa (fst T A).left (V := ⊤) (le_pre_top _) r) := by
  have e : (T ⊗ A).left.basicOpen (pa (fst T A).left (V := ⊤) (le_pre_top _) r) =
      (fst T A).left ⁻¹ᵁ T.left.basicOpen r := by
    have := Scheme.basicOpen_appLE (fst T A).left ⊤ ⊤ (le_pre_top _) r
    rw [top_inf_eq] at this
    exact this
  rw [e, ← hr]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨(fst T' A).left y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, whisker_fst_left]
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback (isPullback_whisker A h) x y hy.symm
    exact ⟨z, hz⟩

omit [GrpObj A] in
theorem qcqs [IsProper A.hom] [IsAffine T.left] :
    CompactSpace (T ⊗ A).left ∧ QuasiSeparatedSpace (T ⊗ A).left := by
  have : IsProper (fst T A).left := inferInstanceAs (IsProper (pullback.fst T.hom A.hom))
  exact ⟨QuasiCompact.compactSpace_of_compactSpace (fst T A).left,
    quasiSeparatedSpace_of_quasiSeparated (fst T A).left⟩

theorem pull_kill [IsProper A.hom] [IsAffine T.left] (hL : L.IsLB) (h : T' ⟶ T)
    [IsOpenImmersion h.left] (r : Γ(T.left, ⊤)) (hr : h.left.opensRange = T.left.basicOpen r)
    (s : SecM A L a T) (hs : pull A L a h s = 0) : ∃ N : ℕ, r ^ N • s = 0 := by
  have := whisker_open A h
  obtain ⟨_, _⟩ := qcqs A (T := T)
  obtain ⟨N, hN⟩ := sec_kill (h ▷ A).left _ (whisker_range A h r hr) (LPow A L a T)
    (LB.isLB_linComb hL _ _) (LPow A L a T').U (chart_le A L a h) (chart_ge A L a h)
    (SecM.toSec A s) (fun j => congrFun (congrArg Subtype.val hs) j)
  refine ⟨N, Subtype.ext (funext fun j => ?_)⟩
  have := hN j
  rw [rs_pa] at this
  change liftHom A _ (r ^ N) * s.1 j = 0
  rw [map_pow]
  exact this

theorem pull_extend [IsProper A.hom] [IsAffine T.left] (hL : L.IsLB) (h : T' ⟶ T)
    [IsOpenImmersion h.left] (r : Γ(T.left, ⊤)) (hr : h.left.opensRange = T.left.basicOpen r)
    (t : SecM A L a T') : ∃ (N : ℕ) (s : SecM A L a T),
      pull A L a h s = pa h.left (V := ⊤) (le_pre_top _) r ^ N • t := by
  have := whisker_open A h
  obtain ⟨_, _⟩ := qcqs A (T := T)
  obtain ⟨N, s, hN⟩ := sec_extend (h ▷ A).left _ (whisker_range A h r hr) (LPow A L a T)
    (LB.isLB_linComb hL _ _) (LPow A L a T').U (chart_le A L a h) (chart_ge A L a h)
    t.1 (fun i j => (t.2 i j).trans (congrArg (· * _) (pa_g A L a h i j _).symm))
  refine ⟨N, SecM.ofSec A s, Subtype.ext (funext fun j => ?_)⟩
  refine (hN j).trans ?_
  change _ = liftHom A _ (_ ^ N) * t.1 j
  rw [map_pow, ← pa_liftHom A h (le_pre_top _)]
  rfl

end Pull

section Span
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' T'' : Over S}

theorem pow_smul_mem [IsProper A.hom] [IsAffine T.left] (hL : L.IsLB) (h : T' ⟶ T)
    [IsOpenImmersion h.left] (r : Γ(T.left, ⊤)) (hr : h.left.opensRange = T.left.basicOpen r)
    (W : Submodule Γ(T.left, ⊤) (SecM A L a T)) (s : SecM A L a T)
    (hs : pull A L a h s ∈ Submodule.span Γ(T'.left, ⊤) (pull A L a h '' W)) :
    ∃ N : ℕ, r ^ N • s ∈ W :=
  pow_smul_mem_of (pull A L a h) r
    (fun_extend h.left r hr (isAffineOpen_top T.left) (W' := ⊤) (le_pre_top _) le_top)
    (pull_kill A L a hL h r hr) W s hs

theorem exists_lift (h : T' ⟶ T) (V : T.left.Opens) (hV : ∀ x, h.left x ∈ V) :
    ∃ k : T' ⟶ overRes V, k ≫ overResι V = h := by
  have hr : Set.range h.left ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨_, hV x⟩, rfl⟩
  refine ⟨Over.homMk (IsOpenImmersion.lift V.ι h.left hr) ?_, ?_⟩
  · change _ ≫ V.ι ≫ T.hom = T'.hom
    rw [IsOpenImmersion.lift_fac_assoc, Over.w h]
  · ext1
    exact IsOpenImmersion.lift_fac V.ι h.left hr

instance isOpenImmersion_overResι (V : T.left.Opens) : IsOpenImmersion (overResι V).left :=
  inferInstanceAs (IsOpenImmersion V.ι)

theorem overResι_range (V : T.left.Opens) : (overResι V).left.opensRange = V :=
  Scheme.Opens.opensRange_ι V

theorem isUnit_pa (h : T' ⟶ T) (r : Γ(T.left, ⊤)) (hr : ∀ x, h.left x ∈ T.left.basicOpen r) :
    IsUnit (pa h.left (V := ⊤) (le_pre_top _) r) := by
  have e := Scheme.basicOpen_appLE h.left ⊤ ⊤ (le_pre_top _) r
  refine T'.left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => ?_
  have : x ∈ T'.left.basicOpen (pa h.left (V := ⊤) (le_pre_top _) r) := by
    change x ∈ T'.left.basicOpen (h.left.appLE ⊤ ⊤ (le_pre_top _) r)
    rw [e]
    exact ⟨trivial, hr x⟩
  exact (T'.left.mem_basicOpen _ x hx).1 this

theorem span_of_retract (e : T'' ⟶ T') (e' : T' ⟶ T'') (he : e' ≫ e = 𝟙 T') (k : T'' ⟶ T)
    {κ : Type} (b : κ → SecM A L a T)
    (hb : Submodule.span Γ(T''.left, ⊤) (Set.range fun i => pull A L a k (b i)) = ⊤) :
    Submodule.span Γ(T'.left, ⊤) (Set.range fun i => pull A L a (e' ≫ k) (b i)) = ⊤ := by
  refine eq_top_iff.2 fun σ _ => ?_
  have := map_mem_span (pull A L a e') _ (pull A L a e σ) (hb.ge trivial)
  rw [pull_pull, he, pull_id] at this
  simp only [pull_pull] at this
  exact this

theorem exists_spec_retract {V : S.Opens} [IsAffine T'.left]
    (g : T' ⟶ overRes (T := baseOver S) V) :
    ∃ (R : Type) (_ : CommRing R)
      (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver S) V).left)
      (e : baseAt t ⟶ T') (e' : T' ⟶ baseAt t), e' ≫ e = 𝟙 T' ∧ e' ≫ homAt t = g := by
  let t : Spec (CommRingCat.of Γ(T'.left, ⊤)) ⟶ (overRes (T := baseOver S) V).left :=
    T'.left.isoSpec.inv ≫ g.left
  let e : baseAt t ⟶ T' := Over.homMk T'.left.isoSpec.inv (by
    change T'.left.isoSpec.inv ≫ T'.hom = (T'.left.isoSpec.inv ≫ g.left) ≫ _
    rw [Category.assoc, Over.w g])
  let e' : T' ⟶ baseAt t := Over.homMk T'.left.isoSpec.hom (by
    change T'.left.isoSpec.hom ≫ (T'.left.isoSpec.inv ≫ g.left) ≫ _ = T'.hom
    rw [Category.assoc, Over.w g, Iso.hom_inv_id_assoc])
  refine ⟨_, _, t, e, e', ?_, ?_⟩
  · ext1
    exact T'.left.isoSpec.hom_inv_id
  · ext1
    exact T'.left.isoSpec.hom_inv_id_assoc _

end Span

theorem local_span (H : SecBaseChangeSt) (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S)
    (n : ℕ) (hn : 1 ≤ n) (p : S) : ∃ V : S.Opens, p ∈ V ∧
      ∃ b : Fin (n ^ P.g) → SecM P.A P.L n (overRes (T := baseOver S) V),
        ∀ (T' : Over S) [IsAffine T'.left] (g : T' ⟶ overRes (T := baseOver S) V),
          Submodule.span Γ(T'.left, ⊤) (Set.range fun i => pull P.A P.L n g (b i)) = ⊤ := by
  obtain ⟨V, hp, b, hb⟩ := H S P n hn p
  refine ⟨V, hp, fun i => SecM.ofSec P.A (b i), fun T' _ g => ?_⟩
  obtain ⟨R, _, t, e, e', h1, rfl⟩ := exists_spec_retract g
  exact span_of_retract P.A P.L n e e' h1 (homAt t) _ (hb R t
    (fun i => SecM.toSec P.A (pull P.A P.L n (homAt t) (SecM.ofSec P.A (b i))))
    (fun i => (isPullSec_iff P.A P.L n _ _ _).2 rfl)).2

end GlobalTheory.SecAff

open GlobalTheory.SecAff in

theorem GlobalTheory.exists_sections_span_affine :
    SecBaseChangeSt → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → ∀ U : S.Opens, IsAffineOpen U → ∃ (m : ℕ) (b : Fin (m + 1) → LB.Sec (LPow P.A P.L n (overRes (T := baseOver S) U))), ∀ (T' : Over S) [IsAffine T'.left] (h : T' ⟶ overRes (T := baseOver S) U) (b' : Fin (m + 1) → LB.Sec (LPow P.A P.L n T')), (∀ i, IsPullSec P.A P.L n (h ▷ P.A) (whiskerRight_snd h P.A) (b i) (b' i)) → Submodule.span Γ(T'.left, ⊤) (Set.range fun i => (SecM.ofSec P.A (b' i) : SecM P.A P.L n T')) = ⊤ := by
  intro H S _ P n hn U hU
  have := P.isAb.proper
  generalize hT : overRes (T := baseOver S) U = T
  have : IsAffine T.left := by subst hT; exact hU
  clear hT hU

  have loc : ∀ p : T.left, ∃ r : Γ(T.left, ⊤), p ∈ T.left.basicOpen r ∧
      ∃ s : Fin (n ^ P.g) → SecM P.A P.L n T, ∀ (T' : Over S) [IsAffine T'.left] (k : T' ⟶ T),
        (∀ x, k.left x ∈ T.left.basicOpen r) →
        Submodule.span Γ(T'.left, ⊤) (Set.range fun i => pull P.A P.L n k (s i)) = ⊤ := by
    intro p
    obtain ⟨V, hp, b, hb⟩ := local_span H S P n hn (T.hom p)
    obtain ⟨r, hr, hpr⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := T.hom ⁻¹ᵁ V)
      ⟨p, hp⟩ trivial
    obtain ⟨g, -⟩ := exists_lift (T := baseOver S) (T' := overRes (T.left.basicOpen r))
      (Over.homMk (overRes (T.left.basicOpen r)).hom (Category.comp_id _)) V
      (fun x => hr x.2)
    choose N s hs using fun i => pull_extend P.A P.L n P.isLB (overResι (T.left.basicOpen r)) r
      (overResι_range _) (pull P.A P.L n g (b i))
    refine ⟨r, hpr, s, fun T' _ k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_lift k _ hk
    refine eq_top_iff.2 ((hb T' (k' ≫ g)).ge.trans (Submodule.span_le.2 ?_))
    rintro _ ⟨i, rfl⟩
    have hu := ((isUnit_pa (overResι (T.left.basicOpen r)) r (fun x => x.2)).pow (N i)).map
      (pa k'.left (V := ⊤) (le_pre_top _))
    refine (Submodule.smul_mem_iff_of_isUnit _ hu).1 (Submodule.subset_span ⟨i, ?_⟩)
    simp only
    rw [← pull_pull, hs, map_smulₛₗ, pull_pull]
  choose r hr s hs using loc
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover
    (fun p => (T.left.basicOpen (r p) : Set T.left)) (fun p => (T.left.basicOpen (r p)).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hr x⟩)
  let c : Option (I × Fin (n ^ P.g)) → SecM P.A P.L n T := fun o => o.elim 0 fun q => s q.1 q.2
  let e : Option (I × Fin (n ^ P.g)) ≃ Fin (Fintype.card (I × Fin (n ^ P.g)) + 1) :=
    Fintype.equivFinOfCardEq Fintype.card_option
  refine ⟨_, fun i => SecM.toSec P.A (c (e.symm i)), fun T' _ h b' hb' => ?_⟩
  set W := Submodule.span Γ(T'.left, ⊤)
    (Set.range fun i => (SecM.ofSec P.A (b' i) : SecM P.A P.L n T'))
  have hW : ∀ (p : I) i, pull P.A P.L n h (s p i) ∈ W := by
    intro p i
    refine Submodule.subset_span ⟨e (some (p, i)), ?_⟩
    refine ((isPullSec_iff P.A P.L n _ _ _).1 (hb' _)).trans ?_
    simp only [Equiv.symm_apply_apply]
    rfl
  let r' : I → Γ(T'.left, ⊤) := fun p => pa h.left (V := ⊤) (le_pre_top _) (r p)
  have hb : ∀ p x, x ∈ T'.left.basicOpen (r' p) ↔ h.left x ∈ T.left.basicOpen (r p) := by
    intro p x
    change x ∈ T'.left.basicOpen (h.left.appLE ⊤ ⊤ (le_pre_top _) (r p)) ↔ _
    rw [Scheme.basicOpen_appLE]
    exact ⟨fun H => H.2, fun H => ⟨trivial, H⟩⟩
  have hspan : Ideal.span (Set.range r') = ⊤ := by
    rw [← (isAffineOpen_top T'.left).iSup_basicOpen_eq_self_iff]
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨p, hp, hx⟩ := Set.mem_iUnion₂.1 (hI (Set.mem_univ (h.left x)))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨r' ⟨p, hp⟩, ⟨_, rfl⟩⟩, (hb _ _).2 hx⟩
  refine eq_top_iff.2 fun σ _ => ?_
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem W _ hspan σ ?_
  rintro ⟨_, p, rfl⟩
  have : IsAffine (overRes (T'.left.basicOpen (r' p))).left :=
    (isAffineOpen_top T'.left).basicOpen (r' p)
  refine pow_smul_mem P.A P.L n P.isLB (overResι (T'.left.basicOpen (r' p))) (r' p)
    (overResι_range _) W σ ?_
  refine ((hs p _ (overResι (T'.left.basicOpen (r' p)) ≫ h)
    (fun x => (hb p x.1).1 x.2)).ge.trans (Submodule.span_mono ?_)) trivial
  rintro _ ⟨i, rfl⟩
  exact ⟨_, hW p i, pull_pull _ _ _ _ _ _⟩
