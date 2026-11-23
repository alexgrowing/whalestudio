import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.StepAtlas

section Lin

variable {R R' N N' : Type} [CommRing R] [CommRing R'] [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R' N']
  {m k r : ℕ}

def blk (hj : k + r + 1 ≤ m) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (u : Fin m → N) : Fin m → N := fun i =>
  if h : k ≤ (i : ℕ) ∧ (i : ℕ) < k + r + 1 then ∑ l : Fin (r + 1), P l ⟨i - k, by omega⟩ • u ⟨k + l, by omega⟩ else u i

theorem blk_add (hj : k + r + 1 ≤ m) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (u : Fin m → N) (i : Fin (r + 1)) :
    blk hj P u ⟨k + i, by omega⟩ = ∑ l : Fin (r + 1), P l i • u ⟨k + l, by omega⟩ := by
  have h : k ≤ k + (i : ℕ) ∧ k + (i : ℕ) < k + r + 1 := by omega
  simp only [blk, dif_pos h, Nat.add_sub_cancel_left]

theorem map_blk (hj : k + r + 1 ≤ m) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (u : Fin m → N) {φ : R →+* R'}
    (g : N →ₛₗ[φ] N') (i : Fin m) : g (blk hj P u i) = blk hj (P.map φ) (fun j => g (u j)) i := by
  unfold blk
  split_ifs
  · simp only [map_sum, map_smulₛₗ, Matrix.map_apply]
  · rfl

theorem blk_blk (hj : k + r + 1 ≤ m) (P Q : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (u : Fin m → N) :
    blk hj Q (blk hj P u) = blk hj (P * Q) u := by
  funext i
  by_cases h : k ≤ (i : ℕ) ∧ (i : ℕ) < k + r + 1
  · rw [blk, dif_pos h]
    conv_rhs => rw [blk, dif_pos h]
    simp only [blk_add, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  · simp only [blk, dif_neg h]

theorem blk_one (hj : k + r + 1 ≤ m) (u : Fin m → N) : blk hj (1 : Matrix _ _ R) u = u := by
  funext i
  by_cases h : k ≤ (i : ℕ) ∧ (i : ℕ) < k + r + 1
  · rw [blk, dif_pos h]
    simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 1
    ext
    simp only
    omega
  · simp only [blk, dif_neg h]

theorem initSpan_blk_le (hj : k + r + 1 ≤ m) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (u : Fin m → N) {e : ℕ}
    (he : e ≤ k ∨ k + r + 1 ≤ e) : initSpan R (blk hj P u) e ≤ initSpan R u e := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, hi, rfl⟩
  have hi' : (i : ℕ) < e := hi
  by_cases h : k ≤ (i : ℕ) ∧ (i : ℕ) < k + r + 1
  · rw [blk, dif_pos h]
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
    show k + (l : ℕ) < e
    omega
  · rw [blk, dif_neg h]
    exact Submodule.subset_span ⟨i, hi, rfl⟩

theorem initSpan_top (u : Fin m → N) : initSpan R u m = Submodule.span R (Set.range u) := by
  rw [initSpan, ← Set.image_univ]
  congr 2
  exact Set.eq_univ_of_forall fun j => j.2

theorem initSpan_blk (hj : k + r + 1 ≤ m) {P : Matrix (Fin (r + 1)) (Fin (r + 1)) R} (hP : IsUnit P) (u : Fin m → N)
    {e : ℕ} (he : e ≤ k ∨ k + r + 1 ≤ e) : initSpan R (blk hj P u) e = initSpan R u e := by
  obtain ⟨P, rfl⟩ := hP
  refine le_antisymm (initSpan_blk_le hj _ u he) ?_
  have := initSpan_blk_le hj (P⁻¹).val (blk hj P.val u) he
  rwa [blk_blk, Units.mul_inv, blk_one] at this

theorem linearIndependent_blk (hj : k + r + 1 ≤ m) {P : Matrix (Fin (r + 1)) (Fin (r + 1)) R} (hP : IsUnit P)
    {u : Fin m → N} (hu : LinearIndependent R u) : LinearIndependent R (blk hj P u) := by
  obtain ⟨P, rfl⟩ := hP
  have key : ∀ {N : Type} [AddCommGroup N] [Module R N] (Q : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (v : Fin m → N),
      Fintype.linearCombination R v ∘ blk hj Q (Pi.basisFun R (Fin m)) = blk hj Q v := fun Q v => by
    funext i
    rw [Function.comp_apply, map_blk]
    simp [Fintype.linearCombination_apply_single]
  have h1 : LinearIndependent R (blk hj P.val (Pi.basisFun R (Fin m))) := by
    refine LinearIndependent.of_comp (Fintype.linearCombination R (blk hj (P⁻¹).val (Pi.basisFun R (Fin m)))) ?_
    rw [key, blk_blk, Units.inv_mul, blk_one]
    exact (Pi.basisFun R (Fin m)).linearIndependent
  rw [← key]
  exact h1.map' _ (LinearMap.ker_eq_bot'.2 fun a ha => funext (Fintype.linearIndependent_iff.1 hu a ha))

theorem not_mem_initSpan [Nontrivial R] {u : Fin m → N} (hu : LinearIndependent R u) (i : Fin m) :
    u i ∉ initSpan R u i := hu.notMem_span_image (lt_irrefl (i : ℕ))

theorem initSpan_succ_le {u : Fin m → N} {W : Submodule R N} (i : Fin m) (h : initSpan R u i ≤ W) (hi : u i ∈ W) :
    initSpan R u (i + 1) ≤ W := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨j, hj, rfl⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h' | h'
  · exact h (Submodule.subset_span ⟨j, h', rfl⟩)
  · rwa [Fin.ext h']

theorem exists_sub_mem (hj : k + r + 1 ≤ m) (u : Fin m → N) {w : N} (hw : w ∈ initSpan R u (k + r + 1)) :
    ∃ v : Fin (r + 1) → R, w - ∑ l : Fin (r + 1), v l • u ⟨k + l, by omega⟩ ∈ initSpan R u k := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj', rfl⟩ := hx
    have hj'' : (j : ℕ) < k + r + 1 := hj'
    by_cases h : (j : ℕ) < k
    · have : u j ∈ initSpan R u k := Submodule.subset_span ⟨j, h, rfl⟩
      exact ⟨0, by simpa using this⟩
    · refine ⟨Pi.single ⟨j - k, by omega⟩ 1, ?_⟩
      simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      have : (⟨k + (j - k), by omega⟩ : Fin m) = j := Fin.ext (by simp only; omega)
      rw [this, sub_self]
      exact Submodule.zero_mem _
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    convert Submodule.add_mem _ ha hb using 1
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  | smul s x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨s • a, ?_⟩
    convert Submodule.smul_mem _ s ha using 1
    simp only [Pi.smul_apply, smul_eq_mul, smul_sub, Finset.smul_sum, smul_smul]

theorem mem_initSpan_inl {n : ℕ} (b : Module.Basis (Fin k ⊕ Fin n) R N) (v : N) :
    v ∈ initSpan R (fun i : Fin k => b (.inl i)) k ↔ ∀ j, b.repr v (.inr j) = 0 := by
  rw [initSpan_top, show Set.range (fun i : Fin k => b (.inl i)) = b '' Set.range Sum.inl from by
    rw [← Set.range_comp]; rfl, b.mem_span_image]
  refine ⟨fun h j => ?_, fun h => ?_⟩
  · by_contra h'
    obtain ⟨i, hi⟩ := h (Finsupp.mem_support_iff.2 h')
    cases hi
  · rintro (i | j) hi
    · exact ⟨i, rfl⟩
    · exact absurd (h j) (Finsupp.mem_support_iff.1 hi)

end Lin

section Carry

variable {Z Z' : Scheme.{0}} {C : Coc Z} {f : Z' ⟶ Z} {L : C.Line f} {S : Type} [CommRing S] {w : Sp S ⟶ Z'}

theorem carries_smul {α : C.A} {h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α} {ξ : Fin (C.n α) → S} (hξ : L.Carries w α h ξ) (s : Sˣ) :
    L.Carries w α h ((s : S) • ξ) := fun β hw => by
  obtain ⟨u, hu⟩ := hξ β hw
  refine ⟨s * u, ?_⟩
  rw [Matrix.mulVec_smul, hu]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Units.val_mul, mul_assoc]

theorem carries_tr {α β : C.A} {hα : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α} (hβ : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B β) {ξ : Fin (C.n β) → S}
    (hξ : L.Carries w α hα ((C.tr α β (w ≫ f) hα hβ).mulVec ξ)) : L.Carries w β hβ ξ := fun γ hw => by
  obtain ⟨u, hu⟩ := hξ γ hw
  rw [Matrix.mulVec_mulVec, Coc.tr_mul] at hu
  exact ⟨u, hu⟩

theorem exists_chart [IsLocalRing S] (L : C.Line f) (w : Sp S ⟶ Z') : ∃ β, ⊤ ≤ w ⁻¹ᵁ L.B β :=
  FlagMod.exists_chart_of_isLocalRing (eq_top_iff.2 fun x _ => by
    obtain ⟨β, hβ⟩ := L.cover x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨β, hβ⟩) w

end Carry

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F}
  {M : Model Xo c V.subtype} {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ}
  {A : Atlas M π ty} {σ : E →+* ℂ} {k r : ℕ} {K : Type} [Field K]

theorem bc_bc {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T) (u : Vecs Dw M.t R) :
    (u.bc φ).bc ψ = u.bc (ψ.comp φ) := by
  funext τ i
  rw [Vecs.bc, Vecs.bc, Vecs.bc, FlagMod.dualMap_comp, ← spMap_comp', Category.assoc]

def crdL {m : ℕ} {U : X.Opens} {hU : IsAffineOpen U}
    (b : Module.Basis (Fin k ⊕ Fin m) Γ(X, U) (TanM (tau hU ≫ π) M.t.G)) {S : Type} [CommRing S] (z : Sp S ⟶ X)
    (h : ⊤ ≤ z ⁻¹ᵁ U) : TanM (z ≫ π) M.t.G →ₗ[S] (Fin m → S) :=
  LinearMap.pi fun j => (basAt b z h).coord (.inr j)

theorem crd_eq {m : ℕ} {U : X.Opens} {hU : IsAffineOpen U}
    (b : Module.Basis (Fin k ⊕ Fin m) Γ(X, U) (TanM (tau hU ≫ π) M.t.G)) {S : Type} [CommRing S] (z : Sp S ⟶ X)
    (h : ⊤ ≤ z ⁻¹ᵁ U) (v : TanM (z ≫ π) M.t.G) : crd b z h v = crdL b z h v := rfl

theorem crdL_eq_zero_iff (D : Adapted A σ k) {z : Sp K ⟶ X} {u : TVecs Dw M.t (z ≫ π)} (hu : A.FlagAt z (up u))
    (α : D.C.A) (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α) (v : TanM (z ≫ π) M.t.G) :
    crdL (D.b α) z h v = 0 ↔ v ∈ initSpan K (u σ) k := by
  rw [D.int α K z h u hu k le_rfl, mem_initSpan_inl]
  exact funext_iff

theorem linearIndependent_of_flagAt {z : Sp K ⟶ X} {u : TVecs Dw M.t (z ≫ π)} (hu : A.FlagAt z (up u)) (τ : E →+* ℂ) :
    LinearIndependent K (u τ) := by
  obtain ⟨a, φ, -, hf, -⟩ := hu
  exact ((isFrame_up_iff _ _).1 hf τ).1

def Good (D : Adapted A σ k) (hk : k < Dw.mult σ) {X' : Scheme.{0}} {f : X' ⟶ X} (L : D.C.Line f) (w : Sp K ⟶ X')
    (u : TVecs Dw M.t ((w ≫ f) ≫ π)) : Prop :=
  A.FlagAt (w ≫ f) (up u) ∧ ∀ α h, L.Carries w α h (crd (D.b α) (w ≫ f) h (u σ ⟨k, hk⟩))

variable {D : Adapted A σ k} {hk : k < Dw.mult σ} {X' : Scheme.{0}} {f : X' ⟶ X} {L : D.C.Line f} {w : Sp K ⟶ X'}
  {u u' : TVecs Dw M.t ((w ≫ f) ≫ π)} {ty' : (E →+* ℂ) → Finset ℕ}

theorem good_of_one (hu : A.FlagAt (w ≫ f) (up u)) {α : D.C.A} {h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ D.C.B α}
    (hc : L.Carries w α h (crd (D.b α) (w ≫ f) h (u σ ⟨k, hk⟩))) : Good D hk L w u :=
  ⟨hu, fun β hβ => carries_tr (hα := h) hβ (by rwa [D.coord])⟩

theorem Good.le (h : Good D hk L w u) (h' : Good D hk L w u') (h1 : ty' σ = insert (k + 1) (ty σ))
    (h2 : ∀ σ', σ' ≠ σ → ty' σ' = ty σ') : ∀ τ, ∀ j ∈ ty' τ, initSpan K (u' τ) j ≤ initSpan K (u τ) j := by
  intro τ j hj
  by_cases hτ : τ = σ
  swap
  · exact (h'.1.initSpan_eq h.1 τ (h2 τ hτ ▸ hj)).le
  subst hτ
  rw [h1, Finset.mem_insert] at hj
  rcases hj with rfl | hj
  swap
  · exact (h'.1.initSpan_eq h.1 τ hj).le
  obtain ⟨β, hβ⟩ := exists_chart L w
  have hα := le_preimage_map f (L.le β) hβ
  obtain ⟨s, hs⟩ := h.2 _ hα β hβ
  obtain ⟨s', hs'⟩ := h'.2 _ hα β hβ
  rw [Coc.tr_self, Matrix.one_mulVec, crd_eq] at hs hs'
  have hle := FlagMod.initSpan_mono (R := K) (u τ) (Nat.le_succ k)
  refine initSpan_succ_le ⟨k, hk⟩ (fun v hv => hle ?_) ?_
  · exact (crdL_eq_zero_iff D h.1 _ hα v).1 ((crdL_eq_zero_iff D h'.1 _ hα v).2 hv)
  · have : u' τ ⟨k, hk⟩ - ((s' * s⁻¹ : Kˣ) : K) • u τ ⟨k, hk⟩ ∈ initSpan K (u τ) k := by
      rw [← crdL_eq_zero_iff D h.1 _ hα, map_sub, map_smul, hs, hs']
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Units.val_mul, Pi.zero_apply, mul_assoc,
        Units.inv_mul_cancel_left, sub_self]
    have h3 : u τ ⟨k, hk⟩ ∈ initSpan K (u τ) (k + 1) := Submodule.subset_span ⟨_, Nat.lt_succ_self k, rfl⟩
    simpa using Submodule.add_mem _ (hle this) (Submodule.smul_mem _ ((s' * s⁻¹ : Kˣ) : K) h3)

theorem Good.of_le (h : Good D hk L w u) {a : A.ch.ι} {φ : A.ch.R a →+* K} (e : spMap φ ≫ A.ch.χ a = w ≫ f)
    (hf : LocM.IsFrame M.t (φ.comp (A.alg a)) ((w ≫ f) ≫ π) (up u')) (h1 : ty' σ = insert (k + 1) (ty σ))
    (h2 : ∀ σ', σ' ≠ σ → ty' σ' = ty σ') (hle : ∀ τ, ∀ j ∈ ty' τ, initSpan K (u' τ) j ≤ initSpan K (u τ) j) :
    Good D hk L w u' := by
  obtain ⟨u₀, h₀⟩ := A.exists_up_fr e
  have hsub : ∀ τ, ∀ j ∈ ty τ, j ∈ ty' τ := fun τ j hj => by
    by_cases hτ : τ = σ
    · subst hτ
      rw [h1]
      exact Finset.mem_insert_of_mem hj
    · rwa [h2 τ hτ]
  have hi := linearIndependent_of_flagAt h.1
  have hF : A.FlagAt (w ≫ f) (up u') := (A.flagAt_iff e h₀ u').2 ⟨hf, fun τ j hj =>
    (initSpan_eq_of_le (hi τ) ((isFrame_up_iff _ _).1 hf τ).1 (hle τ j (hsub τ j hj))).trans
      (((A.flagAt_iff e h₀ u).1 h.1).2 τ j hj)⟩
  refine ⟨hF, fun α hα => ?_⟩
  have h3 : u' σ ⟨k, hk⟩ ∈ initSpan K (u' σ) (k + 1) := Submodule.subset_span ⟨_, Nat.lt_succ_self k, rfl⟩
  obtain ⟨s, hs, -⟩ := FlagMod.existsUnique_sub_mem_initSpan (hi σ) ⟨k, hk⟩
    (hle σ (k + 1) (h1 ▸ Finset.mem_insert_self _ _) h3)
  have hs' := (crdL_eq_zero_iff D h.1 α hα _).2 hs
  rw [map_sub, map_smul, sub_eq_zero] at hs'
  have h0 : s ≠ 0 := by
    rintro rfl
    rw [zero_smul, crdL_eq_zero_iff D hF] at hs'
    exact not_mem_initSpan (linearIndependent_of_flagAt hF σ) ⟨k, hk⟩ hs'
  rw [crd_eq, hs']
  exact carries_smul (h.2 α hα) (Units.mk0 s h0)

open Classical in

def chg (hj : k + r + 1 ≤ Dw.mult σ) {S : Type} [CommRing S] (P : Matrix (Fin (r + 1)) (Fin (r + 1)) S)
    {x : Sp S ⟶ M.X} (u : TVecs Dw M.t x) : TVecs Dw M.t x := Function.update u σ (blk hj P (u σ))

theorem chg_self (hj : k + r + 1 ≤ Dw.mult σ) {S : Type} [CommRing S] (P : Matrix (Fin (r + 1)) (Fin (r + 1)) S)
    {x : Sp S ⟶ M.X} (u : TVecs Dw M.t x) : chg hj P u σ = blk hj P (u σ) := by
  classical
  unfold chg
  convert Function.update_self σ _ u

theorem chg_ne (hj : k + r + 1 ≤ Dw.mult σ) {S : Type} [CommRing S] (P : Matrix (Fin (r + 1)) (Fin (r + 1)) S)
    {x : Sp S ⟶ M.X} (u : TVecs Dw M.t x) {τ : E →+* ℂ} (h : τ ≠ σ) : chg hj P u τ = u τ := by
  classical
  unfold chg
  convert Function.update_of_ne h _ u

theorem isFrame_chg (hj : k + r + 1 ≤ Dw.mult σ) {S : Type} [CommRing S] {P : Matrix (Fin (r + 1)) (Fin (r + 1)) S}
    (hP : IsUnit P) {x : Sp S ⟶ M.X} {u : TVecs Dw M.t x} {g : c.F →+* S} (hu : LocM.IsFrame M.t g x (up u)) :
    LocM.IsFrame M.t g x (up (chg hj P u)) := by
  rw [isFrame_up_iff] at hu ⊢
  intro τ
  by_cases hτ : τ = σ
  · subst hτ
    rw [chg_self, ← initSpan_top, initSpan_blk hj hP _ (Or.inr hj), initSpan_top]
    exact ⟨linearIndependent_blk hj hP (hu τ).1, (hu τ).2⟩
  · rw [chg_ne hj P u hτ]
    exact hu τ

theorem tanPull_chg (hj : k + r + 1 ≤ Dw.mult σ) {S S' : Type} [CommRing S] [CommRing S']
    (P : Matrix (Fin (r + 1)) (Fin (r + 1)) S) (φ : S →+* S') {x : Sp S ⟶ M.X} {x' : Sp S' ⟶ M.X}
    (e : spMap φ ≫ x = x') (u : TVecs Dw M.t x) :
    (fun τ i => tanPull φ e (chg hj P u τ i)) = chg hj (P.map φ) (fun τ i => tanPull φ e (u τ i)) := by
  funext τ i
  by_cases hτ : τ = σ
  · subst hτ
    rw [chg_self, chg_self, map_blk]
  · rw [chg_ne hj _ _ hτ, chg_ne hj _ _ hτ]

theorem flagAt_chg (hj : k + r + 1 ≤ Dw.mult σ) (hty : ∀ e ∈ ty σ, e ≤ k ∨ k + r + 1 ≤ e)
    {P : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hP : IsUnit P) {z : Sp K ⟶ X} {u : TVecs Dw M.t (z ≫ π)}
    (hu : A.FlagAt z (up u)) : A.FlagAt z (up (chg hj P u)) := by
  obtain ⟨a, φ, e, -⟩ := id hu
  obtain ⟨u₀, h₀⟩ := A.exists_up_fr e
  obtain ⟨h1, h2⟩ := (A.flagAt_iff e h₀ u).1 hu
  refine (A.flagAt_iff e h₀ _).2 ⟨isFrame_chg hj hP h1, fun τ j hj' => Eq.trans ?_ (h2 τ j hj')⟩
  by_cases hτ : τ = σ
  · subst hτ
    rw [chg_self, initSpan_blk hj hP _ (hty j hj')]
  · rw [chg_ne hj _ _ hτ]

theorem crdL_sum {Sb : D.C.Sub A.ch r} {hj : k + r + 1 ≤ Dw.mult σ} (hS : IsFrSub D Sb hj) {a : A.ch.ι}
    {φ : A.ch.R a →+* K} {z : Sp K ⟶ X} (e : spMap φ ≫ A.ch.χ a = z) (h : ⊤ ≤ z ⁻¹ᵁ D.C.B (Sb.α a))
    {u : TVecs Dw M.t (z ≫ π)} (hu : up u = (A.fr a).bc φ) (v : Fin (r + 1) → K) :
    crdL (D.b (Sb.α a)) z h (∑ i : Fin (r + 1), v i • u σ ⟨k + i, by omega⟩) = ((Sb.M a).map φ).mulVec v := by
  rw [map_sum]
  simp only [map_smul, ← crd_eq, ← hS a K φ z e h u hu]
  funext j
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem exists_vec {Sb : D.C.Sub A.ch r} {hj : k + r + 1 ≤ Dw.mult σ} (hS : IsFrSub D Sb hj)
    (hty : k + r + 1 ∈ ty σ ∨ k + r + 1 = Dw.mult σ) (hk : k < Dw.mult σ) {a : A.ch.ι}
    {φ : A.ch.R a →+* K} {u : Vecs Dw M.t K} (hu : A.FlagAt (spMap φ ≫ A.ch.χ a) u) :
    ∃ v : Fin (r + 1) → K, v ≠ 0 ∧ ∀ z : Sp K ⟶ X, z = spMap φ ≫ A.ch.χ a → ∀ U : TVecs Dw M.t (z ≫ π), up U = u →
      ∀ h, crd (D.b (Sb.α a)) z h (U σ ⟨k, hk⟩) = ((Sb.M a).map φ).mulVec v := by
  obtain ⟨U, rfl⟩ := hu.exists_up
  obtain ⟨u₀, h₀⟩ := A.exists_up_fr (φ := φ) rfl
  obtain ⟨h1, h2⟩ := (A.flagAt_iff rfl h₀ U).1 hu
  have hF : A.FlagAt (spMap φ ≫ A.ch.χ a) (up u₀) := h₀ ▸ A.flagAt_fr rfl
  have h3 : U σ ⟨k, hk⟩ ∈ initSpan K (u₀ σ) (k + r + 1) := by
    have h4 : U σ ⟨k, hk⟩ ∈ initSpan K (U σ) (k + r + 1) := Submodule.subset_span ⟨_, show k < k + r + 1 by omega, rfl⟩
    rcases hty with h | h
    · rwa [← h2 σ _ h]
    · have f₀ := A.isFrame_bc (φ := φ) rfl
      rw [← h₀] at f₀
      rw [h, initSpan_top, ((isFrame_up_iff _ _).1 f₀ σ).2, ← ((isFrame_up_iff _ _).1 h1 σ).2]
      exact Submodule.subset_span ⟨_, rfl⟩
  obtain ⟨v, hv⟩ := exists_sub_mem hj _ h3
  have key : ∀ h, crd (D.b (Sb.α a)) _ h (U σ ⟨k, hk⟩) = ((Sb.M a).map φ).mulVec v := fun h => by
    have := (crdL_eq_zero_iff D hF _ h _).2 hv
    rwa [map_sub, sub_eq_zero, crdL_sum hS rfl h h₀] at this
  refine ⟨v, ?_, ?_⟩
  · rintro rfl
    have := key (le_preimage_comp _ (Sb.le a))
    rw [Matrix.mulVec_zero, crd_eq, crdL_eq_zero_iff D hu] at this
    exact not_mem_initSpan (linearIndependent_of_flagAt hu σ) ⟨k, hk⟩ this
  · rintro z rfl U' hU'
    rw [up_injective hU']
    exact key

section Closure

variable {D : Adapted A σ k} {Sb : D.C.Sub A.ch r} (Cl : Sb.Closure (π ≫ M.s))

def frBelow (q : Cl.ch'.ι) : TVecs Dw M.t ((Cl.ch'.χ q ≫ Cl.f) ≫ π) := (A.exists_up_fr (Cl.sq q).symm).choose

theorem up_frBelow (q : Cl.ch'.ι) : up (frBelow Cl q) = (A.fr (Cl.b q)).bc (Cl.ρ q) :=
  (A.exists_up_fr (Cl.sq q).symm).choose_spec

def pre (hj : k + r + 1 ≤ Dw.mult σ) : PreAtlas M Cl.Z' where
  ch := Cl.ch'
  alg q := (Cl.ρ q).comp (A.alg (Cl.b q))
  fr q := up (chg hj (Cl.P q) (frBelow Cl q))

theorem chg_k (hj : k + r + 1 ≤ Dw.mult σ) (hk : k < Dw.mult σ) {S : Type} [CommRing S]
    (P : Matrix (Fin (r + 1)) (Fin (r + 1)) S) {x : Sp S ⟶ M.X} (u : TVecs Dw M.t x) :
    chg hj P u σ ⟨k, hk⟩ = ∑ l : Fin (r + 1), P l 0 • u σ ⟨k + l, by omega⟩ := by
  rw [chg_self]
  exact blk_add hj P _ 0

theorem sq_point (q : Cl.ch'.ι) {ψ : Cl.ch'.R q →+* K} {w : Sp K ⟶ Cl.Z'} (e : spMap ψ ≫ Cl.ch'.χ q = w) :
    spMap (ψ.comp (Cl.ρ q)) ≫ A.ch.χ (Cl.b q) = w ≫ Cl.f := by
  rw [← spMap_comp', Category.assoc, ← Cl.sq, ← Category.assoc, e]

theorem exists_good (hj : k + r + 1 ≤ Dw.mult σ) (hk : k < Dw.mult σ) (hS : IsFrSub D Sb hj)
    (hty : ∀ e ∈ ty σ, e ≤ k ∨ k + r + 1 ≤ e) (q : Cl.ch'.ι) {ψ : Cl.ch'.R q →+* K} {w : Sp K ⟶ Cl.Z'}
    (e : spMap ψ ≫ Cl.ch'.χ q = w) : ∃ U : TVecs Dw M.t ((w ≫ Cl.f) ≫ π),
      up U = ((pre Cl hj).fr q).bc ψ ∧ Good D hk Cl.L w U := by
  have e' := sq_point Cl q e
  have e2 : spMap ψ ≫ (Cl.ch'.χ q ≫ Cl.f) ≫ π = (w ≫ Cl.f) ≫ π := by
    rw [← e]; simp only [Category.assoc]
  let U₀ : TVecs Dw M.t ((w ≫ Cl.f) ≫ π) := fun τ i => tanPull ψ e2 (frBelow Cl q τ i)
  have h₀ : up U₀ = (A.fr (Cl.b q)).bc (ψ.comp (Cl.ρ q)) := by
    rw [up_tanPull ψ e2, up_frBelow, bc_bc]
  have hF : A.FlagAt (w ≫ Cl.f) (up U₀) := h₀ ▸ A.flagAt_fr e'
  have hP : IsUnit ((Cl.P q).map ψ) := by
    have := (Cl.P_unit q).map (RingHom.mapMatrix ψ)
    exact this
  have hU : (fun τ i => tanPull ψ e2 (chg hj (Cl.P q) (frBelow Cl q) τ i)) = chg hj ((Cl.P q).map ψ) U₀ :=
    tanPull_chg hj _ ψ e2 _
  refine ⟨chg hj ((Cl.P q).map ψ) U₀, ?_, ?_⟩
  · rw [← hU]
    exact up_tanPull ψ e2 _
  · have h : ⊤ ≤ (w ≫ Cl.f) ⁻¹ᵁ D.C.B (Sb.α (Cl.b q)) := e' ▸ le_preimage_comp _ (Sb.le _)
    refine good_of_one (flagAt_chg hj hty hP hF) (α := Sb.α (Cl.b q)) (h := h) ?_
    rw [crd_eq, chg_k hj hk]
    have := crdL_sum hS e' h h₀ (fun l => ψ (Cl.P q l 0))
    simp only [Matrix.map_apply]
    rw [this]
    exact Cl.car q K ψ w e h

theorem pre_flagAt_iff (hj : k + r + 1 ≤ Dw.mult σ) (hk : k < Dw.mult σ) (hS : IsFrSub D Sb hj)
    (hty : ∀ e ∈ ty σ, e ≤ k ∨ k + r + 1 ≤ e) (h1 : ty' σ = insert (k + 1) (ty σ))
    (h2 : ∀ σ', σ' ≠ σ → ty' σ' = ty σ') (w : Sp K ⟶ Cl.Z') (U : TVecs Dw M.t ((w ≫ Cl.f) ≫ π)) :
    (pre Cl hj).FlagAt (Cl.f ≫ π) ty' w (up U) ↔ Good D hk Cl.L w U := by
  have ex : w ≫ Cl.f ≫ π = (w ≫ Cl.f) ≫ π := (Category.assoc _ _ _).symm
  constructor
  · rintro ⟨q, ψ, e, hf, hs⟩
    obtain ⟨U₀, hU₀, hg⟩ := exists_good Cl hj hk hS hty q e
    rw [ex] at hf hs
    have hs' : SameFlag ty' M.t ((w ≫ Cl.f) ≫ π) (up U₀) (up U) := by rw [hU₀]; exact hs
    rw [sameFlag_up_iff] at hs'
    exact hg.of_le (sq_point Cl q e) hf h1 h2 hs'
  · intro hg
    obtain ⟨a, φ, e, -⟩ := id hg.1
    have hr : w (IsLocalRing.closedPoint K) ∈ Cl.ch'.carrier := by
      rw [Cl.carrier_eq]
      exact A.ch.range_subset e ⟨IsLocalRing.closedPoint K, rfl⟩
    obtain ⟨q, ψ, eq⟩ := Cl.ch'.exists_fac w hr
    obtain ⟨U₀, hU₀, hg₀⟩ := exists_good Cl hj hk hS hty q eq
    have e' := sq_point Cl q eq
    obtain ⟨u₁, h₁⟩ := A.exists_up_fr e'
    have hfr := ((A.flagAt_iff e' h₁ U).1 hg.1).1
    have hs := (sameFlag_up_iff U₀ U).2 (hg₀.le hg h1 h2)
    rw [hU₀] at hs
    exact ⟨q, ψ, eq, by rw [ex]; exact hfr, by rw [ex]; exact hs⟩

theorem pre_cover : Cl.ch'.carrier = (Cl.f ≫ π) ⁻¹' Set.range M.j := by
  rw [Cl.carrier_eq, A.cover]
  ext x
  simp only [Set.mem_preimage, Scheme.Hom.comp_apply]

theorem pre_alg_s (q : Cl.ch'.ι) : Cl.ch'.χ q ≫ (Cl.f ≫ π) ≫ M.s =
    spMap (((Cl.ρ q).comp (A.alg (Cl.b q))).comp V.subtype) := by
  have := A.affineOpenChart_comp_structure_eq_spMap (Cl.sq q).symm
  simp only [Category.assoc] at this ⊢
  exact this

theorem pre_smooth (q : Cl.ch'.ι) : Smooth (Cl.ch'.χ q ≫ Cl.f ≫ π) := by
  have h3 : Cl.ch'.χ q ≫ Cl.f ≫ π = spMap (Cl.ρ q) ≫ A.ch.χ (Cl.b q) ≫ π := by
    rw [← Category.assoc, Cl.sq, Category.assoc]
  have := Cl.smooth q
  have := A.smooth (Cl.b q)
  rw [h3]
  infer_instance

theorem pre_frame (hj : k + r + 1 ≤ Dw.mult σ) (q : Cl.ch'.ι) : LocM.IsFrame M.t ((Cl.ρ q).comp (A.alg (Cl.b q)))
    (Cl.ch'.χ q ≫ Cl.f ≫ π) (up (chg hj (Cl.P q) (frBelow Cl q))) := by
  have hf := A.isFrame_bc (Cl.sq q).symm
  have hf' : LocM.IsFrame M.t ((Cl.ρ q).comp (A.alg (Cl.b q))) ((Cl.ch'.χ q ≫ Cl.f) ≫ π) (up (frBelow Cl q)) := by
    rw [up_frBelow]; exact hf
  have h5 : ∀ {x x' : Sp (Cl.ch'.R q) ⟶ M.X} (_ : x = x') {v : Vecs Dw M.t (Cl.ch'.R q)},
      LocM.IsFrame M.t ((Cl.ρ q).comp (A.alg (Cl.b q))) x v → LocM.IsFrame M.t ((Cl.ρ q).comp (A.alg (Cl.b q))) x' v := by
    rintro _ _ rfl _ h
    exact h
  exact h5 (Category.assoc _ _ _) (isFrame_chg hj (Cl.P_unit q) hf')

theorem pre_glue (hj : k + r + 1 ≤ Dw.mult σ) (hk : k < Dw.mult σ) (hS : IsFrSub D Sb hj)
    (hty : ∀ e ∈ ty σ, e ≤ k ∨ k + r + 1 ≤ e) (h1 : ty' σ = insert (k + 1) (ty σ))
    (h2 : ∀ σ', σ' ≠ σ → ty' σ' = ty σ') (K : Type) [Field K] (q q' : Cl.ch'.ι) (ψ : Cl.ch'.R q →+* K)
    (ψ' : Cl.ch'.R q' →+* K) (e : spMap ψ ≫ Cl.ch'.χ q = spMap ψ' ≫ Cl.ch'.χ q') :
    SameFlag ty' M.t (spMap ψ ≫ Cl.ch'.χ q ≫ Cl.f ≫ π) (((pre Cl hj).fr q).bc ψ) (((pre Cl hj).fr q').bc ψ') := by
  obtain ⟨U, hU, hg⟩ := exists_good Cl hj hk hS hty q (rfl : spMap ψ ≫ Cl.ch'.χ q = _)
  obtain ⟨U', hU', hg'⟩ := exists_good Cl hj hk hS hty q' e.symm
  have hs := (sameFlag_up_iff U U').2 (hg.le hg' h1 h2)
  rw [hU, hU'] at hs
  have ex : spMap ψ ≫ Cl.ch'.χ q ≫ Cl.f ≫ π = ((spMap ψ ≫ Cl.ch'.χ q) ≫ Cl.f) ≫ π := by
    simp only [Category.assoc]
  rw [ex]
  exact hs

def atlas (hj : k + r + 1 ≤ Dw.mult σ) (hk : k < Dw.mult σ) (hS : IsFrSub D Sb hj)
    (hty₀ : k + r + 1 ∈ ty σ ∨ k + r + 1 = Dw.mult σ) (hty : ∀ e ∈ ty σ, e ≤ k ∨ k + r + 1 ≤ e)
    (h1 : ty' σ = insert (k + 1) (ty σ)) (h2 : ∀ σ', σ' ≠ σ → ty' σ' = ty σ') : Atlas M (Cl.f ≫ π) ty' where
  toPreAtlas := pre Cl hj
  cover := pre_cover Cl
  alg_s q := pre_alg_s Cl q
  smooth q := pre_smooth Cl q
  frame q := pre_frame Cl hj q
  glue K _ q q' ψ ψ' e := pre_glue Cl hj hk hS hty h1 h2 K q q' ψ ψ' e
  bij K _ g y hy u hu := by
    obtain ⟨w₀, ⟨hw₀, hF⟩, hun⟩ := A.bij K g y hy u hu
    obtain ⟨a, φ, rfl, -⟩ := id hF
    obtain ⟨v, hv0, hv⟩ := exists_vec hS hty₀ hk hF
    obtain ⟨w, ⟨hw1, hw2⟩, hwu⟩ := Cl.bij a K φ v hv0
    have hx : ∀ {w' : Sp K ⟶ Cl.Z'}, w' ≫ Cl.f ≫ π = y ≫ M.j → ∃ U : TVecs Dw M.t ((w' ≫ Cl.f) ≫ π), up U = u :=
      fun {w'} e => exists_up fun τ i => by
        have e' : (w' ≫ Cl.f) ≫ π = y ≫ M.j := (Category.assoc _ _ _).trans e
        rw [e']
        exact (hu.1 τ i).1
    have hw : w ≫ Cl.f ≫ π = y ≫ M.j := by rw [← Category.assoc, hw1, hw₀]
    refine ⟨w, ⟨hw, ?_⟩, ?_⟩
    · have h3 : A.FlagAt (w ≫ Cl.f) u := by rw [hw1]; exact hF
      have h : ⊤ ≤ (w ≫ Cl.f) ⁻¹ᵁ D.C.B (Sb.α a) := by rw [hw1]; exact le_preimage_comp _ (Sb.le a)
      obtain ⟨U, rfl⟩ := hx hw
      refine (pre_flagAt_iff Cl hj hk hS hty h1 h2 w U).2 (good_of_one h3 (α := Sb.α a) (h := h) ?_)
      rw [hv _ hw1 U rfl h]
      exact hw2 h
    · rintro w' ⟨e1, e2⟩
      obtain ⟨U, rfl⟩ := hx e1
      have hg := (pre_flagAt_iff Cl hj hk hS hty h1 h2 w' U).1 e2
      have e3 : w' ≫ Cl.f = spMap φ ≫ A.ch.χ a :=
        hun _ ⟨(Category.assoc _ _ _).trans e1, hg.1⟩
      refine hwu w' ⟨e3, fun h => ?_⟩
      rw [← hv _ e3 U rfl h]
      exact hg.2 _ h

end Closure

theorem exists_stepAtlas (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F)
    [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X)
    (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k r : ℕ) (D : Adapted A σ k)
    (hj : k + r + 1 ≤ Dw.mult σ) (hk : k < Dw.mult σ) (Sb : D.C.Sub A.ch r) (Cl : Sb.Closure (π ≫ M.s))
    (ty' : (E →+* ℂ) → Finset ℕ) : IsFrSub D Sb hj → (k + r + 1 ∈ ty σ ∨ k + r + 1 = Dw.mult σ) →
      (∀ e ∈ ty σ, e ≤ k ∨ k + r + 1 ≤ e) → ty' σ = insert (k + 1) (ty σ) → (∀ σ', σ' ≠ σ → ty' σ' = ty σ') →
      ∃ A' : Atlas M (Cl.f ≫ π) ty', StepRel D hk Cl.L A' := fun hS hty₀ hty h1 h2 =>
  ⟨atlas Cl hj hk hS hty₀ hty h1 h2, fun _ _ w U => pre_flagAt_iff Cl hj hk hS hty h1 h2 w U⟩

end GlobalTheory.DRFlag.StepAtlas
