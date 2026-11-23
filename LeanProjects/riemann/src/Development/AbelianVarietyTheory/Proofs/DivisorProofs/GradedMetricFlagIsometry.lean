import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.FlagChain
open GlobalTheory.VBExt (AdaptedChart)
open GlobalTheory.Twist (resM app_resM)
open scoped ComplexOrder

namespace GlobalTheory.FlagConcat

section Fibre

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {A B C D E : X.Modules}
  {a b c d e : ℕ} {y : CxPts p σ}

def fib (hA : IsVB A a) (hB : IsVB B b) (φ : A ⟶ B) (y : CxPts p σ) : Matrix (Fin b) (Fin a) ℂ :=
  Matrix.of fun i j => (hB.pick y).crd p σ (φ.app (hA.pick y).U ((hA.pick y).e j)) y i

def bil (h : Met p σ A a) (y : CxPts p σ) (v w : Fin a → ℂ) : ℂ := form (h.G (h.isVB.pick y) y) v w

theorem fib_crd (hA : IsVB A a) (hB : IsVB B b) (φ : A ⟶ B) {V : X.Opens} (s : Γ(A, V)) (hy : y ∈ ptsIn p σ V) :
    fib hA hB φ y *ᵥ (hA.pick y).crd p σ s y = (hB.pick y).crd p σ (φ.app V s) y :=
  (Chart.crd_app _ _ φ s hy (hA.mem_pick y)).symm

theorem mulVec_ext {m n : Type} [Fintype n] [DecidableEq n] {M N : Matrix m n ℂ}
    (h : ∀ j, M *ᵥ Pi.single j 1 = N *ᵥ Pi.single j 1) : M = N := by
  ext i j
  simpa using congrFun (h j) i

theorem fib_comp (hA : IsVB A a) (hB : IsVB B b) (hC : IsVB C c) (φ : A ⟶ B) (ψ : B ⟶ C) (v : Fin a → ℂ) :
    fib hB hC ψ y *ᵥ (fib hA hB φ y *ᵥ v) = fib hA hC (φ ≫ ψ) y *ᵥ v := by
  rw [mulVec_mulVec]
  refine congrArg (· *ᵥ v) (mulVec_ext fun j => ?_)
  have hy := hA.mem_pick y
  rw [← mulVec_mulVec, ← (hA.pick y).crd_frame hy j, fib_crd _ _ _ _ hy, fib_crd _ _ _ _ hy, fib_crd _ _ _ _ hy]
  rfl

theorem fib_zero (hA : IsVB A a) (hB : IsVB B b) (v : Fin a → ℂ) : fib hA hB 0 y *ᵥ v = 0 := by
  rw [show fib hA hB 0 y = 0 from ?_, zero_mulVec]
  ext i j
  exact congrFun ((hB.pick y).crd_zero y) i

theorem fib_id (hA : IsVB A a) (v : Fin a → ℂ) : fib hA hA (𝟙 A) y *ᵥ v = v := by
  rw [show fib hA hA (𝟙 A) y = 1 from (hA.pick y).tr_self (hA.mem_pick y), one_mulVec]

theorem bil_eq (hA : IsVB A a) (hB : IsVB B b) {h : Met p σ C c} {h' : Met p σ D d} {φ : A ⟶ C} {ψ : B ⟶ C}
    {φ' : A ⟶ D} {ψ' : B ⟶ D} (H : ∀ (V : X.Opens) (s : Γ(A, V)) (t : Γ(B, V)), y ∈ ptsIn p σ V →
      h.form (φ.app V s) (ψ.app V t) y = h'.form (φ'.app V s) (ψ'.app V t) y) (v : Fin a → ℂ) (w : Fin b → ℂ) :
    bil h y (fib hA h.isVB φ y *ᵥ v) (fib hB h.isVB ψ y *ᵥ w) =
      bil h' y (fib hA h'.isVB φ' y *ᵥ v) (fib hB h'.isVB ψ' y *ᵥ w) := by
  have key {F : X.Modules} {n : ℕ} (m : Met p σ F n) (f : A ⟶ F) (g : B ⟶ F) (i : Fin a) (j : Fin b) :
      ((fib hA m.isVB f y)ᵀ * m.G (m.isVB.pick y) y * (fib hB m.isVB g y)ᴴᵀ) i j =
        m.form (f.app _ (resM A (inf_le_left : (hA.pick y).U ⊓ (hB.pick y).U ≤ _) ((hA.pick y).e i)))
          (g.app _ (resM B inf_le_right ((hB.pick y).e j))) y := by
    have hy := mem_ptsIn_inf.2 ⟨hA.mem_pick y, hB.mem_pick y⟩
    rw [Met.form, ← fib_crd hA _ _ _ hy, ← fib_crd hB _ _ _ hy, Chart.crd_resM _ _ _ hy, Chart.crd_resM _ _ _ hy,
      Chart.crd_frame _ (hA.mem_pick y), Chart.crd_frame _ (hB.mem_pick y), form_mulVec]
    simp [form]
  rw [bil, bil, form_mulVec, form_mulVec]
  congr 2
  ext i j
  rw [key, key, H _ _ _ (mem_ptsIn_inf.2 ⟨hA.mem_pick y, hB.mem_pick y⟩)]

theorem conj_bil (h : Met p σ A a) (v w : Fin a → ℂ) : starRingEnd ℂ (bil h y v w) = bil h y w v :=
  conj_form (h.posDef _ y (h.isVB.mem_pick y)).isHermitian _ _

theorem bil_add_right (h : Met p σ A a) (v w w' : Fin a → ℂ) : bil h y v (w + w') = bil h y v w + bil h y v w' :=
  form_add_right _ _ _ _

theorem surj_of_isometry {h : Met p σ A a} {h' : Met p σ B a} {M : Matrix (Fin a) (Fin a) ℂ}
    (H : ∀ v w, bil h' y (M *ᵥ v) (M *ᵥ w) = bil h y v w) (w : Fin a → ℂ) : ∃ v, M *ᵥ v = w := by
  refine mulVec_surjective_iff_isUnit.2 (mulVec_injective_iff_isUnit.1 ?_) w
  refine (injective_iff_map_eq_zero M.mulVecLin).2 fun v (hv : M *ᵥ v = 0) => by_contra fun h0 => ?_
  have := (posDef_iff.1 (h.posDef _ y (h.isVB.mem_pick y))).2 v h0
  have e := H v v
  rw [hv] at e
  change _ = form _ v v at e
  rw [← e] at this
  simp [bil, form] at this

def Coiso (h : Met p σ A a) (h' : Met p σ B b) (y : CxPts p σ) (M : Matrix (Fin b) (Fin a) ℂ) : Prop :=
  ∀ ξ, ∃ v, M *ᵥ v = ξ ∧ ∀ w, bil h y v w = bil h' y ξ (M *ᵥ w)

variable {S : ShortComplex X.Modules}

theorem exists_frame (hS : S.ShortExact) (h₁ : IsVB S.X₁ a) (h₂ : IsVB S.X₂ (a + b)) (h₃ : IsVB S.X₃ b)
    (ch : AdaptedChart S a b) (hy : y ∈ ptsIn p σ ch.U) :
    let M := Matrix.of fun i j => (h₂.pick y).crd p σ (ch.frame j) y i
    (∀ v, ∃ x, M *ᵥ x = v) ∧ (∀ x, M *ᵥ (incl _ _ *ᵥ x) = fib h₁ h₂ S.f y *ᵥ ((h₁.pick y).tr p σ ch.sub y *ᵥ x)) ∧
      ∀ x, fib h₂ h₃ S.g y *ᵥ (M *ᵥ x) = (h₃.pick y).tr p σ ch.quot y *ᵥ (quotMap _ _ *ᵥ x) := by
  intro M
  refine ⟨fun v => ?_, fun x => ?_, fun x => ?_⟩
  · obtain ⟨x, rfl⟩ := mulVec_surjective_iff_isUnit.2 ((h₂.pick y).isUnit_tr (ch.mid hS) (h₂.mem_pick y) hy) v
    refine ⟨x ∘ finSumFinEquiv, ?_⟩
    have : M = ((h₂.pick y).tr p σ (ch.mid hS) y).submatrix id finSumFinEquiv := by
      ext i j
      simp [M, Chart.tr, AdaptedChart.mid]
    rw [this, submatrix_mulVec_equiv]
    simp [Function.comp_assoc]
  · rw [mulVec_mulVec, mulVec_mulVec]
    refine congrArg (· *ᵥ x) (Matrix.ext fun i j => ?_)
    refine Eq.trans ?_ (congrFun (fib_crd h₁ h₂ S.f (ch.e j) hy) i).symm
    simp [M, incl, mul_apply, AdaptedChart.frame, one_apply]
  · rw [mulVec_mulVec, mulVec_mulVec]
    refine congrArg (· *ᵥ x) (Matrix.ext fun i j => ?_)
    refine (congrFun (fib_crd h₂ h₃ S.g (ch.frame j) hy) i).trans ?_
    rcases j with j | j
    · rw [show S.g.app ch.U (ch.frame (.inl j)) = 0 from congr(($(S.zero)).app ch.U (ch.e j)), Chart.crd_zero]
      simp [quotMap, mul_apply]
    · simp [quotMap, mul_apply, one_apply, Chart.tr, AdaptedChart.quot, AdaptedChart.frame]

theorem fib_exact (hS : S.ShortExact) (h₁ : IsVB S.X₁ a) (h₂ : IsVB S.X₂ c) (h₃ : IsVB S.X₃ b) {v : Fin c → ℂ}
    (hv : fib h₂ h₃ S.g y *ᵥ v = 0) : ∃ x, fib h₁ h₂ S.f y *ᵥ x = v := by
  have : Nonempty X := ⟨y.1 (IsLocalRing.closedPoint ℂ)⟩
  obtain rfl := (VBExt.isVB_and_cls_det_of_shortExact X _ a b hS h₁ h₃).1.rank_unique h₂
  obtain ⟨ch, hy⟩ := Met.exists_adapted hS h₁ h₃ y
  obtain ⟨e₁, e₂, e₃⟩ := exists_frame hS h₁ h₂ h₃ ch hy
  obtain ⟨x, rfl⟩ := e₁ v
  rw [e₃] at hv
  have hx := mulVec_injective_iff_isUnit.2 ((h₃.pick y).isUnit_tr ch.quot (h₃.mem_pick y) hy)
    (hv.trans (mulVec_zero _).symm)
  refine ⟨_, (e₂ (orthProj 0 *ᵥ x)).symm.trans (congrArg _ ?_)⟩
  conv_rhs => rw [← one_mulVec x, ← incl_mul_orthProj_add 0, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hx,
    mulVec_zero, add_zero]

theorem coiso_quot (hS : S.ShortExact) (h₁ : IsVB S.X₁ a) (h : Met p σ S.X₂ (a + b)) (h₃ : IsVB S.X₃ b) :
    Coiso h (h.quot hS h₁ h₃) y (fib h.isVB h₃ S.g y) := fun ξ => by
  obtain ⟨ch, hy⟩ := Met.exists_adapted hS h₁ h₃ y
  obtain ⟨e₁, -, e₃⟩ := exists_frame hS h₁ h.isVB h₃ ch hy
  obtain ⟨q, rfl⟩ := mulVec_surjective_iff_isUnit.2 ((h₃.pick y).isUnit_tr ch.quot (h₃.mem_pick y) hy) ξ
  have hu := (posDef_subGram (h.posDef_gram_frame hS ch hy)).det_pos.ne'.isUnit
  refine ⟨_, (e₃ (orthLift (h.gram ch.frame y) *ᵥ q)).trans ?_, fun w => ?_⟩
  · rw [mulVec_mulVec q, quotMap_mul_orthLift, one_mulVec]
  · obtain ⟨x, rfl⟩ := e₁ w
    rw [e₃, bil, bil, ← form_chg, ← form_chg, ← h.gram_eq _ (h.isVB.mem_pick y) _ hy,
      ← Met.trans _ _ _ _ (h₃.mem_pick y), h.quot_G hS h₁ h₃ ch hy, ← form_orthLift hu]
    conv_lhs => rw [← one_mulVec x, ← incl_mul_orthProj_add (h.gram ch.frame y), add_mulVec, ← mulVec_mulVec,
      ← mulVec_mulVec, form_add_right, form_orthLift_incl hu, zero_add]

theorem Coiso.comp {h : Met p σ A a} {h' : Met p σ B b} {h'' : Met p σ C c} {φ : A ⟶ B} {ψ : B ⟶ C}
    (H : Coiso h h' y (fib h.isVB h'.isVB φ y)) (H' : Coiso h' h'' y (fib h'.isVB h''.isVB ψ y)) :
    Coiso h h'' y (fib h.isVB h''.isVB (φ ≫ ψ) y) := fun ξ => by
  obtain ⟨v, rfl, hv⟩ := H' ξ
  obtain ⟨v', rfl, hv'⟩ := H v
  exact ⟨v', (fib_comp _ _ _ _ _ _).symm, fun w => by rw [hv', hv, fib_comp _ _ _ _ _ w, fib_comp]⟩

theorem form_eq_of_coiso {h : Met p σ A a} {h' : Met p σ B b} {h'' : Met p σ C c} {φ : A ⟶ B} {ψ : B ≅ C}
    (H : Coiso h h' y (fib h.isVB h'.isVB φ y)) (H' : Coiso h h'' y (fib h.isVB h''.isVB (φ ≫ ψ.hom) y))
    {V : X.Opens} (s t : Γ(B, V)) (hy : y ∈ ptsIn p σ V) :
    h''.form (ψ.hom.app V s) (ψ.hom.app V t) y = h'.form s t y := by
  rw [Met.form, Met.form, ← fib_crd h'.isVB _ _ _ hy, ← fib_crd h'.isVB _ _ _ hy]
  generalize (h'.isVB.pick y).crd p σ s y = ξ, (h'.isVB.pick y).crd p σ t y = η
  obtain ⟨v, rfl, hv⟩ := H ξ
  obtain ⟨w, e, hw⟩ := H' (fib h'.isVB h''.isVB ψ.hom y *ᵥ η)
  have e' := congrArg (fib h''.isVB h'.isVB ψ.inv y *ᵥ ·) e
  simp only [fib_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id, fib_id] at e'
  change bil _ _ _ _ = bil _ _ _ _
  rw [← conj_bil, fib_comp, ← hw, conj_bil, hv, e']

theorem exists_add (hS : S.ShortExact) (h₁ : IsVB S.X₁ a) (h₂ : IsVB S.X₂ c) (h₃ : IsVB S.X₃ b) (hD : IsVB D d)
    {τ : D ⟶ S.X₂} (hs : ∀ ξ, ∃ x, fib hD h₃ (τ ≫ S.g) y *ᵥ x = ξ) (w : Fin c → ℂ) :
    ∃ x z, w = fib hD h₂ τ y *ᵥ x + fib h₁ h₂ S.f y *ᵥ z := by
  obtain ⟨x, hx⟩ := hs (fib h₂ h₃ S.g y *ᵥ w)
  obtain ⟨z, hz⟩ := fib_exact hS h₁ h₂ h₃ (v := w - fib hD h₂ τ y *ᵥ x) (by rw [mulVec_sub, fib_comp, hx, sub_self])
  exact ⟨x, z, by rw [hz, add_sub_cancel]⟩

theorem coiso_of_split (hS : S.ShortExact) (h₁ : IsVB S.X₁ a) (h₂ : Met p σ S.X₂ c) (h₃ : Met p σ S.X₃ b)
    (hD : Met p σ D b) {τ : D ⟶ S.X₂}
    (i₂ : ∀ v w, bil h₂ y (fib hD.isVB h₂.isVB τ y *ᵥ v) (fib hD.isVB h₂.isVB τ y *ᵥ w) = bil hD y v w)
    (i₃ : ∀ v w, bil h₃ y (fib hD.isVB h₃.isVB (τ ≫ S.g) y *ᵥ v) (fib hD.isVB h₃.isVB (τ ≫ S.g) y *ᵥ w) = bil hD y v w)
    (o : ∀ v w, bil h₂ y (fib hD.isVB h₂.isVB τ y *ᵥ v) (fib h₁ h₂.isVB S.f y *ᵥ w) = 0) :
    Coiso h₂ h₃ y (fib h₂.isVB h₃.isVB S.g y) := fun ξ => by
  obtain ⟨v, rfl⟩ := surj_of_isometry i₃ ξ
  refine ⟨_, fib_comp _ _ _ _ _ v, fun w => ?_⟩
  obtain ⟨x, z, rfl⟩ := exists_add hS h₁ h₂.isVB h₃.isVB hD.isVB (surj_of_isometry i₃) w
  rw [bil_add_right, i₂, o, mulVec_add, fib_comp, fib_comp, S.zero, fib_zero, add_zero, add_zero, i₃]

theorem bil_restrict (h : Met p σ B b) {i : A ⟶ B} (hi : IsSubbundle i) (hA : IsVB A a) (v w : Fin a → ℂ) :
    bil (h.restrict hi hA) y v w = bil h y (fib hA h.isVB i y *ᵥ v) (fib hA h.isVB i y *ᵥ w) := by
  rw [← bil_eq hA hA (h := h.restrict hi hA) (φ := 𝟙 A) (ψ := 𝟙 A) fun V s t hy => h.form_restrict hi hA s t hy,
    fib_id, fib_id]

end Fibre

section Squares

variable {𝒞 : Type*} [Category 𝒞] [Abelian 𝒞] {W G Q' Q : 𝒞} {f : W ⟶ G} {α : W ⟶ Q'} {κ : G ⟶ Q} {ι : Q' ⟶ Q}

theorem isIso_cokernel_map (sq : IsPullback f α κ ι) [Epi κ] : IsIso (cokernel.map f ι α κ sq.w) := by
  have := Abelian.mono_cokernel_map_of_isPullback sq
  have : Epi (cokernel.map f ι α κ sq.w) :=
    epi_of_epi_fac (f := cokernel.π f) (h := κ ≫ cokernel.π ι) (cokernel.π_desc _ _ _)
  exact isIso_of_mono_of_epi _

theorem shortExact_pullback (sq : IsPullback f α κ ι) {K : 𝒞} {s : K ⟶ G} {z : s ≫ κ = 0}
    (hS : (ShortComplex.mk s κ z).ShortExact) :
    (ShortComplex.mk (sq.lift s 0 (by rw [z, zero_comp])) α (sq.lift_snd _ _ _)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have hm : Mono (sq.lift s 0 (by rw [z, zero_comp])) := mono_of_mono_fac (sq.lift_fst _ _ _)
  have he : Epi α := (MorphismProperty.epimorphisms 𝒞).of_isPullback sq hS.epi_g
  refine { exact := ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι' _ _ fun {T} x hx => ?_) }
  have hx' : (x ≫ f) ≫ κ = 0 := by rw [Category.assoc, sq.w, reassoc_of% hx, zero_comp]
  refine ⟨hS.exact.lift (x ≫ f) hx', sq.hom_ext ?_ ?_⟩
  · rw [Category.assoc, sq.lift_fst]
    exact hS.exact.lift_f _ _
  · rw [Category.assoc, sq.lift_snd, comp_zero]
    exact hx.symm

end Squares

section Flags

variable {X : Scheme.{0}} {A B L : X.Modules} {g : ℕ}

theorem le_of_rank_eq [Nonempty X] {u : A ⟶ L} {v : B ⟶ L} {n : ℕ} (hu : IsSubbundle u) (hv : IsSubbundle v)
    (hA : IsVB A n) (hB : IsVB B n) (hL : IsVB L g) (h : Le u v) : Le v u := by
  obtain ⟨t, rfl⟩ := h
  have := hv.mono
  have := hu.mono
  have : Mono t := mono_of_mono t v
  obtain ⟨s, e, hs⟩ := isVB_cokernel hu hA hL
  obtain ⟨s', e', hs'⟩ := isVB_cokernel hv hB hL
  obtain rfl : s = 0 + s' := by omega
  have h0 := isVB_zero_iff.1 (VB.isVB_X₁_of_shortExact X _ 0 _ (Vert.shortExact_cokernel_comp t v) hs hs')
  have : Epi t := Preadditive.epi_of_isZero_cokernel t h0
  have := isIso_of_mono_of_epi t
  exact ⟨inv t, IsIso.inv_hom_id_assoc _ _⟩

theorem exists_flag [Nonempty X] (hL : IsVB L g) {J : Type} {P : J → X.Modules} (j : ∀ a, P a ⟶ L) (n : J → ℕ)
    (hj : ∀ a, IsSubbundle (j a)) (hP : ∀ a, IsVB (P a) (n a)) (hle : ∀ a b, n a ≤ n b → Le (j a) (j b))
    (hs : ∀ x : Fin g, ∃ a, n a = x + 1) :
    ∃ w : Vert.Flag L g, ∀ a (x : Fin (g + 1)), n a = x → Le (j a) (w.ι x) ∧ Le (w.ι x) (j a) := by
  have key (x : Fin (g + 1)) : ∃ (A : X.Modules) (i : A ⟶ L), IsSubbundle i ∧ IsVB A x ∧
      ∀ a, (n a ≤ x → Le (j a) i) ∧ (x ≤ n a → Le i (j a)) := by
    induction x using Fin.cases with
    | zero =>
      have hz : IsZero (kernel (𝟙 L)) := isZero_kernel_of_mono _
      refine ⟨_, 0, ⟨hz.mono _, g, hL.of_iso cokernelZeroIsoTarget.symm⟩, isVB_zero_iff.2 hz,
        fun a => ⟨fun h => ⟨0, ?_⟩, fun _ => ⟨0, hz.eq_of_src _ _⟩⟩⟩
      have h0 := hP a
      rw [Nat.le_zero.1 h] at h0
      exact (isVB_zero_iff.1 h0).eq_of_src _ _
    | succ x =>
      obtain ⟨b, hb⟩ := hs x
      exact ⟨_, j b, hj b, by rw [Fin.val_succ, ← hb]; exact hP b,
        fun a => ⟨fun h => hle _ _ (hb ▸ h), fun h => hle _ _ (hb ▸ h)⟩⟩
  choose F i h₁ h₂ h₃ using key
  have hst (x : Fin g) : Le (i x.castSucc) (i x.succ) := by
    obtain ⟨b, hb⟩ := hs x
    exact ((h₃ _ b).2 (by simp [hb])).trans ((h₃ _ b).1 hb.le)
  choose st hst using hst
  have hl : IsIso (i (Fin.last g)) := by
    obtain ⟨t, ht⟩ := le_of_rank_eq (h₁ _) (isSubbundle_of_isIso (𝟙 L)) (h₂ (Fin.last g)) hL hL ⟨_, Category.comp_id _⟩
    have := (h₁ (Fin.last g)).mono
    have := epi_of_epi_fac ht
    exact isIso_of_mono_of_epi _
  exact ⟨⟨F, i, h₁, h₂, st, hst, hl⟩, fun a x h => ⟨(h₃ x a).1 h.le, (h₃ x a).2 h.ge⟩⟩

theorem flag_le (w : Vert.Flag L g) {x x' : Fin (g + 1)} (h : x ≤ x') : Le (w.ι x) (w.ι x') := by
  induction x' using Fin.induction with
  | zero => rw [Fin.le_zero_iff.1 h]; exact ⟨𝟙 _, Category.id_comp _⟩
  | succ i ih =>
    rcases h.eq_or_lt with rfl | h
    · exact ⟨𝟙 _, Category.id_comp _⟩
    · exact (ih (Fin.le_castSucc_iff.2 h)).trans ⟨_, w.step_ι i⟩

end Flags

theorem exists_numbering {ι : Type} {m : ℕ} (o : ι ≃ Fin m) (r : ι → ℕ) (n : Fin (m + 1) → ℕ) (h₀ : n 0 = 0)
    (hn : ∀ a, n (o a).succ = n (o a).castSucc + r a) :
    ∃ e : (Σ a, Fin (r a)) ≃ Fin (n (Fin.last m)), ∀ z, (e z : ℕ) = n (o z.1).castSucc + z.2 := by
  obtain ⟨r', rfl⟩ : ∃ r' : Fin m → ℕ, r = fun a => r' (o a) := ⟨fun i => r (o.symm i), by simp⟩
  have key (i : Fin (m + 1)) : n i = ∑ b : Fin i, r' (Fin.castLE (Nat.lt_succ_iff.1 i.2) b) := by
    induction i using Fin.induction with
    | zero => exact h₀.trans (Finset.sum_of_isEmpty (ι := Fin 0) _).symm
    | succ i ih =>
      obtain ⟨a, rfl⟩ := o.surjective i
      rw [hn, ih]
      exact (Fin.sum_univ_castSucc fun b : Fin ((o a : ℕ) + 1) => r' (Fin.castLE (o a).2 b)).symm
  refine ⟨((Equiv.sigmaCongrLeft (β := fun i => Fin (r' i)) o).trans finSigmaFinEquiv).trans
    (finCongr (key (Fin.last m)).symm), fun z => ?_⟩
  exact (finSigmaFinEquiv_apply _).trans (congrArg (· + _) (key (o z.1).castSucc).symm)

section Step

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {L K G E Q : X.Modules} {g n r : ℕ}

theorem isometric_step {hL : VMetric p L g} (HL : hL.IsCInf) (w : Vert.Flag L g) (x : Fin g) {h : VMetric p E r}
    {h' : VMetric p Q r} (H' : h'.IsCInf) {fl : Vert.Flag E r} {fl' : Vert.Flag Q r} (i : Fin r) {s : K ⟶ G} {κ : G ⟶ Q}
    {z : s ≫ κ = 0} (hS : (ShortComplex.mk s κ z).ShortExact) (hK : IsVB K n) {j : G ⟶ L} [Mono j] {t : E ⟶ G}
    (hu : IsoHom h h' (t ≫ κ)) (hc : Compat (t ≫ κ) fl fl')
    (hT : ∀ σ y v v', bil (hL.met σ) y (fib h.isVB hL.isVB (t ≫ j) y *ᵥ v) (fib h.isVB hL.isVB (t ≫ j) y *ᵥ v') =
      bil (h.met σ) y v v')
    (ho : ∀ σ y v v', bil (hL.met σ) y (fib h.isVB hL.isVB (t ≫ j) y *ᵥ v) (fib hK hL.isVB (s ≫ j) y *ᵥ v') = 0)
    {f₀ : w.F x.castSucc ⟶ G} {α₀ : w.F x.castSucc ⟶ fl'.F i.castSucc} (sq₀ : IsPullback f₀ α₀ κ (fl'.ι i.castSucc))
    (e₀ : f₀ ≫ j = w.ι _) {f₁ : w.F x.succ ⟶ G} {α₁ : w.F x.succ ⟶ fl'.F i.succ}
    (sq₁ : IsPullback f₁ α₁ κ (fl'.ι i.succ)) (e₁ : f₁ ≫ j = w.ι _) :
    (VMetric.grLB w x HL).Isometric (VMetric.grLB fl' i H') := by
  have hS₁ := shortExact_pullback sq₁ hS
  have : Epi α₁ := hS₁.epi_g
  have a₁ : w.step x ≫ f₁ = f₀ := by rw [← cancel_mono j, Category.assoc, e₁, e₀, w.step_ι]
  have a₂ : w.step x ≫ α₁ = α₀ ≫ fl'.step i := by
    rw [← cancel_mono (fl'.ι i.succ), Category.assoc, Category.assoc, ← sq₁.w, fl'.step_ι, ← sq₀.w, reassoc_of% a₁]
  have sq : IsPullback (w.step x) α₀ α₁ (fl'.step i) :=
    IsPullback.of_right (by rw [a₁, fl'.step_ι]; exact sq₀) a₂ sq₁
  let φ : w.gr x ≅ fl'.gr i := @asIso _ _ _ _ _ (isIso_cokernel_map sq)
  have hφ : w.π x ≫ φ.hom = α₁ ≫ fl'.π i := cokernel.π_desc _ _ _
  obtain ⟨c, hc⟩ := hc i.succ
  let τ : fl.F i.succ ⟶ w.F x.succ := sq₁.lift (fl.ι _ ≫ t) c (by rw [hc, Category.assoc])
  have b₁ : τ ≫ w.ι _ = fl.ι _ ≫ t ≫ j := by rw [← e₁, sq₁.lift_fst_assoc, Category.assoc]
  have b₂ : (τ ≫ α₁) ≫ fl'.ι _ = fl.ι _ ≫ t ≫ κ := by rw [sq₁.lift_snd, hc]
  refine VMetric.isometric_det_of_isIsometry k X p _ _ 1 _ _ φ _ _ fun σ V s₁ s₂ y hy => ?_
  refine form_eq_of_coiso (h := (hL.stepMet w x).met σ) (φ := w.π x)
    (coiso_quot (VMetric.stepSeq_shortExact w x) (w.isVB x.castSucc) _ (w.isVB_gr x)) ?_ s₁ s₂ hy
  rw [hφ]
  refine Coiso.comp (h' := (h'.stepMet fl' i).met σ) ?_
    (coiso_quot (VMetric.stepSeq_shortExact fl' i) (fl'.isVB i.castSucc) _ (fl'.isVB_gr i))
  refine coiso_of_split hS₁ hK _ _ ((h.stepMet fl i).met σ) (τ := τ) (fun v v' => ?_) (fun v v' => ?_) fun v v' => ?_
  · refine (bil_restrict (hL.met σ) (w.isSubbundle _) (w.isVB _) _ _).trans
      (Eq.trans ?_ (bil_restrict (h.met σ) (fl.isSubbundle _) (fl.isVB _) _ _).symm)
    rw [← hT]
    congr 1 <;> exact (fib_comp _ _ _ _ _ _).trans (b₁ ▸ (fib_comp _ _ _ _ _ _).symm)
  · refine (bil_restrict (h'.met σ) (fl'.isSubbundle _) (fl'.isVB _) _ _).trans
      (Eq.trans ?_ (bil_restrict (h.met σ) (fl.isSubbundle _) (fl.isVB _) _ _).symm)
    have := bil_eq h.isVB h.isVB (h := h'.met σ) (h' := h.met σ) (φ' := 𝟙 E) (ψ' := 𝟙 E) (y := y)
      fun V s t hy => hu σ V s t y hy
    simp only [fib_id] at this
    rw [← this]
    congr 1 <;> exact (fib_comp _ _ _ _ _ _).trans (b₂ ▸ (fib_comp _ _ _ _ _ _).symm)
  · refine (bil_restrict (hL.met σ) (w.isSubbundle _) (w.isVB _) _ _).trans ?_
    rw [← ho σ y (fib (fl.isVB i.succ) h.isVB (fl.ι _) y *ᵥ v) v']
    congr 1
    · exact (fib_comp _ _ _ _ _ _).trans (b₁ ▸ (fib_comp _ _ _ _ _ _).symm)
    · refine (fib_comp _ _ _ _ _ _).trans ?_
      rw [← e₁, sq₁.lift_fst_assoc]

end Step

theorem exists_adapted_flag : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (ι : Type) [Fintype ι] (L : X.Modules) (g : ℕ) (hL : VMetric p L g) (HL : hL.IsCInf) (E E' : ι → X.Modules) (r : ι → ℕ) (h : ∀ a, VMetric p (E a) (r a)) (h' : ∀ a, VMetric p (E' a) (r a)) (H' : ∀ a, (h' a).IsCInf) (u : ∀ a, E a ⟶ E' a) (m : ℕ) (o : ι ≃ Fin m), (∀ a, IsoHom (h a) (h' a) (u a)) → IsGraded hL o h u → ∀ (fl : ∀ a, Vert.Flag (E a) (r a)) (fl' : ∀ a, Vert.Flag (E' a) (r a)), (∀ a, Compat (u a) (fl a) (fl' a)) → ∃ (T : ∀ a, E a ⟶ L) (w : Vert.Flag L g) (e : (Σ a, Fin (r a)) ≃ Fin g), OrthEmb hL h T ∧ Adapted T fl w e ∧ ∀ z, (VMetric.grLB w (e z) HL).Isometric (VMetric.grLB (fl' z.1) z.2 (H' z.1)) := by
  intro k _ X _ p ι _ L g hL HL E E' r h h' H' u m o hu ⟨F, j, s, κ, t, z, hF, h0, hl, hs, hS, ht, hT⟩ fl fl' hc
  obtain rfl : u = fun a => t a ≫ κ a := funext fun a => (ht a).symm
  choose hj n hn using hF
  have hm (i) : Mono (j i) := (hj i).mono
  have he (a) : Epi (κ a) := (hS a).epi_g
  have n₀ : n 0 = 0 := (hn 0).rank_unique (isVB_zero_iff.2 h0)
  have n₁ (a) : n (o a).succ = n (o a).castSucc + r a :=
    (hn _).rank_unique (VBExt.isVB_and_cls_det_of_shortExact X _ _ _ (hS a) (hn _) (h' a).isVB).1
  obtain rfl : n (Fin.last m) = g := ((hn _).of_iso (asIso (j _))).rank_unique hL.isVB
  obtain ⟨e, hen⟩ := exists_numbering o r n n₀ n₁
  have nm : Monotone n := Fin.monotone_iff_le_succ.2 fun i => by
    obtain ⟨a, rfl⟩ := o.surjective i
    rw [n₁]; omega
  have jm {x x' : Fin (m + 1)} (h : x ≤ x') : Le (j x) (j x') := by
    induction x' using Fin.induction with
    | zero => rw [Fin.le_zero_iff.1 h]; exact ⟨𝟙 _, Category.id_comp _⟩
    | succ i ih =>
      rcases h.eq_or_lt with rfl | h
      · exact ⟨𝟙 _, Category.id_comp _⟩
      · exact (ih (Fin.le_castSucc_iff.2 h)).trans ⟨_, hs i⟩
  let J := Σ a, Fin (r a + 1)
  let P : J → X.Modules := fun c => pullback (κ c.1) ((fl' c.1).ι c.2)
  let jP : ∀ c : J, P c ⟶ L := fun c => pullback.fst _ _ ≫ j _
  let nP : J → ℕ := fun c => n (o c.1).castSucc + c.2
  have sq (c : J) := IsPullback.of_hasPullback (κ c.1) ((fl' c.1).ι c.2)
  have hjP (c : J) : IsSubbundle (jP c) := by
    have := isIso_cokernel_map (sq c)
    exact isSubbundle_comp ⟨inferInstance, _, ((fl' c.1).isVB_cokernel c.2).of_iso
      (asIso (cokernel.map _ _ _ _ (sq c).w)).symm⟩ (hj _)
  have hP (c : J) : IsVB (P c) (nP c) :=
    (VBExt.isVB_and_cls_det_of_shortExact X _ _ _ (shortExact_pullback (sq c) (hS c.1)) (hn _) ((fl' c.1).isVB _)).1
  have lt (c c' : J) (h : o c.1 < o c'.1) : Le (jP c) (jP c') :=
    (Le.trans ⟨_, rfl⟩ (jm (Fin.succ_le_castSucc_iff.2 h))).trans
      ⟨(sq c').lift (s _) 0 (by rw [z, zero_comp]), ((sq c').lift_fst_assoc _ _ _ _).trans (hs _)⟩
  have hle (c c' : J) (h : nP c ≤ nP c') : Le (jP c) (jP c') := by
    rcases lt_trichotomy (o c.1) (o c'.1) with h₁ | h₁ | h₁
    · exact lt _ _ h₁
    · obtain ⟨a, i⟩ := c
      obtain ⟨b, i'⟩ := c'
      obtain rfl : a = b := o.injective h₁
      obtain ⟨v, hv⟩ := flag_le (fl' a) (show i ≤ i' from Nat.le_of_add_le_add_left h)
      exact ⟨(sq ⟨a, i'⟩).lift (pullback.fst _ _) (pullback.snd _ _ ≫ v) (by
        rw [Category.assoc, hv]; exact (sq ⟨a, i⟩).w), (sq ⟨a, i'⟩).lift_fst_assoc _ _ _ _⟩
    · have h₂ := nm (Fin.succ_le_castSucc_iff.2 h₁)
      have h₃ := c'.2.2
      rw [n₁] at h₂
      have h₄ : nP c' = nP c := by simp only [nP] at h ⊢; omega
      exact le_of_rank_eq (hjP c') (hjP c) (h₄ ▸ hP c') (hP c) hL.isVB (lt _ _ h₁)
  obtain ⟨w, hw⟩ := exists_flag hL.isVB jP nP hjP hP hle fun x => by
    obtain ⟨c, rfl⟩ := e.surjective x
    exact ⟨⟨c.1, c.2.succ⟩, by rw [hen]; rfl⟩
  have hsq (c : J) (x) (hx : nP c = x.val) : ∃ f α, IsPullback f α (κ c.1) ((fl' c.1).ι c.2) ∧ f ≫ j _ = w.ι x := by
    obtain ⟨⟨v, hv⟩, v', hv'⟩ := hw c x hx
    have := (hjP c).mono
    let φ : w.F x ≅ P c := ⟨v', v, by rw [← cancel_mono (w.ι x), Category.assoc, hv, hv', Category.id_comp],
      by rw [← cancel_mono (jP c), Category.assoc, hv', hv, Category.id_comp]⟩
    exact ⟨_, _, IsPullback.of_iso_pullback ⟨by rw [Category.assoc, Category.assoc, (sq c).w]⟩ φ rfl rfl,
      (Category.assoc _ _ _).trans hv'⟩
  have hu' (a σ y v v') : bil ((h' a).met σ) y (fib (h a).isVB (h' a).isVB (t a ≫ κ a) y *ᵥ v)
      (fib (h a).isVB (h' a).isVB (t a ≫ κ a) y *ᵥ v') = bil ((h a).met σ) y v v' := by
    simpa only [fib_id] using bil_eq (h a).isVB (h a).isVB (h := (h' a).met σ) (h' := (h a).met σ) (φ' := 𝟙 _)
      (ψ' := 𝟙 _) (y := y) (fun V s t hy => hu a σ V s t y hy) v v'
  have ho (a σ y v) (i : Fin (m + 1)) (hi : i ≤ (o a).castSucc) (v') : bil (hL.met σ) y
      (fib (h a).isVB hL.isVB (t a ≫ j _) y *ᵥ v) (fib (hn i) hL.isVB (j i) y *ᵥ v') = 0 := by
    induction i using Fin.induction with
    | zero => rw [h0.eq_of_src (j 0) 0, fib_zero]; simp [bil, form]
    | succ i ih =>
      obtain ⟨b, rfl⟩ := o.surjective i
      have hab : a ≠ b := fun e => by
        subst e
        exact absurd hi (not_le.2 Fin.castSucc_lt_succ)
      obtain ⟨x, x', rfl⟩ := exists_add (hS b) (hn _) (hn _) (h' b).isVB (h b).isVB
        (surj_of_isometry (hu' b σ y)) v'
      rw [mulVec_add, bil_add_right, fib_comp, fib_comp, hs, ih (Fin.castSucc_le_succ _ |>.trans hi), add_zero]
      rw [bil_eq (h a).isVB (h b).isVB (h := hL.met σ) (h' := hL.met σ) (φ' := 0) (ψ' := 0) fun V s t hy =>
        (hT.2 a b hab σ V s t y hy).trans ?_, fib_zero, fib_zero]
      · simp [bil, form]
      · change _ = (hL.met σ).form 0 0 y
        simp [Met.form, Chart.crd_zero, form]
  refine ⟨_, w, e, hT, ⟨fun a i i' hi => ?_, fun c => ?_⟩, fun c => ?_⟩
  · rw [Fin.lt_def, hen, hen]
    exact Nat.add_lt_add_left hi _
  · obtain ⟨f, α, q, hf⟩ := hsq ⟨c.1, c.2.succ⟩ (e c).succ (by rw [Fin.val_succ, hen]; rfl)
    obtain ⟨v, hv⟩ := hc c.1 c.2.succ
    exact ⟨q.lift ((fl c.1).ι _ ≫ t _) v (by rw [hv, Category.assoc]), by
      rw [← hf, q.lift_fst_assoc, Category.assoc]⟩
  · obtain ⟨f₀, α₀, q₀, hf₀⟩ := hsq ⟨c.1, c.2.castSucc⟩ (e c).castSucc (hen c).symm
    obtain ⟨f₁, α₁, q₁, hf₁⟩ := hsq ⟨c.1, c.2.succ⟩ (e c).succ (by rw [Fin.val_succ, hen]; rfl)
    refine isometric_step HL w (e c) (H' c.1) c.2 (hS c.1) (hn _) (hu c.1) (hc c.1) (fun σ y v v' => ?_)
      (fun σ y v v' => ?_) q₀ hf₀ q₁ hf₁
    · simpa only [fib_id] using bil_eq (h c.1).isVB (h c.1).isVB (h := hL.met σ) (h' := (h c.1).met σ) (φ' := 𝟙 _)
        (ψ' := 𝟙 _) (y := y) (fun V s t hy => hT.1 c.1 σ V s t y hy) v v'
    · rw [hs]
      exact ho _ σ y v _ le_rfl v'

end GlobalTheory.FlagConcat

end
