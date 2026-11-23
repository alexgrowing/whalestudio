import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsStableBasOfPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LocallyQuasiFiniteOfTrivialOnFibres

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FrameFinite

open GlobalTheory.SecAff GlobalTheory.LN GlobalTheory.ThetaAct GlobalTheory.GeomPointSections GlobalTheory.FrameBasis

theorem top_le {X : Scheme.{0}} {W V : X.Opens} (h : W ≤ V) : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ V := fun t _ => h t.2

theorem pa_ι_bijective {X : Scheme.{0}} (V : X.Opens) : Function.Bijective (pa V.ι (top_le le_rfl)) :=
  pa_bijective V.ι _ le_top (by rw [Scheme.Opens.opensRange_ι])

theorem gm_eq_of_pa {X Z : Scheme.{0}} (q : X ⟶ Z) {W V V' : X.Opens} {U : Z.Opens} (l₁ : W ≤ V) (l₂ : W ≤ V')
    (l₃ : W ≤ q ⁻¹ᵁ U) (u : Γ(X, V)ˣ) (u' : Γ(X, V')ˣ) (g : Γ(Z, U)ˣ) (l₄ : ⊤ ≤ (W.ι ≫ q) ⁻¹ᵁ U)
    (h : pa W.ι (top_le l₁) u.val = pa (W.ι ≫ q) l₄ g.val * pa W.ι (top_le l₂) u'.val) (x : X) (hx : x ∈ W) :
    gm (𝟙 X) x V u = gm (𝟙 X ≫ q) x U g * gm (𝟙 X) x V' u' := by
  have e : rs l₁ u.val = pa q l₃ g.val * rs l₂ u'.val := (pa_ι_bijective W).1 (by
    rw [map_mul, pa_rs, pa_rs, pa_pa q W.ι l₃ _ _ rfl l₄]
    exact h)
  apply Units.ext
  rw [Units.val_mul, ← gs_unit (𝟙 X) x _ (l₁ hx), ← gs_unit (𝟙 X) x _ (l₂ hx), ← gs_unit (𝟙 X ≫ q) x _ (l₃ hx),
    ← gs_res (𝟙 X) x l₁ hx, ← gs_res (𝟙 X) x l₂ hx, ← Geo.Tor.gs_appLE q _ W l₃ (𝟙 X) x hx,
    ← gs_mul (𝟙 X) x W hx]
  exact congrArg (gs (𝟙 X) x W) e

theorem exists_gen_of_affine {X Z : Scheme.{0}} {A : LB Z} (hA : A.IsLB) (q : X ⟶ Z)
    (R : ∀ (T : Scheme.{0}) (_ : T ⟶ X) (_ : A.ι), Γ(T, ⊤) → Prop)
    (ex : ∀ (T : Scheme.{0}) [IsAffine T] (r : T ⟶ X) (i : A.ι), (∀ t, q (r t) ∈ A.U i) → ∃ d, IsUnit d ∧ R T r i d)
    (re : ∀ (T T' : Scheme.{0}) (s : T' ⟶ T) (r : T ⟶ X) i d, R T r i d → R T' (s ≫ r) i (pa s (le_pre_top _) d))
    (cmp : ∀ (T : Scheme.{0}) [IsAffine T] (r : T ⟶ X) i j d d' (h : ⊤ ≤ (r ≫ q) ⁻¹ᵁ (A.U i ⊓ A.U j)),
      R T r i d → R T r j d' → d = pa (r ≫ q) h (A.g i j).val * d') :
    ∃ t : (A.pull q).Gen, t.IsGen := by
  have ex' : ∀ (i : A.ι) (V : {V : X.Opens // IsAffineOpen V ∧ V ≤ (A.pull q).U fun _ => i}),
      ∃ u : Γ(X, V.1)ˣ, R V.1 V.1.ι i (pa V.1.ι (top_le le_rfl) u.val) := fun i V => by
    have : IsAffine V.1 := V.2.1
    obtain ⟨d, hd, hR⟩ := ex V.1 V.1.ι i fun t => mem_pull.1 (V.2.2 t.2)
    obtain ⟨u, rfl⟩ := (pa_ι_bijective V.1).2 d
    obtain ⟨u, rfl⟩ := (MulEquiv.isUnit_map (f := RingEquiv.ofBijective _ (pa_ι_bijective V.1))).1 hd
    exact ⟨u, hR⟩
  choose u hu using ex'
  have key : ∀ i V j V' x, x ∈ V.1 → x ∈ V'.1 →
      gm (𝟙 X) x _ (u i V) = gm (𝟙 X ≫ q) x _ (A.g i j) * gm (𝟙 X) x _ (u j V') := by
    intro i V j V' x hx hx'
    obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := V.1 ⊓ V'.1) ⟨hx, hx'⟩
    have : IsAffine W := hW
    have l₁ : W ≤ V.1 := fun y hy => (hle hy).1
    have l₂ : W ≤ V'.1 := fun y hy => (hle hy).2
    have l₃ : W ≤ q ⁻¹ᵁ (A.U i ⊓ A.U j) := fun y hy => ⟨mem_pull.1 (V.2.2 (l₁ hy)), mem_pull.1 (V'.2.2 (l₂ hy))⟩
    have r₁ := re _ _ (X.homOfLE l₁) _ _ _ (hu i V)
    have r₂ := re _ _ (X.homOfLE l₂) _ _ _ (hu j V')
    rw [pa_pa _ _ _ _ _ (X.homOfLE_ι l₁) (top_le l₁), X.homOfLE_ι] at r₁
    rw [pa_pa _ _ _ _ _ (X.homOfLE_ι l₂) (top_le l₂), X.homOfLE_ι] at r₂
    exact gm_eq_of_pa q l₁ l₂ l₃ _ _ _ (top_le l₃) (cmp _ _ _ _ _ _ _ r₁ r₂) x hxW
  have cov : ∀ i x, x ∈ (A.pull q).U (fun _ => i) →
      ∃ V : {V : X.Opens // IsAffineOpen V ∧ V ≤ (A.pull q).U fun _ => i}, x ∈ V.1 := fun i x hx => by
    obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) hx
    exact ⟨⟨W, hW, hle⟩, hxW⟩
  have gl : ∀ i, ∃ s : Γ(X, (A.pull q).U fun _ => i)ˣ, ∀ V, res V.2.2 s = u i V := fun i =>
    glue_unit _ (fun V : {V : X.Opens // IsAffineOpen V ∧ V ≤ (A.pull q).U fun _ => i} => V.1) (fun V => V.2.2)
      (fun x hx => TopologicalSpace.Opens.mem_iSup.2 (cov i x hx)) (u i) (fun V V' x hx => by
        rw [key i V i V' x hx.1 hx.2, gm_self hA (𝟙 X ≫ q) x (mem_pull.1 (V.2.2 hx.1)), _root_.one_mul])
  choose s hs using gl
  refine ⟨⟨fun J => s (J PUnit.unit)⟩, fun J J' => unit_ext fun x hx => ?_⟩
  obtain ⟨V, hV⟩ := cov (J PUnit.unit) x hx.1
  obtain ⟨V', hV'⟩ := cov (J' PUnit.unit) x hx.2
  have := key _ V _ V' x hV hV'
  rw [← hs, ← hs, gm_res (𝟙 X) x _ hV, gm_res (𝟙 X) x _ hV', ← gm_pull_g A q (𝟙 X) x J J' hx.1 hx.2] at this
  exact (gm_res (𝟙 X) x _ hx _).trans (this.trans
    ((map_mul _ _ _).trans (congrArg _ (gm_res (𝟙 X) x _ hx _))).symm)

section Det

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {a : ℤ} {T T' T₀ T₁ T₂ : Over S} {n : ℕ}

def Det (e : Fin n → SecM A L a T₁) (e₀ : Fin n → SecM A L a T₀) (χ : T ⟶ T₁) (ρ : T ⟶ T₀) (d : Γ(T.left, ⊤)) : Prop :=
  ∃ P : Matrix (Fin n) (Fin n) Γ(T.left, ⊤),
    (∀ k, pull A L a χ (e k) = ∑ l, P k l • pull A L a ρ (e₀ l)) ∧ P.det = d

variable {e : Fin n → SecM A L a T₁} {e₀ : Fin n → SecM A L a T₀} {e' : Fin n → SecM A L a T₂}

theorem exists_det [IsAffine T.left] (he : StableBas e) (he₀ : StableBas e₀) (χ : T ⟶ T₁) (ρ : T ⟶ T₀) :
    ∃ d : Γ(T.left, ⊤)ˣ, Det e e₀ χ ρ d.val := by
  choose P hP using fun k => (((isBas_iff_existsUnique _).1 (he₀ _ ρ)) (pull A L a χ (e k))).exists
  obtain ⟨d, hd⟩ := ((he₀ _ ρ).iff_det (Matrix.of P) hP).1 (he _ χ)
  exact ⟨d, Matrix.of P, hP, hd.symm⟩

theorem Det.comp {χ : T ⟶ T₁} {ρ : T ⟶ T₀} {d} (h : Det e e₀ χ ρ d) (s : T' ⟶ T) {χ' : T' ⟶ T₁} {ρ' : T' ⟶ T₀}
    (h₁ : s ≫ χ = χ') (h₂ : s ≫ ρ = ρ') : Det e e₀ χ' ρ' (pa s.left (le_pre_top _) d) := by
  obtain ⟨P, hP, rfl⟩ := h
  subst h₁ h₂
  refine ⟨(pa s.left (V := ⊤) (le_pre_top _)).mapMatrix P, fun k => ?_, (RingHom.map_det _ _).symm⟩
  rw [← pull_pull, hP, map_sum]
  simp only [map_smulₛₗ, pull_pull]
  rfl

theorem Det.mul [IsAffine T.left] (he₀ : StableBas e₀) {χ : T ⟶ T₁} {ρ : T ⟶ T₀} {χ' : T ⟶ T₂} {d d' m}
    (h : Det e e₀ χ ρ d) (h' : Det e' e₀ χ' ρ d') (hm : Det e e' χ χ' m) : d = m * d' := by
  obtain ⟨P, hP, rfl⟩ := h
  obtain ⟨P', hP', rfl⟩ := h'
  obtain ⟨M, hM, rfl⟩ := hm
  rw [← Matrix.det_mul]
  congr 1
  ext1 k l
  refine congrFun ((((isBas_iff_existsUnique _).1 (he₀ _ ρ)) (pull A L a χ (e k))).unique (hP k) ?_) l
  rw [hM]
  simp only [hP', Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, mul_smul]
  exact Finset.sum_comm

end Det

section Transport

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} {g : A'.left ⟶ A.left}
  [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {w : LB.Iso L' (L.pull g)}

theorem exists_natEquiv (hg : IsPullback g A'.hom A.hom f) (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) (a : ℤ) :
    ∃ Φ : ∀ T : Over S', SecM A' L' a T ≃+ SecM A L a ((Over.map f).obj T),
      (∀ (T : Over S') (c : Γ(T.left, ⊤)) x, Φ T (c • x) = (show Γ(((Over.map f).obj T).left, ⊤) from c) • Φ T x) ∧
      ∀ (T T₀ : Over S') (u : T ⟶ T₀) x, Φ T (pull A' L' a u x) = pull A L a ((Over.map f).map u) (Φ T₀ x) := by
  choose h hi f₁ s₁ using fun T : Over S' =>
    exists_total hg ((Over.map f).obj T) T (𝟙 _) (Category.id_comp _).symm
  choose E hE R using fun T : Over S' =>
    exists_secEquiv hw hL hL' (IsIso.inv_hom_id (h T)) (IsIso.hom_inv_id (h T)) (s₁ T).symm (fun c => c)
      (fun c => congrArg (fun q => q.appTop.hom c) ((f₁ T).trans (Category.comp_id _))) a
  refine ⟨E, hE, fun T T₀ u x => ?_⟩
  have nat : h T ≫ ((Over.map f).map u ▷ A).left = (u ▷ A').left ≫ h T₀ := by
    apply pullback.hom_ext
    · change (h T ≫ ((Over.map f).map u ▷ A).left) ≫ (fst _ A).left =
        ((u ▷ A').left ≫ h T₀) ≫ (fst ((Over.map f).obj T₀) A).left
      rw [Category.assoc, whisker_fst_left, ← Category.assoc, f₁, Category.assoc, Category.assoc, f₁,
        ← Category.assoc (u ▷ A').left, whisker_fst_left]
      simp
    · change (h T ≫ ((Over.map f).map u ▷ A).left) ≫ (snd _ A).left =
        ((u ▷ A').left ≫ h T₀) ≫ (snd ((Over.map f).obj T₀) A).left
      rw [Category.assoc, whisker_snd_left, s₁, Category.assoc, s₁, ← Category.assoc, whisker_snd_left]
  refine Subtype.ext ((R T _).unique_left hL' (IsIso.inv_hom_id (h T)) fun Z r z p q hp hq => ?_)
  rw [gs_pull_apply ((Over.map f).map u) _ (r ≫ h T) z p hp, gs_pull_apply u _ r z q hq, Category.assoc, nat,
    ← Category.assoc, R T₀ x Z (r ≫ (u ▷ A').left) z p q ?_ (chart_le A' L' a u q hq), ← pw_comp]
  · simp only [whisker_snd_left]
  · exact (congrArg (fun φ => φ (r z) ∈ LB.wchart L (fun _ : Fin 1 => (snd ((Over.map f).obj T₀) A).left) p)
      nat).mp (chart_le A L a ((Over.map f).map u) p hp)

theorem exists_frames (hg : IsPullback g A'.hom A.hom f) (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {a : ℤ}
    {κ : Type} {T : κ → Over S'} {n : ℕ} (e : ∀ i, Fin n → SecM A' L' a (T i)) (he : ∀ i, StableBas (e i)) :
    ∃ e' : ∀ i, Fin n → SecM A L a ((Over.map f).obj (T i)), (∀ i, StableBas (e' i)) ∧
      ∀ i j (T' : Over S') (χ : T' ⟶ T i) (ρ : T' ⟶ T j) d, Det (e i) (e j) χ ρ d →
        Det (e' i) (e' j) ((Over.map f).map χ) ((Over.map f).map ρ) d := by
  obtain ⟨Φ, h₁, h₂⟩ := exists_natEquiv hg hw hL hL' a
  refine ⟨fun i k => Φ _ (e i k), fun i T₁ _ u => ?_, ?_⟩
  · let T' : Over S' := Over.mk (Y := T₁.left) (u.left ≫ (T i).hom)
    let u' : T' ⟶ T i := Over.homMk u.left rfl
    have : IsAffine T'.left := ‹IsAffine T₁.left›
    have key : IsBas Γ(T₁.left, ⊤) fun k => pull A L a ((Over.map f).map u') (Φ _ (e i k)) := by
      let E' : SecM A' L' a T' ≃ₗ[Γ(T₁.left, ⊤)] SecM A L a ((Over.map f).obj T') := { Φ T' with map_smul' := h₁ T' }
      obtain ⟨b₁, b₂⟩ := he i T' u'
      have e₁ : (fun k => pull A L a ((Over.map f).map u') (Φ _ (e i k))) =
          E'.toLinearMap ∘ fun k => pull A' L' a u' (e i k) := funext fun k => (h₂ _ _ _ _).symm
      rw [e₁]
      refine ⟨b₁.map' _ E'.ker, ?_⟩
      rw [Set.range_comp, ← Submodule.map_span]
      exact (congrArg (Submodule.map E'.toLinearMap) b₂).trans ((Submodule.map_top _).trans E'.range)
    have gen : ∀ (X : Scheme.{0}) (x x' : X ⟶ S) (_ : x = x') (T₀ : Over S) (v : Over.mk x ⟶ T₀)
        (v' : Over.mk x' ⟶ T₀) (_ : v.left = v'.left) (b : Fin n → SecM A L a T₀),
        IsBas Γ(X, ⊤) (fun k => pull A L a v (b k)) → IsBas Γ(X, ⊤) (fun k => pull A L a v' (b k)) := by
      rintro X x _ rfl T₀ v v' hv b H
      obtain rfl : v = v' := Over.OverMorphism.ext hv
      exact H
    exact gen T₁.left ((u.left ≫ (T i).hom) ≫ f) T₁.hom ((Category.assoc _ _ _).trans (Over.w u)) _
      ((Over.map f).map u') u rfl _ key
  · rintro i j T' χ ρ d ⟨P, hP, rfl⟩
    refine ⟨P, fun k => ?_, rfl⟩
    rw [← h₂, hP]
    exact (map_sum (Φ T').toAddMonoidHom _ _).trans
      (Finset.sum_congr rfl fun l _ => (h₁ _ _ _).trans (congrArg _ (h₂ _ _ _ _)))

end Transport

section Main

variable {Z Y C : Scheme.{0}} {f : Z ⟶ Y} {G : Over Z} {G' : Over Y} {g : G.left ⟶ G'.left}
  [GrpObj G] [GrpObj G'] {L : LB G.left} {L' : LB G'.left} {w : LB.Iso L (L'.pull g)} {N : ℕ}

theorem exists_det_trans (hL : L.IsLB) (A : AmpFrames G L N) (i j : A.A.ι) :
    ∃ c m : Γ((A.A.U i ⊓ A.A.U j).toScheme, ⊤)ˣ,
      Det (fun _ : Fin 1 => SecM.ofSec G (A.th i)) (fun _ : Fin 1 => SecM.ofSec G (A.th j))
        (Over.homMk (Z.homOfLE inf_le_left) (by simp) : Over.mk (A.A.U i ⊓ A.A.U j).ι ⟶ Over.mk (A.A.U i).ι)
        (Over.homMk (Z.homOfLE inf_le_right) (by simp) : Over.mk (A.A.U i ⊓ A.A.U j).ι ⟶ Over.mk (A.A.U j).ι) c.val ∧
      Det (fun k => SecM.ofSec G (A.b i k)) (fun k => SecM.ofSec G (A.b j k))
        (Over.homMk (Z.homOfLE inf_le_left) (by simp) : Over.mk (A.A.U i ⊓ A.A.U j).ι ⟶ Over.mk (A.A.U i).ι)
        (Over.homMk (Z.homOfLE inf_le_right) (by simp) : Over.mk (A.A.U i ⊓ A.A.U j).ι ⟶ Over.mk (A.A.U j).ι) m.val ∧
      pa (A.A.U i ⊓ A.A.U j).ι (top_le le_rfl) (A.A.g i j).val = (c ^ A.r * m ^ A.s).val := by
  obtain ⟨c, M, ⟨t, h₁, h₂⟩, h₃, h₄⟩ := A.trans i j
  refine ⟨c, Matrix.GeneralLinearGroup.det M, ⟨Matrix.of fun _ _ => c.val, fun k => ?_, Matrix.det_fin_one _⟩,
    ⟨M.val, fun k => ?_, rfl⟩, ?_⟩
  · rw [lin_iff hL] at h₁ h₂
    rw [Fin.sum_univ_one, one_smul] at h₁
    exact h₁.symm.trans h₂
  · obtain ⟨t, h₁, h₂⟩ := h₃ k
    rw [lin_iff hL] at h₁ h₂
    rw [Fin.sum_univ_one, one_smul] at h₁
    exact h₁.symm.trans h₂
  · refine Eq.trans ?_ h₄
    have e : (A.A.U i ⊓ A.A.U j).topIso.inv = (A.A.U i ⊓ A.A.U j).ι.appLE (A.A.U i ⊓ A.A.U j) ⊤ (top_le le_rfl) :=
      (Scheme.Opens.ι_appLE (A.A.U i ⊓ A.A.U j) (A.A.U i ⊓ A.A.U j) ⊤ (top_le le_rfl)).symm
    rw [e]; rfl

theorem exists_gen_pull (hg : IsPullback g G.hom G'.hom f) (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    (A : AmpFrames G L N) (s₁ : ∀ i, StableBas fun _ : Fin 1 => SecM.ofSec G (A.th i))
    (s₂ : ∀ i, StableBas fun k => SecM.ofSec G (A.b i k)) (q : C ⟶ Z) (i₀ : A.A.ι) (q₀ : C ⟶ (A.A.U i₀).toScheme)
    (hq : q₀ ≫ (A.A.U i₀).ι ≫ f = q ≫ f) : ∃ t : (A.A.pull q).Gen, t.IsGen := by
  obtain ⟨th, t₁, d₁⟩ := exists_frames hg hw hL' hL _ s₁
  obtain ⟨b, t₂, d₂⟩ := exists_frames hg hw hL' hL _ s₂
  let ρ : ∀ {T : Scheme.{0}} (r : T ⟶ C), Over.mk (r ≫ q ≫ f) ⟶ (Over.map f).obj (Over.mk (A.A.U i₀).ι) :=
    fun r => Over.homMk (r ≫ q₀) ((Category.assoc _ _ _).trans (congrArg (r ≫ ·) hq))
  let χ : ∀ {T : Scheme.{0}} (r : T ⟶ C) {i} (x : T ⟶ (A.A.U i).toScheme), x ≫ (A.A.U i).ι = r ≫ q →
      (Over.mk (r ≫ q ≫ f) ⟶ (Over.map f).obj (Over.mk (A.A.U i).ι)) :=
    fun r _ x hx => Over.homMk x ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ f) hx).trans (Category.assoc _ _ _)))
  refine exists_gen_of_affine A.isLB q
    (fun T r i d => ∃ (x : T ⟶ (A.A.U i).toScheme) (hx : x ≫ (A.A.U i).ι = r ≫ q) (c m : Γ(T, ⊤)ˣ),
      Det (th i) (th i₀) (χ r x hx) (ρ r) c.val ∧ Det (b i) (b i₀) (χ r x hx) (ρ r) m.val ∧
        d = (c ^ A.r * m ^ A.s).val) (fun T _ r i hi => ?_) ?_ ?_
  · have hr : Set.range (r ≫ q) ⊆ Set.range (A.A.U i).ι := by
      rintro _ ⟨y, rfl⟩
      exact ⟨⟨_, hi y⟩, rfl⟩
    have : IsAffine (Over.mk (r ≫ q ≫ f)).left := ‹IsAffine T›
    have hx := IsOpenImmersion.lift_fac _ _ hr
    obtain ⟨c, hc⟩ := exists_det (t₁ i) (t₁ i₀) (χ r _ hx) (ρ r)
    obtain ⟨m, hm⟩ := exists_det (t₂ i) (t₂ i₀) (χ r _ hx) (ρ r)
    exact ⟨_, Units.isUnit _, _, hx, c, m, hc, hm, rfl⟩
  · rintro T T' s r i _ ⟨x, hx, c, m, hc, hm, rfl⟩
    let s' : Over.mk ((s ≫ r) ≫ q ≫ f) ⟶ Over.mk (r ≫ q ≫ f) := Over.homMk s (Category.assoc _ _ _).symm
    let φ : Γ(T, ⊤)ˣ →* Γ(T', ⊤)ˣ := Units.map (pa s (V := ⊤) (le_pre_top _)).toMonoidHom
    have hx' : (s ≫ x) ≫ (A.A.U i).ι = (s ≫ r) ≫ q := by rw [Category.assoc, hx, Category.assoc]
    have e₁ : s' ≫ χ r x hx = χ (s ≫ r) (s ≫ x) hx' := Over.OverMorphism.ext rfl
    have e₂ : s' ≫ ρ r = ρ (s ≫ r) := Over.OverMorphism.ext (Category.assoc _ _ _).symm
    refine ⟨s ≫ x, hx', φ c, φ m, hc.comp s' e₁ e₂, hm.comp s' e₁ e₂, ?_⟩
    rw [← map_zpow, ← map_zpow, ← map_mul]
    rfl
  · rintro T _ r i j _ _ h ⟨x, hx, c, m, hc, hm, rfl⟩ ⟨x', hx', c', m', hc', hm', rfl⟩
    have hr : Set.range (r ≫ q) ⊆ Set.range (A.A.U i ⊓ A.A.U j).ι := by
      rintro _ ⟨y, rfl⟩
      exact ⟨⟨_, h (show y ∈ (⊤ : T.Opens) from trivial)⟩, rfl⟩
    obtain ⟨s, hs⟩ : ∃ s : T ⟶ (A.A.U i ⊓ A.A.U j).toScheme, s ≫ (A.A.U i ⊓ A.A.U j).ι = r ≫ q :=
      ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
    have : IsAffine (Over.mk (r ≫ q ≫ f)).left := ‹IsAffine T›
    obtain ⟨c₀, m₀, k₁, k₂, k₃⟩ := exists_det_trans hL A i j
    let s' : Over.mk (r ≫ q ≫ f) ⟶ (Over.map f).obj (Over.mk (A.A.U i ⊓ A.A.U j).ι) :=
      Over.homMk s ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f) hs).trans (Category.assoc _ _ _)))
    let φ : Γ((A.A.U i ⊓ A.A.U j).toScheme, ⊤)ˣ →* Γ(T, ⊤)ˣ :=
      Units.map (pa s (V := ⊤) (le_pre_top _)).toMonoidHom
    have e₁ : s ≫ Z.homOfLE inf_le_left = x := by
      rw [← cancel_mono (A.A.U i).ι, Category.assoc, Scheme.homOfLE_ι, hs, hx]
    have e₂ : s ≫ Z.homOfLE inf_le_right = x' := by
      rw [← cancel_mono (A.A.U j).ι, Category.assoc, Scheme.homOfLE_ι, hs, hx']
    have a₁ : c = φ c₀ * c' := Units.ext (hc.mul (t₁ i₀) hc' ((d₁ _ _ _ _ _ _ k₁).comp s'
      (Over.OverMorphism.ext e₁) (Over.OverMorphism.ext e₂)))
    have a₂ : m = φ m₀ * m' := Units.ext (hm.mul (t₂ i₀) hm' ((d₂ _ _ _ _ _ _ k₂).comp s'
      (Over.OverMorphism.ext e₁) (Over.OverMorphism.ext e₂)))
    rw [← pa_pa _ s (top_le le_rfl) (le_pre_top _) _ hs h, k₃, a₁, a₂, mul_zpow, mul_zpow, _root_.mul_mul_mul_comm,
      ← map_zpow, ← map_zpow, ← map_mul]
    rfl

end Main

theorem exists_sec_fin {X : Scheme.{0}} {A : LB X} (hA : A.IsLB) (d : ℕ) (s : H0 A d) :
    ∃ s' : LB.Sec (LB.LinComb A (K := Fin d) (fun _ => 𝟙 X) (fun _ => 1)), nonzeroLocus s' = nonzeroLocus s := by
  obtain ⟨s', hs⟩ := exists_sec hA (φ' := fun _ : Fin d => 𝟙 X) (ε' := fun _ => 1) (fun U _ h => by simp) s
  refine ⟨s', TopologicalSpace.Opens.ext (Set.ext fun y => ?_)⟩
  choose J hJ using fun χ : X ⟶ X => exists_chart hA (χ y)
  have hJ' : Geo.Tor.Good A y J := hJ
  exact (mem_nonzeroLocus_iff_isUnit s' (hJ'.mem (fun _ : Fin d => 𝟙 X) (𝟙 X))).trans
    ((congrArg IsUnit (hs X (𝟙 X) y J hJ')).to_iff.trans
      (mem_nonzeroLocus_iff_isUnit s (hJ'.mem (fun _ : Fin 1 => 𝟙 X) (𝟙 X))).symm)

theorem isFinite_of_ampFrames : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z Y : Scheme.{0}) [IsLocallyNoetherian Z] (z : Z ⟶ Sp ℤ) (t : SAB H Z) (t' : SAB H Y) (f : Z ⟶ Y) (_ : SABMap t t' f) (N : ℕ) (_ : GlobalTheory.LN.AmpFrames t.G t.PP.L N), 0 < N → Geo.Tor.IsNormalScheme Z → Flat z → IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → IsProper f → IsFinite f := by
  intro h₁ h₂ E _ _ _ H Z Y _ z t t' f ν N A hN hZ hz hp hA hK hf
  have hL := t.PP.isLB
  have hb := basisAlong_of_ampFrames h₁ h₂ E H Z z t N A hN hZ hz hp hA hK
  have s₁ : ∀ i, StableBas fun _ : Fin 1 => SecM.ofSec t.G (A.th i) := fun i =>
    stableBas_of_traits hL _ (exists_stableBas_local h₂.secBaseChangeAny t hp hA hK 1 le_rfl) fun p =>
      ⟨(A.A.U i).toScheme.presheaf.stalk p, inferInstance, inferInstance, (A.A.U i).toScheme.fromSpecStalk p,
        Scheme.fromSpecStalk_closedPoint, (basisAlong_iff hL _ _ _).1 (hb i _ _).1⟩
  have s₂ : ∀ i, StableBas fun k => SecM.ofSec t.G (A.b i k) := fun i =>
    stableBas_of_traits hL _ (exists_stableBas_local h₂.secBaseChangeAny t hp hA hK N hN) fun p =>
      ⟨(A.A.U i).toScheme.presheaf.stalk p, inferInstance, inferInstance, (A.A.U i).toScheme.fromSpecStalk p,
        Scheme.fromSpecStalk_closedPoint, (basisAlong_iff hL _ _ _).1 (hb i _ _).2⟩
  obtain ⟨w, hw, -⟩ := ν.lin
  have : LocallyQuasiFinite f := by
    refine GlobalTheory.AmpleFibre.locallyQuasiFinite_of_trivial_on_fibres Z Y f A.A hf A.isLB (fun x => ?_) fun k _ _ y C _ i hi => ?_
    · obtain ⟨d, s, -, hs⟩ := A.ample x
      obtain ⟨s', e⟩ := exists_sec_fin A.isLB d s
      exact ⟨d, s', by rw [e]; exact hs⟩
    · have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace (i ≫ pullback.snd f y)
      obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set C)) Set.univ_nonempty
        isClosed_univ.isLocallyClosed
      replace hc : IsClosed {c} := hc
      obtain ⟨x, hx⟩ : ∃ x : Sp k ⟶ C, x ≫ i ≫ pullback.snd f y = 𝟙 _ :=
        ⟨pointOfClosedPoint _ c hc, pointOfClosedPoint_comp _ c hc⟩
      obtain ⟨i₀, hi₀⟩ := exists_chart A.isLB ((x ≫ i ≫ pullback.fst f y) (IsLocalRing.closedPoint k))
      have hr : Set.range (x ≫ i ≫ pullback.fst f y) ⊆ Set.range (A.A.U i₀).ι := by
        rintro _ ⟨u, rfl⟩
        obtain rfl : u = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
        exact ⟨⟨_, hi₀⟩, rfl⟩
      refine exists_gen_pull ν.cart.1 ((isGen_iff w).1 hw) hL t'.PP.isLB A s₁ s₂ _ i₀
        ((i ≫ pullback.snd f y) ≫ IsOpenImmersion.lift _ _ hr) ?_
      rw [Category.assoc, IsOpenImmersion.lift_fac_assoc]
      simp only [Category.assoc, pullback.condition, reassoc_of% hx]
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end GlobalTheory.FrameFinite
