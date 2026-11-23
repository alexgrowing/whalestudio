import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.Descent

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)

theorem res_self {U : X.Opens} (h : U ≤ U) (b : Sec s U) : Sec.res s h b = b :=
  congrArg (fun q ↦ q.hom b) (X.presheaf.map_id (op U))

variable {C D E : Type} [Category.{0} C] [Category.{0} D] [Category.{0} E]

def rm (f : C ⥤ AffOp X) (g : D ⥤ AffOp X) (σ : D ⥤ C)
    (h : ∀ T, (g.obj T).unop.1 ≤ (f.obj (σ.obj T)).unop.1) :
    CoefMap (RingHom.id R) (f ⋙ OAff s) (g ⋙ OAff s) where
  G := σ
  α T := (Sec.res s (h T)).toRingHom
  naturality {T T'} φ b := by
    have h1 := Sec.res_res s (leOfHom (f.map (σ.map φ)).unop) (h T') b
    have h2 := Sec.res_res s (h T) (leOfHom (g.map φ).unop) b
    exact h1.symm.trans h2
  smul T r b := map_smul (Sec.res s (h T)) r b

theorem rm_pull (f : C ⥤ AffOp X) (g : D ⥤ AffOp X) (σ : D ⥤ C) (h) (i : ℕ) (z : Cn (f ⋙ OAff s) i)
    (c : Fin (i + 1) ⥤ D) :
    pulln (rm s f g σ h) i z c = Sec.res s (h (c.obj (Fin.last i))) (z (c ⋙ σ)) := rfl

theorem pull_rm_rm (f : C ⥤ AffOp X) (g : D ⥤ AffOp X) (k : E ⥤ AffOp X) (σ : D ⥤ C) (τ : E ⥤ D) (h h')
    (h'' : ∀ T, (k.obj T).unop.1 ≤ (f.obj ((τ ⋙ σ).obj T)).unop.1) (i : ℕ) (z : Cn (f ⋙ OAff s) i) :
    pulln (rm s g k τ h') i (pulln (rm s f g σ h) i z) = pulln (rm s f k (τ ⋙ σ) h'') i z := by
  funext c
  exact (Sec.res_res s (h _) (h' _) _).symm

theorem pull_rm_id (f : C ⥤ AffOp X) (h) (i : ℕ) (z : Cn (f ⋙ OAff s) i) :
    pulln (rm s f f (𝟭 C) h) i z = z := by
  funext c
  exact res_self s _ _

def aug (f : E ⥤ AffOp X) (W : X.Opens) (hle : ∀ T, (f.obj T).unop.1 ≤ W) :
    Sec s W →ₗ[R] Cn (f ⋙ OAff s) 0 :=
  LinearMap.pi fun c ↦ (Sec.res s (hle (c.obj (Fin.last 0)))).toLinearMap

def Acyc (f : E ⥤ AffOp X) (W : X.Opens) (hle : ∀ T, (f.obj T).unop.1 ≤ W) : Prop :=
  Function.Injective (aug s f W hle) ∧ Function.Exact (aug s f W hle) (dn (f ⋙ OAff s) 0) ∧
    ∀ n, Function.Exact (dn (f ⋙ OAff s) n) (dn (f ⋙ OAff s) (n + 1))

theorem Acyc.congr {f f' : E ⥤ AffOp X} (e : f = f') {W : X.Opens} {hle} {hle'}
    (h : Acyc s f W hle) : Acyc s f' W hle' := by
  subst e; exact h

section Calculus

variable {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}

theorem pull_d (hCx : CxSt) (m : CoefMap (RingHom.id R) F G) (n : ℕ) (z : Cn F n) :
    pulln m (n + 1) (dn F n z) = dn G n (pulln m n z) :=
  LinearMap.congr_fun ((hCx R C F).2 D G m n) z

theorem d_d (hCx : CxSt) (n : ℕ) (z : Cn F n) : dn F (n + 1) (dn F n z) = 0 :=
  LinearMap.congr_fun ((hCx R C F).1 n) z

theorem allQIso_congr {m m' : CoefMap (RingHom.id R) F G} (h : ∀ i z, pulln m i z = pulln m' i z)
    (q : AllQIso m) : AllQIso m' := by
  have e : ∀ i, pulln m i = pulln m' i := fun i ↦ LinearMap.ext (h i)
  unfold AllQIso at q ⊢
  simpa only [e] using q

theorem allQIso_of_inv (hCx : CxSt) (m : CoefMap (RingHom.id R) F G) (m' : CoefMap (RingHom.id R) G F)
    (h : ∀ i z, pulln m' i (pulln m i z) = z) (h' : ∀ i z, pulln m i (pulln m' i z) = z) : AllQIso m := by
  refine ⟨⟨fun x _ ⟨y, hy⟩ ↦ ⟨0, ?_⟩, fun z hz ↦ ⟨pulln m' 0 z, 0, ?_, ?_⟩⟩, fun n ↦
    ⟨fun x _ ⟨y, hy⟩ ↦ ⟨pulln m' n y, ?_⟩, fun z hz ↦ ⟨pulln m' (n + 1) z, 0, ?_, ?_⟩⟩⟩
  · have : pulln m 0 x = 0 := by simpa using hy.symm
    have k := h 0 x
    rw [this, map_zero] at k
    simpa using k
  · rw [← pull_d hCx, hz, map_zero]
  · simp [h']
  · rw [← pull_d hCx, hy, h]
  · rw [← pull_d hCx, hz, map_zero]
  · simp [h']

end Calculus

section Opens

def v₀ (W : X.affineOpens) : Fin 1 →o X.affineOpens := ⟨fun _ ↦ W, monotone_const⟩

def pt (W : X.affineOpens) : (Fin 1)ᵒᵖ ⥤ AffOp X := (v₀ W).monotone.functor.op

theorem acyc_fin (hA : AffAcycSt) {Q : Type} [SemilatticeInf Q] [Finite Q] (v : Q →o X.affineOpens)
    (W : X.affineOpens) (hle : ∀ a, (v a).1 ≤ W.1) (hinf : ∀ a b, (v (a ⊓ b)).1 = (v a).1 ⊓ (v b).1)
    (hcov : ⨆ a, (v a).1 = W.1) : Acyc s v.monotone.functor.op W.1 (fun T ↦ hle T.unop) := by
  have k := hA R X s W Q v hle hinf hcov
  exact k

theorem acyc_pt (hA : AffAcycSt) (W : X.affineOpens) :
    Acyc s (pt W) W.1 (fun _ ↦ le_rfl) :=
  acyc_fin s hA (v₀ W) W (fun _ ↦ le_rfl) (fun _ _ ↦ (inf_idem _).symm)
    (le_antisymm (iSup_le fun _ ↦ le_rfl) (le_iSup (fun a ↦ (v₀ W a).1) 0))

theorem pull_aug (f : D ⥤ AffOp X) (f' : E ⥤ AffOp X) (σ : E ⥤ D) (h) (W : X.Opens) (hle hle')
    (w : Sec s W) :
    pulln (rm s f f' σ h) 0 (aug s f W hle w) = aug s f' W hle' w := by
  funext c
  exact (Sec.res_res s (hle _) (h _) w).symm

theorem d_aug (hCx : CxSt) (hA : AffAcycSt) (f : E ⥤ AffOp X) (W : X.affineOpens) (hle) (w : Sec s W.1) :
    dn (f ⋙ OAff s) 0 (aug s f W.1 hle w) = 0 := by
  have k := pull_aug s (pt W) f ((Functor.const E).obj (op (0 : Fin 1))) hle W.1 (fun _ ↦ le_rfl) hle w
  have z := ((acyc_pt s hA W).2.1 (aug s (pt W) W.1 (fun _ ↦ le_rfl) w)).2 ⟨w, rfl⟩
  rw [← k, ← pull_d hCx, z, map_zero]

theorem acyc_of_map (hCx : CxSt) (hA : AffAcycSt) (f : D ⥤ AffOp X) (f' : E ⥤ AffOp X) (σ : E ⥤ D) (h)
    (W : X.affineOpens) (hle hle')
    (Q1 : ∀ x, dn (f ⋙ OAff s) 0 x = 0 → pulln (rm s f f' σ h) 0 x = 0 → x = 0)
    (Q2 : ∀ n x, dn (f ⋙ OAff s) (n + 1) x = 0 →
      (∃ y, dn (f' ⋙ OAff s) n y = pulln (rm s f f' σ h) (n + 1) x) → ∃ y, dn (f ⋙ OAff s) n y = x)
    (A : Acyc s f' W.1 hle') : Acyc s f W.1 hle := by
  refine ⟨fun a b hab ↦ A.1 ?_, fun x ↦ ⟨fun hx ↦ ?_, ?_⟩, fun n x ↦ ⟨fun hx ↦ ?_, ?_⟩⟩
  · rw [← pull_aug s f f' σ h W.1 hle hle', ← pull_aug s f f' σ h W.1 hle hle', hab]
  · have k : dn (f' ⋙ OAff s) 0 (pulln (rm s f f' σ h) 0 x) = 0 := by
      rw [← pull_d hCx, hx, map_zero]
    obtain ⟨w, hw⟩ := (A.2.1 _).1 k
    refine ⟨w, sub_eq_zero.1 (Q1 _ ?_ ?_)⟩
    · rw [map_sub, d_aug s hCx hA, hx, sub_zero]
    · rw [map_sub, pull_aug s f f' σ h W.1 hle hle', hw, sub_self]
  · rintro ⟨w, rfl⟩
    exact d_aug s hCx hA f W hle w
  · have k : dn (f' ⋙ OAff s) (n + 1) (pulln (rm s f f' σ h) (n + 1) x) = 0 := by
      rw [← pull_d hCx, hx, map_zero]
    exact Q2 n x hx ((A.2.2 n _).1 k)
  · rintro ⟨y, rfl⟩
    exact d_d hCx n y

theorem acyc_of_cone (hCx : CxSt) (hHt : HtpySt) (hA : AffAcycSt) [Quiver.IsThin E] (f : E ⥤ AffOp X)
    (W : X.affineOpens) (hle) (t : E) (ht : W.1 ≤ (f.obj t).unop.1) (e : E ⥤ E)
    (a₁ : ∀ T, T ⟶ e.obj T) (a₂ : ∀ T, t ⟶ e.obj T)
    (he : ∀ T, (f.obj T).unop.1 ≤ (f.obj (e.obj T)).unop.1) : Acyc s f W.1 hle := by
  let c₁ := (Functor.const ((Fin 1)ᵒᵖ)).obj t
  let c₂ := (Functor.const E).obj (op (0 : Fin 1))
  have hc₁ : ∀ T, ((pt W).obj T).unop.1 ≤ (f.obj (c₁.obj T)).unop.1 := fun _ ↦ ht
  have hc₂ : ∀ T, (f.obj T).unop.1 ≤ ((pt W).obj (c₂.obj T)).unop.1 := hle
  have hcc : ∀ T, (f.obj T).unop.1 ≤ (f.obj ((c₂ ⋙ c₁).obj T)).unop.1 := fun T ↦ (hle T).trans ht
  let m₀ := rm s f f (𝟭 E) (fun _ ↦ le_rfl)
  let mₑ := rm s f f e he
  let mc := rm s f f (c₂ ⋙ c₁) hcc
  have H₁ := hHt R E (f ⋙ OAff s) E (f ⋙ OAff s) m₀ mₑ
    { app := a₁, naturality := fun _ _ _ ↦ Subsingleton.elim _ _ }
    (fun T b ↦ (Sec.res_res s _ _ b).symm.trans rfl)
  have H₂ := hHt R E (f ⋙ OAff s) E (f ⋙ OAff s) mc mₑ
    { app := a₂, naturality := fun _ _ _ ↦ Subsingleton.elim _ _ }
    (fun T b ↦ (Sec.res_res s _ _ b).symm.trans rfl)
  have hp : ∀ i z, pulln (rm s (pt W) f c₂ hc₂) i (pulln (rm s f (pt W) c₁ hc₁) i z) = pulln mc i z :=
    fun i z ↦ pull_rm_rm s f (pt W) f c₁ c₂ hc₁ hc₂ hcc i z
  have h₀ : ∀ i z, pulln m₀ i z = z := fun i z ↦ pull_rm_id s f _ i z
  refine acyc_of_map s hCx hA f (pt W) c₁ hc₁ W hle (fun _ ↦ le_rfl) (fun x hx hx' ↦ ?_)
    (fun n x hx ⟨y, hy⟩ ↦ ?_) (acyc_pt s hA W)
  · have k₁ := (H₁.1 x hx).trans (H₂.1 x hx).symm
    rw [h₀, ← hp, hx', map_zero] at k₁
    exact k₁
  · obtain ⟨y₁, e₁⟩ := H₁.2 n x hx
    obtain ⟨y₂, e₂⟩ := H₂.2 n x hx
    refine ⟨pulln (rm s (pt W) f c₂ hc₂) n y + y₁ - y₂, ?_⟩
    rw [map_sub, map_add, ← e₁, ← e₂, ← pull_d hCx, hy, hp, h₀]
    abel

theorem acyc_member (hCx : CxSt) (hHt : HtpySt) (hA : AffAcycSt) {L : Type} [SemilatticeInf L]
    (f : Lᵒᵖ ⥤ AffOp X) (W : X.affineOpens) (hle) (t : L) (ht : W.1 ≤ (f.obj (op t)).unop.1)
    (he : ∀ a, (f.obj (op a)).unop.1 ≤ (f.obj (op (a ⊓ t))).unop.1) : Acyc s f W.1 hle :=
  acyc_of_cone s hCx hHt hA f W hle (op t) ht
    (Monotone.functor (f := fun a : L ↦ a ⊓ t) fun _ _ h ↦ inf_le_inf_right t h).op
    (fun T ↦ (homOfLE inf_le_left).op) (fun T ↦ (homOfLE inf_le_right).op) (fun T ↦ he T.unop)

def pj (f : C ⥤ AffOp X) (w : C × D ⥤ AffOp X) (h : ∀ T, (w.obj T).unop.1 ≤ (f.obj T.1).unop.1) :
    Proj (f ⋙ OAff s) (w ⋙ OAff s) where
  α T := Sec.res s (h T)
  naturality {T T'} φ b := by
    have h1 := Sec.res_res s (leOfHom (f.map φ.1).unop) (h T') b
    have h2 := Sec.res_res s (h T) (leOfHom (w.map φ).unop) b
    exact h1.symm.trans h2

theorem fub (hFub : FubiniSt) [Quiver.IsThin C] [Quiver.IsThin D] (f : C ⥤ AffOp X) (w : C × D ⥤ AffOp X)
    (h : ∀ T, (w.obj T).unop.1 ≤ (f.obj T.1).unop.1)
    (A : ∀ c, Acyc s (CategoryTheory.Prod.sectR c D ⋙ w) (f.obj c).unop.1 (fun T ↦ h (c, T))) :
    AllQIso (rm s f w (CategoryTheory.Prod.fst C D) h) :=
  hFub R C (f ⋙ OAff s) D (w ⋙ OAff s) (pj s f w h) (fun T ↦ A T)

theorem compare (hCx : CxSt) (hQ : QCalcSt) (hFub : FubiniSt) [Quiver.IsThin C] [Quiver.IsThin D]
    (f : C ⥤ AffOp X) (g : D ⥤ AffOp X) (w : C × D ⥤ AffOp X) (σ : D ⥤ C)
    (h₁ : ∀ T, (w.obj T).unop.1 ≤ (f.obj T.1).unop.1) (h₂ : ∀ T, (w.obj T).unop.1 ≤ (g.obj T.2).unop.1)
    (h₃ : ∀ d, (g.obj d).unop.1 ≤ (w.obj (σ.obj d, d)).unop.1)
    (A₁ : ∀ c, Acyc s (CategoryTheory.Prod.sectR c D ⋙ w) (f.obj c).unop.1 (fun T ↦ h₁ (c, T)))
    (A₂ : ∀ d, Acyc s (CategoryTheory.Prod.sectR d C ⋙ CategoryTheory.Prod.swap D C ⋙ w) (g.obj d).unop.1 (fun T ↦ h₂ (T, d))) :
    AllQIso (rm s f g σ (fun d ↦ (h₃ d).trans (h₁ (σ.obj d, d)))) := by
  have Q₁ := fub s hFub f w h₁ A₁
  let w' : D × C ⥤ AffOp X := CategoryTheory.Prod.swap D C ⋙ w
  have h₂' : ∀ T : D × C, (w'.obj T).unop.1 ≤ (g.obj T.1).unop.1 := fun T ↦ h₂ (T.2, T.1)
  have Q₂ := fub s hFub g w' h₂' A₂
  let sc : D ⥤ D × C := (𝟭 D).prod' σ
  have ht : ∀ d, (g.obj d).unop.1 ≤ (w'.obj (sc.obj d)).unop.1 := h₃
  have Qid : AllQIso (rm s g g (𝟭 D) (fun _ ↦ le_rfl)) :=
    allQIso_of_inv hCx _ (rm s g g (𝟭 D) (fun _ ↦ le_rfl))
      (fun i z ↦ by rw [pull_rm_id, pull_rm_id]) (fun i z ↦ by rw [pull_rm_id, pull_rm_id])
  have Qt : AllQIso (rm s w' g sc ht) :=
    ((hQ R D (g ⋙ OAff s) (D × C) D (w' ⋙ OAff s) (g ⋙ OAff s) (rm s g w' (CategoryTheory.Prod.fst D C) h₂')
      (rm s w' g sc ht) (rm s g g (𝟭 D) (fun _ ↦ le_rfl))
      (fun i z ↦ (pull_rm_rm s g w' g (CategoryTheory.Prod.fst D C) sc h₂' ht (fun _ ↦ le_rfl) i z).symm)).2.1 Q₂ Qid)
  have hsw : ∀ T, (w'.obj T).unop.1 ≤ (w.obj ((CategoryTheory.Prod.swap D C).obj T)).unop.1 := fun _ ↦ le_rfl
  have hsw' : ∀ T, (w.obj T).unop.1 ≤ (w'.obj ((CategoryTheory.Prod.swap C D).obj T)).unop.1 := fun _ ↦ le_rfl
  have Qsw : AllQIso (rm s w w' (CategoryTheory.Prod.swap D C) hsw) :=
    allQIso_of_inv hCx _ (rm s w' w (CategoryTheory.Prod.swap C D) hsw')
      (fun i z ↦ (pull_rm_rm s w w' w _ _ hsw hsw' (fun _ ↦ le_rfl) i z).trans (pull_rm_id s w _ i z))
      (fun i z ↦ (pull_rm_rm s w' w w' _ _ hsw' hsw (fun _ ↦ le_rfl) i z).trans (pull_rm_id s w' _ i z))
  have hk₁ : ∀ T, (w'.obj T).unop.1 ≤ (f.obj ((CategoryTheory.Prod.swap D C ⋙ CategoryTheory.Prod.fst C D).obj T)).unop.1 :=
    fun T ↦ h₁ _
  have Qk₁ : AllQIso (rm s f w' (CategoryTheory.Prod.swap D C ⋙ CategoryTheory.Prod.fst C D) hk₁) :=
    ((hQ R C (f ⋙ OAff s) (C × D) (D × C) (w ⋙ OAff s) (w' ⋙ OAff s) (rm s f w (CategoryTheory.Prod.fst C D) h₁)
      (rm s w w' (CategoryTheory.Prod.swap D C) hsw) (rm s f w' (CategoryTheory.Prod.swap D C ⋙ CategoryTheory.Prod.fst C D) hk₁)
      (fun i z ↦ (pull_rm_rm s f w w' _ _ h₁ hsw hk₁ i z).symm)).1 Q₁ Qsw)
  have hk₂ : ∀ T, (g.obj T).unop.1 ≤ (f.obj ((sc ⋙ CategoryTheory.Prod.swap D C ⋙ CategoryTheory.Prod.fst C D).obj T)).unop.1 :=
    fun d ↦ (h₃ d).trans (h₁ (σ.obj d, d))
  exact ((hQ R C (f ⋙ OAff s) (D × C) D (w' ⋙ OAff s) (g ⋙ OAff s)
      (rm s f w' (CategoryTheory.Prod.swap D C ⋙ CategoryTheory.Prod.fst C D) hk₁) (rm s w' g sc ht)
      (rm s f g (sc ⋙ CategoryTheory.Prod.swap D C ⋙ CategoryTheory.Prod.fst C D) hk₂)
      (fun i z ↦ (pull_rm_rm s f w' g _ _ hk₁ ht hk₂ i z).symm)).1 Qk₁ Qt)

end Opens

section Meet

variable (hi : ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1))

def meet (U V : X.affineOpens) : X.affineOpens := ⟨U.1 ⊓ V.1, hi U V⟩

theorem meet_le {U U' V V' : X.affineOpens} (h : U.1 ≤ U'.1) (h' : V.1 ≤ V'.1) :
    meet hi U V ≤ meet hi U' V' := by
  change U.1 ⊓ V.1 ≤ U'.1 ⊓ V'.1
  exact inf_le_inf h h'

theorem meet_le_left (U V : X.affineOpens) : meet hi U V ≤ U := by
  change U.1 ⊓ V.1 ≤ U.1
  exact inf_le_left

theorem meet_le_right (U V : X.affineOpens) : meet hi U V ≤ V := by
  change U.1 ⊓ V.1 ≤ V.1
  exact inf_le_right

def wFun (f : C ⥤ AffOp X) (g : D ⥤ AffOp X) : C × D ⥤ AffOp X where
  obj T := op (meet hi (f.obj T.1).unop (g.obj T.2).unop)
  map {T T'} φ := (homOfLE (show meet hi (f.obj T'.1).unop (g.obj T'.2).unop ≤
    meet hi (f.obj T.1).unop (g.obj T.2).unop by
      change (f.obj T'.1).unop.1 ⊓ (g.obj T'.2).unop.1 ≤ (f.obj T.1).unop.1 ⊓ (g.obj T.2).unop.1
      exact inf_le_inf (leOfHom (f.map φ.1).unop) (leOfHom (g.map φ.2).unop))).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

theorem exists_finite_cover {P : Type} (v : P → X.affineOpens) (W : X.affineOpens)
    (hcov : ⨆ a, (v a).1 = W.1) : ∃ T : Finset P, W.1 ≤ ⨆ a : T, (v a.1).1 := by
  obtain ⟨T, hT⟩ := W.2.isCompact.elim_finite_subcover (fun a ↦ ((v a).1 : Set X))
    (fun a ↦ (v a).1.isOpen) (by
      intro x hx
      have : x ∈ ((⨆ a, (v a).1 : X.Opens) : Set X) := by rw [hcov]; exact hx
      simpa [TopologicalSpace.Opens.coe_iSup] using this)
  refine ⟨T, fun x hx ↦ ?_⟩
  have := hT hx
  simpa [TopologicalSpace.Opens.coe_iSup] using this

include hi in
theorem acyc_of_cover (hCx : CxSt) (hHt : HtpySt) (hQ : QCalcSt) (hFub : FubiniSt) (hA : AffAcycSt)
    {P : Type} [SemilatticeInf P] (v : P →o X.affineOpens)
    (hinf : ∀ a b, (v (a ⊓ b)).1 = (v a).1 ⊓ (v b).1) (W : X.affineOpens) (hle : ∀ a, (v a).1 ≤ W.1)
    (hcov : ⨆ a, (v a).1 = W.1) :
    Acyc s v.monotone.functor.op W.1 (fun T ↦ hle T.unop) := by
  obtain ⟨T, hT⟩ := exists_finite_cover v W hcov
  let Q : Set P := infClosure (T : Set P)
  letI : SemilatticeInf Q := Subtype.semilatticeInf (fun x y hx hy ↦ infClosed_infClosure hx hy)
  haveI : Finite Q := (T.finite_toSet.infClosure).to_subtype
  let vQ : Q →o X.affineOpens := ⟨fun q ↦ v q.1, fun a b h ↦ v.monotone h⟩
  have hleQ : ∀ a, (vQ a).1 ≤ W.1 := fun a ↦ hle a.1
  have hinfQ : ∀ a b, (vQ (a ⊓ b)).1 = (vQ a).1 ⊓ (vQ b).1 := fun a b ↦ hinf a.1 b.1
  have hcovQ' : W.1 ≤ ⨆ a, (vQ a).1 := hT.trans (iSup_le fun a ↦
    le_iSup (fun q : Q ↦ (vQ q).1) ⟨a.1, subset_infClosure a.2⟩)
  have hcovQ : ⨆ a, (vQ a).1 = W.1 := le_antisymm (iSup_le hleQ) hcovQ'
  let fP : Pᵒᵖ ⥤ AffOp X := v.monotone.functor.op
  let fQ : Qᵒᵖ ⥤ AffOp X := vQ.monotone.functor.op
  let σ : Qᵒᵖ ⥤ Pᵒᵖ := (Subtype.mono_coe _ : Monotone (Subtype.val : Q → P)).functor.op
  let w := wFun hi fP fQ
  have h₁ : ∀ T, (w.obj T).unop.1 ≤ (fP.obj T.1).unop.1 := fun _ ↦ inf_le_left
  have h₂ : ∀ T, (w.obj T).unop.1 ≤ (fQ.obj T.2).unop.1 := fun _ ↦ inf_le_right
  have h₃ : ∀ d, (fQ.obj d).unop.1 ≤ (w.obj (σ.obj d, d)).unop.1 := fun _ ↦ le_inf le_rfl le_rfl
  have hr := compare s hCx hQ hFub fP fQ w σ h₁ h₂ h₃ (fun c ↦ ?_) (fun d ↦ ?_)
  · exact acyc_of_map s hCx hA fP fQ σ _ W _ (fun T ↦ hleQ T.unop)
      (fun x hx hx' ↦ by
        obtain ⟨y, hy⟩ := hr.1.1 x hx ⟨0, by rw [hx', map_zero]⟩
        simpa using hy.symm)
      (fun n x hx hy ↦ (hr.2 n).1 x hx hy)
      (acyc_fin s hA vQ W hleQ hinfQ hcovQ)
  · let v' : Q →o X.affineOpens :=
      ⟨fun q ↦ meet hi (v c.unop) (vQ q), fun a b h ↦ meet_le hi le_rfl (vQ.monotone h)⟩
    have hle' : ∀ q, (v' q).1 ≤ (v c.unop).1 := fun _ ↦ inf_le_left
    have hinf' : ∀ a b, (v' (a ⊓ b)).1 = (v' a).1 ⊓ (v' b).1 := fun a b ↦ by
      change (v c.unop).1 ⊓ (vQ (a ⊓ b)).1 = ((v c.unop).1 ⊓ (vQ a).1) ⊓ ((v c.unop).1 ⊓ (vQ b).1)
      rw [hinfQ, inf_inf_distrib_left]
    have hcov' : ⨆ a, (v' a).1 = (v c.unop).1 := by
      refine le_antisymm (iSup_le hle') ?_
      change _ ≤ ⨆ a, (v c.unop).1 ⊓ (vQ a).1
      rw [← inf_iSup_eq]
      exact le_inf le_rfl ((hle _).trans hcovQ')
    exact (acyc_fin s hA v' (v c.unop) hle' hinf' hcov').congr s
      (CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _))
  · refine acyc_member s hCx hHt hA _ (vQ d.unop) _ d.unop.1 (le_inf le_rfl le_rfl) (fun a ↦ ?_)
    change (v a).1 ⊓ (vQ d.unop).1 ≤ (v (a ⊓ d.unop.1)).1 ⊓ (vQ d.unop).1
    rw [hinf]
    exact le_inf (le_inf inf_le_left inf_le_right) inf_le_right

include hi in
theorem resSys_qiso (hCx : CxSt) (hHt : HtpySt) (hQ : QCalcSt) (hFub : FubiniSt) (hA : AffAcycSt)
    {P : Type} [SemilatticeInf P] (S : Sys X P) : AllQIso (resSys s S) := by
  let f : AffOp X ⥤ AffOp X := 𝟭 _
  let w := wFun hi f S.fn
  have h₁ : ∀ T, (w.obj T).unop.1 ≤ (f.obj T.1).unop.1 := fun _ ↦ inf_le_left
  have h₂ : ∀ T, (w.obj T).unop.1 ≤ (S.fn.obj T.2).unop.1 := fun _ ↦ inf_le_right
  have h₃ : ∀ d, (S.fn.obj d).unop.1 ≤ (w.obj (S.fn.obj d, d)).unop.1 := fun _ ↦ le_inf le_rfl le_rfl
  have hr := compare s hCx hQ hFub f S.fn w S.fn h₁ h₂ h₃ (fun U ↦ ?_) (fun a ↦ ?_)
  · exact allQIso_congr (fun i z ↦ funext fun c ↦ res_self s _ _) hr
  · let v' : P →o X.affineOpens :=
      ⟨fun a ↦ meet hi U.unop (S.u a), fun a b h ↦ meet_le hi le_rfl (S.mono h)⟩
    have hle' : ∀ a, (v' a).1 ≤ U.unop.1 := fun _ ↦ inf_le_left
    have hinf' : ∀ a b, (v' (a ⊓ b)).1 = (v' a).1 ⊓ (v' b).1 := fun a b ↦ by
      change U.unop.1 ⊓ (S.u (a ⊓ b)).1 = (U.unop.1 ⊓ (S.u a).1) ⊓ (U.unop.1 ⊓ (S.u b).1)
      rw [S.map_inf, inf_inf_distrib_left]
    have hcov' : ⨆ a, (v' a).1 = U.unop.1 := by
      refine le_antisymm (iSup_le hle') ?_
      change _ ≤ ⨆ a, U.unop.1 ⊓ (S.u a).1
      rw [← inf_iSup_eq, S.cover, inf_top_eq]
    exact (acyc_of_cover s hi hCx hHt hQ hFub hA v' hinf' U.unop hle' hcov').congr s
      (CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _))
  · refine acyc_of_cone s hCx hHt hA _ (S.fn.obj a).unop _ (S.fn.obj a) (le_inf le_rfl le_rfl)
      (CategoryTheory.Prod.sectR (S.fn.obj a) (AffOp X) ⋙ CategoryTheory.Prod.swap _ _ ⋙
        wFun hi (𝟭 _) (𝟭 _)) (fun T ↦ (homOfLE (meet_le_left hi T.unop _)).op) (fun T ↦ (homOfLE (meet_le_right hi T.unop _)).op)
      (fun T ↦ ?_)
    exact le_inf (le_inf inf_le_left inf_le_right) inf_le_right

end Meet

theorem isAffineOpen_inf (hs : IsSeparated s) (U V : X.affineOpens) : IsAffineOpen (U.1 ⊓ V.1) := by
  haveI : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from s]
    infer_instance⟩
  exact U.2.inf V.2

theorem descentSt : CxSt → HtpySt → QCalcSt → FubiniSt → AffAcycSt → DescentSt :=
  fun hCx hHt hQ hFub hA R _ X s hs P _ S ↦
    resSys_qiso s (isAffineOpen_inf s hs) hCx hHt hQ hFub hA S

end GlobalTheory.CompanionTheory.Descent
