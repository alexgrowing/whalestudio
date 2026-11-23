import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

universe u v w

namespace CrystallineSemistableComparison.HT

open PAlg

section Gen
variable {O : Type} [CommRing O] {F : B.Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}

theorem pd_pull_eq {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c : Λ →+* b.R} {σ : Λ →+* Λ'} {C' : Type u} [Category.{v} C']
    {F' : C' ⥤ ModuleCat.{w} Λ'} {r : ℕ} (m m' : CH.Mor (B.pdS (F.cr b ht κ) c r).fn F' σ) (η : ∀ T, m.G.obj T ⟶ m'.G.obj T)
    (nat : ∀ {T T' : C'} (f : T ⟶ T') (x : (m.G.obj T).B), (η T').φ ((m.G.map f).φ x) = (m'.G.map f).φ ((η T).φ x))
    (hτ : ∀ (T : C') (x : (m.G.obj T).B) hx hx', m'.τ T ⟨(η T).φ x, hx'⟩ = m.τ T ⟨x, hx⟩) (n : ℕ)
    (x : CH.H (B.pdS (F.cr b ht κ) c r).fn n) : m.pull n x = m'.pull n x :=
  CrystallineSemistableComparison.P.prism m m' ⟨η, fun _ _ f => Thick.Hom.ext (RingHom.ext (nat f)) (funext fun j => j.elim)⟩
    (fun T x => hτ T x.1 x.2 _) n x

end Gen

theorem pd_square {O : Type} [CommRing O] {F₁ F₂ F₃ F₄ : B.Fn O} {b₁ b₂ b₃ b₄ : Base} {h₁ : b₁.t = 1} {h₂ : b₂.t = 1} {h₃ : b₃.t = 1}
    {h₄ : b₄.t = 1} {κ₁ : O →+* b₁.R ⧸ b₁.I} {κ₂ : O →+* b₂.R ⧸ b₂.I} {κ₃ : O →+* b₃.R ⧸ b₃.I} {κ₄ : O →+* b₄.R ⧸ b₄.I}
    {Λ : Type} [CommRing Λ] {c₁ : Λ →+* b₁.R} {c₂ : Λ →+* b₂.R} {c₃ : Λ →+* b₃.R} {c₄ : Λ →+* b₄.R}
    {σa : b₁.R →+* b₂.R} {σb : b₂.R →+* b₄.R} {σc : b₁.R →+* b₃.R} {σd : b₃.R →+* b₄.R} {τ : Λ →+* Λ}
    (ma : Mor (F₁.cr b₁ h₁ κ₁) (F₂.cr b₂ h₂ κ₂) σa) (mb : Mor (F₂.cr b₂ h₂ κ₂) (F₄.cr b₄ h₄ κ₄) σb)
    (mc : Mor (F₁.cr b₁ h₁ κ₁) (F₃.cr b₃ h₃ κ₃) σc) (md : Mor (F₃.cr b₃ h₃ κ₃) (F₄.cr b₄ h₄ κ₄) σd)
    (ha : ∀ a, σa (c₁ a) = c₂ (τ a)) (hb : ∀ a, σb (c₂ a) = c₄ (RingHom.id Λ a)) (hc : ∀ a, σc (c₁ a) = c₃ (RingHom.id Λ a))
    (hd : ∀ a, σd (c₃ a) = c₄ (τ a)) (hσ : ∀ r, σb (σa r) = σd (σc r))
    (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F₄.cr b₄ h₄ κ₄).Pt.obj B₀),
      (ma.pt.app B₀ (mb.pt.app B₀ y)).1.2 = (mc.pt.app B₀ (md.pt.app B₀ y)).1.2)
    (r j : ℕ) (x : CH.H (B.pdS (F₁.cr b₁ h₁ κ₁) c₁ r).fn j) :
    (pdOm (c := c₂) (c' := c₄) mb (RingHom.id Λ) hb r).pull j ((pdOm (c := c₁) (c' := c₂) ma τ ha r).pull j x) =
      (pdOm (c := c₃) (c' := c₄) md τ hd r).pull j ((pdOm (c := c₁) (c' := c₃) mc (RingHom.id Λ) hc r).pull j x) := by
  rw [pull_pull τ, pull_pull τ]
  exact pd_pull_eq _ _ (fun T => crHom (T := ma.obj (mb.obj T)) (T' := mc.obj (md.obj T)) (RingHom.id T.B)
    (fun r => congrArg T.i (hσ r)) (DPMorphism.id T.δ).isDPMorphism fun h => (pt_id _ h _).trans (hpt _ _))
    (fun _ _ => rfl) (fun _ _ _ _ => rfl) j x

theorem pd_id {O : Type} [CommRing O] {F : B.Fn O} {b : Base} {h : b.t = 1} {κ : O →+* b.R ⧸ b.I} {Λ : Type} [CommRing Λ]
    {c : Λ →+* b.R} {σ : b.R →+* b.R} (m : Mor (F.cr b h κ) (F.cr b h κ) σ) (hc : ∀ a, σ (c a) = c (RingHom.id Λ a))
    (hσ : ∀ r, σ r = r) (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F.cr b h κ).Pt.obj B₀), (m.pt.app B₀ y).1.2 = y.1.2)
    (r j : ℕ) (x : CH.H (B.pdS (F.cr b h κ) c r).fn j) : (pdOm (c := c) (c' := c) m (RingHom.id Λ) hc r).pull j x = x :=
  (pd_pull_eq (pdOm (c := c) (c' := c) m (RingHom.id Λ) hc r) (CH.Mor.id _)
    (fun T => crHom (T := m.obj T) (T' := T) (RingHom.id T.B) (fun r => congrArg T.i (hσ r)) (DPMorphism.id T.δ).isDPMorphism
      fun h => (pt_id _ h _).trans (hpt _ _)) (fun _ _ => rfl) (fun _ _ _ _ => rfl) j x).trans
    (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id Λ) (CH.Mor.id _) (CH.Mor.id _) j x).2

theorem pd_om_sh {b b' : Base} {L : b.Fun} {L' : b'.Fun} {σ : b.R →+* b'.R} (m : Mor L L' σ) {Λ : Type} [CommRing Λ]
    {c : Λ →+* b.R} {c' : Λ →+* b'.R} (h : ∀ a, σ (c a) = c' (RingHom.id Λ a)) {t : Λ} (h1 : c t ∈ b.I) (h2 : c' t ∈ b'.I)
    {r r' : ℕ} (k : ℕ) (e : r + k = r') (j : ℕ) (x : CH.H (B.pdS L c r).fn j) :
    (pdOm (c := c) (c' := c') m (RingHom.id Λ) h r').pull j ((pdSh L c h1 k e).pull j x) =
      (pdSh L' c' h2 k e).pull j ((pdOm (c := c) (c' := c') m (RingHom.id Λ) h r).pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  exact congrArg (fun u => (s.obj (Fin.last j)).i u *
    (show (s.obj (Fin.last j)).B from (show (B.pdS L c r).S _ from z.1 (s ⋙ m.functor)).1)) (h (t ^ k))

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section F
variable {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l)

theorem red_gal_pd (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (r n j : ℕ)
    (x : CH.H (B.pdS (B.Lc F κ false (n + 1)) ((base l).cris (n + 1)) r).fn j) :
    (pdOm (CrystallineSemistableComparison.SH.redM F κ false n) (RingHom.id _) (B.red_cris _ n.le_succ) r).pull j
        ((pdOm (CrystallineSemistableComparison.SH.galM F κ σ hσ false (n + 1)) (ACris.galCris σ) (galBase_cris σ (n + 1)) r).pull j x) =
      (pdOm (CrystallineSemistableComparison.SH.galM F κ σ hσ false n) (ACris.galCris σ) (galBase_cris σ n) r).pull j
        ((pdOm (CrystallineSemistableComparison.SH.redM F κ false n) (RingHom.id _) (B.red_cris _ n.le_succ) r).pull j x) :=
  pd_square (CrystallineSemistableComparison.SH.galM F κ σ hσ false (n + 1)) (CrystallineSemistableComparison.SH.redM F κ false n) (CrystallineSemistableComparison.SH.redM F κ false n)
    (CrystallineSemistableComparison.SH.galM F κ σ hσ false n) (galBase_cris σ (n + 1)) (B.red_cris _ n.le_succ) (B.red_cris _ n.le_succ) (galBase_cris σ n)
    (CrystallineSemistableComparison.SH.red_galBase σ n)
    (CrystallineSemistableComparison.SH.base_base F (B.gal_κb κ σ hσ false (n + 1)) (B.red_κb κ false n.le_succ) (B.red_κb κ false n.le_succ)
      (B.gal_κb κ σ hσ false n)) r j x

variable {F} {F' : B.Fn O}

theorem red_pull_pd (u : B.Fn.Map F F') (r n j : ℕ) (x : CH.H (B.pdS (B.Lc F' κ false (n + 1)) ((base l).cris (n + 1)) r).fn j) :
    (pdOm (CrystallineSemistableComparison.SH.redM F κ false n) (RingHom.id _) (B.red_cris _ n.le_succ) r).pull j
        ((pdOm (CrystallineSemistableComparison.SH.pullM κ u false (n + 1)) (RingHom.id _) (CrystallineSemistableComparison.SH.idc _) r).pull j x) =
      (pdOm (CrystallineSemistableComparison.SH.pullM κ u false n) (RingHom.id _) (CrystallineSemistableComparison.SH.idc _) r).pull j
        ((pdOm (CrystallineSemistableComparison.SH.redM F' κ false n) (RingHom.id _) (B.red_cris _ n.le_succ) r).pull j x) :=
  pd_square (CrystallineSemistableComparison.SH.pullM κ u false (n + 1)) (CrystallineSemistableComparison.SH.redM F κ false n) (CrystallineSemistableComparison.SH.redM F' κ false n)
    (CrystallineSemistableComparison.SH.pullM κ u false n) (CrystallineSemistableComparison.SH.idc _) (B.red_cris _ n.le_succ) (B.red_cris _ n.le_succ) (CrystallineSemistableComparison.SH.idc _)
    (fun r => (CrystallineSemistableComparison.SH.idc ((base l).red n.le_succ) r).symm) (CrystallineSemistableComparison.SH.base_map u (B.red_κb κ false n.le_succ)) r j x

end F

variable {M N : Model l K} {r r' j : ℕ}

theorem fam_add (x y : Fam M r j) (n : ℕ) : (x + y) n = x n + y n := rfl

theorem comp_add {x y : Fam M r j} (hx : Comp x) (hy : Comp y) : Comp (x + y) := fun n =>
  (map_add (redS M r n j) (x (n + 1)) (y (n + 1))).trans (congrArg₂ (· + ·) (hx n) (hy n))

theorem comp_smul (c : Acris l) {x : Fam M r j} (hx : Comp x) : Comp (c • x) := fun n =>
  (map_smul (redS M r n j) c (x (n + 1))).trans (congrArg (c • ·) (hx n))

theorem comp_sh (ht : TFil l) (k : ℕ) (h : r + k = r') {x : Fam M r j} (hx : Comp x) : Comp (shS ht k h x) := fun n =>
  (pd_om_sh (CrystallineSemistableComparison.SH.redM (B.schFn M.p) (okToOC l K) false n) (B.red_cris _ n.le_succ) (ht (base l) (n + 1)) (ht (base l) n)
    k h j (x (n + 1))).trans (congrArg ((pdSh (M.L false n) ((base l).cris n) (ht (base l) n) k h).pull j) (hx n))

theorem comp_gal (σ : K.fixingSubgroup) {x : Fam M r j} (hx : Comp x) : Comp (galS σ x) := fun n =>
  (red_gal_pd (B.schFn M.p) (okToOC l K) (IntermediateField.fixingSubgroupEquiv K σ) (galOC_okToOC _) r n j (x (n + 1))).trans
    (congrArg ((pdOm (CrystallineSemistableComparison.SH.galM (B.schFn M.p) (okToOC l K) (IntermediateField.fixingSubgroupEquiv K σ) (galOC_okToOC _) false n)
      (ACris.galCris (IntermediateField.fixingSubgroupEquiv K σ)) (galBase_cris _ n) r).pull j) (hx n))

theorem comp_pull (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) {x : Fam N r j} (hx : Comp x) : Comp (pullS u hu x) := fun n =>
  (red_pull_pd (okToOC l K) (B.schMap u hu) r n j (x (n + 1))).trans
    (congrArg ((pdOm (CrystallineSemistableComparison.SH.pullM (okToOC l K) (B.schMap u hu) false n) (RingHom.id _) (CrystallineSemistableComparison.SH.idc _) r).pull j) (hx n))

end CrystallineSemistableComparison.HT
