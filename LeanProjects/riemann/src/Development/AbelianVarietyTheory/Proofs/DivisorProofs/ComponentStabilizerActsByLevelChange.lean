import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrMoveTransfer
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculusStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompLevelStab

theorem mem_iff_of_inv {X : Scheme.{0}} (Z : Set X) (hZ : IsClopen Z) (hI : IsIrreducible Z) (f g : X ⟶ X)
    (hfg : f ≫ g = 𝟙 X) (x : X) (hx : x ∈ Z) (hfx : f.base x ∈ Z) (y : X) : f.base y ∈ Z ↔ y ∈ Z := by
  have hgf : ∀ z, g.base (f.base z) = z := fun z => by
    have := congrArg (fun h : X ⟶ X => h.base z) hfg
    simpa using this
  have A : f.base '' Z ⊆ Z :=
    (hI.image _ f.continuous.continuousOn).isPreirreducible.isPreconnected.subset_isClopen hZ ⟨_, ⟨x, hx, rfl⟩, hfx⟩
  have B : g.base '' Z ⊆ Z :=
    (hI.image _ g.continuous.continuousOn).isPreirreducible.isPreconnected.subset_isClopen hZ
      ⟨_, ⟨f.base x, hfx, rfl⟩, by rw [hgf]; exact hx⟩
  exact ⟨fun h => hgf y ▸ B ⟨_, h, rfl⟩, fun h => A ⟨y, h, rfl⟩⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

section Moves

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Xo : Moduli Dw l)

def mv (γ : LevelAut Dw l) : Xo.X ⟶ Xo.X := (GlobalTheory.LevelActionLaws.exists_move hpq hA Xo γ).choose

theorem mv_spec (γ : LevelAut Dw l) : ∃ ν : SABMap Xo.univ.t Xo.univ.t (mv hpq hA Xo γ),
    IsIso (mv hpq hA Xo γ) ∧ IsLevMove (mv hpq hA Xo γ) ν (liftLa γ) LinearMap.id :=
  (GlobalTheory.LevelActionLaws.exists_move hpq hA Xo γ).choose_spec

theorem x_move (c : Coeff l) (γ : LevelAut Dw l) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    (move Xo c γ y).x = y.x ≫ mv hpq hA Xo γ := by
  obtain ⟨ν, i, h⟩ := mv_spec hpq hA Xo γ
  exact (GlobalTheory.LevelActionLaws.frMove_transfer hpq hA Xo c γ i h (GlobalTheory.LevDesc.levR_move hpq hA γ y)).1

theorem mv_over (γ : LevelAut Dw l) : mv hpq hA Xo γ ≫ Xo.s = Xo.s := by
  obtain ⟨ν, i, h⟩ := mv_spec hpq hA Xo γ
  exact h.1

theorem mv_mul (c : Coeff l) (γ δ : LevelAut Dw l) : mv hpq hA Xo (γ * δ) = mv hpq hA Xo γ ≫ mv hpq hA Xo δ := by
  obtain ⟨ν, i, h⟩ := mv_spec hpq hA Xo γ
  obtain ⟨ν', i', h'⟩ := mv_spec hpq hA Xo δ
  obtain ⟨ν₂, i₂, h₂⟩ := mv_spec hpq hA Xo (γ * δ)
  obtain ⟨μ, hμ, -⟩ := (GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c).2.1 _ _ ν ν'
  have hc : IsLevMove (mv hpq hA Xo γ ≫ mv hpq hA Xo δ) μ (liftLa (γ * δ)) LinearMap.id := by
    refine ⟨?_, fun a => ?_, fun a => ?_⟩
    · rw [Category.assoc, h'.1, h.1]
    · rw [GlobalTheory.LevelActionLaws.eta_congr Xo (GlobalTheory.LevelActionLaws.liftLa_mul_sub γ δ a), hμ, ← Category.assoc, h.2.1,
        Category.assoc, h'.2.1, Category.assoc]
    · have e : (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a = (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) ((LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a) := rfl
      rw [e, hμ, ← Category.assoc, h.2.2, Category.assoc, h'.2.2, Category.assoc]
  exact (GlobalTheory.LevelActionLaws.move_unique hpq hA Xo c (γ * δ) i₂ inferInstance h₂ hc).1

theorem mv_one (c : Coeff l) : mv hpq hA Xo 1 = 𝟙 Xo.X := by
  obtain ⟨ν, i, h⟩ := mv_spec hpq hA Xo 1
  obtain ⟨ι, hι, -⟩ := (GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c).1
  have hc : IsLevMove (𝟙 Xo.X) ι (liftLa (1 : LevelAut Dw l)) LinearMap.id := by
    refine ⟨Category.id_comp _, fun a => ?_, fun a => ?_⟩
    · rw [hι, Category.comp_id, Category.id_comp]
      exact congrArg _ (GlobalTheory.LevelActionLaws.eta_congr Xo (GlobalTheory.LevelActionLaws.liftLa_one_sub a))
    · rw [hι, Category.comp_id, Category.id_comp]
      rfl
  exact (GlobalTheory.LevelActionLaws.move_unique hpq hA Xo c 1 i inferInstance h hc).1

end Moves

section Base

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Xo : Moduli Dw l) (c : Coeff l)

def mvF (γ : LevelAut Dw l) : Xo.XF c ⟶ Xo.XF c :=
  pullback.lift (pullback.fst _ _ ≫ mv hpq hA Xo γ) (pullback.snd _ _) (by
    rw [Category.assoc, mv_over, pullback.condition])

theorem mvF_fst (γ : LevelAut Dw l) : mvF hpq hA Xo c γ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ mv hpq hA Xo γ :=
  pullback.lift_fst _ _ _

theorem mvF_snd (γ : LevelAut Dw l) : mvF hpq hA Xo c γ ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

theorem mvF_mul (γ δ : LevelAut Dw l) : mvF hpq hA Xo c (γ * δ) = mvF hpq hA Xo c γ ≫ mvF hpq hA Xo c δ := by
  apply pullback.hom_ext
  · rw [mvF_fst, Category.assoc, mvF_fst, ← Category.assoc, mvF_fst, Category.assoc, mv_mul hpq hA Xo c]
  · rw [mvF_snd, Category.assoc, mvF_snd, mvF_snd]

theorem mvF_one : mvF hpq hA Xo c 1 = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [mvF_fst, mv_one hpq hA Xo c, Category.comp_id, Category.id_comp]
  · rw [mvF_snd, Category.id_comp]

theorem mvF_inv_comp (γ : LevelAut Dw l) : mvF hpq hA Xo c γ⁻¹ ≫ mvF hpq hA Xo c γ = 𝟙 _ := by
  rw [← mvF_mul, inv_mul_cancel, mvF_one]

theorem mvF_comp_inv (γ : LevelAut Dw l) : mvF hpq hA Xo c γ ≫ mvF hpq hA Xo c γ⁻¹ = 𝟙 _ := by
  rw [← mvF_mul, mul_inv_cancel, mvF_one]

theorem ptF_move (γ : LevelAut Dw l) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    ptF (move Xo c γ y) = ptF y ≫ mvF hpq hA Xo c γ := by
  apply pullback.hom_ext
  · rw [Category.assoc, mvF_fst, ← Category.assoc]
    simp only [ptF, pullback.lift_fst]
    exact x_move hpq hA Xo c γ y
  · rw [Category.assoc, mvF_snd]
    simp only [ptF, pullback.lift_snd]

variable (Z : Comp Xo c)

def stab : Subgroup (LevelAut Dw l) where
  carrier := {h | ∀ x, (mvF hpq hA Xo c h⁻¹).base x ∈ (Z : Set (Xo.XF c)) ↔ x ∈ (Z : Set (Xo.XF c))}
  one_mem' := fun x => by rw [inv_one, mvF_one]; rfl
  mul_mem' := by
    intro a b ha hb x
    rw [Set.mem_setOf_eq] at ha hb
    rw [mul_inv_rev, mvF_mul, Scheme.Hom.comp_apply, ha, hb]
  inv_mem' := by
    intro a ha x
    rw [Set.mem_setOf_eq] at ha
    have e : (mvF hpq hA Xo c a⁻¹).base ((mvF hpq hA Xo c a).base x) = x := by
      have := congrArg (fun f : Xo.XF c ⟶ Xo.XF c => f.base x) (mvF_comp_inv hpq hA Xo c a)
      simpa using this
    rw [inv_inv, ← ha, e]

end Base

section Restrict

variable {hpq : 1 ≤ Dw.p + Dw.q} {hA : l.A.Coprime l.M} {Xo : Moduli Dw l} {c : Coeff l}
  (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c)

theorem mem_V₀ (x : Xo.XF c) : x ∈ Y.j ⁻¹ᵁ barComp Y Z ↔ x ∈ (Z : Set (Xo.XF c)) := j_mem_barComp Z x

theorem le_V₀ (g : LevelAut Dw l) (hg : ∀ x, (mvF hpq hA Xo c g).base x ∈ (Z : Set (Xo.XF c)) ↔ x ∈ (Z : Set (Xo.XF c))) :
    Y.j ⁻¹ᵁ barComp Y Z ≤ mvF hpq hA Xo c g ⁻¹ᵁ (Y.j ⁻¹ᵁ barComp Y Z) := fun x hx =>
  (mem_V₀ Y Z _).2 ((hg x).2 ((mem_V₀ Y Z x).1 hx))

theorem inv_mem_stab {h : LevelAut Dw l} (hh : h ∈ stab hpq hA Xo c Z) :
    ∀ x, (mvF hpq hA Xo c h).base x ∈ (Z : Set (Xo.XF c)) ↔ x ∈ (Z : Set (Xo.XF c)) := by
  have h2 := (stab hpq hA Xo c Z).inv_mem hh
  change ∀ x, (mvF hpq hA Xo c h⁻¹⁻¹).base x ∈ (Z : Set (Xo.XF c)) ↔ x ∈ (Z : Set (Xo.XF c)) at h2
  simpa only [inv_inv] using h2

def resAut (h : LevelAut Dw l) (hh : h ∈ stab hpq hA Xo c Z) : Aut (V₀ Y Z) where
  hom := (mvF hpq hA Xo c h⁻¹).resLE _ _ (le_V₀ Y Z h⁻¹ hh)
  inv := (mvF hpq hA Xo c h).resLE _ _ (le_V₀ Y Z h (inv_mem_stab Z hh))
  hom_inv_id := by
    rw [← cancel_mono (Y.j ⁻¹ᵁ barComp Y Z).ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, mvF_inv_comp, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    rw [← cancel_mono (Y.j ⁻¹ᵁ barComp Y Z).ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, mvF_comp_inv, Category.comp_id, Category.id_comp]

theorem resAut_ι (h : LevelAut Dw l) (hh : h ∈ stab hpq hA Xo c Z) :
    (resAut Y Z h hh).hom ≫ i₀ Y Z = i₀ Y Z ≫ mvF hpq hA Xo c h⁻¹ :=
  Scheme.Hom.resLE_comp_ι _ _

def resHom (S : Subgroup (LevelAut Dw l)) : ↥(S ⊓ stab hpq hA Xo c Z) →* Aut (V₀ Y Z) :=
  MonoidHom.mk' (fun g => resAut Y Z g.1 (Subgroup.mem_inf.1 g.2).2) fun a b => by
    apply Iso.ext
    rw [Aut.Aut_mul_def]
    change (resAut Y Z (a * b).1 (Subgroup.mem_inf.1 (a * b).2).2).hom =
      (resAut Y Z b.1 (Subgroup.mem_inf.1 b.2).2).hom ≫ (resAut Y Z a.1 (Subgroup.mem_inf.1 a.2).2).hom
    rw [← cancel_mono (i₀ Y Z), Category.assoc, resAut_ι, resAut_ι,
      ← Category.assoc, resAut_ι, Category.assoc, ← mvF_mul, Subgroup.coe_mul, mul_inv_rev]

theorem j₀_s₀ : j₀ Y Z ≫ s₀ Y Z = i₀ Y Z ≫ pullback.snd _ _ ≫ spMap (RingHom.id c.F) := by
  show j₀ Y Z ≫ (barComp Y Z).ι ≫ Y.s = _
  rw [← Category.assoc, j₀_ι, Category.assoc, Model.j, Category.assoc, pullback.condition, ← Category.assoc Y.jQ,
    Y.jQ_over]

end Restrict

theorem stab_acts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ S : Subgroup (LevelAut Dw l), ∃ (Γ : Subgroup (LevelAut Dw l)) (ρ : Γ →* Aut (V₀ Y Z)), Γ ≤ S ∧ ActsBy Γ.subtype ρ ∧ ∀ h ∈ S, ∀ y : FrPt Xo c ℂ, LiesOn Z y → LiesOn Z (move Xo c h⁻¹ y) → h ∈ Γ := by
  intro E _ _ _ H Dw l Xo c Y Z hpq hl S
  have hA : l.A.Coprime l.M := by rw [hl]; exact Nat.coprime_one_left _
  refine ⟨S ⊓ stab hpq hA Xo c Z, resHom (hpq := hpq) (hA := hA) Y Z S, inf_le_left, ⟨fun g => ?_, ?_⟩, ?_⟩
  · show (resAut Y Z g.1 (Subgroup.mem_inf.1 g.2).2).hom ≫ j₀ Y Z ≫ s₀ Y Z = j₀ Y Z ≫ s₀ Y Z
    rw [j₀_s₀, ← Category.assoc, resAut_ι, Category.assoc, ← Category.assoc (mvF _ _ _ _ _), mvF_snd]
  · intro g R _ _ y v hv
    show v ≫ (resAut Y Z g.1 (Subgroup.mem_inf.1 g.2).2).hom ≫ i₀ Y Z = _
    rw [resAut_ι, ← Category.assoc, hv, ← ptF_move]
    rfl
  · intro h hS y hy hy'
    refine Subgroup.mem_inf.2 ⟨hS, ?_⟩
    let pt : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
    have h1 := hy' pt
    rw [ptF_move hpq hA Xo c, Scheme.Hom.comp_apply] at h1
    exact mem_iff_of_inv _ (TrivOrderTieCompare.isClopen_comp Z) Z.2.1 (mvF hpq hA Xo c h⁻¹) (mvF hpq hA Xo c h)
      (mvF_inv_comp hpq hA Xo c h) _ (hy pt) h1

end GlobalTheory.CompLevelStab
