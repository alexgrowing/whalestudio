import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem val_sub_pull {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {Y Y' : Scheme.{0}}
    {t : Y ⟶ Sp R} {t' : Y' ⟶ Sp R'} {φ : Y' ⟶ Y} (m : IsMor (dp0 R) t (dp0 R') t' σ φ)
    (E : SqExt R) (E' : SqExt R') (ρ : E.C →+* E'.C) (ρ₀ : E.B →+* E'.B)
    (hρ : ∀ r, ρ (algebraMap R E.C r) = algebraMap R' E'.C (σ r))
    (hρ₀ : ∀ r, ρ₀ (algebraMap R E.B r) = algebraMap R' E'.B (σ r))
    (hπ : ∀ c, ρ₀ (E.π c) = E'.π (ρ c)) (hi : ∀ b, ρ (E.i b) = E'.i (ρ₀ b))
    {T₀ : Thick (dp0 R) t} {T₀' : Thick (dp0 R') t'} (a : T₀ ⟶ m.obj T₀')
    (z : Sp E.C ⟶ Y) (hz : z ≫ t = spMap (algebraMap R E.C))
    (z' : Sp E'.C ⟶ Y') (hz' : z' ≫ t' = spMap (algebraMap R' E'.C))
    (τ : T₀ ⟶ Thick.triv E.C z hz) (τ' : T₀' ⟶ Thick.triv E'.C z' hz')
    (h : ∀ c, ρ (τ.φ c) = τ'.φ (a.φ c)) (f : Z1 (O (dp0 R) t)) :
    ∃ b : E'.B, E'.val z' hz' (m.coef.pullbackOneCocycle f) - ev (m.coef.pullbackOneCocycle f) τ' =
      ρ (E.val z hz f - ev f τ) + τ'.φ (ev f a) - E'.i b := by
  have e : spMap ρ ≫ z = z' ≫ φ := by
    let u : T₀.B₀ →+* E.C := τ.φ₀
    let u' : T₀'.B₀ →+* E'.C := τ'.φ₀
    let a₀ : T₀.B₀ →+* T₀'.B₀ := a.φ₀
    have h1 : spMap u ≫ T₀.x = z := τ.pt
    have h2 : spMap u' ≫ T₀'.x = z' := τ'.pt
    have h3 : spMap a₀ ≫ T₀.x = T₀'.x ≫ φ := a.pt
    rw [← h1, ← h2, Category.assoc, ← h3, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 2
    refine RingHom.ext fun c ↦ ?_
    obtain ⟨c, rfl⟩ := T₀.surj c
    exact (congrArg ρ (τ.comm c)).trans ((h c).trans
      ((τ'.comm (a.φ c)).symm.trans (congrArg τ'.φ₀ (a.comm c).symm)))
  have e₀ : spMap ρ₀ ≫ spMap (E.π : E.C →+* E.B) ≫ z = (spMap (E'.π : E'.C →+* E'.B) ≫ z') ≫ φ := by
    rw [Category.assoc, ← e, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 2
    exact RingHom.ext hπ
  let Φ : E.thick _ (E.red_w hz) ⟶ m.obj (E'.thick _ (E'.red_w hz')) :=
    { φ := { ρ with commutes' := hρ }
      φ₀ := ρ₀
      comm := hπ
      dp := isDPMorphism_sqDP E.sq E'.sq _ fun c hc ↦ by
        have hc' : E.π c = 0 := hc
        change E'.π (ρ c) = 0
        rw [← hπ, hc', map_zero]
      pt := e₀ }
  let b : Thick.triv E.B _ (E.red_w hz) ⟶ m.obj (Thick.triv E'.B _ (E'.red_w hz')) :=
    Thick.trivHom { ρ₀ with commutes' := hρ₀ } e₀
  have k1 := ev_sq f b (m.functor.map (E'.secHom (E'.red_w hz') E'.i E'.π_i))
    (E.secHom (E.red_w hz) E.i E.π_i) Φ fun c ↦ (hi c).symm
  have k2 := ev_sq f a (m.functor.map (τ' ≫ E'.idHom hz')) (τ ≫ E.idHom hz) Φ fun c ↦ (h c).symm
  have k3 := ev_comp f τ (E.idHom hz)
  have k4 := ev_comp (m.coef.pullbackOneCocycle f) τ' (E'.idHom hz')
  have key : ∀ (A B C : E.C) (x y u v w k l : E'.C) (N : E.C), x + y = ρ A + w → l + k = ρ N + w → N = C + B →
      k = v + u → y - u - v = ρ (A - B - C) + l - x := fun A B C x y u v w k l N h1 h2 h3 h4 ↦ by
    subst h3 h4
    rw [map_add] at h2
    rw [map_sub, map_sub]
    linear_combination h1 - h2
  exact ⟨ev f b, key _ _ _ _ _ _ _ _ _ _ _ k1 k2 k3 k4⟩

attribute [local instance] cotOp cotCentral cotTower

def cotRingHom {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {D D' : Type} [CommRing D] [Bialgebra R D]
    [CommRing D'] [Bialgebra R' D'] (s : SemiBialgHom σ D D') :
    TrivSqZeroExt R (Cot R D) →+* TrivSqZeroExt R' (Cot R' D') where
  toFun c := TrivSqZeroExt.inl (σ c.fst) + TrivSqZeroExt.inr (s.cot c.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp [map_smulₛₗ]

theorem cotVal_pull : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X : Over (Sp R)) (X' : Over (Sp R')) (φ : X'.left ⟶ X.left) (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R') (X'.hom ≫ 𝟙 _) σ φ) (D D' : Type) [CommRing D] [Bialgebra R D] [CommRing D'] [Bialgebra R' D'] (s : SemiBialgHom σ D D') (y : Pt X D) (y' : Pt X' D') (a : trivAt y ⟶ m.obj (trivAt y')) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))), (∀ r, a.φ r = s r) → cotVal (m.coef.pullbackOneCocycle f) y' = s.cot (cotVal f y) + dUnit R' (show D' from ev f a) := by
  intro R R' _ _ σ X X' φ m D D' _ _ _ _ s y y' a f ha
  have hf : ∀ c, (cotRingHom s c).fst = σ c.fst := fun c ↦ add_zero _
  have hs : ∀ c, (cotRingHom s c).snd = s.cot c.snd := fun c ↦ zero_add _
  have pf : ∀ c : D, TrivSqZeroExt.fst (cotPt R D c) = Coalgebra.counit c := fun c ↦ add_zero _
  have ps : ∀ c : D, TrivSqZeroExt.snd (cotPt R D c) = dUnit R c := fun c ↦ zero_add _
  have pf' : ∀ c : D', TrivSqZeroExt.fst (cotPt R' D' c) = Coalgebra.counit c := fun c ↦ add_zero _
  have ps' : ∀ c : D', TrivSqZeroExt.snd (cotPt R' D' c) = dUnit R' c := fun c ↦ zero_add _
  obtain ⟨b, hb⟩ := val_sub_pull m (cotExt R D) (cotExt R' D') (cotRingHom s) σ
    (fun r ↦ TrivSqZeroExt.ext (hf _) ((hs _).trans (map_zero _))) (fun _ ↦ rfl) (fun c ↦ (hf c).symm)
    (fun r ↦ TrivSqZeroExt.ext (hf _) ((hs _).trans (map_zero _))) a
    (spOver (cotPt R D) ≫ y).left (Pt.w _) (spOver (cotPt R' D') ≫ y').left (Pt.w _)
    (trivMap (cotPt R D) y) (trivMap (cotPt R' D') y') (fun c ↦ by
      change cotRingHom s (cotPt R D c) = cotPt R' D' (a.φ c)
      rw [ha]
      ext
      · rw [hf, pf, pf', s.counit_map]
      · rw [hs, ps, ps', s.cot_d]) f
  refine (congrArg (cotSnd R' D') hb).trans ?_
  rw [map_sub, map_add]
  refine (sub_zero _).trans ?_
  exact congrArg₂ (· + ·) (hs _) (ps' _)

end GlobalTheory.PtExt
