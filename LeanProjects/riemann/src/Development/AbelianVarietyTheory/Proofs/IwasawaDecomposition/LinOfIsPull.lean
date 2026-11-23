import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionFramesMoveToCoverAndRingExtension

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LN
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

def LinA {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (b : Fin n → LB.Sec (LPow G L (N : ℤ) T)) (c : Fin n → Γ(T'.left, ⊤)) (a : Γ(T'.left, ⊤))
    (s : LB.Sec (LPow G L (N : ℤ) T')) : Prop :=
  ∀ (z : (T' ⊗ G).left) (J), Good L z J →
    gs (fst T' G).left z ⊤ a *
        sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) s (𝟙 _) z J =
      ∑ i, gs (fst T' G).left z ⊤ (c i) *
        sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) (b i) (h ▷ G).left z J

def jC {R W V : Type} [CommRing R] [CommRing W] [CommRing V] (φ : R →+* W) (g : W →+* V) :
    Over.mk (spMap (g.comp φ)) ⟶ Over.mk (spMap φ) :=
  Over.homMk (spMap g) (by
    show Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom (g.comp φ))
    rw [← Spec.map_comp]; rfl)

theorem jC_toBase {R W V : Type} [CommRing R] [CommRing W] [CommRing V] (φ : R →+* W) (g : W →+* V) :
    jC φ g ≫ toBase φ = toBase (g.comp φ) := by
  ext1
  show Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom (g.comp φ))
  rw [← Spec.map_comp]; rfl

theorem fnR_one (R : Type) [CommRing R] : GlobalTheory.OneBasis.fnR (1 : R) = 1 := map_one _

section
variable {S : Scheme.{0}} {G : Over S} {L : LB G.left} {N : ℕ} {T T' : Over S} {h : T' ⟶ T} {n : ℕ}
  {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)} {c : Fin n → Γ(T'.left, ⊤)} {s : LB.Sec (LPow G L (N : ℤ) T')}

theorem lin_iff_linA : Lin G L N h b c s ↔ LinA G L N h b c 1 s := by
  refine forall_congr' fun z => forall_congr' fun J => imp_congr_right fun _ => ?_
  rw [GlobalTheory.FramePull.gs_one, _root_.one_mul]

theorem linA_scale (a : Γ(T'.left, ⊤)) (H : Lin G L N h b c s) : LinA G L N h b (fun i => a * c i) a s := by
  intro z J hJ
  rw [H z J hJ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_eq _ z ⊤ trivial, gs_eq _ z ⊤ trivial, gs_eq _ z ⊤ trivial, map_mul, map_mul, _root_.mul_assoc]

end

open GlobalTheory.FramePull in

theorem lin_comp {S : Scheme.{0}} {G : Over S} {L : LB G.left} {N : ℕ} {T T' T'' : Over S} (h : T' ⟶ T) (u : T'' ⟶ T')
    {n : ℕ} {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)} {c : Fin n → Γ(T'.left, ⊤)} {s : LB.Sec (LPow G L (N : ℤ) T')}
    {s'' : LB.Sec (LPow G L (N : ℤ) T'')} (H : Lin G L N h b c s)
    (hs : Lin G L N u (fun _ : Fin 1 => s) (fun _ => 1) s'') :
    Lin G L N (u ≫ h) b (fun i => u.left.appTop.hom (c i)) s'' := by
  have hp := isPull_of_lin hs
  rw [lin_iff] at H ⊢
  intro W r z J hJ
  rw [hp W r z J hJ, H W _ z J hJ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [comp_whiskerRight, Over.comp_left, Category.assoc, Category.assoc, ← Over.comp_left, whiskerRight_fst,
    Over.comp_left, ← Category.assoc]
  exact congrArg (· * _) (gs_pull _ u.left z ⊤ trivial _).symm

open GlobalTheory.FramePull in

theorem lin_of_isPull {S : Scheme.{0}} {G : Over S} {L : LB G.left} {N : ℕ} {T T' : Over S} {u : T' ⟶ T}
    {s : LB.Sec (LPow G L (N : ℤ) T)} {s' : LB.Sec (LPow G L (N : ℤ) T')} (H : IsPull u s s') :
    Lin G L N u (fun _ : Fin 1 => s) (fun _ => 1) s' := by
  rw [lin_iff]
  intro W r z J hJ
  rw [H W r z J hJ, Fin.sum_univ_one, gs_one, _root_.one_mul]

end GlobalTheory.TorRef
