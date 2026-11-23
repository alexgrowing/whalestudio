import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu.Base

variable {p : ℕ} [Fact p.Prime] {P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop} (B : Base p P)
  {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem map_id' {G : PDivGroup p k} (hG : P k G) : B.map hG hG (𝟙 G) = LinearMap.id :=
  LinearMap.ext fun m => B.smap_id G hG m

theorem map_comp' {G H K : PDivGroup p k} (hG : P k G) (hH : P k H) (hK : P k K) (f : G ⟶ H) (g : H ⟶ K) :
    B.map hG hK (f ≫ g) = B.map hG hH f ∘ₗ B.map hH hK g :=
  LinearMap.ext fun m => B.smap_comp hG hH hK (SemiHom.ofHom g) (SemiHom.ofHom f) (SemiHom.ofHom (f ≫ g))
    (fun _ _ => rfl) m

theorem map_add' {G H : PDivGroup p k} (hG : P k G) (hH : P k H) (f g : G ⟶ H) :
    B.map hG hH (f + g) = B.map hG hH f + B.map hG hH g :=
  LinearMap.ext fun m => B.smap_add hG hH f g m

def mapAdd {G H : PDivGroup p k} (hG : P k G) (hH : P k H) :
    (G ⟶ H) →+ (B.M H hH →ₗ[WittVector p k] B.M G hG) :=
  AddMonoidHom.mk' (B.map hG hH) (B.map_add' hG hH)

theorem map_zero' {G H : PDivGroup p k} (hG : P k G) (hH : P k H) : B.map hG hH (0 : G ⟶ H) = 0 :=
  map_zero (B.mapAdd hG hH)

theorem map_pow_smul {G H : PDivGroup p k} (hG : P k G) (hH : P k H) (n : ℕ) (f : G ⟶ H) (m : B.M H hH) :
    B.map hG hH ((p : ℤ_[p]) ^ n • f) m = p ^ n • B.map hG hH f m := by
  have e : (p : ℤ_[p]) ^ n • f = (p ^ n) • f := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  have e2 : B.map hG hH ((p ^ n) • f) = (p ^ n) • B.map hG hH f := map_nsmul (B.mapAdd hG hH) _ _
  rw [e, e2, LinearMap.smul_apply]

theorem red_map {G H : PDivGroup p k} (hG : P k G) (hH : P k H) (f : G ⟶ H) (m : B.M H hH) :
    B.red G hG (B.map hG hH f m) = rigExtMap f (B.red H hH m) := by
  have := B.red_smap hG hH (SemiHom.ofHom f) m
  rw [SemiHom.ofHom_rig] at this
  exact this

theorem map_F {G H : PDivGroup p k} (hG : P k G) (hH : P k H) (f : G ⟶ H) (m : B.M H hH) :
    B.map hG hH f (B.F H hH m) = B.F G hG (B.map hG hH f m) := by
  let u := (SemiHom.ofHom f).comp (absFrob (p_eq_zero p k) H)
  have e1 : B.smap hG hH u m = B.map hG hH f (B.F H hH m) :=
    B.smap_comp hG hH hH (absFrob (p_eq_zero p k) H) (SemiHom.ofHom f) u (fun _ _ => rfl) m
  have e2 : B.smap hG hH u m = B.F G hG (B.map hG hH f m) :=
    B.smap_comp hG hG hH (SemiHom.ofHom f) (absFrob (p_eq_zero p k) G) u
      (fun n a => by simp only [u, SemiHom.comp_app, SemiHom.ofHom_app, absFrob_app, map_pow]) m
  exact e1.symm.trans e2

theorem finrank_M (G : PDivGroup p k) (hG : P k G) :
    Module.finrank (WittVector p k) (B.M G hG) = G.height := by
  haveI := B.free G hG
  haveI := B.finite G hG
  obtain ⟨_, h5⟩ := finrank_eq_of_semilinear_surjective (WittVector.constantCoeff_surjective p)
    (p_eq_zero p k) (B.red G hG) (B.red_surjective G hG) fun m => (B.red_eq_zero G hG m).1
  exact h5.symm.trans (rigExt_field_of_charP p k (p_eq_zero p k) G).2.1

theorem eq_zero_of_pow_smul {G : PDivGroup p k} (hG : P k G) (n : ℕ) (m : B.M G hG) (h : p ^ n • m = 0) :
    m = 0 := by
  haveI := B.free G hG
  rw [← Nat.cast_smul_eq_nsmul (WittVector p k)] at h
  refine (smul_eq_zero.1 h).resolve_left ?_
  rw [Nat.cast_pow]
  exact pow_ne_zero _ (WittVector.p_nonzero p k)

end GlobalTheory.Dieu.Base

namespace GlobalTheory.Dieu

theorem base_functor_props : ∀ (p : ℕ) [Fact p.Prime] (P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop) (B : Base p P) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H K : PDivGroup p k) (hG : P k G) (hH : P k H) (hK : P k K), B.map hG hG (𝟙 G) = LinearMap.id ∧ (∀ (f : G ⟶ H) (g : H ⟶ K), B.map hG hK (f ≫ g) = B.map hG hH f ∘ₗ B.map hH hK g) ∧ (∀ f g : G ⟶ H, B.map hG hH (f + g) = B.map hG hH f + B.map hG hH g) ∧ B.map hG hH (0 : G ⟶ H) = 0 ∧ (∀ (n : ℕ) (f : G ⟶ H) (m : B.M H hH), B.map hG hH ((p : ℤ_[p]) ^ n • f) m = p ^ n • B.map hG hH f m) ∧ (∀ (f : G ⟶ H) (m : B.M H hH), B.red G hG (B.map hG hH f m) = rigExtMap f (B.red H hH m)) ∧ (∀ (f : G ⟶ H) (m : B.M H hH), B.map hG hH f (B.F H hH m) = B.F G hG (B.map hG hH f m)) ∧ Module.finrank (WittVector p k) (B.M G hG) = G.height ∧ ∀ (n : ℕ) (m : B.M G hG), p ^ n • m = 0 → m = 0 := by
  intro p _ P B k _ _ _ G H K hG hH hK
  exact ⟨B.map_id' hG, fun f g => B.map_comp' hG hH hK f g, B.map_add' hG hH, B.map_zero' hG hH,
    B.map_pow_smul hG hH, B.red_map hG hH, B.map_F hG hH, B.finrank_M G hG, B.eq_zero_of_pow_smul hG⟩

end GlobalTheory.Dieu
