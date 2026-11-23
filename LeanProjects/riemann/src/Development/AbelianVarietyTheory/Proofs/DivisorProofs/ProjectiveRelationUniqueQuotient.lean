import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineQuot

open GlobalTheory.Twist (resM app_resM sec_ext_of_cover)

attribute [local instance] Abelian.hasFiniteBiproducts

section
variable {T : Scheme.{0}} {L Q : T.Modules} {N : ℕ}

theorem desc_app (s : Fin (N + 1) → (L ⟶ Q)) (V : T.Opens) (t : Γ(⨁ fun _ : Fin (N + 1) => L, V)) :
    (biproduct.desc s).app V t = ∑ m, (s m).app V ((biproduct.π (fun _ : Fin (N + 1) => L) m).app V t) := by
  have h : biproduct.desc s = ∑ m, biproduct.π (fun _ : Fin (N + 1) => L) m ≫ s m := by
    rw [← Category.id_comp (biproduct.desc s), ← biproduct.total, Preadditive.sum_comp]
    simp
  let ev : ((⨁ fun _ : Fin (N + 1) => L) ⟶ Q) →+ Γ(Q, V) :=
    { toFun := fun f => f.app V t
      map_zero' := by simp
      map_add' := fun f g => by simp }
  rw [h]
  exact (map_sum ev (fun m => biproduct.π (fun _ : Fin (N + 1) => L) m ≫ s m) Finset.univ).trans
    (Finset.sum_congr rfl fun m _ => rfl)

theorem desc_app_eq_zero {k : Type} [CommRing k] {Q' : T.Modules} {φ : T ⟶ PSpace k N}
    {s : Fin (N + 1) → (L ⟶ Q)} {s' : Fin (N + 1) → (L ⟶ Q')} (hs : Rel φ s) (hs' : Rel φ s')
    {W : T.Opens} (i j : Fin (N + 1)) (hi : W ≤ φ ⁻¹ᵁ ProjSpace.chart k N i)
    (hj : Function.Injective ((s j).app W)) (u : Γ(⨁ fun _ : Fin (N + 1) => L, W))
    (h0 : (biproduct.desc s).app W u = 0) : (biproduct.desc s').app W u = 0 := by
  set v : Γ(L, W) := ∑ m, ProjSpace.pullRatio φ W i hi m •
    (biproduct.π (fun _ : Fin (N + 1) => L) m).app W u with hv
  have key : ∀ {Q₁ : T.Modules} (s₁ : Fin (N + 1) → (L ⟶ Q₁)), Rel φ s₁ →
      (biproduct.desc s₁).app W u = (s₁ i).app W v := by
    intro Q₁ s₁ h₁
    rw [desc_app, hv, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [h₁ i m W hi, Scheme.Modules.Hom.app_smul]
  have hv0 : v = 0 := hj (by rw [hs i j W hi, ← key s hs, h0, smul_zero, map_zero])
  rw [key s' hs', hv0, map_zero]

end

theorem exists_factor_of_rel : ∀ (k : Type) [CommRing k] (N : ℕ) (T : Scheme.{0}) (L Q Q' : T.Modules)
    (s : Fin (N + 1) → (L ⟶ Q)) (s' : Fin (N + 1) → (L ⟶ Q')) (φ : T ⟶ PSpace k N),
    IsVB L 1 → IsVB Q 1 → JointEpi s → Gen s → Rel φ s → Rel φ s' →
      ∃ e : Q ⟶ Q', ∀ j, s j ≫ e = s' j := by
  intro k _ N T L Q Q' s s' φ _ _ hJ hG hs hs'
  have hepi : Epi (biproduct.desc s) := Preadditive.epi_of_cancel_zero _ fun {Z} a ha =>
    hJ Z a fun j => by simpa using congrArg (biproduct.ι (fun _ : Fin (N + 1) => L) j ≫ ·) ha
  choose j G hxG hGb using hG
  choose i hi using fun x : T => ProjSpace.exists_mem_chart k N (φ x)
  have loc : ∀ (V : T.Opens) (t : Γ(⨁ fun _ : Fin (N + 1) => L, V)),
      (biproduct.desc s).app V t = 0 → (biproduct.desc s').app V t = 0 := by
    intro V t h0
    refine sec_ext_of_cover (fun x => V ⊓ G x ⊓ φ ⁻¹ᵁ ProjSpace.chart k N (i x))
      (fun _ => inf_le_left.trans inf_le_left)
      (fun y hy => TopologicalSpace.Opens.mem_iSup.2 ⟨y, ⟨⟨hy, hxG y⟩, hi y⟩⟩) fun x => ?_
    rw [← app_resM, map_zero]
    refine desc_app_eq_zero hs hs' (i x) (j x) inf_le_right
      (hGb x _ (inf_le_left.trans inf_le_right)).1 _ ?_
    rw [app_resM, h0, map_zero]
  have hk : kernel.ι (biproduct.desc s) ≫ biproduct.desc s' = 0 := by
    ext V x
    have h := congrArg (fun f => f.app V x) (kernel.condition (biproduct.desc s))
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.zero_app] at h ⊢
    exact loc V _ h
  refine ⟨Abelian.epiDesc _ _ hk, fun j => ?_⟩
  rw [← biproduct.ι_desc s j, Category.assoc, Abelian.comp_epiDesc, biproduct.ι_desc]

end GlobalTheory.LineQuot
