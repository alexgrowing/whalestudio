import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.GrpBox

open GlobalTheory.SumDeg

theorem isBoxGen_extGen {X X₁ X₂ Y Y₁ Y₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : X ⟶ X₁) (f₂ : X ⟶ X₂)
    {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h₁ : Y ⟶ Y₁) (φ₁ : K → (Y₁ ⟶ X₁)) (e₁ : ∀ k, ψ k ≫ f₁ = h₁ ≫ φ₁ k) (t₁ : LB.Gen (LB.LinComb L₁ φ₁ ε))
    (h₂ : Y ⟶ Y₂) (φ₂ : K → (Y₂ ⟶ X₂)) (e₂ : ∀ k, ψ k ≫ f₂ = h₂ ≫ φ₂ k) (t₂ : LB.Gen (LB.LinComb L₂ φ₂ ε))
    (ht₁ : t₁.IsGen) (ht₂ : t₂.IsGen) :
    IsBoxGen (CubePf.idIsoL (extLB L₁ L₂ f₁ f₂)) h₁ h₂ (extGen L₁ L₂ f₁ f₂ ψ ε h₁ φ₁ e₁ t₁ h₂ φ₂ e₂ t₂) t₁ t₂ := by
  intro Z r z J₁ J₂ J hJ₁ hJ₂ hJ
  have hE := good_ext (f₁ := f₁) (f₂ := f₂) hJ₁ hJ₂
  have key := gen_trans (isGen_extGen L₁ L₂ f₁ f₂ ψ ε h₁ φ₁ e₁ t₁ h₂ φ₂ e₂ t₂ ht₁ ht₂) r z (hE.mem ψ r) (hJ.mem ψ r)
  have k2 := gm_extGen L₁ L₂ f₁ f₂ ψ ε h₁ φ₁ e₁ t₁ h₂ φ₂ e₂ t₂ r z _ (hE.mem ψ r)
  rw [val_of t₁ (r ≫ h₁) z J₁ (fun k => J₁ ((r ≫ ψ k) ≫ f₁)) (fun k => by rw [Category.assoc, Category.assoc, e₁]),
    val_of t₂ (r ≫ h₂) z J₂ (fun k => J₂ ((r ≫ ψ k) ≫ f₂)) (fun k => by rw [Category.assoc, Category.assoc, e₂])]
  exact key.symm.trans k2

section Grp

variable {S : Scheme.{0}} {A A₁ A₂ : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A₁] [IsCommMonObj A₁]
  [GrpObj A₂] [IsCommMonObj A₂]

def pullCub (L : RigLB A₁) (c : CubicalStr A₁ L) (a : A ⟶ A₁) [IsMonHom a] :=
  CubePf.cubical (CubeMap.ofHom a) L c (LB.isLB_pull L.isLB _)
    (LBxP.isGen_pullAlong L.L a.left (𝟙 _) (fun _ : PUnit => eSec A₁) (fun _ => 1)
      (fun _ => eSec A) (fun _ => (CubeMap.ofHom a).e_comm) L.rig L.rigGen)

theorem exists_strBox (a₁ : A ⟶ A₁) (a₂ : A ⟶ A₂) [IsMonHom a₁] [IsMonHom a₂]
    (L₁ : RigLB A₁) (L₂ : RigLB A₂) (c₁ : CubicalStr A₁ L₁) (c₂ : CubicalStr A₂ L₂)
    (s₁ : SymGen A₁ L₁.L) (s₂ : SymGen A₂ L₂.L) (hs₁ : s₁.IsGen) (hs₂ : s₂.IsGen)
    (n₁ : LB.Gen.Corr L₁.L _ _ _ _ (LB.pullGen L₁.L _ _ s₁ (eSec A₁)) (LB.oneGen L₁.L))
    (n₂ : LB.Gen.Corr L₂.L _ _ _ _ (LB.pullGen L₂.L _ _ s₂ (eSec A₂)) (LB.oneGen L₂.L)) :
    ∃ (L : RigLB A) (c : CubicalStr A L) (s : SymGen A L.L)
      (w : LB.Iso L.L (extLB L₁.L L₂.L a₁.left a₂.left)), s.IsGen ∧
      LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec A)) (LB.oneGen L.L) ∧
      StrBox a₁ a₂ w L.rig L₁.rig L₂.rig c.t c₁.t c₂.t s s₁ s₂ := by
  have hL := isLB_extLB L₁.isLB L₂.isLB a₁.left a₂.left
  refine ⟨⟨extLB L₁.L L₂.L a₁.left a₂.left,
      extAt L₁.L L₂.L a₁.left a₂.left (eSec A) 1 _ (eSec_comp a₁) L₁.rig _ (eSec_comp a₂) L₂.rig, hL,
      isGen_extAt _ _ _ _ _ _ _ _ _ _ _ _ L₁.rigGen L₂.rigGen⟩,
    tensCub (pullCub L₁ c₁ a₁) (pullCub L₂ c₂ a₂) _ hL _,
    extGen L₁.L L₂.L a₁.left a₂.left _ _ a₁.left _ (inv_comp a₁) s₁ a₂.left _ (inv_comp a₂) s₂,
    CubePf.idIsoL _, isGen_extGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs₁ hs₂, ?_, CubePf.idIsoL_isGen hL,
    isBoxGen_extGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ L₁.rigGen L₂.rigGen,
    isBoxGen_extGen L₁.L L₂.L a₁.left a₂.left (thφ A (x3 A)) thε
      (a₁ ⊗ₘ a₁ ⊗ₘ a₁).left (thφ A₁ (x3 A₁)) (fun I => (CubeMap.ofHom a₁).psum_comm I.down) c₁.t
      (a₂ ⊗ₘ a₂ ⊗ₘ a₂).left (thφ A₂ (x3 A₂)) (fun I => (CubeMap.ofHom a₂).psum_comm I.down) c₂.t
      c₁.isGen c₂.isGen,
    isBoxGen_extGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs₁ hs₂⟩
  refine corr_of_val hL fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at L₁.isLB y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at L₂.isLB y
  have o : eSec A ≫ (ι[A]).left = eSec A :=
    congrArg (fun m => m.left) (GrpObj.one_inv : η[A] ≫ ι[A] = η[A])
  have v₁ : val s₁ (eSec A₁) y J₁ = 1 := by
    have v := val_corr hJ₁ n₁ (𝟙 _)
    rwa [val_pull hJ₁, Category.id_comp, val_one] at v
  have v₂ : val s₂ (eSec A₂) y J₂ = 1 := by
    have v := val_corr hJ₂ n₂ (𝟙 _)
    rwa [val_pull hJ₂, Category.id_comp, val_one] at v
  have e := (val_extGen L₁.L L₂.L a₁.left a₂.left _ _ a₁.left _ (inv_comp a₁) s₁ a₂.left _ (inv_comp a₂) s₂
    hs₁ hs₂ (eSec A) hJ hJ₁ hJ₂).trans (congrArg₂ (· * ·) (prod_sym (eSec A) _) rfl)
  rw [o, mul_inv_cancel, eSec_comp, eSec_comp, v₁, v₂, _root_.mul_one, _root_.mul_one] at e
  rw [val_pull hJ, Category.id_comp, val_one]
  exact e

end Grp

theorem exists_prod : ∀ (S : Scheme.{0}) (G₁ G₂ : Over S) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (L₁ : RigLB G₁) (L₂ : RigLB G₂) (c₁ : CubicalStr G₁ L₁) (c₂ : CubicalStr G₂ L₂) (s₁ : SymGen G₁ L₁.L) (s₂ : SymGen G₂ L₂.L), s₁.IsGen → s₂.IsGen → LB.Gen.Corr L₁.L _ _ _ _ (LB.pullGen L₁.L _ _ s₁ (eSec G₁)) (LB.oneGen L₁.L) → LB.Gen.Corr L₂.L _ _ _ _ (LB.pullGen L₂.L _ _ s₂ (eSec G₂)) (LB.oneGen L₂.L) → ∃ (L : RigLB (G₁ ⊗ G₂)) (c : CubicalStr (G₁ ⊗ G₂) L) (s : SymGen (G₁ ⊗ G₂) L.L) (w : LB.Iso L.L (extLB L₁.L L₂.L (fst G₁ G₂).left (snd G₁ G₂).left)), s.IsGen ∧ LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec (G₁ ⊗ G₂))) (LB.oneGen L.L) ∧ StrBox (fst G₁ G₂) (snd G₁ G₂) w L.rig L₁.rig L₂.rig c.t c₁.t c₂.t s s₁ s₂ := by
  intro S G₁ G₂ _ _ _ _ L₁ L₂ c₁ c₂ s₁ s₂ hs₁ hs₂ n₁ n₂
  exact exists_strBox (fst G₁ G₂) (snd G₁ G₂) L₁ L₂ c₁ c₂ s₁ s₂ hs₁ hs₂ n₁ n₂

end GlobalTheory.GrpBox
