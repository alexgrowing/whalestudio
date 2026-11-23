import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CubBoxVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif
namespace GlobalTheory.ProdUnif

open GlobalTheory.WCub GlobalTheory.PowUnif

set_option maxHeartbeats 1600000 in

theorem cubAlong_prod : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (wM : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left)) (L : LB (G₁ ⊗ G₂).left) (c : CubGen (G₁ ⊗ G₂) L) (wL : LB.Iso L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left)), L.IsLB → IsBoxGen (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (φ₁ := thφ D₁.toPre.P.A (x3 D₁.toPre.P.A)) (φ₂ := thφ D₂.toPre.P.A (x3 D₂.toPre.P.A)) (ε := thε) wM (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left D.toPre.cub.t D₁.toPre.cub.t D₂.toPre.cub.t → IsBoxGen (φ₁ := thφ G₁ (x3 G₁)) (φ₂ := thφ G₂ (x3 G₂)) wL (fst G₁ G₂ ⊗ₘ fst G₁ G₂ ⊗ₘ fst G₁ G₂).left (snd G₁ G₂ ⊗ₘ snd G₁ G₂ ⊗ₘ snd G₁ G₂).left c U₁.cubG.t U₂.cubG.t → ∀ (e : ℕ) (g : GtCoord I D.toPre e (G₁ ⊗ G₂)), g.pG.left ≫ p₁.left = ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ≫ (U₁.gt e).pG.left → g.pG.left ≫ p₂.left = ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ≫ (U₂.gt e).pG.left → ∀ w : LB.Iso (L.pull (fstG I e (G₁ ⊗ G₂)).left) (D.toPre.P.L.pull g.pG.left), BoxSq (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left) (T₂ := (thickObj R I e G₂).left) wM wL w (U₁.w e) (U₂.w e) ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left → CubAlong I D.toPre e (G₁ ⊗ G₂) L c g.pG w := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D p₁ p₂ q₁ q₂ hS wM L c wL hLB hM hL e g h₁ h₂ w hQ T x jL jM cL cM
  have := g.q_hom
  have := (U₁.gt e).q_hom
  have := (U₂.gt e).q_hom
  have := hS.hom₁
  have := hS.hom₂
  refine (clause_iff (tri (thick R I e) g.pG x) (tri (thick R I e) (fstG I e (G₁ ⊗ G₂)) x)
    (fun k : thK => (psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left) _ _ _ (D.toPre.cub.t.s jM) (c.s jL)
    (fun k => w.s (fun _ => jM k, fun _ => jL k)) thε).2 fun y hB hG' _ => ?_
  obtain ⟨J, hJ, eJ⟩ := exists_good D.toPre.P.L D.toPre.P.isLB y _ jM cM (fun k => Set.mem_iInter.1 hB k)
  obtain ⟨N, hN, eN⟩ := exists_good L hLB y _ jL cL (fun k => Set.mem_iInter.1 hG' k)
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.BoxFamily.exists_good_at D₁.toPre.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := GlobalTheory.BoxFamily.exists_good_at D₂.toPre.P.isLB y
  obtain ⟨N₁, hN₁⟩ := GlobalTheory.BoxFamily.exists_good_at U₁.LG.isLB y
  obtain ⟨N₂, hN₂⟩ := GlobalTheory.BoxFamily.exists_good_at U₂.LG.isLB y
  have tM₁ := (tri_map (thick R I e) (U₁.gt e).pG g.pG x _ p₁ h₁).2
  have tM₂ := (tri_map (thick R I e) (U₂.gt e).pG g.pG x _ p₂ h₂).2
  have tL₁ := (tri_map (thick R I e) (fstG I e G₁) (fstG I e (G₁ ⊗ G₂)) x _ (fst G₁ G₂)
    (thick_fstG I e (fst G₁ G₂))).2
  have tL₂ := (tri_map (thick R I e) (fstG I e G₂) (fstG I e (G₁ ⊗ G₂)) x _ (snd G₁ G₂)
    (thick_fstG I e (snd G₁ G₂))).2
  have bM := hM T.left (tri (thick R I e) g.pG x) y J₁ J₂ J hJ₁ hJ₂ hJ
  rw [tM₁, tM₂] at bM
  have bL := hL T.left (tri (thick R I e) (fstG I e (G₁ ⊗ G₂)) x) y N₁ N₂ N hN₁ hN₂ hN
  rw [tL₁, tL₂] at bL
  have v₁ := w_cub_val.{0} U₁ e T (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) y hJ₁ hN₁
  have v₂ := w_cub_val.{0} U₂ e T (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) y hJ₂ hN₂

  have fM := fun k : thK => tri_thφ (thick R I e) g.pG x g.q rfl k
  have fG := fun k : thK => tri_thφ (thick R I e) (fstG I e (G₁ ⊗ G₂)) x (𝟙 _) (Category.id_comp _).symm k
  have fM₁ := fun k : thK => tri_thφ (thick R I e) (U₁.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) (U₁.gt e).q rfl k
  have fM₂ := fun k : thK => tri_thφ (thick R I e) (U₂.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) (U₂.gt e).q rfl k
  have fG₁ := fun k : thK => tri_thφ (thick R I e) (fstG I e G₁) (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) (𝟙 _)
    (Category.id_comp _).symm k
  have fG₂ := fun k : thK => tri_thφ (thick R I e) (fstG I e G₂) (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) (𝟙 _)
    (Category.id_comp _).symm k
  have ps₁ := fun k : thK => psum_comp x ((Over.pullback (thick R I e)).map (fst G₁ G₂)) k.down
  have ps₂ := fun k : thK => psum_comp x ((Over.pullback (thick R I e)).map (snd G₁ G₂)) k.down
  have key := rel_alg thε
    (fun k => om wM y J₁ J₂ J (tri (thick R I e) g.pG x ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k))
    (fun k => om wL y N₁ N₂ N (tri (thick R I e) (fstG I e (G₁ ⊗ G₂)) x ≫ thφ (G₁ ⊗ G₂) (x3 (G₁ ⊗ G₂)) k))
    (fun k => gw w (psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left y (jM k) (fun _ => jL k))
    (fun k => gw (U₁.w e) (psum (thickObj R I e G₁) (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) k.down).left y
      (J₁ (tri (thick R I e) (U₁.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ thφ D₁.toPre.P.A (x3 D₁.toPre.P.A) k))
      (fun _ => N₁ (tri (thick R I e) (fstG I e G₁) (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ thφ G₁ (x3 G₁) k)))
    (fun k => gw (U₂.w e) (psum (thickObj R I e G₂) (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) k.down).left y
      (J₂ (tri (thick R I e) (U₂.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ thφ D₂.toPre.P.A (x3 D₂.toPre.P.A) k))
      (fun _ => N₂ (tri (thick R I e) (fstG I e G₂) (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ thφ G₂ (x3 G₂) k)))
    (fun k => by
      have q := hQ T.left (psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left y J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
      have a₁ : ((psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left ≫ g.pG.left) ≫ p₁.left =
          tri (thick R I e) (U₁.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ thφ D₁.toPre.P.A (x3 D₁.toPre.P.A) k := by
        rw [Category.assoc, h₁, ← Category.assoc, ps₁ k, fM₁ k]
      have a₂ : ((psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left ≫ g.pG.left) ≫ p₂.left =
          tri (thick R I e) (U₂.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ thφ D₂.toPre.P.A (x3 D₂.toPre.P.A) k := by
        rw [Category.assoc, h₂, ← Category.assoc, ps₂ k, fM₂ k]
      have b₁ : ((psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left ≫ (fstG I e (G₁ ⊗ G₂)).left) ≫ (fst G₁ G₂).left =
          tri (thick R I e) (fstG I e G₁) (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ thφ G₁ (x3 G₁) k := by
        rw [Category.assoc, thick_fstG I e (fst G₁ G₂), ← Category.assoc, ps₁ k, fG₁ k]
      have b₂ : ((psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left ≫ (fstG I e (G₁ ⊗ G₂)).left) ≫ (snd G₁ G₂).left =
          tri (thick R I e) (fstG I e G₂) (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ thφ G₂ (x3 G₂) k := by
        rw [Category.assoc, thick_fstG I e (snd G₁ G₂), ← Category.assoc, ps₂ k, fG₂ k]
      rw [a₁, a₂, b₁, b₂, ps₁ k, ps₂ k, ← fM k, ← fG k, eJ k, eN k] at q
      exact q)
    bM bL v₁ v₂
  refine (val_of _ _ y J jM eJ).symm.trans (key.trans ?_)
  exact congrArg _ (val_of c _ y N jL eN)

end GlobalTheory.ProdUnif
