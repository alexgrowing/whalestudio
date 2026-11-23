import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

noncomputable section

namespace GlobalTheory.ProdUnif

open GlobalTheory.UnifPullRig

theorem rigAlong_box : ∀ {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁} {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {p₁ : T₁ ⟶ B₁} {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂} (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)) (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)), M.IsLB → M₁.IsLB → M₂.IsLB → L.IsLB → L₁.IsLB → L₂.IsLB → p ≫ b₁ = h₁ ≫ p₁ → p ≫ b₂ = h₂ ≫ p₂ → f ≫ g₁ = h₁ ≫ f₁ → f ≫ g₂ = h₂ ≫ f₂ → ∀ (we : LB.Iso (L.pull f) (M.pull p)), BoxSq wM wL we we₁ we₂ h₁ h₂ → ∀ {S S₀ : Scheme.{0}} (u : S ⟶ T) (u₁ : S ⟶ T₁) (u₂ : S ⟶ T₂) (s : S ⟶ S₀) {eG : S₀ ⟶ G} {eG₁ : S₀ ⟶ G₁} {eG₂ : S₀ ⟶ G₂} {eB : S₀ ⟶ B} {eB₁ : S₀ ⟶ B₁} {eB₂ : S₀ ⟶ B₂} (rL : LB.Gen (L.pull eG)) (rL₁ : LB.Gen (L₁.pull eG₁)) (rL₂ : LB.Gen (L₂.pull eG₂)) (rM : LB.Gen (M.pull eB)) (rM₁ : LB.Gen (M₁.pull eB₁)) (rM₂ : LB.Gen (M₂.pull eB₂)), u ≫ h₁ = u₁ → u ≫ h₂ = u₂ → u ≫ f = s ≫ eG → u ≫ p = s ≫ eB → u₁ ≫ f₁ = s ≫ eG₁ → u₁ ≫ p₁ = s ≫ eB₁ → u₂ ≫ f₂ = s ≫ eG₂ → u₂ ≫ p₂ = s ≫ eB₂ → IsBoxGen wL (𝟙 S₀) (𝟙 S₀) rL rL₁ rL₂ → IsBoxGen wM (𝟙 S₀) (𝟙 S₀) rM rM₁ rM₂ → GlobalTheory.UnifPullRig.RigAlong we₁ u₁ s rL₁ rM₁ → GlobalTheory.UnifPullRig.RigAlong we₂ u₂ s rL₂ rM₂ → GlobalTheory.UnifPullRig.RigAlong we u s rL rM := by
  intro B B₁ B₂ G G₁ G₂ T T₁ T₂ M M₁ M₂ L L₁ L₂ b₁ b₂ g₁ g₂ p f p₁ f₁ p₂ f₂ h₁ h₂ wM wL we₁ we₂ hM hM₁ hM₂
    hL hL₁ hL₂ hpb₁ hpb₂ hfg₁ hfg₂ we hQ S S₀ u u₁ u₂ s eG eG₁ eG₂ eB eB₁ eB₂ rL rL₁ rL₂ rM rM₁ rM₂ hu₁ hu₂
    hf hp hf₁ hp₁ hf₂ hp₂ bL bM H₁ H₂
  rintro ⟨qM, qL⟩ V a₁ a₂ a₃
  refine unit_ext fun y hy => ?_
  obtain ⟨J, hJ, eJ⟩ := exists_good M hM y (K := PUnit) (fun _ => s ≫ eB) (fun _ => qM ⟨⟩)
    (fun _ _ _ => rfl) (fun _ => (mem_pull (F := eB) (x := s y)).1 (a₃ hy))
  obtain ⟨N, hN, eN⟩ := exists_good L hL y (K := PUnit) (fun _ => s ≫ eG) (fun _ => qL ⟨⟩)
    (fun _ _ _ => rfl) (fun _ => (mem_pull (F := eG) (x := s y)).1 (a₂ hy))
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at hM₁ y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at hM₂ y
  obtain ⟨N₁, hN₁⟩ := BoxFamily.exists_good_at hL₁ y
  obtain ⟨N₂, hN₂⟩ := BoxFamily.exists_good_at hL₂ y
  have m₁ : (u ≫ p) ≫ b₁ = s ≫ eB₁ := by rw [Category.assoc, hpb₁, ← Category.assoc, hu₁, hp₁]
  have m₂ : (u ≫ p) ≫ b₂ = s ≫ eB₂ := by rw [Category.assoc, hpb₂, ← Category.assoc, hu₂, hp₂]
  have n₁ : (u ≫ f) ≫ g₁ = s ≫ eG₁ := by rw [Category.assoc, hfg₁, ← Category.assoc, hu₁, hf₁]
  have n₂ : (u ≫ f) ≫ g₂ = s ≫ eG₂ := by rw [Category.assoc, hfg₂, ← Category.assoc, hu₂, hf₂]
  have Q := hQ S u y J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
  rw [m₁, m₂, n₁, n₂, hu₁, hu₂, hp, hf] at Q
  have HM := bM S s y J₁ J₂ J hJ₁ hJ₂ hJ
  have HL := bL S s y N₁ N₂ N hN₁ hN₂ hN
  simp only [Category.comp_id] at HM HL
  have E₁ := H₁.stalk hf₁ hp₁ (𝟙 S) y (J₁ (s ≫ eB₁)) (N₁ (s ≫ eG₁))
    ((pt_of_eq hp₁ y).symm ▸ hJ₁ (s ≫ eB₁)) ((pt_of_eq hf₁ y).symm ▸ hN₁ (s ≫ eG₁))
  have E₂ := H₂.stalk hf₂ hp₂ (𝟙 S) y (J₂ (s ≫ eB₂)) (N₂ (s ≫ eG₂))
    ((pt_of_eq hp₂ y).symm ▸ hJ₂ (s ≫ eB₂)) ((pt_of_eq hf₂ y).symm ▸ hN₂ (s ≫ eG₂))
  simp only [Category.id_comp] at E₁ E₂
  have key := rel_alg (K := PUnit) (fun _ => 1) (fun _ => om wM y J₁ J₂ J (s ≫ eB))
    (fun _ => om wL y N₁ N₂ N (s ≫ eG)) (fun _ => gw we u y (J (s ≫ eB)) (fun _ => N (s ≫ eG)))
    (fun _ => gw we₁ u₁ y (J₁ (s ≫ eB₁)) (fun _ => N₁ (s ≫ eG₁)))
    (fun _ => gw we₂ u₂ y (J₂ (s ≫ eB₂)) (fun _ => N₂ (s ≫ eG₂))) (fun _ => Q) HM HL
    (by rw [Fintype.prod_unique, zpow_one]; exact E₁.symm) (by rw [Fintype.prod_unique, zpow_one]; exact E₂.symm)
  rw [Fintype.prod_unique, zpow_one, val_of rM s y J qM (fun k => eJ k), val_of rL s y N qL (fun k => eN k),
    eJ ⟨⟩, eN ⟨⟩] at key
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_res_pull _ u y a₁ hy _)
    (gm_res_pull _ s y a₂ hy _)).trans (Eq.trans ?_ (gm_res_pull _ s y a₃ hy _).symm))
  simp only [Category.id_comp]
  exact key.symm

end GlobalTheory.ProdUnif
