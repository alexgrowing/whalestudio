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

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.UnifPullRig

theorem compat_box₂ : ∀ {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁} {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {p₁ : T₁ ⟶ B₁} {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂} (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)) (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)), M.IsLB → M₁.IsLB → M₂.IsLB → L.IsLB → L₁.IsLB → L₂.IsLB → p ≫ b₁ = h₁ ≫ p₁ → p ≫ b₂ = h₂ ≫ p₂ → f ≫ g₁ = h₁ ≫ f₁ → f ≫ g₂ = h₂ ≫ f₂ → ∀ (we : LB.Iso (L.pull f) (M.pull p)), BoxSq wM wL we we₁ we₂ h₁ h₂ → ∀ {T' T₁' T₂' : Scheme.{0}} {p' : T' ⟶ B} {f' : T' ⟶ G} {p₁' : T₁' ⟶ B₁} {f₁' : T₁' ⟶ G₁} {p₂' : T₂' ⟶ B₂} {f₂' : T₂' ⟶ G₂} {h₁' : T' ⟶ T₁'} {h₂' : T' ⟶ T₂'} (we' : LB.Iso (L.pull f') (M.pull p')) (we₁' : LB.Iso (L₁.pull f₁') (M₁.pull p₁')) (we₂' : LB.Iso (L₂.pull f₂') (M₂.pull p₂')), BoxSq wM wL we' we₁' we₂' h₁' h₂' → ∀ (m : T ⟶ T') (m₁ : T₁ ⟶ T₁') (m₂ : T₂ ⟶ T₂'), m ≫ h₁' = h₁ ≫ m₁ → m ≫ h₂' = h₂ ≫ m₂ → m ≫ f' = f → m ≫ p' = p → m₁ ≫ f₁' = f₁ → m₁ ≫ p₁' = p₁ → m₂ ≫ f₂' = f₂ → m₂ ≫ p₂' = p₂ → GlobalTheory.UnifPullRig.CompatAlong we₁' we₁ m₁ → GlobalTheory.UnifPullRig.CompatAlong we₂' we₂ m₂ → GlobalTheory.UnifPullRig.CompatAlong we' we m := by
  intro B B₁ B₂ G G₁ G₂ T T₁ T₂ M M₁ M₂ L L₁ L₂ b₁ b₂ g₁ g₂ p f p₁ f₁ p₂ f₂ h₁ h₂ wM wL we₁ we₂ hM hM₁ hM₂ hL hL₁ hL₂
    ep₁ ep₂ ef₁ ef₂ we Q T' T₁' T₂' p' f' p₁' f₁' p₂' f₂' h₁' h₂' we' we₁' we₂' Q' m m₁ m₂ hm₁ hm₂ hmf hmp hm₁f hm₁p
    hm₂f hm₂p H₁ H₂
  rintro ⟨qM, qL⟩ V a₁ a₂
  refine unit_ext fun y hy => ?_
  have bM : p y ∈ M.U (qM ⟨⟩) := mem_pull.1 (a₂ hy).1
  have bL : f y ∈ L.U (qL ⟨⟩) := mem_pull.1 (a₂ hy).2
  obtain ⟨J, hJ, eJ⟩ := exists_good M hM y (K := PUnit) (fun _ => p) (fun _ => qM ⟨⟩) (fun _ _ _ => rfl)
    (fun _ => bM)
  obtain ⟨N, hN, eN⟩ := exists_good L hL y (K := PUnit) (fun _ => f) (fun _ => qL ⟨⟩) (fun _ _ _ => rfl)
    (fun _ => bL)
  obtain ⟨J₁, hJ₁⟩ := exists_good_at hM₁ y
  obtain ⟨J₂, hJ₂⟩ := exists_good_at hM₂ y
  obtain ⟨N₁, hN₁⟩ := exists_good_at hL₁ y
  obtain ⟨N₂, hN₂⟩ := exists_good_at hL₂ y
  have e₀ := Q T (𝟙 T) y J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
  have e₁ := Q' T m y J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
  have c₁ := H₁.stalk hm₁f hm₁p h₁ y (J₁ (p ≫ b₁)) (N₁ (f ≫ g₁))
    ((pt_of_eq ep₁ y) ▸ hJ₁ (p ≫ b₁)) ((pt_of_eq ef₁ y) ▸ hN₁ (f ≫ g₁))
  have c₂ := H₂.stalk hm₂f hm₂p h₂ y (J₂ (p ≫ b₂)) (N₂ (f ≫ g₂))
    ((pt_of_eq ep₂ y) ▸ hJ₂ (p ≫ b₂)) ((pt_of_eq ef₂ y) ▸ hN₂ (f ≫ g₂))
  simp only [Category.id_comp] at e₀
  rw [hmp, hmf, hm₁, hm₂, c₁, c₂, ← e₀] at e₁
  have e := mul_left_cancel e₁
  rw [eJ ⟨⟩, eN ⟨⟩] at e
  exact (gm_res_pull _ m y a₁ hy _).trans ((Category.id_comp m).symm ▸ e.trans (gm_res _ y a₂ hy _).symm)

end GlobalTheory.ProdUnif
