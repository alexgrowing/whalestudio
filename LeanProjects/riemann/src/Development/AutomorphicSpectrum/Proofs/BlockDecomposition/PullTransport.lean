import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CompatH
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.IsFirstChernClassOfLineBundle
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitsAbs
import BuildAid.D3
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.FirstChernComparison

universe w w' u₁ v₁ u₂ v₂ u₃ v₃

theorem pull_transport' {R : Type} [CommRing R] {Th : Type u₁} [Category.{v₁} Th] {Ec : Type u₂} [Category.{v₂} Ec]
    {C : Type u₃} [Category.{v₃} C]  (F : Th ⥤ ModuleCat.{w} R) (F' : Ec ⥤ ModuleCat.{w'} R) (m : CH.Mor F F' (RingHom.id R)) (G : C ⥤ Ec)
    (x : CH.H F 2) {Pc : CH.Cn ((G ⋙ m.G) ⋙ F) 2 → Prop} (h : ∃ (c : CH.Cn ((G ⋙ m.G) ⋙ F) 2) (hc : CH.d _ 2 c = 0), (CH.cx _).cls c hc = (CH.Mor.restrict F (G ⋙ m.G)).pull 2 x ∧ Pc c)
    (P : CH.Cn (G ⋙ F') 2 → Prop) (hP : ∀ z : CH.Cn (G ⋙ F') 2, ∀ c, (∀ s, z s = m.τ _ (c s)) → Pc c → P z) :
    ∃ (z : CH.Cn (G ⋙ F') 2) (hz : CH.d (G ⋙ F') 2 z = 0), P z ∧
      (CH.cx _).cls z hz = (CH.Mor.restrict F' G).pull 2 (m.pull 2 x) := by
  obtain ⟨c, hc, h, hp⟩ := h
  obtain ⟨hz, e⟩ := pull_transport F F' m G x c hc h
  exact ⟨_, hz, hP _ c (fun _ => rfl) hp, e⟩

section
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* OC l}
  {C : Type 1} [Category.{0} C] {G : C ⥤ El (PX q κ)} {D : E.LineData X} (k : Bool) (n : ℕ)

theorem st1 (Λ : E.Lift G D) (x : ∀ n, Hc (schFn q) κ k n 2) (hx : IsFirstChernFamily q D κ k x) :
    ∃ (c : CH.Cn (gG k n G ⋙ OM _ ((PAlg.base l).cris n)) 2) (hz : CH.d _ 2 c = 0),
      (CH.cx _).cls _ hz = (CH.Mor.restrict (OM _ ((PAlg.base l).cris n)) (gG k n G)).pull 2 (x n) ∧
      c = (lam k n Λ).coc ((PAlg.base l).cris n) (l * n) := by
  have h := hx n C (gG k n G) (lam k n Λ)
  exact ⟨_, h.choose, h.choose_spec, rfl⟩

theorem st2 (Λ : E.Lift G D) (s : ComposableArrows C 2) (y : (G.obj (s.obj (Fin.last 2))).1.obj.Acr n)
    (hy : y = dlog (DD k (G.obj (s.obj (Fin.last 2))).1.obj n) (l * n) ((lam k n Λ).r s).val) :
    E.IsLog (G.obj (s.obj (Fin.last 2))).1.obj n (E.tei (G.obj (s.obj (Fin.last 2))).1.obj (Λ.r s)) y := by
  rw [hy]
  have h1 : (G.obj (s.obj (Fin.last 2))).1.obj.sharp (Λ.r s).val = 1 :=
    sharp_r Λ (s.map' 0 1) (s.map' 1 2) (s.map' 0 2) (by rw [← Functor.map_comp]; rfl)
  exact isLog_dlog k _ n _ h1 _ (lam_r k n Λ s)

theorem st3 (Λ : E.Lift G D) (x : ∀ n, Hc (schFn q) κ k n 2) (hx : IsFirstChernFamily q D κ k x) :
    ∃ (z : CH.Cn (G ⋙ CH.modF (AcrEl (PX q κ) n)) 2) (hz : CH.d _ 2 z = 0), Λ.IsCoc n z ∧
      (CH.cx _).cls z hz = (CH.Mor.restrict (CH.modF (AcrEl (PX q κ) n)) G).pull 2 (β (schFn q) κ k n 2 (x n)) :=
  pull_transport' (Oc (schFn q) κ k n) (CH.modF (AcrEl ((schFn q).pt κ) n)) (βMor (schFn q) κ k n) G (x n)
    (st1 k n Λ x hx) (fun z => Λ.IsCoc n z) (fun z c hs hc s => st2 k n Λ s _ ((hs s).trans (congrArg _ (congrFun hc s))))
end

theorem main : ∀ (l : ℕ) [Fact l.Prime], FirstChernCompatible l := by
  intro l _ O _ X q κ k D x hx C _ G Λ n
  exact st3 k n Λ x hx

end GlobalTheory.CompanionTheory.FirstChernComparison
