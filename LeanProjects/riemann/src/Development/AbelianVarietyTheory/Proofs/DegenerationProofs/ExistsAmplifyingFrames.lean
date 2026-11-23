import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfFrames
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalBasisAlong

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.LN.LocalFrames

open GlobalTheory.FrameGen

variable {Z : Scheme.{0}} {G : Over Z} {L : LB G.left} {N : ℕ}

def IsPull {T T' : Over Z} (h : T' ⟶ T) (a : LB.Sec (LPow G L (N : ℤ) T)) (s : LB.Sec (LPow G L (N : ℤ) T')) : Prop :=
  ∀ (Y : Scheme.{0}) (r : Y ⟶ (T' ⊗ G).left) (z : Y) (J), Good L z J →
    sv G L N s r z J = sv G L N a (r ≫ (h ▷ G).left) z J

theorem IsPull.lin {T T' T'' : Over Z} {h : T' ⟶ T} {k : T'' ⟶ T} (g : T'' ⟶ T') (e : g ≫ h = k)
    {a : LB.Sec (LPow G L (N : ℤ) T)} {a' : LB.Sec (LPow G L (N : ℤ) T')} {s : LB.Sec (LPow G L (N : ℤ) T'')}
    (ha : IsPull h a a') (hs : IsPull k a s) : Lin G L N g (fun _ : Fin 1 => a') (fun _ => 1) s := by
  intro z J hJ
  subst e
  rw [Fin.sum_univ_one, gs_top, map_one, _root_.one_mul]
  refine (hs _ (𝟙 _) z J hJ).trans (Eq.trans ?_ (ha _ _ z J hJ).symm)
  rw [Category.id_comp, comp_whiskerRight, Over.comp_left]

theorem basisAlong_id {T T' : Over Z} {h : T' ⟶ T} {n : ℕ} {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)}
    {b' : Fin n → LB.Sec (LPow G L (N : ℤ) T')} (hb : ∀ i, IsPull h (b i) (b' i)) (H : BasisAlong G L N h b) :
    BasisAlong G L N (𝟙 _) b' := by
  intro s
  have key : ∀ c, Lin G L N (𝟙 _) b' c s ↔ Lin G L N h b c s := fun c =>
    forall_congr' fun z => forall_congr' fun J => forall_congr' fun hJ => by
      refine Eq.congr_right (Finset.sum_congr rfl fun i _ => congrArg _ ?_)
      refine (hb i _ _ z J hJ).trans ?_
      rw [← Over.comp_left, ← comp_whiskerRight, Category.id_comp]
      rfl
  simpa only [key] using H s

theorem exists_isFrame (hL : L.IsLB) {n : ℕ} (b : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk (⊤ : Z.Opens).ι)))
    (hb : ∀ (W : Type) [CommRing W] (χ : Sp W ⟶ (⊤ : Z.Opens).toScheme),
      BasisAlong G L N (Over.homMk χ rfl : Over.mk (χ ≫ (⊤ : Z.Opens).ι) ⟶ Over.mk (⊤ : Z.Opens).ι) b)
    {R : Type} [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ Z) :
    ∃ f : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x)), IsFrame G L N x f := by
  obtain ⟨yx⟩ := exists_lift x ⊤ (fun _ => trivial)
  choose f hf using fun i => exists_pull hL yx (b i)
  refine ⟨f, fun W _ _ _ _ φ gam _ χ h => ?_⟩
  obtain ⟨χ₀, rfl⟩ : ∃ χ₀ : Sp W ⟶ (⊤ : Z.Opens).toScheme, χ₀ ≫ (⊤ : Z.Opens).ι = χ :=
    (exists_lift χ ⊤ (fun _ => trivial)).elim fun y => ⟨y.left, Over.w y⟩
  obtain ⟨y⟩ := exists_lift (jK W ≫ χ₀ ≫ (⊤ : Z.Opens).ι) ⊤ (fun _ => trivial)
  choose b' hb' using fun i =>
    exists_pull hL (Over.homMk χ₀ rfl : Over.mk (χ₀ ≫ (⊤ : Z.Opens).ι) ⟶ Over.mk (⊤ : Z.Opens).ι) (b i)
  refine ⟨b', basisAlong_id hb' (hb W χ₀), fun i => ?_⟩
  obtain ⟨s, hs⟩ := exists_pull hL y (b i)
  exact ⟨s, IsPull.lin _ (hom_unique _ _) (hf i) hs, IsPull.lin _ (hom_unique _ _) (hb' i) hs⟩

theorem ampFrames_and_isFrame : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (P : PolAV (Sp R)) (N : ℕ), 1 ≤ N →
    Nonempty (AmpFrames P.A P.L N) ∧ ∃ (n : ℕ) (f : Fin n → _), IsFrame P.A P.L N (jK R) f := by
  intro hL _ R _ _ _ _ P N hN
  refine ⟨⟨(PolFrames.exists_ampFrames_local N hL.secBaseChange R P hN).choose⟩, N ^ P.g, ?_⟩
  obtain ⟨U, hU, b, hb⟩ := PolFrames.exists_local_basisAlong N hL.secBaseChange P hN (IsLocalRing.closedPoint R)
  obtain rfl : U = ⊤ := DVR.eq_top_of_closedPoint_mem U hU
  exact exists_isFrame P.isLB b hb (jK R)

end GlobalTheory.LN.LocalFrames
end
