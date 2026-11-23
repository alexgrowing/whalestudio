import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.EdgeRed

theorem res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res h (Sec.res g x) = Sec.res (h ≫ g) x := by
  simp [Sec.res]

theorem res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun t => t.hom x) h).symm

variable {C C' : Type 1} [Category.{0} C] [Category.{0} C']

def redResMor (hS : KapSpec) (hK : KapRed) (hR : InRed) {Q q : ℕ} [NeZero Q] [NeZero q] (h : q ∣ Q)
    (P : Probe C Q) (P' : Probe C' q) (m : Mor P.L P'.L (RingHom.id ℤ))
    (g : ∀ c : C', P'.U c ⟶ P.U (m.G.obj c))
    (hg : ∀ {c c' : C'} (φ : c ⟶ c'), g c' ≫ (P.S.map (m.G.map φ)).unop = (P'.S.map φ).unop ≫ g c)
    (hτ : ∀ c (f : LocallyConstant (P.U (m.G.obj c)) (ZMod Q)),
      m.τ c f = lcRes q (g c) (f.map (ZMod.castHom h (ZMod q))))
    (hζ : ∀ c, (P'.ζ c).1 = (primRes (g c) (P.ζ _)).1 ^ (Q / q)) (i : ℤ) :
    ResMor (P.res i) (P'.res i) m where
  τ s c :=
    { toFun := fun x => Sec.res (g c) ((redMap Q q i).app (P.U (m.G.obj c)) (s : ℤ) x)
      map_zero' := by simp
      map_add' := fun x y => by simp }
  nat s {c c'} φ x := by
    change Sec.res (g c') ((redMap Q q i).app _ (s : ℤ) (Sec.res (P.S.map (m.G.map φ)).unop x)) =
      Sec.res (P'.S.map φ).unop (Sec.res (g c) ((redMap Q q i).app _ (s : ℤ) x))
    rw [← (redMap Q q i).nat, res_res, res_res, hg]
  ι c x := by
    change Sec.res (g c) ((redMap Q q i).app _ 0 (Sec.map (resι _ (tw Q i)) (kap i (P.ζ (m.G.obj c)) x))) =
      Sec.map (resι _ (tw q i)) (kap i (P'.ζ c) (m.τ c x))
    rw [(redMap Q q i).nat, res_map, (hS Q i _ (P.ζ (m.G.obj c)) x).2.2 _ (g c),
      hK hR Q q h i _ (primRes (g c) (P.ζ (m.G.obj c))) (P'.ζ c) (hζ c), hτ]
    rfl
  dv s c x := by
    change Sec.res (g c) ((redMap Q q i).app _ ((s + 1 : ℕ) : ℤ) (Sec.map ((GlobalTheory.EtC.res _ (tw Q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) x)) =
      Sec.map ((GlobalTheory.EtC.res _ (tw q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) (Sec.res (g c) ((redMap Q q i).app _ (s : ℤ) x))
    rw [← (redMap Q q i).comm, res_map]

theorem etRed : CrystallineSemistableComparison.E.EtSpec → CrystallineSemistableComparison.E.EdgeMap → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.RepOp → CrystallineSemistableComparison.E.KapSpec →
    CrystallineSemistableComparison.E.KapRed → CrystallineSemistableComparison.E.EtRed := by
  intro hSpec hEdge hRep hOpR hS hK hGen hR hOp Q q _ _ h C C' _ _ P P' X Y Y' m g hg hτ hy hζ i j x
  obtain ⟨a, ha⟩ := (hRep _ _ X (j : ℤ)).1 x
  have hE := (hSpec hGen Q C P X Y i j x).1 a ha
  have hE' := hEdge ℤ ℤ (RingHom.id ℤ) C C' P.L P'.L (P.res i) (P'.res i) m
    (redResMor hS hK hR h P P' m g hg hτ hζ i) j _ _ hE
  have hr : Rep (red Q q _ (j : ℤ) i x) ((redMap Q q i).app X (j : ℤ) a) :=
    hOpR hOp _ _ _ _ (redMap Q q i) X (j : ℤ) x a ha
  refine (hSpec hGen q C' P' X Y' i j (red Q q _ (j : ℤ) i x)).2 _ ⟨_, hr, ?_⟩
  convert hE' using 1
  funext t
  change Sec.res (Y'.y _) ((redMap Q q i).app X (j : ℤ) a) =
    Sec.res (g _) ((redMap Q q i).app _ (j : ℤ) (Sec.res (Y.y _) a))
  rw [← (redMap Q q i).nat, res_res, hy]

end GlobalTheory.CompanionTheory.EdgeRed
