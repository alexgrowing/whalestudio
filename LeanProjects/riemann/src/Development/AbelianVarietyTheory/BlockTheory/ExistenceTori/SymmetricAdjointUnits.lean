import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.JetChartLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubicalPullBaseChangeSt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RigidAdjointFrameLaws

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws

section Gen

variable {X Y : Scheme.{0}} (L : LB X)

def unitGen {B : Type} [CommRing B] (u : Bˣ) :
    LB.Gen (LB.LinComb L (Y := Sp B) (K := PEmpty) PEmpty.elim PEmpty.elim) where
  s := fun _ => res le_top (unitOn u)

def isoGen {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X))
    (ε' : K' → ℤ) (w : LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')) :
    LB.Gen (LB.LinComb L (K := K' ⊕ K) (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k)) where
  s := fun j => res
    (le_inf (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k))
      (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)) :
      LB.wchart L (Sum.elim φ' φ) j ≤ LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inr))
    (w.s (j ∘ Sum.inl, j ∘ Sum.inr))

end Gen

variable {X₀ : Scheme.{0}} {S : Type} [CommRing S]

section Group

variable (G : Over X₀) [GrpObj G] [IsCommMonObj G]

def lamφ {T : Over X₀} (p : Fin 2 → (T ⟶ G)) : ULift.{0} (Finset (Fin 2)) → (T.left ⟶ G.left) :=
  fun I => (psum G p I.down).left

def lamε : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)

def IsRigAdj (L : LB G.left) (α β : G ⟶ G)
    (w : LB.Iso (cubeLB G ![fst G G ≫ α, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ β] L)) : Prop :=
  w.IsGen ∧
  LB.Gen.Corr L _ _ (Y := G.left) _ _
    (LB.pullGen L _ _
      (isoGen L (lamφ G ![fst G G ≫ α, snd G G]) lamε (lamφ G ![fst G G, snd G G ≫ β]) lamε w)
      (lift (𝟙 G) (1 : G ⟶ G)).left) (LB.oneGen L) ∧
  LB.Gen.Corr L _ _ (Y := G.left) _ _
    (LB.pullGen L _ _
      (isoGen L (lamφ G ![fst G G ≫ α, snd G G]) lamε (lamφ G ![fst G G, snd G G ≫ β]) lamε w)
      (lift (1 : G ⟶ G) (𝟙 G)).left) (LB.oneGen L)

variable (x : Sp S ⟶ X₀) {d : ℕ}

omit [GrpObj G] [IsCommMonObj G] in

def jPt (j : JetPts G x d) (n m : ℕ) (k : Fin n) : algO x (Jet S (Fin n × Fin d) m) ⟶ G :=
  algMap x (jetIn k) ≫ j m

abbrev FrameFam (L : LB G.left) (j : JetPts G x d) : Type :=
  ∀ m : ℕ, LB.Gen (cubeLB G (jPt G x j 2 m) L)

def subst2 {n : ℕ} (m : ℕ) (a b : Germ.Pt S n d) :
    Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m :=
  jetSubstPS fun p : Fin 2 × Fin d => (![a, b] : Fin 2 → Germ.Pt S n d) p.1 p.2

variable {G x}

def frAt {L : LB G.left} {j : JetPts G x d} (e : FrameFam G x L j) {n : ℕ} (m : ℕ) (a b : Germ.Pt S n d) :
    LB.Gen (LB.LinComb L (fun I => (algMap x (subst2 m a b)).left ≫ lamφ G (jPt G x j 2 m) I) lamε) :=
  LB.pullGen L (lamφ G (jPt G x j 2 m)) lamε (e m) (algMap x (subst2 m a b)).left

def IsFrame {L : LB G.left} {j : JetPts G x d} (e : FrameFam G x L j) : Prop :=
  (∀ m, (e m).IsGen) ∧
  (∀ m, LB.Gen.Corr L _ _ (lamφ G (jPt G x j 2 m)) lamε
    (LB.pullGen L (lamφ G (jPt G x j 2 (m + 1))) lamε (e (m + 1))
      (algMap x (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left) (e m)) ∧
  (∀ m, LB.Gen.Corr L _ _ _ _ (frAt e (n := 1) m 0 (Germ.pt S d 0)) (LB.oneGen L)) ∧
  (∀ m, LB.Gen.Corr L _ _ _ _ (frAt e (n := 1) m (Germ.pt S d 0) 0) (LB.oneGen L))

def cubAt {L : RigLB G} (c : CubicalStr G L) (j : JetPts G x d) (m : ℕ) :
    LB.Gen (LB.LinComb L.L (fun I => (lift (jPt G x j 3 m 0) (lift (jPt G x j 3 m 1) (jPt G x j 3 m 2))).left ≫
      thφ G (x3 G) I) thε) :=
  LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift (jPt G x j 3 m 0) (lift (jPt G x j 3 m 1) (jPt G x j 3 m 2))).left

def FrameFamilyFirstCubicLaw {L : RigLB G} (c : CubicalStr G L) {j : JetPts G x d} (e : FrameFam G x L.L j)
    (F : Fin d → Germ.PS S 2 d) (ph1 : Germ.PS S 3 d) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧
    LB.Gen.Corr L.L _ _ _ _
      (LB.mulGen L.L _ _ _ _
        (LB.mulGen L.L _ _ _ _ (frAt e (n := 3) m (Germ.pt S d 0) (Germ.pt S d 2))
          (frAt e (n := 3) m (Germ.pt S d 1) (Germ.pt S d 2)))
        (cubAt c j m))
      (LB.mulGen L.L _ _ _ _ (unitGen L.L u)
        (frAt e (n := 3) m (Germ.addOf F (Germ.pt S d 0) (Germ.pt S d 1)) (Germ.pt S d 2)))

def FrameFamilySecondCubicLaw {L : RigLB G} (c : CubicalStr G L) {j : JetPts G x d} (e : FrameFam G x L.L j)
    (F : Fin d → Germ.PS S 2 d) (ph2 : Germ.PS S 3 d) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph2 ∧
    LB.Gen.Corr L.L _ _ _ _
      (LB.mulGen L.L _ _ _ _
        (LB.mulGen L.L _ _ _ _ (frAt e (n := 3) m (Germ.pt S d 0) (Germ.pt S d 1))
          (frAt e (n := 3) m (Germ.pt S d 0) (Germ.pt S d 2)))
        (cubAt c j m))
      (LB.mulGen L.L _ _ _ _ (unitGen L.L u)
        (frAt e (n := 3) m (Germ.pt S d 0) (Germ.addOf F (Germ.pt S d 1) (Germ.pt S d 2))))

def SymIs {L : LB G.left} {j : JetPts G x d} (e : FrameFam G x L j) (sy : Germ.PS S 2 d) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧
    LB.Gen.Corr L _ _ _ _
      (frAt e (n := 2) m (Germ.pt S d 1) (Germ.pt S d 0))
      (LB.mulGen L _ _ (lamφ G (jPt G x j 2 m)) lamε (unitGen L u) (e m))

def AdjVia {L : LB G.left} {j : JetPts G x d} (e : FrameFam G x L j) {α β : G ⟶ G}
    (w : LB.Iso (cubeLB G ![fst G G ≫ α, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ β] L))
    (A B : Germ.Pt S 1 d) (ad : Germ.PS S 2 d) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m ad ∧
    LB.Gen.Corr L _ _ _ _
      (LB.mulGen L _ _ _ _
        (LB.pullGen L _ _
          (isoGen L (lamφ G ![fst G G ≫ α, snd G G]) lamε (lamφ G ![fst G G, snd G G ≫ β]) lamε w)
          (lift (jPt G x j 2 m 0) (jPt G x j 2 m 1)).left)
        (frAt e (n := 2) m (Germ.comp1 A (Germ.pt S d 0)) (Germ.pt S d 1)))
      (LB.mulGen L _ _ _ _ (unitGen L u)
        (frAt e (n := 2) m (Germ.pt S d 0) (Germ.comp1 B (Germ.pt S d 1))))

def AdjIs {L : LB G.left} {j : JetPts G x d} (e : FrameFam G x L j) (α β : G ⟶ G)
    (A B : Germ.Pt S 1 d) (ad : Germ.PS S 2 d) : Prop :=
  ∃ w : LB.Iso (cubeLB G ![fst G G ≫ α, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ β] L),
    IsRigAdj G L α β w ∧ AdjVia e w A B ad

theorem comp_lamφ {T T' : Over X₀} (h : T' ⟶ T) (p : Fin 2 → (T ⟶ G)) (I : ULift.{0} (Finset (Fin 2))) :
    h.left ≫ lamφ G p I = lamφ G (fun k => h ≫ p k) I := by
  simp only [lamφ, psum]
  rw [foldr_padd_pre, Over.comp_left]

end Group

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def HasUnits (t : SAB H X₀) (x : Sp S ⟶ X₀) {d : ℕ} {j : JetPts t.G x d} (e : FrameFam t.G x t.PP.L j)
    (F : Fin d → Germ.PS S 2 d) (A : 𝓞 E → Germ.Pt S 1 d) (ph1 ph2 : Germ.PS S 3 d) (sy : Germ.PS S 2 d)
    (ad : 𝓞 E → Germ.PS S 2 d) : Prop :=
  IsFrame e ∧ FrameFamilyFirstCubicLaw t.cub e F ph1 ∧ FrameFamilySecondCubicLaw t.cub e F ph2 ∧ SymIs e sy ∧
    ∀ a, AdjIs e (t.act.act a) (t.act.act (H.bar a)) (A a) (A (H.bar a)) (ad a)

def Realises [StarRing (𝓞 E)] (t : SAB H X₀) (x : Sp S ⟶ X₀) {d : ℕ} (j : JetPts t.G x d)
    (e : FrameFam t.G x t.PP.L j) (B : Germ.FB S d (𝓞 E)) : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) ∧
  IsFormalParam t.G x j ∧ LawIs t.G x j B.G.F ∧ (∀ a, EndIs t.G x j (t.act.act a) (B.A.act a)) ∧
    HasUnits t x e B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad

end GlobalTheory.IndefiniteRowSideFullHecke.RigidAdjointFrameLaws
