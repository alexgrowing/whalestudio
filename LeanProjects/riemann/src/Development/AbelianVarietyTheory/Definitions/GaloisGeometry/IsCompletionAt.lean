import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRankOneIdem
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.RangeOnLieUnitEOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField TensorProduct

namespace GlobalTheory.UPel.HT.WPart

open GlobalTheory.UPel.HT GlobalTheory.VDiv GlobalTheory.VDefo GlobalTheory.MoritaHT GlobalTheory.IwLevel GlobalTheory.DrinLev.HT IsLocalRing

variable {p : ℕ} [Fact p.Prime]

section Corner

variable {Λ : Type} [Ring Λ] {Ow : Type} [CommRing Ow] {n : ℕ} [NeZero n] {T : Type} [CommRing T]
  [Algebra Ow T]

def IsWCorner (πw : Λ →+* Matrix (Fin n) (Fin n) Ow) (E : Λ) {G : PDivGroup p T}
    (ρ : PDivGroup.Action Λ G) (H : VarpiDivModule p Ow T) (iH : H.G ⟶ G) (rH : G ⟶ H.G) : Prop :=
  IsIdempotentElem E ∧ πw E = unitE Ow n ∧ (∀ x ∈ RingHom.ker πw, E * x = 0) ∧
    iH ≫ rH = 𝟙 H.G ∧ rH ≫ iH = (ρ E : G ⟶ G) ∧
    ∀ (a : Ow) (c : Λ), πw c = Matrix.scalar (Fin n) a →
      (H.ι a : H.G ⟶ H.G) = iH ≫ (ρ c : G ⟶ G) ≫ rH

theorem IsWCorner.rH_eq {πw : Λ →+* Matrix (Fin n) (Fin n) Ow} {E : Λ} {G : PDivGroup p T}
    {ρ : PDivGroup.Action Λ G} {H : VarpiDivModule p Ow T} {iH : H.G ⟶ G} {rH : G ⟶ H.G}
    (h : IsWCorner πw E ρ H iH rH) : (ρ E : G ⟶ G) ≫ rH = rH := by
  rw [← h.2.2.2.2.1, Category.assoc, h.2.2.2.1, Category.comp_id]

theorem IsWCorner.iH_eq {πw : Λ →+* Matrix (Fin n) (Fin n) Ow} {E : Λ} {G : PDivGroup p T}
    {ρ : PDivGroup.Action Λ G} {H : VarpiDivModule p Ow T} {iH : H.G ⟶ G} {rH : G ⟶ H.G}
    (h : IsWCorner πw E ρ H iH rH) : iH ≫ (ρ E : G ⟶ G) = iH := by
  rw [← h.2.2.2.2.1, ← Category.assoc, h.2.2.2.1, Category.id_comp]

theorem IsWCorner.corner_congr {πw : Λ →+* Matrix (Fin n) (Fin n) Ow} {E : Λ} {G : PDivGroup p T}
    {ρ : PDivGroup.Action Λ G} {H : VarpiDivModule p Ow T} {iH : H.G ⟶ G} {rH : G ⟶ H.G}
    (h : IsWCorner πw E ρ H iH rH) {c c' : Λ} (hc : πw c = πw c') :
    iH ≫ (ρ c : G ⟶ G) ≫ rH = iH ≫ (ρ c' : G ⟶ G) ≫ rH := by
  have key : ∀ d : Λ, (ρ d : G ⟶ G) ≫ rH = (ρ (E * d) : G ⟶ G) ≫ rH := fun d => by
    rw [map_mul, End.mul_def, Category.assoc, h.rH_eq]
  have e : E * c = E * c' := by
    have := h.2.2.1 (c - c') (by rw [RingHom.mem_ker, map_sub, hc, sub_self])
    rwa [mul_sub, sub_eq_zero] at this
  rw [key c, key c', e]

end Corner

end GlobalTheory.UPel.HT.WPart

namespace GlobalTheory.UPel.HT.WPart

open GlobalTheory.UPel.HT GlobalTheory.VDiv GlobalTheory.VDefo GlobalTheory.MoritaHT GlobalTheory.IwLevel GlobalTheory.DrinLev.HT IsLocalRing

variable {p : ℕ} [Fact p.Prime]

instance neZero_m (D : Datum p) : NeZero D.m := ⟨D.m_pos.ne'⟩

def IsCompletionAt {D : Datum p} {Ow : Type} [CommRing Ow] [IsLocalRing Ow] (b : Base D Ow) (i₀ : Fin D.a)
    (w : Ideal (𝓞 D.F)) : Prop :=
  ∀ k : ℕ, (maximalIdeal Ow ^ k).comap (b.t i₀) = w ^ k ∧
    Function.Surjective ((Ideal.Quotient.mk (maximalIdeal Ow ^ k)).comp (b.t i₀))

structure WProj (D : Datum p) {Ow : Type} [CommRing Ow] [Algebra ℤ_[p] Ow] (b : Base D Ow) (i₀ : Fin D.a) where

  π : ℤ_[p] ⊗[ℤ] D.O →+* Matrix (Fin D.m) (Fin D.m) Ow

  surj : Function.Surjective π

  padic : ∀ c : ℤ_[p], π (c ⊗ₜ 1) = Matrix.scalar (Fin D.m) (algebraMap ℤ_[p] Ow c)

  scalar : ∀ c : 𝓞 D.F, π (1 ⊗ₜ algebraMap (𝓞 D.F) D.O c) = Matrix.scalar (Fin D.m) (b.t i₀ c)

variable {D : Datum p} {Ow : Type} [CommRing Ow] [Algebra ℤ_[p] Ow] {b : Base D Ow} {i₀ : Fin D.a}

structure WPartOf (πw : WProj D b i₀) {T : Type} [CommRing T] [Algebra Ow T] (A : Over (Sp T)) [GrpObj A]
    [IsCommMonObj A] (a : Out.RingAct A D.O) (H : VarpiDivModule p Ow T) where

  G : PDivGroup p T

  t : G.TorsionTower A

  E : ℤ_[p] ⊗[ℤ] D.O

  iH : H.G ⟶ G

  rH : G ⟶ H.G

  corner : IsWCorner πw.π E (t.ringAct a).padicExtend H iH rH

namespace WPartOf

variable {πw : WProj D b i₀} {T : Type} [CommRing T] [Algebra Ow T] {A : Over (Sp T)} [GrpObj A]
  [IsCommMonObj A] {a : Out.RingAct A D.O} {H : VarpiDivModule p Ow T}

theorem iH_rH (w : WPartOf πw A a H) : w.iH ≫ w.rH = 𝟙 H.G := w.corner.2.2.2.1

theorem rH_iH (w : WPartOf πw A a H) :
    w.rH ≫ w.iH = ((w.t.ringAct a).padicExtend w.E : w.G ⟶ w.G) := w.corner.2.2.2.2.1

theorem π_E (w : WPartOf πw A a H) : πw.π w.E = unitE Ow D.m := w.corner.2.1

theorem ι_eq (w : WPartOf πw A a H) (x : Ow) (c : ℤ_[p] ⊗[ℤ] D.O) (hc : πw.π c = Matrix.scalar (Fin D.m) x) :
    (H.ι x : H.G ⟶ H.G) = w.iH ≫ ((w.t.ringAct a).padicExtend c : w.G ⟶ w.G) ≫ w.rH :=
  w.corner.2.2.2.2.2 x c hc

end WPartOf

abbrev WPart (πw : WProj D b i₀) {T : Type} [CommRing T] [Algebra Ow T] {N : ℕ}
    (o : Obj b N (spMap (algebraMap Ow T))) (H : VarpiDivModule p Ow T) : Type 1 :=
  WPartOf πw o.A (htAct o) H

def IsWPart (πw : WProj D b i₀) {T : Type} [CommRing T] [Algebra Ow T] {N : ℕ}
    (o : Obj b N (spMap (algebraMap Ow T))) (H : VarpiDivModule p Ow T) : Prop :=
  Nonempty (WPart πw o H)

section Pull

variable {πw : WProj D b i₀} {T T' : Type} [CommRing T] [Algebra Ow T] [CommRing T'] [Algebra Ow T']
  {σ : T →+* T'}

def TowerInduced {G : PDivGroup p T} {G' : PDivGroup p T'} {A : Over (Sp T)} [GrpObj A] {A' : Over (Sp T')}
    [GrpObj A'] (t : G.TorsionTower A) (t' : G'.TorsionTower A') (φ : A'.left ⟶ A.left)
    (u : PDivGroup.SemiHom σ G' G) : Prop :=
  ∀ k, spMap (u.app k).toRingHom ≫ (t.y k).left = (t'.y k).left ≫ φ

theorem TowerInduced.unique {G : PDivGroup p T} {G' : PDivGroup p T'} {A : Over (Sp T)} [GrpObj A]
    {A' : Over (Sp T')} [GrpObj A'] {t : G.TorsionTower A} {t' : G'.TorsionTower A'} {φ : A'.left ⟶ A.left}
    {u v : PDivGroup.SemiHom σ G' G} (hu : TowerInduced t t' φ u) (hv : TowerInduced t t' φ v) : u = v :=
  PDivGroup.SemiHom.ext_apply fun k a => RingHom.congr_fun (t.ringHom_ext ((hu k).trans (hv k).symm)) a

theorem TowerInduced.exists {G : PDivGroup p T} {G' : PDivGroup p T'} {A : Over (Sp T)} [GrpObj A]
    {A' : Over (Sp T')} [GrpObj A'] (t : G.TorsionTower A) (t' : G'.TorsionTower A') {φ : A'.left ⟶ A.left}
    (h : IsGrpPullback A' A (spMap σ) φ) : ∃ u : PDivGroup.SemiHom σ G' G, TowerInduced t t' φ u :=
  ⟨_, t'.semiOf_y t (GlobalTheory.PDiv.grpMor_of_isGrpPullback h)⟩

variable {A : Over (Sp T)} [GrpObj A] [IsCommMonObj A] {A' : Over (Sp T')} [GrpObj A'] [IsCommMonObj A']
  {a : Out.RingAct A D.O} {a' : Out.RingAct A' D.O} {H : VarpiDivModule p Ow T} {H' : VarpiDivModule p Ow T'}

def IsInducedOf (w : WPartOf πw A a H) (w' : WPartOf πw A' a' H') (φ : A'.left ⟶ A.left)
    (s : PDivGroup.SemiHom σ H'.G H.G) : Prop :=
  ∃ u : PDivGroup.SemiHom σ w'.G w.G, TowerInduced w.t w'.t φ u ∧ s = cornerMap w'.iH w.rH u

theorem IsInducedOf.unique {w : WPartOf πw A a H} {w' : WPartOf πw A' a' H'} {φ : A'.left ⟶ A.left}
    {s s' : PDivGroup.SemiHom σ H'.G H.G} (h : IsInducedOf w w' φ s) (h' : IsInducedOf w w' φ s') : s = s' := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨u', hu', rfl⟩ := h'
  rw [hu.unique hu']

theorem IsInducedOf.exists (w : WPartOf πw A a H) (w' : WPartOf πw A' a' H') {φ : A'.left ⟶ A.left}
    (h : IsGrpPullback A' A (spMap σ) φ) : ∃ s : PDivGroup.SemiHom σ H'.G H.G, IsInducedOf w w' φ s := by
  obtain ⟨u, hu⟩ := TowerInduced.exists w.t w'.t h
  exact ⟨_, u, hu, rfl⟩

end Pull

end GlobalTheory.UPel.HT.WPart

namespace GlobalTheory.UPel.HT.WPart

open GlobalTheory.UPel.HT GlobalTheory.VDiv GlobalTheory.VDefo GlobalTheory.MoritaHT GlobalTheory.IwLevel GlobalTheory.DrinLev.HT IsLocalRing

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {Ow : Type} [CommRing Ow] [Algebra ℤ_[p] Ow] {b : Base D Ow}
  {i₀ : Fin D.a} {πw : WProj D b i₀} {N : ℕ}

section ObjPull

variable {T T' : Type} [CommRing T] [Algebra Ow T] [CommRing T'] [Algebra Ow T'] {σ : T →+* T'}
  {o : Obj b N (spMap (algebraMap Ow T))} {o' : Obj b N (spMap (algebraMap Ow T'))}
  {H : VarpiDivModule p Ow T} {H' : VarpiDivModule p Ow T'}

def IsInduced (w : WPart πw o H) (w' : WPart πw o' H') (m : ObjMap o' o (spMap σ))
    (s : PDivGroup.SemiHom σ H'.G H.G) : Prop :=
  IsInducedOf w w' m.φ s

theorem IsInduced.exists (w : WPart πw o H) (w' : WPart πw o' H') (m : ObjMap o' o (spMap σ)) :
    ∃ s : PDivGroup.SemiHom σ H'.G H.G, IsInduced w w' m s :=
  IsInducedOf.exists w w' m.cart

theorem IsInduced.unique {w : WPart πw o H} {w' : WPart πw o' H'} {m : ObjMap o' o (spMap σ)}
    {s s' : PDivGroup.SemiHom σ H'.G H.G} (h : IsInduced w w' m s) (h' : IsInduced w w' m s') : s = s' :=
  IsInducedOf.unique h h'

end ObjPull

section Defo

variable {Or : Type} [CommRing Or] [IsLocalRing Or] [Algebra Ow Or]
  {Hb : VarpiDivModule p Ow (ResidueField Or)} {ox : Obj b N (spMap (algebraMap Ow (ResidueField Or)))}

def IsPointDefo (wx : WPart πw ox Hb) (A : LocAlg Ow Or) {oA : Obj b N (spMap (algebraMap Ow A.A))}
    (m : ObjMap ox oA (spMap A.red)) (Dd : Defo p Hb A.A A.red) : Prop :=
  ∃ wA : WPart πw oA Dd.H, IsInduced wA wx m Dd.s

end Defo

section Levels

variable {T : Type} [CommRing T] [Algebra Ow T] {o : Obj b N (spMap (algebraMap Ow T))}
  {H : VarpiDivModule p Ow T}

def IsCornerMod (πw : WProj D b i₀) (e : D.O) (ϖ : Ow) (k : ℕ) : Prop :=
  ∀ i j, πw.π (1 ⊗ₜ e) i j - unitE Ow D.m i j ∈ Ideal.span {ϖ ^ k}

def LevelMatch (w : WPart πw o H) {wI : Ideal (𝓞 D.F)} {k : ℕ} {e : D.O} {ϖ : Ow}
    (αh : HTLevel o wI k e) (αl : Level p H.G H.ι ϖ D.n k T) : Prop :=
  ∀ (x : Fin D.n → 𝓞 D.F) (y : Fin D.n → Ow), (∀ i, y i - b.t i₀ (x i) ∈ Ideal.span {ϖ ^ k}) →
    (αh.α fun i => Ideal.Quotient.mk _ (x i)).left =
      spMap ((αl.α fun i => Ideal.Quotient.mk _ (y i)).comp
        (w.iH.app k : w.G.A k →ₐ[T] H.G.A k)).toRingHom ≫ (w.t.y k).left

end Levels

end GlobalTheory.UPel.HT.WPart

namespace GlobalTheory.UPel.HT.WPart

open GlobalTheory.UPel.HT GlobalTheory.VDiv GlobalTheory.VDefo GlobalTheory.MoritaHT

section Basic₂

example (p : ℕ) [Fact p.Prime] :
    IsWCorner (Matrix.scalar (Fin 1) : ℤ_[p] →+* Matrix (Fin 1) (Fin 1) ℤ_[p]) 1
      (VarpiDivModule.muMod p).G.padicAction (VarpiDivModule.muMod p) (𝟙 _) (𝟙 _) := by
  refine ⟨IsIdempotentElem.one, by rw [map_one, unitE_one], fun x hx => ?_, Category.id_comp _, ?_,
    fun a c hc => ?_⟩
  · rw [_root_.one_mul]
    rw [RingHom.mem_ker] at hx
    exact (Matrix.scalar_inj).1 (hx.trans (map_zero _).symm)
  · rw [map_one, Category.id_comp]; rfl
  · obtain rfl := (Matrix.scalar_inj).1 hc.symm
    rw [Category.id_comp, Category.comp_id]
    rfl

example (p : ℕ) [Fact p.Prime] : (VarpiDivModule.muMod p).HasOHeight 1 ∧ ¬ (VarpiDivModule.muMod p).HasOHeight 0 :=
  ⟨VarpiDivModule.muMod_hasOHeight, fun h => one_ne_zero (h.2.2.trans (zero_mul _))⟩

example {p : ℕ} [Fact p.Prime] {D : Datum p} {Ow : Type} [CommRing Ow] [Algebra ℤ_[p] Ow] {b : Base D Ow}
    {i₀ : Fin D.a} (πw : WProj D b i₀) (e : D.O) (ϖ : Ow) : IsCornerMod πw e ϖ 0 := fun i j => by
  rw [pow_zero, Ideal.span_singleton_one]; exact Submodule.mem_top

example {p : ℕ} [Fact p.Prime] {D : Datum p} {Ow : Type} [CommRing Ow] [Algebra ℤ_[p] Ow] {b : Base D Ow}
    {i₀ : Fin D.a} (πw : WProj D b i₀) :
    πw.π 1 = 1 ∧ πw.π ((p : ℤ_[p]) ⊗ₜ 1) = Matrix.scalar (Fin D.m) (p : Ow) := by
  refine ⟨map_one _, ?_⟩
  rw [πw.padic, map_natCast]

end Basic₂

end GlobalTheory.UPel.HT.WPart
