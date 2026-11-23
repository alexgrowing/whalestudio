import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IntegOfMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.CongKSOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.EtLevForget

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open GlobalTheory.GalV (HTower Splits)
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD TjE KSOKE)
open scoped TensorProduct

namespace UpperTheory.Gal.Int.Geo

section Obj

variable {q : ℕ} [Fact q.Prime] {D : Datum q} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R'] {b : Base D R}
  {gb : GBase D.toG R'} {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R'} {N N₀ : ℕ}

structure QMap (o' : GObj gb N s') (o : Obj b N₀ s) (f : S' ⟶ S) (c : ℕ) where
  φ : o'.A.left ⟶ o.A.left
  φ₂ : (G2 o'.A).left ⟶ (G2 o.A).left
  cart : IsGrpPullback o'.A o.A f φ
  sq : IsSquare φ φ₂
  act : ∀ x : D.O, (o'.act.act x).left ≫ φ = φ ≫ (o.act.act x).left
  pol : LBIso o'.P (o.P.pull φ₂)
  eta : ∀ y : D.La, (o'.eta (c • y)).left ≫ φ = f ≫ (o.eta y).left

structure Cls {𝔞 : Ideal (𝓞 D.F)} (E : EtModel b N₀ 𝔞 1) (β : R →+* R') (o' : GObj gb N s') (c : ℕ) (a : 𝓞 D.F) where
  j : S' ⟶ E.X
  ov : j ≫ E.s = s' ≫ spMap β
  m : QMap o' E.univ j c
  lv : ∀ y : D.La, (o'.eta (algebraMap (𝓞 D.F) D.O a • y)).left ≫ m.φ = j ≫ (E.lv y).left

def Cls.pw {𝔞 : Ideal (𝓞 D.F)} {E : EtModel b N₀ 𝔞 1} {β : R →+* R'} {o' : GObj gb N s'} {c : ℕ} {a : 𝓞 D.F} (C : Cls E β o' c a) (k : ℕ) :
    (GlobalTheory.KS.pow o'.A k).left ⟶ (GlobalTheory.KS.pow E.univ.A k).left := GlobalTheory.KS.powMap C.j C.m.φ C.m.cart.1.w k

def Match (b : Base D R) (gb : GBase D.toG R') (β : R →+* R') : Prop := gb.ρ = β b.ρ ∧ ∀ i, gb.t i = β.comp (b.t i)

end Obj

def IsGen {A : Type} [CommRing A] (a : A) (N : ℕ) (𝔞 : Ideal A) : Prop := (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 = Ideal.span {(N : A)}

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G}

abbrev datAt {q : ℕ} [Fact q.Prime] {r : ℤ} {𝔴 : Ideal (𝓞 D.F)} (h : AtPrime D q r 𝔴)
    (sp : Nonempty ((D.O ⊗[ℤ] ℤ_[q]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[q]))) : Datum q :=
  { D with disc_p := h.disc, split := ⟨r, h.root⟩, splitP := sp, perfP := h.perf }

variable {E : Type} [Field E] [NumberField E]

structure Site (gb : GBase D.toG E) (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) : Type 1 where
  atq : AtPrime D q r 𝔴
  sp : Nonempty ((D.O ⊗[ℤ] ℤ_[q]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[q]))
  f : ℕ
  b : Base (datAt atq sp) (Ow w)
  mat : Match (D := datAt atq sp) b gb (algebraMap (Ow w) E)
  N₀ : ℕ
  𝔞 : Ideal (𝓞 D.F)
  std : Std f b N₀ r 𝔴
  qmem : (q : 𝓞 E) ∈ w.asIdeal
  norm : Ideal.absNorm w.asIdeal = q ^ f
  cop : N₀.Coprime p
  sup : 𝔞 ⊔ 𝔴 = ⊤
  upow : ∃ e : ℕ, uId D q r ^ e ≤ 𝔞
  lev : 𝔫 = Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞
  M : Model b N₀
  Y : EtModel b N₀ 𝔞 1
  π : Y.X ⟶ M.X
  ov : π ≫ M.s = Y.s
  mπ : ObjMap Y.univ M.univ π
  fin : IsFinite π
  et : Etale π
  proj : ∀ k, IsProjOver ((GlobalTheory.KS.pow Y.univ.A k).hom ≫ Y.s)
  dim : ∀ k, ∃ d, SmoothOfRelativeDimension d ((GlobalTheory.KS.pow Y.univ.A k).hom ≫ Y.s)

section Tower

variable {gb : GBase D.toG E} {w : HeightOneSpectrum (𝓞 E)} {q : ℕ} [Fact q.Prime] {r : ℤ} {𝔴 𝔫 : Ideal (𝓞 D.F)}
  (S : Site gb w q r 𝔴 𝔫) {k : ℕ} (T : KS L gb k)

abbrev Site.Cl {X : Scheme.{0}} {s : X ⟶ Sp E} {N : ℕ} (o : GObj gb N s) (c : ℕ) (a : 𝓞 D.F) : Type :=
  Cls (D := datAt S.atq S.sp) (gb := gb) S.Y (algebraMap (Ow w) E) o c a

def Site.pi {N : Lv p} {c : ℕ} {a : 𝓞 D.F} (C : S.Cl (T.M N).univ c a) : T.X.Z (T.lev N) ⟶ (GlobalTheory.KS.pow S.Y.univ.A k).left :=
  (T.e N).hom ≫ C.pw k

def Site.Num (N c : ℕ) (a : 𝓞 D.F) : Prop := N = S.N₀ * c ∧ IsGen a N S.𝔞

structure Wit (h : G.GAf) (N' N : Lv p) : Type 1 where
  π : (T.M N').X ⟶ (T.M N).X
  o : GObj gb N.1 (T.M N').s
  ψ : (T.M N').univ.A ⟶ o.A
  φ : GObjMap o (T.M N).univ π
  ov : π ≫ (T.M N).s = (T.M N').s
  trans : IsTrans L h (T.M N').univ o ψ

structure Lift {i cc : ℕ} {Tj : TjD S.M r 𝔴 i cc} (Lj : TjE S.Y S.mπ Tj) {h : G.GAf} {N' N : Lv p} (W : Wit T h N' N)
    {c c' : ℕ} {a a' : 𝓞 D.F} (C' : S.Cl (T.M N').univ c' a') (C : S.Cl (T.M N).univ c a) : Type where
  y : (T.M N').X ⟶ Lj.Z
  ys : y ≫ Lj.s = C'.j
  yt : y ≫ Lj.t = W.π ≫ C.j
  m : QMap (D := datAt S.atq S.sp) (gb := gb) (T.M N').univ Lj.o y c'
  ms : m.φ ≫ Lj.ms.φ = C'.m.φ
  mt : m.φ ≫ Lj.ψ.left ≫ Lj.mt.φ = W.ψ.left ≫ W.φ.φ ≫ C.m.φ

end Tower

end UpperTheory.Gal.Int.Geo

end
