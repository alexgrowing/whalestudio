import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.Divisibility.Frames
import Formalism.HarderNarasimhan.StatementPl

open Module NumberField IsDedekindDomain MeasureTheory
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.Lat

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section BC

variable {K L Rl : Type} [Field K] [Field L] [AddCommGroup Rl] [Module K Rl]

open Classical in

def basV (C : Submodule K Rl) (i : Fin (finrank K C)) : C :=
  if _h : Module.Finite K C then Module.finBasis K C i else 0

open Classical in

def crdV (C : Submodule K Rl) : C →ₗ[K] (Fin (finrank K C) → K) :=
  if _h : Module.Finite K C then (Module.finBasis K C).equivFun.toLinearMap else 0

open Classical in

def resL (C C' : Submodule K Rl) (f : Rl →ₗ[K] Rl) : C →ₗ[K] C' :=
  if h : ∀ x ∈ C, f x ∈ C' then f.restrict h else 0

def matV (C C' : Submodule K Rl) (f : Rl →ₗ[K] Rl) : Matrix (Fin (finrank K C')) (Fin (finrank K C)) K :=
  Matrix.of fun k i => crdV C' (resL C C' f (basV C i)) k

variable (φ : K →+* L)

def bcVec (C : Submodule K Rl) (x : C) : Fin (finrank K C) → L := fun i => φ (crdV C x i)

def bcMap (C C' : Submodule K Rl) (f : Rl →ₗ[K] Rl) : (Fin (finrank K C) → L) →ₗ[L] (Fin (finrank K C') → L) :=
  ((matV C C' f).map φ).mulVecLin

def bcLat (C : Submodule K Rl) (M : Set Rl) : Submodule (𝓞 L) (Fin (finrank K C) → L) :=
  Submodule.span (𝓞 L) (bcVec φ C '' {x : C | (x : Rl) ∈ M})

theorem bcLat_mono (C : Submodule K Rl) {M M' : Set Rl} (h : M ⊆ M') : bcLat φ C M ≤ bcLat φ C M' :=
  Submodule.span_mono (Set.image_mono fun _ hx => h hx)

theorem bcMap_bcVec (C C' : Submodule K Rl) [Module.Finite K C] (f : Rl →ₗ[K] Rl) (x : C) :
    bcMap φ C C' f (bcVec φ C x) = bcVec φ C' (resL C C' f x) := by
  have hC : Module.Finite K C := inferInstance
  have hx : x = ∑ i, crdV C x i • basV C i := by
    simp only [crdV, basV, dif_pos hC]
    exact ((Module.finBasis K C).sum_equivFun x).symm
  funext k
  conv_rhs => rw [hx]
  simp only [bcMap, bcVec, matV, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply,
    map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

open Classical in

def preF (z : L) : K := if h : ∃ a, φ a = z then h.choose else 0

theorem preF_spec {z : L} (h : ∃ a, φ a = z) : φ (preF φ z) = z := by
  unfold preF; rw [dif_pos h]; exact h.choose_spec

end BC

section OLat

variable {K Rl : Type} [Field K] [NumberField K] [CommRing Rl] [Algebra K Rl] [Algebra (𝓞 K) Rl] [IsScalarTower (𝓞 K) K Rl]

def supLat (C : Submodule K Rl) (Vs : HeightOneSpectrum (𝓞 K) → Set (Rl → EReal)) (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) :
    Submodule (𝓞 K) Rl :=
  (latOf C Vs hV).map (C.subtype.restrictScalars (𝓞 K))

theorem mem_supLat (C : Submodule K Rl) (Vs : HeightOneSpectrum (𝓞 K) → Set (Rl → EReal)) (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v)
    (f : Rl) : f ∈ supLat C Vs hV ↔ f ∈ C ∧ ∀ la, ∀ v ∈ Vs la, 0 ≤ v f := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hf, h⟩
    exact ⟨⟨f, hf⟩, h, rfl⟩

end OLat

section SecZ

variable {K : Type} [Field K] {ι : Type} [Fintype ι]
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)

def secWZ (e : ι → ℤ) : Submodule K (Rules pts) where
  carrier := {f | IsNatural pts mapR f ∧ ∀ (p : TRing K) (t : ι → (p.R)ˣ) (y y' : pts p.R), borR t y y' →
      f p y' = ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) * f p y}
  zero_mem' := ⟨fun p q φ y z _ => by simp, fun p t y y' _ => by simp⟩
  add_mem' := fun {f g} hf hg =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h, hg.1 p q φ y z h],
     fun p t y y' h => by simp [hf.2 p t y y' h, hg.2 p t y y' h, mul_add]⟩
  smul_mem' := fun c f hf =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h],
     fun p t y y' h => by simp [hf.2 p t y y' h]⟩

theorem secWZ_nat (e : ι → ℕ) : secWZ pts mapR borR (fun i => (e i : ℤ)) = secW pts mapR borR e := by
  have hw : ∀ (p : TRing K) (t : ι → (p.R)ˣ), ((∏ i, t i ^ (e i : ℤ) : (p.R)ˣ) : p.R) = wchar e t := fun p t => by
    simp [wchar]
  ext f
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun p t y y' h => by rw [h2 p t y y' h, hw]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun p t y y' h => by rw [h2 p t y y' h, hw]⟩

end SecZ

section Forms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

abbrev ExZ (E : Type) [Field E] : Type := (E →+* ℂ) × ℕ → ℤ

def exZ (Dw : Datum H) (a : ExZ E) (n : ℕ) : Ix Dw → ℤ
  | none => n
  | some x => a (x.1, x.2)

variable (Xo : Moduli Dw l) (c : Coeff l)

def secZ (a : ExZ E) (n : ℕ) : Submodule c.F (Rul Xo c) :=
  secWZ (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y') (exZ Dw a n)

theorem secZ_nat (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : secZ Xo c (fun x => (a x : ℤ)) n = sec Xo c a n := by
  have he : exZ Dw (fun x => (a x : ℤ)) n = fun i => (ex Dw a n i : ℤ) := funext fun i => by cases i <;> rfl
  unfold secZ sec
  rw [he, secWZ_nat]

variable {Xo c} {r : ℕ}

open Classical in

def laZ {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (a : ExZ E) (n : ℕ) (k : U.Comp) : Wt (U.X k).Ψ r :=
  fun τ j => if (U.X k).p0 ≤ (j : ℕ) then
      a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) + ((n / 2 : ℕ) : ℤ)
    else -a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) - ((n / 2 : ℕ) : ℤ)

theorem laZ_nat {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    laZ U (fun x => (a x : ℤ)) n = laU U a n := rfl

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def cuspZ (a : ExZ E) (n : ℕ) : Submodule c.F (Rul Xo c) :=
  secZ Xo c a n ⊓ ⨅ (σ : c.F →+* ℂ) (_ : GoodEmb c σ), (holSub (U σ).X (laZ (U σ) a n)).comap (rdU (U σ))

theorem cuspZ_nat (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : cuspZ U (fun x => (a x : ℤ)) n = cusp Xo c U a n := by
  unfold cuspZ cusp
  rw [secZ_nat]
  rfl

def latZ (a : ExZ E) (n : ℕ) : Submodule (𝓞 c.F) (Rul Xo c) :=
  supLat (cuspZ U a n) (valSet Xo c (algCls Xo c)) fun la => isVal_valSet la

theorem mem_latZ (a : ExZ E) (n : ℕ) (f : Rul Xo c) :
    f ∈ latZ U a n ↔ f ∈ cuspZ U a n ∧ ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f :=
  mem_supLat _ _ _ f

def lieZ (Dw : Datum H) (x : ℝ) (a : ExZ E) : ℝ :=
  Real.exp (-((∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) / 2) * Real.log (2 * Real.pi * x))

theorem lieZ_nat (Dw : Datum H) (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) : lieZ Dw x (fun y => (a y : ℤ)) = lieFac Dw x a := by
  simp [lieZ, lieFac]

def supZ (x : ℝ) (σ : c.F →+* ℂ) (a : ExZ E) (n : ℕ) (f : Rul Xo c) : ENNReal :=
  ENNReal.ofReal (lieZ Dw x a) * supE (U σ).X (laZ (U σ) a n) (rdU (U σ) f)

end Forms

section Pet

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (W : HSp D) (dict : ∀ σ : c.F →+* ℂ, GA D W → Σ k, Frame ((U σ).X k).Ψ D.R.r)

abbrev rk (a : ExZ D.host.E) (n : ℕ) : ℕ := finrank c.F (cuspZ U a n)

def ML {L : Type} [Field L] (φ : c.F →+* L) (a : ExZ D.host.E) (n : ℕ) : Submodule (𝓞 L) (Fin (rk U a n) → L) :=
  bcLat φ (cuspZ U a n) (latZ U a n : Set (Rul Xo c))

def fn (σ : c.F →+* ℂ) (f : Rul Xo c) (q : AutQ W) : ℂ :=
  rdU (U σ) f (dict σ q.out).1 (dict σ q.out).2

def petZ (σ : c.F →+* ℂ) (a : ExZ D.host.E) (f g : Rul Xo c) : ℂ :=
  ((lieZ Dw (xiR D) a ^ 2 : ℝ) : ℂ) * ∫ q, starRingEnd ℂ (fn U W dict σ f q) * fn U W dict σ g q ∂(muQ1 W)

def gramG (σ : c.F →+* ℂ) (a : ExZ D.host.E) (n : ℕ) : Matrix (Fin (rk U a n)) (Fin (rk U a n)) ℂ :=
  Matrix.of fun k k' => petZ U W dict σ a (basV (cuspZ U a n) k : Rul Xo c) (basV (cuspZ U a n) k' : Rul Xo c)

open Classical in

def gramZ (σ : c.F →+* ℂ) (a : ExZ D.host.E) (n : ℕ) : Matrix (Fin (rk U a n)) (Fin (rk U a n)) ℂ :=
  if GoodEmb c σ then gramG U W dict σ a n else (gramG U W dict ((starRingEnd ℂ).comp σ) a n)ᵀ

def XZ {L : Type} [Field L] (φ : c.F →+* L) (a : ExZ D.host.E) (n : ℕ) (v : InfinitePlace L) :
    Matrix (Fin (rk U a n)) (Fin (rk U a n)) ℂ :=
  frameOf (gramZ U W dict (v.embedding.comp φ) a n)

def MF (a : ExZ D.host.E) (n : ℕ) : Submodule (𝓞 c.F) (Fin (rk U a n) → c.F) :=
  bcLat (RingHom.id c.F) (cuspZ U a n) (latZ U a n : Set (Rul Xo c))

def XF (a : ExZ D.host.E) (n : ℕ) (v : InfinitePlace c.F) : Matrix (Fin (rk U a n)) (Fin (rk U a n)) ℂ :=
  frameOf (gramZ U W dict v.embedding a n)

end Pet

end GlobalTheory.CompanionTheory.Ar.Rec.Lat
