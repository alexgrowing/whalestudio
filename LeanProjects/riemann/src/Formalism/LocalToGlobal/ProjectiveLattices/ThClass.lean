import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD NumberField
open MvPolynomial Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def thLaValAt (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (La : GenLat E n) (N : ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  ShortValAt Xo c nab w La 1 N P y v

abbrev LevQc (Dw : Datum H) (l : Level H) : Type := Dw.La ⧸ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)

def phiHat {n : ℕ} (φ : (Fin n → LevQc Dw l) → c.F) : (Fin n → LevQ Dw l) → c.F :=
  fun q => ∑ᶠ x : Fin n → LevQc Dw l, φ x * zetaM c ^ pairL (l := l) (fun b => qRep (x b)) (fun b => levRep (q b))

def indPhi {n : ℕ} (x0 : Fin n → LevQc Dw l) : (Fin n → LevQc Dw l) → c.F :=
  open Classical in fun x => if x = x0 then 1 else 0

def BaseFrameShape {n : ℕ} (x0 : Fin n → LevQc Dw l) : Prop :=
  (∀ b : Fin n, Dw.p + Dw.q ≤ b.val → x0 b = 0) ∧
  Submodule.span (𝓞 E) (Set.range fun b : {b : Fin n // b.val < Dw.p + Dw.q} => x0 b.1) = ⊤

section Cls

variable {n : ℕ} {Cl : Type} [Fintype Cl] {Vs : Type} [AddCommGroup Vs] [Module c.F Vs]

def ThClsValAt (nab : NabV Xo c) (w : Cl → (Fin n → LevQ Dw l) → c.F) (La : Cl → GenLat E n) (Nc : Cl → ℕ)
    (gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xi : Rul Xo c) (x : Cl → Vs)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  ∃ vc : Cl → S, (∀ k, thLaValAt Xo c nab (w k) (La k) (Nc k) (io (x k)) y (vc k)) ∧
    v = evR Xo c xi y * ∑ k, algebraMap c.F S (vol * ((gam k : c.F))⁻¹ * ep k) * vc k

def IsThCls (nab : NabV Xo c) (w : Cl → (Fin n → LevQ Dw l) → c.F) (La : Cl → GenLat E n) (Nc : Cl → ℕ)
    (gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xi : Rul Xo c) (x : Cl → Vs)
    (f : Rul Xo c) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R), ThClsValAt Xo c nab w La Nc gam vol ep io xi x y (f p y)

def GenLat.SplitSupp (H : Host E) (Λ : GenLat E n) : Prop :=
  ∃ m : 𝓞 E, m ≠ 0 ∧ Ideal.span {m} • Λ.La ≤ stdLat E n ∧ Ideal.span {m} • stdLat E n ≤ Λ.La ∧
    ∀ P : Ideal (𝓞 E), P.IsPrime → m ∈ P → P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P

def RepsOK (bad : ℕ) (La : Cl → GenLat E n) (Nc : Cl → ℕ) (gam : Cl → ℕ) : Prop :=
  ∀ k, (La k).Unimod ∧ (La k).TrivAt bad ∧ (La k).TrivAt l.M ∧ (La k).LevOK (Nc k) l.M ∧ 0 < gam k ∧
    GenLat.SplitSupp H (La k)

def ThLaTot (nab : NabV Xo c) (w : Cl → (Fin n → LevQ Dw l) → c.F) (La : Cl → GenLat E n) (Nc : Cl → ℕ)
    (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) : Prop :=
  ∀ (k : Cl) (v : Vs) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S),
    ∃! t : S, thLaValAt Xo c nab (w k) (La k) (Nc k) (io v) y t

theorem existsUnique_thCls (nab : NabV Xo c) (w : Cl → (Fin n → LevQ Dw l) → c.F) (La : Cl → GenLat E n)
    (Nc : Cl → ℕ) (gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xi : Rul Xo c)
    (h : ThLaTot Xo c nab w La Nc io) (x : Cl → Vs) :
    ∃! f : Rul Xo c, IsThCls Xo c nab w La Nc gam vol ep io xi x f := by
  classical
  refine ⟨fun p y => evR Xo c xi y * ∑ k, algebraMap c.F p.R (vol * ((gam k : c.F))⁻¹ * ep k) *
      (h k (x k) p.R y).choose, ?_, ?_⟩
  · intro p y
    exact ⟨fun k => (h k (x k) p.R y).choose, fun k => (h k (x k) p.R y).choose_spec.1, rfl⟩
  · intro f' hf'
    funext p y
    obtain ⟨vc, hvc, hv⟩ := hf' p y
    rw [hv]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(h k (x k) p.R y).choose_spec.2 (vc k) (hvc k)]

def ThClsInCusp (nab : NabV Xo c) (w : Cl → (Fin n → LevQ Dw l) → c.F) (La : Cl → GenLat E n) (Nc : Cl → ℕ)
    (gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xi : Rul Xo c)
    (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) (a : (E →+* ℂ) × ℕ → ℕ) : Prop :=
  ∀ (x : Cl → Vs) (f : Rul Xo c), IsThCls Xo c nab w La Nc gam vol ep io xi x f → f ∈ cusp a n

end Cls

def gaStar {n : ℕ} (ga : Matrix (Fin n) (Fin n) E) : MvPolynomial (LtN Dw n) c.F →ₐ[c.F] MvPolynomial (LtN Dw n) c.F :=
  aeval fun ℓ => letB (Dw := Dw) c ℓ.1 ℓ.2.1 (fun j => ga j ℓ.2.2)

def minorPolynomial {n : ℕ} (σ : E →+* ℂ) (i : ℕ) (hi : i < Dw.mult σ) (col : Fin (i + 1) → Fin n) :
    MvPolynomial (LtN Dw n) c.F :=
  Matrix.det (Matrix.of fun s b : Fin (i + 1) => X (⟨σ, ⟨s.val, by omega⟩, col b⟩ : LtN Dw n))

def aStep (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (σ : E →+* ℂ) (i : ℕ) : ℕ :=
  a (σ, i) - (if i + 1 < Dw.mult σ then a (σ, i + 1) else 0)

open Classical in

def pG (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : MvPolynomial (LtN Dw n) c.F :=
  ∏ σ : E →+* ℂ, ∏ i : Fin (Dw.mult σ),
    (if h : i.val + 1 ≤ n then
      (if InPsi H σ then minorPolynomial c σ i.val i.isLt (Fin.castLE h)
        else minorPolynomial c σ i.val i.isLt (fun b => Fin.cast (by omega) (Fin.natAdd (n - (i.val + 1)) b)))
      else 0) ^ aStep Dw a σ i.val

def idlE (I : Ideal (𝓞 E)) : Submodule (𝓞 E) E := Submodule.map (Algebra.linearMap (𝓞 E) E) I

def EpIs {n : ℕ} (bad : ℕ) (B : Ideal (𝓞 E) → c.F) (epF : Submodule (𝓞 E) (Fin n → E) → c.F) : Prop :=
  ∀ (L : Submodule (𝓞 E) (Fin n → E)) (cc : Ideal (𝓞 E)),
    (⟨L⟩ : GenLat E n).Unimod → (⟨L⟩ : GenLat E n).TrivAt bad → GenLat.SplitSupp H (⟨L⟩ : GenLat E n) →
    cc ⊔ cc.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ →
    Submodule.span (𝓞 E) (detSet L) * idlE (cc.map (H.bar : 𝓞 E →+* 𝓞 E)) = idlE cc →
    ∃ q : ℚ, 0 < q ∧
      q ^ 2 * (((L ⊓ stdLat E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℚ) ^ (Dw.p + Dw.q) =
        (Ideal.absNorm cc : ℚ) ∧
      epF L = (B cc)⁻¹ * (q : c.F)

def BAbs (B : Ideal (𝓞 E) → c.F) : Prop :=
  ∀ cc : Ideal (𝓞 E), cc ⊔ cc.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → ∀ σ : c.F →+* ℂ, ‖σ (B cc)‖ ^ 2 = (Ideal.absNorm cc : ℝ)

section Io

variable {n : ℕ} {Vs : Type} [AddCommGroup Vs] [Module c.F Vs] [Module (𝓞 c.F) Vs] [IsScalarTower (𝓞 c.F) c.F Vs]

def IoLF (a : (E →+* ℂ) × ℕ → ℕ) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
    (rho : Matrix (Fin n) (Fin n) E → Vs →ₗ[c.F] Vs) (cga : Matrix (Fin n) (Fin n) E → c.F)
    (nab0 : Submodule (𝓞 c.F) Vs) (hw : Vs) (pG : MvPolynomial (LtN Dw n) c.F) : Prop :=
  Dw.p + Dw.q ≤ n ∧ Function.Injective io ∧
  LinearMap.range io = Submodule.span c.F (HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H)
    (fun τ i => a (τ, i))) ∧
  (∀ ga : Matrix (Fin n) (Fin n) E, ga.conjTranspose * ga = 1 → ∀ v, io (rho ga v) = cga ga • gaStar c (ga.map (IsCMField.complexConj E)) (io v)) ∧
  hw ∈ nab0 ∧ (∀ s : c.F, s • hw ∈ nab0 → ∃ o : 𝓞 c.F, s = (o : c.F)) ∧ io hw = pG ∧
  harmA (Dw := Dw) c a n ⊆ io '' (nab0 : Set Vs)

def LatPin {Cl : Type} (Lh : Cl → Submodule (𝓞 E) (Fin n → E)) (La : Cl → GenLat E n) : Prop :=
  ∀ k (v : Fin n → E), v ∈ (La k).La ↔ (fun j => IsCMField.complexConj E (v j)) ∈ Lh k

def HarmInNab {Cl : Type} (a : (E →+* ℂ) × ℕ → ℕ) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (La : Cl → GenLat E n)
    (nabK : Cl → Submodule (𝓞 c.F) Vs) : Prop :=
  ∀ k, harmL (Dw := Dw) c (La k) a ⊆ io '' (nabK k : Set Vs)

end Io

section Ep

variable {n : ℕ} {Cl : Type}

def EpAbs (La : Cl → GenLat E n) (ep : Cl → c.F) : Prop :=
  ∀ (k : Cl) (σ : c.F →+* ℂ), ‖σ (ep k)‖ ^ 2 *
    (((La k).Ln.toAddSubgroup.addSubgroupOf (La k).La.toAddSubgroup).index : ℝ) ^ (Dw.p + Dw.q) = 1

end Ep

section Row

variable {n : ℕ} {Cl : Type} [Fintype Cl] {Vs : Type} [AddCommGroup Vs] [Module c.F Vs]

def OneMod {n : ℕ} (lev : ℕ) (ga : Matrix (Fin n) (Fin n) E) : Prop :=
  ∃ k : ℕ, Nat.Coprime k lev ∧ ∀ i j, ∃ o : 𝓞 E, (k : E) * (ga - 1) i j = (lev : E) * (o : E)

def ThClsRepIndep (nab : NabV Xo c) (bad lev : ℕ) (w : Cl → (Fin n → LevQ Dw l) → c.F) (gam : Cl → ℕ) (vol : c.F)
    (epF : Submodule (𝓞 E) (Fin n → E) → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
    (rho : Matrix (Fin n) (Fin n) E → Vs →ₗ[c.F] Vs) (xi : Rul Xo c) : Prop :=
  ∀ (Lh Lh' : Cl → Submodule (𝓞 E) (Fin n → E)) (La La' : Cl → GenLat E n) (Nc Nc' : Cl → ℕ)
    (ga : Cl → Matrix (Fin n) (Fin n) E) (x : Cl → Vs) (f f' : Rul Xo c),
    RepsOK (l := l) bad La Nc gam → RepsOK (l := l) bad La' Nc' gam → LatPin Lh La → LatPin Lh' La' →
    (∀ k, (ga k).conjTranspose * ga k = 1 ∧ OneMod lev (ga k) ∧
      ∀ v : Fin n → E, v ∈ Lh' k ↔ ∃ u ∈ Lh k, v = (ga k).mulVec u) →
    IsThCls Xo c nab w La Nc gam vol (fun k => epF (Lh k)) io xi x f →
    IsThCls Xo c nab w La' Nc' gam vol (fun k => epF (Lh' k)) io xi (fun k => rho (ga k) (x k)) f' →
    f = f'

def ThClsScalar (nab : NabV Xo c) (bad lev : ℕ) (w : Cl → (Fin n → LevQ Dw l) → c.F) (gam : Cl → ℕ) (vol : c.F)
    (epF : Submodule (𝓞 E) (Fin n → E) → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
    (rho : Matrix (Fin n) (Fin n) E → Vs →ₗ[c.F] Vs) (xi : Rul Xo c) : Prop :=
  ∀ (Lh Lh' : Cl → Submodule (𝓞 E) (Fin n → E)) (La La' : Cl → GenLat E n) (Nc Nc' : Cl → ℕ)
    (z : Cl → E) (x : Cl → Vs) (f f' : Rul Xo c),
    RepsOK (l := l) bad La Nc gam → RepsOK (l := l) bad La' Nc' gam → LatPin Lh La → LatPin Lh' La' →
    (∀ k, z k ≠ 0 ∧ OneMod lev ((z k / IsCMField.complexConj E (z k)) • (1 : Matrix (Fin n) (Fin n) E)) ∧
      ∀ v : Fin n → E, v ∈ Lh' k ↔ ∃ u ∈ Lh k, v = (z k / IsCMField.complexConj E (z k)) • u) →
    IsThCls Xo c nab w La Nc gam vol (fun k => epF (Lh k)) io xi x f →
    IsThCls Xo c nab w La' Nc' gam vol (fun k => epF (Lh' k)) io xi
      (fun k => rho ((z k / IsCMField.complexConj E (z k)) • (1 : Matrix (Fin n) (Fin n) E)) (x k)) f' →
    f = f'

def IsThClsD (dδ : DeltaDat Xo c n) (w : Cl → (Fin n → LevQ Dw dδ.l₂) → c.F) (La : Cl → GenLat E n) (Nc : Cl → ℕ)
    (gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (x : Cl → Vs)
    (f : Rul Xo c) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra dδ.c₂.F k],
    (∀ a : c.F, algebraMap dδ.c₂.F k (dδ.eF a) = algebraMap c.F k a) →
    ∀ (y : FrPt Xo c k) (y₂ : FrPt dδ.Xo₂ dδ.c₂ k), FrOver dδ y₂ y →
      ∃ vc : Cl → k, (∀ cl, thLaValAt dδ.Xo₂ dδ.c₂ dδ.nab₂ (fun q => dδ.eF (w cl q)) (La cl) (Nc cl)
          (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) (io (x cl))) y₂ (vc cl)) ∧
        evR Xo c f y = evR dδ.Xo₂ dδ.c₂ dδ.cδ y₂ *
          ∑ cl, algebraMap c.F k (vol * ((gam cl : c.F))⁻¹ * ep cl) * vc cl

def OneMapRow {D : D7} (V : HSp D) {σ0 : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ0 r)
    (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (mu : GA D V → ℂ) (xr : ℝ) (a : (E →+* ℂ) × ℕ → ℕ)
    {G : Type} [Group G] (act : G → Rul Xo c →ₗ[c.F] Rul Xo c) {Tup : Type*} (dδ : Tup → DeltaDat Xo c n)
    (Cl' : Tup → Type) [∀ t, Fintype (Cl' t)]
    (w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c.F) (La : ∀ t, Cl' t → GenLat E n) (Nc : ∀ t, Cl' t → ℕ)
    (gam : ∀ t, Cl' t → ℕ) (vol : Tup → c.F) (ep : ∀ t, Cl' t → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
    (thAd : ∀ t, (Cl' t → Vs) → (AutQ V → ℂ)) (Pl : ∀ t, (Cl' t → Vs) → Prop) (LL : IntermediateField ℚ ℂ)
    (Cu : Submodule c.F (Rul Xo c)) (cc : U.Comp → ℂ) (ph : ℂ) : Prop :=
  (∀ k, ‖cc k‖ = 1) ∧ ‖ph‖ = 1 ∧ ∃ z : G, z ∈ Subgroup.center G ∧
    ∀ t : Tup, ∃ ze : ℂ, ze ∈ LL ∧ (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x : Cl' t → Vs, Pl t x →
      (∃ f ∈ Cu, IsThClsD Xo c (dδ t) (w t) (La t) (Nc t) (gam t) (vol t) (ep t) io x f) ∧
      (∀ f ∈ sec Xo c a n, IsThClsD Xo c (dδ t) (w t) (La t) (Nc t) (gam t) (vol t) (ep t) io x f →
        ∀ q : AutQ V, ph * thAd t x q =
          ze * cc (dict q.out).1 * (lieFac Dw xr a : ℂ) * jFn V σ0 (rdU U) dict mu (act z f) q)

end Row

end Formalism.L2.Pj
