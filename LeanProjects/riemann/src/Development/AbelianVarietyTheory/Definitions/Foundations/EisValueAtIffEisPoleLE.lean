import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRestrictedProdFinAwayIffIsProdMeasureFinAway
import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow

noncomputable section

namespace GlobalTheory.Eis

open scoped NNReal ENNReal ComplexConjugate
open Filter Topology Set MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (V : HSp D)

abbrev SiegelCosets : Type := Cosets (siegel V) (GQ (dblSp V))

def eis (Φ : GA D (dblSp V) → ℂ) : GA D (dblSp V) → ℂ := cosetSum (siegel V) (GQ (dblSp V)) Φ

def EisConv (Φ : GA D (dblSp V) → ℂ) (g : GA D (dblSp V)) : Prop := CosetConv (siegel V) (GQ (dblSp V)) Φ g

def SphConv (a : GL (Fin V.rank) (AE D)) : Prop := ∀ σ : ℝ, (V.rank : ℝ) / 2 < σ →
  Summable fun q : SiegelCosets V => (hgt V a (q.out : GQ (dblSp V)) : ℝ) ^ (σ + (V.rank : ℝ) / 2)

def sph (a : GL (Fin V.rank) (AE D)) (s : ℂ) : GA D (dblSp V) → ℂ := fun g => npow (hgt V a g) (s + (V.rank : ℂ) / 2)

section Family

variable (Φ : ℂ → GA D (dblSp V) → ℂ)

def IsEisFamily : Prop := ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → LeftInv (siegelQ V) (Φ s) ∧ ∀ g, EisConv V (Φ s) g

def eisSer (g : GA D (dblSp V)) : ℂ → ℂ := fun s => eis V (Φ s) g

def IsEisExt (U : Set ℂ) (E : ℂ → GA D (dblSp V) → ℂ) : Prop :=
  IsEisFamily V Φ ∧ IsRightDomain U ∧ (∀ g, MeromorphicOn (E · g) U) ∧ ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → E s = eis V (Φ s)

def IsEisHolExt (U : Set ℂ) (E : ℂ → GA D (dblSp V) → ℂ) : Prop :=
  IsEisFamily V Φ ∧ IsRightDomain U ∧ (∀ g, AnalyticOnNhd ℂ (E · g) U) ∧ ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → E s = eis V (Φ s)

def EisContinues : Prop := IsEisFamily V Φ ∧ ∀ g, Continues (eisSer V Φ g)

def EisValueAt (s₀ : ℂ) (φ : GA D (dblSp V) → ℂ) : Prop := IsEisFamily V Φ ∧ ∀ g, HolValueAt (eisSer V Φ g) s₀ (φ g)

def EisCoeffAt (s₀ : ℂ) (n : ℤ) (φ : GA D (dblSp V) → ℂ) : Prop :=
  IsEisFamily V Φ ∧ ∀ g, CoeffAt (eisSer V Φ g) s₀ n (φ g)

def EisPoleLE (s₀ : ℂ) (k : ℕ) : Prop := IsEisFamily V Φ ∧ ∀ g, PoleLE (eisSer V Φ g) s₀ k

def eisCont (s : ℂ) : GA D (dblSp V) → ℂ := fun g => cont (eisSer V Φ g) s

def eisLaurent (s₀ : ℂ) (n : ℤ) : GA D (dblSp V) → ℂ := fun g => laurent (eisSer V Φ g) s₀ n

end Family

section Integral

variable (μ : (AE D)ˣ →* Circle)

def dblIntegrand (E : GA D (dblSp V) → ℂ) (f₁ f₂ : GA D V → ℂ) : GA D V × GA D V → ℂ :=
  fun g => E (io V g) * conj (f₁ g.1) * f₂ g.2 * (μ (detA V g.2) : ℂ)⁻¹

def dblIntegrandQ (E : GA D (dblSp V) → ℂ) (f₁ f₂ : GA D V → ℂ) : AutQ V × AutQ V → ℂ :=
  fun q => dblIntegrand V μ E f₁ f₂ (q.1.out, q.2.out)

variable (m : Measure (GA D V))

def dblInt (E : GA D (dblSp V) → ℂ) (f₁ f₂ : GA D V → ℂ) : ℂ :=
  ∫ q, dblIntegrandQ V μ E f₁ f₂ q ∂(autMeasure V m).prod (autMeasure V m)

def DblConv (E : GA D (dblSp V) → ℂ) (f₁ f₂ : GA D V → ℂ) : Prop :=
  LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ E f₁ f₂) ∧
    Integrable (dblIntegrandQ V μ E f₁ f₂) ((autMeasure V m).prod (autMeasure V m))

variable (Φ : ℂ → GA D (dblSp V) → ℂ) (f₁ f₂ : GA D V → ℂ)

def zeta : ℂ → ℂ := fun s => dblInt V μ m (eis V (Φ s)) f₁ f₂

def IsZetaFamily : Prop := IsEisFamily V Φ ∧ ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → DblConv V μ m (eis V (Φ s)) f₁ f₂

def ZetaContinues : Prop := IsZetaFamily V μ m Φ f₁ f₂ ∧ Continues (zeta V μ m Φ f₁ f₂)

def ZetaValueAt (s₀ c : ℂ) : Prop := IsZetaFamily V μ m Φ f₁ f₂ ∧ ValueAt (zeta V μ m Φ f₁ f₂) s₀ c

def ZetaHolValueAt (s₀ c : ℂ) : Prop := IsZetaFamily V μ m Φ f₁ f₂ ∧ HolValueAt (zeta V μ m Φ f₁ f₂) s₀ c

def ZetaCoeffAt (s₀ : ℂ) (n : ℤ) (c : ℂ) : Prop := IsZetaFamily V μ m Φ f₁ f₂ ∧ CoeffAt (zeta V μ m Φ f₁ f₂) s₀ n c

end Integral

variable {V} {a : GL (Fin V.rank) (AE D)} {μ : (AE D)ˣ →* Circle}

section One

variable {Φ Ψ : GA D (dblSp V) → ℂ} {g : GA D (dblSp V)} {s : ℂ}

theorem leftInv_of_mem (hμ : IsHeckeChar D μ) (hΦ : Φ ∈ degPS V a μ s) : LeftInv (siegelQ V) Φ :=
  fun _ hγ g => apply_siegelQ_mul V a hμ hΦ hγ g

theorem EisConv.hasSum (h : EisConv V Φ g) :
    HasSum (fun q : SiegelCosets V => Φ ((q.out : GQ (dblSp V)) * g)) (eis V Φ g) := CosetConv.hasSum h

theorem leftInv_eis (h : LeftInv (siegelQ V) Φ) : LeftInv (GQ (dblSp V)) (eis V Φ) := leftInv_cosetSum h

theorem eis_rTr (k : GA D (dblSp V)) (Φ : GA D (dblSp V) → ℂ) : eis V (rTr _ k Φ) = rTr _ k (eis V Φ) :=
  funext (cosetSum_mul_right Φ k)

theorem eis_add (h : EisConv V Φ g) (h' : EisConv V Ψ g) : eis V (Φ + Ψ) g = eis V Φ g + eis V Ψ g := cosetSum_add h h'

theorem eis_smul (c : ℂ) (Φ : GA D (dblSp V) → ℂ) : eis V (c • Φ) = c • eis V Φ := funext (cosetSum_smul c Φ)

theorem injective_mk_io : Function.Injective fun γ : GQ V =>
    (mk _ ⟨io V (γ, 1), io_mem_GQ V γ.2 (one_mem _)⟩ : SiegelCosets V) := fun γ δ e => by
  obtain ⟨p, hp⟩ := mk_eq_iff.1 e
  have h1 : ((p : GQ (dblSp V)) : GA D (dblSp V)) = io V (δ * (γ : GA D V)⁻¹, 1) := by
    rw [eq_mul_inv_of_mul_eq (congrArg Subtype.val hp), ← map_inv, ← map_mul]; simp
  exact Subtype.ext (mul_inv_eq_one.1 ((io_mem_siegel V).1 (h1 ▸ p.2))).symm

end One

section Families

variable {Φ Ψ E : ℂ → GA D (dblSp V) → ℂ} {φ ψ : GA D (dblSp V) → ℂ} {U : Set ℂ} {s s₀ : ℂ} {n : ℤ} {k : ℕ}

theorem IsEisFamily.eqRight (h : IsEisFamily V Φ) {γ : GA D (dblSp V)} (hγ : γ ∈ GQ (dblSp V)) (g : GA D (dblSp V)) :
    EqRight (eisSer V Φ (γ * g)) (eisSer V Φ g) := ⟨_, fun s hs => leftInv_eis (h s hs).1 γ hγ g⟩

theorem IsEisFamily.add (h : IsEisFamily V Φ) (h' : IsEisFamily V Ψ) : IsEisFamily V (Φ + Ψ) := fun s hs =>
  ⟨fun γ hγ g => congrArg₂ (· + ·) ((h s hs).1 γ hγ g) ((h' s hs).1 γ hγ g), fun g => ((h s hs).2 g).add ((h' s hs).2 g)⟩

theorem IsEisFamily.smul (h : IsEisFamily V Φ) (c : ℂ → ℂ) : IsEisFamily V (c • Φ) := fun s hs =>
  ⟨fun γ hγ g => congrArg (c s • ·) ((h s hs).1 γ hγ g), fun g => ((h s hs).2 g).smul (c s)⟩

theorem IsEisFamily.rTr (h : IsEisFamily V Φ) (x : GA D (dblSp V)) : IsEisFamily V fun s => rTr _ x (Φ s) := fun s hs =>
  ⟨(h s hs).1.mul_right x, fun g => (cosetConv_mul_right (Φ s) x g).2 ((h s hs).2 _)⟩

theorem IsEisHolExt.isEisExt (h : IsEisHolExt V Φ U E) : IsEisExt V Φ U E :=
  ⟨h.1, h.2.1, fun g => (h.2.2.1 g).meromorphicOn, h.2.2.2⟩

theorem IsEisExt.isMerExt (h : IsEisExt V Φ U E) (g : GA D (dblSp V)) : IsMerExt (eisSer V Φ g) U (E · g) :=
  ⟨h.2.1, h.2.2.1 g, _, fun s hs => congrFun (h.2.2.2 s hs) g⟩

theorem IsEisExt.eisValueAt (h : IsEisExt V Φ U E) (hs : s₀ ∈ U) (ha : ∀ g, AnalyticAt ℂ (E · g) s₀) :
    EisValueAt V Φ s₀ (E s₀) := ⟨h.1, fun g => ⟨_, (h.isMerExt g).isExtAt hs, ha g, rfl⟩⟩

theorem IsEisHolExt.eisValueAt (h : IsEisHolExt V Φ U E) (hs : s₀ ∈ U) : EisValueAt V Φ s₀ (E s₀) :=
  h.isEisExt.eisValueAt hs fun g => h.2.2.1 g _ hs

theorem EisValueAt.eisCoeffAt (h : EisValueAt V Φ s₀ φ) : EisCoeffAt V Φ s₀ 0 φ :=
  ⟨h.1, fun g => coeffAt_zero.2 (h.2 g).valueAt⟩

theorem eisValueAt_iff_eisPoleLE : EisValueAt V Φ s₀ φ ↔ EisPoleLE V Φ s₀ 0 ∧ EisCoeffAt V Φ s₀ 0 φ := by
  simp only [EisValueAt, EisPoleLE, EisCoeffAt, holValueAt_iff_poleLE, coeffAt_zero, forall_and]
  tauto

theorem EisCoeffAt.eisLaurent_eq (h : EisCoeffAt V Φ s₀ n φ) : eisLaurent V Φ s₀ n = φ := funext fun g => (h.2 g).laurent_eq

theorem EisValueAt.eisCont_eq (h : EisValueAt V Φ s₀ φ) : eisCont V Φ s₀ = φ := h.eisCoeffAt.eisLaurent_eq

theorem EisCoeffAt.unique (h : EisCoeffAt V Φ s₀ n φ) (h' : EisCoeffAt V Φ s₀ n ψ) : φ = ψ :=
  h.eisLaurent_eq.symm.trans h'.eisLaurent_eq

theorem EisValueAt.unique (h : EisValueAt V Φ s₀ φ) (h' : EisValueAt V Φ s₀ ψ) : φ = ψ := h.eisCoeffAt.unique h'.eisCoeffAt

theorem EisCoeffAt.leftInv (h : EisCoeffAt V Φ s₀ n φ) : LeftInv (GQ (dblSp V)) φ :=
  fun _ hγ g => ((h.2 _).congr (h.1.eqRight hγ g)).unique (h.2 g)

theorem EisValueAt.leftInv (h : EisValueAt V Φ s₀ φ) : LeftInv (GQ (dblSp V)) φ := h.eisCoeffAt.leftInv

theorem IsEisFamily.leftInv_eisLaurent (h : IsEisFamily V Φ) (s₀ : ℂ) (n : ℤ) :
    LeftInv (GQ (dblSp V)) (eisLaurent V Φ s₀ n) := fun γ hγ g => by
  have e : CoeffAt (eisSer V Φ (γ * g)) s₀ n = CoeffAt (eisSer V Φ g) s₀ n :=
    funext fun c => propext ⟨fun b => b.congr (h.eqRight hγ g), fun b => b.congr (h.eqRight hγ g).symm⟩
  unfold eisLaurent laurent
  rw [e]

theorem EisContinues.eisCoeffAt (h : EisContinues V Φ) (s₀ : ℂ) (n : ℤ) : EisCoeffAt V Φ s₀ n (eisLaurent V Φ s₀ n) :=
  ⟨h.1, fun g => let ⟨_, b⟩ := h.2 g; coeffAt_laurent (b.subset_contDom trivial) n⟩

theorem EisCoeffAt.add (h : EisCoeffAt V Φ s₀ n φ) (h' : EisCoeffAt V Ψ s₀ n ψ) : EisCoeffAt V (Φ + Ψ) s₀ n (φ + ψ) :=
  ⟨h.1.add h'.1, fun g => ((h.2 g).add (h'.2 g)).congr ⟨_, fun s hs => (eis_add ((h.1 s hs).2 g) ((h'.1 s hs).2 g)).symm⟩⟩

theorem EisValueAt.add (h : EisValueAt V Φ s₀ φ) (h' : EisValueAt V Ψ s₀ ψ) : EisValueAt V (Φ + Ψ) s₀ (φ + ψ) :=
  ⟨h.1.add h'.1, fun g => ((h.2 g).add (h'.2 g)).congr ⟨_, fun s hs => (eis_add ((h.1 s hs).2 g) ((h'.1 s hs).2 g)).symm⟩⟩

theorem EisCoeffAt.smul (h : EisCoeffAt V Φ s₀ n φ) (c : ℂ) : EisCoeffAt V (c • Φ) s₀ n (c • φ) :=
  ⟨h.1.smul fun _ => c, fun g => ((h.2 g).const_mul c).congr ⟨0, fun s _ => (congrFun (eis_smul c (Φ s)) g).symm⟩⟩

theorem EisValueAt.smul (h : EisValueAt V Φ s₀ φ) (c : ℂ) : EisValueAt V (c • Φ) s₀ (c • φ) :=
  ⟨h.1.smul fun _ => c, fun g => ((holValueAt_const c s₀).mul (h.2 g)).congr
    ⟨0, fun s _ => (congrFun (eis_smul c (Φ s)) g).symm⟩⟩

theorem EisCoeffAt.rTr (h : EisCoeffAt V Φ s₀ n φ) (x : GA D (dblSp V)) :
    EisCoeffAt V (fun s => rTr _ x (Φ s)) s₀ n (rTr _ x φ) :=
  ⟨h.1.rTr x, fun g => (h.2 (g * x)).congr ⟨0, fun s _ => (congrFun (eis_rTr x (Φ s)) g).symm⟩⟩

theorem EisValueAt.rTr (h : EisValueAt V Φ s₀ φ) (x : GA D (dblSp V)) :
    EisValueAt V (fun s => rTr _ x (Φ s)) s₀ (rTr _ x φ) :=
  ⟨h.1.rTr x, fun g => (h.2 (g * x)).congr ⟨0, fun s _ => (congrFun (eis_rTr x (Φ s)) g).symm⟩⟩

section Holomorphic

variable (h : IsEisFamily V Φ) (ha : ∀ g, AnalyticOnNhd ℂ (eisSer V Φ g) (rightOf (V.rank / 2)))
include h ha

theorem IsEisFamily.isEisHolExt : IsEisHolExt V Φ (rightOf (V.rank / 2)) fun s => eis V (Φ s) :=
  ⟨h, isRightDomain_rightOf _, ha, fun _ _ => rfl⟩

theorem IsEisFamily.eisValueAt (hs : (V.rank : ℝ) / 2 < s₀.re) : EisValueAt V Φ s₀ (eis V (Φ s₀)) :=
  (h.isEisHolExt ha).eisValueAt hs

end Holomorphic

theorem IsEisFamily.analyticOnNhd_flat {s₁ : ℂ} (h : IsEisFamily V (flat V a φ s₁)) (g : GA D (dblSp V)) :
    AnalyticOnNhd ℂ (eisSer V (flat V a φ s₁) g) (rightOf (V.rank / 2)) :=
  analyticOnNhd_tsum_npow (f := term _ _ φ g) (a := term _ _ (hgt V a) g) (fun _ => hgtH_pos _) fun s hs => (h s hs).2 g

section Spherical

variable (hμ : IsHeckeChar D μ) (hI : HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a)) (hs : SphConv V a)

omit hμ hs in
include hI in

theorem isIwasawa_Khat : IsIwasawa ((absA D).comp (aP V)) (Khat V a) :=
  haveI := t2Space_adeleRing' (F := D.host.F)
  hI.iwasawaOf continuous_absE (isCompact_Khat V a)

variable (hc : ContinuousOn (fun x : ℂ × GA D (dblSp V) => Φ x.1 x.2) (rightOf (V.rank / 2) ×ˢ univ))
  (hl : ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → Φ s ∈ degPS V a μ s)

omit hμ hI hs hc in
include hl in

theorem indLaw_of_mem : ∀ s ∈ rightOf (V.rank / 2),
    IndLaw ((absA D).comp (aP V)) (μ.comp (aP V)) (s + ((V.rank : ℝ) / 2 : ℝ)) (Φ s) := fun s hs p g => by
  rw [((mem_degPS V a).1 (hl s hs)).1 p g]; push_cast; rfl

omit hμ hI in
include hs in

theorem SphConv.summable : ∀ τ, (V.rank : ℝ) / 2 < τ → Summable fun q =>
    ((term (siegel V) (GQ (dblSp V)) (iwAbs ((absA D).comp (aP V)) (Khat V a)) 1 q : ℝ≥0) : ℝ) ^ (τ + (V.rank : ℝ) / 2) :=
  fun τ hτ => by simp only [term, mul_one]; exact hs τ hτ

include hμ hI hs hc hl

theorem SphConv.isEisFamily : IsEisFamily V Φ := fun s h => ⟨leftInv_of_mem hμ (hl s h),
  cosetConv_of_spherical (isIwasawa_Khat hI) (isCompact_Khat V a) hc (indLaw_of_mem hl) hs.summable h⟩

omit hμ in

theorem SphConv.continuousOn_eis :
    ContinuousOn (fun x : ℂ × GA D (dblSp V) => eis V (Φ x.1) x.2) (rightOf (V.rank / 2) ×ˢ univ) :=
  continuousOn_cosetSum (isIwasawa_Khat hI) (isCompact_Khat V a) hc (indLaw_of_mem hl) hs.summable

end Spherical

section Flat

variable (hI : HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a)) {s₁ : ℂ} (hφ : φ ∈ degPS V a μ s₁)
include hI hφ

theorem flat_mem (s : ℂ) : flat V a φ s₁ s ∈ degPS V a μ s :=
  haveI := t2Space_adeleRing' (F := D.host.F)
  hI.flatH_mem continuous_absE (isCompact_Khat V a) hφ s

theorem continuous_flat : Continuous fun x : ℂ × GA D (dblSp V) => flat V a φ s₁ x.1 x.2 := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  have h1 : Continuous (hgt V a) := hI.continuous_hgtH continuous_absE (isCompact_Khat V a)
  have h2 : Continuous fun g => Real.log (hgt V a g) :=
    (NNReal.continuous_coe.comp h1).log fun g => (NNReal.coe_pos.2 (hgtH_pos g)).ne'
  have h3 : Continuous φ := hφ.2.1
  simp only [flatH_apply, npow_eq_exp (hgtH_pos _)]
  exact (h3.comp continuous_snd).mul (((Complex.continuous_ofReal.comp (h2.comp continuous_snd)).mul
    (continuous_fst.sub continuous_const)).cexp)

theorem SphConv.isEisFamily_flat (hs : SphConv V a) (hμ : IsHeckeChar D μ) : IsEisFamily V (flat V a φ s₁) :=
  hs.isEisFamily hμ hI (continuous_flat hI hφ).continuousOn fun s _ => flat_mem hI hφ s

theorem SphConv.continuous_eis (hs : SphConv V a) (h : (V.rank : ℝ) / 2 < s₁.re) : Continuous (eis V φ) := by
  have := (hs.continuousOn_eis hI (continuous_flat hI hφ).continuousOn fun s _ => flat_mem hI hφ s).comp_continuous
    (f := fun g => (s₁, g)) (by fun_prop) fun g => ⟨h, trivial⟩
  simpa only [Function.comp_def, flatH_self] using this

theorem SphConv.eisValueAt_flat (hs : SphConv V a) (hμ : IsHeckeChar D μ) (h : (V.rank : ℝ) / 2 < s₁.re) :
    EisValueAt V (flat V a φ s₁) s₁ (eis V φ) := by
  have h1 := hs.isEisFamily_flat hI hφ hμ
  simpa only [flatH_self] using h1.eisValueAt h1.analyticOnNhd_flat h

omit hφ in

theorem sph_mem (s : ℂ) : sph V a s ∈ degPS V a 1 s :=
  haveI := t2Space_adeleRing' (F := D.host.F)
  hI.spherical_mem continuous_absE (isCompact_Khat V a) s

open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
omit hφ in

theorem sphConv_iff : SphConv V a ↔ IsEisFamily V (sph V a) ∧
    ∀ σ : ℝ, (V.rank : ℝ) / 2 < σ → 1 ≤ (eis V (sph V a σ) 1).re := by
  have h1 : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  have h2 : ∀ (σ : ℝ) g, sph V a σ g = ((hgt V a g : ℝ) ^ (σ + (V.rank : ℝ) / 2) : ℝ) := fun σ g => by
    rw [Complex.ofReal_cpow (NNReal.coe_nonneg _)]; push_cast; rfl
  refine ⟨fun hs => ⟨?_, fun σ hσ => ?_⟩, fun h σ hσ => ((h.1 σ hσ).2 1).congr fun q => ?_⟩
  · rw [show sph V a = flat V a (sph V a 0) 0 from funext fun s => funext fun g => by
      exact (congrArg (npow _) (by ring)).trans (npow_add (hgtH_pos g) _ _)]
    exact hs.isEisFamily_flat hI (sph_mem hI 0) h1
  · have h3 : eis V (sph V a σ) 1 = (∑' q : SiegelCosets V,
        (hgt V a (q.out : GQ (dblSp V)) : ℝ) ^ (σ + (V.rank : ℝ) / 2) : ℝ) := by
      rw [Complex.ofReal_tsum]; exact tsum_congr fun q => by rw [term, mul_one, h2]
    have h4 := term_mk (leftInv_of_mem h1 (sph_mem hI σ)) 1 1
    rw [term, mul_one, h2, h2, Complex.ofReal_inj, OneMemClass.coe_one, mul_one,
      show hgt V a 1 = 1 from (isIwasawa_Khat hI).iwAbs_of_mem (one_mem _), NNReal.coe_one, Real.one_rpow] at h4
    rw [h3, Complex.ofReal_re, ← h4]
    exact (hs σ hσ).le_tsum _ fun _ _ => by positivity
  · rw [term, mul_one, h2, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

end Flat

end Families

section Dbl

variable {m : Measure (GA D V)} {E E' : GA D (dblSp V) → ℂ} {f₁ f₂ f : GA D V → ℂ} {𝓕 : Set (GA D V)}

theorem apply_detA (hμ : IsHeckeChar D μ) {γ : GA D V} (hγ : γ ∈ GQ V) : μ (detA V γ) = 1 := by
  obtain ⟨x, hx⟩ := exists_aH_eq_of_mem_ratPts (ioDiag (gram_hdbl V) γ) (io_mem_GQ V hγ hγ)
  rw [← aH_ioDiag (gram_hdbl V), hx]
  exact hμ.2 x

theorem leftInv_dblIntegrand (hμ : IsHeckeChar D μ) (hE : LeftInv (GQ (dblSp V)) E) (h₁ : LeftInv (GQ V) f₁)
    (h₂ : LeftInv (GQ V) f₂) : LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ E f₁ f₂) := fun γ hγ g => by
  simp only [dblIntegrand, map_mul (io V), hE _ (io_mem_GQ V hγ.1 hγ.2), Prod.fst_mul, Prod.snd_mul, h₁ _ hγ.1, h₂ _ hγ.2,
    map_mul (detA V), map_mul μ, apply_detA hμ hγ.2, one_mul]

open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in

theorem continuous_detA : Continuous (detA V) := by
  have h1 : Continuous (aP V) := continuous_aH
  have h2 : Continuous fun g : GA D V => (⟨io V (g, g), (io_mem_siegel V).2 rfl⟩ : siegel V) :=
    ((continuous_io V).comp (continuous_id.prodMk continuous_id)).subtype_mk _
  exact (h1.comp h2).congr fun g => aH_ioDiag (gram_hdbl V) g

open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in

theorem continuous_dblIntegrand (hμ : IsHeckeChar D μ) (hE : Continuous E) (h₁ : Continuous f₁) (h₂ : Continuous f₂) :
    Continuous (dblIntegrand V μ E f₁ f₂) :=
  have h : Continuous fun g : GA D V => (μ (detA V g) : ℂ) := continuous_subtype_val.comp (hμ.1.comp continuous_detA)
  (((hE.comp (continuous_io V)).mul (Complex.continuous_conj.comp (h₁.comp continuous_fst))).mul
    (h₂.comp continuous_snd)).mul ((h.comp continuous_snd).inv₀ fun _ => Circle.coe_ne_zero _)

theorem dblIntegrandQ_mk (h : LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ E f₁ f₂)) (g₁ g₂ : GA D V) :
    dblIntegrandQ V μ E f₁ f₂ (mk (GQ V) g₁, mk (GQ V) g₂) = dblIntegrand V μ E f₁ f₂ (g₁, g₂) := by
  obtain ⟨γ, e⟩ := mk_eq_iff.1 (Quotient.out_eq (mk (GQ V) g₁)).symm
  obtain ⟨δ, e'⟩ := mk_eq_iff.1 (Quotient.out_eq (mk (GQ V) g₂)).symm
  rw [← h (γ, δ) ⟨γ.2, δ.2⟩ (g₁, g₂), Prod.mk_mul_mk, e, e']
  rfl

theorem dblIntegrand_mul {s : ℂ} (hE : E ∈ degPS V a μ s) (g x : GA D V) :
    dblIntegrand V μ E f₁ f₂ (x * g, x) = E (io V (g, 1)) * conj (f₁ (x * g)) * f₂ x := by
  have := apply_io_mul V a hE x g 1
  rw [mul_one] at this
  simp only [dblIntegrand, this]
  field_simp [Circle.coe_ne_zero]

theorem dblInt_smul (c c₁ c₂ : ℂ) : dblInt V μ m (c • E) (c₁ • f₁) (c₂ • f₂) = c * conj c₁ * c₂ * dblInt V μ m E f₁ f₂ :=
  (integral_congr_ae (.of_forall fun q => by
    simp only [dblIntegrandQ, dblIntegrand, Pi.smul_apply, smul_eq_mul, map_mul]; ring)).trans (integral_const_mul _ _)

theorem dblInt_add (h : DblConv V μ m E f₁ f₂) (h' : DblConv V μ m E' f₁ f₂) :
    dblInt V μ m (E + E') f₁ f₂ = dblInt V μ m E f₁ f₂ + dblInt V μ m E' f₁ f₂ :=
  (integral_congr_ae (.of_forall fun q => by
    simp only [dblIntegrandQ, dblIntegrand, Pi.add_apply]; ring)).trans (integral_add h.2 h'.2)

variable [SigmaFinite m]

theorem dblInt_smul_measure (c : ℝ≥0) : dblInt V μ (c • m) E f₁ f₂ = (c : ℂ) ^ 2 * dblInt V μ m E f₁ f₂ := by
  have e : autMeasure V (c • m) = c • autMeasure V m := quotMeasure_smul (c : ℝ≥0∞)
  rw [dblInt, e, Measure.prod_smul_left, Measure.prod_smul_right, integral_smul_nnreal_measure,
    integral_smul_nnreal_measure, smul_smul, ← sq, NNReal.smul_def, Complex.real_smul]
  push_cast; rfl

theorem dblInt_of_factor {A B : GA D V → ℂ} (h : ∀ g₁ g₂, E (io V (g₁, g₂)) = A g₁ * conj (B g₂) * μ (detA V g₂)) :
    dblInt V μ m E f₁ f₂ = Cusp.petersson V m A f₁ * Cusp.petersson V m f₂ B := by
  refine (integral_congr_ae (.of_forall fun q => ?_)).trans (integral_prod_mul _ _)
  simp only [dblIntegrandQ, dblIntegrand, h, AutomorphicL2Unitary.descend]
  field_simp [Circle.coe_ne_zero]

variable [m.IsMulLeftInvariant]

theorem DblConv.dblInt_eq (hc : DblConv V μ m E f₁ f₂) (h : IsFundamentalDomain (GQ V) 𝓕 m) :
    IntegrableOn (dblIntegrand V μ E f₁ f₂) (𝓕 ×ˢ 𝓕) (m.prod m) ∧
      dblInt V μ m E f₁ f₂ = ∫ g in 𝓕 ×ˢ 𝓕, dblIntegrand V μ E f₁ f₂ g ∂m.prod m := by
  have h1 := (measurePreserving_mk h).prod (measurePreserving_mk h)
  have e : dblIntegrandQ V μ E f₁ f₂ ∘ Prod.map (mk (GQ V)) (mk (GQ V)) = dblIntegrand V μ E f₁ f₂ :=
    funext fun g => dblIntegrandQ_mk hc.1 g.1 g.2
  rw [IntegrableOn, ← Measure.prod_restrict, ← e]
  refine ⟨h1.integrable_comp_of_integrable hc.2, ?_⟩
  have h2 := hc.2.1
  rw [dblInt, autMeasure, ← h1.map_eq] at *
  exact integral_map h1.measurable.aemeasurable h2

theorem dblConv_iff (hi : LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ E f₁ f₂))
    (hm : Measurable (dblIntegrand V μ E f₁ f₂)) (h : IsFundamentalDomain (GQ V) 𝓕 m) :
    DblConv V μ m E f₁ f₂ ↔ IntegrableOn (dblIntegrand V μ E f₁ f₂) (𝓕 ×ˢ 𝓕) (m.prod m) := by
  refine ⟨fun hc => (hc.dblInt_eq h).1, fun hc => ⟨hi, ?_⟩⟩
  have e : dblIntegrandQ V μ E f₁ f₂ ∘ Prod.map (mk (GQ V)) (mk (GQ V)) = dblIntegrand V μ E f₁ f₂ :=
    funext fun g => dblIntegrandQ_mk hi g.1 g.2
  have e' : dblIntegrandQ V μ E f₁ f₂ = dblIntegrand V μ E f₁ f₂ ∘ Prod.map (sec (GQ V)) (sec (GQ V)) :=
    funext fun q => (congrArg _ (Prod.ext (mk_sec q.1) (mk_sec q.2)).symm).trans (dblIntegrandQ_mk hi _ _)
  rw [IntegrableOn, ← Measure.prod_restrict, ← e] at hc
  exact (((measurePreserving_mk h).prod (measurePreserving_mk h)).integrable_comp (e' ▸ (hm.comp
    (measurableEmbedding_sec.measurable.prodMap measurableEmbedding_sec.measurable)).aestronglyMeasurable)).1 hc

end Dbl

section ZetaNonvanishing₂

variable {m : Measure (GA D V)} {Φ : ℂ → GA D (dblSp V) → ℂ} {f₁ f₂ : GA D V → ℂ} {s₀ c c' : ℂ} {n : ℤ}

theorem ZetaValueAt.unique (h : ZetaValueAt V μ m Φ f₁ f₂ s₀ c) (h' : ZetaValueAt V μ m Φ f₁ f₂ s₀ c') : c = c' :=
  h.2.unique h'.2

theorem ZetaCoeffAt.unique (h : ZetaCoeffAt V μ m Φ f₁ f₂ s₀ n c) (h' : ZetaCoeffAt V μ m Φ f₁ f₂ s₀ n c') : c = c' :=
  h.2.unique h'.2

end ZetaNonvanishing₂

section Euler

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] {T : Set (HeightOneSpectrum (𝓞 K))} {c : LFun.Fam K} {σ : ℝ} {Λ : ℂ → ℂ}

end Euler

example (h0 : V.rank = 0) {Φ : GA D (dblSp V) → ℂ} (h : LeftInv (siegelQ V) Φ) (g : GA D (dblSp V)) :
    EisConv V Φ g ∧ eis V Φ g = Φ g :=
  cosetSum_of_le (fun _ _ => mem_siegelOf.2 ((keepsDiag_iff _).2 fun i => absurd i.2 (by omega))) h g

theorem eis_smul_indicator (V : HSp D) (c : ℂ → ℂ) :
    IsEisFamily V (fun s => c s • indicator (siegelQ V : Set (GA D (dblSp V))) 1) ∧
      ∀ s, eis V (c s • indicator (siegelQ V : Set (GA D (dblSp V))) 1) = c s • indicator (GQ (dblSp V) : Set _) 1 :=
  ⟨IsEisFamily.smul (Φ := fun _ => _) (fun _ _ => ⟨(cosetSum_indicator 1).1, fun g => (cosetSum_indicator g).2.1⟩) c,
    fun s => (eis_smul _ _).trans (congrArg _ (funext fun g => (cosetSum_indicator g).2.2))⟩

example (V : HSp D) (s₀ : ℂ) : ∃ Φ, EisContinues V Φ ∧ EisPoleLE V Φ s₀ 1 ∧
    EisCoeffAt V Φ s₀ (-1) (indicator (GQ (dblSp V) : Set _) 1) ∧ ∀ φ, ¬ EisValueAt V Φ s₀ φ := by
  obtain ⟨h1, h2⟩ := eis_smul_indicator V fun s => (s - s₀)⁻¹
  have h3 : ∀ g, IsMerExt (eisSer V (fun s => (s - s₀)⁻¹ • indicator (siegelQ V : Set (GA D (dblSp V))) 1) g) univ
      fun s => (s - s₀)⁻¹ * indicator (GQ (dblSp V) : Set _) 1 g := fun g =>
    ⟨isRightDomain_univ, fun s _ => by fun_prop, 0, fun s _ => (congrFun (h2 s) g).symm⟩
  have h4 : ∀ z : ℂ, Tendsto (fun s => (s - s₀) ^ 1 * ((s - s₀)⁻¹ * z)) (𝓝[≠] s₀) (𝓝 z) := fun z =>
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs => by simp [sub_ne_zero.2 hs])
  refine ⟨_, ⟨h1, fun g => ⟨_, h3 g⟩⟩, ⟨h1, fun g => ((h3 g).isExtAt trivial).poleLE_iff.2 ⟨_, h4 _⟩⟩,
    ⟨h1, fun g => ((h3 g).isExtAt trivial).coeffAt_of_tendsto (h4 _)⟩, fun φ h => ?_⟩
  have h5 := ((tendsto_nhdsWithin_of_tendsto_nhds (s := {s₀}ᶜ) ((continuous_sub_right s₀).pow 1).continuousAt.tendsto).mul
    (((h3 1).isExtAt trivial).holValueAt_iff.1 (h.2 1)))
  simpa [indicator_of_mem (one_mem (GQ (dblSp V)))] using tendsto_nhds_unique h5 (h4 _)

example (m : Measure (GA D V)) [m.IsHaarMeasure] (c c₁ c₂ : ℂ) :
    DblConv V 1 m (fun _ => c) (fun _ => c₁) (fun _ => c₂) ∧
      dblInt V 1 m (fun _ => c) (fun _ => c₁) (fun _ => c₂) = c * conj c₁ * c₂ * (autMeasure V m).real univ ^ 2 := by
  have e : dblIntegrandQ V 1 (fun _ => c) (fun _ => c₁) (fun _ => c₂) = fun _ => c * conj c₁ * c₂ :=
    funext fun _ => by simp [dblIntegrandQ, dblIntegrand]
  refine ⟨⟨fun _ _ _ => rfl, e ▸ integrable_const _⟩, ?_⟩
  rw [dblInt, e, integral_const, ← univ_prod_univ, measureReal_prod_prod, Complex.real_smul]
  push_cast; ring

end GlobalTheory.Eis

end
