import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts

noncomputable section

namespace GlobalTheory.Doubling

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU

section Points

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (ν : (R ⊗[F] E)ˣ →* ℝ≥0)
  (K : Subgroup (HA R σ Q))

def HasIwasawa : Prop := ∀ g : HA R σ Q, ∃ p : siegelH R σ Q, ∃ k ∈ K, g = p * k

abbrev hgtH : HA R σ Q → ℝ≥0 := hgtOf finSumFinEquiv (matHom R σ Q) ν K

abbrev degPSH [TopologicalSpace R] (μ : (R ⊗[F] E)ˣ →* Circle) (s : ℂ) : Submodule ℂ (HA R σ Q → ℂ) :=
  degPSOf finSumFinEquiv (matHom R σ Q) ν K μ s

abbrev flatH (Φ : HA R σ Q → ℂ) (s₀ s : ℂ) : HA R σ Q → ℂ := flatOf finSumFinEquiv (matHom R σ Q) ν K Φ s₀ s

variable {Q}

def zetaH [TopologicalSpace R] (h : Q = dblGram finSumFinEquiv J) (m : Measure (HA R σ J)) (Φ : HA R σ Q → ℂ)
    (c : HA R σ J → ℂ) : ℂ := pairInt m (fun g => Φ (ioH R σ h (g, 1))) c

def ZetaConvH [TopologicalSpace R] (h : Q = dblGram finSumFinEquiv J) (m : Measure (HA R σ J)) (Φ : HA R σ Q → ℂ)
    (c : HA R σ J → ℂ) : Prop := PairConv m (fun g => Φ (ioH R σ h (g, 1))) c

variable {σ ν K}

theorem hgtH_pos (g : HA R σ Q) : 0 < hgtH σ Q ν K g := hgtOf_pos g

theorem flatH_apply (Φ : HA R σ Q → ℂ) (s₀ s : ℂ) (g : HA R σ Q) :
    flatH σ Q ν K Φ s₀ s g = Φ g * npow (hgtH σ Q ν K g) (s - s₀) := rfl

@[simp] theorem flatH_self (Φ : HA R σ Q → ℂ) (s₀ : ℂ) : flatH σ Q ν K Φ s₀ s₀ = Φ := flatSec_self Φ s₀

variable [TopologicalSpace R]

theorem mem_degPSH {μ : (R ⊗[F] E)ˣ →* Circle} {s : ℂ} {Φ : HA R σ Q → ℂ} : Φ ∈ degPSH σ Q ν K μ s ↔
    (∀ (p : siegelH R σ Q) (g : HA R σ Q),
      Φ (p * g) = μ (aH R σ Q p) * npow (ν (aH R σ Q p)) (s + (n : ℂ) / 2) * Φ g) ∧ Continuous Φ ∧ IsKFinite K Φ := by
  rw [mem_degPSOf, Fintype.card_fin]

theorem zetaH_eq (h : Q = dblGram finSumFinEquiv J) (m : Measure (HA R σ J)) (Φ : HA R σ Q → ℂ) (c : HA R σ J → ℂ) :
    zetaH σ h m Φ c = ∫ g, Φ (ioH R σ h (g, 1)) * starRingEnd ℂ (c g) ∂m := rfl

theorem zetaConvH_iff (h : Q = dblGram finSumFinEquiv J) (m : Measure (HA R σ J)) (Φ : HA R σ Q → ℂ)
    (c : HA R σ J → ℂ) :
    ZetaConvH σ h m Φ c ↔ Integrable (fun g => Φ (ioH R σ h (g, 1)) * starRingEnd ℂ (c g)) m := Iff.rfl

omit [TopologicalSpace R] in

theorem abs_detH (hν : ∀ x, ν (conjUnit σ x) = ν x) {m : ℕ} {J : Matrix (Fin m) (Fin m) E} (hJ : J.det ≠ 0)
    (g : HA R σ J) : ν (detH R σ J g) = 1 := by
  have h := hν (detH R σ J g)
  rw [conjUnit_detH hJ, map_inv, inv_eq_iff_eq_inv, ← mul_eq_one_iff_eq_inv₀ (hom_pos ν _).ne', ← sq] at h
  exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h

theorem apply_ioH_mul (h : Q = dblGram finSumFinEquiv J) (hν : ∀ x, ν (conjUnit σ x) = ν x) (hJ : J.det ≠ 0)
    {μ : (R ⊗[F] E)ˣ →* Circle} {s : ℂ} {Φ : HA R σ Q → ℂ} (hΦ : Φ ∈ degPSH σ Q ν K μ s) (x g g' : HA R σ J) :
    Φ (ioH R σ h (x * g, x * g')) = μ (detH R σ J x) * Φ (ioH R σ h (g, g')) := by
  have := (mem_degPSH.1 hΦ).1 (ioDiag h x) (ioH R σ h (g, g'))
  rwa [coe_ioDiag, ← map_mul, aH_ioDiag, abs_detH hν hJ, one_npow, mul_one] at this

variable [IsTopologicalRing R] [FiniteDimensional F E]

theorem continuous_aH : Continuous (aH R σ Q) :=
  haveI := isTopologicalRing_tens (F := F) (E := E) (R := R)
  continuous_aOf (isEmbedding_matHom R σ Q).continuous

variable [T2Space R]

theorem isClosed_siegelH : IsClosed (siegelH R σ Q : Set (HA R σ Q)) :=
  haveI := isTopologicalRing_tens (F := F) (E := E) (R := R)
  haveI := t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := R)
  isClosed_siegelOf (isEmbedding_matHom R σ Q).continuous

variable (hν : Continuous ν) (hK : IsCompact (K : Set (HA R σ Q)))
include hν hK

theorem abs_aH_eq_one (p : siegelH R σ Q) (hp : (p : HA R σ Q) ∈ K) : ν (aH R σ Q p) = 1 :=
  triv_of_isCompact (δ := absAOf finSumFinEquiv (matHom R σ Q) ν) isClosed_siegelH (hν.comp continuous_aH) hK p hp

theorem hgtH_mul (p : siegelH R σ Q) {k : HA R σ Q} (hk : k ∈ K) : hgtH σ Q ν K (p * k) = ν (aH R σ Q p) :=
  iwAbs_mul_of_triv (δ := absAOf finSumFinEquiv (matHom R σ Q) ν) (abs_aH_eq_one hν hK) p hk

theorem hgtH_of_mem {k : HA R σ Q} (hk : k ∈ K) : hgtH σ Q ν K k = 1 := by simpa using hgtH_mul hν hK 1 hk

namespace HasIwasawa

variable (hI : HasIwasawa σ Q K)
include hI

theorem iwasawaOf : IwasawaOf finSumFinEquiv (matHom R σ Q) ν K := ⟨hI, abs_aH_eq_one hν hK⟩

theorem hgtH_left (p : siegelH R σ Q) (g : HA R σ Q) : hgtH σ Q ν K (p * g) = ν (aH R σ Q p) * hgtH σ Q ν K g :=
  IsIwasawa.iwAbs_left (hI.iwasawaOf hν hK) p g

theorem hgtH_right (g : HA R σ Q) {k : HA R σ Q} (hk : k ∈ K) : hgtH σ Q ν K (g * k) = hgtH σ Q ν K g :=
  IsIwasawa.iwAbs_right (hI.iwasawaOf hν hK) g hk

theorem continuous_hgtH : Continuous (hgtH σ Q ν K) :=
  haveI := isTopologicalRing_tens (F := F) (E := E) (R := R)
  haveI := t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := R)
  (hI.iwasawaOf hν hK).continuous_hgtOf (isEmbedding_matHom R σ Q).continuous hν hK

theorem flatH_mem {μ : (R ⊗[F] E)ˣ →* Circle} {s₀ : ℂ} {Φ : HA R σ Q → ℂ} (hΦ : Φ ∈ degPSH σ Q ν K μ s₀) (s : ℂ) :
    flatH σ Q ν K Φ s₀ s ∈ degPSH σ Q ν K μ s :=
  haveI := isTopologicalRing_tens (F := F) (E := E) (R := R)
  haveI := t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := R)
  (hI.iwasawaOf hν hK).flatOf_mem (isEmbedding_matHom R σ Q).continuous hν hK hΦ s

theorem spherical_mem (s : ℂ) : (fun g => npow (hgtH σ Q ν K g) (s + (n : ℂ) / 2)) ∈ degPSH σ Q ν K 1 s := by
  haveI := isTopologicalRing_tens (F := F) (E := E) (R := R)
  haveI := t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := R)
  simpa only [Fintype.card_fin] using
    (hI.iwasawaOf hν hK).spherical_mem (isEmbedding_matHom R σ Q).continuous hν hK s

theorem exists_norm_le {μ : (R ⊗[F] E)ˣ →* Circle} {s : ℂ} {Φ : HA R σ Q → ℂ} (hΦ : Φ ∈ degPSH σ Q ν K μ s) :
    ∃ C : ℝ, ∀ g, ‖Φ g‖ ≤ C * (hgtH σ Q ν K g : ℝ) ^ (s.re + (n : ℝ) / 2) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΦ.2.1.continuousOn
  refine ⟨C, fun g => ?_⟩
  have := IsIwasawa.norm_le (hI.iwasawaOf hν hK) hΦ.1 hC g
  simp only [Fintype.card_fin, Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re] at this
  exact this

end HasIwasawa

end Points

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (L : Submodule (𝓞 E) (Fin n → E))

section Defs

variable (v : HeightOneSpectrum (𝓞 F)) (w : InfinitePlace F) (b : GL (Fin n) (w.Completion ⊗[F] E))
  (a : GL (Fin n) (AF F ⊗[F] E))

abbrev hgtFin : GLoc σ Q v → ℝ≥0 := hgtH σ Q (absEv F E v) (KFin σ Q L v)

abbrev hgtArch : GArch σ Q w → ℝ≥0 := hgtH σ Q (absEw F E w) (KArch σ Q w b)

abbrev hgtAd : GAd σ Q → ℝ≥0 := hgtH σ Q (absE F E) (KAd σ Q L a)

abbrev degPSFin (μ : (Fv F v ⊗[F] E)ˣ →* Circle) (s : ℂ) : Submodule ℂ (GLoc σ Q v → ℂ) :=
  degPSH σ Q (absEv F E v) (KFin σ Q L v) μ s

abbrev degPSArch (μ : (w.Completion ⊗[F] E)ˣ →* Circle) (s : ℂ) : Submodule ℂ (GArch σ Q w → ℂ) :=
  degPSH σ Q (absEw F E w) (KArch σ Q w b) μ s

abbrev degPSAd (μ : (AF F ⊗[F] E)ˣ →* Circle) (s : ℂ) : Submodule ℂ (GAd σ Q → ℂ) :=
  degPSH σ Q (absE F E) (KAd σ Q L a) μ s

abbrev flatFin (Φ : GLoc σ Q v → ℂ) (s₀ s : ℂ) : GLoc σ Q v → ℂ := flatH σ Q (absEv F E v) (KFin σ Q L v) Φ s₀ s

abbrev flatArch (Φ : GArch σ Q w → ℂ) (s₀ s : ℂ) : GArch σ Q w → ℂ := flatH σ Q (absEw F E w) (KArch σ Q w b) Φ s₀ s

abbrev flatAd (Φ : GAd σ Q → ℂ) (s₀ s : ℂ) : GAd σ Q → ℂ := flatH σ Q (absE F E) (KAd σ Q L a) Φ s₀ s

def prodFun (Φi : ∀ w, GArch σ Q w → ℂ) (Φf : ∀ v, GLoc σ Q v → ℂ) : GAd σ Q → ℂ :=
  fun g => (∏ w, Φi w (projArch σ Q w g)) * ∏ᶠ v, Φf v (proj σ Q v g)

def AlmostOne (Φf : ∀ v, GLoc σ Q v → ℂ) : Prop := ∀ᶠ v in Filter.cofinite, ∀ k ∈ KFin σ Q L v, Φf v k = 1

variable {Q} (h : Q = dblGram finSumFinEquiv J) {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

def zetaFin (m : Measure (GLoc σ J v)) (Φ : GLoc σ Q v → ℂ) (s₀ s : ℂ) (π : GLoc σ J v → X → X) (x y : X) : ℂ :=
  zetaH σ h m (flatFin σ Q L v Φ s₀ s) (coef π x y)

def ZetaConvFin (m : Measure (GLoc σ J v)) (Φ : GLoc σ Q v → ℂ) (s₀ s : ℂ) (π : GLoc σ J v → X → X) (x y : X) : Prop :=
  ZetaConvH σ h m (flatFin σ Q L v Φ s₀ s) (coef π x y)

def zetaArch (m : Measure (GArch σ J w)) (Φ : GArch σ Q w → ℂ) (s₀ s : ℂ) (π : GArch σ J w → X → X) (x y : X) : ℂ :=
  zetaH σ h m (flatArch σ Q w b Φ s₀ s) (coef π x y)

def ZetaConvArch (m : Measure (GArch σ J w)) (Φ : GArch σ Q w → ℂ) (s₀ s : ℂ) (π : GArch σ J w → X → X) (x y : X) :
    Prop := ZetaConvH σ h m (flatArch σ Q w b Φ s₀ s) (coef π x y)

end Defs

section Lemmas

variable {σ Q L} {a : GL (Fin n) (AF F ⊗[F] E)}

theorem apply_rat_mul {μ : (AF F ⊗[F] E)ˣ →* Circle} (hμ : ∀ x : Eˣ, μ (Units.map (inclR (F := F) (AF F)).toMonoidHom x) = 1)
    {s : ℂ} {Φ : GAd σ Q → ℂ} (hΦ : Φ ∈ degPSAd σ Q L a μ s) {γ : GAd σ Q} (hγ : γ ∈ siegelH _ σ Q)
    (hγ' : γ ∈ AdelicU.ratPts σ Q) (g : GAd σ Q) : Φ (γ * g) = Φ g := by
  obtain ⟨x, hx⟩ := exists_aH_eq_of_mem_ratPts ⟨γ, hγ⟩ hγ'
  have := (mem_degPSH.1 hΦ).1 ⟨γ, hγ⟩ g
  rwa [hx, hμ, absE_inclR, one_npow, Circle.coe_one, one_mul, one_mul] at this

omit [NumberField E] in
theorem HasIwasawa.fin (hI : HasIwasawa σ Q (KAd σ Q L a)) (v : HeightOneSpectrum (𝓞 F)) :
    HasIwasawa σ Q (KFin σ Q L v) := fun g => by
  obtain ⟨p, k, hk, e⟩ := hI (emb σ Q v g)
  exact ⟨projP v p, _, (mem_KAd.1 hk).1 v, by rw [coe_projP, ← map_mul, ← e, proj_emb_self]⟩

omit [NumberField E] in
theorem HasIwasawa.arch (hI : HasIwasawa σ Q (KAd σ Q L a)) (w : InfinitePlace F) :
    HasIwasawa σ Q (KArch σ Q w (bc (compInf F E w) a)) := fun g => by
  obtain ⟨p, k, hk, e⟩ := hI (embArch σ Q w g)
  exact ⟨projArchP w p, _, (mem_KAd.1 hk).2 w, by rw [coe_projArchP, ← map_mul, ← e, projArch_embArch_self]⟩

theorem isCompact_KArch (hc : IsCMExt F E σ) (w : InfinitePlace F) (b : GL (Fin n) (w.Completion ⊗[F] E)) :
    IsCompact (KArch σ Q w b : Set (GArch σ Q w)) := Frames.isCompact_stabArch hc Q w _

theorem hgtArch_mul (hc : IsCMExt F E σ) {w : InfinitePlace F} {b : GL (Fin n) (w.Completion ⊗[F] E)}
    (p : siegelH w.Completion σ Q) {k : GArch σ Q w} (hk : k ∈ KArch σ Q w b) :
    hgtArch σ Q w b (p * k) = absEw F E w (aH _ σ Q p) := hgtH_mul (continuous_absEw w) (isCompact_KArch hc w b) p hk

variable [Submodule.IsLattice E L]

theorem isCompact_KFin (v : HeightOneSpectrum (𝓞 F)) : IsCompact (KFin σ Q L v : Set (GLoc σ Q v)) :=
  isCompact_stabLoc σ Q _ v

theorem isOpen_KFin (v : HeightOneSpectrum (𝓞 F)) : IsOpen (KFin σ Q L v : Set (GLoc σ Q v)) := isOpen_stabLoc σ Q _ v

theorem isCompact_KAd (hc : IsCMExt F E σ) : IsCompact (KAd σ Q L a : Set (GAd σ Q)) := isCompact_levelAll hc Q _ _

theorem t2Space_adeleRing' : T2Space (AF F) :=
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  inferInstanceAs (T2Space (Ainf F × Af F))

theorem hgtFin_mul {v : HeightOneSpectrum (𝓞 F)} (p : siegelH (Fv F v) σ Q) {k : GLoc σ Q v} (hk : k ∈ KFin σ Q L v) :
    hgtFin σ Q L v (p * k) = absEv F E v (aH _ σ Q p) := hgtH_mul (continuous_absEv v) (isCompact_KFin v) p hk

theorem hgtAd_mul (hc : IsCMExt F E σ) (p : siegelH (AF F) σ Q) {k : GAd σ Q} (hk : k ∈ KAd σ Q L a) :
    hgtAd σ Q L a (p * k) = absE F E (aH _ σ Q p) :=
  haveI := t2Space_adeleRing' (F := F)
  hgtH_mul continuous_absE (isCompact_KAd hc) p hk

theorem AlmostOne.finite {Φf : ∀ v, GLoc σ Q v → ℂ} (h : AlmostOne σ Q L Φf) (g : GAd σ Q) :
    (Function.mulSupport fun v => Φf v (proj σ Q v g)).Finite :=
  (Filter.eventually_cofinite.1 (h.and (eventually_proj_mem_stabLoc σ Q (sumLat finSumFinEquiv L L) g))).subset
    fun _ hv h' => hv (h'.1 _ h'.2)

theorem finite_mulSupport_hgtFin (g : GAd σ Q) : (Function.mulSupport fun v => hgtFin σ Q L v (proj σ Q v g)).Finite :=
  (Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc σ Q (sumLat finSumFinEquiv L L) g)).subset
    fun v hv h' => hv (hgtH_of_mem (continuous_absEv v) (isCompact_KFin v) h')

theorem HasIwasawa.hgtAd_eq (hI : HasIwasawa σ Q (KAd σ Q L a)) (hc : IsCMExt F E σ) (g : GAd σ Q) :
    hgtAd σ Q L a g = (∏ w, hgtArch σ Q w (bc (compInf F E w) a) (projArch σ Q w g)) *
      ∏ᶠ v, hgtFin σ Q L v (proj σ Q v g) := by
  obtain ⟨p, k, hk, rfl⟩ := hI g
  rw [hgtAd_mul hc p hk, absE_apply]
  congr 1
  · exact Finset.prod_congr rfl fun w _ => by
      rw [map_mul, ← coe_projArchP, hgtArch_mul hc _ ((mem_KAd.1 hk).2 w), aH_projArchP]
  · exact finprod_congr fun v => by rw [map_mul, ← coe_projP, hgtFin_mul _ ((mem_KAd.1 hk).1 v), aH_projP]

end Lemmas

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev negSp (V : HSp D) : HSp D := hneg V

abbrev sumSp (V W : HSp D) : HSp D := hsum V W

abbrev dblSp (V : HSp D) : HSp D := hdbl V

def ioSum (V W : HSp D) : GA D V × GA D W →* GA D (sumSp V W) := sumH _ D.sp.cm.sig (gram_hsum V W)

variable (V : HSp D)

def negEquiv : GA D (negSp V) ≃* GA D V :=
  MulEquiv.subgroupCongr ((congrArg (UJ _) (Matrix.map_neg _ (map_neg (incA D)) V.gram)).trans (UJ_neg _ _))

def io : GA D V × GA D V →* GA D (dblSp V) := ioH _ D.sp.cm.sig (gram_hdbl V)

abbrev siegel : Subgroup (GA D (dblSp V)) := siegelH _ D.sp.cm.sig (dblSp V).gram

abbrev siegelQ : Subgroup (GA D (dblSp V)) := siegel V ⊓ GQ (dblSp V)

abbrev aP : siegel V →* (AE D)ˣ := aH _ D.sp.cm.sig (dblSp V).gram

abbrev detA : GA D V →* (AE D)ˣ := detH _ D.sp.cm.sig V.gram

variable (D) in

abbrev absA : (AE D)ˣ →* ℝ≥0 := absE D.host.F D.host.E

abbrev IsMaj (a : GL (Fin V.rank) (AE D)) : Prop := IsMajorantFrame D.sp.cm.sig V.gram a

variable (a : GL (Fin V.rank) (AE D))

abbrev Kmax : Subgroup (GA D V) := levelAll D.sp.cm.sig V.gram (frameLat V) a

abbrev Khat : Subgroup (GA D (dblSp V)) := KAd D.sp.cm.sig (dblSp V).gram (frameLat V) a

abbrev hgt : GA D (dblSp V) → ℝ≥0 := hgtAd D.sp.cm.sig (dblSp V).gram (frameLat V) a

abbrev degPS (μ : (AE D)ˣ →* Circle) (s : ℂ) : Submodule ℂ (GA D (dblSp V) → ℂ) :=
  degPSAd D.sp.cm.sig (dblSp V).gram (frameLat V) a μ s

abbrev flat (Φ : GA D (dblSp V) → ℂ) (s₀ s : ℂ) : GA D (dblSp V) → ℂ :=
  flatAd D.sp.cm.sig (dblSp V).gram (frameLat V) a Φ s₀ s

abbrev zetaA (m : Measure (GA D V)) (Φ : GA D (dblSp V) → ℂ) (s₀ s : ℂ) (c : GA D V → ℂ) : ℂ :=
  zetaH D.sp.cm.sig (gram_hdbl V) m (flat V a Φ s₀ s) c

abbrev ZetaConvA (m : Measure (GA D V)) (Φ : GA D (dblSp V) → ℂ) (s₀ s : ℂ) (c : GA D V → ℂ) : Prop :=
  ZetaConvH D.sp.cm.sig (gram_hdbl V) m (flat V a Φ s₀ s) c

section Local

variable (v : HeightOneSpectrum (𝓞 D.host.F)) (w : InfinitePlace D.host.F)
  {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

abbrev Gv : Type := GLoc D.sp.cm.sig V.gram v

abbrev Gw : Type := GArch D.sp.cm.sig V.gram w

abbrev degPSv (μ : (AE D)ˣ →* Circle) (s : ℂ) : Submodule ℂ (Gv (dblSp V) v → ℂ) :=
  degPSFin D.sp.cm.sig (dblSp V).gram (frameLat V) v (charAt μ v) s

abbrev degPSw (μ : (AE D)ˣ →* Circle) (s : ℂ) : Submodule ℂ (Gw (dblSp V) w → ℂ) :=
  degPSArch D.sp.cm.sig (dblSp V).gram w (bc (compInf _ _ w) a) (charAtInf μ w) s

abbrev Zv (m : Measure (Gv V v)) (Φ : Gv (dblSp V) v → ℂ) (s₀ s : ℂ) (π : Gv V v → X → X) (x y : X) : ℂ :=
  zetaFin D.sp.cm.sig (frameLat V) v (gram_hdbl V) m Φ s₀ s π x y

abbrev ZvConv (m : Measure (Gv V v)) (Φ : Gv (dblSp V) v → ℂ) (s₀ s : ℂ) (π : Gv V v → X → X) (x y : X) : Prop :=
  ZetaConvFin D.sp.cm.sig (frameLat V) v (gram_hdbl V) m Φ s₀ s π x y

abbrev Zw (m : Measure (Gw V w)) (Φ : Gw (dblSp V) w → ℂ) (s₀ s : ℂ) (π : Gw V w → X → X) (x y : X) : ℂ :=
  zetaArch D.sp.cm.sig w (bc (compInf _ _ w) a) (gram_hdbl V) m Φ s₀ s π x y

abbrev ZwConv (m : Measure (Gw V w)) (Φ : Gw (dblSp V) w → ℂ) (s₀ s : ℂ) (π : Gw V w → X → X) (x y : X) : Prop :=
  ZetaConvArch D.sp.cm.sig w (bc (compInf _ _ w) a) (gram_hdbl V) m Φ s₀ s π x y

abbrev dLoc (W : HSp D) (s : ℂ) : ℂ := GlobalTheory.LFun.dv D.host.E V.rank W.rank v s

end Local

instance isLattice_frameLat_host : Submodule.IsLattice D.host.E (frameLat V) := isLattice_frameLat V

theorem isHermND_gram : IsHermND D.sp.cm.sig V.gram :=
  ⟨fun i j => V.herm.eq (V.frame j) (V.frame i), (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero⟩

theorem exists_isMaj : ∃ a, IsMaj V a :=
  (Frames.exists_isLatticeFrame_isMajorantFrame (isCMExt_host D) (isHermND_gram V) (frameLat V)).imp fun _ h => h.2

theorem matHom_io (g g' : GA D V) : Formalism.L2.Theta.matHom (dblSp V) (io V (g, g')) =
    blkGL finSumFinEquiv (Formalism.L2.Theta.matHom V g, Formalism.L2.Theta.matHom V g') := rfl

theorem matHom_ioSum (W : HSp D) (g : GA D V) (g' : GA D W) : Formalism.L2.Theta.matHom (sumSp V W) (ioSum V W (g, g')) =
    blkGL finSumFinEquiv (Formalism.L2.Theta.matHom V g, Formalism.L2.Theta.matHom W g') := rfl

theorem io_eq_ioSum (g : GA D V) (g' : GA D (negSp V)) : ioSum V (negSp V) (g, g') = io V (g, negEquiv V g') :=
  matHom_injective _ D.sp.cm.sig (dblSp V).gram ((matHom_ioSum V (negSp V) g g').trans (matHom_io V g (negEquiv V g')).symm)

theorem continuous_io : Continuous (io V) := continuous_ioH _
theorem io_injective : Function.Injective (io V) := ioH_injective _

theorem io_mem_GQ {g g' : GA D V} (h : g ∈ GQ V) (h' : g' ∈ GQ V) : io V (g, g') ∈ GQ (dblSp V) := ioH_mem_ratPts _ h h'

theorem io_mem_siegel {g g' : GA D V} : io V (g, g') ∈ siegel V ↔ g = g' := ioH_mem_siegelH _

theorem Khat_eq : Khat V a = Kmax (dblSp V) (blkGL finSumFinEquiv (a, a)) :=
  congrArg (fun L => levelAll D.sp.cm.sig (dblSp V).gram L (blkGL finSumFinEquiv (a, a))) (frameLat_hsum V (hneg V)).symm

theorem IsMaj.dbl {V : HSp D} {a : GL (Fin V.rank) (AE D)} (h : IsMaj V a) :
    IsMaj (dblSp V) (blkGL finSumFinEquiv (a, a)) :=
  isMajorantFrame_dbl (σ := D.sp.cm.sig) (J := V.gram) (Q := (dblSp V).gram) (a := a) (gram_hdbl V) h

theorem io_mem_Khat {g g' : GA D V} : io V (g, g') ∈ Khat V a ↔ g ∈ Kmax V a ∧ g' ∈ Kmax V a := ioH_mem_KAd _

theorem isCompact_Khat : IsCompact (Khat V a : Set (GA D (dblSp V))) := isCompact_KAd (isCMExt_host D)

theorem hgt_mul (p : siegel V) {k : GA D (dblSp V)} (hk : k ∈ Khat V a) : hgt V a (p * k) = absA D (aP V p) :=
  hgtAd_mul (Q := (dblSp V).gram) (L := frameLat V) (a := a) (isCMExt_host D) p hk

theorem mem_degPS {μ : (AE D)ˣ →* Circle} {s : ℂ} {Φ : GA D (dblSp V) → ℂ} : Φ ∈ degPS V a μ s ↔
    (∀ (p : siegel V) (g : GA D (dblSp V)),
      Φ (p * g) = μ (aP V p) * npow (absA D (aP V p)) (s + (V.rank : ℂ) / 2) * Φ g) ∧
      Continuous Φ ∧ IsKFinite (Khat V a) Φ := mem_degPSH

theorem apply_siegelQ_mul {μ : (AE D)ˣ →* Circle} (hμ : IsHeckeChar D μ) {s : ℂ} {Φ : GA D (dblSp V) → ℂ}
    (hΦ : Φ ∈ degPS V a μ s) {γ : GA D (dblSp V)} (hγ : γ ∈ siegelQ V) (g : GA D (dblSp V)) : Φ (γ * g) = Φ g :=
  apply_rat_mul hμ.2 hΦ hγ.1 hγ.2 g

theorem apply_io_mul {μ : (AE D)ˣ →* Circle} {s : ℂ} {Φ : GA D (dblSp V) → ℂ} (hΦ : Φ ∈ degPS V a μ s)
    (x g g' : GA D V) : Φ (io V (x * g, x * g')) = μ (detA V x) * Φ (io V (g, g')) :=
  apply_ioH_mul (gram_hdbl V) (absE_conjUnit _) (isHermND_gram V).2 hΦ x g g'

theorem comp_conjUnit_eq_inv {μ : (AE D)ˣ →* Circle} {k : ℕ} (h : ResEta D μ k) :
    μ.comp (conjUnit D.sp.cm.sig) = μ⁻¹ := by
  obtain ⟨⟨η, hη⟩, h⟩ := h
  refine MonoidHom.ext fun x => eq_inv_of_mul_eq_one_right ?_
  have h1 := h η hη (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) x)
  rw [hη.2.2.1, one_pow] at h1
  rw [MonoidHom.comp_apply, ← map_mul, ← h1]
  exact congrArg μ (Units.ext (algebraMap_norm_eq (isCMExt_host D) x.1).symm)

example (g : GA D V) : hgt V a (io V (g, g)) = 1 := by
  have := hgt_mul V a (ioDiag (gram_hdbl V) g) (one_mem _)
  rwa [mul_one, aH_ioDiag, abs_detH (absE_conjUnit _) (isHermND_gram V).2] at this

end Record

theorem exists_leviH {R : Type} [CommRing R] [Algebra F R] {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x)
    {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} (h : Q = dblGram finSumFinEquiv J) (hJ : IsHermND σ J)
    (α : GL (Fin n) (R ⊗[F] E)) : ∃ p : siegelH R σ Q, (p : HA R σ Q) ∈ leviH R σ Q ∧
      leviOf finSumFinEquiv (matHom R σ Q) p = α ∧ aH R σ Q p = Matrix.GeneralLinearGroup.det α := by
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  letI : Invertible (2 : R ⊗[F] E) := (Invertible.map (algebraMap F (R ⊗[F] E)) 2).copy _ (map_ofNat _ 2).symm
  obtain ⟨β, hβ⟩ := exists_leviElt_mem_UJ finSumFinEquiv (σ := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) (sigR_invol hσ)
    (J := JR R J) (by ext i j; exact congrArg (fun x => (1 : R) ⊗ₜ[F] x) (hJ.1 i j)) (isUnit_det_JR hJ.2) α
  rw [← JR_dblGram, ← h] at hβ
  obtain ⟨g, hg⟩ : ∃ g : HA R σ Q, matHom R σ Q g = leviElt finSumFinEquiv (α, β) := ⟨⟨_, hβ⟩, rfl⟩
  have h1 : g ∈ siegelH R σ Q := Subgroup.mem_comap.2 (hg ▸ leviElt_mem_diag finSumFinEquiv (α, β))
  have e : leviOf finSumFinEquiv (matHom R σ Q) ⟨g, h1⟩ = α :=
    Units.ext (by rw [val_leviOf, hg, leviMat_leviElt])
  exact ⟨⟨g, h1⟩, ⟨h1, Subgroup.mem_comap.2 (hg ▸ leviElt_mem_anti finSumFinEquiv (α, β))⟩, e,
    by rw [aH, aOf, MonoidHom.comp_apply, e]⟩

example (hd : Module.finrank F E = 2) {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J)
    [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)) (c : (Fv F v)ˣ) :
    ∃ g, hgtFin σ (dblGram finSumFinEquiv J) L v g = ‖c.1‖₊ ^ (2 * n) := by
  obtain ⟨p, -, -, hp⟩ := exists_leviH hσ rfl hJ (Matrix.GeneralLinearGroup.scalar (Fin n)
    (Units.map (algebraMap (Fv F v) (Fv F v ⊗[F] E)).toMonoidHom c))
  refine ⟨p * 1, ?_⟩
  rw [hgtFin_mul p (one_mem _), hp, pow_mul, ← hd, ← absEv_algebraMap, ← map_pow]
  congr 1
  ext
  simp

example {R : Type} [CommRing R] [Algebra F R] (Q : Matrix (Fin (0 + 0)) (Fin (0 + 0)) E) (K : Subgroup (HA R σ Q)) :
    HasIwasawa σ Q K := fun g =>
  ⟨⟨g, mem_siegelOf.2 (Subsingleton.elim _ _)⟩, 1, one_mem _, (mul_one g).symm⟩

end GlobalTheory.Doubling

end
