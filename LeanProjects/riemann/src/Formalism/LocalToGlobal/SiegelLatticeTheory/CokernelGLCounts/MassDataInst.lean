import Mathlib
import Formalism.HermitianCurvature.StatementPB
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes

noncomputable section

namespace Formalism.L2.SG.TypedSets

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Classical

section Typed

variable (F : Type) [Field F] [NumberField F]

def IsTyped (g1 g2 : ℕ) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  (g1 : 𝓞 F) ∈ v.asIdeal ∨ (g2 : 𝓞 F) ∈ v.asIdeal

theorem finite_over (g : ℕ) (hg : g ≠ 0) : {v : HeightOneSpectrum (𝓞 F) | (g : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have hg' : ((g : 𝓞 F)) ≠ 0 := Nat.cast_ne_zero.mpr hg
  have hI : Ideal.span {(g : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hg'
  refine (Ideal.finite_factors hI).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem typed_finite (g1 g2 : ℕ) (h1 : g1 ≠ 0) (h2 : g2 ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | IsTyped F g1 g2 v}.Finite := ((finite_over F g1 h1).union (finite_over F g2 h2)).subset fun v hv => hv

def typSet (g1 g2 : ℕ) : Finset (HeightOneSpectrum (𝓞 F)) :=
  if h : {v : HeightOneSpectrum (𝓞 F) | IsTyped F g1 g2 v}.Finite then h.toFinset else ∅

theorem mem_typSet (g1 g2 : ℕ) (h1 : g1 ≠ 0) (h2 : g2 ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ typSet F g1 g2 ↔ IsTyped F g1 g2 v := by
  unfold typSet
  rw [dif_pos (typed_finite F g1 g2 h1 h2), Set.Finite.mem_toFinset]
  rfl

abbrev TypP (g1 g2 : ℕ) : Type := ↥(typSet F g1 g2)

variable {F}

def gOf {g1 g2 : ℕ} (p : TypP F g1 g2) : ℕ := if (g1 : 𝓞 F) ∈ p.1.asIdeal then g1 else g2

end Typed

def glkC (k g : ℕ) : ℕ := Nat.card (GL (Fin k) (ZMod g))

def ukC (k g : ℕ) : ℕ := Nat.card (Formalism.DoubleCosetMeasures.upUniG (ZMod g) k)

def nnC (r k g : ℕ) : ℕ := Nat.card {x : Matrix (Formalism.FourierDecayAlt.S3.Idx r k) (Formalism.FourierDecayAlt.S3.Idx r k) (ZMod g) //
  Formalism.FourierDecayAlt.S3.IsN x}

def ggC (r k g : ℕ) : ℕ := Nat.card (GL (Formalism.FourierDecayAlt.S3.Idx r k) (ZMod g))

def covolBy {G : Type} [Group G] [MeasurableSpace G] (Γ : Subgroup G) (μ : Measure G) : ℝ :=
  if h : ∃ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ then (μ h.choose).toReal else 0

def massCl {G : Type} [Group G] (Γ K : Subgroup G) : ℝ :=
  ∑ᶠ c : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
    ((Nat.card ↥(Γ ⊓ K.map (MulAut.conj (Quotient.out c)).toMonoidHom) : ℕ) : ℝ)⁻¹

def MassFinite {G : Type} [Group G] (Γ K : Subgroup G) : Prop :=
  Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) ∧ ∀ x : G, Finite ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom)

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E) (Λ : Set (Fin n → E))

def Kv (v : HeightOneSpectrum (𝓞 F)) : Set (HA (Fv F v) σ J) :=
  {x | HA.mat (Fv F v) σ J x ∈ Kloc (E := E) v Λ}

def Kgv (g : ℕ) (v : HeightOneSpectrum (𝓞 F)) : Set (HA (Fv F v) σ J) :=
  {x | x ∈ Kv σ J Λ v ∧ ∀ y ∈ latLoc (E := E) v Λ, ∃ z ∈ latLoc (E := E) v Λ,
    Matrix.mulVec ((HA.mat (Fv F v) σ J x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) - 1) y =
      (g : v.adicCompletionIntegers F) • z}

def Knatv {r : ℕ} (P : Frame E n r) (g : ℕ) (v : HeightOneSpectrum (𝓞 F)) : Set (HA (Fv F v) σ J) :=
  {x | x ∈ Kv σ J Λ v ∧ ∃ s κ, s ∈ (Ssub (Fv F v) σ J P : Set (HA (Fv F v) σ J)) ∧ s ∈ Kv σ J Λ v ∧
    κ ∈ Kgv σ J Λ g v ∧ x = s * κ}

def compSet (Kpp : Set (HA (Af F) σ J)) (v : HeightOneSpectrum (𝓞 F)) : Set (HA (Fv F v) σ J) :=
  haMap σ J (evalV F v) '' Kpp

def massH {r : ℕ} (P : Frame E n r) : ℝ :=
  massCl (G := ↥(Hsub (Af F) σ J P))
    ((HFinIn (Af F) σ J : Subgroup (HA (Af F) σ J)).subgroupOf (Hsub (Af F) σ J P))
    ((Kf σ J Λ).subgroupOf (Hsub (Af F) σ J P))

end Loc

structure LocIn (P : Type) where
  Mp : P → ℝ
  localVolumeAtPlace : P → ℝ
  Mo : ℝ
  localVolumeArchimedean : ℝ
  volZZ : ℝ
  volPP : ℝ
  al : ℝ

structure AnIn where
  Coo : ℝ
  deg : ℝ
  IntN : ℝ
  IntC : ℝ
  IntOO : ℝ
  Sig : ℝ
  KV : ℝ
  KtopV : ℝ
  Kgs2 : ℝ
  supdens : ℝ
  e1 : ℝ
  δ : ℝ

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E) (Λ : Set (Fin n → E)) {r : ℕ} (k : ℕ) (P P' : Frame E n r)
  (Kpp Kpp1 Kpp2 : Set (HA (Af F) σ J)) (MG : MeasG σ J r) (MW : MeasW σ J P) (MW' : MeasW σ J P')
  (X0 : Fin (2 * r + 2) → Fin n → E) (g1 g2 : ℕ) (du du' dπ dπ' vH vH' vN vN' : ℝ) (L : LocIn (TypP F g1 g2)) (A : AnIn)

def massDataPre : Formalism.FourierDecayAlt.S3.MassData (TypP F g1 g2) where
  g p := gOf p
  glk p := glkC k (gOf p)
  uk p := ukC k (gOf p)
  nn p := nnC r k (gOf p)
  gg p := ggC r k (gOf p)
  μKp p := (MG.μGv p.1 (Kv σ J Λ p.1)).toReal
  μKnatp p := (MG.μGv p.1 (Knatv σ J Λ P (gOf p) p.1)).toReal
  μKppp p := (MG.μGv p.1 (compSet σ J Kpp p.1)).toReal
  μSp p := (MW.μSv p.1 (Subtype.val ⁻¹' Kv σ J Λ p.1)).toReal
  μSp' p := (MW'.μSv p.1 (Subtype.val ⁻¹' Kv σ J Λ p.1)).toReal
  μSppp p := (MW.μSv p.1 (Subtype.val ⁻¹' compSet σ J Kpp1 p.1)).toReal
  μSppp' p := (MW'.μSv p.1 (Subtype.val ⁻¹' compSet σ J Kpp2 p.1)).toReal
  Mp := L.Mp
  localVolumeAtPlace := L.localVolumeAtPlace
  μKo := (MG.μGf (Kf σ J Λ)).toReal / ∏ p : TypP F g1 g2, (MG.μGv p.1 (Kv σ J Λ p.1)).toReal
  μSo := (MW.μSf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J)))).toReal /
    ∏ p : TypP F g1 g2, (MW.μSv p.1 (Subtype.val ⁻¹' Kv σ J Λ p.1)).toReal
  μSo' := (MW'.μSf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J)))).toReal /
    ∏ p : TypP F g1 g2, (MW'.μSv p.1 (Subtype.val ⁻¹' Kv σ J Λ p.1)).toReal
  Mo := L.Mo
  localVolumeArchimedean := L.localVolumeArchimedean
  μH := (MW.μHf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J)))).toReal
  μH' := (MW'.μHf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J)))).toReal
  μHpp := (MW.μHf (Subtype.val ⁻¹' Kpp1)).toReal
  μHpp' := (MW'.μHf (Subtype.val ⁻¹' Kpp2)).toReal
  μN := (MW.μNf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J)))).toReal
  μN' := (MW'.μNf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J)))).toReal
  volZZ := L.volZZ
  volPP := L.volPP
  al := L.al
  volG := covolBy (G := HA (AF F) σ J) (HFinIn (AF F) σ J) MG.μG
  volHa := covol MW.μH
  volHa' := covol MW'.μH
  volNa := covol MW.μN
  volNa' := covol MW'.μN
  volB := covol (MG.μB X0)
  volH := vH
  volH' := vH'
  volN := vN
  volN' := vN'
  Coo := A.Coo
  deg := A.deg
  dimπ := dπ
  dimπ' := dπ'
  ρ0 := massH σ J Λ P
  ρ0' := massH σ J Λ P'
  d := du
  d' := du'
  n0c := 0
  supdens := A.supdens
  e1 := A.e1
  δ := A.δ
  Kgs2 := A.Kgs2
  KV := A.KV
  Sig := A.Sig
  KtopV := A.KtopV
  IntN := A.IntN
  IntC := A.IntC
  IntOO := A.IntOO

def massDataOf : Formalism.FourierDecayAlt.S3.MassData (TypP F g1 g2) :=
  { massDataPre σ J Λ k P P' Kpp Kpp1 Kpp2 MG MW MW' X0 g1 g2 du du' dπ dπ' vH vH' vN vN' L A with
    n0c := (massDataPre σ J Λ k P P' Kpp Kpp1 Kpp2 MG MW MW' X0 g1 g2 du du' dπ dπ' vH vH' vN vN' L A).AA /
      (massDataPre σ J Λ k P P' Kpp Kpp1 Kpp2 MG MW MW' X0 g1 g2 du du' dπ dπ' vH vH' vN vN' L A).ρ0 }

theorem inMass_massDataOf (h : massH σ J Λ P ≠ 0) :
    (massDataOf σ J Λ k P P' Kpp Kpp1 Kpp2 MG MW MW' X0 g1 g2 du du' dπ dπ' vH vH' vN vN' L A).InMass := by
  unfold Formalism.FourierDecayAlt.S3.MassData.InMass
  exact div_mul_cancel₀ _ h

end Gen

section OfSetting

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter)

def frameOf (u : D.what₂.Word) : Frame X.B.I.E X.B.I.n D.R.rS :=
  ⟨fun a => crdOf X.B.I X.ιE X.bas (X.eX a), fun a => crdOf X.B.I X.ιE X.bas (X.fY a),
    crdOf X.B.I X.ιE X.bas (X.zu u)⟩

def finHA (x : X.B.I.Gf) : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J :=
  (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (1, x))).2

def levelUnitary : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := finHA X hb '' X.K2

def K2u (u : D.what₂.Word) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
  (fun y => finHA X hb (X.xu u) * y * (finHA X hb (X.xu u))⁻¹) '' levelUnitary X hb

abbrev TypX : Type := TypP X.B.I.F (D.host.g 0) (D.host.g 1)

def bOf (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : LocIn (TypX X)) (A : AnIn) :
    Formalism.FourierDecayAlt.S3.MassData (TypX X) :=
  massDataOf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) D.R.k (frameOf X u) (frameOf X u')
    (levelUnitary X hb) (K2u X hb u) (K2u X hb u') X.measG (X.measW u) (X.measW u') X0 (D.host.g 0) (D.host.g 1)
    (Module.finrank ℂ (Formalism.L2.SG.PoincareInHH.PoincareSetting.Cu X u hK))
    (Module.finrank ℂ (Formalism.L2.SG.PoincareInHH.PoincareSetting.Cu X u' hK))
    (Module.finrank ℂ (X.Vpi u)) (Module.finrank ℂ (X.Vpi u'))
    (X.muH u Set.univ).toReal (X.muH u' Set.univ).toReal (X.muN u FdN).toReal (X.muN u' FdN').toReal L A

def HypX (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word) : Prop :=
  X.MeasTie hb ∧ X.LevelSubgroupNormalized ∧ IsSFund X.B.I (Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) FdN ∧
    IsSFund X.B.I (Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u') FdN'

end OfSetting

section Stmts

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Volumes

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
  (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : LocIn (TypX X)) (A : AnIn)

def InLevelSAt : Prop :=
  HypX X hb FdN FdN' u u' → (bOf X hb hK FdN FdN' u u' X0 L A).InLevelS

def InMassesAt : Prop :=
  HypX X hb FdN FdN' u u' → (bOf X hb hK FdN FdN' u u' X0 L A).InMasses

def InColumnsAt : Prop :=
  HypX X hb FdN FdN' u u' → (bOf X hb hK FdN FdN' u u' X0 L A).InColumns

def InIndicesAt : Prop :=
  HypX X hb FdN FdN' u u' → (bOf X hb hK FdN FdN' u u' X0 L A).InIndices

def KppVolAt : Prop :=
  HypX X hb FdN FdN' u u' → (bOf X hb hK FdN FdN' u u' X0 L A).μKpp = (X.measG.μGf (levelUnitary X hb)).toReal

def InVolumesAt : Prop :=
  HypX X hb FdN FdN' u u' → ∀ ψ : AddChar (AF X.B.I.F) ℂ, IsCharAF X.B.I.F ψ →
    ∀ (hT1 : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u)) j i) =
        gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u)) i j) (νH : Measure _),
      IsOmT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ψ _ hT1 νH →
      IsCompatT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (tupH (frameOf X u)) X.measG.μG (X.measW u).μH νH →
    ∀ (hT1' : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
        gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j) (νH' : Measure _),
      IsOmT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ψ _ hT1' νH' →
      IsCompatT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (tupH (frameOf X u')) X.measG.μG (X.measW u').μH νH' →
    ∀ (hTB : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J X0 j i) = gramE X.B.I.cm.sig X.B.I.J X0 i j)
      (νB : Measure _),
      (gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0 →
      IsOmT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ψ _ hTB νB →
      IsCompatT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J X0 X.measG.μG (X.measG.μB X0) νB →
    covol (X.measW u).μN = 1 → covol (X.measW u').μN = 1 →
    (bOf X hb hK FdN FdN' u u' X0 L A).InVolumes

def InFormAt : Prop :=
  HypX X hb FdN FdN' u u' → (bOf X hb hK FdN FdN' u u' X0 L A).InForm

def RealInputsAt (jn sd C Th : ℝ) : Prop :=
  (bOf X hb hK FdN FdN' u u' X0 L A).InNu ∧ (bOf X hb hK FdN FdN' u u' X0 L A).InJacMod ∧
    (bOf X hb hK FdN FdN' u u' X0 L A).InInfinity ∧
    Formalism.FourierDecayAlt.PB.EnergyLink (bOf X hb hK FdN FdN' u u' X0 L A) jn sd C Th D.R.rS (Fintype.card (InfinitePlace X.B.I.F))

def LinkAt {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) {ι : Type} [Fintype ι]
    (G : Formalism.FourierDecayAlt.Sz.Glob ι) (de : ℕ → ℝ) : Prop :=
  Formalism.FourierDecayAlt.PB.Link T (bOf X hb hK FdN FdN' u u' X0 L A) G de (D.mem u).A.T
    (Module.finrank ℂ (Formalism.L2.SG.PoincareInHH.PoincareSetting.Cu X u hK))
    (Module.finrank ℂ (Formalism.L2.SG.PoincareInHH.PoincareSetting.Cu X u' hK))

end Stmts

end Formalism.L2.SG.TypedSets
