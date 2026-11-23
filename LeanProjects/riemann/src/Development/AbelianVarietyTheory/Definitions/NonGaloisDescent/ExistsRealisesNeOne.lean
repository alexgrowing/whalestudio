import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.EpsilonConsistencyFiniteOrder
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocExtProper

noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.DelEps
open GroundTheory.Global (HeckeCharacter localAdelicChar)
open GroundTheory.Automorphic.GodementSection (localChar)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DelGlob

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

open Classical in
variable (F) in

def unifU : Fˣ := if hx : ∃ y : Fˣ, ord F y = 1 then hx.choose else 1

open Classical in

def lfac (χ : Fˣ →* ℂˣ) (s : ℂ) : ℂ :=
  if IsUnram χ then 1 - ((χ (unifU F) : ℂˣ) : ℂ) * (resCard F : ℂ) ^ (-s) else 1

end Local

variable {Ω : Type} [Field Ω]

section Galois

variable (k L Ω : Type) [Field k] [Field L] [Field Ω] [Algebra k Ω] [Algebra L Ω] [Algebra k L] [IsScalarTower k L Ω]

def resG : G L Ω →* G k Ω := AlgEquiv.restrictScalarsHom k

variable {L Ω}

open Classical in

def ext0 (χ : G L Ω →* ℂˣ) (σ : G k Ω) : ℂ :=
  if hx : ∃ τ : G L Ω, resG k L Ω τ = σ then ((χ hx.choose : ℂˣ) : ℂ) else 0

def gInd (χ : G L Ω →* ℂˣ) (σ : G k Ω) : ℂ :=
  ∑ᶠ q : G k Ω ⧸ (resG k L Ω).range, ext0 k χ (q.out⁻¹ * σ * q.out)

end Galois

section Hecke

variable {L : Type} [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω]

def Matches (χ : G L Ω →* ℂˣ) (X : HeckeCharacter L) : Prop :=
  ∀ (A : ValuationSubring Ω) (u : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A u) (a : Weil h →* (u.adicCompletion L)ˣ),
    IsLocalArtin h a → ∀ σ : Weil h, localChar X u (a σ) = χ (σ : G L Ω)

open Classical in

def hk (χ : G L Ω →* ℂˣ) : HeckeCharacter L :=
  if hx : ∃ X : HeckeCharacter L, Matches χ X ∧ ∃ N : ℕ, 0 < N ∧ X ^ N = 1 then hx.choose else 1

theorem matches_one : Matches (1 : G L Ω →* ℂˣ) (1 : HeckeCharacter L) := fun _ _ _ _ _ _ => Units.ext rfl

end Hecke

structure GTerm (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] where

  L : Type
  [fld : Field L]
  [nf : NumberField L]
  [alg : Algebra L Ω]
  [cl : IsAlgClosure L Ω]
  [algK : Algebra k L]
  [tow : IsScalarTower k L Ω]

  χ : G L Ω →* ℂˣ

  op : IsOpen (χ.ker : Set (G L Ω))

  n : ℤ

attribute [instance] GTerm.fld GTerm.nf GTerm.alg GTerm.cl GTerm.algK GTerm.tow

section Global

variable {k : Type} [Field k] [NumberField k] [Algebra k Ω] [IsAlgClosure k Ω]

def GTerm.self (χ : G k Ω →* ℂˣ) (op : IsOpen (χ.ker : Set (G k Ω))) (n : ℤ) : GTerm k Ω :=
  { L := k, χ := χ, op := op, n := n }

def GRel (gl : List (GTerm k Ω)) : Prop :=
  ∀ σ : G k Ω, (gl.map fun t => (t.n : ℂ) * (gInd k t.χ σ - gInd k (1 : G t.L Ω →* ℂˣ) σ)).sum = 0

abbrev GTerm.Over (t : GTerm k Ω) (w : HeightOneSpectrum (𝓞 k)) : Type :=
  {u : HeightOneSpectrum (𝓞 t.L) // u.under (𝓞 k) = w}

def GTerm.eps (t : GTerm k Ω) (w : HeightOneSpectrum (𝓞 k)) : ℂ :=
  ∏ᶠ u : t.Over w,
    (tateEps (localAdelicChar t.L u.1) (localChar (hk t.χ) u.1) / tateEps (localAdelicChar t.L u.1) 1) ^ t.n

def GTerm.lf (t : GTerm k Ω) (w : HeightOneSpectrum (𝓞 k)) (s : ℂ) : ℂ :=
  ∏ᶠ u : t.Over w, (lfac (localChar (hk t.χ) u.1) s / lfac (1 : (u.1.adicCompletion t.L)ˣ →* ℂˣ) s) ^ t.n

def geps (gl : List (GTerm k Ω)) (w : HeightOneSpectrum (𝓞 k)) : ℂ := (gl.map fun t => t.eps w).prod

def glf (gl : List (GTerm k Ω)) (w : HeightOneSpectrum (𝓞 k)) (s : ℂ) : ℂ := (gl.map fun t => t.lf w s).prod

omit [NumberField k] [IsAlgClosure k Ω] in

theorem continuous_resG (L : Type) [Field L] [Algebra L Ω] [Algebra k L] [IsScalarTower k L Ω] :
    Continuous (resG k L Ω) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff k Ω U).1 hU
  let b := Module.finBasis k E
  let S : Set Ω := Set.range fun i => (b i : Ω)
  haveI : Finite S := (Set.finite_range _).to_subtype
  have hS : ∀ x ∈ S, IsIntegral L x := by
    rintro _ ⟨i, rfl⟩
    exact ((IsIntegral.of_finite k (b i)).map E.val).tower_top
  have hfd := IntermediateField.finiteDimensional_adjoin hS
  refine Filter.mem_map.2 ((krullTopology_mem_nhds_one_iff L Ω _).2
    ⟨IntermediateField.adjoin L S, hfd, fun σ hσ => hEU ?_⟩)
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  intro x hx
  have e : (resG k L Ω σ).toLinearMap ∘ₗ E.val.toLinearMap = E.val.toLinearMap :=
    b.ext fun i => hσ _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  exact LinearMap.congr_fun e ⟨x, hx⟩

def GTerm.twist (t : GTerm k Ω) (ξ : G k Ω →* ℂˣ) (hξ : IsOpen (ξ.ker : Set (G k Ω))) : GTerm k Ω :=
  { t with
    χ := t.χ * ξ.comp (resG k t.L Ω)
    op := Subgroup.isOpen_mono (H₁ := t.χ.ker ⊓ ξ.ker.comap (resG k t.L Ω))
      (fun σ hσ => by
        have h1 : t.χ σ = 1 := hσ.1
        have h2 : ξ (resG k t.L Ω σ) = 1 := hσ.2
        simp [MonoidHom.mem_ker, h1, h2])
      (t.op.inter (hξ.preimage (continuous_resG t.L))) }

def GTerm.cotwist (t : GTerm k Ω) (ξ : G k Ω →* ℂˣ) (hξ : IsOpen (ξ.ker : Set (G k Ω))) : GTerm k Ω :=
  { t with
    χ := ξ.comp (resG k t.L Ω)
    op := hξ.preimage (continuous_resG t.L)
    n := -t.n }

def gtw (gl : List (GTerm k Ω)) (ξ : G k Ω →* ℂˣ) (hξ : IsOpen (ξ.ker : Set (G k Ω))) : List (GTerm k Ω) :=
  (gl.map fun t => t.twist ξ hξ) ++ gl.map fun t => t.cotwist ξ hξ

def GUnr (gl : List (GTerm k Ω)) (A : ValuationSubring Ω) : Prop :=
  ∀ t ∈ gl, ∀ σ ∈ Ine (F := k) A, ∀ g : G k Ω, ∃ τ : G t.L Ω, resG k t.L Ω τ = g⁻¹ * σ * g ∧ t.χ τ = 1

end Global

section Place

variable {A : ValuationSubring Ω} {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v} {ψ : AddChar (v.adicCompletion K) Circle}

def BRel (l : List (BTerm h ψ)) : Prop :=
  ∀ σ : Weil h, (l.map fun t => (t.n : ℂ) * (trW t.indChi σ - trW t.indOne σ)).sum = 0

def wfix (E : LocExt h) : Subgroup (Weil h) := (resG K E.L Ω).range.comap (Weil h).subtype

open Classical in

def wext (E : LocExt h) (ξ : Weil E.h' →* ℂˣ) (σ : Weil h) : ℂ :=
  if hx : ∃ τ : Weil E.h', resG K E.L Ω τ = σ then ((ξ hx.choose : ℂˣ) : ℂ) else 0

open Classical in

def pull (b : BTerm h ψ) (ξ : Weil h →* ℂˣ) : (b.E.v'.adicCompletion b.E.L)ˣ →* ℂˣ :=
  if hx : ∃ η : (b.E.v'.adicCompletion b.E.L)ˣ →* ℂˣ, IsSmoothChar η ∧
      ∀ (τ : Weil b.E.h') (σ : Weil h), resG K b.E.L Ω τ = σ → η (b.a τ) = ξ σ then hx.choose else 1

def tval (l : List (BTerm h ψ)) (ξ : Weil h →* ℂˣ) : ℂ :=
  (l.map fun b => (tateEps b.ψ' (b.χ * pull b ξ) / tateEps b.ψ' (pull b ξ)) ^ b.n).prod

def blf (l : List (BTerm h ψ)) (s : ℂ) : ℂ :=
  (l.map fun b => (lfac b.χ s / lfac (1 : (b.E.v'.adicCompletion b.E.L)ˣ →* ℂˣ) s) ^ b.n).prod

structure FCorr (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]
    (u : HeightOneSpectrum (𝓞 L)) (E : LocExt h) (g : G K Ω)
    (i : u.adicCompletion L ≃+* E.v'.adicCompletion E.L) : Prop where

  cont : Continuous i

  psi : ∀ x, localAdelicChar E.L E.v' (i x) = localAdelicChar L u x

  fix : ∀ σ : Weil h, σ ∈ wfix E ↔ g⁻¹ * (σ : G K Ω) * g ∈ (resG K L Ω).range

  art : ∀ (χ : G L Ω →* ℂˣ) (X : HeckeCharacter L), Matches χ X →
    ∀ a : Weil E.h' →* (E.v'.adicCompletion E.L)ˣ, IsLocalArtin E.h' a →
      ∀ (σ : Weil E.h') (τ : G L Ω) (x : (u.adicCompletion L)ˣ),
        resG K L Ω τ = g⁻¹ * resG K E.L Ω σ * g → Units.map i.toRingHom.toMonoidHom x = a σ → localChar X u x = χ τ

end Place

structure Realises {A : ValuationSubring Ω} {k : Type} [Field k] [NumberField k] [Algebra k Ω] [IsAlgClosure k Ω]
    {w : HeightOneSpectrum (𝓞 k)} {h : IsPlaceOver A w} (t : GTerm k Ω)
    (b : t.Over w → BTerm h (localAdelicChar k w)) (g : t.Over w → G k Ω)
    (i : ∀ u : t.Over w, u.1.adicCompletion t.L ≃+* (b u).E.v'.adicCompletion (b u).E.L) : Prop where

  corr : ∀ u, FCorr t.L u.1 (b u).E (g u) (i u)

  n_eq : ∀ u, (b u).n = t.n

  psi : ∀ u, (b u).ψ' = localAdelicChar (b u).E.L (b u).E.v'

  chi : ∀ u x, (b u).χ (Units.map (i u).toRingHom.toMonoidHom x) = localChar (hk t.χ) u.1 x

  indChi : ∀ σ : Weil h, gInd k t.χ σ = ∑ᶠ u, trW (b u).indChi σ

  indOne : ∀ σ : Weil h, gInd k (1 : G t.L Ω →* ℂˣ) σ = ∑ᶠ u, trW (b u).indOne σ

example {k : Type} [Field k] [NumberField k] [Algebra k Ω] [IsAlgClosure k Ω] (χ : G k Ω →* ℂˣ)
    (op : IsOpen (χ.ker : Set (G k Ω))) : GRel [GTerm.self χ op 1, GTerm.self χ op (-1)] := fun σ => by
  simp [GTerm.self]

namespace Inh

variable {L : Type} [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω]

theorem exists_pow_eq_one (χ : G L Ω →* ℂˣ) (op : IsOpen (χ.ker : Set (G L Ω))) :
    ∃ N : ℕ, 0 < N ∧ ∀ σ, χ σ ^ N = 1 := by
  have : IsGalois L Ω := IsAlgClosure.isGalois L Ω
  have : Finite (G L Ω ⧸ χ.ker) := Subgroup.quotient_finite_of_isOpen _ op
  have : χ.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine ⟨χ.ker.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, fun σ => ?_⟩
  rw [← map_pow]
  exact χ.ker.pow_index_mem σ

theorem exists_matches (χ : G L Ω →* ℂˣ) (op : IsOpen (χ.ker : Set (G L Ω))) :
    ∃ X : HeckeCharacter L, Matches χ X ∧ ∃ N : ℕ, 0 < N ∧ X ^ N = 1 := by
  obtain ⟨N, hN, hχ⟩ := exists_pow_eq_one χ op
  obtain ⟨art, hart⟩ := GlobalTheory.globalArtinReciprocity_holds L Ω
  have hn : ∀ σ, ‖((χ σ : ℂˣ) : ℂ)‖ = 1 := fun σ =>
    Complex.norm_eq_one_of_pow_eq_one (n := N) (by rw [← Units.val_pow_eq_pow_val, hχ, Units.val_one]) hN.ne'
  let c : G L Ω →* Circle :=
    { toFun := fun σ => ⟨χ σ, by simpa [Submonoid.unitSphere] using hn σ⟩
      map_one' := Circle.ext (by simp)
      map_mul' := fun _ _ => Circle.ext (by simp; rfl) }
  have hc : ∀ σ, ((c σ : Circle) : ℂ) = χ σ := fun _ => rfl
  have hk : c.ker = χ.ker := by
    ext σ
    simp only [MonoidHom.mem_ker, Circle.ext_iff, hc, Units.ext_iff]
    rfl
  have hop : IsOpen (c.ker : Set (G L Ω)) := hk ▸ op
  have hcc : Continuous c := by
    refine continuous_of_continuousAt_one _ ?_
    refine continuousAt_const.congr (f := fun _ => 1) ?_
    filter_upwards [hop.mem_nhds c.ker.one_mem] with σ hσ using (hσ : c σ = 1).symm
  have hle : (commutator (G L Ω)).topologicalClosure ≤ c.ker :=
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker c) (c.ker.isClosed_of_isOpen hop)
  let d : GlobalTheory.HeckeGal.Gab L Ω →* Circle := QuotientGroup.lift _ c hle
  have hd : Continuous d := (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 hcc
  have hdiag : (GroundTheory.Global.IdeleGroup.diagonal L).range ≤ (d.comp art).ker := by
    intro x hx
    have : x ∈ art.ker := by
      rw [hart.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left hx)
    exact (congrArg d (this : art x = 1)).trans (map_one d)
  let X : HeckeCharacter L :=
    { toMonoidHom := QuotientGroup.lift _ (d.comp art) hdiag
      continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (hd.comp hart.quot.continuous) }
  refine ⟨X, fun A u h a ha σ => Units.ext ?_, N, hN, ?_⟩
  · have := ha.glob art hart σ
    change ((d (art (Neutral.B1.localIdele L u (a σ))) : Circle) : ℂ) = _
    rw [this]
    rfl
  · ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (art y)
    have e : X y = c σ := by
      change d (art y) = _
      rw [← hσ]; rfl
    have : (X ^ N) y = X y ^ N := ContinuousMonoidHom.pow_apply _ _ _
    rw [this, e]
    simp only [Circle.coe_pow, hc]
    rw [← Units.val_pow_eq_pow_val, hχ]
    rfl

theorem hk_spec (χ : G L Ω →* ℂˣ) (op : IsOpen (χ.ker : Set (G L Ω))) :
    Matches χ (hk χ) ∧ ∃ N : ℕ, 0 < N ∧ hk χ ^ N = 1 := by
  have hx := exists_matches χ op
  rw [hk, dif_pos hx]
  exact hx.choose_spec

section Ind

variable (k : Type) [Field k] [Algebra k Ω] [Algebra k L] [IsScalarTower k L Ω]

omit [NumberField L] [IsAlgClosure L Ω] in

theorem resG_injective : Function.Injective (resG k L Ω) := fun _ _ e =>
  AlgEquiv.ext fun x => DFunLike.congr_fun e x

omit [NumberField L] [IsAlgClosure L Ω] in

theorem extendByZero_restrict (χ : G L Ω →* ℂˣ) (τ : G L Ω) : ext0 k χ (resG k L Ω τ) = χ τ := by
  have hx : ∃ τ' : G L Ω, resG k L Ω τ' = resG k L Ω τ := ⟨τ, rfl⟩
  rw [ext0, dif_pos hx, resG_injective k hx.choose_spec]

omit [NumberField L] [IsAlgClosure L Ω] in

theorem gInd_twist (χ : G L Ω →* ℂˣ) (ξ : G k Ω →* ℂˣ) (σ : G k Ω) :
    gInd k (χ * ξ.comp (resG k L Ω)) σ = ξ σ * gInd k χ σ := by
  rw [gInd, gInd, mul_finsum]
  refine finsum_congr fun q => ?_
  by_cases hx : ∃ τ : G L Ω, resG k L Ω τ = q.out⁻¹ * σ * q.out
  · obtain ⟨τ, hτ⟩ := hx
    have : ξ (resG k L Ω τ) = ξ σ := by rw [hτ]; simp [mul_comm]
    rw [← hτ, extendByZero_restrict, extendByZero_restrict]
    simp [this, mul_comm]
  · simp [ext0, hx]

end Ind

section Self

variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)}

theorem gInd_self (χ : G L Ω →* ℂˣ) (σ : G L Ω) : gInd L χ σ = χ σ := by
  have ht : (resG L L Ω).range = ⊤ := eq_top_iff.2 fun τ _ => ⟨τ, rfl⟩
  have : Subsingleton (G L Ω ⧸ (resG L L Ω).range) := ht ▸ QuotientGroup.subsingleton_quotient_top
  let _ : Unique (G L Ω ⧸ (resG L L Ω).range) := uniqueOfSubsingleton (QuotientGroup.mk 1)
  rw [gInd, finsum_unique]
  generalize (Quotient.out (default : G L Ω ⧸ (resG L L Ω).range) : G L Ω) = g
  exact (extendByZero_restrict L χ (g⁻¹ * σ * g)).trans (by simp [mul_comm])

theorem trW_char (h : IsPlaceOver A w) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) (σ : Weil h) :
    trW (WD.lpOfChar h ξ hξ) σ = ξ σ := by
  rw [WD.lpOfChar, trW_mk]
  have : (WDRep.ofChars h (ι := Fin 1) (fun _ => ξ) fun _ => hξ).ρ σ = ((ξ σ : ℂˣ) : ℂ) • 1 := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp
  rw [this]; simp

theorem under_self (u : HeightOneSpectrum (𝓞 L)) : u.under (𝓞 L) = u := by
  ext x
  simp [HeightOneSpectrum.under, Ideal.under, Ideal.mem_comap]

theorem smooth_localChar (h : IsPlaceOver A w) (χ : G L Ω →* ℂˣ) (op : IsOpen (χ.ker : Set (G L Ω))) :
    IsSmoothChar (localChar (hk χ) w) := by
  obtain ⟨a, ha⟩ := GlobalTheory.localArtinExists_holds L Ω A w h
  obtain ⟨η, hη, e⟩ := ha.factor (χ.comp (Weil h).subtype) (op.preimage continuous_subtype_val)
  have : localChar (hk χ) w = η := MonoidHom.ext fun x => by
    obtain ⟨σ, rfl⟩ := ha.surj x
    exact ((hk_spec χ op).1 A w h a ha σ).trans (DFunLike.congr_fun e σ)
  exact this ▸ hη

theorem fcorr_self (h : IsPlaceOver A w) : FCorr L w (LocExt.self h) 1 (RingEquiv.refl _) where
  cont := continuous_id
  psi := fun _ => rfl
  fix := fun σ => ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨(σ : G L Ω), rfl⟩⟩
  art := fun χ X hX a ha (σ : Weil h) τ x e hx => by
    have e1 : τ = (σ : G L Ω) := resG_injective L (by rw [inv_one, one_mul, mul_one] at e; exact e)
    have e2 : x = a σ := Units.ext (congrArg Units.val hx)
    rw [e1, e2]
    exact hX A w h a ha σ

def selfTerm (h : IsPlaceOver A w) (χ : G L Ω →* ℂˣ) (op : IsOpen (χ.ker : Set (G L Ω))) (n : ℤ)
    (u : HeightOneSpectrum (𝓞 L)) (e : u = w) : BTerm h (localAdelicChar L w) where
  E := { L := L, v' := u, h' := e ▸ h, loc := isLocalExt_self h }
  ψ' := localAdelicChar L u
  cont := GroundTheory.Global.continuous_localAdelicChar u
  tr := fun z => by
    subst e
    show localAdelicChar L u (algebraMap L _ z) = localAdelicChar L u (algebraMap L _ (Algebra.trace L L z))
    simp
  a := (GlobalTheory.localArtinExists_holds L Ω A u (e ▸ h)).choose
  ha := (GlobalTheory.localArtinExists_holds L Ω A u (e ▸ h)).choose_spec
  χ := localChar (hk χ) u
  hχ := smooth_localChar (e ▸ h) χ op
  n := n

theorem realises_self (h : IsPlaceOver A w) (χ : G L Ω →* ℂˣ) (op : IsOpen (χ.ker : Set (G L Ω))) (n : ℤ) :
    Realises (GTerm.self χ op n) (fun u => selfTerm h χ op n u.1 ((under_self u.1).symm.trans u.2)) (fun _ => 1)
      (fun _ => RingEquiv.refl _) := by
  have hs : Subsingleton ((GTerm.self χ op n).Over w) := ⟨fun u u' => Subtype.ext
    (((under_self u.1).symm.trans u.2).trans ((under_self u'.1).symm.trans u'.2).symm)⟩
  let _ : Unique ((GTerm.self χ op n).Over w) := { default := ⟨w, under_self w⟩, uniq := fun _ => hs.elim _ _ }
  refine ⟨fun ⟨u, hu⟩ => ?_, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun σ => ?_, fun σ => ?_⟩
  · obtain rfl : u = w := (under_self u).symm.trans hu
    exact fcorr_self h
  · rw [finsum_unique]
    refine (gInd_self χ σ).trans (Eq.symm ?_)
    refine (trW_indOf_self _ _ σ).trans ((trW_char h _ _ σ).trans ?_)
    exact congrArg Units.val ((hk_spec χ op).1 A w h _ (GlobalTheory.localArtinExists_holds L Ω A w h).choose_spec σ)
  · rw [finsum_unique]
    refine (gInd_self (1 : G L Ω →* ℂˣ) (σ : G L Ω)).trans (Eq.symm ?_)
    exact (trW_indOf_self (1 : Weil h →* ℂˣ) (isSmooth_one h) σ).trans (trW_char h 1 (isSmooth_one h) σ)

end Self

section Rel

variable {k : Type} [Field k] [NumberField k] [Algebra k Ω] [IsAlgClosure k Ω]

omit [NumberField k] [IsAlgClosure k Ω] in

theorem GRel.gtw {gl : List (GTerm k Ω)} (H : GRel gl) (ξ : G k Ω →* ℂˣ) (hξ : IsOpen (ξ.ker : Set (G k Ω))) :
    GRel (gtw gl ξ hξ) := fun σ => by
  have key : ∀ l : List (GTerm k Ω),
      ((GlobalTheory.DelGlob.gtw l ξ hξ).map fun t => (t.n : ℂ) * (gInd k t.χ σ - gInd k (1 : G t.L Ω →* ℂˣ) σ)).sum =
        ξ σ * (l.map fun t => (t.n : ℂ) * (gInd k t.χ σ - gInd k (1 : G t.L Ω →* ℂˣ) σ)).sum := fun l => by
    simp only [GlobalTheory.DelGlob.gtw, List.map_append, List.sum_append, List.map_map]
    induction l with
    | nil => simp
    | cons t l ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply]
      have e1 := gInd_twist k t.χ ξ σ
      have e2 := gInd_twist k (1 : G t.L Ω →* ℂˣ) ξ σ
      rw [one_mul] at e2
      have e3 : ((t.twist ξ hξ).n : ℂ) * (gInd k (t.twist ξ hξ).χ σ - gInd k (1 : G (t.twist ξ hξ).L Ω →* ℂˣ) σ) =
          t.n * (ξ σ * gInd k t.χ σ - gInd k (1 : G t.L Ω →* ℂˣ) σ) := by rw [← e1]; rfl
      have e4 : ((t.cotwist ξ hξ).n : ℂ) * (gInd k (t.cotwist ξ hξ).χ σ - gInd k (1 : G (t.cotwist ξ hξ).L Ω →* ℂˣ) σ) =
          (-t.n : ℤ) * (ξ σ * gInd k (1 : G t.L Ω →* ℂˣ) σ - gInd k (1 : G t.L Ω →* ℂˣ) σ) := by rw [← e2]; rfl
      rw [e3, e4]
      push_cast
      linear_combination ih
  rw [key, H σ, mul_zero]

theorem gRel_self_iff (χ : G k Ω →* ℂˣ) (op : IsOpen (χ.ker : Set (G k Ω))) : GRel [GTerm.self χ op 1] ↔ χ = 1 := by
  refine ⟨fun H => MonoidHom.ext fun σ => Units.ext ?_, ?_⟩
  · have := H σ
    simp only [GTerm.self, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, gInd_self] at this
    simpa [sub_eq_zero] using this
  · rintro rfl σ
    simp [GTerm.self]

theorem fcorr_locExt {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 k)} {h : IsPlaceOver A w} (E : LocExt h) :
    FCorr E.L E.v' E 1 (RingEquiv.refl _) where
  cont := continuous_id
  psi := fun _ => rfl
  fix := fun σ => by rw [inv_one, one_mul, mul_one]; rfl
  art := fun χ X hX a ha σ τ x e hx => by
    have e1 : τ = (σ : G E.L Ω) := resG_injective k (by rw [inv_one, one_mul, mul_one] at e; exact e)
    have e2 : x = a σ := Units.ext (congrArg Units.val hx)
    rw [e1, e2]
    exact hX A E.v' E.h' a ha σ

theorem exists_gterm_proper {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 k)} (h : IsPlaceOver A v) (d : ℕ)
    (hd : 0 < d) (n : ℤ) : ∃ t : GTerm k Ω, Module.finrank k t.L = d ∧ t.χ ≠ 1 ∧ t.n = n := by
  obtain ⟨E, hE⟩ := exists_locExt_finrank_eq h d hd
  obtain ⟨F, hF⟩ := exists_locExt_finrank_eq E.h' 2 two_pos
  let M : IntermediateField E.L Ω := (IsScalarTower.toAlgHom E.L F.L Ω).fieldRange
  have hM : Module.finrank E.L M = 2 :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom E.L F.L Ω)).toLinearEquiv.finrank_eq.symm.trans hF
  have : FiniteDimensional E.L M := Module.finite_of_finrank_pos (by omega)
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E.L
  have : IsGalois E.L Ω := {}
  have hi : M.fixingSubgroup.index = 2 := (IntermediateField.finrank_eq_fixingSubgroup_index Ω M).symm.trans hM
  have ho : IsOpen (M.fixingSubgroup : Set (G E.L Ω)) := M.fixingSubgroup_isOpen
  generalize M.fixingSubgroup = H at hi ho
  classical
  let χ : G E.L Ω →* ℂˣ := MonoidHom.mk' (fun σ => if σ ∈ H then 1 else -1) fun σ τ => by
    have := Subgroup.mul_mem_iff_of_index_two hi (a := σ) (b := τ)
    by_cases h1 : σ ∈ H <;> by_cases h2 : τ ∈ H <;> simp_all
  have hker : H ≤ χ.ker := fun σ hσ => by simp [χ, MonoidHom.mem_ker, hσ]
  refine ⟨{ L := E.L, χ := χ, op := Subgroup.isOpen_mono hker ho, n := n }, hE, fun h1 => ?_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ, σ ∉ H := by
    by_contra! H'
    rw [(Subgroup.eq_top_iff' _).2 H', Subgroup.index_top] at hi
    omega
  have h2 : χ σ = 1 := DFunLike.congr_fun h1 σ
  simp [χ, hσ] at h2

theorem exists_realises_ne_one {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 k)} (h : IsPlaceOver A v) (n : ℤ) :
    ∃ (t : GTerm k Ω) (w : HeightOneSpectrum (𝓞 t.L)) (B : ValuationSubring Ω) (h' : IsPlaceOver B w), t.χ ≠ 1 ∧
      ∃ b g i, Realises (h := h') (GTerm.self t.χ t.op n) b g i := by
  obtain ⟨t, -, ht, -⟩ := exists_gterm_proper h 1 one_pos n
  obtain ⟨w⟩ : Nonempty (HeightOneSpectrum (𝓞 t.L)) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 t.L)
    exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField _)⟩⟩
  obtain ⟨B, h'⟩ := exists_isPlaceOver Ω w
  exact ⟨t, w, B, h', ht, _, _, _, realises_self h' t.χ t.op n⟩

end Rel

end Inh

end GlobalTheory.DelGlob

end
