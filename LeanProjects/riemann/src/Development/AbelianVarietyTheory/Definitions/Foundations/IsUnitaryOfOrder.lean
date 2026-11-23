import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
import Development.AbelianVarietyTheory.Definitions.Foundations.ValuedAlgebraMapEqOne

noncomputable section
section

open NumberField IsDedekindDomain nonZeroDivisors

namespace GlobalTheory.Mem.Chr

variable (L : Type) [Field L] [NumberField L]

def hcharSub : Subgroup (Ideles L →* ℂˣ) where
  carrier := {χ | Continuous χ ∧ ∀ k : Lˣ, χ (diagUnits L k) = 1}
  one_mem' := ⟨continuous_const, fun _ => rfl⟩
  mul_mem' := fun {a b} ha hb => ⟨ha.1.mul hb.1, fun k => by
    rw [MonoidHom.mul_apply, ha.2 k, hb.2 k, one_mul]⟩
  inv_mem' := fun {a} ha => ⟨ha.1.inv, fun k => by rw [MonoidHom.inv_apply, ha.2 k, inv_one]⟩

abbrev HChar : Type := ↥(hcharSub L)

variable {L}

def atFin (v : HeightOneSpectrum (𝓞 L)) : Lˣ →* (v.adicCompletion L)ˣ :=
  Units.map (algebraMap L (v.adicCompletion L)).toMonoidHom

def atInf (w : InfinitePlace L) : Lˣ →* (w.Completion)ˣ :=
  Units.map (algebraMap L w.Completion).toMonoidHom

def IsUnitAt (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) : Prop :=
  Valued.v (x : v.adicCompletion L) = 1

def IsUnifAt (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) : Prop :=
  Valued.v (x : v.adicCompletion L) = WithZero.exp (-1 : ℤ)

def ordF (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : ℤ := -WithZero.log (v.valuation L (k : L))

def infDiag : Lˣ →* Ideles L := ∏ w : InfinitePlace L, (infIdele L w).comp (atInf w)

theorem exists_unif (v : HeightOneSpectrum (𝓞 L)) : ∃ k : Lˣ, IsUnifAt v (atFin v k) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer L
  have h0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  refine ⟨Units.mk0 π h0, ?_⟩
  show Valued.v ((π : L) : v.adicCompletion L) = _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]

def unif (v : HeightOneSpectrum (𝓞 L)) : Lˣ := Classical.choose (exists_unif v)

theorem unif_spec (v : HeightOneSpectrum (𝓞 L)) : IsUnifAt v (atFin v (unif v)) :=
  Classical.choose_spec (exists_unif v)

namespace HChar

variable (χ : HChar L)

def loc (v : HeightOneSpectrum (𝓞 L)) : (v.adicCompletion L)ˣ →* ℂˣ := χ.1.comp (localIdele L v)

def locInf (w : InfinitePlace L) : (w.Completion)ˣ →* ℂˣ := χ.1.comp (infIdele L w)

def locK (v : HeightOneSpectrum (𝓞 L)) : Lˣ →* ℂˣ := (χ.loc v).comp (atFin v)

def inf : Lˣ →* ℂˣ := χ.1.comp infDiag

def LevelLe (v : HeightOneSpectrum (𝓞 L)) (n : ℕ) : Prop :=
  ∀ x : (v.adicCompletion L)ˣ, IsUnitAt v x →
    Valued.v ((x : v.adicCompletion L) - 1) ≤ WithZero.exp (-(n : ℤ)) → χ.loc v x = 1

def UnrAt (v : HeightOneSpectrum (𝓞 L)) : Prop := ∀ x : (v.adicCompletion L)ˣ, IsUnitAt v x → χ.loc v x = 1

def TameAt (v : HeightOneSpectrum (𝓞 L)) : Prop := χ.LevelLe v 1

def IsCond (𝔣 : Ideal (𝓞 L)) : Prop :=
  𝔣 ≠ ⊥ ∧ ∀ (v : HeightOneSpectrum (𝓞 L)) (n : ℕ), χ.LevelLe v n ↔ ¬ v.asIdeal ^ (n + 1) ∣ 𝔣

def val (v : HeightOneSpectrum (𝓞 L)) : ℂˣ := χ.locK v (unif v)

def onId (I : FractionalIdeal (𝓞 L)⁰ L) : ℂˣ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 L), χ.val v ^ FractionalIdeal.count L v I

def valTw (s : ℝ) (v : HeightOneSpectrum (𝓞 L)) : ℂ :=
  (χ.val v : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s : ℂ))

def IsUnitary : Prop := ∀ x : Ideles L, ‖((χ.1 x : ℂˣ) : ℂ)‖ = 1

def OrderDvd (n : ℕ) : Prop := χ ^ n = 1

def HasInf {I : Type} [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ) : Prop :=
  ∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ i, (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i

def HasInfQ {I : Type} [Fintype I] (φ : I → L →+* ℂ) (a : I → ℚ) : Prop :=
  ∃ n : I → ℤ, (∀ i, (n i : ℚ) = 2 * a i) ∧ χ.HasInf φ n

def IsAlg (n : (L →+* ℂ) → ℤ) : Prop :=
  ∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ φ : L →+* ℂ, φ (k : L) ^ n φ

def IsAbsPow (s : ℝ) : Prop :=
  (∀ v, χ.UnrAt v) ∧ (∀ v, ((χ.val v : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s : ℂ))) ∧
    ∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ φ : L →+* ℂ, ((‖φ (k : L)‖ : ℝ) : ℂ) ^ (s : ℂ)

def IsUnitaryNormOf (χ' : HChar L) (s : ℝ) : Prop :=
  χ.IsUnitary ∧ ∃ ν : HChar L, ν.IsAbsPow s ∧ χ' = χ * ν

def ValuesIn (s : ℝ) {C : Type} [Field C] (e : C →+* ℂ) : Prop :=
  ∀ v, χ.UnrAt v → ∃ y : C, e y = χ.valTw s v

def ProductRule : Prop :=
  ∀ S : Finset (HeightOneSpectrum (𝓞 L)), (∀ v, v ∉ S → χ.UnrAt v) → ∀ k : Lˣ,
    χ.inf k * (∏ v ∈ S, χ.locK v k) * (∏ᶠ (v : HeightOneSpectrum (𝓞 L)) (_ : v ∉ S), χ.val v ^ ordF v k) = 1

theorem unrAt_iff (v : HeightOneSpectrum (𝓞 L)) : χ.UnrAt v ↔ χ.LevelLe v 0 := by
  constructor
  · intro h x hx _; exact h x hx
  · intro h x hx
    refine h x hx ?_
    have h1 : Valued.v ((x : v.adicCompletion L) - 1) ≤ max (Valued.v (x : v.adicCompletion L)) (Valued.v (1 : v.adicCompletion L)) :=
      Valuation.map_sub _ _ _
    rw [hx, map_one, max_self] at h1
    simpa using h1

theorem val_eq {v : HeightOneSpectrum (𝓞 L)} (h : χ.UnrAt v) (x : (v.adicCompletion L)ˣ) (hx : IsUnifAt v x) :
    χ.loc v x = χ.val v := by
  have hu : IsUnitAt v (x * (atFin v (unif v))⁻¹) := by
    have h2 := unif_spec v
    unfold IsUnitAt IsUnifAt at *
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hx, h2]
    exact mul_inv_cancel₀ (by simp)
  have h3 := h _ hu
  rw [map_mul, map_inv, mul_inv_eq_one] at h3
  exact h3

@[simp] theorem loc_mul (χ χ' : HChar L) (v : HeightOneSpectrum (𝓞 L)) (x) : (χ * χ').loc v x = χ.loc v x * χ'.loc v x := rfl
@[simp] theorem loc_inv (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) (x) : (χ⁻¹).loc v x = (χ.loc v x)⁻¹ := rfl
@[simp] theorem loc_one (v : HeightOneSpectrum (𝓞 L)) (x) : (1 : HChar L).loc v x = 1 := rfl
@[simp] theorem locInf_mul (χ χ' : HChar L) (w : InfinitePlace L) (x) : (χ * χ').locInf w x = χ.locInf w x * χ'.locInf w x := rfl
@[simp] theorem locInf_inv (χ : HChar L) (w : InfinitePlace L) (x) : (χ⁻¹).locInf w x = (χ.locInf w x)⁻¹ := rfl
@[simp] theorem val_mul (χ χ' : HChar L) (v : HeightOneSpectrum (𝓞 L)) : (χ * χ').val v = χ.val v * χ'.val v := rfl
@[simp] theorem val_inv (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) : (χ⁻¹).val v = (χ.val v)⁻¹ := rfl
@[simp] theorem inf_mul (χ χ' : HChar L) (k : Lˣ) : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
@[simp] theorem inf_inv (χ : HChar L) (k : Lˣ) : (χ⁻¹).inf k = (χ.inf k)⁻¹ := rfl

def bar : HChar L :=
  ⟨(Units.map (starRingEnd ℂ).toMonoidHom).comp χ.1,
    (Continuous.units_map _ Complex.continuous_conj).comp χ.2.1, fun k => by
      rw [MonoidHom.comp_apply, χ.2.2 k, map_one]⟩

end HChar

abbrev AlgHChar (L : Type) [Field L] [NumberField L] : Type := {χ : HChar L // ∃ n, χ.IsAlg n}

section Res

variable (F : Type) [Field F] [NumberField F] [Algebra F L]

theorem finite_aboveF (v : HeightOneSpectrum (𝓞 F)) :
    {P : HeightOneSpectrum (𝓞 L) | P.under (𝓞 F) = v}.Finite := by
  have hfin := IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)
  refine (hfin.preimage (f := HeightOneSpectrum.asIdeal)
    (fun _ _ _ _ h => HeightOneSpectrum.ext h)).subset ?_
  rintro P rfl
  exact ⟨P.isPrime, ⟨rfl⟩⟩

def aboveF (v : HeightOneSpectrum (𝓞 F)) : Finset (HeightOneSpectrum (𝓞 L)) := (finite_aboveF F v).toFinset

open Classical in

def aboveInf (w : InfinitePlace F) : Finset (InfinitePlace L) :=
  Finset.univ.filter fun w' => w'.comap (algebraMap F L) = w

def upF : Fˣ →* Lˣ := Units.map (algebraMap F L).toMonoidHom

variable {F}

def HChar.resFin (χ : HChar L) (v : HeightOneSpectrum (𝓞 F)) : Fˣ →* ℂˣ :=
  ∏ P ∈ aboveF (L := L) F v, (χ.locK P).comp (upF F)

def HChar.resInf (χ : HChar L) (w : InfinitePlace F) : Fˣ →* ℂˣ :=
  ∏ w' ∈ aboveInf (L := L) F w, ((χ.locInf w').comp (atInf w')).comp (upF F)

variable (F)

def HChar.TrivOn (χ : HChar L) : Prop :=
  (∀ (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ), χ.resFin v k = 1) ∧ ∀ (w : InfinitePlace F) (k : Fˣ), χ.resInf w k = 1

def etaFin (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : ℂˣ :=
  if (aboveF (L := L) F v).card = 1 then (-1) ^ ordF v k else 1

def etaInf (w : InfinitePlace F) (k : Fˣ) : ℂˣ := if (w.embedding (k : F)).re < 0 then -1 else 1

def HChar.ResEta (χ : HChar L) : Prop :=
  (∀ (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ), χ.resFin v k = etaFin (L := L) F v k) ∧
    ∀ (w : InfinitePlace F) (k : Fˣ), χ.resInf w k = etaInf F w k

end Res

end GlobalTheory.Mem.Chr

end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Chr

open Formalism.BasicNotions Formalism.FrobeniusOrbits

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def OverP (p : ℕ) (v : HeightOneSpectrum (𝓞 H.E)) : Prop := ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal

instance psiFintype (φ : Formalism.HC.Frame) : Fintype φ.Psi := Fintype.ofFinite _

def embPsi (g : R.Psi) : H.E →+* ℂ := H.emb (g : R.GG)

structure IsClsF (ξ : HChar H.E) : Prop where
  unitary : ξ.IsUnitary
  unr : ∀ v, ξ.UnrAt v
  inf : ∀ k, ξ.inf k = 1
  triv : ξ.TrivOn H.F

structure IsEtaT (χ : HChar H.E) : Prop where
  unitary : χ.IsUnitary
  unr : ∀ v, χ.UnrAt v
  res : χ.ResEta H.F
  inf : χ.HasInf (embPsi H) (fun _ => 1)

def etaAlg (χ : HChar H.E) (v : HeightOneSpectrum (𝓞 H.E)) : ℂ := χ.valTw (1 / 2) v

def IsEtaAlg (χa : HChar H.E) : Prop := ∃ χ : HChar H.E, IsEtaT H χ ∧ χ.IsUnitaryNormOf χa (1 / 2)

def EtaTExists : Prop := ∃ χ : HChar H.E, IsEtaT H χ

structure IsChiPsi (χ : HChar H.E) : Prop where
  unitary : χ.IsUnitary
  unr : ∀ v, χ.UnrAt v
  triv : χ.TrivOn H.F
  inf : χ.HasInf (embPsi H) (fun _ => 2)

structure PiBar where
  pb : Fin 2 → HeightOneSpectrum (𝓞 H.K)
  pb_over : ∀ k, ((H.g k : ℕ) : 𝓞 H.K) ∈ (pb k).asIdeal

def PiBar.Div {H : Formalism.BasicNotions.Host R} (P : PiBar H) (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)) : Prop :=
  w.under (𝓞 H.K) = P.pb k

structure Omg where
  om : ∀ k : Fin 2, (ZMod (H.g k))ˣ →* ℂˣ
  gen : ∀ k, Function.Injective (om k)

variable {H}

structure IsMu0 (P : PiBar H) (W : Omg H) (e : R.Psi → ℚ) (j : ℕ) (χ : HChar H.E) : Prop where
  unitary : χ.IsUnitary
  triv : χ.TrivOn H.F
  inf : χ.HasInfQ (embPsi H) (fun τ => -e τ)
  unr : ∀ v, (∀ k, ¬ OverP H (H.g k) v) → χ.UnrAt v
  tame : ∀ v, χ.TameAt v
  atg : ∀ (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)), P.Div k w → ∀ (a : ℕ) (ha : a.Coprime (H.g k)) (x : H.Eˣ),
    (x : H.E) = (a : H.E) → χ.locK w x = (W.om k (ZMod.unitOfCoprime a ha) ^ (2 * (j + 1)))⁻¹

def Mu0Exists (P : PiBar H) (W : Omg H) (e : R.Psi → ℚ) (j : ℕ) : Prop := ∃ χ : HChar H.E, IsMu0 P W e j χ

structure IsDelta (p : ℕ) (χ : HChar H.E) : Prop where
  fin : ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n
  triv : χ.TrivOn H.F
  tame : ∀ v, χ.TameAt v
  unr : ∀ v, ¬ OverP H p v → χ.UnrAt v
  ine : ∀ v, OverP H p v → ∀ n : ℕ, (∀ x, IsUnitAt v x → χ.loc v x ^ n = 1) ↔ 15 ∣ n

def DeltaExists (p : ℕ) : Prop := ∃ χ : HChar H.E, IsDelta (H := H) p χ

structure IsPsi (l : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 H.E))) (χ : HChar H.E) : Prop where
  ord : ∃ a : ℕ, χ.OrderDvd (l ^ a)
  triv : χ.TrivOn H.F
  tame : ∀ v, χ.TameAt v
  ram : ∀ v, χ.UnrAt v ↔ v ∉ Q
  atl : ∀ v, OverP H l v → ∀ x, χ.loc v x = 1
  split : ∀ v ∈ Q, IsSplitPl H v

def SplitsCompletely (Q : Finset (HeightOneSpectrum (𝓞 H.E))) : Prop :=
  ∀ v ∈ Q, ∀ p : ℕ, p.Prime → OverP H p v → ∀ v' : HeightOneSpectrum (𝓞 H.E), OverP H p v' →
    Ideal.absNorm v'.asIdeal = p ∧ ((p : ℕ) : 𝓞 H.E) ∉ v'.asIdeal ^ 2

end GlobalTheory.Mem.Chr

end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Chr

open Formalism.BasicNotions Formalism.FrobeniusOrbits

section General

variable {L : Type} [Field L] [NumberField L] {F : Type} [Field F] [NumberField F] [Algebra F L]

namespace HChar

theorem resFin_apply (χ : HChar L) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    χ.resFin v k = ∏ P ∈ aboveF (L := L) F v, χ.locK P (upF F k) := by
  simp [HChar.resFin]

theorem resInf_apply (χ : HChar L) (w : InfinitePlace F) (k : Fˣ) :
    χ.resInf w k = ∏ w' ∈ aboveInf (L := L) F w, χ.locInf w' (atInf w' (upF F k)) := by
  simp [HChar.resInf]

theorem resFin_mul (χ χ' : HChar L) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    (χ * χ').resFin v k = χ.resFin v k * χ'.resFin v k := by
  rw [resFin_apply, resFin_apply, resFin_apply, ← Finset.prod_mul_distrib]; rfl

theorem resFin_inv (χ : HChar L) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    (χ⁻¹).resFin v k = (χ.resFin v k)⁻¹ := by
  rw [resFin_apply, resFin_apply, ← Finset.prod_inv_distrib]; rfl

theorem resInf_mul (χ χ' : HChar L) (w : InfinitePlace F) (k : Fˣ) :
    (χ * χ').resInf w k = χ.resInf w k * χ'.resInf w k := by
  rw [resInf_apply, resInf_apply, resInf_apply, ← Finset.prod_mul_distrib]; rfl

theorem resInf_inv (χ : HChar L) (w : InfinitePlace F) (k : Fˣ) :
    (χ⁻¹).resInf w k = (χ.resInf w k)⁻¹ := by
  rw [resInf_apply, resInf_apply, ← Finset.prod_inv_distrib]; rfl

theorem TrivOn.mul {χ χ' : HChar L} (h : χ.TrivOn F) (h' : χ'.TrivOn F) : (χ * χ').TrivOn F :=
  ⟨fun v k => by rw [resFin_mul, h.1, h'.1, one_mul], fun w k => by rw [resInf_mul, h.2, h'.2, one_mul]⟩

theorem TrivOn.inv {χ : HChar L} (h : χ.TrivOn F) : (χ⁻¹).TrivOn F :=
  ⟨fun v k => by rw [resFin_inv, h.1, inv_one], fun w k => by rw [resInf_inv, h.2, inv_one]⟩

theorem ResEta.mul {χ ξ : HChar L} (h : χ.ResEta F) (h' : ξ.TrivOn F) : (χ * ξ).ResEta F :=
  ⟨fun v k => by rw [resFin_mul, h.1, h'.1, mul_one], fun w k => by rw [resInf_mul, h.2, h'.2, mul_one]⟩

theorem ResEta.div {χ χ' : HChar L} (h : χ.ResEta F) (h' : χ'.ResEta F) : (χ' * χ⁻¹).TrivOn F :=
  ⟨fun v k => by rw [resFin_mul, resFin_inv, h.1, h'.1, mul_inv_cancel],
    fun w k => by rw [resInf_mul, resInf_inv, h.2, h'.2, mul_inv_cancel]⟩

theorem LevelLe.mul {χ χ' : HChar L} {v : HeightOneSpectrum (𝓞 L)} {n : ℕ} (h : χ.LevelLe v n) (h' : χ'.LevelLe v n) :
    (χ * χ').LevelLe v n := fun x hx hx' => by rw [loc_mul, h x hx hx', h' x hx hx', one_mul]

theorem LevelLe.inv {χ : HChar L} {v : HeightOneSpectrum (𝓞 L)} {n : ℕ} (h : χ.LevelLe v n) :
    (χ⁻¹).LevelLe v n := fun x hx hx' => by rw [loc_inv, h x hx hx', inv_one]

theorem UnrAt.mul {χ χ' : HChar L} {v : HeightOneSpectrum (𝓞 L)} (h : χ.UnrAt v) (h' : χ'.UnrAt v) :
    (χ * χ').UnrAt v := fun x hx => by rw [loc_mul, h x hx, h' x hx, one_mul]

theorem UnrAt.inv {χ : HChar L} {v : HeightOneSpectrum (𝓞 L)} (h : χ.UnrAt v) :
    (χ⁻¹).UnrAt v := fun x hx => by rw [loc_inv, h x hx, inv_one]

theorem UnrAt.levelLe {χ : HChar L} {v : HeightOneSpectrum (𝓞 L)} (h : χ.UnrAt v) (n : ℕ) : χ.LevelLe v n :=
  fun x hx _ => h x hx

theorem IsUnitary.mul {χ χ' : HChar L} (h : χ.IsUnitary) (h' : χ'.IsUnitary) : (χ * χ').IsUnitary := fun x => by
  show ‖((χ.1 x * χ'.1 x : ℂˣ) : ℂ)‖ = 1
  rw [Units.val_mul, norm_mul, h x, h' x, one_mul]

theorem IsUnitary.inv {χ : HChar L} (h : χ.IsUnitary) : (χ⁻¹).IsUnitary := fun x => by
  show ‖(((χ.1 x)⁻¹ : ℂˣ) : ℂ)‖ = 1
  rw [Units.val_inv_eq_inv_val, norm_inv, h x, inv_one]

theorem HasInf.mul_triv {I : Type} [Fintype I] {φ : I → L →+* ℂ} {n : I → ℤ} {χ ξ : HChar L}
    (h : χ.HasInf φ n) (h' : ∀ k, ξ.inf k = 1) : (χ * ξ).HasInf φ n := fun k => by
  rw [inf_mul, h' k, mul_one]; exact h k

theorem HasInf.div {I : Type} [Fintype I] {φ : I → L →+* ℂ} {n : I → ℤ} {χ χ' : HChar L}
    (h : χ.HasInf φ n) (h' : χ'.HasInf φ n) (k : Lˣ) : (χ' * χ⁻¹).inf k = 1 := by
  rw [inf_mul, inf_inv, mul_inv_eq_one]
  exact Units.ext ((h' k).trans (h k).symm)

theorem HasInfQ.mul_triv {I : Type} [Fintype I] {φ : I → L →+* ℂ} {a : I → ℚ} {χ ξ : HChar L}
    (h : χ.HasInfQ φ a) (h' : ∀ k, ξ.inf k = 1) : (χ * ξ).HasInfQ φ a := by
  obtain ⟨n, hn, h⟩ := h
  exact ⟨n, hn, h.mul_triv h'⟩

theorem HasInfQ.div {I : Type} [Fintype I] {φ : I → L →+* ℂ} {a : I → ℚ} {χ χ' : HChar L}
    (h : χ.HasInfQ φ a) (h' : χ'.HasInfQ φ a) (k : Lˣ) : (χ' * χ⁻¹).inf k = 1 := by
  obtain ⟨n, hn, h⟩ := h
  obtain ⟨n', hn', h'⟩ := h'
  have e : n' = n := funext fun i => by exact_mod_cast (hn' i).trans (hn i).symm
  subst e
  exact h.div h' k

end HChar

end General

variable {R : Ranks} {H : Formalism.BasicNotions.Host R}

theorem isClsF_one : IsClsF H (1 : HChar H.E) :=
  ⟨fun _ => by show ‖((1 : ℂˣ) : ℂ)‖ = 1; simp, fun _ _ _ => rfl, fun _ => rfl,
    fun v k => by rw [HChar.resFin_apply]; exact Finset.prod_eq_one fun _ _ => rfl,
    fun w k => by rw [HChar.resInf_apply]; exact Finset.prod_eq_one fun _ _ => rfl⟩

theorem IsEtaT.mul_cls {χ ξ : HChar H.E} (h : IsEtaT H χ) (hξ : IsClsF H ξ) : IsEtaT H (χ * ξ) :=
  ⟨h.unitary.mul hξ.unitary, fun v => (h.unr v).mul (hξ.unr v), h.res.mul hξ.triv, h.inf.mul_triv hξ.inf⟩

theorem IsEtaT.div_cls {χ χ' : HChar H.E} (h : IsEtaT H χ) (h' : IsEtaT H χ') : IsClsF H (χ' * χ⁻¹) :=
  ⟨h'.unitary.mul h.unitary.inv, fun v => (h'.unr v).mul (h.unr v).inv, h.inf.div h'.inf, h.res.div h'.res⟩

theorem IsChiPsi.mul_cls {χ ξ : HChar H.E} (h : IsChiPsi H χ) (hξ : IsClsF H ξ) : IsChiPsi H (χ * ξ) :=
  ⟨h.unitary.mul hξ.unitary, fun v => (h.unr v).mul (hξ.unr v), h.triv.mul hξ.triv, h.inf.mul_triv hξ.inf⟩

theorem IsChiPsi.div_cls {χ χ' : HChar H.E} (h : IsChiPsi H χ) (h' : IsChiPsi H χ') : IsClsF H (χ' * χ⁻¹) :=
  ⟨h'.unitary.mul h.unitary.inv, fun v => (h'.unr v).mul (h.unr v).inv, h.inf.div h'.inf, h'.triv.mul h.triv.inv⟩

theorem IsEtaT.sq_chiPsi {χ : HChar H.E} (h : IsEtaT H χ) : IsChiPsi H (χ * χ) where
  unitary := h.unitary.mul h.unitary
  unr v := (h.unr v).mul (h.unr v)
  triv := by
    refine ⟨fun v k => ?_, fun w k => ?_⟩
    · rw [HChar.resFin_mul, h.res.1]
      unfold etaFin
      split_ifs
      · rw [← mul_zpow]; simp
      · simp
    · rw [HChar.resInf_mul, h.res.2]
      unfold etaInf
      split_ifs <;> simp
  inf k := by
    rw [HChar.inf_mul, Units.val_mul, h.inf k, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun g _ => ?_
    rw [← zpow_add' (by right; left; norm_num)]
    norm_num

theorem PiBar.overP (P : PiBar H) {k : Fin 2} {w : HeightOneSpectrum (𝓞 H.E)} (hw : P.Div k w) : OverP H (H.g k) w := by
  have h := P.pb_over k
  rw [← hw] at h
  have h2 : algebraMap (𝓞 H.K) (𝓞 H.E) ((H.g k : ℕ) : 𝓞 H.K) ∈ w.asIdeal := h
  rwa [map_natCast] at h2

theorem isUnitAt_nat {p a : ℕ} {w : HeightOneSpectrum (𝓞 H.E)} (hw : OverP H p w) (ha : a.Coprime p) {x : H.Eˣ}
    (hx : (x : H.E) = (a : H.E)) : IsUnitAt w (atFin w x) := by
  have hna : ((a : ℕ) : 𝓞 H.E) ∉ w.asIdeal := by
    intro hmem
    obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr ha)
    have h1 : (1 : 𝓞 H.E) ∈ w.asIdeal := by
      have e : (1 : 𝓞 H.E) = (u : 𝓞 H.E) * ((a : ℕ) : 𝓞 H.E) + (v : 𝓞 H.E) * ((p : ℕ) : 𝓞 H.E) := by
        have := congrArg (fun z : ℤ => (z : 𝓞 H.E)) huv
        push_cast at this
        exact this.symm
      rw [e]
      exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hmem) (w.asIdeal.mul_mem_left _ hw)
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have h := valued_algebraMap_eq_one H.E w _ hna
  show Valued.v (algebraMap H.E (w.adicCompletion H.E) (x : H.E)) = 1
  rw [hx]
  simpa using h

theorem IsMu0.mul_cls {P : PiBar H} {W : Omg H} {e : R.Psi → ℚ} {j : ℕ} {χ ξ : HChar H.E}
    (h : IsMu0 P W e j χ) (hξ : IsClsF H ξ) : IsMu0 P W e j (χ * ξ) where
  unitary := h.unitary.mul hξ.unitary
  triv := h.triv.mul hξ.triv
  inf := h.inf.mul_triv hξ.inf
  unr v hv := (h.unr v hv).mul (hξ.unr v)
  tame v := (h.tame v).mul ((hξ.unr v).levelLe 1)
  atg k w hw a ha x hx := by
    have h1 : ξ.locK w x = 1 := hξ.unr w _ (isUnitAt_nat (P.overP hw) ha hx)
    show χ.locK w x * ξ.locK w x = _
    rw [h1, mul_one, h.atg k w hw a ha x hx]

theorem IsMu0.div_cls {P : PiBar H} {W : Omg H} {e : R.Psi → ℚ} {j : ℕ} {χ χ' : HChar H.E}
    (h : IsMu0 P W e j χ) (h' : IsMu0 P W e j χ')
    (hg : ∀ k v, OverP H (H.g k) v → (χ' * χ⁻¹).UnrAt v) : IsClsF H (χ' * χ⁻¹) where
  unitary := h'.unitary.mul h.unitary.inv
  unr v := by
    by_cases hv : ∀ k, ¬ OverP H (H.g k) v
    · exact (h'.unr v hv).mul (h.unr v hv).inv
    · push Not at hv
      obtain ⟨k, hk⟩ := hv
      exact hg k v hk
  inf := h.inf.div h'.inf
  triv := h'.triv.mul h.triv.inv

def Mu0Unique (P : PiBar H) (W : Omg H) (e : R.Psi → ℚ) (j : ℕ) : Prop :=
  (∀ k, {v : HeightOneSpectrum (𝓞 H.E) | OverP H (H.g k) v}.ncard = Module.finrank ℚ H.E) →
    ∀ χ χ' : HChar H.E, IsMu0 P W e j χ → IsMu0 P W e j χ' → IsClsF H (χ' * χ⁻¹)

theorem isPsi_one (l : ℕ) : IsPsi (H := H) l ∅ (1 : HChar H.E) where
  ord := ⟨0, one_pow _⟩
  triv := isClsF_one.triv
  tame := fun _ _ _ _ => rfl
  ram := fun v => ⟨fun _ => Finset.notMem_empty v, fun _ _ _ => rfl⟩
  atl := fun _ _ _ => rfl
  split := fun _ hv => absurd hv (Finset.notMem_empty _)

theorem HChar.isUnitary_of_order {L : Type} [Field L] [NumberField L] {χ : HChar L} {n : ℕ} (hn : 0 < n) (h : χ.OrderDvd n) :
    χ.IsUnitary := fun x => by
  have h1 : (χ.1 x) ^ n = 1 := by
    have := congrArg (fun ξ : HChar L => ξ.1 x) h
    exact this
  have h2 : ‖((χ.1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1]; simp
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp h2

theorem IsDelta.unitary {p : ℕ} {χ : HChar H.E} (h : IsDelta (H := H) p χ) : χ.IsUnitary := by
  obtain ⟨n, hn, ho⟩ := h.fin
  exact HChar.isUnitary_of_order hn ho

end GlobalTheory.Mem.Chr

end
