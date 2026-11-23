import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapF
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PPrAdm

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

section Abstract

variable {A B : Type}

def prodSpan (U₁ : Submodule ℂ (A → ℂ)) (U₂ : Submodule ℂ (B → ℂ)) : Submodule ℂ (A × B → ℂ) :=
  Submodule.span ℂ {F | ∃ a ∈ U₁, ∃ b ∈ U₂, F = fun x => a x.1 * b x.2}

end Abstract

section Lin

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N r s : ℕ}

variable (E) in

abbrev KO (n : ℕ) : Subgroup (GL (Fin n) (Af E)) := GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n

def typeF (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) : Submodule ℂ (GA E N → ℂ) where
  carrier := {f | (∀ u ∈ K, ∀ g, f (g * finGL E N u) = f g) ∧
    ∀ g, (fun k : Kinf E N => f (g * infGL E N (Unitary.toUnits k))) ∈ W}
  add_mem' := fun {f f'} h h' => ⟨fun u hu g => by simp only [Pi.add_apply, h.1 u hu g, h'.1 u hu g],
    fun g => W.add_mem (h.2 g) (h'.2 g)⟩
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ => W.zero_mem⟩
  smul_mem' := fun c f h => ⟨fun u hu g => by simp only [Pi.smul_apply, h.1 u hu g],
    fun g => W.smul_mem c (h.2 g)⟩

def typed (U : Submodule ℂ (Sm E N)) (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) :
    Submodule ℂ (Sm E N) :=
  U ⊓ (typeF K W).comap (Sm E N).subtype

structure FlatFn (e : GA E N → ℂ) : Prop where
  ne : ∀ x, e x ≠ 0
  rinv : ∀ x (k : Kinf E N), ∀ c ∈ KO E N, e (x * cf N k c) = e x
  sm : e ∈ Sm E N

def Carries (e : GA E N → ℂ) (U U' : Submodule ℂ (Sm E N)) : Prop :=
  ∀ φ ∈ U, ∃ φ' ∈ U', ∀ x, φ'.1 x = e x * φ.1 x

def FinStable (U : Submodule ℂ (Sm E N)) : Prop := ∀ (g : GL (Fin N) (Af E)), ∀ φ ∈ U, act (.fin g) φ ∈ U

def indSpan (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) : Submodule ℂ (Sm E (r + s)) :=
  Submodule.span ℂ {φ | MemInd2 U₁ U₂ φ}

theorem exists_iw (x : GA E (r + s)) : ∃ (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s))
    (c : GL (Fin (r + s)) (Af E)), c ∈ KO E (r + s) ∧ x = unip u * lev (Ad E) r s m * cf (r + s) k c := by
  obtain ⟨b, hb, k, hy⟩ := GlobalTheory.IwasawaAdelic.exists_upper_mul_unitary_inf E (r + s)
    (GeneralLinearGroup.map (pInf E) x)
  have hb' : (((b⁻¹ : GL (Fin (r + s)) (Cinf E))) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)).BlockTriangular id := by
    letI : Invertible (b : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) := Units.invertible b
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  obtain ⟨xi, mi, hbi⟩ := IwaFin.exists_unip_mul_lev r s b
    (fun i j hi hj => hb (show j < i from Fin.lt_def.2 (lt_of_lt_of_le hj hi)))
    (fun i j hi hj => hb' (show j < i from Fin.lt_def.2 (lt_of_lt_of_le hj hi)))
  obtain ⟨xf, mf, c, hc, hf⟩ := IwaFin.exists_unip_lev_integral E r s (GeneralLinearGroup.map (pFin E) x)
  have e1 : ∀ p, pInf E (sInf E (xi p) + sFin E (xf p)) = xi p := fun p => by
    rw [map_add, show pInf E (sInf E (xi p)) = xi p from (infEq E).symm_apply_apply _,
      show pInf E (sFin E (xf p)) = 0 from map_zero (infEq E).symm, add_zero]
  have e2 : ∀ p, pFin E (sInf E (xi p) + sFin E (xf p)) = xf p := fun p => by
    rw [map_add, show pFin E (sInf E (xi p)) = 0 from rfl, show pFin E (sFin E (xf p)) = xf p from rfl, zero_add]
  refine ⟨fun p => sInf E (xi p) + sFin E (xf p),
    (infGL E r mi.1 * finGL E r mf.1, infGL E s mi.2 * finGL E s mf.2), k, c, hc, ga_ext ?_ ?_⟩
  · simp only [cf, map_mul, IwaAd.map_unip, IwaAd.map_lev, e1, pInf_infGL, pInf_finGL, mul_one, one_mul]
    rw [hy, hbi]
  · simp only [cf, map_mul, IwaAd.map_unip, IwaAd.map_lev, e2, pFin_infGL, pFin_finGL, mul_one, one_mul]
    rw [hf]

def leviOf (x : GA E (r + s)) : GA E r × GA E s := (exists_iw x).choose_spec.choose

def nodeFn (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ) (x : GA E (r + s)) : ℂ := e₁ (leviOf x).1 * e₂ (leviOf x).2

def absFn (N : ℕ) (w : ℂ) (x : GA E N) : ℂ := (chiDet N (GlobalTheory.CuspRep.Model.absC E w) x : ℂˣ)

end Lin

section Pair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def typeHF (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
    (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)) : Submodule ℂ (H E a b → ℂ) where
  carrier := {F | TypeH K₁ K₂ W₁ W₂ F}
  add_mem' := fun {F F'} h h' => ⟨fun u₁ hu₁ u₂ hu₂ x => by
      simp only [Pi.add_apply, h.1 u₁ hu₁ u₂ hu₂ x, h'.1 u₁ hu₁ u₂ hu₂ x],
    fun x => Submodule.add_mem _ (h.2 x) (h'.2 x)⟩
  zero_mem' := ⟨fun _ _ _ _ _ => rfl, fun _ => Submodule.zero_mem _⟩
  smul_mem' := fun c F h => ⟨fun u₁ hu₁ u₂ hu₂ x => by simp only [Pi.smul_apply, h.1 u₁ hu₁ u₂ hu₂ x],
    fun x => Submodule.smul_mem _ c (h.2 x)⟩

end Pair

end GlobalTheory.CompanionTheory.LimV

end
