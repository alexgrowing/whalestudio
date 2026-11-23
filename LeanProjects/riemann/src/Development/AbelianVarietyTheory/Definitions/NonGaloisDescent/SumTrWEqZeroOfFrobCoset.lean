import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonodromyFreeSumIrreducibles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilGroupIsSemisimpleOfSemisimpleFrob
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentTrace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSemisimple

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace GlobalTheory.VWeil

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem exists_pow_frob_comm (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ) :
    ∃ m : ℕ, 0 < m ∧ ∀ σ, Commute (ρ σ) (ρ (frob h) ^ m) := by
  classical
  have h1 : ∀ T : Set.range fun τ : Ine (F := E) A => ρ (ineIncl h τ),
      ∃ m : ℕ, 0 < m ∧ Commute T.1 (ρ (frob h) ^ m) := by
    rintro ⟨_, τ, rfl⟩
    obtain ⟨m, hm, hpow⟩ := exists_pow_eq_pow_of_deg_eq E Ω A w h V ρ hρ
      (ineIncl h τ * frob h * (ineIncl h τ)⁻¹) (frob h) (by simp)
    refine ⟨m, hm, ?_⟩
    rw [← map_pow, conj_pow] at hpow
    show ρ (ineIncl h τ) * _ = _ * ρ (ineIncl h τ)
    conv_rhs => rw [← hpow]
    rw [← map_pow, ← map_mul, ← map_mul, inv_mul_cancel_right]
  choose m hm hc using h1
  haveI := hρ.finite_range.fintype
  refine ⟨∏ T, m T, Finset.prod_pos fun T _ => hm T, fun σ => ?_⟩
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
  rw [hτ, map_mul]
  refine Commute.mul_left ?_ ?_
  · rw [← map_pow]
    exact ((Commute.refl (frob h)).zpow_left _).pow_right _ |>.map ρ
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ ⟨_, τ, rfl⟩)
    rw [hk, pow_mul]
    exact (hc ⟨_, τ, rfl⟩).pow_right k

theorem isSemisimple_apply (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ)
    (hss : ρ.IsSemisimpleRepresentation) (σ : Weil h) : End.IsSemisimple (ρ σ) := by
  classical
  obtain ⟨m, hm, hc⟩ := exists_pow_frob_comm ρ hρ
  refine isSemisimple_of_isSemisimple_frob E Ω A w h V ρ hρ (frob h) deg_frob
    (FrobSemisimple.isSemisimple_of_pow ((Group.isUnit _).map ρ) hm ?_) σ
  set T := ρ (frob h) ^ m with hT
  let p : ℂ[X] := ∏ μ ∈ (minpoly ℂ T).roots.toFinset, (X - C μ)
  refine End.isSemisimple_of_squarefree_aeval_eq_zero (p := p)
    (Separable.squarefree (separable_prod_X_sub_C_iff'.2 fun _ _ _ _ e => e)) ?_
  have hcp : ∀ g, Commute (ρ g) (aeval T p) := fun g => by
    simp only [p, map_prod]
    rw [aeval_eq_sum_range]
    exact Commute.sum_right _ _ _ fun i _ => ((hc g).pow_right i).smul_right _
  let K : Subrepresentation ρ := ⟨LinearMap.ker (aeval T p), fun g v hv => by
    rw [LinearMap.mem_ker, ← End.mul_apply, ← (hcp g).eq, End.mul_apply, LinearMap.mem_ker.1 hv,
      map_zero]⟩
  obtain ⟨Q, hQ⟩ := hss.exists_isCompl K
  have hinf : K.toSubmodule ⊓ Q.toSubmodule = ⊥ :=
    congrArg Subrepresentation.toSubmodule hQ.inf_eq_bot
  have hsup : K.toSubmodule ⊔ Q.toSubmodule = ⊤ :=
    congrArg Subrepresentation.toSubmodule hQ.sup_eq_top
  have hQT : ∀ v ∈ Q.toSubmodule, T v ∈ Q.toSubmodule := fun v hv => by
    rw [hT, ← map_pow]; exact Q.apply_mem_toSubmodule _ hv
  have hQ0 : Q.toSubmodule = ⊥ := by
    by_contra hne
    haveI : Nontrivial Q.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hne
    obtain ⟨μ, hμ⟩ := End.exists_eigenvalue (T.restrict hQT)
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hv1 : T v = μ • (v : V) := congrArg Subtype.val hv.apply_eq_smul
    have hv0 : (v : V) ≠ 0 := fun e => hv.2 (Subtype.ext e)
    have hvT : End.HasEigenvector T μ v := ⟨End.mem_eigenspace_iff.2 hv1, hv0⟩
    have hroot : μ ∈ (minpoly ℂ T).roots.toFinset := by
      rw [Multiset.mem_toFinset, mem_roots (minpoly.ne_zero_of_finite ℂ T)]
      exact End.hasEigenvalue_iff_isRoot.1 (End.hasEigenvalue_of_hasEigenvector hvT)
    have hK : (v : V) ∈ K.toSubmodule := by
      show aeval T p v = 0
      rw [End.aeval_apply_of_hasEigenvector hvT, show p.eval μ = 0 from ?_, zero_smul]
      simp only [p, eval_prod]
      exact Finset.prod_eq_zero hroot (by simp)
    exact hv0 ((Submodule.mem_bot ℂ).1 (hinf ▸ Submodule.mem_inf.2 ⟨hK, v.2⟩))
  rw [hQ0, sup_bot_eq] at hsup
  exact LinearMap.ker_eq_top.1 hsup

def wdOfRep (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ)
    (hss : ρ.IsSemisimpleRepresentation) : WDRep h V where
  ρ := ρ
  N := 0
  smooth := hρ
  semisimple := isSemisimple_apply ρ hρ hss
  nilpotent := IsNilpotent.zero
  comm σ := by simp

@[simp] theorem wdOfRep_ρ (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ)
    (hss : ρ.IsSemisimpleRepresentation) : (wdOfRep ρ hρ hss).ρ = ρ := rfl

@[simp] theorem wdOfRep_N (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ)
    (hss : ρ.IsSemisimpleRepresentation) : (wdOfRep ρ hρ hss).N = 0 := rfl

theorem trace_eq_of_iso {V' : Type} [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) (σ : Weil h) :
    LinearMap.trace ℂ V (a.ρ σ) = LinearMap.trace ℂ V' (b.ρ σ) := by
  obtain ⟨e, h1, -⟩ := hab
  rw [← LinearMap.trace_conj' (a.ρ σ) e]
  congr 1
  ext v
  simp [LinearEquiv.conj_apply, h1]

def trW (x : WD h) (σ : Weil h) : ℂ :=
  Quotient.lift (s := isoSetoid h) (fun a => LinearMap.trace ℂ _ (a.2.ρ σ))
    (fun _ _ hab => trace_eq_of_iso hab σ) x

@[simp] theorem trW_mk (a : WDRep h V) (σ : Weil h) :
    trW (WD.mk a) σ = LinearMap.trace ℂ V (a.ρ σ) :=
  (trace_eq_of_iso (WD.iso_std a) σ).symm

theorem trW_one (x : WD h) : trW x 1 = x.lpDim := by
  induction x using WD.ind with
  | hP n a => rw [trW_mk, WD.lpDim_mk, map_one, LinearMap.trace_one]

@[simp] theorem trW_lpSum (x y : WD h) (σ : Weil h) : trW (x.lpSum y) σ = trW x σ + trW y σ := by
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP m b => rw [WD.lpSum_mk, trW_mk, trW_mk, trW_mk, WDRep.sum_ρ, LinearMap.trace_prodMap']

@[simp] theorem trW_lpChar (x y : WD h) (σ : Weil h) : trW (x.lpChar y) σ = trW x σ * trW y σ := by
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP m b => rw [WD.lpChar_mk, trW_mk, trW_mk, trW_mk, WDRep.tensor_ρ, LinearMap.trace_tensorProduct']

@[simp] theorem trW_lpZero (σ : Weil h) : trW (WD.lpZero h) σ = 0 := by
  rw [WD.lpZero, trW_mk, Subsingleton.elim ((WDRep.diag h (ι := Fin 0) fun i => i.elim0).ρ σ) 0,
    map_zero]

theorem trW_sumList (l : List (WD h)) (σ : Weil h) :
    trW (sumList l) σ = (l.map fun x => trW x σ).sum := by
  induction l with
  | nil => exact trW_lpZero σ
  | cons x l ih =>
    rw [show sumList (x :: l) = x.lpSum (sumList l) from rfl, trW_lpSum, ih, List.map_cons,
      List.sum_cons]

@[simp] theorem trW_lpTwist (x : WD h) (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) (σ : Weil h) :
    trW (x.lpTwist χ hχ) σ = χ σ * trW x σ := by
  induction x using WD.ind with
  | hP n a => rw [WD.lpTwist_mk, trW_mk, trW_mk, WDRep.twist_ρ, map_smul, smul_eq_mul]

@[simp] theorem trW_lpOfChar (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) (σ : Weil h) :
    trW (WD.lpOfChar h χ hχ) σ = χ σ := by
  rw [WD.lpOfChar, trW_mk, WDRep.ofChars_ρ]
  have : (diagEnd fun _ : Fin 1 => (χ σ : ℂ)) = (χ σ : ℂ) • (1 : End ℂ (Fin 1 → ℂ)) :=
    LinearMap.ext fun v => funext fun i => by simp
  rw [this, map_smul, LinearMap.trace_one]
  simp

variable (h) in

abbrev IrrW : Type := {x : WD h // IsIrrWD x}

theorem isIrrWD_mk (a : WDRep h V) : IsIrrWD (WD.mk a) ↔ a.ρ.IsIrreducible := by
  constructor
  · rintro ⟨n, b, hb, hirr⟩
    obtain ⟨e, he, -⟩ := WD.mk_eq_mk.1 hb
    exact IrrDecomp.isIrreducible_of_equiv e he hirr
  · intro hirr
    obtain ⟨e, he, -⟩ := WD.iso_std a
    exact ⟨_, (WD.std a).2, (WD.sound (WD.iso_std _)).symm, IrrDecomp.isIrreducible_of_equiv e he hirr⟩

theorem nontrivial_of_irr {ρ : Representation ℂ (Weil h) V} (hρ : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  exact bot_ne_top (α := Subrepresentation ρ)
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem N_eq_zero_of_irr (a : WDRep h V) (hirr : a.ρ.IsIrreducible) : a.N = 0 := by
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans (one_lt_normV w)).ne'
  let S : Subrepresentation a.ρ := ⟨LinearMap.ker a.N, fun σ v hv => by
    have h1 := a.comm_apply σ v
    rw [LinearMap.mem_ker.1 hv, map_zero] at h1
    exact LinearMap.mem_ker.2 ((smul_eq_zero.1 h1.symm).resolve_left (zpow_ne_zero _ hq))⟩
  rcases hirr.eq_bot_or_eq_top S with hS | hS
  · exfalso
    have hinj : Function.Injective a.N := by
      rw [← LinearMap.ker_eq_bot]
      exact congrArg Subrepresentation.toSubmodule hS
    obtain ⟨m, hm⟩ := a.nilpotent
    have hinj' : Function.Injective (a.N ^ m) := by
      rw [End.coe_pow]; exact hinj.iterate m
    rw [hm] at hinj'
    have := nontrivial_of_irr hirr
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv (hinj' (a₁ := v) (a₂ := 0) (by simp))
  · exact LinearMap.ker_eq_top.1 (congrArg Subrepresentation.toSubmodule hS)

theorem IrrW.mono0 (z : IrrW h) : z.1.mono0 := by
  obtain ⟨_, n, a, rfl, ha⟩ := z
  exact (WD.monodromyZero_ofWeilDeligneRepClass_iff a).2 (N_eq_zero_of_irr a ha)

theorem IrrW.lpDim_pos (z : IrrW h) : 0 < z.1.lpDim := by
  obtain ⟨_, n, a, rfl, ha⟩ := z
  have := nontrivial_of_irr ha
  show 0 < (WD.mk a).lpDim
  rw [WD.lpDim_mk]
  exact finrank_pos

def IrrW.ofRep (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ) (hirr : ρ.IsIrreducible) :
    IrrW h :=
  ⟨WD.mk (wdOfRep ρ hρ inferInstance), (isIrrWD_mk _).2 hirr⟩

theorem isIrrWD_lpTwist {x : WD h} (hx : IsIrrWD x) (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) :
    IsIrrWD (x.lpTwist χ hχ) := by
  obtain ⟨n, a, rfl, ha⟩ := hx
  refine ⟨n, a.twist χ hχ, (WD.lpTwist_mk a χ hχ).symm, ?_⟩
  have hρ : ∀ g v, (a.twist χ hχ).ρ g v = ((χ g : ℂˣ) : ℂ) • a.ρ g v := fun _ _ => rfl
  let e : Subrepresentation (a.twist χ hχ).ρ ≃o Subrepresentation a.ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        have := S.toSubmodule.smul_mem (((χ g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
        rw [hρ, smul_smul] at this
        simpa using this⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        rw [hρ]; exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact e.isSimpleOrder_iff.2 ha

def IrrW.twist (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) (z : IrrW h) : IrrW h :=
  ⟨z.1.lpTwist χ hχ, isIrrWD_lpTwist z.2 χ hχ⟩

theorem isIrrWD_lpOfChar (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) : IsIrrWD (WD.lpOfChar h χ hχ) := by
  refine ⟨1, _, rfl, ?_⟩
  haveI : IsSimpleModule ℂ (Fin 1 → ℂ) := isSimpleModule_iff_finrank_eq_one.2 (by simp)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun hbt => ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
  · exact bot_ne_top (α := Submodule ℂ (Fin 1 → ℂ)) (congrArg Subrepresentation.toSubmodule hbt)
  · rcases eq_bot_or_eq_top U.toSubmodule with hU | hU
    · exact Or.inl (Subrepresentation.toSubmodule_injective hU)
    · exact Or.inr (Subrepresentation.toSubmodule_injective hU)

def IrrW.ofChar (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) : IrrW h :=
  ⟨WD.lpOfChar h χ hχ, isIrrWD_lpOfChar χ hχ⟩

theorem linearIndependent_trW : LinearIndependent ℂ fun z : IrrW h => trW z.1 := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  choose n a ha hirr using fun z : IrrW h => z.2
  have key := SimpleCharIndep.linearIndependent_trace (MonoidAlgebra ℂ (Weil h)) s
    (fun z => (a z).ρ.asModule)
    (fun z => (Representation.irreducible_iff_isSimpleModule_asModule _).1 (hirr z)) (by
      rintro z z' ⟨e⟩
      refine Subtype.ext (Subtype.ext ?_)
      rw [← ha z, ← ha z']
      refine WD.sound ⟨((a z).ρ.asModuleEquiv.symm.trans (e.restrictScalars ℂ)).trans
        (a z').ρ.asModuleEquiv, fun σ v => ?_, fun v => ?_⟩
      · show (a z').ρ.asModuleEquiv (e ((a z).ρ.asModuleEquiv.symm ((a z).ρ σ v))) =
          (a z').ρ σ ((a z').ρ.asModuleEquiv (e ((a z).ρ.asModuleEquiv.symm v)))
        rw [Representation.asModuleEquiv_symm_map_rho, map_smul,
          Representation.asModuleEquiv_map_smul, MonoidAlgebra.of_apply,
          Representation.asAlgebraHom_single_one]
      · simp [N_eq_zero_of_irr _ (hirr _)])
  rw [Fintype.linearIndependent_iff] at key ⊢
  intro g hg
  refine key g (funext fun t => ?_)
  have hl : ∀ (z : s) (t : MonoidAlgebra ℂ (Weil h)), LinearMap.trace ℂ ((a z).ρ.asModule)
      (Algebra.lsmul ℂ ℂ ((a z).ρ.asModule) t) =
      LinearMap.trace ℂ _ ((a z).ρ.asAlgebraHom t) := fun _ _ => rfl
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hl]
  induction t using MonoidAlgebra.induction_on with
  | of σ =>
    have := congr_fun hg σ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Function.comp] at this
    rw [← this]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← ha z, trW_mk, MonoidAlgebra.of_apply, Representation.asAlgebraHom_single_one]
  | add t t' ht ht' => simp only [map_add, mul_add, Finset.sum_add_distrib, ht, ht', add_zero]
  | smul c t ht =>
    simp only [map_smul, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum, ht, mul_zero]

variable (h) in

def frobCoset (r : ℕ) : Set (Weil h) := {τ | deg τ = -(r : ℤ)}

@[simp] theorem mem_frobCoset {r : ℕ} {τ : Weil h} : τ ∈ frobCoset h r ↔ deg τ = -(r : ℤ) := Iff.rfl

variable (w) in

def qPowC (s : ℂ) : ℂˣ :=
  Units.mk0 (((normV w : ℕ) : ℂ) ^ s) (by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot))

omit [IsAlgClosure E Ω] in

@[simp] theorem coe_qPowC (s : ℂ) : (qPowC w s : ℂ) = ((normV w : ℕ) : ℂ) ^ s := rfl

variable (h) in

def absChar (s : ℂ) : Weil h →* ℂˣ := unrChar h (qPowC w s)

theorem isSmooth_absChar (s : ℂ) : IsSmooth (absChar h s) := isSmooth_unrChar h _

theorem absChar_apply (s : ℂ) (σ : Weil h) :
    (absChar h s σ : ℂ) = ((normV w : ℕ) : ℂ) ^ (s * deg σ) := by
  rw [absChar, unrChar_apply, Units.val_zpow_eq_zpow_val, coe_qPowC, mul_comm,
    Complex.cpow_int_mul]

theorem absChar_of_mem_frobCoset (s : ℂ) {r : ℕ} {τ : Weil h} (hτ : τ ∈ frobCoset h r) :
    (absChar h s τ : ℂ) = ((normV w : ℕ) : ℂ) ^ (-(r * s)) := by
  rw [absChar_apply, mem_frobCoset.1 hτ]
  congr 1
  push_cast; ring

@[simp] theorem absChar_zero : absChar h 0 = 1 :=
  MonoidHom.ext fun σ => Units.ext (by simp [absChar_apply])

theorem absChar_add (s t : ℂ) : absChar h (s + t) = absChar h s * absChar h t :=
  MonoidHom.ext fun σ => Units.ext (by
    rw [MonoidHom.mul_apply, Units.val_mul, absChar_apply, absChar_apply, absChar_apply, add_mul]
    exact Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot))

section Artin

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end Artin

variable (h) in

abbrev VR : Type := IrrW h →₀ ℚ

namespace VR

def irr (z : IrrW h) : VR h := Finsupp.single z 1

variable (h) in

def dim : VR h →ₗ[ℚ] ℚ := Finsupp.linearCombination ℚ fun z : IrrW h => (z.1.lpDim : ℚ)

def tr (τ : Weil h) : VR h →ₗ[ℚ] ℂ := Finsupp.linearCombination ℚ fun z : IrrW h => trW z.1 τ

def twist (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) : VR h →ₗ[ℚ] VR h :=
  Finsupp.lmapDomain ℚ ℚ (IrrW.twist χ hχ)

def tw (s : ℂ) : VR h →ₗ[ℚ] VR h := twist (absChar h s) (isSmooth_absChar s)

variable (h) in

def posCone : Submodule ℚ≥0 (VR h) where
  carrier := {x | ∀ z, 0 ≤ x z}
  zero_mem' _ := le_rfl
  add_mem' hx hy z := add_nonneg (hx z) (hy z)
  smul_mem' c _ hx z := mul_nonneg c.2 (hx z)

variable (h) in

def intLattice : Submodule ℤ (VR h) where
  carrier := {x | ∀ z, ∃ m : ℤ, x z = m}
  zero_mem' _ := ⟨0, by simp⟩
  add_mem' {x y} hx hy z := by
    obtain ⟨m, hm⟩ := hx z
    obtain ⟨n, hn⟩ := hy z
    exact ⟨m + n, by simp [hm, hn]⟩
  smul_mem' c x hx z := by
    obtain ⟨m, hm⟩ := hx z
    exact ⟨c * m, by simp [hm]⟩

@[simp] theorem dim_irr (z : IrrW h) : dim h (irr z) = z.1.lpDim := by simp [dim, irr]

@[simp] theorem tr_irr (τ : Weil h) (z : IrrW h) : tr τ (irr z) = trW z.1 τ := by simp [tr, irr]

@[simp] theorem twist_irr (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) (z : IrrW h) :
    twist χ hχ (irr z) = irr (z.twist χ hχ) := by simp [twist, irr]

theorem tr_apply (τ : Weil h) (x : VR h) : tr τ x = ∑ z ∈ x.support, (x z : ℂ) * trW z.1 τ := by
  simp [tr, Finsupp.linearCombination_apply, Finsupp.sum, Rat.smul_def]

theorem dim_apply (x : VR h) : dim h x = ∑ z ∈ x.support, x z * (z.1.lpDim : ℚ) := by
  simp [dim, Finsupp.linearCombination_apply, Finsupp.sum]

theorem irr_mem_posCone (z : IrrW h) : irr z ∈ posCone h := fun y => by
  classical
  rw [irr, Finsupp.single_apply]; split_ifs <;> norm_num

theorem eq_sum_irr (x : VR h) : x = ∑ z ∈ x.support, x z • irr z := by
  conv_lhs => rw [← Finsupp.sum_single x]
  simp [Finsupp.sum, irr]

theorem tr_one (x : VR h) : tr 1 x = (dim h x : ℂ) := by
  simp [tr_apply, dim_apply, trW_one]

@[simp] theorem tr_twist (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) (τ : Weil h) (x : VR h) :
    tr τ (twist χ hχ x) = χ τ * tr τ x := by
  rw [eq_sum_irr x]
  simp only [map_sum, map_smul, twist_irr, tr_irr, IrrW.twist, trW_lpTwist, Finset.mul_sum,
    mul_smul_comm]

theorem tr_tw (s : ℂ) (τ : Weil h) (x : VR h) :
    tr τ (tw s x) = ((normV w : ℕ) : ℂ) ^ (s * deg τ) * tr τ x := by
  rw [tw, tr_twist, absChar_apply]

theorem tr_tw_of_mem_frobCoset (s : ℂ) {r : ℕ} {τ : Weil h} (hτ : τ ∈ frobCoset h r) (x : VR h) :
    tr τ (tw s x) = ((normV w : ℕ) : ℂ) ^ (-(r * s)) * tr τ x := by
  rw [tw, tr_twist, absChar_of_mem_frobCoset s hτ]

theorem ext_tr {x y : VR h} (H : ∀ τ, tr τ x = tr τ y) : x = y := by
  rw [← sub_eq_zero]
  have h0 : ∀ τ, tr τ (x - y) = 0 := fun τ => by rw [map_sub, H, sub_self]
  generalize x - y = u at h0
  have := linearIndependent_iff'.1 (linearIndependent_trW (h := h)) u.support (fun z => (u z : ℂ))
    (funext fun τ => by simpa [tr_apply, Finset.sum_apply] using h0 τ)
  ext z
  by_contra hz
  exact hz (by exact_mod_cast this z (Finsupp.mem_support_iff.2 hz))

@[simp] theorem dim_twist (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) (x : VR h) :
    dim h (twist χ hχ x) = dim h x := by
  have := tr_twist χ hχ 1 x
  rw [tr_one, tr_one, map_one, Units.val_one, one_mul] at this
  exact_mod_cast this

@[simp] theorem dim_tw (s : ℂ) (x : VR h) : dim h (tw s x) = dim h x := dim_twist _ _ x

@[simp] theorem tw_zero (x : VR h) : tw 0 x = x := ext_tr fun τ => by simp [tr_tw]

theorem tw_tw (s t : ℂ) (x : VR h) : tw t (tw s x) = tw (s + t) x := ext_tr fun τ => by
  simp only [tw, tr_twist, absChar_add, MonoidHom.mul_apply, Units.val_mul]
  ring

theorem exists_list_tr (x : WD h) :
    ∃ l : List (IrrW h), ∀ τ, tr τ (l.map irr).sum = trW x τ := by
  induction x using WD.ind with
  | hP n a =>
    obtain ⟨L, hL, hsum⟩ := IrrDecomp.exists_irr_list _ _
      (wdOfRep a.ρ a.smooth (WDRep.isSemisimpleRepresentation_rho E Ω A w h n a)) rfl rfl
    refine ⟨L.attach.map fun z => ⟨z.1, hL z.1 z.2⟩, fun τ => ?_⟩
    have h1 := congrArg (fun y => trW y τ) hsum
    simp only [trW_mk, wdOfRep_ρ, trW_sumList] at h1
    rw [trW_mk, h1, map_list_sum, List.map_map, List.map_map]
    conv_rhs => rw [← List.attach_map_subtype_val L, List.map_map]
    congr 1
    exact List.map_congr_left fun z _ => by simp

def ofWD (x : WD h) : VR h := ((exists_list_tr x).choose.map irr).sum

@[simp] theorem tr_ofWD (τ : Weil h) (x : WD h) : tr τ (ofWD x) = trW x τ :=
  (exists_list_tr x).choose_spec τ

@[simp] theorem dim_ofWD (x : WD h) : dim h (ofWD x) = x.lpDim := by
  have := tr_ofWD 1 x
  rw [tr_one, trW_one] at this
  exact_mod_cast this

@[simp] theorem ofWD_irr (z : IrrW h) : ofWD z.1 = irr z := ext_tr fun τ => by simp

@[simp] theorem ofWD_lpZero : ofWD (WD.lpZero h) = 0 := ext_tr fun τ => by simp

@[simp] theorem ofWD_lpSum (x y : WD h) : ofWD (x.lpSum y) = ofWD x + ofWD y :=
  ext_tr fun τ => by simp

@[simp] theorem ofWD_lpTwist (x : WD h) (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) :
    ofWD (x.lpTwist χ hχ) = twist χ hχ (ofWD x) := ext_tr fun τ => by simp

@[simp] theorem ofWD_lpTw (x : WD h) (s : ℝ) : ofWD (x.lpTw s) = tw s (ofWD x) :=
  ofWD_lpTwist x _ _

def ofRep (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ)
    (hss : ρ.IsSemisimpleRepresentation) : VR h := ofWD (WD.mk (wdOfRep ρ hρ hss))

@[simp] theorem tr_ofRep (τ : Weil h) (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ)
    (hss : ρ.IsSemisimpleRepresentation) : tr τ (ofRep ρ hρ hss) = LinearMap.trace ℂ V (ρ τ) := by
  simp [ofRep]

@[simp] theorem dim_ofRep (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ)
    (hss : ρ.IsSemisimpleRepresentation) : dim h (ofRep ρ hρ hss) = finrank ℂ V := by
  simp [ofRep]

variable (h) in

def IsGenuine (n : ℕ) (x : VR h) : Prop :=
  ∃ (ρ : Representation ℂ (Weil h) (Fin n → ℂ)) (hρ : IsSmooth ρ)
    (hss : ρ.IsSemisimpleRepresentation), ofRep ρ hρ hss = x

def ofChar (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) : VR h := irr (IrrW.ofChar χ hχ)

@[simp] theorem tr_ofChar (τ : Weil h) (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) :
    tr τ (ofChar χ hχ) = χ τ := by simp [ofChar, IrrW.ofChar]

@[simp] theorem ofWD_lpOfChar (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) :
    ofWD (WD.lpOfChar h χ hχ) = ofChar χ hχ := ofWD_irr (IrrW.ofChar χ hχ)

variable (h) in

def triv : VR h := ofChar 1 (IsSmooth.of_trivial fun _ => rfl)

@[simp] theorem tr_triv (τ : Weil h) : tr τ (triv h) = 1 := by simp [triv]

@[simp] theorem dim_triv : dim h (triv h) = 1 := by
  have := tr_triv (1 : Weil h)
  rw [tr_one] at this
  exact_mod_cast this

example : tr (frob h)⁻¹ (tw 1 (triv h)) = ((normV w : ℕ) : ℂ)⁻¹ := by
  rw [tr_tw_of_mem_frobCoset (r := 1) 1 (by simp)]
  simp [Complex.cpow_neg_one]

example : (1 / 2 : ℚ) • triv h ∈ posCone h ∧ dim h ((1 / 2 : ℚ) • triv h) = 1 / 2 ∧
    (1 / 2 : ℚ) • triv h ∉ intLattice h := by
  refine ⟨fun z => mul_nonneg (by norm_num) (irr_mem_posCone _ z), by simp, fun H => ?_⟩
  obtain ⟨m, hm⟩ := H (IrrW.ofChar 1 (IsSmooth.of_trivial fun _ => rfl))
  have h1 : (1 : ℚ) = 2 * m := by
    rw [← hm]; simp [triv, ofChar, irr]
  have h2 : (1 : ℤ) = 2 * m := by exact_mod_cast h1
  omega

example : dim h (ofWD (WD.lpSp h 2)) = 2 := by simp

example (r : ℕ) : frob h ∉ frobCoset h r := by
  rw [mem_frobCoset, deg_frob]; omega

end VR

end GlobalTheory.VWeil
