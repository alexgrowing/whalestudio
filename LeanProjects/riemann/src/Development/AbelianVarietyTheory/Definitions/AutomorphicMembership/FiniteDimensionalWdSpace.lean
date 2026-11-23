import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.Pst

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)

@[reducible] def algC (LL : FinExt l) : Algebra ↥LL.1 ℂ :=
  (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))).toAlgebra

def urC : ↥(MaximalUnramifiedExtension l) →+* ℂ := ι.toRingHom.comp (algebraMap ↥(MaximalUnramifiedExtension l) (Om l))

section Space

variable {K LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)

abbrev WDSpace : Type :=
  @Letter ↥LL.1 ↥(MaximalUnramifiedExtension l) ↥(Dpst P ρ) _ _ _ _ (mulD P ρ) ℂ _ (algC ι LL) (urC ι)

def wdMk (x : ↥(Dpst P ρ)) : WDSpace P ι ρ :=
  @letterMk ↥LL.1 ↥(MaximalUnramifiedExtension l) ↥(Dpst P ρ) _ _ _ _ (mulD P ρ) ℂ _ (algC ι LL) (urC ι) x

def wdMap (T : End ↥LL.1 ↥(Dpst P ρ)) (hT : ∀ c, T * mulD P ρ c = mulD P ρ c * T) :
    End ℂ (WDSpace P ι ρ) :=
  @letterMap ↥LL.1 ↥(MaximalUnramifiedExtension l) ↥(Dpst P ρ) _ _ _ _ (mulD P ρ) ℂ _ (algC ι LL) (urC ι) T hT

@[simp] theorem wdMap_mk (T : End ↥LL.1 ↥(Dpst P ρ)) (hT : ∀ c, T * mulD P ρ c = mulD P ρ c * T)
    (x : ↥(Dpst P ρ)) : wdMap P ι ρ T hT (wdMk P ι ρ x) = wdMk P ι ρ (T x) := rfl

@[simp] theorem wdMk_zero : wdMk P ι ρ 0 = 0 := letI := algC ι LL; letterMk_zero _ _ _

theorem wdMk_add (x y : ↥(Dpst P ρ)) : wdMk P ι ρ (x + y) = wdMk P ι ρ x + wdMk P ι ρ y :=
  letI := algC ι LL; letterMk_add _ _ _ x y

theorem wdMk_smul (a : ↥LL.1) (x : ↥(Dpst P ρ)) :
    wdMk P ι ρ (a • x) = ι (a : Om l) • wdMk P ι ρ x :=
  letI := algC ι LL; letterMk_smul _ _ _ a x

theorem wdMk_mul (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρ)) :
    wdMk P ι ρ (mulD P ρ c x) = ι (c : Om l) • wdMk P ι ρ x :=
  letI := algC ι LL; letterMk_mul _ _ _ c x

theorem span_wdMk : Submodule.span ℂ (Set.range (wdMk P ι ρ)) = ⊤ :=
  letI := algC ι LL; span_letterMk _ _ _

theorem wd_ext {f g : End ℂ (WDSpace P ι ρ)} (h : ∀ x, f (wdMk P ι ρ x) = g (wdMk P ι ρ x)) : f = g :=
  LinearMap.ext_on_range (span_wdMk P ι ρ) h

def wdN : End ℂ (WDSpace P ι ρ) := wdMap P ι ρ (monD P ρ) (monD_mulD P ρ)

@[simp] theorem wdN_mk (x : ↥(Dpst P ρ)) : wdN P ι ρ (wdMk P ι ρ x) = wdMk P ι ρ (monD P ρ x) := rfl

instance finiteDimensional_wdSpace [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] :
    FiniteDimensional ℂ (WDSpace P ι ρ) :=
  letI := algC ι LL
  finiteDimensional_letter _ _ _
    (fun i => (toUr P ρ).symm (finBasis ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) i)) fun x =>
      ⟨_, ((finBasis ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)).sum_repr (toUr P ρ x)).symm⟩

theorem isNilpotent_wdN [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] : IsNilpotent (wdN P ι ρ) := by
  obtain ⟨n, hn⟩ := isNilpotent_monD (P := P) (ρ := ρ)
  have hp : ∀ (k : ℕ) x, (wdN P ι ρ ^ k) (wdMk P ι ρ x) = wdMk P ι ρ ((monD P ρ ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih => intro x; rw [pow_succ, pow_succ, End.mul_apply, End.mul_apply, wdN_mk, ih]
  exact ⟨n, wd_ext P ι ρ fun x => by rw [hp, hn]; simp⟩

variable {P ρ} in

theorem IsPst.finite [FiniteDimensional ↥LL.1 V] (hV : IsPst P ρ) :
    FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) :=
  haveI := LL.2
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  hV.finiteDimensional

end Space

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]

section Param

variable [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)
  {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V)

def trivWD (a : ℕ) : WD h := WD.mk (WDRep.diag h fun _ : Fin a => 1)

@[simp] theorem lpDim_trivWD (a : ℕ) : (trivWD h a).lpDim = a := by simp [trivWD]

section Fin

variable [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)]

def wdRho : Representation ℂ ↥(Weil h) (WDSpace P ι ρ) where
  toFun σ := wdMap P ι ρ (weilD Bw h P ρ σ) (weilD_mulD Bw h P ρ hj σ)
  map_one' := wd_ext P ι ρ fun x => by simp
  map_mul' σ τ := wd_ext P ι ρ fun x => by simp

@[simp] theorem wdRho_mk (σ : ↥(Weil h)) (x : ↥(Dpst P ρ)) :
    wdRho P ι Bw h hj ρ σ (wdMk P ι ρ x) = wdMk P ι ρ (weilD Bw h P ρ σ x) := rfl

theorem isSmooth_wdRho : IsSmooth (wdRho P ι Bw h hj ρ) :=
  (isSmooth_weilD Bw h P ρ hj).of_le fun σ hσ => wd_ext P ι ρ fun x => by simp [hσ]

theorem wdRho_wdN (σ : ↥(Weil h)) : wdRho P ι Bw h hj ρ σ * wdN P ι ρ =
    ((normV w : ℕ) : ℂ) ^ deg σ • (wdN P ι ρ * wdRho P ι Bw h hj ρ σ) :=
  wd_ext P ι ρ fun x => by
    have h1 := LinearMap.congr_fun (weilD_monD Bw h P ρ hj σ) x
    rw [End.mul_apply, LinearMap.smul_apply, End.mul_apply] at h1
    have e : ι (((((normV w : ℕ) : ↥LL.1) ^ deg σ : ↥LL.1)) : Om l) = ((normV w : ℕ) : ℂ) ^ deg σ :=
      (map_zpow₀ (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) ((normV w : ℕ) : ↥LL.1) (deg σ)).trans
        (by rw [map_natCast])
    have h2 := congrArg (wdMk P ι ρ) h1
    rw [wdMk_smul, e] at h2
    exact h2

def wdRep : WDRep h (WDSpace P ι ρ) :=
  (exists_frobenius_semisimplification E Ω A w h _ (wdRho P ι Bw h hj ρ) (wdN P ι ρ)
    (isSmooth_wdRho P ι Bw h hj ρ) (isNilpotent_wdN P ι ρ) (wdRho_wdN P ι Bw h hj ρ)).choose

theorem wdRep_spec : ∃ u : (End ℂ (WDSpace P ι ρ))ˣ, (wdRep P ι Bw h hj ρ).N = wdN P ι ρ ∧
    IsNilpotent ((u : End ℂ (WDSpace P ι ρ)) - 1) ∧ Commute (u : End ℂ (WDSpace P ι ρ)) (wdN P ι ρ) ∧
    (∀ σ, Commute (u : End ℂ (WDSpace P ι ρ)) (wdRho P ι Bw h hj ρ σ)) ∧
    ∀ σ, wdRho P ι Bw h hj ρ σ = (wdRep P ι Bw h hj ρ).ρ σ *
      ((u ^ deg σ : (End ℂ (WDSpace P ι ρ))ˣ) : End ℂ (WDSpace P ι ρ)) :=
  (exists_frobenius_semisimplification E Ω A w h _ (wdRho P ι Bw h hj ρ) (wdN P ι ρ)
    (isSmooth_wdRho P ι Bw h hj ρ) (isNilpotent_wdN P ι ρ) (wdRho_wdN P ι Bw h hj ρ)).choose_spec

@[simp] theorem wdRep_N : (wdRep P ι Bw h hj ρ).N = wdN P ι ρ :=
  (wdRep_spec P ι Bw h hj ρ).choose_spec.1

theorem wdRep_ineIncl (σ : ↥(Ine (F := E) A)) :
    (wdRep P ι Bw h hj ρ).ρ (ineIncl h σ) = wdRho P ι Bw h hj ρ (ineIncl h σ) := by
  obtain ⟨u, -, -, -, -, hu⟩ := wdRep_spec P ι Bw h hj ρ
  rw [hu]; simp

end Fin

variable [FiniteDimensional ↥LL.1 V]

open Classical in

def wdPst : WD h :=
  if hV : IsPst P ρ then haveI := hV.finite; WD.mk (wdRep P ι Bw h hj ρ) else trivWD h (finrank ↥LL.1 V)

variable {P ρ}

theorem wdPst_of_isPst (hV : IsPst P ρ) :
    wdPst P ι Bw h hj ρ = haveI := hV.finite; WD.mk (wdRep P ι Bw h hj ρ) := dif_pos hV

theorem wdPst_of_not_isPst (hV : ¬ IsPst P ρ) : wdPst P ι Bw h hj ρ = trivWD h (finrank ↥LL.1 V) :=
  dif_neg hV

theorem lpDim_wdPst (hV : IsPst P ρ) : (wdPst P ι Bw h hj ρ).lpDim = finrank ℂ (WDSpace P ι ρ) := by
  have := hV.finite
  rw [wdPst_of_isPst ι Bw h hj hV, WD.lpDim_mk]

theorem mono0_wdPst (hV : IsPst P ρ) : (wdPst P ι Bw h hj ρ).mono0 ↔ wdN P ι ρ = 0 := by
  have := hV.finite
  rw [wdPst_of_isPst ι Bw h hj hV, WD.monodromyZero_ofWeilDeligneRepClass_iff, wdRep_N]

theorem unr_wdPst (hV : IsPst P ρ) : (wdPst P ι Bw h hj ρ).unr ↔ wdN P ι ρ = 0 ∧
    ∀ (σ : ↥(Ine (F := E) A)) (x : ↥(Dpst P ρ)),
      wdMk P ι ρ (actD P ρ (weilToGK Bw h (ineIncl h σ)) x) = wdMk P ι ρ x := by
  have := hV.finite
  rw [wdPst_of_isPst ι Bw h hj hV, WD.unr_mk, WDRep.Unr, wdRep_N]
  refine and_congr_right fun _ => forall_congr' fun σ => ?_
  rw [wdRep_ineIncl, ← weilD_ineIncl]
  exact ⟨fun h1 x => by rw [← wdRho_mk P ι Bw h hj, h1]; rfl, fun h1 => wd_ext P ι ρ h1⟩

end Param

section Model

variable {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {a : ℕ}
  (r : ↥Gw →* GL (Fin a) (Om l))

def IsModel (LL' : FinExt l) (r' : ↥Gw →* GL (Fin a) ↥LL'.1) : Prop :=
  Bw.LL.1 ≤ LL'.1 ∧ Formalism.MainNotions.N.mapRep (algebraMap ↥LL'.1 (Om l)) r' = r

def IsCrysAt : Prop := ∃ LL' r', IsModel Bw r LL' r' ∧ Bw.IsCrysE P LL' r'

def IsPotCrysAt : Prop := ∃ LL' r', IsModel Bw r LL' r' ∧ Bw.IsPotCrysE P LL' r'

def IsdRAt : Prop := ∃ LL' r', IsModel Bw r LL' r' ∧ Bw.IsdRE P LL' r'

def IsPstAt : Prop := ∃ LL' r', IsModel Bw r LL' r' ∧ IsPst P (Bw.repE LL' r')

def IsInduced (τ : E →+* Om l) {LL' : FinExt l} (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) : Prop :=
  ∀ x : E, τ x = ((τ' ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩ : ↥LL'.1) : Om l)

def IsJumpsAt (τ : E →+* Om l) (J : Multiset ℤ) : Prop :=
  ∃ LL' r', IsModel Bw r LL' r' ∧ Bw.IsdRE P LL' r' ∧ ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1,
    IsInduced Bw τ τ' ∧ ∀ n : ℤ, (J.count n : ℤ) = Bw.multE P LL' r' τ' n

omit [NumberField E] in

theorem IsCrysAt.isPotCrysAt (hr : IsCrysAt P Bw r) : IsPotCrysAt P Bw r := by
  obtain ⟨LL', r', h1, h2⟩ := hr
  exact ⟨LL', r', h1, Bw.Kw, le_rfl, h2⟩

omit [NumberField E] in

theorem IsModel.unique {LL' : FinExt l} {r₁ r₂ : ↥Gw →* GL (Fin a) ↥LL'.1} (h₁ : IsModel Bw r LL' r₁)
    (h₂ : IsModel Bw r LL' r₂) : r₁ = r₂ := by
  ext g i j
  exact congrArg (fun f : ↥Gw →* GL (Fin a) (Om l) => (f g : Matrix (Fin a) (Fin a) (Om l)) i j)
    (h₁.2.trans h₂.2.symm)

omit [NumberField E] in

theorem isModel_one : IsModel Bw (1 : ↥Gw →* GL (Fin a) (Om l)) Bw.LL 1 :=
  ⟨le_rfl, MonoidHom.ext fun _ => by simp [Formalism.MainNotions.N.mapRep]⟩

end Model

section At

variable [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {a : ℕ}
  (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l))

open Classical in

def wdAt : WD h :=
  if hr : IsPstAt P Bw r then wdPst P ι Bw h hj (Bw.repE hr.choose hr.choose_spec.choose) else trivWD h a

variable {P r}

theorem wdAt_of_isPstAt (hr : IsPstAt P Bw r) : ∃ LL' r', IsModel Bw r LL' r' ∧ IsPst P (Bw.repE LL' r') ∧
    wdAt P ι Bw h hj r = wdPst P ι Bw h hj (Bw.repE LL' r') :=
  ⟨_, _, hr.choose_spec.choose_spec.1, hr.choose_spec.choose_spec.2, dif_pos hr⟩

theorem wdAt_of_not_isPstAt (hr : ¬ IsPstAt P Bw r) : wdAt P ι Bw h hj r = trivWD h a := dif_neg hr

end At

section Global

variable (pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω)
  (br : ∀ w : HeightOneSpectrum (𝓞 E), w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (pl w)) O)
  {a : ℕ} (r : G E Ω →* GL (Fin a) (Om l))

abbrev resDec (w : HeightOneSpectrum (𝓞 E)) : ↥(Dec (F := E) (pl w)) →* GL (Fin a) (Om l) :=
  r.comp (Dec (F := E) (pl w)).subtype

def IsCrysW (w : HeightOneSpectrum (𝓞 E)) : Prop := ∃ hw, IsCrysAt P (br w hw) (resDec pl r w)

def IsPotCrysW (w : HeightOneSpectrum (𝓞 E)) : Prop := ∃ hw, IsPotCrysAt P (br w hw) (resDec pl r w)

def IsdRW (w : HeightOneSpectrum (𝓞 E)) : Prop := ∃ hw, IsdRAt P (br w hw) (resDec pl r w)

def IsJumpsW (τ : E →+* Om l) (J : Multiset ℤ) : Prop :=
  ∃ w hw, IsJumpsAt P (br w hw) (resDec pl r w) τ J

open Classical in

def jumpsW (τ : E →+* Om l) : Multiset ℤ :=
  if hJ : ∃ J, IsJumpsW P pl br r τ J then hJ.choose else 0

theorem isJumpsW_jumpsW {τ : E →+* Om l} (hJ : ∃ J, IsJumpsW P pl br r τ J) :
    IsJumpsW P pl br r τ (jumpsW P pl br r τ) := by
  rw [jumpsW, dif_pos hJ]; exact hJ.choose_spec

theorem isCrysW_iff {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ placesOver E l) :
    IsCrysW P pl br r w ↔ IsCrysAt P (br w hw) (resDec pl r w) := ⟨fun ⟨_, h⟩ => h, fun h => ⟨hw, h⟩⟩

theorem isPotCrysW_iff {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ placesOver E l) :
    IsPotCrysW P pl br r w ↔ IsPotCrysAt P (br w hw) (resDec pl r w) := ⟨fun ⟨_, h⟩ => h, fun h => ⟨hw, h⟩⟩

theorem isdRW_iff {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ placesOver E l) :
    IsdRW P pl br r w ↔ IsdRAt P (br w hw) (resDec pl r w) := ⟨fun ⟨_, h⟩ => h, fun h => ⟨hw, h⟩⟩

def wdL [IsAlgClosure E Ω] (hpl : ∀ w, IsPlaceOver (pl w) w) (hbr : ∀ w hw, Induces (br w hw))
    (w : HeightOneSpectrum (𝓞 E)) (hw : w ∈ placesOver E l) : WD (hpl w) :=
  wdAt P ι (br w hw) (hpl w) (hbr w hw) (resDec pl r w)

end Global

section Examples

variable (K : FinExt l)

def tInv : P.R.B := ((isUnit_tB P).unit⁻¹ : P.R.Bˣ)

theorem tInv_mul : tInv P * P.tB = 1 := (isUnit_tB P).val_inv_mul

theorem smul_actQ_tInv (g : GQ l) : (P.χQ g : ℚ_[l]) • P.actQ g (tInv P) = tInv P := by
  have h := congrArg (P.actQ g) (tInv_mul P)
  rw [map_mul, map_one, localPrime_galoisAction_periodT, mul_smul_comm, ← smul_mul_assoc] at h
  exact (isUnit_tB P).mul_right_cancel (h.trans (tInv_mul P).symm)

theorem smul_phiB_tInv : (l : ℚ_[l]) • P.φB (tInv P) = tInv P := by
  have h := congrArg P.φB (tInv_mul P)
  rw [map_mul, map_one, localPrime_frobenius_periodT, mul_smul_comm, ← smul_mul_assoc] at h
  exact (isUnit_tB P).mul_right_cancel (h.trans (tInv_mul P).symm)

def tateRep : Representation ℚ_[l] ↥(GK K) (ℚ_[l] × ℚ_[l]) where
  toFun g := LinearMap.prod ((P.χQ (g : GQ l) : ℚ_[l]) • LinearMap.fst ℚ_[l] ℚ_[l] ℚ_[l] +
    (kummer P (g : GQ l) : ℚ_[l]) • LinearMap.snd ℚ_[l] ℚ_[l] ℚ_[l]) (LinearMap.snd ℚ_[l] ℚ_[l] ℚ_[l])
  map_one' := by ext <;> simp
  map_mul' g h := by ext <;> simp [kummer_mul, add_comm]

def tateX : (ℚ_[l] × ℚ_[l]) ⊗[ℚ_[l]] Bst P := (1, 0) ⊗ₜ C (tInv P)

def tateY : (ℚ_[l] × ℚ_[l]) ⊗[ℚ_[l]] Bst P := (0, 1) ⊗ₜ 1 - (1, 0) ⊗ₜ (C (tInv P) * X)

example (ρ : Representation ℚ_[l] ↥(GK K) (Fin 0 → ℚ_[l])) : IsPst P ρ := by
  have : Subsingleton (DpstUr P ρ) := inferInstanceAs (Subsingleton ↥(Dpst P ρ))
  rw [IsPst, rank_subsingleton', rank_subsingleton']

end Examples

end GlobalTheory.Pst
