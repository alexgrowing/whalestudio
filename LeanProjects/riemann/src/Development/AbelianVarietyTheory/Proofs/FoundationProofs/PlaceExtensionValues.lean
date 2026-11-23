import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.RationalFormValues
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.RationalFormValues

namespace GlobalTheory.Proof.PlaceExtensionValues

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Coef

variable {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} {ι : K →+* K'}
  {I : Type} [Fintype I] {n : ℕ} {lam : I → DomWeight n} {W : Type} [AddCommGroup W] [Module ℂ W]
  {c₀ : VV K lam →ₛₗ[σ] W} {c' : VV K' lam →ₛₗ[σ'] W}

theorem exists_ext_val (hE : IsCoefExt ι lam c₀ c') (v : VV K lam) : ∃ v' : VV K' lam, c' v' = c₀ v :=
  ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV ι lam _ v.2⟩, hE v _ rfl⟩

theorem ext_induction (hE : IsCoefExt ι lam c₀ c') {p : W → Prop} (h0 : ∀ v, p (c₀ v)) (hadd : ∀ x y, p x → p y → p (x + y))
    (hsmul : ∀ (a : K') x, p x → p (σ' a • x)) (v' : VV K' lam) : p (c' v') := by
  have hv : v' ∈ Submodule.span K' (Set.range (bVV K' lam)) := by rw [(bVV K' lam).span_eq]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    obtain ⟨F, hF, hj⟩ := GlobalTheory.Proof.TensorMapDescent.bVVfun_desc ι lam j
    rw [hE ⟨F, hF⟩ (bVV K' lam j) ((bVV_coe _ _ _).trans hj)]
    exact h0 _
  | zero => have := h0 0; rw [map_zero] at this ⊢; exact this
  | add x y _ _ hx hy => rw [map_add]; exact hadd _ _ hx hy
  | smul a x _ hx => rw [map_smulₛₗ]; exact hsmul _ _ hx

theorem ext_stable (hE : IsCoefExt ι lam c₀ c') (T : W →ₗ[ℂ] W) (hT : ∀ v, ∃ u, c₀ u = T (c₀ v)) (v' : VV K' lam) :
    ∃ u', c' u' = T (c' v') := by
  refine ext_induction hE (p := fun w => ∃ u', c' u' = T w) (fun v => ?_) ?_ ?_ v'
  · obtain ⟨u, hu⟩ := hT v
    obtain ⟨u', hu'⟩ := exists_ext_val hE u
    exact ⟨u', hu'.trans hu⟩
  · rintro x y ⟨u, hu⟩ ⟨u', hu'⟩
    exact ⟨u + u', by rw [map_add, map_add, hu, hu']⟩
  · rintro a x ⟨u, hu⟩
    exact ⟨a • u, by rw [map_smulₛₗ, map_smul, hu]⟩

theorem scalar_mem (hσ : σ'.comp ι = σ) (hE : IsCoefExt ι lam c₀ c')
    (hli : LinearIndependent ℂ fun j => c₀ (bVV K lam j)) {z : ℂ} {u v : VV K' lam} (hv : c' v ≠ 0) (h : c' u = z • c' v) :
    ∃ a : K', σ' a = z := by
  classical
  have key : ∀ v' : VV K' lam, ∃ a : VVIdx lam → K', c' v' = ∑ j, σ' (a j) • c₀ (bVV K lam j) := by
    refine ext_induction hE (p := fun w => ∃ a : VVIdx lam → K', w = ∑ j, σ' (a j) • c₀ (bVV K lam j)) (fun v => ?_) ?_ ?_
    · refine ⟨fun j => ι ((bVV K lam).repr v j), ?_⟩
      conv_lhs => rw [← (bVV K lam).sum_repr v, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smulₛₗ, ← RingHom.congr_fun hσ]; rfl
    · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨a + b, by simp [← Finset.sum_add_distrib, add_smul]⟩
    · rintro c _ ⟨a, rfl⟩
      exact ⟨fun j => c * a j, by simp [Finset.smul_sum, mul_smul]⟩
  obtain ⟨a, ha⟩ := key v
  obtain ⟨b, hb⟩ := key u
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hv (by simp [ha, hn])
  have h0 : ∑ j, (σ' (b j) - z * σ' (a j)) • c₀ (bVV K lam j) = 0 := by
    simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, ← ha, ← hb, h, sub_self]
  have h1 := Fintype.linearIndependent_iff.1 hli _ h0 j
  refine ⟨b j / a j, ?_⟩
  rw [map_div₀, div_eq_iff ((map_ne_zero σ').2 hj)]
  exact sub_eq_zero.1 h1

end Coef

section Reps

variable {Gp Γ : Type} [Group Gp] [Group Γ] {ι : Γ →* Gp} {J : Subgroup Gp}

open Classical in

theorem isReps_update {I : Type} {y : I → Gp} (hy : Bridge.IsReps ι J y) (g : Gp) :
    ∃ i, Bridge.IsReps ι J (Function.update y i g) := by
  obtain ⟨i, ⟨γ, k, hg⟩, -⟩ := hy g
  refine ⟨i, fun h => ?_⟩
  have key : ∀ j, (∃ (γ' : Γ) (k' : J), h = ι γ' * Function.update y i g j * k') ↔ ∃ (γ' : Γ) (k' : J), h = ι γ' * y j * k' := by
    intro j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      constructor
      · rintro ⟨γ', k', rfl⟩
        exact ⟨γ' * γ, k * k', by rw [hg]; simp [mul_assoc]⟩
      · rintro ⟨γ', k', rfl⟩
        exact ⟨γ' * γ⁻¹, k⁻¹ * k', by rw [hg]; simp [mul_assoc]⟩
    · rw [Function.update_of_ne hj]
  simp only [key]
  exact hy h

end Reps

section Row

open Formalism.IndefR.FWT

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)
  {K' : Type} [Field K'] {σ' : K' →+* ℂ}

theorem lamV_eq : GlobalTheory.IndefiniteRowSideFullHecke.RationalFormValues.lamV D i = FWT.lamV D i := rfl

theorem formFn_eq (x : A.fam.amb.FL i t) : formFn R i t x = (R.HV i t).e (jVx R i t x) := rfl

theorem isCoefExt_iff_c0BC (jL : D.what₂.LL →+* K') (c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W)
    (c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) :
    IsCoefExt jL (FWT.lamV D i) c₀ c' ↔ CoefficientBaseChange R i jL σ' c₀ c' := by
  constructor
  · intro h v
    exact ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV jL _ _ v.2⟩, rfl, h v _ rfl⟩
  · intro h v v' hv
    obtain ⟨w, hw, hc⟩ := h v
    rw [show v' = w from Subtype.ext (hv.trans hw.symm)]
    exact hc

variable (c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W)

theorem placeEx_iff {Cl : Type} (h : Cl → GA D (Vc D i)) :
    PlaceEx R i t h c' ↔ ∀ (x : A.fam.amb.FL i t) (k : Cl), ∃ v, c' v = formFn R i t x (fin _ (h k)) := by
  constructor
  · intro H x k
    obtain ⟨v, hv⟩ := H x
    exact ⟨v k, (hv k).symm⟩
  · intro H x
    choose v hv using H x
    exact ⟨v, fun k => (hv k).symm⟩

theorem placeEx_of_valuesIn (H : ValuesIn R i t c') {Cl : Type} (h : Cl → GA D (Vc D i)) : PlaceEx R i t h c' :=
  (placeEx_iff R i t c' h).2 fun x k => H x _

theorem valuesIn_iff_forall_placeEx :
    ValuesIn R i t c' ↔ ∀ (Cl : Type) (h : Cl → GA D (Vc D i)), PlaceEx R i t h c' := by
  refine ⟨fun H Cl h => placeEx_of_valuesIn R i t c' H h, fun H x g => ?_⟩
  obtain ⟨h, hh⟩ := (finHom (Vc D i)).rangeRestrict_surjective g
  obtain ⟨v, hv⟩ := (placeEx_iff R i t c' fun _ : Unit => h).1 (H Unit _) x ()
  exact ⟨v, hv.trans (congrArg _ hh)⟩

theorem valuesIn_iff_forall_reps :
    ValuesIn R i t c' ↔ ∀ (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)),
      Bridge.IsReps (Bridge.ratF (Vc D i)) (levJ R i t) (fun k => fin _ (h k)) → PlaceEx R i t h c' := by
  classical
  refine ⟨fun H Cl _ h _ => placeEx_of_valuesIn R i t c' H h, fun H x g => ?_⟩
  obtain ⟨c, hc⟩ := isReps_update (R.B.L i t).pres.reps g
  choose h hh using fun k => (finHom (Vc D i)).rangeRestrict_surjective (Function.update (R.B.L i t).pres.y c g k)
  have hr : Bridge.IsReps (Bridge.ratF (Vc D i)) (levJ R i t) (fun k => fin _ (h k)) := by
    rw [show (fun k => fin _ (h k)) = Function.update (R.B.L i t).pres.y c g from funext hh]
    exact hc
  obtain ⟨v, hv⟩ := (placeEx_iff R i t c' h).1 (@H _ (A.MtCSD i t).finCl h hr) x c
  exact ⟨v, hv.trans (congrArg _ ((hh c).trans (Function.update_self ..)))⟩

def TypeIn (σ' : K' →+* ℂ) (J' : Subgroup (Bridge.Gf (Vc D i))) : Prop :=
  ∀ k : levJ R i t, (k : Bridge.Gf (Vc D i)) ∈ J' → ∃ a : K', σ' a = (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂˣ) : ℂ)

variable {R i t c'}

theorem formFn_law (hV : R.models_HV) (x : A.fam.amb.FL i t) (γ : GQ (Vc D i)) (g : Bridge.Gf (Vc D i)) (k : levJ R i t) :
    formFn R i t x (Bridge.ratF (Vc D i) γ * g * k) =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂˣ) : ℂ) • (R.cV i).coef.ρ γ (formFn R i t x g) := by
  have hm := (hV i t).2.1.le (LinearMap.mem_range_self (R.HV i t).e (R.jV i t x))
  exact hm γ g k

variable {gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E}
  {c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W}
  {c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).coef.W} {jL : D.what₂.LL →+* K'}

theorem valuesIn_iff_placeEx_of_typeIn (hV : R.models_HV)
    (hT : Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (FWT.lamV D)
      gramR c0R c0L) (hc : CoefficientBaseChange R i jL σ' (c0L i) c')
    {Cl : Type} {h : Cl → GA D (Vc D i)} {J' : Subgroup (Bridge.Gf (Vc D i))} (hJ : J' ≤ levJ R i t)
    (hr : Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => fin _ (h k))) (hχ : TypeIn R i t σ' J') :
    ValuesIn R i t c' ↔ PlaceEx R i t h c' := by
  refine ⟨fun H => placeEx_of_valuesIn R i t c' H h, fun H x g => ?_⟩
  obtain ⟨c, ⟨γ, k, hg⟩, -⟩ := hr g
  obtain ⟨v, hv⟩ := (placeEx_iff R i t c' h).1 H x c
  obtain ⟨a, ha⟩ := hχ ⟨k, hJ k.2⟩ k.2
  obtain ⟨γE, hγ⟩ : ∃ γE, Bridge.IsRatMat (Vc D i) γ γE := by
    obtain ⟨g, hg⟩ := γ.2
    exact ⟨g, hg.2.symm⟩
  obtain ⟨u, hu⟩ := ext_stable ((isCoefExt_iff_c0BC R i jL (c0L i) c').2 hc) ((R.cV i).coef.ρ γ)
    (fun w => ⟨_, (hT.mapL i).1 γ γE hγ w⟩) v
  refine ⟨a • u, ?_⟩
  have hl := formFn_law hV x γ (fin _ (h c)) ⟨k, hJ k.2⟩
  rw [map_smulₛₗ, hu, hv, ha, hg]
  exact hl.symm

set_option maxHeartbeats 1000000 in

theorem typeIn_of_valuesIn (hV : R.models_HV)
    (hT : Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (FWT.lamV D)
      gramR c0R c0L) (hσ : σ'.comp jL = D.what₂.embLL) (hc : CoefficientBaseChange R i jL σ' (c0L i) c')
    (hne : ∃ x, formFn R i t x ≠ 0) (H : ValuesIn R i t c') : TypeIn R i t σ' ⊤ := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨g, hg⟩ := Function.ne_iff.1 hx
  intro k _
  obtain ⟨v, hv⟩ := H x g
  obtain ⟨u, hu⟩ := H x (Bridge.ratF (Vc D i) 1 * g * k)
  have h1 : (R.cV i).coef.ρ 1 (formFn R i t x g) = formFn R i t x g :=
    LinearMap.congr_fun (MonoidHom.map_one (R.cV i).coef.ρ) _
  have hl := hu.trans ((formFn_law hV x 1 g k).trans (congrArg (HSMul.hSMul _) (h1.trans hv.symm)))
  have hli : LinearIndependent ℂ fun j => (c0L i (bVV D.what₂.LL (FWT.lamV D i) j) : (R.cV i).W) := (hT.mapL i).2.1
  exact scalar_mem (W := (R.cV i).W) (c₀ := c0L i) (c' := c') (lam := FWT.lamV D i) hσ
    ((isCoefExt_iff_c0BC R i jL (c0L i) c').2 hc) hli (u := u) (v := v) (fun h0 => hg (hv.symm.trans h0)) hl

theorem valuesIn_iff_placeEx_and_typeIn (hV : R.models_HV)
    (hT : Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (FWT.lamV D)
      gramR c0R c0L) (hσ : σ'.comp jL = D.what₂.embLL) (hc : CoefficientBaseChange R i jL σ' (c0L i) c')
    {Cl : Type} {h : Cl → GA D (Vc D i)} {J' : Subgroup (Bridge.Gf (Vc D i))} (hJ : J' ≤ levJ R i t)
    (hr : Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => fin _ (h k))) (hne : ∃ x, formFn R i t x ≠ 0) :
    ValuesIn R i t c' ↔ PlaceEx R i t h c' ∧ TypeIn R i t σ' J' :=
  ⟨fun H => ⟨placeEx_of_valuesIn R i t c' H h, fun k _ => typeIn_of_valuesIn hV hT hσ hc hne H k trivial⟩,
    fun H => (valuesIn_iff_placeEx_of_typeIn hV hT hc hJ hr H.2).2 H.1⟩

theorem typeIn_top_of_placeEx (hV : R.models_HV)
    (hT : Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (FWT.lamV D)
      gramR c0R c0L) (hσ : σ'.comp jL = D.what₂.embLL) (hc : CoefficientBaseChange R i jL σ' (c0L i) c')
    {Cl : Type} {h : Cl → GA D (Vc D i)} {J' : Subgroup (Bridge.Gf (Vc D i))} (hJ : J' ≤ levJ R i t)
    (hr : Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => fin _ (h k))) (hχ : TypeIn R i t σ' J')
    (hne : ∃ x, formFn R i t x ≠ 0) (H : PlaceEx R i t h c') : TypeIn R i t σ' ⊤ :=
  typeIn_of_valuesIn hV hT hσ hc hne ((valuesIn_iff_placeEx_of_typeIn hV hT hc hJ hr hχ).2 H)

variable (R)

def CoefPins (i : Fin D.R.m) (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ) (c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) : Prop :=
  σ'.comp jL = D.what₂.embLL ∧
    ∃ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
      (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L ∧ CoefficientBaseChange R i jL σ' (c0L i) c'

theorem CoefPins.of_thPinsR {v₀ : (R.MW i (sg0 D A)).Vec} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)} {M : ℕ} {Mh : Ideal (𝓞 D.host.E)} {lev : G → La →ₗ[𝓞 D.host.E] La}
    (H : ThPinsR R i jL σ' v₀ c' ι M Mh lev) : CoefPins R i jL σ' c' :=
  ⟨H.field, H.c0⟩

theorem rationalValuesAt_iff_pins : RationalValuesAt R ↔
    ∀ (i : Fin D.R.m) (K' : Type) [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ) (c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W),
      CoefPins R i jL σ' c' → ∀ t, ValuesIn R i t c' := by
  constructor
  · rintro H i K' _ jL σ' c' ⟨hσ, gramR, c0R, c0L, hT, hc⟩ t
    exact H gramR c0R c0L hT i t K' jL σ' hσ c' ((isCoefExt_iff_c0BC R i jL (c0L i) c').2 hc)
  · intro H gramR c0R c0L hT i t K' _ jL σ' hσ c' hc
    exact H i K' jL σ' c' ⟨hσ, gramR, c0R, c0L, hT, (isCoefExt_iff_c0BC R i jL (c0L i) c').1 hc⟩ t

def PlaceAt : Prop :=
  ∀ (i : Fin D.R.m) (K' : Type) [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ) (c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W),
    CoefPins R i jL σ' c' → ∀ (t : T) (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))),
      J' ≤ levJ R i t → Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => fin _ (h k)) → PlaceEx R i t h c'

theorem rationalValuesAt_iff : RationalValuesAt R ↔ PlaceAt R := by
  rw [rationalValuesAt_iff_pins]
  exact ⟨fun H i K' _ jL σ' c' hp t Cl _ h _ _ _ => placeEx_of_valuesIn R i t c' (H i K' jL σ' c' hp t) h,
    fun H i K' _ jL σ' c' hp t => (valuesIn_iff_forall_reps R i t c').2 fun Cl _ h hr => H i K' jL σ' c' hp t Cl h _ le_rfl hr⟩

def PlacePinnedAt : Prop :=
  ∀ (i : Fin D.R.m) (K' : Type) [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ) (c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W),
    CoefPins R i jL σ' c' → ∀ (t : T) (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)) (bad : ℕ)
      (J' : Subgroup (Bridge.Gf (Vc D i))) (Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) (gam : Cl → ℕ) (vol : K'),
      RepsR R i t h bad J' Lh gam vol → PlaceEx R i t h c'

theorem placePinnedAt_of_rationalValuesAt (H : RationalValuesAt R) : PlacePinnedAt R :=
  fun i K' _ jL σ' c' hp t Cl _ h _ J' _ _ _ hr =>
    (rationalValuesAt_iff R).1 H i K' jL σ' c' hp t Cl h J' hr.2.2.1 hr.2.2.2.2.2.1

theorem rationalValuesAt_iff_placePinnedAt (hV : R.models_HV)
    (hex : ∀ i t, ∃ (Cl : Type) (_ : Fintype Cl) (h : Cl → GA D (Vc D i)) (bad : ℕ) (J' : Subgroup (Bridge.Gf (Vc D i)))
      (Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) (gam : Cl → ℕ) (vol : D.what₂.LL),
      RepsR R i t h bad J' Lh gam vol ∧ TypeIn R i t D.what₂.embLL J') :
    RationalValuesAt R ↔ PlacePinnedAt R := by
  refine ⟨placePinnedAt_of_rationalValuesAt R, fun H => (rationalValuesAt_iff_pins R).2 fun i K' _ jL σ' c' hp t => ?_⟩
  obtain ⟨Cl, _, h, bad, J', Lh, gam, vol, ⟨h1, h2, h3, h4, -, h6, h7⟩, hχ⟩ := hex i t
  have hP := H i K' jL σ' c' hp t Cl h bad J' Lh gam _ ⟨h1, h2, h3, h4, rfl, h6, h7⟩
  obtain ⟨hσ, gramR, c0R, c0L, hT, hc⟩ := hp
  refine (valuesIn_iff_placeEx_of_typeIn hV hT hc h3 h6 fun k hk => ?_).2 hP
  obtain ⟨a, ha⟩ := hχ k hk
  exact ⟨jL a, (RingHom.congr_fun hσ a).trans ha⟩

end Row

def PlaceRow : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → PlaceAt R

theorem rationalValues_iff : RationalValues ↔ PlaceRow :=
  ⟨fun H D G _ _ Pl0 T A Ks _ _ _ R F h1 h2 h3 h4 => (rationalValuesAt_iff R).1 (H D G Pl0 T A Ks R F h1 h2 h3 h4),
    fun H D G _ _ Pl0 T A Ks _ _ _ R F h1 h2 h3 h4 => (rationalValuesAt_iff R).2 (H D G Pl0 T A Ks R F h1 h2 h3 h4)⟩

end GlobalTheory.Proof.PlaceExtensionValues

end
