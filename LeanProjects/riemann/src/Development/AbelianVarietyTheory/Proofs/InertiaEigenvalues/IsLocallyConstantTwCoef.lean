import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientRingPadicIntegersFinExt
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
open ReciprocityTheory.Def (Z1 H1)

namespace GlobalTheory.TopSteps.CharAllCoef

section General

variable {O G : Type} [CommRing O] [Group G] [TopologicalSpace G]

theorem exists_mapH1_eq {M' M M'' : Type} [AddCommGroup M'] [Module O M'] [AddCommGroup M] [Module O M]
    [AddCommGroup M''] [Module O M''] {π' : Representation O G M'} {π : Representation O G M}
    {π'' : Representation O G M''} (f : M' →ₗ[O] M) (hf : ∀ g m, f (π' g m) = π g (f m))
    (q : M →ₗ[O] M'') (hq : ∀ g m, q (π g m) = π'' g (q m)) (hfi : Function.Injective f)
    (hqs : Function.Surjective q) (hex : Function.Exact f q)
    (hlc : ∀ m, IsLocallyConstant fun g => π g m) (c : H1 π ⊤) (hc : mapH1 q hq c = 0) :
    ∃ c₀ : H1 π' ⊤, mapH1 f hf c₀ = c := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  obtain ⟨b'', -, hb⟩ := (Submodule.Quotient.mk_eq_zero _).mp hc
  obtain ⟨b, rfl⟩ := hqs b''
  have hb' : ∀ g, π'' g (q b) - q b = q ((z : G → M) g) := fun g => congrFun hb g
  have hr : ∀ g, ∃ y, f y = (z : G → M) g - (π g b - b) := fun g =>
    (hex _).mp (by rw [map_sub, map_sub, hq, hb', sub_self])
  choose w hw using hr
  have hwlc : IsLocallyConstant w := by
    have h1 : IsLocallyConstant fun g => (z : G → M) g - (π g b - b) :=
      z.2.1.1.sub ((hlc b).sub (IsLocallyConstant.const b))
    refine IsLocallyConstant.desc w f ?_ hfi
    have : f ∘ w = fun g => (z : G → M) g - (π g b - b) := funext hw
    rw [this]; exact h1
  refine ⟨Submodule.Quotient.mk ⟨w, ⟨hwlc, fun _ => Submodule.mem_top⟩, ?_⟩, ?_⟩
  · funext x
    change π' x.1 (w x.2) - w (x.1 * x.2) + w x.1 = 0
    apply hfi
    rw [map_add, map_sub, hf, hw, hw, hw, cocycle_mul, map_zero, map_mul]
    simp only [map_sub, Module.End.mul_apply]
    abel
  · refine (Submodule.Quotient.eq _).mpr ⟨-b, Submodule.mem_top, ?_⟩
    funext g
    change π g (-b) - -b = f (w g) - (z : G → M) g
    rw [hw, map_neg]
    abel

theorem exists_res_inj [IsDomain O] [IsDiscreteValuationRing O] {lam : O} (hl : Irreducible lam)
    (X : Type) [AddCommGroup X] [Module O X] [Finite X] [Nontrivial X] :
    ∃ f : (O ⧸ Ideal.span {lam}) →ₗ[O] X, Function.Injective f ∧ f ≠ 0 := by
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {lam} := hl.maximalIdeal_eq
  obtain ⟨x, hx0, hx⟩ : ∃ x : X, x ≠ 0 ∧ lam • x = 0 := by
    by_contra h
    push Not at h
    have hinj : Function.Injective (fun x : X => lam • x) := by
      intro a b hab
      by_contra hne
      exact h (a - b) (sub_ne_zero.mpr hne) (by rw [smul_sub]; exact sub_eq_zero.mpr hab)
    have hsurj := Finite.surjective_of_injective hinj
    have : (⊤ : Submodule O X) = ⊥ := by
      refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {lam}) ⊤ Module.Finite.fg_top ?_ ?_
      · intro y _
        obtain ⟨y', rfl⟩ := hsurj y
        exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
      · rw [← hmax, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact top_ne_bot this
  refine ⟨Submodule.liftQ (Ideal.span {lam}) (LinearMap.toSpanSingleton O X x) ?_, ?_, ?_⟩
  · rw [Ideal.span, Submodule.span_le]
    rintro _ rfl
    exact hx
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hy' : y • x = 0 := hy
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    rw [← hmax]
    intro hu
    exact hx0 (hu.smul_eq_zero.mp hy')
  · intro h
    have : (1 : O) • x = 0 := LinearMap.congr_fun h (Submodule.Quotient.mk 1)
    exact hx0 (by simpa using this)

theorem cls_eq_zero [IsDomain O] [IsDiscreteValuationRing O] {lam : O} (hl : Irreducible lam)
    {M : Type} [AddCommGroup M] [Module O M] [Module.Flat O M] (W : Representation O G M) (χ : G →* Oˣ)
    (cls : ∀ (X : Type) [AddCommGroup X] [Module O X], Set (H1 (twCoef W χ X) ⊤))
    (hlc : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X] (m : M ⊗[O] X),
      IsLocallyConstant fun g => twCoef W χ X g m)
    (h0 : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X], 0 ∈ cls X)
    (hmap : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X]
      (X' : Type) [AddCommGroup X'] [Module O X'] [Finite X'] (f : X →ₗ[O] X') (c : H1 (twCoef W χ X) ⊤),
      (c ∈ cls X → coefH1 W χ f c ∈ cls X') ∧ (Function.Injective f → coefH1 W χ f c ∈ cls X' → c ∈ cls X))
    (hres : ∀ (s : ℕ) (c : Fin s → H1 (twCoef W χ (O ⧸ Ideal.span {lam})) ⊤),
      (∀ a, c a ∈ cls (O ⧸ Ideal.span {lam})) → IndepMod lam c → s ≤ 0)
    (X : Type) [AddCommGroup X] [Module O X] [Finite X] : cls X = {0} := by
  have hk : ∀ c ∈ cls (O ⧸ Ideal.span {lam}), c = 0 := by
    intro c hc
    by_contra hne
    have := hres 1 (fun _ => c) (fun _ => hc) (by
      intro x hx a
      rw [Fin.sum_univ_one] at hx
      rw [Subsingleton.elim a 0, ← Ideal.mem_span_singleton, ← hl.maximalIdeal_eq]
      intro hu
      exact hne (hu.smul_eq_zero.mp hx))
    omega
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨h0 X, ?_⟩
  generalize hn : Nat.card X = n
  induction n using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    intro c hc
    rcases subsingleton_or_nontrivial X with hX | hX
    · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
      have : z = 0 := Subtype.ext (funext fun g => Subsingleton.elim _ _)
      rw [this, Submodule.Quotient.mk_zero]
    · obtain ⟨f, hfi, hf0⟩ := exists_res_inj hl X
      haveI : Finite (O ⧸ Ideal.span {lam}) := Finite.of_injective f hfi
      haveI : Finite (X ⧸ LinearMap.range f) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
      have hlt : Nat.card (X ⧸ LinearMap.range f) < n := by
        rw [← hn, Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)]
        haveI : Nontrivial (LinearMap.range f) :=
          Submodule.nontrivial_iff_ne_bot.mpr (fun h => hf0 (LinearMap.range_eq_bot.mp h))
        have h1 : 1 < Nat.card (LinearMap.range f) := Finite.one_lt_card
        have h2 : 0 < Nat.card (X ⧸ LinearMap.range f) := Nat.card_pos
        nlinarith
      have hq := ih _ hlt (X ⧸ LinearMap.range f) rfl _
        ((hmap X _ (LinearMap.range f).mkQ c).1 hc)
      obtain ⟨c₀, hc₀⟩ := exists_mapH1_eq (π' := twCoef W χ (O ⧸ Ideal.span {lam})) (f.lTensor M)
        (fun g m => by
          induction m using TensorProduct.induction_on with
          | zero => simp
          | tmul a x => simp [coefRep_tmul]
          | add a b ha hb => simp only [map_add, ha, hb])
        ((LinearMap.range f).mkQ.lTensor M) _
        (Module.Flat.lTensor_preserves_injective_linearMap f hfi)
        (LinearMap.lTensor_surjective M (Submodule.mkQ_surjective _))
        (lTensor_exact M (LinearMap.exact_map_mkQ_range f) (Submodule.mkQ_surjective _))
        (hlc X) c hq
      have hc₀' : coefH1 W χ f c₀ = c := hc₀
      have := hk c₀ ((hmap _ X f c₀).2 hfi (hc₀' ▸ hc))
      rw [← hc₀', this, map_zero]

theorem isLocallyConstant_smul {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] O] {Y : Type} [AddCommGroup Y] [Module O Y]
    [Finite Y] (m : Y) : IsLocallyConstant fun a : ℤ_[l] => algebraMap ℤ_[l] O a • m := by
  rw [IsLocallyConstant.iff_exists_open]
  intro a
  have hN : (Nat.card Y : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  refine ⟨Metric.ball a ‖(Nat.card Y : ℤ_[l])‖, Metric.isOpen_ball, Metric.mem_ball_self (norm_pos_iff.mpr hN), ?_⟩
  intro b hb
  rw [mem_ball_iff_norm] at hb
  have hd : (Nat.card Y : ℤ_[l]) ∣ b - a := by
    rcases ValuationRing.dvd_total (Nat.card Y : ℤ_[l]) (b - a) with h | ⟨d, hd⟩
    · exact h
    · exfalso
      rw [hd, norm_mul] at hb
      have := PadicInt.norm_le_one d
      nlinarith [norm_nonneg (b - a)]
  obtain ⟨d, hd⟩ := hd
  rw [← sub_eq_zero, ← sub_smul, ← map_sub, hd, mul_comm, map_mul, mul_smul, map_natCast,
    Nat.cast_smul_eq_nsmul, card_nsmul_eq_zero', smul_zero]

end General

theorem isLocallyConstant_twCoef {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    [Algebra ℤ_[l] O] (Γ : GalData G Qp LL O) (χ : G → ℤ_[l]ˣ) (hc : Continuous χ)
    (hε : ∀ g, (Γ.ε g : O) = algebraMap ℤ_[l] O (χ g)) (c : ℕ)
    (Y : Type) [AddCommGroup Y] [Module O Y] [Finite Y] (m : O ⊗[O] Y) :
    IsLocallyConstant fun g => twCoef (Γ.Wchi c) Γ.χ₁ Y g m := by
  haveI : Finite (O ⊗[O] Y) := Finite.of_equiv _ (TensorProduct.lid O Y).toEquiv.symm
  have hε' : ∀ g, Γ.ε g = Units.map (algebraMap ℤ_[l] O : ℤ_[l] →* O) (χ g) := fun g => Units.ext (hε g)
  have h1 : Continuous fun g : G => (((χ g) ^ (-((c : ℤ) - 1)) : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.continuous_val.comp (hc.zpow _)
  have h2 := (isLocallyConstant_smul (l := l) (O := O) m).comp_continuous h1
  convert h2 using 2 with g
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.twCoef_Wchi, hε', ← map_zpow]
  rfl

theorem exists_eps {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) :
    ∃ χ : S.G → ℤ_[l]ˣ, Continuous χ ∧ ∀ g, (S.Γ.ε g : S.O) = algebraMap ℤ_[l] S.O (χ g) := by
  obtain ⟨χ, hχ, hc, -⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l P
  refine ⟨fun g => χ g, hc.comp continuous_subtype_val, fun g => ?_⟩
  apply Subtype.ext
  have h1 := S.hyp.2.1.2.2.2 g
  have h2 : ((P.PD S.K).χ g : ℚ_[l]) = (P.χQ g : ℚ_[l]) := P.PD_χ S.K g
  rw [h2, ← hχ] at h1
  exact h1

theorem zero_mem {O N : Type} [CommRing O] [AddCommGroup N] [Module O N] {s : Set N}
    (h : ∃ A : Submodule O N, s = A) : 0 ∈ s := by
  obtain ⟨A, rfl⟩ := h
  exact A.zero_mem

theorem cls_eq_zero_of_flat {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) {M : Type} [AddCommGroup M]
    [Module S.O M] [Module.Flat S.O M] (W : Representation S.O S.G M) (hL : S.Lem0 W) (hR : S.ResBound W 0)
    (hlc : ∀ (X : Type) [AddCommGroup X] [Module S.O X] [Finite X] (m : M ⊗[S.O] X),
      IsLocallyConstant fun g => twCoef W S.Γ.χ₁ X g m)
    (X : Type) [AddCommGroup X] [Module S.O X] [Finite X] : S.cls W X = {0} := by
  obtain ⟨⟨hD, hV, -⟩, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
  have hl : Irreducible S.Γ.lam := S.hyp.1.2.2.2.2.2
  exact @cls_eq_zero S.O S.G _ _ _ hD hV _ hl M _ _ _ W S.Γ.χ₁
    (fun X _ _ => S.cls W X) hlc (fun Y _ _ _ => zero_mem (hL Y).1)
    (fun Y _ _ _ Y' _ _ _ f x => (hL Y).2.2 Y' f x) hR X _ _ _

theorem main : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), ∀ c : ℕ, S.Lem0 (S.Γ.Wchi c) → S.ResBound (S.Γ.Wchi c) 0 → ∀ (X : Type) [AddCommGroup X] [Module S.O X] [Finite X], S.cls (S.Γ.Wchi c) X = {0} := by
  intro l _ P S c hL hR X _ _ _
  exact cls_eq_zero_of_flat S _ hL hR
    (fun Y _ _ _ m => (exists_eps S).elim fun χ h => isLocallyConstant_twCoef S.Γ χ h.1 h.2 c Y m) X

end GlobalTheory.TopSteps.CharAllCoef
