import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.MemZeroSubCoe
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
import Formalism.SharpRestriction.LevelLetterCocycles.ExpRules

noncomputable section

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2E

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 Formalism.MainNotions.N.Pv.LocalLengthBound TensorProduct
open Formalism.MainNotions.CrystallineLiftingInputs (DL)

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable (W : LocWach PD LL O v n)

theorem filtrationLevel_antitone (T : LocLat G Qp LL O) (i : ZMod n) {a b : ℤ} (hab : a ≤ b) :
    Formalism.MainNotions.WachCoordinates.FilLev W T i 0 b ≤ Formalism.MainNotions.WachCoordinates.FilLev W T i 0 a := by

  have hF : PD.Fil b ≤ PD.Fil a := by
    induction b, hab using Int.le_induction with
    | base => exact le_rfl
    | succ k _ ih => exact (PD.Fil_anti k).trans ih
  unfold Formalism.MainNotions.WachCoordinates.FilLev Formalism.WeaklyAdmissibleFiltrations.FilCris
  apply Submodule.map_mono
  apply Submodule.map_mono
  apply inf_le_inf_right
  apply inf_le_inf_left
  apply Submodule.comap_mono
  unfold Formalism.WeaklyAdmissibleFiltrations.FilV
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v f => exact LinearMap.mem_range.mpr ⟨v ⊗ₜ ⟨f.1, hF f.2⟩, by simp⟩
  | add y z hy hz =>
    rw [map_add]
    exact Submodule.add_mem _ (hy (LinearMap.mem_range_self _ _)) (hz (LinearMap.mem_range_self _ _))

theorem filtration_quotient_finiteDimensional [NeZero n] (hD : Sh.FilDim W) {d : ℕ} {T₁ T₂ : LocLat G Qp LL O}
    {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ} (hDq : DdREqDcris PD LL)
    (hS : SetCS W d T₁ T₂ F b S η m) (i : ZMod n) :
    FiniteDimensional LL ↥((Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 (-(η : ℤ))).map
        (Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 0).mkQ) ∧
      finrank LL ↥((Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 (-(η : ℤ))).map
        (Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 0).mkQ) ≤ m := by
  obtain ⟨hA, -, -, -, -, ⟨-, hcr, -⟩, -, hm, -, -⟩ := hS

  let e : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hA.1
  let τ : K →ₐ[Qp] LL := (W.emb i).comp e.symm.toAlgHom
  have hτ' : τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = W.emb i := by
    ext x
    exact congrArg (W.emb i) (e.symm_apply_apply x)
  have hτ : Formalism.MainNotions.LiftingTheory.Over W τ i := hτ'
  obtain ⟨-, hdiff⟩ := hD hA T₂ hcr i τ hτ
  obtain ⟨hfinE, -, hFR⟩ := (hDq hA.1 T₂.V T₂.ρ hcr).2 τ
  haveI := hfinE

  have hle : ∀ a : ℤ, Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 a ≤ DdRE PD T₂.ρ τ := by
    intro a
    have h1 : Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 a = FildR PD T₂.ρ τ a := by
      rw [hFR a, hτ']
      unfold Formalism.MainNotions.WachCoordinates.FilLev
      rw [Nat.cast_zero, sub_zero, pow_zero]
      congr 1
      exact Submodule.map_id _
    rw [h1]
    exact inf_le_left
  have hfin : ∀ a : ℤ, FiniteDimensional LL (Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 a) := fun a =>
    Module.Finite.of_injective (Submodule.inclusion (hle a)) (Submodule.inclusion_injective (hle a))
  haveI := hfin (-(η : ℤ))
  haveI := hfin 0
  have h0E : Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 0 ≤ Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 (-(η : ℤ)) :=
    filtrationLevel_antitone W T₂ i (by omega)
  let g := (Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 0).mkQ ∘ₗ (Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 (-(η : ℤ))).subtype
  have hrange : (Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 (-(η : ℤ))).map (Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 0).mkQ =
      LinearMap.range g := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hker : LinearMap.ker g =
      (Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 0).comap (Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 (-(η : ℤ))).subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  rw [hker, (Submodule.comapSubtypeEquivOfLe h0E).finrank_eq] at hrn
  have h1 : Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 ((η : ℤ) + 1) ≤ Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 0 :=
    filtrationLevel_antitone W T₂ i (by omega)
  have hmono : finrank LL ↥(Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 ((η : ℤ) + 1)) ≤
      finrank LL ↥(Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 0) := by
    rw [← (Submodule.comapSubtypeEquivOfLe h1).finrank_eq]
    exact Submodule.finrank_le _
  have hsum := hdiff (-(η : ℤ)) ((η : ℤ) + 1) (by omega)
  have hIco : Finset.Ico (-(η : ℤ)) ((η : ℤ) + 1) = Finset.Icc (-(η : ℤ)) (η : ℤ) := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [hIco] at hsum
  have hmm := hm i τ hτ
  rw [hrange]
  refine ⟨inferInstance, ?_⟩
  omega

theorem level_q_pow_ne_zero [NeZero n] (hR : Sh.ExpRing W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (i : ZMod n) (ζ : LL)
    (hζ : IsPrimitiveRoot ζ PD.p) (k : ℕ) : W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ k) ≠ 0 := by

  obtain ⟨⟨u, hu, hq⟩, -, -⟩ := hR hA i ζ hζ
  rw [map_pow, hq]
  exact pow_ne_zero _ (mul_ne_zero hu.ne_zero PowerSeries.X_ne_zero)

private lemma exists_finset_card_le_span_eq_top_of_fg {O₁ L₁ : Type} [CommRing O₁] [IsDomain O₁] [IsPrincipalIdealRing O₁]
    [Field L₁] [Algebra O₁ L₁] [IsFractionRing O₁ L₁] {r : ℕ} (Q : Submodule O₁ (Fin r → L₁))
    (hQ : Q.FG) : ∃ s : Finset Q, s.card ≤ r ∧ Submodule.span O₁ (↑s : Set Q) = ⊤ := by
  haveI : Module.Finite O₁ Q := Module.Finite.iff_fg.mpr hQ
  haveI : Module.Free O₁ Q := Module.free_of_finite_type_torsion_free'
  let bQ := Module.finBasis O₁ Q
  refine ⟨Finset.univ.image bQ, ?_, ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
    have hli : LinearIndependent O₁ (fun j => (bQ j : Fin r → L₁)) :=
      bQ.linearIndependent.map' Q.subtype (Submodule.ker_subtype Q)
    have hli' : LinearIndependent L₁ (fun j => (bQ j : Fin r → L₁)) :=
      (LinearIndependent.iff_fractionRing (R := O₁) (K := L₁)).mp hli
    have h := hli'.fintype_card_le_finrank
    simpa using h
  · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact bQ.span_eq

theorem passage_to_quotient [NeZero n] (hK : Sh.LemK W) (hD : Sh.FilDim W) (hR : Sh.ExpRing W)
    (hE : Sh.ExpRules W) {d : ℕ} {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L}
    {b : ZMod n → ℕ} {S η m : ℕ} (hDq : DdREqDcris PD LL) (hS : SetCS W d T₁ T₂ F b S η m)
    [IsDomain O] [IsPrincipalIdealRing O] [IsFractionRing O LL]
    {FF : Type} [AddCommGroup FF] [Module O FF] [Module.Finite O FF] (F₁ : Submodule O FF)
    (uh : ZMod n → ↥F₁ →ₗ[O] W.DD T₂)
    (hq : ∀ c ∈ evens n d, ∀ f, Formalism.MainNotions.LiftingTheory.qp W ^ η • uh c f ∈ W.N T₂)
    (hdl : ∀ c ∈ evens n d, ∀ f, DL W T₂ (c + 1) (uh c f))
    (hg : ∀ c ∈ evens n d, ∀ f, W.γ T₂ (uh c f) - uh c f ∈ W.N T₂) (lenO : ℕ∞) (cc : ℝ) :
    ∃ F₂ : Submodule O FF, F₂ ≤ F₁ ∧ PChain lenO m cc F₁ F₂ (evens n d).card 0 ∧
      (m = 0 → F₂ = F₁) ∧ ∀ c ∈ evens n d, ∀ f : ↥F₁, (f : FF) ∈ F₂ → uh c f ∈ W.N T₂ := by
  have hS0 := hS
  obtain ⟨hA, -, -, -, ⟨ζ, hζ⟩, ⟨-, hcr, -⟩, -, -, -, -⟩ := hS0

  have key : ∀ c ∈ evens n d, ∃ (r : ℕ) (ψ : ↥F₁ →ₗ[O] (Fin r → LL)), r ≤ m ∧
      ∀ f, ψ f = 0 ↔ uh c f ∈ W.N T₂ := by
    intro c hc
    have hex := fun f : ↥F₁ => (hE hA T₂ hcr (c + 1) ζ hζ).1 (uh c f) _ (hq c hc f)
      (level_q_pow_ne_zero W hR hA (c + 1) ζ hζ η)
    let D : ↥F₁ → ℤ → T₂.V ⊗[Qp] BdR := fun f => (hex f).exists.choose
    have hD1 := fun f : ↥F₁ => (hex f).exists.choose_spec
    have hadd : ∀ f g, D (f + g) = D f + D g := fun f g =>
      (hex (f + g)).unique (hD1 (f + g)) (by
        have h := (hE hA T₂ hcr (c + 1) ζ hζ).2.2.1 _ _ _ _ (hD1 f) (hD1 g)
        rw [← (uh c).map_add f g] at h
        exact h)
    have hsm : ∀ (a : O) f, D (a • f) = fun k => algebraMap O LL a • D f k := fun a f =>
      (hex (a • f)).unique (hD1 (a • f)) (by
        have h := (hE hA T₂ hcr (c + 1) ζ hζ).2.2.2.1 a _ _ (hD1 f)
        rw [← (uh c).map_smul a f] at h
        exact h)
    have hLK : ∀ f, D f 0 ∈ Formalism.MainNotions.WachCoordinates.FilLev W T₂ (c + 1) 0 (-(η : ℤ)) ∧
        (uh c f ∈ W.N T₂ ↔ D f 0 ∈ Formalism.MainNotions.WachCoordinates.FilLev W T₂ (c + 1) 0 0) := fun f =>
      (hK hA T₂ hcr (c + 1) ζ hζ (uh c f) (D f) (hdl c hc f) (hD1 f)
        ⟨0, by rw [pow_zero, one_smul]; exact hg c hc f⟩).2 η (hq c hc f)
    obtain ⟨hfinQ, hrk⟩ := filtration_quotient_finiteDimensional W hD hDq hS (c + 1)
    let Mq := (Formalism.MainNotions.WachCoordinates.FilLev W T₂ (c + 1) 0 (-(η : ℤ))).map
      (Formalism.MainNotions.WachCoordinates.FilLev W T₂ (c + 1) 0 0).mkQ
    haveI hfinQ' : FiniteDimensional LL ↥Mq := hfinQ
    let bas := Module.finBasis LL ↥Mq
    let φ0 : ↥F₁ → ↥Mq := fun f =>
      ⟨(Formalism.MainNotions.WachCoordinates.FilLev W T₂ (c + 1) 0 0).mkQ (D f 0), Submodule.mem_map_of_mem (hLK f).1⟩
    have hφadd : ∀ f g, φ0 (f + g) = φ0 f + φ0 g := fun f g => by
      apply Subtype.ext
      show (Formalism.MainNotions.WachCoordinates.FilLev W T₂ (c + 1) 0 0).mkQ (D (f + g) 0) =
        (Formalism.MainNotions.WachCoordinates.FilLev W T₂ (c + 1) 0 0).mkQ (D f 0) +
          (Formalism.MainNotions.WachCoordinates.FilLev W T₂ (c + 1) 0 0).mkQ (D g 0)
      rw [hadd f g, Pi.add_apply]
      exact map_add _ _ _
    have hφsmul : ∀ (a : O) f, φ0 (a • f) = algebraMap O LL a • φ0 f := fun a f => by
      apply Subtype.ext
      show (Formalism.MainNotions.WachCoordinates.FilLev W T₂ (c + 1) 0 0).mkQ (D (a • f) 0) =
        algebraMap O LL a • (Formalism.MainNotions.WachCoordinates.FilLev W T₂ (c + 1) 0 0).mkQ (D f 0)
      rw [hsm a f]
      exact LinearMap.map_smul _ _ _
    refine ⟨Module.finrank LL ↥Mq,
      { toFun := fun f => bas.equivFun (φ0 f), map_add' := ?_, map_smul' := ?_ }, hrk, ?_⟩
    · intro f g
      show bas.equivFun (φ0 (f + g)) = bas.equivFun (φ0 f) + bas.equivFun (φ0 g)
      rw [hφadd, map_add]
    · intro a f
      show bas.equivFun (φ0 (a • f)) = a • bas.equivFun (φ0 f)
      rw [hφsmul, LinearEquiv.map_smul, algebraMap_smul]
    · intro f
      show bas.equivFun (φ0 f) = 0 ↔ uh c f ∈ W.N T₂
      rw [LinearEquiv.map_eq_zero_iff, (hLK f).2]
      constructor
      · intro h
        have h' : (Formalism.MainNotions.WachCoordinates.FilLev W T₂ (c + 1) 0 0).mkQ (D f 0) = 0 := congrArg Subtype.val h
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h'
        exact h'
      · intro h
        apply Subtype.ext
        show (Formalism.MainNotions.WachCoordinates.FilLev W T₂ (c + 1) 0 0).mkQ (D f 0) = 0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact h

  have main : ∀ l : List (ZMod n), (∀ c ∈ l, c ∈ evens n d) → ∃ (k : ℕ) (Fl : ℕ → Submodule O FF),
      k ≤ l.length ∧ Fl 0 = F₁ ∧ Fl k ≤ F₁ ∧ (∀ i < k, PStep lenO m cc (Fl i) (Fl (i + 1)) True) ∧
      (m = 0 → Fl k = F₁) ∧ ∀ c ∈ l, ∀ f : ↥F₁, (f : FF) ∈ Fl k → uh c f ∈ W.N T₂ := by
    intro l
    induction l with
    | nil =>
      intro _
      exact ⟨0, fun _ => F₁, Nat.zero_le _, rfl, le_rfl, fun i hi => absurd hi (Nat.not_lt_zero _),
        fun _ => rfl, fun c hc => by simp at hc⟩
    | cons a l ih =>
      intro hsub
      obtain ⟨k, Fl, hk, h0, hFl, hstep, hm0, hN⟩ := ih (fun c hc => hsub c (by simp [hc]))
      have haE : a ∈ evens n d := hsub a (by simp)
      obtain ⟨r, ψ, hr, hψ⟩ := key a haE
      let C : Submodule O FF := Fl k ⊓ (LinearMap.ker ψ).map F₁.subtype
      have hnew : PStep lenO m cc (Fl k) C True := by
        let ob0 : ↥(Fl k) →ₗ[O] (Fin r → LL) := ψ ∘ₗ Submodule.inclusion hFl
        haveI : Module.Finite O ↥(Fl k) := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian (Fl k))
        have hfg : (LinearMap.range ob0).FG := by
          rw [LinearMap.range_eq_map]
          exact (Module.finite_def.mp inferInstance).map ob0
        obtain ⟨s, hs, hspan⟩ := exists_finset_card_le_span_eq_top_of_fg (LinearMap.range ob0) hfg
        refine ⟨inf_le_left, ↥(LinearMap.range ob0), inferInstance, inferInstance, ob0.rangeRestrict,
          ?_, fun _ => ⟨s, hs.trans hr, hspan⟩, fun h => absurd trivial h⟩
        intro x
        rw [← LinearMap.mem_ker, LinearMap.ker_rangeRestrict, LinearMap.mem_ker]
        constructor
        · intro h0x
          exact Submodule.mem_inf.mpr ⟨x.2, Submodule.mem_map.mpr
            ⟨Submodule.inclusion hFl x, LinearMap.mem_ker.mpr h0x, rfl⟩⟩
        · intro hx
          obtain ⟨g, hg0, hgx⟩ := Submodule.mem_map.mp (Submodule.mem_inf.mp hx).2
          have hgeq : g = Submodule.inclusion hFl x := Subtype.ext hgx
          rw [hgeq] at hg0
          exact LinearMap.mem_ker.mp hg0
      have hC : m = 0 → C = Fl k := by
        intro h0m
        apply le_antisymm inf_le_left
        intro x hx
        have hxF : x ∈ F₁ := hFl hx
        have hr0 : r = 0 := by omega
        subst hr0
        exact Submodule.mem_inf.mpr ⟨hx, Submodule.mem_map.mpr
          ⟨⟨x, hxF⟩, LinearMap.mem_ker.mpr (Subsingleton.elim _ _), rfl⟩⟩
      refine ⟨k + 1, fun j => if j ≤ k then Fl j else C, by simp only [List.length_cons]; omega,
        ?_, ?_, ?_, ?_, ?_⟩
      · show (if 0 ≤ k then Fl 0 else C) = F₁
        rw [if_pos (Nat.zero_le k)]
        exact h0
      · show (if k + 1 ≤ k then Fl (k + 1) else C) ≤ F₁
        rw [if_neg (by omega)]
        exact inf_le_left.trans hFl
      · intro i hi
        show PStep lenO m cc (if i ≤ k then Fl i else C) (if i + 1 ≤ k then Fl (i + 1) else C) True
        by_cases hik : i < k
        · rw [if_pos hik.le, if_pos (show i + 1 ≤ k by omega)]
          exact hstep i hik
        · have hik' : i = k := by omega
          rw [if_pos (by omega), if_neg (by omega), hik']
          exact hnew
      · intro h0m
        show (if k + 1 ≤ k then Fl (k + 1) else C) = F₁
        rw [if_neg (by omega), hC h0m, hm0 h0m]
      · intro c hc f hf
        have hf' : (f : FF) ∈ C := by
          have h : (f : FF) ∈ (if k + 1 ≤ k then Fl (k + 1) else C) := hf
          rwa [if_neg (by omega)] at h
        rcases List.mem_cons.mp hc with hca | hc'
        · obtain ⟨g, hg0, hgf⟩ := Submodule.mem_map.mp (Submodule.mem_inf.mp hf').2
          have hgeq : g = f := Subtype.ext hgf
          rw [hgeq] at hg0
          rw [hca]
          exact (hψ f).mp (LinearMap.mem_ker.mp hg0)
        · exact hN c hc' f (Submodule.mem_inf.mp hf').1
  obtain ⟨k, Fl, hk, h0, hFl, hstep, hm0, hN⟩ :=
    main (evens n d).toList (fun c hc => Finset.mem_toList.mp hc)
  refine ⟨Fl k, hFl, ⟨k, Fl, Finset.range k, h0, rfl, Finset.Subset.refl _, ?_, ?_, ?_⟩, hm0, ?_⟩
  · rw [Finset.card_range]
    simpa using hk
  · simp
  · intro i hi
    have e : (i ∈ Finset.range k) = True := eq_true (Finset.mem_range.mpr hi)
    rw [e]
    exact hstep i hi
  · intro c hc f hf
    exact hN c (Finset.mem_toList.mpr hc) f hf

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2E

end
