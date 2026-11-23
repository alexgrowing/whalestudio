import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.SchAtlas

open GlobalTheory.AbLaw GlobalTheory.PrimSec

variable {O : Type} [CommRing O] {X : Scheme.{0}}

def subOf (q : X ⟶ Spec (CommRingCat.of O)) (U : X.Opens) : (schFn q).Sub where
  In {B} y := ⊤ ≤ (show Spec B ⟶ X from y) ⁻¹ᵁ U
  in_map {B B'} φ y h := by
    intro p _
    exact h (show (Spec.map φ p : Spec B) ∈ (⊤ : (Spec B).Opens) from trivial)

theorem fromSpec_comp_cst (q : X ⟶ Spec (CommRingCat.of O)) {W : X.Opens} (hW : IsAffineOpen W) :
    hW.fromSpec ≫ q = Spec.map (CommRingCat.ofHom (cst q W)) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec q (isAffineOpen_top _) hW (fun _ _ => trivial),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  congr 1

theorem small_of_affine (q : X ⟶ Spec (CommRingCat.of O)) (V : (schFn q).Sub) {W : X.Opens}
    (hW : IsAffineOpen W)
    (hV : ∀ {B : CommRingCat.{0}} (y : Spec B ⟶ X), V.In (B := B) y ↔ ⊤ ≤ y ⁻¹ᵁ W)
    {d : ℕ} (T : Fin d → Γ(X, W)ˣ)
    (et : (MvPolynomial.eval₂Hom (cst q W) fun k => (T k : Γ(X, W))).Etale) :
    Nonempty (V.fn.Small d) := by
  refine ⟨{ R := Γ(X, W), a := cst q W, T := T, et := et,
            y₀ := ⟨hW.fromSpec, (hV _).2 hW.fromSpec_preimage_self.ge⟩,
            ov := fromSpec_comp_cst q hW,
            univ := ?_ }⟩
  intro B y f _
  have hy : ⊤ ≤ (show Spec B ⟶ X from y.1) ⁻¹ᵁ W := (hV _).1 y.2
  have hr : Set.range (show Spec B ⟶ X from y.1) ⊆ Set.range hW.fromSpec := by
    rintro _ ⟨p, rfl⟩
    exact hW.range_fromSpec.ge (hy (show p ∈ (⊤ : (Spec B).Opens) from trivial))
  refine ⟨(Spec.preimage (IsOpenImmersion.lift hW.fromSpec (show Spec B ⟶ X from y.1) hr)).hom, ?_, ?_⟩
  · refine Subtype.ext ?_
    exact (congrArg (· ≫ hW.fromSpec) (Spec.map_preimage _)).trans (IsOpenImmersion.lift_fac _ _ _)
  · intro g hg
    have h1 : Spec.map (CommRingCat.ofHom g) ≫ hW.fromSpec = (show Spec B ⟶ X from y.1) :=
      congrArg Subtype.val hg
    have h2 : Spec.map (CommRingCat.ofHom g) =
        IsOpenImmersion.lift hW.fromSpec (show Spec B ⟶ X from y.1) hr := by
      rw [← cancel_mono hW.fromSpec, IsOpenImmersion.lift_fac, h1]
    have h3 := Spec.map_injective (h2.trans (Spec.map_preimage _).symm)
    exact congrArg CommRingCat.Hom.hom h3

theorem rs_etale {U W : X.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : W ≤ U) :
    (rs X h).Etale := by
  have h1 := (𝟙 X : X ⟶ X).etale_appLE hU hW h
  have e : (𝟙 X : X ⟶ X).appLE U W h = X.presheaf.map (homOfLE h).op := by
    simp [Scheme.Hom.appLE]
  rw [e] at h1
  exact h1

theorem et_res (q : X ⟶ Spec (CommRingCat.of O)) {U W : X.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) (h : W ≤ U) {d : ℕ} (t : Fin d → Γ(X, U))
    (et : (MvPolynomial.eval₂Hom (cst q U) t).Etale) :
    (MvPolynomial.eval₂Hom (cst q W) fun k => rs X h (t k)).Etale := by
  have e : MvPolynomial.eval₂Hom (cst q W) (fun k => rs X h (t k)) =
      (rs X h).comp (MvPolynomial.eval₂Hom (cst q U) t) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun k => ?_
    · simp [rs_cst]
    · simp
  rw [e]
  exact RingHom.Etale.stableUnderComposition _ _ et (rs_etale hU hW h)

theorem et_shift {R : Type} [CommRing R] (a : O →+* R) {d : ℕ} (t : Fin d → R) (e : Fin d → O)
    (et : (MvPolynomial.eval₂Hom a t).Etale) :
    (MvPolynomial.eval₂Hom a fun k => t k + a (e k)).Etale := by
  let σ : MvPolynomial (Fin d) O →+* MvPolynomial (Fin d) O :=
    MvPolynomial.eval₂Hom MvPolynomial.C fun k => MvPolynomial.X k + MvPolynomial.C (e k)
  let σ' : MvPolynomial (Fin d) O →+* MvPolynomial (Fin d) O :=
    MvPolynomial.eval₂Hom MvPolynomial.C fun k => MvPolynomial.X k - MvPolynomial.C (e k)
  have h1 : σ.comp σ' = RingHom.id _ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun k => ?_ <;> simp [σ, σ']
  have h2 : σ'.comp σ = RingHom.id _ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun k => ?_ <;> simp [σ, σ']
  have hb : Function.Bijective σ := Function.bijective_iff_has_inverse.2
    ⟨σ', fun x => RingHom.congr_fun h2 x, fun x => RingHom.congr_fun h1 x⟩
  have e1 : MvPolynomial.eval₂Hom a (fun k => t k + a (e k)) =
      (MvPolynomial.eval₂Hom a t).comp σ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun k => ?_ <;> simp [σ]
  rw [e1]
  exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective hb) et

theorem exists_unit_chart (q : X ⟶ Spec (CommRingCat.of O)) [Smooth q] (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∃ (n : ℕ) (T : Fin n → Γ(X, U)ˣ),
      (MvPolynomial.eval₂Hom (cst q U) fun k => (T k : Γ(X, U))).Etale := by
  classical
  obtain ⟨V, hV, hx, -, n, φ, hφC, hφ⟩ := exists_etale_chart q (U := ⊤) (x := x) trivial
  let t : Fin n → Γ(X, V) := fun k => φ (MvPolynomial.X k)
  have e0 : φ = MvPolynomial.eval₂Hom (cst q V) t := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun k => ?_
    · simpa using RingHom.congr_fun hφC r
    · simp [t]
  rw [e0] at hφ
  let P : Ideal Γ(X, V) := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have hP : P.IsPrime := (hV.primeIdealOf ⟨x, hx⟩).isPrime
  have hc : ∀ k, ∃ e : O, t k + cst q V e ∉ P := by
    intro k
    by_cases h : t k ∈ P
    · refine ⟨1, fun h' => hP.ne_top ((Ideal.eq_top_iff_one _).2 ?_)⟩
      have := P.sub_mem h' h
      simpa using this
    · exact ⟨0, by simpa using h⟩
  choose e he using hc
  have et := et_shift (cst q V) t e hφ
  let t' : Fin n → Γ(X, V) := fun k => t k + cst q V (e k)
  let h : Γ(X, V) := ∏ k, t' k
  have hh : h ∉ P := by
    intro hm
    obtain ⟨k, -, hk⟩ := (hP.prod_mem_iff).1 hm
    exact he k hk
  have hxW : x ∈ X.basicOpen h := (mem_basicOpen_iff hV ⟨x, hx⟩ h).2 hh
  have hle : X.basicOpen h ≤ V := X.basicOpen_le h
  have hW := hV.basicOpen h
  have hunit : IsUnit (rs X hle h) := RingedSpace.isUnit_res_basicOpen _ h
  have hu : ∀ k, IsUnit (rs X hle (t' k)) := fun k =>
    isUnit_of_dvd_unit (map_dvd (rs X hle) (Finset.dvd_prod_of_mem _ (Finset.mem_univ k))) hunit
  exact ⟨X.basicOpen h, hW, hxW, n, fun k => (hu k).unit, et_res q hV hW hle t' et⟩

theorem exists_unimodular_cover_refining_opens {A : Type} (U : A → X.Opens) (hU : ∀ x : X, ∃ α, x ∈ U α) {B : CommRingCat.{0}}
    (y : Spec B ⟶ X) : ∃ (m : ℕ) (s : Fin m → B), Ideal.span (Set.range s) = ⊤ ∧
      ∀ k (B' : CommRingCat.{0}) (φ : B ⟶ B'), IsUnit (φ.hom (s k)) →
        ∃ α, ⊤ ≤ (Spec.map φ ≫ y) ⁻¹ᵁ U α := by
  classical
  let S : Set B := {s | ∃ α, ∀ p : PrimeSpectrum B, s ∉ p.asIdeal → y p ∈ U α}
  have hS : Ideal.span S = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    let p : PrimeSpectrum B := ⟨M, hM.isPrime⟩
    obtain ⟨α, hα⟩ := hU (y p)
    have hop : IsOpen {p : PrimeSpectrum B | y p ∈ U α} := (y ⁻¹ᵁ U α).isOpen
    obtain ⟨_, ⟨r, rfl⟩, hpr, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show p ∈ {p : PrimeSpectrum B | y p ∈ U α} from hα) hop
    have hr : r ∈ S := ⟨α, fun p' hp' => hsub hp'⟩
    exact hpr (hle (Ideal.subset_span hr))
  obtain ⟨s', hs', hspan⟩ := (Ideal.span_eq_top_iff_finite S).1 hS
  refine ⟨s'.card, fun k => (s'.equivFin.symm k).1, ?_, ?_⟩
  · have : Set.range (fun k => (s'.equivFin.symm k).1) = (s' : Set B) := by
      ext b
      constructor
      · rintro ⟨k, rfl⟩
        exact (s'.equivFin.symm k).2
      · intro hb
        exact ⟨s'.equivFin ⟨b, hb⟩, by simp⟩
    rw [this, hspan]
  · intro k B' φ hu
    obtain ⟨α, hα⟩ := hs' (s'.equivFin.symm k).2
    refine ⟨α, fun p' _ => ?_⟩
    have h1 : (s'.equivFin.symm k).1 ∉ (PrimeSpectrum.comap φ.hom p').asIdeal := fun hm =>
      (p' : PrimeSpectrum B').isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)
    exact hα _ h1

theorem preimage_open_top_of_jacobson_surjection (U : X.Opens) (B B' : CommRingCat.{0}) (φ : B ⟶ B') (y : Spec B ⟶ X)
    (hs : Function.Surjective φ.hom) (hk : RingHom.ker φ.hom ≤ (⊥ : Ideal B).jacobson)
    (h : ⊤ ≤ (Spec.map φ ≫ y) ⁻¹ᵁ U) : ⊤ ≤ y ⁻¹ᵁ U := by
  intro p _
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (p : PrimeSpectrum B).asIdeal (p : PrimeSpectrum B).isPrime.ne_top
  let m : PrimeSpectrum B := ⟨M, hM.isPrime⟩
  have hker : RingHom.ker φ.hom ≤ M := hk.trans (sInf_le ⟨bot_le, hM⟩)
  haveI := hM.isPrime
  let m' : PrimeSpectrum B' := ⟨M.map φ.hom, Ideal.map_isPrime_of_surjective hs hker⟩
  have hm' : PrimeSpectrum.comap φ.hom m' = m := by
    refine PrimeSpectrum.ext ?_
    change Ideal.comap φ.hom (M.map φ.hom) = M
    rw [Ideal.comap_map_of_surjective' _ hs, sup_eq_left]
    exact hker
  have h1 : y m ∈ U := by
    have := h (show (m' : Spec B') ∈ (⊤ : (Spec B').Opens) from trivial)
    rw [← hm']
    exact this
  exact ((PrimeSpectrum.le_iff_specializes _ _).mp hle).mem_open (y ⁻¹ᵁ U).isOpen h1

theorem mem_biInf_of_finite {A : Type} [Finite A] (S : Set A) (U : A → X.Opens) {x : X}
    (h : ∀ β ∈ S, x ∈ U β) : x ∈ ⨅ β ∈ S, U β := by
  let G : X.Opens := ⟨⋂ β ∈ S, (U β : Set X), S.toFinite.isOpen_biInter fun β _ => (U β).isOpen⟩
  have hG : G ≤ ⨅ β ∈ S, U β :=
    le_iInf₂ fun β hβ y hy => Set.mem_iInter₂.1 hy β hβ
  exact hG (Set.mem_iInter₂.2 h)

theorem exists_atlas {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O))
    [Smooth q] [IsSeparated q] [QuasiCompact q] : ∃ d, Nonempty ((schFn q).Atlas d) := by
  classical
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  haveI : X.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← Limits.terminal.comp_from q]
    infer_instance
  choose U hU hx n T et using exists_unit_chart q
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover (fun x => (U x : Set X))
    (fun x _ => (U x).isOpen.mem_nhds (hx x))
  have hcov : ∀ x : X, ∃ α : {x // x ∈ t}, x ∈ U α.1 := by
    intro x
    have := ht.2 (Set.mem_univ x)
    simp only [Set.mem_iUnion] at this
    obtain ⟨a, ha, hxa⟩ := this
    exact ⟨⟨a, ha⟩, hxa⟩
  refine ⟨t.sup n, ⟨⟨{x // x ∈ t}, inferInstance, fun α => subOf q (U α.1),
    fun B y => ?_, fun α B B' φ y hs hk h => ?_, fun S hS => ?_⟩⟩⟩
  · exact exists_unimodular_cover_refining_opens (fun α : {x // x ∈ t} => U α.1) hcov y
  · exact preimage_open_top_of_jacobson_surjection (U α.1) B B' φ y hs hk h
  · obtain ⟨α, hα⟩ := hS
    have hW : IsAffineOpen (⨅ β ∈ S, U (Subtype.val β)) :=
      IsAffineOpen.biInf S S.toFinite ⟨α, hα⟩ fun i _ => hU i.1
    have hle : (⨅ β ∈ S, U (Subtype.val β)) ≤ U α.1 := iInf₂_le α hα
    refine ⟨n α.1, Finset.le_sup α.2, ?_⟩
    refine small_of_affine q _ hW ?_ (fun k => Units.map (rs X hle).toMonoidHom (T α.1 k))
      (et_res q (hU α.1) hW hle _ (et α.1))
    intro B y
    change (∀ β ∈ S, ⊤ ≤ y ⁻¹ᵁ U β.1) ↔ _
    constructor
    · intro h p _
      exact mem_biInf_of_finite S (fun β : {x // x ∈ t} => U β.1)
        fun β hβ => h β hβ (show p ∈ (⊤ : (Spec B).Opens) from trivial)
    · intro h β hβ p hp
      exact (iInf₂_le (f := fun (β : {x // x ∈ t}) (_ : β ∈ S) => U β.1) β hβ) (h hp)

end GlobalTheory.CompanionTheory.SchAtlas
