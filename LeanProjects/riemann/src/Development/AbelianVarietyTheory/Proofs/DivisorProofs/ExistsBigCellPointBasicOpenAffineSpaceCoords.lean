import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenCellChoose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBigCellSectionOverBasicOpenInteriorStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

noncomputable section

namespace GlobalTheory.LogPole

theorem eq_of_eq_lower_mul_upper {S : Type} [CommRing S] {m : ℕ} {M B L N : Matrix (Fin m) (Fin m) S}
    (hB : ∀ i j, i < j → B i j = 0) (hL : ∀ i j, i < j → L i j = 0)
    (hN : ∀ i j, j < i → N i j = 0) (hN1 : ∀ i, N i i = 1)
    (hM : ∀ i j, j < i → M i j = 0) (hM1 : ∀ i, M i i = 1) (h : M = B * (L * N)) : M = N := by
  set C := B * L with hC
  have hClow : ∀ i j, i < j → C i j = 0 := fun i j hij => by
    rw [hC, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge i l with h1 | h1
    · rw [hB i l h1, zero_mul]
    · rw [hL l j (lt_of_le_of_lt h1 hij), mul_zero]
  have hMC : M = C * N := by rw [h, hC, Matrix.mul_assoc]
  have hNt : N.BlockTriangular id := fun i j hij => hN i j hij
  have hdet : IsUnit N.det := by
    rw [Matrix.det_of_upperTriangular hNt]
    simp [hN1]
  have hCM : C = M * N⁻¹ := by
    rw [hMC, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  letI := N.invertibleOfIsUnitDet hdet
  have hMt : M.BlockTriangular id := fun i j hij => hM i j hij
  have hCup : C.BlockTriangular id := hCM ▸ hMt.mul (Matrix.blockTriangular_inv_of_blockTriangular hNt)
  have hC1 : C = 1 := by
    ext i j
    rcases lt_trichotomy i j with h1 | rfl | h1
    · rw [hClow i j h1, Matrix.one_apply_ne h1.ne]
    · have e := congrFun (congrFun hMC i) i
      rw [Matrix.mul_apply, Finset.sum_eq_single i (fun l _ hl => ?_) (by simp), hN1, mul_one, hM1] at e
      · rw [← e, Matrix.one_apply_eq]
      · rcases lt_or_gt_of_ne hl with h2 | h2
        · rw [hCup (show id l < id i from h2), zero_mul]
        · rw [hN l i h2, mul_zero]
    · rw [hCup (show id j < id i from h1), Matrix.one_apply_ne h1.ne']
  rw [hMC, hC1, Matrix.one_mul]

theorem top_le_basicOpen_of_isUnit {S : Type} [CommRing S] {X : Scheme.{0}} (x : Sp S ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) (hu : IsUnit (ev x U h a)) : ⊤ ≤ x ⁻¹ᵁ X.basicOpen a := by
  have hu' : IsUnit ((x.appLE U ⊤ h).hom a) := by
    have : (x.appLE U ⊤ h).hom a = (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (ev x U h a) := by
      show _ = (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom _)
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id]
      rfl
    rw [this]
    exact hu.map _
  have e := Scheme.basicOpen_appLE x ⊤ U h a
  rw [Scheme.basicOpen_of_isUnit _ hu', top_inf_eq] at e
  exact e.le

theorem exists_basicOpen_sub {A : Type} [CommRing A] (O : (Sp A).Opens) (p : Sp A) (hp : p ∈ O) :
    ∃ f : A, f ∉ p.asIdeal ∧ ∀ q : Sp A, f ∉ q.asIdeal → q ∈ O := by
  have hO : IsOpen ((O : Set (Sp A)) : Set (PrimeSpectrum A)) := O.isOpen
  obtain ⟨_, ⟨f, rfl⟩, hpf, hfle⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens (R := A)).exists_subset_of_mem_open
    (a := p) hp hO
  exact ⟨f, hpf, fun q hq => hfle hq⟩

theorem exists_away_sub {R : Type} [CommRing R] (c : R) (O : (Sp (Localization.Away c)).Opens)
    (p : Sp (Localization.Away c)) (hp : p ∈ O) :
    ∃ (h : R) (ι : Localization.Away c →+* Localization.Away (c * h)), ¬ IsNilpotent (c * h) ∧
      (∀ x, ι (algebraMap R _ x) = algebraMap R _ x) ∧ ⊤ ≤ spMap ι ⁻¹ᵁ O := by
  obtain ⟨f, hpf, hfle⟩ := exists_basicOpen_sub O p hp
  obtain ⟨⟨h', s⟩, hs⟩ := IsLocalization.mk'_surjective (Submonoid.powers c) f
  have hfs : f * algebraMap R (Localization.Away c) s.1 = algebraMap R _ h' := by
    rw [← hs]; exact IsLocalization.mk'_spec _ h' s
  let ι : Localization.Away c →+* Localization.Away (c * h') := IsLocalization.Away.awayToAwayRight c h'
  have hι : ∀ x, ι (algebraMap R _ x) = algebraMap R (Localization.Away (c * h')) x :=
    fun x => IsLocalization.Away.awayToAwayRight_eq c h' x
  have hgu : IsUnit (algebraMap R (Localization.Away (c * h')) (c * h')) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hιf : IsUnit (ι f) := by
    have e := congrArg ι hfs
    rw [map_mul, hι, hι] at e
    rw [map_mul] at hgu
    have hh' := isUnit_of_mul_isUnit_right hgu
    rw [← e] at hh'
    exact isUnit_of_mul_isUnit_left hh'
  refine ⟨h', ι, ?_, hι, fun q _ => ?_⟩
  · rintro ⟨m, hm⟩
    have hA : (algebraMap R (Localization.Away c) (c * h')) ^ m ∈ p.asIdeal := by
      rw [← map_pow, hm, map_zero]; exact p.asIdeal.zero_mem
    have hA' := p.isPrime.mem_of_pow_mem _ hA
    rw [map_mul, ← hfs] at hA'
    have hCa : IsUnit (algebraMap R (Localization.Away c) c) := IsLocalization.Away.algebraMap_isUnit _
    have hsu : IsUnit (algebraMap R (Localization.Away c) s.1) := IsLocalization.map_units _ s
    rcases p.isPrime.mem_or_mem hA' with h1 | h1
    · exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 hCa)
    · rcases p.isPrime.mem_or_mem h1 with h2 | h2
      · exact hpf h2
      · exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 hsu)
  · have : f ∉ ((spMap ι) q).asIdeal := fun hq => q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hq hιf)
    exact hfle _ this

theorem not_isNilpotent_of_comp_eq {R T : Type} [CommRing R] [CommRing T] (g : R) (hg : ¬ IsNilpotent g)
    (φ : R →+* T) (ψ : T →+* Localization.Away g) (h : ψ.comp φ = algebraMap R _) : ¬ IsNilpotent (φ g) := by
  rintro ⟨m, hm⟩
  have e : algebraMap R (Localization.Away g) (g ^ m) = 0 := by
    rw [map_pow, ← h, RingHom.comp_apply, ← map_pow, hm, map_zero]
  obtain ⟨⟨_, m', rfl⟩, hm'⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ _).1 e
  exact hg ⟨m' + m, by rw [pow_add]; exact hm'⟩

theorem exists_section_of_away {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (W V : Y.Opens) (hWU : W ≤ f ⁻¹ᵁ U)
    {I : Type} (cc : I → Γ(Y, W)) (a : Γ(X, U)) (ha : f ⁻¹ᵁ X.basicOpen a ≤ V)
    (z₁ : Sp (Localization.Away (MvPolynomial.C a : MvPolynomial I Γ(X, U))) ⟶ Y) (hV : ⊤ ≤ z₁ ⁻¹ᵁ V)
    (hU : ⊤ ≤ (z₁ ≫ f) ⁻¹ᵁ U)
    (hbase : ∀ r, ev (z₁ ≫ f) U hU r = algebraMap (MvPolynomial I Γ(X, U)) _ (MvPolynomial.C r))
    (p : Sp (Localization.Away (MvPolynomial.C a : MvPolynomial I Γ(X, U)))) (hp : p ∈ z₁ ⁻¹ᵁ W)
    (hrel : ∀ (S : Type) [CommRing S] (ψ : Localization.Away (MvPolynomial.C a : MvPolynomial I Γ(X, U)) →+* S)
      (hW : ⊤ ≤ (spMap ψ ≫ z₁) ⁻¹ᵁ W) (i : I),
      ev (spMap ψ ≫ z₁) W hW (cc i) = ψ (algebraMap (MvPolynomial I Γ(X, U)) _ (MvPolynomial.X i))) :
    ∃ g : MvPolynomial I Γ(X, U), ¬ IsNilpotent (MvPolynomial.eval₂Hom (f.appLE U W hWU).hom cc g) ∧
      (∀ (S : Type) [CommRing S] (z₀ : Sp S ⟶ Y) (hz₀ : ⊤ ≤ z₀ ⁻¹ᵁ W),
        IsUnit (ev z₀ W hz₀ (MvPolynomial.eval₂Hom (f.appLE U W hWU).hom cc g)) → ⊤ ≤ z₀ ⁻¹ᵁ V) ∧
      ∃ (z : Sp (Localization.Away g) ⟶ Y) (hz : ⊤ ≤ z ⁻¹ᵁ W), ⊤ ≤ z ⁻¹ᵁ V ∧
        (∀ r, ev z W hz ((f.appLE U W hWU).hom r) =
          algebraMap (MvPolynomial I Γ(X, U)) (Localization.Away g) (MvPolynomial.C r)) ∧
        ∀ i, ev z W hz (cc i) = algebraMap (MvPolynomial I Γ(X, U)) (Localization.Away g) (MvPolynomial.X i) := by
  obtain ⟨h', ι, hnil, hι, hz⟩ := exists_away_sub _ (z₁ ⁻¹ᵁ W) p hp
  have hz' : ⊤ ≤ (spMap ι ≫ z₁) ⁻¹ᵁ W := hz
  have hbz : ∀ r, ev (spMap ι ≫ z₁) W hz' ((f.appLE U W hWU).hom r) =
      algebraMap (MvPolynomial I Γ(X, U)) _ (MvPolynomial.C r) := fun r => by
    rw [FlagMod.ev_appLE (spMap ι ≫ z₁) f hWU hz' (FlagMod.le_preimage_map f hWU hz'),
      FlagMod.ev_congr (Category.assoc _ _ _) U _ (FlagMod.le_preimage_comp (spMap ι) hU),
      FlagMod.ev_spMap ι (z₁ ≫ f) U hU, RingHom.comp_apply, hbase, hι]
  have hcz : ∀ i, ev (spMap ι ≫ z₁) W hz' (cc i) =
      algebraMap (MvPolynomial I Γ(X, U)) _ (MvPolynomial.X i) := fun i => by
    rw [hrel _ ι hz' i, hι]
  refine ⟨MvPolynomial.C a * h', ?_, ?_, spMap ι ≫ z₁, hz', FlagMod.le_preimage_comp _ hV, hbz, hcz⟩
  · refine not_isNilpotent_of_comp_eq _ hnil _ (ev (spMap ι ≫ z₁) W hz') ?_
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      exact hbz r
    · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      exact hcz i
  · intro S _ z₀ hz₀ hu
    rw [map_mul, map_mul] at hu
    have hu1 := isUnit_of_mul_isUnit_left hu
    rw [MvPolynomial.eval₂Hom_C, FlagMod.ev_appLE z₀ f hWU hz₀ (FlagMod.le_preimage_map f hWU hz₀)] at hu1
    have hb := top_le_basicOpen_of_isUnit _ _ _ a hu1
    exact fun q _ => ha (hb (Set.mem_univ q))

theorem map_entry_eq_of_lower_mul {R A S : Type} [CommRing R] [CommRing A] [CommRing S] {m : ℕ} (χ : R →+* S)
    (ε : A →+* S) (t : ∀ i j : Fin m, i < j → R) {L N : Matrix (Fin m) (Fin m) A} {b : Matrix (Fin m) (Fin m) S}
    (hL : ∀ i j, i < j → L i j = 0) (hN : ∀ i j, j < i → N i j = 0) (hN1 : ∀ i, N i i = 1)
    (hb : ∀ i j, i < j → b i j = 0)
    (hbe : ∀ i j, χ (if h : i < j then t i j h else if i = j then 1 else 0) = ∑ k, b i k * ε ((L * N) k j))
    (i j : Fin m) (hij : i < j) : ε (N i j) = χ (t i j hij) := by
  have key := eq_of_eq_lower_mul_upper
    (M := Matrix.of fun i j => χ (if h : i < j then t i j h else if i = j then 1 else 0))
    (B := b) (L := L.map ε) (N := N.map ε) hb
    (fun i j hij => by simp [Matrix.map_apply, hL i j hij])
    (fun i j hij => by simp [Matrix.map_apply, hN i j hij])
    (fun i => by simp [Matrix.map_apply, hN1 i])
    (fun i j hij => by simp [Matrix.of_apply, not_lt.2 hij.le, hij.ne'])
    (fun i => by simp [Matrix.of_apply])
    (by
      ext i j
      rw [Matrix.of_apply, hbe i j, ← Matrix.map_mul, Matrix.mul_apply]
      rfl)
  have e := congrFun (congrFun key i) j
  simp only [Matrix.of_apply, Matrix.map_apply, dif_pos hij] at e
  exact e.symm

theorem exists_cell_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N), Nonempty W → ∃ g : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1), ¬ IsNilpotent (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N) g) ∧ (∀ (S : Type) [CommRing S] (z₀ : Sp S ⟶ Y₀ TF.X Z) (hz₀ : ⊤ ≤ z₀ ⁻¹ᵁ W), IsUnit (ev z₀ W hz₀ (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N) g)) → ⊤ ≤ z₀ ⁻¹ᵁ U₀ TF.X Z) ∧ ∃ (z : Sp (Localization.Away g) ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W), ⊤ ≤ z ⁻¹ᵁ U₀ TF.X Z ∧ (∀ r, ev z W hz (((toBase TF Z).appLE U.1 W h.2.1).hom r) = algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) (Localization.Away g) (MvPolynomial.C r)) ∧ ∀ i, ev z W hz (cellCoord N i) = algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) (Localization.Away g) (MvPolynomial.X i) := by
  intro E _ _ _ H Dw l Xo c TF Z hF U n e v hv W k L N h hWne
  have h1 := exists_basicOpen_cell_choose E H Dw l Xo c TF Z U W k h.2.1 h.2.2.1 hWne
  refine h1.elim fun a ha => ?_
  have h2 := GlobalTheory.T.exists_bigCellSection_over_basicOpen_interior E H Dw l Xo c TF Z hF U n e v hv W k L N h a ha.1 ha.2
  refine h2.elim fun z₁ hz₁ => hz₁.2.1.elim fun hU hbase => hz₁.2.2.1.elim fun p hp => ?_
  refine exists_section_of_away (toBase TF Z) U.1 W (U₀ TF.X Z) h.2.1 (cellCoord N) a ?_ z₁ hz₁.1 hU hbase p hp ?_
  · intro w hw
    have hcomp : toBase TF Z w = TF.X.π w.1 := Scheme.Hom.comp_apply _ _ _
    have hI : toBase TF Z w ∈ LogKS.interior TF.Y := (ha.1 hw).1.1
    rw [hcomp] at hI
    exact hI
  · intro S _ ψ hW i
    refine (hz₁.2.2.2 S ψ hW i.1).elim fun b hb => ?_
    exact map_entry_eq_of_lower_mul (ψ.comp (algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) _))
      (ev (spMap ψ ≫ z₁) W hW) (fun i' j' hij => MvPolynomial.X ⟨i.1, ⟨(i', j'), hij⟩⟩)
      (h.2.2.2.1 i.1) (h.2.2.2.2.2.1 i.1) (h.2.2.2.2.2.2.1 i.1) hb.1 hb.2 i.2.1.1 i.2.1.2 i.2.2

end GlobalTheory.LogPole
