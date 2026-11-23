import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.ComplSmulMapE
import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.AdeleIntA

open NumberField IsDedekindDomain MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Mv

theorem desc_map {K : Type} [Field K] (σ : K →+* ℂ) (k : K) : desc σ (σ k) = k := by
  have hex : ∃ k' : K, σ k' = σ k := ⟨k, rfl⟩
  unfold desc
  rw [dif_pos hex]
  exact σ.injective hex.choose_spec

section Jet

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

theorem jetLin_monomial (J : (DVar ι a b →₀ ℕ) → K) (m : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) (c : K) :
    jetLin J (monomial m c) =
      monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (c * J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have h : (monomial m c : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) =
      c • basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K m := by
    simp only [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul]
  unfold jetLin
  rw [Module.Basis.constr_basis, MvPolynomial.smul_monomial, smul_eq_mul]

theorem jetLin_sum {κ : Type} (s : Finset κ) (J : κ → (DVar ι a b →₀ ℕ) → K) :
    jetLin (fun m => ∑ i ∈ s, J i m) = ∑ i ∈ s, jetLin (J i) := by
  refine (basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).ext fun m => ?_
  unfold jetLin
  simp only [LinearMap.sum_apply, Module.Basis.constr_basis, map_sum]

theorem jetOp_sum {κ : Type} (s : Finset κ) (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (J : κ → (DVar ι a b →₀ ℕ) → K)
    (n : ι → ℕ) : jetOp lam lam' (fun m => ∑ i ∈ s, J i m) n = ∑ i ∈ s, jetOp lam lam' (J i) n := by
  unfold jetOp jetMap
  rw [jetLin_sum]
  refine LinearMap.ext fun P => ?_
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]

end Jet

section Props

variable {X : Fields} (A : Amb X) {a b : ℕ} (Sall SB : Finset (HeightOneSpectrum (𝓞 X.E)))
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
  (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)

theorem isLift_congr (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x x' : HomE X.E a b)
    (h : x - x' ∈ mulLat c (homAt Sall N N')) : A.IsLift Sall N N' c x = A.IsLift Sall N N' c x' := by
  funext s
  unfold Amb.IsLift
  apply propext
  refine and_congr_right fun _ => ?_
  constructor
  · intro h'
    simpa using Submodule.add_mem _ h' h
  · intro h'
    simpa using Submodule.sub_mem _ h' h

theorem mem_divLat_add {E : Type} [Field E] [NumberField E] {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (D c : ℕ) (M : Submodule (𝓞 E) H)
    {x y : H} (hx : x ∈ divLat D M) (hy : y ∈ mulLat c M) : x + y ∈ divLat D M := by
  simp only [divLat, mulLat, Submodule.mem_comap, Submodule.mem_map, LinearMap.smul_apply,
    LinearMap.id_apply] at hx hy ⊢
  obtain ⟨m, hm, rfl⟩ := hy
  rw [smul_add]
  exact M.add_mem hx (M.smul_mem _ (M.smul_mem _ hm))

theorem InRange.add {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} {Sall : Finset (HeightOneSpectrum (𝓞 E))} {D c c₁ : ℕ}
    {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} {x y : HomE E a b} (h : InRange Sall D c N N' x)
    (hy : y ∈ mulLat c₁ (homAt Sall N N')) : InRange Sall D c N N' (x + y) := by
  unfold InRange at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, mem_divLat_add D c₁ _ h.2.2.2.2 hy⟩

theorem mem_divLat_congr {E : Type} [Field E] [NumberField E] {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (D c : ℕ) (M : Submodule (𝓞 E) H)
    {x x' : H} (h : x - x' ∈ mulLat c M) : x ∈ divLat D M ↔ x' ∈ divLat D M := by
  constructor
  · intro hx
    simpa using mem_divLat_add D c M hx (neg_mem h)
  · intro hx'
    simpa using mem_divLat_add D c M hx' h

theorem homAt_gmap_iff {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E)))
    (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (x : HomE E a b) :
    (γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap) ∈ homAt S (gmap γ N) (gmap γ' N') ↔ x ∈ homAt S N N' := by
  constructor
  · intro h P hP y hy
    have h1 := h P hP (γ y) ((mem_localization_gmap P γ N _).2 (by simpa using hy))
    have h2 := (mem_localization_gmap P γ' N' _).1 h1
    simpa using h2
  · intro h P hP y hy
    have h1 := h P hP (γ.symm y) ((mem_localization_gmap P γ N _).1 hy)
    exact (mem_localization_gmap P γ' N' _).2 (by simpa using h1)

theorem divLat_gmap_iff {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) (D : ℕ)
    (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (x : HomE E a b) :
    (γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap) ∈ divLat D (homAt S (gmap γ N) (gmap γ' N')) ↔ x ∈ divLat D (homAt S N N') := by
  simp only [divLat, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
  rw [← homAt_gmap_iff S γ γ' N N' ((D : 𝓞 E) • x)]
  have e : (D : 𝓞 E) • (γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap) =
      γ'.toLinearMap ∘ₗ ((D : 𝓞 E) • x) ∘ₗ γ.symm.toLinearMap := by
    rw [← algebraMap_smul E (D : 𝓞 E), ← algebraMap_smul E (D : 𝓞 E) x, LinearMap.smul_comp, LinearMap.comp_smul]
  rw [e]

variable (D : ℕ)

theorem thDistC_cong (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB)
    (c : ℕ) (x x' : HomE X.E a b) (h : x - x' ∈ mulLat c (homAt Sall N N')) :
    thDistC A Sall SB D sel mU mI lam lam' n N fr N' fr' c x = thDistC A Sall SB D sel mU mI lam lam' n N fr N' fr' c x' := by
  have h1 : A.thInd Sall N N' c x = A.thInd Sall N N' c x' := by
    unfold Amb.thInd Amb.liftW
    rw [isLift_congr A Sall N N' c x x' h]
  have h2 : (c ∣ D ∧ x ∈ divLat D (homAt Sall N N')) = (c ∣ D ∧ x' ∈ divLat D (homAt Sall N N')) := by
    rw [mem_divLat_congr D c _ h]
  unfold thDistC Amb.jetK
  by_cases hx : c ∣ D ∧ x ∈ divLat D (homAt Sall N N')
  · rw [if_pos hx, if_pos (h2 ▸ hx), h1]
  · rw [if_neg hx, if_neg (h2 ▸ hx)]

theorem thDistC_det (sS sT : SB → X.E → X.K) (ha : MuDetLaw a mI sS) (hb : MuDetLaw b mI sS) (hi : UnitInv sS sT)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB)
    (c : ℕ) (x : HomE X.E a b) (κ : ∀ P : SB, ↥(GLint X.E a P.1)) (κ' : ∀ P : SB, ↥(GLint X.E b P.1)) :
    thDistC A Sall SB D sel mU mI lam lam' n N (fun P => fr P * (κ P).1) N' (fun P => fr' P * (κ' P).1) c x =
      (∏ P : SB, sS P (LinearEquiv.det (κ P).1 : X.Eˣ) * sT P (LinearEquiv.det (κ' P).1 : X.Eˣ)) •
        thDistC A Sall SB D sel mU mI lam lam' n N fr N' fr' c x := by
  have e1 : ∀ P : SB, mI P ((LinearEquiv.det (fr P * (κ P).1) : X.Eˣ) : X.E) =
      mI P ((LinearEquiv.det (fr P) : X.Eˣ) : X.E) * sS P ((LinearEquiv.det (κ P).1 : X.Eˣ) : X.E) :=
    fun P => ha P (fr P) (κ P)
  have e2 : ∀ P : SB, mI P ((LinearEquiv.det (fr' P * (κ' P).1) : X.Eˣ) : X.E) =
      mI P ((LinearEquiv.det (fr' P) : X.Eˣ) : X.E) * sS P ((LinearEquiv.det (κ' P).1 : X.Eˣ) : X.E) :=
    fun P => hb P (fr' P) (κ' P)
  have e3 : ∀ (P : SB) (y : X.E), sT P y = (sS P y)⁻¹ := hi
  unfold thDistC
  split_ifs
  · rw [smul_smul]
    congr 1
    unfold muInvDet
    simp only [e1, e2, e3, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    ring
  · rw [smul_zero]

theorem jetAdd_of (hfin : LatFin (X := X) a b Sall) (hadd : A.IndAdd a b Sall D) (hsm : A.IndSmooth a b Sall D)
    (hrat : A.JetsRat a b Sall D) : A.JetAdd a b Sall D := by
  intro N N' c c' x hc hc' hR m
  have := hfin N N' c c' hR.1 hR.2.1 hc hc'
  let _ := Fintype.ofFinite (↥(mulLat c (homAt Sall N N')) ⧸ (mulLat (c * c') (homAt Sall N N')).comap (mulLat c (homAt Sall N N')).subtype)
  unfold latSum
  rw [finsum_eq_sum_of_fintype]
  set rep := fun z : ↥(mulLat c (homAt Sall N N')) ⧸ (mulLat (c * c') (homAt Sall N N')).comap (mulLat c (homAt Sall N N')).subtype =>
    ((Function.surjInv (Submodule.Quotient.mk_surjective ((mulLat (c * c') (homAt Sall N N')).comap (mulLat c (homAt Sall N N')).subtype)) z :
      ↥(mulLat c (homAt Sall N N'))) : HomE X.E a b) with hrep
  have hRz : ∀ z, InRange Sall D (c * c') N N' (x + rep z) := fun z => hR.add (Subtype.coe_prop _)
  have h1 : A.thInd Sall N N' c x = fun w => ∑ z, A.thInd Sall N N' (c * c') (x + rep z) w := by
    funext w
    rw [hadd N N' c c' x hc hc' hR w]
    unfold latSum
    rw [finsum_eq_sum_of_fintype]
  have h2 : derivAt0 (A.thInd Sall N N' c x) m = ∑ z, derivAt0 (A.thInd Sall N N' (c * c') (x + rep z)) m := by
    unfold derivAt0
    rw [h1, iteratedFDeriv_sum (fun z _ => hsm N N' (c * c') (x + rep z) (hRz z) _)]
    rw [Finset.sum_apply, _root_.sum_apply]
  choose k hk using fun z => hrat N N' (c * c') (x + rep z) (hRz z) m
  have h3 : (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' c x) m = A.σ₀ (∑ z, k z) := by
    rw [map_sum]
    simp only [hk]
    unfold jetC
    rw [h2, Finset.mul_sum, Finset.mul_sum]
  unfold Amb.jetK
  rw [h3, desc_map]
  refine Finset.sum_congr rfl fun z _ => ?_
  show k z = desc A.σ₀ ((A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' (c * c') (x + rep z)) m)
  rw [← hk z, desc_map]

theorem thDistC_add (hfin : LatFin (X := X) a b Sall) (hadd : A.JetAdd a b Sall D)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB)
    (c c' : ℕ) (x : HomE X.E a b) (hc : 0 < c) (hc' : 0 < c') (hR : InRange Sall D (c * c') N N' x) :
    thDistC A Sall SB D sel mU mI lam lam' n N fr N' fr' c x =
      latSum (mulLat c (homAt Sall N N')) (mulLat (c * c') (homAt Sall N N')) fun y =>
        thDistC A Sall SB D sel mU mI lam lam' n N fr N' fr' (c * c') (x + y) := by
  have := hfin N N' c c' hR.1 hR.2.1 hc hc'
  let _ := Fintype.ofFinite (↥(mulLat c (homAt Sall N N')) ⧸ (mulLat (c * c') (homAt Sall N N')).comap (mulLat c (homAt Sall N N')).subtype)
  have hJ : A.jetK Sall N N' c x = fun m => ∑ z : ↥(mulLat c (homAt Sall N N')) ⧸ (mulLat (c * c') (homAt Sall N N')).comap (mulLat c (homAt Sall N N')).subtype,
      A.jetK Sall N N' (c * c') (x + ((Function.surjInv (Submodule.Quotient.mk_surjective
        ((mulLat (c * c') (homAt Sall N N')).comap (mulLat c (homAt Sall N N')).subtype)) z : ↥(mulLat c (homAt Sall N N'))) : HomE X.E a b)) m := by
    funext m
    rw [hadd N N' c c' x hc hc' hR m]
    unfold latSum
    rw [finsum_eq_sum_of_fintype]
  unfold latSum
  rw [finsum_eq_sum_of_fintype]
  unfold thDistC
  rw [if_pos ⟨(Dvd.intro _ rfl).trans hR.2.2.2.1, hR.2.2.2.2⟩, hJ, jetOp_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  exact (if_pos ⟨hR.2.2.2.1, mem_divLat_add D c _ hR.2.2.2.2 (Subtype.coe_prop _)⟩).symm

theorem thDistC_equiv (hD : 0 < D) (rho : UF X.E a →* Module.End X.K (DIV.VV X.K lam)) (rho' : UF X.E b →* Module.End X.K (DIV.VV X.K lam'))
    (heq : ThEquivP (thDistC A Sall SB D sel mU mI lam lam' n) Sall D rho rho')
    (γ : UF X.E a) (γ' : UF X.E b) (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB)
    (c : ℕ) (x : HomE X.E a b) (hN : IsSdLat N) (hN' : IsSdLat N') :
    thDistC A Sall SB D sel mU mI lam lam' n (gmap γ.1 N) (fun P => γ.1 * fr P) (gmap γ'.1 N') (fun P => γ'.1 * fr' P) c
        (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) =
      (rho' γ') ∘ₗ (thDistC A Sall SB D sel mU mI lam lam' n N fr N' fr' c x) ∘ₗ (rho γ⁻¹) := by
  by_cases hR : c ∣ D ∧ x ∈ divLat D (homAt Sall N N')
  · exact heq γ γ' N fr N' fr' c x ⟨hN, hN', Nat.pos_of_dvd_of_pos hR.1 hD, hR.1, hR.2⟩
  · have hR' : ¬ (c ∣ D ∧ (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) ∈ divLat D (homAt Sall (gmap γ.1 N) (gmap γ'.1 N'))) := by
      rw [divLat_gmap_iff]; exact hR
    unfold thDistC
    rw [if_neg hR, if_neg hR', LinearMap.zero_comp, LinearMap.comp_zero]

theorem thDistC_ok (hD : 0 < D) (rho : UF X.E a →* Module.End X.K (DIV.VV X.K lam)) (rho' : UF X.E b →* Module.End X.K (DIV.VV X.K lam'))
    (sS sT : SB → X.E → X.K) (hfin : LatFin (X := X) a b Sall) (hadd : A.JetAdd a b Sall D)
    (heq : ThEquivP (thDistC A Sall SB D sel mU mI lam lam' n) Sall D rho rho')
    (ha : MuDetLaw a mI sS) (hb : MuDetLaw b mI sS) (hi : UnitInv sS sT) :
    ThDist.Ok (thDistC A Sall SB D sel mU mI lam lam' n) Sall D rho rho' sS sT where
  cong := fun N fr N' fr' c x x' _ _ h => thDistC_cong A Sall SB sel mU mI lam lam' n D N fr N' fr' c x x' h
  add := fun N fr N' fr' c c' x hN hN' hc hc' hd hx =>
    thDistC_add A Sall SB sel mU mI lam lam' n D hfin hadd N fr N' fr' c c' x hc hc' ⟨hN, hN', Nat.mul_pos hc hc', hd, hx⟩
  equiv := thDistC_equiv A Sall SB sel mU mI lam lam' n D hD rho rho' heq
  det := fun N fr N' fr' c x κ κ' _ _ => thDistC_det A Sall SB sel mU mI lam lam' n D sS sT ha hb hi N fr N' fr' c x κ κ'

end Props

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

theorem unitV_inv {E K : Type} [Field E] [NumberField E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
    (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (x : E) : LocE.unitV χ⁻¹ x = (LocE.unitV χ x)⁻¹ := by
  unfold LocE.unitV
  split_ifs with h
  · simp
  · simp

theorem unitInv_rho (i : ℕ) : UnitInv (rhoS Ch sel mu i) (rhoT Ch sel mu i) := by
  intro P x
  unfold rhoS rhoT
  split_ifs with h
  · exact unitV_inv _ x
  · rw [unitV_inv, inv_inv]

variable {u : Pr.Word} {m2 : ℕ} (T : ChTh W sel mu u m2) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)

theorem chKer_mat (P : LevFam X.E X.K R.r Pr.vGs) (hM : MatEquiv W Ch sel mu cst L T) (h1 : Cp1Equiv W Ch sel mu cst L T b hY)
    (h2 : Cp2Equiv W Ch sel mu cst L T b hY P) (i : ℕ) (hi : i < m2) (al : L.β i) (be : L.β (i + 1))
    (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1)) :
    ((chKer W Ch sel mu cst L T b hY P hM h1 h2).kk i al be).k p p' =
      kerOf (T.th i) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (frsF sel mu p)
        p'.deco.1.N (frsF sel mu p') (XiEntry Ch sel mu cst L i al be p p') := by
  show ((if h : i < m2 then ClsKer.mk (matK W Ch sel mu cst L T i al be) (hM i h al be) else zeroKer _ _ :
    ClsKer ((chF W sel mu L u i).mem al) ((chF W sel mu L u (i + 1)).mem be))).k p p' = _
  rw [dif_pos hi]
  rfl

theorem chainKernel_penultimate_eq_on (P : LevFam X.E X.K R.r Pr.vGs) (hM : MatEquiv W Ch sel mu cst L T) (h1 : Cp1Equiv W Ch sel mu cst L T b hY)
    (h2 : Cp2Equiv W Ch sel mu cst L T b hY P) (al : L.β m2) (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1))
    (Y : Set (Sp X.E (R.N (m2 + 1)))) (hYm : Y ∈ ybSet sel mu cst p.deco.1.N) :
    ((chKer W Ch sel mu cst L T b hY P hM h1 h2).cp al).k1 p₀ p Y =
      kerOf (T.th m2) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p₀.deco.1.N (frsF sel mu p₀)
        p.deco.1.N (frsF sel mu p) (XiCpl1 Ch sel mu cst L m2 al p₀ p Y) :=
  if_pos hYm

theorem chainKernel_coupled_eq_on (P : LevFam X.E X.K R.r Pr.vGs) (hM : MatEquiv W Ch sel mu cst L T) (h1 : Cp1Equiv W Ch sel mu cst L T b hY)
    (h2 : Cp2Equiv W Ch sel mu cst L T b hY P) (al : L.β m2) (p : ChPt (R := R) sel mu u (m2 + 1))
    (Y : Set (Sp X.E (R.N (m2 + 1)))) (d : RowPt Pr R sel mu) (hYm : Y ∈ ybSet sel mu cst p.deco.1.N) :
    ((chKer W Ch sel mu cst L T b hY P hM h1 h2).cp al).k2 p Y d =
      kerOf T.top (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (frsF sel mu p)
        (tilQ sel mu u d).1.N (frsT sel mu u d) (XiCpl2 Ch sel mu cst m2 p Y d) :=
  if_pos hYm

theorem chKer_shape (P : LevFam X.E X.K R.r Pr.vGs) (hM : MatEquiv W Ch sel mu cst L T) (h1 : Cp1Equiv W Ch sel mu cst L T b hY)
    (h2 : Cp2Equiv W Ch sel mu cst L T b hY P)
    (hlev : (cst.sharp = false ∧ P = rP0 Ch) ∨ (cst.sharp = true ∧ P = rPsymF Ch)) :
    (chKer W Ch sel mu cst L T b hY P hM h1 h2).Shape T where
  lev := hlev
  mat i hi al be p p' := chKer_mat W Ch sel mu cst L T b hY P hM h1 h2 i hi al be p p'
  cp1 al p₀ p Y hYm := chainKernel_penultimate_eq_on W Ch sel mu cst L T b hY P hM h1 h2 al p₀ p Y hYm
  cp2 al p Y d hYm := chainKernel_coupled_eq_on W Ch sel mu cst L T b hY P hM h1 h2 al p Y d hYm

end Chain

section Units

variable {E K : Type} [Field E] [NumberField E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem isUnit_reduction_of_integralAt_inv {u : E} (hu : IntAt P u) (hu' : IntAt P u⁻¹) (h0 : u ≠ 0) : IsUnit (redP P u) := by
  have hu1 : redP P u * redP P u⁻¹ = 1 := by
    rw [← reduction_mul hu hu', mul_inv_cancel₀ h0]
    have := reduction_coe P (1 : 𝓞 E)
    simpa using this
  exact IsUnit.of_mul_eq_one _ hu1

theorem intAt_of_isUnit {y : E} (h : IsUnit (redP P y)) : IntAt P y := by
  by_contra hn
  rw [reduction_eq_zero_of_not_integral P hn] at h
  exact not_isUnit_zero h

theorem isUnit_reduction_mul_iff {u : E} (hu : IntAt P u) (hu' : IntAt P u⁻¹) (h0 : u ≠ 0) (y : E) :
    IsUnit (redP P (y * u)) ↔ IsUnit (redP P y) := by
  constructor
  · intro h
    have hy : IntAt P y := by
      have := (intAt_of_isUnit h).mul hu'
      rwa [mul_assoc, mul_inv_cancel₀ h0, mul_one] at this
    rw [reduction_mul hy hu] at h
    exact isUnit_of_mul_isUnit_left h
  · intro h
    rw [reduction_mul (intAt_of_isUnit h) hu]
    exact h.mul (isUnit_reduction_of_integralAt_inv hu hu' h0)

theorem unitV_mul_unit (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {u : E} (hu : IntAt P u) (hu' : IntAt P u⁻¹) (h0 : u ≠ 0) (y : E) :
    LocE.unitV χ (y * u) = LocE.unitV χ y * LocE.unitV χ u := by
  unfold LocE.unitV
  have hU := isUnit_reduction_of_integralAt_inv hu hu' h0
  by_cases h : IsUnit (redP P y)
  · have h1 := (isUnit_reduction_mul_iff hu hu' h0 y).2 h
    rw [dif_pos h, dif_pos h1, dif_pos hU, ← Units.val_mul, ← map_mul]
    congr 2
    apply Units.ext
    simp [reduction_mul (intAt_of_isUnit h) hu]
  · have h1 : ¬ IsUnit (redP P (y * u)) := fun h' => h ((isUnit_reduction_mul_iff hu hu' h0 y).1 h')
    rw [dif_neg h, dif_neg h1, zero_mul]

theorem valuation_mul_unit (q : ℕ) {u : E} (hu : IntAt P u) (hu' : IntAt P u⁻¹) (h0 : u ≠ 0) (y : E) :
    LocE.vP P q (y * u) = LocE.vP P q y := by
  unfold LocE.vP
  congr 1
  funext z
  rw [mul_div_right_comm, isUnit_reduction_mul_iff hu hu' h0]

theorem locChar_mul_unit (q : ℕ) (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {u : E} (hu : IntAt P u) (hu' : IntAt P u⁻¹) (h0 : u ≠ 0)
    (y : E) : LocE.locChar q cq χ (y * u) = LocE.locChar q cq χ y * LocE.unitV χ u := by
  unfold LocE.locChar
  rw [valuation_mul_unit q hu hu' h0, mul_div_right_comm, unitV_mul_unit χ hu hu' h0, mul_assoc]

def intSub (P : HeightOneSpectrum (𝓞 E)) : Subring E where
  carrier := {a | IntAt P a}
  mul_mem' := IntAt.mul
  add_mem' := IntAt.add
  one_mem' := by simpa using IntAt.coe P (1 : 𝓞 E)
  zero_mem' := by simpa using IntAt.coe P (0 : 𝓞 E)
  neg_mem' := fun {a} h => by
    have := (IntAt.coe P (-1 : 𝓞 E)).mul h
    simpa using this

theorem intAt_det [StarRing E] {n : ℕ} (κ : Sp E n ≃ₗ[E] Sp E n) (hκ : κ ∈ GLint E n P) : IntAt P ((LinearEquiv.det κ : Eˣ) : E) := by
  have hent : ∀ i j, IntAt P (LinearMap.toMatrix' κ.toLinearMap i j) := by
    intro i j
    have h1 : (Pi.single j 1 : Sp E n) ∈ stdAt E n P := by
      refine (mem_localization_standardLattice P _).2 fun k => ?_
      by_cases hk : k = j
      · subst hk; simpa using IntAt.coe P (1 : 𝓞 E)
      · simpa [Pi.single_apply, hk] using IntAt.coe P (0 : 𝓞 E)
    have h2 := (mem_localization_standardLattice P _).1 ((hκ _).2 h1) i
    simpa [LinearMap.toMatrix'_apply] using h2
  have hM : LinearMap.toMatrix' κ.toLinearMap =
      (intSub P).subtype.mapMatrix (Matrix.of fun i j => (⟨LinearMap.toMatrix' κ.toLinearMap i j, hent i j⟩ : intSub P)) := by
    ext i j; rfl
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix', hM, ← RingHom.map_det]
  exact (Matrix.of fun i j => (⟨LinearMap.toMatrix' κ.toLinearMap i j, hent i j⟩ : intSub P)).det.2

theorem intAt_det_inv [StarRing E] {n : ℕ} (κ : Sp E n ≃ₗ[E] Sp E n) (hκ : κ ∈ GLint E n P) : IntAt P ((LinearEquiv.det κ : Eˣ) : E)⁻¹ := by
  have := intAt_det κ⁻¹ ((GLint E n P).inv_mem hκ)
  rwa [map_inv, Units.val_inv_eq_inv_val] at this

end Units

section Units2

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem muDetLaw_chain (i n : ℕ) : MuDetLaw n (muAt Ch sel mu cst i) (rhoS Ch sel mu i) := by
  intro P f κ
  rw [map_mul, Units.val_mul]
  unfold muAt rhoS
  exact locChar_mul_unit _ _ _ (intAt_det κ.1 κ.2) (intAt_det_inv κ.1 κ.2) (Units.ne_zero _) _

end Units2

section Tests

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

private theorem comapDomain_inl_mapDomain_add (p : (ι × Fin b × Fin b) →₀ ℕ) (m : DVar ι a b →₀ ℕ) :
    (p.mapDomain Sum.inl + m.mapDomain Sum.inr).comapDomain Sum.inl Sum.inl_injective.injOn = p := by
  ext v
  rw [Finsupp.comapDomain_apply, Finsupp.add_apply, Finsupp.mapDomain_apply Sum.inl_injective,
    Finsupp.mapDomain_notin_range (f := Sum.inr) m (Sum.inl v) (by simp), add_zero]

private theorem comapDomain_inr_mapDomain_add (p : (ι × Fin b × Fin b) →₀ ℕ) (m : DVar ι a b →₀ ℕ) :
    (p.mapDomain Sum.inl + m.mapDomain Sum.inr).comapDomain Sum.inr Sum.inr_injective.injOn = m := by
  ext v
  rw [Finsupp.comapDomain_apply, Finsupp.add_apply, Finsupp.mapDomain_notin_range (f := Sum.inl) p (Sum.inr v) (by simp),
    Finsupp.mapDomain_apply Sum.inr_injective, zero_add]

theorem jetLin_mixed (J : (DVar ι a b →₀ ℕ) → K) (p : (ι × Fin b × Fin b) →₀ ℕ) (m : DVar ι a b →₀ ℕ) (c : K) :
    jetLin J (monomial (p.mapDomain Sum.inl + m.mapDomain Sum.inr) c) = monomial p (c * J m) := by
  rw [jetLin_monomial, comapDomain_inl_mapDomain_add, comapDomain_inr_mapDomain_add]

theorem jetMap_one (J : (DVar ι a b →₀ ℕ) → K) : jetMap J (fun _ => 0) (1 : Pol K ι a) = C (J 0) := by
  unfold jetMap
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, pow_zero, Finset.prod_const_one, mul_one,
    AlgHom.toLinearMap_apply, map_one]
  rw [← MvPolynomial.C_1, MvPolynomial.C_apply, jetLin_monomial]
  simp only [Finsupp.comapDomain_zero, one_mul, MvPolynomial.C_apply]

end Tests

section Tests2

variable {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E)))
  (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))

theorem opU_smul {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (x : V) (k : ℂ) (F : V → ℂ) (z : V) :
    opU H x (fun w => k * F w) z = k * opU H x F z := by
  unfold opU; ring

end Tests2

section Smooth

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem contDiff_opU (H : Sesq (VCx ι a b)) (x : VCx ι a b) (F : VCx ι a b → ℂ) (k : ℕ) (hF : ContDiff ℂ k F) :
    ContDiff ℂ k (opU H x F) := by
  unfold opU
  have h1 : ContDiff ℂ k fun z : VCx ι a b => F (z + x) := hF.comp (contDiff_id.add contDiff_const)
  have h2 : ContDiff ℂ k fun z : VCx ι a b => H z x :=
    (LinearMap.toContinuousLinearMap (H.flip x)).contDiff
  exact h1.mul (Complex.contDiff_exp.comp (((contDiff_const.mul h2)).sub contDiff_const))

theorem contDiff_sumU (H : Sesq (VCx ι a b)) (α : VCx ι a b → ℂ) (S : Finset (VCx ι a b)) (F : VCx ι a b → ℂ) (k : ℕ)
    (hF : ContDiff ℂ k F) : ContDiff ℂ k (sumU H α S F) := by
  unfold sumU
  exact ContDiff.sum fun x _ => contDiff_const.mul (contDiff_opU H x F k hF)

end Smooth

section Final

variable {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)

theorem indSmooth_of (h : A.ESmooth a b) : A.IndSmooth a b Sall D := by
  intro N N' c x hR k
  unfold Amb.thInd xiInd xiS
  exact contDiff_const.mul (contDiff_const.mul (contDiff_opU _ _ _ k (contDiff_sumU _ _ _ _ k (h N N' hR.1 hR.2.1 k))))

end Final

section Final2

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

theorem qOf_pos {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : 0 < Col.qOf P := by
  unfold Col.qOf
  exact Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)

theorem modulus_pos (u : Pr.Word) (hT : 0 < Pr.T u) : 0 < cAof sel mu cst * cBof sel mu cst u := by
  have h : 0 < ∏ P : rowSG Pr sel mu, Col.qOf P.1 := Finset.prod_pos fun P _ => qOf_pos P.1
  unfold cAof cBof
  exact Nat.mul_pos (pow_pos h _) (Nat.mul_pos hT (pow_pos h _))

theorem muAt_eq_muAtT (hq : MuqTie Ch sel mu cst) (i : ℕ) (hi : i < R.m) : muAt Ch sel mu cst i = muAtT Ch sel mu cst i := by
  funext P
  unfold muAt muAtT
  by_cases h : P.1 ∈ Pr.vGs
  · simp only [if_pos h]
  · simp only [if_neg h, hq i hi P h]

theorem stepC_eq_stepT (hq : MuqTie Ch sel mu cst) (A : Amb X) (u : Pr.Word) (i : ℕ) (hi : i < R.m) {b : ℕ} (lam' : X.Tau → DomWeight b) :
    stepC W Ch sel mu cst A u i lam' = stepT W Ch sel mu cst A u i lam' := by
  unfold stepC stepT
  rw [muAt_eq_muAtT Ch sel mu cst hq i hi]

theorem stepC_ok (A : Amb X) (u : Pr.Word) (i : ℕ) (hi : i < R.m) {b : ℕ} (lam' : X.Tau → DomWeight b) (hT : 0 < Pr.T u)
    (rho : UF X.E (R.N i) →* Module.End X.K (DIV.VV X.K (W.lamTrue u i))) (rho' : UF X.E b →* Module.End X.K (DIV.VV X.K lam'))
    (hq : MuqTie Ch sel mu cst)
    (hs : A.StepHyp (R.N i) b (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u))
    (heqT : ThEquivP (stepT W Ch sel mu cst A u i lam') (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) rho rho') :
    ThDist.Ok (stepC W Ch sel mu cst A u i lam') (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) rho rho'
      (rhoS Ch sel mu i) (rhoT Ch sel mu i) :=
  have heq : ThEquivP (stepC W Ch sel mu cst A u i lam') (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) rho rho' := by
    rw [stepC_eq_stepT W Ch sel mu cst hq A u i hi lam']; exact heqT
  thDistC_ok A (Sall sel mu u) (rowSG Pr sel mu) sel (mUof Ch mu i) (muAt Ch sel mu cst i) (W.lamTrue u i) lam' (nuLast W u i) _
    (modulus_pos sel mu cst u hT) rho rho' _ _ hs.1
    (jetAdd_of A (Sall sel mu u) _ hs.1 hs.2.1 (indSmooth_of A _ _ _ _ hs.2.2.1) hs.2.2.2) heq
    (muDetLaw_chain Ch sel mu cst i _) (muDetLaw_chain Ch sel mu cst i _) (unitInv_rho Ch sel mu i)

theorem chTh_ok (A : Amb X) (u : Pr.Word) (m2 : ℕ) (hm : m2 + 1 < R.m) (hT : 0 < Pr.T u) (hq : MuqTie Ch sel mu cst)
    (hs : ∀ i, i ≤ m2 → A.StepHyp (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u))
    (hst : A.StepHyp (R.N (m2 + 1)) (R.N R.m) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u))
    (heq : ∀ i, i ≤ m2 → ThEquivP ((chThT W Ch sel mu cst A u m2).th i) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u i).rho (colValF W sel mu u (i + 1)).rho)
    (htop : ThEquivP (chThT W Ch sel mu cst A u m2).top (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u (m2 + 1)).rho (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).rho) :
    ChTh.Ok (Ch := Ch) cst (chTh W Ch sel mu cst A u m2) where
  th i hi := stepC_ok W Ch sel mu cst A u i (by omega) _ hT _ _ hq (hs i hi) (heq i hi)
  top := stepC_ok W Ch sel mu cst A u (m2 + 1) hm _ hT _ _ hq hst htop

theorem chKerC_shape (A : Amb X) (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
    (P : LevFam X.E X.K R.r Pr.vGs) (h : KerEquivC W Ch sel mu cst L A u m2 b hY P)
    (hlev : (cst.sharp = false ∧ P = rP0 Ch) ∨ (cst.sharp = true ∧ P = rPsymF Ch)) :
    (chKerC W Ch sel mu cst L A u m2 b hY P h).Shape (chTh W Ch sel mu cst A u m2) :=
  chKer_shape W Ch sel mu cst L _ b hY P h.1 h.2.1 h.2.2 hlev

end Final2

section QTest

theorem valuation_self {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal)
    (h0 : 0 < q) : LocE.vP P q (q : E) = 1 := by
  have hqE : (q : E) ≠ 0 := by exact_mod_cast h0.ne'
  have hnu : ¬ IsUnit (0 : 𝓞 E ⧸ P.asIdeal) := not_isUnit_zero
  have key : ∀ z : ℤ, IsUnit (redP P ((q : E) / (q : E) ^ z)) ↔ z = 1 := by
    intro z
    constructor
    · intro h
      by_contra hz
      rcases lt_or_gt_of_ne hz with hlt | hgt
      · obtain ⟨k, hk⟩ : ∃ k : ℕ, z = -(k : ℤ) := ⟨(-z).toNat, by omega⟩
        have e : (q : E) / (q : E) ^ z = algebraMap (𝓞 E) E (((q : ℕ) : 𝓞 E) ^ (k + 1)) := by
          rw [hk, zpow_neg, zpow_natCast, div_inv_eq_mul, map_pow, map_natCast, pow_succ']
        rw [e, reduction_coe] at h
        have h1 : Ideal.Quotient.mk P.asIdeal (((q : ℕ) : 𝓞 E) ^ (k + 1)) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_of_mem _ hq _ (Nat.succ_pos k))
        rw [h1] at h; exact hnu h
      · obtain ⟨k, hk⟩ : ∃ k : ℕ, z = (k : ℤ) + 2 := ⟨(z - 2).toNat, by omega⟩
        have e : (q : E) / (q : E) ^ z = ((q : E) ^ (k + 1))⁻¹ := by
          have e1 : (q : E) ^ z = (q : E) ^ (k + 1) * (q : E) := by
            rw [hk, ← pow_succ, ← zpow_natCast]; congr 1
          rw [e1, div_mul_eq_div_div_swap, div_self hqE, one_div]
        have hni : ¬ IntAt P ((q : E) / (q : E) ^ z) := by
          rintro ⟨r, s, hs, hrs⟩
          apply hs
          have h2 : algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E (r * ((q : ℕ) : 𝓞 E) ^ (k + 1)) := by
            rw [map_mul, ← hrs, e, map_pow, map_natCast, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hqE), mul_one]
          rw [(FaithfulSMul.algebraMap_injective (𝓞 E) E) h2]
          exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hq _ (Nat.succ_pos k))
        rw [reduction_eq_zero_of_not_integral P hni] at h; exact hnu h
    · rintro rfl
      rw [zpow_one, div_self hqE]
      have h3 : (1 : E) = algebraMap (𝓞 E) E 1 := (map_one _).symm
      rw [h3, reduction_coe, map_one]; exact isUnit_one
  unfold LocE.vP
  have h4 : (fun z : ℤ => IsUnit (redP P ((q : E) / (q : E) ^ z))) = fun z => z = 1 := funext fun z => propext (key z)
  rw [h4]
  exact Classical.epsilon_spec (p := fun z : ℤ => z = 1) ⟨1, rfl⟩

theorem locChar_q {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} (q : ℕ)
    (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (h0 : 0 < q) (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) : LocE.locChar q cq χ (q : E) = cq := by
  have hqE : (q : E) ≠ 0 := by exact_mod_cast h0.ne'
  have h1 : redP P (1 : E) = 1 := by
    have h3 : (1 : E) = algebraMap (𝓞 E) E 1 := (map_one _).symm
    rw [h3, reduction_coe, map_one]
  have hu : IsUnit (redP P (1 : E)) := by rw [h1]; exact isUnit_one
  unfold LocE.locChar
  rw [valuation_self P q hq h0, zpow_one, zpow_one, div_self hqE]
  unfold LocE.unitV
  rw [dif_pos hu]
  have h2 : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, h1]; rfl)
  rw [h2, map_one, Units.val_one, mul_one]

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem muAt_q (i : ℕ) (P : rowSG Pr sel mu) : muAt Ch sel mu cst i P ((Col.qOf P.1 : ℕ) : X.E) = cst.muq (i + 1) P := by
  unfold muAt
  exact locChar_q _ (Ideal.absNorm_mem P.1.asIdeal) (qOf_pos P.1) _ _

theorem muqTie_of_ok (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) {G : ChGlob X R.m} {m2 : ℕ} (hL : L.Ok Ch sel mu cst G m2) :
    MuqTie Ch sel mu cst := by
  intro i hi P hP
  rw [hL.muqQ i hi P hP]
  unfold muqT qVal
  rw [dif_pos hi]

theorem muqTieG_of_ok (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) {G : ChGlob X R.m} {m2 : ℕ} (hL : L.Ok Ch sel mu cst G m2) :
    MuqTieG sel mu cst G.σ₀ G.mu0 :=
  fun i hi P hP qu hqu => hL.muqG i hi P hP qu hqu

end QTest

section ReadBack

theorem retrVV_coe {K : Type} [Field K] {ι : Type} [Fintype ι] {b : ℕ} (lam' : ι → DomWeight b) (v : DIV.VV K lam') :
    retrVV K lam' (v : Pol K ι b) = v := by
  unfold retrVV
  simp

theorem jetOp_coe {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ)
    (hV : JetInVV K lam lam' n) (J : (DVar ι a b →₀ ℕ) → K) (P : DIV.VV K lam) :
    ((jetOp lam lam' J n P : DIV.VV K lam') : Pol K ι b) = jetMap J n (P : Pol K ι a) := by
  have hmem := hV J P P.2
  have e := retrVV_coe lam' (⟨jetMap J n P, hmem⟩ : DIV.VV K lam')
  unfold jetOp
  simp only [LinearMap.comp_apply, Submodule.coe_subtype]
  rw [e]

variable {X : Fields} (A : Amb X) {a b : ℕ} (Sall SB : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)

theorem jetK_spec (hrat : A.JetsRat a b Sall D) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ)
    (x : HomE X.E a b) (hR : InRange Sall D c N N' x) (m : DVar X.Tau a b →₀ ℕ) :
    A.σ₀ (A.jetK Sall N N' c x m) = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' c x) m := by
  obtain ⟨k, hk⟩ := hrat N N' c x hR m
  have hex : ∃ k' : X.K, A.σ₀ k' = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' c x) m := ⟨k, hk⟩
  unfold Amb.jetK desc
  rw [dif_pos hex]
  exact hex.choose_spec

end ReadBack

section Comparison₂

variable {ι : Type} [Fintype ι] {a b : ℕ}

def polDx (cD : ι → ℂ) (y' : ι × Fin b × Fin b → ℂ) : Pol ℂ ι a →ₐ[ℂ] MvPolynomial (DVar ι a b) ℂ :=
  aeval fun k => ∑ β : Fin b, C (cD k.1 * (if h : k.2.2.1 < b then y' (k.1, β, ⟨k.2.2.1, h⟩) else 0)) * X ((k.1, β, k.2.1) : DVar ι a b)

def atZero (G : VCx ι a b → ℂ) : MvPolynomial (DVar ι a b) ℂ →ₗ[ℂ] ℂ :=
  (basisMonomials (DVar ι a b) ℂ).constr ℂ fun α => derivAt0 G α

theorem atZero_monomial (G : VCx ι a b → ℂ) (α : DVar ι a b →₀ ℕ) (c : ℂ) : atZero G (monomial α c) = c * derivAt0 G α := by
  have h : (monomial α c : MvPolynomial (DVar ι a b) ℂ) = c • basisMonomials (DVar ι a b) ℂ α := by
    simp only [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul]
  unfold atZero
  rw [Module.Basis.constr_basis, smul_eq_mul]

theorem atZero_eq_sum (G : VCx ι a b → ℂ) (P : MvPolynomial (DVar ι a b) ℂ) :
    atZero G P = ∑ α ∈ P.support, coeff α P * derivAt0 G α := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  simp only [atZero_monomial]

def evY (cD : ι → ℂ) (y' : ι × Fin b × Fin b → ℂ) : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ →ₐ[ℂ] MvPolynomial (DVar ι a b) ℂ :=
  aeval (Sum.elim (fun v => C (y' v)) fun k => C (cD k.1) * X k)

theorem evY_subD (cD : ι → ℂ) (y' : ι × Fin b × Fin b → ℂ) : (evY cD y').comp (subD ℂ ι a b) = polDx (a := a) cD y' := by
  refine MvPolynomial.algHom_ext fun v => ?_
  simp only [AlgHom.comp_apply]
  unfold subD polDx
  rw [aeval_X, aeval_X]
  split_ifs with h
  · simp only [map_sum, map_mul, evY, aeval_X, Sum.elim_inl, Sum.elim_inr]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  · simp

theorem split_mono (m : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) :
    m = (m.comapDomain Sum.inl Sum.inl_injective.injOn).mapDomain Sum.inl + (m.comapDomain Sum.inr Sum.inr_injective.injOn).mapDomain Sum.inr := by
  ext x
  rcases x with v | v
  · rw [Finsupp.add_apply, Finsupp.mapDomain_apply Sum.inl_injective,
      Finsupp.mapDomain_notin_range (f := Sum.inr) _ (Sum.inl v) (by simp), Finsupp.comapDomain_apply, add_zero]
  · rw [Finsupp.add_apply, Finsupp.mapDomain_notin_range (f := Sum.inl) _ (Sum.inr v) (by simp),
      Finsupp.mapDomain_apply Sum.inr_injective, Finsupp.comapDomain_apply, zero_add]

theorem evY_mixed (cD : ι → ℂ) (y' : ι × Fin b × Fin b → ℂ) (p : (ι × Fin b × Fin b) →₀ ℕ) (q : DVar ι a b →₀ ℕ) :
    evY cD y' (monomial (p.mapDomain Sum.inl + q.mapDomain Sum.inr) 1) =
      monomial q ((p.prod fun v n => y' v ^ n) * (q.prod fun k n => cD k.1 ^ n)) := by
  have h : (monomial (p.mapDomain Sum.inl + q.mapDomain Sum.inr) 1 : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) =
      rename Sum.inl (monomial p 1) * rename Sum.inr (monomial q 1) := by
    rw [rename_monomial, rename_monomial, monomial_mul, one_mul]
  have h1 : (p.prod fun v n => (C (y' v) : MvPolynomial (DVar ι a b) ℂ) ^ n) = C (p.prod fun v n => y' v ^ n) := by
    simp only [Finsupp.prod, map_prod, C_pow]
  have h2 : (q.prod fun k n => (C (cD k.1) * X k : MvPolynomial (DVar ι a b) ℂ) ^ n) =
      C (q.prod fun k n => cD k.1 ^ n) * q.prod fun k n => X k ^ n := by
    simp only [Finsupp.prod, map_prod, C_pow, mul_pow, Finset.prod_mul_distrib]
  rw [h, map_mul, evY, aeval_rename, aeval_rename, aeval_monomial, aeval_monomial, monomial_eq]
  simp only [map_one, one_mul, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  rw [h1, h2, C_mul]
  ring

theorem eval_jetLin (cD : ι → ℂ) (y' : ι × Fin b × Fin b → ℂ) (G : VCx ι a b → ℂ)
    (R : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) :
    eval y' (jetLin (jetC cD G) R) = atZero G (evY cD y' R) := by
  refine MvPolynomial.induction_on' R (fun m c => ?_) (fun p q hp hq => ?_)
  · conv_rhs => rw [← mul_one c, ← MvPolynomial.C_mul_monomial]
    rw [split_mono m, jetLin_mixed, MvPolynomial.eval_monomial, map_mul, evY_mixed]
    unfold evY
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.C_mul_monomial, atZero_monomial]
    unfold jetC
    ring
  · simp only [map_add, hp, hq]

theorem jetMap_eval (cD : ι → ℂ) (G : VCx ι a b → ℂ) (Q : Pol ℂ ι a) (y' : ι × Fin b × Fin b → ℂ) :
    eval y' (jetMap (jetC cD G) (fun _ => 0) Q) =
      ∑ α ∈ (polDx cD y' Q).support, coeff α (polDx cD y' Q) * derivAt0 G α := by
  unfold jetMap
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, pow_zero, Finset.prod_const_one, mul_one,
    AlgHom.toLinearMap_apply]
  rw [eval_jetLin, ← AlgHom.comp_apply, evY_subD, atZero_eq_sum]

end Comparison₂

section Tie2

open Formalism.MainNotions

theorem derivAt0_eq_taylor (D : D7) {N N' : ℕ} (G : TaylorLogMetric.VC D N N' → ℂ) (α : TaylorLogMetric.Mono D N N') :
    (α.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D G α = derivAt0 (ι := D.what₂.Tau) G α := by
  have h0 : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 := by
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  unfold TaylorLogMetric.taylor derivAt0
  rw [mul_div_cancel₀ _ h0]
  congr 1

theorem jetMap_applyAt0 (D : D7) {N N' : ℕ} (s : D.what₂.Tau → ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (y' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) :
    eval (fun k : D.what₂.Tau × Fin N' × Fin N' => y' k.1 k.2.1 k.2.2) (jetMap (ι := D.what₂.Tau) (jetC s G) (fun _ => 0) Q) =
      GL3Theta.applyAt0 D (GL3Theta.polD D s Q y') G := by
  rw [jetMap_eval]
  unfold GL3Theta.applyAt0
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [mul_assoc, derivAt0_eq_taylor]
  rfl

end Tie2

section NoCut

variable {X : Fields} (A : Amb X) {a b : ℕ} (Sall SB : Finset (HeightOneSpectrum (𝓞 X.E)))

theorem divLat_mul_of {E : Type} [Field E] [NumberField E] {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (cA cB : ℕ) (M : Submodule (𝓞 E) H)
    {x : H} (hx : x ∈ divLat cA M) : x ∈ divLat (cA * cB) M := by
  simp only [divLat, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
  rw [Nat.cast_mul, mul_comm, ← smul_smul]
  exact M.smul_mem _ hx

theorem kerOf_thDistC (cA cB : ℕ) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
    (mI : SB → X.E → X.K) (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB) (Ξ : HomE X.E a b → X.K) :
    kerOf (thDistC A Sall SB (cA * cB) sel mU mI lam lam' n) Sall cA cB N fr N' fr' Ξ =
      latSum (divLat cA (homAt Sall N N')) (mulLat cB (homAt Sall N N')) fun x =>
        Ξ x • ((muInvDet sel SB mU mI N fr * (muInvDet sel SB mU mI N' fr')⁻¹) • jetOp lam lam' (A.jetK Sall N N' cB x) n) := by
  unfold kerOf latSum
  refine finsum_congr fun z => ?_
  have hx := SetLike.coe_mem (Function.surjInv (Submodule.Quotient.mk_surjective
    ((mulLat cB (homAt Sall N N')).comap (divLat cA (homAt Sall N N')).subtype)) z)
  simp only [thDistC, if_pos (And.intro (dvd_mul_left cB cA) (divLat_mul_of cA cB _ hx))]

end NoCut

section OnYs

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  {u : Pr.Word} {m2 : ℕ} (T : ChTh W sel mu u m2) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)

theorem cplEq1_of_on {K : Type} [Field K] [NumberField K] [StarRing K] {S₀ S : GSD K} (Y : Cpl S) (k1 : S₀.D → S.D → Y.Yb → (S₀.V →ₗ[K] S.V))
    (h : CplEq1On Y k1) (h0 : ∀ d₀ d y, y ∉ Y.ys d → k1 d₀ d y = 0) : CplEq1 Y k1 := by
  intro g₀ g d₀ d y
  by_cases hy : y ∈ Y.ys d
  · exact h g₀ g d₀ d y hy
  · rw [h0 d₀ d y hy, h0 _ _ _ (fun h' => hy ((Y.equiv g d y).1 h')), LinearMap.zero_comp, LinearMap.comp_zero]

theorem cplEq2_of_on {K : Type} [Field K] [NumberField K] [StarRing K] {S S₁ : GSD K} (Y : Cpl S) (k2 : S.D → Y.Yb → S₁.D → (S.V →ₗ[K] S₁.V))
    (h : CplEq2On Y k2) (h0 : ∀ d y d₁, y ∉ Y.ys d → k2 d y d₁ = 0) : CplEq2 Y k2 := by
  intro g g₁ d y d₁
  by_cases hy : y ∈ Y.ys d
  · exact h g g₁ d y d₁ hy
  · rw [h0 d y d₁ hy, h0 _ _ _ (fun h' => hy ((Y.equiv g d y).1 h')), LinearMap.zero_comp, LinearMap.comp_zero]

theorem cp1Equiv_of_on (h : Cp1EquivOn W Ch sel mu cst L T b hY) : Cp1Equiv W Ch sel mu cst L T b hY := fun al =>
  cplEq1_of_on _ _ (h al) fun _ _ _ hy => if_neg hy

theorem cp2Equiv_of_on (P : LevFam X.E X.K R.r Pr.vGs) (h : Cp2EquivOn W Ch sel mu cst L T b hY P) :
    Cp2Equiv W Ch sel mu cst L T b hY P :=
  cplEq2_of_on _ _ h fun _ _ _ hy => if_neg hy

end OnYs

section LiftAbs

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem lf_class (H : Sesq V) (hH : IsHerm H) (α : V → ℂ) (A' B Λ L : AddSubgroup V) (hA : IsSemiChar H A' α) (hB : IsSemiChar H B α)
    (SA SB : Finset V) (hSA : IsReps B L SA) (hSB : IsReps Λ B SB) (vol : ℝ) (θ : V → ℂ) (hθ : θ ∈ fixedBy H α Λ)
    {s m : V} (hs : s ∈ A') (hm : m ∈ A') (hmB : m ∈ B) (z : V) :
    xiInd H α vol B SA SB θ (s + m) z = xiInd H α vol B SA SB θ s z := by
  have hz : ∀ w, xiS H α vol SA SB (indL B) θ w = ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * (((vol : ℝ) : ℂ) / (SA.card : ℂ)) * sumU H α SB θ w := by
    intro w
    simp only [xiS, sumU]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [hatS_ind H hH α B _ hB vol SA hSA (hSB.1 y hy)]; ring
  have hneg := (semicharacterBasic V H hH A' α hA).2.1
  set G := xiS H α vol SA SB (indL B) θ with hG
  have hfix : (fun v => α (-m) * opU H (-m) G v) = G := by
    funext v
    have hG' : G = fun w => ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * (((vol : ℝ) : ℂ) / (SA.card : ℂ)) * sumU H α SB θ w := funext hz
    rw [hG', Inv.opU_const_mul, mul_left_comm, sumU_fixed H hH α B Λ hB SB hSB θ hθ (B.neg_mem hmB)]
  have h1 := semicharacterHom V H hH A' α hA (-s) (A'.neg_mem hs) (-m) (A'.neg_mem hm) G z
  rw [hfix] at h1
  show α (s + m) * opU H (-(s + m)) G z = α s * opU H (-s) G z
  rw [← hneg (s + m) (A'.add_mem hs hm), neg_add, ← h1, hneg s hs]

end LiftAbs

section LiftLat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem lf_common (P : HeightOneSpectrum (𝓞 E)) (N' : Submodule (𝓞 E) (Sp E b)) (x : HomE E a b) (T : Finset (Sp E a))
    (h : ∀ y ∈ T, x y ∈ localization₂ P.asIdeal N') : ∃ u ∈ P.asIdeal.primeCompl, ∀ y ∈ T, u • x y ∈ N' := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, Submonoid.one_mem _, fun y hy => absurd hy (Finset.notMem_empty y)⟩
  | insert y₀ T _ ih =>
    obtain ⟨u, hu, hT⟩ := ih fun y hy => h y (Finset.mem_insert_of_mem hy)
    obtain ⟨v, hv, hy₀⟩ := h y₀ (Finset.mem_insert_self _ _)
    refine ⟨v * u, Submonoid.mul_mem _ hv hu, fun y hy => ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hy
    · rw [mul_comm, mul_smul]; exact N'.smul_mem u hy₀
    · rw [mul_smul]; exact N'.smul_mem v (hT y hy)

theorem homAt_le_locP_perO (S : Finset (HeightOneSpectrum (𝓞 E))) (AA0 : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (hN : N.FG) {P : HeightOneSpectrum (𝓞 E)} (hP : P ∈ S)
    (hAA : localization₂ P.asIdeal AA0 = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) {x : HomE E a b} (hx : x ∈ homAt S N N') :
    x ∈ localization₂ P.asIdeal (perO AA0 N N') := by
  obtain ⟨T, hT⟩ := hN
  obtain ⟨u, hu, huT⟩ := lf_common P N' x T fun y hy =>
    hx P hP y (le_locP' N P (hT ▸ Submodule.subset_span (Finset.mem_coe.2 hy)))
  have hux : u • x ∈ homO N N' := by
    intro y hy
    rw [← hT] at hy
    show (u • x) y ∈ N'
    induction hy using Submodule.span_induction with
    | mem y hy => rw [LinearMap.smul_apply]; exact huT y (Finset.mem_coe.1 hy)
    | zero => rw [map_zero]; exact N'.zero_mem
    | add y y' _ _ h1 h2 => rw [map_add]; exact N'.add_mem h1 h2
    | smul r y _ h1 =>
      have e : (u • x) (r • y) = r • (u • x) y := by
        rw [← algebraMap_smul E r y, map_smul, algebraMap_smul]
      rw [e]; exact N'.smul_mem r h1
  have h1 : (1 : E) ∈ localization₂ P.asIdeal AA0 := by
    rw [hAA]; exact le_locP' _ P (Submodule.mem_one.2 ⟨1, map_one _⟩)
  obtain ⟨v, hv, hv1⟩ := h1
  refine ⟨v * u, Submonoid.mul_mem _ hv hu, ?_⟩
  refine Submodule.subset_span ⟨v • (1 : E), hv1, u • x, hux, ?_⟩
  rw [smul_assoc, one_smul, mul_smul]

variable {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

theorem lf_int_smul_mem (L : Submodule (𝓞 E) W) (k : ℤ) {x : W} (hx : x ∈ L) : (k : E) • x ∈ L := by
  have e : (k : E) • x = (k : 𝓞 E) • x := by
    rw [← algebraMap_smul E (k : 𝓞 E) x, map_intCast]
  rw [e]
  exact L.smul_mem _ hx

theorem lf_gcd (S : Finset (HeightOneSpectrum (𝓞 E))) (M : Submodule (𝓞 E) (HomE E a b)) (c₁ c₂ : ℕ) (h₁ : 0 < c₁) {s : HomE E a b}
    (hs : s ∈ halfAO S M c₁) (hs₂ : ∀ Q ∈ S, (c₂ : E) • s ∈ localization₂ Q.asIdeal M) : s ∈ halfAO S M (Nat.gcd c₁ c₂) := by
  have hs' := (mem_twO _ _ _ _).1 hs
  refine (mem_twO _ _ _ _).2 fun Q => ?_
  have hQ := hs' Q
  have hc₁ : (c₁ : E) ≠ 0 := Nat.cast_ne_zero.2 h₁.ne'
  have hg : ((Nat.gcd c₁ c₂ : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.2 (Nat.gcd_pos_of_pos_left _ h₁).ne'
  rcases expS_cases S Q with h1 | h1 | h1
  · have hQS := expS_eq_one S Q h1
    simp only [h1, zpow_neg_one, inv_inv] at hQ ⊢
    have hb : ((Nat.gcd c₁ c₂ : ℕ) : E) = (c₁ : E) * ((Nat.gcdA c₁ c₂ : ℤ) : E) + (c₂ : E) * ((Nat.gcdB c₁ c₂ : ℤ) : E) := by
      have := Nat.gcd_eq_gcd_ab c₁ c₂
      exact_mod_cast congrArg (Int.cast : ℤ → E) this
    rw [hb, add_smul, mul_comm (c₁ : E), mul_comm (c₂ : E), mul_smul, mul_smul]
    exact Submodule.add_mem _ (lf_int_smul_mem _ _ hQ) (lf_int_smul_mem _ _ (hs₂ Q hQS))
  · simp only [h1, neg_zero, zpow_zero] at hQ ⊢
    exact hQ
  · simp only [h1, neg_neg, zpow_one] at hQ ⊢
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left c₁ c₂
    have e : ((Nat.gcd c₁ c₂ : ℕ) : E)⁻¹ • s = (k : E) • ((c₁ : E)⁻¹ • s) := by
      rw [smul_smul]; congr 1
      have hk' : (c₁ : E) = ((Nat.gcd c₁ c₂ : ℕ) : E) * (k : E) := by exact_mod_cast congrArg (Nat.cast : ℕ → E) hk
      field_simp
      rw [hk']
    rw [e]; exact nat_smul_mem _ k hQ

theorem lf_halfB (S : Finset (HeightOneSpectrum (𝓞 E))) (M : Submodule (𝓞 E) (HomE E a b)) (g c : ℕ) (hg : 0 < g) {m : HomE E a b}
    (hm : m ∈ halfAO S M g) (hm₂ : ∀ Q ∈ S, (c : E)⁻¹ • m ∈ localization₂ Q.asIdeal M) : m ∈ halfBO S M c := by
  have hm' := (mem_twO _ _ _ _).1 hm
  refine (mem_twO _ _ _ _).2 fun Q => ?_
  have hQ := hm' Q
  have hgE : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg.ne'
  rcases expS_cases S Q with h1 | h1 | h1
  · rw [h1, zpow_one]; exact hm₂ Q (expS_eq_one S Q h1)
  · simp only [h1, neg_zero, zpow_zero] at hQ ⊢
    exact hQ
  · simp only [h1, neg_neg, zpow_one] at hQ
    rw [h1, zpow_neg_one, inv_inv]
    have h2 := nat_smul_mem _ c (nat_smul_mem _ g hQ)
    rwa [smul_smul (g : E) (g : E)⁻¹, mul_inv_cancel₀ hgE, one_smul] at h2

theorem lf_mulLat (S : Finset (HeightOneSpectrum (𝓞 E))) (AA0 : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (hN : N.FG) (hAA : ∀ P ∈ S, localization₂ P.asIdeal AA0 = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) (c : ℕ) (hc : 0 < c)
    {m : HomE E a b} (hm : m ∈ mulLat c (homAt S N N')) :
    ∀ Q ∈ S, (c : E)⁻¹ • m ∈ localization₂ Q.asIdeal (perO AA0 N N') ∧ m ∈ localization₂ Q.asIdeal (perO AA0 N N') := by
  intro Q hQ
  simp only [mulLat, Submodule.mem_map, LinearMap.smul_apply, LinearMap.id_apply] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  have h0 := homAt_le_locP_perO S AA0 N N' hN hQ (hAA Q hQ) hm₀
  have hc' : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨?_, Submodule.smul_mem _ _ h0⟩
  rw [← algebraMap_smul E (c : 𝓞 E) m₀, map_natCast, smul_smul, inv_mul_cancel₀ hc', one_smul]
  exact h0

end LiftLat

section LiftMain

variable {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E)))

theorem liftIndep_of (h : A.HeisHyp a b Sall) : A.LiftIndep a b Sall := by
  obtain ⟨-, -, -, hAA, hall⟩ := h
  intro N N' c x s hN hN' hc hs z
  obtain ⟨hθ, hlev⟩ := hall N N' hN hN'
  have hs₀ : A.IsLift Sall N N' c x (A.liftW Sall N N' c x) := Classical.epsilon_spec (p := A.IsLift Sall N N' c x) ⟨s, hs⟩
  set s₀ := A.liftW Sall N N' c x with hs₀def
  obtain ⟨⟨c₁, hc₁, h1⟩, h1x⟩ := hs
  obtain ⟨⟨c₂, hc₂, h2⟩, h2x⟩ := hs₀
  have hm : s₀ - s ∈ mulLat c (homAt Sall N N') := by
    have e : s₀ - s = (s₀ - x) - (s - x) := by abel
    rw [e]; exact Submodule.sub_mem _ h2x h1x
  have hmQ := lf_mulLat Sall A.AA N N' hN.1.fg hAA c hc hm
  have hc₁E : (c₁ : X.E) ≠ 0 := Nat.cast_ne_zero.2 hc₁.ne'
  have hc₂E : (c₂ : X.E) ≠ 0 := Nat.cast_ne_zero.2 hc₂.ne'
  have hP1 : ∀ Q ∈ Sall, (c₁ : X.E) • s ∈ localization₂ Q.asIdeal (perO A.AA N N') := by
    intro Q hQ
    have := (mem_twO _ _ _ _).1 h1 Q
    have e1 : expS Sall Q = 1 := by unfold expS; rw [if_pos hQ]
    simpa only [e1, zpow_neg_one, inv_inv] using this
  have hP2 : ∀ Q ∈ Sall, (c₂ : X.E) • s₀ ∈ localization₂ Q.asIdeal (perO A.AA N N') := by
    intro Q hQ
    have := (mem_twO _ _ _ _).1 h2 Q
    have e1 : expS Sall Q = 1 := by unfold expS; rw [if_pos hQ]
    simpa only [e1, zpow_neg_one, inv_inv] using this
  have hg1 : s ∈ halfAO Sall (perO A.AA N N') (Nat.gcd c₁ c₂) := by
    refine lf_gcd Sall _ c₁ c₂ hc₁ h1 fun Q hQ => ?_
    have e : (c₂ : X.E) • s = (c₂ : X.E) • s₀ - (c₂ : X.E) • (s₀ - s) := by rw [← smul_sub]; congr 1; abel
    rw [e]; exact Submodule.sub_mem _ (hP2 Q hQ) (nat_smul_mem _ c₂ (hmQ Q hQ).2)
  have hg2 : s₀ ∈ halfAO Sall (perO A.AA N N') (Nat.gcd c₁ c₂) := by
    rw [Nat.gcd_comm]
    refine lf_gcd Sall _ c₂ c₁ hc₂ h2 fun Q hQ => ?_
    have e : (c₁ : X.E) • s₀ = (c₁ : X.E) • s + (c₁ : X.E) • (s₀ - s) := by rw [← smul_add]; congr 1; abel
    rw [e]; exact Submodule.add_mem _ (hP1 Q hQ) (nat_smul_mem _ c₁ (hmQ Q hQ).2)
  have hgpos : 0 < Nat.gcd c₁ c₂ := Nat.gcd_pos_of_pos_left _ hc₁
  have hmA : s₀ - s ∈ halfAO Sall (perO A.AA N N') (Nat.gcd c₁ c₂) := Submodule.sub_mem _ hg2 hg1
  have hmB : s₀ - s ∈ halfBO Sall (perO A.AA N N') c := lf_halfB Sall _ _ c hgpos hmA fun Q hQ => (hmQ Q hQ).1
  obtain ⟨hSc, hr1, hr2, -⟩ := hlev c hc
  obtain ⟨hSg, -, -, -⟩ := hlev _ hgpos
  have e0 : embH (X.embC A.σ₀) A.δ s₀ = embH (X.embC A.σ₀) A.δ s + embH (X.embC A.σ₀) A.δ (s₀ - s) := by
    rw [← map_add]; congr 1; abel
  unfold Amb.thInd
  rw [← hs₀def, e0]
  congr 1
  exact lf_class _ hSc.1 _ (AC (X.embC A.σ₀) A.δ A.AA Sall N N' (Nat.gcd c₁ c₂)) _ _ _ hSg.2.1 hSc.2.2.1 _ _
    (repsOf_spec _ _ hr1) (repsOf_spec _ _ hr2) _ _ hθ ⟨s, hg1, rfl⟩ ⟨s₀ - s, hmA, rfl⟩ ⟨s₀ - s, hmB, rfl⟩ z

end LiftMain

section LiftMore

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem localization_perO_le_homAt (AA0 : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b))
    {P : HeightOneSpectrum (𝓞 E)} (hAA : localization₂ P.asIdeal AA0 = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) {w : HomE E a b}
    (hw : w ∈ localization₂ P.asIdeal (perO AA0 N N')) : ∀ y ∈ localization₂ P.asIdeal N, w y ∈ localization₂ P.asIdeal N' := by
  have hper : ∀ w' ∈ perO AA0 N N', ∀ y ∈ localization₂ P.asIdeal N, w' y ∈ localization₂ P.asIdeal N' := by
    intro w' hw'
    induction hw' using Submodule.span_induction with
    | mem w' h =>
      obtain ⟨r, hr, x, hx, rfl⟩ := h
      rintro y ⟨t, ht, hty⟩
      have hr1 : r ∈ localization₂ P.asIdeal (1 : Submodule (𝓞 E) E) := hAA ▸ le_locP' AA0 P hr
      obtain ⟨v, hv, hvr⟩ := hr1
      obtain ⟨ρ, hρ⟩ := Submodule.mem_one.1 hvr
      refine ⟨v * t, Submonoid.mul_mem _ hv ht, ?_⟩
      have e : (v * t) • (r • x) y = ρ • x (t • y) := by
        rw [← algebraMap_smul E t y, map_smul, LinearMap.smul_apply, ← algebraMap_smul E ρ, hρ, ← algebraMap_smul E (v * t),
          Algebra.smul_def v r, smul_smul, smul_smul, map_mul]
        congr 1; ring
      rw [e]; exact N'.smul_mem ρ (hx _ hty)
    | zero => intro y _; exact Submodule.zero_mem _
    | add w₁ w₂ _ _ h1 h2 => intro y hy; exact Submodule.add_mem _ (h1 y hy) (h2 y hy)
    | smul r w₁ _ h1 => intro y hy; exact Submodule.smul_mem _ r (h1 y hy)
  obtain ⟨u, hu, huw⟩ := hw
  intro y hy
  obtain ⟨t, ht, h⟩ := hper _ huw y hy
  exact ⟨t * u, Submonoid.mul_mem _ ht hu, by rw [mul_smul]; exact h⟩

theorem lf_span (AA0 : Submodule (𝓞 E) E) (hAA0 : AA0 ≠ ⊥) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (hN : N.FG)
    (hN' : Submodule.span E (N' : Set (Sp E b)) = ⊤) (x : HomE E a b) : ∃ n : ℕ, 0 < n ∧ (n : E) • x ∈ perO AA0 N N' := by
  obtain ⟨ν, hν, hνx⟩ := exists_smul_le (N.map (x.restrictScalars (𝓞 E))) N' (hN.map _) hN'
  have hh : ν • x ∈ homO N N' := fun y hy => hνx _ ⟨y, hy, rfl⟩
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hAA0
  have hνE : algebraMap (𝓞 E) E ν ≠ 0 := fun h0 => hν ((FaithfulSMul.algebraMap_injective (𝓞 E) E) (by rw [h0, map_zero]))
  obtain ⟨e, he, hint⟩ := exists_int_mul_integral (r * algebraMap (𝓞 E) E ν)⁻¹
  obtain ⟨k, hk⟩ : ∃ k : 𝓞 E, algebraMap (𝓞 E) E k = (e : E) * (r * algebraMap (𝓞 E) E ν)⁻¹ := ⟨⟨_, hint⟩, rfl⟩
  have hmem : (e : E) • x ∈ perO AA0 N N' := by
    have e1 : (e : E) • x = k • (r • (ν • x)) := by
      rw [← algebraMap_smul E k, ← algebraMap_smul E ν x, smul_smul, smul_smul, hk]
      congr 1
      field_simp
    rw [e1]
    exact Submodule.smul_mem _ k (Submodule.subset_span ⟨r, hr, ν • x, hh, rfl⟩)
  refine ⟨e.natAbs, Int.natAbs_pos.2 he, ?_⟩
  rcases Int.natAbs_eq e with h | h
  · have : ((e.natAbs : ℕ) : E) = (e : E) := by
      conv_rhs => rw [h]
      simp
    rw [this]; exact hmem
  · have : ((e.natAbs : ℕ) : E) = -(e : E) := by
      conv_rhs => rw [h]
      simp
    rw [this, neg_smul]; exact Submodule.neg_mem _ hmem

end LiftMore

section LiftMore2

variable {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E)))

variable {a b} in

theorem lf_isLift_of_liftS (hAA : A.AAUnit Sall) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) {c D : ℕ} (hD : 0 < D)
    (hcD : c ∣ D) {x s : HomE X.E a b} (h : IsLiftS Sall (perO A.AA N N') D x s) : A.IsLift Sall N N' c x s := by
  obtain ⟨k, rfl⟩ := hcD
  have hk : (k : X.E) ≠ 0 := by
    have : k ≠ 0 := by rintro rfl; simp at hD
    exact_mod_cast this
  have hc : (c : X.E) ≠ 0 := by
    have : c ≠ 0 := by rintro rfl; simp at hD
    exact_mod_cast this
  unfold IsLiftS at h
  unfold Amb.IsLift
  refine ⟨⟨c * k, hD, h.1⟩, ?_⟩
  simp only [mulLat, Submodule.mem_map, LinearMap.smul_apply, LinearMap.id_apply]
  refine ⟨(k : 𝓞 X.E) • (((c * k : ℕ) : X.E)⁻¹ • (s - x)), ?_, ?_⟩
  · intro P hP y hy
    have hw := localization_perO_le_homAt A.AA N N' (hAA P hP) (h.2 P hP) y hy
    rw [LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ hw
  · rw [smul_smul, ← algebraMap_smul X.E ((c : 𝓞 X.E) * (k : 𝓞 X.E)), map_mul, map_natCast, map_natCast, smul_smul,
      Nat.cast_mul, mul_inv_cancel₀ (mul_ne_zero hc hk), one_smul]

variable {a b} in

theorem lf_exists_liftS (hAA : A.AAUnit Sall) (hAA0 : A.AA ≠ ⊥) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (hN : IsSdLat N) (hN' : IsSdLat N') {D : ℕ} (hD : 0 < D) {x : HomE X.E a b} (hx : x ∈ divLat D (homAt Sall N N')) :
    ∃ s, IsLiftS Sall (perO A.AA N N') D x s := by
  obtain ⟨n, hn0, hn⟩ := lf_span A.AA hAA0 N N' hN.1.fg hN'.1.span_eq_top x
  refine exists_lift Sall (perO A.AA N N') D n hD hn0 hn fun P hP => ?_
  have h1 : ((D : 𝓞 X.E) • (LinearMap.id : HomE X.E a b →ₗ[𝓞 X.E] HomE X.E a b)) x ∈ homAt Sall N N' := hx
  rw [LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul X.E] at h1
  exact homAt_le_locP_perO Sall A.AA N N' hN.1.fg hP (hAA P hP) h1

variable {a b} in

theorem lf_halfB_iff (hAA : A.AAUnit Sall) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (hN : N.FG) {c g : ℕ} (hc : 0 < c)
    (hg : 0 < g) {w : HomE X.E a b} (hw : w ∈ halfAO Sall (perO A.AA N N') g) :
    w ∈ halfBO Sall (perO A.AA N N') c ↔ w ∈ mulLat c (homAt Sall N N') := by
  have hcE : (c : X.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  constructor
  · intro h
    have h' := (mem_twO _ _ _ _).1 h
    have hh : (c : X.E)⁻¹ • w ∈ homAt Sall N N' := by
      intro P hP
      have e1 : expS Sall P = 1 := by unfold expS; rw [if_pos hP]
      have h2 := h' P
      rw [e1, zpow_one] at h2
      exact localization_perO_le_homAt A.AA N N' (hAA P hP) h2
    refine ⟨(c : X.E)⁻¹ • w, hh, ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul X.E, smul_smul, mul_inv_cancel₀ hcE, one_smul]
  · intro h
    exact lf_halfB Sall _ g c hg hw fun Q hQ => (lf_mulLat Sall A.AA N N' hN hAA c hc h Q hQ).1

end LiftMore2

section TieLat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem ti_mul_mono {H : Type} [AddCommGroup H] [Module (𝓞 E) H] {c D : ℕ} (h : c ∣ D) (M : Submodule (𝓞 E) H) {w : H}
    (hw : w ∈ mulLat D M) : w ∈ mulLat c M := by
  obtain ⟨k, rfl⟩ := h
  simp only [mulLat, Submodule.mem_map, LinearMap.smul_apply, LinearMap.id_apply] at hw ⊢
  obtain ⟨m, hm, rfl⟩ := hw
  exact ⟨(k : 𝓞 E) • m, M.smul_mem _ hm, by rw [smul_smul, Nat.cast_mul]⟩

theorem ti_mul_of_inv {c : ℕ} (hc : 0 < c) (M : Submodule (𝓞 E) (HomE E a b)) {w : HomE E a b} (hw : (c : E)⁻¹ • w ∈ M) :
    w ∈ mulLat c M := by
  have hc' : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  simp only [mulLat, Submodule.mem_map, LinearMap.smul_apply, LinearMap.id_apply]
  refine ⟨(c : E)⁻¹ • w, hw, ?_⟩
  rw [← algebraMap_smul E (c : 𝓞 E), map_natCast, smul_smul, mul_inv_cancel₀ hc', one_smul]

theorem ti_exists_lift (AA : Submodule (𝓞 E) E) (S : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (hN : N.FG) (hN' : Submodule.span E (N' : Set (Sp E b)) = ⊤)
    (hA : ∀ P ∈ S, localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) {D : ℕ} (hD : 0 < D) {x : HomE E a b}
    (hx : x ∈ divLat D (homAt S N N')) :
    ∃ s, s ∈ halfAO S (perO AA N N') D ∧ s - x ∈ mulLat D (homAt S N N') := by
  rcases S.eq_empty_or_nonempty with hS | ⟨P0, hP0⟩
  · subst hS
    refine ⟨0, zero_mem _, ti_mul_of_inv hD _ ?_⟩
    show ∀ P ∈ (∅ : Finset (HeightOneSpectrum (𝓞 E))), _
    intro P hP
    exact absurd hP (Finset.notMem_empty P)
  · have h1 : (1 : E) ∈ localization₂ P0.asIdeal AA := by
      rw [hA P0 hP0]; exact le_locP' _ P0 (Submodule.mem_one.2 ⟨1, map_one _⟩)
    obtain ⟨v, hv, hv'⟩ := h1
    have hv0 : v ≠ 0 := fun h0 => hv (h0 ▸ P0.asIdeal.zero_mem)
    obtain ⟨ν, hν, hνx⟩ := exists_smul_le (N.map (x.restrictScalars (𝓞 E))) N' (hN.map _) hN'
    have hνO : ν • x ∈ homO N N' := fun y hy => hνx _ ⟨y, hy, rfl⟩
    have hM : (v * ν) • x ∈ perO AA N N' := by
      have e : (v * ν) • x = (v • (1 : E)) • (ν • x) := by rw [mul_smul, smul_assoc, one_smul]
      rw [e]; exact Submodule.subset_span ⟨_, hv', _, hνO, rfl⟩
    have hI : Ideal.span {v * ν} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact mul_ne_zero hv0 hν
    have hn0 : 0 < Ideal.absNorm (Ideal.span {v * ν}) := Nat.pos_of_ne_zero fun h0 => hI (Ideal.absNorm_eq_zero_iff.1 h0)
    obtain ⟨ρ, hρ⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {v * ν}))
    have hn : ((Ideal.absNorm (Ideal.span {v * ν}) : ℕ) : E) • x ∈ perO AA N N' := by
      have e : ((Ideal.absNorm (Ideal.span {v * ν}) : ℕ) : E) • x = ρ • ((v * ν) • x) := by
        rw [smul_smul, hρ, ← IsScalarTower.algebraMap_smul E ((Ideal.absNorm (Ideal.span {v * ν}) : ℕ) : 𝓞 E) x, map_natCast]
      rw [e]; exact Submodule.smul_mem _ ρ hM
    have hxP : ∀ P ∈ S, (D : E) • x ∈ localization₂ P.asIdeal (perO AA N N') := by
      intro P hP
      have h2 : (D : 𝓞 E) • x ∈ homAt S N N' := hx
      rw [← IsScalarTower.algebraMap_smul E (D : 𝓞 E) x, map_natCast] at h2
      exact homAt_le_locP_perO S AA N N' hN hP (hA P hP) h2
    obtain ⟨s, hs1, hs2⟩ := exists_lift S (perO AA N N') D _ hD hn0 hn hxP
    exact ⟨s, hs1, ti_mul_of_inv hD _ fun P hP => localization_perO_le_homAt AA N N' (hA P hP) (hs2 P hP)⟩

variable {ι : Type} [Fintype ι] [Nonempty ι]

private theorem embH_injective_kernel_local_factors (emb : ι → E →+* ℂ) {δ : ℂ} (hδ : δ ≠ 0) {x y : HomE E a b}
    (h : embH emb δ x = embH emb δ y) : x = y := by
  obtain ⟨τ⟩ := ‹Nonempty ι›
  apply (Pi.basisFun E (Fin a)).ext
  intro j
  funext i
  have := congrFun (congrFun (congrFun h τ) i) j
  change δ * emb τ (x (Pi.single j 1) i) = δ * emb τ (y (Pi.single j 1) i) at this
  rw [Pi.basisFun_apply]
  exact (emb τ).injective (mul_left_cancel₀ hδ this)

theorem ti_onV (emb : ι → E →+* ℂ) {δ : ℂ} (hδ : δ ≠ 0) (Ξ : HomE E a b → ℂ) (t0 : HomE E a b) :
    onV emb δ Ξ (embH emb δ t0) = Ξ t0 := by
  have hex : ∃ x, embH emb δ x = embH emb δ t0 := ⟨t0, rfl⟩
  unfold onV
  rw [dif_pos hex]
  exact congrArg Ξ (embH_injective_kernel_local_factors emb hδ hex.choose_spec)

theorem ti_mem_laV (emb : ι → E →+* ℂ) {δ : ℂ} (hδ : δ ≠ 0) (M : Submodule (𝓞 E) (HomE E a b)) (w : HomE E a b) :
    embH emb δ w ∈ laV emb δ M ↔ w ∈ M := by
  unfold laV
  constructor
  · intro h
    obtain ⟨x, hx, hxw⟩ := AddSubgroup.mem_map.mp h
    rw [← embH_injective_kernel_local_factors emb hδ hxw]
    exact hx
  · intro hw
    exact AddSubgroup.mem_map.mpr ⟨w, hw, rfl⟩

end TieLat

theorem indTieD_of {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (hD : 0 < D)
    (h : A.HeisHyp a b Sall) (hL : A.LiftIndep a b Sall) (hR : A.Refine a b Sall D) : A.IndTieD a b Sall D := by
  intro N N' c x hRg _ z
  obtain ⟨hN, hN', hc, hcD, hx⟩ := hRg
  obtain ⟨hδ, hne, hconj, hAA, hall⟩ := h
  obtain ⟨hθ, hlev⟩ := hall N N' hN hN'
  obtain ⟨hyp, r1, r2, r3⟩ := hlev D hD
  have := hne
  obtain ⟨s, hsA, hsx⟩ := ti_exists_lift A.AA Sall N N' hN.1.fg hN'.1.span_eq_top hAA hD hx
  have hsx' : s - x ∈ mulLat c (homAt Sall N N') := ti_mul_mono hcD _ hsx
  rw [hL N N' c x s hN hN' hc ⟨⟨D, hD, hsA⟩, hsx'⟩ z]
  congr 1
  have hSX := repsOf_spec _ _ r3
  have hSA := repsOf_spec _ _ r1
  have hSB := repsOf_spec _ _ r2
  obtain ⟨T, hT⟩ := exists_reps_AB _ _ _ _ _ hSX hSA
  rw [hR N N' c s hN hN' hc hcD hD hsA T hT z]
  have hInv : InvOn (AC (X.embC A.σ₀) A.δ A.AA Sall N N' D) (BC (X.embC A.σ₀) A.δ A.AA Sall N N' D)
      (onV (X.embC A.σ₀) A.δ (cosInd Sall N N' c x)) := by
    intro t ht m hm hmB
    obtain ⟨t0, ht0, rfl⟩ := ht
    obtain ⟨m0, hm0, rfl⟩ := hm
    rw [← map_add, ti_onV _ hδ, ti_onV _ hδ]
    have hm0B : m0 ∈ halfBO Sall (perO A.AA N N') D := (ti_mem_laV _ hδ _ _).1 hmB
    have hm0c : m0 ∈ mulLat c (homAt Sall N N') := ti_mul_mono hcD _ ((lf_halfB_iff A Sall hAA N N' hN.1.fg hD hD hm0).1 hm0B)
    unfold cosInd
    by_cases hq : t0 - x ∈ mulLat c (homAt Sall N N')
    · have hq' : t0 + m0 - x ∈ mulLat c (homAt Sall N N') := by
        have e : t0 + m0 - x = (t0 - x) + m0 := by abel
        rw [e]; exact add_mem hq hm0c
      rw [if_pos hq, if_pos hq']
    · have hq' : ¬ t0 + m0 - x ∈ mulLat c (homAt Sall N N') := by
        intro h1
        apply hq
        have e : t0 - x = (t0 + m0 - x) - m0 := by abel
        rw [e]; exact sub_mem h1 hm0c
      rw [if_neg hq, if_neg hq']
  have hE := twist_expand_lattice _ _ _ _ _ _ hyp T _ _ _ hT hSX hSA hSB (volC A.AA Sall N N') (A.e a b N N') hθ _ hInv z
  unfold xiC xiV
  rw [hE]
  refine Finset.sum_congr rfl fun t ht => ?_
  congr 1
  obtain ⟨t0, ht0, rfl⟩ := hT.1 t ht
  rw [ti_onV _ hδ, ← map_sub]
  have hiff : embH (X.embC A.σ₀) A.δ (t0 - s) ∈ BC (X.embC A.σ₀) A.δ A.AA Sall N N' c ↔ t0 - x ∈ mulLat c (homAt Sall N N') := by
    constructor
    · intro h1
      have h2 := (lf_halfB_iff A Sall hAA N N' hN.1.fg hc hD (sub_mem ht0 hsA)).1 ((ti_mem_laV _ hδ _ _).1 h1)
      have e : t0 - x = (t0 - s) + (s - x) := by abel
      rw [e]; exact add_mem h2 hsx'
    · intro h1
      have h2 : t0 - s ∈ mulLat c (homAt Sall N N') := by
        have e : t0 - s = (t0 - x) - (s - x) := by abel
        rw [e]; exact sub_mem h1 hsx'
      exact (ti_mem_laV _ hδ _ _).2 ((lf_halfB_iff A Sall hAA N N' hN.1.fg hc hD (sub_mem ht0 hsA)).2 h2)
  unfold indL cosInd
  by_cases hq : t0 - x ∈ mulLat c (homAt Sall N N')
  · rw [if_pos (hiff.2 hq), if_pos hq]
  · rw [if_neg (fun h1 => hq (hiff.1 h1)), if_neg hq]

section RfAbs

variable {V : Type} [AddCommGroup V] [Module ℂ V]

open Classical in
theorem rf_filter_reps {Λ₁ Λ₂ C : AddSubgroup V} {S : Finset V} (hS : IsReps Λ₁ Λ₂ S) (hC : Λ₁ ⊓ Λ₂ ≤ C) :
    IsReps Λ₁ (Λ₂ ⊓ C) (S.filter (· ∈ C)) := by
  refine ⟨fun x hx => ?_, fun x hx y hy h => ?_, fun y hy => ?_⟩
  · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx; exact ⟨hS.1 x h1, h2⟩
  · exact hS.2.1 x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1 h
  · obtain ⟨x, hx, hd⟩ := hS.2.2 y hy.1
    refine ⟨x, Finset.mem_filter.2 ⟨hx, ?_⟩, hd⟩
    have h1 : y - x ∈ C := hC ⟨hd, Λ₂.sub_mem hy.1 (hS.1 x hx)⟩
    have : x = y - (y - x) := by abel
    rw [this]; exact C.sub_mem hy.2 h1

open Classical in
theorem rf_sum_ind (C : AddSubgroup V) (S : Finset V) (f : V → ℂ) :
    ∑ t ∈ S, indL C t * f t = ∑ t ∈ S.filter (· ∈ C), f t := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold indL
  split_ifs <;> simp

theorem rf_altE_swap (H : Sesq V) (hH : IsHerm H) (x y : V) : altE H y x = -altE H x y := by
  unfold altE
  rw [hH x y]
  simp

theorem rf_int_swap (H : Sesq V) (hH : IsHerm H) {x y : V} (h : ∃ m : ℤ, altE H x y = (m : ℝ)) : ∃ m : ℤ, altE H y x = (m : ℝ) := by
  obtain ⟨m, hm⟩ := h
  exact ⟨-m, by rw [rf_altE_swap H hH x y, hm, Int.cast_neg]⟩

theorem rf_crit (H : Sesq V) (hH : IsHerm H) (α : V → ℂ) (A B B₁ : AddSubgroup V) (hB : IsSemiChar H B α) (hB₁ : IsSelfDual H B₁)
    (h2 : B₁ ≤ (A ⊓ B₁) ⊔ (B ⊓ B₁)) {y : V} (hy : y ∈ B) (ho : ∀ t ∈ A ⊓ B₁, ∃ m : ℤ, altE H t y = (m : ℝ)) : y ∈ B₁ := by
  rw [← hB₁]
  intro w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 (h2 hw)
  obtain ⟨m, hm⟩ := rf_int_swap H hH (ho a ha)
  obtain ⟨k, hk⟩ := (semicharacterBasic V H hH B α hB).2.2 hy b hb.1
  refine ⟨m + k, ?_⟩
  simp only [altE] at hm hk ⊢
  simp [hm, hk]

theorem rf_hat (H : Sesq V) (hH : IsHerm H) (α : V → ℂ) (A B B₁ Λ : AddSubgroup V) (hA : IsSemiChar H A α) (hB : IsSemiChar H B α)
    (hB₁s : IsSemiChar H B₁ α) (hB₁ : IsSelfDual H B₁) (h1 : A ⊓ B₁ ≤ Λ) (h2 : B₁ ≤ (A ⊓ B₁) ⊔ (B ⊓ B₁))
    (SA : Finset V) (hSA : IsReps B (Λ ⊓ A) SA) {y : V} (hy : y ∈ B) :
    ∑ t ∈ SA, indL B₁ t * (brk H y t)⁻¹ = indL B₁ y * ((open Classical in SA.filter (· ∈ B₁)).card : ℂ) := by
  classical
  have hF6 : B ⊓ (Λ ⊓ A) ≤ B₁ := fun m hm =>
    rf_crit H hH α A B B₁ hB hB₁ h2 hm.1 fun t ht => (semicharacterBasic V H hH A α hA).2.2 ht.1 m hm.2.2
  have hF := rf_filter_reps hSA hF6
  rw [rf_sum_ind]
  by_cases hy1 : y ∈ B₁
  · have : ∀ t ∈ SA.filter (· ∈ B₁), (brk H y t)⁻¹ = 1 := by
      intro t ht
      rw [brk_one_of_int H ((semicharacterBasic V H hH B₁ α hB₁s).2.2 (Finset.mem_filter.1 ht).2 y hy1), inv_one]
    rw [Finset.sum_congr rfl this]
    simp [indL, hy1]
  · have hex : ∃ t ∈ A ⊓ B₁, ¬ ∃ m : ℤ, altE H t y = (m : ℝ) := by
      by_contra hcon
      exact hy1 (rf_crit H hH α A B B₁ hB hB₁ h2 hy fun t ht => by
        by_contra hn
        exact hcon ⟨t, ht, hn⟩)
    obtain ⟨t₀, ht₀, hne⟩ := hex
    have h0 := char_sum_zero hF (fun t => (brk H y t)⁻¹) (fun x x' => by rw [brk_add_right, mul_inv])
      (fun m _ hm => by rw [brk_one_of_int H ((semicharacterBasic V H hH B α hB).2.2 hm y hy), inv_one])
      (x₀ := t₀) ⟨⟨h1 ht₀, ht₀.1⟩, ht₀.2⟩ (fun h => hne (int_of_brk_one H (inv_eq_one.1 h)))
    rw [h0]
    simp [indL, hy1]

theorem rf_repsB (H : Sesq V) (hH : IsHerm H) (α : V → ℂ) (A B B₁ Λ : AddSubgroup V) (hB : IsSemiChar H B α) (hΛ : IsSemiChar H Λ α)
    (hB₁ : IsSelfDual H B₁) (h1 : A ⊓ B₁ ≤ Λ) (h2 : B₁ ≤ (A ⊓ B₁) ⊔ (B ⊓ B₁)) (SB : Finset V) (hSB : IsReps Λ B SB) :
    IsReps Λ B₁ (open Classical in SB.filter (· ∈ B₁)) := by
  classical
  have hF3 : Λ ⊓ B ≤ B₁ := fun m hm =>
    rf_crit H hH α A B B₁ hB hB₁ h2 hm.2 fun t ht => (semicharacterBasic V H hH Λ α hΛ).2.2 (h1 ht) m hm.1
  have hF := rf_filter_reps hSB hF3
  refine ⟨fun x hx => (hF.1 x hx).2, hF.2.1, fun y hy => ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 (h2 hy)
  obtain ⟨x, hx, hd⟩ := hF.2.2 b hb
  refine ⟨x, hx, ?_⟩
  have : a + b - x = a + (b - x) := by abel
  rw [this]; exact Λ.add_mem (h1 ha) hd

theorem rf_count (A B A₁ B₁ Λ : AddSubgroup V) (hF6 : B ⊓ (Λ ⊓ A) ≤ B₁) (h4 : Λ ⊓ A ≤ A₁)
    (h5 : ∀ r ∈ Λ ⊓ A₁, ∃ u ∈ Λ ⊓ A, u - r ∈ B₁) (SA SA₁ : Finset V) (hSA : IsReps B (Λ ⊓ A) SA) (hSA₁ : IsReps B₁ (Λ ⊓ A₁) SA₁) :
    (SA.card : ℂ) = (SA₁.card : ℂ) * ((open Classical in SA.filter (· ∈ B₁)).card : ℂ) := by
  classical
  have hu : ∀ r ∈ SA₁, ∃ u ∈ Λ ⊓ A, u - r ∈ B₁ := fun r hr => h5 r (hSA₁.1 r hr)
  choose! u hu1 hu2 using hu
  have hinv : ∀ x ∈ Λ ⊓ A, ∀ m ∈ Λ ⊓ A, m ∈ B → indL B₁ (x + m) = indL B₁ x := by
    intro x _ m hm hmB
    have hm1 : m ∈ B₁ := hF6 ⟨hmB, hm⟩
    unfold indL
    by_cases hx : x ∈ B₁
    · rw [if_pos hx, if_pos (B₁.add_mem hx hm1)]
    · rw [if_neg hx, if_neg]
      intro h
      apply hx
      have : x = x + m - m := by abel
      rw [this]; exact B₁.sub_mem h hm1
  have hrow : ∀ t ∈ SA, ∑ r ∈ SA₁, indL B₁ (-u r + t) = 1 := by
    intro t ht
    obtain ⟨r₀, hr₀, hd⟩ := hSA₁.2.2 t ⟨(hSA.1 t ht).1, h4 (hSA.1 t ht)⟩
    rw [Finset.sum_eq_single r₀]
    · have : -u r₀ + t = (t - r₀) - (u r₀ - r₀) := by abel
      rw [this]; unfold indL; rw [if_pos (B₁.sub_mem hd (hu2 r₀ hr₀))]
    · intro r hr hne
      unfold indL
      rw [if_neg]
      intro h
      apply hne
      apply hSA₁.2.1 r hr r₀ hr₀
      have : r - r₀ = (t - r₀) - (-u r + t) - (u r - r) := by abel
      rw [this]; exact B₁.sub_mem (B₁.sub_mem hd h) (hu2 r hr)
    · intro h; exact absurd hr₀ h
  have hcol : ∀ r ∈ SA₁, ∑ t ∈ SA, indL B₁ (-u r + t) = ((SA.filter (· ∈ B₁)).card : ℂ) := by
    intro r hr
    rw [sum_reps_shift hSA (indL B₁) hinv ((Λ ⊓ A).neg_mem (hu1 r hr))]
    have := rf_sum_ind B₁ SA (fun _ => (1 : ℂ))
    simp only [mul_one] at this
    rw [this]; simp
  calc (SA.card : ℂ) = ∑ t ∈ SA, (1 : ℂ) := by simp
    _ = ∑ t ∈ SA, ∑ r ∈ SA₁, indL B₁ (-u r + t) := Finset.sum_congr rfl fun t ht => (hrow t ht).symm
    _ = ∑ r ∈ SA₁, ∑ t ∈ SA, indL B₁ (-u r + t) := Finset.sum_comm
    _ = ∑ r ∈ SA₁, ((SA.filter (· ∈ B₁)).card : ℂ) := Finset.sum_congr rfl hcol
    _ = _ := by simp

theorem rf_zero (H : Sesq V) (α : V → ℂ) (A B A₁ B₁ Λ : AddSubgroup V) (hyp : SplitHyp H α A B Λ) (hyp₁ : SplitHyp H α A₁ B₁ Λ)
    (h1 : A ⊓ B₁ ≤ Λ) (h2 : B₁ ≤ (A ⊓ B₁) ⊔ (B ⊓ B₁)) (h4 : Λ ⊓ A ≤ A₁) (h5 : ∀ r ∈ Λ ⊓ A₁, ∃ u ∈ Λ ⊓ A, u - r ∈ B₁)
    (SA SB SA₁ SB₁ : Finset V) (hSA : IsReps B (Λ ⊓ A) SA) (hSB : IsReps Λ B SB) (hSA₁ : IsReps B₁ (Λ ⊓ A₁) SA₁) (hSB₁ : IsReps Λ B₁ SB₁)
    (vol : ℝ) (θ : V → ℂ) (hθ : θ ∈ fixedBy H α Λ) (z : V) :
    xiS H α vol SA SB (indL B₁) θ z = xiS H α vol SA₁ SB₁ (indL B₁) θ z := by
  classical
  rw [twist_induced_vanish V H α A₁ B₁ Λ hyp₁ SA₁ SB₁ hSA₁ hSB₁ vol θ z]
  obtain ⟨hH, hA, hB, -, -, hΛ, -⟩ := hyp
  obtain ⟨-, -, hB₁s, -, hB₁, -⟩ := hyp₁
  have hF6 : B ⊓ (Λ ⊓ A) ≤ B₁ := fun m hm =>
    rf_crit H hH α A B B₁ hB hB₁ h2 hm.1 fun t ht => (semicharacterBasic V H hH A α hA).2.2 ht.1 m hm.2.2
  have hcount := rf_count A B A₁ B₁ Λ hF6 h4 h5 SA SA₁ hSA hSA₁
  have hn : ((SA.filter (· ∈ B₁)).card : ℂ) ≠ 0 := by
    obtain ⟨x, hx, -⟩ := (rf_filter_reps hSA hF6).2.2 0 (AddSubgroup.zero_mem _)
    exact_mod_cast (Finset.card_pos.2 ⟨x, hx⟩).ne'
  have hterm : ∀ y ∈ SB, hatS H vol SA (indL B₁) y * α y * opU H y θ z =
      (((Real.sqrt vol : ℝ) : ℂ)⁻¹ * (((vol : ℝ) : ℂ) / (SA₁.card : ℂ))) * (indL B₁ y * (α y * opU H y θ z)) := by
    intro y hy
    unfold hatS
    rw [rf_hat H hH α A B B₁ Λ hA hB hB₁s hB₁ h1 h2 SA hSA (hSB.1 y hy), hcount]
    by_cases h0 : (SA₁.card : ℂ) = 0
    · simp [h0]
    · field_simp
  show ∑ y ∈ SB, hatS H vol SA (indL B₁) y * α y * opU H y θ z = _
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, rf_sum_ind]
  congr 1
  exact sum_reps_eq (rf_repsB H hH α A B B₁ Λ hB hΛ hB₁ h1 h2 SB hSB) hSB₁ (fun y => α y * opU H y θ z)
    (fun x hx y hy hyΛ => InterClass_of semicharacterHom V H hH Λ B₁ α hB₁s θ hθ x hx y hy hyΛ z)

theorem rf_abs (H : Sesq V) (α : V → ℂ) (A B A₁ B₁ Λ : AddSubgroup V) (hyp : SplitHyp H α A B Λ) (hyp₁ : SplitHyp H α A₁ B₁ Λ)
    (h1 : A ⊓ B₁ ≤ Λ) (h2 : B₁ ≤ (A ⊓ B₁) ⊔ (B ⊓ B₁)) (h4 : Λ ⊓ A ≤ A₁) (h5 : ∀ r ∈ Λ ⊓ A₁, ∃ u ∈ Λ ⊓ A, u - r ∈ B₁)
    (SA SB SA₁ SB₁ T : Finset V) (hSA : IsReps B (Λ ⊓ A) SA) (hSB : IsReps Λ B SB) (hSA₁ : IsReps B₁ (Λ ⊓ A₁) SA₁) (hSB₁ : IsReps Λ B₁ SB₁)
    (hT : IsReps B A T) (vol : ℝ) (θ : V → ℂ) (hθ : θ ∈ fixedBy H α Λ) {s : V} (hs : s ∈ A) (z : V) :
    xiInd H α vol B₁ SA₁ SB₁ θ s z = ∑ t ∈ T, indL B₁ (t - s) * xiInd H α vol B SA SB θ t z := by
  classical
  have hcl := twist_induced_class V H α A B Λ hyp SA SB hSA hSB vol θ hθ
  have hES := twist_expand_series V H α A B Λ hyp SA SB hSA hSB vol θ hθ
  have hZ := rf_zero H α A B A₁ B₁ Λ hyp hyp₁ h1 h2 h4 h5 SA SB SA₁ SB₁ hSA hSB hSA₁ hSB₁ vol θ hθ
  obtain ⟨hH, hA, hB, -, -, hΛ, -⟩ := hyp
  obtain ⟨-, -, hB₁s, -, hB₁, -⟩ := hyp₁
  have hAB : B ⊓ A ≤ B₁ := fun m hm =>
    rf_crit H hH α A B B₁ hB hB₁ h2 hm.1 fun t ht => (semicharacterBasic V H hH A α hA).2.2 ht.1 m hm.2
  have hF6 : B ⊓ (Λ ⊓ A) ≤ B₁ := fun m hm => hAB ⟨hm.1, hm.2.2⟩
  have hneg := (semicharacterBasic V H hH A α hA).2.1

  have hinner : ∀ v, ∑ t ∈ T, indL B₁ t * xiInd H α vol B SA SB θ t v = xiS H α vol SA₁ SB₁ (indL B₁) θ v := by
    intro v
    rw [← hZ v, hES (indL B₁) v, rf_sum_ind, rf_sum_ind]
    have e : Λ ⊓ A ⊓ B₁ = A ⊓ B₁ := le_antisymm (fun m hm => ⟨hm.1.2, hm.2⟩) (fun m hm => ⟨⟨h1 hm, hm.1⟩, hm.2⟩)
    have hr1 := rf_filter_reps hT hAB
    have hr2 := rf_filter_reps hSA hF6
    rw [e] at hr2
    exact sum_reps_eq hr1 hr2 (fun t => xiInd H α vol B SA SB θ t v) (fun x hx m hm hmB => hcl x hx.1 m hm.1 hmB v)

  have hinv : ∀ x ∈ A, ∀ m ∈ A, m ∈ B → indL B₁ (x + m - s) * xiInd H α vol B SA SB θ (x + m) z =
      indL B₁ (x - s) * xiInd H α vol B SA SB θ x z := by
    intro x hx m hm hmB
    rw [hcl x hx m hm hmB z]
    congr 1
    have hm1 : m ∈ B₁ := hAB ⟨hmB, hm⟩
    unfold indL
    by_cases hx1 : x - s ∈ B₁
    · rw [if_pos hx1, if_pos]
      have : x + m - s = (x - s) + m := by abel
      rw [this]; exact B₁.add_mem hx1 hm1
    · rw [if_neg hx1, if_neg]
      intro h
      apply hx1
      have : x - s = (x + m - s) - m := by abel
      rw [this]; exact B₁.sub_mem h hm1
  rw [← sum_reps_shift hT (fun t => indL B₁ (t - s) * xiInd H α vol B SA SB θ t z) hinv hs]
  have hterm : ∀ t ∈ T, indL B₁ (s + t - s) * xiInd H α vol B SA SB θ (s + t) z =
      α (-s) * opU H (-s) (fun v => indL B₁ t * xiInd H α vol B SA SB θ t v) z := by
    intro t ht
    rw [Inv.opU_const_mul, mul_left_comm, xiInd_shift H hH α A hA vol B SA SB θ (A.neg_mem hs) (hT.1 t ht) z]
    have e1 : s + t - s = t := by abel
    have e2 : t - -s = s + t := by abel
    rw [e1, e2]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Inv.opU_finset_sum, funext hinner, hneg s hs]
  rfl

end RfAbs

section RfLat

variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

theorem rf_B_iff (SS : Finset (HeightOneSpectrum (𝓞 E))) (M : Submodule (𝓞 E) W) (c : ℕ) (x : W) :
    x ∈ twist₂ M c (expS SS) ↔ ∀ Q : HeightOneSpectrum (𝓞 E), (expS SS Q = 1 → (c : E)⁻¹ • x ∈ localization₂ Q.asIdeal M) ∧
      (expS SS Q = 0 → x ∈ localization₂ Q.asIdeal M) ∧ (expS SS Q = -1 → (c : E) • x ∈ localization₂ Q.asIdeal M) := by
  simp only [twist₂, Submodule.mem_iInf, Submodule.mem_comap]
  refine forall_congr' fun Q => ?_
  unfold expS
  split_ifs <;> simp

theorem rf_A_iff (SS : Finset (HeightOneSpectrum (𝓞 E))) (M : Submodule (𝓞 E) W) (c : ℕ) (x : W) :
    x ∈ twist₂ M c (fun Q => -expS SS Q) ↔ ∀ Q : HeightOneSpectrum (𝓞 E), (expS SS Q = 1 → (c : E) • x ∈ localization₂ Q.asIdeal M) ∧
      (expS SS Q = 0 → x ∈ localization₂ Q.asIdeal M) ∧ (expS SS Q = -1 → (c : E)⁻¹ • x ∈ localization₂ Q.asIdeal M) := by
  simp only [twist₂, Submodule.mem_iInf, Submodule.mem_comap]
  refine forall_congr' fun Q => ?_
  unfold expS
  split_ifs <;> simp

theorem rf_of_inv (L : Submodule (𝓞 E) W) {c : ℕ} (hc : 0 < c) {x : W} (h : (c : E)⁻¹ • x ∈ L) : x ∈ L := by
  have hc' : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have e : x = (c : 𝓞 E) • ((c : E)⁻¹ • x) := by
    rw [← algebraMap_smul E (c : 𝓞 E), map_natCast, smul_smul, mul_inv_cancel₀ hc', one_smul]
  rw [e]
  exact L.smul_mem _ h

theorem rf_inv_dvd (L : Submodule (𝓞 E) W) {c D : ℕ} (hD : 0 < D) (hcD : c ∣ D) {x : W} (h : (D : E)⁻¹ • x ∈ L) : (c : E)⁻¹ • x ∈ L := by
  obtain ⟨k, rfl⟩ := hcD
  have hk : (k : E) ≠ 0 := by
    have : k ≠ 0 := by rintro rfl; simp at hD
    exact_mod_cast this
  have e : (c : E)⁻¹ • x = (k : 𝓞 E) • (((c * k : ℕ) : E)⁻¹ • x) := by
    rw [← algebraMap_smul E (k : 𝓞 E), map_natCast, smul_smul, Nat.cast_mul, mul_inv, mul_comm ((c : E))⁻¹,
      ← mul_assoc, mul_inv_cancel₀ hk, one_mul]
  rw [e]
  exact L.smul_mem _ h

theorem rf_smul_dvd (L : Submodule (𝓞 E) W) {c D : ℕ} (hcD : c ∣ D) {x : W} (h : (c : E) • x ∈ L) : (D : E) • x ∈ L := by
  obtain ⟨k, rfl⟩ := hcD
  have e : ((c * k : ℕ) : E) • x = (k : 𝓞 E) • ((c : E) • x) := by
    rw [← algebraMap_smul E (k : 𝓞 E), map_natCast, smul_smul, Nat.cast_mul, mul_comm]
  rw [e]
  exact L.smul_mem _ h

theorem rf_loc_div (M : Submodule (𝓞 E) W) (Q : HeightOneSpectrum (𝓞 E)) {K : ℕ} (hK : 0 < K) {ε t : 𝓞 E} (ht : t ∉ Q.asIdeal)
    (hd : (K : 𝓞 E) ∣ t * ε) {w : W} (hw : w ∈ localization₂ Q.asIdeal M) : (K : E)⁻¹ • (ε • w) ∈ localization₂ Q.asIdeal M := by
  have hKE : (K : E) ≠ 0 := by exact_mod_cast hK.ne'
  obtain ⟨u, hu, huw⟩ := hw
  obtain ⟨r, hr⟩ := hd
  refine ⟨u * t, Submonoid.mul_mem _ hu ht, ?_⟩
  have e1 : (u * t) • ((K : E)⁻¹ • (ε • w)) = r • (u • w) := by
    rw [← IsScalarTower.algebraMap_smul E (u * t), ← IsScalarTower.algebraMap_smul E ε w, ← IsScalarTower.algebraMap_smul E r (u • w),
      ← IsScalarTower.algebraMap_smul E u w, smul_smul, smul_smul, smul_smul]
    congr 1
    have h2 := congrArg (algebraMap (𝓞 E) E) hr
    simp only [map_mul, map_natCast] at h2 ⊢
    field_simp
    linear_combination (algebraMap (𝓞 E) E u) * h2
  rw [e1]; exact M.smul_mem r huw

theorem mem_of_mem_twisted_both (SS : Finset (HeightOneSpectrum (𝓞 E))) (M : Submodule (𝓞 E) W) {c D : ℕ} (hc : 0 < c) (hD : 0 < D) {x : W}
    (hA : x ∈ twist₂ M D (fun Q => -expS SS Q)) (hB : x ∈ twist₂ M c (expS SS)) : x ∈ M := by
  rw [rf_A_iff] at hA
  rw [rf_B_iff] at hB
  apply mem_of_forall_locP
  intro Q
  rcases expS_cases SS Q with h | h | h
  · exact rf_of_inv _ hc ((hB Q).1 h)
  · exact (hB Q).2.1 h
  · exact rf_of_inv _ hD ((hA Q).2.2 h)

theorem twisted_mem_of_divides (SS : Finset (HeightOneSpectrum (𝓞 E))) (M : Submodule (𝓞 E) W) {c D : ℕ} (hD : 0 < D) (hcD : c ∣ D) {x : W}
    (hx : x ∈ M) (hA : x ∈ twist₂ M D (fun Q => -expS SS Q)) : x ∈ twist₂ M c (fun Q => -expS SS Q) := by
  rw [rf_A_iff] at hA ⊢
  intro Q
  exact ⟨fun _ => nat_smul_mem _ c (le_locP' M Q hx), fun _ => le_locP' M Q hx, fun h => rf_inv_dvd _ hD hcD ((hA Q).2.2 h)⟩

theorem exists_twisted_approximant (SS : Finset (HeightOneSpectrum (𝓞 E))) (hSS : ∀ P ∈ SS, conjPrime₂ P ∉ SS) (M : Submodule (𝓞 E) W) {c D : ℕ} (hc : 0 < c) (hD : 0 < D)
    (hcD : c ∣ D) {r : W} (hr : r ∈ M) : ∃ u ∈ M, u ∈ twist₂ M D (fun Q => -expS SS Q) ∧ u - r ∈ twist₂ M c (expS SS) := by
  obtain ⟨ε, h1, h2⟩ := exists_idem SS hSS D hD
  refine ⟨ε • r, M.smul_mem ε hr, ?_, ?_⟩
  · refine tw_mem_of M D hD _ hr ε (fun Q => ?_) (fun Q hQ => h2 Q (expS_eq_neg_one SS Q hQ))
    rcases expS_cases SS Q with h | h | h <;> simp [h]
  · have e : ε • r - r = (-(1 - ε)) • r := by rw [neg_sub, sub_smul, one_smul]
    rw [e]
    refine tw_mem_of M c hc _ hr _ (expS_cases SS) (fun Q hQ => ?_)
    obtain ⟨t, ht, hd⟩ := h1 Q (expS_eq_one SS Q hQ)
    refine ⟨t, ht, ?_⟩
    have h3 : (c : 𝓞 E) ∣ (D : 𝓞 E) := by exact_mod_cast (Nat.cast_dvd_cast (α := 𝓞 E) hcD)
    rw [mul_neg]
    exact (dvd_neg).2 (h3.trans hd)

theorem twisted_decomposition_sum (SS : Finset (HeightOneSpectrum (𝓞 E))) (hSS : ∀ P ∈ SS, conjPrime₂ P ∉ SS) (M : Submodule (𝓞 E) W) {c D : ℕ} (hc : 0 < c) (hD : 0 < D)
    (hcD : c ∣ D) {y : W} (hy : y ∈ twist₂ M c (expS SS)) :
    ∃ a b : W, a ∈ twist₂ M D (fun Q => -expS SS Q) ∧ a ∈ twist₂ M c (expS SS) ∧ b ∈ twist₂ M D (expS SS) ∧ b ∈ twist₂ M c (expS SS) ∧ a + b = y := by
  obtain ⟨ε, h1, h2⟩ := exists_idem SS hSS (c * D) (Nat.mul_pos hc hD)
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have hDE : (D : E) ≠ 0 := by exact_mod_cast hD.ne'
  refine ⟨ε • y, (1 - ε) • y, ?_, Submodule.smul_mem _ ε hy, ?_, Submodule.smul_mem _ (1 - ε) hy, by rw [← add_smul]; simp⟩
  · have hy' := (rf_B_iff SS M c y).1 hy
    rw [rf_A_iff]
    intro Q
    refine ⟨fun h => ?_, fun h => Submodule.smul_mem _ ε ((hy' Q).2.1 h), fun h => ?_⟩
    · exact nat_smul_mem _ D (Submodule.smul_mem _ ε (rf_of_inv _ hc ((hy' Q).1 h)))
    · obtain ⟨t, ht, hd⟩ := h2 Q (expS_eq_neg_one SS Q (by rw [h]; rfl))
      have h3 := rf_loc_div M Q (Nat.mul_pos hc hD) ht hd ((hy' Q).2.2 h)
      have e : ((c * D : ℕ) : E)⁻¹ • (ε • ((c : E) • y)) = (D : E)⁻¹ • (ε • y) := by
        rw [← IsScalarTower.algebraMap_smul E ε, ← IsScalarTower.algebraMap_smul E ε y, smul_smul, smul_smul, smul_smul]
        congr 1
        push_cast
        field_simp
      rwa [e] at h3
  · have hy' := (rf_B_iff SS M c y).1 hy
    rw [rf_B_iff]
    intro Q
    refine ⟨fun h => ?_, fun h => Submodule.smul_mem _ (1 - ε) ((hy' Q).2.1 h), fun h => ?_⟩
    · obtain ⟨t, ht, hd⟩ := h1 Q (expS_eq_one SS Q h)
      have h3 : (D : 𝓞 E) ∣ ((c * D : ℕ) : 𝓞 E) := by push_cast; exact Dvd.intro_left _ rfl
      exact rf_loc_div M Q hD ht (h3.trans hd) (rf_of_inv _ hc ((hy' Q).1 h))
    · have h3 := Submodule.smul_mem _ (1 - ε) (rf_smul_dvd _ hcD ((hy' Q).2.2 h))
      rwa [smul_comm] at h3

end RfLat

section RfConc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] [Nonempty ι] {a b : ℕ}

theorem rf_mem_laV (emb : ι → E →+* ℂ) {δ : ℂ} (hδ : δ ≠ 0) (M : Submodule (𝓞 E) (HomE E a b)) (x : HomE E a b) :
    embH emb δ x ∈ laV emb δ M ↔ x ∈ M := ti_mem_laV emb hδ M x

theorem rf_facts (emb : ι → E →+* ℂ) {δ : ℂ} (hδ : δ ≠ 0) (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E)))
    (hSS : ∀ P ∈ SS, conjPrime₂ P ∉ SS) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) {c D : ℕ} (hc : 0 < c) (hD : 0 < D)
    (hcD : c ∣ D) :
    AC emb δ AA0 SS N N' D ⊓ BC emb δ AA0 SS N N' c ≤ LamC emb δ AA0 N N' ∧
    BC emb δ AA0 SS N N' c ≤ (AC emb δ AA0 SS N N' D ⊓ BC emb δ AA0 SS N N' c) ⊔ (BC emb δ AA0 SS N N' D ⊓ BC emb δ AA0 SS N N' c) ∧
    LamC emb δ AA0 N N' ⊓ AC emb δ AA0 SS N N' D ≤ AC emb δ AA0 SS N N' c ∧
    ∀ r ∈ LamC emb δ AA0 N N' ⊓ AC emb δ AA0 SS N N' c, ∃ u ∈ LamC emb δ AA0 N N' ⊓ AC emb δ AA0 SS N N' D, u - r ∈ BC emb δ AA0 SS N N' c := by
  unfold AC BC LamC halfAO halfBO
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro v ⟨⟨x, hx, rfl⟩, hv⟩
    exact (rf_mem_laV emb hδ _ x).2 (mem_of_mem_twisted_both SS _ hc hD hx ((rf_mem_laV emb hδ _ x).1 hv))
  · rintro v ⟨y, hy, rfl⟩
    obtain ⟨p, q, h1, h2, h3, h4, rfl⟩ := twisted_decomposition_sum SS hSS _ hc hD hcD hy
    refine AddSubgroup.mem_sup.2 ⟨embH emb δ p, ⟨(rf_mem_laV emb hδ _ p).2 h1, (rf_mem_laV emb hδ _ p).2 h2⟩, embH emb δ q,
      ⟨(rf_mem_laV emb hδ _ q).2 h3, (rf_mem_laV emb hδ _ q).2 h4⟩, (map_add _ _ _).symm⟩
  · rintro v ⟨⟨x, hx, rfl⟩, hv⟩
    exact (rf_mem_laV emb hδ _ x).2 (twisted_mem_of_divides SS _ hD hcD hx ((rf_mem_laV emb hδ _ x).1 hv))
  · rintro v ⟨⟨r, hr, rfl⟩, -⟩
    obtain ⟨u, hu, hu1, hu2⟩ := exists_twisted_approximant SS hSS _ hc hD hcD hr
    refine ⟨embH emb δ u, ⟨(rf_mem_laV emb hδ _ u).2 hu, (rf_mem_laV emb hδ _ u).2 hu1⟩, ?_⟩
    rw [← map_sub]
    exact (rf_mem_laV emb hδ _ _).2 hu2

end RfConc

theorem refine_of {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (h : A.HeisHyp a b Sall) :
    A.Refine a b Sall D := by
  obtain ⟨hδ, hne, hSS, -, hL⟩ := h
  intro N N' c s hN hN' hc hcD hD hs T hT z
  obtain ⟨hθ, hlev⟩ := hL N N' hN hN'
  obtain ⟨hyp₁, hr1, hr2, -⟩ := hlev c hc
  obtain ⟨hyp, hR1, hR2, -⟩ := hlev D hD
  obtain ⟨f1, f2, f4, f5⟩ := rf_facts (X.embC A.σ₀) hδ A.AA Sall hSS N N' hc hD hcD
  exact rf_abs _ _ _ _ _ _ _ hyp hyp₁ f1 f2 f4 f5 _ _ _ _ T (repsOf_spec _ _ hR1) (repsOf_spec _ _ hR2) (repsOf_spec _ _ hr1)
    (repsOf_spec _ _ hr2) hT _ _ hθ ⟨s, hs, rfl⟩ z

theorem induced_kernel_degree_compat {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (hD : 0 < D)
    (h : A.HeisHyp a b Sall) : A.IndTieD a b Sall D := indTieD_of A a b Sall D hD h (liftIndep_of A a b Sall h) (refine_of A a b Sall D h)

section HhLat

open scoped Pointwise

variable {E : Type} [Field E] [NumberField E] [StarRing E]
  {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

theorem hh_tw_of (M : Submodule (𝓞 E) W) {c : ℕ} (hc : 0 < c) (e : HeightOneSpectrum (𝓞 E) → ℤ) (he : ∀ Q, e Q = 1 ∨ e Q = 0 ∨ e Q = -1)
    {x : W} (hx : x ∈ M) : (c : 𝓞 E) • x ∈ twist₂ M c e := by
  have hcE : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  rw [mem_twO]
  intro Q
  rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E]
  apply le_locP'
  rcases he Q with h | h | h
  · rw [h, zpow_one, smul_smul, inv_mul_cancel₀ hcE, one_smul]; exact hx
  · rw [h, zpow_zero, inv_one, one_smul]; exact nat_smul_mem _ c hx
  · rw [h, zpow_neg_one, inv_inv]; exact nat_smul_mem _ c (nat_smul_mem _ c hx)

theorem hh_of_tw (M : Submodule (𝓞 E) W) {c : ℕ} (hc : 0 < c) (e : HeightOneSpectrum (𝓞 E) → ℤ) (he : ∀ Q, e Q = 1 ∨ e Q = 0 ∨ e Q = -1)
    {x : W} (hx : x ∈ twist₂ M c e) : (c : 𝓞 E) • x ∈ M := by
  have hcE : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E]
  apply mem_of_forall_locP
  intro Q
  have hQ := (mem_twO _ _ _ _).1 hx Q
  rcases he Q with h | h | h
  · rw [h, zpow_one] at hQ
    have h2 := nat_smul_mem _ c (nat_smul_mem _ c hQ)
    rwa [smul_smul (c : E) (c : E)⁻¹, mul_inv_cancel₀ hcE, one_smul] at h2
  · rw [h, zpow_zero, inv_one, one_smul] at hQ; exact nat_smul_mem _ c hQ
  · rw [h, zpow_neg_one, inv_inv] at hQ; exact hQ

theorem hh_tw_lattice {n : ℕ} (N' : Submodule (𝓞 E) (Sp E n)) (hL : Submodule.IsLattice E N') {c : ℕ} (hc : 0 < c)
    (e : HeightOneSpectrum (𝓞 E) → ℤ) (he : ∀ Q, e Q = 1 ∨ e Q = 0 ∨ e Q = -1) : Submodule.IsLattice E (twist₂ N' c e) := by
  have hc0 : (c : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have hcE : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  refine ⟨fg_of_scale _ _ hL.fg (c : 𝓞 E) hc0 fun x hx => hh_of_tw N' hc e he hx, ?_⟩
  rw [eq_top_iff, ← hL.span_eq_top]
  apply Submodule.span_le.2
  intro y hy
  have h1 : (c : 𝓞 E) • y ∈ twist₂ N' c e := hh_tw_of N' hc e he hy
  have h2 : (c : E)⁻¹ • ((c : 𝓞 E) • y) = y := by
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul, inv_mul_cancel₀ hcE, one_smul]
  rw [SetLike.mem_coe, ← h2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

variable {a b : ℕ}

theorem hh_perO_fg (AA0 : Submodule (𝓞 E) E) (hAA : AA0.FG) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b))
    (hN : Submodule.IsLattice E N) (hN' : Submodule.IsLattice E N') : (perO AA0 N N').FG := by
  have sa := stdLat_lattice (E := E) (n := a)
  have sb := stdLat_lattice (E := E) (n := b)
  obtain ⟨νa₁, ha₁0, ha₁⟩ := exists_smul_le (stdLat E a) N sa.fg hN.span_eq_top
  obtain ⟨νb₁, hb₁0, hb₁⟩ := exists_smul_le N' (stdLat E b) hN'.fg sb.span_eq_top
  have h1 := perO_scale AA0 N (stdLat E a) N' (stdLat E b) νa₁ νb₁ ha₁ hb₁
  have hone : Submodule.span E (((1 : Submodule (𝓞 E) E) : Submodule (𝓞 E) E) : Set E) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h1 : (1 : E) ∈ Submodule.span E (((1 : Submodule (𝓞 E) E) : Submodule (𝓞 E) E) : Set E) :=
      Submodule.subset_span (Submodule.one_le.1 le_rfl)
    have := Submodule.smul_mem _ x h1
    simpa using this
  obtain ⟨ν₀, h00, h0⟩ := exists_smul_le AA0 (1 : Submodule (𝓞 E) E) hAA hone
  have hM₀ : (perO AA0 (stdLat E a) (stdLat E b)).FG := by
    refine fg_of_scale _ _ (homO_std_fg (E := E) (a := a) (b := b)) ν₀ h00 ?_
    have hle : perO AA0 (stdLat E a) (stdLat E b) ≤ (homO (stdLat E a) (stdLat E b)).comap
        (ν₀ • (LinearMap.id : HomE E a b →ₗ[𝓞 E] HomE E a b)) := by
      apply Submodule.span_le.2
      rintro _ ⟨r, hr, x, hx, rfl⟩
      show ν₀ • (r • x) ∈ homO (stdLat E a) (stdLat E b)
      obtain ⟨ρ, hρ⟩ := Submodule.mem_one.1 (h0 r hr)
      rw [smul_smul_eq_of (ν₀) r x ρ hρ]
      exact Submodule.smul_mem _ ρ hx
    exact fun x hx => hle hx
  exact fg_of_scale _ _ hM₀ _ (mul_ne_zero ha₁0 hb₁0) h1

variable {ι : Type} [Fintype ι]

theorem hh_cover (emb : ι → E →+* ℂ) (δ : ℂ) (M₁ M₂ : Submodule (𝓞 E) (HomE E a b)) (hM : M₂.FG) (ν : 𝓞 E) (hν : ν ≠ 0)
    (h : ∀ x ∈ M₂, ν • x ∈ M₁) : ∃ R : Set (VV ι a b), R.Finite ∧ ∀ x ∈ laV emb δ M₂, ∃ ρ ∈ R, x - ρ ∈ laV emb δ M₁ := by
  have : Finite (𝓞 E ⧸ Ideal.span {ν}) := Ideal.finiteQuotientOfFreeOfNeBot _ (by rwa [Ne, Ideal.span_singleton_eq_bot])
  have : Module.Finite (𝓞 E) M₂ := Module.Finite.iff_fg.2 hM
  have : Subsingleton (M₂ ⧸ (⊤ : Submodule (𝓞 E) M₂)) :=
    ⟨fun p q => Quotient.inductionOn₂' p q fun x y => (Submodule.Quotient.eq ⊤).2 Submodule.mem_top⟩
  have hfin : Finite (M₂ ⧸ (Ideal.span {ν} • (⊤ : Submodule (𝓞 E) M₂))) :=
    Submodule.finite_quotient_smul (Ideal.span {ν}) Module.Finite.fg_top
  let out : M₂ ⧸ (Ideal.span {ν} • (⊤ : Submodule (𝓞 E) M₂)) → M₂ := Function.surjInv (Submodule.Quotient.mk_surjective _)
  refine ⟨Set.range fun q => embH emb δ ((out q : M₂) : HomE E a b), Set.finite_range _, ?_⟩
  rintro _ ⟨m, hm, rfl⟩
  refine ⟨_, ⟨Submodule.Quotient.mk ⟨m, hm⟩, rfl⟩, ?_⟩
  have h1 : Submodule.Quotient.mk (p := Ideal.span {ν} • (⊤ : Submodule (𝓞 E) M₂)) (out (Submodule.Quotient.mk ⟨m, hm⟩))
      = Submodule.Quotient.mk ⟨m, hm⟩ := Function.surjInv_eq _ _
  have h2 := (Submodule.Quotient.eq _).1 h1
  have h2' : out (Submodule.Quotient.mk ⟨m, hm⟩) - ⟨m, hm⟩ ∈ ν • (⊤ : Submodule (𝓞 E) M₂) := by
    rw [← Submodule.ideal_span_singleton_smul]; exact h2
  obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h2'
  have h3 : ((out (Submodule.Quotient.mk ⟨m, hm⟩) : M₂) : HomE E a b) - m = ν • (y : HomE E a b) := by
    have := congrArg (Subtype.val) hy
    simpa using this.symm
  refine ⟨m - ((out (Submodule.Quotient.mk ⟨m, hm⟩) : M₂) : HomE E a b), ?_, map_sub _ _ _⟩
  have h4 : m - ((out (Submodule.Quotient.mk ⟨m, hm⟩) : M₂) : HomE E a b) = -(ν • (y : HomE E a b)) := by rw [← h3]; abel
  rw [h4]
  exact neg_mem (h _ y.2)

end HhLat

theorem heisHyp_of {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (h : A.LaHyp a b Sall) :
    A.HeisHyp a b Sall := by
  obtain ⟨hδ, hne, hSS, hAA, hFG, hall⟩ := h
  refine ⟨hδ, hne, hSS, hAA, fun N N' hN hN' => ⟨(hall N N' hN hN').1, fun c hc => ?_⟩⟩
  have := hne
  have hc0 : (c : 𝓞 X.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have he1 : ∀ Q, expS Sall Q = 1 ∨ expS Sall Q = 0 ∨ expS Sall Q = -1 := expS_cases Sall
  have he2 : ∀ Q, (fun Q => -expS Sall Q) Q = 1 ∨ (fun Q => -expS Sall Q) Q = 0 ∨ (fun Q => -expS Sall Q) Q = -1 := by
    intro Q
    have := he1 Q
    show -expS Sall Q = 1 ∨ -expS Sall Q = 0 ∨ -expS Sall Q = -1
    omega
  have hconj1 : ∀ Q, expS Sall (conjPrime₂ Q) = -expS Sall Q := exponent_set_conjugate X.E Sall hSS
  have hconj2 : ∀ Q, (fun Q => -expS Sall Q) (conjPrime₂ Q) = -(fun Q => -expS Sall Q) Q := by
    intro Q
    show -expS Sall (conjPrime₂ Q) = - -expS Sall Q
    rw [hconj1 Q]
  have sdB : IsSdLat (twist₂ N' c (expS Sall)) :=
    ⟨hh_tw_lattice N' hN'.1 hc _ he1, twist_selfDual X.E b N' c _ hN'.1.fg hc hconj1 hN'.2⟩
  have sdA : IsSdLat (twist₂ N' c fun Q => -expS Sall Q) :=
    ⟨hh_tw_lattice N' hN'.1 hc _ he2, twist_selfDual X.E b N' c _ hN'.1.fg hc hconj2 hN'.2⟩
  have hS := half_periods_of_lattice X.E X.Tau a b (X.embC A.σ₀) A.δ A.d A.sc A.AA Sall N N' c hδ hc hSS hN.1.fg (hall N N' hN hN').2
    (hall N _ hN sdB).2 (hall N _ hN sdA).2
  have hP := hh_perO_fg A.AA hFG N N' hN.1 hN'.1
  have hBfg : (halfBO Sall (perO A.AA N N') c).FG := fg_of_scale _ _ hP (c : 𝓞 X.E) hc0 fun x hx => hh_of_tw _ hc _ he1 hx
  have hAfg : (halfAO Sall (perO A.AA N N') c).FG := fg_of_scale _ _ hP (c : 𝓞 X.E) hc0 fun x hx => hh_of_tw _ hc _ he2 hx
  refine ⟨hS, ?_, ?_, ?_⟩
  · obtain ⟨R, hR, hcov⟩ := hh_cover (X.embC A.σ₀) A.δ (halfBO Sall (perO A.AA N N') c) (perO A.AA N N') hP _ hc0
      (fun x hx => hh_tw_of _ hc _ he1 hx)
    exact relIndex_ne_zero_of_cover _ _ R hR fun x hx => hcov x hx.1
  · obtain ⟨R, hR, hcov⟩ := hh_cover (X.embC A.σ₀) A.δ (perO A.AA N N') (halfBO Sall (perO A.AA N N') c) hBfg _ hc0
      (fun x hx => hh_of_tw _ hc _ he1 hx)
    exact relIndex_ne_zero_of_cover _ _ R hR hcov
  · obtain ⟨R, hR, hcov⟩ := hh_cover (X.embC A.σ₀) A.δ (perO A.AA N N') (halfAO Sall (perO A.AA N N') c) hAfg _ hc0
      (fun x hx => hh_of_tw _ hc _ he2 hx)
    exact relIndex_ne_zero_of_cover _ _ R hR hcov

theorem indTieD_of_la {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (hD : 0 < D)
    (h : A.LaHyp a b Sall) : A.IndTieD a b Sall D := induced_kernel_degree_compat A a b Sall D hD (heisHyp_of A a b Sall h)

section AddAbs

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem ad_xiL_sum {κ : Type} (H : Sesq V) (α : V → ℂ) (vol : ℝ) (SX SA SB : Finset V) (s : Finset κ) (Φ : κ → V → ℂ) (e : V → ℂ) (z : V) :
    xiL H α vol SX SA SB (fun t => ∑ i ∈ s, Φ i t) e z = ∑ i ∈ s, xiL H α vol SX SA SB (Φ i) e z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := (twist_linear V H α vol SX SA SB (-1) (fun _ => 0) (fun _ => 0) e e z).2.2.1
    simp only [mul_zero, add_zero] at h
    simp only [Finset.sum_empty]
    linear_combination h
  | insert i s hi ih =>
    have h := (twist_linear V H α vol SX SA SB 1 (Φ i) (fun t => ∑ j ∈ s, Φ j t) e e z).2.2.1
    simp only [one_mul] at h
    simp only [Finset.sum_insert hi]
    rw [h, ih]

end AddAbs

section AddLat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ}

theorem ad_onV_sum {κ : Type} (emb : ι → E →+* ℂ) (δ : ℂ) (s : Finset κ) (Ξ : κ → HomE E a b → ℂ) (v : VV ι a b) :
    onV emb δ (fun t => ∑ i ∈ s, Ξ i t) v = ∑ i ∈ s, onV emb δ (Ξ i) v := by
  by_cases h : ∃ x, embH emb δ x = v
  · simp only [onV, dif_pos h]
  · simp only [onV, dif_neg h, Finset.sum_const_zero]

theorem ad_mulLat_le {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (c c' : ℕ) (M : Submodule (𝓞 E) H) : mulLat (c * c') M ≤ mulLat c M := by
  intro w hw
  exact ti_mul_mono (Dvd.intro c' rfl) M hw

open Classical in

theorem ad_ind_sum {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (A B : Submodule (𝓞 E) H) (hBA : B ≤ A) [Fintype (↥A ⧸ B.comap A.subtype)] (w : H) :
    (if w ∈ A then (1 : ℂ) else 0) = ∑ z : ↥A ⧸ B.comap A.subtype,
      if w - ((Function.surjInv (Submodule.Quotient.mk_surjective (B.comap A.subtype)) z : ↥A) : H) ∈ B then (1 : ℂ) else 0 := by
  have hmk : ∀ z : ↥A ⧸ B.comap A.subtype,
      Submodule.Quotient.mk (p := B.comap A.subtype) (Function.surjInv (Submodule.Quotient.mk_surjective (B.comap A.subtype)) z) = z :=
    fun z => Function.surjInv_eq _ z
  by_cases h : w ∈ A
  · rw [if_pos h]
    have h1 : ∀ z : ↥A ⧸ B.comap A.subtype,
        (w - ((Function.surjInv (Submodule.Quotient.mk_surjective (B.comap A.subtype)) z : ↥A) : H) ∈ B) ↔
          Submodule.Quotient.mk (p := B.comap A.subtype) ⟨w, h⟩ = z := by
      intro z
      conv_rhs => rw [← hmk z]
      rw [Submodule.Quotient.eq]
      rfl
    rw [Finset.sum_congr rfl fun z _ => if_congr (h1 z) rfl rfl, Finset.sum_ite_eq]
    simp
  · rw [if_neg h]
    symm
    refine Finset.sum_eq_zero fun z _ => if_neg fun hz => h ?_
    have h2 := add_mem (hBA hz) (Function.surjInv (Submodule.Quotient.mk_surjective (B.comap A.subtype)) z : ↥A).2
    rwa [sub_add_cancel] at h2

theorem ad_cosInd_sum (S : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (c c' : ℕ)
    [Fintype (↥(mulLat c (homAt S N N')) ⧸ (mulLat (c * c') (homAt S N N')).comap (mulLat c (homAt S N N')).subtype)] (x t : HomE E a b) :
    cosInd S N N' c x t = ∑ z : ↥(mulLat c (homAt S N N')) ⧸ (mulLat (c * c') (homAt S N N')).comap (mulLat c (homAt S N N')).subtype,
      cosInd S N N' (c * c') (x + ((Function.surjInv (Submodule.Quotient.mk_surjective
        ((mulLat (c * c') (homAt S N N')).comap (mulLat c (homAt S N N')).subtype)) z : ↥(mulLat c (homAt S N N'))) : HomE E a b)) t := by
  unfold cosInd
  rw [ad_ind_sum _ _ (ad_mulLat_le c c' (homAt S N N')) (t - x)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [sub_add_eq_sub_sub]

end AddLat

section AddMain

variable {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)

theorem indAdd_of (hD : 0 < D) (hfin : LatFin (X := X) a b Sall) (hT : A.IndTieD a b Sall D) : A.IndAdd a b Sall D := by
  intro N N' c c' x hc hc' hR z
  have := hfin N N' c c' hR.1 hR.2.1 hc hc'
  let _ := Fintype.ofFinite (↥(mulLat c (homAt Sall N N')) ⧸ (mulLat (c * c') (homAt Sall N N')).comap (mulLat c (homAt Sall N N')).subtype)
  have hRc : InRange Sall D c N N' x := ⟨hR.1, hR.2.1, hc, (Dvd.intro _ rfl).trans hR.2.2.2.1, hR.2.2.2.2⟩
  unfold latSum
  rw [finsum_eq_sum_of_fintype, hT N N' c x hRc hD z]
  have h1 : ∀ q : ↥(mulLat c (homAt Sall N N')) ⧸ (mulLat (c * c') (homAt Sall N N')).comap (mulLat c (homAt Sall N N')).subtype,
      InRange Sall D (c * c') N N' (x + ((Function.surjInv (Submodule.Quotient.mk_surjective
        ((mulLat (c * c') (homAt Sall N N')).comap (mulLat c (homAt Sall N N')).subtype)) q : ↥(mulLat c (homAt Sall N N'))) : HomE X.E a b)) :=
    fun q => hR.add (Subtype.coe_prop _)
  rw [Finset.sum_congr rfl fun q _ => hT N N' (c * c') _ (h1 q) hD z, ← Finset.mul_sum]
  congr 1
  unfold xiC xiV
  rw [← ad_xiL_sum]
  congr 1
  funext v
  rw [← ad_onV_sum]
  congr 1
  funext t
  exact ad_cosInd_sum Sall N N' c c' x t

end AddMain

theorem stepHyp_of_la {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (hD : 0 < D)
    (h : A.LaHyp a b Sall) (hfin : LatFin (X := X) a b Sall) (hsm : A.ESmooth a b) (hrat : A.JetsRat a b Sall D) : A.StepHyp a b Sall D := by
  unfold Amb.StepHyp
  exact ⟨hfin, indAdd_of A a b Sall D hD hfin (indTieD_of_la A a b Sall D hD h), hsm, hrat⟩

section QValU

open Formalism.UG Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct

section QU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem qu_tow (a : 𝓞 F) : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap F E (algebraMap (𝓞 F) F a) :=
  (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E a).symm.trans (IsScalarTower.algebraMap_apply (𝓞 F) F E a)

theorem qu_move (x : F) (d : FiniteAdeleRing (𝓞 F) F) :
    (algebraMap F E x) ⊗ₜ[F] d = (1 : E) ⊗ₜ[F] (algebraMap F (FiniteAdeleRing (𝓞 F) F) x * d) := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]

theorem qu_right (d : FiniteAdeleRing (𝓞 F) F) (hd : d ∈ intAd F) : (1 : E) ⊗ₜ[F] d ∈ RInt F E :=
  Subring.subset_closure (Or.inr ⟨⟨d, hd⟩, rfl⟩)

theorem qu_sgl_int (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) (hx : x ∈ v.adicCompletionIntegers F) :
    Formalism.L2.G.sgl F v x ∈ intAd F := by
  intro v'
  by_cases h : v' = v
  · subst h
    show evalV F v' (Formalism.L2.G.sgl F v' x) ∈ _
    rw [Formalism.L2.G.sgl_apply_same]; exact hx
  · show evalV F v' (Formalism.L2.G.sgl F v x) ∈ _
    rw [Formalism.L2.G.sgl_apply_ne F v x h]; exact zero_mem _

variable (E) in

def quE (v : HeightOneSpectrum (𝓞 F)) : RInt F E :=
  ⟨(1 : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1, qu_right _ (qu_sgl_int v 1 (one_mem _))⟩

theorem qu_eps_mem (v : HeightOneSpectrum (𝓞 F)) (I : Ideal (𝓞 E)) (a : 𝓞 F) (haI : algebraMap (𝓞 F) (𝓞 E) a ∈ I) (hav : a ∉ v.asIdeal) :
    quE E v ∈ I.map (toRInt F E) := by
  have hval : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) = 1 := by
    rw [AdeleIntA.val_R, intValuation_eq_one_iff_mem_primeCompl]
    exact Ideal.mem_primeCompl_iff.mpr hav
  have ha0 : algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) ≠ 0 := by
    intro h; rw [h, map_zero] at hval; exact zero_ne_one hval
  have hc : (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [mem_adicCompletionIntegers, map_inv₀, hval, inv_one]
  have e : quE E v = toRInt F E (algebraMap (𝓞 F) (𝓞 E) a) *
      ⟨(1 : E) ⊗ₜ[F] Formalism.L2.G.sgl F v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))⁻¹, qu_right _ (qu_sgl_int v _ hc)⟩ := by
    apply Subtype.ext
    show (1 : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1 = ((algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a)) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) *
      ((1 : E) ⊗ₜ[F] Formalism.L2.G.sgl F v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))⁻¹)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, qu_tow, qu_move, ← Algebra.smul_def, ← map_smul, Algebra.smul_def,
      mul_inv_cancel₀ ha0]
  rw [e]; exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ haI)

theorem qu_one_sub_mem (v : HeightOneSpectrum (𝓞 F)) (I : Ideal (𝓞 E)) (k : ℕ) (hI : ∀ a ∈ v.asIdeal ^ k, algebraMap (𝓞 F) (𝓞 E) a ∈ I) :
    1 - quE E v ∈ I.map (toRInt F E) := by
  have he : Formalism.L2.G.sgl F v 1 ∈ intAd F := qu_sgl_int v 1 (one_mem _)
  have hc : AdeleIntA.IsInt (1 - Formalism.L2.G.sgl F v 1) := fun v' => (intAd F).sub_mem (intAd F).one_mem he v'
  have hn0 : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ≠ 0 := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast this
  have hr0 : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ^ k ≠ 0 := pow_ne_zero _ hn0
  have hrk : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ^ k ∈ v.asIdeal ^ k := Ideal.pow_mem_pow (Ideal.absNorm_mem _) k
  generalize ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ^ k = r at hr0 hrk
  obtain ⟨a, ha⟩ := AdeleIntA.exists_approx (1 - Formalism.L2.G.sgl F v 1) hc r hr0
  have hak : a ∈ v.asIdeal ^ k := by
    have h1 := ha v
    have h2 : (1 - Formalism.L2.G.sgl F v 1 : FiniteAdeleRing (𝓞 F) F) v = 0 := by
      show evalV F v (1 - Formalism.L2.G.sgl F v 1) = 0
      rw [map_sub, map_one, Formalism.L2.G.sgl_apply_same, sub_self]
    rw [h2, zero_sub, Valuation.map_neg, AdeleIntA.val_R] at h1
    rw [← intValuation_le_pow_iff_mem] at hrk ⊢
    exact h1.trans hrk
  have hrF : algebraMap (𝓞 F) F r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hr0
  have hd : algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F r)⁻¹ *
      ((1 - Formalism.L2.G.sgl F v 1) - algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F a)) ∈ intAd F := by
    intro v'
    show algebraMap F (v'.adicCompletion F) (algebraMap (𝓞 F) F r)⁻¹ *
      ((1 - Formalism.L2.G.sgl F v 1 : FiniteAdeleRing (𝓞 F) F) v' - algebraMap F (v'.adicCompletion F) (algebraMap (𝓞 F) F a)) ∈ _
    rw [mem_adicCompletionIntegers, map_mul, map_inv₀, map_inv₀, AdeleIntA.val_R]
    exact inv_mul_le_one_of_le₀ (ha v') zero_le
  have hdec : (1 : FiniteAdeleRing (𝓞 F) F) - Formalism.L2.G.sgl F v 1 = algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F a) +
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F r) * (algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F r)⁻¹ *
      ((1 - Formalism.L2.G.sgl F v 1) - algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F a))) := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hrF, (algebraMap F (FiniteAdeleRing (𝓞 F) F)).map_one, one_mul]; ring
  have e2 : 1 - quE E v = toRInt F E (algebraMap (𝓞 F) (𝓞 E) a) + toRInt F E (algebraMap (𝓞 F) (𝓞 E) r) * ⟨(1 : E) ⊗ₜ[F] _, qu_right _ hd⟩ := by
    apply Subtype.ext
    show (1 : AfE F E) - (1 : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1 =
      (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a)) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) +
        ((algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r)) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * ((1 : E) ⊗ₜ[F] _)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, qu_tow, qu_tow, qu_move, qu_move, mul_one, ← TensorProduct.tmul_add, ← hdec,
      TensorProduct.tmul_sub]
    rfl
  rw [e2]
  exact Ideal.add_mem _ (Ideal.mem_map_of_mem _ (hI a hak)) (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hI r hrk)))

theorem qu_idem (v : HeightOneSpectrum (𝓞 F)) : quE E v * quE E v = quE E v := by
  apply Subtype.ext
  show ((1 : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1) * ((1 : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1) = (1 : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Formalism.L2.G.sgl_mul, one_mul]

theorem qu_prV (v v' : HeightOneSpectrum (𝓞 F)) (h : v' ≠ v) : prV (E := E) v' ((quE E v : RInt F E) : AfE F E) = 0 := by
  show (Algebra.TensorProduct.map (AlgHom.id F E) (evalV F v')) ((1 : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1) = 0
  rw [Algebra.TensorProduct.map_tmul, Formalism.L2.G.sgl_apply_ne F v 1 h, TensorProduct.tmul_zero]

end QU

end QValU

section QValE

open Formalism.UG Formalism.UG.P

section QEx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem qe_denom (y : (AfE F E)ˣ) (y₀ : RInt F E) (hy : (y₀ : AfE F E) = (y : AfE F E)) :
    ∃ D : 𝓞 F, D ≠ 0 ∧ toRInt F E (algebraMap (𝓞 F) (𝓞 E) D) ∈ Ideal.span {y₀} := by
  obtain ⟨d, hd, hdx⟩ := levelaf_denom (E := E) ((y⁻¹ : (AfE F E)ˣ) : AfE F E)
  refine ⟨d, hd, Ideal.mem_span_singleton'.2 ⟨⟨_, hdx⟩, Subtype.ext ?_⟩⟩
  show levelafC E d * ((y⁻¹ : (AfE F E)ˣ) : AfE F E) * (y₀ : AfE F E) =
    ((toRInt F E (algebraMap (𝓞 F) (𝓞 E) d) : RInt F E) : AfE F E)
  rw [hy, mul_assoc, Units.inv_mul, mul_one, b_toRInt_alg]
  rfl

theorem qe_strip (P : HeightOneSpectrum (𝓞 E)) (K : Ideal (RInt F E))
    (hK : ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → P'.asIdeal.map (toRInt F E) ⊔ K = ⊤) (I : Ideal (𝓞 E)) :
    I ≠ 0 → ∀ m : ℕ, (P.asIdeal ^ m * I).map (toRInt F E) ≤ K → ∃ n : ℕ, (P.asIdeal ^ n).map (toRInt F E) ≤ K := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h
  | h₂ x hx =>
    intro _ m h
    rw [Ideal.isUnit_iff] at hx
    exact ⟨m, by rwa [hx, Ideal.mul_top] at h⟩
  | h₃ a p ha hp ih =>
    intro _ m h
    by_cases hpP : p = P.asIdeal
    · apply ih ha (m + 1)
      have e : P.asIdeal ^ (m + 1) * a = P.asIdeal ^ m * (p * a) := by rw [hpP]; ring
      rw [e]; exact h
    · have h1 := hK ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩ (fun h => hpP (congrArg HeightOneSpectrum.asIdeal h))
      apply ih ha m
      calc (P.asIdeal ^ m * a).map (toRInt F E) = (P.asIdeal ^ m * a).map (toRInt F E) * ⊤ := (Ideal.mul_top _).symm
        _ = (P.asIdeal ^ m * a).map (toRInt F E) * (p.map (toRInt F E) ⊔ K) := by rw [← h1]
        _ = (P.asIdeal ^ m * a).map (toRInt F E) * p.map (toRInt F E) ⊔ (P.asIdeal ^ m * a).map (toRInt F E) * K := Ideal.mul_sup _ _ _
        _ ≤ K := by
          refine sup_le ?_ Ideal.mul_le_right
          rw [← Ideal.map_mul]
          have e : P.asIdeal ^ m * a * p = P.asIdeal ^ m * (p * a) := by ring
          rw [e]; exact h

theorem qe_sup (P : HeightOneSpectrum (𝓞 E)) (q : 𝓞 E) (hq : q ∈ P.asIdeal) (hq2 : q ∉ P.asIdeal ^ 2) :
    Ideal.span {q} ⊔ P.asIdeal ^ 2 = P.asIdeal := by
  have hlt : P.asIdeal ^ (1 + 1) < Ideal.span {q} ⊔ P.asIdeal ^ 2 := by
    refine lt_of_le_of_ne le_sup_right fun h => hq2 ?_
    show q ∈ P.asIdeal ^ (1 + 1)
    rw [h]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self q)
  have hle : Ideal.span {q} ⊔ P.asIdeal ^ 2 ≤ P.asIdeal ^ 1 := by
    rw [pow_one]
    exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hq) (Ideal.pow_le_self two_ne_zero)
  have h := Ideal.eq_prime_pow_of_succ_lt_of_le P.ne_bot hlt hle
  rwa [pow_one] at h

theorem qe_le (P : HeightOneSpectrum (𝓞 E)) (y : (AfE F E)ˣ) (y₀ : RInt F E) (hy : (y₀ : AfE F E) = (y : AfE F E)) (q : 𝓞 E)
    (hq : q ∈ P.asIdeal) (hq2 : q ∉ P.asIdeal ^ 2) (h1 : y₀ - toRInt F E q ∈ (P.asIdeal ^ 2).map (toRInt F E))
    (h2 : ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → y₀ - 1 ∈ P'.asIdeal.map (toRInt F E)) :
    P.asIdeal.map (toRInt F E) ≤ Ideal.span {y₀} := by
  have hy0 : y₀ ∈ Ideal.span {y₀} := Ideal.mem_span_singleton_self _
  have hK : ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → P'.asIdeal.map (toRInt F E) ⊔ Ideal.span {y₀} = ⊤ := by
    intro P' hP'
    rw [Ideal.eq_top_iff_one]
    have e : (1 : RInt F E) = -(y₀ - 1) + y₀ := by ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (neg_mem (h2 P' hP'))) (Ideal.mem_sup_right hy0)
  have hB : P.asIdeal.map (toRInt F E) ≤ Ideal.span {y₀} ⊔ (P.asIdeal ^ 2).map (toRInt F E) := by
    conv_lhs => rw [← qe_sup P q hq hq2]
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    refine sup_le ?_ le_sup_right
    rw [Ideal.span_singleton_le_iff_mem]
    have e : toRInt F E q = y₀ - (y₀ - toRInt F E q) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left hy0) (Ideal.mem_sup_right h1)
  obtain ⟨D, hD0, hD⟩ := qe_denom y y₀ hy
  have hI : Ideal.span {algebraMap (𝓞 F) (𝓞 E) D} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    intro h
    apply adelstab_algebraMap_ne_zero (E := E) D hD0
    rw [IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, h, map_zero]
  obtain ⟨n, hn⟩ := qe_strip P _ hK _ hI 0 (by
    rw [pow_zero, one_mul, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]; exact hD)
  have hdesc : ∀ n : ℕ, (P.asIdeal ^ (n + 1)).map (toRInt F E) ≤ Ideal.span {y₀} → P.asIdeal.map (toRInt F E) ≤ Ideal.span {y₀} := by
    intro n
    induction n with
    | zero => intro h; rwa [zero_add, pow_one] at h
    | succ n ih =>
      intro h
      apply ih
      rw [pow_succ, Ideal.map_mul]
      refine (Ideal.mul_mono_right hB).trans ?_
      rw [Ideal.mul_sup]
      refine sup_le Ideal.mul_le_right ?_
      rw [← Ideal.map_mul, ← pow_add]
      exact h
  exact hdesc n ((Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ n))).trans hn)

variable {L : Type} [Field L]

theorem qe_same (ξ : Chr F E L) (hξ : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) (P : HeightOneSpectrum (𝓞 E)) (q : 𝓞 E)
    (hq : q ∈ P.asIdeal) (hq2 : q ∉ P.asIdeal ^ 2) (v : HeightOneSpectrum (𝓞 F)) (y y' : (AfE F E)ˣ) (y₀ y₀' : RInt F E)
    (hy : (y₀ : AfE F E) = (y : AfE F E)) (hy' : (y₀' : AfE F E) = (y' : AfE F E)) (hs : y ∈ suppAt E v) (hs' : y' ∈ suppAt E v)
    (h1 : y₀ - toRInt F E q ∈ (P.asIdeal ^ 2).map (toRInt F E)) (h1' : y₀' - toRInt F E q ∈ (P.asIdeal ^ 2).map (toRInt F E))
    (h2 : ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → y₀ - 1 ∈ P'.asIdeal.map (toRInt F E))
    (h2' : ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → y₀' - 1 ∈ P'.asIdeal.map (toRInt F E)) : ξ y = ξ y' := by
  have hle := qe_le P y y₀ hy q hq hq2 h1 h2
  have hle' := qe_le P y' y₀' hy' q hq hq2 h1' h2'
  have hmem : ∀ z₀ : RInt F E, z₀ - toRInt F E q ∈ (P.asIdeal ^ 2).map (toRInt F E) → z₀ ∈ P.asIdeal.map (toRInt F E) := by
    intro z₀ hz
    have e : z₀ = (z₀ - toRInt F E q) + toRInt F E q := by ring
    rw [e]
    exact add_mem (Ideal.map_mono (Ideal.pow_le_self two_ne_zero) hz) (Ideal.mem_map_of_mem _ hq)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (hle' (hmem y₀ h1))
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.1 (hle (hmem y₀' h1'))
  have haa : a * a' = 1 := by
    have e0 : a * a' * y₀ = y₀ := by rw [mul_assoc, ha', ha]
    have e1 : ((a * a' : RInt F E) : AfE F E) * (y : AfE F E) = 1 * (y : AfE F E) := by
      rw [one_mul, ← hy]
      exact congrArg Subtype.val e0
    exact Subtype.ext (y.isUnit.mul_right_cancel e1)
  let u : (RInt F E)ˣ := ⟨a, a', haa, by rw [mul_comm]; exact haa⟩
  have hu : Units.map (RInt F E).subtype.toMonoidHom u = y * y'⁻¹ := by
    apply Units.ext
    show (a : AfE F E) = (y : AfE F E) * ((y'⁻¹ : (AfE F E)ˣ) : AfE F E)
    have e2 : (a : AfE F E) * (y' : AfE F E) = (y : AfE F E) := by
      rw [← hy, ← hy']
      exact congrArg Subtype.val ha
    rw [← e2, mul_assoc, Units.mul_inv, mul_one]
  have hw : Units.map (RInt F E).subtype.toMonoidHom u ∈ wildAt E v := by
    apply tpWild_proof' v u (by rw [hu]; exact mul_mem hs (inv_mem hs'))
    intro P'
    show a - 1 ∈ P'.asIdeal.map (toRInt F E)
    by_cases hP' : P' = P
    · rw [hP']
      by_contra hn
      obtain ⟨b, hb⟩ := tpApprox_proof' (F := F) P (a - 1)
      have hbP : b ∉ P.asIdeal := fun hbP => hn (by
        have e : a - 1 = (a - 1 - toRInt F E b) + toRInt F E b := by ring
        rw [e]; exact add_mem hb (Ideal.mem_map_of_mem _ hbP))
      obtain ⟨b', i, hi, hbi⟩ := P.isMaximal.exists_inv hbP
      have hp : (a - 1) * toRInt F E b' - 1 ∈ P.asIdeal.map (toRInt F E) := by
        have e3 := congrArg (toRInt F E) hbi
        simp only [map_add, map_mul, map_one] at e3
        have e : (a - 1) * toRInt F E b' - 1 = (a - 1 - toRInt F E b) * toRInt F E b' - toRInt F E i := by
          linear_combination e3
        rw [e]
        exact sub_mem (Ideal.mul_mem_right _ _ hb) (Ideal.mem_map_of_mem _ hi)
      have hd : y₀' * (a - 1) ∈ (P.asIdeal ^ 2).map (toRInt F E) := by
        have e : y₀' * (a - 1) = (y₀ - toRInt F E q) - (y₀' - toRInt F E q) := by rw [← ha]; ring
        rw [e]; exact sub_mem h1 h1'
      have hy2 : y₀' ∈ (P.asIdeal ^ 2).map (toRInt F E) := by
        have e : y₀' = y₀' * (a - 1) * toRInt F E b' - y₀' * ((a - 1) * toRInt F E b' - 1) := by ring
        rw [e]
        refine sub_mem (Ideal.mul_mem_right _ _ hd) ?_
        rw [pow_two, Ideal.map_mul]
        exact Ideal.mul_mem_mul (hmem y₀' h1') hp
      have hq' : toRInt F E q ∈ (P.asIdeal ^ 2).map (toRInt F E) := by
        have e : toRInt F E q = y₀' - (y₀' - toRInt F E q) := by ring
        rw [e]; exact sub_mem hy2 h1'
      obtain ⟨D, hD0, hD⟩ := b_under_elt (F := F) P
      exact hq2 (b_comap (P.asIdeal ^ 2) (D ^ 2) (pow_ne_zero 2 hD0) (by rw [map_pow]; exact Ideal.pow_mem_pow hD 2) q hq')
    · have e : a - 1 = a * (-(y₀' - 1)) + (y₀ - 1) := by rw [← ha]; ring
      rw [e]
      exact add_mem (Ideal.mul_mem_left _ _ (neg_mem (h2' P' hP'))) (h2 P' hP')
  have h3 := hξ v hw
  rw [hu, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h3
  exact h3

end QEx

theorem value_at_q_exists : QValExists := by
  intro F E _ _ _ _ _ L _ ξ P hξ hq2
  classical
  by_cases hex : ∃ (v : HeightOneSpectrum (𝓞 F)) (y : (AfE F E)ˣ) (y₀ : RInt F E), P.asIdeal.under (𝓞 F) = v.asIdeal ∧
      (y₀ : AfE F E) = (y : AfE F E) ∧ y ∈ suppAt E v ∧
      y₀ - toRInt F E ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ (P.asIdeal ^ 2).map (toRInt F E) ∧
      ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → y₀ - 1 ∈ P'.asIdeal.map (toRInt F E)
  · obtain ⟨v1, y1, y1₀, hv1, hy1, hs1, h11, h12⟩ := hex
    refine ⟨ξ y1, fun v hv y y₀ hy hs h1 h2 => ?_⟩
    have hvv : v = v1 := HeightOneSpectrum.ext (hv.symm.trans hv1)
    subst hvv
    exact qe_same ξ hξ P _ (Ideal.absNorm_mem P.asIdeal) hq2 v y y1 y₀ y1₀ hy hy1 hs hs1 h1 h11 h2 h12
  · exact ⟨1, fun v hv y y₀ hy hs h1 h2 => absurd ⟨v, y, y₀, hv, hy, hs, h1, h2⟩ hex⟩

end QValE

theorem qVal_spec {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L] (ξ : Chr F E L)
    (P : HeightOneSpectrum (𝓞 E)) (hξ : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) : IsQVal ξ P (qVal ξ P) := by
  have hex : ∃ k, IsQValC ξ P k := value_at_q_exists F E L ξ P hξ hq
  unfold qVal qValC
  rw [dif_pos hex]
  exact hex.choose_spec

theorem qVal_spec_tup {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L] {S : Set ℕ}
    (mu : Tup F E L S) (P : HeightOneSpectrum (𝓞 E)) (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) :
    IsQVal (mu : Chr F E L) P (qVal (mu : Chr F E L) P) :=
  qVal_spec _ P (fun v => mem_kills.1 ((Subgroup.mem_iInf.1 mu.2.1.2) v)) hq

end Formalism.L2.Ker
