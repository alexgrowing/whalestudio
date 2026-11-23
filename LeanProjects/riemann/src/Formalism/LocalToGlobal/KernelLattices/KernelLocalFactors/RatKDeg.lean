import Mathlib
import Formalism.LocalToGlobal.KernelLattices.RatKDeg
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.JetsRationalOfKernelRationality
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H Formalism.MainNotions

theorem natW_cast {n : ℕ} (lam : DomWeight n) (i : Fin n) : ((lam.natW i : ℕ) : ℤ) = lam.w i - lam.detShift := by
  unfold DomWeight.natW
  have h : lam.detShift ≤ lam.w i := by
    unfold DomWeight.detShift
    have hn : 0 < n := Fin.pos i
    rw [dif_pos hn]
    exact lam.anti (show i ≤ ⟨n - 1, by omega⟩ from Fin.mk_le_mk.2 (by omega))
  omega

theorem chain_degree_eq : StepDegIs := by
  intro X Pr R W u i hi τ
  unfold stepDeg opDeg
  push_cast
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [natW_cast, nuLast_eq W u i hi τ]
  have hN : 0 < R.N i := R.N_pos i
  have d0 : (W.lamTrue u i τ).detShift = (W.lamTrue u i τ).w ⟨R.N i - 1, by omega⟩ := by
    unfold DomWeight.detShift
    exact dif_pos hN
  have d1 : (W.nuW u (i + 1) τ).detShift = (W.nuW u (i + 1) τ).w ⟨R.N i - 1, by show R.N i - 1 < R.N i; omega⟩ := by
    unfold DomWeight.detShift
    exact dif_pos hN
  rw [d0, d1]
  show (W.lamN u i τ).w r + _ - ((W.lamN u i τ).w _ + _) + ((W.lamN u i τ).w _ + _) = (W.lamN u i τ).w r + _
  ring

section Op

variable {K : Type} [Field K] [Infinite K] {ι : Type} [Fintype ι] {a b : ℕ}

theorem jetOp_congr (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ) (J J' : (DVar ι a b →₀ ℕ) → K)
    (h : ∀ m, (∀ τ, degAt m τ = opDeg lam n τ) → J m = J' m) : jetOp lam lam' J n = jetOp lam lam' J' n := by
  ext P
  unfold jetOp
  simp only [LinearMap.comp_apply, Submodule.subtype_apply]
  rw [jet_local_rationality K ι a b lam n J J' h P P.2]

end Op

section Props

variable {X : Fields} (A : Amb X) {a b : ℕ} (Sall SB : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)

theorem jetK_spec_deg (dg : X.Tau → ℕ) (hrat : A.JetsRatDeg a b Sall D dg) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ)
    (x : HomE X.E a b) (hR : InRange Sall D c N N' x) (m : DVar X.Tau a b →₀ ℕ) (hm : ∀ τ, degAt m τ = dg τ) :
    A.σ₀ (A.jetK Sall N N' c x m) = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' c x) m := by
  obtain ⟨k, hk⟩ := hrat N N' c x hR m hm
  unfold Amb.jetK
  rw [← hk, desc_map]

theorem jetAddDeg_of (dg : X.Tau → ℕ) (hfin : LatFin (X := X) a b Sall) (hadd : A.IndAdd a b Sall D) (hsm : A.IndSmooth a b Sall D)
    (hrat : A.JetsRatDeg a b Sall D dg) : A.JetAddDeg a b Sall D dg := by
  intro N N' c c' x hc hc' hR m hm
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
  choose k hk using fun z => hrat N N' (c * c') (x + rep z) (hRz z) m hm
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

variable (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
  (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)

theorem thDistC_add_deg (hfin : LatFin (X := X) a b Sall) (hadd : A.JetAddDeg a b Sall D (opDeg lam n))
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB)
    (c c' : ℕ) (x : HomE X.E a b) (hc : 0 < c) (hc' : 0 < c') (hR : InRange Sall D (c * c') N N' x) :
    thDistC A Sall SB D sel mU mI lam lam' n N fr N' fr' c x =
      latSum (mulLat c (homAt Sall N N')) (mulLat (c * c') (homAt Sall N N')) fun y =>
        thDistC A Sall SB D sel mU mI lam lam' n N fr N' fr' (c * c') (x + y) := by
  have := hfin N N' c c' hR.1 hR.2.1 hc hc'
  let _ := Fintype.ofFinite (↥(mulLat c (homAt Sall N N')) ⧸ (mulLat (c * c') (homAt Sall N N')).comap (mulLat c (homAt Sall N N')).subtype)
  have hJ : jetOp lam lam' (A.jetK Sall N N' c x) n = jetOp lam lam' (fun m => ∑ z : ↥(mulLat c (homAt Sall N N')) ⧸ (mulLat (c * c') (homAt Sall N N')).comap (mulLat c (homAt Sall N N')).subtype,
      A.jetK Sall N N' (c * c') (x + ((Function.surjInv (Submodule.Quotient.mk_surjective
        ((mulLat (c * c') (homAt Sall N N')).comap (mulLat c (homAt Sall N N')).subtype)) z : ↥(mulLat c (homAt Sall N N'))) : HomE X.E a b)) m) n := by
    refine jetOp_congr lam lam' n _ _ fun m hm => ?_
    rw [hadd N N' c c' x hc hc' hR m hm]
    unfold latSum
    rw [finsum_eq_sum_of_fintype]
  unfold latSum
  rw [finsum_eq_sum_of_fintype]
  unfold thDistC
  rw [if_pos ⟨(Dvd.intro _ rfl).trans hR.2.2.2.1, hR.2.2.2.2⟩, hJ, jetOp_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  exact (if_pos ⟨hR.2.2.2.1, mem_divLat_add D c _ hR.2.2.2.2 (Subtype.coe_prop _)⟩).symm

theorem thDistC_ok_deg (hD : 0 < D) (rho : UF X.E a →* Module.End X.K (DIV.VV X.K lam)) (rho' : UF X.E b →* Module.End X.K (DIV.VV X.K lam'))
    (sS sT : SB → X.E → X.K) (hfin : LatFin (X := X) a b Sall) (hadd : A.JetAddDeg a b Sall D (opDeg lam n))
    (heq : ThEquivP (thDistC A Sall SB D sel mU mI lam lam' n) Sall D rho rho')
    (ha : MuDetLaw a mI sS) (hb : MuDetLaw b mI sS) (hi : UnitInv sS sT) :
    ThDist.Ok (thDistC A Sall SB D sel mU mI lam lam' n) Sall D rho rho' sS sT where
  cong := fun N fr N' fr' c x x' _ _ h => thDistC_cong A Sall SB sel mU mI lam lam' n D N fr N' fr' c x x' h
  add := fun N fr N' fr' c c' x hN hN' hc hc' hd hx =>
    thDistC_add_deg A Sall SB D sel mU mI lam lam' n hfin hadd N fr N' fr' c c' x hc hc' ⟨hN, hN', Nat.mul_pos hc hc', hd, hx⟩
  equiv := thDistC_equiv A Sall SB sel mU mI lam lam' n D hD rho rho' heq
  det := fun N fr N' fr' c x κ κ' _ _ => thDistC_det A Sall SB sel mU mI lam lam' n D sS sT ha hb hi N fr N' fr' c x κ κ'

end Props

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ)

theorem jetAddDeg_of_ana {a b : ℕ} {Sall : Finset (HeightOneSpectrum (𝓞 X.E))} {D : ℕ} {dg : X.Tau → ℕ} (hD : 0 < D) (h : A.AnaStepD a b Sall D dg) :
    A.JetAddDeg a b Sall D dg :=
  jetAddDeg_of A Sall D dg (lattice_classes_finite_refinement X a b Sall) (indAdd_of A a b Sall D hD (lattice_classes_finite_refinement X a b Sall) (indTieD_of_la A a b Sall D hD h.1))
    (indSmooth_of A _ _ _ _ h.2.1) h.2.2

theorem stepC_ok_deg (i : ℕ) (hi : i < R.m) {b : ℕ} (lam' : X.Tau → DomWeight b) (hT : 0 < Pr.T u)
    (rho : UF X.E (R.N i) →* Module.End X.K (DIV.VV X.K (W.lamTrue u i))) (rho' : UF X.E b →* Module.End X.K (DIV.VV X.K lam'))
    (hq : MuqTie Ch sel mu cst)
    (hs : A.AnaStepD (R.N i) b (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (stepDeg W u i))
    (heqT : ThEquivP (stepT W Ch sel mu cst A u i lam') (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) rho rho') :
    ThDist.Ok (stepC W Ch sel mu cst A u i lam') (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) rho rho'
      (rhoS Ch sel mu i) (rhoT Ch sel mu i) :=
  have heq : ThEquivP (stepC W Ch sel mu cst A u i lam') (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) rho rho' := by
    rw [stepC_eq_stepT W Ch sel mu cst hq A u i hi lam']; exact heqT
  thDistC_ok_deg A (Sall sel mu u) (rowSG Pr sel mu) _ sel (mUof Ch mu i) (muAt Ch sel mu cst i) (W.lamTrue u i) lam' (nuLast W u i)
    (modulus_pos sel mu cst u hT) rho rho' _ _ (lattice_classes_finite_refinement X _ _ _)
    (jetAddDeg_of_ana A (modulus_pos sel mu cst u hT) hs) heq
    (muDetLaw_chain Ch sel mu cst i _) (muDetLaw_chain Ch sel mu cst i _) (unitInv_rho Ch sel mu i)

theorem chTh_ok_ambD (hm : m2 + 1 < R.m) (hT : 0 < Pr.T u) (hq : MuqTie Ch sel mu cst) (h : ThHypD W Ch sel mu cst A u m2) :
    ChTh.Ok (Ch := Ch) cst (chTh W Ch sel mu cst A u m2) where
  th i hi := stepC_ok_deg W Ch sel mu cst A u i (by omega) _ hT _ _ hq (h.1 i hi) (h.2.2.1 i hi)
  top := stepC_ok_deg W Ch sel mu cst A u (m2 + 1) hm _ hT _ _ hq h.2.1 h.2.2.2

theorem inst_ambD (hm : m2 + 1 < R.m) (hT : 0 < Pr.T u) (hq : MuqTie Ch sel mu cst) (hTh : ThHypD W Ch sel mu cst A u m2)
    (b : L.β (m2 + 1)) (P : LevFam X.E X.K R.r Pr.vGs)
    (hK : KerHypOn W Ch sel mu cst L A u m2 b (coupling_index_set_finite sel mu cst L u m2 b) P)
    (hlev : (cst.sharp = false ∧ P = rP0 Ch) ∨ (cst.sharp = true ∧ P = rPsymF Ch)) :
    ChTh.Ok (Ch := Ch) cst (chTh W Ch sel mu cst A u m2) ∧
      (chKerC W Ch sel mu cst L A u m2 b (coupling_index_set_finite sel mu cst L u m2 b) P (kerEquivC_of W Ch sel mu cst L A u m2 b _ P hK)).Shape
        (chTh W Ch sel mu cst A u m2) :=
  ⟨chTh_ok_ambD W Ch sel mu cst A u m2 hm hT hq hTh, chKerC_shape W Ch sel mu cst L A u m2 b _ P _ hlev⟩

theorem theta_hypothesis_degree_form : ThHypDOf := by
  intro X Pr R W Ch sel S mu cst A u m2 h
  exact ⟨fun i hi => ⟨(h.1 i hi).1, (h.1 i hi).2.1, jets_rational_of_degree_form _ _ _ _ _ _ _ (h.1 i hi).2.2⟩,
    ⟨h.2.1.1, h.2.1.2.1, jets_rational_of_degree_form _ _ _ _ _ _ _ h.2.1.2.2⟩, h.2.2.1, h.2.2.2⟩

end Chain

section ChainN

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m)
  {D : D7} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (u : Pr.Word) (m2 : ℕ)

theorem chTh_ok_ofD (hm : m2 + 1 < R.m) (hT : 0 < Pr.T u) (h : ThHypND W Ch sel mu cst G s B χ cD u m2) :
    ChTh.Ok (Ch := Ch) cst (chTh W Ch sel mu cst (ambOf s B χ cD) u m2) :=
  chTh_ok_ambD W Ch sel mu cst (ambOf s B χ cD) u m2 hm hT h.2.1.1 h.2.2

theorem inst_ofD (hm : m2 + 1 < R.m) (hT : 0 < Pr.T u) (hTh : ThHypND W Ch sel mu cst G s B χ cD u m2)
    (b : L.β (m2 + 1)) (P : LevFam X.E X.K R.r Pr.vGs)
    (hK : KerHypOn W Ch sel mu cst L (ambOf s B χ cD) u m2 b (coupling_index_set_finite sel mu cst L u m2 b) P)
    (hlev : (cst.sharp = false ∧ P = rP0 Ch) ∨ (cst.sharp = true ∧ P = rPsymF Ch)) :
    ChTh.Ok (Ch := Ch) cst (chTh W Ch sel mu cst (ambOf s B χ cD) u m2) ∧
      (chKerC W Ch sel mu cst L (ambOf s B χ cD) u m2 b (coupling_index_set_finite sel mu cst L u m2 b) P
        (kerEquivC_of W Ch sel mu cst L (ambOf s B χ cD) u m2 b _ P hK)).Shape (chTh W Ch sel mu cst (ambOf s B χ cD) u m2) :=
  inst_ambD W Ch sel mu cst L (ambOf s B χ cD) u m2 hm hT hTh.2.1.1 hTh.2.2 b P hK hlev

end ChainN

theorem theta_distribution_unfold_degree : ThDistUnfD := by
  intro X A a b Sall SB D sel mU mI lam lam' n hV hrat Y Y' fr fr' hinj hdet sh sS sD hn N f N' f' c x hR P
  have h1 : ((thDistC A Sall SB D sel mU mI lam lam' n N f N' f' c x P : DIV.VV X.K lam') : DIV.Pol X.K X.Tau b) =
      (muInvDet sel SB mU mI N f * (muInvDet sel SB mU mI N' f')⁻¹) • jetMap (A.jetK Sall N N' c x) n (P : DIV.Pol X.K X.Tau a) := by
    unfold thDistC
    rw [if_pos ⟨hR.2.2.2.1, hR.2.2.2.2⟩, LinearMap.smul_apply, Submodule.coe_smul, jetOp_coe lam lam' n hV]
  have hPc := map_mem_VV A.σ₀ lam (P : DIV.Pol X.K X.Tau a) P.2
  have key := unfolding_gl_eval ℂ X.Tau a b Y Y' fr fr' hinj hdet (RingHom.id ℂ) A.cD (A.thInd Sall N N' c x)
    (fun m => (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' c x) m) (A.chiF a b N N')⁻¹ (fun _ => rfl) sh sS sD n hn (MvPolynomial.map A.σ₀ (P : DIV.Pol X.K X.Tau a))
  have hloc : jetMap (fun m => (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' c x) m) n (MvPolynomial.map A.σ₀ (P : DIV.Pol X.K X.Tau a)) =
      jetMap (fun m => A.σ₀ (A.jetK Sall N N' c x m)) n (MvPolynomial.map A.σ₀ (P : DIV.Pol X.K X.Tau a)) :=
    jet_local_rationality ℂ X.Tau a b lam n _ _ (fun m hm => (jetK_spec_deg A Sall D _ hrat N N' c x hR m hm).symm) _ hPc
  rw [hloc, ← map_jetMap, evG_id_map, evG_id_map] at key
  rw [h1, evG_smul, key, smul_smul]

theorem kernel_table_spec_degree : TabKSpecD := by
  intro X A a b Sall cA cB dg hA hB hsm hrat N N' hN hN' Ξ m hm
  have := kerFin Sall N N' hN hN' cA cB hA hB
  let _ := Fintype.ofFinite (↥(divLat cA (homAt Sall N N')) ⧸ (mulLat cB (homAt Sall N N')).comap (divLat cA (homAt Sall N N')).subtype)
  set rep := fun z : ↥(divLat cA (homAt Sall N N')) ⧸ (mulLat cB (homAt Sall N N')).comap (divLat cA (homAt Sall N N')).subtype =>
    ((Function.surjInv (Submodule.Quotient.mk_surjective ((mulLat cB (homAt Sall N N')).comap (divLat cA (homAt Sall N N')).subtype)) z :
      ↥(divLat cA (homAt Sall N N'))) : HomE X.E a b) with hrep
  have hR : ∀ z, InRange Sall (cA * cB) cB N N' (rep z) := fun z =>
    ⟨hN, hN', hB, Dvd.intro_left _ rfl, divLat_mul_of cA cB _ (Subtype.coe_prop _)⟩
  have hs := indSmooth_of A a b Sall (cA * cB) hsm
  have h1 : A.thDat Sall cA cB N N' Ξ = fun w => ∑ z, A.σ₀ (Ξ (rep z)) * A.thInd Sall N N' cB (rep z) w := by
    funext w
    unfold Amb.thDat latSum
    rw [finsum_eq_sum_of_fintype]
  have h2 : derivAt0 (A.thDat Sall cA cB N N' Ξ) m = ∑ z, A.σ₀ (Ξ (rep z)) * derivAt0 (A.thInd Sall N N' cB (rep z)) m := by
    have h3 : derivAt0 (A.thDat Sall cA cB N N' Ξ) m = ∑ z, derivAt0 (fun w => A.σ₀ (Ξ (rep z)) * A.thInd Sall N N' cB (rep z) w) m := by
      unfold derivAt0
      rw [h1, iteratedFDeriv_sum (fun z _ => contDiff_const.mul (hs N N' cB (rep z) (hR z) _))]
      rw [Finset.sum_apply, _root_.sum_apply]
    rw [h3]
    exact Finset.sum_congr rfl fun z _ => derivAt0_const_mul _ _ (hs N N' cB (rep z) (hR z)) m
  have h4 : A.tabK Sall cA cB N N' Ξ m = ∑ z, Ξ (rep z) * A.jetK Sall N N' cB (rep z) m := by
    unfold Amb.tabK latSum
    rw [finsum_eq_sum_of_fintype]
  rw [h4, map_sum]
  unfold jetC
  rw [h2, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [map_mul, jetK_spec_deg A Sall (cA * cB) dg hrat N N' cB (rep z) (hR z) m hm]
  unfold jetC
  ring

theorem descent_table_spec : DescentTableSpec := by
  intro X A a b Sall cA cB dg N N' Ξ h m hm
  obtain ⟨k, hk⟩ := h m hm
  unfold Amb.descentTableFirst
  rw [← hk, desc_map]

theorem descent_table_eq : DescentTablesAgree := by
  intro X A a b Sall cA cB dg hA hB hsm hrat N N' hN hN' Ξ
  have h := kernel_table_spec_degree X A a b Sall cA cB dg hA hB hsm hrat N N' hN hN' Ξ
  refine ⟨fun m hm => ⟨_, h m hm⟩, fun m hm => ?_⟩
  unfold Amb.descentTableFirst
  rw [← h m hm, desc_map]

theorem jetFieldDeg_le_iff {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (dg : X.Tau → ℕ) (k : IntermediateField ℚ ℂ) :
    A.jetFieldDeg a b Sall D dg ≤ k ↔ ∀ z ∈ A.jetSetDeg a b Sall D dg, z ∈ k := by
  unfold Amb.jetFieldDeg
  rw [IntermediateField.adjoin_le_iff]
  rfl

theorem jets_rational_degree_iff : JetsRatDegIff := by
  intro X A a b Sall D dg
  constructor
  · intro h z hz
    have hle : A.jetFieldDeg a b Sall D dg ≤ rangeIF A.σ₀ := by
      rw [jetFieldDeg_le_iff]
      rintro w ⟨N, N', c, x, m, hr, hm, rfl⟩
      exact (mem_rangeIF _ _).2 (h N N' c x hr m hm)
    exact (mem_rangeIF _ _).1 (hle hz)
  · intro h N N' c x hr m hm
    exact h _ (IntermediateField.subset_adjoin ℚ _ ⟨N, N', c, x, m, hr, hm, rfl⟩)

theorem jets_rational_degree_with_field : JetsRatDegWithK := by
  intro X A M _ _ hM a b Sall D dg hle N N' c x hr m hm
  have hz : (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' c x) m ∈ A.jetFieldDeg a b Sall D dg :=
    IntermediateField.subset_adjoin ℚ _ ⟨N, N', c, x, m, hr, hm, rfl⟩
  refine ⟨⟨_, hle hz⟩, ?_⟩
  exact congrArg (fun G => (A.chiF a b N N')⁻¹ * jetC A.cD G m) (withK_thInd A M hM Sall N N' c x).symm

theorem jetFieldDeg_le {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (dg : X.Tau → ℕ) :
    A.jetFieldDeg a b Sall D dg ≤ A.jetField a b Sall D := by
  rw [jetFieldDeg_le_iff]
  rintro w ⟨N, N', c, x, m, hr, _, rfl⟩
  exact IntermediateField.subset_adjoin ℚ _ ⟨N, N', c, x, m, hr, rfl⟩

theorem chain_rational_degree_of_cosets : StepsRatDegOfCos := by
  intro D L hT Gi Gl K Y cX ex t hF hC u μ hU i hi N N' c x hR m hm
  obtain ⟨k, hk⟩ := hC u μ hU i hi N N' c x hR m hm
  obtain ⟨y, hy⟩ := hF k
  exact ⟨y, hy.trans hk⟩

theorem chain_rational_degree_each : StepsRatStepDeg := by
  intro D L hT Gi Gl K Y cX ex t W hF hC hW u μ hU i hi
  have e : stepDeg W (t.word u) i = fun τ => ∑ r, nuT D u i (t.seam.iT τ) r := funext fun τ => hW u i hi τ
  rw [e]
  exact chain_rational_degree_of_cosets D L hT Gi Gl K Y cX ex t hF hC u μ hU i hi

theorem anaTopD_of {X : Fields} (A : Amb X) {R : Ranks} {m2 : ℕ} (hm : R.m = m2 + 2) {Sall : Finset (HeightOneSpectrum (𝓞 X.E))} {D : ℕ} {dg : X.Tau → ℕ}
    (h : A.AnaStepD (R.N (m2 + 1)) (R.N (m2 + 1 + 1)) Sall D dg) : A.AnaStepD (R.N (m2 + 1)) (R.N R.m) Sall D dg := by
  rw [hm]; exact h

open Classical in

theorem exists_degAt {ι : Type} [Fintype ι] {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (dg : ι → ℕ) : ∃ m : DVar ι a b →₀ ℕ, ∀ τ, degAt m τ = dg τ := by
  refine ⟨Finsupp.equivFunOnFinite.symm fun k => if k.2 = (⟨0, hb⟩, ⟨0, ha⟩) then dg k.1 else 0, fun τ => ?_⟩
  rw [degAt_eq, Finset.sum_eq_single (τ, (⟨0, hb⟩, ⟨0, ha⟩))]
  · simp
  · rintro ⟨τ', k⟩ _ hne
    by_cases h1 : τ' = τ
    · subst h1
      have : k ≠ (⟨0, hb⟩, ⟨0, ha⟩) := fun h => hne (by rw [h])
      simp [this]
    · simp [h1]
  · simp

open Classical in

theorem exists_tabNe_deg {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (u : Pr.Word) (i : ℕ) :
    ∃ J : (DVar X.Tau (R.N i) (R.N (i + 1)) →₀ ℕ) → X.K, (∀ m, (¬ ∀ τ, degAt m τ = stepDeg W u i τ) → J m = 0) ∧ TabNe (W.lamTrue u i) (nuLast W u i) J := by
  obtain ⟨J, P, hP, hne⟩ := exists_tabNe_step W u i
  refine ⟨fun m => if ∀ τ, degAt m τ = stepDeg W u i τ then J m else 0, fun m hm => if_neg hm, P, hP, ?_⟩
  have e : jetMap (fun m => if ∀ τ, degAt m τ = stepDeg W u i τ then J m else 0) (nuLast W u i) P = jetMap J (nuLast W u i) P :=
    jet_local_rationality X.K X.Tau _ _ (W.lamTrue u i) (nuLast W u i) _ J (fun m hm => if_pos hm) P hP
  rw [e]
  exact hne

end Formalism.L2.Ker
