import Mathlib
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCastMemDifferentIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRayFieldInRestrictScalars
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionParamLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvdDiscrTorsionField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscFieldEqTorsionField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardFilterLeLogClassNumber
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeDvdOfMemDifferent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host Formalism.L2.Rows GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open GlobalTheory.HilbertInClosure
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.SmallFieldPieces

section Copy

variable (ι : Qb →+* ℂ)

theorem qb_eq_of_map {L : Fld} {M : IntermediateField ℚ ℂ} (h : L.map ι.toRatAlgHom = M) : qb ι M = L := by
  rw [← h, qb, IntermediateField.comap_map]

theorem map_qb (M : IntermediateField ℚ ℂ) [Algebra.IsAlgebraic ℚ M] : (qb ι M).map ι.toRatAlgHom = M := by
  refine IntermediateField.map_comap_eq_self fun z hz => ?_
  exact exists_eq_of_isAlgebraic ι
    (IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (⟨z, hz⟩ : M)))

theorem qb_mono {M N : IntermediateField ℚ ℂ} (h : M ≤ N) : qb ι M ≤ qb ι N := fun _ hx => h hx

theorem finrank_qb (M : IntermediateField ℚ ℂ) [Algebra.IsAlgebraic ℚ M] :
    Module.finrank ℚ (qb ι M) = Module.finrank ℚ M :=
  (AlgEquiv.ofRingEquiv (R := ℚ) (f := qbEquiv ι M) fun q => by simp).toLinearEquiv.finrank_eq

theorem discr_qb (M : IntermediateField ℚ ℂ) [NumberField M] [NumberField (qb ι M)] : discr (qb ι M) = discr M :=
  discr_eq_discr_of_ringEquiv _ (qbEquiv ι M)

theorem qb_imField {E : Type} [Field E] [NumberField E] (j : E →ₐ[ℚ] Qb) (φ : E →+* ℂ) (h : ∀ x, ι (j x) = φ x) :
    qb ι (imField φ) = j.fieldRange := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, ι.injective ((h y).trans hy)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, (h y).symm⟩

theorem qb_cycField {n : ℕ} (hn : n ≠ 0) : qb ι (cycField n) = muFld n := by
  refine qb_eq_of_map ι ?_
  rw [muFld, IntermediateField.adjoin_map]
  refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (cycField_le_iff.2 ?_)
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_cycField hn (by rw [← map_pow, show x ^ n = 1 from hx, map_one])
  · have h1 : rootOne n ^ n = 1 := (Complex.isPrimitiveRoot_exp n hn).pow_eq_one
    obtain ⟨x, hx⟩ := exists_eq_of_isAlgebraic ι (z := rootOne n)
      (IsAlgebraic.of_pow (Nat.pos_of_ne_zero hn) (h1 ▸ isAlgebraic_one))
    exact IntermediateField.subset_adjoin ℚ _ ⟨x, ι.injective (by rw [map_pow, hx, h1, map_one]), hx⟩

theorem qb_KC (d : ℕ) : qb ι (KC d) = KQ d := by
  refine qb_eq_of_map ι ?_
  rw [KQ, sqQ, IntermediateField.adjoin_map]
  refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_simple_le_iff.2 ?_)
  · rintro _ ⟨x, hx, rfl⟩
    have h1 : ι x ^ 2 = sqrtNegNat d ^ 2 := by
      rw [← map_pow, show x ^ 2 = _ from hx, sqrtNegNat_sq]
      simp
    have h2 := IntermediateField.mem_adjoin_simple_self ℚ (sqrtNegNat d)
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exact (show ι x ∈ KC d from h ▸ h2)
    · exact (show ι x ∈ KC d from h ▸ neg_mem h2)
  · obtain ⟨x, hx⟩ := exists_eq_of_isAlgebraic ι (z := sqrtNegNat d)
      (IsAlgebraic.of_pow two_pos (by rw [sqrtNegNat_sq]; exact (isAlgebraic_nat d).neg))
    refine IntermediateField.subset_adjoin ℚ _ ⟨x, ι.injective ?_, hx⟩
    rw [map_pow, hx, sqrtNegNat_sq]
    simp

end Copy

theorem abelOver_of_isAbelianGalois {E : Type} [Field E] [NumberField E] (j : E →ₐ[ℚ] Qb) (L : Fld)
    (h : j.fieldRange ≤ L) (hab : letI := algThrough j L h; IsAbelianGalois E L) : AbelOver j.fieldRange L := by
  have hm : ∀ σ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → σ ∈ GalOf j.fieldRange := fun σ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).2
  refine ⟨h, fun σ hσ => map_mem_of_normal j L h ?_ σ (hm σ hσ),
    fun σ τ hσ hτ => (isAbelianGalois_iff j L h).1 hab σ (hm σ hσ) τ (hm τ hτ)⟩
  let := algThrough j L h
  infer_instance

theorem isHilbertCF_qb (hA : GlobalArtinReciprocity) (hW : WeberRayFieldSt) (ι : Qb →+* ℂ) {d : ℕ}
    {F : IntermediateField ℚ ℂ} {A : WeierstrassCurve F} (hd : d.Prime) (h4 : d % 4 = 3) (h3 : 3 < d)
    (hF : IsGoodCMCurve d F A) :
    ∃ (_ : NumberField (hilbertField d F)) (_ : FiniteDimensional ℚ (qb ι (hilbertField d F))),
      IsHilbertCF d (qb ι (hilbertField d F)) := by
  obtain ⟨hN, hdisc, h2, hR⟩ := isRayFieldIn_hilbertField hW d F A hd h4 h3 hF
  have hx : (IntermediateField.AdjoinSimple.gen ℚ (sqrtNegNat d)) ^ 2 =
      -(d : ℚ⟮sqrtNegNat d⟯) := Subtype.ext (by simpa using sqrtNegNat_sq d)
  have hTC := isTotallyComplex_of_sq_eq_neg hd.pos hx
  let j : ℚ⟮sqrtNegNat d⟯ →ₐ[ℚ] Qb :=
    ((qb ι ℚ⟮sqrtNegNat d⟯).val.toRingHom.comp (qbEquiv ι ℚ⟮sqrtNegNat d⟯).symm.toRingHom).toRatAlgHom
  have hj : ∀ x, ι (j x) = x := fun x =>
    congrArg Subtype.val ((qbEquiv ι ℚ⟮sqrtNegNat d⟯).apply_symm_apply x)
  have hr : j.fieldRange = KQ d := by
    rw [← qb_KC ι d, ← qb_imField ι j (ℚ⟮sqrtNegNat d⟯.val : ℚ⟮sqrtNegNat d⟯ →+* ℂ) hj]
    exact congrArg _ (le_antisymm (fun _ ⟨x, hx⟩ => hx ▸ x.2) fun z hz => ⟨⟨z, hz⟩, rfl⟩)
  have he : (ℚ⟮sqrtNegNat d⟯.val : ℚ⟮sqrtNegNat d⟯ →+* ℂ) = ι.comp j.toRingHom := RingHom.ext fun x => (hj x).symm
  obtain ⟨hN', h, hab, hd', hmax⟩ := hilbert_qb hA _ j ι _ (he ▸ hR)
  rw [hdisc, h2, Int.natAbs_neg, Int.natAbs_natCast] at hd' hmax
  refine ⟨hR.numberField, inferInstance, hr ▸ abelOver_of_isAbelianGalois j _ h hab, hd', fun L _ hL hU => ?_⟩
  have : NumberField L := {}
  rw [← hr] at hL
  refine hmax L hL.1 ((isAbelianGalois_iff j L hL.1).2 fun σ hσ τ hτ => hL.2.2 σ τ ?_ ?_) hU
  exacts [(IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ]

theorem squarefree_modulus (P : Pre) : Squarefree (modulus P) := by
  have g0 := P.host.g_prime 0
  have g1 := P.host.g_prime 1
  have p0 := P.host.pde_prime
  have p1 := P.host.pde'_prime
  simp only [modulus, Nat.squarefree_mul_iff, Nat.coprime_mul_iff_left, Nat.coprime_primes, g0, g1, p0, p1,
    g0.squarefree, g1.squarefree, p0.squarefree, p1.squarefree, and_true]
  exact ⟨⟨⟨(P.host.pde_ne_g 0).2.symm, (P.host.pde_ne_g 1).2.symm⟩, P.host.pde_ne⟩,
    ⟨(P.host.pde_ne_g 0).1.symm, (P.host.pde_ne_g 1).1.symm⟩, P.host.g_ne⟩

theorem coprime_discr {R : Ranks} (H : Host R) {p : ℕ} (hp : p % (H.QS * H.q * H.d) = 1) :
    Nat.Coprime p (discr H.E).natAbs := by
  have hc : Nat.Coprime p (H.QS * H.q * H.d) := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hp, Nat.gcd_one_left]
  refine Nat.Coprime.symm (Nat.coprime_of_dvd fun k hk h1 h2 => ?_)
  exact hk.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc h2 (H.der.discr_primes.1 k hk (Int.natCast_dvd.2 h1)))

theorem ray_qb (hA : GlobalArtinReciprocity) {P : Pre} (δ : FieldDat P) (T : Frame P.host) :
    ∃ _ : NumberField (qb T.ι δ.ray), AbelOver T.j.fieldRange (qb T.ι δ.ray) ∧
      (discr (qb T.ι δ.ray)).natAbs ∣
        (discr P.host.E).natAbs ^ (Module.finrank ℚ (qb T.ι δ.ray) / Module.finrank ℚ P.host.E) *
          modulus P ^ Module.finrank ℚ (qb T.ι δ.ray) := by
  have he : P.host.φ₀ = T.ι.comp T.j.toRingHom := RingHom.ext fun x => (T.phi0 x).symm
  obtain ⟨hN, h, hR⟩ := isRayField_qb T.j T.ι (he ▸ δ.isRay)
  refine ⟨hN, abelOver_of_isAbelianGalois _ _ h hR.1, ?_⟩
  let := algThrough T.j _ h
  rw [finrank_div]
  refine RayDiscr.natAbs_discr_dvd hA.rayClassFieldSt _ _ _ (squarefree_modulus P) ?_ hR
  exact (((coprime_discr _ (P.g_cond 0)).mul_left (coprime_discr _ (P.g_cond 1))).mul_left
    (coprime_discr _ P.pde_cond.1)).mul_left (coprime_discr _ P.pde_cond.2)

theorem kPsi_qb {P : Pre} (δ : FieldDat P) (T : Frame P.host) :
    ∃ S : Fin P.R.m → Finset Qb, (∀ j, (S j).card ≤ Nat.log 2 (classNumber P.host.E)) ∧
      (∀ j, ∀ y ∈ S j, ∃ n : ℕ, 0 < n ∧ n ∣ classNumber P.host.E ∧ y ^ n ∈ T.j.fieldRange) ∧
      qb T.ι (⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j) =
        T.j.fieldRange ⊔ muFld (classNumber P.host.E) ⊔ IntermediateField.adjoin ℚ (⋃ j, (S j : Set Qb)) := by
  choose S hc hy hK using fun j : ℕ =>
    exists_kPsiField_generators P.R P.host δ.basis (P.R.sigW j).1 (P.R.sigW j).2
  have hE := qb_imField T.ι T.j P.host.φ₀ T.phi0
  have hal : ∀ j, ∀ y ∈ S j, IsAlgebraic ℚ y := fun j y h => by
    obtain ⟨n, hn, -, x, hx⟩ := hy j y h
    exact IsAlgebraic.of_pow hn (hx ▸ (Algebra.IsAlgebraic.isAlgebraic x).algHom P.host.φ₀.toRatAlgHom)
  refine ⟨fun j => (S (j + 1)).preimage T.ι T.ι.injective.injOn, fun j => le_trans ?_ (hc (j + 1)), fun j y h => ?_, ?_⟩
  · exact Finset.card_le_card_of_injOn T.ι (fun y h => Finset.mem_preimage.1 h) T.ι.injective.injOn
  · obtain ⟨n, hn, hd, h⟩ := hy _ _ (Finset.mem_preimage.1 h)
    exact ⟨n, hn, hd, hE ▸ mem_qb.2 (by rwa [map_pow])⟩
  · have hm := P.R.two_le_m
    have : Algebra.IsAlgebraic ℚ (imField P.host.φ₀) :=
      (AlgEquiv.ofInjectiveField P.host.φ₀.toRatAlgHom).isAlgebraic
    have h0 := classNumber_ne_zero P.host.E
    have : Algebra.IsAlgebraic ℚ (cycField (classNumber P.host.E)) :=
      IntermediateField.isAlgebraic_adjoin_simple (IsIntegral.of_pow (Nat.pos_of_ne_zero h0) (by
        rw [(Complex.isPrimitiveRoot_exp _ h0).pow_eq_one]; exact isIntegral_one))
    refine qb_eq_of_map _ ?_
    rw [← hE, ← qb_cycField T.ι h0, IntermediateField.map_sup, IntermediateField.map_sup, map_qb, map_qb,
      IntermediateField.adjoin_map, Set.image_iUnion]
    have hi : ∀ j, T.ι.toRatAlgHom '' ((S j).preimage T.ι T.ι.injective.injOn : Set Qb) = S j := fun j => by
      rw [Finset.coe_preimage]
      exact Set.image_preimage_eq_of_subset fun z hz => exists_eq_of_isAlgebraic _ (hal j z hz)
    simp only [hi, FieldDat.KPsi, hK]
    refine le_antisymm (sup_le ?_ (IntermediateField.adjoin_le_iff.2 (Set.iUnion_subset fun j => ?_)))
      (iSup₂_le fun j hj => sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _)
    · exact le_iSup₂_of_le 1 ⟨le_rfl, by omega⟩ le_sup_left
    · exact IntermediateField.adjoin_le_iff.1 (le_iSup₂_of_le (j + 1) ⟨by omega, j.2⟩ le_sup_right)
    · refine Set.subset_iUnion_of_subset ⟨j - 1, by have := hj.1; have := hj.2; omega⟩ ?_
      rw [Nat.sub_add_cancel hj.1]

theorem exists_twelfth_root (M : Fld) [NumberField M] {y : Qb} (hy : y ∈ M) :
    ∃ h : y ^ 12 ∈ M, (∃ I : FractionalIdeal (𝓞 M)⁰ M,
      FractionalIdeal.spanSingleton (𝓞 M)⁰ (⟨y ^ 12, h⟩ : M) = I ^ 12) ∧ M = M ⊔ IntermediateField.adjoin ℚ {y} :=
  ⟨pow_mem hy 12, ⟨FractionalIdeal.spanSingleton _ ⟨y, hy⟩, by rw [FractionalIdeal.spanSingleton_pow]; rfl⟩,
    (sup_eq_left.2 (IntermediateField.adjoin_simple_le_iff.2 hy)).symm⟩

theorem exists_pieces : GlobalArtinReciprocity → WeberRayFieldSt → ∀ (X : Stages) (f : Fr X.B.toPre)
    (δ : FieldDat X.B.toPre) (T : HostTied X.toD7), ∃ P : KsPieces X.toD7 T,
      P.HK = qb T.fr.ι (hilbertField X.B.host.d δ.jField) ∧ P.rcf = qb T.fr.ι δ.ray ∧ P.M = qb T.fr.ι δ.M ∧
        P.MDel = qb T.fr.ι δ.M' ∧ P.KPs = qb T.fr.ι (⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j) := by
  intro hA hW X _ δ T
  have h16 : X.B.host.d % 16 = 7 := X.B.host.hyp.2.2.2.1
  obtain ⟨hH, hH', hilb⟩ := isHilbertCF_qb hA hW T.fr.ι X.B.host.hyp.2.1 (by omega) (by omega) δ.good
  obtain ⟨hR, hab, hcond⟩ := ray_qb hA δ T.fr
  obtain ⟨hF, hEll, -, -, -, -, hred⟩ := δ.good
  obtain ⟨hMf, hdeg⟩ := TorsionDegree.finrank_torsionField_le X.B.host.d δ.jField δ.curve
  have hM : NumberField δ.M := @NumberField.of_module_finite ℚ _ _ _ _ _ hMf
  have hMq := numberField_qb T.fr.ι δ.M
  have hMM : δ.M' = δ.M := DiscRoot.discField_eq_torsionField _ _ _
  obtain ⟨hK, hKram⟩ := KPsiRam.prime_dvd_discr_iSup_kPsi _ δ
  have hKq := numberField_qb T.fr.ι (⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j :)
  have hHq := numberField_qb T.fr.ι (hilbertField X.B.host.d δ.jField)
  have hram : ∀ p : ℕ, p.Prime → p ∣ (discr (qb T.fr.ι δ.M)).natAbs → p ∣ 6 * X.B.host.d := fun p hp h => by
    rw [discr_qb] at h
    have : NumberField (torsionField X.B.host.d δ.curve) := hM
    refine (TorsionRam.dvd_discr_torsionField _ _ δ.curve hred p hp h).elim id fun h => ?_
    rw [← discr_qb T.fr.ι, show (discr (qb T.fr.ι (hilbertField X.B.host.d δ.jField))).natAbs = _ from hilb.2.1] at h
    exact (hp.dvd_of_dvd_pow h).mul_left 6
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (δ.curve.Δ : ℂ) (show 0 < 12 by norm_num)
  have hzM : z ∈ δ.M := hMM ▸ ((discField_le_iff _ δ.curve).1 le_rfl).2.2.2 z hz
  have hz0 : z ≠ 0 := fun h => δ.curve.isUnit_Δ.ne_zero (Subtype.ext (by rw [← hz, h]; norm_num))
  let y := (qbEquiv T.fr.ι δ.M).symm ⟨z, hzM⟩
  have hy0 : (y : Qb) ≠ 0 := fun h => hz0 (congrArg Subtype.val
    ((map_eq_zero (qbEquiv T.fr.ι δ.M).symm).1 (Subtype.ext h)))
  obtain ⟨hy, hI, hgen⟩ := exists_twelfth_root _ y.2
  obtain ⟨S, hS1, hS2, hS3⟩ := kPsi_qb δ T.fr
  exact ⟨{
    HK := qb T.fr.ι (hilbertField X.B.host.d δ.jField)
    rcf := qb T.fr.ι δ.ray
    M := qb T.fr.ι δ.M
    MDel := qb T.fr.ι δ.M
    KPs := qb T.fr.ι (⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j)
    HK_hilb := hilb
    E_le_rcf := hab.1
    rcf_abel := hab
    rcf_cond := hcond
    HK_le_M := qb_mono _ (hilbertField_le_torsionField _ _)
    M_deg := by rw [finrank_qb, finrank_qb]; exact hdeg
    M_ram := hram
    MDel_gen := ⟨y, hy, hy0, hI, hgen⟩
    MDel_ram := hram
    KPs_gen := ⟨S, hS1, hS2, hS3⟩
    KPs_ram := fun p hp h => hKram p hp (by rwa [discr_qb] at h)
    M_le_MDel := le_rfl
    E_le_KPs := hS3 ▸ le_sup_left.trans le_sup_left }, rfl, rfl, rfl, by rw [hMM], rfl⟩

end GlobalTheory.SmallFieldPieces

end
