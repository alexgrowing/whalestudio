import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.UnipTorsion
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.CurveNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ZpowWNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext

set_option linter.overlappingInstances false

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V

private theorem pe_const {k K : Type} [Field k] [Finite k] [Field K] (φ : k →+* PowerSeries K) (a : k) :
    φ a = PowerSeries.C (PowerSeries.constantCoeff (φ a)) := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  set p := ringChar k with hpdef
  haveI : CharP k p := ringChar.charP k
  haveI : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  obtain ⟨m, _, hcard⟩ := FiniteField.card k p
  haveI : CharP (PowerSeries K) p := charP_of_injective_ringHom φ.injective p
  set f := φ a with hf
  set c := PowerSeries.constantCoeff f with hc
  set g := f - PowerSeries.C c with hg
  have hfq : f ^ Fintype.card k = f := by
    rw [hf, ← map_pow, FiniteField.pow_card]
  have hcq : c ^ Fintype.card k = c := by
    rw [hc, ← map_pow, hfq]
  have hsplit : f = PowerSeries.C c + g := by rw [hg]; ring
  have hgq : g ^ Fintype.card k = g := by
    have e := hfq
    rw [hsplit, hcard, add_pow_char_pow, ← map_pow, ← hcard, hcq] at e
    exact add_left_cancel e
  have hg0 : PowerSeries.constantCoeff g = 0 := by
    rw [hg, map_sub, PowerSeries.constantCoeff_C, hc, sub_self]
  by_contra hne
  have hgne : g ≠ 0 := fun h0 => hne (by rw [← sub_eq_zero]; exact h0)
  have ho1 : 1 ≤ g.order := PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hg0
  have hotop : g.order ≠ ⊤ := fun ht => hgne (PowerSeries.order_eq_top.mp ht)
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hotop
  have hq : 2 ≤ Fintype.card k := Fintype.one_lt_card
  have e2 := congrArg PowerSeries.order hgq
  rw [PowerSeries.order_pow, ← hd, nsmul_eq_mul] at e2
  rw [← hd] at ho1
  have e3 : Fintype.card k * d = d := by exact_mod_cast e2
  have e4 : 1 ≤ d := by exact_mod_cast ho1
  nlinarith

private theorem pe_curve (l : ℕ) [Fact l.Prime] (O O' R : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]
    [CommRing O'] [IsLocalRing O'] [Finite (ResidueField O')] [CommRing R] [Algebra O' R] [IsCO O' R] [Algebra O R]
    (p : Ideal R) (hp : p.IsPrime) (hd : ringKrullDim (R ⧸ p) = 1) (hl : (l : R) ∈ p)
    (hm : ∀ a ∈ maximalIdeal O, algebraMap O R a ∈ p) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : Algebra (ResidueField O) K) (_ : Algebra O K)
      (_ : IsScalarTower O (ResidueField O) K) (j : R →ₐ[O] PowerSeries K), RingHom.ker j = p ∧ IsLocalHom j := by
  haveI : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
  haveI : IsDomain (R ⧸ p) := (Ideal.Quotient.isDomain_iff_prime p).mpr hp
  haveI hco : IsCO O' (R ⧸ p) := co_quot O' R (R ⧸ p) (Ideal.Quotient.mkₐ O' p) Ideal.Quotient.mk_surjective
  haveI : IsNoetherianRing (R ⧸ p) := hco.toIsNoetherian
  haveI : IsAdicComplete (maximalIdeal (R ⧸ p)) (R ⧸ p) := hco.complete
  haveI : IsLocalHom (algebraMap O' (R ⧸ p)) := hco.isLocalHom
  haveI : Finite (ResidueField (R ⧸ p)) := by
    refine Finite.of_surjective (ResidueField.map (algebraMap O' (R ⧸ p))) ?_
    intro y
    obtain ⟨z, rfl⟩ := residue_surjective y
    obtain ⟨a, ha⟩ := hco.res_surj z
    refine ⟨residue O' a, ?_⟩
    rw [ResidueField.map_residue, eq_comm]
    exact Ideal.Quotient.eq.mpr ha
  haveI : CharP (R ⧸ p) l := by
    rw [CharP.charP_iff_prime_eq_zero (Fact.out)]
    rw [← map_natCast (Ideal.Quotient.mk p), Ideal.Quotient.eq_zero_iff_mem]
    exact hl
  obtain ⟨k, _, _, f, hfi, hfl, _⟩ := Pr.T.curveNorm l hd
  let g : O →+* R ⧸ p := (Ideal.Quotient.mk p).comp (algebraMap O R)
  have hg : ∀ a ∈ maximalIdeal O, g a = 0 := fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (hm a ha)
  let ψ : ResidueField O →+* R ⧸ p := Ideal.Quotient.lift (maximalIdeal O) g hg
  let φ : ResidueField O →+* PowerSeries k := f.comp ψ
  let c : ResidueField O →+* k := PowerSeries.constantCoeff.comp φ
  letI ak : Algebra (ResidueField O) k := c.toAlgebra
  letI aO : Algebra O k := (c.comp (residue O)).toAlgebra
  haveI tw : IsScalarTower O (ResidueField O) k := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let j : R →ₐ[O] PowerSeries k :=
    { toRingHom := f.comp (Ideal.Quotient.mk p)
      commutes' := by
        intro a
        rw [PowerSeries.algebraMap_apply]
        change φ (residue O a) = PowerSeries.C (c (residue O a))
        exact pe_const φ (residue O a) }
  refine ⟨k, inferInstance, inferInstance, ak, aO, tw, j, ?_, ?_⟩
  · ext z
    change f (Ideal.Quotient.mk p z) = 0 ↔ z ∈ p
    rw [map_eq_zero_iff f hfi, Ideal.Quotient.eq_zero_iff_mem]
  · refine ⟨fun z hz => ?_⟩
    have h1 : IsUnit (f (Ideal.Quotient.mk p z)) := hz
    have h2 : IsUnit (Ideal.Quotient.mk p z) := hfl.map_nonunit _ h1
    haveI := IsLocalHom.of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
    exact IsLocalHom.map_nonunit _ h2

private theorem pe_res {O B K : Type} [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B] [IsCO O B] [Field K]
    [Finite K] [Algebra (ResidueField O) K] [Algebra O K] [IsScalarTower O (ResidueField O) K] (f : B →+* K)
    (hf : ∀ a, f (algebraMap O B a) = algebraMap O K a) :
    f = (algebraMap (ResidueField O) K).comp (res O B : B →+* ResidueField O) := by
  have hmax : RingHom.ker f = maximalIdeal B := by
    haveI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
    haveI : Finite (B ⧸ RingHom.ker f) := Finite.of_injective _ (RingHom.kerLift_injective f)
    have hM := Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (B ⧸ RingHom.ker f))
    exact IsLocalRing.eq_maximalIdeal hM
  ext b
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) (R := B) b
  have h1 : f (b - algebraMap O B a) = 0 := by
    rw [← RingHom.mem_ker, hmax]
    exact ha
  have h2 : res O B (b - algebraMap O B a) = 0 := (res_eq_zero_iff O B _).mpr ha
  rw [map_sub, sub_eq_zero] at h1 h2
  rw [RingHom.comp_apply, h1, hf]
  erw [h2]
  rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

private theorem pe_inj {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (f : A →+* B)
    (hf : Function.Injective f) (D D' : W.GDet n A G) (h : D.map f = D'.map f) : D = D' := by
  refine CA.d_gext D D' fun g i _ _ => hf ?_
  rw [← ((CA.d_gmap D).2.2.1 f _).2 i, ← ((CA.d_gmap D').2.2.1 f _).2 i, h]

private theorem pe_chi {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (W.GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  rw [Matrix.charpoly]
  show Matrix.det _ = _
  congr 1
  simp [W.GDet.repAlg, MonoidAlgebra.lift_single, Matrix.charmatrix, Matrix.smul_one_eq_diagonal]

private theorem pe_cont {Γ R R' : Type} [TopologicalSpace Γ] [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (f : R →+* R') [IsLocalHom f] {a : Γ → R} (h : AdicCont (maximalIdeal R) a) :
    AdicCont (maximalIdeal R') fun g => f (a g) := by
  intro N
  have h0 : maximalIdeal R ≤ Ideal.comap f (maximalIdeal R') := fun x hx => by
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => (IsLocalRing.mem_maximalIdeal x).mp hx (isUnit_of_map_unit f x hu)
  have hle : maximalIdeal R ^ N ≤ Ideal.comap f (maximalIdeal R' ^ N) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact pow_le_pow_left' (Ideal.map_le_iff_le_comap.mpr h0) N
  have e : (fun g => Ideal.Quotient.mk (maximalIdeal R' ^ N) (f (a g))) =
      (Ideal.quotientMap _ f hle) ∘ (fun g => Ideal.Quotient.mk (maximalIdeal R ^ N) (a g)) := by
    funext g
    simp [Ideal.quotientMap_mk]
  show IsLocallyConstant (fun g => Ideal.Quotient.mk (maximalIdeal R' ^ N) (f (a g)))
  rw [e]
  exact (h N).comp _

section Tw

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
  {F : Frame l (ResidueField O)} {n : ℕ} {G : W.GFrame l} {r : W.Resid G O n} (K : Pr.TwLink F r)
  {A A' : Type} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A']

private theorem pe_tw_map (f : A →ₐ[O] A') (ρ : NRep F n A) :
    K.tw (ρ.map (f : A →+* A')) = (f : A →+* A').mapMatrix.toMonoidHom.comp (K.tw ρ) := by
  ext g i j
  simp [Pr.TwLink.tw, Pr.TwLink.κA]

private theorem pe_twψ_map (f : A →ₐ[O] A') (ρ : NRep F n A) (v : G.Vl) (i : Fin n) :
    K.twψ (ρ.map (f : A →+* A')) v i = W.pushCh (f : A →+* A') (K.twψ ρ v i) := by
  ext g
  simp [Pr.TwLink.twψ, Pr.TwLink.κA]

private theorem pe_maps {B : Type} [CommRing B] [Algebra O B] [IsCO O B] (u : W.Pair r B) (φ : B →+* A)
    (f : A →ₐ[O] A') (ρ : NRep F n A) (h : u.Maps φ (W.GDet.ofRep (K.tw ρ)) (K.twψ ρ)) :
    u.Maps ((f : A →+* A').comp φ) (W.GDet.ofRep (K.tw (ρ.map (f : A →+* A')))) (K.twψ (ρ.map (f : A →+* A'))) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun v i => ?_⟩
  · rw [pe_tw_map K f ρ, ← (CA.d_gmap u.D).2.1 φ (f : A →+* A'), h1,
      (CA.d_gmap (W.GDet.ofRep (K.tw ρ))).2.2.2]
  · rw [pe_twψ_map K f ρ v i, ← h2 v i]
    ext g
    rfl

private theorem pe_maps_of {B : Type} [CommRing B] [Algebra O B] [IsCO O B] (u : W.Pair r B) (φ : B →+* A)
    (f : A →ₐ[O] A') (hf : Function.Injective f) (ρ : NRep F n A)
    (h : u.Maps ((f : A →+* A').comp φ) (W.GDet.ofRep (K.tw (ρ.map (f : A →+* A'))))
      (K.twψ (ρ.map (f : A →+* A')))) : u.Maps φ (W.GDet.ofRep (K.tw ρ)) (K.twψ ρ) := by
  refine ⟨pe_inj (f : A →+* A') hf _ _ ?_, fun v i => ?_⟩
  · rw [(CA.d_gmap u.D).2.1, h.1, (CA.d_gmap (W.GDet.ofRep (K.tw ρ))).2.2.2, pe_tw_map]
  · have h1 := h.2 v i
    rw [pe_twψ_map] at h1
    ext g
    exact hf (congrArg Units.val (DFunLike.congr_fun h1 g))

private theorem pe_form (ρ : NRep F n A) : G.IsForm O n (K.tw ρ).toHomUnits (Jgl A n) := by
  intro g
  have hk : (K.κA A) g * (K.κA A) (G.conj g) = (G.eps O A) g ^ (1 - (n : ℤ)) := by
    have h := congrArg (Units.map ((algebraMap O A : O →+* A) : O →* A)) (K.κ_conj g)
    rw [map_mul, map_zpow] at h
    have e1 : ∀ x, K.κA A x = Units.map ((algebraMap O A : O →+* A) : O →* A) (K.κ x) := fun x => rfl
    have e2 : G.eps O A g = Units.map ((algebraMap O A : O →+* A) : O →* A) (G.eps O O g) := by
      ext
      simp [W.GFrame.eps, W.pushCh]
    rw [e1, e1, e2]
    exact h
  have hstar : ∀ h : F.G0, ρ.r (F.conj h) = Jmat A n * (ρ.r h⁻¹)ᵀ * Jmat A n := by
    intro h
    have h' := ρ.pol h⁻¹
    simpa [Frame.star] using h'
  have hinv : ∀ h : F.G0, (ρ.r h)ᵀ * (ρ.r h⁻¹)ᵀ = 1 := by
    intro h
    rw [← Matrix.transpose_mul, ← map_mul, inv_mul_cancel, map_one, Matrix.transpose_one]
  have hJ : ((Jgl A n : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = Jmat A n := rfl
  show (K.tw ρ g)ᵀ * _ * K.tw ρ (G.conj g) = _
  rw [hJ]
  simp only [Pr.TwLink.tw, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [K.π_conj g, hstar, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  have hm : (ρ.r (K.π g))ᵀ * Jmat A n * (Jmat A n * (ρ.r (K.π g)⁻¹)ᵀ * Jmat A n) = Jmat A n := by
    calc (ρ.r (K.π g))ᵀ * Jmat A n * (Jmat A n * (ρ.r (K.π g)⁻¹)ᵀ * Jmat A n)
        = (ρ.r (K.π g))ᵀ * (Jmat A n * Jmat A n) * (ρ.r (K.π g)⁻¹)ᵀ * Jmat A n := by
          simp only [Matrix.mul_assoc]
      _ = Jmat A n := by
          rw [Jmat_mul_Jmat, Matrix.mul_one, hinv, Matrix.one_mul]
  rw [hm]
  congr 1
  rw [mul_comm, ← Units.val_mul, hk]

private theorem pe_flag (ρ : NRep F n A) (v : G.Vl)
    (h : W.HasFlag (ρ.r.comp (F.loc0 (K.e v))).toHomUnits (ρ.ψ (K.e v))) :
    W.HasFlag ((K.tw ρ).toHomUnits.comp (G.φ v)) (K.twψ ρ v) := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P, fun s => ?_⟩
  obtain ⟨h1, h2⟩ := hP (K.lam v s)
  have key : ((P * ((K.tw ρ).toHomUnits.comp (G.φ v)) s * P⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)
      = ((K.κA A) (G.φ v s) : A) •
        ((P * (ρ.r.comp (F.loc0 (K.e v))).toHomUnits (K.lam v s) * P⁻¹ : GL (Fin n) A) :
          Matrix (Fin n) (Fin n) A) := by
    simp only [Units.val_mul, MonoidHom.comp_apply, MonoidHom.coe_toHomUnits]
    simp only [Pr.TwLink.tw, MonoidHom.coe_mk, OneHom.coe_mk, K.lam_loc]
    rw [Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [key, Matrix.smul_apply, h1 i j hij, smul_zero]
  · rw [key, Matrix.smul_apply, h2 i]
    simp [Pr.TwLink.twψ, mul_comm]
    try rfl

private theorem pe_tw_cont [IsLocalRing A] [IsLocalHom (algebraMap O A)] (ρ : NRep F n A)
    (h : ∀ i j, AdicCont (maximalIdeal A) fun g => ρ.r g i j) (i j : Fin n) :
    AdicCont (maximalIdeal A) fun g => K.tw ρ g i j := by
  intro N
  have hloc : maximalIdeal O ≤ Ideal.comap (algebraMap O A) (maximalIdeal A) := by
    intro a ha
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp ha)) (isUnit_of_map_unit (algebraMap O A) a hu)
  have hle : maximalIdeal O ^ N ≤ Ideal.comap (algebraMap O A) (maximalIdeal A ^ N) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hloc) N
  have hκ : IsLocallyConstant fun g : G.G₀ =>
      Ideal.Quotient.mk (maximalIdeal A ^ N) (algebraMap O A (K.κ g : O)) := by
    have h' := (K.κ_cont N).comp (Ideal.quotientMap (maximalIdeal A ^ N) (algebraMap O A) hle)
    convert h' using 1
    funext g
    simp [Ideal.quotientMap_mk]
  have hr : IsLocallyConstant fun g : G.G₀ =>
      Ideal.Quotient.mk (maximalIdeal A ^ N) (ρ.r (K.π g) i j) :=
    (h i j N).comp_continuous K.π_cont
  have h2 := IsLocallyConstant.comp₂ hκ hr (· * ·)
  convert h2 using 1
  funext g
  simp [Pr.TwLink.tw, Pr.TwLink.κA, W.pushCh, map_mul]
  rw [Algebra.smul_def, map_mul]
  rfl

private theorem pe_ine {k : Type} [Field k] [Algebra (ResidueField O) k] [CharP (ResidueField O) l]
    [Algebra O (PowerSeries k)] (ρ : NRep F n (PowerSeries k))
    (h : (W.GDet.ofRep (K.tw ρ)).map (PowerSeries.constantCoeff : PowerSeries k →+* k) =
      r.Dbar.map (algebraMap (ResidueField O) k)) (u : G.St) (g : G.G₀) (hg : g ∈ r.Ip u) : K.tw ρ g = 1 := by
  have hIu : g ∈ G.Iu u := (Subgroup.mem_inf.mp hg).1
  have hker : ∀ i, r.chib i g = 1 := by
    intro i
    have h' := (Subgroup.mem_inf.mp hg).2
    exact (Subgroup.mem_iInf.mp h' i)
  obtain ⟨m, hlm, hπ, hκ⟩ := K.tame u g hIu
  have hdiag : W.diagRep r.chib g = 1 := by
    simp [W.diagRep, hker]
  have hchi : Polynomial.map (PowerSeries.constantCoeff : PowerSeries k →+* k) (K.tw ρ g).charpoly
      = (Polynomial.X - 1) ^ n := by
    have e := congrArg (fun D : W.GDet n k G.G₀ => D.chi (MonoidAlgebra.single g (1 : k))) h
    have s1 : MonoidAlgebra.mapRingHom G.G₀ (PowerSeries.constantCoeff : PowerSeries k →+* k)
        (MonoidAlgebra.single g 1) = MonoidAlgebra.single g 1 := by simp
    have s2 : MonoidAlgebra.mapRingHom G.G₀ (algebraMap (ResidueField O) k)
        (MonoidAlgebra.single g 1) = MonoidAlgebra.single g 1 := by simp
    have e1 := ((CA.d_gmap (W.GDet.ofRep (K.tw ρ))).2.2.1
      (PowerSeries.constantCoeff : PowerSeries k →+* k) (MonoidAlgebra.single g 1)).1
    have e2 := ((CA.d_gmap r.Dbar).2.2.1 (algebraMap (ResidueField O) k) (MonoidAlgebra.single g 1)).1
    rw [s1] at e1
    rw [s2] at e2
    rw [e1, e2] at e
    simp only [W.Resid.Dbar, pe_chi, hdiag, Matrix.charpoly_one, Fintype.card_fin, Polynomial.map_pow,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one] at e
    exact e
  have hres : Polynomial.map (residue (PowerSeries k)) (K.tw ρ g).charpoly = (Polynomial.X - 1) ^ n := by
    have hq : Polynomial.map (PowerSeries.constantCoeff : PowerSeries k →+* k)
        ((Polynomial.X - 1) ^ n : Polynomial (PowerSeries k)) = (Polynomial.X - 1) ^ n := by simp
    have hz : ∀ a : PowerSeries k, PowerSeries.constantCoeff a = 0 → residue (PowerSeries k) a = 0 := by
      intro a ha
      rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, ha]
      exact not_isUnit_zero
    have h0 : Polynomial.map (PowerSeries.constantCoeff : PowerSeries k →+* k)
        ((K.tw ρ g).charpoly - (Polynomial.X - 1) ^ n) = 0 := by
      rw [Polynomial.map_sub, hchi, hq, sub_self]
    have hd : Polynomial.map (residue (PowerSeries k)) ((K.tw ρ g).charpoly - (Polynomial.X - 1) ^ n) = 0 := by
      ext i
      rw [Polynomial.coeff_map, Polynomial.coeff_zero]
      apply hz
      have h3 : (Polynomial.map (PowerSeries.constantCoeff : PowerSeries k →+* k)
          ((K.tw ρ g).charpoly - (Polynomial.X - 1) ^ n)).coeff i = (0 : Polynomial k).coeff i := by
        rw [h0]
      rw [Polynomial.coeff_map, Polynomial.coeff_zero] at h3
      exact h3
    rw [Polynomial.map_sub, sub_eq_zero] at hd
    rw [hd]
    simp
  haveI : CharP k l := charP_of_injective_algebraMap (algebraMap (ResidueField O) k).injective l
  have hm : IsUnit ((m : ℕ) : PowerSeries k) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, map_natCast, isUnit_iff_ne_zero, Ne, CharP.cast_eq_zero_iff k l]
    exact hlm
  have hpow : (K.tw ρ g) ^ m = 1 := by
    rw [← map_pow]
    simp [Pr.TwLink.tw, Pr.TwLink.κA, W.pushCh, hπ, hκ]
  exact Pr.T.unipTorsion (K.tw ρ g) _ n m (Matrix.charpoly_monic _) (Matrix.aeval_self_charpoly _) hres hm hpow

end Tw

theorem UpperTheory.V.Pr.pointEx_of_le {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsCoef l O] [Algebra ℤ_[l] O] {F : Frame l (ResidueField O)} {n : ℕ} (T : Pr.Setup F n)
    (Φ : T.B.B →ₐ[O] T.S.B) (hΦ : T.IsPhi Φ) (x : Ideal T.S.A) (L : T.S.Loc x) (p : Ideal L.R) (hp : p.IsPrime)
    (hd : Pr.qdim p = 1) (hm : ∀ a ∈ maximalIdeal O, algebraMap O L.R a ∈ p) :
    ∃ (y : W.Point T.r) (j : L.R →ₐ[O] y.A), RingHom.ker j = p ∧ IsLocalHom j ∧
      W.mat y.ρ = T.K.tw (L.ρ.map (j : L.R →+* y.A)) ∧ y.ψ = T.K.twψ (L.ρ.map (j : L.R →+* y.A)) ∧
      T.B.IsPt y (j.comp (T.phi Φ L)) := by
  classical
  haveI : Finite (ResidueField O) := IsCoef.fin (l := l)
  have hl : ((l : ℕ) : L.R) ∈ p := by
    have h1 : ((l : ℕ) : O) ∈ maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
      haveI := IsCoef.char (l := l) (O := O)
      exact CharP.cast_eq_zero _ l
    have h2 := hm _ h1
    rwa [map_natCast] at h2
  haveI : Finite (ResidueField L.O') := IsCoef.fin (l := l)
  obtain ⟨K, _, _, _, _, _, j, hjk, hjl⟩ := pe_curve l O L.O' L.R p hp hd hl hm
  have hSu : T.S.u.map (T.S.A.val : T.S.A →+* T.S.R) = T.S.ρ :=
    NRep.ext (by ext g i j; rfl) (by funext v i; ext g; rfl)
  have h0 : T.B.u.Maps ((T.S.A.val : T.S.A →+* T.S.R).comp ((T.S.inc.comp Φ : T.B.B →ₐ[O] T.S.A) : T.B.B →+* T.S.A))
      (W.GDet.ofRep (T.K.tw (T.S.u.map (T.S.A.val : T.S.A →+* T.S.R))))
      (T.K.twψ (T.S.u.map (T.S.A.val : T.S.A →+* T.S.R))) := by
    rw [hSu]
    exact hΦ
  have h1 := pe_maps_of T.K T.B.u _ T.S.A.val Subtype.val_injective T.S.u h0
  have h2 := pe_maps T.K T.B.u _ (j.comp L.ι) T.S.u h1
  have hρ : T.S.u.map ((j.comp L.ι : T.S.A →ₐ[O] PowerSeries K) : T.S.A →+* PowerSeries K)
      = L.ρ.map (j : L.R →+* PowerSeries K) := by
    rw [Space.Loc.ρ, NRep.map_map]
    rfl
  rw [hρ] at h2
  have hpt : T.B.u.Maps ((j.comp (T.phi Φ L) : T.B.B →ₐ[O] PowerSeries K) : T.B.B →+* PowerSeries K)
      (W.GDet.ofRep (T.K.tw (L.ρ.map (j : L.R →+* PowerSeries K))))
      (T.K.twψ (L.ρ.map (j : L.R →+* PowerSeries K))) := h2
  have hmat : W.mat (T.K.tw (L.ρ.map (j : L.R →+* PowerSeries K))).toHomUnits
      = T.K.tw (L.ρ.map (j : L.R →+* PowerSeries K)) :=
    MonoidHom.ext fun g => MonoidHom.coe_toHomUnits _ g
  have hres := pe_res (O := O) (B := T.B.B) (K := K)
    ((PowerSeries.constantCoeff : PowerSeries K →+* K).comp
      ((j.comp (T.phi Φ L) : T.B.B →ₐ[O] PowerSeries K) : T.B.B →+* PowerSeries K))
    (fun a => by
      show PowerSeries.constantCoeff ((j.comp (T.phi Φ L)) (algebraMap O T.B.B a)) = _
      rw [AlgHom.commutes, PowerSeries.algebraMap_apply, PowerSeries.constantCoeff_C])
  have hred : (W.GDet.ofRep (T.K.tw (L.ρ.map (j : L.R →+* PowerSeries K)))).map
      (PowerSeries.constantCoeff : PowerSeries K →+* K) = T.r.Dbar.map (algebraMap (ResidueField O) K) := by
    rw [← hpt.1, (CA.d_gmap _).2.1, hres, ← (CA.d_gmap _).2.1, T.B.u.red]
  haveI : IsLocalHom (algebraMap O (PowerSeries K)) := ⟨fun a ha => by
    by_contra hna
    have hr : algebraMap O (ResidueField O) a = 0 :=
      (IsLocalRing.residue_eq_zero_iff a).mpr ((IsLocalRing.mem_maximalIdeal a).mpr hna)
    have h0 : algebraMap O K a = 0 := by
      rw [IsScalarTower.algebraMap_apply O (ResidueField O) K, hr, map_zero]
    rw [PowerSeries.algebraMap_apply, h0, map_zero] at ha
    exact not_isUnit_zero ha⟩
  haveI : IsLocalHom (j : L.R →+* PowerSeries K) := ⟨fun a ha => hjl.map_nonunit a ha⟩
  have hcont : ∀ i k, AdicCont (maximalIdeal (PowerSeries K))
      fun g => (L.ρ.map (j : L.R →+* PowerSeries K)).r g i k := fun i k =>
    pe_cont (j : L.R →+* PowerSeries K) ((loc_rho T.ok T.n23 T.S x L).1.1 i k)
  refine ⟨⟨K, (T.K.tw (L.ρ.map (j : L.R →+* PowerSeries K))).toHomUnits, ?_, Jgl _ n, ?_,
    pe_form T.K _, ?_, ?_, T.K.twψ (L.ρ.map (j : L.R →+* PowerSeries K)), ?_, ?_⟩, j, hjk, hjl,
    hmat, rfl, ?_⟩
  · intro a b
    rw [hmat]
    exact pe_tw_cont T.K _ hcont a b
  · exact Jmat_transpose n
  · rw [hmat]
    exact hred
  · intro u g hg
    haveI := IsCoef.char (l := l) (O := O)
    apply Units.ext
    rw [MonoidHom.coe_toHomUnits]
    exact pe_ine T.K _ hred u g hg
  · intro v i
    rw [← hpt.2 v i]
    refine MonoidHom.ext fun g => Units.ext ?_
    show PowerSeries.constantCoeff _ = algebraMap (ResidueField O) K _
    rw [← (T.B.u.psi v i).red g]
    exact RingHom.congr_fun hres _
  · intro v
    have hf0 := flag T.ok T.n23 T.S (PowerSeries K)
      ((j.comp L.ι : T.S.A →ₐ[O] PowerSeries K) : T.S.A →+* PowerSeries K) (T.K.e v)
    rw [hρ] at hf0
    obtain ⟨g, hg⟩ := pe_flag T.K _ v hf0
    refine ⟨Matrix.GeneralLinearGroup.map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) g,
      fun s => ⟨fun a b hab => ?_, fun a => ?_⟩⟩
    · have e := (hg s).1 a b hab
      rw [W.pushRep, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
      show (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) _ = 0
      exact (congrArg (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) e).trans (map_zero _)
    · have e := (hg s).2 a
      rw [W.pushRep, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
      show (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) _ =
        (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) _
      exact congrArg (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) e
  · exact ⟨hpt.1.trans (congrArg _ hmat.symm), hpt.2⟩

theorem UpperTheory.V.Pr.pointEx :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n), T.PointEx := by
  intro l _ O _ _ _ _ _ F n T Φ hΦ x L p hp hd hl
  have h0 := T.lne
  refine UpperTheory.V.Pr.pointEx_of_le T Φ hΦ x L p hp hd fun a ha => ?_
  haveI := hp
  have h1 : (l : O) ∈ p.comap (algebraMap O L.R) := by
    rw [Ideal.mem_comap, map_natCast]
    exact hl
  have h2 : (p.comap (algebraMap O L.R)).IsMaximal :=
    IsPrime.to_maximal_ideal fun h => h0 (by rwa [h, Ideal.mem_bot] at h1)
  rw [← eq_maximalIdeal h2] at ha
  exact ha
