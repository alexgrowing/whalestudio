import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PhiMaps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ThickAlg

set_option linter.overlappingInstances false

noncomputable section

open IsLocalRing Matrix Polynomial UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.W UpperTheory.V.CA UpperTheory.V.Pr.Thick

namespace UpperTheory.V.Pr

private theorem exists_emb' {k κ K : Type} [Field k] [Field κ] [Algebra k κ] [Algebra.IsAlgebraic k κ] [Field K]
    [IsAlgClosed K] (φ : k →+* K) : ∃ j : κ →+* K, ∀ a, j (algebraMap k κ a) = φ a := by
  letI : Algebra k K := φ.toAlgebra
  haveI : Module.IsTorsionFree k κ := Module.isTorsionFree_iff_algebraMap_injective.2 (algebraMap k κ).injective
  haveI : Module.IsTorsionFree k K := Module.isTorsionFree_iff_algebraMap_injective.2 φ.injective
  let j : κ →ₐ[k] K := IsAlgClosed.lift
  exact ⟨j, fun a => j.commutes a⟩

private theorem exists_emb {k K : Type} [Field k] [Field K] [IsAlgClosed K] (φ : k →+* K) :
    ∃ j : AlgebraicClosure k →+* K, ∀ a, j (algebraMap k (AlgebraicClosure k) a) = φ a :=
  exists_emb' φ

section Link

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
  {F : Frame l (ResidueField O)} {G : W.GFrame l} {r : W.Resid G O 3} (K : TwLink F r)
  {Q : Type} [CommRing Q] [Algebra O Q]

private def twr (s : F.G0 →* Matrix (Fin 3) (Fin 3) Q) : G.G₀ →* Matrix (Fin 3) (Fin 3) Q where
  toFun g := algebraMap O Q (K.κ g) • s (K.π g)
  map_one' := by simp
  map_mul' g h := by rw [map_mul, map_mul, map_mul, Units.val_mul, map_mul, smul_mul_smul_comm]

private theorem twr_apply (s : F.G0 →* Matrix (Fin 3) (Fin 3) Q) (g : G.G₀) :
    twr K s g = algebraMap O Q (K.κ g) • s (K.π g) := rfl

private theorem ofRep_twr (ρ : NRep F 3 Q) (s : F.G0 →* Matrix (Fin 3) (Fin 3) Q) (hs : IsThickMod ρ s)
    (hρ : ∀ g i j, Odd (w 3 i - w 3 j) → ρ.r g i j = 0) : GDet.ofRep (K.tw ρ) = GDet.ofRep (twr K s) := by
  refine d_gext _ _ fun g i _ _ => ?_
  unfold GDet.lam
  have e : ∀ σ : G.G₀ →* Matrix (Fin 3) (Fin 3) Q, GDet.repAlg σ Q (MonoidAlgebra.single g 1) = σ g := fun σ => by
    ext a b
    simp [GDet.repAlg]
  rw [chi_ofRep, chi_ofRep, e, e]
  have h : (K.tw ρ g).charpoly = (twr K s g).charpoly := by
    change (algebraMap O Q (K.κ g) • ρ.r (K.π g)).charpoly = (algebraMap O Q (K.κ g) • s (K.π g)).charpoly
    have e00 := hs.even (K.π g) 0 0 (by decide)
    have e11 := hs.even (K.π g) 1 1 (by decide)
    have e22 := hs.even (K.π g) 2 2 (by decide)
    have e02 := hs.even (K.π g) 0 2 (by decide)
    have e20 := hs.even (K.π g) 2 0 (by decide)
    have e10 := hρ (K.π g) 1 0 (by decide)
    have e12 := hρ (K.π g) 1 2 (by decide)
    obtain ⟨s10, s12⟩ := hs.sub (K.π g)
    simp [Matrix.charpoly, Matrix.det_fin_three, e00, e11, e22, e02, e20, e10, e12, s10, s12]
  rw [h]

private theorem th_star {B : Type} [CommRing B] [Algebra O B] (f : B →ₐ[O] Q) (s : F.G0 →* Matrix (Fin 3) (Fin 3) Q)
    (g : G.G₀) (a : B) : th (f : B →+* Q) (twr K s) (G.star O B 3 (MonoidAlgebra.single g a)) =
      f a • algebraMap O Q (K.κ g) • s (F.star (K.π g)) := by
  have h1 : K.π (G.conj g)⁻¹ = F.star (K.π g) := by rw [map_inv, K.π_conj, Frame.star, map_inv]
  have h2 : K.κ g = G.eps O O g ^ (1 - ((3 : ℕ) : ℤ)) * K.κ (G.conj g)⁻¹ := by
    rw [← K.κ_conj, map_inv, mul_inv_cancel_right]
  have h3 : f ((G.eps O B g ^ (1 - ((3 : ℕ) : ℤ)) : Bˣ) : B) =
      algebraMap O Q ((G.eps O O g ^ (1 - ((3 : ℕ) : ℤ)) : Oˣ) : O) := by
    have : G.eps O B g = Units.map (algebraMap O B : O →* B) (G.eps O O g) := Units.ext rfl
    rw [this, ← map_zpow]
    exact f.commutes _
  rw [star_single, th_single, twr_apply, h1, h2, smul_smul, smul_smul, Units.val_mul, map_mul, map_mul,
    RingHom.coe_coe, h3, mul_assoc]

private theorem kills [CharP (ResidueField O) l] [IsLocalRing Q] [IsNoetherianRing Q] (B : UniversalOrdinaryDeterminantRing r) (f : B.B →ₐ[O] Q)
    (hf : ∀ a ∈ maximalIdeal B.B, f a ∈ maximalIdeal Q) (ρ : NRep F 3 Q) (s : F.G0 →* Matrix (Fin 3) (Fin 3) Q)
    (hs : IsThickMod ρ s) (hc : ∀ i j, AdicCont (maximalIdeal Q) fun g => s g i j)
    (hD : B.u.D.map (f : B.B →+* Q) = GDet.ofRep (twr K s))
    (hψ : ∀ v i, pushCh (f : B.B →+* Q) (B.u.ψ v i) = K.twψ ρ v i) :
    ∀ y ∈ B.GroupAlgebraKernelIdeal, th (f : B.B →+* Q) (twr K s) y = 0 := by
  have hψ' : ∀ v i g, f (B.u.ψ v i g) = algebraMap O Q (K.κ (G.φ v g)) * ρ.ψ (K.e v) i (K.lam v g) := fun v i g => by
    rw [mul_comm]
    exact congrArg (fun χ : G.Gv v →* Qˣ => (χ g : Q)) (hψ v i)
  intro y hy
  refine th_closure _ (f : B.B →+* Q) hf _ (fun i j N => ?_) _ ?_ hy
  · have hO : maximalIdeal O ≤ (maximalIdeal Q).comap (algebraMap O Q) := fun a ha => by
      have : algebraMap O B.B a ∈ maximalIdeal B.B := map_nonunit _ a ha
      have h := hf _ this
      rwa [f.commutes] at h
    have hle : maximalIdeal O ^ N ≤ (maximalIdeal Q ^ N).comap (algebraMap O Q) :=
      le_trans (Ideal.pow_right_mono hO N) (Ideal.le_comap_pow _ N)
    have h1 := (K.κ_cont N).comp (Ideal.quotientMap _ (algebraMap O Q) hle)
    have h2 := (hc i j N).comp_continuous K.π_cont
    exact h1.mul h2
  · rintro z ((hz | ⟨v, g, rfl | rfl⟩) | ⟨u, g, hg, hz⟩)
    · exact th_CH hD hz
    · have h0 := hs.ord (K.e v) fun i => K.lam v (g i)
      have e : ∀ i, th (f : B.B →+* Q) (twr K s) (MonoidAlgebra.single (G.φ v (g i)) 1 -
          MonoidAlgebra.single 1 (B.u.ψ v i (g i) : B.B)) = algebraMap O Q (K.κ (G.φ v (g i))) •
            (s (F.loc0 _ (K.lam v (g i))) - (ρ.ψ (K.e v) i (K.lam v (g i)) : Q) • 1) := fun i => by
        rw [map_sub, th_single, th_single, map_one, map_one, one_smul, twr_apply, RingHom.coe_coe, hψ', K.lam_loc,
          smul_sub, smul_smul]
      simp only [ordProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one] at h0
      simp only [GFrame.oEl, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, map_mul, e,
        smul_mul_assoc, mul_smul_comm, h0, smul_zero]
    · have h0 := hs.ord_star (K.e v) fun i => K.lam v (g i.rev)
      have e : ∀ i, th (f : B.B →+* Q) (twr K s) (G.star O B.B 3 (MonoidAlgebra.single (G.φ v (g i)) 1 -
          MonoidAlgebra.single 1 (B.u.ψ v i (g i) : B.B))) = algebraMap O Q (K.κ (G.φ v (g i))) •
            (s (F.star (F.loc0 _ (K.lam v (g i)))) - (ρ.ψ (K.e v) i (K.lam v (g i)) : Q) • 1) := fun i => by
        have e1 : ∀ a b, G.star O B.B 3 (a - b) = G.star O B.B 3 a - G.star O B.B 3 b := fun a b => by
          simp [GFrame.star]
        rw [e1, map_sub, th_star, th_star, hψ', K.lam_loc, smul_sub, smul_smul]
        simp [Frame.star, smul_smul]
      have e2 : ∀ a b, G.star O B.B 3 (a * b) = G.star O B.B 3 b * G.star O B.B 3 a := fun a b => by
        simp [GFrame.star]
      simp only [ordProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one] at h0
      simp only [GFrame.oEl, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, map_mul, e, e2,
        smul_mul_assoc, mul_smul_comm, mul_assoc]
      erw [h0]
      simp
    · obtain ⟨m, hm, h1, h2⟩ := K.tame u g hg.1
      have hm' : IsUnit (m : Q) := by
        have : IsUnit (m : O) := by
          rw [← notMem_maximalIdeal, ← residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero_iff _ l]
          exact hm
        simpa using this.map (algebraMap O Q)
      have h3 : algebraMap O Q (K.κ g) ^ m = 1 := by
        rw [← map_pow, ← Units.val_pow_eq_pow_val, h2, Units.val_one, map_one]
      rcases hz with rfl | rfl
      · refine th_Ip B hg (f := (f : B.B →+* Q)) hf hD hm' _ (Or.inl rfl) ?_
        rw [th_single, map_one, one_smul, twr_apply, _root_.smul_pow, h3, ← map_pow, h1, map_one, one_smul]
      · refine th_Ip B hg (f := (f : B.B →+* Q)) hf hD hm' _ (Or.inr rfl) ?_
        rw [th_star, map_one, one_smul, _root_.smul_pow, h3, ← map_pow, Frame.star, ← map_pow, inv_pow, h1, inv_one,
          map_one, map_one, one_smul]

end Link

end UpperTheory.V.Pr

end

open IsLocalRing Matrix Polynomial UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.W UpperTheory.V.CA UpperTheory.V.Pr.Thick in
theorem UpperTheory.V.Pr.thickOf :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (T : UpperTheory.V.Pr.Setup F 3), T.ThickOf := by
  intro l _ O _ _ _ _ _ F T Φ hΦ x L P hP hthick
  obtain ⟨hTE, s, hc, hs⟩ := hthick
  haveI : Nontrivial (L.R ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP.ne_top
  haveI : IsLocalRing (L.R ⧸ P) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have hmax : (maximalIdeal L.R).map (Ideal.Quotient.mk P) = maximalIdeal (L.R ⧸ P) :=
    map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  rw [hmax] at hc
  haveI : Finite (ResidueField L.R) := Finite.of_surjective _ (resMap_bijective L.O' L.R).2
  let f : T.B.B →ₐ[O] L.R ⧸ P := ((Ideal.Quotient.mkₐ O P).comp L.ι).comp (T.S.inc.comp Φ)
  have hf : ∀ a ∈ maximalIdeal T.B.B, f a ∈ maximalIdeal (L.R ⧸ P) := fun a ha => by
    rw [← hmax]
    exact Ideal.mem_map_of_mem _ (local_of_finite (T.phi Φ L : T.B.B →+* L.R) a ha)
  obtain ⟨hD, hψ⟩ := TwLink.IsPhi.maps T.K hΦ ((Ideal.Quotient.mkₐ O P).comp L.ι)
  change T.B.u.D.map (f : T.B.B →+* L.R ⧸ P) = GDet.ofRep (T.K.tw (L.ρ.map (Ideal.Quotient.mk P))) at hD
  change ∀ v i, pushCh (f : T.B.B →+* L.R ⧸ P) _ = T.K.twψ (L.ρ.map (Ideal.Quotient.mk P)) v i at hψ
  rw [ofRep_twr T.K _ s hs fun g i j h => Ideal.Quotient.eq_zero_iff_mem.2
    (hTE.2.2 (Ideal.subset_span ⟨g, i, j, h, rfl⟩))] at hD
  have hk := kills T.K T.B f hf _ s hs hc hD hψ
  let K' := AlgebraicClosure (FractionRing (L.R ⧸ P))
  let ι : L.R ⧸ P →+* K' := (algebraMap (FractionRing (L.R ⧸ P)) K').comp (algebraMap _ _)
  have hι : Function.Injective ι :=
    (algebraMap (FractionRing (L.R ⧸ P)) K').injective.comp (IsFractionRing.injective _ _)
  let q := T.back Φ L P
  have hq : ∀ a, ι (f a) = 0 ↔ a ∈ q.asIdeal := fun a => by
    rw [map_eq_zero_iff _ hι]
    exact Ideal.Quotient.eq_zero_iff_mem
  obtain ⟨j, hj⟩ : ∃ j : T.B.kap q →+* K', j.comp (T.B.toKap q) = ι.comp (f : T.B.B →+* L.R ⧸ P) := by
    obtain ⟨j, hj⟩ := exists_emb (Ideal.ResidueField.lift q.asIdeal (ι.comp (f : T.B.B →+* L.R ⧸ P))
      (fun a ha => (hq a).2 ha) fun a ha => Ne.isUnit fun h => ha ((hq a).1 h))
    exact ⟨j, RingHom.ext fun a => (hj _).trans (Ideal.ResidueField.lift_algebraMap _ _ _ _ a)⟩
  let σ := ι.mapMatrix.toMonoidHom.comp (twr T.K s)
  have hσ : ∀ g, σ g 1 0 = 0 ∧ σ g 1 2 = 0 := fun g => by
    change ι (_ * s (T.K.π g) 1 0) = 0 ∧ ι (_ * s (T.K.π g) 1 2) = 0
    simp [hs.sub]
  have hD' : (T.B.u.D.map (T.B.toKap q)).map j = GDet.ofRep σ := by
    refine Eq.trans ?_ ((d_gmap (GDet.ofRep (twr T.K s))).2.2.2 ι _)
    rw [(d_gmap _).2.1, hj, ← hD, (d_gmap _).2.1]
  refine ⟨fun ⟨ρ₀, h1, h2⟩ => not_irr j σ hσ ρ₀ (h2 ▸ hD') h1, fun hss => hs.nonsplit K' ι hι ?_⟩
  have hle : TwoSidedIdeal.span (MonoidAlgebra.mapRingHom T.G.G₀ (T.B.toKap q) '' T.B.GroupAlgebraKernelIdeal) ≤
      TwoSidedIdeal.ker (th j σ) := by
    rw [TwoSidedIdeal.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_ker, th_comp, hj, th_map, hk z hz]
    exact Matrix.map_zero _ (map_zero ι)
  obtain ⟨y, hy1, hy⟩ := split_of_ss j σ hσ _ hD' _ (fun y hy => (TwoSidedIdeal.mem_ker _).1 (hle hy)) hss
  refine ⟨y, hy1, fun g => ?_⟩
  obtain ⟨g, rfl⟩ := T.K.π_surj g
  have hu : ι (algebraMap O _ (T.K.κ g)) ≠ 0 := (((T.K.κ g).isUnit.map _).map ι).ne_zero
  have e : σ g = ι (algebraMap O _ (T.K.κ g)) • (s (T.K.π g)).map ι := by
    ext a b
    exact map_mul ι _ _
  have h := hy g
  rw [e, Matrix.smul_mulVec, Matrix.smul_apply, smul_assoc] at h
  exact smul_right_injective _ hu h
