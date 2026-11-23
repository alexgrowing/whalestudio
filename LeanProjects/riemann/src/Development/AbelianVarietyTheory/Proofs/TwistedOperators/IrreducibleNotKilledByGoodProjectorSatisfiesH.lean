import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IsometryCarriesCharacter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MonotoneTwoBlockIndicator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEqMapDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTameCharactersSeriesIdempotentsTameLabelleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapRangeAdjointLeBlockSum
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.GoodProjHypH

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.factPrime

theorem exists_char_of_fixed {K G W : Type} [Field K] [CharZero K] [Group G] [Fintype G] (emb : K →+* ℂ)
    (X : Finset (G → K)) (hX : ∀ χ ∈ X, Formalism.L2.DIV.IsAbsIrrChar χ) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (τ : Representation ℂ G W) (hτ : τ.IsIrreducible) (x : W) (hx0 : x ≠ 0)
    (hx : ∑ g, emb ((Formalism.L2.DIV.idemOf X).coeff g) • τ g x = x) : ∃ χ ∈ X, ∀ g, τ.character g = emb (χ g) := by
  classical
  let P : W →ₗ[ℂ] W := ∑ g, emb ((Formalism.L2.DIV.idemOf X).coeff g) • τ g
  have hPz : ∀ z, P z = ∑ g, emb ((Formalism.L2.DIV.idemOf X).coeff g) • τ g z := fun z => by
    simp [P, LinearMap.sum_apply]
  have hPx : P x = x := (hPz x).trans hx
  have hidem : IsIdempotentElem P := by
    refine LinearMap.ext fun z => ?_
    show P (P z) = P z
    rw [hPz, hPz z]
    exact GlobalTheory.AdjBlock.idem_idem emb hX τ z
  have htr : LinearMap.trace ℂ W P ≠ 0 := by
    intro h0
    have h1 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hidem h0
    exact hx0 (by rw [← hPx, h1, LinearMap.zero_apply])
  have htr' : LinearMap.trace ℂ W P =
      ∑ χ ∈ X, ∑ g, emb (χ 1 / (Fintype.card G : K) * χ g⁻¹) * τ.character g := by
    simp only [P, map_sum, map_smul, smul_eq_mul, Formalism.L2.DIV.coeff_idemOf, Finset.sum_mul]
    rw [Finset.sum_comm]
    rfl
  rw [htr'] at htr
  obtain ⟨χ, hχ, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero htr
  refine ⟨χ, hχ, ?_⟩
  obtain ⟨n, ρ, hρi, hρ⟩ := GlobalTheory.GoodTypeGeneric.isIrrChar_of_isAbsIrrChar emb (hX χ hχ)
  beta_reduce at hρ
  have hpair := GlobalTheory.BI.pair_character_eq_finrank ℂ ℂ G (Fin n → ℂ) W ρ τ
  have hfin : Module.finrank ℂ (ρ.IntertwiningMap τ) ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hpair
    apply hne
    unfold GlobalTheory.BI.pair at hpair
    rw [finsum_eq_sum_of_fintype] at hpair
    have hc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    have hs : ∑ g, τ.character g * ρ.character g⁻¹ = 0 := by
      simpa [hc] using hpair
    calc ∑ g, emb (χ 1 / (Fintype.card G : K) * χ g⁻¹) * τ.character g =
        emb (χ 1) / (Fintype.card G : ℂ) * ∑ g, τ.character g * ρ.character g⁻¹ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [map_mul, map_div₀, map_natCast, hρ g⁻¹]
          simp only [Algebra.algebraMap_self, RingHom.id_apply]
          ring
      _ = 0 := by rw [hs, mul_zero]
  haveI : ρ.IsIrreducible := hρi
  haveI : τ.IsIrreducible := hτ
  haveI := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hfin)
  obtain ⟨f, hf⟩ := exists_ne (0 : ρ.IntertwiningMap τ)
  rcases Representation.IsIrreducible.bijective_or_eq_zero f with hb | h0
  · intro g
    rw [hρ g, ← Representation.char_iso (Representation.IntertwiningMap.ofBijective f hb)]
    simp
  · exact absurd h0 hf

open GlobalTheory.BI Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.FiniteGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel GlobalTheory.GoodTypeGeneric in

theorem sum_typeChar_radical {p : ℕ} [Fact p.Prime] {r : ℕ} (s : GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.SSParam p ℂ r)
    (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.IsRegularParam s) {a : ℕ} (h0 : 0 < a) (ha : a < r)
    (hA : ∀ A : Finset (GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.Cyc s.1), ∑ c ∈ A, GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.cycLen s.1 c ≠ a)
    [Fintype (unipRadical (ZMod p) (Formalism.L2.DIV.blk2 (n := r) a))] :
    ∑ u : unipRadical (ZMod p) (Formalism.L2.DIV.blk2 (n := r) a), GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.typeChar s (u : GL (Fin r) (ZMod p)) = 0 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let b₀ : Fin r → ℕ := fun i => (s.1 i : ℕ)
  let w := Tuple.sort b₀
  let e := (cycEquiv s.1).trans w.symm
  have he : ∀ x y, (b₀ ∘ w) (e x) = (b₀ ∘ w) (e y) ↔ x.1 = y.1 := by
    intro x y
    simp only [e, b₀, Function.comp, Equiv.trans_apply, Equiv.apply_symm_apply, apply_cycEquiv, Fin.val_inj,
      Subtype.ext_iff]
  obtain ⟨n, σ, hσ, hch⟩ := exists_isCuspDatum (F := ZMod p) (Tuple.monotone_sort b₀) e he (fun c => cuspOn (s.2 c))
    (fun c => (irr_and_sum_of_isCusp (isCusp_cuspOn hs c)).1) fun c => (irr_and_sum_of_isCusp (isCusp_cuspOn hs c)).2
  have hchar : ∀ x, typeChar s x = (parInd (b₀ ∘ w) σ).character x := by
    intro x
    have hm : ∀ z : GL (Fin r) (ZMod p),
        ((permGL (ZMod p) w * z * (permGL (ZMod p) w)⁻¹ : GL (Fin r) (ZMod p)) :
          Matrix (Fin r) (Fin r) (ZMod p)).BlockTriangular s.1 ↔ z ∈ blockTri (κ := ZMod p) (b₀ ∘ w) := fun z =>
      Iff.trans Iff.rfl (conj_mem_blockTri (b := b₀))
    rw [character_coind_eq_ind]
    unfold typeChar ind
    congr 1
    · congr 2
      exact (Nat.card_congr ((MulAut.conj (permGL (ZMod p) w)).toEquiv.subtypeEquiv fun z => (hm z).symm)).symm
    · letI := Fintype.ofFinite (GL (Fin r) (ZMod p))
      rw [finsum_eq_sum_of_fintype]
      symm
      refine Fintype.sum_equiv (Equiv.mulRight (permGL (ZMod p) w)⁻¹) _ _ fun y => ?_
      have h1 : (Equiv.mulRight (permGL (ZMod p) w)⁻¹ y)⁻¹ * x * Equiv.mulRight (permGL (ZMod p) w)⁻¹ y =
          permGL (ZMod p) w * (y⁻¹ * x * y) * (permGL (ZMod p) w)⁻¹ := by
        simp only [Equiv.coe_mulRight]
        group
      rw [h1]
      unfold ext0
      by_cases hz : y⁻¹ * x * y ∈ blockTri (κ := ZMod p) (b₀ ∘ w)
      · rw [dif_pos hz, if_pos ((hm _).2 hz), hch]
        refine Finset.prod_congr rfl fun c _ => ?_
        unfold cuspOn
        congr 1
        ext i j
        rw [Matrix.submatrix_apply, blocksHom_apply]
        simp only [e, Equiv.trans_apply, cycEquiv_apply]
        rw [← conj_permGL_apply w, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        rfl
      · rw [dif_neg hz, if_neg (mt (hm _).1 hz)]
  have hnf : GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.NoFixed (parInd (b₀ ∘ w) σ) (GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical (ZMod p) r a) := by
    by_contra hfix
    obtain ⟨J, hJ, hJa⟩ := GlobalTheory.GoodNoFixed.fixedVectorBlocks (ZMod p) r (b₀ ∘ w) _ σ hσ _ (parInd (b₀ ∘ w) σ)
      ⟨LinearMap.id, Function.injective_id, fun _ => rfl⟩ a h0 ha hfix
    set Af := Finset.univ.filter fun c : Cyc s.1 => (c.1 : ℕ) ∈ J with hAf
    apply hA Af
    have hJim : J = Af.image fun c => (c.1 : ℕ) := by
      ext j
      simp only [hAf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hj
        obtain ⟨i, -, hi⟩ := Finset.mem_image.1 (hJ hj)
        exact ⟨⟨s.1 (w i), w i, rfl⟩, by rw [← hi] at hj; exact hj, hi⟩
      · rintro ⟨c, hc, rfl⟩
        exact hc
    rw [hJa, hJim, Finset.sum_image fun c _ c' _ h => Subtype.ext (Fin.ext h)]
    refine Finset.sum_congr rfl fun c _ => Fintype.card_congr (w.symm.subtypeEquiv fun i => ?_)
    simp only [b₀, Function.comp, Fin.val_inj, Equiv.apply_symm_apply]
  have h1 := (GlobalTheory.GoodNoFixed.noFixed_iff_sum (parInd (b₀ ∘ w) σ) (MonoidHom.id _)).1
    (by rwa [MonoidHom.coe_id, Set.image_id])
  simpa only [hchar, MonoidHom.id_apply] using h1

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.DimPartsCompare GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.FiniteGL in

theorem hypH_of_goodProj : GlobalTheory.Published.GreenCuspidal → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), Given R F → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (τ : Representation ℂ (G0 R.Pg D.R.r) W), τ.IsIrreducible →
    (∃ x : W, x ≠ 0 ∧ ∑ g, RealDat.eC (A := A) D.what₂.embLL g • τ (R.eG g) x = x) →
    ∀ a : ℕ, 0 < a → a < D.R.r → ∃ PP : R.Pg, GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.NoFixed τ
      {g | (∀ PP' : R.Pg, PP' ≠ PP → g PP' = 1) ∧ g PP ∈ GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical (kP PP.1) D.R.r a} := by
  intro hG D G _ _ Pl0 T A Ks _ _ _ R F hR W _ _ _ τ hτ hx a h0 ha
  classical
  obtain ⟨x, hx0, hx⟩ := hx
  obtain ⟨om, hT⟩ := GlobalTheory.T.exists_tameCharacters_seriesIdempotentsTameLabelled R F hR
  have hI := GlobalTheory.GoodIdemTie.idemTie_of_tameTie hG D om hT
  obtain ⟨χ, hχ, hτχ⟩ := exists_char_of_fixed D.what₂.embLL A.X hR.irr (τ.comp R.eG.toMonoidHom)
    (GlobalTheory.FinGL.Transport.isIrreducible_comp τ _ R.eG.surjective hτ) x hx0 hx
  obtain ⟨eR, plg, iso, h1, -, h2⟩ := hR.core.grp.record
  let π : LevelCuspCharacters.LevelGroup D.host ≃* G0g D.nd :=
    MulEquiv.ofBijective (⟨⟨pull, rfl⟩, fun _ _ => rfl⟩ : LevelCuspCharacters.LevelGroup D.host →* G0g D.nd) pull_bijective
  let φ : G ≃* LevelCuspCharacters.LevelGroup D.host := eR.trans π.symm
  have hφ : ∀ g, pull (φ g) = eR g := fun g => π.apply_symm_apply (eR g)
  have hreg : ∀ s : ∀ v : LevelCuspCharacters.Sq D.host, LevelCuspCharacters.SSParam (D.host.g v.1) ℂ D.R.r, LevelCuspCharacters.IsGoodParam om s →
      ∀ v, CuspidalProductMultiplicity.IsCuspProdChar (LevelCuspCharacters.typeChar (s v)) := fun s hs v =>
    GlobalTheory.GoodTypeGeneric.isCuspProdChar_typeChar ((hs v.1).1 v.2)
  obtain ⟨θ, hθ, hχθ⟩ := GlobalTheory.GoodTypeGeneric.exists_eq_of_idemOf D.what₂.embLL A.X hR.irr
    (LevelCuspCharacters.goodTypes_finite (H := D.host) om).toFinset (fun θ g => θ (φ g)) (fun θ hθ => by
      obtain ⟨s, hs, rfl⟩ := (Set.Finite.mem_toFinset _).1 hθ
      letI := Fintype.ofFinite (LevelCuspCharacters.Sq D.host)
      refine GlobalTheory.GoodTypeGeneric.isChar_prod (χ := fun v g => LevelCuspCharacters.typeChar (s v) (φ g v)) fun v => ?_
      obtain ⟨n, ρ, hρ⟩ := GlobalTheory.GoodTypeGeneric.isChar_of_isCuspProdChar (hreg s hs v)
      exact ⟨n, ρ.comp ((Pi.evalMonoidHom _ v).comp φ.toMonoidHom), fun g => hρ _⟩) (fun g => by
      rw [h1, ← hφ, hI, Nat.card_congr φ.toEquiv]
      simp only [LevelCuspCharacters.goodIdem, LevelCuspCharacters.centralIdem, MonoidAlgebra.coeff_sum, Finset.sum_apply', map_one, map_inv]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp [Finsupp.single_apply]) hχ
  obtain ⟨s, hs, rfl⟩ := (Set.Finite.mem_toFinset _).1 hθ
  have hchar : ∀ g, τ.character (R.eG g) = LevelCuspCharacters.tupleChar s (φ g) := fun g => (hτχ g).trans (hχθ g)

  have htot : ∀ v : LevelCuspCharacters.Sq D.host, ∑ c : LevelCuspCharacters.Cyc (s v).1, LevelCuspCharacters.cycLen (s v).1 c = D.R.r := fun v => by
    have := Fintype.card_congr (GlobalTheory.GoodTypeGeneric.cycEquiv (s v).1)
    simpa [Fintype.card_sigma] using this
  obtain ⟨w, hw⟩ : ∃ w : LevelCuspCharacters.PlOver D.host 0, ∀ A : Finset (LevelCuspCharacters.Cyc (s ⟨0, w⟩).1),
      ∑ c ∈ A, LevelCuspCharacters.cycLen (s ⟨0, w⟩).1 c ≠ a := by
    have hiv := (hs 0).2.2.2.1
    by_contra hne
    push_neg at hne
    by_cases h2 : 2 * a ≤ D.R.r
    · exact hiv ⟨a, h0, h2, hne⟩
    · refine hiv ⟨D.R.r - a, by omega, by omega, fun v => ?_⟩
      obtain ⟨A', hA'⟩ := hne v
      refine ⟨A'ᶜ, ?_⟩
      have := Finset.sum_add_sum_compl A' (fun c => LevelCuspCharacters.cycLen (s ⟨0, v⟩).1 c)
      rw [htot] at this
      beta_reduce at hA' ⊢
      omega
  obtain ⟨kv, hkv⟩ := (sqEquiv D).surjective ⟨0, w⟩
  rw [← hkv] at hw
  refine ⟨plg kv, ?_⟩
  letI : Field (kP (plg kv).1) := Ideal.Quotient.field _
  haveI : Finite (kP (plg kv).1) := CuspidalProductMultiplicity.finite_kP _
  letI := Fintype.ofFinite (unipRadical (kP (plg kv).1) (blk2 (n := D.R.r) a))
  let ι : GL (Fin D.R.r) (kP (plg kv).1) →* G0 R.Pg D.R.r :=
    MonoidHom.mulSingle (fun PP : ↥R.Pg => GL (Fin D.R.r) (kP PP.1)) (plg kv)
  have hset : {g : G0 R.Pg D.R.r | (∀ PP' : R.Pg, PP' ≠ plg kv → g PP' = 1) ∧
      g (plg kv) ∈ GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical (kP (plg kv).1) D.R.r a} = ι '' GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical _ D.R.r a := by
    ext g
    constructor
    · rintro ⟨hg1, hg2⟩
      refine ⟨g (plg kv), hg2, ?_⟩
      funext PP'
      by_cases h : PP' = plg kv
      · subst h
        exact Pi.mulSingle_eq_same (M := fun PP : ↥R.Pg => GL (Fin D.R.r) (kP PP.1)) _ _
      · rw [hg1 PP' h]
        exact Pi.mulSingle_eq_of_ne (M := fun PP : ↥R.Pg => GL (Fin D.R.r) (kP PP.1)) h _
    · rintro ⟨u, hu, rfl⟩
      refine ⟨fun PP' h => Pi.mulSingle_eq_of_ne (M := fun PP : ↥R.Pg => GL (Fin D.R.r) (kP PP.1)) h _, ?_⟩
      rw [show ι u (plg kv) = u from Pi.mulSingle_eq_same (M := fun PP : ↥R.Pg => GL (Fin D.R.r) (kP PP.1)) _ _]
      exact hu
  rw [hset, GlobalTheory.GoodNoFixed.noFixed_iff_sum τ ι]

  have hbc : ∀ {k k' : Type} [CommRing k] [CommRing k'] (e : k ≃+* k') (y : GL (Fin D.R.r) k),
      Formalism.UG.bc (e.symm : k' →+* k) (Formalism.UG.bc (e : k →+* k') y) = y := by
    intro k k' _ _ e y
    apply Units.ext
    ext i j
    simp [Formalism.UG.bc]
  have hval : ∀ u : GL (Fin D.R.r) (kP (plg kv).1), τ.character (ι u) =
      LevelCuspCharacters.typeChar (s (sqEquiv D kv)) (Formalism.UG.bc ((iso kv).symm : kP (plg kv).1 →+* ZMod (D.host.g kv.1)) u) *
        ∏ PP ∈ Finset.univ.erase (plg kv), LevelCuspCharacters.typeChar (s (sqEquiv D (plg.symm PP))) 1 := by
    intro u
    obtain ⟨g', hg'⟩ := R.eG.surjective (ι u)
    have key : ∀ kv', φ g' (sqEquiv D kv') =
        Formalism.UG.bc ((iso kv').symm : kP (plg kv').1 →+* ZMod (D.host.g kv'.1)) (ι u (plg kv')) := by
      intro kv'
      rw [← hg', h2 g' kv', hbc]
      exact congrFun (hφ g') kv'
    rw [← hg', hchar, LevelCuspCharacters.tupleChar]
    letI := Fintype.ofFinite (LevelCuspCharacters.Sq D.host)
    rw [← Fintype.prod_equiv (plg.symm.trans (sqEquiv D))
      (fun PP => LevelCuspCharacters.typeChar (s (sqEquiv D (plg.symm PP))) (φ g' (sqEquiv D (plg.symm PP)))) _ (fun _ => rfl),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ (plg kv))]
    refine congrArg₂ (· * ·) ?_ (Finset.prod_congr rfl fun PP hPP => ?_)
    · rw [Equiv.symm_apply_apply, key, show ι u (plg kv) = u from Pi.mulSingle_eq_same (M := fun PP : ↥R.Pg => GL (Fin D.R.r) (kP PP.1)) _ _]
    · rw [key (plg.symm PP), show ι u (plg (plg.symm PP)) = 1 from
        Pi.mulSingle_eq_of_ne (M := fun PP : ↥R.Pg => GL (Fin D.R.r) (kP PP.1))
          (by rw [Equiv.apply_symm_apply]; exact Finset.ne_of_mem_erase hPP) _, map_one]
      rfl
  simp only [hval]
  rw [← Finset.sum_mul]
  refine mul_eq_zero_of_left ?_ _
  haveI : NeZero (D.host.g kv.1) := ⟨(Fact.out : (D.host.g kv.1).Prime).ne_zero⟩
  letI := Fintype.ofFinite (unipRadical (ZMod (D.host.g kv.1)) (blk2 (n := D.R.r) a))
  let E : unipRadical (ZMod (D.host.g kv.1)) (blk2 (n := D.R.r) a) ≃ unipRadical (kP (plg kv).1) (blk2 (n := D.R.r) a) :=
    { toFun := fun u => ⟨Formalism.UG.bc ((iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1)) u,
        GlobalTheory.GoodNoFixed.mem_radical_iff.1 (GlobalTheory.GoodNoFixed.map_mem_radical _ (GlobalTheory.GoodNoFixed.mem_radical_iff.2 u.2))⟩
      invFun := fun u => ⟨Formalism.UG.bc (((iso kv).symm : kP (plg kv).1 →+* ZMod (D.host.g kv.1))) u,
        GlobalTheory.GoodNoFixed.mem_radical_iff.1 (GlobalTheory.GoodNoFixed.map_mem_radical _ (GlobalTheory.GoodNoFixed.mem_radical_iff.2 u.2))⟩
      left_inv := fun u => Subtype.ext (hbc (iso kv) u)
      right_inv := fun u => Subtype.ext (by simpa using hbc (iso kv).symm u) }
  have hreg0 : LevelCuspCharacters.IsRegularParam (s (sqEquiv D kv)) := (hs (sqEquiv D kv).1).1 (sqEquiv D kv).2
  have hB := sum_typeChar_radical (p := D.host.g kv.1) (r := D.R.r) (s (sqEquiv D kv)) hreg0 h0 ha hw
  have hS : ∑ u : unipRadical (kP (plg kv).1) (blk2 (n := D.R.r) a), LevelCuspCharacters.typeChar (s (sqEquiv D kv))
      (Formalism.UG.bc ((iso kv).symm : kP (plg kv).1 →+* ZMod (D.host.g kv.1)) (u : GL (Fin D.R.r) (kP (plg kv).1))) =
      ∑ u : unipRadical (ZMod (D.host.g kv.1)) (blk2 (n := D.R.r) a),
        LevelCuspCharacters.typeChar (s (sqEquiv D kv)) (u : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
    refine (Fintype.sum_equiv E _ _ fun u => ?_).symm
    exact congrArg _ (hbc (iso kv) (u : GL (Fin D.R.r) (ZMod (D.host.g kv.1)))).symm
  exact hS.trans hB

end GlobalTheory.GoodProjHypH
