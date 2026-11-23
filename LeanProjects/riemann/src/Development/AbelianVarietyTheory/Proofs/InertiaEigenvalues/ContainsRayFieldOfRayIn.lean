import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliarySquarefreeLevelTwistPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesRay
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSelfDualLatticeIffIntegralFrameMatricesHalf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCoverFormsMulComponentFunctionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaWeilTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameHeckeCharTrivialOnFiniteUnitsCongOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryAdelicCharOfHeckeChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterQuotientValuesInEmbeddingField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRayFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexLinearExtensionCoefficientMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvPlaceNormProductMemCoefficientRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceInUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceOfValuationRing

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT
  Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.SeriesTie
  GlobalTheory.SeriesTie.UnivRat
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.XiIntSteps

theorem mem_of_pow_eq_one {Λ : Subring ℂ} {z : ℂ} {m : ℕ} (hm : 0 < m) (h : z ^ m = 1) (hz : z ∈ Λ ∨ z⁻¹ ∈ Λ) : z ∈ Λ := by
  rcases hz with h1 | h1
  · exact h1
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hk : z ^ k = z⁻¹ := by
      rw [pow_succ] at h; exact eq_inv_of_mul_eq_one_left h
    have : z = (z⁻¹) ^ k := by rw [inv_pow, hk, inv_inv]
    rw [this]; exact Λ.pow_mem h1 k

theorem comap_eq_of_le_one_iff {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L)
    (p : HeightOneSpectrum (𝓞 K)) (la : HeightOneSpectrum (𝓞 L))
    (h : ∀ x : K, la.valuation L (φ x) ≤ 1 ↔ p.valuation K x ≤ 1) :
    la.asIdeal.comap (RingOfIntegers.mapRingHom φ) = p.asIdeal := by
  ext x
  rw [Ideal.mem_comap, ← la.valuation_lt_one_iff_mem (K := L), ← p.valuation_lt_one_iff_mem (K := K)]
  change la.valuation L (φ (algebraMap _ K x)) < 1 ↔ p.valuation K (algebraMap _ K x) < 1
  generalize algebraMap _ K x = y
  by_cases hy : y = 0
  · simp [hy]
  have h1 : la.valuation L (φ y) ≠ 0 := by simpa using hy
  have h2 : p.valuation K y ≠ 0 := by simpa using hy
  have := h y⁻¹
  rw [map_inv₀, map_inv₀, map_inv₀, inv_le_one₀ (zero_lt_iff.2 h1), inv_le_one₀ (zero_lt_iff.2 h2)] at this
  rw [← not_le, ← not_le, this]

variable {D : D7}

theorem containsRayField_of_rayIn {N : ℕ} {L : Type} [Field L] [NumberField L] (σ : L →+* ℂ) (h : RayIn D N σ.fieldRange) :
    ∃ φ : D.host.K →+* L, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ N := by
  obtain ⟨H, _, _, _, i4, ⟨hun, -, hart⟩, jj, -, hv⟩ := h
  haveI : IsGalois D.host.K H := i4.toIsGalois
  have hc : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (algebraMap D.host.K H) N :=
    GlobalTheory.FieldSize.RayNorm.containsRayField_of_ray (K := D.host.K) (L := H) N hun (fun I hI hc hχ => (hart I hI hc).1 hχ)
  let τ : H →+* L := (σ.rangeRestrictFieldEquiv.symm : σ.fieldRange →+* L).comp (jj.codRestrict σ.fieldRange hv)
  exact ⟨τ.comp (algebraMap D.host.K H), GlobalTheory.RayUp.containsRayField_up _ τ N hc⟩

section Datum

variable {S T : HSp D}

open Classical in

theorem isLevelFn_datumFn {B : Base S T} (hB : B.Good) {Q : Finset (Pl D.host.E)} (hQ : B.admitted Q)
    (hbad : ∀ PP, PP ∈ B.G.Pg ∨ PP ∈ B.de.Q ∪ Q →
      ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (N : ℕ) (hN : ∀ PP, PP ∈ B.G.Pg ∨ PP ∈ B.de.Q ∪ Q → (N : 𝓞 D.host.E) ∈ PP.asIdeal) (k : Subring ℂ)
    (h1 : ∀ u, ((B.G.P.chi u : ℂˣ) : ℂ) ∈ k) (h2 : ∀ PP ∈ B.G.Pg, ∀ x, ((B.G.muC PP x : ℂˣ) : ℂ) ∈ k)
    (h3 : ∀ PP ∈ B.de.Q, ∀ x, ((B.de.resC PP x : ℂˣ) : ℂ) ∈ k)
    (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) (h4 : ∀ PP y, φ PP y ∈ k) :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsLevelFn (halfIdem B.G.Pg (B.de.Q ∪ Q)) (latO S T B.F.ΛS B.F.ΛT fun _ => True) N
      (B.F.datumFn B.G (B.de.Q ∪ Q) (B.locFn Q φ)) ∧ ∀ t, B.F.datumFn B.G (B.de.Q ∪ Q) (B.locFn Q φ) t ∈ k := by
  have hlat := fun x => @GlobalTheory.ExportSeries.LatHalf.mem_lat_iff_isIntM_halfIdem D S T B.F hB.frame _ _ hQ.1 hbad x
  refine ⟨⟨fun t ht => ?_, fun u hu hue t => ?_⟩, fun t => ?_⟩
  · unfold Frame.datumFn at ht
    have c1 := left_ne_zero_of_mul ht
    have c2 := right_ne_zero_of_mul ht
    have d1 := (ite_ne_right_iff.1 c1).1
    have d2 := (ite_ne_right_iff.1 c2).1
    exact ⟨(hlat t d1.1).2 ⟨d1.2, d2.2⟩, d1.1⟩
  · obtain ⟨i1, i2⟩ := (hlat u hue).1 hu
    have e1 : frMapAdj S T B.F.βS B.F.βT (t + N • u) = frMapAdj S T B.F.βS B.F.βT t + N • frMapAdj S T B.F.βS B.F.βT u := by
      rw [GlobalTheory.RefDatumLev.frMapAdj_add', GlobalTheory.RefDatumLev.frMapAdj_nsmul']
    have hKu : IsHalf (halfIdem B.G.Pg (B.de.Q ∪ Q)) (N • u) := fun a b => by
      rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hue a b]
    have hh : IsHalf (halfIdem B.G.Pg (B.de.Q ∪ Q)) (t + N • u) ↔ IsHalf (halfIdem B.G.Pg (B.de.Q ∪ Q)) t := by
      constructor
      · intro h a b
        have := h a b
        rw [Matrix.add_apply, mul_add, hKu a b] at this
        exact add_right_cancel this
      · intro h a b
        rw [Matrix.add_apply, mul_add, h a b, hKu a b]
    unfold Frame.datumFn
    rw [e1, frMapO_add_nsmul]
    simp only [hh, GlobalTheory.RefDatumLev.isIntM_add_nsmul_iff i1, GlobalTheory.RefDatumLev.isIntM_add_nsmul_iff i2]
    congr 1
    · refine ite_congr rfl (fun hc => ?_) fun _ => rfl
      exact GlobalTheory.PlaceDatum.omegaG_congr _ _ _ _ fun PP hPP =>
        GlobalTheory.RefDatumLev.redM_add_nsmul PP hc.2 i1 _ (hN PP (Or.inl hPP))
    · refine ite_congr rfl (fun hc => ?_) fun _ => rfl
      unfold Base.locFn
      congr 1
      · exact Finset.prod_congr rfl fun PP hPP => by
          beta_reduce
          rw [GlobalTheory.RefDatumLev.redM_add_nsmul PP hc.2 i2 _ (hN PP (Or.inr (Finset.mem_union_left _ hPP)))]
      · exact Finset.prod_congr rfl fun PP _ => by
          beta_reduce
          rw [GlobalTheory.RefDatumLev.redM_add_nsmul PP.1 hc.2 i2 _ (hN PP.1 (Or.inr (Finset.mem_union_right _ PP.2)))]
  · unfold Frame.datumFn
    refine mul_mem ?_ ?_
    · split_ifs
      · unfold omegaG
        split_ifs
        · refine mul_mem (mul_mem (h1 _) (prod_mem fun PP _ => prod_mem fun c hc => absurd hc (Finset.notMem_empty _))) ?_
          refine prod_mem fun PP _ => ?_
          rw [← Units.val_inv_eq_inv_val, ← map_inv]
          exact h2 PP.1 PP.2 _
        · exact zero_mem _
      · exact zero_mem _
    · split_ifs
      · unfold Base.locFn
        refine mul_mem (prod_mem fun PP hPP => ?_) (prod_mem fun PP _ => h4 PP _)
        unfold GlobalTheory.ExportSeries.flat
        split_ifs
        · exact h3 PP hPP _
        · exact zero_mem _
      · exact zero_mem _

end Datum

section Twist

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem theta_twist (hL : R.toLevCh.Is A.μ0) (hP : R.IsThP) (i : Fin D.R.m) {L : Type} [Field L] [NumberField L] (σ : L →+* ℂ)
    {pd : ℕ} (hodd : Odd pd) {δ : Formalism.L2.Host.HChar D.host.E} {δc : (AE D)ˣ →* Circle} (htw : IsTwist pd σ δ δc)
    {om : PairRep (Vc D i) (Wc D i)}
    (hom : IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (Lift.tup R.mu0 δc) R.eta ((i : ℕ) + 1)).1
      (Lift.chrTh (Lift.tup R.mu0 δc) R.eta ((i : ℕ) + 1)).2 om) (s : GA D (Vc D i)) :
    ∃ c ∈ σ.fieldRange, (∃ m : ℕ, 0 < m ∧ c ^ m = 1) ∧ ∃ xi : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTwist σ pd xi ∧
      ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ g : GA D (Wc D i), thetaKO om s g f =
        c * (((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) : ℂˣ) : ℂ) * thetaKO (R.ωP i A.μ0) s g f) := by
  obtain ⟨hE, ⟨n, hn, ho⟩, hTriv, htame, hunr, hval⟩ := id htw
  have hxi : R.xi A.μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0))
  have hmu : R.toLevCh.mu A.μ0 = Lift.tup R.mu0 (1 : (AE D)ˣ →* Circle) := by
    unfold LevCh.mu
    rw [hxi]
  have hω : IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh R.mu0 R.eta ((i : ℕ) + 1)).1
      (Lift.chrTh R.mu0 R.eta ((i : ℕ) + 1)).2 (R.ωP i A.μ0) := by
    have h := hP.ωP i A.μ0
    rw [hmu, GlobalTheory.SplitChange.chrTh_tup] at h
    simpa only [mul_one] using h
  rw [GlobalTheory.SplitChange.chrTh_tup] at hom
  have hδH : IsHeckeChar D δc := hE.1
  have hδF : ∀ a, δc (idF D a) = 1 := GlobalTheory.GridWeil.triv_base hE hTriv
  have hpow : ∀ x, δc x ^ n = 1 :=
    GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (δc ^ n) ⟨hE.1.1.pow n, fun x => by
      rw [MonoidHom.pow_apply, hE.1.2, one_pow]⟩ (GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D δc δ hE n ho)
  obtain ⟨nV, hnV, -⟩ := GlobalTheory.Member.exists_muVal D (Vc D i) δc hδH hδF
  obtain ⟨nW, hnW, -⟩ := GlobalTheory.Member.exists_muVal D (Wc D i) δc hδH hδF
  obtain ⟨xi, hxiT, hxiV⟩ := GlobalTheory.AntiCycRead.read_anticyc D (Wc D i) _ σ pd hodd δc hδH hδF
    ⟨n, hn, hpow⟩ (GlobalTheory.tame_heckeChar_eq_one_of_finUnit D δc δ hE htame pd hunr)
    (fun x => GlobalTheory.WeilTwistSeries.twist_val_mem htw x)
  obtain ⟨x, hx⟩ := hnV.1 s
  refine ⟨(nV s)⁻¹, ?_, ⟨n, hn, ?_⟩, xi, hxiT, fun f hf g => ?_⟩
  · rw [hnV.2 s x hx]
    exact inv_mem (GlobalTheory.WeilTwistSeries.twist_val_mem htw x)
  · rw [hnV.2 s x hx, inv_pow, ← Circle.coe_pow, hpow x, Circle.coe_one, inv_one]
  · obtain ⟨y, hy⟩ := hnW.1 g
    rw [GlobalTheory.SplitChange.thetaKO_twist hω hδH hδF hom hnV hnW s g hf, hxiV g y hy, ← hnW.2 g y hy]
    ring

end Twist

section Cover

variable {T : CoreJ D} {j : Fin D.R.m} {C : Cover T ((j : ℕ) + 1) T.σ₀}

open Classical in

theorem intForms_fibre (hRF : GlobalTheory.NT.RayField) (hT : LawsJ T) (hU : C.IsUnif)
    (hray : RayIn D (T.Q.l.M * C.d.pd) C.σ₂.fieldRange) {A : Type} [AddCommGroup A] {u : UnivTwist D A}
    {Q : Finset (Pl D.host.E)} (hu : u.Good Q) (hQ : ∀ PP ∈ Q, ((T.Q.l.M * C.d.pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (a : ↥Q → A) (w : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)))
    {ψ : GA D (T.V ((j : ℕ) + 1) T.σ₀) → ℂ} (h : ψ ∈ C.intForms w n S) :
    (fun g => (if Multiplicative.toAdd (detChar _ (u.delQ Q) g) = a then 1 else 0) * ψ g) ∈ C.intForms w n S := by
  have hM : C.d.l₂.M = T.Q.l.M * C.d.pd := hU.1.2.1
  have h3 : 3 ≤ C.d.l₂.M := C.d.l₂.three_le
  rw [← hM] at hray hQ
  obtain ⟨l1, l2, l3⟩ := delQ_det_laws hu (T.V ((j : ℕ) + 1) T.σ₀) C.d.l₂.odd hQ
  have key := (GlobalTheory.T.levelCover_forms_mul_componentFunction D T hT _ (inR j) T.σ₀ T.toCore.good_σ₀ C hU C.d.l₂.M (by omega) dvd_rfl
    (Or.inr (GlobalTheory.TwistRat.Field.curveOver_of_rayIn hRF D T.Q hT.pins.1 _ h3 _ C.σ₂ hray))
    (fun g => if Multiplicative.toAdd (detChar _ (u.delQ Q) g) = a then 1 else 0)
    (fun g g' e => by rw [l1 g g' e]) (fun γ hγ g => by rw [l2 γ hγ g]) (fun k _ hk g => by rw [l3 k hk g])
    w n).2 S (fun la _ g => by split_ifs <;> simp) ψ h
  convert key using 1
  funext g
  split_ifs <;> simp

end Cover

section Main

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
  {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {ρ : Setup D.ntw} (hρ : ρ.Good)
  (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

theorem coprime_pDel (l : ℕ) (hl : l.Prime) : Nat.Coprime (pDel D l) l := by
  unfold pDel
  split_ifs with h
  · exact (Nat.coprime_primes D.host.pde'_prime hl).2 fun e => D.host.pde_ne (h.symm.trans e.symm)
  · exact (Nat.coprime_primes D.host.pde_prime hl).2 fun e => h e.symm

include YS hρ in

theorem exists_cover_coprime (hRF : GlobalTheory.NT.RayField) (hT : LawsJ T) (halg : AlgTie T) (hgal : IsGalois ℚ D.LL0)
    (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hray : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (hde : D.host.cls D.host.pde = .splitK ∧ D.host.cls D.host.pde' = .splitK) (hU : ρ.LevelOf D.nexp)
    (Q : Finset (Pl D.host.E)) (hcls : Formalism.MainNotions.IntegralHeckeForms.ClsQ (D := D) Q) (hS : Disjoint Q (D.ntw.S0 i)) (n : ℕ) :
    ∃ C : Cover T ((j : ℕ) + 1) T.σ₀, GoodCover T Rl.toRealDat j C n ∧ Nat.Coprime C.d.pd (D.ntw.l i) ∧
      (embLL0 D).fieldRange ≤ C.σ₂.fieldRange ∧
      C.σ₂.fieldRange ≤ (ρ.e i b).fieldRange ∧ pDel D (D.ntw.l i) ∣ C.d.pd ∧
      (∀ P ∈ Q, ((C.d.pd : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) ∧
      (∀ g, (((ρ.B i j b).G.P.chi g : ℂˣ) : ℂ) ∈ C.σ₂.fieldRange) ∧
      ∀ PP ∈ (ρ.B i j b).de.Q, ∀ x, (((ρ.B i j b).de.resC PP x : ℂˣ) : ℂ) ∈ C.σ₂.fieldRange := by
  have hB := hρ.base i j b
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := hT.toLawsM.pins.2.1.1
  obtain ⟨N, hN0, hNl, haux, hNQ⟩ := exists_auxiliary_squarefree_level_twistPlaces hρ hde i Q hcls hS
  obtain ⟨L₀, i1, i2, h1, h2, h3, h4⟩ := GlobalTheory.RayInFrac.exists_field D ρ hρ i b hRF hray
    (D.host.g 0 * D.host.g 1 * pDel D (D.ntw.l i)) N (dvd_mul_right _ _) (by
      rcases pDel_cases (D := D) (D.ntw.l i) with e | e <;> rw [e]
      · exact dvd_mul_right _ _
      · rw [mul_right_comm _ D.host.pde]; exact dvd_mul_right _ _) hN0 hNl
  haveI : Normal ℚ L₀ := (i2 hgal).to_normal
  haveI : ∀ PP : Pl D.host.E, Finite (kP PP) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  have hord : ∀ {H : Type} [Group H] [Finite H] (f : H →* ℂˣ) (x : H), IsOfFinOrder ((f x : ℂˣ) : ℂ) := fun f x =>
    MonoidHom.isOfFinOrder ((Units.coeHom ℂ).comp f) (isOfFinOrder_of_finite x)
  obtain ⟨L, i3, i4, h5, h6, h7⟩ := exists_field_adjoin_roots (ρ.e i b).fieldRange
    (Z := Set.range (fun g => (((ρ.B i j b).G.P.chi g : ℂˣ) : ℂ)) ∪
      ⋃ PP ∈ (ρ.B i j b).de.Q, Set.range fun x => (((ρ.B i j b).de.resC PP x : ℂˣ) : ℂ))
    ((Set.finite_range _).union ((ρ.B i j b).de.Q.finite_toSet.biUnion fun _ _ => Set.finite_range _)) (by
      rintro z (⟨g, rfl⟩ | hz)
      · exact ⟨type_mem_range i j b hU g, hord _ _⟩
      · obtain ⟨PP, hPP, x, rfl⟩ := Set.mem_iUnion₂.1 hz
        refine ⟨?_, hord _ _⟩
        obtain ⟨y, hy⟩ := GlobalTheory.ConjTwist.exists_isLocUnit (hB.de.split.isIdemAt hPP) x
        obtain ⟨hx, hr⟩ := hy.res
        obtain ⟨a, ha⟩ := GlobalTheory.DeltaRange.delta_value_mem_range hρ i j b y
        rw [hB.de.res PP hPP y hy.off hx x hr] at ha
        exact ⟨a, ha⟩) L₀ h2
  have h8 : (embLL0 D).fieldRange ≤ L.toSubfield := fun z hz => h5 (h1 hz)
  rw [← hMg] at haux
  obtain ⟨I, hK, hprod, hsup⟩ := GlobalTheory.HalfCharacter.exists_half_of_auxiliary_split_level D T hT _ haux
  have hMN : T.Q.l.M * (pDel D (D.ntw.l i) * N) = D.host.g 0 * D.host.g 1 * pDel D (D.ntw.l i) * N := by
    rw [hMg, mul_assoc (D.host.g 0 * D.host.g 1)]
  have hne : T.Q.l.M * (pDel D (D.ntw.l i) * N) ≠ 0 :=
    mul_ne_zero (by have := T.Q.l.three_le; omega) fun h0 => Nat.not_odd_zero (h0 ▸ haux.1)
  obtain ⟨C, hpd, -, hfr, hG⟩ := GlobalTheory.CoverGalois.exists_goodCover_galois D T Rl.toRealDat hT j (inR j) n _ I haux hK hprod hsup L
    (fun z hz => h8 (GlobalTheory.CoverSmall.core_le_small T Rl cG S YS hT halg j hz))
    (h5 (h4 _ (by rw [← hMN]; exact (Complex.isPrimitiveRoot_exp _ hne).pow_eq_one)))
    ⟨fun v hv => by
        obtain ⟨y, hy⟩ := hval.mu0 j v hv
        exact ⟨⟨embLL0 D y, h8 ⟨y, rfl⟩⟩, hy⟩,
      fun v hv => by
        obtain ⟨y, hy⟩ := hval.eta v hv
        exact ⟨⟨embLL0 D y, h8 ⟨y, rfl⟩⟩, hy⟩⟩
    (by
      obtain ⟨H, j1, j2, j3, j4, hH, jj, hjj, hv⟩ := h3
      rw [hMN]
      exact ⟨H, j1, j2, j3, j4, hH, jj, hjj, fun x => h5 (hv x)⟩)
  refine ⟨C, hG, ?_, hfr ▸ h8, hfr ▸ h6, hpd ▸ dvd_mul_right _ _, fun P hP => ?_, fun g => ?_, fun PP hPP x => ?_⟩
  · rw [hpd]
    exact Nat.Coprime.mul_left (coprime_pDel _ (D.ntw.lPrime i).out) hNl
  · rw [hpd]
    exact GlobalTheory.HalfCompare.mem_of_dvd (hNQ P hP) (dvd_mul_left _ _)
  · rw [hfr]
    exact h7 _ (Or.inl ⟨g, rfl⟩)
  · rw [hfr]
    exact h7 _ (Or.inr (Set.mem_iUnion₂.2 ⟨PP, hPP, x, rfl⟩))

end Main

end GlobalTheory.XiIntSteps
