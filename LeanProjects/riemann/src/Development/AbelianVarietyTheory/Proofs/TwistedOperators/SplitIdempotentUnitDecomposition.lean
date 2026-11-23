import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyEqTensorPowerVacuum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplittingHeckeCharExistsArchimedeanExponent
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIndexUnitIdlSup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceProjectionEqOfPrimeComponentEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdeleEquivFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCoprimeMulIsIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section
namespace GlobalTheory.SplitCharValue

theorem values_of_rel (D : D7) (z : ℂ) (K : ℕ) (b : D.host.Eˣ) (m : D.what₂.Tau → ℤ) (hK : 0 < K)
    (h : z ^ K * ∏ τ, (tauE D τ (b : D.host.E) / (‖tauE D τ (b : D.host.E)‖ : ℂ)) ^ m τ = 1) :
    Mod1All z ∧ ∀ (q : ℕ) [Fact q.Prime], (∀ P : HeightOneSpectrum (𝓞 D.host.E), ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      P.valuation D.host.E (b : D.host.E) = 1) → GlobalTheory.MovedKappaEx.UnitAt q z := by
  have : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨hz, H⟩ := GlobalTheory.HeckeVal.root_value (tauE D) m b z K hK h
  refine ⟨⟨hz, fun σ => H ℂ σ fun τ => ?_⟩, fun q hq hb lam => ?_⟩
  · have := IsCMField.complexEmbedding_complexConj D.host.E (σ.comp τ) (b : D.host.E)
    simp only [RingHom.comp_apply] at this
    rw [this, Complex.norm_conj]
  · obtain ⟨M, hM, i1⟩ := GlobalTheory.KerTie.MuqUnit.exists_coprime_mul_isIntegral hq.out (b : D.host.E)
      fun P hP => (hb P hP).le
    obtain ⟨M', hM', i2⟩ := GlobalTheory.KerTie.MuqUnit.exists_coprime_mul_isIntegral hq.out (b : D.host.E)⁻¹
      fun P hP => by rw [map_inv₀, hb P hP, inv_one]
    have key : ∀ ψ : D.host.E →+* ℂ_[q], ‖ψ (b : D.host.E)‖ = 1 := fun ψ => by
      have j1 := GlobalTheory.HeckeVal.norm_le_one_of_denom ψ hM i1
      have j2 := GlobalTheory.HeckeVal.norm_le_one_of_denom ψ hM' i2
      rw [map_inv₀, norm_inv] at j2
      have h0 : 0 < ‖ψ b‖ := norm_pos_iff.2 ((map_ne_zero _).2 b.ne_zero)
      exact le_antisymm j1 ((inv_le_one₀ h0).1 j2)
    rw [Formalism.MainNotions.TaylorLogMetric.lamC, dif_pos hz]
    refine H _ lam fun τ => ?_
    exact (key (lam.comp τ)).trans
      (key ((lam.comp τ).comp (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E))).symm

theorem inf_val (D : D7) (c : (Formalism.L2.Theta.AE D)ˣ →* Circle) (n : ℕ) (hc : Formalism.L2.Theta.IsHeckeChar D c)
    (hr : Formalism.L2.Theta.ResEta D c n) : ∃ m : D.what₂.Tau → ℤ, ∀ (k : D.host.Eˣ) (x : (Formalism.L2.Theta.AE D)ˣ),
      Formalism.L2.Theta.finPart D (x : Formalism.L2.Theta.AE D) = 1 →
      Formalism.L2.Theta.infPart D (x : Formalism.L2.Theta.AE D) = Formalism.L2.Theta.infPart D (Formalism.L2.Theta.incA D (k : D.host.E)) →
      ((c x : Circle) : ℂ) = ∏ τ, (tauE D τ (k : D.host.E) / (‖tauE D τ (k : D.host.E)‖ : ℂ)) ^ m τ := by
  classical
  obtain ⟨θ, hθ⟩ : ∃ θ : InfFam D, IsInfFam θ := GlobalTheory.DualPairCompare.exists_infFam D
  have H : ∀ τ, ∃ m : ℤ, ∀ x : (Formalism.L2.Theta.AE D)ˣ, Formalism.L2.Theta.finPart D (x : Formalism.L2.Theta.AE D) = 1 →
      (∀ τ', τ' ≠ τ → θ τ' (Formalism.L2.Theta.infPart D (x : Formalism.L2.Theta.AE D)) = 1) →
        ((c x : Circle) : ℂ) = (θ τ (Formalism.L2.Theta.infPart D (x : Formalism.L2.Theta.AE D)) / (‖θ τ (Formalism.L2.Theta.infPart D (x : Formalism.L2.Theta.AE D))‖ : ℂ)) ^ m := fun τ => by
    obtain ⟨a, m, -, -, h⟩ := GlobalTheory.SplitCharExp.exists_hasInfExp D θ c n τ hθ hc hr
    exact ⟨m, h θ hθ⟩
  choose m hm using H
  refine ⟨m, fun k x hx1 hx2 => ?_⟩
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, -, e1, e2⟩ := GlobalTheory.SplitCharExp.exists_real_hom h
  let z : D.what₂.Tau → ℂˣ := fun τ => Units.map (tauE D τ).toMonoidHom k
  let f : ∀ _ : D.what₂.Tau, ℂ →* Formalism.L2.Theta.AE D := fun τ => e.comp (MonoidHom.mulSingle (fun _ : D.what₂.Tau => ℂ) τ)
  have hθk : ∀ τ, θ τ (Formalism.L2.Theta.infPart D (Formalism.L2.Theta.incA D (k : D.host.E))) = tauE D τ k := fun τ => (hθ τ).1 k
  have ex : x = ∏ τ, Units.map (f τ) (z τ) := by
    apply Units.ext
    rw [Units.coe_prod]
    have e3 : (∏ τ, ((Units.map (f τ) (z τ) : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D)) = e (fun τ => tauE D τ k) := by
      change ∏ τ, e (Pi.mulSingle τ (tauE D τ k)) = _
      rw [← map_prod, Finset.univ_prod_mulSingle]
    rw [e3]
    exact GlobalTheory.SplitCharExp.ext_of_chart h (hx1.trans (e1 _).symm) fun τ => by rw [hx2, hθk, e2]
  rw [ex, map_prod]
  refine (map_prod Circle.coeHom _ _).trans (Finset.prod_congr rfl fun τ _ => ?_)
  have f2 : ∀ τ', θ τ' (Formalism.L2.Theta.infPart D ((Units.map (f τ) (z τ) : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D)) =
      (Pi.mulSingle τ (tauE D τ k) : D.what₂.Tau → ℂ) τ' := fun τ' => e2 _ τ'
  have := hm τ (Units.map (f τ) (z τ)) (e1 _) fun τ' ht => by rw [f2, Pi.mulSingle_eq_of_ne ht]
  rw [f2, Pi.mulSingle_eq_same] at this
  exact this

def finIso (D : D7) : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv.trans (GlobalTheory.Mem.Col2.afIso D.host.F D.host.E)

theorem finIso_one_tmul (D : D7) (x : D.host.E) : finIso D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
    algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x := GlobalTheory.Mem.Col2.afIso_tmul_one _ _ x

theorem mem_intAE_iff (D : D7) (y : Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (finIso D y P) ≤ 1 :=
  (GlobalTheory.HostAdeleIso.mem_intAE_iff_comm D y).trans (GlobalTheory.Mem.Col2.mem_rInt_iff _ _ _)

set_option maxHeartbeats 800000 in

theorem exists_pow_rel (D : D7) (x : (Formalism.L2.Theta.AE D)ˣ) (hx : Formalism.L2.Theta.infPart D (x : Formalism.L2.Theta.AE D) = 1) :
    ∃ (h : ℕ) (k : D.host.Eˣ) (y w : (Formalism.L2.Theta.AE D)ˣ), 0 < h ∧ Formalism.L2.Pj.FinUnit w ∧ Formalism.L2.Theta.finPart D (y : Formalism.L2.Theta.AE D) = 1 ∧
      Formalism.L2.Theta.infPart D (y : Formalism.L2.Theta.AE D) = Formalism.L2.Theta.infPart D (Formalism.L2.Theta.incA D (k : D.host.E)) ∧
      x ^ h * y = w * Units.map (Formalism.L2.Theta.incA D).toMonoidHom k ∧
      ∀ P : HeightOneSpectrum (𝓞 D.host.E), finIso D (Formalism.L2.Theta.finPart D (x : Formalism.L2.Theta.AE D)) P = 1 →
        P.valuation D.host.E (k : D.host.E) = 1 := by
  obtain ⟨Φ, -, -, h1, -, h3⟩ := GlobalTheory.DetRootRead.exists_adele_equiv_fin D (finIso D) (finIso_one_tmul D) (mem_intAE_iff D)
  obtain ⟨s, hs, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hs1 : ∀ z : Formalism.L2.Theta.AE D, (s z).1 = Formalism.L2.Theta.infPart D z := fun z => (hs z).1
  have hs2 : ∀ z : Formalism.L2.Theta.AE D, (s z).2 = Formalism.L2.Theta.finPart D z := fun z => (hs z).2
  have hfi := GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup D.host.E
  obtain ⟨u, hu, _, ⟨k, rfl⟩, e⟩ := Subgroup.mem_sup.1 ((GlobalTheory.Mem.Chr.unitIdl D.host.E ⊔
    (Neutral.B1.diagUnits D.host.E).range).pow_index_mem (Units.map Φ.toRingHom.toMonoidHom x))
  generalize hh : (GlobalTheory.Mem.Chr.unitIdl D.host.E ⊔ (Neutral.B1.diagUnits D.host.E).range).index = h at e
  have h0 : 0 < h := hh ▸ Nat.pos_of_ne_zero hfi.index_ne_zero
  let Ψ : (AdeleRing (𝓞 D.host.E) D.host.E)ˣ →* (Formalism.L2.Theta.AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hΨ : ∀ a, Φ ((Ψ a : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) = a := fun a => Φ.apply_symm_apply _
  let K : (Formalism.L2.Theta.AE D)ˣ := Units.map (Formalism.L2.Theta.incA D).toMonoidHom k
  have e' : Ψ u * K = x ^ h := by
    have a1 : Ψ (Neutral.B1.diagUnits D.host.E k) = K := Units.ext (Φ.symm_apply_eq.2 (h1 k).symm)
    have a2 : Ψ (Units.map Φ.toRingHom.toMonoidHom x) = x := Units.ext (Φ.symm_apply_apply _)
    rw [← a1, ← map_mul, e, map_pow, a2]
  let g : Formalism.L2.Theta.AE D →* Formalism.L2.Theta.AE D := s.symm.toRingHom.toMonoidHom.comp
    ((MonoidHom.inl _ (Af D.host.F ⊗[D.host.F] D.host.E)).comp (Formalism.L2.Theta.infPart D).toMonoidHom)
  have g1 : ∀ a, Formalism.L2.Theta.infPart D (g a) = Formalism.L2.Theta.infPart D a := fun a =>
    (hs1 _).symm.trans (congrArg Prod.fst (s.apply_symm_apply (Formalism.L2.Theta.infPart D a, 1)))
  have g2 : ∀ a, Formalism.L2.Theta.finPart D (g a) = 1 := fun a =>
    (hs2 _).symm.trans (congrArg Prod.snd (s.apply_symm_apply (Formalism.L2.Theta.infPart D a, 1)))
  have hint : ∀ a ∈ GlobalTheory.Mem.Chr.unitIdl D.host.E, ∀ b : (Formalism.L2.Theta.AE D)ˣ,
      Formalism.L2.Theta.finPart D ((Ψ a * Units.map g b : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) ∈ intAE D := fun a ha b => by
    have : Formalism.L2.Theta.finPart D ((Units.map g b : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) = 1 := g2 _
    rw [Units.val_mul, RingHom.map_mul, this, mul_one, mem_intAE_iff, ← (h3 _).2, hΨ]
    exact fun P => (ha P).le
  refine ⟨h, k, Units.map g K, Ψ u * Units.map g K, h0, ⟨?_, hint u hu K, ?_⟩, g2 _, g1 _, ?_, fun P hP => ?_⟩
  · have a1 : Formalism.L2.Theta.infPart D ((Units.map g K : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) = Formalism.L2.Theta.infPart D (K : Formalism.L2.Theta.AE D) := g1 _
    rw [Units.val_mul, RingHom.map_mul, a1, ← RingHom.map_mul, ← Units.val_mul, e', Units.val_pow_eq_pow_val,
      RingHom.map_pow, hx, one_pow]
  · rw [mul_inv, ← Ψ.map_inv u, ← (Units.map g).map_inv K]
    exact hint u⁻¹ ((GlobalTheory.Mem.Chr.unitIdl D.host.E).inv_mem hu) K⁻¹
  · rw [← e', mul_right_comm]
  · have a1 : (u : AdeleRing (𝓞 D.host.E) D.host.E).2 P * algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E) =
        ((Φ (x : Formalism.L2.Theta.AE D)).2 P) ^ h :=
      congrArg (fun a : (AdeleRing (𝓞 D.host.E) D.host.E)ˣ => (a : AdeleRing (𝓞 D.host.E) D.host.E).2 P) e
    rw [(h3 _).2, hP, one_pow] at a1
    have a2 := congrArg (Valued.v : Valuation (P.adicCompletion D.host.E) _) a1
    rw [map_mul, hu P, one_mul, map_one] at a2
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P (k : D.host.E)).symm.trans a2

theorem finIso_idem (D : D7) {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {q : ℕ} (hq : GlobalTheory.MovedKappaEx.OffPrime e q)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) : finIso D (Formalism.L2.Theta.finPart D e) P = 0 := by
  obtain ⟨h1, h2, v, ε, hε, h4⟩ := he
  have hv := hq v ε hε h4
  obtain ⟨α, rfl, -, hα⟩ := hε
  have hne : P.under (𝓞 D.host.F) ≠ v := by
    rintro rfl
    apply hv
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (q : 𝓞 D.host.F) ∈ P.asIdeal
    rwa [map_natCast]
  have h5 : finIso D (Formalism.L2.Theta.finPart D (e + cA D e)) P = 0 := by
    rw [h4]
    refine (GlobalTheory.SplitProj.afIso_one_tmul_apply α P).trans ?_
    have : α (P.under (𝓞 D.host.F)) = 0 := hα _ hne
    rw [GlobalTheory.AdeleBaseChange.adMap_apply, this, map_zero]
  have h6 : e = e * (e + cA D e) := by rw [mul_add, h1, h2, add_zero]
  rw [h6, RingHom.map_mul, RingEquiv.map_mul]
  show finIso D (Formalism.L2.Theta.finPart D e) P * finIso D (Formalism.L2.Theta.finPart D (e + cA D e)) P = 0
  rw [h5, mul_zero]

theorem char_split_value (D : D7) (c : (Formalism.L2.Theta.AE D)ˣ →* Circle) (n : ℕ) (hc : Formalism.L2.Theta.IsHeckeChar D c)
    (hr : Formalism.L2.Theta.ResEta D c n) (e : Formalism.L2.Theta.AE D) (he : IsSplitIdem D e) (x₀ : (Formalism.L2.Theta.AE D)ˣ)
    (a : Formalism.L2.Theta.AE D) (hx : (x₀ : Formalism.L2.Theta.AE D) = e * a + (1 - e)) :
    Mod1All ((c x₀ : Circle) : ℂ) ∧ ∀ (q : ℕ) [Fact q.Prime], GlobalTheory.MovedKappaEx.OffPrime e q →
      GlobalTheory.MovedKappaEx.UnitAt q ((c x₀ : Circle) : ℂ) := by
  obtain ⟨m, hm⟩ := inf_val D c n hc hr
  obtain ⟨-, -, -, M, hM, hMu⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c hc.1
  have hinf : Formalism.L2.Theta.infPart D (x₀ : Formalism.L2.Theta.AE D) = 1 := by
    rw [hx, RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_one,
      GlobalTheory.SplitScalar.infPart_splitIdem he, zero_mul, sub_zero, zero_add]
  obtain ⟨h, k, y, w, hh, hw, hy1, hy2, e1, hk⟩ := exists_pow_rel D x₀ hinf
  have e2 : c x₀ ^ (h * M) * c y ^ M = 1 := by
    rw [pow_mul, ← mul_pow, ← map_pow, ← map_mul, e1, map_mul, hc.2 k, mul_one, hMu w hw]
  have e3 : ((c x₀ : Circle) : ℂ) ^ (h * M) *
      ∏ τ, (tauE D τ (k : D.host.E) / (‖tauE D τ (k : D.host.E)‖ : ℂ)) ^ (m τ * M) = 1 := by
    simp only [zpow_mul, zpow_natCast]
    rw [Finset.prod_pow, ← hm k y hy1 hy2, ← Circle.coe_pow, ← Circle.coe_pow, ← Circle.coe_mul, e2, Circle.coe_one]
  obtain ⟨h1, h2⟩ := values_of_rel D _ (h * M) k (fun τ => m τ * M) (Nat.mul_pos hh hM) e3
  refine ⟨h1, fun q _ hq => h2 q fun P hP => hk P ?_⟩
  rw [hx, RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_one, RingEquiv.map_add, RingEquiv.map_sub,
    RingEquiv.map_mul, RingEquiv.map_one]
  show finIso D (Formalism.L2.Theta.finPart D e) P * finIso D (Formalism.L2.Theta.finPart D a) P + (1 - finIso D (Formalism.L2.Theta.finPart D e) P) = 1
  rw [finIso_idem D he hq P hP, zero_mul, sub_zero, zero_add]

theorem offPrime_conj {D : D7} {e : Formalism.L2.Theta.AE D} {q : ℕ} (h : GlobalTheory.MovedKappaEx.OffPrime e q) :
    GlobalTheory.MovedKappaEx.OffPrime (cA D e) q := fun v ε hv hε =>
  h v ε hv (by rw [← hε, GlobalTheory.MovedIdem.cA_cA, add_comm])

theorem defPair_inRange {T : Type} {m : ℕ} {p : Pair T} (h : DefPair m p) : p.InRange m := by
  cases p <;> simp only [DefPair, Pair.InRange, Pair.big, Node.InRange] at h ⊢ <;> omega

theorem split_chars : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ x₀ : (Formalism.L2.Theta.AE D)ˣ,
    (∃ a : Formalism.L2.Theta.AE D, (x₀ : Formalism.L2.Theta.AE D) = e * a + (1 - e) ∨ (x₀ : Formalism.L2.Theta.AE D) = cA D e * a + (1 - cA D e)) →
    (Mod1All ((ch.G.chrS p x₀ : Circle) : ℂ) ∧ Mod1All ((ch.G.chrT p x₀ : Circle) : ℂ)) ∧
    ∀ (q : ℕ) [Fact q.Prime], GlobalTheory.MovedKappaEx.OffPrime e q →
      GlobalTheory.MovedKappaEx.UnitAt q ((ch.G.chrS p x₀ : Circle) : ℂ) ∧ GlobalTheory.MovedKappaEx.UnitAt q ((ch.G.chrT p x₀ : Circle) : ℂ) := by
  intro _ _ D Γ _ _ Pl0 T A Ks _ _ _ R ch _ p hp e he x₀ hx
  have hW := ch.W.om_is p (defPair_inRange hp)
  obtain ⟨e', he', hoff, a, hx'⟩ : ∃ e' : Formalism.L2.Theta.AE D, IsSplitIdem D e' ∧
      (∀ q, GlobalTheory.MovedKappaEx.OffPrime e q → GlobalTheory.MovedKappaEx.OffPrime e' q) ∧
      ∃ a : Formalism.L2.Theta.AE D, (x₀ : Formalism.L2.Theta.AE D) = e' * a + (1 - e') := by
    obtain ⟨a, ha | ha⟩ := hx
    · exact ⟨e, he, fun _ h => h, a, ha⟩
    · exact ⟨cA D e, GlobalTheory.ConjAdjWeil.isSplitIdem_conj he, fun _ h => offPrime_conj h, a, ha⟩
  have hS := char_split_value D _ _ hW.hecS hW.resS e' he' x₀ a hx'
  have hT := char_split_value D _ _ hW.hecT hW.resT e' he' x₀ a hx'
  exact ⟨⟨hS.1, hT.1⟩, fun q _ hq => ⟨hS.2 q (hoff q hq), hT.2 q (hoff q hq)⟩⟩

end GlobalTheory.SplitCharValue
