import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FromNAdd
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelHodgeRelayStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PtAfTypeMain
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TestOrderSections
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.KernelMem
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ReducesAtOfWithE
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsDualFamily
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Typed
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsUnitOfVal
import Development.WeilBound.CoreStatements.HodgeTatePoints.ValCastSub
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.TestGroupPoint

theorem spanOver_ind {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o C] [Algebra Ω C] (RC : Subalgebra o C)
    {r : ℕ} (L : AddSubgroup (Fin r → Ω)) (T : AddSubgroup (Fin r → C)) (hT : ∀ t ∈ RC, ∀ a ∈ T, t • a ∈ T)
    (h : ∀ a ∈ L, (fun k => algebraMap Ω C (a k)) ∈ T) : spanOver RC (bcMap Ω C _ '' L) ≤ T := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨t, ht, _, ⟨a, ha, rfl⟩, rfl⟩
  exact hT t ht _ (h a ha)

theorem mem_spanOver {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o C] [Algebra Ω C] (RC : Subalgebra o C)
    {r : ℕ} (L : AddSubgroup (Fin r → Ω)) {a : Fin r → Ω} (ha : a ∈ L) :
    (fun k => algebraMap Ω C (a k)) ∈ spanOver RC (bcMap Ω C _ '' L) :=
  AddSubgroup.subset_closure ⟨1, RC.one_mem, _, ⟨a, ha, rfl⟩, (one_smul _ _).symm⟩

def smallSub {C : Type} [Field C] (v : Valuation C NNReal) (t : NNReal) {r : ℕ} {I : Type}
    (f : I → ((Fin r → C) →ₗ[C] C)) : AddSubgroup (Fin r → C) where
  carrier := {a | ∀ m, v (f m a) ≤ t}
  add_mem' ha hb m := by rw [map_add]; exact v.map_add_le (ha m) (hb m)
  zero_mem' m := by simp
  neg_mem' ha m := by rw [map_neg, Valuation.map_neg]; exact ha m

theorem bar_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a :=
  RingOfIntegers.ext (by rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply])

end PositivityTheory.Xgn.TestGroupPoint

open PositivityTheory.Xgn.TestGroupPoint PositivityTheory.HtPt.Sgp in
theorem PositivityTheory.Xgn.test_group_point_exists : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∀ (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → v (p : C) < 1 → ∀ τ (hb : ((Fin (labelRk D (e τ)) → C) →ₗ[C] (Fin (D.p + D.q) → C))), Function.Injective hb → LinearMap.range hb = LinearMap.ker (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) → (stdLat RC _).comap hb.toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).W τ → (∀ a ∈ ((chartD e b pq sc w P i).bc RC).W τ, hb a - GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (i τ) a ∈ mulLat (algebraMap O C w) (stdLat RC _)) → (((chartD e b pq sc w P i).bc RC).hh RC p (fun a => χ τ a)).map (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))).toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).om τ ∧ (((chartD e b pq sc w P i).bc RC).hh RC p (fun a => χ τ a)).comap hb.toAddMonoidHom = divLat (algebraMap O C w) (((chartD e b pq sc w P i).bc RC).lie τ) := by
  intro hF _ _ hHD hOC E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hd hpq p _ hpS hfree hp2 hdisc b hb φ hφ A _ _ _ m _
    hpm O _ _ _ _ _ _ _ t₀ Sg _ e φ' F _ _ _ pq sc w σF hO hsec G c' hc' P i hseq hbase C _ _ _ _ RC hT χ hχ _ _ _ v hv hvp
    τ hbm _ _ hW hcl
  have hpp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  haveI : NeZero (p ^ 𝔐.R p) := ⟨pow_ne_zero _ hpp.ne_zero⟩
  have hR4 := 𝔐.R_ge p hpS
  obtain ⟨h0, hNoe, hIC, hFr⟩ := Par.chart_facts E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd p hpS A m hpm O c' hc'
  obtain ⟨-, hN, -⟩ := GlobalTheory.T.hodge_tate_free_integral_models E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS (Par.zp Ω p) (Par.mem_range_zp Ω p)
  obtain ⟨AA, AW, hAA, hAW, hM, hret, -⟩ := PositivityTheory.Xgn.test_order_sections E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p
    hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σF hO hsec G c' hc' P i hseq hbase C RC hT χ hχ
  obtain ⟨-, htight⟩ := GlobalTheory.T.arith_variety_model_hodge_relay hHD hOC E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p
    hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σF hO hsec G c' hc' P i hseq hbase C RC hT χ hχ v hv hvp
  obtain ⟨g, io, ev, Hm, Eg, hio, hev, hcard, hEt, ⟨Ei, hEi, hiso⟩, hE, hH⟩ :=
    point_data hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p hpS A m hpm O G c' hc' P C RC w hO.2.2.2.2.2.2.2 hT
  obtain ⟨Dv, hD, hDs, hDch⟩ := exists_der hpS P hT.2.2.2 io
  have hlat := fun t => lattices E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p hpS A m hpm O G c' hc' P C RC hdisc
    hT.2.2.2 io ev hio hev t (b t) (hb t).1 (hb t).2
  haveI := hT.1
  haveI : CharZero C := charZero_of_injective_algebraMap (algebraMap Ω C).injective
  have hint : v.Integers RC := ⟨Subtype.val_injective, fun x => (hv _).1 x.2, fun r hr => ⟨⟨r, (hv _).2 hr⟩, rfl⟩⟩
  obtain ⟨φN, hφN⟩ := exists_phiN E (D.p + D.q) p
  have hζ : IsPrimitiveRoot (algebraMap Ω C (G.ζ ^ p ^ (𝔐.R p - 1))) p :=
    (G.ζ_prim.pow (pow_pos hpp.pos _) (by rw [← pow_succ, Nat.sub_add_cancel (by omega)])).map_of_injective
      (algebraMap Ω C).injective
  let ih : (Fin (D.p + D.q) → 𝓞 E) →+ (Fin g → RC) := io.toAddMonoidHom.comp (P.Dh.h.codRestrict P.Dh.om P.Dh.h_mem)
  obtain ⟨cp, hcp, k0, k1, k2, k3, k4⟩ := core_pull hint hvp hp2 φN hφN AA _ hAA htight hcard
    (dvd_pow_self p (show 𝔐.R p ≠ 0 by omega)) G.e hζ (kernel_mem hpS P hT) Dv hD (Set.range io) hio
    (by rintro _ ⟨u, rfl⟩; exact hDs u) ih hDch Hm Eg Ei hEt hEi hiso hE hH
  obtain ⟨σ, hσ, hσs, -⟩ := PositivityTheory.Xgn.exists_cm_type_embedding E H D l Xo c O₀ β Y S Ω K J y 𝔐 (e τ)
  obtain ⟨hσO, x₀, hx₀, o₀, ho₀⟩ := PositivityTheory.Xgn.SequenceDifferentials.main E Ω p hdisc A m hpm O σ
  have hOC' : ∀ o : O, algebraMap Ω C (algebraMap O Ω o) = algebraMap O C o := fun o =>
    (IsScalarTower.algebraMap_apply O Ω C o).symm
  obtain ⟨σ', s, hσ', hs, hdu⟩ := exists_dualOf (R := RC) (C := C) Subtype.val_injective ((algebraMap Ω C).comp σ)
    (fun a => by
      obtain ⟨o, ho⟩ := hσO a
      exact ⟨algebraMap O RC o, by rw [RingHom.comp_apply, ← ho, hOC']; rfl⟩)
    (fun k => by
      obtain ⟨z, hz⟩ := HT.exists_different_mul_dualInt E x₀ hx₀ k
      obtain ⟨o, ho⟩ := hσO z
      refine ⟨algebraMap O RC (o₀ * o), ?_⟩
      have : algebraMap O Ω (o₀ * o) = σ (HT.dualInt E k) := by
        rw [map_mul, ho, hz, map_mul, ← _root_.mul_assoc, ho₀, _root_.one_mul]
      rw [RingHom.comp_apply, ← this, hOC']; rfl)
  obtain ⟨χ', hχ', hcong⟩ := chi_cong p RC v hv pq sc hsec (σF τ) (χ τ) (hχ τ) σ' fun a => by
    obtain ⟨o, ho, ho'⟩ := hO.2.2.2.2.1 τ a
    exact ⟨o, by rw [← hOC', ho, ← hσ]; exact (hσ' a).symm, ho'⟩
  have hst := afLat_stable hdu φN hφN AA.carrier (fun a f hf => by rw [hAA] at hf ⊢; exact act_mem P a f hf) _
    (mem_pull φN AA)
  have hhh := (pt_af_type_main RC p (ReciprocityTheory.PGsh.Up.hopfPull φN AA).carrier (ReciprocityTheory.PGsh.Up.hopfPull φN AA).le_int
    ((chartD e b pq sc w P i).bc RC) χ' (Subtype.ext (by rw [← hχ', map_zero]; rfl))
    (Subtype.ext (by rw [← hχ', map_one]; rfl))
    (φN.symm.toAddMonoidHom.comp (TestPt.toNAdd sc)) ((TestPt.fromNAdd pq).comp φN.toAddMonoidHom)
    (fun z => by
      change TestPt.fromNAdd pq (φN (φN.symm (TestPt.toNAdd sc z))) = z
      rw [AddEquiv.apply_symm_apply]
      exact funext fun k => hsec.1 (z k))
    (fun h hh => by
      obtain ⟨f, hf, rfl⟩ := (mem_pull φN AA h).1 hh
      refine (mem_pull φN AA _).2 ⟨_, hret f hf, funext fun x => ?_⟩
      change _ = f (φN (φN.symm _))
      rw [AddEquiv.apply_symm_apply]
      rfl)
    (by
      rw [← hM, hAW, TestPt.testOrdW, ← hAA]
      congr 1
      ext f
      constructor
      · rintro ⟨h, hh, rfl⟩
        obtain ⟨f, hf, rfl⟩ := (mem_pull φN AA h).1 hh
        refine ⟨f, hf, funext fun x => ?_⟩
        change _ = f (φN (φN.symm _))
        rw [AddEquiv.apply_symm_apply]
        rfl
      · rintro ⟨f, hf, rfl⟩
        refine ⟨_, (mem_pull φN AA _).2 ⟨f, hf, rfl⟩, funext fun x => ?_⟩
        change f (φN (φN.symm _)) = _
        rw [AddEquiv.apply_symm_apply]
        rfl)
    (Pm _ σ') (Jm _ s) (Pm_mul_Jm hdu) (Pm_cong pq φN hφN χ' hcong) hst).2
  simp only [← hχ'] at hhh
  obtain ⟨u, hu, hwu⟩ := hO.2.2.2.2.2.2.1.2.1
  have hp3 : 2 ≤ p - 1 := by have := hpp.two_le; omega
  have hvw : v (algebraMap O C w) ^ (p - 1) = v (p : C) := by
    rw [← map_pow, ← map_pow, hwu, map_mul, map_mul, map_natCast,
      show v (algebraMap O C u) = 1 from hint.one_of_isUnit (hu.map (algebraMap O RC)), _root_.one_mul]
  have hw1 : v (algebraMap O C w) < 1 := lt_of_not_ge fun h => absurd (hvw ▸ one_le_pow₀ h) (not_le.2 hvp)
  have hw0 : algebraMap O C w ≠ 0 := fun h => by
    rw [h, map_zero, zero_pow (by omega), eq_comm, Valuation.zero_iff] at hvw
    exact Nat.cast_ne_zero.2 hpp.ne_zero hvw
  have hpw : v (p : C) ≤ v (algebraMap O C w) * v (algebraMap O C w) := by
    rw [← hvw, ← sq]
    exact pow_le_pow_of_le_one zero_le hw1.le hp3
  have hWl : ∀ a ∈ ((chartD e b pq sc w P i).bc RC).W τ, algebraMap O C w • a ∈ ((chartD e b pq sc w P i).bc RC).lie τ :=
    fun a ha => spanOver_ind RC _ (divLat (algebraMap O C w) (((chartD e b pq sc w P i).bc RC).lie τ))
      (fun t ht a ha => by
        simp only [divLat, AddSubgroup.mem_comap, DistribMulAction.toAddMonoidHom_apply] at ha ⊢
        rw [smul_comm]
        exact smul_mem_spanOver RC _ ht ha)
      (fun a ha => by
        have h1 : algebraMap O Ω w • a ∈ (chartD e b pq sc w P i).lie τ := (hbase.incl τ).2.1 ha
        have h2 := mem_spanOver RC _ h1
        have e : algebraMap O C w • (fun k => algebraMap Ω C (a k)) =
            fun k => algebraMap Ω C ((algebraMap O Ω w • a) k) := by
          funext k
          change _ = algebraMap Ω C (algebraMap O Ω w * a k)
          rw [map_mul, hOC']
          rfl
        simp only [divLat, AddSubgroup.mem_comap, DistribMulAction.toAddMonoidHom_apply]
        rw [e]
        exact h2) ha
  have heig : ∀ t a k, 𝔐.ρ a (b t k) = 𝔐.emb t a • b t k := fun t a k => by
    have : b t k ∈ 𝔐.Vgen t := (hb t).2 ▸ Submodule.subset_span ⟨k, rfl⟩
    simp only [HodgeCpt.Vgen, GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      sub_eq_zero] at this
    exact this a
  refine typed RC v hv (p : C) (algebraMap O C w) hw0 hw1 hpw cp (p : RC)
    ((pow_left_inj₀ zero_le zero_le (by omega)).1 (hcp.trans hvw.symm)) (SubringClass.coe_natCast _ _) _ Hm Eg Ei hEi
    k0 k1 k2 k3 k4 (Pm _ σ') (Jm _ s) (Pm_mul_Jm hdu) hst _ hhh (fun k => ev (b (e τ).swap k)) (fun k => ev (b (e τ) k))
    _ _ _ (hlat (e τ).swap).1 (hlat (e τ)).2
    (spanOver_ind RC _ _ (fun t ht a ha => smul_mem_spanOver RC _ ht ha) fun a ha =>
      mem_spanOver RC _ ((hbase.incl τ).1 ha)) hWl _
    (hq_chart P.Dh 𝔐.ρ H.bar io ev Hm (by omega) P.Dh_act hev hH σ σ' hσ' (b (e τ).swap) fun a k => ?_)
    (TestPt.bcLin C (i τ)) hbm (fun a ha => ?_) hW hcl
  · rw [heig, ← hσs, H.bar_eq, RingHom.comp_apply]
    congr 2
    first
      | exact IsCMField.complexConj_apply_apply E _
      | simp [HT.cmConj]
  · let f : Ix E (D.p + D.q) → ((Fin (labelRk D (e τ)) → C) →ₗ[C] C) := fun m =>
      ∑ m', (Eg m m' : C) • (LinearMap.proj m' ∘ₗ ((Jm _ s).map (algebraMap RC C)).mulVecLin ∘ₗ TestPt.bcLin C (i τ)) +
        ∑ k, ev (b (e τ) k) (fun j => (Hm j m : C)) • LinearMap.proj k
    have hf : ∀ m a, f m a = ∑ m', (Eg m m' : C) * ((Jm _ s).map (algebraMap RC C)).mulVec (TestPt.bcLin C (i τ) a) m' +
        ∑ k, a k * ev (b (e τ) k) fun j => (Hm j m : C) := fun m a => by
      simp only [f, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
        LinearMap.proj_apply, Matrix.mulVecLin_apply, smul_eq_mul, mul_comm (a _)]
    intro m
    rw [← hf]
    refine spanOver_ind RC _ (smallSub v (v (algebraMap O C w)) f) (fun t ht a ha m => ?_) (fun a ha m => ?_) ha m
    · rw [map_smul, smul_eq_mul, map_mul]
      exact (mul_le_of_le_one_left zero_le ((hv _).1 ht)).trans (ha m)
    · rw [hf, show TestPt.bcLin C (i τ) (fun k => algebraMap Ω C (a k)) = fun l => algebraMap Ω C (i τ a l) from
        funext (bcLin_bc _ _)]
      exact hdual_chart P.Dh 𝔐.ρ H.bar io ev Hm (by omega) P.Dh_act hev hH (bar_bar H)
        (by rw [P.Dh_e]; exact G.adj) Eg (by rw [P.Dh_e]; exact hE) σ σ' hσ' s hs hdu (b (e τ))
        (fun a k => by rw [heig, hσ]) v hv _ hw0 hw1.le hpw a (i τ a)
        (fun l => (hseq τ).1.1 a ha l (Set.mem_univ l)) (M := 𝔐.R p - 2) (by omega) ((hseq τ).2 σ hσ a ha)
        ((hlat (e τ)).2 _ |>.1 (hWl _ (mem_spanOver RC _ ha))) m
