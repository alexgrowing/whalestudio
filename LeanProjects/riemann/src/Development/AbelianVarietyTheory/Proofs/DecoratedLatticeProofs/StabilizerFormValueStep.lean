import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HermitianCodeWordWeilElementMemQuadraticField
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KmapEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KmapMemValCTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KAtTopEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DifferentiableSumU
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelTermTargetStabiliserLaw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelLawOfFiniteDatumLaw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnFieldRamificationIdxInEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberBadPrimesNoConjugatePair
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetUnitaryStabiliserSelfDualLatticeNormOne

noncomputable section

namespace GlobalTheory.KerStab

section Datum

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep GlobalTheory.TopLaw GlobalTheory.Mem.Col2

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ} {u : Pr.Word}

theorem factor_of_fix (i : ℕ) {j j' : ℕ} {Λ : LevFam X.E X.K (R.N j) Pr.vGs} {Θ : LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))}
    {Λ' : LevFam X.E X.K (R.N j') Pr.vGs} {Θ' : LevQFam X.E X.K (R.N j') (QE sel (mu : Chr X.F X.E X.K))}
    (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K))) (p : ChPt (R := R) sel mu u j) (p' : ChPt (R := R) sel mu u j')
    (g : FrmG Λ' Θ') (hg : g • p' = p') :
    ∃ (κ : GLQ X.E (R.N j) (rowSG Pr sel mu)) (κ' : GLQ X.E (R.N j') (rowSG Pr sel mu)) (a a' : rowSG Pr sel mu → X.Kˣ),
      (∀ P, frsF sel mu p P = (1 : UF X.E (R.N j)).1 * (frsF sel mu p P * ((κ P)⁻¹).1)) ∧
      (∀ P, frsF sel mu p' P = g.1.1 * (frsF sel mu p' P * ((κ' P)⁻¹).1)) ∧
      (∀ P, LevAt Λ Θ P (κ P) (a P)) ∧ (∀ P, LevAt Λ' Θ' P (κ' P) (a' P)) ∧
      ∏ P : rowSG Pr sel mu, (rhoS Ch sel mu i P ((LinearEquiv.det (κ⁻¹ P).1 : X.Eˣ) : X.E) *
          rhoT Ch sel mu i P ((LinearEquiv.det (κ'⁻¹ P).1 : X.Eˣ) : X.E)) =
        ∏ P : rowSG Pr sel mu, muAt Ch sel mu cst i P ((LinearEquiv.det g.1.1 : X.Eˣ) : X.E) ∧
      (∏ P, a' P) * (∏ P, a P)⁻¹ = Λ'.chr g.2.1 * Θ'.chr g.2.2 := by
  obtain ⟨κ, a, hκ, ha, ea⟩ := exists_pass hd (1 : FrmG Λ Θ) p
  obtain ⟨κ', a', hκ', ha', ea'⟩ := exists_pass hd g p'
  rw [one_smul] at hκ
  rw [hg] at hκ'
  refine ⟨κ, κ', a, a', hκ, hκ', ha, ha', Finset.prod_congr rfl fun P _ => ?_, ?_⟩
  · have h1 : ((κ P)⁻¹).1 = 1 := by
      have h := hκ P
      change _ = 1 * _ at h
      rw [one_mul] at h
      exact (left_eq_mul.1 h)
    have h2 : LinearEquiv.det (κ' P).1 = LinearEquiv.det g.1.1 := by
      have h := congrArg LinearEquiv.det (hκ' P)
      rw [map_mul, map_mul, Subgroup.coe_inv, map_inv, mul_left_comm, left_eq_mul, mul_inv_eq_one] at h
      exact h.symm
    have h3 : rhoS Ch sel mu i P ((LinearEquiv.det (κ⁻¹ P).1 : X.Eˣ) : X.E) = 1 := by
      rw [Pi.inv_apply, h1, map_one, Units.val_one]
      have hr : redP P.1 (1 : X.E) = 1 := reduction_coe P.1 1
      have hu : IsUnit (redP P.1 (1 : X.E)) := hr ▸ isUnit_one
      unfold rhoS LocE.unitV
      rw [dif_pos hu, show hu.unit = 1 from Units.ext hr, map_one, Units.val_one]
    rw [h3, one_mul, Pi.inv_apply, rhoT_inv, ← GlobalTheory.MatLaw.muAt_det (cst := cst), h2]
  · rw [ea', ea]
    change _ * (Λ.chr 1 * Θ.chr 1)⁻¹ = _
    rw [map_one, map_one, mul_one, inv_one, mul_one]

theorem xiAt_stab (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S ∧ ∀ i, Pr.g i ∈ S)
    (hL : L.Ok Ch sel mu cst G m2) (hs : cst.sharp = true) {i : ℕ} (hi : i < R.m) (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1))
    (p : PtAt R sel mu cst u i) (p' : PtAt R sel mu cst u (i + 1))
    (g : FrmG (levGAt sel mu L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) (i + 1) b')
      (levQAt sel mu L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) (i + 1) b'))
    (h1 : g • p'.1.1 = p'.1.1) (h2 : (fun v => g.1.1 v) '' p'.1.2 = p'.1.2) (x : HomE X.E (R.N i) (R.N (i + 1))) :
    xiAt Ch sel mu cst L u i b b' p p' (g.1.1.toLinearMap ∘ₗ x) *
        ∏ P : rowSG Pr sel mu, muAt Ch sel mu cst i P ((LinearEquiv.det g.1.1 : X.Eˣ) : X.E) =
      (((levGAt sel mu L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) (i + 1) b').chr g.2.1 *
        (levQAt sel mu L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) (i + 1) b').chr g.2.2 : X.Kˣ) : X.K) *
        xiAt Ch sel mu cst L u i b b' p p' x := by
  have hd := (tilOk_of_avoid (mu := mu) hPr hsel u hS).2.2
  have hm := hL.hm
  have e0 : phiT X.K p.1.1.deco.1 p'.1.1.deco.1 (g.1.1.toLinearMap ∘ₗ x ∘ₗ (1 : UF X.E (R.N i)).1.symm.toLinearMap) =
      phiT X.K p.1.1.deco.1 p'.1.1.deco.1 x :=
    (congrArg₂ (fun (q : ChPt (R := R) sel mu u i) (q' : ChPt (R := R) sel mu u (i + 1)) =>
      phiT X.K q.deco.1 q'.deco.1 (g.1.1.toLinearMap ∘ₗ x ∘ₗ (1 : UF X.E (R.N i)).1.symm.toLinearMap))
      (one_smul (FrmG (levGAt sel mu L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) i b)
        (levQAt sel mu L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) i b)) p.1.1) h1).symm.trans (phiT_act _ _ _ _ _ _ _)
  rcases lt_trichotomy (i + 2) R.m with h | h | h
  · obtain ⟨al, rfl⟩ : ∃ al, b = Idx.of al (by omega) := ⟨_, (Idx.of_get b (by omega) _).symm⟩
    obtain ⟨be, rfl⟩ : ∃ be, b' = Idx.of be (by omega) := ⟨_, (Idx.of_get b' (by omega) _).symm⟩
    obtain ⟨κ, κ', a, a', hκ, hκ', ha, ha', e1, e2⟩ := factor_of_fix (Ch := Ch) (cst := cst) (Λ := L.levG i al) (Θ := L.levQ i al) i hd p.1.1 p'.1.1 g h1
    rw [xiAt_entry Ch sel mu cst L h rfl rfl, ← e1, ← e2]
    exact GlobalTheory.MatLaw.xiEntry_law hX hPr hsel hL (by omega) hκ hκ' ha ha' x e0
  · obtain rfl : m2 = i := by omega
    obtain ⟨al, rfl⟩ : ∃ al, b = Idx.of al (by omega) := ⟨_, (Idx.of_get b (by omega) _).symm⟩
    obtain ⟨be, rfl⟩ : ∃ be, b' = Idx.of be (by omega) := ⟨_, (Idx.of_get b' (by omega) _).symm⟩
    obtain ⟨κ, κ', a, a', hκ, hκ', ha, ha', e1, e2⟩ := factor_of_fix (Ch := Ch) (cst := cst) (Λ := L.levG m2 al) (Θ := L.levQ m2 al) m2 hd p.1.1 p'.1.1 g h1
    have hY := PtAt.mem_ybSet p' h
    have key := GlobalTheory.CoupledLaw.xiCpl1_law (b := be) hX hPr hL hY (h2.symm ▸ hY) hκ hκ' ha ha' x e0
    rw [h2] at key
    rw [xiAt_penultimate_eq_xiCpl1 Ch sel mu cst L h rfl, ← e1, ← e2]
    exact key
  · obtain rfl : i = m2 + 1 := by omega
    have hj : m2 + 1 + 1 = R.m := by omega
    have hY := PtAt.mem_ybSet p hj
    obtain ⟨al, rfl⟩ : ∃ al, b = Idx.of al (by omega) := ⟨_, (Idx.of_get b (by omega) _).symm⟩
    rw [xiAt_last Ch sel mu cst L hj]
    have key : ∀ (j : ℕ) (h : j = R.m) {Λ : LevFam X.E X.K (R.N j) Pr.vGs} {Θ : LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))}
        (_ : Λ = (topLev Ch sel mu cst (rPsymF (R := R) Ch)).levG j) (_ : Θ = (topLev Ch sel mu cst (rPsymF (R := R) Ch)).levQ j)
        (q : ChPt (R := R) sel mu u j) (g : FrmG Λ Θ) (_ : g • q = q) (x : HomE X.E (R.N (m2 + 1)) (R.N j))
        (_ : phiT X.K p.1.1.deco.1 q.deco.1 (g.1.1.toLinearMap ∘ₗ x ∘ₗ (1 : UF X.E (R.N (m2 + 1))).1.symm.toLinearMap) =
          phiT X.K p.1.1.deco.1 q.deco.1 x),
        xiOver Ch sel mu cst m2 h p.1.1 p.1.2 q (g.1.1.toLinearMap ∘ₗ x) *
          ∏ P : rowSG Pr sel mu, muAt Ch sel mu cst (m2 + 1) P ((LinearEquiv.det g.1.1 : X.Eˣ) : X.E) =
        ((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ) : X.K) * xiOver Ch sel mu cst m2 h p.1.1 p.1.2 q x := by
      rintro _ rfl Λ Θ hΛ hΘ q g h1 x e0
      obtain rfl := hΛ.trans (topLev_levG_m_eq Ch sel mu cst _)
      obtain rfl := hΘ.trans (topLev_levQ_m_eq Ch sel mu cst _)
      obtain ⟨κ, κ', a, a', hκ, hκ', ha, ha', e1, e2⟩ :=
        factor_of_fix (Ch := Ch) (cst := cst) (Λ := L.levG (m2 + 1) al) (Θ := L.levQ (m2 + 1) al) (m2 + 1) hd p.1.1 q g h1
      have hI : (fun v => (1 : UF X.E (R.N (m2 + 1))).1 v) '' p.1.2 = p.1.2 := Set.image_id _
      have key := xiTop_law default hX hPr hsel hL (Or.inr ⟨hs, rfl⟩) hY (hI.symm ▸ hY) hκ hκ' ha ha' x e0
      rw [hI] at key
      rw [xiOver_rfl, ← e1, ← e2]
      exact key
    exact key _ hj (levGAt_of_le sel mu L _ hj.ge b') (levQAt_of_le sel mu L _ hj.ge b') _ g h1 x e0

theorem xiAt_invariant (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < R.m) (b : Idx sel mu L i)
    (b' : Idx sel mu L (i + 1)) (p : PtAt R sel mu cst u i) (p' : PtAt R sel mu cst u (i + 1)) (x z : HomE X.E (R.N i) (R.N (i + 1)))
    (hz : z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.1.1.deco.1.N p'.1.1.deco.1.N)) :
    xiAt Ch sel mu cst L u i b b' p p' (x + z) = xiAt Ch sel mu cst L u i b b' p p' x := by
  have hm := hL.hm
  rcases lt_trichotomy (i + 2) R.m with h | h | h
  · rw [xiAt_entry Ch sel mu cst L h (b.some_get (by omega)).symm (b'.some_get (by omega)).symm]
    exact GlobalTheory.MatLaw.xiEntry_invariant hPr hL (by omega) _ _ _ _ x z hz
  · obtain rfl : m2 = i := by omega
    rw [xiAt_penultimate_eq_xiCpl1 Ch sel mu cst L h (b.some_get (by omega)).symm]
    exact GlobalTheory.CoupledLaw.xiCpl1_invariant hPr hL _ _ _ _ x z hz
  · obtain rfl : i = m2 + 1 := by omega
    have hj : m2 + 1 + 1 = R.m := by omega
    rw [xiAt_last Ch sel mu cst L hj]
    have key : ∀ (j : ℕ) (h : j = R.m) (q : ChPt (R := R) sel mu u j) (x z : HomE X.E (R.N (m2 + 1)) (R.N j)),
        z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.1.1.deco.1.N q.deco.1.N) →
        xiOver Ch sel mu cst m2 h p.1.1 p.1.2 q (x + z) = xiOver Ch sel mu cst m2 h p.1.1 p.1.2 q x := by
      rintro _ rfl q x z hz
      exact GlobalTheory.TopXiInv.xiTop_invariant Ch sel mu cst m2 u hPr hm hL.cst_ok hL.depthQ _ _ q (p.mem_ybSet hj) x z hz
    exact key _ hj _ x z hz

theorem xiAt_invariant_levC (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < R.m) (b : Idx sel mu L i)
    (b' : Idx sel mu L (i + 1)) (p : PtAt R sel mu cst u i) (p' : PtAt R sel mu cst u (i + 1)) (x z : HomE X.E (R.N i) (R.N (i + 1)))
    (hz : z ∈ mulLat (levC sel mu cst u) (homAt (Sall sel mu u) p.1.1.deco.1.N p'.1.1.deco.1.N)) :
    xiAt Ch sel mu cst L u i b b' p p' (x + z) = xiAt Ch sel mu cst L u i b b' p p' x := by
  refine xiAt_invariant hPr hL hi b b' p p' x z ?_
  obtain ⟨v, hv, rfl⟩ := hz
  refine ⟨((cAof sel mu cst : ℕ) : 𝓞 X.E) • v, Submodule.smul_mem _ _ hv, ?_⟩
  simp only [levC, LinearMap.smul_apply, LinearMap.id_apply, smul_smul, Nat.cast_mul, mul_comm]

end Datum

section True

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC
attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre}

theorem sall_away (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) :
    ∀ P ∈ Sall (Pr := B.primes X) I.sel (I.tup a) u,
      (((I.rec7 l Z).host.QS : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal ∧ (((I.rec7 l Z).host.q : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal := by
  intro P hP
  obtain ⟨p, hp, hpP, hk⟩ := sall_nat (Pr := B.primes X) I.sel (I.tup a) l.pr h.sel_ok u hP
  have hp2 : p ∉ (I.rec7 l Z).host.small ∧ p ≠ (I.rec7 l Z).host.q := by
    rcases hk with e | ⟨j, e⟩ | hn
    · rw [e]; exact ⟨UpperTheory.Small.not_mem_of_mod _ ((I.rec7 l Z).T_mod_cond u), (I.rec7 l Z).T_ne_q u⟩
    · rw [e]; exact ⟨UpperTheory.Ram.g_notMem_small (I.rec7 l Z) j, GlobalTheory.ShortOwnCompare.level_ne_q (I.rec7 l Z) j⟩
    · exact ⟨fun e => hn (h.small_mem e), fun e => hn (e ▸ h.two_q_d_mem.2.1)⟩
  have key : ∀ r : ℕ, r.Prime → r ≠ p → ((r : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal := by
    intro r hr hrp hrP
    have hc : IsCoprime ((p : ℕ) : 𝓞 B.fields.E) ((r : ℕ) : 𝓞 B.fields.E) := by
      have h1 := (Nat.coprime_primes hp hr).2 (Ne.symm hrp)
      have h2 := (Nat.isCoprime_iff_coprime.2 h1).map (Int.castRingHom (𝓞 B.fields.E))
      simpa using h2
    obtain ⟨s, t, hst⟩ := hc
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hst ▸ add_mem (P.asIdeal.mul_mem_left s hpP) (P.asIdeal.mul_mem_left t hrP)))
  exact ⟨UpperTheory.Ram.natCast_notMem_of_coprime P.isPrime.ne_top hpP
    ((Nat.Prime.coprime_iff_not_dvd hp).2 (UpperTheory.Small.not_dvd_QS _ hp hp2.1)).symm, key _ (I.rec7 l Z).host.hyp.1 hp2.2.symm⟩

theorem prod_muAt_det (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) {i : ℕ} (hi : i < B.R.m)
    (p' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1)) (γ : UF B.fields.E (B.R.N (i + 1)))
    (hγ : gmap γ.1 p'.1.1.deco.1.N = p'.1.1.deco.1.N) :
    B.embLL (∏ P : rowSG (B.primes X) I.sel (I.tup a), muAt I.Ch I.sel (I.tup a) (I.cst a) i P
        ((LinearEquiv.det γ.1 : B.fields.Eˣ) : B.fields.E)) =
      ∏ τ, B.fields.embC B.embLL τ ((LinearEquiv.det γ.1 : B.fields.Eˣ) : B.fields.E) ^ (-(I.chain l u a).sDiv i τ) := by
  have hX := (base_fields_primes_ok B X).1
  have hok := seamOf_ok B (I.cols l) Z.W Z.V Z.S Z.N Z.G
  have hχ : TaylorLogMetric.IsChi (I.rec7 l Z) I.chi := GlobalTheory.Mem.ChiIdeal.isChi_chiId _ _ I.C.isChi
  have hA := admissible_assembled_evenRanks B (I.cols l) Z.W Z.V Z.S Z.N Z.G (i + 1) (i + 1) p'.1.1.deco p'.1.1.deco
  obtain ⟨hzs, hzi, hprod1⟩ := GlobalTheory.DetFields.det_of_stab (I.rec7 l Z) B.fields (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hok hχ _ _
    ((seamOf_lat B (I.cols l) Z.W Z.V Z.S Z.N Z.G _).symm ▸ hA.2.2.1) γ hγ
  generalize ((LinearEquiv.det γ.1 : B.fields.Eˣ) : B.fields.E) = z at hzs hzi hprod1 ⊢
  have hz0 : z ≠ 0 := left_ne_zero_of_mul_eq_one hzs
  let eZ : Fin B.R.m → B.fields.Tau → ℤ := fun j τ => (I.chain l u a).sDiv j τ + ((B.R.N j / 2 : ℕ) : ℤ)
  have heZ : ∀ j τ, ((eZ j τ : ℤ) : ℚ) = (B.hc τ).e j := by
    intro j τ
    have h1 := (I.chain l u a).sDiv_eq j j.2 τ
    rw [show (B.hcW u τ).e = (B.hc τ).e from (I.rec7 l Z).hcW_e u τ] at h1
    obtain ⟨m, hm⟩ := rank_even B.R j
    have h2 : ((B.R.N j / 2 : ℕ) : ℚ) = (B.R.N j : ℚ) / 2 := by
      rw [hm]; push_cast; rw [show m + m = 2 * m by ring, Nat.mul_div_cancel_left _ two_pos]; push_cast; ring
    simp only [eZ]
    rw [Int.cast_add, h1, Int.cast_natCast, h2, sExp, Nat.add_sub_cancel]
    show (B.hc τ).e j - _ + _ = _
    ring
  have hTied : I.Ch.Tied B.embLL (fun j τ => ((eZ j τ : ℤ) : ℚ)) I.C.mu0 I.C.eta := by
    have e : (fun j τ => ((eZ j τ : ℤ) : ℚ)) = (fun j τ => (B.hc τ).e j) := funext fun j => funext fun τ => heZ j τ
    rw [e]; exact h.ch_tied
  have hP := GlobalTheory.NormOneUnit.prod_muAt I.Ch I.sel (I.tup a) (I.cst a) B.embLL eZ I.C.mu0 I.C.eta hX l.pr h.sel_ok h.g_mem
    (GlobalTheory.ColumnField.ramificationIdxIn_eq_one (I.rec7 l Z) B.fields _ hX hok) hTied ⟨i, hi⟩ z hzs hzi
  refine hP.trans ?_
  have hw0 : ∀ τ, B.fields.embC B.embLL τ z ≠ 0 := fun τ => (map_ne_zero _).2 hz0
  have h1 : ∏ τ, B.fields.embC B.embLL τ z = 1 := (Finset.prod_congr rfl fun τ _ => hok.1 τ z).trans hprod1
  simp only [eZ]
  have e1 : ∀ τ, B.fields.embC B.embLL τ z ^ (-((I.chain l u a).sDiv i τ + ((B.R.N i / 2 : ℕ) : ℤ))) =
      B.fields.embC B.embLL τ z ^ (-(I.chain l u a).sDiv i τ) * B.fields.embC B.embLL τ z ^ (-((B.R.N i / 2 : ℕ) : ℤ)) :=
    fun τ => by rw [neg_add, zpow_add₀ (hw0 τ)]
  rw [Finset.prod_congr rfl fun τ _ => e1 τ, Finset.prod_mul_distrib, Finset.prod_zpow, h1, one_zpow, mul_one]

theorem th_law (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) {i : ℕ} (hi : i < B.R.m)
    (b : (I.stp u a i).β) (b' : (I.stp u a (i + 1)).β) (p : (I.stp u a i).D b) (p' : (I.stp u a (i + 1)).D b') :
    Differentiable ℂ (I.th u a i b b' p p') ∧ ∀ (γ : UF B.fields.E (B.R.N (i + 1))), gmap γ.1 p'.1.1.deco.1.N = p'.1.1.deco.1.N →
      ∀ k : ℂ, (∀ x, B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i b b' p p' (γ.1.toLinearMap ∘ₗ x)) =
        k * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i b b' p p' x)) →
      ∀ z : VCx B.fields.Tau (B.R.N i) (B.R.N (i + 1)), I.th u a i b b' p p'
        (fun τ => (((LinearMap.toMatrix' γ.1.toLinearMap).map (B.fields.embC B.embLL τ)) * Matrix.of (z τ) : Matrix _ _ ℂ)) =
          k * I.th u a i b b' p p' z := by
  have hX := (base_fields_primes_ok B X).1
  have hok := seamOf_ok B (I.cols l) Z.W Z.V Z.S Z.N Z.G
  have hχ : TaylorLogMetric.IsChi (I.rec7 l Z) I.chi := GlobalTheory.Mem.ChiIdeal.isChi_chiId _ _ I.C.isChi
  have hcc : TaylorLogMetric.IsCurveIdeal (I.rec7 l Z) ⊤ := ⟨top_ne_bot, by simp⟩
  have hδ := ((I.J.ok_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G).1 h.amb_ok).1
  have hA : TaylorLogMetric.admitted (I.rec7 l Z) _ _ ((seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G).lat p.1.1.deco.1.N)
      ((seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G).lat p'.1.1.deco.1.N) := by
    rw [seamOf_lat, seamOf_lat]
    exact admissible_assembled_evenRanks B (I.cols l) Z.W Z.V Z.S Z.N Z.G i (i + 1) p.1.1.deco p'.1.1.deco
  have eA : I.A = ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi I.J.cD :=
    AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J I.chi
  unfold TC.th thAt thOf
  rw [eA]
  refine ⟨GlobalTheory.KerFinEntire.kerFin_entire _ _ _ _ _ _ _ _ hok hcc hδ hχ _ _ _ _ hA _ _ _, fun γ hγ k hk z => ?_⟩
  refine GlobalTheory.KerLaw.thC_left_stab _ _ _ _ _ _ _ _ hok hcc hδ hχ _ _ _ _ hA _ _ _
    (modulus_pos (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u (l.pr.T_prime _).pos)
    (GlobalTheory.BadNoConj.sall_noConj_ok (Pr := B.primes X) I.sel (I.tup a) hX l.pr h.sel_ok u (h.T_mem u) h.g_mem)
    (sall_away I h l Z u a) (fun x w hw => ?_) γ hγ k hk z
  exact congrArg B.embLL (xiAt_invariant_levC l.pr (h.idx_ok a) hi b b' p p' x w hw)

theorem Kmap_stab_tuple (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) {i : ℕ}
    (hi : i < B.R.m) (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) (g : (I.stp u a (i + 1)).Stab c')
    (f : Fr B.fields.emb B.embLL (B.R.N i) → ℂ) :
    (I.stp u a (i + 1)).tr B.fields.emb B.embLL c'.1 g.1 ((I.chain l u a).Kmap i c c' f) = (I.chain l u a).Kmap i c c' f := by
  have hX := (base_fields_primes_ok B X).1
  obtain ⟨g, hg⟩ := g
  have hg' : (I.stp u a (i + 1)).act c'.1 g ((I.stp u a (i + 1)).rep c') = (I.stp u a (i + 1)).rep c' := hg
  have h1 : g • ((I.stp u a (i + 1)).rep c').1.1 = ((I.stp u a (i + 1)).rep c').1.1 := congrArg (fun q => q.1.1) hg'
  have h2 : (fun v => g.1.1 v) '' ((I.stp u a (i + 1)).rep c').1.2 = ((I.stp u a (i + 1)).rep c').1.2 := congrArg (fun q => q.1.2) hg'
  have hγ : gmap g.1.1 ((I.stp u a (i + 1)).rep c').1.1.deco.1.N = ((I.stp u a (i + 1)).rep c').1.1.deco.1.N :=
    congrArg (fun q => q.1.1.deco.1.N) hg'
  have hXi := fun x => congrArg B.embLL (xiAt_stab (Pr := B.primes X) hX l.pr h.sel_ok ⟨h.T_mem u, h.g_mem⟩ (h.idx_ok a) (h.sharp a) hi
    c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') g h1 h2 x)
  simp only [map_mul B.embLL] at hXi
  rw [prod_muAt_det I h l Z u a hi _ g.1 hγ] at hXi
  obtain ⟨hd, hth⟩ := th_law I h l Z u a hi c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c')
  set γ : B.fields.Tau → Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) ℂ :=
    fun τ => (LinearMap.toMatrix' g.1.1.toLinearMap).map (B.fields.embC B.embLL τ) with hγdef
  have hdet : ∀ τ, (γ τ).det = B.fields.embC B.embLL τ ((LinearEquiv.det g.1.1 : B.fields.Eˣ) : B.fields.E) := fun τ => by
    rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix', RingHom.map_det]
    rfl
  simp only [← hdet] at hXi
  have hne : ∀ τ, (γ τ).det ≠ 0 := fun τ => by
    rw [hdet]; exact (map_ne_zero _).2 (Units.ne_zero _)
  set M : ℂ := ∏ τ, (γ τ).det ^ (-(I.chain l u a).sDiv i τ) with hM
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hne τ)
  set χ : ℂ := B.embLL (((I.stp u a (i + 1)).chr c'.1 g : B.fields.Kˣ) : B.fields.K) with hχ
  have hk := hth g.1 hγ (χ / M) fun x => by
    rw [div_mul_eq_mul_div, eq_div_iff hM0]
    exact hXi x
  have hK : ∀ y : Fr B.fields.emb B.embLL (B.R.N (i + 1)), (I.chain l u a).Kmap i c c' f y =
      ((I.chIn u a).rho i c * (I.chIn u a).rho' i c') * ((∏ τ, (y.1 τ).det ^ (I.chain l u a).sDiv i τ)⁻¹ *
        GL3Theta.applyAt0 (I.rec7 l Z) (GL3Theta.polD (I.rec7 l Z) I.J.cD
          (GlobalTheory.GO.ChSrc.fnPol B.fields B.embLL _ ((I.chain l u a).sharp i f)) y.1)
          (I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c'))) := fun y =>
    congrArg (fun t => _ * (_ * t)) ((GlobalTheory.GO.ChSrc.polFn_apply (X := B.fields) B.embLL _ y).trans
      (GlobalTheory.GO.eval_jetMap_jetC (I.rec7 l Z) _ _ _ _))
  funext y
  obtain ⟨y', rfl⟩ := (frEquiv B.fields.emb B.embLL ((I.stp u a (i + 1)).gam c'.1 g)).surjective y
  have e1 : frMul B.fields.emb B.embLL ((I.stp u a (i + 1)).gam c'.1 g)⁻¹
      (frEquiv B.fields.emb B.embLL ((I.stp u a (i + 1)).gam c'.1 g) y') = y' :=
    (frEquiv B.fields.emb B.embLL ((I.stp u a (i + 1)).gam c'.1 g)).left_inv y'
  have e2 : (frEquiv B.fields.emb B.embLL ((I.stp u a (i + 1)).gam c'.1 g) y').1 = fun τ => γ τ * y'.1 τ := rfl
  refine (trFr_apply _ _ _ _ _ _).trans ?_
  have e3 : (∏ τ, (γ τ * y'.1 τ).det ^ (I.chain l u a).sDiv i τ)⁻¹ = M * (∏ τ, (y'.1 τ).det ^ (I.chain l u a).sDiv i τ)⁻¹ := by
    simp only [hM, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib, zpow_neg, Finset.prod_inv_distrib, mul_inv]
  have e4 := GlobalTheory.KerJ.applyAt0_polD_eigen (I.rec7 l Z) _ _ I.J.cD
    (GlobalTheory.GO.ChSrc.fnPol B.fields B.embLL _ ((I.chain l u a).sharp i f)) y'.1 γ _ (χ / M) hne hd hk
  rw [e1, hK, hK, e2]
  refine Eq.trans ?_ (congrArg₂ (fun s t => _ * (s * t)) e3 e4).symm
  have alg : ∀ r d t : ℂ, χ * (r * (d * t)) = r * (M * d * (χ / M * t)) := fun r d t => by field_simp
  exact alg _ _ _

end True

end GlobalTheory.KerStab

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem GlobalTheory.KerStab.Kmap_stab : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → I.IsTw → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (i : ℕ), i < B.R.m →
    ∀ (c : (I.stp u I.mu0 i).Cl) (c' : (I.stp u I.mu0 (i + 1)).Cl) (g : (I.stp u I.mu0 (i + 1)).Stab c')
      (f : Fr B.fields.emb B.embLL (B.R.N i) → ℂ),
      f ∈ Formalism.L2.Forms.ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i) →
      (I.stp u I.mu0 (i + 1)).tr B.fields.emb B.embLL c'.1 g.1 ((I.chain l u I.mu0).Kmap i c c' f) = (I.chain l u I.mu0).Kmap i c c' f :=
  fun I h _ _ l Z u _ hi c c' g f _ => GlobalTheory.KerStab.Kmap_stab_tuple I h l Z u I.mu0 hi c c' g f

end
