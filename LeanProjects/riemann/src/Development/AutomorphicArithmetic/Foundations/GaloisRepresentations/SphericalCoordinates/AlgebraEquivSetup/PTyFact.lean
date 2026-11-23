import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TrivOfLe
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.Gal.W2.Seed.mem_cj_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (hG : UpperTheory.Gal.CertificateRingHomMap.LocComm)
    {q : ℕ} [Fact q.Prime] {w : Plc E} (hw : IsSplitAt w) (h : (q : 𝓞 E) ∈ w.asIdeal) : (q : 𝓞 E) ∈ (CertificateRingHomMap.cj w).asIdeal := by
  by_contra hn
  have hap : GlobalTheory.Cong.Apart w (CertificateRingHomMap.cj w) := UpperTheory.Gal.W2.Seed.apart_of_not_mem hn h
  obtain ⟨-, -, -, hs, hcc, -⟩ := hG E n w hw
  exact ((hG E n (CertificateRingHomMap.cj w) hs).2.1 w).1 hap |>.2 hcc.symm

theorem UpperTheory.Gal.W2.Seed.pTyFact :
    FacEq → LevSec → LevFact → AtApart → CongGrpEx → Denom → UpperTheory.Gal.W2.Seed.LocComm → UpperTheory.Gal.CertificateRingHomMap.LocComm → TyFact := by
  intro hF hS hLF hA hC hD hc hG E _ _ _ A n p _ S F x U w₀ Up V _ _ _ hOff _ r W hAux N _ _ L hw Ty hTy
  have hj : F.j = F.tr.j := F.j_tr
  have hL : ∀ w, L w = fac F.tr hc w := fun w => (hF E A n p S F hc w).2 _ (hTy.fac w)
  haveI : Fact r.Prime := ⟨hAux.prime⟩
  have hK1 : ∀ k, (∃ k', F.j k' = k ∧ F.th k' ∈ lev V.S V.Kw) ↔ k ∈ F.tr.lv (lev V.S (CertificateRingHomMap.levT V.Kw)) := by
    intro k
    constructor
    · rintro ⟨k', rfl, h⟩
      rw [th_eq, CertificateRingHomMap.th_mem_lev] at h
      rw [hj]
      exact (hS E A n p S F.tr V.S _ hOff.1).1 k' h
    · intro h
      refine ⟨F.tr.sec k, by rw [hj]; exact F.tr.j_sec k, ?_⟩
      rw [th_eq, CertificateRingHomMap.th_mem_lev]
      exact h
  have hKiff : ∀ k, k ∈ Ty.K ↔ k ∈ F.tr.lv (lev V.S (CertificateRingHomMap.levT V.Kw)) ∧ ∀ w ∈ W, (L w).pr k ∈ Iw n w.1 :=
    fun k => (hTy.K_iff k).trans (and_congr_left' (hK1 k))
  have hIK : ∀ w : Plc E, Iw n w ≤ GlobalTheory.LFun.KGL w n := fun w => by
    obtain ⟨K, -, -, -, -, -, -, h⟩ := hC E n 1 one_pos w
    exact h
  have hnS : ∀ w ∈ W, w.1 ∉ V.S ∧ CertificateRingHomMap.cj w.1 ∉ V.S := fun w hw' =>
    ⟨fun h => hAux.off _ h (hAux.half.above w hw'),
      fun h => hAux.off _ h (mem_cj_of_mem n hG w.2.1 (hAux.half.above w hw'))⟩
  have hAw₀ : ∀ w : Spl E p, w.1 ∉ V.S → CertificateRingHomMap.cj w.1 ∉ V.S → GlobalTheory.Cong.Apart w₀ w.1 := fun w h1 h2 =>
    ((hG E n w.1 w.2.1).2.1 w₀).2 ⟨fun e => h1 (e ▸ V.shape.mem), fun e => h2 (e ▸ V.shape.mem)⟩
  have hAp : ∀ w w' : Spl E p, GlobalTheory.Cong.Apart w.1 w'.1 → (L w).Apart (L w') := fun w w' h => by
    rw [hL, hL]
    exact (hA E A n p S F.tr hc w.1 w.2.1 w.2.2).2 w'.1 w'.2.1 w'.2.2 h
  have hLF' : ∀ w : Spl E p, w.1 ∉ V.S → CertificateRingHomMap.cj w.1 ∉ V.S →
      (L w).Fact (F.tr.lv (lev V.S (CertificateRingHomMap.levT V.Kw))) (GlobalTheory.LFun.KGL w.1 n) := fun w h1 h2 => by
    rw [hL]
    exact (hLF E A n p S F.tr hc V.S (CertificateRingHomMap.levT V.Kw) w.1 w.2.1 w.2.2 h2).2 h1
  have hTyAp : ∀ w : Spl E p, w.1 ∉ V.S → CertificateRingHomMap.cj w.1 ∉ V.S → Ty.L.Apart (L w) := fun w h1 h2 => by
    rw [hTy.L_eq]
    exact hAp ⟨w₀, hw⟩ w (hAw₀ w h1 h2)
  refine ⟨fun w hw' => ⟨⟨fun y hy => ?_, fun g hg => ((hKiff g).1 hg).2 w hw'⟩, hTyAp w (hnS w hw').1 (hnS w hw').2,
      fun w' hw'' e => hAp w w' (hAux.half.apart w hw' w' hw'' e)⟩,
    fun w h1 h2 h3 => ⟨⟨fun y hy => (hKiff _).2 ⟨(hLF' w h1 h2).1 y hy, fun u hu => ?_⟩,
      fun g hg => (hLF' w h1 h2).2 g ((hKiff g).1 hg).1⟩, hTyAp w h1 h2⟩, ?_⟩
  · refine (hKiff _).2 ⟨(hLF' w (hnS w hw').1 (hnS w hw').2).1 y (hIK w.1 hy), fun w' hw'' => ?_⟩
    by_cases e : w = w'
    · subst e
      rw [(L w).pr_loc]
      exact hy
    · rw [(hAp w' w (hAux.half.apart w' hw'' w hw' (Ne.symm e))).1 y]
      exact one_mem _
  · rw [(hAp w u (h3 u hu)).2 y]
    exact one_mem _
  · haveI : (Ty.K₀.subgroupOf Ty.K).FiniteIndex := ⟨Ty.idx⟩
    haveI : Fintype (Ty.K ⧸ Ty.K₀.subgroupOf Ty.K) := Fintype.ofFinite _
    choose c hc0 hcp hcv using fun q : Ty.K ⧸ Ty.K₀.subgroupOf Ty.K => hD p S.D S.G S.L (q.out : S.G.GAf)
    refine ⟨∏ q, c q, Finset.prod_pos fun q _ => hc0 q, Nat.Coprime.prod_left fun q _ => hcp q, fun k hk v hv => ?_⟩
    obtain ⟨q, hq⟩ : ∃ q : Ty.K ⧸ Ty.K₀.subgroupOf Ty.K, q = QuotientGroup.mk ⟨k, hk⟩ := ⟨_, rfl⟩
    have hu : (q.out : S.G.GAf)⁻¹ * k ∈ Ty.K₀ := by
      have : q.out⁻¹ * ⟨k, hk⟩ ∈ Ty.K₀.subgroupOf Ty.K := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq', hq]
      simpa [Subgroup.mem_subgroupOf] using this
    have hint : Integ S.L ((q.out : S.G.GAf)⁻¹ * k) := integ_of_mem (KN_anti (one_dvd N.1) (hTy.K₀_eq ▸ hu))
    have hk' : k = (q.out : S.G.GAf) * ((q.out : S.G.GAf)⁻¹ * k) := by group
    have h1 := hcv q _ (hint v hv)
    rw [hk', map_mul, Module.End.mul_apply, ← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ q), mul_comm, mul_smul]
    exact nsmul_mem h1 _
